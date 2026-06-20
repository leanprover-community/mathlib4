/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia, Wenrong Zou
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.PowerSeries.Substitution

import Mathlib.RingTheory.PowerSeries.Ideal

/-!
# Equivalences related to power series rings

This file establishes a number of equivalences related to power series rings and
is patterned after `Mathlib/Algebra/MvPolynomial/Equiv.lean`.

* `MvPowerSeries.isEmptyEquiv` : The isomorphism between multivariable power series
  in no variables and the ground ring.

* `MvPowerSeries.optionEquivLeft` : The isomorphism between multivariable power series
  in `Option σ` and power series with coefficients in `MvPowerSeries σ R`.

* `MvPowerSeries.finSuccEquiv` : The isomorphism between multivariable power series
  in `Fin (n + 1)` and power series over multivariable power series in `Fin n`.

* `MvPowerSeries.toAdicCompletionAlgEquiv` : the canonical isomorphism from
  multivariate power series to the adic completion of multivariate polynomials
  with respect to the ideal spanned by all variables when the index is finite.

-/

@[expose] public section

noncomputable section

open Finsupp Finset Function

namespace MvPowerSeries

section CommSemiRing

variable {σ R : Type*} [CommSemiring R]

section isEmptyEquiv

variable (σ R) in
/-- The isomorphism between multivariable power series in no variables and the ground ring. -/
@[simps!]
def isEmptyEquiv [IsEmpty σ] : MvPowerSeries σ R ≃ₐ[R] R where
  __ := constantCoeff
  invFun := C
  left_inv _ := by ext x; simp [Subsingleton.eq_zero x]
  commutes' _ := rfl

end isEmptyEquiv

section optionEquivLeft

private theorem image_optionElim_product_antidiagonal [DecidableEq σ]
    {x : σ →₀ ℕ} {n : ℕ} : image (fun ((x, y), z, w) ↦
      (z.optionElim x, w.optionElim y)) (antidiagonal n ×ˢ antidiagonal x) =
    antidiagonal (x.optionElim n) := by
  symm; ext ⟨u, v⟩
  simp only [mem_antidiagonal, mem_image, mem_product, Prod.mk.injEq, Prod.exists]
  refine ⟨fun h ↦ ⟨u none, v none, u.some, v.some, ⟨?_, ?_⟩, by simp⟩,
    fun ⟨a, b, i, j, h1, h2, h3⟩ ↦ ?_⟩
  · rw [← Finsupp.add_apply, h, optionElim_apply_none]
  · rw [← some_add, h, some_optionElim]
  · rw [← h2, ← h3, ← optionElim_add, h1.left, h1.right]

variable (R σ) in
/-- Implementation detail for `optionEquivLeft`. Use `MvPowerSeries.optionEquivLeft` instead. -/
def optionFunLeft (p : MvPowerSeries (Option σ) R) : PowerSeries (MvPowerSeries σ R) :=
  .mk fun n ↦ fun x ↦ p.coeff (x.optionElim n)

private lemma coeff_coeff_optionFunLeft (p : MvPowerSeries (Option σ) R) (n : ℕ) (x : σ →₀ ℕ) :
    coeff x (PowerSeries.coeff n (optionFunLeft σ R p)) = coeff (x.optionElim n) p := by
  rw [optionFunLeft, PowerSeries.coeff_mk, coeff]
  exact LinearMap.proj_apply ..

private theorem optionFunLeft_monomial (x : Option σ →₀ ℕ) (r : R) :
    optionFunLeft σ R (monomial x r) = PowerSeries.monomial (x none) (monomial x.some r) := by
  classical
  ext n y
  rw [PowerSeries.coeff_monomial, coeff_coeff_optionFunLeft, coeff_monomial]
  split_ifs with h1 h2 h3
  · rw [← h1]; simp
  · absurd h2
    rw [← optionElim_apply_none n, h1]
  · replace h1 : ¬ y = x.some := fun h ↦ by
      absurd h1; ext u; cases u
      · simpa
      · simpa using DFunLike.congr_fun h _
    rw [coeff_monomial, if_neg h1]
  · rw [coeff_zero]

private lemma optionFunLeft_mul (p q : MvPowerSeries (Option σ) R) :
    optionFunLeft σ R (p * q) = optionFunLeft σ R p * optionFunLeft σ R q := by
  classical
  ext
  simpa [coeff_coeff_optionFunLeft, coeff_mul, PowerSeries.coeff_mul, ← sum_product',
    ← image_optionElim_product_antidiagonal] using sum_image
      (LeftInverse.injective (g := fun (x, y) ↦ ((x none, y none), x.some, y.some))
      (fun _ ↦ by simp)).injOn

variable (R σ) in
/-- An inverse function of `optionFunLeft`. -/
def optionInvFunLeft (p : PowerSeries (MvPowerSeries σ R)) : MvPowerSeries (Option σ) R :=
  fun x ↦ (p.coeff (x none)).coeff x.some

lemma coeff_optionInvFunLeft (p : PowerSeries (MvPowerSeries σ R)) (x : Option σ →₀ ℕ) :
    coeff x (optionInvFunLeft σ R p) = (p.coeff (x none)).coeff x.some := rfl

variable (R σ) in
/-- The algebra isomorphism between multivariable power series in `Option σ` and
  power series with coefficients in `MvPowerSeries σ R`. -/
@[no_expose]
def optionEquivLeft : MvPowerSeries (Option σ) R ≃ₐ[R] PowerSeries (MvPowerSeries σ R) where
  toFun := optionFunLeft σ R
  invFun := optionInvFunLeft σ R
  left_inv _ := by ext; simp [coeff_optionInvFunLeft, coeff_coeff_optionFunLeft]
  right_inv _ := by ext; simp [coeff_optionInvFunLeft, coeff_coeff_optionFunLeft]
  map_mul' := optionFunLeft_mul
  map_add' _ _ := by ext; simp [coeff_coeff_optionFunLeft]
  commutes' := by
    simpa [MvPowerSeries.algebraMap_apply, PowerSeries.C] using
      optionFunLeft_monomial (0 : Option σ →₀ ℕ)

lemma coeff_coeff_optionEquivLeft (p : MvPowerSeries (Option σ) R) (n : ℕ) (x : σ →₀ ℕ) :
    coeff x (PowerSeries.coeff n (optionEquivLeft σ R p)) = coeff (x.optionElim n) p :=
  coeff_coeff_optionFunLeft ..

theorem optionEquivLeft_monomial (x : Option σ →₀ ℕ) (r : R) :
    optionEquivLeft σ R (monomial x r) = PowerSeries.monomial (x none) (monomial x.some r) :=
  optionFunLeft_monomial ..

@[simp]
lemma optionEquivLeft_X_some (i : σ) :
    optionEquivLeft σ R (X (Option.some i)) = (PowerSeries.C (X i)) := by
  have : (optionElim 0 (single i 1)) = single (Option.some i) 1 := by
    classical
    ext a; cases a <;> simp [single_apply]
  simpa [← X_def, PowerSeries.monomial_eq_C_mul_X_pow, this] using
    optionEquivLeft_monomial (single (Option.some i) 1 : Option σ →₀ ℕ) (1 : R)

@[simp]
lemma optionEquivLeft_X_none : optionEquivLeft σ R (X none) = PowerSeries.X := by
  simpa [PowerSeries.monomial_eq_C_mul_X_pow, ← X_def] using
    optionEquivLeft_monomial (single none 1 : Option σ →₀ ℕ) (1 : R)

@[simp]
lemma optionEquivLeft_C (r : R) : (optionEquivLeft σ R) (C r) = PowerSeries.C (C r) := by
  simpa using optionEquivLeft_monomial (0 : Option σ →₀ ℕ) (r : R)

end optionEquivLeft

section finSuccEquiv

variable {n : ℕ}

private lemma embDomain_finSuccEquiv_cons {M : Type*} [AddCommMonoid M] {n : ℕ} (i : M)
    (x : Fin n →₀ M) : embDomain (finSuccEquiv n).toEmbedding (cons i x) = optionElim i x := by
  ext a; cases a <;> simp [embDomain_eq_mapDomain]

variable (n R) in
/-- The algebra isomorphism between multivariable power series in `Fin (n + 1)` and
power series over multivariable power series in `Fin n`. -/
def finSuccEquiv : MvPowerSeries (Fin (n + 1)) R ≃ₐ[R] PowerSeries (MvPowerSeries (Fin n) R) :=
  (renameEquiv R (_root_.finSuccEquiv n)).trans (optionEquivLeft (Fin n) R)

theorem coeff_coeff_finSuccEquiv (p : MvPowerSeries (Fin (n + 1)) R) {k : ℕ} {x : Fin n →₀ ℕ} :
    coeff x (PowerSeries.coeff k (finSuccEquiv R n p)) = coeff (x.cons k) p := by
  suffices coeff x (PowerSeries.coeff k (optionEquivLeft (Fin n) R
    (rename (_root_.finSuccEquiv n) p))) = coeff (Finsupp.cons k x) p by simpa [finSuccEquiv]
  simp_rw [← Equiv.coe_toEmbedding, coeff_coeff_optionEquivLeft, ← embDomain_finSuccEquiv_cons,
    coeff_embDomain_rename]

@[simp]
theorem finSuccEquiv_X_zero : finSuccEquiv R n (X 0) = .X := by
  ext k x
  simp_rw [coeff_coeff_finSuccEquiv, PowerSeries.coeff_X, coeff_X, cons_eq_single_zero_iff]
  split_ifs with h1 h2 h3
  · simp [h1.left]
  · tauto
  · rw [coeff_one, if_neg (by tauto)]
  · rw [coeff_zero]

@[simp]
theorem finSuccEquiv_X_succ (j : Fin n) : finSuccEquiv R n (X j.succ) = .C (X j) := by
  ext k x
  simp_rw [coeff_coeff_finSuccEquiv, PowerSeries.coeff_C, coeff_X, cons_eq_single_succ_iff]
  split_ifs with h1 h2 h3
  · simp [h1.left]
  · tauto
  · rw [coeff_X, if_neg (by tauto)]
  · rw [coeff_zero]

@[simp]
theorem finSuccEquiv_C (r : R) : (finSuccEquiv R n) (C r) = PowerSeries.C (C r) := by
  ext k x
  simp_rw [coeff_coeff_finSuccEquiv, PowerSeries.coeff_C, coeff_C, ← cons_zero_zero,
    cons_injective2.eq_iff]
  split_ifs with h1 h2 h3
  · simp [h1.right]
  · tauto
  · rw [coeff_C, if_neg (by tauto)]
  · rw [coeff_zero]

theorem finSuccEquiv_comp_C : (MvPowerSeries.finSuccEquiv R n).symm.toRingHom.comp
    (PowerSeries.C.comp MvPowerSeries.C) = MvPowerSeries.C := by
  ext1; simp [AlgEquiv.symm_apply_eq]

variable (S : Type*) [CommRing S] [IsNoetherianRing S]

theorem isNoetherianRing_fin (n : ℕ) : IsNoetherianRing (MvPowerSeries (Fin n) S) := by
  induction n with
  | zero =>
    exact isNoetherianRing_of_ringEquiv S (isEmptyEquiv (Fin 0) S).toRingEquiv.symm
  | succ n _ =>
    exact isNoetherianRing_of_ringEquiv (PowerSeries (MvPowerSeries (Fin n) S))
      (finSuccEquiv S n).toRingEquiv.symm

instance isNoetherianRing [Finite σ] : IsNoetherianRing (MvPowerSeries σ S) := by
  cases nonempty_fintype σ
  have := isNoetherianRing_fin S (Fintype.card σ)
  exact isNoetherianRing_of_ringEquiv (MvPowerSeries (Fin (Fintype.card σ)) S)
    (renameEquiv S (Fintype.equivFin σ)).toRingEquiv.symm

end finSuccEquiv

end CommSemiRing

section toAdicCompletion

open Finsupp

variable {σ R : Type*} {n : ℕ} [CommRing R] [Finite σ]

lemma truncTotal_sub_truncTotal_mem_pow_idealOfVars {l m n : ℕ} (h : l ≤ m) (h' : l ≤ n)
    (p : MvPowerSeries σ R) : p.truncTotal m - p.truncTotal n ∈
      MvPolynomial.idealOfVars σ R ^ l := by
  refine (MvPolynomial.mem_pow_idealOfVars_iff' ..).mpr (fun x hx ↦ ?_)
  rw [MvPolynomial.coeff_sub, sub_eq_zero, coeff_truncTotal _ (by lia),
    coeff_truncTotal _ (by lia)]

lemma truncTotal_mul_sub_mul_truncTotal_mem_pow_idealOfVars (p q : MvPowerSeries σ R) :
    (p * q).truncTotal n - p.truncTotal n * q.truncTotal n ∈
      MvPolynomial.idealOfVars σ R ^ n := by
  refine (MvPolynomial.mem_pow_idealOfVars_iff' ..).mpr (fun x hx ↦ ?_)
  rw [MvPolynomial.coeff_sub, sub_eq_zero, coeff_truncTotal _ hx,
    coeff_truncTotal_mul_truncTotal_eq_coeff_mul _ _ hx]

/-- The canonical map induced by `truncTotal` from multivariate power series to
the quotient ring of multivariate polynomials by the `n`-th power of
the ideal spanned by all variables. -/
@[simps]
def truncTotalAlgHom (σ R : Type*) [Finite σ] [CommRing R] (n : ℕ) :
    MvPowerSeries σ R →ₐ[MvPolynomial σ R]
      MvPolynomial σ R ⧸ (MvPolynomial.idealOfVars σ R) ^ n where
  toFun p := truncTotal n p
  map_one' := by
    by_cases! h : n = 0
    · have := Ideal.Quotient.subsingleton_iff.mpr
        (show MvPolynomial.idealOfVars σ R ^ n = ⊤ by simp [h])
      exact Subsingleton.allEq ..
    rw [truncTotal_one h, map_one]
  map_mul' p q := by
    rw [← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact truncTotal_mul_sub_mul_truncTotal_mem_pow_idealOfVars p q
  map_zero' := by rw [map_zero, map_zero]
  map_add' _ _ := by simp
  commutes' p := by
    change (Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ n)) (truncTotal n p) =
      (Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ n)) p
    rw [Ideal.Quotient.eq, MvPolynomial.mem_pow_idealOfVars_iff']
    intro x h
    rw [MvPolynomial.coeff_sub, sub_eq_zero, coeff_truncTotal _ h, MvPolynomial.coeff_coe]

/-- The canonical map from multivariate power series to the adic completion of
multivariate polynomials with respect to the ideal spanned by all variables
when the index is finite. -/
def toAdicCompletion (σ R : Type*) [Finite σ] [CommRing R] :
    MvPowerSeries σ R →ₐ[MvPolynomial σ R]
      AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R) :=
  AdicCompletion.liftAlgHom (MvPolynomial.idealOfVars σ R) (truncTotalAlgHom σ R)
    (fun h ↦ AlgHom.ext fun _ ↦ by
      simpa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] using
        truncTotal_sub_truncTotal_mem_pow_idealOfVars h (le_refl _) _)

lemma toAdicCompletion_apply_eq_mk_truncTotal {n : ℕ} {p : MvPowerSeries σ R} :
    (toAdicCompletion σ R p).val n = truncTotal n p := by rfl

theorem coeff_toAdicCompletion_val_apply_out {x : σ →₀ ℕ} {p : MvPowerSeries σ R} {n : ℕ}
    (hx : degree x < n) : (Quotient.out (((toAdicCompletion σ R) p).val n)).coeff x =
      (coeff x) p := by
  rw [← coeff_truncTotal _ hx, ← sub_eq_zero, ← MvPolynomial.coeff_sub]
  apply (MvPolynomial.mem_pow_idealOfVars_iff' n _).mp
  · rw [toAdicCompletion_apply_eq_mk_truncTotal, smul_eq_mul]
    nth_rw 1 [← Ideal.mul_top (MvPolynomial.idealOfVars σ R ^ n), ← Ideal.Quotient.eq,
      Ideal.Quotient.mk_out]
  exact hx

theorem toAdicCompletion_coe (p : MvPolynomial σ R) :
    toAdicCompletion σ R p = .of (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R) p := by
  symm; ext n
  suffices p - (truncTotal n) p ∈ MvPolynomial.idealOfVars σ R ^ n by
    simpa [toAdicCompletion, AdicCompletion.liftAlgHom, AdicCompletion.liftRingHom,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact (MvPolynomial.mem_pow_idealOfVars_iff' ..).mpr fun x hx ↦ by simp [coeff_truncTotal _ hx]

/-- An inverse function of `toAdicCompletion`. -/
def toAdicCompletionInv (σ R : Type*) [CommRing R]
    (f : AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R)) :
      MvPowerSeries σ R := fun x ↦ (f.val (degree x + 1)).out.coeff x

omit [Finite σ] in
lemma coeff_toAdicCompletionInv {x : σ →₀ ℕ}
    {f : AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R)} :
      coeff x (toAdicCompletionInv σ R f) = (f.val (degree x + 1)).out.coeff x := by rfl

theorem mk_truncTotal_toAdicCompletionInv {n : ℕ}
    {f : AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R)} :
      Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ n • ⊤)
    ((truncTotal n) (toAdicCompletionInv σ R f)) = f.val n := by
  rw [← Ideal.Quotient.mk_out (f.val n), Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  simp only [smul_eq_mul, Ideal.mul_top, MvPolynomial.mem_pow_idealOfVars_iff',
    MvPolynomial.coeff_sub]
  intro x h
  rw [coeff_truncTotal _ h, coeff_toAdicCompletionInv, ← MvPolynomial.coeff_sub]
  apply (MvPolynomial.mem_pow_idealOfVars_iff' (degree x + 1) _).mp
  · nth_rw 1 [← Ideal.mul_top (MvPolynomial.idealOfVars σ R ^ (degree x + 1)),
      ← smul_eq_mul, ← Ideal.Quotient.eq]
    simp only [Submodule.mapQ_eq_factor, Submodule.factor_eq_factor, Ideal.Quotient.mk_out]
    rw [← AdicCompletion.transitionMap_ideal_mk _ (Nat.lt_iff_add_one_le.mp h), eq_comm]
    convert! f.prop h; simp
  simp

/-- The isomorphism from multivariate power series to the adic completion of
multivariate polynomials with respect to the ideal spanned by all variables
when the index is finite. -/
def toAdicCompletionAlgEquiv (σ R : Type*) [Finite σ] [CommRing R] :
    MvPowerSeries σ R ≃ₐ[MvPolynomial σ R]
      AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R) where
  __ := toAdicCompletion σ R
  invFun := toAdicCompletionInv σ R
  left_inv _ := by
    ext; simp [coeff_toAdicCompletionInv, coeff_toAdicCompletion_val_apply_out]
  right_inv _ := by ext; simpa using! mk_truncTotal_toAdicCompletionInv

@[simp]
lemma toAdicCompletionAlgEquiv_apply (p : MvPowerSeries σ R) :
    toAdicCompletionAlgEquiv σ R p = toAdicCompletion σ R p := by rfl

@[simp]
lemma toAdicCompletionAlgEquiv_symm_apply
    (x : AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R)) :
      (toAdicCompletionAlgEquiv σ R).symm x = toAdicCompletionInv σ R x := by
  rfl

end toAdicCompletion

end MvPowerSeries

section toMvPowerSeries

variable {R σ τ : Type*} [CommSemiring R] {f : PowerSeries R} (i : σ) (r : R)

open PowerSeries Filter
namespace PowerSeries

/-- Given a power series `p : R⟦X⟧` and an index `i`, we may view it as a
multivariate power series `toMvPowerSeries i p : MvPowerSeries σ R`. -/
noncomputable
def toMvPowerSeries : PowerSeries R →ₐ[R] MvPowerSeries σ R :=
  MvPowerSeries.rename (fun _ ↦ i)

theorem toMvPowerSeries_apply : f.toMvPowerSeries i = f.rename (fun _ ↦ i) := rfl

@[simp]
theorem toMvPowerSeries_C : (C r).toMvPowerSeries i = MvPowerSeries.C r := by
  rw [toMvPowerSeries_apply, C_apply, MvPowerSeries.rename_C]

@[simp]
theorem toMvPowerSeries_X : X.toMvPowerSeries i = MvPowerSeries.X i (R := R) := by
  rw [toMvPowerSeries_apply, X_apply, MvPowerSeries.rename_X]

theorem toMvPowerSeries_injective (i : σ) : Function.Injective (toMvPowerSeries (R := R) i) :=
  MvPowerSeries.rename_injective (Embedding.punit i)

theorem toMvPowerSeries_inj (i : σ) {p q : R⟦X⟧} :
    p.toMvPowerSeries i = q.toMvPowerSeries i ↔ p = q :=
  (toMvPowerSeries_injective i).eq_iff

section CommRing

variable {R : Type*} [CommRing R] {f : R⟦X⟧} {i : σ}

theorem toMvPowerSeries_eq_subst : f.toMvPowerSeries i = f.subst (MvPowerSeries.X i) := by
  rw [toMvPowerSeries_apply, MvPowerSeries.rename_eq_subst, comp_def, subst]

theorem subst_toMvPowerSeries {a : σ → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a) :
    (f.toMvPowerSeries i).subst a = f.subst (a i) := by
  rw [toMvPowerSeries_eq_subst, subst, MvPowerSeries.subst_comp_subst_apply
    (HasSubst.const (HasSubst.X _)) ha, MvPowerSeries.subst_X ha, subst]

lemma toMvPowerSeries_coeff_eq_zero {d : σ →₀ ℕ} (hd : d i = 0) (hf : f.constantCoeff = 0) :
    (f.toMvPowerSeries i).coeff d = 0 := by classical
  rw [toMvPowerSeries_apply, MvPowerSeries.rename_eq_subst, subst_X_comp_const,
    coeff_subst (HasSubst.X _), finsum_eq_zero_of_forall_eq_zero]
  simp only [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one,
    mul_zero, ite_eq_right_iff]
  intro _ a
  subst a
  simp_all

theorem _root_.MvPowerSeries.HasSubst.toMvPowerSeries (hf : f.constantCoeff = 0) :
    MvPowerSeries.HasSubst (f.toMvPowerSeries · (σ := σ)) (S := R) where
  const_coeff := by simp_all [constantCoeff, toMvPowerSeries_apply]
  coeff_zero d := Set.Finite.subset (Finite.of_fintype d.support) fun s => by
    contrapose
    simpa using fun hd ↦ toMvPowerSeries_coeff_eq_zero hd hf

end CommRing

end PowerSeries

variable (f : σ → τ) [TendstoCofinite f] (a : σ) (p : R⟦X⟧)

@[simp]
lemma MvPowerSeries.rename_comp_toMvPowerSeries :
    (rename (R := R) f).comp (PowerSeries.toMvPowerSeries a) =
      PowerSeries.toMvPowerSeries (f a) := by
  ext
  simp [toMvPowerSeries_apply, comp_def]

@[simp]
lemma MvPowerSeries.rename_toMvPowerSeries :
    (p.toMvPowerSeries a).rename f = p.toMvPowerSeries (f a) :=
  DFunLike.congr_fun (rename_comp_toMvPowerSeries ..) p

end toMvPowerSeries
