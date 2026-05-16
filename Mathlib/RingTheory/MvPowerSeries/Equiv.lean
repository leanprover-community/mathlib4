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

/-!
# Equivalences related to power series rings

This file establishes a number of equivalences related to power series rings.

* `MvPowerSeries.toAdicCompletionAlgEquiv` : the canonical isomorphism from
  multivariate power series to the adic completion of multivariate polynomials
  with respect to the ideal spanned by all variables when the index is finite.

-/

@[expose] public section

universe u v w

noncomputable section

namespace MvPowerSeries

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
    convert f.prop h; simp
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
  right_inv _ := by ext; simpa using mk_truncTotal_toAdicCompletionInv

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

variable {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
variable {σ τ : Type*} {f : PowerSeries R} (i : σ) (r : R)

open Function PowerSeries Filter Finsupp
namespace PowerSeries

/-- Given a power series p(X) ∈ R⟦X⟧ and an index i, we may view it as a
multivariate power series p(X_i) ∈ R⟦X_1, ..., X_n⟧.
-/
noncomputable
def toMvPowerSeries : PowerSeries R →ₐ[R] MvPowerSeries σ R :=
  MvPowerSeries.rename (fun _ => i)

theorem toMvPowerSeries_apply : f.toMvPowerSeries i = f.rename (fun _ => i) := rfl

theorem toMvPowerSeries_C : (C r).toMvPowerSeries i = MvPowerSeries.C r := by
  have : C r = MvPowerSeries.C r := rfl
  rw [toMvPowerSeries_apply, this, MvPowerSeries.rename_C]

theorem toMvPowerSeries_X : X.toMvPowerSeries i = MvPowerSeries.X i (R := R) := by
  rw [toMvPowerSeries_apply, X, MvPowerSeries.rename_X]

theorem toMvPowerSeries_injective (i : σ) : Function.Injective (toMvPowerSeries (R := R) i) :=
  MvPowerSeries.rename_injective (Embedding.punit i)

section CommRing

variable {R : Type*} [CommRing R] {f : PowerSeries R} (i : σ) (r : R) (p : R⟦X⟧)

theorem toMvPowerSeries_eq_subst : f.toMvPowerSeries i = f.subst (MvPowerSeries.X i) := by
  rw [toMvPowerSeries_apply, MvPowerSeries.rename_eq_subst, comp_def, subst]

theorem HasSubst.toMvPowerSeries (hf : f.constantCoeff = 0) :
    MvPowerSeries.HasSubst (f.toMvPowerSeries · (σ := σ)) (S := R) where
  const_coeff := by simp_all [constantCoeff, toMvPowerSeries_apply]
  coeff_zero d := Set.Finite.subset (Finite.of_fintype ↥d.support) fun s => by classical
    contrapose
    simp only [SetLike.mem_coe, mem_support_iff, Decidable.not_not, Set.mem_setOf_eq]
    have : (MvPowerSeries.subst (MvPowerSeries.X (R := R) ∘ fun x ↦ s) f)
      = f.subst (MvPowerSeries.X s) := rfl
    intro hd
    rw [toMvPowerSeries_apply, MvPowerSeries.rename_eq_subst, this, coeff_subst (HasSubst.X _),
      finsum_eq_zero_of_forall_eq_zero]
    intro n
    by_cases! hn : n = 0
    · simp [hn, hf]
    have : d ≠ single s n := ne_iff.mpr ⟨s, by simp [hd, hn.symm]⟩
    rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, if_neg this, smul_zero]

theorem toMvPowerSeries_val {a : σ → MvPowerSeries τ R} (i : σ)
    (ha : MvPowerSeries.HasSubst a) : (f.toMvPowerSeries i).subst a = f.subst (a i) := by
  rw [toMvPowerSeries_eq_subst, subst, MvPowerSeries.subst_comp_subst_apply
    (HasSubst.const (HasSubst.X _)) ha, MvPowerSeries.subst_X ha, subst]

end CommRing

end PowerSeries

variable (f : σ → τ) [TendstoCofinite f] (a : σ) (p : R⟦X⟧)

@[simp]
lemma MvPowerSeries.rename_comp_toMvPowerSeries :
    (rename (R := R) f).comp (PowerSeries.toMvPowerSeries a)
      = PowerSeries.toMvPowerSeries (f a) := by
  ext
  simp [toMvPowerSeries_apply, comp_def]

@[simp]
lemma MvPowerSeries.rename_toMvPowerSeries :
    (p.toMvPowerSeries a).rename f = p.toMvPowerSeries (f a) :=
  DFunLike.congr_fun (rename_comp_toMvPowerSeries ..) p

end toMvPowerSeries
