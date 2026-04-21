/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.MvPowerSeries.Rename

/-!
# Equivalences related to power series rings

This file establishes a number of equivalences related to power series rings and
is patterned after `Mathlib/Algebra/MvPolynomial/Equiv.lean`.

* `MvPowerSeries.isEmptyEquiv` : The isomorphism between multivariable power series
  in no variables and the ground ring.

* `MvPowerSeries.uniqueEquiv` : The isomorphism between multivariable power series
  in a single variable and power series over the ground ring.

* `MvPowerSeries.congrRingEquiv`, `MvPowerSeries.congrAlgEquiv` : The isomorhism between
  multivariable power series induced by an isomorphism between the coefficient rings.

* `MvPowerSeries.sumAlgEquiv` : The isomorphism between multivariable power series
  in a sum of two types, and multivariable power series in one of the types,
  with coefficients in multivariable power series in the other type.

* `MvPowerSeries.commAlgEquiv` : The isomorphism between multivariable power series
  in variables `σ` of multivariable power series in variables `τ` and multivariable power series
  in variables `τ` of multivariable power series in variables `σ`.

* `MvPowerSeries.optionEquivLeft` : The isomorphism between multivariable power series
  in `Option σ` and power series with coefficients in `MvPowerSeries σ R`.

* `MvPowerSeries.optionEquivRight` : The isomorphism between multivariable power series
  in `Option σ` and multivariable power series in `σ` with coefficients in `PowerSeries R`.

* `MvPowerSeries.finSuccEquiv` : The isomorphism between multivariable power series
  in `Fin (n + 1)` and power series over multivariable power series in `Fin n`.

* `MvPowerSeries.toAdicCompletionAlgEquiv` : the canonical isomorphism from
  multivariate power series to the adic completion of multivariate polynomials
  with respect to the ideal spanned by all variables when the index is finite.

# TODO

* Prove that the equivalences introduced in this file preserve the topologies
  on the rings of formal power series when the base ring is equipped with a topology
  (e.g., a linear topology).

-/

@[expose] public section

noncomputable section

namespace MvPowerSeries

variable {σ τ R S : Type*}

open Finsupp Function

section CommSemiring

variable [CommSemiring R]

section isEmptyEquiv

variable (σ R) in
/-- The isomorphism between multivariable power series in no variables and the ground ring. -/
@[simps!]
def isEmptyEquiv [IsEmpty σ] : MvPowerSeries σ R ≃ₐ[R] R where
  __ := constantCoeff
  invFun := C
  left_inv _ := by
    ext x; rw [Subsingleton.eq_zero x]
    simp
  commutes' _ := rfl

end isEmptyEquiv

section uniqueEquiv

variable (σ R) in
/-- The isomorphism between multivariable power series in a single variable and
power series over the ground ring. -/
abbrev uniqueEquiv [Unique σ] : MvPowerSeries σ R ≃ₐ[R] PowerSeries R :=
  renameEquiv R (Equiv.ofUnique σ Unit)

theorem coeff_uniqueEquiv [Unique σ] (p : MvPowerSeries σ R) (n : ℕ) :
    PowerSeries.coeff n (uniqueEquiv σ R p) = p.coeff (single default n) := by
  simp [PowerSeries.coeff, ← coeff_embDomain_rename (Equiv.ofUnique σ Unit).toEmbedding p]

lemma uniqueEquiv_X [Unique σ] : uniqueEquiv σ R (X default) = .X := by simp [PowerSeries.X]

lemma uniqueEquiv_C [Unique σ] (r : R) : uniqueEquiv σ R (C r) = .C r := by simp [PowerSeries.C]

end uniqueEquiv

section Map

variable [CommSemiring S] {f : R →+* S}

variable (σ) in
/-- If `e : A ≃+* B` is an isomorphism of rings, then so is `map e`. -/
@[simps apply]
def congrRingEquiv (e : R ≃+* S) : MvPowerSeries σ R ≃+* MvPowerSeries σ S where
  __ := map (e : R →+* S)
  invFun := map (e.symm : S →+* R)
  left_inv := map_leftInverse e.left_inv
  right_inv := map_rightInverse e.right_inv

@[simp]
theorem congrRingEquiv_refl : congrRingEquiv σ (RingEquiv.refl R) = RingEquiv.refl _ :=
  RingEquiv.ext (by simp)

@[simp]
theorem congrRingEquiv_symm (e : R ≃+* S) : (congrRingEquiv σ e).symm = congrRingEquiv σ e.symm :=
  rfl

@[simp]
theorem congrRingEquiv_trans {S' : Type*} [CommSemiring S'] (e : R ≃+* S) (f : S ≃+* S') :
    (congrRingEquiv σ e).trans (congrRingEquiv σ f) = congrRingEquiv σ (e.trans f) :=
  RingEquiv.ext fun p => by simp

variable {A₁ A₂ A₃ : Type*} [CommSemiring A₁] [CommSemiring A₂] [CommSemiring A₃]
variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]

variable (σ) in
/-- If `e : A ≃ₐ[R] B` is an isomorphism of `R`-algebras, then so is `map e`. -/
@[simps apply]
def congrAlgEquiv (e : A₁ ≃ₐ[R] A₂) : MvPowerSeries σ A₁ ≃ₐ[R] MvPowerSeries σ A₂ := {
  mapAlgHom (e : A₁ →ₐ[R] A₂), congrRingEquiv σ (e : A₁ ≃+* A₂) with toFun := map (e : A₁ →+* A₂) }

@[simp]
theorem congrAlgEquiv_refl : congrAlgEquiv σ (AlgEquiv.refl : A₁ ≃ₐ[R] A₁) = AlgEquiv.refl :=
  AlgEquiv.ext (by simp)

@[simp]
theorem congrAlgEquiv_symm (e : A₁ ≃ₐ[R] A₂) : (congrAlgEquiv σ e).symm = congrAlgEquiv σ e.symm :=
  rfl

@[simp]
theorem congrAlgEquiv_trans (e : A₁ ≃ₐ[R] A₂) (f : A₂ ≃ₐ[R] A₃) :
    (congrAlgEquiv σ e).trans (congrAlgEquiv σ f) = congrAlgEquiv σ (e.trans f) := by
  ext; simp

end Map

section sum

variable (R σ τ) in
/-- Implementation detail for `sumToIter`. Use `MvPowerSeries.sumToIter` instead. -/
def sumToIterFun (p : MvPowerSeries (σ ⊕ τ) R) :
    MvPowerSeries σ (MvPowerSeries τ R) := fun x ↦ fun y ↦ coeff (x.sumElim y) p

private lemma coeff_sumToIterFun (x : σ →₀ ℕ) (y : τ →₀ ℕ) (p : MvPowerSeries (σ ⊕ τ) R) :
    coeff y (coeff x (sumToIterFun σ τ R p)) = coeff (x.sumElim y) p := rfl

private lemma sumToIterFun_monomial (x : σ ⊕ τ →₀ ℕ) (r : R) :
    sumToIterFun σ τ R (monomial x r) = monomial (comapDomain Sum.inl x Sum.inl_injective.injOn)
      ((monomial (comapDomain Sum.inr x Sum.inr_injective.injOn)) r) := by
  classical
  ext y z
  simp only [coeff_sumToIterFun, coeff_monomial, Finsupp.ext_iff, coe_sumElim, Sum.forall,
    Sum.elim_inl, Sum.elim_inr, comapDomain_apply]
  split_ifs
  · rw [coeff_monomial, if_pos (by ext; grind [comapDomain_apply])]
  · grind
  · rw [coeff_monomial, if_neg (by simp [Finsupp.ext_iff]; grind)]
  · simp

open Finset in
private lemma sumToIterFun_mul (p q) : sumToIterFun σ τ R (p * q) =
    sumToIterFun σ τ R p * sumToIterFun σ τ R q := by
  classical
  ext x y
  simp only [coeff_sumToIterFun, coeff_mul, map_sum, ← sum_product']
  rw [← image_sumElim_product_antidiagonal, sum_image
    (LeftInverse.injective (g := fun (x, y) ↦ ((x.comapDomain Sum.inl Sum.inl_injective.injOn,
    y.comapDomain Sum.inl Sum.inl_injective.injOn), x.comapDomain Sum.inr Sum.inr_injective.injOn,
    y.comapDomain Sum.inr Sum.inr_injective.injOn)) (fun _ ↦ by simp)).injOn]

variable (R σ τ) in
/-- The map from multivariable power series in the sum of the two types to
multivariable power peries in one type with coefficients in
multivariable power series in another type.

See `sumToIterEquiv` for the isomorphism. -/
@[no_expose]
def sumToIter : MvPowerSeries (σ ⊕ τ) R →ₐ[R] MvPowerSeries σ (MvPowerSeries τ R) where
  toFun := sumToIterFun σ τ R
  map_one' := by simpa using sumToIterFun_monomial (0 : σ ⊕ τ →₀ ℕ) (1 : R)
  map_mul' := sumToIterFun_mul
  map_zero' := by ext; simp [coeff_sumToIterFun]
  map_add' _ _ := by ext; simp [coeff_sumToIterFun]
  commutes' := by simpa [MvPowerSeries.algebraMap_apply] using sumToIterFun_monomial 0

lemma coeff_sumToIter (x : σ →₀ ℕ) (y : τ →₀ ℕ) (p : MvPowerSeries (σ ⊕ τ) R) :
    coeff y (coeff x (sumToIter σ τ R p)) = coeff (x.sumElim y) p := by rfl

theorem sumToIter_monomial (x : σ ⊕ τ →₀ ℕ) (r : R) :
    sumToIter σ τ R (monomial x r) = monomial (comapDomain Sum.inl x Sum.inl_injective.injOn)
      ((monomial (comapDomain Sum.inr x Sum.inr_injective.injOn)) r) := sumToIterFun_monomial ..

@[simp]
theorem sumToIter_C (r : R) : sumToIter σ τ R (C r) = C (C r) := by
  simpa using sumToIter_monomial 0 r

@[simp]
theorem sumToIter_Xl (b : σ) : sumToIter σ τ R (X (Sum.inl b)) = X b := by
  simpa [X_def] using sumToIter_monomial ((single b 1).sumElim (0 : τ →₀ ℕ)) (1 : R)

@[simp]
theorem sumToIter_Xr (b : τ) : sumToIter σ τ R (X (Sum.inr b)) = C (X b) := by
  simpa [X_def] using sumToIter_monomial ((0 : σ →₀ ℕ).sumElim (single b 1)) 1

variable (R σ τ) in
/-- An inverse function of `sumToIter`. -/
def iterToSumFun (p : MvPowerSeries σ (MvPowerSeries τ R)) :
    MvPowerSeries (σ ⊕ τ) R := fun x ↦ coeff (comapDomain Sum.inr x Sum.inr_injective.injOn)
  (coeff (comapDomain Sum.inl x Sum.inl_injective.injOn) p)

private lemma coeff_iterToSumFun (p : MvPowerSeries σ (MvPowerSeries τ R)) (x : σ ⊕ τ →₀ ℕ) :
    coeff x (iterToSumFun σ τ R p) = coeff (comapDomain Sum.inr x Sum.inr_injective.injOn)
      (coeff (comapDomain Sum.inl x Sum.inl_injective.injOn) p) := rfl

variable (R σ τ) in
/-- The isomorphism between multivariable power series in a sum of two types,
and multivariable power series in one of the types,
with coefficients in multivariable power series in the other type. -/
@[simps! apply]
def sumAlgEquiv : MvPowerSeries (σ ⊕ τ) R ≃ₐ[R] MvPowerSeries σ (MvPowerSeries τ R) where
  __ := sumToIter σ τ R
  invFun := iterToSumFun σ τ R
  left_inv _ := by
    ext; simp [coeff_iterToSumFun, coeff_sumToIter, comapDomain_sumElim_comapDomain]
  right_inv _ := by
    ext; simp [coeff_sumToIter, coeff_iterToSumFun, comapDomain_inr_sumElim,
      comapDomain_inl_sumElim]

theorem coeff_sumAlgEquiv_symm_apply (p : MvPowerSeries σ (MvPowerSeries τ R)) (x : σ ⊕ τ →₀ ℕ) :
    coeff x ((sumAlgEquiv σ τ R).symm p) = coeff (comapDomain Sum.inr x Sum.inr_injective.injOn)
      (coeff (comapDomain Sum.inl x Sum.inl_injective.injOn) p) := coeff_iterToSumFun ..

@[simp]
theorem sumAlgEquiv_symm_C_C (a : R) : (sumAlgEquiv σ τ R).symm (C (C a)) = C a := by
  simp [AlgEquiv.symm_apply_eq]

@[simp]
theorem sumAlgEquiv_symm_X (b : σ) : (sumAlgEquiv σ τ R).symm (X b) = X (Sum.inl b) := by
  simp [AlgEquiv.symm_apply_eq]

@[simp]
theorem sumAlgEquiv_symm_C_X (c : τ) : (sumAlgEquiv σ τ R).symm (C (X c)) = X (Sum.inr c) := by
  simp [AlgEquiv.symm_apply_eq]

theorem sumAlgEquiv_comp_rename_inr : (sumAlgEquiv σ τ R).toAlgHom.comp
    (rename Embedding.inr) = IsScalarTower.toAlgHom R (MvPowerSeries τ R)
      (MvPowerSeries σ (MvPowerSeries τ R)) := by
  classical
  ext _ x y
  simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, AlgHom.coe_coe, comp_apply,
    sumAlgEquiv_apply, coeff_sumToIter, IsScalarTower.coe_toAlgHom', algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, coeff_C]
  split_ifs with h
  · simp [h, ← embDomain_inr]
  · replace h : x.sumElim y ∉ Set.range (mapDomain Embedding.inr) := by
      rw [mem_range_mapDomain_iff _ (Embedding.injective _)]
      revert h; simp [Finsupp.ext_iff]
    rw [coeff_rename_eq_zero _ _ h, map_zero]

theorem sumAlgEquiv_comp_rename_inl : (sumAlgEquiv σ τ R).toAlgHom.comp
    (rename Embedding.inl) = mapAlgHom (Algebra.ofId ..) := by
  classical
  ext p x y
  simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, AlgHom.coe_coe, comp_apply,
    sumAlgEquiv_apply, coeff_sumToIter,
    show (coeff x) ((mapAlgHom (Algebra.ofId R (MvPowerSeries τ R))) p) = C (coeff x p) from rfl]
  by_cases h : y = 0
  · simp [h, ← embDomain_inl]
  · have : x.sumElim y ∉ Set.range (mapDomain Embedding.inl) := by
      rw [mem_range_mapDomain_iff _ (Embedding.injective _)]
      revert h; simp [Finsupp.ext_iff]
    rw [coeff_rename_eq_zero _ _ this, coeff_C, if_neg h]

variable (R σ τ) in
/-- The algebra isomorphism between multivariable power series in variables `σ` of multivariable
power series in variables `τ` and multivariable power series in variables `τ` of multivariable
power series in variables `σ`. -/
def commAlgEquiv :
    MvPowerSeries σ (MvPowerSeries τ R) ≃ₐ[R] MvPowerSeries τ (MvPowerSeries σ R) :=
  (sumAlgEquiv σ τ R).symm.trans <| (renameEquiv _ (.sumComm σ τ)).trans (sumAlgEquiv τ σ R)

@[simp]
lemma commAlgEquiv_C (p : MvPowerSeries τ R) : commAlgEquiv σ τ R (C p) = map C p := by
  classical
  ext y x
  simp only [commAlgEquiv, AlgEquiv.trans_apply, renameEquiv_apply,
    AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_toMonoidHom,
    OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe, sumAlgEquiv_apply,
    coeff_sumToIter, coeff_map, coeff_C]
  by_cases h : y.sumElim x ∈ Set.range (mapDomain (Equiv.sumComm σ τ).toEmbedding)
  · rw [← funext_iff.mpr (embDomain_eq_mapDomain _)] at h
    rcases h with ⟨z, hz⟩
    simp_rw [← hz, ← Equiv.coe_toEmbedding, coeff_embDomain_rename, coeff_sumAlgEquiv_symm_apply]
    rw [embDomain_eq_mapDomain, Equiv.coe_toEmbedding, Equiv.sumComm_apply,
      ← mapDomain_swap_sumElim (M := ℕ), (mapDomain_injective
        Sum.swap_leftInverse.injective).eq_iff] at hz
    rw [hz, comapDomain_inr_sumElim, comapDomain_inl_sumElim, coeff_C]
    split <;> simp
  · simp_rw [← Equiv.coe_toEmbedding, coeff_rename_eq_zero _ _ h]
    rw [mem_range_mapDomain_iff _ (Embedding.injective _)] at h
    simp at h

@[simp]
lemma commAlgEquiv_X (i : σ) : commAlgEquiv σ τ R (X i) = C (X i) := by
  simp [commAlgEquiv]

end sum

section optionEquivLeft

private lemma embDomain_finSuccEquiv_cons {M : Type*} [AddCommMonoid M] {n : ℕ} (i : M)
    (x : Fin n →₀ M) : embDomain (finSuccEquiv n).toEmbedding (cons i x) = optionElim i x := by
  ext a; cases a <;> simp [embDomain_eq_mapDomain]

open Finset in
private theorem image_optionElim_product_antidiagonal [DecidableEq σ]
    {x : σ →₀ ℕ} {n : ℕ} : image (fun ((x, y), z, w) ↦
      (z.optionElim x, w.optionElim y)) (antidiagonal n ×ˢ antidiagonal x) =
    antidiagonal (x.optionElim n) := by
  symm; ext ⟨u, v⟩
  simp only [mem_antidiagonal, mem_image, mem_product, Prod.mk.injEq, Prod.exists]
  refine ⟨fun h ↦ ⟨u none, v none, u.some, v.some, ⟨?_, ?_⟩, by simp⟩,
    fun ⟨a, b, i, j, h1, h2, h3⟩ ↦ ?_⟩
  · rw [← add_apply, h, optionElim_apply_none]
  · rw [← some_add, h, some_optionElim]
  · rw [← h2, ← h3, ← optionElim_add, h1.left, h1.right]

variable (R σ) in
/-- Implementation detail for `optionEquivLeft`. Use `MvPowerSeries.optionEquivLeft` instead. -/
def optionFunLeft (p : MvPowerSeries (Option σ) R) : PowerSeries (MvPowerSeries σ R) :=
  .mk fun n ↦ fun x ↦ p.coeff (x.optionElim n)

private lemma coeff_coeff_optionFunLeft (p : MvPowerSeries (Option σ) R) (n : ℕ) (x : σ →₀ ℕ) :
    coeff x (PowerSeries.coeff n (optionFunLeft σ R p)) = coeff (x.optionElim n) p := by
  rw [optionFunLeft, PowerSeries.coeff_mk]
  rfl

private theorem optionFunLeft_monomial (x : Option σ →₀ ℕ) (r : R) :
    optionFunLeft σ R (monomial x r) = PowerSeries.monomial (x none) (monomial x.some r) := by
  classical
  ext1 n; rw [PowerSeries.coeff_monomial]
  split_ifs with h
  · ext y; rw [h, coeff_coeff_optionFunLeft, coeff_monomial]
    split_ifs with h'
    · rw [← h']; simp
    refine (coeff_monomial_ne ?_ _).symm
    intro h''; simp [h''] at h'
  · ext y; rw [coeff_coeff_optionFunLeft, map_zero]
    exact coeff_monomial_ne (by simpa [Finsupp.ext_iff] using ⟨none, by simpa⟩) r

open Finset in
private lemma optionFunLeft_mul (p q : MvPowerSeries (Option σ) R) :
    optionFunLeft σ R (p * q) = optionFunLeft σ R p * optionFunLeft σ R q := by
  classical
  ext
  simpa [coeff_coeff_optionFunLeft, coeff_mul, PowerSeries.coeff_mul, map_sum, ← sum_product',
    ← image_optionElim_product_antidiagonal] using sum_image (LeftInverse.injective
      (g := fun (x, y) ↦ ((x none, y none), x.some, y.some)) (fun _ ↦ by simp)).injOn

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
    simpa [MvPowerSeries.algebraMap_apply, PowerSeries.algebraMap_apply] using
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

section optionEquivRight

variable (R σ) in
/-- Implementation detail for `optionEquivRight`. Use `MvPowerSeries.optionEquivRight` instead. -/
def optionFunRight (p : MvPowerSeries (Option σ) R) : MvPowerSeries σ (PowerSeries R) :=
  fun x ↦ .mk fun n ↦ p.coeff (x.optionElim n)

set_option backward.isDefEq.respectTransparency false in
private theorem coeff_coeff_optionFunRight (p : MvPowerSeries (Option σ) R) (x : σ →₀ ℕ) (n : ℕ) :
    ((optionFunRight σ R p).coeff x).coeff n = p.coeff (x.optionElim n) := by
  simp [PowerSeries.coeff, coeff, LinearMap.proj, optionFunRight, PowerSeries.mk]

private theorem optionFunRight_monomial (x : Option σ →₀ ℕ) (r : R) :
    optionFunRight σ R (monomial x r) = monomial x.some (PowerSeries.monomial (x none) r) := by
  classical
  ext y n
  rw [coeff_coeff_optionFunRight, coeff_monomial, coeff_monomial]
  split_ifs with h h' h''
  · rw [PowerSeries.coeff_monomial, eq_comm, ite_eq_left_iff]
    suffices h : n = x none by simp [h]
    simpa using DFunLike.congr_fun h none
  · exfalso; revert h'; rw [imp_false, not_not]
    ext i; rw [← optionElim_apply_some n, h, some_apply]
  · rw [PowerSeries.coeff_monomial, eq_comm, ite_eq_right_iff]
    intro h'; exfalso; revert h
    simp [h', h'']
  · simp

open Finset in
private lemma optionFunRight_mul (p q : MvPowerSeries (Option σ) R) :
    optionFunRight σ R (p * q) = optionFunRight σ R p * optionFunRight σ R q := by
  classical
  ext
  simpa [coeff_coeff_optionFunRight, coeff_mul, ← image_optionElim_product_antidiagonal,
    map_sum, PowerSeries.coeff_mul, ← sum_product_right'] using sum_image (LeftInverse.injective
      (g := fun (x, y) ↦ ((x none, y none), x.some, y.some)) (fun _ ↦ by simp)).injOn

variable (R σ) in
/-- An inverse function of `optionFunRight`. -/
def optionInvFunRight (p : MvPowerSeries σ (PowerSeries R)) : MvPowerSeries (Option σ) R :=
  fun x ↦ (p.coeff x.some).coeff (x none)

lemma coeff_optionInvFunRight (p : MvPowerSeries σ (PowerSeries R)) (x : Option σ →₀ ℕ) :
    coeff x (optionInvFunRight σ R p) = (p.coeff x.some).coeff (x none) := rfl

variable (R σ) in
/-- The algebra isomorphism between multivariable power series in `Option σ` and
  multivariable power series in `σ` with coefficients in `PowerSeries R`. -/
@[no_expose]
def optionEquivRight : MvPowerSeries (Option σ) R ≃ₐ[R] MvPowerSeries σ (PowerSeries R) where
  toFun := optionFunRight σ R
  invFun := optionInvFunRight σ R
  left_inv _ := by ext; simp [coeff_optionInvFunRight, coeff_coeff_optionFunRight]
  right_inv _ := by ext; simp [coeff_optionInvFunRight, coeff_coeff_optionFunRight]
  map_mul' := optionFunRight_mul
  map_add' _ _ := by ext; simp [coeff_coeff_optionFunRight]
  commutes' := by simpa [MvPowerSeries.algebraMap_apply] using optionFunRight_monomial 0

theorem coeff_coeff_optionEquivRight (p : MvPowerSeries (Option σ) R) (x : σ →₀ ℕ) (n : ℕ) :
    ((optionEquivRight σ R p).coeff x).coeff n = p.coeff (x.optionElim n) :=
  coeff_coeff_optionFunRight p x n

theorem optionEquivRight_monomial (x : Option σ →₀ ℕ) (r : R) :
    optionEquivRight σ R (monomial x r) = monomial x.some (PowerSeries.monomial (x none) r) :=
  optionFunRight_monomial x r

lemma optionEquivRight_X_some (i : σ) : optionEquivRight σ R (X (some i)) = X i := by
  simpa [← X_def] using optionEquivRight_monomial (single (some i) 1) (1 : R)

lemma optionEquivRight_X_none : optionEquivRight σ R (X none) = C PowerSeries.X := by
  simpa [← X_def] using optionEquivRight_monomial (single none 1) (1 : R)

lemma optionEquivRight_C (r : R) : optionEquivRight σ R (C r) = C (PowerSeries.C r) := by
  simpa using optionEquivRight_monomial 0 (r : R)

end optionEquivRight

section finSuccEquiv

variable {n : ℕ}

variable (n R) in
/-- The algebra isomorphism between multivariable power series in `Fin (n + 1)` and
power series over multivariable power series in `Fin n`. -/
def finSuccEquiv : MvPowerSeries (Fin (n + 1)) R ≃ₐ[R] PowerSeries (MvPowerSeries (Fin n) R) :=
  (renameEquiv R (_root_.finSuccEquiv n)).trans (optionEquivLeft (Fin n) R)

theorem coeff_coeff_finSuccEquiv (p : MvPowerSeries (Fin (n + 1)) R) {k x} :
    coeff x (PowerSeries.coeff k (finSuccEquiv R n p)) = coeff (x.cons k) p := by
  suffices (coeff x) ((PowerSeries.coeff k) ((optionEquivLeft (Fin n) R)
    ((rename (_root_.finSuccEquiv n)) p))) = (coeff (Finsupp.cons k x)) p by simpa [finSuccEquiv]
  simp_rw [← Equiv.coe_toEmbedding, coeff_coeff_optionEquivLeft,
    ← embDomain_finSuccEquiv_cons, coeff_embDomain_rename]

theorem finSuccEquiv_X_zero : finSuccEquiv R n (X 0) = .X := by
  ext k x
  rw [coeff_coeff_finSuccEquiv, PowerSeries.coeff_X, coeff_X]
  split_ifs with h1 h2 h3
  · rw [cons_eq_single_zero_iff] at h1
    simp [h1.left]
  · grind [cons_eq_single_zero_iff]
  · rw [cons_eq_single_zero_iff, not_and'] at h1
    rw [coeff_one, if_neg (h1 h3)]
  · rw [coeff_zero]

theorem finSuccEquiv_X_succ {j : Fin n} : finSuccEquiv R n (X j.succ) = .C (X j) := by
  ext k x
  rw [coeff_coeff_finSuccEquiv, PowerSeries.coeff_C, coeff_X]
  split_ifs with h1 h2 h3
  · rw [cons_eq_single_succ_iff] at h1
    simp [h1.left]
  · grind [cons_eq_single_succ_iff]
  · rw [cons_eq_single_succ_iff, not_and'] at h1
    rw [coeff_X, if_neg (h1 h3)]
  · rw [coeff_zero]

theorem finSuccEquiv_comp_C : (MvPowerSeries.finSuccEquiv R n).symm.toRingHom.comp
    (PowerSeries.C.comp MvPowerSeries.C) = MvPowerSeries.C := RingHom.ext fun r ↦ by
  classical
  rw [AlgEquiv.symm_toRingEquiv, RingEquiv.toRingHom_eq_coe, RingHom.coe_comp,
    RingHom.coe_coe, comp_apply, RingEquiv.symm_apply_eq]
  ext; simp only [RingHom.coe_comp, comp_apply, PowerSeries.coeff_C,
    AlgEquiv.coe_ringEquiv, coeff_coeff_finSuccEquiv, coeff_C]
  rw [← single_zero 0]
  grind [coeff_C, cons_eq_single_zero_iff]

/-- Consider a multivariate power series `p` whose variables are indexed by `Option σ`,
and suppose that `σ ≃ Fin n`.
Then one may view `p` as a power series over `MvPowerSeries (Fin n) R`, by

1. renaming the variables via `Option σ ≃ Fin (n+1)`, and then singling out the `0`-th variable
    via `MvPowerSeries.finSuccEquiv`;
2. first viewing it as power series over `MvPowerSeries σ R` via `MvPowerSeries.optionEquivLeft`,
    and then renaming the variables.

This lemma shows that both constructions are the same. -/
lemma finSuccEquiv_renameEquiv_finSuccEquiv (e : σ ≃ Fin n) (p) :
    (renameEquiv R ((Equiv.optionCongr e).trans (_root_.finSuccEquiv n).symm)).trans
      (finSuccEquiv R n) p = PowerSeries.map (rename e).toRingHom
        (optionEquivLeft σ R p) := by
  ext k x
  simp only [AlgEquiv.trans_apply, renameEquiv_apply, Equiv.coe_trans, AlgHom.toRingHom_eq_coe,
    RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_toMonoidHom, OneHom.toFun_eq_coe,
    MonoidHom.toOneHom_coe, MonoidHom.coe_coe, PowerSeries.coeff_map, RingHom.coe_coe]
  have aux : x.cons k = embDomain (e.optionCongr.toEmbedding.trans
    (_root_.finSuccEquiv n).symm.toEmbedding) ((x.mapDomain e.symm).optionElim k) := by
    rw [embDomain_eq_mapDomain, ← Equiv.trans_toEmbedding, Equiv.coe_toEmbedding,
      ← equivMapDomain_eq_mapDomain, ← equivCongrLeft_apply, eq_comm,
      Equiv.apply_eq_iff_eq_symm_apply]
    ext a; cases a <;> simp
  have aux' : x = embDomain e.toEmbedding (x.mapDomain e.symm) := by
    rw [embDomain_eq_mapDomain, Equiv.coe_toEmbedding, ← mapDomain_comp,
      Equiv.self_comp_symm, mapDomain_id]
  simp_rw [coeff_coeff_finSuccEquiv, aux, ← Equiv.coe_toEmbedding, ← Embedding.coe_trans,
    ← Equiv.trans_toEmbedding, coeff_embDomain_rename]
  nth_rw 2 [aux']
  rw [coeff_embDomain_rename, ← coeff_coeff_optionEquivLeft, Equiv.coe_toEmbedding]

end finSuccEquiv

end CommSemiring

section CommRing

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

end CommRing

end MvPowerSeries
