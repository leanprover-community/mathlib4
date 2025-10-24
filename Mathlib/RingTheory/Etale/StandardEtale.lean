/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Etale.Basic

/-!

# Standard etale maps

# Main definitions
- `StandardEtalePair`:
  A pair `f g : R[X]` such that `f` is monic and `f'` is invertible in `R[X][1/g]`.
- `StandardEtalePair`: The standard etale algebra corresponding to a `StandardEtalePair`.
- `StandardEtalePair.equivPolynomialQuotient`   : `P.Ring ≃ R[X][Y]/⟨f, Yg-1⟩`
- `StandardEtalePair.equivAwayAdjoinRoot`       : `P.Ring ≃ (R[X]/f)[1/g]`
- `StandardEtalePair.equivAwayQuotient`         : `P.Ring ≃ R[X][1/g]/f`
- `StandardEtalePair.equivMvPolynomialQuotient` : `P.Ring ≃ R[X, Y]/⟨f, Yg-1⟩`
- `StandardEtalePair.homEquiv`:
  Maps out of `P.Ring` corresponds to `x` such that `f(x) = 0` and `g(x)` is invertible.
- We also provide the instance that `P.Ring` is etale over `R`.

-/

universe u

open Polynomial

noncomputable section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

variable (R) in
/-- A `StandardEtalePair R` is a pair `f g : R[X]` such that `f` is monic,
and `f'` is invertible in `R[X][1/g]`. -/
structure StandardEtalePair : Type _ where
  f : R[X]
  monic_f : f.Monic
  g : R[X]
  cond : ∃ p₁ p₂ n, derivative f * p₁ + f * p₂ = g ^ n

variable (P : StandardEtalePair R)

/-- The standard etale algebra `R[X][Y]/⟨f, Yg-1⟩` associated to a `StandardEtalePair R`.
Also see
`equivPolynomialQuotient   : P.Ring ≃ R[X][Y]/⟨f, Yg-1⟩`
`equivAwayAdjoinRoot       : P.Ring ≃ (R[X]/f)[1/g]`
`equivAwayQuotient         : P.Ring ≃ R[X][1/g]/f`
`equivMvPolynomialQuotient : P.Ring ≃ R[X, Y]/⟨f, Yg-1⟩` -/
protected def StandardEtalePair.Ring := R[X][X] ⧸ Ideal.span {C P.f, .X * C P.g - 1}
  deriving CommRing, Algebra R

namespace StandardEtalePair

/-- The `X` in the standard etale algebra `R[X][Y]/⟨f, Yg-1⟩`. -/
protected def X : P.Ring := Ideal.Quotient.mk _ (C .X)

/-- There is a map from a standard etale algebra `R[X][Y]/⟨f, Yg-1⟩` to `S` sending `X` to `x` iff
`f(x) = 0` and `g(x)` is invertible. Also see `StandardEtalePair.homEquiv`. -/
def HasMap (x : S) : Prop :=
  aeval x P.f = 0 ∧ IsUnit (aeval x P.g)

/-- The map `R[X][Y]/⟨f, Yg-1⟩ →ₐ[R] S` sending `X` to `x`, given `P.HasMap x`. -/
def lift (x : S) (h : P.HasMap x) : P.Ring →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (aevalAeval x ↑(h.2.unit⁻¹))
    (Ideal.span_le (I := RingHom.ker _).mpr (by simp [Set.pair_subset_iff, h.1]))

@[simp]
lemma lift_X (x : S) (h : P.HasMap x) : P.lift x h P.X = x := by
  simp [lift, StandardEtalePair.Ring, StandardEtalePair.X]

variable {P} in
lemma HasMap.map {x : S} (h : P.HasMap x) (f : S →ₐ[R] T) : P.HasMap (f x) :=
  ⟨by simp [aeval_algHom, h.1], by simpa [aeval_algHom] using h.2.map f⟩

lemma HasMap.isUnit_derivative_f {x : S} (h : P.HasMap x) :
    IsUnit (P.f.derivative.aeval x) := by
  obtain ⟨p₁, p₂, n, e⟩ := P.cond
  have : aeval x P.f.derivative ∣ aeval x P.g ^ n :=
    ⟨_, by simpa [h.1] using congr(aeval x $e.symm)⟩
  exact isUnit_of_dvd_unit this (.pow _ h.2)

lemma aeval_X_g_mul_mk_X : aeval P.X P.g * Ideal.Quotient.mk _ .X = 1 := by
  have : aeval (R := R) P.X = (Ideal.Quotient.mkₐ _ _).comp Polynomial.CAlgHom := by
    ext; simp [StandardEtalePair.Ring, StandardEtalePair.X]
  rw [this]
  dsimp [StandardEtalePair.Ring]
  rw [← map_mul, ← map_one (Ideal.Quotient.mk _), ← sub_eq_zero, ← map_sub, mul_comm]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))

variable {P} in
lemma hasMap_X : P.HasMap P.X :=
  have : aeval (R := R) P.X = (Ideal.Quotient.mkₐ _ _).comp Polynomial.CAlgHom := by
    ext; simp [StandardEtalePair.Ring, StandardEtalePair.X]
  ⟨this ▸ Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _)),
    isUnit_of_mul_eq_one _ _ P.aeval_X_g_mul_mk_X⟩

variable {P} in
@[ext]
lemma hom_ext {f g : P.Ring →ₐ[R] S} (H : f P.X = g P.X) : f = g := by
  have H : (f.comp (Ideal.Quotient.mkₐ R _)).comp CAlgHom =
    (g.comp (Ideal.Quotient.mkₐ R _)).comp CAlgHom := Polynomial.algHom_ext (by simpa)
  have H' : aeval (R := R) P.X = (Ideal.Quotient.mkₐ _ _).comp Polynomial.CAlgHom := by
    ext; simp [StandardEtalePair.Ring, StandardEtalePair.X]
  refine Ideal.Quotient.algHom_ext _ (Polynomial.algHom_ext' H ?_)
  change f.toMonoidHom (Ideal.Quotient.mk _ .X) = g.toMonoidHom (Ideal.Quotient.mk _ .X)
  rw [← show (↑P.hasMap_X.2.unit⁻¹ : P.Ring) = Ideal.Quotient.mk _ .X from
    Units.mul_eq_one_iff_inv_eq.mp P.aeval_X_g_mul_mk_X, ← Units.coe_map_inv, ← Units.coe_map_inv]
  congr 2
  ext
  simpa [H'] using congr($H _)

@[simp]
lemma lift_X_left : P.lift P.X P.hasMap_X = .id _ _ :=
  P.hom_ext (by simp)

lemma inv_aeval_X_g :
    (↑P.hasMap_X.2.unit⁻¹ : P.Ring) = Ideal.Quotient.mk _ .X :=
  Units.mul_eq_one_iff_inv_eq.mp P.aeval_X_g_mul_mk_X

/-- Maps out of `R[X][Y]/⟨f, Yg-1⟩` corresponds bijectively with
`x` such that `f(x) = 0` and `g(x)` is invertible. -/
@[simps]
def homEquiv : (P.Ring →ₐ[R] S) ≃ { x : S // P.HasMap x } where
  toFun f := ⟨f P.X, hasMap_X.map f⟩
  invFun x := P.lift x.1 x.2
  left_inv f := P.hom_ext (by simp)
  right_inv x := by simp

lemma existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot
    (I : Ideal S) (hI : I ^ 2 = ⊥) (x : S) (hx : P.HasMap (Ideal.Quotient.mk I x)) :
    ∃! ε, ε ∈ I ∧ P.HasMap (x + ε) := by
  have hf := Ideal.Quotient.eq_zero_iff_mem.mp
    ((aeval_algHom_apply (Ideal.Quotient.mkₐ R I) _ _).symm.trans hx.1)
  obtain ⟨⟨_, a, ha, -⟩, rfl⟩ := hx.2
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  simp_rw [← Ideal.Quotient.mkₐ_eq_mk R, aeval_algHom_apply, ← map_mul, ← map_one
    (Ideal.Quotient.mkₐ R I), Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at ha
  obtain ⟨p₁, p₂, n, e⟩ := P.cond
  apply_fun aeval x at e
  simp only [map_add, map_mul, map_pow] at e
  obtain ⟨ε, hεI, b, hb⟩ : ∃ ε ∈ I, ∃ b, aeval x (derivative P.f) * b = 1 + ε := by
    refine ⟨_, ?_, (a ^ n * aeval x p₁), sub_eq_iff_eq_add'.mp rfl⟩
    convert_to (aeval x P.g * a) ^ n - 1 - aeval x P.f * (a ^ n * aeval x p₂) ∈ I
    · linear_combination a ^ n * e
    · exact sub_mem (Ideal.mem_of_dvd _ (sub_one_dvd_pow_sub_one _ _) ha) (I.mul_mem_right _ hf)
  have : aeval x P.f ^ 2 = 0 := hI.le (Ideal.pow_mem_pow hf 2)
  have : aeval x P.f * ε = 0 := ((pow_two _).symm.trans hI).le (Ideal.mul_mem_mul hf hεI)
  refine ⟨aeval x P.f * -b, ⟨I.mul_mem_right _ hf, ?_, ?_⟩, ?_⟩
  · rw [Polynomial.aeval_add_of_sq_eq_zero _ _ _ (by grind)]; grind
  · rw [← IsNilpotent.isUnit_quotient_mk_iff (I := I) ⟨2, hI⟩, ← Ideal.Quotient.mkₐ_eq_mk R,
      ← aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, map_add,
      Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_right _ hf), add_zero]
    exact hx.2
  · rintro ε' ⟨hε'I, hε', hε''⟩
    rw [Polynomial.aeval_add_of_sq_eq_zero _ _ _ (hI.le (Ideal.pow_mem_pow hε'I 2))] at hε'
    have : ε * ε' = 0 := ((pow_two _).symm.trans hI).le (Ideal.mul_mem_mul hεI hε'I)
    grind

-- This works even if `f` is not monic. Generalize if we care.
instance : Algebra.FormallyEtale R P.Ring := by
  refine ⟨fun S _ _ I hI ↦ ?_⟩
  rw [← P.homEquiv.symm.bijective.of_comp_iff, ← P.homEquiv.bijective.of_comp_iff']
  suffices ∀ x, P.HasMap (Ideal.Quotient.mk I x) → ∃! a : { x : S // P.HasMap x }, a - x ∈ I by
    simpa [Function.bijective_iff_existsUnique, Ideal.Quotient.mk_surjective.forall,
      Subtype.ext_iff, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  intro x hx
  obtain ⟨ε, ⟨hεI, hε⟩, H⟩ := P.existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot I hI _ hx
  exact ⟨⟨x + ε, hε⟩, by simpa, fun y hy ↦
    Subtype.ext (sub_eq_iff_eq_add'.mp (H _ ⟨hy, by simpa using y.2⟩))⟩

/-- An `AlgEquiv` between `P.Ring` and `R[X][Y]/⟨f, Yg-1⟩`,
to not abuse the defeq between the two. -/
def equivPolynomialQuotient :
    P.Ring ≃ₐ[R] R[X][X] ⧸ Ideal.span {C P.f, .X * C P.g - 1} := .refl ..

/-- `R[X][Y]/⟨f, Yg-1⟩ ≃ (R[X]/f)[1/g]` -/
def equivAwayAdjoinRoot :
    P.Ring ≃ₐ[R] Localization.Away (AdjoinRoot.mk P.f P.g) := by
  refine .ofAlgHom (P.lift (algebraMap (AdjoinRoot P.f) _ (.root P.f)) ⟨?_, ?_⟩)
    (IsLocalization.liftAlgHom (M := .powers <| AdjoinRoot.mk P.f P.g)
      (f := AdjoinRoot.liftAlgHom _ _ P.X P.hasMap_X.1) <| Subtype.forall.mpr ?_) ?_ ?_
  · rw [aeval_algebraMap_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  · rw [aeval_algebraMap_apply, AdjoinRoot.aeval_eq]
    exact IsLocalization.Away.algebraMap_isUnit ..
  · change Submonoid.powers _ ≤ (IsUnit.submonoid _).comap _
    simpa [Submonoid.powers_le,  IsUnit.mem_submonoid_iff] using P.hasMap_X.2
  · ext; simp [Algebra.algHom]
  · ext; simp

/-- `R[X][Y]/⟨f, Yg-1⟩ ≃ R[X][1/g]/f` -/
def equivAwayQuotient :
    P.Ring ≃ₐ[R] Localization.Away P.g ⧸ Ideal.span {algebraMap _ (Localization.Away P.g) P.f} := by
  refine .ofAlgHom (P.lift (algebraMap R[X] _ .X) ⟨?_, ?_⟩)
    (Ideal.Quotient.liftₐ _ (IsLocalization.liftAlgHom (M := .powers <| P.g)
      (f := aeval P.X) <| Subtype.forall.mpr ?_) ?_)
      ?_ ?_
  · rw [aeval_algebraMap_apply, IsScalarTower.algebraMap_apply _ (Localization.Away P.g) (_ ⧸ _),
      Ideal.Quotient.algebraMap_eq, aeval_X_left_apply, Ideal.Quotient.mk_singleton_self]
  · rw [aeval_algebraMap_apply, IsScalarTower.algebraMap_apply _ (Localization.Away P.g) (_ ⧸ _),
      aeval_X_left_apply]
    exact (IsLocalization.Away.algebraMap_isUnit ..).map _
  · change Submonoid.powers _ ≤ (IsUnit.submonoid _).comap _
    simpa [Submonoid.powers_le,  IsUnit.mem_submonoid_iff] using P.hasMap_X.2
  · change Ideal.span _ ≤ RingHom.ker _
    simpa [Ideal.span_le] using P.hasMap_X.1
  · apply Ideal.Quotient.algHom_ext
    ext
    simp [Algebra.algHom, IsScalarTower.algebraMap_apply R[X] (Localization.Away P.g) (_ ⧸ _),
      -Ideal.Quotient.mk_algebraMap]
  · ext; simp [IsScalarTower.algebraMap_apply R[X] (Localization.Away P.g) (_ ⧸ _),
      -Ideal.Quotient.mk_algebraMap]

/-- `R[X][Y]/⟨f, Yg-1⟩ ≃ R[X, Y]/⟨f, Yg-1⟩` -/
def equivMvPolynomialQuotient :
    P.Ring ≃ₐ[R] MvPolynomial (Fin 2) R ⧸ Ideal.span
      {Bivariate.equivMvPolynomial R (C P.f), Bivariate.equivMvPolynomial R (.X * C P.g - 1)} :=
  Ideal.quotientEquivAlg _ _ (Bivariate.equivMvPolynomial R)
    (by simp only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]; rfl)

@[simp]
lemma equivMvPolynomialQuotient_symm_apply :
    P.equivMvPolynomialQuotient.symm (Ideal.Quotient.mk _ (.X 0)) = P.X := by
  simp [equivMvPolynomialQuotient, StandardEtalePair.Ring]; rfl

end StandardEtalePair
