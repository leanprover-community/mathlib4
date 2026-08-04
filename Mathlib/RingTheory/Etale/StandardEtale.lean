/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Ideal.IdempotentFG

/-!

# Standard etale maps

## Main definitions
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

- `Algebra.IsStandardEtale`: The class of standard etale algebras.

-/

@[expose] public section

universe u

open Polynomial

open scoped Bivariate

noncomputable section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

variable (R) in
/-- A `StandardEtalePair R` is a pair `f g : R[X]` such that `f` is monic,
and `f'` is invertible in `R[X][1/g]/f`. -/
structure StandardEtalePair : Type _ where
  /-- The monic polynomial to be quotiented out in a standard etale algebra. -/
  f : R[X]
  monic_f : f.Monic
  /-- The polynomial to be localized away from in a standard etale algebra. -/
  g : R[X]
  cond : ∃ p₁ p₂ n, derivative f * p₁ + f * p₂ = g ^ n

variable (P : StandardEtalePair R)

/-- The standard etale algebra `R[X][Y]/⟨f, Yg-1⟩` associated to a `StandardEtalePair R`.
Also see
`equivPolynomialQuotient   : P.Ring ≃ R[X][Y]/⟨f, Yg-1⟩`
`equivAwayAdjoinRoot       : P.Ring ≃ (R[X]/f)[1/g]`
`equivAwayQuotient         : P.Ring ≃ R[X][1/g]/f`
`equivMvPolynomialQuotient : P.Ring ≃ R[X, Y]/⟨f, Yg-1⟩` -/
protected def StandardEtalePair.Ring := R[X][Y] ⧸ Ideal.span {C P.f, Y * C P.g - 1}
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

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
lemma aeval_X_g_mul_mk_X : aeval P.X P.g * Ideal.Quotient.mk _ .X = 1 := by
  have : aeval (R := R) P.X = (Ideal.Quotient.mkₐ _ _).comp Polynomial.CAlgHom := by
    ext; simp [StandardEtalePair.Ring, StandardEtalePair.X]
  rw [this]
  dsimp [StandardEtalePair.Ring]
  rw [← map_mul, ← map_one (Ideal.Quotient.mk _), ← sub_eq_zero, ← map_sub, mul_comm]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))

set_option backward.isDefEq.respectTransparency false in
variable {P} in
lemma hasMap_X : P.HasMap P.X :=
  have : aeval (R := R) P.X = (Ideal.Quotient.mkₐ _ _).comp Polynomial.CAlgHom := by
    ext; simp [StandardEtalePair.Ring, StandardEtalePair.X]
  ⟨this ▸ Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _)),
    IsUnit.of_mul_eq_one _ P.aeval_X_g_mul_mk_X⟩

set_option backward.isDefEq.respectTransparency false in
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
  simpa [H'] using! congr($H _)

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
  refine Algebra.FormallyEtale.iff_comp_bijective.mpr fun S _ _ I hI ↦ ?_
  rw [← P.homEquiv.symm.bijective.of_comp_iff, ← P.homEquiv.bijective.of_comp_iff']
  suffices ∀ x, P.HasMap (Ideal.Quotient.mk I x) → ∃! a : { x : S // P.HasMap x }, a - x ∈ I by
    simpa [Function.bijective_iff_existsUnique, Ideal.Quotient.mk_surjective.forall,
      Subtype.ext_iff, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  intro x hx
  obtain ⟨ε, ⟨hεI, hε⟩, H⟩ := P.existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot I hI _ hx
  exact ⟨⟨x + ε, hε⟩, by simpa, fun y hy ↦
    Subtype.ext (sub_eq_iff_eq_add'.mp (H _ ⟨hy, by simpa using y.2⟩))⟩

instance : Algebra.Etale R P.Ring where
  finitePresentation := .quotient (Submodule.fg_span (by simp))

/-- An `AlgEquiv` between `P.Ring` and `R[X][Y]/⟨f, Yg-1⟩`,
to not abuse the defeq between the two. -/
def equivPolynomialQuotient :
    P.Ring ≃ₐ[R] R[X][Y] ⧸ Ideal.span {C P.f, Y * C P.g - 1} := .refl ..

set_option backward.isDefEq.respectTransparency.types false in
/-- `R[X][Y]/⟨f, Yg-1⟩ ≃ (R[X]/f)[1/g]` -/
def equivAwayAdjoinRoot :
    P.Ring ≃ₐ[R] Localization.Away (AdjoinRoot.mk P.f P.g) := by
  refine .ofAlgHom (P.lift (algebraMap (AdjoinRoot P.f) _ (.root P.f)) ⟨?_, ?_⟩)
    (IsLocalization.Away.liftAlgHom (AdjoinRoot.mk P.f P.g)
      (f := AdjoinRoot.liftAlgHom _ _ P.X P.hasMap_X.1) P.hasMap_X.2) ?_ ?_
  · rw [aeval_algebraMap_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  · rw [aeval_algebraMap_apply, AdjoinRoot.aeval_eq]
    exact IsLocalization.Away.algebraMap_isUnit ..
  · ext; simp [Algebra.algHom]
  · ext; simp

set_option backward.isDefEq.respectTransparency.types false in
/-- `R[X][Y]/⟨f, Yg-1⟩ ≃ R[X][1/g]/f` -/
def equivAwayQuotient :
    P.Ring ≃ₐ[R] Localization.Away P.g ⧸ Ideal.span {algebraMap _ (Localization.Away P.g) P.f} := by
  refine .ofAlgHom (P.lift (algebraMap R[X] _ .X) ⟨?_, ?_⟩)
    (Ideal.Quotient.liftₐ _ (IsLocalization.Away.liftAlgHom (P.g) P.hasMap_X.2) ?_) ?_ ?_
  · rw [aeval_algebraMap_apply, IsScalarTower.algebraMap_apply _ (Localization.Away P.g) (_ ⧸ _),
      Ideal.Quotient.algebraMap_eq, aeval_X_left_apply, Ideal.Quotient.mk_singleton_self]
  · rw [aeval_algebraMap_apply, IsScalarTower.algebraMap_apply _ (Localization.Away P.g) (_ ⧸ _),
      aeval_X_left_apply]
    exact (IsLocalization.Away.algebraMap_isUnit ..).map _
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

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma equivMvPolynomialQuotient_symm_apply :
    P.equivMvPolynomialQuotient.symm (Ideal.Quotient.mk _ (.X 0)) = P.X := by
  simp [equivMvPolynomialQuotient, StandardEtalePair.Ring]; rfl

/-- Mapping a standard etale pair under a ring homomorphism. -/
@[simps] protected noncomputable def map (f : R →+* S) : StandardEtalePair S where
  f := P.f.map f
  monic_f := P.monic_f.map _
  g := P.g.map f
  cond := by
    obtain ⟨p₁, p₂, n, e⟩ := P.cond
    refine ⟨p₁.map f, p₂.map f, n, ?_⟩
    simp [← Polynomial.map_mul, ← Polynomial.map_add, e]

lemma HasMap.map_algebraMap [Algebra S T] [IsScalarTower R S T] {x : T} (H : P.HasMap x) :
    (P.map (algebraMap R S)).HasMap x := by
  simpa [HasMap]

end StandardEtalePair

/-- An isomorphism to the standard etale algebra of a standard etale pair. -/
structure StandardEtalePresentation (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] extends
    P : StandardEtalePair R where
  /-- The image of X in a `StandardEtalePresentation`. -/
  x : S
  hasMap : P.HasMap x
  lift_bijective : Function.Bijective (P.lift x hasMap)

variable (P : StandardEtalePresentation R S)

/-- The isomorphism to the standard etale algebra given a `StandardEtalePresentation`. -/
def StandardEtalePresentation.equivRing : S ≃ₐ[R] P.Ring :=
  .symm <| .ofBijective _ P.lift_bijective

@[simp]
lemma StandardEtalePresentation.equivRing_symm_X : P.equivRing.symm P.X = P.x :=
  P.lift_X _ P.hasMap

@[simp]
lemma StandardEtalePresentation.equivRing_x : P.equivRing P.x = P.X :=
  (P.equivRing.symm_apply_eq.mp P.equivRing_symm_X).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The `Algebra.Presentation` associated to a standard etale presentation. -/
@[simps! relation val]
def StandardEtalePresentation.toPresentation : Algebra.Presentation R S (Fin 2) (Fin 2) where
  __ := Algebra.Generators.ofAlgHom ((P.lift _ P.hasMap).comp
      (P.equivMvPolynomialQuotient.symm.toAlgHom.comp (Ideal.Quotient.mkₐ _ _)))
    (P.lift_bijective.surjective.comp
      (P.equivMvPolynomialQuotient.symm.surjective.comp Ideal.Quotient.mk_surjective))
  relation := ![Bivariate.equivMvPolynomial R (C P.f),
    Bivariate.equivMvPolynomial R (.X * C P.g - 1)]
  span_range_relation_eq_ker := by
    rw [Algebra.Generators.ker_ofAlgHom, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      AlgHom.comp_toRingHom,
      RingHom.ker_comp_of_injective _ (by exact P.lift_bijective.injective),
      RingHom.ker_comp_of_injective _ (by exact P.equivMvPolynomialQuotient.symm.injective)]
    simp [Set.pair_comm]

set_option backward.isDefEq.respectTransparency.types false in
@[simp] lemma StandardEtalePresentation.aeval_val_equivMvPolynomial (p : R[X]) :
    MvPolynomial.aeval P.toPresentation.val
    (Bivariate.equivMvPolynomial R (.C p)) = p.aeval P.x := by
  change (((MvPolynomial.aeval _).comp (Bivariate.equivMvPolynomial R).toAlgHom).comp CAlgHom) _ = _
  congr 1
  ext
  simp

attribute [local simp] Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det
  Matrix.det_fin_two Algebra.PreSubmersivePresentation.jacobiMatrix_apply
  Polynomial.Bivariate.pderiv_zero_equivMvPolynomial
  Polynomial.Bivariate.pderiv_one_equivMvPolynomial

set_option backward.isDefEq.respectTransparency.types false in
/-- The `Algebra.SubmersivePresentation` associated to a standard etale presentation. -/
@[simps map toPreSubmersivePresentation_toPresentation]
def StandardEtalePresentation.toSubmersivePresentation :
    Algebra.SubmersivePresentation R S (Fin 2) (Fin 2) where
  __ := P.toPresentation
  map := id
  map_inj := Function.injective_id
  jacobian_isUnit := by simp [P.hasMap.2, P.hasMap.isUnit_derivative_f]

set_option backward.isDefEq.respectTransparency.types false in
lemma StandardEtalePresentation.toSubmersivePresentation_jacobian :
    P.toSubmersivePresentation.jacobian = aeval P.x P.f.derivative * aeval P.x P.g := by
  simp [StandardEtalePresentation.toSubmersivePresentation]

set_option backward.isDefEq.respectTransparency.types false in
lemma StandardEtalePresentation.exists_mul_aeval_x_g_pow_eq_aeval_x (x : S) :
    ∃ p : R[X], ∃ n, x * P.g.aeval P.x ^ n = p.aeval P.x := by
  obtain ⟨x, rfl⟩ := (P.equivRing.trans P.P.equivAwayAdjoinRoot).symm.surjective x
  obtain ⟨⟨p, ⟨_, n, rfl⟩⟩, e⟩ := IsLocalization.surj (.powers (AdjoinRoot.mk P.f P.g)) x
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective p
  refine ⟨p, n, P.equivRing.injective ?_⟩
  simpa [← aeval_algHom_apply, StandardEtalePair.equivAwayAdjoinRoot, ← aeval_def] using
    congr(P.equivAwayAdjoinRoot.symm $e)

set_option backward.isDefEq.respectTransparency.types false in
/-- Mapping `StandardEtalePresentation` under `AlgEquiv`s. -/
def StandardEtalePresentation.mapEquiv (e : S ≃ₐ[R] T) : StandardEtalePresentation R T where
  P := P.P
  x := e P.x
  hasMap := P.hasMap.map e.toAlgHom
  lift_bijective := (show P.lift (e P.x) (P.hasMap.map e.toAlgHom) = e.toAlgHom.comp
    (P.lift _ P.hasMap) from P.hom_ext (by simp)) ▸ e.bijective.comp P.lift_bijective

lemma StandardEtalePresentation.hom_ext {f₁ f₂ : S →ₐ[R] T} (h : f₁ P.x = f₂ P.x) : f₁ = f₂ := by
  have : f₁.comp P.equivRing.symm.toAlgHom = f₂.comp P.equivRing.symm.toAlgHom :=
    P.P.hom_ext (by simpa)
  ext x
  obtain ⟨x, rfl⟩ := P.equivRing.symm.surjective x
  exact congr($this x)

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency.types false in
/-- The base change of a standard etale algebra is standard etale. -/
noncomputable
def StandardEtalePresentation.baseChange :
    StandardEtalePresentation T (T ⊗[R] S) where
  __ := P.map (algebraMap R T)
  x := 1 ⊗ₜ P.x
  hasMap := (P.hasMap.map (Algebra.TensorProduct.includeRight (R := R) (A := T))).map_algebraMap
  lift_bijective := by
    algebraize [(algebraMap T (P.map (algebraMap R T)).Ring).comp (algebraMap R T)]
    have H : P.HasMap (P.map (algebraMap R T)).X := by
      simpa [StandardEtalePair.HasMap] using (P.map (algebraMap R T)).hasMap_X
    let f : T ⊗[R] S →ₐ[T] (P.map (algebraMap R T)).Ring :=
      Algebra.TensorProduct.lift (Algebra.ofId _ _) ((P.lift (P.map _).X H).comp P.equivRing)
        fun _ _ ↦ .all _ _
    let α : T ⊗[R] S ≃ₐ[T] (P.map (algebraMap R T)).Ring :=
      .ofAlgHom f ((P.map (algebraMap R T)).lift (1 ⊗ₜ[R] P.x)
        (P.hasMap.map (Algebra.TensorProduct.includeRight (R := R) (A := T))).map_algebraMap) (by
        ext; simp [f]) (by ext1; apply P.hom_ext; simp [f])
    exact α.symm.bijective

namespace Algebra

/-- The class of standard etale algebras,
defined to be the existence of a `StandardEtalePresentation`. -/
class IsStandardEtale (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] where
  nonempty_standardEtalePresentation : Nonempty (StandardEtalePresentation R S)

attribute [instance] IsStandardEtale.nonempty_standardEtalePresentation

instance (P : StandardEtalePair R) : IsStandardEtale R P.Ring :=
  ⟨⟨P, P.X, P.hasMap_X, by simpa [StandardEtalePair.lift_X_left] using Function.bijective_id⟩⟩

instance (priority := low) [IsStandardEtale R S] : Algebra.Etale R S :=
  .of_equiv IsStandardEtale.nonempty_standardEtalePresentation.some.equivRing.symm

lemma IsStandardEtale.of_equiv (e : S ≃ₐ[R] T) [IsStandardEtale R S] : IsStandardEtale R T :=
  ⟨⟨IsStandardEtale.nonempty_standardEtalePresentation.some.mapEquiv e⟩⟩

instance : IsStandardEtale R R :=
  ⟨⟨⟨⟨.X, by simp, 1, 1, 0, 0, by simp⟩, 0, ⟨by simp, by simp⟩, by
    set P : StandardEtalePair R := ⟨.X, by simp, 1, 1, 0, 0, by simp⟩
    have : P.X = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))
    let e := AlgEquiv.ofAlgHom (P.lift (0 : R) ⟨by simp [P], by simp [P]⟩) (Algebra.ofId _ _)
      (by ext) (by ext; simp [this])
    exact e.bijective⟩⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
lemma IsStandardEtale.of_isLocalizationAway [IsStandardEtale R S]
    {Sₛ : Type*} [CommRing Sₛ] [Algebra S Sₛ]
    [Algebra R Sₛ] [IsScalarTower R S Sₛ] (s : S) [IsLocalization.Away s Sₛ] :
    IsStandardEtale R Sₛ := by
  have P : StandardEtalePresentation R S := IsStandardEtale.nonempty_standardEtalePresentation.some
  obtain ⟨p, n, hp⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x s
  let P' : StandardEtalePair R := ⟨P.f, P.monic_f, p * P.g, have ⟨p₁, p₂, m, e⟩ := P.cond;
    ⟨p₁ * p ^ m, p₂ * p ^ m, m, by linear_combination e * p ^ m⟩⟩
  let S' := Localization.Away (AdjoinRoot.mk P.f P.g)
  let e : S ≃ₐ[R] S' := P.equivRing.trans P.P.equivAwayAdjoinRoot
  have := IsLocalization.Away.mul S' (Localization.Away (algebraMap _ S' (AdjoinRoot.mk P.f p)))
    (AdjoinRoot.mk P.f P.g) (.mk _ p)
  rw [← map_mul] at this
  have H : Submonoid.map e.symm.toRingEquiv.toMonoidHom (.powers
      (algebraMap _ S' (AdjoinRoot.mk P.f p))) = .powers (aeval P.x p) := by
    have : ((e.symm.toAlgHom.comp (IsScalarTower.toAlgHom R _ S')).comp (AdjoinRoot.mkₐ P.f)) =
      aeval P.x := by ext; simp [e, StandardEtalePair.equivAwayAdjoinRoot]
    rw [Submonoid.map_powers]
    exact congr(Submonoid.powers ($this p))
  have : IsLocalization.Away (aeval P.x p) Sₛ :=
    IsLocalization.Away.of_associated (r := s) ⟨(P.hasMap.2.pow n).unit, hp⟩
  let e₁ : P'.Ring ≃ₐ[R]
      Localization.Away (algebraMap _ S' (AdjoinRoot.mk P.f p)) :=
    P'.equivAwayAdjoinRoot.trans ((IsLocalization.algEquiv (.powers (AdjoinRoot.mk P.f (p * P.g)))
      (Localization.Away (AdjoinRoot.mk P.f (p * P.g))) _).restrictScalars R)
  let e₂ : Localization.Away (algebraMap _ S' (AdjoinRoot.mk P.f p)) ≃ₐ[R] Sₛ :=
    { __ := IsLocalization.ringEquivOfRingEquiv _ _ _ H,
      commutes' r := by
        simp [IsScalarTower.algebraMap_apply R S' (Localization.Away _),
          - AlgEquiv.symm_toRingEquiv, IsScalarTower.algebraMap_eq R S Sₛ] }
  exact .of_equiv (e₁.trans e₂)

/-- If `T` is an etale algebra, and a standard etale algebra surjects onto `T`, then
  `T` is also standard etale. -/
lemma IsStandardEtale.of_surjective
    [IsStandardEtale R S] [Algebra.Etale R T] (f : S →ₐ[R] T) (hf : Function.Surjective f) :
    IsStandardEtale R T := by
  let := f.toAlgebra
  obtain ⟨e, he, hfe⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg _ (Algebra.FinitePresentation.ker_fG_of_surjective f hf)).mp
      ((Algebra.FormallyEtale.iff_of_surjective hf).mp (.of_restrictScalars (R := R)))
  have := IsLocalization.away_of_isIdempotentElem he.one_sub (hfe.trans (by simp)) hf
  exact .of_isLocalizationAway (1 - e)

instance [Algebra.IsStandardEtale R S] :
    Algebra.IsStandardEtale T (T ⊗[R] S) :=
  ⟨⟨Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some.baseChange⟩⟩

end Algebra
