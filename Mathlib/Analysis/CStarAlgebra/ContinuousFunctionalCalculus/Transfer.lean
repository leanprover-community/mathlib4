import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital

namespace StarAlgEquiv

variable {R A₁ A₂ A₃ A₁' A₂' A₃' : Type*}
  [CommSemiring R] [Semiring A₁] [Semiring A₂] [Semiring A₃]
  [Semiring A₁'] [Semiring A₂'] [Semiring A₃']
  [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]
  [Algebra R A₁'] [Algebra R A₂'] [Algebra R A₃']
  [Star A₁] [Star A₂] [Star A₃]
  [Star A₁'] [Star A₂'] [Star A₃']
  (e : A₁ ≃⋆ₐ[R] A₂)

/-- Reintrepret a star algebra equivalence as a star algebra homomorphism. -/
@[simps]
def toStarAlgHom : A₁ →⋆ₐ[R] A₂ where
  toFun := e
  map_add' := map_add e
  map_zero' := map_zero e
  map_mul' := map_mul e
  map_one' := map_one e
  commutes' := e.toAlgEquiv.commutes
  map_star' := map_star e

@[simp]
lemma toStarAlgHom_comp (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₂ : A₂ ≃⋆ₐ[R] A₃) :
    e₂.toStarAlgHom.comp e₁.toStarAlgHom = toStarAlgHom (e₁.trans e₂) := rfl

/-- If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'`, then the type of maps
`A₁ →ₐ[R] A₂` is equivalent to the type of maps `A₁' →ₐ[R] A₂'`. -/
@[simps apply]
def arrowCongr (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') : (A₁ →⋆ₐ[R] A₂) ≃ (A₁' →⋆ₐ[R] A₂') where
  toFun f := (e₂.toStarAlgHom.comp f).comp e₁.symm.toStarAlgHom
  invFun f := (e₂.symm.toStarAlgHom.comp f).comp e₁.toStarAlgHom
  left_inv f := by ext; simp
  right_inv f := by ext; simp

theorem arrowCongr_comp (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂')
    (e₃ : A₃ ≃⋆ₐ[R] A₃') (f : A₁ →⋆ₐ[R] A₂) (g : A₂ →⋆ₐ[R] A₃) :
    arrowCongr e₁ e₃ (g.comp f) = (arrowCongr e₂ e₃ g).comp (arrowCongr e₁ e₂ f) := by
  ext
  simp

@[simp]
theorem arrowCongr_refl : arrowCongr .refl .refl = Equiv.refl (A₁ →⋆ₐ[R] A₂) :=
  rfl

@[simp]
theorem arrowCongr_trans (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₁' : A₁' ≃⋆ₐ[R] A₂')
    (e₂ : A₂ ≃⋆ₐ[R] A₃) (e₂' : A₂' ≃⋆ₐ[R] A₃') :
    arrowCongr (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr e₁ e₁').trans (arrowCongr e₂ e₂') :=
  rfl

@[simp]
theorem arrowCongr_symm (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') :
    (arrowCongr e₁ e₂).symm = arrowCongr e₁.symm e₂.symm :=
  rfl

#check ContinuousFunctionalCalculus

variable {R A B : Type*} {p : A → Prop} {q : B → Prop}
  [CommSemiring R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
  [Ring A] [StarRing A] [TopologicalSpace A] [Algebra R A]
  [Ring B] [StarRing B] [TopologicalSpace B] [Algebra R B]
  [instCFC : ContinuousFunctionalCalculus R A p]

open ContinuousFunctionalCalculus in
example (e : A ≃⋆ₐ[R] B) (hpq : ∀ x, p x ↔ q (e x)) (he : Continuous e) :
    ContinuousFunctionalCalculus R B q where
  predicate_zero := map_zero e ▸ (hpq 0 |>.mp instCFC.predicate_zero)
  compactSpace_spectrum b := by
    rw [← isCompact_iff_compactSpace, ← e.apply_symm_apply b, AlgEquiv.spectrum_eq]
    exact isCompact_spectrum (e.symm b)
  spectrum_nonempty b hb := by
    rw [← e.apply_symm_apply b, AlgEquiv.spectrum_eq]
    have := e.nontrivial
    exact spectrum_nonempty (e.symm b) <| by simpa [hpq]
  exists_cfc_of_predicate b hb := by
    have ha : p (e.symm b) := by simpa [hpq]
    have hs : spectrum R b = spectrum R (e.symm b) := by rw [AlgEquiv.spectrum_eq]
    refine ⟨(Homeomorph.setCongr hs).compStarAlgEquiv' R R |>.arrowCongr e (cfcHom ha),
      ?hom_continuous, ?hom_injective, ?hom_id, ?hom_spectrum, ?hom_predicate⟩
    case hom_continuous =>
      exact (he.comp <| cfcHom_continuous ha).comp <| ContinuousMap.continuous_precomp _
    case hom_injective => sorry
    case hom_id => sorry
    case hom_spectrum => sorry
    case hom_predicate => sorry


#exit
#check NonUnitalContinuousFunctionalCalculus

variable (R : Type u_1) (A : Type u_2) (p : outParam (A → Prop))
  [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
  [NonUnitalRing A] [StarRing A] [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] : Prop
