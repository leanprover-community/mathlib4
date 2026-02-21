import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital

namespace StarAlgEquiv

section NonUnital

variable {R A₁ A₂ A₃ A₁' A₂' A₃' : Type*} [Monoid R]
  [NonUnitalNonAssocSemiring A₁] [DistribMulAction R A₁] [Star A₁]
  [NonUnitalNonAssocSemiring A₂] [DistribMulAction R A₂] [Star A₂]
  [NonUnitalNonAssocSemiring A₃] [DistribMulAction R A₃] [Star A₃]
  [NonUnitalNonAssocSemiring A₁'] [DistribMulAction R A₁'] [Star A₁']
  [NonUnitalNonAssocSemiring A₂'] [DistribMulAction R A₂'] [Star A₂']
  [NonUnitalNonAssocSemiring A₃'] [DistribMulAction R A₃'] [Star A₃']
  (e : A₁ ≃⋆ₐ[R] A₂)

/-- Reintrepret a star algebra equivalence as a non-unital star algebra homomorphism. -/
@[simps]
def toNonUnitalStarAlgHom : A₁ →⋆ₙₐ[R] A₂ where
  toFun := e
  map_add' := map_add e
  map_zero' := map_zero e
  map_mul' := map_mul e
  map_smul' := map_smul e
  map_star' := map_star e

@[simp]
lemma toNonUnitalStarAlgHom_comp (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₂ : A₂ ≃⋆ₐ[R] A₃) :
    e₂.toNonUnitalStarAlgHom.comp e₁.toNonUnitalStarAlgHom =
      (e₁.trans e₂).toNonUnitalStarAlgHom := rfl

/-- If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'`, then the type of maps
`A₁ →ₐ[R] A₂` is equivalent to the type of maps `A₁' →ₐ[R] A₂'`. -/
@[simps apply]
def arrowCongr' (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') :
    (A₁ →⋆ₙₐ[R] A₂) ≃ (A₁' →⋆ₙₐ[R] A₂') where
  toFun f := (e₂.toNonUnitalStarAlgHom.comp f).comp e₁.symm.toNonUnitalStarAlgHom
  invFun f := (e₂.symm.toNonUnitalStarAlgHom.comp f).comp e₁.toNonUnitalStarAlgHom
  left_inv f := by ext; simp
  right_inv f := by ext; simp

theorem arrowCongr'_comp (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂')
    (e₃ : A₃ ≃⋆ₐ[R] A₃') (f : A₁ →⋆ₙₐ[R] A₂) (g : A₂ →⋆ₙₐ[R] A₃) :
    arrowCongr' e₁ e₃ (g.comp f) = (arrowCongr' e₂ e₃ g).comp (arrowCongr' e₁ e₂ f) := by
  ext
  simp

@[simp]
theorem arrowCongr'_refl : arrowCongr' .refl .refl = Equiv.refl (A₁ →⋆ₙₐ[R] A₂) :=
  rfl

@[simp]
theorem arrowCongr'_trans (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₁' : A₁' ≃⋆ₐ[R] A₂')
    (e₂ : A₂ ≃⋆ₐ[R] A₃) (e₂' : A₂' ≃⋆ₐ[R] A₃') :
    arrowCongr' (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr' e₁ e₁').trans (arrowCongr' e₂ e₂') :=
  rfl

@[simp]
theorem arrowCongr'_symm (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') :
    (arrowCongr' e₁ e₂).symm = arrowCongr' e₁.symm e₂.symm :=
  rfl

/-- Construct a star algebra equivalence from a pair of non-unital star algebra homomorphisms. -/
@[simps]
def ofHomInv' {R A B : Type*} [Monoid R]
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
    (f : A →⋆ₙₐ[R] B) (g : B →⋆ₙₐ[R] A) (h₁ : g.comp f = .id R A) (h₂ : f.comp g = .id R B) :
    A ≃⋆ₐ[R] B where
  toFun := f
  invFun := g
  left_inv x := congr($h₁ x)
  right_inv x := congr($h₂ x)
  map_mul' := map_mul f
  map_add' := map_add f
  map_star' := map_star f
  map_smul' := map_smul f

end NonUnital

section Unital

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
    e₂.toStarAlgHom.comp e₁.toStarAlgHom = (e₁.trans e₂).toStarAlgHom := rfl

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

/-- Construct a star algebra equivalence from a pair of star algebra homomorphisms. -/
@[simps]
def ofHomInv {R A B : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B]
    (f : A →⋆ₐ[R] B) (g : B →⋆ₐ[R] A) (h₁ : g.comp f = .id R A) (h₂ : f.comp g = .id R B) :
    A ≃⋆ₐ[R] B where
  toFun := f
  invFun := g
  left_inv x := congr($h₁ x)
  right_inv x := congr($h₂ x)
  map_mul' := map_mul f
  map_add' := map_add f
  map_star' := map_star f
  map_smul' := map_smul f

end Unital

end StarAlgEquiv

section UnitalTransfer

variable {R A B : Type*} {p : A → Prop} {q : B → Prop}
  [CommSemiring R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
  [Ring A] [StarRing A] [TopologicalSpace A] [Algebra R A]
  [Ring B] [StarRing B] [TopologicalSpace B] [Algebra R B]
  [instCFC : ContinuousFunctionalCalculus R A p]

@[simps!]
noncomputable def cfcHomTransfer (e : A ≃⋆ₐ[R] B) (hpq : ∀ x, p x ↔ q (e x))
    (b : B) (hb : q b) : C(spectrum R b, R) →⋆ₐ[R] B :=
  (Homeomorph.setCongr (by simp)).compStarAlgEquiv' R R |>.arrowCongr
    e (cfcHom (hpq (e.symm b) |>.mpr <| by simpa))

lemma continuous_cfcHomTransfer (e : A ≃⋆ₐ[R] B) (hpq : ∀ x, p x ↔ q (e x))
    (b : B) (hb : q b) (he : Continuous e) : Continuous (cfcHomTransfer e hpq b hb) :=
  (he.comp <| cfcHom_continuous _).comp <| ContinuousMap.continuous_precomp _

omit [TopologicalSpace B] in
lemma cfcHomTransfer_injective (e : A ≃⋆ₐ[R] B) (hpq : ∀ x, p x ↔ q (e x))
    (b : B) (hb : q b) : Function.Injective (cfcHomTransfer e hpq b hb) :=
  e.injective.comp (cfcHom_injective _) |>.comp <| Equiv.injective _

omit [TopologicalSpace B] in
lemma cfcHomTransfer_id (e : A ≃⋆ₐ[R] B) (hpq : ∀ x, p x ↔ q (e x)) (b : B) (hb : q b) :
    cfcHomTransfer e hpq b hb (.restrict (spectrum R b) (.id R) ) = b := by
  convert e.apply_symm_apply b
  congrm(e $(cfcHom_id _))

open ContinuousFunctionalCalculus in
/-- Transfer a continuous functional calculus instance to a type synonym with
a weaker topology. -/
theorem ContinuousFunctionCalculus.transfer (e : A ≃⋆ₐ[R] B)
    (he : Continuous e) (hpq : ∀ x, p x ↔ q (e x)) :
    ContinuousFunctionalCalculus R B q where
  predicate_zero := map_zero e ▸ (hpq 0 |>.mp instCFC.predicate_zero)
  compactSpace_spectrum b := by
    rw [← isCompact_iff_compactSpace, ← e.apply_symm_apply b, AlgEquiv.spectrum_eq]
    exact isCompact_spectrum (e.symm b)
  spectrum_nonempty b hb := by
    rw [← e.apply_symm_apply b, AlgEquiv.spectrum_eq]
    have := e.nontrivial
    exact spectrum_nonempty (e.symm b) <| by simpa [hpq]
  exists_cfc_of_predicate b hb :=
    have ha : p (e.symm b) := by simpa [hpq]
    ⟨cfcHomTransfer e hpq b hb,
      continuous_cfcHomTransfer e hpq b hb he,
      cfcHomTransfer_injective e hpq b hb,
      cfcHomTransfer_id e hpq b hb,
      fun f ↦ by simp [cfcHom_map_spectrum ha],
      fun f ↦ by simp [← hpq, cfcHom_predicate ha]⟩

end UnitalTransfer

section NonUnitalTransfer

open scoped ContinuousMapZero

variable {R A B : Type*} {p : A → Prop} {q : B → Prop}
  [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R]
  [IsTopologicalSemiring R] [ContinuousStar R]
  [NonUnitalRing A] [StarRing A] [TopologicalSpace A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalRing B] [StarRing B] [TopologicalSpace B]
  [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  [instCFC : NonUnitalContinuousFunctionalCalculus R A p]

@[simps!]
def ContinuousMapZero.starAlgEquiv_precomp {X Y : Type*} (R : Type*) [Zero X] [Zero Y]
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace R]
    [CommSemiring R] [StarRing R] [IsTopologicalSemiring R] [ContinuousStar R]
    (f : X ≃ₜ Y) (hf : f 0 = 0) :
    ContinuousMapZero Y R ≃⋆ₐ[R] ContinuousMapZero X R :=
  StarAlgEquiv.ofHomInv'
    (nonUnitalStarAlgHom_precomp R ⟨f, hf⟩)
    (nonUnitalStarAlgHom_precomp R ⟨f.symm, by simpa using congr(f.symm $hf.symm)⟩)
    (by ext; simp) (by ext; simp)

@[simp]
theorem ContinuousMapZero.coe_comp {X Y R : Type*} [Zero X] [Zero Y] [Zero R]
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace R]
    (g : ContinuousMapZero Y R) (f : ContinuousMapZero X Y) :
    g.comp f = g ∘ f :=
  rfl

-- `AlgEquiv` is too strong. That's terrible. We shouldn't need `Star` here
@[simp]
lemma AlgEquiv.quasispectrum_eq {F R A B : Type*} [CommSemiring R] [NonUnitalRing A]
    [NonUnitalRing B] [Module R A] [Module R B] [Star A] [Star B] [EquivLike F A B]
    [NonUnitalAlgEquivClass F R A B] [StarHomClass F A B]
    (f : F) (a : A) : quasispectrum R (f a) = quasispectrum R a := by
  let e := StarAlgEquivClass.toStarAlgEquiv f
  apply subset_antisymm
  · exact NonUnitalAlgHom.quasispectrum_apply_subset' R e a
  · simpa using NonUnitalAlgHom.quasispectrum_apply_subset' R e.symm (e a)

@[simps!]
noncomputable def cfcₙHomTransfer (e : A ≃⋆ₐ[R] B) (hpq : ∀ x, p x ↔ q (e x))
    (b : B) (hb : q b) : C(quasispectrum R b, R)₀ →⋆ₙₐ[R] B :=
  ContinuousMapZero.starAlgEquiv_precomp R
    (Homeomorph.setCongr (by simp)) (by ext; simp [Homeomorph.setCongr]) |>.arrowCongr'
    e (cfcₙHom (hpq (e.symm b) |>.mpr <| by simpa))

omit [IsScalarTower R B B] [SMulCommClass R B B] in
lemma continuous_cfcₙHomTransfer (e : A ≃⋆ₐ[R] B) (hpq : ∀ x, p x ↔ q (e x))
    (b : B) (hb : q b) (he : Continuous e) : Continuous (cfcₙHomTransfer e hpq b hb) :=
  (he.comp <| cfcₙHom_continuous _).comp <| ContinuousMapZero.continuous_precomp _

omit [TopologicalSpace B] [IsScalarTower R B B] [SMulCommClass R B B] in
lemma cfcₙHomTransfer_injective (e : A ≃⋆ₐ[R] B) (hpq : ∀ x, p x ↔ q (e x))
    (b : B) (hb : q b) : Function.Injective (cfcₙHomTransfer e hpq b hb) :=
  e.injective.comp (cfcₙHom_injective _) |>.comp <| Equiv.injective _

omit [TopologicalSpace B] [IsScalarTower R B B] [SMulCommClass R B B] in
lemma cfcₙHomTransfer_id (e : A ≃⋆ₐ[R] B) (hpq : ∀ x, p x ↔ q (e x)) (b : B) (hb : q b) :
    cfcₙHomTransfer e hpq b hb (.id (quasispectrum R b)) = b := by
  convert e.apply_symm_apply b
  congrm(e $(cfcₙHom_id _))

open NonUnitalContinuousFunctionalCalculus in
/-- Transfer a continuous functional calculus instance to a type synonym with
a weaker topology. -/
theorem NonUnitalContinuousFunctionCalculus.transfer (e : A ≃⋆ₐ[R] B)
    (he : Continuous e) (hpq : ∀ x, p x ↔ q (e x)) :
    NonUnitalContinuousFunctionalCalculus R B q where
  predicate_zero := map_zero e ▸ (hpq 0 |>.mp instCFC.predicate_zero)
  compactSpace_quasispectrum b := by
    rw [← isCompact_iff_compactSpace, ← e.apply_symm_apply b, AlgEquiv.quasispectrum_eq]
    exact isCompact_quasispectrum (e.symm b)
  exists_cfc_of_predicate b hb :=
    have ha : p (e.symm b) := by simpa [hpq]
    ⟨cfcₙHomTransfer e hpq b hb,
      continuous_cfcₙHomTransfer e hpq b hb he,
      cfcₙHomTransfer_injective e hpq b hb,
      cfcₙHomTransfer_id e hpq b hb,
      fun f ↦ by simp [cfcₙHom_map_quasispectrum ha, ContinuousMapZero.starAlgEquiv_precomp],
      fun f ↦ by simp [← hpq, cfcₙHom_predicate ha]⟩


end NonUnitalTransfer
