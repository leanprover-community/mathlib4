/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital

/-! # Transfer instances of the continuous functional calculus

One may transfer instances of the continuous functional calculus across a star algebra equivalence,
so long as this equivalence is continuous. Crucially, it's inverse need not be continuous. This
allows to, for example, equip type synonyms of a C⋆-algebra with weaker topologies with instances
of the continuous functional calculus.
-/

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
  StarAlgEquiv.ofNonUnitalStarAlgHom
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
