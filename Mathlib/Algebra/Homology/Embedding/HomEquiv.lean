/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Embedding.Restriction
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.Embedding.Boundary
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Relations between `extend` and `restriction`

Given an embedding `e : Embedding c c'` of complex shapes satisfying `e.IsRelIff`,
we obtain a bijection `e.homEquiv` between the type of morphisms
`K ⟶ L.extend e` (with `K : HomologicalComplex C c'` and `L : HomologicalComplex C c`)
and the subtype of morphisms `φ : K.restriction e ⟶ L` which satisfy a certain
condition `e.HasLift φ`.

## TODO
* obtain dual results for morphisms `L.extend e ⟶ K`.

-/

open CategoryTheory Category Limits

namespace ComplexShape

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')
  {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

namespace Embedding

open HomologicalComplex

variable {K K' : HomologicalComplex C c'} {L L' : HomologicalComplex C c}
  [e.IsRelIff]

section

/-- The condition on a morphism `K.restriction e ⟶ L` which allows to
extend it as a morphism `K ⟶ L.extend e`, see `Embedding.homEquiv`. -/
def HasLift (φ : K.restriction e ⟶ L) : Prop :=
  ∀ (j : ι) (_ : e.BoundaryGE j) (i' : ι')
    (_ : c'.Rel i' (e.f j)), K.d i' _ ≫ φ.f j = 0

namespace liftExtend

variable (φ : K.restriction e ⟶ L)

variable {e}

open Classical in
/-- Auxiliary definition for `liftExtend`. -/
noncomputable def f (i' : ι') : K.X i' ⟶ (L.extend e).X i' :=
  if hi' : ∃ i, e.f i = i' then
    (K.restrictionXIso e hi'.choose_spec).inv ≫ φ.f hi'.choose ≫
      (L.extendXIso e hi'.choose_spec).inv
  else 0

lemma f_eq {i' : ι'} {i : ι} (hi : e.f i = i') :
    f φ i' = (K.restrictionXIso e hi).inv ≫ φ.f i ≫ (L.extendXIso e hi).inv := by
  have hi' : ∃ k, e.f k = i' := ⟨i, hi⟩
  have : hi'.choose = i := e.injective_f (by rw [hi'.choose_spec, hi])
  dsimp [f]
  grind [f]

@[reassoc (attr := simp)]
lemma comm (hφ : e.HasLift φ) (i' j' : ι') :
    f φ i' ≫ (L.extend e).d i' j' = K.d i' j' ≫ f φ j' := by
  by_cases hij' : c'.Rel i' j'
  · by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi'
      rw [f_eq φ hi]
      by_cases hj' : ∃ j, e.f j = j'
      · obtain ⟨j, hj⟩ := hj'
        rw [f_eq φ hj, L.extend_d_eq e hi hj]
        subst hi hj
        simp [HomologicalComplex.restrictionXIso]
      · apply (L.isZero_extend_X e j' (by simpa using hj')).eq_of_tgt
    · have : (L.extend e).d i' j' = 0 := by
        apply (L.isZero_extend_X e i' (by simpa using hi')).eq_of_src
      rw [this, comp_zero]
      by_cases hj' : ∃ j, e.f j = j'
      · obtain ⟨j, rfl⟩ := hj'
        rw [f_eq φ rfl]
        dsimp [restrictionXIso]
        rw [id_comp, reassoc_of% (hφ j (e.boundaryGE hij'
          (by simpa using hi')) i' hij'), zero_comp]
      · have : f φ j' = 0 := by
          apply (L.isZero_extend_X e j' (by simpa using hj')).eq_of_tgt
        rw [this, comp_zero]
  · simp [HomologicalComplex.shape _ _ _ hij']

end liftExtend

variable (φ : K.restriction e ⟶ L) (hφ : e.HasLift φ)

/-- The morphism  `K ⟶ L.extend e` given by a morphism `K.restriction e ⟶ L`
which satisfy `e.HasLift φ`. -/
noncomputable def liftExtend :
    K ⟶ L.extend e where
  f i' := liftExtend.f φ i'
  comm' _ _ _ := liftExtend.comm φ hφ _ _

variable {i' : ι'} {i : ι} (hi : e.f i = i')

lemma liftExtend_f :
    (e.liftExtend φ hφ).f i' = (K.restrictionXIso e hi).inv ≫ φ.f i ≫
      (L.extendXIso e hi).inv := by
  apply liftExtend.f_eq

/-- Given `φ : K.restriction e ⟶ L` such that `hφ : e.HasLift φ`, this is
the isomorphisms in the category of arrows between the maps
`(e.liftExtend φ hφ).f i'` and `φ.f i` when `e.f i = i'`. -/
noncomputable def liftExtendfArrowIso :
    Arrow.mk ((e.liftExtend φ hφ).f i') ≅ Arrow.mk (φ.f i) :=
  Arrow.isoMk (K.restrictionXIso e hi).symm (L.extendXIso e hi)
    (by simp [e.liftExtend_f φ hφ hi])

lemma isIso_liftExtend_f_iff (hi : e.f i = i') :
    IsIso ((e.liftExtend φ hφ).f i') ↔ IsIso (φ.f i) :=
  (MorphismProperty.isomorphisms C).arrow_mk_iso_iff (e.liftExtendfArrowIso φ hφ hi)

lemma mono_liftExtend_f_iff (hi : e.f i = i') :
    Mono ((e.liftExtend φ hφ).f i') ↔ Mono (φ.f i) :=
  (MorphismProperty.monomorphisms C).arrow_mk_iso_iff (e.liftExtendfArrowIso φ hφ hi)

lemma epi_liftExtend_f_iff (hi : e.f i = i') :
    Epi ((e.liftExtend φ hφ).f i') ↔ Epi (φ.f i) :=
  (MorphismProperty.epimorphisms C).arrow_mk_iso_iff (e.liftExtendfArrowIso φ hφ hi)

end

namespace homRestrict

variable {e}
variable (ψ : K ⟶ L.extend e)

/-- Auxiliary definition for `Embedding.homRestrict`. -/
noncomputable def f (i : ι) : (K.restriction e).X i ⟶ L.X i :=
  ψ.f (e.f i) ≫ (L.extendXIso e rfl).hom

lemma f_eq {i : ι} {i' : ι'} (h : e.f i = i') :
    f ψ i = (K.restrictionXIso e h).hom ≫ ψ.f i' ≫ (L.extendXIso e h).hom := by
  subst h
  simp [f, restrictionXIso]

@[reassoc (attr := simp)]
lemma comm (i j : ι) :
    f ψ i ≫ L.d i j = K.d (e.f i) (e.f j) ≫ f ψ j := by
  dsimp [f]
  simp only [assoc, ← ψ.comm_assoc, L.extend_d_eq e rfl rfl, Iso.inv_hom_id, comp_id]

end homRestrict

/-- The morphism `K.restriction e ⟶ L` induced by a morphism `K ⟶ L.extend e`. -/
noncomputable def homRestrict (ψ : K ⟶ L.extend e) : K.restriction e ⟶ L where
  f i := homRestrict.f ψ i

lemma homRestrict_f (ψ : K ⟶ L.extend e) {i : ι} {i' : ι'} (h : e.f i = i') :
    (e.homRestrict ψ).f i = (K.restrictionXIso e h).hom ≫ ψ.f i' ≫ (L.extendXIso e h).hom :=
  homRestrict.f_eq ψ h

lemma homRestrict_hasLift (ψ : K ⟶ L.extend e) :
    e.HasLift (e.homRestrict ψ) := by
  intro j hj i' hij'
  have : (L.extend e).d i' (e.f j) = 0 := by
    apply (L.isZero_extend_X e i' (hj.notMem hij')).eq_of_src
  dsimp [homRestrict]
  rw [homRestrict.f_eq ψ rfl, restrictionXIso, eqToIso_refl, Iso.refl_hom, id_comp,
    ← ψ.comm_assoc, this, zero_comp, comp_zero]

@[simp]
lemma liftExtend_homRestrict (ψ : K ⟶ L.extend e) :
    e.liftExtend (e.homRestrict ψ) (e.homRestrict_hasLift ψ) = ψ := by
  ext i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    simp [e.homRestrict_f _ rfl, e.liftExtend_f _ _ rfl]
  · apply (L.isZero_extend_X e i' (by simpa using hi')).eq_of_tgt

@[simp]
lemma homRestrict_liftExtend (φ : K.restriction e ⟶ L) (hφ : e.HasLift φ) :
    e.homRestrict (e.liftExtend φ hφ) = φ := by
  ext i
  simp [e.homRestrict_f _ rfl, e.liftExtend_f _ _ rfl]

@[reassoc]
lemma homRestrict_precomp (α : K' ⟶ K) (ψ : K ⟶ L.extend e) :
    e.homRestrict (α ≫ ψ) = restrictionMap α e ≫ e.homRestrict ψ := by
  ext i
  simp [homRestrict_f _ _ rfl, restrictionXIso]

@[reassoc]
lemma homRestrict_comp_extendMap (ψ : K ⟶ L.extend e) (β : L ⟶ L') :
    e.homRestrict (ψ ≫ extendMap β e) =
      e.homRestrict ψ ≫ β := by
  ext i
  simp [homRestrict_f _ _ rfl, extendMap_f β e rfl]

variable (K L)

/-- The bijection between `K ⟶ L.extend e` and the subtype of `K.restriction e ⟶ L`
consisting of morphisms `φ` such that `e.HasLift φ`. -/
@[simps]
noncomputable def homEquiv :
    (K ⟶ L.extend e) ≃ { φ : K.restriction e ⟶ L // e.HasLift φ } where
  toFun ψ := ⟨e.homRestrict ψ, e.homRestrict_hasLift ψ⟩
  invFun φ := e.liftExtend φ.1 φ.2
  left_inv ψ := by simp
  right_inv φ := by simp

end Embedding

end ComplexShape
