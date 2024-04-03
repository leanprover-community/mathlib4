import Mathlib.Algebra.Homology.Embedding.Restriction
import Mathlib.Algebra.Homology.Embedding.Extend

open CategoryTheory Category Limits

namespace ComplexShape

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (e : Embedding c c')
  {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

namespace Embedding

open HomologicalComplex

variable {K : HomologicalComplex C c'} {L : HomologicalComplex C c}
  [e.IsRelIff]

section

def HasLift (φ : K.restriction e ⟶ L) : Prop :=
  ∀ (j : ι) (_ : e.BoundaryGE j) (i' : ι')
    (_ : c'.Rel i' (e.f j)), K.d i' _ ≫ φ.f j = 0

namespace liftExtend

variable (φ : K.restriction e ⟶ L) (hφ : e.HasLift φ)

variable {e}

open Classical in
noncomputable def f (i' : ι') : K.X i' ⟶ (L.extend e).X i' :=
  if hi' : ∃ i, e.f i = i'
  then (K.restrictionXIso e hi'.choose_spec).inv ≫ φ.f hi'.choose ≫
      (L.extendXIso e hi'.choose_spec).inv
  else 0

lemma f_eq {i' : ι'} {i : ι} (hi : e.f i = i') :
    f φ i' = (K.restrictionXIso e hi).inv ≫ φ.f i ≫ (L.extendXIso e hi).inv := by
  have hi' : ∃ k, e.f k = i' := ⟨i, hi⟩
  have : hi'.choose = i := e.injective_f (by rw [hi'.choose_spec, hi])
  dsimp [f]
  rw [dif_pos ⟨i, hi⟩]
  subst this
  rfl

@[reassoc (attr := simp)]
lemma comm (i' j' : ι') : f φ i' ≫ (L.extend e).d i' j' = K.d i' j' ≫ f φ j' := by
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
        rw [id_comp, reassoc_of% (hφ j (e.mem_boundaryGE hij'
          (by simpa using hi')) i' hij'), zero_comp]
      · have : f φ j' = 0 := by
          apply (L.isZero_extend_X e j' (by simpa using hj')).eq_of_tgt
        rw [this, comp_zero]
  · simp [HomologicalComplex.shape _ _ _ hij']

end liftExtend

noncomputable def liftExtend (φ : K.restriction e ⟶ L) (hφ : e.HasLift φ) :
    K ⟶ L.extend e where
  f i' := liftExtend.f φ i'
  comm' _ _ _ := liftExtend.comm φ hφ _ _

lemma liftExtend_f (φ : K.restriction e ⟶ L) (hφ : e.HasLift φ)
    {i' : ι'} {i : ι} (hi : e.f i = i') :
    (e.liftExtend φ hφ).f i' = (K.restrictionXIso e hi).inv ≫ φ.f i ≫
      (L.extendXIso e hi).inv := by
  apply liftExtend.f_eq

end

namespace homRestrict

variable {e}
variable (ψ : K ⟶ L.extend e)

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

noncomputable def homRestrict (ψ : K ⟶ L.extend e) : K.restriction e ⟶ L where
  f i := homRestrict.f ψ i

lemma homRestrict_f (ψ : K ⟶ L.extend e) {i : ι} {i' : ι'} (h : e.f i = i') :
    (e.homRestrict ψ).f i = (K.restrictionXIso e h).hom ≫ ψ.f i' ≫ (L.extendXIso e h).hom :=
  homRestrict.f_eq ψ h

lemma homRestrict_hasLift (ψ : K ⟶ L.extend e) :
    e.HasLift (e.homRestrict ψ) := by
  intro j hj i' hij'
  have : (L.extend e).d i' (e.f j) = 0 := by
    apply (L.isZero_extend_X e i' (hj.not_mem hij')).eq_of_src
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

variable (K L)

noncomputable def homEquiv :
    (K ⟶ L.extend e) ≃ { φ : K.restriction e ⟶ L // e.HasLift φ } where
  toFun ψ := ⟨e.homRestrict ψ, e.homRestrict_hasLift ψ⟩
  invFun φ := e.liftExtend φ.1 φ.2
  left_inv ψ := by simp
  right_inv φ := by simp

end Embedding

end ComplexShape
