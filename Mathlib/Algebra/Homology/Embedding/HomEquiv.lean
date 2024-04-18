import Mathlib.Algebra.Homology.Embedding.Restriction
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.CategoryTheory.MorphismProperty

open CategoryTheory Category Limits

namespace ComplexShape

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (e : Embedding c c')
  {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

namespace Embedding

open HomologicalComplex

variable {K K' : HomologicalComplex C c'} {L L' : HomologicalComplex C c}
  [e.IsRelIff]

section

def HasLift (φ : K.restriction e ⟶ L) : Prop :=
  ∀ (j : ι) (_ : e.BoundaryGE j) (i' : ι')
    (_ : c'.Rel i' (e.f j)), K.d i' _ ≫ φ.f j = 0

def HasDesc (φ : L ⟶ K.restriction e) : Prop :=
  ∀ (i : ι) (_ : e.BoundaryLE i) (j' : ι')
    (_ : c'.Rel (e.f i) j' ), φ.f i ≫ K.d _ j' = 0

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

variable (φ : K.restriction e ⟶ L) (hφ : e.HasLift φ)

noncomputable def liftExtend :
    K ⟶ L.extend e where
  f i' := liftExtend.f φ i'
  comm' _ _ _ := liftExtend.comm φ hφ _ _

variable {i' : ι'} {i : ι} (hi : e.f i = i')

lemma liftExtend_f :
    (e.liftExtend φ hφ).f i' = (K.restrictionXIso e hi).inv ≫ φ.f i ≫
      (L.extendXIso e hi).inv := by
  apply liftExtend.f_eq

noncomputable def liftExtendfArrowIso :
    Arrow.mk ((e.liftExtend φ hφ).f i') ≅ Arrow.mk (φ.f i) :=
  Arrow.isoMk (K.restrictionXIso e hi).symm (L.extendXIso e hi)
    (by simp [e.liftExtend_f φ hφ hi])

lemma isIso_liftExtend_f_iff :
    IsIso ((e.liftExtend φ hφ).f i') ↔ IsIso (φ.f i) :=
  (MorphismProperty.RespectsIso.isomorphisms C).arrow_mk_iso_iff (e.liftExtendfArrowIso φ hφ hi)

lemma mono_liftExtend_f_iff :
    Mono ((e.liftExtend φ hφ).f i') ↔ Mono (φ.f i) :=
  (MorphismProperty.RespectsIso.monomorphisms C).arrow_mk_iso_iff (e.liftExtendfArrowIso φ hφ hi)

lemma epi_liftExtend_f_iff :
    Epi ((e.liftExtend φ hφ).f i') ↔ Epi (φ.f i) :=
  (MorphismProperty.RespectsIso.epimorphisms C).arrow_mk_iso_iff (e.liftExtendfArrowIso φ hφ hi)


namespace descExtend

variable (φ : L ⟶ K.restriction e) (hφ : e.HasDesc φ)

variable {e}

open Classical in
noncomputable def f (i' : ι') : (L.extend e).X i' ⟶ K.X i' :=
  if hi' : ∃ i, e.f i = i'
  then (L.extendXIso e hi'.choose_spec).hom ≫ φ.f hi'.choose ≫
    (K.restrictionXIso e hi'.choose_spec).hom
  else 0

lemma f_eq {i' : ι'} {i : ι} (hi : e.f i = i') :
    f φ i' = (L.extendXIso e hi).hom ≫ φ.f i ≫ (K.restrictionXIso e hi).hom := by
  have hi' : ∃ k, e.f k = i' := ⟨i, hi⟩
  have : hi'.choose = i := e.injective_f (by rw [hi'.choose_spec, hi])
  dsimp [f]
  rw [dif_pos ⟨i, hi⟩]
  subst this
  rfl

@[reassoc (attr := simp)]
lemma comm (i' j' : ι') : f φ i' ≫ K.d i' j' = (L.extend e).d i' j' ≫ f φ j' := by
  by_cases hij' : c'.Rel i' j'
  · by_cases hj' : ∃ j, e.f j = j'
    · obtain ⟨j, hj⟩ := hj'
      rw [f_eq φ hj]
      by_cases hi' : ∃ i, e.f i = i'
      · obtain ⟨i, hi⟩ := hi'
        rw [f_eq φ hi, L.extend_d_eq e hi hj]
        subst hi hj
        simpa [HomologicalComplex.restrictionXIso] using φ.comm i j
      · apply (L.isZero_extend_X e i' (by simpa using hi')).eq_of_src
    · have : (L.extend e).d i' j' = 0 := by
        apply (L.isZero_extend_X e j' (by simpa using hj')).eq_of_tgt
      rw [this, zero_comp]
      by_cases hi' : ∃ i, e.f i = i'
      · obtain ⟨i, rfl⟩ := hi'
        rw [f_eq φ rfl]
        dsimp [restrictionXIso]
        rw [comp_id, assoc, hφ i (e.mem_boundaryLE hij' (by simpa using hj')) j' hij', comp_zero]
      · have : f φ i' = 0 := by
          apply (L.isZero_extend_X e i' (by simpa using hi')).eq_of_src
        rw [this, zero_comp]
  · simp [HomologicalComplex.shape _ _ _ hij']

end descExtend

variable (φ : L ⟶ K.restriction e) (hφ : e.HasDesc φ)

noncomputable def descExtend :
    L.extend e ⟶ K where
  f i' := descExtend.f φ i'
  comm' _ _ _ := descExtend.comm φ hφ _ _

variable {i' : ι'} {i : ι} (hi : e.f i = i')

lemma descExtend_f :
    (e.descExtend φ hφ).f i' = (L.extendXIso e hi).hom ≫ φ.f i ≫(K.restrictionXIso e hi).hom := by
  apply descExtend.f_eq

noncomputable def descExtendfArrowIso :
    Arrow.mk ((e.descExtend φ hφ).f i') ≅ Arrow.mk (φ.f i) :=
  Arrow.isoMk (L.extendXIso e hi) (K.restrictionXIso e hi).symm
    (by simp [e.descExtend_f φ hφ hi])

lemma isIso_descExtend_f_iff :
    IsIso ((e.descExtend φ hφ).f i') ↔ IsIso (φ.f i) :=
  (MorphismProperty.RespectsIso.isomorphisms C).arrow_mk_iso_iff (e.descExtendfArrowIso φ hφ hi)

lemma mono_descExtend_f_iff :
    Mono ((e.descExtend φ hφ).f i') ↔ Mono (φ.f i) :=
  (MorphismProperty.RespectsIso.monomorphisms C).arrow_mk_iso_iff (e.descExtendfArrowIso φ hφ hi)

lemma epi_descExtend_f_iff :
    Epi ((e.descExtend φ hφ).f i') ↔ Epi (φ.f i) :=
  (MorphismProperty.RespectsIso.epimorphisms C).arrow_mk_iso_iff (e.descExtendfArrowIso φ hφ hi)

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

@[reassoc]
lemma homRestrict_precomp (α : K' ⟶ K) (ψ : K ⟶ L.extend e) :
    e.homRestrict (α ≫ ψ) = restrictionMap α e ≫ e.homRestrict ψ := by
  ext i
  simp [homRestrict_f _ _ rfl, restrictionXIso]

@[reassoc]
lemma homRestrict_comp_extend (ψ : K ⟶ L.extend e) (β : L ⟶ L') :
    e.homRestrict (ψ ≫ extendMap β e) =
      e.homRestrict ψ ≫ β := by
  ext i
  simp [homRestrict_f _ _ rfl, extendMap_f β e rfl]

namespace homRestrict'

variable {e}
variable (ψ : L.extend e ⟶ K)

noncomputable def f (i : ι) : L.X i ⟶ (K.restriction e).X i :=
  (L.extendXIso e rfl).inv ≫ ψ.f (e.f i)

lemma f_eq {i : ι} {i' : ι'} (h : e.f i = i') :
    f ψ i = (L.extendXIso e h).inv ≫ ψ.f i' ≫ (K.restrictionXIso e h).inv := by
  subst h
  simp [f, restrictionXIso]

@[reassoc (attr := simp)]
lemma comm (i j : ι) :
    f ψ i ≫ K.d (e.f i) (e.f j) = L.d i j ≫ f ψ j := by
  dsimp [f]
  rw [assoc, Hom.comm, L.extend_d_eq e rfl rfl, assoc, assoc, Iso.inv_hom_id_assoc]

end homRestrict'

noncomputable def homRestrict' (ψ : L.extend e ⟶ K) : L ⟶ K.restriction e where
  f i := homRestrict'.f ψ i

lemma homRestrict'_f (ψ : L.extend e ⟶ K) {i : ι} {i' : ι'} (h : e.f i = i') :
    (e.homRestrict' ψ).f i = (L.extendXIso e h).inv ≫ ψ.f i'≫ (K.restrictionXIso e h).inv:=
  homRestrict'.f_eq ψ h

lemma homRestrict'_hasDesc (ψ : L.extend e ⟶ K) :
    e.HasDesc (e.homRestrict' ψ) := by
  intro i hi j' hij'
  have : (L.extend e).d (e.f i) j' = 0 := by
    apply (L.isZero_extend_X e j' (hi.not_mem hij')).eq_of_tgt
  dsimp [homRestrict']
  rw [homRestrict'.f_eq ψ rfl, restrictionXIso, eqToIso_refl, Iso.refl_inv, assoc, assoc]
  dsimp
  rw [id_comp, ψ.comm, this, zero_comp, comp_zero]

@[simp]
lemma descExtend_homRestrict' (ψ : L.extend e ⟶ K) :
    e.descExtend (e.homRestrict' ψ) (e.homRestrict'_hasDesc ψ) = ψ := by
  ext i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    simp [e.homRestrict'_f _ rfl, e.descExtend_f _ _ rfl]
  · apply (L.isZero_extend_X e i' (by simpa using hi')).eq_of_src

@[simp]
lemma homRestrict'_descExtend (φ : L ⟶ K.restriction e) (hφ : e.HasDesc φ) :
    e.homRestrict' (e.descExtend φ hφ) = φ := by
  ext i
  simp [e.homRestrict'_f _ rfl, e.descExtend_f _ _ rfl]

@[reassoc]
lemma homRestrict'_postcomp (α : K ⟶ K') (ψ : L.extend e ⟶ K) :
    e.homRestrict' (ψ ≫ α) = e.homRestrict' ψ ≫ restrictionMap α e:= by
  ext i
  simp [homRestrict'_f _ _ rfl, restrictionXIso]

@[reassoc]
lemma extend_comp_homRestrict' (ψ : L.extend e ⟶ K) (β : L' ⟶ L) :
    e.homRestrict' (extendMap β e ≫ ψ) =
      β ≫ e.homRestrict' ψ := by
  ext i
  simp [homRestrict'_f _ _ rfl, extendMap_f β e rfl]

variable (K L)

@[simps]
noncomputable def homEquiv :
    (K ⟶ L.extend e) ≃ { φ : K.restriction e ⟶ L // e.HasLift φ } where
  toFun ψ := ⟨e.homRestrict ψ, e.homRestrict_hasLift ψ⟩
  invFun φ := e.liftExtend φ.1 φ.2
  left_inv ψ := by simp
  right_inv φ := by simp

@[simps]
noncomputable def homEquiv' (L : HomologicalComplex C c) (K : HomologicalComplex C c') :
    (L.extend e ⟶ K) ≃ { φ : L ⟶ K.restriction e // e.HasDesc φ } where
  toFun ψ := ⟨e.homRestrict' ψ, e.homRestrict'_hasDesc ψ⟩
  invFun φ := e.descExtend φ.1 φ.2
  left_inv ψ := by simp
  right_inv φ := by simp

end Embedding

end ComplexShape
