/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# The extension functor on the homotopy categories

Given an embedding of complex shapes `e : c.Embedding c'` and a preadditive
category `C`, we define a fully faithful functor
`e.extendHomotopyFunctor C : HomotopyCategory C c ⥤ HomotopyCategory C c'`.

-/

@[expose] public section

open CategoryTheory Category Limits ZeroObject

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace Homotopy

open HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C]
  {K L : HomologicalComplex C c} {f g : K ⟶ L}

namespace extend

variable (e : c.Embedding c') (φ : ∀ i j, K.X i ⟶ L.X j)

/-- Auxiliary definition for `Homotopy.extend` -/
noncomputable def homAux (i' j' : Option ι) : extend.X K i' ⟶ extend.X L j' :=
  match i', j' with
  | none, _ => 0
  | _, none => 0
  | some i, some j => φ i j

lemma homAux_eq (i' j' : Option ι) (i j : ι) (hi : i' = some i) (hj : j' = some j) :
    homAux φ i' j' = (extend.XIso K hi).hom ≫ φ i j ≫ (extend.XIso L hj).inv := by
  subst hi hj
  simp [homAux, extend.XIso, extend.X]

/-- Auxiliary defnition for `Homotopy.extend`. -/
noncomputable def hom (i' j' : ι') : (K.extend e).X i' ⟶ (L.extend e).X j' :=
  extend.homAux φ (e.r i') (e.r j')

lemma hom_eq_zero₁ (i' j' : ι') (hi' : ∀ i, e.f i ≠ i') :
    hom e φ i' j' = 0 :=
  (isZero_extend_X _ _ _ hi').eq_of_src _ _

lemma hom_eq_zero₂ (i' j' : ι') (hj' : ∀ j, e.f j ≠ j') :
    hom e φ i' j' = 0 :=
  (isZero_extend_X _ _ _ hj').eq_of_tgt _ _

lemma hom_eq {i' j' : ι'} {i j : ι} (hi : e.f i = i') (hj : e.f j = j') :
    hom e φ i' j' = (K.extendXIso e hi).hom ≫ φ i j ≫ (L.extendXIso e hj).inv :=
  homAux_eq φ (e.r i') (e.r j') i j (e.r_eq_some hi) (e.r_eq_some hj)

end extend

/-- If `e : c.Embedding c'` is an embedding of complex shapes and `h` is a
homotopy between morphisms of homological complexes of shape `c`, this is
the corresponding homotopy between the extension of these morphisms. -/
noncomputable def extend (h : Homotopy f g) (e : c.Embedding c') [e.IsRelIff] :
    Homotopy (extendMap f e) (extendMap g e) where
  hom := extend.hom e h.hom
  comm i' := by
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      rw [extendMap_f _ _ rfl, extendMap_f _ _ rfl, h.comm i, Preadditive.add_comp,
        Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_add, add_left_inj]
      congr 1
      · by_cases hi : c.Rel i (c.next i)
        · have hi' : c'.Rel (e.f i) (e.f (c.next i)) := by rwa [e.rel_iff]
          simp [dNext_eq _ hi, dNext_eq _ hi', extend.hom_eq _ _ rfl rfl,
            extend_d_eq _ _ rfl rfl]
        · rw [dNext_eq_zero _ _ hi]
          by_cases hi' : c'.Rel (e.f i) (c'.next (e.f i))
          · simp [dNext_eq _ hi', K.extend_d_from_eq_zero _ _ _ _ rfl hi]
          · simp [dNext_eq_zero _ _ hi']
      · by_cases hi : c.Rel (c.prev i) i
        · have hi' : c'.Rel (e.f (c.prev i)) (e.f i) := by rwa [e.rel_iff]
          simp [prevD_eq _ hi, prevD_eq _ hi', extend.hom_eq _ _ rfl rfl,
            extend_d_eq _ _ rfl rfl]
        · rw [prevD_eq_zero _ _ hi]
          by_cases hi' : c'.Rel (c'.prev (e.f i)) (e.f i)
          · simp [prevD_eq _ hi', L.extend_d_to_eq_zero _ _ _ _ rfl hi]
          · simp [prevD_eq_zero _ _ hi']
    · exact (isZero_extend_X _ _ _ (by tauto)).eq_of_src _ _
  zero i' j' hij' := by
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      by_cases hj' : ∃ j, e.f j = j'
      · obtain ⟨j, rfl⟩ := hj'
        rw [extend.hom_eq _ _ rfl rfl, h.zero _ _ (by rwa [← e.rel_iff]),
          zero_comp, comp_zero]
      · exact extend.hom_eq_zero₂ _ _ _ _ (by tauto)
    · exact extend.hom_eq_zero₁ _ _ _ _ (by tauto)

lemma extend_hom_eq (h : Homotopy f g) (e : c.Embedding c') [e.IsRelIff]
    {i' j' : ι'} {i j : ι} (hi : e.f i = i') (hj : e.f j = j') :
    (h.extend e).hom i' j' = (K.extendXIso e hi).hom ≫ h.hom i j ≫ (L.extendXIso e hj).inv :=
  extend.hom_eq _ _ _ _

/-- If `e : c.Embedding c'` is an embedding of complex shapes,
`f` and `g` are morphism between cochain complexes of shape `c`,
and `h` is an homotopy between the extensions `extendMap f e` and `extendMap g e`,
then this is the corresponding homotopy between `f` and `g`. -/
@[simps -isSimp]
noncomputable def ofExtend {e : c.Embedding c'} [e.IsRelIff]
    (h : Homotopy (extendMap f e) (extendMap g e)) :
    Homotopy f g where
  hom i j := (K.extendXIso e rfl).inv ≫ h.hom (e.f i) (e.f j) ≫ (L.extendXIso e rfl).hom
  comm i := by
    have := h.comm (e.f i)
    simp only [extendMap_f _ _ rfl] at this
    simp only [← cancel_mono (L.extendXIso e rfl).inv,
      ← cancel_epi (K.extendXIso e rfl).hom, this, Preadditive.add_comp,
      Preadditive.comp_add, add_left_inj]
    congr 1
    · by_cases hi : c.Rel i (c.next i)
      · have hi' : c'.Rel (e.f i) (e.f (c.next i)) := by rwa [e.rel_iff]
        simp [dNext_eq _ hi, dNext_eq _ hi', K.extend_d_eq _ rfl rfl]
      · rw [dNext_eq_zero _ _ hi]
        by_cases hi' : c'.Rel (e.f i) (c'.next (e.f i))
        · simp [dNext_eq _ hi', extend_d_from_eq_zero _ _ _ _ _ rfl hi]
        · simp [dNext_eq_zero _ _ hi']
    · by_cases hi : c.Rel (c.prev i) i
      · have hi' : c'.Rel (e.f (c.prev i)) (e.f i) := by rwa [e.rel_iff]
        simp [prevD_eq _ hi, prevD_eq _ hi', L.extend_d_eq _ rfl rfl]
      · rw [prevD_eq_zero _ _ hi]
        by_cases hi' : c'.Rel (c'.prev (e.f i)) (e.f i)
        · simp [prevD_eq _ hi', extend_d_to_eq_zero _ _ _ _ _ rfl hi]
        · simp [prevD_eq_zero _ _ hi']
  zero i j hij := by rw [h.zero _ _ (by rwa [e.rel_iff]), zero_comp, comp_zero]

@[simp]
lemma extend_ofExtend {e : c.Embedding c'} [e.IsRelIff]
    (h : Homotopy (extendMap f e) (extendMap g e)) :
    (ofExtend h).extend e = h := by
  ext i' j'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    by_cases hj' : ∃ j, e.f j = j'
    · obtain ⟨j, rfl⟩ := hj'
      simp [extend_hom_eq _ e rfl rfl, ofExtend_hom]
    · exact (isZero_extend_X _ _ _ (by tauto)).eq_of_tgt _ _
  · exact (isZero_extend_X _ _ _ (by tauto)).eq_of_src _ _

@[simp]
lemma ofExtend_extend (h : Homotopy f g) (e : c.Embedding c') [e.IsRelIff] :
    (h.extend e).ofExtend = h := by
  ext i j
  simp [ofExtend_hom, h.extend_hom_eq e rfl rfl]


/-- If `e : c.Embedding c'` is an embedding of complex shapes,
`f` and `g` are morphism between cochain complexes of shape `c`,
this is the bijection between homotopies between `f` and `g`,
and homotopies between the extensions `extendMap f e` and `extendMap g e`. -/
noncomputable def extendEquiv (e : c.Embedding c') [e.IsRelIff] :
    Homotopy f g ≃ Homotopy (extendMap f e) (extendMap g e) where
  toFun h := h.extend e
  invFun h := h.ofExtend
  left_inv _ := by simp
  right_inv _ := by simp

end Homotopy

namespace ComplexShape.Embedding

variable (e : Embedding c c') [e.IsRelIff]
  (C : Type*) [Category* C] [HasZeroObject C] [Preadditive C]

/-- Given an embedding `e : c.Embedding c'` of complex shapes, this is
the functor `HomotopyCategory C c ⥤ HomotopyCategory C c'` which
extend complexes along `e`. -/
noncomputable def extendHomotopyFunctor :
    HomotopyCategory C c ⥤ HomotopyCategory C c' :=
  CategoryTheory.Quotient.lift _ (e.extendFunctor C ⋙ HomotopyCategory.quotient C c') (by
    rintro K L f₁ f₂ ⟨h⟩
    exact HomotopyCategory.eq_of_homotopy _ _ (h.extend e))

/-- Given an embedding `e : c.Embedding c'` of complex shapes, the
functor `e.extendHomotopyFunctor C` on homotopy categories is
induced by the functor `e.extendFunctor C` on homological complexes. -/
noncomputable def extendHomotopyFunctorFactors :
    HomotopyCategory.quotient C c ⋙ e.extendHomotopyFunctor C ≅
      e.extendFunctor C ⋙ HomotopyCategory.quotient C c' :=
  Iso.refl _

instance : (e.extendHomotopyFunctor C).Full where
  map_surjective {K L} φ := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    obtain ⟨φ : K.extend e ⟶ L.extend e, rfl⟩ :=
      (HomotopyCategory.quotient C c').map_surjective φ
    obtain ⟨φ, rfl⟩ := (e.extendFunctor C).map_surjective φ
    exact ⟨(HomotopyCategory.quotient _ _).map φ, rfl⟩

instance : (e.extendHomotopyFunctor C).Faithful where
  map_injective {K L} φ₁ φ₂ hφ := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    obtain ⟨φ₁, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective φ₁
    obtain ⟨φ₂, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective φ₂
    exact HomotopyCategory.eq_of_homotopy _ _
      (.ofExtend (HomotopyCategory.homotopyOfEq _ _ hφ))

end ComplexShape.Embedding
