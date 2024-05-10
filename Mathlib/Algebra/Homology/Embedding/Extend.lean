import Mathlib.Algebra.Homology.Embedding.Basic
import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

open CategoryTheory Category Limits ZeroObject

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace HomologicalComplex


variable {C : Type*} [Category C] [HasZeroObject C]

section

variable [HasZeroMorphisms C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

namespace extend

noncomputable def X : Option ι → C
  | some x => K.X x
  | none => 0

noncomputable def XIso {i : Option ι} {j : ι} (hj : i = some j) :
    X K i ≅ K.X j := eqToIso (by subst hj; rfl)

lemma isZero_X {i : Option ι} (hi : i = none) :
    IsZero (X K i) := by
  subst hi
  exact Limits.isZero_zero _

noncomputable def d : ∀ (i j : Option ι), extend.X K i ⟶ extend.X K j
  | none, _ => 0
  | some i, some j => K.d i j
  | some _, none => 0

lemma d_none_eq_zero (i j : Option ι) (hi : i = none) :
    d K i j = 0 := by subst hi; rfl

lemma d_none_eq_zero' (i j : Option ι) (hj : j = none) :
    d K i j = 0 := by subst hj; cases i <;> rfl

lemma d_eq {i j : Option ι} {a b : ι}
    (hi : i = some a) (hj : j = some b) :
    d K i j = (XIso K hi).hom ≫ K.d a b ≫ (XIso K hj).inv := by
  subst hi hj
  dsimp [XIso, d]
  erw [id_comp, comp_id]

variable {K L}

noncomputable def mapX : ∀ (i : Option ι), X K i ⟶ X L i
  | some i => φ.f i
  | none => 0

lemma mapX_some {i : Option ι} {a : ι} (hi : i = some a) :
    mapX φ i = (XIso K hi).hom ≫ φ.f a ≫ (XIso L hi).inv := by
  subst hi
  dsimp [XIso]
  erw [id_comp, comp_id]
  rfl

lemma mapX_none {i : Option ι} (hi : i = none) :
    mapX φ i = 0 := by subst hi; rfl

end extend

noncomputable def extend : HomologicalComplex C c' where
  X i' := extend.X K (e.r i')
  d i' j' := extend.d K (e.r i') (e.r j')
  shape i' j' h := by
    dsimp
    obtain hi'|⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
    · rw [extend.d_none_eq_zero K _ _ hi']
    · obtain hj'|⟨j, hj⟩ := (e.r j').eq_none_or_eq_some
      · rw [extend.d_none_eq_zero' K _ _ hj']
      · rw [extend.d_eq K hi hj,K.shape, zero_comp, comp_zero]
        obtain rfl := e.f_eq_of_r_eq_some hi
        obtain rfl := e.f_eq_of_r_eq_some hj
        intro hij
        exact h (e.rel hij)
  d_comp_d' i' j' k' _ _ := by
    dsimp
    obtain hi'|⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
    · rw [extend.d_none_eq_zero K _ _ hi', zero_comp]
    · obtain hj'|⟨j, hj⟩ := (e.r j').eq_none_or_eq_some
      · rw [extend.d_none_eq_zero K _ _ hj', comp_zero]
      · obtain hk'|⟨k, hk⟩ := (e.r k').eq_none_or_eq_some
        · rw [extend.d_none_eq_zero' K _ _ hk', comp_zero]
        · rw [extend.d_eq K hi hj,
            extend.d_eq K hj hk, assoc, assoc,
            Iso.inv_hom_id_assoc, K.d_comp_d_assoc, zero_comp, comp_zero]

noncomputable def extendXIso {i' : ι'} {i : ι} (h : e.f i = i') :
    (K.extend e).X i' ≅ K.X i :=
  extend.XIso K (e.r_eq_some h)

lemma isZero_extend_X' (i' : ι') (hi' : e.r i' = none) :
    IsZero ((K.extend e).X i') :=
  extend.isZero_X K hi'

lemma isZero_extend_X (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    IsZero ((K.extend e).X i') :=
  K.isZero_extend_X' e i' (by
    obtain hi'|⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
    · exact hi'
    · exfalso
      exact hi' _ (e.f_eq_of_r_eq_some hi))

instance : (K.extend e).IsStrictlySupported e where
  isZero i' hi' := K.isZero_extend_X e i' hi'

lemma extend_d_eq {i' j' : ι'} {i j : ι} (hi : e.f i = i') (hj : e.f j = j') :
    (K.extend e).d i' j' = (K.extendXIso e hi).hom ≫ K.d i j ≫
      (K.extendXIso e hj).inv := by
  apply extend.d_eq

lemma extend_d_from_eq_zero (i' j' : ι') (i : ι) (hi : e.f i = i') (hi' : ¬ c.Rel i (c.next i)) :
    (K.extend e).d i' j' = 0 := by
  obtain hj'|⟨j, hj⟩ := (e.r j').eq_none_or_eq_some
  · exact extend.d_none_eq_zero' _ _ _ hj'
  · rw [extend_d_eq K e hi (e.f_eq_of_r_eq_some hj), K.shape, zero_comp, comp_zero]
    intro hij
    obtain rfl := c.next_eq' hij
    exact hi' hij

lemma extend_d_to_eq_zero (i' j' : ι') (j : ι) (hj : e.f j = j') (hj' : ¬ c.Rel (c.prev j) j) :
    (K.extend e).d i' j' = 0 := by
  obtain hi'|⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
  · exact extend.d_none_eq_zero _ _ _ hi'
  · rw [extend_d_eq K e (e.f_eq_of_r_eq_some hi) hj, K.shape, zero_comp, comp_zero]
    intro hij
    obtain rfl := c.prev_eq' hij
    exact hj' hij

variable {K L M}

noncomputable def extendMap : K.extend e ⟶ L.extend e where
  f _ := extend.mapX φ _
  comm' i' j' _ := by
    dsimp
    by_cases hi : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi
      by_cases hj : ∃ j, e.f j = j'
      · obtain ⟨j, hj⟩ := hj
        rw [K.extend_d_eq e hi hj, L.extend_d_eq e hi hj,
          extend.mapX_some φ (e.r_eq_some hi),
          extend.mapX_some φ (e.r_eq_some hj)]
        simp [extendXIso]
      · have hj' := e.r_eq_none j' (fun j'' hj'' => hj ⟨j'', hj''⟩)
        dsimp [extend]
        rw [extend.d_none_eq_zero' _ _ _ hj', extend.d_none_eq_zero' _ _ _ hj',
          comp_zero, zero_comp]
    · have hi' := e.r_eq_none i' (fun i'' hi'' => hi ⟨i'', hi''⟩)
      dsimp [extend]
      rw [extend.d_none_eq_zero _ _ _ hi', extend.d_none_eq_zero _ _ _ hi',
        comp_zero, zero_comp]

lemma extendMap_f {i : ι} {i' : ι'} (h : e.f i = i') :
    (extendMap φ e).f i' =
      (extendXIso K e h).hom ≫ φ.f i ≫ (extendXIso L e h).inv := by
  dsimp [extendMap]
  rw [extend.mapX_some φ (e.r_eq_some h)]
  rfl

lemma extendMap_f_eq_zero (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    (extendMap φ e).f i' = 0 := by
  dsimp [extendMap]
  rw [extend.mapX_none φ (e.r_eq_none i' hi')]

@[reassoc (attr := simp)]
lemma extendMap_comp_f (i' : ι') :
    (extendMap (φ ≫ φ') e).f i' = (extendMap φ e).f i' ≫ (extendMap φ' e).f i' := by
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · simp [extendMap_f_eq_zero _ e i' (fun i hi => hi' ⟨i, hi⟩)]

@[reassoc (attr := simp)]
lemma extendMap_comp :
    extendMap (φ ≫ φ') e = extendMap φ e ≫ extendMap φ' e := by aesop_cat

variable (K L M)

@[simp]
lemma extendMap_id_f (i' : ι') : (extendMap (𝟙 K) e).f i' = 𝟙 _ := by
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · apply (K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

@[simp]
lemma extendMap_id : extendMap (𝟙 K) e = 𝟙 _ := by aesop_cat

@[simp]
lemma extendMap_zero_f (i' : ι') : (extendMap (0 : K ⟶ L) e).f i' = 0 := by
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · apply (K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

@[simp]
lemma extendMap_zero : extendMap (0 : K ⟶ L) e = 0 := by aesop_cat

end

section

variable [Preadditive C] {K L : HomologicalComplex C c} (φ φ' : K ⟶ L) (e : c.Embedding c')

@[simp]
lemma extendMap_add_f (i' : ι') :
    (extendMap (φ + φ') e).f i' = (extendMap φ e).f i' + (extendMap φ' e).f i' := by
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · apply (K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

@[simp]
lemma extendMap_add : extendMap (0 : K ⟶ L) e = 0 := by aesop_cat

end

end HomologicalComplex

namespace ComplexShape.Embedding

variable (e : Embedding c c') (C : Type*) [Category C] [HasZeroObject C]

@[simps]
noncomputable def extendFunctor [HasZeroMorphisms C] :
    HomologicalComplex C c ⥤ HomologicalComplex C c' where
  obj K := K.extend e
  map φ := HomologicalComplex.extendMap φ e

instance [HasZeroMorphisms C] : (e.extendFunctor C).PreservesZeroMorphisms where

instance [Preadditive C] : (e.extendFunctor C).Additive where

end ComplexShape.Embedding
