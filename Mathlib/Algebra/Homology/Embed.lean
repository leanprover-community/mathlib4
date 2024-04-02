import Mathlib.Algebra.Homology.HomologicalComplex

-- mostly from LTE

open CategoryTheory Limits ZeroObject Category

variable {ι ι' : Type*} (c : ComplexShape ι) (c' : ComplexShape ι')

lemma Option.eq_none_or_eq_some (x : Option ι) :
    x = none ∨ ∃ y, x = some y := by
  cases x
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

namespace ComplexShape

structure Embed where
  f : ι → ι'
  injective_f : Function.Injective f
  rel {i₁ i₂ : ι} (h : c.Rel i₁ i₂) : c'.Rel (f i₁) (f i₂)

namespace Embed

variable {c c'}
variable (e : Embed c c')

open Classical in
noncomputable def r (i' : ι') : Option ι :=
  if h : ∃ (i : ι), e.f i = i'
  then some h.choose
  else none

lemma r_eq_some (i : ι) (i' : ι') (hi : e.f i = i') :
    e.r i' = some i := by
  have h : ∃ (i : ι), e.f i = i' := ⟨i, hi⟩
  have : h.choose = i := e.injective_f (h.choose_spec.trans (hi.symm))
  dsimp [r]
  rw [dif_pos ⟨i, hi⟩, this]

lemma f_eq_of_r_eq_some (i : ι) (i' : ι') (hi : e.r i' = some i) :
    e.f i = i' := by
  by_cases h : ∃ (k : ι), e.f k = i'
  · obtain ⟨k, hk⟩ := h
    have : some i = some k := by
      rw [← e.r_eq_some _ _ hk, hi]
    rw [← hk]
    congr 1
    simpa using this
  · simp [r, dif_neg h] at hi

end Embed

end ComplexShape

namespace HomologicalComplex

variable {c c'} {C : Type*} [Category C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K : HomologicalComplex C c) (e : c.Embed c')

namespace extend

noncomputable def X : Option ι → C
  | some x => K.X x
  | none => 0

noncomputable def XIso (i : Option ι) (j : ι) (hj : i = some j) :
    X K i ≅ K.X j := eqToIso (by subst hj; rfl)

lemma isZero_X (i : Option ι) (hi : i = none) :
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

lemma d_eq (i j : Option ι) (a b : ι)
    (hi : i = some a) (hj : j = some b) :
    d K i j = (XIso K i a hi).hom ≫ K.d a b ≫ (XIso K j b hj).inv := by
  subst hi hj
  dsimp [XIso, d]
  erw [id_comp, comp_id]

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
      · rw [extend.d_eq K _ _ _ _ hi hj,K.shape, zero_comp, comp_zero]
        obtain rfl := e.f_eq_of_r_eq_some _ _ hi
        obtain rfl := e.f_eq_of_r_eq_some _ _ hj
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
        · rw [extend.d_eq K _ _ _ _ hi hj,
            extend.d_eq K _ _ _ _ hj hk, assoc, assoc,
            Iso.inv_hom_id_assoc, K.d_comp_d_assoc, zero_comp, comp_zero]

noncomputable def extendXIso (i' : ι') (i : ι) (h : e.f i = i') :
    (K.extend e).X i' ≅ K.X i :=
  extend.XIso K _ _ (e.r_eq_some _ _ h)

lemma isZero_extend_X (i' : ι') (hi' : e.r i' = none) :
    IsZero ((K.extend e).X i') :=
  extend.isZero_X K _ hi'

lemma extend_d_eq (i' j' : ι') (i j : ι) (hi : e.f i = i') (hj : e.f j = j') :
    (K.extend e).d i' j' = (K.extendXIso e i' i hi).hom ≫ K.d i j ≫
      (K.extendXIso e j' j hj).inv := by
  apply extend.d_eq

end HomologicalComplex
