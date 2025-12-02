/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.IsSupported
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Opposite

/-!
# The extension of a homological complex by an embedding of complex shapes

Given an embedding `e : Embedding c c'` of complex shapes,
and `K : HomologicalComplex C c`, we define `K.extend e : HomologicalComplex C c'`, and this
leads to a functor `e.extendFunctor C : HomologicalComplex C c ⥤ HomologicalComplex C c'`.

This construction first appeared in the Liquid Tensor Experiment.

-/

@[expose] public section

open CategoryTheory Category Limits ZeroObject

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace HomologicalComplex

variable {C : Type*} [Category C] [HasZeroObject C]

section

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

namespace extend

/-- Auxiliary definition for the `X` field of `HomologicalComplex.extend`. -/
noncomputable def X : Option ι → C
  | some x => K.X x
  | none => 0

/-- The isomorphism `X K i ≅ K.X j` when `i = some j`. -/
noncomputable def XIso {i : Option ι} {j : ι} (hj : i = some j) :
    X K i ≅ K.X j := eqToIso (by subst hj; rfl)

lemma isZero_X {i : Option ι} (hi : i = none) :
    IsZero (X K i) := by
  subst hi
  exact Limits.isZero_zero _

/-- The canonical isomorphism `X K.op i ≅ Opposite.op (X K i)`. -/
noncomputable def XOpIso (i : Option ι) : X K.op i ≅ Opposite.op (X K i) :=
  match i with
  | some _ => Iso.refl _
  | none => IsZero.iso (isZero_X _ rfl) (isZero_X K rfl).op

/-- Auxiliary definition for the `d` field of `HomologicalComplex.extend`. -/
noncomputable def d : ∀ (i j : Option ι), extend.X K i ⟶ extend.X K j
  | none, _ => 0
  | some i, some j => K.d i j
  | some _, none => 0

lemma d_none_eq_zero (i j : Option ι) (hi : i = none) :
    d K i j = 0 := by subst hi; rfl

lemma d_none_eq_zero' (i j : Option ι) (hj : j = none) :
    d K i j = 0 := by subst hj; cases i <;> rfl

lemma d_eq {i j : Option ι} {a b : ι} (hi : i = some a) (hj : j = some b) :
    d K i j = (XIso K hi).hom ≫ K.d a b ≫ (XIso K hj).inv := by
  subst hi hj
  simp [XIso, X, d]

@[reassoc]
lemma XOpIso_hom_d_op (i j : Option ι) :
    (XOpIso K i).hom ≫ (d K j i).op =
      d K.op i j ≫ (XOpIso K j).hom :=
  match i, j with
  | none, _ => by
      simp only [d_none_eq_zero, d_none_eq_zero', comp_zero, zero_comp, op_zero]
  | some i, some j => by
      dsimp [XOpIso]
      simp only [d_eq _ rfl rfl, op_comp, assoc, id_comp, comp_id]
      rfl
  | some _, none => by
      simp only [d_none_eq_zero, d_none_eq_zero', comp_zero, zero_comp, op_zero]

variable {K L}

/-- Auxiliary definition for `HomologicalComplex.extendMap`. -/
noncomputable def mapX : ∀ (i : Option ι), X K i ⟶ X L i
  | some i => φ.f i
  | none => 0

lemma mapX_some {i : Option ι} {a : ι} (hi : i = some a) :
    mapX φ i = (XIso K hi).hom ≫ φ.f a ≫ (XIso L hi).inv := by
  subst hi
  dsimp [XIso, X]
  rw [id_comp, comp_id]
  rfl

lemma mapX_none {i : Option ι} (hi : i = none) :
    mapX φ i = 0 := by subst hi; rfl

end extend

/-- Given `K : HomologicalComplex C c` and `e : c.Embedding c'`,
this is the extension of `K` in `HomologicalComplex C c'`: it is
zero in the degrees that are not in the image of `e.f`. -/
noncomputable def extend : HomologicalComplex C c' where
  X i' := extend.X K (e.r i')
  d i' j' := extend.d K (e.r i') (e.r j')
  shape i' j' h := by
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
    obtain hi'|⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
    · rw [extend.d_none_eq_zero K _ _ hi', zero_comp]
    · obtain hj'|⟨j, hj⟩ := (e.r j').eq_none_or_eq_some
      · rw [extend.d_none_eq_zero K _ _ hj', comp_zero]
      · obtain hk'|⟨k, hk⟩ := (e.r k').eq_none_or_eq_some
        · rw [extend.d_none_eq_zero' K _ _ hk', comp_zero]
        · rw [extend.d_eq K hi hj, extend.d_eq K hj hk, assoc, assoc,
            Iso.inv_hom_id_assoc, K.d_comp_d_assoc, zero_comp, comp_zero]

/-- The isomorphism `(K.extend e).X i' ≅ K.X i` when `e.f i = i'`. -/
noncomputable def extendXIso {i' : ι'} {i : ι} (h : e.f i = i') :
    (K.extend e).X i' ≅ K.X i :=
  extend.XIso K (e.r_eq_some h)

lemma isZero_extend_X' (i' : ι') (hi' : e.r i' = none) :
    IsZero ((K.extend e).X i') :=
  extend.isZero_X K hi'

lemma isZero_extend_X (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    IsZero ((K.extend e).X i') :=
  K.isZero_extend_X' e i' (ComplexShape.Embedding.r_eq_none e i' hi')

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

/-- Given an embedding `e : c.Embedding c'` of complexes shapes, this is the
morphism `K.extend e ⟶ L.extend e` induced by a morphism `K ⟶ L` in
`HomologicalComplex C c`. -/
noncomputable def extendMap : K.extend e ⟶ L.extend e where
  f _ := extend.mapX φ _
  comm' i' j' _ := by
    by_cases hi : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi
      by_cases hj : ∃ j, e.f j = j'
      · obtain ⟨j, hj⟩ := hj
        rw [K.extend_d_eq e hi hj, L.extend_d_eq e hi hj,
          extend.mapX_some φ (e.r_eq_some hi),
          extend.mapX_some φ (e.r_eq_some hj)]
        simp only [extendXIso, assoc, Iso.inv_hom_id_assoc, Hom.comm_assoc]
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

@[reassoc, simp]
lemma extendMap_comp :
    extendMap (φ ≫ φ') e = extendMap φ e ≫ extendMap φ' e := by
  ext i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · simp [extendMap_f_eq_zero _ e i' (fun i hi => hi' ⟨i, hi⟩)]

variable (K L M)

lemma extendMap_id_f (i' : ι') : (extendMap (𝟙 K) e).f i' = 𝟙 _ := by
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · apply (K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

@[simp]
lemma extendMap_id : extendMap (𝟙 K) e = 𝟙 _ := by
  ext i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · apply (K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

@[simp]
lemma extendMap_zero : extendMap (0 : K ⟶ L) e = 0 := by
  ext i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · apply (K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

/-- The canonical isomorphism `K.op.extend e.op ≅ (K.extend e).op`. -/
noncomputable def extendOpIso : K.op.extend e.op ≅ (K.extend e).op :=
  Hom.isoOfComponents (fun _ ↦ extend.XOpIso _ _) (fun _ _ _ ↦
    extend.XOpIso_hom_d_op _ _ _)

@[reassoc]
lemma extend_op_d (i' j' : ι') :
    (K.op.extend e.op).d i' j' =
      (K.extendOpIso e).hom.f i' ≫ ((K.extend e).d j' i').op ≫
        (K.extendOpIso e).inv.f j' := by
  have := (K.extendOpIso e).inv.comm i' j'
  dsimp at this
  rw [← this, ← comp_f_assoc, Iso.hom_inv_id, id_f, id_comp]

end

@[simp]
lemma extendMap_add [Preadditive C] {K L : HomologicalComplex C c} (φ φ' : K ⟶ L)
    (e : c.Embedding c') : extendMap (φ + φ' : K ⟶ L) e = extendMap φ e + extendMap φ' e := by
  ext i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · apply (K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

section

variable [HasZeroMorphisms C] [DecidableEq ι]
  (e : c.Embedding c') (X : C)

@[simp]
lemma extend_single_d (i : ι) (j' k' : ι') :
    (((single C c i).obj X).extend e).d j' k' = 0 := by
  by_cases hj : ∃ j, e.f j = j'
  · obtain ⟨j, rfl⟩ := hj
    by_cases hk : ∃ k, e.f k = k'
    · obtain ⟨k, rfl⟩ := hk
      simp [extend_d_eq _ _ rfl rfl]
    · exact IsZero.eq_of_tgt (isZero_extend_X _ _ _ (by tauto)) _ _
  · exact IsZero.eq_of_src (isZero_extend_X _ _ _ (by tauto)) _ _

variable [DecidableEq ι'] (i : ι) (i' : ι')

/-- The extension of a single complex is a single complex. -/
noncomputable def extendSingleIso (h : e.f i = i') :
    ((single C c i).obj X).extend e ≅ (single C c' i').obj X where
  hom :=
    mkHomToSingle
      ((((single C c i).obj X).extendXIso e h).hom ≫ (singleObjXSelf c i X).hom) (by simp)
  inv :=
    mkHomFromSingle
      ((singleObjXSelf c i X).inv ≫ (((single C c i).obj X).extendXIso e h).inv) (by simp)
  hom_inv_id := by
    ext j'
    by_cases hj : ∃ j, e.f j = j'
    · obtain ⟨j, hj⟩ := hj
      by_cases hij : j = i
      · obtain rfl : i' = j' := by rw [← hj, hij, h]
        simp
      · exact ((isZero_single_obj_X _ _ _ _ hij).of_iso
          (((single C c i).obj X).extendXIso e hj)).eq_of_src _ _
    · exact IsZero.eq_of_src (isZero_extend_X _ _ _ (by tauto)) _ _

@[reassoc]
lemma extendSingleIso_hom_f (h : e.f i = i') :
    (extendSingleIso e X i i' h).hom.f i' =
      (((single C c i).obj X).extendXIso e h).hom ≫ (singleObjXSelf c i X).hom ≫
        (singleObjXSelf c' i' X).inv := by
  simp [extendSingleIso]

@[reassoc]
lemma extendSingleIso_inv_f (h : e.f i = i') :
    (extendSingleIso e X i i' h).inv.f i' =
      (singleObjXSelf c' i' X).hom ≫ (singleObjXSelf c i X).inv ≫
        (((single C c i).obj X).extendXIso e h).inv := by
  simp [extendSingleIso]

end

end HomologicalComplex

namespace ComplexShape.Embedding

variable (e : Embedding c c') (C : Type*) [Category C] [HasZeroObject C]

/-- Given an embedding `e : c.Embedding c'` of complex shapes, this is
the functor `HomologicalComplex C c ⥤ HomologicalComplex C c'` which
extend complexes along `e`: the extended complexes are zero
in the degrees that are not in the image of `e.f`. -/
@[simps]
noncomputable def extendFunctor [HasZeroMorphisms C] :
    HomologicalComplex C c ⥤ HomologicalComplex C c' where
  obj K := K.extend e
  map φ := HomologicalComplex.extendMap φ e

instance [HasZeroMorphisms C] : (e.extendFunctor C).PreservesZeroMorphisms where

instance [Preadditive C] : (e.extendFunctor C).Additive where

end ComplexShape.Embedding
