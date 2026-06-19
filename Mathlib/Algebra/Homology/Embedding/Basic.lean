/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.Push

/-! # Embeddings of complex shapes

Given two complex shapes `c : ComplexShape ι` and `c' : ComplexShape ι'`,
an embedding from `c` to `c'` (`e : c.Embedding c'`) consists of the data
of an injective map `f : ι → ι'` such that for all `i₁ i₂ : ι`,
`c.Rel i₁ i₂` implies `c'.Rel (e.f i₁) (e.f i₂)`.
We define a type class `e.IsRelIff` to express that this implication is an equivalence.
Other type classes `e.IsTruncLE` and `e.IsTruncGE` are introduced in order to
formalize truncation functors.

This notion first appeared in the Liquid Tensor Experiment, and was developed there
mostly by Johan Commelin, Adam Topaz and Joël Riou. It shall be used in order to
relate the categories `CochainComplex C ℕ` and `ChainComplex C ℕ` to `CochainComplex C ℤ`.
It shall also be used in the construction of the canonical t-structure on the derived
category of an abelian category (TODO).

## Description of the API

- The extension functor `e.extendFunctor C : HomologicalComplex C c ⥤ HomologicalComplex C c'`
  (extending by the zero object outside of the image of `e.f`) is defined in
  the file `Embedding.Extend`;
- assuming `e.IsRelIff`, the restriction functor
  `e.restrictionFunctor C : HomologicalComplex C c' ⥤ HomologicalComplex C c`
  is defined in the file `Embedding.Restriction`;
- the stupid truncation functor
  `e.stupidTruncFunctor C : HomologicalComplex C c' ⥤ HomologicalComplex C c'`
  which is the composition of the two previous functors is defined in the file
  `Embedding.StupidTrunc`.
- assuming `e.IsTruncGE`, we have truncation functors
  `e.truncGE'Functor C : HomologicalComplex C c' ⥤ HomologicalComplex C c` and
  `e.truncGEFunctor C : HomologicalComplex C c' ⥤ HomologicalComplex C c'`
  (see the file `Embedding.TruncGE`), and a natural
  transformation `e.πTruncGENatTrans : 𝟭 _ ⟶ e.truncGEFunctor C` which is a quasi-isomorphism
  in degrees in the image of `e.f` (TODO);
- assuming `e.IsTruncLE`, we have truncation functors
  `e.truncLE'Functor C : HomologicalComplex C c' ⥤ HomologicalComplex C c` and
  `e.truncLEFunctor C : HomologicalComplex C c' ⥤ HomologicalComplex C c'`, and a natural
  transformation `e.ιTruncLENatTrans : e.truncGEFunctor C ⟶ 𝟭 _` which is a quasi-isomorphism
  in degrees in the image of `e.f` (TODO);

-/

@[expose] public section

assert_not_exists Nat.instAddMonoidWithOne Nat.instMulZeroClass

variable {ι ι' : Type*} (c : ComplexShape ι) (c' : ComplexShape ι')

namespace ComplexShape

/-- An embedding of a complex shape `c : ComplexShape ι` into a complex shape
`c' : ComplexShape ι'` consists of an injective map `f : ι → ι'` which satisfies
a compatibility with respect to the relations `c.Rel` and `c'.Rel`. -/
structure Embedding where
  /-- the map between the underlying types of indices -/
  f : ι → ι'
  injective_f : Function.Injective f
  rel {i₁ i₂ : ι} (h : c.Rel i₁ i₂) : c'.Rel (f i₁) (f i₂)

namespace Embedding

variable {c c'}
variable (e : Embedding c c')

/-- The opposite embedding in `Embedding c.symm c'.symm` of `e : Embedding c c'`. -/
@[simps]
def op : Embedding c.symm c'.symm where
  f := e.f
  injective_f := e.injective_f
  rel h := e.rel h

/-- An embedding of complex shapes `e` satisfies `e.IsRelIff` if the implication
`e.rel` is an equivalence. -/
class IsRelIff : Prop where
  rel' (i₁ i₂ : ι) (h : c'.Rel (e.f i₁) (e.f i₂)) : c.Rel i₁ i₂

lemma rel_iff [e.IsRelIff] (i₁ i₂ : ι) : c'.Rel (e.f i₁) (e.f i₂) ↔ c.Rel i₁ i₂ := by
  constructor
  · apply IsRelIff.rel'
  · exact e.rel

instance [e.IsRelIff] : e.op.IsRelIff where
  rel' i₁ i₂ h := (e.rel_iff i₂ i₁).1 h

section

variable (c c')
variable (f : ι → ι') (hf : Function.Injective f)
    (iff : ∀ (i₁ i₂ : ι), c.Rel i₁ i₂ ↔ c'.Rel (f i₁) (f i₂))

/-- Constructor for embeddings between complex shapes when we have an equivalence
`∀ (i₁ i₂ : ι), c.Rel i₁ i₂ ↔ c'.Rel (f i₁) (f i₂)`. -/
@[simps]
def mk' : Embedding c c' where
  f := f
  injective_f := hf
  rel h := (iff _ _).1 h

instance : (mk' c c' f hf iff).IsRelIff where
  rel' _ _ h := (iff _ _).2 h

end

/-- The condition that the image of the map `e.f` of an embedding of
complex shapes `e : Embedding c c'` is stable by `c'.next`. -/
class IsTruncGE : Prop extends e.IsRelIff where
  mem_next {j : ι} {k' : ι'} (h : c'.Rel (e.f j) k') :
    ∃ k, e.f k = k'

lemma mem_next [e.IsTruncGE] {j : ι} {k' : ι'} (h : c'.Rel (e.f j) k') : ∃ k, e.f k = k' :=
  IsTruncGE.mem_next h

/-- The condition that the image of the map `e.f` of an embedding of
complex shapes `e : Embedding c c'` is stable by `c'.prev`. -/
class IsTruncLE : Prop extends e.IsRelIff where
  mem_prev {i' : ι'} {j : ι} (h : c'.Rel i' (e.f j)) :
    ∃ i, e.f i = i'

lemma mem_prev [e.IsTruncLE] {i' : ι'} {j : ι} (h : c'.Rel i' (e.f j)) : ∃ i, e.f i = i' :=
  IsTruncLE.mem_prev h

instance [e.IsTruncGE] : e.op.IsTruncLE where
  mem_prev h := e.mem_next h

instance [e.IsTruncLE] : e.op.IsTruncGE where
  mem_next h := e.mem_prev h

open Classical in
/-- The map `ι' → Option ι` which sends `e.f i` to `some i` and the other elements to `none`. -/
noncomputable def r (i' : ι') : Option ι :=
  if h : ∃ (i : ι), e.f i = i'
  then some h.choose
  else none

lemma r_eq_some {i : ι} {i' : ι'} (hi : e.f i = i') :
    e.r i' = some i := by
  have h : ∃ (i : ι), e.f i = i' := ⟨i, hi⟩
  have : h.choose = i := e.injective_f (h.choose_spec.trans (hi.symm))
  dsimp [r]
  rw [dif_pos ⟨i, hi⟩, this]

lemma r_eq_none (i' : ι') (hi : ∀ i, e.f i ≠ i') :
    e.r i' = none :=
  dif_neg (by
    rintro ⟨i, hi'⟩
    exact hi i hi')

@[simp] lemma r_f (i : ι) : e.r (e.f i) = some i := r_eq_some _ rfl

lemma f_eq_of_r_eq_some {i : ι} {i' : ι'} (hi : e.r i' = some i) :
    e.f i = i' := by
  by_cases h : ∃ (k : ι), e.f k = i'
  · obtain ⟨k, rfl⟩ := h
    rw [r_f] at hi
    congr 1
    simpa using hi.symm
  · simp [e.r_eq_none i' (by simpa using h)] at hi

end Embedding

section

variable {A : Type*} [AddCommSemigroup A] [IsRightCancelAdd A] [One A]

set_option backward.defeqAttrib.useBackward true in
/-- The embedding from `up' a` to itself via (· + b). -/
@[simps!]
def embeddingUp'Add (a b : A) : Embedding (up' a) (up' a) :=
  Embedding.mk' _ _ (· + b)
    (fun _ _ h => by simpa using h)
    (by dsimp; simp_rw [add_right_comm _ b a, add_right_cancel_iff, implies_true])

instance (a b : A) : (embeddingUp'Add a b).IsRelIff := by dsimp [embeddingUp'Add]; infer_instance

instance (a b : A) : (embeddingUp'Add a b).IsTruncGE where
  mem_next {j _} h := ⟨j + a, (add_right_comm _ _ _).trans h⟩

set_option backward.defeqAttrib.useBackward true in
/-- The embedding from `down' a` to itself via (· + b). -/
@[simps!]
def embeddingDown'Add (a b : A) : Embedding (down' a) (down' a) :=
  Embedding.mk' _ _ (· + b)
    (fun _ _ h => by simpa using h)
    (by dsimp; simp_rw [add_right_comm _ b a, add_right_cancel_iff, implies_true])

instance (a b : A) : (embeddingDown'Add a b).IsRelIff := by
  dsimp [embeddingDown'Add]; infer_instance

instance (a b : A) : (embeddingDown'Add a b).IsTruncLE where
  mem_prev {_ x} h := ⟨x + a, (add_right_comm _ _ _).trans h⟩

end

set_option backward.defeqAttrib.useBackward true in
/-- The obvious embedding from `up ℕ` to `up ℤ`. -/
@[simps!]
def embeddingUpNat : Embedding (up ℕ) (up ℤ) :=
  Embedding.mk' _ _ (fun n => n)
    (fun _ _ h => by simpa using h)
    (by dsimp; lia)

instance : embeddingUpNat.IsRelIff := by dsimp [embeddingUpNat]; infer_instance

instance : embeddingUpNat.IsTruncGE where
  mem_next {j _} h := ⟨j + 1, h⟩

set_option backward.defeqAttrib.useBackward true in
/-- The embedding from `down ℕ` to `up ℤ` with sends `n` to `-n`. -/
@[simps!]
def embeddingDownNat : Embedding (down ℕ) (up ℤ) :=
  Embedding.mk' _ _ (fun n => -n)
    (fun _ _ h => by simpa using h)
    (by dsimp; lia)

instance : embeddingDownNat.IsRelIff := by dsimp [embeddingDownNat]; infer_instance

set_option backward.defeqAttrib.useBackward true in
instance : embeddingDownNat.IsTruncLE where
  mem_prev {i j} h := ⟨j + 1, by dsimp at h ⊢; lia⟩

variable (p : ℤ)

set_option backward.defeqAttrib.useBackward true in
/-- The embedding from `up ℕ` to `up ℤ` which sends `n : ℕ` to `p + n`. -/
@[simps!]
def embeddingUpIntGE : Embedding (up ℕ) (up ℤ) :=
  Embedding.mk' _ _ (fun n => p + n)
    (fun _ _ h => by dsimp at h; lia)
    (by dsimp; lia)

instance : (embeddingUpIntGE p).IsRelIff := by dsimp [embeddingUpIntGE]; infer_instance

set_option backward.defeqAttrib.useBackward true in
instance : (embeddingUpIntGE p).IsTruncGE where
  mem_next {j _} h := ⟨j + 1, by dsimp at h ⊢; lia⟩

set_option backward.defeqAttrib.useBackward true in
/-- The embedding from `down ℕ` to `up ℤ` which sends `n : ℕ` to `p - n`. -/
@[simps!]
def embeddingUpIntLE : Embedding (down ℕ) (up ℤ) :=
  Embedding.mk' _ _ (fun n => p - n)
    (fun _ _ h => by dsimp at h; lia)
    (by dsimp; lia)

instance : (embeddingUpIntLE p).IsRelIff := by dsimp [embeddingUpIntLE]; infer_instance

set_option backward.defeqAttrib.useBackward true in
instance : (embeddingUpIntLE p).IsTruncLE where
  mem_prev {_ k} h := ⟨k + 1, by dsimp at h ⊢; lia⟩

set_option backward.defeqAttrib.useBackward true in
lemma notMem_range_embeddingUpIntLE_iff (n : ℤ) :
    (∀ (i : ℕ), (embeddingUpIntLE p).f i ≠ n) ↔ p < n := by
  constructor
  · intro h
    by_contra
    exact h (p - n).natAbs (by simp; lia)
  · intros
    dsimp
    lia

set_option backward.defeqAttrib.useBackward true in
lemma notMem_range_embeddingUpIntGE_iff (n : ℤ) :
    (∀ (i : ℕ), (embeddingUpIntGE p).f i ≠ n) ↔ n < p := by
  constructor
  · intro h
    by_contra
    exact h (n - p).natAbs (by simp; lia)
  · intros
    dsimp
    lia

end ComplexShape
