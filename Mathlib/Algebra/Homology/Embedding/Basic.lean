/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomologicalComplex

/-! # Embeddings of complex shapes

Given two complexes shapes `c : ComplexShape ι` and `c' : ComplexShape ι'`,
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

## TODO

Define the following:
- the extension functor `e.extendFunctor C : HomologicalComplex C c ⥤ HomologicalComplex C c'`
(extending by the zero object outside of the image of `e.f`);
- assuming `e.IsRelIff`, the restriction functor
`e.restrictionFunctor C : HomologicalComplex C c' ⥤ HomologicalComplex C c`;
- the stupid truncation functor
`e.stupidTruncFunctor C : HomologicalComplex C c' ⥤ HomologicalComplex C c'` which is
the composition of the two previous functors.
- assuming `e.IsTruncGE`, truncation functors
`e.truncGE'Functor C : HomologicalComplex C c' ⥤ HomologicalComplex C c` and
`e.truncGEFunctor C : HomologicalComplex C c' ⥤ HomologicalComplex C c'`, and a natural
transformation `e.πTruncGENatTrans : 𝟭 _ ⟶ e.truncGEFunctor C` which is a quasi-isomorphism
in degrees in the image of `e.f`;
- assuming `e.IsTruncLE`, truncation functors
`e.truncLE'Functor C : HomologicalComplex C c' ⥤ HomologicalComplex C c` and
`e.truncLEFunctor C : HomologicalComplex C c' ⥤ HomologicalComplex C c'`, and a natural
transformation `e.ιTruncLENatTrans : e.truncGEFunctor C ⟶ 𝟭 _` which is a quasi-isomorphism
in degrees in the image of `e.f`;

-/

namespace ComplexShape

variable {ι ι' : Type*} (c : ComplexShape ι) (c' : ComplexShape ι')

/-- An embedding of a complex shape `c : ComplexShape ι` into a complex shape
`c' : ComplexShape ι'` consists of a injective map `f : ι → ι'` which satisfies
to a compatiblity with respect to the relations `c.Rel` and `c'.Rel`. -/
structure Embedding where
  /-- the map between the underlying types of indices -/
  f : ι → ι'
  injective_f : Function.Injective f
  rel {i₁ i₂ : ι} (h : c.Rel i₁ i₂) : c'.Rel (f i₁) (f i₂)

namespace Embedding

variable {c c'}
variable (e : Embedding c c')

/-- An embedding of complex shapes `e` satisfies `e.IsRelIff` if the implication
`e.rel` is an equivalence. -/
class IsRelIff : Prop where
  rel' (i₁ i₂ : ι) (h : c'.Rel (e.f i₁) (e.f i₂)) : c.Rel i₁ i₂

lemma rel_iff [e.IsRelIff] (i₁ i₂ : ι) : c'.Rel (e.f i₁) (e.f i₂) ↔ c.Rel i₁ i₂ := by
  constructor
  · apply IsRelIff.rel'
  · exact e.rel

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
class IsTruncGE extends e.IsRelIff : Prop where
  mem_next {j : ι} {k' : ι'} (h : c'.Rel (e.f j) k') :
    ∃ k, e.f k = k'

/-- The condition that the image of the map `e.f` of an embedding of
complex shapes `e : Embedding c c'` is stable by `c'.prev`. -/
class IsTruncLE extends e.IsRelIff : Prop where
  mem_prev {i' : ι'} {j : ι} (h : c'.Rel i' (e.f j)) :
    ∃ i, e.f i = i'

lemma mem_next [e.IsTruncGE] {j : ι} {k' : ι'} (h : c'.Rel (e.f j) k') : ∃ k, e.f k = k' :=
  IsTruncGE.mem_next h

lemma mem_prev [e.IsTruncLE] {i' : ι'} {j : ι} (h : c'.Rel i' (e.f j)) : ∃ i, e.f i = i' :=
  IsTruncLE.mem_prev h

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

@[simp]
lemma r_f (i : ι) : e.r (e.f i) = some i := r_eq_some _ rfl

lemma f_eq_of_r_eq_some {i : ι} {i' : ι'} (hi : e.r i' = some i) :
    e.f i = i' := by
  by_cases h : ∃ (k : ι), e.f k = i'
  · obtain ⟨k, rfl⟩ := h
    rw [r_f] at hi
    congr 1
    simpa using hi.symm
  · simp [e.r_eq_none i' (by simpa using h)] at hi

/-- The lower boundary of an embedding `e : Embedding c c'`, as a predicate on `ι`.
It is satisfied by `j : ι` when there exists `i' : ι'` not in the image of `e.f`
such that `c'.Rel i' (e.f j)`. -/
def BoundaryGE (j : ι) : Prop :=
  c'.Rel (c'.prev (e.f j)) (e.f j) ∧ ∀ i, ¬c'.Rel (e.f i) (e.f j)

lemma mem_boundaryGE {i' : ι'} {j : ι} (hj : c'.Rel i' (e.f j)) (hi' : ∀ i, e.f i ≠ i') :
    e.BoundaryGE j := by
  constructor
  · simpa only [c'.prev_eq' hj] using hj
  · intro i hi
    apply hi' i
    rw [← c'.prev_eq' hj, c'.prev_eq' hi]

lemma not_mem_next_boundaryGE [e.IsRelIff] {j k : ι} (hk : c.Rel j k) :
    ¬ e.BoundaryGE k := by
  dsimp [BoundaryGE]
  simp only [not_and, not_forall, not_not]
  intro
  exact ⟨j, by simpa only [e.rel_iff] using hk⟩

variable {e} in
lemma BoundaryGE.not_mem {j : ι} (hj : e.BoundaryGE j) {i' : ι'} (hi' : c'.Rel i' (e.f j))
    (a : ι) : e.f a ≠ i' := fun ha =>
  hj.2 a (by simpa only [ha] using hi')

/-- The upper boundary of an embedding `e : Embedding c c'`, as a predicate on `ι`.
It is satisfied by `j : ι` when there exists `k' : ι'` not in the image of `e.f`
such that `c'.Rel (e.f j) k'`. -/
def BoundaryLE (j : ι) : Prop :=
  c'.Rel (e.f j) (c'.next (e.f j)) ∧ ∀ k, ¬c'.Rel (e.f j) (e.f k)

lemma mem_boundaryLE {j : ι} {k' : ι'} (hj : c'.Rel (e.f j) k') (hk' : ∀ k, e.f k ≠ k') :
    e.BoundaryLE j := by
  constructor
  · simpa only [c'.next_eq' hj] using hj
  · intro k hk
    apply hk' k
    rw [← c'.next_eq' hj, c'.next_eq' hk]

lemma not_mem_prev_boundaryLE [e.IsRelIff] {i j : ι} (hi : c.Rel i j) :
    ¬ e.BoundaryLE i := by
  dsimp [BoundaryLE]
  simp only [not_and, not_forall, not_not]
  intro
  exact ⟨j, by simpa only [e.rel_iff] using hi⟩

variable {e} in
lemma BoundaryLE.not_mem {j : ι} (hj : e.BoundaryLE j) {k' : ι'} (hk' : c'.Rel (e.f j) k')
    (a : ι) : e.f a ≠ k' := fun ha =>
  hj.2 a (by simpa only [ha] using hk')

end Embedding

/-- The obvious embedding from `up ℕ` to `up ℤ`. -/
@[simps!]
def embeddingUpNat : Embedding (up ℕ) (up ℤ) :=
  Embedding.mk' _ _ (fun n => n)
    (fun _ _ h => by simpa using h)
    (by dsimp; omega)

/-- The embedding from `down ℕ` to `up ℤ` with sends `n` to `-n`. -/
@[simps!]
def embeddingDownNat : Embedding (down ℕ) (up ℤ) :=
  Embedding.mk' _ _ (fun n => -n)
    (fun _ _ h => by simpa using h)
    (by dsimp; omega)

instance : embeddingUpNat.IsRelIff := by dsimp [embeddingUpNat]; infer_instance

instance : embeddingDownNat.IsRelIff := by dsimp [embeddingDownNat]; infer_instance

instance : embeddingUpNat.IsTruncGE where
  mem_next {j _} h := ⟨j + 1, h⟩

instance : embeddingDownNat.IsTruncLE where
  mem_prev {i j} h := ⟨j + 1, by dsimp at h ⊢; omega⟩

lemma boundaryGE_embeddingUpNat_iff (n : ℕ) :
    embeddingUpNat.BoundaryGE n ↔ n = 0 := by
  constructor
  · intro h
    obtain _|n := n
    · rfl
    · simpa using h.2 n
  · rintro rfl
    constructor
    · simp
    · intro i hi
      dsimp at hi
      omega

lemma boundaryLE_embeddingDownNat_iff (n : ℕ) :
    embeddingDownNat.BoundaryLE n ↔ n = 0 := by
  constructor
  · intro h
    obtain _|n := n
    · rfl
    · simpa using h.2 n
  · rintro rfl
    constructor
    · simp
    · intro i hi
      dsimp at hi
      omega

end ComplexShape

lemma Option.eq_none_or_eq_some {ι : Type*} (x : Option ι) :
    x = none ∨ ∃ y, x = some y := by
  cases x <;> aesop
