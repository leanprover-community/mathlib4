/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
<<<<<<< HEAD
import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
=======
import Mathlib.Algebra.Homology.ComplexShape
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Ring.Int.Defs
>>>>>>> origin/ext-change-of-universes

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

variable {ι ι' : Type*} (c : ComplexShape ι) (c' : ComplexShape ι')

namespace ComplexShape

/-- An embedding of a complex shape `c : ComplexShape ι` into a complex shape
`c' : ComplexShape ι'` consists of a injective map `f : ι → ι'` which satisfies
<<<<<<< HEAD
to a compatiblity with respect to the relations `c.Rel` and `c'.Rel`. -/
=======
a compatibility with respect to the relations `c.Rel` and `c'.Rel`. -/
>>>>>>> origin/ext-change-of-universes
structure Embedding where
  /-- the map between the underlying types of indices -/
  f : ι → ι'
  injective_f : Function.Injective f
  rel {i₁ i₂ : ι} (h : c.Rel i₁ i₂) : c'.Rel (f i₁) (f i₂)

namespace Embedding

variable {c c'}
variable (e : Embedding c c')

<<<<<<< HEAD
=======
/-- The opposite embedding in `Embedding c.symm c'.symm` of `e : Embedding c c'`. -/
>>>>>>> origin/ext-change-of-universes
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

<<<<<<< HEAD
instance [e.IsRelIff] : e.op.IsRelIff where
  rel' _ _ h := (e.rel_iff _ _).1 h

=======
>>>>>>> origin/ext-change-of-universes
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

<<<<<<< HEAD
=======
lemma mem_next [e.IsTruncGE] {j : ι} {k' : ι'} (h : c'.Rel (e.f j) k') : ∃ k, e.f k = k' :=
  IsTruncGE.mem_next h

>>>>>>> origin/ext-change-of-universes
/-- The condition that the image of the map `e.f` of an embedding of
complex shapes `e : Embedding c c'` is stable by `c'.prev`. -/
class IsTruncLE extends e.IsRelIff : Prop where
  mem_prev {i' : ι'} {j : ι} (h : c'.Rel i' (e.f j)) :
    ∃ i, e.f i = i'

<<<<<<< HEAD
lemma mem_next [e.IsTruncGE] {j : ι} {k' : ι'} (h : c'.Rel (e.f j) k') : ∃ k, e.f k = k' :=
  IsTruncGE.mem_next h

lemma _root_.ComplexShape.next_eq_self' (c : ComplexShape ι) (j : ι) (hj : ∀ k, ¬ c.Rel j k) :
    c.next j = j :=
  dif_neg (by simpa using hj)

lemma _root_.ComplexShape.prev_eq_self' (c : ComplexShape ι) (j : ι) (hj : ∀ i, ¬ c.Rel i j) :
    c.prev j = j :=
  dif_neg (by simpa using hj)

lemma _root_.ComplexShape.next_eq_self (c : ComplexShape ι) (j : ι) (hj : ¬ c.Rel j (c.next j)) :
    c.next j = j :=
  c.next_eq_self' j (fun k hk' => hj (by simpa only [c.next_eq' hk'] using hk'))

lemma _root_.ComplexShape.prev_eq_self (c : ComplexShape ι) (j : ι) (hj : ¬ c.Rel (c.prev j) j) :
    c.prev j = j :=
  c.prev_eq_self' j (fun k hk' => hj (by simpa only [c.prev_eq' hk'] using hk'))

lemma next_f [e.IsTruncGE] {j k : ι} (hjk : c.next j = k) : c'.next (e.f j) = e.f k := by
  by_cases hj : c'.Rel (e.f j) (c'.next (e.f j))
  · obtain ⟨k', hk'⟩ := e.mem_next hj
    rw [← hk', e.rel_iff] at hj
    rw [← hk', ← c.next_eq' hj, hjk]
  · rw [c'.next_eq_self _ hj, ← hjk, c.next_eq_self j]
    intro hj'
    apply hj
    rw [← e.rel_iff] at hj'
    simpa only [c'.next_eq' hj'] using hj'

lemma mem_prev [e.IsTruncLE] {i' : ι'} {j : ι} (h : c'.Rel i' (e.f j)) : ∃ i, e.f i = i' :=
  IsTruncLE.mem_prev h

instance [e.IsTruncLE] : e.op.IsTruncGE where
  mem_next h := e.mem_prev h

instance [e.IsTruncGE] : e.op.IsTruncLE where
  mem_prev h := e.mem_next h

=======
lemma mem_prev [e.IsTruncLE] {i' : ι'} {j : ι} (h : c'.Rel i' (e.f j)) : ∃ i, e.f i = i' :=
  IsTruncLE.mem_prev h

>>>>>>> origin/ext-change-of-universes
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

<<<<<<< HEAD
@[simp]
lemma r_f (i : ι) : e.r (e.f i) = some i := r_eq_some _ rfl
=======
@[simp] lemma r_f (i : ι) : e.r (e.f i) = some i := r_eq_some _ rfl
>>>>>>> origin/ext-change-of-universes

lemma f_eq_of_r_eq_some {i : ι} {i' : ι'} (hi : e.r i' = some i) :
    e.f i = i' := by
  by_cases h : ∃ (k : ι), e.f k = i'
  · obtain ⟨k, rfl⟩ := h
    rw [r_f] at hi
    congr 1
    simpa using hi.symm
  · simp [e.r_eq_none i' (by simpa using h)] at hi

<<<<<<< HEAD
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

lemma not_mem_next_boundaryGE' [e.IsRelIff] {j k : ι} (hj : ¬ e.BoundaryGE j) (hk : c.next j = k) :
    ¬ e.BoundaryGE k := by
  by_cases hjk : c.Rel j k
  · exact e.not_mem_next_boundaryGE hjk
  · subst hk
    simpa only [c.next_eq_self j hjk] using hj

variable {e} in
lemma BoundaryGE.not_mem {j : ι} (hj : e.BoundaryGE j) {i' : ι'} (hi' : c'.Rel i' (e.f j))
    (a : ι) : e.f a ≠ i' := fun ha =>
  hj.2 a (by simpa only [ha] using hi')

lemma prev_f_of_not_mem_boundaryGE [e.IsRelIff] {i j : ι} (hij : c.prev j = i)
    (hj : ¬ e.BoundaryGE j) :
    c'.prev (e.f j) = e.f i := by
  by_cases hij' : c.Rel i j
  · exact c'.prev_eq' (by simpa only [e.rel_iff] using hij')
  · obtain rfl : j = i := by
      simpa only [c.prev_eq_self j (by simpa only [hij] using hij')] using hij
    apply c'.prev_eq_self
    intro hj'
    simp only [BoundaryGE, not_and, not_forall, not_not] at hj
    obtain ⟨i, hi⟩ := hj hj'
    rw [e.rel_iff] at hi
    rw [c.prev_eq' hi] at hij
    exact hij' (by simpa only [hij] using hi)

variable {e} in
lemma BoundaryGE.false {j : ι} (hj : e.BoundaryGE j) [e.IsTruncLE] : False := by
  obtain ⟨i, hi⟩ := e.mem_prev hj.1
  exact hj.2 i (by simpa only [hi] using hj.1)

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

variable {e} in
lemma BoundaryLE.false {j : ι} (hj : e.BoundaryLE j) [e.IsTruncGE] : False := by
  obtain ⟨i, hi⟩ := e.mem_next hj.1
  exact hj.2 i (by simpa only [hi] using hj.1)

=======
>>>>>>> origin/ext-change-of-universes
end Embedding

/-- The obvious embedding from `up ℕ` to `up ℤ`. -/
@[simps!]
def embeddingUpNat : Embedding (up ℕ) (up ℤ) :=
  Embedding.mk' _ _ (fun n => n)
    (fun _ _ h => by simpa using h)
    (by dsimp; omega)

instance : embeddingUpNat.IsRelIff := by dsimp [embeddingUpNat]; infer_instance

instance : embeddingUpNat.IsTruncGE where
  mem_next {j _} h := ⟨j + 1, h⟩

/-- The embedding from `down ℕ` to `up ℤ` with sends `n` to `-n`. -/
@[simps!]
def embeddingDownNat : Embedding (down ℕ) (up ℤ) :=
  Embedding.mk' _ _ (fun n => -n)
    (fun _ _ h => by simpa using h)
    (by dsimp; omega)

instance : embeddingDownNat.IsRelIff := by dsimp [embeddingDownNat]; infer_instance

instance : embeddingDownNat.IsTruncLE where
  mem_prev {i j} h := ⟨j + 1, by dsimp at h ⊢; omega⟩

<<<<<<< HEAD
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

=======
>>>>>>> origin/ext-change-of-universes
variable (p : ℤ)

/-- The embedding from `up ℕ` to `up ℤ` which sends `n : ℕ` to `p + n`. -/
@[simps!]
def embeddingUpIntGE : Embedding (up ℕ) (up ℤ) :=
  Embedding.mk' _ _ (fun n => p + n)
    (fun _ _ h => by dsimp at h; omega)
    (by dsimp; omega)

instance : (embeddingUpIntGE p).IsRelIff := by dsimp [embeddingUpIntGE]; infer_instance

instance : (embeddingUpIntGE p).IsTruncGE where
  mem_next {j _} h := ⟨j + 1, by dsimp at h ⊢; omega⟩

/-- The embedding from `down ℕ` to `up ℤ` which sends `n : ℕ` to `p - n`. -/
@[simps!]
def embeddingUpIntLE : Embedding (down ℕ) (up ℤ) :=
  Embedding.mk' _ _ (fun n => p - n)
    (fun _ _ h => by dsimp at h; omega)
    (by dsimp; omega)

instance : (embeddingUpIntLE p).IsRelIff := by dsimp [embeddingUpIntLE]; infer_instance

instance : (embeddingUpIntLE p).IsTruncLE where
  mem_prev {_ k} h := ⟨k + 1, by dsimp at h ⊢; omega⟩

<<<<<<< HEAD
lemma boundaryGE_embeddingUpIntGE_iff (n : ℕ) :
    (embeddingUpIntGE p).BoundaryGE n ↔ n = 0 := by
  constructor
  · intro h
    obtain _|n := n
    · rfl
    · have := h.2 n
      dsimp at this
      omega
  · rintro rfl
    constructor
    · simp
    · intro i hi
      dsimp at hi
      omega

lemma boundaryLE_embeddingUpIntLE_iff (n : ℕ) :
    (embeddingUpIntGE p).BoundaryGE n ↔ n = 0 := by
  constructor
  · intro h
    obtain _|n := n
    · rfl
    · have := h.2 n
      dsimp at this
      omega
  · rintro rfl
    constructor
    · simp
    · intro i hi
      dsimp at hi
      omega

lemma not_mem_range_embeddingUpIntLE_iff (n : ℤ) :
    (∀ (i : ℕ), (embeddingUpIntLE p).f i ≠ n) ↔ p < n := by
  constructor
  · intro h
    by_contra!
    obtain ⟨k, rfl⟩:= Int.eq_add_ofNat_of_le this
    exact (h k) (by simp)
  · intros
    dsimp
    omega

lemma not_mem_range_embeddingUpIntGE_iff (n : ℤ) :
    (∀ (i : ℕ), (embeddingUpIntGE p).f i ≠ n) ↔ n < p := by
  constructor
  · intro h
    by_contra!
    obtain ⟨k, rfl⟩:= Int.eq_add_ofNat_of_le this
    exact (h k) (by simp)
  · intros
    dsimp
    omega

end ComplexShape

open CategoryTheory Limits ZeroObject

namespace HomologicalComplex

section

variable {c c'}
variable {C : Type*} [Category C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (e' : K ≅ L) (e : c.Embedding c')

class IsStrictlySupported : Prop where
  isZero (i' : ι') (hi' : ∀ i, e.f i ≠ i') : IsZero (K.X i')

lemma isZero_X_of_isStrictlySupported [K.IsStrictlySupported e]
    (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    IsZero (K.X i') :=
  IsStrictlySupported.isZero i' hi'

variable {K L} in
lemma isStrictlySupported_of_iso [K.IsStrictlySupported e] : L.IsStrictlySupported e where
  isZero i' hi' := (K.isZero_X_of_isStrictlySupported e i' hi').of_iso
    ((eval _ _ i').mapIso e'.symm)

class IsSupported : Prop where
  exactAt (i' : ι') (hi' : ∀ i, e.f i ≠ i') : K.ExactAt i'

lemma exactAt_of_isSupported [K.IsSupported e] (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    K.ExactAt i' :=
  IsSupported.exactAt i' hi'

variable {K L} in
lemma isSupported_of_iso [K.IsSupported e] : L.IsSupported e where
  exactAt i' hi' := (K.exactAt_of_isSupported e i' hi').of_iso e'

instance [K.IsStrictlySupported e] : K.IsSupported e where
  exactAt i' hi' := by
    rw [exactAt_iff]
    exact ShortComplex.exact_of_isZero_X₂ _ (K.isZero_X_of_isStrictlySupported e i' hi')

structure IsStrictlySupportedOutside : Prop where
  isZero (i : ι) : IsZero (K.X (e.f i))

structure IsSupportedOutside : Prop where
  exactAt (i : ι) : K.ExactAt (e.f i)

variable {K e} in
lemma IsStrictlySupportedOutside.isSupportedOutside (h : K.IsStrictlySupportedOutside e) :
    K.IsSupportedOutside e where
  exactAt i := by
    rw [exactAt_iff]
    exact ShortComplex.exact_of_isZero_X₂ _ (h.isZero i)

instance [HasZeroObject C] : (0 : HomologicalComplex C c').IsStrictlySupported e where
  isZero i _ := (eval _ _ i).map_isZero (Limits.isZero_zero _)

lemma isZero_iff_isStrictlySupported_and_isStrictlySupportedOutside :
    IsZero K ↔ K.IsStrictlySupported e ∧ K.IsStrictlySupportedOutside e := by
  constructor
  · intro hK
    constructor
    all_goals
      constructor
      intros
      exact (eval _ _ _).map_isZero hK
  · rintro ⟨h₁, h₂⟩
    rw [IsZero.iff_id_eq_zero]
    ext n
    apply IsZero.eq_of_src
    by_cases hn : ∃ i, e.f i = n
    · obtain ⟨i, rfl⟩ := hn
      exact h₂.isZero i
    · exact K.isZero_X_of_isStrictlySupported e _ (by simpa using hn)

instance [K.IsStrictlySupported e] : K.op.IsStrictlySupported e.op where
  isZero j hj' := (K.isZero_X_of_isStrictlySupported e j hj').op

end

section

variable {c c'}
variable {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  (K : HomologicalComplex C c') (F : C ⥤ D) [F.PreservesZeroMorphisms] (e : c.Embedding c')

instance map_isStrictlySupported [K.IsStrictlySupported e] :
    ((F.mapHomologicalComplex c').obj K).IsStrictlySupported e where
  isZero i' hi' := by
    rw [IsZero.iff_id_eq_zero]
    dsimp
    rw [← F.map_id, (K.isZero_X_of_isStrictlySupported e i' hi').eq_of_src (𝟙 _) 0, F.map_zero]

end

end HomologicalComplex

lemma Option.eq_none_or_eq_some {ι : Type*} (x : Option ι) :
    x = none ∨ ∃ y, x = some y := by
  cases x <;> aesop
=======
end ComplexShape
>>>>>>> origin/ext-change-of-universes
