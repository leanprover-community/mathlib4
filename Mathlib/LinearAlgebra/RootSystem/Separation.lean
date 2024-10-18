/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.RootSystem.Defs

/-!
# Separations of a root system
This file defines separations and the corresponding systems of simple roots in a root system.
We work over a commutative ring `R`, and consider systems of positive roots and
their generators.

## Main definitions
* `Separation` : A positivity condition on roots that is preserved by addition, such that any root
  is either positive, or its negative is positive.
* `IsDecomposableFor` : A root is decomposable for a subset `s` if it lies in `s` and is the sum of
  two elements of `s`.
* `Base` : Given a root pairing and separation, the base is the set of indecomposable positive
  elements
* `CartanMatrix` : This function takes two base elements and produces their pairing.

## Results
None yet

## Todo
(May belong in a separate file)
* Any separation (satisfying some condition) comes from some regular element.
* A base is linearly independent in the positive definite case (use obtuse angle lemma).
* A base is a basis (finite case)
* Simple reflections change positivity of exactly one root pair (may need linear independence).
* Weyl orbits of bases : unique for finite and affine case.
## References
* Moody, Pianzola, "Infinite root systems"
-/

variable {ι R M N : Type*}

noncomputable section

namespace RootPairing

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

section

variable (P : RootPairing ι R M N)

/-- A separation is a subset of roots, called `positive`, such that any root is either positive or
its reflection in itself is positive, and any root that is the sum of positive roots is positive. -/
structure Separation (P : RootPairing ι R M N) where
  /-- The positivity predicate. -/
  pos : Set ι
  /-- A root is either positive or minus one times a positive root. -/
  pos_iff : ∀ i, pos i ↔ ¬ pos (P.reflection_perm i i)
  /-- A root that is the sum of positive roots is positive. -/
  add_pos : ∀ i j k, pos i → pos j → P.root i + P.root j = P.root k → pos k

/-- A root is decomposable (with respect to a subset `s` of `ι`) if it is indexed by an element of
`s`, and is the sum of two roots indexed by `s`. -/
def IsDecomposableFor (i : ι) (s : Set ι) : Prop :=
  i ∈ s ∧ ∃ (a b : ι), P.root a + P.root b = P.root i ∧ a ∈ s ∧ b ∈ s

lemma decomposableFor_def (i : ι) (s : Set ι) : P.IsDecomposableFor i s ↔
    i ∈ s ∧ ∃ (a b : ι), P.root a + P.root b = P.root i ∧ a ∈ s ∧ b ∈ s :=
  Eq.to_iff rfl

end

variable {P : RootPairing ι R M N} (S : Separation P)

lemma pos_iff_neg_not_pos (i : ι) :
    S.pos i ↔ ¬ S.pos (P.reflection_perm i i) :=
  S.pos_iff i

lemma pos_of_pos_add {i j k : ι} (hi : S.pos i) (hj : S.pos j)
    (hijk : P.root i + P.root j = P.root k) :
    S.pos k :=
  S.add_pos i j k hi hj hijk

/-- The base of a separation is the set of indecomposably positive elements. -/
def base : Set ι :=
  {i | S.pos i ∧ ¬ IsDecomposableFor P i S.pos}

lemma base_def (i : ι) :
    i ∈ base S ↔ (S.pos i ∧ ¬ IsDecomposableFor P i S.pos) :=
  Set.mem_def

lemma sum_of_pos_not_in_base {i j k : ι} (hi : S.pos i) (hj : S.pos j)
    (hijk : P.root i + P.root j = P.root k) :
    k ∉ base S := by
  have := base_def S k
  contrapose! this
  exact Or.inl ⟨this, fun hk => (decomposableFor_def P k S.pos).mpr
    ⟨hk, Exists.intro i (Exists.intro j ⟨hijk, ⟨hi, hj⟩⟩)⟩⟩

/-- The Cartan matrix of a separation. -/
def cartanMatrix : base S × base S → R :=
  fun (i, j) => P.pairing i j

@[simp]
lemma cartanMatrix_entry {i j : ι} (hi : i ∈ base S) (hj : j ∈ base S) :
    cartanMatrix S (⟨i, hi⟩, ⟨j, hj⟩) = P.pairing i j :=
  rfl

lemma cartanMatrix_same {i : ι} (hi : i ∈ base S) :
    cartanMatrix S (⟨i, hi⟩, ⟨i, hi⟩) = 2 := by
  simp

end RootPairing
