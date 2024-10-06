/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.RootSystem.Defs

/-!
# Systems of simple roots and bases of a root system

This file defines systems of simple roots in a root system.  We work over a linearly ordered
commutative ring `R`, and consider systems of positive roots and their generators.

## Main definitions

* `Thin` : A root system is thin if it admits a functional such that there are only finitely many
roots in the preimage of any interval.  This lets us prove some properties by induction on height.
* `RegularElement` : A regular element is a linear functional on the root space that takes no roots
to zero.  This corresponds to an element of a Lie algebra with minimal centralizer.
* `Separation` : A positivity condition on roots that is preserved by addition, such that any root
  is either positive, or its negative is positive.
* `IsDecomposableFor` : A positive root is decomposable if it is the sum of two positive roots.
* `Base` : Given a root pairing and separation, the base is the set of indecomposable positive
  elements
* `cartanMatrix` : This function takes two base elements and produces their pairing.

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

section unordered

variable  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) (i : ι)

/-- A regular element is a linear functional that takes no roots to zero. -/
def IsRegularElement (x : N) : Prop := ∀(i : ι), P.toPerfectPairing (P.root i) x ≠ 0

/-- A separation is a subset of roots, called `positive`, such that any root is either positive or
minus one times positive, and any root that is the sum of positive roots is positive.-/
structure Separation (P : RootPairing ι R M N) where
  /-- The positivity predicate. -/
  pos : Set ι
  /-- A root is either positive or minus one times a positive root. -/
  pos_iff : ∀ i, pos i ↔ ¬ pos (P.reflection_perm i i)
  /-- A root that is the sum of positive roots is positive. -/
  add_pos : ∀ i j k, pos i → pos j → P.root i + P.root j = P.root k → pos k

lemma pos_iff_neg_not_pos {P : RootPairing ι R M N} (S : Separation P) (i : ι) :
    S.pos i ↔ ¬ S.pos (P.reflection_perm i i) :=
  S.pos_iff i

lemma pos_of_pos_add {P : RootPairing ι R M N} (S : Separation P) {i j k : ι} (hi : S.pos i)
    (hj : S.pos j) (hijk : P.root i + P.root j = P.root k) : S.pos k := S.add_pos i j k hi hj hijk

-- instance (S : Separation P) : PartialOrder S.pos where i < j iff pos (P.root i - P.root j)

--theorem isWF (S : Separation P) :

-- define simple system = set of irreducible elements for separation = base cases for WF

/-- A root is decomposable (with respect to a subset `s` of `ι`) if it is indexed by an element of
`s`, and is the sum of two roots indexed by `s`. -/
def IsDecomposableFor (i : ι) (s : Set ι) : Prop :=
  i ∈ s ∧ ∃ (a b : ι), P.root a + P.root b = P.root i ∧ a ∈ s ∧ b ∈ s

lemma decomposableFor_def (i : ι) (s : Set ι) : P.IsDecomposableFor i s ↔
    i ∈ s ∧ ∃ (a b : ι), P.root a + P.root b = P.root i ∧ a ∈ s ∧ b ∈ s :=
  Eq.to_iff rfl

/-- The base of a separation is the set of indecomposably positive elements. -/
def base {P : RootPairing ι R M N} (S : Separation P) : Set ι :=
  {i | S.pos i ∧ ¬ IsDecomposableFor P i S.pos}

lemma base_def {P : RootPairing ι R M N} (S : Separation P) (i : ι) :
    i ∈ base S ↔ (S.pos i ∧ ¬ IsDecomposableFor P i S.pos) :=
  Set.mem_def

lemma sum_of_pos_not_in_base {P : RootPairing ι R M N} (S : Separation P) {i j k : ι} (hi : S.pos i)
    (hj : S.pos j) (hijk : P.root i + P.root j = P.root k) : k ∉ base S := by
  have := base_def S k
  contrapose! this
  exact Or.inl ⟨this, fun hk => (decomposableFor_def P k S.pos).mpr
    ⟨hk, Exists.intro i (Exists.intro j ⟨hijk, ⟨hi, hj⟩⟩)⟩⟩

/-- The Cartan matrix of a separation. -/
def cartanMatrix {P : RootPairing ι R M N} (S : Separation P) : base S × base S → R :=
  fun (i, j) => P.pairing i j

@[simp]
lemma cartanMatrix_entry {P : RootPairing ι R M N} (S : Separation P) {i j : ι} (hi : i ∈ base S)
    (hj : j ∈ base S) : cartanMatrix S (⟨i, hi⟩, ⟨j, hj⟩) = P.pairing i j :=
  rfl

lemma cartanMatrix_same {P : RootPairing ι R M N} (S : Separation P) {i : ι} (hi : i ∈ base S) :
    cartanMatrix S (⟨i, hi⟩, ⟨i, hi⟩) = 2 := by
  simp

/-!
/-- View a root as an element of the span of roots. -/
def root' : ι → (Submodule.span R (Set.range P.root)) :=
  fun i => ⟨P.root i, Submodule.subset_span <| @Set.mem_range_self _ _ P.root i⟩

/-- A base is a parametrized subset of roots forming an `R`-basis of the span of roots, such
that the coordinates of any root are all nonpositive or all nonnegative. (maybe just restrict this
definition to root systems?)-/
structure Base extends Basis α R (Submodule.span R (Set.range P.root)) where
  /-- An injection from the type parametrizing the basis to the type parametrizing roots. -/
  f : α ↪ ι
  /-- Any basis vector is equal to the corresponding root. -/
  eq_root : ∀ (i : α), DFunLike.coe repr.symm (Finsupp.single i 1) = P.root (f i)
  /-- Any root has same-sign coordinates with respect to the basis. -/
  same_sign : ∀(i : ι) (j k : α), 0 ≤ (repr (P.root' i) j) * (repr (P.root' i) k)
-/
end unordered

section ordered

-- Thin-slicing property for regular elements gives stability of separation against small changes.

variable [LinearOrderedCommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N) (i : ι)
/-- An element in the coroot space is thin-slicing if any interval in `R` has finite preimage in
the set of roots. -/
def IsThinSlicing (x : N) : Prop := ∀ (n : R), 0 ≤ n →
  Finite { i | (P.toPerfectPairing (P.root i) x) ∈ Set.Icc 0 n}

theorem thinSlicing_ofFinite [Finite ι] (x : N) : IsThinSlicing P x :=
  fun n _ ↦ Finite.Set.finite_inter_of_left
    (fun i ↦ Preorder.toLE.1 0 ((P.toPerfectPairing (P.root i)) x))
    fun i ↦ Preorder.toLE.1 ((P.toPerfectPairing (P.root i)) x) n

/-- A root pairing is thin if there is a thin-slicing element.  Borcherds-Kac-Moody Lie
algebras admit a `ℤ`-grading with finite dimensional pieces (except possibly for Cartan), so
their root systems are always thin. -/
def IsThin : Prop := ∃ (x : N), IsThinSlicing P x

/-- Produce a separation from a regular element. -/
def separation_of_regular (x : N) (hx : IsRegularElement P x) :
    Separation P where
  pos := fun i => P.toPerfectPairing (P.root i) x > 0
  pos_iff := fun i => by
    constructor
    · intro hi
      simp_all only [← toLin_toPerfectPairing, PerfectPairing.toLin_apply, gt_iff_lt,
        root_reflection_perm, reflection_apply_self, map_neg, LinearMap.neg_apply, Left.neg_pos_iff,
        not_lt]
      exact le_of_lt hi
    · intro hi
      simp_all only [root_reflection_perm, reflection_apply_self, ← toLin_toPerfectPairing, map_neg,
        PerfectPairing.toLin_apply, LinearMap.neg_apply, gt_iff_lt, Left.neg_pos_iff, not_lt]
      have h : P.toPerfectPairing (P.root i) x ≠ 0 := by
        simp_all only [IsRegularElement, ne_eq, not_false_eq_true]
      exact lt_of_le_of_ne hi h.symm
  add_pos := fun i j k hi hj hijk => by
    simp_all only [← toLin_toPerfectPairing, PerfectPairing.toLin_apply, map_add,
      LinearMap.add_apply, ← hijk]
    exact Right.add_pos' hi hj


end ordered

section finite

end finite

end RootPairing
