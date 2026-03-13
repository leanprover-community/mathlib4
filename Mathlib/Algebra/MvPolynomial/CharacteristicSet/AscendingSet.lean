/-
Copyright (c) 2026 Yuxuan Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Xiao
-/
module

public import Mathlib.Algebra.MvPolynomial.CharacteristicSet.Reduce

/-!
# Ascending sets and basic sets

This file defines the abstract theory of **ascending sets** and **basic sets**.
An ascending set is a triangular set with additional reduction properties.
A basic set is the "smallest" ascending set contained in a given set of polynomials.

## Main declarations

* `AscendingSetTheory`: A typeclass abstracting the definition of an ascending set
  (e.g., strong vs. weak reduction).
* `HasBasicSet`: A typeclass abstracting the algorithm to compute a basic set
  from a list of polynomials.

-/

@[expose] public section

open MvPolynomial

/--
The abstract theory of Ascending Sets.
This class allows us to define what it means for a `TriangularSet` to be an "Ascending Set".
Different instances can implement Ritt's strong ascending sets or Wu's weak ascending sets.
-/
class AscendingSetTheory (σ R : Type*) [CommSemiring R] [DecidableEq R] [LinearOrder σ] where
  /-- The reduction relation used to define the ascending property. -/
  protected reducedTo' : MvPolynomial σ R → MvPolynomial σ R → Prop
  decidableReducedTo : DecidableRel reducedTo' := by infer_instance
  /-- A key property linking the ascending set structure to the initial.
  If `S` is an ascending set, the initial of any non-constant element in `S`
  must be reduced with respect to `S`. -/
  protected initial_reducedToSet_of_mainVariable_ne_bot : ∀ ⦃S : TriangularSet σ R⦄ ⦃i : ℕ⦄,
    (∀ ⦃i j⦄, i < j → j < S.length → reducedTo' (S j) (S i)) →
    (S i).mainVariable ≠ ⊥ → (S i).initial.reducedToSet S

attribute [instance_reducible, instance 900] AscendingSetTheory.decidableReducedTo

variable {R σ : Type*} [CommSemiring R] [DecidableEq R] [LinearOrder σ]

namespace TriangularSet

variable [AscendingSetTheory σ R] {S : TriangularSet σ R} {p : MvPolynomial σ R}

/-- A Triangular Set is an Ascending Set
if every element is reduced with respect to its predecessors. -/
def isAscendingSet (S : TriangularSet σ R) : Prop :=
  ∀ ⦃i j⦄, i < j → j < S.length → AscendingSetTheory.reducedTo' (S j) (S i)

lemma isAscendingSet_iff : isAscendingSet S ↔ ∀ j < S.length, ∀ i < j,
    AscendingSetTheory.reducedTo' (S j) (S i) where
  mp h _ hj _ hi := h hi hj
  mpr h i j hi hj := h j hj i hi

instance : @DecidablePred (TriangularSet σ R) isAscendingSet := fun _ ↦
  decidable_of_iff _ isAscendingSet_iff.symm

theorem isAscendingSet_single (p : MvPolynomial σ R) : (single p).isAscendingSet :=
  fun i _ hij hj ↦ False.elim <| Nat.not_lt_zero i <| lt_of_lt_of_le hij <|
    Nat.le_of_lt_succ <| lt_of_lt_of_le hj <| length_single_le_one

theorem isAscendingSet_empty : (∅ : TriangularSet σ R).isAscendingSet :=
  (single_eq_zero_iff.mp rfl : single (0 : MvPolynomial σ R) = ∅) ▸ isAscendingSet_single 0

theorem isAscendingSet_take (n : ℕ) :
    S.isAscendingSet → (S.take n).isAscendingSet := fun hs i j hij hj ↦ by
  rewrite [take_apply' hj, take_apply' (lt_trans hij hj)]
  exact hs hij (lt_of_lt_of_le hj (Nat.min_le_right ..))

theorem isAscendingSet_drop (n : ℕ) : S.isAscendingSet → (S.drop n).isAscendingSet :=
  fun hs _ _ hij hj ↦ hs (Nat.add_lt_add_right hij n) (Nat.add_lt_of_lt_sub hj)

protected theorem isAscendingSet_concat (h : S.canConcat p)
    (hp : ∀ i < S.length, AscendingSetTheory.reducedTo' p (S i)) :
    S.isAscendingSet → (S.concat p).isAscendingSet := fun hs i j hij hj ↦ by
  have hi : i < S.length := lt_of_lt_of_le hij <| Nat.le_of_lt_succ hj
  simp only [length_concat, concat_apply, hi, reduceIte] at hj ⊢
  match Nat.lt_succ_iff_lt_or_eq.mp hj with
  | .inl hj => rewrite [if_pos hj]; exact hs hij hj
  | .inr hj => simp only [hj, lt_self_iff_false, reduceIte]; exact hp i hi

protected theorem isAscendingSet_takeConcat
    (hp : ∀ i < S.length, AscendingSetTheory.reducedTo' p (S i)) :
    S.isAscendingSet → (S.takeConcat p).isAscendingSet := fun h ↦ by
  unfold takeConcat
  split_ifs with h1 hc
  repeat exact isAscendingSet_single p
  refine TriangularSet.isAscendingSet_concat _ (fun n hn ↦ ?_) <| isAscendingSet_take _ h
  rewrite [take_apply' hn]
  exact hp _ (lt_of_lt_of_le hn (Nat.min_le_right ..))

end TriangularSet

/-- The type of Ascending Sets, which are Triangular Sets satisfying the ascending property. -/
def AscendingSet (σ R : Type*) [CommSemiring R] [LinearOrder σ] [DecidableEq R]
    [AscendingSetTheory σ R] := { TS : TriangularSet σ R // TS.isAscendingSet }

/--
The interface for algorithms computing Basic Sets.
Any instance of this class provides a `basicSet` function that computes a minimal ascending set
contained in a given list of polynomials.
-/
class HasBasicSet (σ R : Type*) [CommSemiring R] [DecidableEq R] [LinearOrder σ]
    extends AscendingSetTheory σ R where
  /-- Computes a Basic Set from a list of polynomials. -/
  basicSet : List (MvPolynomial σ R) → TriangularSet σ R
  /-- The output is always an Ascending Set. -/
  basicSet_isAscendingSet (l : List (MvPolynomial σ R)) : (basicSet l).isAscendingSet
  /-- The output is a subset of the input. -/
  basicSet_subset (l : List (MvPolynomial σ R)) : ∀ ⦃c⦄, c ∈ basicSet l → c ∈ l
  /-- Minimality condition: the output is ≤ any other ascending set contained in the input. -/
  basicSet_minimal (l : List (MvPolynomial σ R)) :
      ∀ ⦃S⦄, S.isAscendingSet → (∀ ⦃p⦄, p ∈ S → p ∈ l) → basicSet l ≤ S
  /-- Order reduction property: appending a reduced element strictly decreases the basic set order.
  Crucial for proving termination of zero decomposition. -/
  basicSet_append_lt_of_exists_reducedToSet : ∀ ⦃l1 l2 : List (MvPolynomial σ R)⦄,
      (∃ p ∈ l2, p ≠ 0 ∧ p.reducedToSet (basicSet l1)) → basicSet (l2 ++ l1) < basicSet l1

/-- Definition of Standard (Ritt) Ascending Set: strict degree reduction. -/
def StandardAscendingSet.isAscendingSet (S : TriangularSet σ R) : Prop :=
  ∀ ⦃i j⦄, i < j → j < S.length → (S j).reducedTo (S i)

/-- Definition of Weak (Wu) Ascending Set: initial reduction. -/
def WeakAscendingSet.isAscendingSet (S : TriangularSet σ R) : Prop :=
  ∀ ⦃i j⦄, i < j → j < S.length → (S j).initial.reducedTo (S i)

theorem WeakAscendingSet.isAscendingSet_of_isStandardAscendingSet {S : TriangularSet σ R} :
    StandardAscendingSet.isAscendingSet S → WeakAscendingSet.isAscendingSet S :=
  fun h _ _ hij hj ↦ initial_reducedTo (h hij hj)


open TriangularSet

namespace AscendingSet

variable [AscendingSetTheory σ R] {S T : AscendingSet σ R} {p : MvPolynomial σ R}

theorem initial_reducedToSet_of_mainVariable_ne_bot {S : TriangularSet σ R} {i : ℕ} :
    S.isAscendingSet → (S i).mainVariable ≠ ⊥ → (S i).initial.reducedToSet S := fun h ↦
  AscendingSetTheory.initial_reducedToSet_of_mainVariable_ne_bot h

theorem initial_reducedToSet_of_mainVariable_ne_bot' {S : TriangularSet σ R}
    (h : S.isAscendingSet) :
    p ∈ S → p.mainVariable ≠ ⊥ → p.initial.reducedToSet S := fun ⟨_, _, hi2⟩ hc ↦
  hi2 ▸ AscendingSet.initial_reducedToSet_of_mainVariable_ne_bot h (hi2 ▸ hc)

/-- Construct an ascending set from a triangular set and a proof of the ascending property. -/
def mk {S : TriangularSet σ R} (h : S.isAscendingSet) : AscendingSet σ R := ⟨S, h⟩

instance : Coe (AscendingSet σ R) (TriangularSet σ R) := ⟨Subtype.val⟩

@[simp] theorem coe_mk (h) : (⟨S, h⟩ : AscendingSet σ R) = S := rfl

theorem coe_mk' (S : TriangularSet σ R) (h) : (⟨S, h⟩ : AscendingSet σ R) = S := rfl

theorem eq_of_coe_eq (h : S.val = T.val) : S = T := Subtype.ext h

theorem ne_of_coe_ne (h : S.val ≠ T.val) : S ≠ T := Subtype.coe_ne_coe.mp h

theorem coe_eq_coe : S.val = T.val ↔ S = T := Subtype.ext_iff.symm

theorem coe_ne_coe : S.val ≠ T.val ↔ S ≠ T := Subtype.coe_ne_coe

/-- The length of the ascending set. -/
def length (S : AscendingSet σ R) : ℕ := S.val.length

theorem length_coe : S.length = S.val.length := rfl

instance : FunLike (AscendingSet σ R) ℕ (MvPolynomial σ R) where
  coe S := S.val
  coe_injective' := DFunLike.coe_injective'.comp Subtype.coe_injective

@[ext]
theorem ext (h : ∀ i, S i = T i) : S = T := DFunLike.ext _ _ h

theorem ext' (h1 : S.length = T.length) (h2 : ∀ i < S.length, S i = T i) : S = T :=
  eq_of_coe_eq <| TriangularSet.ext' h1 h2

instance instSetLike : SetLike (AscendingSet σ R) (MvPolynomial σ R) where
  coe := fun S ↦ S.val
  coe_injective' := SetLike.coe_injective'.comp Subtype.coe_injective

theorem mem_def : p ∈ S ↔ p ∈ S.val := Iff.rfl

instance : HasSubset (AscendingSet σ R) where
  Subset := InvImage (· ⊆ ·) Subtype.val

instance : HasSSubset (AscendingSet σ R) where
  SSubset := InvImage (· ⊂ ·) Subtype.val

theorem subset_def : S ⊆ T ↔ S.val ⊆ T.val := Iff.rfl

theorem ssubset_def : S ⊂ T ↔ S.val ⊂ T.val := Iff.rfl

/-- Converts a ascending set to a finite set. -/
def toFinset (S : AscendingSet σ R) : Finset (MvPolynomial σ R) := S.val.toFinset

/-- Converts a ascending set to a list. -/
def toList (S : AscendingSet σ R) : List (MvPolynomial σ R) := S.val.toList

noncomputable instance : EmptyCollection (AscendingSet σ R) := ⟨⟨∅, isAscendingSet_empty⟩⟩

noncomputable instance : Inhabited (AscendingSet σ R) := ⟨∅⟩

theorem empty_coe : (∅ : AscendingSet σ R) = (∅ : TriangularSet σ R) := rfl

theorem empty_eq_default : (∅ : AscendingSet σ R) = default := rfl

/-- The order on the ascending set is exactly the order on the underlying triangular set. -/
noncomputable def order (S : AscendingSet σ R) : Lex (ℕ → WithTop (WithBot σ ×ₗ ℕ)) :=
  S.val.order

theorem order_coe : S.order = S.val.order := rfl

instance : Preorder (AscendingSet σ R) := Preorder.lift ((↑) : _ → TriangularSet σ R)

theorem lt_def : S < T ↔ S.val < T.val := Iff.rfl

theorem le_def : S ≤ T ↔ S.val ≤ T.val := Iff.rfl

noncomputable instance : DecidableLE (AscendingSet σ R) :=
  fun _ _ ↦ decidable_of_iff _ le_def'.symm

noncomputable instance : DecidableLT (AscendingSet σ R) := decidableLTOfDecidableLE

instance : Setoid (AscendingSet σ R) := Setoid.comap ((↑) : _ → TriangularSet σ R) inferInstance

noncomputable instance instDecidableRelEquiv : @DecidableRel (AscendingSet σ R) _ (· ≈ ·) :=
  fun _ _ ↦ instDecidableAnd

theorem equiv_def : S ≈ T ↔ S.val ≈ T.val := Iff.rfl

section WellFounded

variable [Finite σ] (S' : Set (AscendingSet σ R))

instance instWellFoundedLT : WellFoundedLT (AscendingSet σ R) :=
  Subrelation.isWellFounded (InvImage (· < ·) Subtype.val) Iff.rfl.mp

instance instWellFoundedRelation : WellFoundedRelation (AscendingSet σ R) :=
  ⟨(· < ·), instWellFoundedLT.wf⟩

theorem Set.has_min (h : S'.Nonempty) : ∃ S ∈ S', ∀ T ∈ S', S ≤ T :=
  haveI : WellFounded (· < ·) := @wellFounded_lt (AscendingSet σ R) _ _
  have ⟨S, hS1, hS2⟩ := WellFounded.has_min this S' h
  ⟨S, hS1, fun T hT ↦ not_lt_iff_ge.mp (hS2 T hT)⟩

theorem Set.has_min' (h : S'.Nonempty) : ∃ S, Minimal (· ∈ S') S :=
  have ⟨S, hS1, hS2⟩ := has_min S' h
  ⟨S, minimal_iff_forall_lt.mpr ⟨hS1, fun T hT1 hT2 ↦ absurd (hS2 T hT2) <| not_le_of_gt hT1⟩⟩

/-- The minimal element of a nonempty set of ascending sets. -/
noncomputable def Set.min (h : S'.Nonempty) : AscendingSet σ R := Exists.choose (has_min S' h)

theorem Set.min_mem (h : S'.Nonempty) : min S' h ∈ S' :=
  (Exists.choose_spec (has_min S' h)).1

theorem Set.min_le (h : S'.Nonempty) : ∀ T ∈ S', min S' h ≤ T :=
  (Exists.choose_spec (has_min S' h)).2

end WellFounded

noncomputable instance instDecidableRelReducedToSet :
    @DecidableRel _ (AscendingSet σ R) MvPolynomial.reducedToSet :=
  fun _ S ↦ @decidable_of_iff _ _ reducedToSet_iff.symm (S.length.decidableBallLT _)

end AscendingSet


namespace MvPolynomial
namespace Classical

noncomputable section

variable [AscendingSetTheory σ R] [Finite σ] {α : Type*} [Membership (MvPolynomial σ R) α]

/-- The main variableical existence of a Basic Set for any set of polynomials `a`.
This is guaranteed by the well-foundedness of the order. -/
protected theorem hasBasicSet (a : α) :
    ∃ S : AscendingSet σ R, Minimal (fun a' ↦ ∀ ⦃p⦄, p ∈ a' → p ∈ a) S :=
  AscendingSet.Set.has_min' _ ⟨∅, fun n hn ↦ absurd hn <| notMem_empty n⟩

/-- Non-computable choice of a Basic Set for `a`. -/
protected def basicSet (a : α) : AscendingSet σ R := (Classical.hasBasicSet a).choose

protected theorem basicSet_minimal' (a : α) :
    Minimal (fun a' ↦ ∀ ⦃p⦄, p ∈ a' → p ∈ a) (Classical.basicSet a) :=
  (Classical.hasBasicSet a).choose_spec

end
end Classical

namespace List

variable [HasBasicSet σ R] (l : List (MvPolynomial σ R))
variable {l1 l2 : List (MvPolynomial σ R)} {S T : AscendingSet σ R}

/-- The Basic Set of a list `l`, as computed by the `HasBasicSet` instance. -/
def basicSet : AscendingSet σ R := ⟨HasBasicSet.basicSet l, HasBasicSet.basicSet_isAscendingSet l⟩

theorem basicSet_subset : ↑l.basicSet ⊆ {p | p ∈ l} := HasBasicSet.basicSet_subset l

theorem basicSet_minimal : ∀ ⦃S⦄, ↑S ⊆ {p | p ∈ l} → l.basicSet ≤ S :=
  fun ⟨_, hS⟩ ↦ HasBasicSet.basicSet_minimal l hS

theorem basicSet_toList_equiv : l.basicSet.toList.basicSet ≈ l.basicSet := by
  refine And.intro ?_ ?_
  <;> refine basicSet_minimal _ fun p hp ↦ ?_
  · exact mem_toList_iff.mpr hp
  exact l.basicSet_subset <| mem_toList_iff.mp <| basicSet_subset _ hp

theorem basicSet_ge_of_subset : l1 ⊆ l2 → l2.basicSet ≤ l1.basicSet :=
  fun h ↦ l2.basicSet_minimal fun _ hp ↦ h <| l1.basicSet_subset hp

theorem basicSet_append_comm : (l1 ++ l2).basicSet ≈ (l2 ++ l1).basicSet :=
  have (l1 l2 : List (MvPolynomial σ R)) : l2 ++ l1 ⊆ l1 ++ l2 := List.append_subset.mpr ⟨
    List.subset_append_of_subset_right l1 fun _ ↦ id,
    List.subset_append_of_subset_left l2 fun _ ↦ id⟩
  And.intro (basicSet_ge_of_subset <| this l1 l2) (basicSet_ge_of_subset <| this l2 l1)

theorem basicSet_append_lt_of_exists_reducedToSet
    (h : ∃ p ∈ l2, p ≠ 0 ∧ p.reducedToSet l1.basicSet) : (l2 ++ l1).basicSet < l1.basicSet :=
  HasBasicSet.basicSet_append_lt_of_exists_reducedToSet h

theorem _root_.TriangularSet.basicSet_toList_le_of_isAscendingSet {S : TriangularSet σ R}
    (hS : S.isAscendingSet) : S.toList.basicSet ≤ S := by
  change S.toList.basicSet ≤ ⟨S, hS⟩
  apply S.toList.basicSet_minimal
  simp only [mem_toList_iff, SetLike.setOf_mem_eq]
  rfl

end MvPolynomial.List
