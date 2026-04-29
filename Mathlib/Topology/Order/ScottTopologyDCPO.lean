/-
Copyright (c) 2025 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando, Bhavik Mehta
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Order.ScottTopology
public import Mathlib.Topology.Sets.Opens

/-!
# Scott Complete Partial Order

Properties of Scott topologies over Pointed (Directed) `CompletePartialOrder`, and Algebraic DCPOs.

## Main Definitions
- `Compact`: The element x is compact if for any directed subset A ⊆ D, whenever `x ≤ sSup A`,
  there is some a ∈ A s.t. x ≤ a already.
- `AlgebraicDCPO`: an extension of pointed `CompletePartialOrder` which is additionally "algebraic".
  Pointed is just `OrderBot`.
  Algebraicity has a correspondence with the 'inaccessibility of directed joins'
  property of Scott topologies, which can be seen in some of the proofs below.

## Main Statements
- `specialization_iff_ge`: The original order and the specialization order induced by the Scott
  topology, correspond. Prop 3.5.2 in [renata2024]. Prop 2.3.2(1) in [abramsky_gabbay_maibaum_1994].
- `isTopologicalBasis_Ici_image_compactSet`: The upward closures of compact elements form a
  topological basis under the Scott Topology. Prop 3.5.2 in [renata2024].

## Ideas
Brief primer to domain theory (please see [renata2024] or [abramsky_gabbay_maibaum_1994] for more
detail):
- The order structures we consider, `CompletePartialOrder` and `AlgebraicDCPO` should be thought
  of as containing the semantics of imperative programs, more concretely a partial function on
  some state denoted `Σ ⇀ Σ`. Note that non-terminating computations are modelled by the partiality
  (lack of an end state).
- From a computational perspective we would like even the infinite computations to be expressible as
  the limit of a sequence of finite computations.
- We take Directed sets to be a generalisation of a such a sequence of computations. The supremum of
  such a set is a possibly infinite computation (thought of as limit of a sequence).
- Compact elements model finite computations, since the computation in question is always
  reached before (is contained in the directed set) before reaching the supremum.
- An `AlgebraicDCPO` models all finitely generated computations. Every element is the supremum of
  a set of compact elements.

## Notation
* `e` `c` : elements in the a set, usually of an open set, often compact.
* `e'` : upwards closures of point.

## Implementation notes
The namespaces of this file aims to match `Mathlib.Topology.Order.ScottTopology`.

## References
Statements and proofs match the first source. Exact or equivalent statements in the 2nd source are
stated.

* [Renata, *Duality in Domain Theory*][renata2024]
* [Abramsky and Jung, *Domain Theory*][abramsky_gabbay_maibaum_1994]

## Tags

Scott topology, Algebraic DCPO, Stone Duality
-/

@[expose] public section

namespace CompletePartialOrder
variable {α : Type*} [CompletePartialOrder α]

/-- An element `k` is compact in a complete partial order if and only if
any directed set with `sSup` above `k` already got above `k` at some point in the set. -/
theorem isCompactElement_iff_le_of_directed_sSup_le (k : α) :
    IsCompactElement k ↔
      ∀ s : Set α, s.Nonempty → DirectedOn (· ≤ ·) s → k ≤ sSup s → ∃ x : α, x ∈ s ∧ k ≤ x := by
  constructor
  · intro hk s hs hs' h_le
    exact hk s (sSup s) hs hs' (lubOfDirected s hs') h_le
  · intro h s u hs hs' hu h_le
    have u_eq_sSup: u = sSup s := IsLUB.unique hu (lubOfDirected s hs')
    rw [u_eq_sSup] at h_le
    exact h s hs hs' h_le

/-- `⊥` in a `CompletePartialOrder` is compact. -/
lemma isCompactElement_bot : IsCompactElement (⊥ : α) := by
  rw [isCompactElement_iff_le_of_directed_sSup_le]
  intro s ⟨e, he⟩ _ _
  use e, he
  exact OrderBot.bot_le e

/-- An algebraic directed complete partial order is a `CompletePartialOrder` with 1) a least
element and 2) every element is given by the supremum of a set of compact elements (algebraic). -/
class AlgebraicDCPO (α : Type*) extends CompletePartialOrder α where
  algebraic (x : α) : DirectedOn (· ≤ ·) {y : α | IsCompactElement y ∧ y ≤ x} ∧
    x = sSup {y : α | IsCompactElement y ∧ y ≤ x}

end CompletePartialOrder

namespace Topology
namespace IsScott
open Topology.IsScott TopologicalSpace Set Topology CompletePartialOrder
section CompletePartialOrder

variable {α : Type*} [TopologicalSpace α] [CompletePartialOrder α]
  [IsScott α univ]

/-- The order from `CompletePartialOrder` and the specialization order induced by the Scott
topology, correspond. Unfortunately Mathlib's specialization order `⤳` is opposite to `≤`.
Prop 3.5.2 in [renata2024]. Prop 2.3.2(1) in [abramsky_gabbay_maibaum_1994]. -/
lemma specialization_iff_ge {x y : α} : y ⤳ x ↔ x ≤ y  := by
  rw [specializes_iff_forall_open]
  constructor
  · let u := {z : α | ¬(z ≤ y)}
    have hu: IsOpen u := by
      rw [isOpen_iff_isUpperSet_and_dirSupInaccOn univ]
      constructor
      · intro a b a_le_b a_in_u b_le_y
        exact (and_not_self_iff (a ≤ y)).1 ⟨a_le_b.trans b_le_y, a_in_u⟩
      · intro d hd hd₁ _ join h_join join_in_u
        by_contra inter_empty
        simp only [Set.Nonempty, mem_inter_iff, mem_setOf_eq, not_exists, not_and, not_not,
          u] at inter_empty
        have join_le_y : join ≤ y := by
          have y_in_UB_d : y ∈ upperBounds d := by
            simp_all only [mem_setOf_eq, u]
            exact inter_empty
          have h_join := isLUB_iff_le_iff.1 h_join y
          rwa [←  h_join] at y_in_UB_d
        exact (and_not_self_iff (join ≤ y)).1 ⟨join_le_y, join_in_u⟩
    intro h_specialize
    -- Take the contrapose of x being in an open implying y must also be in it
    have h_specialize := not_imp_not.2 <| h_specialize u hu
    -- we know y ∉ u as y ≤ y. And from specialization relation on y we deduce that x ∉ u
    simp only [mem_setOf_eq, le_refl, not_true_eq_false, not_false_eq_true, not_not, forall_const,
      u] at h_specialize
    -- in other words x ≤ y as required
    exact h_specialize
  · intro x_le_y u hu x_in_u
    apply isUpperSet_of_isOpen univ at hu
    exact hu x_le_y x_in_u

/-- The upward closure of a compact element (`Ici e`) is an open set. -/
lemma IsCompactElement.isOpen_Ici (e : α) (he₀ : IsCompactElement e) : IsOpen (Ici e) := by
  rw [isOpen_iff_isUpperSet_and_dirSupInaccOn univ]
  constructor
  · grind [IsUpperSet]
  · rw [dirSupInaccOn_univ]
    intro d nonempty hd x hx hx'
    exact he₀ d x nonempty hd hx hx'

/-- The upwards closure of a compact element forms an open set.
In this version the data is implicit. -/
abbrev IsCompactElement.toOpen {c : α} (hc : IsCompactElement c) : Opens α :=
  ⟨Ici c, IsCompactElement.isOpen_Ici c hc⟩

/-- A compact element as a subtype. -/
abbrev CompactElement (α : Type*) [PartialOrder α] := {c : α // IsCompactElement c}

/-- The upwards closure of a compact element forms an open set. -/
abbrev CompactElement.toOpen (c : CompactElement α) : Opens α :=
  ⟨Ici c.val, IsCompactElement.isOpen_Ici c.val c.prop⟩

end CompletePartialOrder

section AlgebraicDCPO
variable {D : Type*} [TopologicalSpace D] [AlgebraicDCPO D] [IsScott D univ]
open Opens

/-- Given any point `x` in `D` in an open set `u`, there exists
an upward closure of a compact element (`Ici e`), within `u` which contains `x`. -/
lemma exists_Ici_mem (x : D) (u : Set D) (x_in_u : x ∈ u) (hu : IsOpen u)
    : ∃ c, IsCompactElement c ∧ x ∈ Ici c ∧ Ici c ⊆ u := by
  rw [isOpen_iff_isUpperSet_and_dirSupInaccOn univ] at hu
  obtain ⟨upper, hausdorff⟩ := hu
  have compactLowerBounded : ∃ c: D, c ≤ x ∧ c ∈ u ∧ IsCompactElement c := by
    -- the Algebraicity property
    obtain ⟨directed_cls, join⟩ := AlgebraicDCPO.algebraic x
    -- We work with this cls to extract a compact elememt from it satisfying our needs
    let cls := {y : D | IsCompactElement y ∧ y ≤ x}
    -- by algebraicity, a point, `x`, is the meet of its `cls`
    have x_is_LUB : IsLUB cls x:= by
      rw [join]
      apply CompletePartialOrder.lubOfDirected cls directed_cls
    have nonempty : {y | IsCompactElement y ∧ y ≤ x}.Nonempty :=
      ⟨⊥, ⟨isCompactElement_bot, OrderBot.bot_le x⟩⟩
    -- We use the innacessible joins property to show get a nonempty intersection
    -- The intersection contains exactly what we want, a compact point in u and ≤ x
    have nonempty_inter := hausdorff (mem_univ _) nonempty directed_cls x_is_LUB x_in_u
    simp only [inter_nonempty] at nonempty_inter
    obtain ⟨c, ⟨hc₀, hc₁⟩, hc₂⟩ := nonempty_inter
    exact ⟨c, hc₁, hc₂, hc₀⟩
  choose c hc₀ hc₁ hc₂ using compactLowerBounded
  exact ⟨c, hc₂, hc₀, upper.Ici_subset hc₁⟩

/-- The upward closures of compact elements form a topological
basis under the Scott Topology. Prop 3.5.2 in [renata2024] -/
theorem isTopologicalBasis_Ici_image_compactSet
    : IsBasis (CompactElement.toOpen '' (@Set.univ (CompactElement D))) := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · grind [IsCompactElement.isOpen_Ici, coe_mk]
  · grind [exists_Ici_mem, Subtype.exists, coe_mk]

end AlgebraicDCPO
end IsScott
end Topology
