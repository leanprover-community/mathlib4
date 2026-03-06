/-
Copyright (c) 2025 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
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
- `Sober`: An alternative equiavlent definition of a Sober topological space as one where
  the unit map of the adjunction to Locales, `adjunctionTopToLocalePT`, is a homeomorphism.

## Main Statements
- `specialization_iff_ge`: The original order and the specialization order induced by the Scott
  topology, correspond. Prop 3.5.2 in [reneta2024]. Prop 2.3.2(1) in [abramsky_gabbay_maibaum_1994].
- `isTopologicalBasis_Ici_image_compactSet`: The upward closures of compact elements form a
  topological basis under the Scott Topology. Prop 3.5.2 in [reneta2024].
- `open_eq_open_of_basis'`: Explicit construction an Open set from the basis mentioned above.
  Prop 2.3.6(2) in [abramsky_gabbay_maibaum_1994].
- `scott_is_sober`: Main result: Scott topologies over algebraic DCPOs are Sober.
  Prop 3.5.3 in [reneta2024] and Prop 2.27 in [abramsky_gabbay_maibaum_1994].

## Ideas
Brief primer to domain theory (please see [reneta2024] or [abramsky_gabbay_maibaum_1994] for more
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

* [Reneta, *Duality in Domain Theory*][reneta2024]
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

/-- An algebraic directed complete partial order is a `CompletePartialOrder` with 1) a least
element and 2) every element is given by the supremum of a set of compact elements (algebraic). -/
class AlgebraicDCPO (α : Type*) extends CompletePartialOrder α, OrderBot α where
  algebraic : ∀ x : α, ({y : α | IsCompactElement y ∧ y ≤ x}).Nonempty ∧ DirectedOn (· ≤ ·)
    {y : α | IsCompactElement y ∧ y ≤ x} ∧ x = sSup {y : α | IsCompactElement y ∧ y ≤ x}

end CompletePartialOrder

namespace Topology
namespace IsScott
open Topology.IsScott TopologicalSpace Set Topology CompletePartialOrder
section CompletePartialOrder

variable {α : Type*} [TopologicalSpace α] [CompletePartialOrder α]
  [IsScott α {d | DirectedOn (· ≤ ·) d}]

/-- The order from `CompletePartialOrder` and the specialization order induced by the Scott
topology, correspond. Unfortunately Mathlib's specialization order `⤳` is opposite to `≤`.
Prop 3.5.2 in [reneta2024]. Prop 2.3.2(1) in [abramsky_gabbay_maibaum_1994]. -/
lemma specialization_iff_ge {x y : α} : x ≤ y ↔ y ⤳ x := by
  rw [specializes_iff_forall_open]
  constructor
  · intro x_le_y u hu x_in_u
    apply (isUpperSet_of_isOpen {d | DirectedOn (· ≤ ·) d }) at hu
    exact hu x_le_y x_in_u
  · let u := {z : α | ¬(z ≤ y)}
    have hu: IsOpen u := by
      rw [isOpen_iff_isUpperSet_and_dirSupInaccOn {d | DirectedOn (· ≤ ·) d }]
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

/-- The upward closure of a compact element (`Ici e`) is an open set.
We refer to the `Ici e` as basis due to `isTopologicalBasis_Ici_image_compactSet`. -/
lemma isOpen_of_basis (e : α) (he₀ : IsCompactElement e) : IsOpen (Ici e) := by
  rw [isOpen_iff_isUpperSet_and_dirSupInaccOn {d | DirectedOn (· ≤ ·) d }]
  constructor
  · -- u is an upper set
    unfold IsUpperSet
    intro x y x_le_y hx
    simp only [Ici, mem_setOf_eq] at hx ⊢
    transitivity x
    · exact hx
    · exact x_le_y
  · -- u is a Scott-Hausdorff open set, ie it has the inaccessable directed joins property
    -- However the directed sets for our topology are defined precisely as
    -- the directed sets of the our DCPOs
    -- So compact points are precisely those points which have directed innaccessable joins
    intro d hd nonempty _  x hx hx' -- he₁
    rw [isCompactElement_iff_le_of_directed_sSup_le] at he₀
    -- rewrite `x`'s LUB propoerty in terms of sSup
    have hx : x = sSup d := IsLUB.unique hx (lubOfDirected d hd)
    have he₁ : e ≤ sSup d := by
      rw [← hx]
      simp only [Ici, mem_setOf_eq] at hx'
      exact hx'
    choose a a_in_d ha' using he₀ d nonempty hd he₁
    exact ⟨a, a_in_d, mem_Ici.mpr ha'⟩

/-- A Subtype for compact elements in an ambient partial order. -/
abbrev CompactElement (α : Type*) [PartialOrder α] := {x : α // IsCompactElement x}

/-- The upwards closure of a compact element forms an open set. -/
abbrev Subtype.toOpen (c : CompactElement α) : Opens α :=
  ⟨Ici c, isOpen_of_basis c.val c.prop⟩

/-- The upwards closure of a compact element forms an open set.
In this version the data is implicit. -/
abbrev IsCompactElement.toOpen {c : α} (hc : IsCompactElement c) : Opens α :=
  (⟨c, hc⟩ : CompactElement α).toOpen

/-- A helper. This can be made more straightforward by replacing `{u : Opens α}` with
`{u : UpperSet}` and applying the additional lemma `Topology.IsScott.isUpperSet_of_isOpen`
at the point of usage. Having this lemma in this form helps inference of optional parameters. -/
private lemma Opens.mem_iff_Ici_subset {e : α} {u : Opens α} : e ∈ u ↔ Ici e ⊆ u := by
  constructor
  · intro e_in_u
    have u_open := u.isOpen
    rw [isOpen_iff_isUpperSet_and_dirSupInaccOn {d | DirectedOn (· ≤ ·) d }] at u_open
    let ⟨u_Ici, _⟩ := u_open
    intro a ha
    exact u_Ici ha e_in_u
  · intro h
    exact h <| mem_Ici.2 (le_refl e)

end CompletePartialOrder

section AlgebraicDCPO
variable {D : Type*} [TopologicalSpace D] [AlgebraicDCPO D] [IsScott D {d | DirectedOn (· ≤ ·) d}]
open Opens

/-- Given any point `x` in `D` in an open set `u`, there exists
an upward closure of a compact element (`Ici e`), within `u` which contains `x`.
We refer to the `Ici e` as basis due to `isTopologicalBasis_Ici_image_compactSet`. -/
lemma exists_basis_mem_basis (x : D) (u : Set D) (x_in_u : x ∈ u) (hu : IsOpen u)
    : ∃ c, IsCompactElement c ∧ x ∈ Ici c ∧ Ici c ⊆ u := by
  rw [isOpen_iff_isUpperSet_and_dirSupInaccOn {d | DirectedOn (· ≤ ·) d }] at hu
  obtain ⟨upper, hausdorff⟩ := hu
  have compactLowerBounded : ∃ c: D, c ≤ x ∧ c ∈ u ∧ IsCompactElement c := by
    -- the Algebraicity property
    obtain ⟨nonempty, directed_cls, join⟩ := AlgebraicDCPO.algebraic x
    -- We work with this cls to extract a compact elememt from it satisfying our needs
    let cls := {y : D | IsCompactElement y ∧ y ≤ x}
    -- by algebraicity, a point, `x`, is the meet of its `cls`
    have x_is_LUB : IsLUB cls x:= by
      rw [join]
      apply CompletePartialOrder.lubOfDirected cls directed_cls
    -- We use the innacessible joins property to show get a nonempty intersection
    -- The intersection contains exactly what we want, a compact point in u and ≤ x
    have nonempty_inter := hausdorff directed_cls nonempty directed_cls x_is_LUB x_in_u
    simp only [inter_nonempty] at nonempty_inter
    obtain ⟨c, ⟨hc₀, hc₁⟩, hc₂⟩ := nonempty_inter
    exact ⟨c, hc₁, hc₂, hc₀⟩
  choose c hc₀ hc₁ hc₂ using compactLowerBounded
  exact ⟨c, hc₂, hc₀, upper.Ici_subset hc₁⟩

/-- The upward closures of compact elements form a topological
basis under the Scott Topology. Prop 3.5.2 in [reneta2024] -/
theorem isTopologicalBasis_Ici_image_compactSet
    : IsTopologicalBasis (Ici '' {x : D | IsCompactElement x}) := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · -- every upper set of a compact element in the DCPO is a Scott open set
    -- This is the true by definition direction, as compactness corresponds to Scott-Hausdorrf open,
    -- and upper set corresponds to Upper set open
    simp only [mem_image, mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    apply isOpen_of_basis
  · -- If a point `x` is in an open set `u`, we can find it in a set in the basis (`Ici c`)
    intro x u x_in_u hu
    choose c hc x_in_c' hc' using exists_basis_mem_basis x u x_in_u hu
    use Ici c
    use ⟨c, hc, rfl⟩

/-- Any open set, `u`, can be constructed as a union of sets from the basis.
    The basis consists of the upward closures of those compact elements in `u`
    This is the weaker version of the lemma using `Set`s instead of `Opens`. -/
lemma open_eq_open_of_basis (u : Set D) (hu : IsOpen u) :
  u = ⋃₀ (Ici '' {c : D | IsCompactElement c ∧ Ici c ⊆ u}) := by
  ext e
  simp only [sUnion_image, mem_setOf_eq, mem_iUnion, exists_prop]
  constructor
  · intro e_in_u
    choose c hc₀ e_in_c' hc'₁ using exists_basis_mem_basis e u e_in_u hu
    use c
  · rintro ⟨c, ⟨hc, hc'⟩, e_in_c'⟩
    apply hc'
    simp_all only

/-- See `open_eq_open_of_basis`
    This is the stronger version of the lemma using `Opens` instead of `Set`s.
    The weaker version is still useful as it is easier to use when sufficient.
    We don't reuse the previous result to prove this, since the proof turns out just as long -/
lemma open_eq_open_of_basis' (u : Opens D) :
    u = ⨆ c : {c | IsCompactElement c ∧ c ∈ u}, IsCompactElement.toOpen c.2.1 := by
  ext e
  simp only [SetLike.mem_coe]
  constructor
  · intro e_in_u
    choose c hc₀ e_in_c' hc'₁ using exists_basis_mem_basis e u e_in_u u.isOpen
    simp only [coe_setOf, IsCompactElement.toOpen, mem_setOf_eq, iSup_mk, mem_mk, mem_iUnion,
      mem_Ici, Subtype.exists, exists_prop]
    exact ⟨c, ⟨hc₀, mem_iff_Ici_subset.2 hc'₁⟩, mem_Ici.1 e_in_c'⟩
  · rintro he
    simp only [coe_setOf, IsCompactElement.toOpen, mem_setOf_eq, iSup_mk, mem_mk, mem_iUnion,
      mem_Ici, Subtype.exists, exists_prop] at he
    obtain ⟨c, ⟨hc₀, c_in_u⟩, he⟩ := he
    rw [mem_iff_Ici_subset] at c_in_u
    apply Set.mem_of_mem_of_subset he c_in_u

-- TODO: note to reviewers. the sSup formulation is the only result used later on
-- The `iSup` version above can be deleted and the below proof restructured (which was
-- indeed the original structure). Is it helpful to leave multiple versions of this statement here?

/-- Version `of open_eq_open_of_basis'_sSup` using `sSup` rather than `iSup` -/
lemma open_eq_open_of_basis'_sSup (u : Opens D) :
    u = sSup ({ o | ∃ (c : D) (hc : IsCompactElement c), c ∈ u ∧ o = hc.toOpen }) := by
  ext e
  simp only [SetLike.mem_coe, Opens.mem_sSup, Set.mem_setOf_eq]
  constructor
  · intro e_in_u
    choose c hc₀ e_in_c' hc'₁ using exists_basis_mem_basis e u e_in_u u.isOpen
    exact ⟨hc₀.toOpen, ⟨c, hc₀, hc'₁ (Set.mem_Ici.2 le_rfl), rfl⟩, e_in_c'⟩
  · rintro ⟨_, ⟨c, hc, c_in_u, rfl⟩, e_in_o⟩
    exact (mem_iff_Ici_subset.mp c_in_u) e_in_o

end AlgebraicDCPO
end IsScott
end Topology
