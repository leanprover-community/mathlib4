/-
Copyright (c) 2025 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Order.ScottTopology
public import Mathlib.Topology.Order.Category.FrameAdjunction

/-!
# Scott Complete Partial Order

Properties of Scott topologies over (Directed) `CompletePartialOrder`, and Algberaic DCPOs.
The main theorem proven is that Scott Topologies over Algebraic DCPOs are sober. Sober goes halfway
in showing that adjunction between `TopCat` and `Loc` defined in
`Topology/Order/Category/FrameAdjunction` is an equivalence. Showing that the adjunction is an
equivalence is the motivation in the first place for restricting DCPOs to Algebraic DCPOs

## Main Definitions
- `Compact` - The element x is compact if for any directed subset A ⊆ D, whenever `x ≤ sSup A`,
there is some a ∈ A s.t. x ≤ a already.
- `AlgebraicDCPO` - an extension of `CompletePartialOrder` which is additionally "algebraic".
Algebraicity has a correspondence with axioms of a Scott topology

## Main Statements
- `specialization_iff_ge`: The original order and the specialization order induced by the Scott
topology, correspond. Prop 3.5.2 in [reneta2025]. Prop 2.3.2(1) in [abramsky_gabbay_maibaum_1994]
- `isTopologicalBasis_of_Ici_compact`: The upward closures of compact elements form a topological
basis under the Scott Topology. Prop 3.5.2 in [reneta2025]
- `open_eq_of_open_basis'`: Explicit construction an Open set from the basis mentioned above.
Prop 2.3.6(2) [abramsky_gabbay_maibaum_1994]

main theorem
- `scott_is_sober`: Scott Topologies over Algebraic DCPOs are Sober. Prop 3.5.3 in [reneta2025] and
Prop 7.2.27 in [abramsky_gabbay_maibaum_1994]

## Notation
* `e` `c` : elements in the a set, usually of an open set, often compact.
referred to as a `point` from here onwards
* `e'` or `eᵘ` : upwards closures of point. for variable name `e'` and for computing value `eᵘ`
* `eᵘᵒ` : upward closure of a compact point. We prove this is an open set

## Implementation notes
The first half of the file (sections CompletePartialOrder and AlgebraicDCPO) is laid out similar to
`Topology/Order/ScottTopology`

## References
Statements and proofs match the first reference. Exact or equivalent statements in the 2nd reference
are provided

* [Reneta, *Duality in Domain Theory*][reneta2025]
* [Abramsky and Jung, *Domain Theory*][abramsky_gabbay_maibaum_1994]

## Tags

Scott topology, Algebraic DCPO, Stone Duality
-/

@[expose] public section

/-- notation for upward closure (↑ was taken) -/
notation x:80 "ᵘ" => Set.Ici x
namespace CompletePartialOrder
/-- approximants: read as x is way smaller than y -/
def Approx {α : Type*} [CompletePartialOrder α] (x : α) (y : α) :=
  ∀ (d : Set α), DirectedOn (· ≤ ·) d → y ≤ sSup d → ∃ a ∈ d, x ≤ a

-- A different notion of compact from what we want is defined here
-- import Mathlib.Topology.Compactness.Compact
-- compactness (in the sense we want) is only defined for CompleteLattice in the below file
-- import Mathlib.Order.CompactlyGenerated.Basic

/-- x approximates itself. Compactness is a key property and abstracted by the
`DirSupInacc` (inacessibility of directed joins property) -/
def Compact {α : Type*} [CompletePartialOrder α] (x : α) := Approx x x
/-- Set of compact points -/
def compactSet (α : Type*) [CompletePartialOrder α] := {x : α | Compact x}
/-- notation for compactSet -/
notation "𝕂" α:80 => compactSet α

/-- Compact points in the `Iic` -/
def compactLowerSet {α : Type*} [CompletePartialOrder α] (x : α) := Set.Iic x ∩ 𝕂 α

/-- Encodes notion of observable properties in programs (points are program semantics) -/
class AlgebraicDCPO (α : Type*) extends CompletePartialOrder α where
  algebraic : ∀ x : α, (compactLowerSet x).Nonempty ∧ DirectedOn (· ≤ ·) (compactLowerSet x) ∧
  x = sSup (compactLowerSet x)

end CompletePartialOrder

namespace Topology
namespace IsScott
open Topology.IsScott TopologicalSpace Set Topology CompletePartialOrder
section CompletePartialOrder

variable {α : Type*} [TopologicalSpace α] [CompletePartialOrder α]
  [IsScott α {d | DirectedOn (· ≤ ·) d}]

/-- The order from `CompletePartialOrder` and the specialization order induced by the Scott
topology, correspond. Unfortunately Mathlib's specialization order `⤳` is opposite to `≤`
Prop 3.5.2 in [reneta2025]. Prop 2.3.2(1) in [abramsky_gabbay_maibaum_1994] -/
lemma specialization_iff_ge {x y : α} : x ≤ y ↔ y ⤳ x := by
  rw [specializes_iff_forall_open]
  constructor
  · intro x_le_y u hu x_in_u
    apply (@isUpperSet_of_isOpen α {d | DirectedOn (· ≤ ·) d }) at hu
    exact hu x_le_y x_in_u
  · let u := {z : α | ¬(z ≤ y)}
    have hu: IsOpen u := by
      rw [@isOpen_iff_isUpperSet_and_dirSupInaccOn α {d | DirectedOn (· ≤ ·) d }]
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

/-- Anticipating the construction of basis proved in `isTopologicalBasis_Ici_image_compactSet`
We use the name `basis` instead of `Ici_image_compactSet` here -/
lemma isOpen_of_basis {u : Set α} (hu : u ∈ Ici '' 𝕂 α) : IsOpen u := by
  rw [@isOpen_iff_isUpperSet_and_dirSupInaccOn α {d | DirectedOn (· ≤ ·) d }]
  constructor
  · -- u is an upper set
    unfold IsUpperSet
    intro x y x_le_y hx
    simp_all only [mem_image]
    obtain ⟨e, he⟩ := hu
    obtain ⟨left, right⟩ := he
    subst right
    simp only [Ici, mem_setOf_eq] at hx ⊢
    transitivity x
    · exact hx
    · exact x_le_y
  · -- u is a Scott-Hausdorff open set, ie it has the inaccessable directed joins property
    -- However the directed sets for our topology are defined precisely as
    -- the directed sets of the our DCPOs
    -- So compact points are precisely those points which have directed innaccessable joins
    intro d hd nonempty _  x hx hx'
    simp only [mem_image] at hu
    choose y yCompact yUpper using hu
    -- rewrite `x`'s LUB propoerty in terms of sSup
    have hx : x = sSup d := by
      have hsSupd := CompletePartialOrder.lubOfDirected d hd
      exact IsLUB.unique hx hsSupd

    have hy : y ≤ sSup d := by
      rw [← hx]

      subst yUpper
      simp only [Ici, mem_setOf_eq] at hx'
      exact hx'

    choose a a_in_d ha' using yCompact d hd hy
    have a_in_u : a ∈ u := by subst yUpper hx; exact ha'
    use a
    constructor
    · exact a_in_d
    · exact a_in_u

/-- The upwards closure of a compact point which we know is open -/
def Opens.ofCompact (c : {c: α // Compact c}) : Opens α :=
  ⟨cᵘ, isOpen_of_basis <| Set.mem_image_of_mem Ici c.2⟩
/-- The upwards closure of a compact point which we know is open.
ᵘᵒ stand for upward open -/
notation c:80"ᵘᵒ"  => Opens.ofCompact c -- Ici, open

/-- A helper. This can be made more straightforward by replacing `{u : Opens α}` with
`{u : UpperSet}` and applying the additional lemma `Topology.IsScott.isUpperSet_of_isOpen`
at the point of usage. Having this lemma in this form helps inference of optional parameters. -/
private lemma Opens.mem_iff_Ici_subset {e : α} {u : Opens α} : e ∈ u ↔ eᵘ ⊆ u := by
  constructor
  · intro e_in_u
    have u_open := u.isOpen
    rw [@isOpen_iff_isUpperSet_and_dirSupInaccOn α {d | DirectedOn (· ≤ ·) d }] at u_open
    let ⟨u_Ici, _⟩ := u_open
    intro a ha
    exact u_Ici ha e_in_u
  · intro h
    exact h <| mem_Ici.2 (le_refl e)

end CompletePartialOrder

section AlgebraicDCPO
variable {D : Type*} [TopologicalSpace D] [AlgebraicDCPO D] [IsScott D {d | DirectedOn (· ≤ ·) d}]
open Opens

/-- Given any point `x` in `D` in an open set `u`, there exists a basis within `u`
which contains `x`.
In anticipation of `isTopologicalBasis_Ici_image_compactSet` we already use the word `basis` -/
lemma exists_basis_mem_basis (x : D) (u : Set D) (x_in_u : x ∈ u) (hu : IsOpen u)
    : ∃ v ∈ Ici '' 𝕂 D, x ∈ v ∧ v ⊆ u := by
  rw [@isOpen_iff_isUpperSet_and_dirSupInaccOn D {d | DirectedOn (· ≤ ·) d }] at hu

  obtain ⟨upper, hausdorff⟩ := hu
  have compactLowerBounded : ∀ x ∈ u, ∃ c: D, c ≤ x ∧ c ∈ u ∧ Compact c := by
    intro x x_in_u
    -- the Algebraicity property
    obtain ⟨nonempty, directedCls, join⟩ := AlgebraicDCPO.algebraic x

    -- We work with this cls to extract a compact elememt from it satisfying our needs
    let cls := (compactLowerSet x)

    -- by algebraicity, a point, `x`, is the meet of its `cls`
    have x_is_LUB : IsLUB cls x:= by
      rw [join]
      apply CompletePartialOrder.lubOfDirected cls directedCls

    -- We use the innacessible joins property to show get a nonempty intersection
    -- The intersection contains exactly what we want, a compact point in u and ≤ x
    have nonempty_inter := hausdorff directedCls nonempty directedCls x_is_LUB x_in_u
    simp only [compactLowerSet, inter_nonempty, mem_inter_iff] at nonempty_inter
    obtain ⟨c, ⟨hc₀, hc₁⟩, hc₂⟩ := nonempty_inter
    exact ⟨c, hc₀, hc₂, hc₁⟩

  -- given an x ∈ u, take it to its compact point
  choose f hf hf' hf'' using compactLowerBounded
  let f' : {x : D // x ∈ u} → D := fun x => f x.1 x.2
  use Ici (f' ⟨x, x_in_u⟩)

  constructor
  · simp only [Ici, mem_image]
    use (f' ⟨x, x_in_u⟩)
    constructor
    · apply hf''
    · simp only [f']
  · constructor
    · apply hf
    · intro y hy
      simp only [mem_Ici, f'] at hy
      apply upper hy
      simp_all only

/-- The upward closures of compact elements form a topological
basis under the Scott Topology. Prop 3.5.2 in [reneta2025] -/
theorem isTopologicalBasis_Ici_image_compactSet : IsTopologicalBasis (Ici '' 𝕂 D) := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · -- every upper set of a compact element in the DCPO is a Scott open set
    -- This is the true by definition direction, as compactness corresponds to Scott-Hausdorrf open,
    -- and upper set corresponds to Upper set open
    apply isOpen_of_basis
  · -- If an element `x` is in an open set `u`, we can find it in a set in the basis (`Ici c`)
    apply exists_basis_mem_basis

/-- Any open set, `u`, can be constructed as a union of sets from the basis.
    The basis consists of the upward closures of those compact elements in `u`
    This is the weaker version of the lemma using `Set`s instead of `Opens`. -/
lemma open_eq_open_of_basis (u : Set D) (hu : IsOpen u) :
  u = ⋃₀ (Ici '' { c ∈ 𝕂 D | cᵘ ⊆ u}) := by
  ext e
  simp only [sUnion_image, mem_setOf_eq, mem_iUnion, exists_prop]
  constructor
  · intro e_in_u
    choose c' hc'₀ e_in_c' hc'₁ using exists_basis_mem_basis e u e_in_u hu
    obtain ⟨c, hc₀, c'_eq⟩ := hc'₀
    use c
    simp_all only [and_self]
  · rintro ⟨c, ⟨hc, hc'⟩, e_in_c'⟩
    apply hc'
    simp_all only

/-- See `open_eq_open_of_basis`
    This is the stronger version of the lemma using `Opens` instead of `Set`s.
    The weaker version is still useful as it is easier to use when sufficient.
    We don't reuse the previous result to prove this, since the proof turns out just as long -/
lemma open_eq_open_of_basis' (u : Opens D) :
    u = sSup ({ o | ∃ (c : D) (hc : c ∈ 𝕂 D), c ∈ u ∧ (o = ⟨c, hc⟩ᵘᵒ) }) := by
  ext e
  simp only [SetLike.mem_coe]
  constructor
  · intro e_in_u
    choose c' hc'₀ e_in_c' hc'₁ using exists_basis_mem_basis e u e_in_u u.isOpen
    simp only [Opens.mem_sSup]
    use ⟨c', isOpen_of_basis hc'₀⟩
    constructor
    · obtain ⟨c, hc₀, c'_eq⟩ := hc'₀
      simp only [ofCompact]
      rw [← c'_eq] at hc'₁
      use c; use hc₀; use mem_iff_Ici_subset.2 hc'₁
      simp only [Opens.mk.injEq]
      exact id (Eq.symm c'_eq)
    · exact e_in_c'
  · rintro he
    simp only [Opens.mem_sSup] at he
    obtain ⟨c', hc'₀, he⟩ := he
    obtain ⟨c, hc₀, hc₁, hc'₁⟩ := hc'₀
    rw [mem_iff_Ici_subset] at hc₁
    rw [ofCompact] at hc'₁
    rw [hc'₁] at he
    exact Set.mem_of_mem_of_subset he hc₁

end AlgebraicDCPO

section Sober
open Locale TopCat CategoryTheory TopologicalSpace Topology.IsScott Set

/-- A topological space is sober if the unit map of `adjunctionTopToLocalePT` is a
homeomorphism -/
def Sober (X : TopCat) := IsHomeomorph (adjunctionTopToLocalePT.unit.app X)

-- TODO prove equivalence of alternative defenitions of Sober
-- lemma alt_def {X: TopCat} : QuasiSober X ∧ T0Space X
--    ↔ Sober X := by sorry

/-- Lean's automation can prove this easily enough if a `simp [map_sSup, sSup_Prop_eq]`.
    But using this lemma improves readability, especially as it's used multiple times -/
lemma of_completelyPrime {D : Type*} [TopologicalSpace D]
{P : Opens D → Prop} {x : PT (Opens D)} :
  (x (sSup {u | P u})) ↔ ∃ u, P u ∧ x u := by
  simp only [map_sSup, sSup_Prop_eq]
  constructor
  · rintro ⟨h, ⟨h2, h3, h4⟩, h5⟩
    use h2
    subst h4
    exact ⟨h3, h5⟩
  · rintro ⟨u, hu, hxu⟩
    use x u
    simp only [Set.mem_image, Set.mem_setOf_eq, eq_iff_iff]
    constructor
    · use u
    · exact hxu

variable {D : Type*} [tD : TopologicalSpace D] [aD : AlgebraicDCPO D]
  [sD : IsScott D {d | DirectedOn (· ≤ ·) d}]

/-- We claim that x is entirely determined by its set of basic opens `K x`.
    Proving this correspondence establishes the homeomorphism below. -/
abbrev K (x : PT (Opens D)) := { c | ∃ hc: c ∈ 𝕂 D, x <| ⟨c, hc⟩ᵘᵒ }

/-- The set of basic opens is directed -/
lemma directed_Kₓ (x : PT (Opens D)) : DirectedOn (· ≤ ·) (K x) := by
  rintro c ⟨hc₀, hc₁⟩ d ⟨hd₀, hd₁⟩
  let inf := ⟨c, hc₀⟩ᵘᵒ  ⊓ ⟨d, hd₀⟩ᵘᵒ
  have inf_in_x : x inf := by
    simp only [map_inf, inf]
    exact ⟨hc₁, hd₁⟩

  have this := by
    rw [open_eq_open_of_basis' inf] at inf_in_x
    exact of_completelyPrime.1 inf_in_x

  obtain ⟨e', ⟨e, he₀, he'₀, he'₁⟩, he'₂⟩ := this

  rw [he'₁] at he'₂
  use e
  constructor
  · simp only [Set.mem_setOf_eq]
    exact ⟨he₀, he'₂⟩
  · simp only [Opens.ofCompact, Opens.mk_inf_mk, inf_eq_inter, Opens.mem_mk, mem_inter_iff, mem_Ici,
      inf] at he'₀ ⊢
    obtain ⟨h₁, h₂⟩ := he'₀
    exact ⟨h₁, h₂⟩

/-- Large calc proof extracted here. Showing surjectivity of the homeomorphism. -/
lemma surjectivity : Function.Surjective (localePointOfSpacePoint D) := by
      intro x
      dsimp [pt, PT] at x
      let Kₓ := K x
      let inp := sSup Kₓ
      use inp
      apply FrameHom.ext
      intro u
      simp only [eq_iff_iff]
      change sSup Kₓ ∈ u ↔ x u

      calc
        _ ↔ sSup Kₓ ∈ u.carrier := by rfl
        _ ↔ sSup Kₓ ∈ ⋃₀ (Ici '' { e ∈ 𝕂 D | eᵘ ⊆ u}) := by
          nth_rewrite 1 [open_eq_open_of_basis u.carrier u.isOpen]
          rfl
        _ ↔ ∃ e ∈ 𝕂 D, eᵘ ⊆ u ∧ e ≤ sSup Kₓ := by
          constructor
          · rintro ⟨e', he'₀, he'₁⟩
            simp only [Set.mem_image, Set.mem_setOf_eq] at he'₀
            choose e he₁ he₂ using he'₀
            use e
            simp only [← he₂, Ici, Set.mem_setOf_eq] at he'₁
            exact ⟨he₁.1, he₁.2, he'₁⟩
          · rintro ⟨e, he₀, he₁, he₂⟩
            have he'₀ : eᵘ ∈ (Ici '' {c | c ∈ 𝕂 D ∧ cᵘ ⊆ u}) := by
              simp only [Set.mem_image, Set.mem_setOf_eq]
              use e
            apply Set.subset_sUnion_of_mem at he'₀
            have he₂ : sSup Kₓ ∈ eᵘ := by aesop
            exact Set.mem_of_mem_of_subset he₂ he'₀
        _ ↔ ∃ (e c : D), c ∈ Kₓ ∧ e ∈ 𝕂 D  ∧ eᵘ ⊆ u ∧ e ≤ c := by
            constructor
            · rintro ⟨e, he₀, he'₀, he₁⟩
              use e
              choose c hc₁ hc₂ using he₀ Kₓ (directed_Kₓ x) he₁
              use c
            · rintro ⟨e, c, hc₀, he₀, he'₀, e_le_c⟩
              use e
              have he₁ : e ≤ sSup Kₓ := by
                trans c
                · assumption
                · have sSup_is_LUB := CompletePartialOrder.lubOfDirected Kₓ (directed_Kₓ x)
                  exact sSup_is_LUB.1 hc₀
              exact ⟨he₀, he'₀, he₁⟩
        _ ↔ ∃ (e c : D) (hc: c ∈ 𝕂 D), e ∈ 𝕂 D ∧ eᵘ ⊆ u ∧ cᵘ ⊆ eᵘ ∧ x (⟨c, hc⟩ᵘᵒ) := by
          constructor
          · rintro ⟨e, c, ⟨hc₀, hc₁⟩, he₀, he₁, e_le_c⟩
            use e; use c; use hc₀
            exact ⟨he₀, he₁, Ici_subset_Ici.2 e_le_c, hc₁⟩

          · rintro ⟨e, c, hc₀, he₀, he'₀, c'_le_e', hc'₀⟩
            use e; use c;
            exact ⟨⟨hc₀, hc'₀⟩, he₀, he'₀, Ici_subset_Ici.1 c'_le_e'⟩
        _ ↔ ∃ (e: D) (he: e ∈ 𝕂 D), eᵘ ⊆ u ∧ x (⟨e, he⟩ᵘᵒ) := by
          constructor
          · rintro ⟨e, c, hc₀, he₀, he'₀, c'_le_e', hc'₀⟩
            use e; use he₀; use he'₀
            have c'_inf_e'_eq_c' : ⟨c, hc₀⟩ᵘᵒ ⊓ ⟨e, he₀⟩ᵘᵒ = ⟨c, hc₀⟩ᵘᵒ :=
              by simp [Opens.ofCompact, Ici_subset_Ici.1 c'_le_e']
            have lifted : x (⟨c, hc₀⟩ᵘᵒ ⊓ ⟨e, he₀⟩ᵘᵒ) = x (⟨c, hc₀⟩ᵘᵒ) :=
              congrArg (⇑x) c'_inf_e'_eq_c'
            simp only [map_inf, inf_Prop_eq, eq_iff_iff, and_iff_left_iff_imp] at lifted
            exact lifted hc'₀
          · -- this direction is trivial as the requirements for c are all satisfied by e itself
            intro ⟨e, he₀, he'₀, he'₁⟩
            use e; use e; use he₀;
        _ ↔ x u := by
          constructor
          · let P (o: Opens D) := ∃ (c: D) (hc: c ∈ 𝕂 D), c ∈ u ∧ (o = ⟨c, hc⟩ᵘᵒ)
            -- intro he
            rintro ⟨e, he₀, he'₀, he'₁⟩
            have he': ∃ u, P u ∧ x u := by
              use ⟨e, he₀⟩ᵘᵒ
              exact ⟨⟨e, he₀, Opens.mem_iff_Ici_subset.2 he'₀, rfl⟩, he'₁⟩

            rw [← of_completelyPrime] at he'
            rw [← open_eq_open_of_basis' u] at he'
            exact he'
          · intro hu
            rw [open_eq_open_of_basis' u] at hu
            rw [of_completelyPrime] at hu

            obtain ⟨e', ⟨e, he₀, he'₀, he'₁⟩ , he'₂⟩ := hu
            rw [he'₁] at he'₂
            exact ⟨e, he₀, Opens.mem_iff_Ici_subset.1 he'₀, he'₂⟩

theorem scott_is_sober : Sober (TopCat.of D) := by
  dsimp only [Functor.id_obj, Functor.comp_obj, topToLocale_obj, adjunctionTopToLocalePT,
        topCatOpToFrm_obj_coe, hom_ofHom, Sober]
  constructor
  · continuity
  · -- Open Map
    intro u hu
    use ⟨u, hu⟩
    ext x
    simp only [Set.mem_setOf_eq, Set.image]
    dsimp only [topCatOpToFrm_obj_coe] at x
    constructor
    · intro he
      choose e he' using (surjectivity x)
      subst he'
      exact ⟨e, he, by rfl⟩
    · intro hx
      choose e he he' using hx
      subst he'
      exact he
  · -- Bijective
    constructor
    · -- Injective
      intro d e
      contrapose
      intro d_ne_e

      change ¬ ((localePointOfSpacePoint D d) = (localePointOfSpacePoint D e))
      rw [@FrameHom.ext_iff (Opens D) Prop (Opens.instCompleteLattice) Prop.instCompleteLattice
        (localePointOfSpacePoint D d) (localePointOfSpacePoint D e)]
      simp only [localePointOfSpacePoint_toFun, eq_iff_iff, not_forall]
      rcases (@Ne.not_le_or_not_ge D _ _ _ d_ne_e) with d_nle_e | e_nle_d
      · simp only [specialization_iff_ge, specializes_iff_forall_open, not_forall] at d_nle_e
        obtain ⟨u, hu, d_in_u, e_ne_u⟩ := d_nle_e
        use ⟨u, hu⟩
        simp only [Opens.mem_mk]
        intro h
        exact (and_not_self_iff (e ∈ u)).1 ⟨h.1 d_in_u, e_ne_u⟩
      · -- This follows dually from above. Attempting to resuse the above proof was unseccessfule
        -- CompletePartialOrder instance for the dual type not implemented.
        -- To do so binary relation, `r` of DirectedOn needs to be inverted,
        -- but `r` is not stored/accessible.
        -- It would be if DirectedOn was a struct rather than a function.
        simp only [specialization_iff_ge, specializes_iff_forall_open, not_forall] at e_nle_d
        obtain ⟨u, hu, e_in_u, d_ne_u⟩ := e_nle_d
        use ⟨u, hu⟩
        simp only [Opens.mem_mk]
        intro h
        exact (and_not_self_iff (d ∈ u)).1 ⟨h.2 e_in_u, d_ne_u⟩
    · -- Surjective
      exact surjectivity


end Sober
end IsScott
end Topology
