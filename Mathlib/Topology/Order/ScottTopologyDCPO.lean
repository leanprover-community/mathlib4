/-
Copyright (c) 2025 Edwin Fernando. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Fernando, Bhavik Mehta
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Order.ScottTopology
public import Mathlib.Topology.Order.Category.FrameAdjunction

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
  topology, correspond. Prop 3.5.2 in [renata2024]. Prop 2.3.2(1) in [abramsky_gabbay_maibaum_1994].
- `isTopologicalBasis_Ici_image_compactSet`: The upward closures of compact elements form a
  topological basis under the Scott Topology. Prop 3.5.2 in [renata2024].
- `scott_is_sober`: Main result: Scott topologies over algebraic DCPOs are Sober.
  Prop 3.5.3 in [renata2024] and Prop 2.27 in [abramsky_gabbay_maibaum_1994].

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
  [IsScott α univ]

/-- The order from `CompletePartialOrder` and the specialization order induced by the Scott
topology, correspond. Unfortunately Mathlib's specialization order `⤳` is opposite to `≤`.
Prop 3.5.2 in [renata2024]. Prop 2.3.2(1) in [abramsky_gabbay_maibaum_1994]. -/
lemma specialization_iff_ge {x y : α} : x ≤ y ↔ y ⤳ x := by
  rw [specializes_iff_forall_open]
  constructor
  · intro x_le_y u hu x_in_u
    apply isUpperSet_of_isOpen univ at hu
    exact hu x_le_y x_in_u
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

/-- The upward closure of a compact element (`Ici e`) is an open set.
We refer to the `Ici e` as basis due to `isTopologicalBasis_Ici_image_compactSet`. -/
lemma isOpen_of_basis (e : α) (he₀ : IsCompactElement e) : IsOpen (Ici e) := by
  rw [isOpen_iff_isUpperSet_and_dirSupInaccOn univ]
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
    intro d _ nonempty hd  x hx hx' -- he₁
    rw [isCompactElement_iff_le_of_directed_sSup_le] at he₀
    -- rewrite `x`'s LUB propoerty in terms of sSup
    have hx : x = sSup d := IsLUB.unique hx (lubOfDirected d hd)
    have he₁ : e ≤ sSup d := by
      rw [← hx]
      simp only [Ici, mem_setOf_eq] at hx'
      exact hx'
    choose a a_in_d ha' using he₀ d nonempty hd he₁
    exact ⟨a, a_in_d, mem_Ici.mpr ha'⟩

/-- The upwards closure of a compact element forms an open set.
In this version the data is implicit. -/
abbrev IsCompactElement.toOpen {c : α} (hc : IsCompactElement c) : Opens α :=
  ⟨Ici c, isOpen_of_basis c hc⟩

/-- A compact element as a subtype. -/
abbrev CompactElement (α : Type*) [PartialOrder α] := {c : α // IsCompactElement c}

/-- The upwards closure of a compact element forms an open set. -/
abbrev CompactElement.toOpen (c : CompactElement α) : Opens α :=
  ⟨Ici c.val, isOpen_of_basis c.val c.prop⟩

end CompletePartialOrder

section AlgebraicDCPO
variable {D : Type*} [TopologicalSpace D] [AlgebraicDCPO D] [IsScott D univ]
open Opens

/-- Given any point `x` in `D` in an open set `u`, there exists
an upward closure of a compact element (`Ici e`), within `u` which contains `x`.
We refer to the `Ici e` as basis due to `isTopologicalBasis_Ici_image_compactSet`. -/
lemma exists_basis_mem_basis (x : D) (u : Set D) (x_in_u : x ∈ u) (hu : IsOpen u)
    : ∃ c, IsCompactElement c ∧ x ∈ Ici c ∧ Ici c ⊆ u := by
  rw [isOpen_iff_isUpperSet_and_dirSupInaccOn univ] at hu
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
  · -- every upper set of a compact element in the DCPO is a Scott open set
    -- This is the true by definition direction, as compactness corresponds to Scott-Hausdorrf open,
    -- and upper set corresponds to Upper set open
    simp only [image_univ, mem_image, mem_range, Subtype.exists, ↓existsAndEq, coe_mk,
      true_and, exists_prop, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    apply isOpen_of_basis
  · -- If a point `x` is in an open set `u`, we can find it in a set in the basis (`Ici c`)
    intro x u x_in_u hu
    choose c hc x_in_c' hc' using exists_basis_mem_basis x u x_in_u hu
    simp only [image_univ, mem_image, mem_range, Subtype.exists, ↓existsAndEq, coe_mk, true_and,
      exists_prop, exists_exists_and_eq_and, mem_Ici]
    use c, hc
    exact ⟨mem_Ici.1 x_in_c', Subset.refl (LE.le (Ici c)) hc'⟩

/- Any open set, `u`, can be constructed as a union (`sSup`) of sets from the basis.
The basis consists of the upward closures of those compact elements in `u`.
Strengthening from `Set` to `Opens` of `TopologicalSpace.IsTopologicalBasis.open_eq_sUnion'`. -/
lemma IsBasis.open_eq_sSup {α : Type*} [t : TopologicalSpace α] {B : Set (Opens α)}
      (hB : IsBasis B) (u : Opens α) :
    u = sSup {s : Opens α | s ∈ B ∧ s ≤ u} := by
  apply Opens.ext
  calc
  ↑u = ⋃₀ {s | s ∈ ((↑): _ → Set α) '' B ∧ s ⊆ u} := IsTopologicalBasis.open_eq_sUnion' hB u.isOpen
  _ = ↑(sSup {s | s ∈ B ∧ s ≤ u}) := by
    simp_all only [mem_image, coe_sSup, mem_setOf_eq]
    ext x : 1
    simp_all only [mem_sUnion, mem_setOf_eq, ↓existsAndEq, and_true, SetLike.coe_subset_coe,
    SetLike.mem_coe, mem_iUnion, exists_prop]

end AlgebraicDCPO

section Sober
open Locale TopCat CategoryTheory TopologicalSpace Topology.IsScott Set

/-- A topological space is sober if the unit map of `adjunctionTopToLocalePT` is a
homeomorphism -/
def Sober (X : TopCat) := IsHomeomorph (adjunctionTopToLocalePT.unit.app X)

-- TODO prove equivalence of alternative defenitions of Sober
-- lemma alt_def {X: TopCat} : QuasiSober X ∧ T0Space X
--    ↔ Sober X := by sorry

variable {D : Type*} [tD : TopologicalSpace D] [aD : AlgebraicDCPO D] [sD : IsScott D univ]

/-- The set of compact elements underlying the basic opens contained in a `PT` is directed.
It is helpful to think of a `PT`, as a set of `Opens` with some additional structure. -/
lemma directed_setOf_compactElement (x : PT (Opens D))
    : DirectedOn (· ≤ ·) {c | ∃ hc: IsCompactElement c, x hc.toOpen} := by
  rintro c ⟨hc₀, hc₁⟩ d ⟨hd₀, hd₁⟩
  simp only [mem_setOf_eq]
  let inf := hc₀.toOpen ⊓ hd₀.toOpen
  have inf_in_x : x inf := by
    simp only [map_inf, inf]
    exact ⟨hc₁, hd₁⟩
  rw [IsBasis.open_eq_sSup isTopologicalBasis_Ici_image_compactSet inf] at inf_in_x
  rw [map_sSup, sSup_Prop_eq] at inf_in_x -- completely prime property of frame hom
  obtain ⟨P, ⟨e', ⟨⟨e, he₁, he₂⟩, he'⟩, e'_in_x⟩, hP⟩ := inf_in_x
  use e, ⟨e.prop, by grind⟩
  subst he₂ e'_in_x
  have inf_eq : inf.carrier = Ici c ∩ Ici d := by simp [inf]
  have subset_inf : Ici ↑e ⊆ inf.carrier := by apply Subset.refl (LE.le e.toOpen) he'
  rw [inf_eq] at subset_inf
  apply subset_inf
  exact self_mem_Ici

/-- The set of compact elements underlying the basic opens contained in a `PT` is nonempty.
It is helpful to think of a `PT`, as a set of `Opens` with some additional structure. -/
lemma nonempty_setOf_compactElement (x : PT (Opens D))
    : {c | ∃ hc: IsCompactElement c, x hc.toOpen}.Nonempty := by
  have h_bot : IsCompactElement (⊥ : D) := by
    rw [isCompactElement_iff_le_of_directed_sSup_le]
    intro s ⟨e, he⟩ _ _
    use e, he
    exact OrderBot.bot_le e
  have top_eq_bot_toOpen : (⊤ : Opens D) = h_bot.toOpen := by
    ext e
    simp_all only [Opens.coe_top, mem_univ, Opens.coe_mk, Ici_bot]
  have h_top : x ⊤ := by
    simp only [map_top, «Prop».top_eq_true]
  rw [Set.Nonempty]
  use ⊥
  use h_bot
  rw [← top_eq_bot_toOpen]
  exact h_top

/-- Large calc proof extracted here. Showing surjectivity of the homeomorphism. -/
lemma surjectivity : Function.Surjective (localePointOfSpacePoint D) := by
  intro x
  dsimp [pt, PT] at x
  let K := {c | ∃ hc: IsCompactElement c, x hc.toOpen}
  use sSup K
  apply FrameHom.ext
  intro u
  simp only [eq_iff_iff]
  change sSup K ∈ u ↔ x u
  calc
    _ ↔ sSup K ∈ u.carrier := by rfl
    _ ↔ sSup K ∈ ⋃₀ (Ici '' { e : D | IsCompactElement e ∧ Ici e ⊆ u}) := by
      rw [IsTopologicalBasis.open_eq_sUnion'
        isTopologicalBasis_Ici_image_compactSet u.isOpen (u:= u.carrier)]
      simp_all only [image_univ, mem_image, mem_range, Subtype.exists, ↓existsAndEq,
        Opens.coe_mk, true_and, exists_prop, Opens.carrier_eq_coe, mem_sUnion, mem_setOf_eq,
        and_true, mem_Ici, sUnion_image, mem_iUnion]
    _ ↔ ∃ e : D, IsCompactElement e ∧ Ici e ⊆ u ∧ e ≤ sSup K := by
      constructor
      · rintro ⟨e', he'₀, he'₁⟩
        simp only [Set.mem_image, Set.mem_setOf_eq] at he'₀
        choose e he₁ he₂ using he'₀
        use e
        simp only [← he₂, Ici, Set.mem_setOf_eq] at he'₁
        exact ⟨he₁.1, he₁.2, he'₁⟩
      · rintro ⟨e, he₀, he₁, he₂⟩
        have he'₀ : Ici e ∈ (Ici '' {c | IsCompactElement c ∧ Ici c ⊆ u}) := by
          simp only [Set.mem_image, Set.mem_setOf_eq]
          use e
        apply Set.subset_sUnion_of_mem at he'₀
        have he₂ : sSup K ∈ Ici e := by aesop
        exact Set.mem_of_mem_of_subset he₂ he'₀
    _ ↔ ∃ (e c : D), c ∈ K ∧ IsCompactElement e ∧ Ici e ⊆ u ∧ e ≤ c := by
        constructor
        · rintro ⟨e, he₀, he'₀, he₁⟩
          use e
          have he₀' := (isCompactElement_iff_le_of_directed_sSup_le e).1 he₀
          choose c hc₁ hc₂ using
            he₀' K (nonempty_setOf_compactElement x) (directed_setOf_compactElement x) he₁
          use c
        · rintro ⟨e, c, hc₀, he₀, he'₀, e_le_c⟩
          use e
          have he₁ : e ≤ sSup K := by
            trans c
            · assumption
            · have sSup_is_LUB :=
                CompletePartialOrder.lubOfDirected K (directed_setOf_compactElement x)
              exact sSup_is_LUB.1 hc₀
          exact ⟨he₀, he'₀, he₁⟩
    _ ↔ ∃ (e c : D) (hc: IsCompactElement c),
        IsCompactElement e ∧ Ici e ⊆ u ∧ Ici c ⊆ Ici e ∧ x hc.toOpen := by
      constructor
      · rintro ⟨e, c, ⟨hc₀, hc₁⟩, he₀, he₁, e_le_c⟩
        use e; use c; use hc₀
        exact ⟨he₀, he₁, Ici_subset_Ici.2 e_le_c, hc₁⟩
      · rintro ⟨e, c, hc₀, he₀, he'₀, c'_le_e', hc'₀⟩
        use e; use c;
        exact ⟨⟨hc₀, hc'₀⟩, he₀, he'₀, Ici_subset_Ici.1 c'_le_e'⟩
    _ ↔ ∃ (e: D) (he: IsCompactElement e), Ici e ⊆ u ∧ x he.toOpen := by
      constructor
      · rintro ⟨e, c, hc₀, he₀, he'₀, c'_le_e', hc'₀⟩
        use e; use he₀; use he'₀
        have c'_inf_e'_eq_c' : hc₀.toOpen ⊓ he₀.toOpen = hc₀.toOpen :=
          by simp [IsCompactElement.toOpen, Ici_subset_Ici.1 c'_le_e']
        have lifted : x (hc₀.toOpen ⊓ he₀.toOpen) = x hc₀.toOpen :=
          congrArg (⇑x) c'_inf_e'_eq_c'
        simp only [map_inf, inf_Prop_eq, eq_iff_iff, and_iff_left_iff_imp] at lifted
        exact lifted hc'₀
      · -- this direction is trivial as the requirements for c are all satisfied by e itself
        intro ⟨e, he₀, he'₀, he'₁⟩
        use e; use e; use he₀;
    _ ↔ x u := by
      constructor
      · rintro ⟨e, he₀, he'₀, he'₁⟩
        rw [IsBasis.open_eq_sSup isTopologicalBasis_Ici_image_compactSet u]
        rw [map_sSup, sSup_Prop_eq] -- completely prime property of frame hom
        use True
        simp only [image_univ, mem_range, Subtype.exists, mem_image, mem_setOf_eq, eq_iff_iff,
          iff_true, ↓existsAndEq, true_and, and_true]
        use e, he₀
        constructor
        · apply he'₀
        · apply he'₁
      · intro hu
        rw [IsBasis.open_eq_sSup isTopologicalBasis_Ici_image_compactSet u] at hu
        rw [map_sSup, sSup_Prop_eq] at hu -- completely prime property of frame hom
        obtain ⟨P, ⟨e', ⟨⟨e, he₁, he₂⟩, he'⟩, e'_in_x⟩, hP⟩ := hu
        subst e'_in_x he₂
        use e, e.prop
        constructor
        · apply he'
        · exact hP

/-- Scott topologies over algebraic DCPOs are Sober.
  Prop 3.5.3 in [renata2024]. Prop 2.27 in [abramsky_gabbay_maibaum_1994] -/
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
    dsimp only [topToLocale_obj, topCatOpToFrm_obj_coe] at x
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
      · -- This follows dually from above. Attempting to resuse the above proof was unseccessful
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
    · exact surjectivity

end Sober
end IsScott
end Topology
