/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.Lattice

/-!
# Lower and Upper topology

This file introduces the lower topology on a preorder as the topology generated by the complements
of the left-closed right-infinite intervals.

For completeness we also introduce the dual upper topology, generated by the complements of the
right-closed left-infinite intervals.

## Main statements

- `IsLower.t0Space` - the lower topology on a partial order is T₀
- `IsLower.isTopologicalBasis` - the complements of the upper closures of finite
  subsets form a basis for the lower topology
- `IsLower.continuousInf` - the inf map is continuous with respect to the lower topology

## Implementation notes

A type synonym `WithLower` is introduced and for a preorder `α`, `WithLower α`
is made an instance of `TopologicalSpace` by the topology generated by the complements of the
closed intervals to infinity.

We define a mixin class `IsLower` for the class of types which are both a preorder and a
topology and where the topology is generated by the complements of the closed intervals to infinity.
It is shown that `WithLower α` is an instance of `IsLower`.

Similarly for the upper topology.

## Motivation

The lower topology is used with the `Scott` topology to define the Lawson topology. The restriction
of the lower topology to the spectrum of a complete lattice coincides with the hull-kernel topology.

## References

* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]

## Tags

lower topology, upper topology, preorder
-/

open Set TopologicalSpace Topology

namespace Topology

/--
The lower topology is the topology generated by the complements of the left-closed right-infinite
intervals.
-/
def lower (α : Type*) [Preorder α] : TopologicalSpace α := generateFrom {s | ∃ a, (Ici a)ᶜ = s}

/--
The upper topology is the topology generated by the complements of the right-closed left-infinite
intervals.
-/
def upper (α : Type*) [Preorder α] : TopologicalSpace α := generateFrom {s | ∃ a, (Iic a)ᶜ = s}

/-- Type synonym for a preorder equipped with the lower set topology. -/
def WithLower (α : Type*) := α

variable {α β : Type*}

namespace WithLower

/-- `toLower` is the identity function to the `WithLower` of a type. -/
@[match_pattern] def toLower : α ≃ WithLower α := Equiv.refl _

/-- `ofLower` is the identity function from the `WithLower` of a type. -/
@[match_pattern] def ofLower : WithLower α ≃ α := Equiv.refl _

@[simp] lemma toLower_symm : (@toLower α).symm = ofLower := rfl
@[deprecated (since := "2024-12-16")] alias to_WithLower_symm_eq := toLower_symm

@[simp] lemma ofLower_symm : (@ofLower α).symm = toLower := rfl
@[deprecated (since := "2024-12-16")] alias of_WithLower_symm_eq := ofLower_symm

@[simp] lemma toLower_ofLower (a : WithLower α) : toLower (ofLower a) = a := rfl

@[simp] lemma ofLower_toLower (a : α) : ofLower (toLower a) = a := rfl

lemma toLower_inj {a b : α} : toLower a = toLower b ↔ a = b := Iff.rfl

-- Porting note: removed @[simp] to make linter happy
theorem ofLower_inj {a b : WithLower α} : ofLower a = ofLower b ↔ a = b :=
  Iff.rfl

/-- A recursor for `WithLower`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
protected def rec {β : WithLower α → Sort*} (h : ∀ a, β (toLower a)) : ∀ a, β a := fun a =>
  h (ofLower a)

instance [Nonempty α] : Nonempty (WithLower α) := ‹Nonempty α›
instance [Inhabited α] : Inhabited (WithLower α) := ‹Inhabited α›

section Preorder

variable [Preorder α] {s : Set α}

instance : Preorder (WithLower α) := ‹Preorder α›
instance : TopologicalSpace (WithLower α) := lower (WithLower α)

@[simp] lemma toLower_le_toLower {x y : α} : toLower x ≤ toLower y ↔ x ≤ y := .rfl
@[simp] lemma toLower_lt_toLower {x y : α} : toLower x < toLower y ↔ x < y := .rfl
@[simp] lemma ofLower_le_ofLower {x y : WithLower α} : ofLower x ≤ ofLower y ↔ x ≤ y := .rfl
@[simp] lemma ofLower_lt_ofLower {x y : WithLower α} : ofLower x < ofLower y ↔ x < y := .rfl

lemma isOpen_preimage_ofLower : IsOpen (ofLower ⁻¹' s) ↔ IsOpen[lower α] s := Iff.rfl

lemma isOpen_def (T : Set (WithLower α)) : IsOpen T ↔ IsOpen[lower α] (WithLower.toLower ⁻¹' T) :=
  Iff.rfl

theorem continuous_toLower [TopologicalSpace α] [ClosedIciTopology α] :
    Continuous (toLower : α → WithLower α) :=
  continuous_generateFrom_iff.mpr <| by rintro _ ⟨a, rfl⟩; exact isClosed_Ici.isOpen_compl

end Preorder

instance [PartialOrder α] : PartialOrder (WithLower α) := ‹PartialOrder α›
instance [LinearOrder α] : LinearOrder (WithLower α) := ‹LinearOrder α›

end WithLower

/-- Type synonym for a preorder equipped with the upper topology. -/
def WithUpper (α : Type*) := α
namespace WithUpper

/-- `toUpper` is the identity function to the `WithUpper` of a type. -/
@[match_pattern] def toUpper : α ≃ WithUpper α := Equiv.refl _

/-- `ofUpper` is the identity function from the `WithUpper` of a type. -/
@[match_pattern] def ofUpper : WithUpper α ≃ α := Equiv.refl _

@[simp] lemma toUpper_symm {α} : (@toUpper α).symm = ofUpper := rfl
@[deprecated (since := "2024-12-16")] alias to_WithUpper_symm_eq := toUpper_symm
@[simp] lemma ofUpper_symm : (@ofUpper α).symm = toUpper := rfl
@[deprecated (since := "2024-12-16")] alias of_WithUpper_symm_eq := ofUpper_symm
@[simp] lemma toUpper_ofUpper (a : WithUpper α) : toUpper (ofUpper a) = a := rfl
@[simp] lemma ofUpper_toUpper (a : α) : ofUpper (toUpper a) = a := rfl
lemma toUpper_inj {a b : α} : toUpper a = toUpper b ↔ a = b := Iff.rfl
lemma ofUpper_inj {a b : WithUpper α} : ofUpper a = ofUpper b ↔ a = b := Iff.rfl

/-- A recursor for `WithUpper`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
protected def rec {β : WithUpper α → Sort*} (h : ∀ a, β (toUpper a)) : ∀ a, β a := fun a =>
  h (ofUpper a)

instance [Nonempty α] : Nonempty (WithUpper α) := ‹Nonempty α›
instance [Inhabited α] : Inhabited (WithUpper α) := ‹Inhabited α›

section Preorder

variable [Preorder α] {s : Set α}

instance : Preorder (WithUpper α) := ‹Preorder α›
instance : TopologicalSpace (WithUpper α) := upper (WithUpper α)

@[simp] lemma toUpper_le_toUpper {x y : α} : toUpper x ≤ toUpper y ↔ x ≤ y := .rfl
@[simp] lemma toUpper_lt_toUpper {x y : α} : toUpper x < toUpper y ↔ x < y := .rfl
@[simp] lemma ofUpper_le_ofUpper {x y : WithUpper α} : ofUpper x ≤ ofUpper y ↔ x ≤ y := .rfl
@[simp] lemma ofUpper_lt_ofUpper {x y : WithUpper α} : ofUpper x < ofUpper y ↔ x < y := .rfl

lemma isOpen_preimage_ofUpper : IsOpen (ofUpper ⁻¹' s) ↔ (upper α).IsOpen s := Iff.rfl

lemma isOpen_def {s : Set (WithUpper α)} : IsOpen s ↔ (upper α).IsOpen (toUpper ⁻¹' s) := Iff.rfl

theorem continuous_toUpper [TopologicalSpace α] [ClosedIicTopology α] :
    Continuous (toUpper : α → WithUpper α) :=
  continuous_generateFrom_iff.mpr <| by rintro _ ⟨a, rfl⟩; exact isClosed_Iic.isOpen_compl

end Preorder

instance [PartialOrder α] : PartialOrder (WithUpper α) := ‹PartialOrder α›
instance [LinearOrder α] : LinearOrder (WithUpper α) := ‹LinearOrder α›

end WithUpper

/--
The lower topology is the topology generated by the complements of the left-closed right-infinite
intervals.
-/
class IsLower (α : Type*) [t : TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_lowerTopology : t = lower α

attribute [nolint docBlame] IsLower.topology_eq_lowerTopology

/--
The upper topology is the topology generated by the complements of the right-closed left-infinite
intervals.
-/
class IsUpper (α : Type*) [t : TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_upperTopology : t = upper α
attribute [nolint docBlame] IsUpper.topology_eq_upperTopology

instance [Preorder α] : IsLower (WithLower α) := ⟨rfl⟩
instance [Preorder α] : IsUpper (WithUpper α) := ⟨rfl⟩

/--
The lower topology is homeomorphic to the upper topology on the dual order
-/
def WithLower.toDualHomeomorph [Preorder α] : WithLower α ≃ₜ WithUpper αᵒᵈ where
  toFun := OrderDual.toDual
  invFun := OrderDual.ofDual
  left_inv := OrderDual.toDual_ofDual
  right_inv := OrderDual.ofDual_toDual
  continuous_toFun := continuous_coinduced_rng
  continuous_invFun := continuous_coinduced_rng

namespace IsLower

/-- The complements of the upper closures of finite sets are a collection of lower sets
which form a basis for the lower topology. -/
def lowerBasis (α : Type*) [Preorder α] :=
  { s : Set α | ∃ t : Set α, t.Finite ∧ (upperClosure t : Set α)ᶜ = s }

section Preorder

variable (α)
variable [Preorder α] [TopologicalSpace α] [IsLower α] {s : Set α}

lemma topology_eq : ‹_› = lower α := topology_eq_lowerTopology

variable {α}

/-- If `α` is equipped with the lower topology, then it is homeomorphic to `WithLower α`.
-/
def withLowerHomeomorph : WithLower α ≃ₜ α :=
  WithLower.ofLower.toHomeomorphOfIsInducing ⟨by erw [topology_eq α, induced_id]; rfl⟩

theorem isOpen_iff_generate_Ici_compl : IsOpen s ↔ GenerateOpen { t | ∃ a, (Ici a)ᶜ = t } s := by
  rw [topology_eq α]; rfl

instance _root_.OrderDual.instIsUpper [Preorder α] [TopologicalSpace α] [IsLower α] :
    IsUpper αᵒᵈ where
  topology_eq_upperTopology := topology_eq_lowerTopology (α := α)

/-- Left-closed right-infinite intervals [a, ∞) are closed in the lower topology. -/
instance : ClosedIciTopology α :=
  ⟨fun a ↦ isOpen_compl_iff.1 <| isOpen_iff_generate_Ici_compl.2 <| GenerateOpen.basic _ ⟨a, rfl⟩⟩

-- Porting note: The old `IsLower.isClosed_Ici` was removed, since one can now use
-- the general `isClosed_Ici` lemma thanks to the instance above.

/-- The upper closure of a finite set is closed in the lower topology. -/
theorem isClosed_upperClosure (h : s.Finite) : IsClosed (upperClosure s : Set α) := by
  simp only [← UpperSet.iInf_Ici, UpperSet.coe_iInf]
  exact h.isClosed_biUnion fun _ _ => isClosed_Ici

/-- Every set open in the lower topology is a lower set. -/
theorem isLowerSet_of_isOpen (h : IsOpen s) : IsLowerSet s := by
  -- Porting note: `rw` leaves a shadowed assumption
  replace h := isOpen_iff_generate_Ici_compl.1 h
  induction h with
  | basic u h' => obtain ⟨a, rfl⟩ := h'; exact (isUpperSet_Ici a).compl
  | univ => exact isLowerSet_univ
  | inter u v _ _ hu2 hv2 => exact hu2.inter hv2
  | sUnion _ _ ih => exact isLowerSet_sUnion ih

theorem isUpperSet_of_isClosed (h : IsClosed s) : IsUpperSet s :=
  isLowerSet_compl.1 <| isLowerSet_of_isOpen h.isOpen_compl

theorem tendsto_nhds_iff_not_le {β : Type*} {f : β → α} {l : Filter β} {x : α} :
    Filter.Tendsto f l (𝓝 x) ↔ ∀ y, ¬y ≤ x → ∀ᶠ z in l, ¬y ≤ f z := by
  simp [topology_eq_lowerTopology, tendsto_nhds_generateFrom_iff, Filter.Eventually, Ici,
    compl_setOf]

/--
The closure of a singleton `{a}` in the lower topology is the left-closed right-infinite interval
[a, ∞).
-/
@[simp]
theorem closure_singleton (a : α) : closure {a} = Ici a :=
  Subset.antisymm ((closure_minimal fun _ h => h.ge) <| isClosed_Ici) <|
    (isUpperSet_of_isClosed isClosed_closure).Ici_subset <| subset_closure rfl

protected theorem isTopologicalBasis : IsTopologicalBasis (lowerBasis α) := by
  convert isTopologicalBasis_of_subbasis (topology_eq α)
  simp_rw [lowerBasis, coe_upperClosure, compl_iUnion]
  ext s
  constructor
  · rintro ⟨F, hF, rfl⟩
    refine ⟨(fun a => (Ici a)ᶜ) '' F, ⟨hF.image _, image_subset_iff.2 fun _ _ => ⟨_, rfl⟩⟩, ?_⟩
    simp only [sInter_image]
  · rintro ⟨F, ⟨hF, hs⟩, rfl⟩
    haveI := hF.to_subtype
    rw [subset_def, Subtype.forall'] at hs
    choose f hf using hs
    exact ⟨_, finite_range f, by simp_rw [biInter_range, hf, sInter_eq_iInter]⟩

/-- A function `f : β → α` with lower topology in the codomain is continuous
if and only if the preimage of every interval `Set.Ici a` is a closed set.
-/
lemma continuous_iff_Ici [TopologicalSpace β] {f : β → α} :
    Continuous f ↔ ∀ a, IsClosed (f ⁻¹' (Ici a)) := by
  obtain rfl := IsLower.topology_eq α
  simp [continuous_generateFrom_iff]

end Preorder

section PartialOrder

variable [PartialOrder α] [TopologicalSpace α] [IsLower α]

-- see Note [lower instance priority]
/-- The lower topology on a partial order is T₀. -/
instance (priority := 90) t0Space : T0Space α :=
  (t0Space_iff_inseparable α).2 fun x y h =>
    Ici_injective <| by simpa only [inseparable_iff_closure_eq, closure_singleton] using h

end PartialOrder

section LinearOrder

variable [LinearOrder α] [TopologicalSpace α] [IsLower α]

lemma isTopologicalBasis_insert_univ_subbasis :
    IsTopologicalBasis (insert univ {s : Set α | ∃ a, (Ici a)ᶜ = s}) :=
  isTopologicalBasis_of_subbasis_of_inter (by rw [topology_eq α, lower]) (by
    rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
    use b ⊓ c
    rw [compl_Ici, compl_Ici, compl_Ici, Iio_inter_Iio])

theorem tendsto_nhds_iff_lt {β : Type*} {f : β → α} {l : Filter β} {x : α} :
    Filter.Tendsto f l (𝓝 x) ↔ ∀ y, x < y → ∀ᶠ z in l, f z < y := by
  simp only [tendsto_nhds_iff_not_le, not_le]

end LinearOrder

section CompleteLinearOrder

variable [CompleteLinearOrder α] [t : TopologicalSpace α] [IsLower α]

lemma isTopologicalSpace_basis (U : Set α) : IsOpen U ↔ U = univ ∨ ∃ a, (Ici a)ᶜ = U := by
  by_cases hU : U = univ
  · simp only [hU, isOpen_univ, compl_Ici, true_or]
  refine ⟨?_, isTopologicalBasis_insert_univ_subbasis.isOpen⟩
  intro hO
  apply Or.inr
  convert IsTopologicalBasis.open_eq_sUnion isTopologicalBasis_insert_univ_subbasis hO
  constructor
  · intro ⟨a, ha⟩
    use {U}
    constructor
    · apply subset_trans (singleton_subset_iff.mpr _) (subset_insert _ _)
      use a
    · rw [sUnion_singleton]
  · intro ⟨S, hS1, hS2⟩
    have hUS : univ ∉ S := by
      by_contra hUS'
      apply hU
      rw [hS2]
      exact sUnion_eq_univ_iff.mpr (fun a => ⟨univ, hUS', trivial⟩)
    use sSup {a | (Ici a)ᶜ ∈ S}
    rw [hS2, sUnion_eq_compl_sInter_compl, compl_inj_iff]
    apply le_antisymm
    · intro b hb
      simp only [sInter_image, mem_iInter, mem_compl_iff]
      intro s hs
      obtain ⟨a,ha⟩ := (subset_insert_iff_of_not_mem hUS).mp hS1 hs
      subst hS2 ha
      simp_all only [compl_Ici, mem_Ici, sSup_le_iff, mem_setOf_eq, mem_Iio, not_lt]
    · intro b hb
      rw [mem_Ici, sSup_le_iff]
      intro c hc
      simp only [sInter_image, mem_iInter] at hb
      rw [← not_lt, ← mem_Iio, ← compl_Ici]
      exact hb _ hc

end CompleteLinearOrder

end IsLower


namespace IsUpper

/-- The complements of the lower closures of finite sets are a collection of upper sets
which form a basis for the upper topology. -/
def upperBasis (α : Type*) [Preorder α] :=
  { s : Set α | ∃ t : Set α, t.Finite ∧ (lowerClosure t : Set α)ᶜ = s }

section Preorder

variable (α)
variable [Preorder α] [TopologicalSpace α] [IsUpper α] {s : Set α}

lemma topology_eq : ‹_› = upper α := topology_eq_upperTopology

variable {α}

/-- If `α` is equipped with the upper topology, then it is homeomorphic to `WithUpper α`.
-/
def withUpperHomeomorph : WithUpper α ≃ₜ α :=
  WithUpper.ofUpper.toHomeomorphOfIsInducing ⟨by erw [topology_eq α, induced_id]; rfl⟩

theorem isOpen_iff_generate_Iic_compl : IsOpen s ↔ GenerateOpen { t | ∃ a, (Iic a)ᶜ = t } s := by
  rw [topology_eq α]; rfl

instance _root_.OrderDual.instIsLower [Preorder α] [TopologicalSpace α] [IsUpper α] :
    IsLower αᵒᵈ where
  topology_eq_lowerTopology := topology_eq_upperTopology (α := α)

/-- Left-infinite right-closed intervals (-∞,a] are closed in the upper topology. -/
instance : ClosedIicTopology α :=
  ⟨fun a ↦ isOpen_compl_iff.1 <| isOpen_iff_generate_Iic_compl.2 <| GenerateOpen.basic _ ⟨a, rfl⟩⟩

/-- The lower closure of a finite set is closed in the upper topology. -/
theorem isClosed_lowerClosure (h : s.Finite) : IsClosed (lowerClosure s : Set α) :=
  IsLower.isClosed_upperClosure (α := αᵒᵈ) h

/-- Every set open in the upper topology is a upper set. -/
theorem isUpperSet_of_isOpen (h : IsOpen s) : IsUpperSet s :=
  IsLower.isLowerSet_of_isOpen (α := αᵒᵈ) h

theorem isLowerSet_of_isClosed (h : IsClosed s) : IsLowerSet s :=
  isUpperSet_compl.1 <| isUpperSet_of_isOpen h.isOpen_compl

theorem tendsto_nhds_iff_not_le {β : Type*} {f : β → α} {l : Filter β} {x : α} :
    Filter.Tendsto f l (𝓝 x) ↔ ∀ y, ¬x ≤ y → ∀ᶠ z in l, ¬f z ≤ y :=
  IsLower.tendsto_nhds_iff_not_le (α := αᵒᵈ)

/--
The closure of a singleton `{a}` in the upper topology is the left-infinite right-closed interval
(-∞,a].
-/
@[simp]
theorem closure_singleton (a : α) : closure {a} = Iic a :=
  IsLower.closure_singleton (α := αᵒᵈ) _

protected theorem isTopologicalBasis : IsTopologicalBasis (upperBasis α) :=
  IsLower.isTopologicalBasis (α := αᵒᵈ)

/-- A function `f : β → α` with upper topology in the codomain is continuous
if and only if the preimage of every interval `Set.Iic a` is a closed set. -/
lemma continuous_iff_Iic [TopologicalSpace β] {f : β → α} :
    Continuous f ↔ ∀ a, IsClosed (f ⁻¹' (Iic a)) :=
  IsLower.continuous_iff_Ici (α := αᵒᵈ)

end Preorder


section PartialOrder

variable [PartialOrder α] [TopologicalSpace α] [IsUpper α]

-- see Note [lower instance priority]
/-- The upper topology on a partial order is T₀. -/
instance (priority := 90) t0Space : T0Space α :=
  IsLower.t0Space (α := αᵒᵈ)

end PartialOrder

section LinearOrder

variable [LinearOrder α] [TopologicalSpace α] [IsUpper α]

lemma isTopologicalBasis_insert_univ_subbasis :
    IsTopologicalBasis (insert univ {s : Set α | ∃ a, (Iic a)ᶜ = s}) :=
  IsLower.isTopologicalBasis_insert_univ_subbasis (α := αᵒᵈ)

theorem tendsto_nhds_iff_lt {β : Type*} {f : β → α} {l : Filter β} {x : α} :
    Filter.Tendsto f l (𝓝 x) ↔ ∀ y < x, ∀ᶠ z in l, y < f z :=
  IsLower.tendsto_nhds_iff_lt (α := αᵒᵈ)

end LinearOrder

section CompleteLinearOrder

variable [CompleteLinearOrder α] [t : TopologicalSpace α] [IsUpper α]

lemma isTopologicalSpace_basis (U : Set α) : IsOpen U ↔ U = univ ∨ ∃ a, (Iic a)ᶜ = U :=
  IsLower.isTopologicalSpace_basis (α := αᵒᵈ) U

end CompleteLinearOrder

end IsUpper

instance instIsLowerProd [Preorder α] [TopologicalSpace α] [IsLower α]
    [OrderBot α] [Preorder β] [TopologicalSpace β] [IsLower β] [OrderBot β] :
    IsLower (α × β) where
  topology_eq_lowerTopology := by
    refine le_antisymm (le_generateFrom ?_) ?_
    · rintro _ ⟨x, rfl⟩
      exact (isClosed_Ici.prod isClosed_Ici).isOpen_compl
    rw [(IsLower.isTopologicalBasis.prod
      IsLower.isTopologicalBasis).eq_generateFrom, le_generateFrom_iff_subset_isOpen,
      image2_subset_iff]
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    dsimp
    simp_rw [coe_upperClosure, compl_iUnion, prod_eq, preimage_iInter, preimage_compl]
    -- without `let`, `refine` tries to use the product topology and fails
    let _ : TopologicalSpace (α × β) := lower (α × β)
    refine (hs.isOpen_biInter fun a _ => ?_).inter (ht.isOpen_biInter fun b _ => ?_)
    · exact GenerateOpen.basic _ ⟨(a, ⊥), by simp [Ici_prod_eq, prod_univ]⟩
    · exact GenerateOpen.basic _ ⟨(⊥, b), by simp [Ici_prod_eq, univ_prod]⟩

instance instIsUpperProd [Preorder α] [TopologicalSpace α] [IsUpper α]
    [OrderTop α] [Preorder β] [TopologicalSpace β] [IsUpper β] [OrderTop β] :
    IsUpper (α × β) where
  topology_eq_upperTopology := by
    suffices IsLower (α × β)ᵒᵈ from IsLower.topology_eq_lowerTopology (α := (α × β)ᵒᵈ)
    exact instIsLowerProd (α := αᵒᵈ) (β := βᵒᵈ)

section CompleteLattice_IsLower

variable [CompleteLattice α] [CompleteLattice β] [TopologicalSpace α] [IsLower α]
  [TopologicalSpace β] [IsLower β]

protected lemma _root_.sInfHom.continuous (f : sInfHom α β) : Continuous f := by
  refine IsLower.continuous_iff_Ici.2 fun b => ?_
  convert isClosed_Ici (a := sInf <| f ⁻¹' Ici b)
  refine Subset.antisymm (fun a => sInf_le) fun a ha => le_trans ?_ <|
    OrderHomClass.mono (f : α →o β) ha
  refine LE.le.trans ?_ (map_sInf f _).ge
  simp

-- see Note [lower instance priority]
instance (priority := 90) IsLower.toContinuousInf : ContinuousInf α :=
  ⟨(infsInfHom : sInfHom (α × α) α).continuous⟩

end CompleteLattice_IsLower

section CompleteLattice_IsUpper

variable [CompleteLattice α] [CompleteLattice β] [TopologicalSpace α] [IsUpper α]
  [TopologicalSpace β] [IsUpper β]

protected lemma _root_.sSupHom.continuous (f : sSupHom α β) : Continuous f :=
  sInfHom.continuous (α := αᵒᵈ) (β := βᵒᵈ) (sSupHom.dual.toFun f)

-- see Note [lower instance priority]
instance (priority := 90) IsUpper.toContinuousInf : ContinuousSup α :=
  ⟨(supsSupHom : sSupHom (α × α) α).continuous⟩

end CompleteLattice_IsUpper

lemma isUpper_orderDual [Preorder α] [TopologicalSpace α] : IsUpper αᵒᵈ ↔ IsLower α := by
  constructor
  · apply OrderDual.instIsLower
  · apply OrderDual.instIsUpper

lemma isLower_orderDual [Preorder α] [TopologicalSpace α] : IsLower αᵒᵈ ↔ IsUpper α :=
  isUpper_orderDual.symm

end Topology

/-- The Sierpiński topology on `Prop` is the upper topology -/
instance : IsUpper Prop where
  topology_eq_upperTopology := by
    rw [Topology.upper, sierpinskiSpace, ← generateFrom_insert_empty]
    congr
    exact le_antisymm
      (fun h hs => by
        simp only [compl_Iic, mem_setOf_eq]
        rw [← Ioi_True, ← Ioi_False] at hs
        rcases hs with (rfl | rfl)
        · use True
        · use False)
      (by rintro _ ⟨a, rfl⟩; by_cases a <;> aesop (add simp [Ioi, lt_iff_le_not_le]))
