/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Order.Hom.CompleteLattice
public import Mathlib.Topology.Compactness.Bases
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.Order.Copy

/-!
# Open sets

## Summary

We define the subtype of open sets in a topological space.

## Main Definitions

### Bundled open sets

- `TopologicalSpace.Opens α` is the type of open subsets of a topological space `α`.
- `TopologicalSpace.Opens.IsBasis` is a predicate saying that a set of `Opens`s form a topological
  basis.
- `TopologicalSpace.Opens.comap`: preimage of an open set under a continuous map as a `FrameHom`.
- `Homeomorph.opensCongr`: order-preserving equivalence between open sets in the domain and the
  codomain of a homeomorphism.

### Bundled open neighborhoods

- `TopologicalSpace.OpenNhdsOf x` is the type of open subsets of a topological space `α` containing
  `x : α`.
- `TopologicalSpace.OpenNhdsOf.comap f x U` is the preimage of open neighborhood `U` of `f x` under
  `f : C(α, β)`.

## Main results

We define order structures on both `Opens α` (`CompleteLattice`, `Frame`) and `OpenNhdsOf x`
(`OrderTop`, `DistribLattice`).

## TODO

- Rename `TopologicalSpace.Opens` to `Open`?
- Port the `auto_cases` tactic version (as a plugin if the ported `auto_cases` will allow plugins).
-/

@[expose] public section


open Filter Function Order Set

open Topology

variable {ι α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

namespace TopologicalSpace

variable (α) in
/-- The type of open subsets of a topological space. -/
structure Opens where
  /-- The underlying set of a bundled `TopologicalSpace.Opens` object. -/
  carrier : Set α
  /-- The `TopologicalSpace.Opens.carrier _` is an open set. -/
  is_open' : IsOpen carrier

namespace Opens

instance : SetLike (Opens α) α where
  coe := Opens.carrier
  coe_injective' := fun ⟨_, _⟩ ⟨_, _⟩ _ => by congr

instance : PartialOrder (Opens α) := .ofSetLike (Opens α) α

instance : CanLift (Set α) (Opens α) (↑) IsOpen :=
  ⟨fun s h => ⟨⟨s, h⟩, rfl⟩⟩

instance instSecondCountableOpens [SecondCountableTopology α] (U : Opens α) :
    SecondCountableTopology U := inferInstanceAs (SecondCountableTopology U.1)

theorem «forall» {p : Opens α → Prop} : (∀ U, p U) ↔ ∀ (U : Set α) (hU : IsOpen U), p ⟨U, hU⟩ :=
  ⟨fun h _ _ => h _, fun h _ => h _ _⟩

@[simp] theorem carrier_eq_coe (U : Opens α) : U.1 = ↑U := rfl

/-- the coercion `Opens α → Set α` applied to a pair is the same as taking the first component -/
@[simp]
theorem coe_mk {U : Set α} {hU : IsOpen U} : ↑(⟨U, hU⟩ : Opens α) = U :=
  rfl

@[simp]
theorem mem_mk {x : α} {U : Set α} {h : IsOpen U} : x ∈ mk U h ↔ x ∈ U := Iff.rfl

protected theorem nonempty_coeSort {U : Opens α} : Nonempty U ↔ (U : Set α).Nonempty :=
  Set.nonempty_coe_sort

-- TODO: should this theorem be proved for a `SetLike`?
protected theorem nonempty_coe {U : Opens α} : (U : Set α).Nonempty ↔ ∃ x, x ∈ U :=
  Iff.rfl

@[ext] -- TODO: replace with `∀ x, x ∈ U ↔ x ∈ V`?
theorem ext {U V : Opens α} (h : (U : Set α) = V) : U = V :=
  SetLike.coe_injective h

theorem coe_inj {U V : Opens α} : (U : Set α) = V ↔ U = V :=
  SetLike.ext'_iff.symm

/-- A version of `Set.inclusion` not requiring definitional abuse -/
abbrev inclusion {U V : Opens α} (h : U ≤ V) : U → V := Set.inclusion h

protected theorem isOpen (U : Opens α) : IsOpen (U : Set α) :=
  U.is_open'

@[simp] theorem mk_coe (U : Opens α) : mk (↑U) U.isOpen = U := rfl

/-- See Note [custom simps projection]. -/
def Simps.coe (U : Opens α) : Set α := U

initialize_simps_projections Opens (carrier → coe, as_prefix coe)

/-- The interior of a set, as an element of `Opens`. -/
@[simps]
protected def interior (s : Set α) : Opens α :=
  ⟨interior s, isOpen_interior⟩

@[simp]
theorem mem_interior {s : Set α} {x : α} : x ∈ Opens.interior s ↔ x ∈ _root_.interior s := .rfl

theorem gc : GaloisConnection ((↑) : Opens α → Set α) Opens.interior := fun U _ =>
  ⟨fun h => interior_maximal h U.isOpen, fun h => le_trans h interior_subset⟩

/-- The Galois coinsertion between sets and opens. -/
def gi : GaloisCoinsertion (↑) (@Opens.interior α _) where
  choice s hs := ⟨s, interior_eq_iff_isOpen.mp <| le_antisymm interior_subset hs⟩
  gc := gc
  u_l_le _ := interior_subset
  choice_eq _s hs := le_antisymm hs interior_subset

instance : CompleteLattice (Opens α) :=
  CompleteLattice.copy (GaloisCoinsertion.liftCompleteLattice gi)
    -- le
    (fun U V => (U : Set α) ⊆ V) rfl
    -- top
    ⟨univ, isOpen_univ⟩ (ext interior_univ.symm)
    -- bot
    ⟨∅, isOpen_empty⟩ rfl
    -- sup
    (fun U V => ⟨↑U ∪ ↑V, U.2.union V.2⟩) rfl
    -- inf
    (fun U V => ⟨↑U ∩ ↑V, U.2.inter V.2⟩)
    (funext₂ fun U V => ext (U.2.inter V.2).interior_eq.symm)
    -- sSup
    (fun S => ⟨⋃ s ∈ S, ↑s, isOpen_biUnion fun s _ => s.2⟩)
    (funext fun _ => ext sSup_image.symm)
    -- sInf
    _ rfl

@[simp]
theorem mk_inf_mk {U V : Set α} {hU : IsOpen U} {hV : IsOpen V} :
    (⟨U, hU⟩ ⊓ ⟨V, hV⟩ : Opens α) = ⟨U ⊓ V, IsOpen.inter hU hV⟩ :=
  rfl

@[simp, norm_cast]
theorem coe_inf (s t : Opens α) : (↑(s ⊓ t) : Set α) = ↑s ∩ ↑t :=
  rfl

@[simp]
lemma mem_inf {s t : Opens α} {x : α} : x ∈ s ⊓ t ↔ x ∈ s ∧ x ∈ t := Iff.rfl

@[simp, norm_cast]
theorem coe_sup (s t : Opens α) : (↑(s ⊔ t) : Set α) = ↑s ∪ ↑t :=
  rfl

@[simp]
theorem mem_sup {s t : Opens α} {x : α} : x ∈ (s ⊔ t) ↔ x ∈ s ∨ x ∈ t :=
  .rfl

@[simp, norm_cast]
theorem coe_bot : ((⊥ : Opens α) : Set α) = ∅ :=
  rfl

@[simp]
lemma mem_bot {x : α} : x ∈ (⊥ : Opens α) ↔ False := Iff.rfl

@[simp] theorem mk_empty : (⟨∅, isOpen_empty⟩ : Opens α) = ⊥ := rfl

@[simp, norm_cast]
theorem coe_eq_empty {U : Opens α} : (U : Set α) = ∅ ↔ U = ⊥ :=
  SetLike.coe_injective.eq_iff' rfl

@[simp]
lemma mem_top (x : α) : x ∈ (⊤ : Opens α) := trivial

@[simp, norm_cast]
theorem coe_top : ((⊤ : Opens α) : Set α) = Set.univ :=
  rfl

@[simp] theorem mk_univ : (⟨univ, isOpen_univ⟩ : Opens α) = ⊤ := rfl

@[simp, norm_cast]
theorem coe_eq_univ {U : Opens α} : (U : Set α) = univ ↔ U = ⊤ :=
  SetLike.coe_injective.eq_iff' rfl

@[simp, norm_cast]
theorem coe_sSup {S : Set (Opens α)} : (↑(sSup S) : Set α) = ⋃ i ∈ S, ↑i :=
  rfl

@[simp, norm_cast]
theorem coe_finset_sup (f : ι → Opens α) (s : Finset ι) : (↑(s.sup f) : Set α) = s.sup ((↑) ∘ f) :=
  map_finset_sup (⟨⟨(↑), coe_sup⟩, coe_bot⟩ : SupBotHom (Opens α) (Set α)) _ _

@[simp, norm_cast]
theorem coe_finset_inf (f : ι → Opens α) (s : Finset ι) : (↑(s.inf f) : Set α) = s.inf ((↑) ∘ f) :=
  map_finset_inf (⟨⟨(↑), coe_inf⟩, coe_top⟩ : InfTopHom (Opens α) (Set α)) _ _

set_option backward.isDefEq.respectTransparency false in
@[simp, norm_cast]
lemma coe_disjoint {s t : Opens α} : Disjoint (s : Set α) t ↔ Disjoint s t := by
  simp [disjoint_iff, ← SetLike.coe_set_eq]

instance : Inhabited (Opens α) := ⟨⊥⟩

instance [IsEmpty α] : Unique (Opens α) where
  uniq _ := ext <| Subsingleton.elim _ _

instance [Nonempty α] : Nontrivial (Opens α) where
  exists_pair_ne := ⟨⊥, ⊤, mt coe_inj.2 empty_ne_univ⟩

@[simp, norm_cast]
theorem coe_iSup {ι} (s : ι → Opens α) : ((⨆ i, s i : Opens α) : Set α) = ⋃ i, s i := by
  simp [iSup]

theorem iSup_def {ι} (s : ι → Opens α) : ⨆ i, s i = ⟨⋃ i, s i, isOpen_iUnion fun i => (s i).2⟩ :=
  ext <| coe_iSup s

@[simp]
theorem iSup_mk {ι} (s : ι → Set α) (h : ∀ i, IsOpen (s i)) :
    (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩ :=
  iSup_def _

@[simp]
theorem mem_iSup {ι} {x : α} {s : ι → Opens α} : x ∈ iSup s ↔ ∃ i, x ∈ s i := by
  rw [← SetLike.mem_coe]
  simp

@[simp]
theorem mem_sSup {Us : Set (Opens α)} {x : α} : x ∈ sSup Us ↔ ∃ u ∈ Us, x ∈ u := by
  simp_rw [sSup_eq_iSup, mem_iSup, exists_prop]

/-- Open sets in a topological space form a frame. -/
@[implicit_reducible]
def frameMinimalAxioms : Frame.MinimalAxioms (Opens α) where
  inf_sSup_le_iSup_inf a s :=
    (ext <| by simp only [coe_inf, coe_iSup, coe_sSup, Set.inter_iUnion₂]).le

instance instFrame : Frame (Opens α) := .ofMinimalAxioms frameMinimalAxioms

/-- The coercion from open sets to sets as a `FrameHom`. -/
@[simps] protected def frameHom : FrameHom (Opens α) (Set α) where
  toFun := (·)
  map_inf' _ _ := rfl
  map_top' := rfl
  map_sSup' _ := by simp

theorem isOpenEmbedding' (U : Opens α) : IsOpenEmbedding (Subtype.val : U → α) :=
  U.isOpen.isOpenEmbedding_subtypeVal

theorem isOpenEmbedding_of_le {U V : Opens α} (i : U ≤ V) :
    IsOpenEmbedding (Set.inclusion <| SetLike.coe_subset_coe.2 i) where
  toIsEmbedding := .inclusion i
  isOpen_range := by
    rw [Set.range_inclusion i]
    exact U.isOpen.preimage continuous_subtype_val

theorem not_nonempty_iff_eq_bot (U : Opens α) : ¬Set.Nonempty (U : Set α) ↔ U = ⊥ := by
  rw [← coe_inj, coe_bot, ← Set.not_nonempty_iff_eq_empty]

theorem ne_bot_iff_nonempty (U : Opens α) : U ≠ ⊥ ↔ Set.Nonempty (U : Set α) := by
  rw [Ne, ← not_nonempty_iff_eq_bot, not_not]

/-- An open set in the indiscrete topology is either empty or the whole space. -/
theorem eq_bot_or_top [IndiscreteTopology α] (U : Opens α) :
    U = ⊥ ∨ U = ⊤ := by
  rw [← coe_eq_empty, ← coe_eq_univ, ← IndiscreteTopology.isOpen_iff]
  exact U.2

set_option backward.isDefEq.respectTransparency false in
instance [Nonempty α] [IndiscreteTopology α] : IsSimpleOrder (Opens α) where
  eq_bot_or_eq_top := eq_bot_or_top

/-- A set of `opens α` is a basis if the set of corresponding sets is a topological basis. -/
def IsBasis (B : Set (Opens α)) : Prop :=
  IsTopologicalBasis (((↑) : _ → Set α) '' B)

theorem isBasis_iff_nbhd {B : Set (Opens α)} :
    IsBasis B ↔ ∀ {U : Opens α} {x}, x ∈ U → ∃ U' ∈ B, x ∈ U' ∧ U' ≤ U := by
  constructor <;> intro h
  · rintro ⟨sU, hU⟩ x hx
    rcases h.mem_nhds_iff.mp (IsOpen.mem_nhds hU hx) with ⟨sV, ⟨⟨V, H₁, H₂⟩, hsV⟩⟩
    refine ⟨V, H₁, ?_⟩
    cases V
    dsimp at H₂
    subst H₂
    exact hsV
  · refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro sU ⟨U, -, rfl⟩
      exact U.2
    · intro x sU hx hsU
      rcases @h ⟨sU, hsU⟩ x hx with ⟨V, hV, H⟩
      exact ⟨V, ⟨V, hV, rfl⟩, H⟩

theorem isBasis_iff_cover {B : Set (Opens α)} :
    IsBasis B ↔ ∀ U : Opens α, ∃ Us, Us ⊆ B ∧ U = sSup Us := by
  constructor
  · intro hB U
    refine ⟨{ V : Opens α | V ∈ B ∧ V ≤ U }, fun U hU => hU.left, ext ?_⟩
    rw [coe_sSup, hB.open_eq_sUnion' U.isOpen]
    simp_rw [sUnion_eq_biUnion, iUnion, mem_setOf_eq, iSup_and, iSup_image]
    rfl
  · intro h
    rw [isBasis_iff_nbhd]
    intro U x hx
    rcases h U with ⟨Us, hUs, rfl⟩
    rcases mem_sSup.1 hx with ⟨U, Us, xU⟩
    exact ⟨U, hUs Us, xU, le_sSup Us⟩

/-- If `α` has a basis consisting of compact opens, then an open set in `α` is compact open iff
  it is a finite union of some elements in the basis -/
theorem IsBasis.isCompact_open_iff_eq_finite_iUnion {ι : Type*} (b : ι → Opens α)
    (hb : IsBasis (Set.range b)) (hb' : ∀ i, IsCompact (b i : Set α)) (U : Set α) :
    IsCompact U ∧ IsOpen U ↔ ∃ s : Set ι, s.Finite ∧ U = ⋃ i ∈ s, b i := by
  apply isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis fun i : ι => (b i).1
  · convert (config := { transparency := .default }) hb
    ext
    simp
  · exact hb'

lemma IsBasis.exists_finite_of_isCompact {B : Set (Opens α)} (hB : IsBasis B) {U : Opens α}
    (hU : IsCompact U.1) : ∃ Us ⊆ B, Us.Finite ∧ U = sSup Us := by
  classical
  obtain ⟨Us', hsub, hsup⟩ := isBasis_iff_cover.mp hB U
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun s : Us' ↦ s.1) (fun s ↦ s.1.2) (by simp [hsup])
  refine ⟨Finset.image Subtype.val t, subset_trans (by simp) hsub, Finset.finite_toSet _, ?_⟩
  exact le_antisymm (subset_trans ht (by simp)) (le_trans (sSup_le_sSup (by simp)) hsup.ge)

lemma IsBasis.le_iff {α} {t₁ t₂ : TopologicalSpace α}
    {Us : Set (Opens α)} (hUs : @IsBasis α t₂ Us) :
    t₁ ≤ t₂ ↔ ∀ U ∈ Us, IsOpen[t₁] U := by
  conv_lhs => rw [hUs.eq_generateFrom]
  simp [Set.subset_def, le_generateFrom_iff_subset_isOpen]

lemma isBasis_sigma {ι : Type*} {α : ι → Type*} [∀ i, TopologicalSpace (α i)]
    {B : ∀ i, Set (Opens (α i))} (hB : ∀ i, IsBasis (B i)) :
    IsBasis (⋃ i : ι, (fun U ↦ ⟨Sigma.mk i '' U.1, isOpenMap_sigmaMk _ U.2⟩) '' B i) := by
  convert TopologicalSpace.IsTopologicalBasis.sigma hB
  simp only [IsBasis, Set.image_iUnion, ← Set.image_comp]
  simp

lemma IsBasis.of_isInducing {B : Set (Opens β)} (H : IsBasis B) {f : α → β} (h : IsInducing f) :
    IsBasis { ⟨f ⁻¹' U, U.2.preimage h.continuous⟩ | U ∈ B } := by
  simp only [IsBasis] at H ⊢
  convert H.isInducing h
  ext; simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem isCompactElement_iff (s : Opens α) :
    IsCompactElement s ↔ IsCompact (s : Set α) := by
  rw [isCompact_iff_finite_subcover, CompleteLattice.isCompactElement_iff_exists_le_iSup_of_le_iSup]
  refine ⟨?_, fun H ι U hU => ?_⟩
  · introv H hU hU'
    obtain ⟨t, ht⟩ := H ι (fun i => ⟨U i, hU i⟩) (by simpa)
    refine ⟨t, Set.Subset.trans ht ?_⟩
    rw [coe_finset_sup, Finset.sup_eq_iSup]
    rfl
  · obtain ⟨t, ht⟩ :=
      H (fun i => U i) (fun i => (U i).isOpen) (by simpa using show (s : Set α) ⊆ ↑(iSup U) from hU)
    refine ⟨t, Set.Subset.trans ht ?_⟩
    simp only [Set.iUnion_subset_iff]
    change ∀ i ∈ t, U i ≤ t.sup U
    exact fun i => Finset.le_sup

/-- The preimage of an open set, as an open set. -/
def comap (f : C(α, β)) : FrameHom (Opens β) (Opens α) where
  toFun s := ⟨f ⁻¹' s, s.2.preimage f.continuous⟩
  map_sSup' s := ext <| by simp only [coe_sSup, preimage_iUnion, biUnion_image, coe_mk]
  map_inf' _ _ := rfl
  map_top' := rfl

@[simp]
theorem comap_id : comap (ContinuousMap.id α) = FrameHom.id _ :=
  FrameHom.ext fun _ => ext rfl

theorem comap_mono (f : C(α, β)) {s t : Opens β} (h : s ≤ t) : comap f s ≤ comap f t :=
  OrderHomClass.mono (comap f) h

@[simp]
theorem coe_comap (f : C(α, β)) (U : Opens β) : ↑(comap f U) = f ⁻¹' U :=
  rfl

@[simp]
theorem mem_comap {f : C(α, β)} {U : Opens β} {x : α} : x ∈ comap f U ↔ f x ∈ U := .rfl

protected theorem comap_comp (g : C(β, γ)) (f : C(α, β)) :
    comap (g.comp f) = (comap f).comp (comap g) :=
  rfl

protected theorem comap_comap (g : C(β, γ)) (f : C(α, β)) (U : Opens γ) :
    comap f (comap g U) = comap (g.comp f) U :=
  rfl

theorem comap_injective [T0Space β] : Injective (comap : C(α, β) → FrameHom (Opens β) (Opens α)) :=
  fun f g h =>
  ContinuousMap.ext fun a =>
    Inseparable.eq <|
      inseparable_iff_forall_isOpen.2 fun s hs =>
        have : comap f ⟨s, hs⟩ = comap g ⟨s, hs⟩ := DFunLike.congr_fun h ⟨_, hs⟩
        show a ∈ f ⁻¹' s ↔ a ∈ g ⁻¹' s from Set.ext_iff.1 (coe_inj.2 this) a

/-- A homeomorphism induces an order-preserving equivalence on open sets, by taking comaps. -/
@[simps -fullyApplied apply]
def _root_.Homeomorph.opensCongr (f : α ≃ₜ β) : Opens α ≃o Opens β where
  toFun := Opens.comap (f.symm : C(β, α))
  invFun := Opens.comap (f : C(α, β))
  left_inv _ := ext <| f.toEquiv.preimage_symm_preimage _
  right_inv _ := ext <| f.toEquiv.symm_preimage_preimage _
  map_rel_iff' := by
    simp only [← SetLike.coe_subset_coe]; exact f.symm.surjective.preimage_subset_preimage_iff

@[simp]
theorem _root_.Homeomorph.opensCongr_symm (f : α ≃ₜ β) : f.opensCongr.symm = f.symm.opensCongr :=
  rfl

instance [Finite α] : Finite (Opens α) :=
  Finite.of_injective _ SetLike.coe_injective

end Opens

/-- The open neighborhoods of a point. See also `Opens` or `nhds`. -/
structure OpenNhdsOf (x : α) extends Opens α where
  /-- The point `x` belongs to every `U : TopologicalSpace.OpenNhdsOf x`. -/
  mem' : x ∈ carrier

namespace OpenNhdsOf

variable {x : α}

theorem toOpens_injective : Injective (toOpens : OpenNhdsOf x → Opens α)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

instance : SetLike (OpenNhdsOf x) α where
  coe U := U.1
  coe_injective' := SetLike.coe_injective.comp toOpens_injective

instance : PartialOrder (OpenNhdsOf x) := .ofSetLike (OpenNhdsOf x) α

instance canLiftSet : CanLift (Set α) (OpenNhdsOf x) (↑) fun s => IsOpen s ∧ x ∈ s :=
  ⟨fun s hs => ⟨⟨⟨s, hs.1⟩, hs.2⟩, rfl⟩⟩

protected theorem mem (U : OpenNhdsOf x) : x ∈ U :=
  U.mem'

protected theorem isOpen (U : OpenNhdsOf x) : IsOpen (U : Set α) :=
  U.is_open'

instance : OrderTop (OpenNhdsOf x) where
  top := ⟨⊤, Set.mem_univ _⟩
  le_top _ := subset_univ _

instance : Inhabited (OpenNhdsOf x) := ⟨⊤⟩
instance : Min (OpenNhdsOf x) := ⟨fun U V => ⟨U.1 ⊓ V.1, U.2, V.2⟩⟩
instance : Max (OpenNhdsOf x) := ⟨fun U V => ⟨U.1 ⊔ V.1, Or.inl U.2⟩⟩

instance [Subsingleton α] : Unique (OpenNhdsOf x) where
  uniq U := SetLike.ext' <| Subsingleton.eq_univ_of_nonempty ⟨x, U.mem⟩

instance : DistribLattice (OpenNhdsOf x) :=
  toOpens_injective.distribLattice _ .rfl .rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

theorem basis_nhds : (𝓝 x).HasBasis (fun _ : OpenNhdsOf x => True) (↑) :=
  (nhds_basis_opens x).to_hasBasis (fun U hU => ⟨⟨⟨U, hU.2⟩, hU.1⟩, trivial, Subset.rfl⟩) fun U _ =>
    ⟨U, ⟨⟨U.mem, U.isOpen⟩, Subset.rfl⟩⟩

/-- Preimage of an open neighborhood of `f x` under a continuous map `f` as a `LatticeHom`. -/
def comap (f : C(α, β)) (x : α) : LatticeHom (OpenNhdsOf (f x)) (OpenNhdsOf x) where
  toFun U := ⟨Opens.comap f U.1, U.mem⟩
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

end OpenNhdsOf

end TopologicalSpace

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: once we port `auto_cases`, port this
-- namespace Tactic

-- namespace AutoCases

-- /-- Find an `auto_cases_tac` which matches `TopologicalSpace.Opens`. -/
-- unsafe def opens_find_tac : expr → Option auto_cases_tac
--   | q(TopologicalSpace.Opens _) => tac_cases
--   | _ => none

-- end AutoCases

-- /-- A version of `tactic.auto_cases` that works for `TopologicalSpace.Opens`. -/
-- @[hint_tactic]
-- unsafe def auto_cases_opens : tactic String :=
--   auto_cases tactic.auto_cases.opens_find_tac

-- end Tactic
