/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn

! This file was ported from Lean 3 source module topology.sets.opens
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Hom.CompleteLattice
import Mathbin.Topology.Bases
import Mathbin.Topology.Homeomorph
import Mathbin.Topology.ContinuousFunction.Basic
import Mathbin.Order.CompactlyGenerated
import Mathbin.Tactic.AutoCases

/-!
# Open sets

## Summary

We define the subtype of open sets in a topological space.

## Main Definitions

### Bundled open sets

- `opens α` is the type of open subsets of a topological space `α`.
- `opens.is_basis` is a predicate saying that a set of `opens`s form a topological basis.
- `opens.comap`: preimage of an open set under a continuous map as a `frame_hom`.
- `homeomorph.opens_congr`: order-preserving equivalence between open sets in the domain and the
  codomain of a homeomorphism.

### Bundled open neighborhoods

- `open_nhds_of x` is the type of open subsets of a topological space `α` containing `x : α`.
- `open_nhds_of.comap f x U` is the preimage of open neighborhood `U` of `f x` under `f : C(α, β)`.

## Main results

We define order structures on both `opens α` (`complete_structure`, `frame`) and `open_nhds_of x`
(`order_top`, `distrib_lattice`).
-/


open Filter Function Order Set

open Topology

variable {ι α β γ : Type _} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

namespace TopologicalSpace

variable (α)

/-- The type of open subsets of a topological space. -/
structure Opens where
  carrier : Set α
  is_open' : IsOpen carrier
#align topological_space.opens TopologicalSpace.Opens

variable {α}

namespace Opens

instance : SetLike (Opens α) α where
  coe := Opens.carrier
  coe_injective' := fun ⟨_, _⟩ ⟨_, _⟩ _ => by congr <;> assumption

instance : CanLift (Set α) (Opens α) coe IsOpen :=
  ⟨fun s h => ⟨⟨s, h⟩, rfl⟩⟩

theorem forall {p : Opens α → Prop} : (∀ U, p U) ↔ ∀ (U : Set α) (hU : IsOpen U), p ⟨U, hU⟩ :=
  ⟨fun h _ _ => h _, fun h ⟨U, hU⟩ => h _ _⟩
#align topological_space.opens.forall TopologicalSpace.Opens.forall

@[simp]
theorem carrier_eq_coe (U : Opens α) : U.1 = ↑U :=
  rfl
#align topological_space.opens.carrier_eq_coe TopologicalSpace.Opens.carrier_eq_coe

/-- the coercion `opens α → set α` applied to a pair is the same as taking the first component -/
@[simp]
theorem coe_mk {U : Set α} {hU : IsOpen U} : ↑(⟨U, hU⟩ : Opens α) = U :=
  rfl
#align topological_space.opens.coe_mk TopologicalSpace.Opens.coe_mk

@[simp]
theorem mem_mk {x : α} {U : Set α} {h : IsOpen U} :
    @Membership.Mem _ (Opens α) _ x ⟨U, h⟩ ↔ x ∈ U :=
  Iff.rfl
#align topological_space.opens.mem_mk TopologicalSpace.Opens.mem_mk

-- todo: make it `simp` for a `set_like`?
@[simp]
protected theorem nonempty_coeSort {U : Opens α} : Nonempty U ↔ (U : Set α).Nonempty :=
  Set.nonempty_coe_sort
#align topological_space.opens.nonempty_coe_sort TopologicalSpace.Opens.nonempty_coeSort

@[ext]
theorem ext {U V : Opens α} (h : (U : Set α) = V) : U = V :=
  SetLike.coe_injective h
#align topological_space.opens.ext TopologicalSpace.Opens.ext

@[simp]
theorem coe_inj {U V : Opens α} : (U : Set α) = V ↔ U = V :=
  SetLike.ext'_iff.symm
#align topological_space.opens.coe_inj TopologicalSpace.Opens.coe_inj

protected theorem isOpen (U : Opens α) : IsOpen (U : Set α) :=
  U.is_open'
#align topological_space.opens.is_open TopologicalSpace.Opens.isOpen

@[simp]
theorem mk_coe (U : Opens α) : mk (↑U) U.IsOpen = U :=
  by
  cases U
  rfl
#align topological_space.opens.mk_coe TopologicalSpace.Opens.mk_coe

/-- See Note [custom simps projection]. -/
def Simps.coe (U : Opens α) : Set α :=
  U
#align topological_space.opens.simps.coe TopologicalSpace.Opens.Simps.coe

initialize_simps_projections Opens (carrier → coe)

/-- The interior of a set, as an element of `opens`. -/
def interior (s : Set α) : Opens α :=
  ⟨interior s, isOpen_interior⟩
#align topological_space.opens.interior TopologicalSpace.Opens.interior

theorem gc : GaloisConnection (coe : Opens α → Set α) interior := fun U s =>
  ⟨fun h => interior_maximal h U.IsOpen, fun h => le_trans h interior_subset⟩
#align topological_space.opens.gc TopologicalSpace.Opens.gc

/-- The galois coinsertion between sets and opens. -/
def gi : GaloisCoinsertion coe (@interior α _)
    where
  choice s hs := ⟨s, interior_eq_iff_isOpen.mp <| le_antisymm interior_subset hs⟩
  gc := gc
  u_l_le _ := interior_subset
  choice_eq s hs := le_antisymm hs interior_subset
#align topological_space.opens.gi TopologicalSpace.Opens.gi

instance : CompleteLattice (Opens α) :=
  CompleteLattice.copy (GaloisCoinsertion.liftCompleteLattice gi)
    (-- le
    fun U V => (U : Set α) ⊆ V)
    rfl-- top
    ⟨univ, isOpen_univ⟩
    (ext interior_univ.symm)-- bot
    ⟨∅, isOpen_empty⟩
    rfl
    (-- sup
    fun U V => ⟨↑U ∪ ↑V, U.2.union V.2⟩)
    rfl
    (-- inf
    fun U V => ⟨↑U ∩ ↑V, U.2.inter V.2⟩)
    (funext₂ fun U V => ext (U.2.inter V.2).interior_eq.symm)
    (-- Sup
    fun S => ⟨⋃ s ∈ S, ↑s, isOpen_bunionᵢ fun s _ => s.2⟩)
    (funext fun S => ext supₛ_image.symm)-- Inf
    _
    rfl

@[simp]
theorem mk_inf_mk {U V : Set α} {hU : IsOpen U} {hV : IsOpen V} :
    (⟨U, hU⟩ ⊓ ⟨V, hV⟩ : Opens α) = ⟨U ⊓ V, IsOpen.inter hU hV⟩ :=
  rfl
#align topological_space.opens.mk_inf_mk TopologicalSpace.Opens.mk_inf_mk

@[simp, norm_cast]
theorem coe_inf (s t : Opens α) : (↑(s ⊓ t) : Set α) = s ∩ t :=
  rfl
#align topological_space.opens.coe_inf TopologicalSpace.Opens.coe_inf

@[simp, norm_cast]
theorem coe_sup (s t : Opens α) : (↑(s ⊔ t) : Set α) = s ∪ t :=
  rfl
#align topological_space.opens.coe_sup TopologicalSpace.Opens.coe_sup

@[simp, norm_cast]
theorem coe_bot : ((⊥ : Opens α) : Set α) = ∅ :=
  rfl
#align topological_space.opens.coe_bot TopologicalSpace.Opens.coe_bot

@[simp, norm_cast]
theorem coe_top : ((⊤ : Opens α) : Set α) = Set.univ :=
  rfl
#align topological_space.opens.coe_top TopologicalSpace.Opens.coe_top

@[simp, norm_cast]
theorem coe_supₛ {S : Set (Opens α)} : (↑(supₛ S) : Set α) = ⋃ i ∈ S, ↑i :=
  rfl
#align topological_space.opens.coe_Sup TopologicalSpace.Opens.coe_supₛ

@[simp, norm_cast]
theorem coe_finset_sup (f : ι → Opens α) (s : Finset ι) : (↑(s.sup f) : Set α) = s.sup (coe ∘ f) :=
  map_finset_sup (⟨⟨coe, coe_sup⟩, coe_bot⟩ : SupBotHom (Opens α) (Set α)) _ _
#align topological_space.opens.coe_finset_sup TopologicalSpace.Opens.coe_finset_sup

@[simp, norm_cast]
theorem coe_finset_inf (f : ι → Opens α) (s : Finset ι) : (↑(s.inf f) : Set α) = s.inf (coe ∘ f) :=
  map_finset_inf (⟨⟨coe, coe_inf⟩, coe_top⟩ : InfTopHom (Opens α) (Set α)) _ _
#align topological_space.opens.coe_finset_inf TopologicalSpace.Opens.coe_finset_inf

instance : Inhabited (Opens α) :=
  ⟨⊥⟩

theorem supᵢ_def {ι} (s : ι → Opens α) : (⨆ i, s i) = ⟨⋃ i, s i, isOpen_unionᵢ fun i => (s i).2⟩ :=
  by
  ext
  simp only [supᵢ, coe_Sup, bUnion_range]
  rfl
#align topological_space.opens.supr_def TopologicalSpace.Opens.supᵢ_def

@[simp]
theorem supᵢ_mk {ι} (s : ι → Set α) (h : ∀ i, IsOpen (s i)) :
    (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_unionᵢ h⟩ :=
  by
  rw [supr_def]
  simp
#align topological_space.opens.supr_mk TopologicalSpace.Opens.supᵢ_mk

@[simp, norm_cast]
theorem coe_supᵢ {ι} (s : ι → Opens α) : ((⨆ i, s i : Opens α) : Set α) = ⋃ i, s i := by
  simp [supr_def]
#align topological_space.opens.coe_supr TopologicalSpace.Opens.coe_supᵢ

@[simp]
theorem mem_supᵢ {ι} {x : α} {s : ι → Opens α} : x ∈ supᵢ s ↔ ∃ i, x ∈ s i :=
  by
  rw [← SetLike.mem_coe]
  simp
#align topological_space.opens.mem_supr TopologicalSpace.Opens.mem_supᵢ

@[simp]
theorem mem_supₛ {Us : Set (Opens α)} {x : α} : x ∈ supₛ Us ↔ ∃ u ∈ Us, x ∈ u := by
  simp_rw [supₛ_eq_supᵢ, mem_supr]
#align topological_space.opens.mem_Sup TopologicalSpace.Opens.mem_supₛ

instance : Frame (Opens α) :=
  { Opens.completeLattice with
    supₛ := supₛ
    inf_sup_le_supᵢ_inf := fun a s =>
      (ext <| by simp only [coe_inf, coe_supr, coe_Sup, Set.inter_unionᵢ₂]).le }

theorem openEmbedding_of_le {U V : Opens α} (i : U ≤ V) : OpenEmbedding (Set.inclusion i) :=
  { inj := Set.inclusion_injective i
    induced := (@induced_compose _ _ _ _ (Set.inclusion i) coe).symm
    open_range := by
      rw [Set.range_inclusion i]
      exact U.is_open.preimage continuous_subtype_val }
#align topological_space.opens.open_embedding_of_le TopologicalSpace.Opens.openEmbedding_of_le

theorem not_nonempty_iff_eq_bot (U : Opens α) : ¬Set.Nonempty (U : Set α) ↔ U = ⊥ := by
  rw [← coe_inj, opens.coe_bot, ← Set.not_nonempty_iff_eq_empty]
#align topological_space.opens.not_nonempty_iff_eq_bot TopologicalSpace.Opens.not_nonempty_iff_eq_bot

theorem ne_bot_iff_nonempty (U : Opens α) : U ≠ ⊥ ↔ Set.Nonempty (U : Set α) := by
  rw [Ne.def, ← opens.not_nonempty_iff_eq_bot, Classical.not_not]
#align topological_space.opens.ne_bot_iff_nonempty TopologicalSpace.Opens.ne_bot_iff_nonempty

/-- An open set in the indiscrete topology is either empty or the whole space. -/
theorem eq_bot_or_top {α} [t : TopologicalSpace α] (h : t = ⊤) (U : Opens α) : U = ⊥ ∨ U = ⊤ :=
  by
  simp only [← coe_inj]
  subst h; letI : TopologicalSpace α := ⊤
  exact (is_open_top_iff _).1 U.2
#align topological_space.opens.eq_bot_or_top TopologicalSpace.Opens.eq_bot_or_top

/-- A set of `opens α` is a basis if the set of corresponding sets is a topological basis. -/
def IsBasis (B : Set (Opens α)) : Prop :=
  IsTopologicalBasis ((coe : _ → Set α) '' B)
#align topological_space.opens.is_basis TopologicalSpace.Opens.IsBasis

theorem isBasis_iff_nbhd {B : Set (Opens α)} :
    IsBasis B ↔ ∀ {U : Opens α} {x}, x ∈ U → ∃ U' ∈ B, x ∈ U' ∧ U' ≤ U :=
  by
  constructor <;> intro h
  · rintro ⟨sU, hU⟩ x hx
    rcases h.mem_nhds_iff.mp (IsOpen.mem_nhds hU hx) with ⟨sV, ⟨⟨V, H₁, H₂⟩, hsV⟩⟩
    refine' ⟨V, H₁, _⟩
    cases V
    dsimp at H₂
    subst H₂
    exact hsV
  · refine' is_topological_basis_of_open_of_nhds _ _
    · rintro sU ⟨U, ⟨H₁, rfl⟩⟩
      exact U.2
    · intro x sU hx hsU
      rcases@h (⟨sU, hsU⟩ : opens α) x hx with ⟨V, hV, H⟩
      exact ⟨V, ⟨V, hV, rfl⟩, H⟩
#align topological_space.opens.is_basis_iff_nbhd TopologicalSpace.Opens.isBasis_iff_nbhd

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (Us «expr ⊆ » B) -/
theorem isBasis_iff_cover {B : Set (Opens α)} :
    IsBasis B ↔ ∀ U : Opens α, ∃ (Us : _)(_ : Us ⊆ B), U = supₛ Us :=
  by
  constructor
  · intro hB U
    refine' ⟨{ V : opens α | V ∈ B ∧ V ≤ U }, fun U hU => hU.left, _⟩
    apply ext
    rw [coe_Sup, hB.open_eq_sUnion' U.is_open]
    simp_rw [sUnion_eq_bUnion, Union, supᵢ_and, supᵢ_image]
    rfl
  · intro h
    rw [is_basis_iff_nbhd]
    intro U x hx
    rcases h U with ⟨Us, hUs, rfl⟩
    rcases mem_Sup.1 hx with ⟨U, Us, xU⟩
    exact ⟨U, hUs Us, xU, le_supₛ Us⟩
#align topological_space.opens.is_basis_iff_cover TopologicalSpace.Opens.isBasis_iff_cover

/-- If `α` has a basis consisting of compact opens, then an open set in `α` is compact open iff
  it is a finite union of some elements in the basis -/
theorem IsBasis.isCompact_open_iff_eq_finite_unionᵢ {ι : Type _} (b : ι → Opens α)
    (hb : IsBasis (Set.range b)) (hb' : ∀ i, IsCompact (b i : Set α)) (U : Set α) :
    IsCompact U ∧ IsOpen U ↔ ∃ s : Set ι, s.Finite ∧ U = ⋃ i ∈ s, b i :=
  by
  apply isCompact_open_iff_eq_finite_unionᵢ_of_isTopologicalBasis fun i : ι => (b i).1
  · convert hb
    ext
    simp
  · exact hb'
#align topological_space.opens.is_basis.is_compact_open_iff_eq_finite_Union TopologicalSpace.Opens.IsBasis.isCompact_open_iff_eq_finite_unionᵢ

@[simp]
theorem isCompactElement_iff (s : Opens α) :
    CompleteLattice.IsCompactElement s ↔ IsCompact (s : Set α) :=
  by
  rw [isCompact_iff_finite_subcover, CompleteLattice.isCompactElement_iff]
  refine' ⟨_, fun H ι U hU => _⟩
  · introv H hU hU'
    obtain ⟨t, ht⟩ := H ι (fun i => ⟨U i, hU i⟩) (by simpa)
    refine' ⟨t, Set.Subset.trans ht _⟩
    rw [coe_finset_sup, Finset.sup_eq_supᵢ]
    rfl
  · obtain ⟨t, ht⟩ :=
      H (fun i => U i) (fun i => (U i).IsOpen) (by simpa using show (s : Set α) ⊆ ↑(supᵢ U) from hU)
    refine' ⟨t, Set.Subset.trans ht _⟩
    simp only [Set.unionᵢ_subset_iff]
    show ∀ i ∈ t, U i ≤ t.sup U
    exact fun i => Finset.le_sup
#align topological_space.opens.is_compact_element_iff TopologicalSpace.Opens.isCompactElement_iff

/-- The preimage of an open set, as an open set. -/
def comap (f : C(α, β)) : FrameHom (Opens β) (Opens α)
    where
  toFun s := ⟨f ⁻¹' s, s.2.Preimage f.Continuous⟩
  map_Sup' s := ext <| by simp only [coe_Sup, preimage_Union, bUnion_image, coe_mk]
  map_inf' a b := rfl
  map_top' := rfl
#align topological_space.opens.comap TopologicalSpace.Opens.comap

@[simp]
theorem comap_id : comap (ContinuousMap.id α) = FrameHom.id _ :=
  FrameHom.ext fun a => ext rfl
#align topological_space.opens.comap_id TopologicalSpace.Opens.comap_id

theorem comap_mono (f : C(α, β)) {s t : Opens β} (h : s ≤ t) : comap f s ≤ comap f t :=
  OrderHomClass.mono (comap f) h
#align topological_space.opens.comap_mono TopologicalSpace.Opens.comap_mono

@[simp]
theorem coe_comap (f : C(α, β)) (U : Opens β) : ↑(comap f U) = f ⁻¹' U :=
  rfl
#align topological_space.opens.coe_comap TopologicalSpace.Opens.coe_comap

protected theorem comap_comp (g : C(β, γ)) (f : C(α, β)) :
    comap (g.comp f) = (comap f).comp (comap g) :=
  rfl
#align topological_space.opens.comap_comp TopologicalSpace.Opens.comap_comp

protected theorem comap_comap (g : C(β, γ)) (f : C(α, β)) (U : Opens γ) :
    comap f (comap g U) = comap (g.comp f) U :=
  rfl
#align topological_space.opens.comap_comap TopologicalSpace.Opens.comap_comap

theorem comap_injective [T0Space β] : Injective (comap : C(α, β) → FrameHom (Opens β) (Opens α)) :=
  fun f g h =>
  ContinuousMap.ext fun a =>
    Inseparable.eq <|
      inseparable_iff_forall_open.2 fun s hs =>
        have : comap f ⟨s, hs⟩ = comap g ⟨s, hs⟩ := FunLike.congr_fun h ⟨_, hs⟩
        show a ∈ f ⁻¹' s ↔ a ∈ g ⁻¹' s from Set.ext_iff.1 (coe_inj.2 this) a
#align topological_space.opens.comap_injective TopologicalSpace.Opens.comap_injective

/-- A homeomorphism induces an order-preserving equivalence on open sets, by taking comaps. -/
@[simps (config := { fullyApplied := false }) apply]
def Homeomorph.opensCongr (f : α ≃ₜ β) : Opens α ≃o Opens β
    where
  toFun := Opens.comap f.symm.toContinuousMap
  invFun := Opens.comap f.toContinuousMap
  left_inv := by
    intro U
    ext1
    exact f.to_equiv.preimage_symm_preimage _
  right_inv := by
    intro U
    ext1
    exact f.to_equiv.symm_preimage_preimage _
  map_rel_iff' U V := by
    simp only [← SetLike.coe_subset_coe] <;> exact f.symm.surjective.preimage_subset_preimage_iff
#align homeomorph.opens_congr Homeomorph.opensCongr

@[simp]
theorem Homeomorph.opensCongr_symm (f : α ≃ₜ β) : f.opensCongr.symm = f.symm.opensCongr :=
  rfl
#align homeomorph.opens_congr_symm Homeomorph.opensCongr_symm

instance [Finite α] : Finite (Opens α) :=
  Finite.of_injective _ SetLike.coe_injective

end Opens

/-- The open neighborhoods of a point. See also `opens` or `nhds`. -/
structure OpenNhdsOf (x : α) extends Opens α where
  mem' : x ∈ carrier
#align topological_space.open_nhds_of TopologicalSpace.OpenNhdsOf

namespace OpenNhdsOf

variable {x : α}

theorem toOpens_injective : Injective (toOpens : OpenNhdsOf x → Opens α)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
#align topological_space.open_nhds_of.to_opens_injective TopologicalSpace.OpenNhdsOf.toOpens_injective

instance : SetLike (OpenNhdsOf x) α where
  coe U := U.1
  coe_injective' := SetLike.coe_injective.comp toOpens_injective

instance canLiftSet : CanLift (Set α) (OpenNhdsOf x) coe fun s => IsOpen s ∧ x ∈ s :=
  ⟨fun s hs => ⟨⟨⟨s, hs.1⟩, hs.2⟩, rfl⟩⟩
#align topological_space.open_nhds_of.can_lift_set TopologicalSpace.OpenNhdsOf.canLiftSet

protected theorem mem (U : OpenNhdsOf x) : x ∈ U :=
  U.mem'
#align topological_space.open_nhds_of.mem TopologicalSpace.OpenNhdsOf.mem

protected theorem isOpen (U : OpenNhdsOf x) : IsOpen (U : Set α) :=
  U.is_open'
#align topological_space.open_nhds_of.is_open TopologicalSpace.OpenNhdsOf.isOpen

instance : OrderTop (OpenNhdsOf x)
    where
  top := ⟨⊤, Set.mem_univ _⟩
  le_top _ := subset_univ _

instance : Inhabited (OpenNhdsOf x) :=
  ⟨⊤⟩

instance : HasInf (OpenNhdsOf x) :=
  ⟨fun U V => ⟨U.1 ⊓ V.1, U.2, V.2⟩⟩

instance : HasSup (OpenNhdsOf x) :=
  ⟨fun U V => ⟨U.1 ⊔ V.1, Or.inl U.2⟩⟩

instance : DistribLattice (OpenNhdsOf x) :=
  toOpens_injective.DistribLattice _ (fun _ _ => rfl) fun _ _ => rfl

theorem basis_nhds : (𝓝 x).HasBasis (fun U : OpenNhdsOf x => True) coe :=
  (nhds_basis_opens x).to_hasBasis (fun U hU => ⟨⟨⟨U, hU.2⟩, hU.1⟩, trivial, Subset.rfl⟩) fun U _ =>
    ⟨U, ⟨⟨U.Mem, U.IsOpen⟩, Subset.rfl⟩⟩
#align topological_space.open_nhds_of.basis_nhds TopologicalSpace.OpenNhdsOf.basis_nhds

/-- Preimage of an open neighborhood of `f x` under a continuous map `f` as a `lattice_hom`. -/
def comap (f : C(α, β)) (x : α) : LatticeHom (OpenNhdsOf (f x)) (OpenNhdsOf x)
    where
  toFun U := ⟨Opens.comap f U.1, U.Mem⟩
  map_sup' U V := rfl
  map_inf' U V := rfl
#align topological_space.open_nhds_of.comap TopologicalSpace.OpenNhdsOf.comap

end OpenNhdsOf

end TopologicalSpace

namespace Tactic

namespace AutoCases

/-- Find an `auto_cases_tac` which matches `topological_space.opens`. -/
unsafe def opens_find_tac : expr → Option auto_cases_tac
  | q(TopologicalSpace.Opens _) => tac_cases
  | _ => none
#align tactic.auto_cases.opens_find_tac tactic.auto_cases.opens_find_tac

end AutoCases

/-- A version of `tactic.auto_cases` that works for `topological_space.opens`. -/
@[hint_tactic]
unsafe def auto_cases_opens : tactic String :=
  auto_cases tactic.auto_cases.opens_find_tac
#align tactic.auto_cases_opens tactic.auto_cases_opens

end Tactic

