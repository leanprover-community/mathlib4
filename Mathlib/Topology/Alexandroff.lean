/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang, Yury Kudryashov

! This file was ported from Lean 3 source module topology.alexandroff
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Fintype.Option
import Mathlib.Topology.Separation
import Mathlib.Topology.Sets.Opens

/-!
# The Alexandroff Compactification

We construct the Alexandroff compactification (the one-point compactification) of an arbitrary
topological space `X` and prove some properties inherited from `X`.

## Main definitions

* `Alexandroff`: the Alexandroff compactification, we use coercion for the canonical embedding
  `X → Alexandroff X`; when `X` is already compact, the compactification adds an isolated point
  to the space.
* `Alexandroff.infty`: the extra point

## Main results

* The topological structure of `Alexandroff X`
* The connectedness of `Alexandroff X` for a noncompact, preconnected `X`
* `Alexandroff X` is `T₀` for a T₀ space `X`
* `Alexandroff X` is `T₁` for a T₁ space `X`
* `Alexandroff X` is normal if `X` is a locally compact Hausdorff space

## Tags

one-point compactification, compactness
-/


open Set Filter Topology

/-!
### Definition and basic properties

In this section we define `Alexandroff X` to be the disjoint union of `X` and `∞`, implemented as
`Option X`. Then we restate some lemmas about `Option X` for `Alexandroff X`.
-/


variable {X : Type _}

/-- The Alexandroff extension of an arbitrary topological space `X` -/
def Alexandroff (X : Type _) :=
  Option X
#align alexandroff Alexandroff

/-- The repr uses the notation from the `Alexandroff` locale. -/
instance [Repr X] : Repr (Alexandroff X) :=
  ⟨fun o _ =>
    match o with
    | none => "∞"
    | some a => "↑" ++ repr a⟩

namespace Alexandroff

/-- The point at infinity -/
@[match_pattern] def infty : Alexandroff X := none
#align alexandroff.infty Alexandroff.infty

@[inherit_doc]
scoped notation "∞" => Alexandroff.infty

/-- Coercion from `X` to `Alexandroff X`. -/
@[coe, match_pattern] def some : X → Alexandroff X := Option.some

instance : CoeTC X (Alexandroff X) := ⟨some⟩

instance : Inhabited (Alexandroff X) := ⟨∞⟩

instance [Fintype X] : Fintype (Alexandroff X) :=
  inferInstanceAs (Fintype (Option X))

instance infinite [Infinite X] : Infinite (Alexandroff X) :=
  inferInstanceAs (Infinite (Option X))
#align alexandroff.infinite Alexandroff.infinite

theorem coe_injective : Function.Injective ((↑) : X → Alexandroff X) :=
  Option.some_injective X
#align alexandroff.coe_injective Alexandroff.coe_injective

@[norm_cast]
theorem coe_eq_coe {x y : X} : (x : Alexandroff X) = y ↔ x = y :=
  coe_injective.eq_iff
#align alexandroff.coe_eq_coe Alexandroff.coe_eq_coe

@[simp]
theorem coe_ne_infty (x : X) : (x : Alexandroff X) ≠ ∞ :=
  fun.
#align alexandroff.coe_ne_infty Alexandroff.coe_ne_infty

@[simp]
theorem infty_ne_coe (x : X) : ∞ ≠ (x : Alexandroff X) :=
  fun.
#align alexandroff.infty_ne_coe Alexandroff.infty_ne_coe

/-- Recursor for `Alexandroff` using the preferred forms `∞` and `↑x`. -/
@[elab_as_elim]
protected def rec {C : Alexandroff X → Sort _} (h₁ : C ∞) (h₂ : ∀ x : X, C x) :
    ∀ z : Alexandroff X, C z
  | ∞ => h₁
  | (x : X) => h₂ x
#align alexandroff.rec Alexandroff.rec

theorem isCompl_range_coe_infty : IsCompl (range ((↑) : X → Alexandroff X)) {∞} :=
  isCompl_range_some_none X
#align alexandroff.is_compl_range_coe_infty Alexandroff.isCompl_range_coe_infty

-- porting note: moved @[simp] to a new lemma
theorem range_coe_union_infty : range ((↑) : X → Alexandroff X) ∪ {∞} = univ :=
  range_some_union_none X
#align alexandroff.range_coe_union_infty Alexandroff.range_coe_union_infty

@[simp]
theorem insert_infty_range_coe : insert ∞ (range (@some X)) = univ :=
  insert_none_range_some _

@[simp]
theorem range_coe_inter_infty : range ((↑) : X → Alexandroff X) ∩ {∞} = ∅ :=
  range_some_inter_none X
#align alexandroff.range_coe_inter_infty Alexandroff.range_coe_inter_infty

@[simp]
theorem compl_range_coe : range ((↑) : X → Alexandroff X)ᶜ = {∞} :=
  compl_range_some X
#align alexandroff.compl_range_coe Alexandroff.compl_range_coe

theorem compl_infty : ({∞}ᶜ : Set (Alexandroff X)) = range ((↑) : X → Alexandroff X) :=
  (@isCompl_range_coe_infty X).symm.compl_eq
#align alexandroff.compl_infty Alexandroff.compl_infty

theorem compl_image_coe (s : Set X) : ((↑) '' s : Set (Alexandroff X))ᶜ = (↑) '' sᶜ ∪ {∞} := by
  rw [coe_injective.compl_image_eq, compl_range_coe]
#align alexandroff.compl_image_coe Alexandroff.compl_image_coe

theorem ne_infty_iff_exists {x : Alexandroff X} : x ≠ ∞ ↔ ∃ y : X, (y : Alexandroff X) = x := by
  induction x using Alexandroff.rec <;> simp
#align alexandroff.ne_infty_iff_exists Alexandroff.ne_infty_iff_exists

instance canLift : CanLift (Alexandroff X) X (↑) fun x => x ≠ ∞ :=
  WithTop.canLift
#align alexandroff.can_lift Alexandroff.canLift

theorem not_mem_range_coe_iff {x : Alexandroff X} : x ∉ range some ↔ x = ∞ := by
  rw [← mem_compl_iff, compl_range_coe, mem_singleton_iff]
#align alexandroff.not_mem_range_coe_iff Alexandroff.not_mem_range_coe_iff

theorem infty_not_mem_range_coe : ∞ ∉ range ((↑) : X → Alexandroff X) :=
  not_mem_range_coe_iff.2 rfl
#align alexandroff.infty_not_mem_range_coe Alexandroff.infty_not_mem_range_coe

theorem infty_not_mem_image_coe {s : Set X} : ∞ ∉ ((↑) : X → Alexandroff X) '' s :=
  not_mem_subset (image_subset_range _ _) infty_not_mem_range_coe
#align alexandroff.infty_not_mem_image_coe Alexandroff.infty_not_mem_image_coe

@[simp]
theorem coe_preimage_infty : ((↑) : X → Alexandroff X) ⁻¹' {∞} = ∅ := by
  ext
  simp
#align alexandroff.coe_preimage_infty Alexandroff.coe_preimage_infty

/-!
### Topological space structure on `Alexandroff X`

We define a topological space structure on `Alexandroff X` so that `s` is open if and only if

* `(↑) ⁻¹' s` is open in `X`;
* if `∞ ∈ s`, then `((↑) ⁻¹' s)ᶜ` is compact.

Then we reformulate this definition in a few different ways, and prove that
`(↑) : X → Alexandroff X` is an open embedding. If `X` is not a compact space, then we also prove
that `(↑)` has dense range, so it is a dense embedding.
-/


variable [TopologicalSpace X]

instance : TopologicalSpace (Alexandroff X) where
  IsOpen s := (∞ ∈ s → IsCompact ((((↑) : X → Alexandroff X) ⁻¹' s)ᶜ)) ∧
    IsOpen (((↑) : X → Alexandroff X) ⁻¹' s)
  isOpen_univ := by simp
  isOpen_inter s t := by
    rintro ⟨hms, hs⟩ ⟨hmt, ht⟩
    refine' ⟨_, hs.inter ht⟩
    rintro ⟨hms', hmt'⟩
    simpa [compl_inter] using (hms hms').union (hmt hmt')
  isOpen_sUnion S ho := by
    suffices IsOpen ((↑) ⁻¹' ⋃₀ S : Set X) by
      refine' ⟨_, this⟩
      rintro ⟨s, hsS : s ∈ S, hs : ∞ ∈ s⟩
      refine' isCompact_of_isClosed_subset ((ho s hsS).1 hs) this.isClosed_compl _
      exact compl_subset_compl.mpr (preimage_mono <| subset_sUnion_of_mem hsS)
    rw [preimage_sUnion]
    exact isOpen_biUnion fun s hs => (ho s hs).2

variable {s : Set (Alexandroff X)} {t : Set X}

theorem isOpen_def :
    IsOpen s ↔ (∞ ∈ s → IsCompact (((↑) ⁻¹' s : Set X)ᶜ)) ∧ IsOpen ((↑) ⁻¹' s : Set X) :=
  Iff.rfl
#align alexandroff.is_open_def Alexandroff.isOpen_def

theorem isOpen_iff_of_mem' (h : ∞ ∈ s) :
    IsOpen s ↔ IsCompact (((↑) ⁻¹' s : Set X)ᶜ) ∧ IsOpen ((↑) ⁻¹' s : Set X) := by
  simp [isOpen_def, h]
#align alexandroff.is_open_iff_of_mem' Alexandroff.isOpen_iff_of_mem'

theorem isOpen_iff_of_mem (h : ∞ ∈ s) :
    IsOpen s ↔ IsClosed (((↑) ⁻¹' s : Set X)ᶜ) ∧ IsCompact (((↑) ⁻¹' s : Set X)ᶜ) := by
  simp only [isOpen_iff_of_mem' h, isClosed_compl_iff, and_comm]
#align alexandroff.is_open_iff_of_mem Alexandroff.isOpen_iff_of_mem

theorem isOpen_iff_of_not_mem (h : ∞ ∉ s) : IsOpen s ↔ IsOpen ((↑) ⁻¹' s : Set X) := by
  simp [isOpen_def, h]
#align alexandroff.is_open_iff_of_not_mem Alexandroff.isOpen_iff_of_not_mem

theorem isClosed_iff_of_mem (h : ∞ ∈ s) : IsClosed s ↔ IsClosed ((↑) ⁻¹' s : Set X) := by
  have : ∞ ∉ sᶜ := fun H => H h
  rw [← isOpen_compl_iff, isOpen_iff_of_not_mem this, ← isOpen_compl_iff, preimage_compl]
#align alexandroff.is_closed_iff_of_mem Alexandroff.isClosed_iff_of_mem

theorem isClosed_iff_of_not_mem (h : ∞ ∉ s) :
    IsClosed s ↔ IsClosed ((↑) ⁻¹' s : Set X) ∧ IsCompact ((↑) ⁻¹' s : Set X) := by
  rw [← isOpen_compl_iff, isOpen_iff_of_mem (mem_compl h), ← preimage_compl, compl_compl]
#align alexandroff.is_closed_iff_of_not_mem Alexandroff.isClosed_iff_of_not_mem

@[simp]
theorem isOpen_image_coe {s : Set X} : IsOpen ((↑) '' s : Set (Alexandroff X)) ↔ IsOpen s := by
  rw [isOpen_iff_of_not_mem infty_not_mem_image_coe, preimage_image_eq _ coe_injective]
#align alexandroff.is_open_image_coe Alexandroff.isOpen_image_coe

theorem isOpen_compl_image_coe {s : Set X} :
    IsOpen (((↑) '' s : Set (Alexandroff X))ᶜ) ↔ IsClosed s ∧ IsCompact s := by
  rw [isOpen_iff_of_mem, ← preimage_compl, compl_compl, preimage_image_eq _ coe_injective]
  exact infty_not_mem_image_coe
#align alexandroff.is_open_compl_image_coe Alexandroff.isOpen_compl_image_coe

@[simp]
theorem isClosed_image_coe {s : Set X} :
    IsClosed ((↑) '' s : Set (Alexandroff X)) ↔ IsClosed s ∧ IsCompact s := by
  rw [← isOpen_compl_iff, isOpen_compl_image_coe]
#align alexandroff.is_closed_image_coe Alexandroff.isClosed_image_coe

/-- An open set in `Alexandroff X` constructed from a closed compact set in `X` -/
def opensOfCompl (s : Set X) (h₁ : IsClosed s) (h₂ : IsCompact s) :
    TopologicalSpace.Opens (Alexandroff X) :=
  ⟨((↑) '' s)ᶜ, isOpen_compl_image_coe.2 ⟨h₁, h₂⟩⟩
#align alexandroff.opens_of_compl Alexandroff.opensOfCompl

theorem infty_mem_opensOfCompl {s : Set X} (h₁ : IsClosed s) (h₂ : IsCompact s) :
    ∞ ∈ opensOfCompl s h₁ h₂ :=
  mem_compl infty_not_mem_image_coe
#align alexandroff.infty_mem_opens_of_compl Alexandroff.infty_mem_opensOfCompl

@[continuity]
theorem continuous_coe : Continuous ((↑) : X → Alexandroff X) :=
  continuous_def.mpr fun _s hs => hs.right
#align alexandroff.continuous_coe Alexandroff.continuous_coe

theorem isOpenMap_coe : IsOpenMap ((↑) : X → Alexandroff X) := fun _ => isOpen_image_coe.2
#align alexandroff.is_open_map_coe Alexandroff.isOpenMap_coe

theorem openEmbedding_coe : OpenEmbedding ((↑) : X → Alexandroff X) :=
  openEmbedding_of_continuous_injective_open continuous_coe coe_injective isOpenMap_coe
#align alexandroff.open_embedding_coe Alexandroff.openEmbedding_coe

theorem isOpen_range_coe : IsOpen (range ((↑) : X → Alexandroff X)) :=
  openEmbedding_coe.open_range
#align alexandroff.is_open_range_coe Alexandroff.isOpen_range_coe

theorem isClosed_infty : IsClosed ({∞} : Set (Alexandroff X)) := by
  rw [← compl_range_coe, isClosed_compl_iff]
  exact isOpen_range_coe
#align alexandroff.is_closed_infty Alexandroff.isClosed_infty

theorem nhds_coe_eq (x : X) : 𝓝 ↑x = map ((↑) : X → Alexandroff X) (𝓝 x) :=
  (openEmbedding_coe.map_nhds_eq x).symm
#align alexandroff.nhds_coe_eq Alexandroff.nhds_coe_eq

theorem nhdsWithin_coe_image (s : Set X) (x : X) :
    𝓝[(↑) '' s] (x : Alexandroff X) = map (↑) (𝓝[s] x) :=
  (openEmbedding_coe.toEmbedding.map_nhdsWithin_eq _ _).symm
#align alexandroff.nhds_within_coe_image Alexandroff.nhdsWithin_coe_image

theorem nhdsWithin_coe (s : Set (Alexandroff X)) (x : X) : 𝓝[s] ↑x = map (↑) (𝓝[(↑) ⁻¹' s] x) :=
  (openEmbedding_coe.map_nhdsWithin_preimage_eq _ _).symm
#align alexandroff.nhds_within_coe Alexandroff.nhdsWithin_coe

theorem comap_coe_nhds (x : X) : comap ((↑) : X → Alexandroff X) (𝓝 x) = 𝓝 x :=
  (openEmbedding_coe.toInducing.nhds_eq_comap x).symm
#align alexandroff.comap_coe_nhds Alexandroff.comap_coe_nhds

/-- If `x` is not an isolated point of `X`, then `x : Alexandroff X` is not an isolated point
of `Alexandroff X`. -/
instance nhdsWithin_compl_coe_neBot (x : X) [h : NeBot (𝓝[≠] x)] :
    NeBot (𝓝[≠] (x : Alexandroff X)) := by
  simpa [nhdsWithin_coe, preimage, coe_eq_coe] using h.map some
#align alexandroff.nhds_within_compl_coe_ne_bot Alexandroff.nhdsWithin_compl_coe_neBot

theorem nhdsWithin_compl_infty_eq : 𝓝[≠] (∞ : Alexandroff X) = map (↑) (coclosedCompact X) := by
  refine' (nhdsWithin_basis_open ∞ _).ext (hasBasis_coclosedCompact.map _) _ _
  · rintro s ⟨hs, hso⟩
    refine' ⟨_, (isOpen_iff_of_mem hs).mp hso, _⟩
    simp [Subset.rfl]
  · rintro s ⟨h₁, h₂⟩
    refine' ⟨_, ⟨mem_compl infty_not_mem_image_coe, isOpen_compl_image_coe.2 ⟨h₁, h₂⟩⟩, _⟩
    simp [compl_image_coe, ← diff_eq, subset_preimage_image]
#align alexandroff.nhds_within_compl_infty_eq Alexandroff.nhdsWithin_compl_infty_eq

/-- If `X` is a non-compact space, then `∞` is not an isolated point of `Alexandroff X`. -/
instance nhdsWithin_compl_infty_neBot [NoncompactSpace X] : NeBot (𝓝[≠] (∞ : Alexandroff X)) := by
  rw [nhdsWithin_compl_infty_eq]
  infer_instance
#align alexandroff.nhds_within_compl_infty_ne_bot Alexandroff.nhdsWithin_compl_infty_neBot

instance (priority := 900) nhdsWithin_compl_neBot [∀ x : X, NeBot (𝓝[≠] x)] [NoncompactSpace X]
    (x : Alexandroff X) : NeBot (𝓝[≠] x) :=
  Alexandroff.rec Alexandroff.nhdsWithin_compl_infty_neBot
    (fun y => Alexandroff.nhdsWithin_compl_coe_neBot y) x
#align alexandroff.nhds_within_compl_ne_bot Alexandroff.nhdsWithin_compl_neBot

theorem nhds_infty_eq : 𝓝 (∞ : Alexandroff X) = map (↑) (coclosedCompact X) ⊔ pure ∞ := by
  rw [← nhdsWithin_compl_infty_eq, nhdsWithin_compl_singleton_sup_pure]
#align alexandroff.nhds_infty_eq Alexandroff.nhds_infty_eq

theorem hasBasis_nhds_infty :
    (𝓝 (∞ : Alexandroff X)).HasBasis (fun s : Set X => IsClosed s ∧ IsCompact s) fun s =>
      (↑) '' sᶜ ∪ {∞} := by
  rw [nhds_infty_eq]
  exact (hasBasis_coclosedCompact.map _).sup_pure _
#align alexandroff.has_basis_nhds_infty Alexandroff.hasBasis_nhds_infty

@[simp]
theorem comap_coe_nhds_infty : comap ((↑) : X → Alexandroff X) (𝓝 ∞) = coclosedCompact X := by
  simp [nhds_infty_eq, comap_sup, comap_map coe_injective]
#align alexandroff.comap_coe_nhds_infty Alexandroff.comap_coe_nhds_infty

theorem le_nhds_infty {f : Filter (Alexandroff X)} :
    f ≤ 𝓝 ∞ ↔ ∀ s : Set X, IsClosed s → IsCompact s → (↑) '' sᶜ ∪ {∞} ∈ f := by
  simp only [hasBasis_nhds_infty.ge_iff, and_imp]
#align alexandroff.le_nhds_infty Alexandroff.le_nhds_infty

theorem ultrafilter_le_nhds_infty {f : Ultrafilter (Alexandroff X)} :
    (f : Filter (Alexandroff X)) ≤ 𝓝 ∞ ↔ ∀ s : Set X, IsClosed s → IsCompact s → (↑) '' s ∉ f := by
  simp only [le_nhds_infty, ← compl_image_coe, Ultrafilter.mem_coe,
    Ultrafilter.compl_mem_iff_not_mem]
#align alexandroff.ultrafilter_le_nhds_infty Alexandroff.ultrafilter_le_nhds_infty

theorem tendsto_nhds_infty' {α : Type _} {f : Alexandroff X → α} {l : Filter α} :
    Tendsto f (𝓝 ∞) l ↔ Tendsto f (pure ∞) l ∧ Tendsto (f ∘ (↑)) (coclosedCompact X) l := by
  simp [nhds_infty_eq, and_comm]
#align alexandroff.tendsto_nhds_infty' Alexandroff.tendsto_nhds_infty'

theorem tendsto_nhds_infty {α : Type _} {f : Alexandroff X → α} {l : Filter α} :
    Tendsto f (𝓝 ∞) l ↔
      ∀ s ∈ l, f ∞ ∈ s ∧ ∃ t : Set X, IsClosed t ∧ IsCompact t ∧ MapsTo (f ∘ (↑)) (tᶜ) s :=
  tendsto_nhds_infty'.trans <| by
    simp only [tendsto_pure_left, hasBasis_coclosedCompact.tendsto_left_iff, forall_and,
      and_assoc, exists_prop]
#align alexandroff.tendsto_nhds_infty Alexandroff.tendsto_nhds_infty

theorem continuousAt_infty' {Y : Type _} [TopologicalSpace Y] {f : Alexandroff X → Y} :
    ContinuousAt f ∞ ↔ Tendsto (f ∘ (↑)) (coclosedCompact X) (𝓝 (f ∞)) :=
  tendsto_nhds_infty'.trans <| and_iff_right (tendsto_pure_nhds _ _)
#align alexandroff.continuous_at_infty' Alexandroff.continuousAt_infty'

theorem continuousAt_infty {Y : Type _} [TopologicalSpace Y] {f : Alexandroff X → Y} :
    ContinuousAt f ∞ ↔
      ∀ s ∈ 𝓝 (f ∞), ∃ t : Set X, IsClosed t ∧ IsCompact t ∧ MapsTo (f ∘ (↑)) (tᶜ) s :=
  continuousAt_infty'.trans <| by simp only [hasBasis_coclosedCompact.tendsto_left_iff, and_assoc]
#align alexandroff.continuous_at_infty Alexandroff.continuousAt_infty

theorem continuousAt_coe {Y : Type _} [TopologicalSpace Y] {f : Alexandroff X → Y} {x : X} :
    ContinuousAt f x ↔ ContinuousAt (f ∘ (↑)) x := by
  rw [ContinuousAt, nhds_coe_eq, tendsto_map'_iff, ContinuousAt]; rfl
#align alexandroff.continuous_at_coe Alexandroff.continuousAt_coe

/-- If `X` is not a compact space, then the natural embedding `X → Alexandroff X` has dense range.
-/
theorem denseRange_coe [NoncompactSpace X] : DenseRange ((↑) : X → Alexandroff X) := by
  rw [DenseRange, ← compl_infty]
  exact dense_compl_singleton _
#align alexandroff.dense_range_coe Alexandroff.denseRange_coe

theorem denseEmbedding_coe [NoncompactSpace X] : DenseEmbedding ((↑) : X → Alexandroff X) :=
  { openEmbedding_coe with dense := denseRange_coe }
#align alexandroff.dense_embedding_coe Alexandroff.denseEmbedding_coe

@[simp]
theorem specializes_coe {x y : X} : (x : Alexandroff X) ⤳ y ↔ x ⤳ y :=
  openEmbedding_coe.toInducing.specializes_iff
#align alexandroff.specializes_coe Alexandroff.specializes_coe

@[simp]
theorem inseparable_coe {x y : X} : Inseparable (x : Alexandroff X) y ↔ Inseparable x y :=
  openEmbedding_coe.toInducing.inseparable_iff
#align alexandroff.inseparable_coe Alexandroff.inseparable_coe

theorem not_specializes_infty_coe {x : X} : ¬Specializes ∞ (x : Alexandroff X) :=
  isClosed_infty.not_specializes rfl (coe_ne_infty x)
#align alexandroff.not_specializes_infty_coe Alexandroff.not_specializes_infty_coe

theorem not_inseparable_infty_coe {x : X} : ¬Inseparable ∞ (x : Alexandroff X) := fun h =>
  not_specializes_infty_coe h.specializes
#align alexandroff.not_inseparable_infty_coe Alexandroff.not_inseparable_infty_coe

theorem not_inseparable_coe_infty {x : X} : ¬Inseparable (x : Alexandroff X) ∞ := fun h =>
  not_specializes_infty_coe h.specializes'
#align alexandroff.not_inseparable_coe_infty Alexandroff.not_inseparable_coe_infty

theorem inseparable_iff {x y : Alexandroff X} :
    Inseparable x y ↔ x = ∞ ∧ y = ∞ ∨ ∃ x' : X, x = x' ∧ ∃ y' : X, y = y' ∧ Inseparable x' y' := by
  induction x using Alexandroff.rec <;> induction y using Alexandroff.rec <;>
    simp [not_inseparable_infty_coe, not_inseparable_coe_infty, coe_eq_coe, Inseparable.refl]
#align alexandroff.inseparable_iff Alexandroff.inseparable_iff

/-!
### Compactness and separation properties

In this section we prove that `Alexandroff X` is a compact space; it is a T₀ (resp., T₁) space if
the original space satisfies the same separation axiom. If the original space is a locally compact
Hausdorff space, then `Alexandroff X` is a normal (hence, T₃ and Hausdorff) space.

Finally, if the original space `X` is *not* compact and is a preconnected space, then
`Alexandroff X` is a connected space.
-/


/-- For any topological space `X`, its one point compactification is a compact space. -/
instance : CompactSpace (Alexandroff X) where
  isCompact_univ := by
    have : Tendsto ((↑) : X → Alexandroff X) (cocompact X) (𝓝 ∞) := by
      rw [nhds_infty_eq]
      exact (tendsto_map.mono_left cocompact_le_coclosedCompact).mono_right le_sup_left
    rw [← insert_none_range_some X]
    exact this.isCompact_insert_range_of_cocompact continuous_coe

/-- The one point compactification of a `T0Space` space is a `T0Space`. -/
instance [T0Space X] : T0Space (Alexandroff X) := by
  refine' ⟨fun x y hxy => _⟩
  rcases inseparable_iff.1 hxy with (⟨rfl, rfl⟩ | ⟨x, rfl, y, rfl, h⟩)
  exacts [rfl, congr_arg some h.eq]

/-- The one point compactification of a `T1Space` space is a `T1Space`. -/
instance [T1Space X] : T1Space (Alexandroff X) where
  t1 z := by
    induction z using Alexandroff.rec
    · exact isClosed_infty
    · rw [← image_singleton, isClosed_image_coe]
      exact ⟨isClosed_singleton, isCompact_singleton⟩

/-- The one point compactification of a locally compact Hausdorff space is a normal (hence,
Hausdorff and regular) topological space. -/
instance [LocallyCompactSpace X] [T2Space X] : NormalSpace (Alexandroff X) := by
  have key : ∀ z : X, Disjoint (𝓝 (some z)) (𝓝 ∞) := fun z => by
    rw [nhds_infty_eq, disjoint_sup_right, nhds_coe_eq, coclosedCompact_eq_cocompact,
      disjoint_map coe_injective, ← principal_singleton, disjoint_principal_right, compl_infty]
    exact ⟨disjoint_nhds_cocompact z, range_mem_map⟩
  suffices : T2Space (Alexandroff X); exact normalOfCompactT2
  refine t2Space_iff_disjoint_nhds.2 fun x y hxy => ?_
  induction x using Alexandroff.rec <;> induction y using Alexandroff.rec
  · exact (hxy rfl).elim
  · exact (key _).symm
  · exact key _
  · rwa [nhds_coe_eq, nhds_coe_eq, disjoint_map coe_injective, disjoint_nhds_nhds,
      ← coe_injective.ne_iff]

/-- If `X` is not a compact space, then `Alexandroff X` is a connected space. -/
instance [PreconnectedSpace X] [NoncompactSpace X] : ConnectedSpace (Alexandroff X) where
  toPreconnectedSpace := denseEmbedding_coe.toDenseInducing.preconnectedSpace
  toNonempty := inferInstance

/-- If `X` is an infinite type with discrete topology (e.g., `ℕ`), then the identity map from
`CofiniteTopology (Alexandroff X)` to `Alexandroff X` is not continuous. -/
theorem not_continuous_cofiniteTopology_of_symm [Infinite X] [DiscreteTopology X] :
    ¬Continuous (@CofiniteTopology.of (Alexandroff X)).symm := by
  inhabit X
  simp only [continuous_iff_continuousAt, ContinuousAt, not_forall]
  use CofiniteTopology.of ↑(default : X)
  simpa [nhds_coe_eq, nhds_discrete, CofiniteTopology.nhds_eq] using
    (finite_singleton ((default : X) : Alexandroff X)).infinite_compl
#align alexandroff.not_continuous_cofinite_topology_of_symm Alexandroff.not_continuous_cofiniteTopology_of_symm

end Alexandroff

/-- A concrete counterexample shows that  `Continuous.homeoOfEquivCompactToT2`
cannot be generalized from `T2Space` to `T1Space`.

Let `α = Alexandroff ℕ` be the one-point compactification of `ℕ`, and let `β` be the same space
`Alexandroff ℕ` with the cofinite topology.  Then `α` is compact, `β` is T1, and the identity map
`id : α → β` is a continuous equivalence that is not a homeomorphism.
-/
theorem Continuous.homeoOfEquivCompactToT2.t1_counterexample :
    ∃ (α β : Type) (_ : TopologicalSpace α) (_ : TopologicalSpace β),
      CompactSpace α ∧ T1Space β ∧ ∃ f : α ≃ β, Continuous f ∧ ¬Continuous f.symm :=
  ⟨Alexandroff ℕ, CofiniteTopology (Alexandroff ℕ), inferInstance, inferInstance, inferInstance,
    inferInstance, CofiniteTopology.of, CofiniteTopology.continuous_of,
    Alexandroff.not_continuous_cofiniteTopology_of_symm⟩
#align continuous.homeo_of_equiv_compact_to_t2.t1_counterexample Continuous.homeoOfEquivCompactToT2.t1_counterexample
