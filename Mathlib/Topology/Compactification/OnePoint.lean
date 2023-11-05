/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang, Yury Kudryashov
-/
import Mathlib.Data.Fintype.Option
import Mathlib.Topology.Separation
import Mathlib.Topology.Sets.Opens

#align_import topology.alexandroff from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# The OnePoint Compactification

We construct the OnePoint compactification (the one-point compactification) of an arbitrary
topological space `X` and prove some properties inherited from `X`.

## Main definitions

* `OnePoint`: the OnePoint compactification, we use coercion for the canonical embedding
  `X → OnePoint X`; when `X` is already compact, the compactification adds an isolated point
  to the space.
* `OnePoint.infty`: the extra point

## Main results

* The topological structure of `OnePoint X`
* The connectedness of `OnePoint X` for a noncompact, preconnected `X`
* `OnePoint X` is `T₀` for a T₀ space `X`
* `OnePoint X` is `T₁` for a T₁ space `X`
* `OnePoint X` is normal if `X` is a locally compact Hausdorff space

## Tags

one-point compactification, compactness
-/


open Set Filter Topology

/-!
### Definition and basic properties

In this section we define `OnePoint X` to be the disjoint union of `X` and `∞`, implemented as
`Option X`. Then we restate some lemmas about `Option X` for `OnePoint X`.
-/


variable {X : Type*}

/-- The OnePoint extension of an arbitrary topological space `X` -/
def OnePoint (X : Type*) :=
  Option X

/-- The repr uses the notation from the `OnePoint` locale. -/
instance [Repr X] : Repr (OnePoint X) :=
  ⟨fun o _ =>
    match o with
    | none => "∞"
    | some a => "↑" ++ repr a⟩

namespace OnePoint

/-- The point at infinity -/
@[match_pattern] def infty : OnePoint X := none

@[inherit_doc]
scoped notation "∞" => OnePoint.infty

/-- Coercion from `X` to `OnePoint X`. -/
@[coe, match_pattern] def some : X → OnePoint X := Option.some

instance : CoeTC X (OnePoint X) := ⟨some⟩

instance : Inhabited (OnePoint X) := ⟨∞⟩

instance [Fintype X] : Fintype (OnePoint X) :=
  inferInstanceAs (Fintype (Option X))

instance infinite [Infinite X] : Infinite (OnePoint X) :=
  inferInstanceAs (Infinite (Option X))

theorem coe_injective : Function.Injective ((↑) : X → OnePoint X) :=
  Option.some_injective X

@[norm_cast]
theorem coe_eq_coe {x y : X} : (x : OnePoint X) = y ↔ x = y :=
  coe_injective.eq_iff

@[simp]
theorem coe_ne_infty (x : X) : (x : OnePoint X) ≠ ∞ :=
  fun.

@[simp]
theorem infty_ne_coe (x : X) : ∞ ≠ (x : OnePoint X) :=
  fun.

/-- Recursor for `OnePoint` using the preferred forms `∞` and `↑x`. -/
@[elab_as_elim]
protected def rec {C : OnePoint X → Sort*} (h₁ : C ∞) (h₂ : ∀ x : X, C x) :
    ∀ z : OnePoint X, C z
  | ∞ => h₁
  | (x : X) => h₂ x

theorem isCompl_range_coe_infty : IsCompl (range ((↑) : X → OnePoint X)) {∞} :=
  isCompl_range_some_none X

-- porting note: moved @[simp] to a new lemma
theorem range_coe_union_infty : range ((↑) : X → OnePoint X) ∪ {∞} = univ :=
  range_some_union_none X

@[simp]
theorem insert_infty_range_coe : insert ∞ (range (@some X)) = univ :=
  insert_none_range_some _

@[simp]
theorem range_coe_inter_infty : range ((↑) : X → OnePoint X) ∩ {∞} = ∅ :=
  range_some_inter_none X

@[simp]
theorem compl_range_coe : (range ((↑) : X → OnePoint X))ᶜ = {∞} :=
  compl_range_some X

theorem compl_infty : ({∞}ᶜ : Set (OnePoint X)) = range ((↑) : X → OnePoint X) :=
  (@isCompl_range_coe_infty X).symm.compl_eq

theorem compl_image_coe (s : Set X) : ((↑) '' s : Set (OnePoint X))ᶜ = (↑) '' sᶜ ∪ {∞} := by
  rw [coe_injective.compl_image_eq, compl_range_coe]

theorem ne_infty_iff_exists {x : OnePoint X} : x ≠ ∞ ↔ ∃ y : X, (y : OnePoint X) = x := by
  induction x using OnePoint.rec <;> simp

instance canLift : CanLift (OnePoint X) X (↑) fun x => x ≠ ∞ :=
  WithTop.canLift

theorem not_mem_range_coe_iff {x : OnePoint X} : x ∉ range some ↔ x = ∞ := by
  rw [← mem_compl_iff, compl_range_coe, mem_singleton_iff]

theorem infty_not_mem_range_coe : ∞ ∉ range ((↑) : X → OnePoint X) :=
  not_mem_range_coe_iff.2 rfl

theorem infty_not_mem_image_coe {s : Set X} : ∞ ∉ ((↑) : X → OnePoint X) '' s :=
  not_mem_subset (image_subset_range _ _) infty_not_mem_range_coe

@[simp]
theorem coe_preimage_infty : ((↑) : X → OnePoint X) ⁻¹' {∞} = ∅ := by
  ext
  simp

/-!
### Topological space structure on `OnePoint X`

We define a topological space structure on `OnePoint X` so that `s` is open if and only if

* `(↑) ⁻¹' s` is open in `X`;
* if `∞ ∈ s`, then `((↑) ⁻¹' s)ᶜ` is compact.

Then we reformulate this definition in a few different ways, and prove that
`(↑) : X → OnePoint X` is an open embedding. If `X` is not a compact space, then we also prove
that `(↑)` has dense range, so it is a dense embedding.
-/


variable [TopologicalSpace X]

instance : TopologicalSpace (OnePoint X) where
  IsOpen s := (∞ ∈ s → IsCompact (((↑) : X → OnePoint X) ⁻¹' s)ᶜ) ∧
    IsOpen (((↑) : X → OnePoint X) ⁻¹' s)
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
      refine' IsCompact.of_isClosed_subset ((ho s hsS).1 hs) this.isClosed_compl _
      exact compl_subset_compl.mpr (preimage_mono <| subset_sUnion_of_mem hsS)
    rw [preimage_sUnion]
    exact isOpen_biUnion fun s hs => (ho s hs).2

variable {s : Set (OnePoint X)} {t : Set X}

theorem isOpen_def :
    IsOpen s ↔ (∞ ∈ s → IsCompact ((↑) ⁻¹' s : Set X)ᶜ) ∧ IsOpen ((↑) ⁻¹' s : Set X) :=
  Iff.rfl

theorem isOpen_iff_of_mem' (h : ∞ ∈ s) :
    IsOpen s ↔ IsCompact ((↑) ⁻¹' s : Set X)ᶜ ∧ IsOpen ((↑) ⁻¹' s : Set X) := by
  simp [isOpen_def, h]

theorem isOpen_iff_of_mem (h : ∞ ∈ s) :
    IsOpen s ↔ IsClosed ((↑) ⁻¹' s : Set X)ᶜ ∧ IsCompact ((↑) ⁻¹' s : Set X)ᶜ := by
  simp only [isOpen_iff_of_mem' h, isClosed_compl_iff, and_comm]

theorem isOpen_iff_of_not_mem (h : ∞ ∉ s) : IsOpen s ↔ IsOpen ((↑) ⁻¹' s : Set X) := by
  simp [isOpen_def, h]

theorem isClosed_iff_of_mem (h : ∞ ∈ s) : IsClosed s ↔ IsClosed ((↑) ⁻¹' s : Set X) := by
  have : ∞ ∉ sᶜ := fun H => H h
  rw [← isOpen_compl_iff, isOpen_iff_of_not_mem this, ← isOpen_compl_iff, preimage_compl]

theorem isClosed_iff_of_not_mem (h : ∞ ∉ s) :
    IsClosed s ↔ IsClosed ((↑) ⁻¹' s : Set X) ∧ IsCompact ((↑) ⁻¹' s : Set X) := by
  rw [← isOpen_compl_iff, isOpen_iff_of_mem (mem_compl h), ← preimage_compl, compl_compl]

@[simp]
theorem isOpen_image_coe {s : Set X} : IsOpen ((↑) '' s : Set (OnePoint X)) ↔ IsOpen s := by
  rw [isOpen_iff_of_not_mem infty_not_mem_image_coe, preimage_image_eq _ coe_injective]

theorem isOpen_compl_image_coe {s : Set X} :
    IsOpen ((↑) '' s : Set (OnePoint X))ᶜ ↔ IsClosed s ∧ IsCompact s := by
  rw [isOpen_iff_of_mem, ← preimage_compl, compl_compl, preimage_image_eq _ coe_injective]
  exact infty_not_mem_image_coe

@[simp]
theorem isClosed_image_coe {s : Set X} :
    IsClosed ((↑) '' s : Set (OnePoint X)) ↔ IsClosed s ∧ IsCompact s := by
  rw [← isOpen_compl_iff, isOpen_compl_image_coe]

/-- An open set in `OnePoint X` constructed from a closed compact set in `X` -/
def opensOfCompl (s : Set X) (h₁ : IsClosed s) (h₂ : IsCompact s) :
    TopologicalSpace.Opens (OnePoint X) :=
  ⟨((↑) '' s)ᶜ, isOpen_compl_image_coe.2 ⟨h₁, h₂⟩⟩

theorem infty_mem_opensOfCompl {s : Set X} (h₁ : IsClosed s) (h₂ : IsCompact s) :
    ∞ ∈ opensOfCompl s h₁ h₂ :=
  mem_compl infty_not_mem_image_coe

@[continuity]
theorem continuous_coe : Continuous ((↑) : X → OnePoint X) :=
  continuous_def.mpr fun _s hs => hs.right

theorem isOpenMap_coe : IsOpenMap ((↑) : X → OnePoint X) := fun _ => isOpen_image_coe.2

theorem openEmbedding_coe : OpenEmbedding ((↑) : X → OnePoint X) :=
  openEmbedding_of_continuous_injective_open continuous_coe coe_injective isOpenMap_coe

theorem isOpen_range_coe : IsOpen (range ((↑) : X → OnePoint X)) :=
  openEmbedding_coe.open_range

theorem isClosed_infty : IsClosed ({∞} : Set (OnePoint X)) := by
  rw [← compl_range_coe, isClosed_compl_iff]
  exact isOpen_range_coe

theorem nhds_coe_eq (x : X) : 𝓝 ↑x = map ((↑) : X → OnePoint X) (𝓝 x) :=
  (openEmbedding_coe.map_nhds_eq x).symm

theorem nhdsWithin_coe_image (s : Set X) (x : X) :
    𝓝[(↑) '' s] (x : OnePoint X) = map (↑) (𝓝[s] x) :=
  (openEmbedding_coe.toEmbedding.map_nhdsWithin_eq _ _).symm

theorem nhdsWithin_coe (s : Set (OnePoint X)) (x : X) : 𝓝[s] ↑x = map (↑) (𝓝[(↑) ⁻¹' s] x) :=
  (openEmbedding_coe.map_nhdsWithin_preimage_eq _ _).symm

theorem comap_coe_nhds (x : X) : comap ((↑) : X → OnePoint X) (𝓝 x) = 𝓝 x :=
  (openEmbedding_coe.toInducing.nhds_eq_comap x).symm

/-- If `x` is not an isolated point of `X`, then `x : OnePoint X` is not an isolated point
of `OnePoint X`. -/
instance nhdsWithin_compl_coe_neBot (x : X) [h : NeBot (𝓝[≠] x)] :
    NeBot (𝓝[≠] (x : OnePoint X)) := by
  simpa [nhdsWithin_coe, preimage, coe_eq_coe] using h.map some

theorem nhdsWithin_compl_infty_eq : 𝓝[≠] (∞ : OnePoint X) = map (↑) (coclosedCompact X) := by
  refine' (nhdsWithin_basis_open ∞ _).ext (hasBasis_coclosedCompact.map _) _ _
  · rintro s ⟨hs, hso⟩
    refine' ⟨_, (isOpen_iff_of_mem hs).mp hso, _⟩
    simp [Subset.rfl]
  · rintro s ⟨h₁, h₂⟩
    refine' ⟨_, ⟨mem_compl infty_not_mem_image_coe, isOpen_compl_image_coe.2 ⟨h₁, h₂⟩⟩, _⟩
    simp [compl_image_coe, ← diff_eq, subset_preimage_image]

/-- If `X` is a non-compact space, then `∞` is not an isolated point of `OnePoint X`. -/
instance nhdsWithin_compl_infty_neBot [NoncompactSpace X] : NeBot (𝓝[≠] (∞ : OnePoint X)) := by
  rw [nhdsWithin_compl_infty_eq]
  infer_instance

instance (priority := 900) nhdsWithin_compl_neBot [∀ x : X, NeBot (𝓝[≠] x)] [NoncompactSpace X]
    (x : OnePoint X) : NeBot (𝓝[≠] x) :=
  OnePoint.rec OnePoint.nhdsWithin_compl_infty_neBot
    (fun y => OnePoint.nhdsWithin_compl_coe_neBot y) x

theorem nhds_infty_eq : 𝓝 (∞ : OnePoint X) = map (↑) (coclosedCompact X) ⊔ pure ∞ := by
  rw [← nhdsWithin_compl_infty_eq, nhdsWithin_compl_singleton_sup_pure]

theorem hasBasis_nhds_infty :
    (𝓝 (∞ : OnePoint X)).HasBasis (fun s : Set X => IsClosed s ∧ IsCompact s) fun s =>
      (↑) '' sᶜ ∪ {∞} := by
  rw [nhds_infty_eq]
  exact (hasBasis_coclosedCompact.map _).sup_pure _

@[simp]
theorem comap_coe_nhds_infty : comap ((↑) : X → OnePoint X) (𝓝 ∞) = coclosedCompact X := by
  simp [nhds_infty_eq, comap_sup, comap_map coe_injective]

theorem le_nhds_infty {f : Filter (OnePoint X)} :
    f ≤ 𝓝 ∞ ↔ ∀ s : Set X, IsClosed s → IsCompact s → (↑) '' sᶜ ∪ {∞} ∈ f := by
  simp only [hasBasis_nhds_infty.ge_iff, and_imp]

theorem ultrafilter_le_nhds_infty {f : Ultrafilter (OnePoint X)} :
    (f : Filter (OnePoint X)) ≤ 𝓝 ∞ ↔ ∀ s : Set X, IsClosed s → IsCompact s → (↑) '' s ∉ f := by
  simp only [le_nhds_infty, ← compl_image_coe, Ultrafilter.mem_coe,
    Ultrafilter.compl_mem_iff_not_mem]

theorem tendsto_nhds_infty' {α : Type*} {f : OnePoint X → α} {l : Filter α} :
    Tendsto f (𝓝 ∞) l ↔ Tendsto f (pure ∞) l ∧ Tendsto (f ∘ (↑)) (coclosedCompact X) l := by
  simp [nhds_infty_eq, and_comm]

theorem tendsto_nhds_infty {α : Type*} {f : OnePoint X → α} {l : Filter α} :
    Tendsto f (𝓝 ∞) l ↔
      ∀ s ∈ l, f ∞ ∈ s ∧ ∃ t : Set X, IsClosed t ∧ IsCompact t ∧ MapsTo (f ∘ (↑)) tᶜ s :=
  tendsto_nhds_infty'.trans <| by
    simp only [tendsto_pure_left, hasBasis_coclosedCompact.tendsto_left_iff, forall_and,
      and_assoc, exists_prop]

theorem continuousAt_infty' {Y : Type*} [TopologicalSpace Y] {f : OnePoint X → Y} :
    ContinuousAt f ∞ ↔ Tendsto (f ∘ (↑)) (coclosedCompact X) (𝓝 (f ∞)) :=
  tendsto_nhds_infty'.trans <| and_iff_right (tendsto_pure_nhds _ _)

theorem continuousAt_infty {Y : Type*} [TopologicalSpace Y] {f : OnePoint X → Y} :
    ContinuousAt f ∞ ↔
      ∀ s ∈ 𝓝 (f ∞), ∃ t : Set X, IsClosed t ∧ IsCompact t ∧ MapsTo (f ∘ (↑)) tᶜ s :=
  continuousAt_infty'.trans <| by simp only [hasBasis_coclosedCompact.tendsto_left_iff, and_assoc]

theorem continuousAt_coe {Y : Type*} [TopologicalSpace Y] {f : OnePoint X → Y} {x : X} :
    ContinuousAt f x ↔ ContinuousAt (f ∘ (↑)) x := by
  rw [ContinuousAt, nhds_coe_eq, tendsto_map'_iff, ContinuousAt]; rfl

/-- If `X` is not a compact space, then the natural embedding `X → OnePoint X` has dense range.
-/
theorem denseRange_coe [NoncompactSpace X] : DenseRange ((↑) : X → OnePoint X) := by
  rw [DenseRange, ← compl_infty]
  exact dense_compl_singleton _

theorem denseEmbedding_coe [NoncompactSpace X] : DenseEmbedding ((↑) : X → OnePoint X) :=
  { openEmbedding_coe with dense := denseRange_coe }

@[simp]
theorem specializes_coe {x y : X} : (x : OnePoint X) ⤳ y ↔ x ⤳ y :=
  openEmbedding_coe.toInducing.specializes_iff

@[simp]
theorem inseparable_coe {x y : X} : Inseparable (x : OnePoint X) y ↔ Inseparable x y :=
  openEmbedding_coe.toInducing.inseparable_iff

theorem not_specializes_infty_coe {x : X} : ¬Specializes ∞ (x : OnePoint X) :=
  isClosed_infty.not_specializes rfl (coe_ne_infty x)

theorem not_inseparable_infty_coe {x : X} : ¬Inseparable ∞ (x : OnePoint X) := fun h =>
  not_specializes_infty_coe h.specializes

theorem not_inseparable_coe_infty {x : X} : ¬Inseparable (x : OnePoint X) ∞ := fun h =>
  not_specializes_infty_coe h.specializes'

theorem inseparable_iff {x y : OnePoint X} :
    Inseparable x y ↔ x = ∞ ∧ y = ∞ ∨ ∃ x' : X, x = x' ∧ ∃ y' : X, y = y' ∧ Inseparable x' y' := by
  induction x using OnePoint.rec <;> induction y using OnePoint.rec <;>
    simp [not_inseparable_infty_coe, not_inseparable_coe_infty, coe_eq_coe, Inseparable.refl]

/-!
### Compactness and separation properties

In this section we prove that `OnePoint X` is a compact space; it is a T₀ (resp., T₁) space if
the original space satisfies the same separation axiom. If the original space is a locally compact
Hausdorff space, then `OnePoint X` is a normal (hence, T₃ and Hausdorff) space.

Finally, if the original space `X` is *not* compact and is a preconnected space, then
`OnePoint X` is a connected space.
-/


/-- For any topological space `X`, its one point compactification is a compact space. -/
instance : CompactSpace (OnePoint X) where
  isCompact_univ := by
    have : Tendsto ((↑) : X → OnePoint X) (cocompact X) (𝓝 ∞) := by
      rw [nhds_infty_eq]
      exact (tendsto_map.mono_left cocompact_le_coclosedCompact).mono_right le_sup_left
    rw [← insert_none_range_some X]
    exact this.isCompact_insert_range_of_cocompact continuous_coe

/-- The one point compactification of a `T0Space` space is a `T0Space`. -/
instance [T0Space X] : T0Space (OnePoint X) := by
  refine' ⟨fun x y hxy => _⟩
  rcases inseparable_iff.1 hxy with (⟨rfl, rfl⟩ | ⟨x, rfl, y, rfl, h⟩)
  exacts [rfl, congr_arg some h.eq]

/-- The one point compactification of a `T1Space` space is a `T1Space`. -/
instance [T1Space X] : T1Space (OnePoint X) where
  t1 z := by
    induction z using OnePoint.rec
    · exact isClosed_infty
    · rw [← image_singleton, isClosed_image_coe]
      exact ⟨isClosed_singleton, isCompact_singleton⟩

/-- The one point compactification of a weakly locally compact Hausdorff space is a T₄
(hence, Hausdorff and regular) topological space. -/
instance [WeaklyLocallyCompactSpace X] [T2Space X] : T4Space (OnePoint X) := by
  have key : ∀ z : X, Disjoint (𝓝 (some z)) (𝓝 ∞) := fun z => by
    rw [nhds_infty_eq, disjoint_sup_right, nhds_coe_eq, coclosedCompact_eq_cocompact,
      disjoint_map coe_injective, ← principal_singleton, disjoint_principal_right, compl_infty]
    exact ⟨disjoint_nhds_cocompact z, range_mem_map⟩
  suffices : T2Space (OnePoint X); infer_instance
  refine t2Space_iff_disjoint_nhds.2 fun x y hxy => ?_
  induction x using OnePoint.rec <;> induction y using OnePoint.rec
  · exact (hxy rfl).elim
  · exact (key _).symm
  · exact key _
  · rwa [nhds_coe_eq, nhds_coe_eq, disjoint_map coe_injective, disjoint_nhds_nhds,
      ← coe_injective.ne_iff]

/-- If `X` is not a compact space, then `OnePoint X` is a connected space. -/
instance [PreconnectedSpace X] [NoncompactSpace X] : ConnectedSpace (OnePoint X) where
  toPreconnectedSpace := denseEmbedding_coe.toDenseInducing.preconnectedSpace
  toNonempty := inferInstance

/-- If `X` is an infinite type with discrete topology (e.g., `ℕ`), then the identity map from
`CofiniteTopology (OnePoint X)` to `OnePoint X` is not continuous. -/
theorem not_continuous_cofiniteTopology_of_symm [Infinite X] [DiscreteTopology X] :
    ¬Continuous (@CofiniteTopology.of (OnePoint X)).symm := by
  inhabit X
  simp only [continuous_iff_continuousAt, ContinuousAt, not_forall]
  use CofiniteTopology.of ↑(default : X)
  simpa [nhds_coe_eq, nhds_discrete, CofiniteTopology.nhds_eq] using
    (finite_singleton ((default : X) : OnePoint X)).infinite_compl

end OnePoint

/-- A concrete counterexample shows that `Continuous.homeoOfEquivCompactToT2`
cannot be generalized from `T2Space` to `T1Space`.

Let `α = OnePoint ℕ` be the one-point compactification of `ℕ`, and let `β` be the same space
`OnePoint ℕ` with the cofinite topology.  Then `α` is compact, `β` is T1, and the identity map
`id : α → β` is a continuous equivalence that is not a homeomorphism.
-/
theorem Continuous.homeoOfEquivCompactToT2.t1_counterexample :
    ∃ (α β : Type) (_ : TopologicalSpace α) (_ : TopologicalSpace β),
      CompactSpace α ∧ T1Space β ∧ ∃ f : α ≃ β, Continuous f ∧ ¬Continuous f.symm :=
  ⟨OnePoint ℕ, CofiniteTopology (OnePoint ℕ), inferInstance, inferInstance, inferInstance,
    inferInstance, CofiniteTopology.of, CofiniteTopology.continuous_of,
    OnePoint.not_continuous_cofiniteTopology_of_symm⟩
