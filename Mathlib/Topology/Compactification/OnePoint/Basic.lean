/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang, Yury Kudryashov
-/
module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Perfect
public import Mathlib.Topology.Sets.Opens

/-!
# The one-point compactification

We construct the one-point compactification of an arbitrary topological space `X` and prove some
properties inherited from `X`.

## Main definitions

* `OnePoint`: the one-point compactification, we use coercion for the canonical embedding
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

one point compactification, Alexandroff compactification, compactness
-/

@[expose] public section


open Set Filter Topology

/-!
### Definition and basic properties

In this section we define `OnePoint X` to be the disjoint union of `X` and `∞`, implemented as
`Option X`. Then we restate some lemmas about `Option X` for `OnePoint X`.
-/


variable {X Y : Type*}

/-- The one-point extension of an arbitrary topological space `X` -/
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

@[simp]
lemma some_eq_iff (x₁ x₂ : X) : (some x₁ = some x₂) ↔ (x₁ = x₂) := by
  rw [iff_eq_eq]
  exact Option.some.injEq x₁ x₂

instance : CoeTC X (OnePoint X) := ⟨some⟩

instance : Inhabited (OnePoint X) := ⟨∞⟩

protected lemma «forall» {p : OnePoint X → Prop} :
    (∀ (x : OnePoint X), p x) ↔ p ∞ ∧ ∀ (x : X), p x :=
  Option.forall

protected lemma «exists» {p : OnePoint X → Prop} :
    (∃ x, p x) ↔ p ∞ ∨ ∃ (x : X), p x :=
  Option.exists

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
  nofun

@[simp]
theorem infty_ne_coe (x : X) : ∞ ≠ (x : OnePoint X) :=
  nofun

/-- Recursor for `OnePoint` using the preferred forms `∞` and `↑x`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def rec {C : OnePoint X → Sort*} (infty : C ∞) (coe : ∀ x : X, C x) :
    ∀ z : OnePoint X, C z
  | ∞ => infty
  | (x : X) => coe x

/-- An elimination principle for `OnePoint`. -/
@[inline] protected def elim : OnePoint X → Y → (X → Y) → Y := Option.elim

@[simp] theorem elim_infty (y : Y) (f : X → Y) : ∞.elim y f = y := rfl

@[simp] theorem elim_some (y : Y) (f : X → Y) (x : X) : (some x).elim y f = f x := rfl

theorem isCompl_range_coe_infty : IsCompl (range ((↑) : X → OnePoint X)) {∞} :=
  isCompl_range_some_none X

theorem range_coe_union_infty : range ((↑) : X → OnePoint X) ∪ {∞} = univ :=
  range_some_union_none X

@[simp]
theorem insert_infty_range_coe : insert ∞ (range (@some X)) = univ :=
  insert_none_range_some _

@[deprecated "Use simp" (since := "2025-11-22")]
theorem range_coe_inter_infty : range ((↑) : X → OnePoint X) ∩ {∞} = ∅ := by simp

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

theorem notMem_range_coe_iff {x : OnePoint X} : x ∉ range some ↔ x = ∞ := by
  rw [← mem_compl_iff, compl_range_coe, mem_singleton_iff]

theorem infty_notMem_range_coe : ∞ ∉ range ((↑) : X → OnePoint X) :=
  notMem_range_coe_iff.2 rfl

theorem infty_notMem_image_coe {s : Set X} : ∞ ∉ ((↑) : X → OnePoint X) '' s :=
  notMem_subset (image_subset_range _ _) infty_notMem_range_coe

@[simp]
theorem coe_preimage_infty : ((↑) : X → OnePoint X) ⁻¹' {∞} = ∅ := by
  ext
  simp

/-- Extend a map `f : X → Y` to a map `OnePoint X → OnePoint Y`
by sending infinity to infinity. -/
protected def map (f : X → Y) : OnePoint X → OnePoint Y :=
  Option.map f

@[simp] theorem map_infty (f : X → Y) : OnePoint.map f ∞ = ∞ := rfl
@[simp] theorem map_some (f : X → Y) (x : X) : (x : OnePoint X).map f = f x := rfl
@[simp] theorem map_id : OnePoint.map (id : X → X) = id := Option.map_id

theorem map_comp {Z : Type*} (f : Y → Z) (g : X → Y) :
    OnePoint.map (f ∘ g) = OnePoint.map f ∘ OnePoint.map g :=
  (Option.map_comp_map _ _).symm

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
    refine ⟨?_, hs.inter ht⟩
    rintro ⟨hms', hmt'⟩
    simpa [compl_inter] using (hms hms').union (hmt hmt')
  isOpen_sUnion S ho := by
    suffices IsOpen ((↑) ⁻¹' ⋃₀ S : Set X) by
      refine ⟨?_, this⟩
      rintro ⟨s, hsS : s ∈ S, hs : ∞ ∈ s⟩
      refine IsCompact.of_isClosed_subset ((ho s hsS).1 hs) this.isClosed_compl ?_
      exact compl_subset_compl.mpr (preimage_mono <| subset_sUnion_of_mem hsS)
    rw [preimage_sUnion]
    exact isOpen_biUnion fun s hs => (ho s hs).2

variable {s : Set (OnePoint X)}

theorem isOpen_def :
    IsOpen s ↔ (∞ ∈ s → IsCompact ((↑) ⁻¹' s : Set X)ᶜ) ∧ IsOpen ((↑) ⁻¹' s : Set X) :=
  Iff.rfl

theorem isOpen_iff_of_mem' (h : ∞ ∈ s) :
    IsOpen s ↔ IsCompact ((↑) ⁻¹' s : Set X)ᶜ ∧ IsOpen ((↑) ⁻¹' s : Set X) := by
  simp [isOpen_def, h]

theorem isOpen_iff_of_mem (h : ∞ ∈ s) :
    IsOpen s ↔ IsClosed ((↑) ⁻¹' s : Set X)ᶜ ∧ IsCompact ((↑) ⁻¹' s : Set X)ᶜ := by
  simp only [isOpen_iff_of_mem' h, isClosed_compl_iff, and_comm]

theorem isOpen_iff_of_notMem (h : ∞ ∉ s) : IsOpen s ↔ IsOpen ((↑) ⁻¹' s : Set X) := by
  simp [isOpen_def, h]

theorem isClosed_iff_of_mem (h : ∞ ∈ s) : IsClosed s ↔ IsClosed ((↑) ⁻¹' s : Set X) := by
  have : ∞ ∉ sᶜ := fun H => H h
  rw [← isOpen_compl_iff, isOpen_iff_of_notMem this, ← isOpen_compl_iff, preimage_compl]

theorem isClosed_iff_of_notMem (h : ∞ ∉ s) :
    IsClosed s ↔ IsClosed ((↑) ⁻¹' s : Set X) ∧ IsCompact ((↑) ⁻¹' s : Set X) := by
  rw [← isOpen_compl_iff, isOpen_iff_of_mem (mem_compl h), ← preimage_compl, compl_compl]

@[simp]
theorem isOpen_image_coe {s : Set X} : IsOpen ((↑) '' s : Set (OnePoint X)) ↔ IsOpen s := by
  rw [isOpen_iff_of_notMem infty_notMem_image_coe, preimage_image_eq _ coe_injective]

theorem isOpen_compl_image_coe {s : Set X} :
    IsOpen ((↑) '' s : Set (OnePoint X))ᶜ ↔ IsClosed s ∧ IsCompact s := by
  rw [isOpen_iff_of_mem, ← preimage_compl, compl_compl, preimage_image_eq _ coe_injective]
  exact infty_notMem_image_coe

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
  mem_compl infty_notMem_image_coe

@[continuity]
theorem continuous_coe : Continuous ((↑) : X → OnePoint X) :=
  continuous_def.mpr fun _s hs => hs.right

theorem isOpenMap_coe : IsOpenMap ((↑) : X → OnePoint X) := fun _ => isOpen_image_coe.2

theorem isOpenEmbedding_coe : IsOpenEmbedding ((↑) : X → OnePoint X) :=
  .of_continuous_injective_isOpenMap continuous_coe coe_injective isOpenMap_coe

theorem isOpen_range_coe : IsOpen (range ((↑) : X → OnePoint X)) :=
  isOpenEmbedding_coe.isOpen_range

theorem isClosed_infty : IsClosed ({∞} : Set (OnePoint X)) := by
  rw [← compl_range_coe, isClosed_compl_iff]
  exact isOpen_range_coe

theorem nhds_coe_eq (x : X) : 𝓝 ↑x = map ((↑) : X → OnePoint X) (𝓝 x) :=
  (isOpenEmbedding_coe.map_nhds_eq x).symm

theorem nhdsWithin_coe_image (s : Set X) (x : X) :
    𝓝[(↑) '' s] (x : OnePoint X) = map (↑) (𝓝[s] x) :=
  (isOpenEmbedding_coe.isEmbedding.map_nhdsWithin_eq _ _).symm

theorem nhdsWithin_coe (s : Set (OnePoint X)) (x : X) : 𝓝[s] ↑x = map (↑) (𝓝[(↑) ⁻¹' s] x) :=
  (isOpenEmbedding_coe.map_nhdsWithin_preimage_eq _ _).symm

theorem comap_coe_nhds (x : X) : comap ((↑) : X → OnePoint X) (𝓝 x) = 𝓝 x :=
  (isOpenEmbedding_coe.isInducing.nhds_eq_comap x).symm

/-- If `x` is not an isolated point of `X`, then `x : OnePoint X` is not an isolated point
of `OnePoint X`. -/
instance nhdsNE_coe_neBot (x : X) [h : NeBot (𝓝[≠] x)] : NeBot (𝓝[≠] (x : OnePoint X)) := by
  simpa [nhdsWithin_coe, preimage, coe_eq_coe] using h.map some

theorem nhdsNE_infty_eq : 𝓝[≠] (∞ : OnePoint X) = map (↑) (coclosedCompact X) := by
  refine (nhdsWithin_basis_open ∞ _).ext (hasBasis_coclosedCompact.map _) ?_ ?_
  · rintro s ⟨hs, hso⟩
    refine ⟨_, (isOpen_iff_of_mem hs).mp hso, ?_⟩
    simp
  · rintro s ⟨h₁, h₂⟩
    refine ⟨_, ⟨mem_compl infty_notMem_image_coe, isOpen_compl_image_coe.2 ⟨h₁, h₂⟩⟩, ?_⟩
    simp [compl_image_coe, ← diff_eq]

/-- If `X` is a non-compact space, then `∞` is not an isolated point of `OnePoint X`. -/
instance nhdsNE_infty_neBot [NoncompactSpace X] : NeBot (𝓝[≠] (∞ : OnePoint X)) := by
  rw [nhdsNE_infty_eq]
  infer_instance

instance (priority := 900) instPerfectSpace [PerfectSpace X] [NoncompactSpace X] :
    PerfectSpace (OnePoint X) :=
  fun x => OnePoint.rec OnePoint.nhdsNE_infty_neBot (fun y => OnePoint.nhdsNE_coe_neBot y) x

theorem nhds_infty_eq : 𝓝 (∞ : OnePoint X) = map (↑) (coclosedCompact X) ⊔ pure ∞ := by
  rw [← nhdsNE_infty_eq, nhdsNE_sup_pure]

theorem tendsto_coe_infty : Tendsto (↑) (coclosedCompact X) (𝓝 (∞ : OnePoint X)) := by
  rw [nhds_infty_eq]
  exact Filter.Tendsto.mono_right tendsto_map le_sup_left

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
    Ultrafilter.compl_mem_iff_notMem]

theorem tendsto_nhds_infty' {α : Type*} {f : OnePoint X → α} {l : Filter α} :
    Tendsto f (𝓝 ∞) l ↔ Tendsto f (pure ∞) l ∧ Tendsto (f ∘ (↑)) (coclosedCompact X) l := by
  simp [nhds_infty_eq, and_comm]

theorem tendsto_nhds_infty {α : Type*} {f : OnePoint X → α} {l : Filter α} :
    Tendsto f (𝓝 ∞) l ↔
      ∀ s ∈ l, f ∞ ∈ s ∧ ∃ t : Set X, IsClosed t ∧ IsCompact t ∧ MapsTo (f ∘ (↑)) tᶜ s :=
  tendsto_nhds_infty'.trans <| by
    simp only [tendsto_pure_left, hasBasis_coclosedCompact.tendsto_left_iff, forall_and,
      and_assoc]

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

lemma continuous_iff {Y : Type*} [TopologicalSpace Y] (f : OnePoint X → Y) : Continuous f ↔
    Tendsto (fun x : X ↦ f x) (coclosedCompact X) (𝓝 (f ∞)) ∧ Continuous (fun x : X ↦ f x) := by
  simp only [continuous_iff_continuousAt, OnePoint.forall, continuousAt_coe, continuousAt_infty',
    Function.comp_def]

/--
A constructor for continuous maps out of a one point compactification, given a continuous map from
the underlying space and a limit value at infinity.
-/
def continuousMapMk {Y : Type*} [TopologicalSpace Y] (f : C(X, Y)) (y : Y)
    (h : Tendsto f (coclosedCompact X) (𝓝 y)) : C(OnePoint X, Y) where
  toFun x := x.elim y f
  continuous_toFun := by
    rw [continuous_iff]
    refine ⟨h, f.continuous⟩

lemma continuous_iff_from_discrete {Y : Type*} [TopologicalSpace Y]
    [DiscreteTopology X] (f : OnePoint X → Y) :
    Continuous f ↔ Tendsto (fun x : X ↦ f x) cofinite (𝓝 (f ∞)) := by
  simp [continuous_iff, cocompact_eq_cofinite, continuous_of_discreteTopology]

/--
A constructor for continuous maps out of a one point compactification of a discrete space, given a
map from the underlying space and a limit value at infinity.
-/
def continuousMapMkDiscrete {Y : Type*} [TopologicalSpace Y]
    [DiscreteTopology X] (f : X → Y) (y : Y) (h : Tendsto f cofinite (𝓝 y)) :
    C(OnePoint X, Y) :=
  continuousMapMk ⟨f, continuous_of_discreteTopology⟩ y (by simpa [cocompact_eq_cofinite])

variable (X) in
/--
Continuous maps out of the one point compactification of an infinite discrete space to a Hausdorff
space correspond bijectively to "convergent" maps out of the discrete space.
-/
noncomputable def continuousMapDiscreteEquiv (Y : Type*) [DiscreteTopology X] [TopologicalSpace Y]
    [T2Space Y] [Infinite X] :
    C(OnePoint X, Y) ≃ { f : X → Y // ∃ L, Tendsto (fun x : X ↦ f x) cofinite (𝓝 L) } where
  toFun f := ⟨(f ·), ⟨f ∞, continuous_iff_from_discrete _ |>.mp (map_continuous f)⟩⟩
  invFun f :=
    { toFun := fun x => match x with
        | ∞ => Classical.choose f.2
        | some x => f.1 x
      continuous_toFun := continuous_iff_from_discrete _ |>.mpr <| Classical.choose_spec f.2 }
  left_inv f := by
    ext x
    refine OnePoint.rec ?_ ?_ x
    · refine tendsto_nhds_unique ?_ (continuous_iff_from_discrete _ |>.mp <| map_continuous f)
      let f' : { f : X → Y // ∃ L, Tendsto (fun x : X ↦ f x) cofinite (𝓝 L) } :=
        ⟨fun x ↦ f x, ⟨f ∞, continuous_iff_from_discrete f |>.mp <| map_continuous f⟩⟩
      exact Classical.choose_spec f'.property
    · simp

lemma continuous_iff_from_nat {Y : Type*} [TopologicalSpace Y] (f : OnePoint ℕ → Y) :
    Continuous f ↔ Tendsto (fun x : ℕ ↦ f x) atTop (𝓝 (f ∞)) := by
  rw [continuous_iff_from_discrete, Nat.cofinite_eq_atTop]

/--
A constructor for continuous maps out of the one point compactification of `ℕ`, given a
sequence and a limit value at infinity.
-/
def continuousMapMkNat {Y : Type*} [TopologicalSpace Y]
    (f : ℕ → Y) (y : Y) (h : Tendsto f atTop (𝓝 y)) :
    C(OnePoint ℕ, Y) :=
  continuousMapMkDiscrete f y (by rwa [Nat.cofinite_eq_atTop])

/--
Continuous maps out of the one point compactification of `ℕ` to a Hausdorff space `Y` correspond
bijectively to convergent sequences in `Y`.
-/
noncomputable def continuousMapNatEquiv (Y : Type*) [TopologicalSpace Y] [T2Space Y] :
    C(OnePoint ℕ, Y) ≃ { f : ℕ → Y // ∃ L, Tendsto (f ·) atTop (𝓝 L) } := by
  refine (continuousMapDiscreteEquiv ℕ Y).trans {
    toFun := fun ⟨f, hf⟩ ↦ ⟨f, by rwa [← Nat.cofinite_eq_atTop]⟩
    invFun := fun ⟨f, hf⟩ ↦ ⟨f, by rwa [Nat.cofinite_eq_atTop]⟩ }

/-- If `X` is not a compact space, then the natural embedding `X → OnePoint X` has dense range.
-/
theorem denseRange_coe [NoncompactSpace X] : DenseRange ((↑) : X → OnePoint X) := by
  rw [DenseRange, ← compl_infty]
  exact dense_compl_singleton _

theorem isDenseEmbedding_coe [NoncompactSpace X] : IsDenseEmbedding ((↑) : X → OnePoint X) :=
  { isOpenEmbedding_coe with dense := denseRange_coe }

@[simp, norm_cast]
theorem specializes_coe {x y : X} : (x : OnePoint X) ⤳ y ↔ x ⤳ y :=
  isOpenEmbedding_coe.isInducing.specializes_iff

@[simp, norm_cast]
theorem inseparable_coe {x y : X} : Inseparable (x : OnePoint X) y ↔ Inseparable x y :=
  isOpenEmbedding_coe.isInducing.inseparable_iff

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

theorem continuous_map_iff [TopologicalSpace Y] {f : X → Y} :
    Continuous (OnePoint.map f) ↔
      Continuous f ∧ Tendsto f (coclosedCompact X) (coclosedCompact Y) := by
  simp_rw [continuous_iff, map_some, ← comap_coe_nhds_infty, tendsto_comap_iff, map_infty,
    isOpenEmbedding_coe.isInducing.continuous_iff (Y := Y)]
  exact and_comm

theorem continuous_map [TopologicalSpace Y] {f : X → Y} (hc : Continuous f)
    (h : Tendsto f (coclosedCompact X) (coclosedCompact Y)) :
    Continuous (OnePoint.map f) :=
  continuous_map_iff.mpr ⟨hc, h⟩

/-!
### Compactness and separation properties

In this section we prove that `OnePoint X` is a compact space; it is a T₀ (resp., T₁) space if
the original space satisfies the same separation axiom. If the original space is a locally compact
Hausdorff space, then `OnePoint X` is a normal (hence, T₃ and Hausdorff) space.

Finally, if the original space `X` is *not* compact and is a preconnected space, then
`OnePoint X` is a connected space.
-/

set_option backward.isDefEq.respectTransparency false in
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
  refine ⟨fun x y hxy => ?_⟩
  rcases inseparable_iff.1 hxy with (⟨rfl, rfl⟩ | ⟨x, rfl, y, rfl, h⟩)
  exacts [rfl, congr_arg some h.eq]

/-- The one point compactification of a `T1Space` space is a `T1Space`. -/
instance [T1Space X] : T1Space (OnePoint X) where
  t1 z := by
    induction z using OnePoint.rec
    · exact isClosed_infty
    · rw [← image_singleton, isClosed_image_coe]
      exact ⟨isClosed_singleton, isCompact_singleton⟩

/-- The one point compactification of a weakly locally compact R₁ space
is a normal topological space. -/
instance [WeaklyLocallyCompactSpace X] [R1Space X] : NormalSpace (OnePoint X) := by
  suffices R1Space (OnePoint X) by infer_instance
  have key : ∀ z : X, Disjoint (𝓝 (some z)) (𝓝 ∞) := fun z ↦ by
    rw [nhds_infty_eq, disjoint_sup_right, nhds_coe_eq, coclosedCompact_eq_cocompact,
      disjoint_map coe_injective, ← principal_singleton, disjoint_principal_right, compl_infty]
    exact ⟨disjoint_nhds_cocompact z, range_mem_map⟩
  refine ⟨fun x y ↦ ?_⟩
  induction x using OnePoint.rec <;> induction y using OnePoint.rec
  · exact .inl le_rfl
  · exact .inr (key _).symm
  · exact .inr (key _)
  · rw [nhds_coe_eq, nhds_coe_eq, disjoint_map coe_injective, specializes_coe]
    apply specializes_or_disjoint_nhds

/-- The one point compactification of a weakly locally compact Hausdorff space is a T₄
(hence, Hausdorff and regular) topological space. -/
example [WeaklyLocallyCompactSpace X] [T2Space X] : T4Space (OnePoint X) := inferInstance

/-- If `X` is not a compact space, then `OnePoint X` is a connected space. -/
instance [PreconnectedSpace X] [NoncompactSpace X] : ConnectedSpace (OnePoint X) where
  toPreconnectedSpace := isDenseEmbedding_coe.isDenseInducing.preconnectedSpace
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

instance (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    TotallySeparatedSpace (OnePoint X) where
  isTotallySeparated_univ x _ y _ hxy := by
    cases x with
    | infty =>
      refine ⟨{y}ᶜ, {y}, isOpen_compl_singleton, ?_, hxy, rfl, (compl_union_self _).symm.subset,
        disjoint_compl_left⟩
      rw [OnePoint.isOpen_iff_of_notMem]
      exacts [isOpen_discrete _, hxy]
    | coe val =>
      refine ⟨{some val}, {some val}ᶜ, ?_, isOpen_compl_singleton, rfl, hxy.symm, by simp,
        disjoint_compl_right⟩
      rw [OnePoint.isOpen_iff_of_notMem]
      exacts [isOpen_discrete _, (Option.some_ne_none val).symm]

section Uniqueness

variable [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  (y : Y) (f : X → Y) (hf : IsEmbedding f) (hy : range f = {y}ᶜ)

open scoped Classical in
/-- If `f` embeds `X` into a compact Hausdorff space `Y`, and has exactly one point outside its
range, then `(Y, f)` is the one-point compactification of `X`. -/
noncomputable def equivOfIsEmbeddingOfRangeEq :
    OnePoint X ≃ₜ Y :=
  have _i := hf.t2Space
  have : Tendsto f (coclosedCompact X) (𝓝 y) := by
    rw [coclosedCompact_eq_cocompact, hasBasis_cocompact.tendsto_left_iff]
    intro N hN
    obtain ⟨U, hU₁, hU₂, hU₃⟩ := mem_nhds_iff.mp hN
    refine ⟨f⁻¹' Uᶜ, ?_, by simpa using (mapsTo_preimage f U).mono_right hU₁⟩
    rw [hf.isCompact_iff, image_preimage_eq_iff.mpr (by simpa [hy])]
    exact (isClosed_compl_iff.mpr hU₂).isCompact
  let e : OnePoint X ≃ Y :=
    { toFun := fun p ↦ p.elim y f
      invFun := fun q ↦ if hq : q = y then ∞ else ↑(show q ∈ range f from by simpa [hy]).choose
      left_inv := fun p ↦ by
        induction p using OnePoint.rec with
        | infty => simp
        | coe p =>
          have hp : f p ≠ y := by simpa [hy] using mem_range_self (f := f) p
          simpa [hp] using hf.injective (mem_range_self p).choose_spec
      right_inv := fun q ↦ by
        rcases eq_or_ne q y with rfl | hq
        · simp
        · have hq' : q ∈ range f := by simpa [hy]
          simpa [hq] using hq'.choose_spec }
  Continuous.homeoOfEquivCompactToT2 <| (continuous_iff e).mpr ⟨this, hf.continuous⟩

@[simp]
lemma equivOfIsEmbeddingOfRangeEq_apply_coe (x : X) :
    equivOfIsEmbeddingOfRangeEq y f hf hy x = f x :=
  rfl

@[simp]
lemma equivOfIsEmbeddingOfRangeEq_apply_infty :
    equivOfIsEmbeddingOfRangeEq y f hf hy ∞ = y :=
  rfl

end Uniqueness

end OnePoint

namespace Homeomorph

variable [TopologicalSpace X] [TopologicalSpace Y]

open OnePoint

/-- Extend a homeomorphism of topological spaces
to the homeomorphism of their one point compactifications. -/
@[simps]
def onePointCongr (h : X ≃ₜ Y) : OnePoint X ≃ₜ OnePoint Y where
  __ := h.toEquiv.withTopCongr
  toFun := OnePoint.map h
  invFun := OnePoint.map h.symm
  continuous_toFun := continuous_map (map_continuous h) h.map_coclosedCompact.le
  continuous_invFun := continuous_map (map_continuous h.symm) h.symm.map_coclosedCompact.le

end Homeomorph

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
