/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Etienne Marion
-/
module

public import Mathlib.Topology.Category.CompHaus.Basic
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Compactly generated topological spaces

This file defines compactly generated topological spaces. A compactly generated space is a space `X`
whose topology is coinduced by continuous maps from compact Hausdorff spaces to `X`. In such a
space, a set `s` is closed (resp. open) if and only if for all compact Hausdorff space `K` and
`f : K → X` continuous, `f ⁻¹' s` is closed (resp. open) in `K`.

We provide two definitions. `UCompactlyGeneratedSpace.{u} X` corresponds to the type class where the
compact Hausdorff spaces are taken in an arbitrary universe `u`, and should therefore always be used
with an explicit universe parameter. It is intended for categorical purposes.

`CompactlyGeneratedSpace X` corresponds to the case where compact Hausdorff spaces are taken in
the same universe as `X`, and is intended for topological purposes.

We prove basic properties and instances, and prove that a `SequentialSpace` is compactly generated,
as well as a Hausdorff `WeaklyLocallyCompactSpace`.

## Main definitions

* `UCompactlyGeneratedSpace.{u} X`: the topology of `X` is coinduced by continuous maps coming from
  compact Hausdorff spaces in universe `u`.
* `CompactlyGeneratedSpace X`: the topology of `X` is coinduced by continuous maps coming from
  compact Hausdorff spaces in the same universe as `X`.

## References

* <https://en.wikipedia.org/wiki/Compactly_generated_space>
* <https://ncatlab.org/nlab/files/StricklandCGHWSpaces.pdf>

## Tags

compactly generated space
-/

@[expose] public section

universe u v w x

open TopologicalSpace Filter Topology Set

section UCompactlyGeneratedSpace

variable {X : Type w} {Y : Type x}

/--
The compactly generated topology on a topological space `X`. This is the finest topology
which makes all maps from compact Hausdorff spaces to `X`, which are continuous for the original
topology, continuous.

Note: this definition should be used with an explicit universe parameter `u` for the size of the
compact Hausdorff spaces mapping to `X`.
-/
@[implicit_reducible]
def TopologicalSpace.compactlyGenerated (X : Type w) [TopologicalSpace X] : TopologicalSpace X :=
  let f : (Σ (i : (S : CompHaus.{u}) × C(S, X)), i.fst) → X := fun ⟨⟨_, i⟩, s⟩ ↦ i s
  coinduced f inferInstance

lemma continuous_from_compactlyGenerated [TopologicalSpace X] [t : TopologicalSpace Y] (f : X → Y)
    (h : ∀ (S : CompHaus.{u}) (g : C(S, X)), Continuous (f ∘ g)) :
        Continuous[compactlyGenerated.{u} X, t] f := by
  rw [continuous_coinduced_dom]
  continuity

/--
A topological space `X` is compactly generated if its topology is finer than (and thus equal to)
the compactly generated topology, i.e. it is coinduced by the continuous maps from compact
Hausdorff spaces to `X`.

This version includes an explicit universe parameter `u` which should always be specified. It is
intended for categorical purposes. See `CompactlyGeneratedSpace` for the version without this
parameter, intended for topological purposes.
-/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the compact space universe `u` would default
-- to a universe output parameter. See Note [universe output parameters and typeclass caching].
@[univ_out_params]
class UCompactlyGeneratedSpace (X : Type v) [t : TopologicalSpace X] : Prop where
  /-- The topology of `X` is finer than the compactly generated topology. -/
  le_compactlyGenerated : t ≤ compactlyGenerated.{u} X

lemma eq_compactlyGenerated [t : TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X] :
    t = compactlyGenerated.{u} X := by
  apply le_antisymm
  · exact UCompactlyGeneratedSpace.le_compactlyGenerated
  · simp only [compactlyGenerated, ← continuous_iff_coinduced_le, continuous_sigma_iff,
      Sigma.forall]
    exact fun S f ↦ f.2

instance (X : Type v) [t : TopologicalSpace X] [DiscreteTopology X] :
    UCompactlyGeneratedSpace.{u} X where
  le_compactlyGenerated := by
    rw [DiscreteTopology.eq_bot (t := t)]
    exact bot_le

/- The unused variable linter flags `[tY : TopologicalSpace Y]`,
but we want to use this as a named argument, so we need to disable the linter. -/
set_option linter.unusedVariables false in
/-- Let `f : X → Y`. Suppose that to prove that `f` is continuous, it suffices to show that
for every compact Hausdorff space `K` and every continuous map `g : K → X`, `f ∘ g` is continuous.
Then `X` is compactly generated. -/
lemma uCompactlyGeneratedSpace_of_continuous_maps [t : TopologicalSpace X]
    (h : ∀ {Y : Type w} [tY : TopologicalSpace Y] (f : X → Y),
      (∀ (S : CompHaus.{u}) (g : C(S, X)), Continuous (f ∘ g)) → Continuous f) :
        UCompactlyGeneratedSpace.{u} X where
  le_compactlyGenerated := by
    suffices Continuous[t, compactlyGenerated.{u} X] (id : X → X) by
      rwa [← continuous_id_iff_le]
    apply h (tY := compactlyGenerated.{u} X)
    intro S g
    let f : (Σ (i : (T : CompHaus.{u}) × C(T, X)), i.fst) → X := fun ⟨⟨_, i⟩, s⟩ ↦ i s
    suffices ∀ (i : (T : CompHaus.{u}) × C(T, X)),
      Continuous[inferInstance, compactlyGenerated X] (fun (a : i.fst) ↦ f ⟨i, a⟩) from this ⟨S, g⟩
    rw [← @continuous_sigma_iff]
    apply continuous_coinduced_rng

variable [tX : TopologicalSpace X] [tY : TopologicalSpace Y]

/-- If `X` is compactly generated, to prove that `f : X → Y` is continuous it is enough to show
that for every compact Hausdorff space `K` and every continuous map `g : K → X`,
`f ∘ g` is continuous. -/
lemma continuous_from_uCompactlyGeneratedSpace [UCompactlyGeneratedSpace.{u} X] (f : X → Y)
    (h : ∀ (S : CompHaus.{u}) (g : C(S, X)), Continuous (f ∘ g)) : Continuous f := by
  apply continuous_le_dom UCompactlyGeneratedSpace.le_compactlyGenerated
  exact continuous_from_compactlyGenerated f h

/-- A topological space `X` is compactly generated if a set `s` is closed when `f ⁻¹' s` is
closed for every continuous map `f : K → X`, where `K` is compact Hausdorff. -/
theorem uCompactlyGeneratedSpace_of_isClosed
    (h : ∀ (s : Set X), (∀ (S : CompHaus.{u}) (f : C(S, X)), IsClosed (f ⁻¹' s)) → IsClosed s) :
    UCompactlyGeneratedSpace.{u} X :=
  uCompactlyGeneratedSpace_of_continuous_maps fun _ h' ↦
    continuous_iff_isClosed.2 fun _ hs ↦ h _ fun S g ↦ hs.preimage (h' S g)

/-- A topological space `X` is compactly generated if a set `s` is open when `f ⁻¹' s` is
open for every continuous map `f : K → X`, where `K` is compact Hausdorff. -/
theorem uCompactlyGeneratedSpace_of_isOpen
    (h : ∀ (s : Set X), (∀ (S : CompHaus.{u}) (f : C(S, X)), IsOpen (f ⁻¹' s)) → IsOpen s) :
    UCompactlyGeneratedSpace.{u} X :=
  uCompactlyGeneratedSpace_of_continuous_maps fun _ h' ↦
    continuous_def.2 fun _ hs ↦ h _ fun S g ↦ hs.preimage (h' S g)

/-- In a compactly generated space `X`, a set `s` is closed when `f ⁻¹' s` is
closed for every continuous map `f : K → X`, where `K` is compact Hausdorff. -/
theorem UCompactlyGeneratedSpace.isClosed [UCompactlyGeneratedSpace.{u} X] {s : Set X}
    (hs : ∀ (S : CompHaus.{u}) (f : C(S, X)), IsClosed (f ⁻¹' s)) : IsClosed s := by
  rw [eq_compactlyGenerated (X := X), TopologicalSpace.compactlyGenerated, isClosed_coinduced,
    isClosed_sigma_iff]
  exact fun ⟨S, f⟩ ↦ hs S f

/-- In a compactly generated space `X`, a set `s` is open when `f ⁻¹' s` is
open for every continuous map `f : K → X`, where `K` is compact Hausdorff. -/
theorem UCompactlyGeneratedSpace.isOpen [UCompactlyGeneratedSpace.{u} X] {s : Set X}
    (hs : ∀ (S : CompHaus.{u}) (f : C(S, X)), IsOpen (f ⁻¹' s)) : IsOpen s := by
  rw [eq_compactlyGenerated (X := X), TopologicalSpace.compactlyGenerated, isOpen_coinduced,
    isOpen_sigma_iff]
  exact fun ⟨S, f⟩ ↦ hs S f

/-- If the topology of `X` is coinduced by a continuous function whose domain is
compactly generated, then so is `X`. -/
theorem uCompactlyGeneratedSpace_of_coinduced
    [UCompactlyGeneratedSpace.{u} X] {f : X → Y} (hf : Continuous f) (ht : tY = coinduced f tX) :
    UCompactlyGeneratedSpace.{u} Y := by
  refine uCompactlyGeneratedSpace_of_isClosed fun s h ↦ ?_
  rw [ht, isClosed_coinduced]
  exact UCompactlyGeneratedSpace.isClosed fun _ ⟨g, hg⟩ ↦ h _ ⟨_, hf.comp hg⟩

/-- The quotient of a compactly generated space is compactly generated. -/
instance {S : Setoid X} [UCompactlyGeneratedSpace.{u} X] :
    UCompactlyGeneratedSpace.{u} (Quotient S) :=
  uCompactlyGeneratedSpace_of_coinduced continuous_quotient_mk' rfl

/-- The sum of two compactly generated spaces is compactly generated. -/
instance [UCompactlyGeneratedSpace.{u} X] [UCompactlyGeneratedSpace.{v} Y] :
    UCompactlyGeneratedSpace.{max u v} (X ⊕ Y) := by
  refine uCompactlyGeneratedSpace_of_isClosed fun s h ↦ isClosed_sum_iff.2 ⟨?_, ?_⟩
  all_goals
    refine UCompactlyGeneratedSpace.isClosed fun S ⟨f, hf⟩ ↦ ?_
  · let g : ULift.{v} S → X ⊕ Y := Sum.inl ∘ f ∘ ULift.down
    have hg : Continuous g := continuous_inl.comp <| hf.comp continuous_uliftDown
    exact (h (CompHaus.of (ULift.{v} S)) ⟨g, hg⟩).preimage continuous_uliftUp
  · let g : ULift.{u} S → X ⊕ Y := Sum.inr ∘ f ∘ ULift.down
    have hg : Continuous g := continuous_inr.comp <| hf.comp continuous_uliftDown
    exact (h (CompHaus.of (ULift.{u} S)) ⟨g, hg⟩).preimage continuous_uliftUp

/-- The sigma type associated to a family of compactly generated spaces is compactly generated. -/
instance {ι : Type v} {X : ι → Type w} [∀ i, TopologicalSpace (X i)]
    [∀ i, UCompactlyGeneratedSpace.{u} (X i)] : UCompactlyGeneratedSpace.{u} (Σ i, X i) :=
  uCompactlyGeneratedSpace_of_isClosed fun _ h ↦ isClosed_sigma_iff.2 fun i ↦
    UCompactlyGeneratedSpace.isClosed fun S ⟨f, hf⟩ ↦
      h S ⟨Sigma.mk i ∘ f, continuous_sigmaMk.comp hf⟩

open OnePoint in
/-- A sequential space is compactly generated.

The proof is taken from <https://ncatlab.org/nlab/files/StricklandCGHWSpaces.pdf>,
Proposition 1.6. -/
instance (priority := 100) [SequentialSpace X] : UCompactlyGeneratedSpace.{u} X := by
  refine uCompactlyGeneratedSpace_of_isClosed fun s h ↦
    SequentialSpace.isClosed_of_seq _ fun u p hu hup ↦ ?_
  let g : ULift.{u} (OnePoint ℕ) → X := (continuousMapMkNat u p hup) ∘ ULift.down
  change ULift.up ∞ ∈ g ⁻¹' s
  have : Filter.Tendsto (@OnePoint.some ℕ) Filter.atTop (𝓝 ∞) := by
    rw [← Nat.cofinite_eq_atTop, ← cocompact_eq_cofinite, ← coclosedCompact_eq_cocompact]
    exact tendsto_coe_infty
  apply IsClosed.mem_of_tendsto _ ((continuous_uliftUp.tendsto ∞).comp this)
  · simp only [Function.comp_apply, mem_preimage, eventually_atTop, ge_iff_le]
    exact ⟨0, fun b _ ↦ hu b⟩
  · exact h (CompHaus.of (ULift.{u} (OnePoint ℕ))) ⟨g, by fun_prop⟩

end UCompactlyGeneratedSpace

section CompactlyGeneratedSpace

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/--
A topological space `X` is compactly generated if its topology is finer than (and thus equal to)
the compactly generated topology, i.e. it is coinduced by the continuous maps from compact
Hausdorff spaces to `X`.

In this version, intended for topological purposes, the compact spaces are taken
in the same universe as `X`. See `UCompactlyGeneratedSpace` for a version with an explicit
universe parameter, intended for categorical purposes.
-/
abbrev CompactlyGeneratedSpace (X : Type u) [TopologicalSpace X] : Prop :=
  UCompactlyGeneratedSpace.{u} X

/-- If `X` is compactly generated, to prove that `f : X → Y` is continuous it is enough to show
that for every compact Hausdorff space `K` and every continuous map `g : K → X`,
`f ∘ g` is continuous. -/
lemma continuous_from_compactlyGeneratedSpace [CompactlyGeneratedSpace X] (f : X → Y)
    (h : ∀ (K : Type u) [TopologicalSpace K], [CompactSpace K] → [T2Space K] →
      (∀ g : K → X, Continuous g → Continuous (f ∘ g))) : Continuous f :=
  continuous_from_uCompactlyGeneratedSpace f fun K ⟨g, hg⟩ ↦ h K g hg

/-- Let `f : X → Y`. Suppose that to prove that `f` is continuous, it suffices to show that
for every compact Hausdorff space `K` and every continuous map `g : K → X`, `f ∘ g` is continuous.
Then `X` is compactly generated. -/
lemma compactlyGeneratedSpace_of_continuous_maps
    (h : ∀ {Y : Type u} [TopologicalSpace Y] (f : X → Y),
      (∀ (K : Type u) [TopologicalSpace K], [CompactSpace K] → [T2Space K] →
        (∀ g : K → X, Continuous g → Continuous (f ∘ g))) → Continuous f) :
    CompactlyGeneratedSpace X :=
  uCompactlyGeneratedSpace_of_continuous_maps fun f h' ↦ h f fun K _ _ _ g hg ↦
    h' (CompHaus.of K) ⟨g, hg⟩

/-- A topological space `X` is compactly generated if a set `s` is closed when `f ⁻¹' s` is
closed for every continuous map `f : K → X`, where `K` is compact Hausdorff. -/
theorem compactlyGeneratedSpace_of_isClosed
    (h : ∀ (s : Set X), (∀ (K : Type u) [TopologicalSpace K], [CompactSpace K] → [T2Space K] →
      ∀ (f : K → X), Continuous f → IsClosed (f ⁻¹' s)) → IsClosed s) :
    CompactlyGeneratedSpace X :=
  uCompactlyGeneratedSpace_of_isClosed fun s h' ↦ h s fun K _ _ _ f hf ↦ h' (CompHaus.of K) ⟨f, hf⟩

/-- In a compactly generated space `X`, a set `s` is closed when `f ⁻¹' s` is
closed for every continuous map `f : K → X`, where `K` is compact Hausdorff. -/
theorem CompactlyGeneratedSpace.isClosed' [CompactlyGeneratedSpace X] {s : Set X}
    (hs : ∀ (K : Type u) [TopologicalSpace K], [CompactSpace K] → [T2Space K] →
      ∀ (f : K → X), Continuous f → IsClosed (f ⁻¹' s)) : IsClosed s :=
  UCompactlyGeneratedSpace.isClosed fun S ⟨f, hf⟩ ↦ hs S f hf

/-- In a compactly generated space `X`, a set `s` is closed when `s ∩ K` is
closed for every compact set `K`. -/
theorem CompactlyGeneratedSpace.isClosed [CompactlyGeneratedSpace X] {s : Set X}
    (hs : ∀ ⦃K⦄, IsCompact K → IsClosed (s ∩ K)) : IsClosed s := by
  refine isClosed' fun K _ _ _ f hf ↦ ?_
  rw [← Set.preimage_inter_range]
  exact (hs (isCompact_range hf)).preimage hf

/-- A topological space `X` is compactly generated if a set `s` is open when `f ⁻¹' s` is
open for every continuous map `f : K → X`, where `K` is compact Hausdorff. -/
theorem compactlyGeneratedSpace_of_isOpen
    (h : ∀ (s : Set X), (∀ (K : Type u) [TopologicalSpace K], [CompactSpace K] → [T2Space K] →
      ∀ (f : K → X), Continuous f → IsOpen (f ⁻¹' s)) → IsOpen s) :
    CompactlyGeneratedSpace X :=
  uCompactlyGeneratedSpace_of_isOpen fun s h' ↦ h s fun K _ _ _ f hf ↦ h' (CompHaus.of K) ⟨f, hf⟩

/-- In a compactly generated space `X`, a set `s` is open when `f ⁻¹' s` is
open for every continuous map `f : K → X`, where `K` is compact Hausdorff. -/
theorem CompactlyGeneratedSpace.isOpen' [CompactlyGeneratedSpace X] {s : Set X}
    (hs : ∀ (K : Type u) [TopologicalSpace K], [CompactSpace K] → [T2Space K] →
      ∀ (f : K → X), Continuous f → IsOpen (f ⁻¹' s)) : IsOpen s :=
  UCompactlyGeneratedSpace.isOpen fun S ⟨f, hf⟩ ↦ hs S f hf

/-- In a compactly generated space `X`, a set `s` is open when `s ∩ K` is
closed for every open set `K`. -/
theorem CompactlyGeneratedSpace.isOpen [CompactlyGeneratedSpace X] {s : Set X}
    (hs : ∀ ⦃K⦄, IsCompact K → IsOpen (s ∩ K)) : IsOpen s := by
  refine isOpen' fun K _ _ _ f hf ↦ ?_
  rw [← Set.preimage_inter_range]
  exact (hs (isCompact_range hf)).preimage hf

/-- If the topology of `X` is coinduced by a continuous function whose domain is
compactly generated, then so is `X`. -/
theorem compactlyGeneratedSpace_of_coinduced
    {X : Type u} [tX : TopologicalSpace X] {Y : Type u} [tY : TopologicalSpace Y]
    [CompactlyGeneratedSpace X] {f : X → Y} (hf : Continuous f) (ht : tY = coinduced f tX) :
    CompactlyGeneratedSpace Y := uCompactlyGeneratedSpace_of_coinduced hf ht

/-- The sigma type associated to a family of compactly generated spaces is compactly generated. -/
instance {ι : Type u} {X : ι → Type v}
    [∀ i, TopologicalSpace (X i)] [∀ i, CompactlyGeneratedSpace (X i)] :
    CompactlyGeneratedSpace (Σ i, X i) := by
  refine compactlyGeneratedSpace_of_isClosed fun s h ↦ isClosed_sigma_iff.2 fun i ↦
    CompactlyGeneratedSpace.isClosed' fun K _ _ _ f hf ↦ ?_
  let g : ULift.{u} K → (Σ i, X i) := Sigma.mk i ∘ f ∘ ULift.down
  have hg : Continuous g := continuous_sigmaMk.comp <| hf.comp continuous_uliftDown
  exact (h _ g hg).preimage continuous_uliftUp

variable [T2Space X]

theorem CompactlyGeneratedSpace.isClosed_iff_of_t2 [CompactlyGeneratedSpace X] (s : Set X) :
    IsClosed s ↔ ∀ ⦃K⦄, IsCompact K → IsClosed (s ∩ K) where
  mp hs _ hK := hs.inter hK.isClosed
  mpr := CompactlyGeneratedSpace.isClosed

/-- Let `s ⊆ X`. Suppose that `X` is Hausdorff, and that to prove that `s` is closed,
it suffices to show that for every compact set `K ⊆ X`, `s ∩ K` is closed.
Then `X` is compactly generated. -/
theorem compactlyGeneratedSpace_of_isClosed_of_t2
    (h : ∀ s, (∀ (K : Set X), IsCompact K → IsClosed (s ∩ K)) → IsClosed s) :
    CompactlyGeneratedSpace X := by
  refine compactlyGeneratedSpace_of_isClosed fun s hs ↦ h s fun K hK ↦ ?_
  rw [Set.inter_comm, ← Subtype.image_preimage_coe]
  apply hK.isClosed.isClosedMap_subtype_val
  have : CompactSpace ↑K := isCompact_iff_compactSpace.1 hK
  exact hs _ Subtype.val continuous_subtype_val

open scoped Set.Notation in
/-- Let `s ⊆ X`. Suppose that `X` is Hausdorff, and that to prove that `s` is open,
it suffices to show that for every compact set `K ⊆ X`, `s ∩ K` is open in `K`.
Then `X` is compactly generated. -/
theorem compactlyGeneratedSpace_of_isOpen_of_t2
    (h : ∀ s, (∀ (K : Set X), IsCompact K → IsOpen (K ↓∩ s)) → IsOpen s) :
    CompactlyGeneratedSpace X := by
  refine compactlyGeneratedSpace_of_isOpen fun s hs ↦ h s fun K hK ↦ ?_
  have : CompactSpace ↑K := isCompact_iff_compactSpace.1 hK
  exact hs _ Subtype.val continuous_subtype_val

/-- A Hausdorff and weakly locally compact space is compactly generated. -/
instance (priority := 100) [WeaklyLocallyCompactSpace X] :
    CompactlyGeneratedSpace X := by
  refine compactlyGeneratedSpace_of_isClosed_of_t2 fun s h ↦ ?_
  rw [isClosed_iff_forall_filter]
  intro x ℱ hℱ₁ hℱ₂ hℱ₃
  rcases exists_compact_mem_nhds x with ⟨K, hK, K_mem⟩
  exact Set.mem_of_mem_inter_left <| isClosed_iff_forall_filter.1 (h _ hK) x ℱ hℱ₁
    (Filter.inf_principal ▸ le_inf hℱ₂ (le_trans hℱ₃ <| Filter.le_principal_iff.2 K_mem)) hℱ₃

/-- Every compactly generated space is a compactly coherent space. -/
instance to_compactlyCoherentSpace [CompactlyGeneratedSpace X] : CompactlyCoherentSpace X :=
  CompactlyCoherentSpace.of_isOpen_forall_compactSpace fun _ h ↦ CompactlyGeneratedSpace.isOpen'
    fun K _ _ _ f hf ↦ h K f hf

/-- A compactly coherent space that is Hausdorff is compactly generated. -/
instance of_compactlyCoherentSpace_of_t2 [CompactlyCoherentSpace X] :
    CompactlyGeneratedSpace X := by
  apply compactlyGeneratedSpace_of_isClosed_of_t2
  intro s hs
  rw [CompactlyCoherentSpace.isClosed_iff]
  intro K hK
  rw [← Subtype.preimage_coe_inter_self]
  exact (hs K hK).preimage_val

end CompactlyGeneratedSpace
