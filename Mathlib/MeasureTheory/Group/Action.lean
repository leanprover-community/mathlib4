/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Dynamics.Minimal
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Group.Defs
import Mathlib.Order.Filter.EventuallyConst

/-!
# Measures invariant under group actions

A measure `μ : Measure α` is said to be *invariant* under an action of a group `G` if scalar
multiplication by `c : G` is a measure-preserving map for all `c`. In this file we define a
typeclass for measures invariant under action of an (additive or multiplicative) group and prove
some basic properties of such measures.
-/


open scoped ENNReal NNReal Pointwise Topology
open MeasureTheory.Measure Set Function Filter

namespace MeasureTheory

universe u v w

variable {G : Type u} {M : Type v} {α : Type w}

namespace SMulInvariantMeasure

@[to_additive]
instance zero [MeasurableSpace α] [SMul M α] : SMulInvariantMeasure M α (0 : Measure α) :=
  ⟨fun _ _ _ => rfl⟩

variable [SMul M α] {m : MeasurableSpace α} {μ ν : Measure α}

@[to_additive]
instance add [SMulInvariantMeasure M α μ] [SMulInvariantMeasure M α ν] :
    SMulInvariantMeasure M α (μ + ν) :=
  ⟨fun c _s hs =>
    show _ + _ = _ + _ from
      congr_arg₂ (· + ·) (measure_preimage_smul c hs) (measure_preimage_smul c hs)⟩

@[to_additive]
instance smul [SMulInvariantMeasure M α μ] (c : ℝ≥0∞) : SMulInvariantMeasure M α (c • μ) :=
  ⟨fun a _s hs => show c • _ = c • _ from congr_arg (c • ·) (measure_preimage_smul a hs)⟩

@[to_additive]
instance smul_nnreal [SMulInvariantMeasure M α μ] (c : ℝ≥0) : SMulInvariantMeasure M α (c • μ) :=
  SMulInvariantMeasure.smul c

end SMulInvariantMeasure

section AE_smul

variable {m : MeasurableSpace α} [SMul G α]
  (μ : Measure α) [SMulInvariantMeasure G α μ] {s : Set α}

/-- See also `measure_preimage_smul_of_nullMeasurableSet` and `measure_preimage_smul`. -/
@[to_additive
/-- See also `measure_preimage_smul_of_nullMeasurableSet` and `measure_preimage_smul`. -/]
theorem measure_preimage_smul_le (c : G) (s : Set α) : μ ((c • ·) ⁻¹' s) ≤ μ s :=
  (outerMeasure_le_iff (m := .map (c • ·) μ.1)).2
    (fun _s hs ↦ (SMulInvariantMeasure.measure_preimage_smul _ hs).le) _

/-- See also `smul_ae`. -/
@[to_additive /-- See also `vadd_ae`. -/]
theorem tendsto_smul_ae (c : G) : Filter.Tendsto (c • ·) (ae μ) (ae μ) := fun _s hs ↦
  eq_bot_mono (measure_preimage_smul_le μ c _) hs

variable {μ}

@[to_additive]
theorem measure_preimage_smul_null (h : μ s = 0) (c : G) : μ ((c • ·) ⁻¹' s) = 0 :=
  eq_bot_mono (measure_preimage_smul_le μ c _) h

@[to_additive]
theorem measure_preimage_smul_of_nullMeasurableSet (hs : NullMeasurableSet s μ) (c : G) :
    μ ((c • ·) ⁻¹' s) = μ s := by
  rw [← measure_toMeasurable s,
    ← SMulInvariantMeasure.measure_preimage_smul c (measurableSet_toMeasurable μ s)]
  exact measure_congr (tendsto_smul_ae μ c hs.toMeasurable_ae_eq) |>.symm

end AE_smul

section AE

variable {m : MeasurableSpace α} [Group G] [MulAction G α]
  (μ : Measure α) [SMulInvariantMeasure G α μ]

@[to_additive (attr := simp)]
theorem measure_preimage_smul (c : G) (s : Set α) : μ ((c • ·) ⁻¹' s) = μ s :=
  (measure_preimage_smul_le μ c s).antisymm <| by
    simpa [preimage_preimage] using measure_preimage_smul_le μ c⁻¹ ((c • ·) ⁻¹' s)

@[to_additive (attr := simp)]
theorem measure_smul (c : G) (s : Set α) : μ (c • s) = μ s := by
  simpa only [preimage_smul_inv] using measure_preimage_smul μ c⁻¹ s

variable {μ}

@[to_additive]
theorem measure_smul_eq_zero_iff {s} (c : G) : μ (c • s) = 0 ↔ μ s = 0 := by
  rw [measure_smul]

@[to_additive]
theorem measure_smul_null {s} (h : μ s = 0) (c : G) : μ (c • s) = 0 :=
  (measure_smul_eq_zero_iff _).2 h

@[to_additive (attr := simp)]
theorem smul_mem_ae (c : G) {s : Set α} : c • s ∈ ae μ ↔ s ∈ ae μ := by
  simp only [mem_ae_iff, ← smul_set_compl, measure_smul_eq_zero_iff]

@[to_additive (attr := simp)]
theorem smul_ae (c : G) : c • ae μ = ae μ := by
  ext s
  simp only [mem_smul_filter, preimage_smul, smul_mem_ae]

@[to_additive (attr := simp)]
theorem eventuallyConst_smul_set_ae (c : G) {s : Set α} :
    EventuallyConst (c • s : Set α) (ae μ) ↔ EventuallyConst s (ae μ) := by
  rw [← preimage_smul_inv, eventuallyConst_preimage, Filter.map_smul, smul_ae]

@[to_additive (attr := simp)]
theorem smul_set_ae_le (c : G) {s t : Set α} : c • s ≤ᵐ[μ] c • t ↔ s ≤ᵐ[μ] t := by
  simp only [ae_le_set, ← smul_set_sdiff, measure_smul_eq_zero_iff]

@[to_additive (attr := simp)]
theorem smul_set_ae_eq (c : G) {s t : Set α} : c • s =ᵐ[μ] c • t ↔ s =ᵐ[μ] t := by
  simp only [Filter.eventuallyLE_antisymm_iff, smul_set_ae_le]

end AE

section MeasurableSMul

variable {m : MeasurableSpace α} [MeasurableSpace M] [SMul M α] [MeasurableSMul M α] (c : M)
  (μ : Measure α) [SMulInvariantMeasure M α μ]

@[to_additive (attr := simp)]
theorem measurePreserving_smul : MeasurePreserving (c • ·) μ μ :=
  { measurable := measurable_const_smul c
    map_eq := by
      ext1 s hs
      rw [map_apply (measurable_const_smul c) hs]
      exact SMulInvariantMeasure.measure_preimage_smul c hs }

@[to_additive (attr := simp)]
protected theorem map_smul : map (c • ·) μ = μ :=
  (measurePreserving_smul c μ).map_eq

end MeasurableSMul

@[to_additive]
theorem MeasurePreserving.smulInvariantMeasure_iterateMulAct
    {f : α → α} {_ : MeasurableSpace α} {μ : Measure α} (hf : MeasurePreserving f μ μ) :
    SMulInvariantMeasure (IterateMulAct f) α μ :=
  ⟨fun n _s hs ↦ (hf.iterate n.val).measure_preimage hs.nullMeasurableSet⟩

@[to_additive]
theorem smulInvariantMeasure_iterateMulAct
    {f : α → α} {_ : MeasurableSpace α} {μ : Measure α} (hf : Measurable f) :
    SMulInvariantMeasure (IterateMulAct f) α μ ↔ MeasurePreserving f μ μ :=
  ⟨fun _ ↦
    have := hf.measurableSMul₂_iterateMulAct
    measurePreserving_smul (IterateMulAct.mk (f := f) 1) μ,
    MeasurePreserving.smulInvariantMeasure_iterateMulAct⟩

section SMulHomClass

universe uM uN uα uβ
variable {M : Type uM} {N : Type uN} {α : Type uα} {β : Type uβ}
  [MeasurableSpace M] [MeasurableSpace N] [MeasurableSpace α] [MeasurableSpace β]

@[to_additive]
theorem smulInvariantMeasure_map [SMul M α] [SMul M β]
    [MeasurableSMul M β]
    (μ : Measure α) [SMulInvariantMeasure M α μ] (f : α → β)
    (hsmul : ∀ (m : M) a, f (m • a) = m • f a) (hf : Measurable f) :
    SMulInvariantMeasure M β (map f μ) where
  measure_preimage_smul m S hS := calc
    map f μ ((m • ·) ⁻¹' S)
    _ = μ (f ⁻¹' ((m • ·) ⁻¹' S)) := map_apply hf <| hS.preimage (measurable_const_smul _)
    _ = μ ((m • f ·) ⁻¹' S) := by rw [preimage_preimage]
    _ = μ ((f <| m • ·) ⁻¹' S) := by simp_rw [hsmul]
    _ = μ ((m • ·) ⁻¹' (f ⁻¹' S)) := by rw [← preimage_preimage]
    _ = μ (f ⁻¹' S) := by rw [SMulInvariantMeasure.measure_preimage_smul m (hS.preimage hf)]
    _ = map f μ S := (map_apply hf hS).symm

@[to_additive]
instance smulInvariantMeasure_map_smul [SMul M α] [SMul N α] [SMulCommClass N M α]
    [MeasurableSMul M α] [MeasurableSMul N α]
    (μ : Measure α) [SMulInvariantMeasure M α μ] (n : N) :
    SMulInvariantMeasure M α (map (n • ·) μ) :=
  smulInvariantMeasure_map μ _ (smul_comm n) <| measurable_const_smul _

end SMulHomClass

variable (G) {m : MeasurableSpace α} [Group G] [MulAction G α] (μ : Measure α)

variable [MeasurableSpace G] [MeasurableSMul G α] in
/-- Equivalent definitions of a measure invariant under a multiplicative action of a group.

- 0: `SMulInvariantMeasure G α μ`;

- 1: for every `c : G` and a measurable set `s`, the measure of the preimage of `s` under scalar
     multiplication by `c` is equal to the measure of `s`;

- 2: for every `c : G` and a measurable set `s`, the measure of the image `c • s` of `s` under
     scalar multiplication by `c` is equal to the measure of `s`;

- 3, 4: properties 2, 3 for any set, including non-measurable ones;

- 5: for any `c : G`, scalar multiplication by `c` maps `μ` to `μ`;

- 6: for any `c : G`, scalar multiplication by `c` is a measure-preserving map. -/
@[to_additive]
theorem smulInvariantMeasure_tfae :
    List.TFAE
      [SMulInvariantMeasure G α μ,
        ∀ (c : G) (s), MeasurableSet s → μ ((c • ·) ⁻¹' s) = μ s,
        ∀ (c : G) (s), MeasurableSet s → μ (c • s) = μ s,
        ∀ (c : G) (s), μ ((c • ·) ⁻¹' s) = μ s,
        ∀ (c : G) (s), μ (c • s) = μ s,
        ∀ c : G, Measure.map (c • ·) μ = μ,
        ∀ c : G, MeasurePreserving (c • ·) μ μ] := by
  tfae_have 1 ↔ 2 := ⟨fun h => h.1, fun h => ⟨h⟩⟩
  tfae_have 1 → 6 := fun h c => (measurePreserving_smul c μ).map_eq
  tfae_have 6 → 7 := fun H c => ⟨measurable_const_smul c, H c⟩
  tfae_have 7 → 4 := fun H c => (H c).measure_preimage_emb (measurableEmbedding_const_smul c)
  tfae_have 4 → 5
  | H, c, s => by
    rw [← preimage_smul_inv]
    apply H
  tfae_have 5 → 3 := fun H c s _ => H c s
  tfae_have 3 → 2
  | H, c, s, hs => by
    rw [preimage_smul]
    exact H c⁻¹ s hs
  tfae_finish

/-- Equivalent definitions of a measure invariant under an additive action of a group.

- 0: `VAddInvariantMeasure G α μ`;

- 1: for every `c : G` and a measurable set `s`, the measure of the preimage of `s` under
     vector addition `(c +ᵥ ·)` is equal to the measure of `s`;

- 2: for every `c : G` and a measurable set `s`, the measure of the image `c +ᵥ s` of `s` under
     vector addition `(c +ᵥ ·)` is equal to the measure of `s`;

- 3, 4: properties 2, 3 for any set, including non-measurable ones;

- 5: for any `c : G`, vector addition of `c` maps `μ` to `μ`;

- 6: for any `c : G`, vector addition of `c` is a measure-preserving map. -/
add_decl_doc vaddInvariantMeasure_tfae

variable {G}
variable [SMulInvariantMeasure G α μ]

variable {μ}
variable [MeasurableSpace G] [MeasurableSMul G α] in
@[to_additive]
theorem NullMeasurableSet.smul {s} (hs : NullMeasurableSet s μ) (c : G) :
    NullMeasurableSet (c • s) μ := by
  simpa only [← preimage_smul_inv] using
    hs.preimage (measurePreserving_smul _ _).quasiMeasurePreserving

section IsMinimal

variable (G)
variable [TopologicalSpace α] [ContinuousConstSMul G α] [MulAction.IsMinimal G α] {K U : Set α}

include G in
/-- If measure `μ` is invariant under a group action and is nonzero on a compact set `K`, then it is
positive on any nonempty open set. In case of a regular measure, one can assume `μ ≠ 0` instead of
`μ K ≠ 0`, see `MeasureTheory.measure_isOpen_pos_of_smulInvariant_of_ne_zero`. -/
@[to_additive]
theorem measure_isOpen_pos_of_smulInvariant_of_compact_ne_zero (hK : IsCompact K) (hμK : μ K ≠ 0)
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < μ U :=
  let ⟨t, ht⟩ := hK.exists_finite_cover_smul G hU hne
  pos_iff_ne_zero.2 fun hμU =>
    hμK <|
      measure_mono_null ht <|
        (measure_biUnion_null_iff t.countable_toSet).2 fun _ _ => by rwa [measure_smul]

/-- If measure `μ` is invariant under an additive group action and is nonzero on a compact set `K`,
then it is positive on any nonempty open set. In case of a regular measure, one can assume `μ ≠ 0`
instead of `μ K ≠ 0`, see `MeasureTheory.measure_isOpen_pos_of_vaddInvariant_of_ne_zero`. -/
add_decl_doc measure_isOpen_pos_of_vaddInvariant_of_compact_ne_zero

include G

@[to_additive]
theorem isLocallyFiniteMeasure_of_smulInvariant (hU : IsOpen U) (hne : U.Nonempty) (hμU : μ U ≠ ∞) :
    IsLocallyFiniteMeasure μ :=
  ⟨fun x =>
    let ⟨g, hg⟩ := hU.exists_smul_mem G x hne
    ⟨(g • ·) ⁻¹' U, (hU.preimage (continuous_id.const_smul _)).mem_nhds hg,
      Ne.lt_top <| by rwa [measure_preimage_smul]⟩⟩

variable [Measure.Regular μ]

@[to_additive]
theorem measure_isOpen_pos_of_smulInvariant_of_ne_zero (hμ : μ ≠ 0) (hU : IsOpen U)
    (hne : U.Nonempty) : 0 < μ U :=
  let ⟨_K, hK, hμK⟩ := Regular.exists_isCompact_not_null.mpr hμ
  measure_isOpen_pos_of_smulInvariant_of_compact_ne_zero G hK hμK hU hne

@[to_additive]
theorem measure_pos_iff_nonempty_of_smulInvariant (hμ : μ ≠ 0) (hU : IsOpen U) :
    0 < μ U ↔ U.Nonempty :=
  ⟨fun h => nonempty_of_measure_ne_zero h.ne',
    measure_isOpen_pos_of_smulInvariant_of_ne_zero G hμ hU⟩

@[to_additive]
theorem measure_eq_zero_iff_eq_empty_of_smulInvariant (hμ : μ ≠ 0) (hU : IsOpen U) :
    μ U = 0 ↔ U = ∅ := by
  rw [← not_iff_not, ← Ne, ← pos_iff_ne_zero,
    measure_pos_iff_nonempty_of_smulInvariant G hμ hU, nonempty_iff_ne_empty]

end IsMinimal

end MeasureTheory
