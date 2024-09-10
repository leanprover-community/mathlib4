/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Measure.ContinuousPreimage
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Ergodicity from minimality


-/

open MeasureTheory Filter Set Function
open scoped Pointwise Topology

variable {X : Type*} [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]

@[to_additive]
theorem aeconst_of_dense_setOf_preimage_smul_ae (G : Type*) [SMul G X]
    [TopologicalSpace G] [ContinuousSMul G X]
    {μ : Measure X} [IsFiniteMeasure μ] [μ.InnerRegular] [ErgodicSMul G X μ]
    {s : Set X} (hsm : NullMeasurableSet s μ)
    (hd : Dense {g : G | (g • ·) ⁻¹' s =ᵐ[μ] s}) : EventuallyConst s (ae μ) := by
  borelize G
  refine aeconst_of_forall_preimage_smul_ae_eq G hsm ?_
  rwa [dense_iff_closure_eq, IsClosed.closure_eq, eq_univ_iff_forall] at hd
  let f : C(G × X, X) := ⟨(· • ·).uncurry, continuous_smul⟩
  exact isClosed_setOf_preimage_ae_eq f.curry.continuous (measurePreserving_smul · μ) _ hsm
    (measure_ne_top _ _)

@[to_additive]
theorem aeconst_of_dense_setOf_preimage_smul_eq (G : Type*) [SMul G X]
    [TopologicalSpace G] [ContinuousSMul G X]
    {μ : Measure X} [IsFiniteMeasure μ] [μ.InnerRegular] [ErgodicSMul G X μ]
    {s : Set X} (hsm : NullMeasurableSet s μ)
    (hd : Dense {g : G | (g • ·) ⁻¹' s = s}) : EventuallyConst s (ae μ) :=
  aeconst_of_dense_setOf_preimage_smul_ae G hsm <| hd.mono fun _ h ↦ mem_setOf.2 <| .of_eq h

@[to_additive]
theorem aeconst_of_dense_aestabilizer_smul {G : Type*} [Group G] [MulAction G X]
    [TopologicalSpace G] [ContinuousSMul G X] [ContinuousInv G]
    {μ : Measure X} [IsFiniteMeasure μ] [μ.InnerRegular] [ErgodicSMul G X μ]
    {s : Set X} (hsm : NullMeasurableSet s μ)
    (hd : Dense (MulAction.aestabilizer G μ s : Set G)) : EventuallyConst s (ae μ) :=
  aeconst_of_dense_setOf_preimage_smul_ae G hsm <| (hd.preimage (isOpenMap_inv _)).mono <|
    fun g hg ↦ by simpa only [preimage_smul] using hg

@[to_additive]
theorem ErgodicSMul.trans_isMinimal (M N : Type*) [Monoid M] [MulAction M N]
    [Monoid N] [TopologicalSpace N] [MulAction.IsMinimal M N]
    [MulAction N X] [SMul M X] [IsScalarTower M N X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.InnerRegular] [ContinuousSMul N X] [ErgodicSMul N X μ] :
    ErgodicSMul M X μ where
  measure_preimage_smul c s hsm := by
    simpa only [smul_one_smul] using SMulInvariantMeasure.measure_preimage_smul (c • 1 : N) hsm
  aeconst_of_forall_preimage_smul_ae_eq {s} hsm hs := by
    refine aeconst_of_dense_setOf_preimage_smul_ae N hsm.nullMeasurableSet ?_
    refine (MulAction.dense_orbit M 1).mono ?_
    rintro _ ⟨g, rfl⟩
    simpa using hs g

@[to_additive]
theorem ergodic_smul_of_denseRange_pow {M : Type*} [Monoid M] [TopologicalSpace M]
    [MulAction M X] [ContinuousSMul M X] {g : M} (hg : DenseRange (g ^ · : ℕ → M))
    (μ : Measure X) [IsFiniteMeasure μ] [μ.InnerRegular] [ErgodicSMul M X μ] :
    Ergodic (g • ·) μ := by
  borelize M
  refine ⟨measurePreserving_smul _ _, ⟨fun s hsm hs ↦ ?_⟩⟩
  refine aeconst_of_dense_setOf_preimage_smul_eq M hsm.nullMeasurableSet (hg.mono ?_)
  refine range_subset_iff.2 fun n ↦ ?_
  rw [mem_setOf, ← smul_iterate, preimage_iterate_eq, iterate_fixed hs]

@[to_additive]
theorem ergodic_smul_of_denseRange_zpow {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousInv G] [MulAction G X] [ContinuousSMul G X] {g : G} (hg : DenseRange (g ^ · : ℤ → G))
    (μ : Measure X) [IsFiniteMeasure μ] [μ.InnerRegular] [ErgodicSMul G X μ] :
    Ergodic (g • ·) μ := by
  borelize G
  refine ⟨measurePreserving_smul _ _, ⟨fun s hsm hs ↦ ?_⟩⟩
  refine aeconst_of_dense_aestabilizer_smul hsm.nullMeasurableSet (hg.mono ?_)
  rw [← Subgroup.coe_zpowers, SetLike.coe_subset_coe, ← Subgroup.zpowers_inv, Subgroup.zpowers_le,
    MulAction.mem_aestabilizer, ← preimage_smul, hs]

@[to_additive]
theorem ergodic_mul_left_of_denseRange_pow {G : Type*} [Group G]
    [TopologicalSpace G] [TopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    {g : G} (hg : DenseRange (g ^ · : ℕ → G))
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegular] [μ.IsMulLeftInvariant] :
    Ergodic (g * ·) μ :=
  ergodic_smul_of_denseRange_pow hg μ

@[to_additive]
theorem ergodic_mul_left_of_denseRange_zpow {G : Type*} [Group G]
    [TopologicalSpace G] [TopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    {g : G} (hg : DenseRange (g ^ · : ℤ → G))
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegular] [μ.IsMulLeftInvariant] :
    Ergodic (g * ·) μ :=
  ergodic_smul_of_denseRange_zpow hg μ

@[to_additive]
theorem DenseRange.zpow_of_ergodic_mul_left {G : Type*} [Group G] [TopologicalSpace G]
    [TopologicalGroup G] [MeasurableSpace G] [OpensMeasurableSpace G]
    {μ : Measure G} [μ.IsOpenPosMeasure] [μ.IsMulLeftInvariant] {g : G} (hg : Ergodic (g * ·) μ) :
    DenseRange (g ^ · : ℤ → G) := by
  intro a
  by_contra h
  obtain ⟨V, hV₁, hVo, hV⟩ :
      ∃ V : Set G, 1 ∈ V ∧ IsOpen V ∧ ∀ x ∈ V, ∀ y ∈ V, ∀ m : ℤ, g ^ m ≠ a * x / y := by
    rw [← mem_compl_iff, ← interior_compl, mem_interior_iff_mem_nhds] at h
    have : Tendsto (fun (x, y) ↦ a * x / y) (𝓝 1) (𝓝 a) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    rw [nhds_prod_eq] at this
    simpa [(nhds_basis_opens (1 : G)).prod_self.mem_iff, prod_subset_iff, and_assoc] using this h
  set s := ⋃ m : ℤ, g ^ m • V
  have hso : IsOpen s := isOpen_iUnion fun m ↦ hVo.smul _
  have hsne : s.Nonempty := ⟨1, mem_iUnion.2 ⟨0, by simpa⟩⟩
  have hd : Disjoint s (a • V) := by
    simp_rw [s, disjoint_iUnion_left, disjoint_left]
    rintro m _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    apply hV y hy x hx m
    simp_all
  have hgs : (g * ·) ⁻¹' s = s := by
    simp only [s, preimage_iUnion, ← smul_eq_mul, preimage_smul]
    refine iUnion_congr_of_surjective _ (add_left_surjective (-1)) fun m ↦ ?_
    simp [zpow_add, mul_smul]
  cases hg.measure_self_or_compl_eq_zero hso.measurableSet hgs with
  | inl h => exact hso.measure_ne_zero _ hsne h
  | inr h =>
    refine (hVo.smul a).measure_ne_zero μ (.image _ ⟨1, hV₁⟩) (measure_mono_null ?_ h)
    rwa [disjoint_right] at hd

@[to_additive]
theorem ergodic_mul_left_iff_denseRange_zpow {G : Type*} [Group G]
    [TopologicalSpace G] [TopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    {g : G} (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegular] [μ.IsMulLeftInvariant]
    [μ.IsOpenPosMeasure] : Ergodic (g * ·) μ ↔ DenseRange (g ^ · : ℤ → G) :=
  ⟨.zpow_of_ergodic_mul_left, (ergodic_mul_left_of_denseRange_zpow · μ)⟩

@[to_additive]
theorem MonoidHom.preErgodic_of_dense_iUnion_preimage_one {G : Type*} [Group G] [TopologicalSpace G]
    [TopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [IsFiniteMeasure μ] [μ.InnerRegular] [μ.IsMulLeftInvariant]
    (f : G →* G) (hf : Dense (⋃ n, f^[n] ⁻¹' 1)) : PreErgodic f μ := by
  refine ⟨fun s hsm hs ↦ aeconst_of_dense_setOf_preimage_smul_eq (G := G) hsm.nullMeasurableSet ?_⟩
  refine hf.mono <| iUnion_subset fun n x hx ↦ ?_
  have hsn : f^[n] ⁻¹' s = s := by
    rw [preimage_iterate_eq, iterate_fixed hs]
  rw [mem_preimage, Set.mem_one] at hx
  rw [mem_setOf, ← hsn]
  ext y
  simp [hx]

@[to_additive]
theorem MonoidHom.ergodic_of_dense_iUnion_preimage_one {G : Type*} [Group G] [TopologicalSpace G]
    [TopologicalGroup G] [CompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
    (f : G →* G) (hf : Dense (⋃ n, f^[n] ⁻¹' 1)) (hcont : Continuous f) (hsurj : Surjective f) :
    Ergodic f μ :=
  ⟨f.measurePreserving hcont hsurj rfl, f.preErgodic_of_dense_iUnion_preimage_one hf⟩
