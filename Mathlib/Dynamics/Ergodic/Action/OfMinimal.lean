import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Measure.ContinuousPreimage

open MeasureTheory Filter Set

variable {X : Type*} [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]

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

theorem aeconst_of_dense_aestabilizer {G : Type*} [Group G] [MulAction G X]
    [TopologicalSpace G] [ContinuousSMul G X] [ContinuousInv G]
    {μ : Measure X} [IsFiniteMeasure μ] [μ.InnerRegular] [ErgodicSMul G X μ]
    {s : Set X} (hsm : NullMeasurableSet s μ)
    (hd : Dense (MulAction.aestabilizer G μ s : Set G)) : EventuallyConst s (ae μ) :=
  aeconst_of_dense_setOf_preimage_smul_ae G hsm <| (hd.preimage (isOpenMap_inv _)).mono <|
    fun g hg ↦ by simpa only [preimage_smul] using hg

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

theorem ergodic_mul_left_of_denseRange_zpow {G : Type*} [Group G]
    [TopologicalSpace G] [TopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    {g : G} (hg : DenseRange (g ^ · : ℤ → G))
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegular] [μ.IsMulLeftInvariant] :
    Ergodic (g * ·) μ := by
  refine ⟨measurePreserving_mul_left μ g, ⟨fun s hsm hgs ↦ ?_⟩⟩
  have : Subgroup.zpowers g ≤ MulAction.aestabilizer G μ s := by
    rw [← Subgroup.zpowers_inv, Subgroup.zpowers_le, MulAction.mem_aestabilizer, ← preimage_smul]
    simp only [smul_eq_mul, hgs, ae_eq_refl]
  exact eventuallyConst_set'.1 <| aeconst_of_dense_aestabilizer hsm.nullMeasurableSet (hg.mono this)
