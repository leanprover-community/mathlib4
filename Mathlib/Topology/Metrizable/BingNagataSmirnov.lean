/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Topology.DiscreteFamily
public import Mathlib.Topology.Metrizable.Urysohn

/-!
# The Bing--Nagata--Smirnov metrization theorem

We prove that a regular topological space with a sigma-locally finite basis is pseudometrizable.
Consequently, a T3 space is metrizable if and only if it has a sigma-locally finite basis, or,
equivalently, a sigma-discrete basis.
-/

@[expose] public section

open Filter Metric Set TopologicalSpace Topology
open scoped BoundedContinuousFunction

namespace TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

private theorem hasSeparatingCover_of_sigmaLocallyFiniteBasis_aux [RegularSpace X]
    (b : ℕ → Set (Set X)) (hb : IsTopologicalBasis (⋃ n, b n))
    (hlf : ∀ n, LocallyFinite ((↑) : b n → Set X)) {s t : Set X} (ht : IsClosed t)
    (hst : Disjoint s t) : HasSeparatingCover s t := by
  let c (n : ℕ) := {U : b n // closure (U : Set X) ⊆ tᶜ}
  let u (n : ℕ) := ⋃ U : c n, (U : Set X)
  have hlfc (n : ℕ) : LocallyFinite ((↑) : c n → Set X) :=
    (hlf n).comp_injective Subtype.val_injective
  refine ⟨u, ?_, fun n ↦
    ⟨isOpen_iUnion fun U ↦ hb.isOpen (mem_iUnion_of_mem n U.1.2), ?_⟩⟩
  · intro x hxs
    obtain ⟨U, hUb, hxU, hU⟩ := hb.exists_closure_subset (ht.isOpen_compl.mem_nhds <|
      disjoint_left.1 hst hxs)
    obtain ⟨n, hUbn⟩ := mem_iUnion.1 hUb
    exact mem_iUnion_of_mem n <| mem_iUnion_of_mem ⟨⟨U, hUbn⟩, hU⟩ hxU
  · rw [hlfc n |>.closure_iUnion]
    exact disjoint_iUnion_left.2 fun U ↦ disjoint_left.2 fun _ hx ht ↦ U.2 hx ht

/-- A regular space with a sigma-locally finite basis is normal. -/
theorem NormalSpace.of_sigmaLocallyFiniteBasis [RegularSpace X]
    (b : ℕ → Set (Set X)) (hb : IsTopologicalBasis (⋃ n, b n))
    (hlf : ∀ n, LocallyFinite ((↑) : b n → Set X)) : NormalSpace X where
  normal _s _t hs ht hst := hasSeparatingCovers_iff_separatedNhds.1
    ⟨hasSeparatingCover_of_sigmaLocallyFiniteBasis_aux b hb hlf ht hst,
      hasSeparatingCover_of_sigmaLocallyFiniteBasis_aux b hb hlf hs hst.symm⟩

private abbrev sigmaLocallyFiniteBasisIndex_aux (b : ℕ → Set (Set X)) :=
  Σ p : ℕ × ℕ, b p.1

private instance instTopologicalSpaceSigmaLocallyFiniteBasisIndex_aux
    (b : ℕ → Set (Set X)) : TopologicalSpace (sigmaLocallyFiniteBasisIndex_aux b) := ⊥

private instance instDiscreteTopologySigmaLocallyFiniteBasisIndex_aux
    (b : ℕ → Set (Set X)) : DiscreteTopology (sigmaLocallyFiniteBasisIndex_aux b) :=
  ⟨rfl⟩

private abbrev sigmaLocallyFiniteBasisInnerIndex_aux (b : ℕ → Set (Set X))
    (q : sigmaLocallyFiniteBasisIndex_aux b) :=
  {V : b q.1.2 // closure (V : Set X) ⊆ (q.2 : Set X)}

private def sigmaLocallyFiniteBasisInnerUnion_aux (b : ℕ → Set (Set X))
    (q : sigmaLocallyFiniteBasisIndex_aux b) : Set X :=
  ⋃ V : sigmaLocallyFiniteBasisInnerIndex_aux b q, (V : Set X)

private theorem closure_sigmaLocallyFiniteBasisInnerUnion_subset_aux
    (b : ℕ → Set (Set X)) (hlf : ∀ n, LocallyFinite ((↑) : b n → Set X))
    (q : sigmaLocallyFiniteBasisIndex_aux b) :
    closure (sigmaLocallyFiniteBasisInnerUnion_aux b q) ⊆ (q.2 : Set X) := by
  change closure (⋃ V, (Subtype.val ∘ Subtype.val) V) ⊆ _
  rw [((hlf q.1.2).comp_injective Subtype.val_injective).closure_iUnion]
  exact iUnion_subset fun V ↦ V.2

private def sigmaLocallyFiniteBasisEmbedding_aux (b : ℕ → Set (Set X))
    (f : sigmaLocallyFiniteBasisIndex_aux b → C(X, ℝ))
    (hf : ∀ q x, f q x ∈ Icc (0 : ℝ) 1) :
    X → (sigmaLocallyFiniteBasisIndex_aux b →ᵇ ℝ) := fun x =>
  ⟨⟨fun q ↦ f q x, continuous_of_discreteTopology⟩, 1,
    fun _ _ ↦ Real.dist_le_of_mem_Icc_01 (hf _ _) (hf _ _)⟩

@[simp]
private theorem sigmaLocallyFiniteBasisEmbedding_apply_aux (b : ℕ → Set (Set X))
    (f : sigmaLocallyFiniteBasisIndex_aux b → C(X, ℝ))
    (hf : ∀ q x, f q x ∈ Icc (0 : ℝ) 1) (x : X)
    (q : sigmaLocallyFiniteBasisIndex_aux b) :
    sigmaLocallyFiniteBasisEmbedding_aux b f hf x q = f q x :=
  rfl

private theorem nhds_le_comap_sigmaLocallyFiniteBasisEmbedding_aux
    (b : ℕ → Set (Set X)) (hlf : ∀ n, LocallyFinite ((↑) : b n → Set X))
    {ε : ℕ × ℕ → ℝ} (hε : Tendsto ε cofinite (nhds 0))
    (f : sigmaLocallyFiniteBasisIndex_aux b → C(X, ℝ))
    (hfε : ∀ q, EqOn (f q) (fun _ ↦ ε q.1) (q.2 : Set X)ᶜ)
    (hf0ε : ∀ q x, f q x ∈ Icc 0 (ε q.1)) (hf01 : ∀ q x, f q x ∈ Icc 0 1)
    (x : X) : nhds x ≤ comap (sigmaLocallyFiniteBasisEmbedding_aux b f hf01)
      (nhds (sigmaLocallyFiniteBasisEmbedding_aux b f hf01 x)) := by
  refine (nhds_basis_closedBall.comap _).ge_iff.2 fun δ hδ ↦ ?_
  have hpfin : {p | δ ≤ ε p}.Finite := by
    simpa only [← not_lt] using! hε (gt_mem_nhds hδ)
  have hp (p : ℕ × ℕ) : ∀ᶠ y in nhds x, ∀ U : b p.1,
      dist (f ⟨p, U⟩ y) (f ⟨p, U⟩ x) ≤ δ := by
    rcases hlf p.1 x with ⟨t, htx, htfin⟩
    have hevent : ∀ᶠ y in nhds x, ∀ U : b p.1, ((U : Set X) ∩ t).Nonempty →
        dist (f ⟨p, U⟩ y) (f ⟨p, U⟩ x) ≤ δ := by
      exact (eventually_all_finite htfin).2 fun U _ ↦
        (f ⟨p, U⟩).continuous.tendsto x (closedBall_mem_nhds _ hδ)
    filter_upwards [htx, hevent] with y hyt hy U
    by_cases hU : ((U : Set X) ∩ t).Nonempty
    · exact hy U hU
    · have hyU : y ∉ (U : Set X) := fun hyU ↦ hU ⟨y, hyU, hyt⟩
      have hxU : x ∉ (U : Set X) := fun hxU ↦ hU ⟨x, hxU, mem_of_mem_nhds htx⟩
      simp only [hfε ⟨p, U⟩ hyU, hfε ⟨p, U⟩ hxU, dist_self, hδ.le]
  have hlarge : ∀ᶠ y in nhds x, ∀ p, δ ≤ ε p → ∀ U : b p.1,
      dist (f ⟨p, U⟩ y) (f ⟨p, U⟩ x) ≤ δ :=
    (eventually_all_finite hpfin).2 fun p _ ↦ hp p
  refine hlarge.mono fun y hy ↦ (BoundedContinuousFunction.dist_le hδ.le).2 fun q ↦ ?_
  rcases le_total δ (ε q.1) with hle | hle
  · exact hy q.1 hle q.2
  · exact (Real.dist_le_of_mem_Icc (hf0ε q _) (hf0ε q _)).trans (by simpa using hle)

private theorem comap_sigmaLocallyFiniteBasisEmbedding_le_nhds_aux [RegularSpace X]
    (b : ℕ → Set (Set X)) (hb : IsTopologicalBasis (⋃ n, b n)) {ε : ℕ × ℕ → ℝ}
    (hε0 : ∀ p, 0 < ε p) (f : sigmaLocallyFiniteBasisIndex_aux b → C(X, ℝ))
    (hf0 : ∀ q, EqOn (f q) 0 (closure (sigmaLocallyFiniteBasisInnerUnion_aux b q)))
    (hfε : ∀ q, EqOn (f q) (fun _ ↦ ε q.1) (q.2 : Set X)ᶜ)
    (hf01 : ∀ q x, f q x ∈ Icc 0 1) (x : X) :
    comap (sigmaLocallyFiniteBasisEmbedding_aux b f hf01)
      (nhds (sigmaLocallyFiniteBasisEmbedding_aux b f hf01 x)) ≤ nhds x := by
  refine ((nhds_basis_ball.comap _).le_basis_iff hb.nhds_hasBasis).2 ?_
  rintro V ⟨hVb, hxV⟩
  obtain ⟨U, hUb, hxU, hUV⟩ := hb.exists_closure_subset (hb.mem_nhds hVb hxV)
  obtain ⟨m, hUm⟩ := mem_iUnion.1 hUb
  obtain ⟨W, hWb, hxW, hWU⟩ := hb.exists_closure_subset (hb.mem_nhds hUb hxU)
  obtain ⟨n, hWn⟩ := mem_iUnion.1 hWb
  set q : sigmaLocallyFiniteBasisIndex_aux b := ⟨(m, n), ⟨U, hUm⟩⟩
  have hxa : x ∈ sigmaLocallyFiniteBasisInnerUnion_aux b q :=
    mem_iUnion_of_mem ⟨⟨W, hWn⟩, hWU⟩ hxW
  refine ⟨ε q.1, hε0 q.1, fun y (hy : dist (sigmaLocallyFiniteBasisEmbedding_aux b f hf01 y)
    (sigmaLocallyFiniteBasisEmbedding_aux b f hf01 x) < ε q.1) ↦ ?_⟩
  have hyq : dist (f q y) (f q x) < ε q.1 :=
    (BoundedContinuousFunction.dist_coe_le_dist q).trans_lt hy
  contrapose! hyq
  rw [hfε q (fun hyU ↦ hyq (hUV (subset_closure hyU))),
    hf0 q (subset_closure hxa), Pi.zero_apply, dist_zero_right]
  exact le_abs_self _

private theorem exists_isInducing_of_sigmaLocallyFiniteBasis_aux [RegularSpace X]
    (b : ℕ → Set (Set X)) (hb : IsTopologicalBasis (⋃ n, b n))
    (hlf : ∀ n, LocallyFinite ((↑) : b n → Set X)) :
    ∃ F : X → (sigmaLocallyFiniteBasisIndex_aux b →ᵇ ℝ), IsInducing F := by
  letI : NormalSpace X := .of_sigmaLocallyFiniteBasis b hb hlf
  obtain ⟨ε, ε01, hε⟩ : ∃ ε : ℕ × ℕ → ℝ,
      (∀ p, ε p ∈ Ioc (0 : ℝ) 1) ∧ Tendsto ε cofinite (nhds 0) := by
    rcases posSumOfEncodable zero_lt_one (ℕ × ℕ) with ⟨ε, hε0, C, hεC, hC⟩
    refine ⟨ε, fun p ↦ ⟨hε0 p, ?_⟩, hεC.summable.tendsto_cofinite_zero⟩
    exact (le_hasSum hεC p fun _ _ ↦ (hε0 _).le).trans hC
  have hf : ∀ q : sigmaLocallyFiniteBasisIndex_aux b, ∃ f : C(X, ℝ),
      EqOn f 0 (closure (sigmaLocallyFiniteBasisInnerUnion_aux b q)) ∧
        EqOn f (fun _ ↦ ε q.1) (q.2 : Set X)ᶜ ∧
        ∀ x, f x ∈ Icc 0 (ε q.1) := by
    intro q
    have hd : Disjoint (closure (sigmaLocallyFiniteBasisInnerUnion_aux b q))
        (q.2 : Set X)ᶜ :=
      (closure_sigmaLocallyFiniteBasisInnerUnion_subset_aux b hlf q).disjoint_compl_right
    rcases exists_continuous_zero_one_of_isClosed isClosed_closure
        (hb.isOpen (mem_iUnion_of_mem q.1.1 q.2.2)).isClosed_compl hd with
      ⟨f, hf₀, hf₁, hf01⟩
    exact ⟨ε q.1 • f, fun x hx ↦ by simp [hf₀ hx], fun x hx ↦ by simp [hf₁ hx],
      fun x ↦ ⟨mul_nonneg (ε01 _).1.le (hf01 _).1,
        mul_le_of_le_one_right (ε01 _).1.le (hf01 _).2⟩⟩
  choose f hf0 hfε hf0ε using hf
  have hf01 : ∀ q x, f q x ∈ Icc (0 : ℝ) 1 :=
    fun q x ↦ Icc_subset_Icc_right (ε01 _).2 (hf0ε q x)
  exact ⟨sigmaLocallyFiniteBasisEmbedding_aux b f hf01, isInducing_iff_nhds.2 fun x ↦
    le_antisymm
      (nhds_le_comap_sigmaLocallyFiniteBasisEmbedding_aux b hlf hε f hfε hf0ε hf01 x)
      (comap_sigmaLocallyFiniteBasisEmbedding_le_nhds_aux b hb (fun p ↦ (ε01 p).1)
        f hf0 hfε hf01 x)⟩

/-- A regular space with a sigma-locally finite basis is pseudometrizable. -/
theorem PseudoMetrizableSpace.of_sigmaLocallyFiniteBasis [RegularSpace X]
    (b : ℕ → Set (Set X)) (hb : IsTopologicalBasis (⋃ n, b n))
    (hlf : ∀ n, LocallyFinite ((↑) : b n → Set X)) : PseudoMetrizableSpace X :=
  let ⟨_, hF⟩ := exists_isInducing_of_sigmaLocallyFiniteBasis_aux b hb hlf
  hF.pseudoMetrizableSpace

/-- A regular space with a sigma-discrete basis is pseudometrizable. -/
theorem PseudoMetrizableSpace.of_sigmaDiscreteBasis [RegularSpace X]
    (b : ℕ → Set (Set X)) (hb : IsTopologicalBasis (⋃ n, b n))
    (hdisc : ∀ n, DiscreteFamily ((↑) : b n → Set X)) : PseudoMetrizableSpace X :=
  .of_sigmaLocallyFiniteBasis b hb fun n ↦ (hdisc n).locallyFinite

/-- A T3 space with a sigma-locally finite basis is metrizable. -/
theorem MetrizableSpace.of_sigmaLocallyFiniteBasis [T3Space X]
    (b : ℕ → Set (Set X)) (hb : IsTopologicalBasis (⋃ n, b n))
    (hlf : ∀ n, LocallyFinite ((↑) : b n → Set X)) : MetrizableSpace X := by
  letI : PseudoMetrizableSpace X := .of_sigmaLocallyFiniteBasis b hb hlf
  infer_instance

/-- A T3 space with a sigma-discrete basis is metrizable. -/
theorem MetrizableSpace.of_sigmaDiscreteBasis [T3Space X]
    (b : ℕ → Set (Set X)) (hb : IsTopologicalBasis (⋃ n, b n))
    (hdisc : ∀ n, DiscreteFamily ((↑) : b n → Set X)) : MetrizableSpace X :=
  .of_sigmaLocallyFiniteBasis b hb fun n ↦ (hdisc n).locallyFinite

/-- The pseudometrizable version of the Bing--Nagata--Smirnov metrization theorem. -/
theorem pseudoMetrizableSpace_iff_exists_sigmaLocallyFiniteBasis :
    PseudoMetrizableSpace X ↔ RegularSpace X ∧
      ∃ b : ℕ → Set (Set X), IsTopologicalBasis (⋃ n, b n) ∧
        ∀ n, LocallyFinite ((↑) : b n → Set X) := by
  constructor
  · intro h
    letI := h
    obtain ⟨b, hb, hdisc⟩ := exists_isTopologicalBasis_sigmaDiscrete (X := X)
    exact ⟨inferInstance, b, hb, fun n ↦ (hdisc n).locallyFinite⟩
  · rintro ⟨hreg, b, hb, hlf⟩
    letI := hreg
    exact .of_sigmaLocallyFiniteBasis b hb hlf

/-- A space is pseudometrizable if and only if it is regular and has a sigma-discrete basis. -/
theorem pseudoMetrizableSpace_iff_exists_sigmaDiscreteBasis :
    PseudoMetrizableSpace X ↔ RegularSpace X ∧
      ∃ b : ℕ → Set (Set X), IsTopologicalBasis (⋃ n, b n) ∧
        ∀ n, DiscreteFamily ((↑) : b n → Set X) := by
  constructor
  · intro h
    letI := h
    exact ⟨inferInstance, exists_isTopologicalBasis_sigmaDiscrete (X := X)⟩
  · rintro ⟨hreg, b, hb, hdisc⟩
    letI := hreg
    exact .of_sigmaDiscreteBasis b hb hdisc

/-- The Bing--Nagata--Smirnov metrization theorem, in terms of sigma-locally finite bases. -/
theorem metrizableSpace_iff_exists_sigmaLocallyFiniteBasis :
    MetrizableSpace X ↔ T3Space X ∧
      ∃ b : ℕ → Set (Set X), IsTopologicalBasis (⋃ n, b n) ∧
        ∀ n, LocallyFinite ((↑) : b n → Set X) := by
  constructor
  · intro h
    letI := h
    obtain ⟨b, hb, hdisc⟩ := exists_isTopologicalBasis_sigmaDiscrete (X := X)
    exact ⟨inferInstance, b, hb, fun n ↦ (hdisc n).locallyFinite⟩
  · rintro ⟨ht3, b, hb, hlf⟩
    letI := ht3
    exact .of_sigmaLocallyFiniteBasis b hb hlf

/-- The Bing--Nagata--Smirnov metrization theorem, in terms of sigma-discrete bases. -/
theorem metrizableSpace_iff_exists_sigmaDiscreteBasis :
    MetrizableSpace X ↔ T3Space X ∧
      ∃ b : ℕ → Set (Set X), IsTopologicalBasis (⋃ n, b n) ∧
        ∀ n, DiscreteFamily ((↑) : b n → Set X) := by
  constructor
  · intro h
    letI := h
    exact ⟨inferInstance, exists_isTopologicalBasis_sigmaDiscrete (X := X)⟩
  · rintro ⟨ht3, b, hb, hdisc⟩
    letI := ht3
    exact .of_sigmaDiscreteBasis b hb hdisc

end TopologicalSpace
