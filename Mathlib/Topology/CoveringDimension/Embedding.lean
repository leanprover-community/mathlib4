/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Topology.CoveringDimension.GeneralPosition
public import Mathlib.Topology.CoveringDimension.Euclidean
import Mathlib.Analysis.Convex.PartitionOfUnity
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Topology.Separation.Hausdorff

/-! # Covering dimension and Euclidean embeddings -/

public section

open scoped CoveringDimension

universe u

/-- Continuous maps whose product maps a compact set of pairs off the diagonal form an open set. -/
lemma isOpen_setOf_mapsTo_compl_diagonal
    {X E : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    [TopologicalSpace E] [T2Space E] {K : Set (X × X)} (hK : IsCompact K) :
    IsOpen {f : C(X, E) | Set.MapsTo (Prod.map f f) K (Set.diagonal E)ᶜ} := by
  have hc : Continuous (fun f : C(X, E) ↦ f.prodMap f) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_eval.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
      (continuous_eval.comp (continuous_fst.prodMk continuous_snd.snd))
  exact (ContinuousMap.isOpen_setOfPred_mapsTo hK
    (isClosed_diagonal (X := E)).isOpen_compl).preimage hc

open scoped Classical in
/-- Helper for Theorem 50.4: covering dimension supplies a finite open cover
whose members are small both in the domain and under a prescribed map. -/
private lemma existsFiniteControlledOpenCover
    {X E : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace E]
    {m : ℕ} (hdim : HasCoveringDimensionLE X m) (f : C(X, E))
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ s : Finset (Set X),
      (∀ U ∈ s, IsOpen U) ∧
      (∀ U ∈ s, U.Nonempty) ∧
      (∀ x, ∃ U ∈ s, x ∈ U) ∧
      (∀ x, (s.filter fun U ↦ x ∈ U).card ≤ m + 1) ∧
      (∀ U ∈ s, ∀ x ∈ U, ∀ y ∈ U, dist x y < δ) ∧
      (∀ U ∈ s, ∀ x ∈ U, ∀ y ∈ U, dist (f x) (f y) < η) := by
  classical
  -- The canonical cover controls domain distance and image distance simultaneously.
  let neighborhood : X → Set X := fun x ↦
    Metric.ball x (δ / 2) ∩ f ⁻¹' Metric.ball (f x) (η / 2)
  let 𝒜 : Set (Set X) := Set.range neighborhood
  have h𝒜_open : ∀ U ∈ 𝒜, IsOpen U := by
    rintro U ⟨x, rfl⟩
    exact Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage f.continuous)
  have h𝒜_cover : ⋃₀ 𝒜 = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    rw [Set.mem_sUnion]
    refine ⟨neighborhood x, ⟨x, rfl⟩, ?_⟩
    constructor
    · exact Metric.mem_ball.mpr (by simpa using hδ)
    · exact Metric.mem_ball.mpr (by simpa using hη)
  obtain ⟨ℬ, hℬ_refines, hℬ_open, hℬ_cover, hℬ_order⟩ :=
    (hasCoveringDimensionLE_iff X m).mp hdim 𝒜 h𝒜_open h𝒜_cover
  have hℬ_subcover : Set.univ ⊆ ⋃ U : ℬ, U.1 := by
    simp only [← Set.sUnion_eq_iUnion, hℬ_cover, Set.Subset.rfl]
  obtain ⟨t, ht_cover⟩ := isCompact_univ.elim_finite_subcover
    (fun U : ℬ ↦ U.1) (fun U ↦ hℬ_open U.1 U.2) hℬ_subcover
  let s : Finset (Set X) := (t.filter fun U : ℬ ↦ U.1.Nonempty).image Subtype.val
  have hsℬ : (s : Set (Set X)) ⊆ ℬ := by
    rintro U hU
    obtain ⟨V, _, rfl⟩ := Finset.mem_image.mp hU
    exact V.2
  refine ⟨s, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Every selected member came from the open refinement.
    exact fun U hUs ↦ hℬ_open U (hsℬ hUs)
  · -- Empty members were discarded explicitly.
    intro U hUs
    rw [Finset.mem_image] at hUs
    obtain ⟨V, hVt, rfl⟩ := hUs
    exact (Finset.mem_filter.mp hVt).2
  · -- The retained nonempty members still cover, since the member containing a
    -- given point is automatically nonempty.
    intro x
    obtain ⟨V, hVt, hxV⟩ := Set.mem_iUnion₂.mp (ht_cover (Set.mem_univ x))
    refine ⟨V.1, ?_, hxV⟩
    rw [Finset.mem_image]
    exact ⟨V, Finset.mem_filter.mpr ⟨hVt, ⟨x, hxV⟩⟩, rfl⟩
  · -- Point multiplicity can only decrease when passing to the finite subfamily.
    intro x
    have hsubset : (s.filter (fun U ↦ x ∈ U) : Set (Set X)) ⊆ {U ∈ ℬ | x ∈ U} := by
      intro U hU
      exact ⟨hsℬ (Finset.mem_filter.mp hU).1, (Finset.mem_filter.mp hU).2⟩
    exact_mod_cast (Set.encard_mono hsubset).trans (Set.hasOrderLE_iff.mp hℬ_order x)
  · -- Refinement into one canonical neighborhood gives the domain estimate.
    intro U hUs x hxU y hyU
    obtain ⟨A, ⟨z, rfl⟩, hUA⟩ := hℬ_refines (hsℬ hUs)
    exact Metric.ball_half_subset z (Metric.mem_ball_comm.mp (hUA hyU).1) (hUA hxU).1
  · -- The same refinement estimate in the codomain controls image oscillation.
    intro U hUs x hxU y hyU
    obtain ⟨A, ⟨z, rfl⟩, hUA⟩ := hℬ_refines (hsℬ hUs)
    exact Metric.ball_half_subset (f z) (Metric.mem_ball_comm.mp (hUA hyU).2) (hUA hxU).2

open scoped Classical in
/-- Helper for Theorem 50.4: bounded affine independence of the vertices makes
the associated barycentric map separate points at the controlled scale. -/
private lemma barycentricMap_mapsTo_compl_diagonal
    {X ι E : Type*} [PseudoMetricSpace X] [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : PartitionOfUnity ι X Set.univ) (U : ι → Set X)
    (hρ : ρ.IsSubordinate U) (z : ι → E) (g : C(X, E))
    {m : ℕ} {δ : ℝ}
    (hg : ∀ x, g x = ∑ i, ρ i x • z i)
    (hactive : ∀ x, (Finset.univ.filter fun i ↦ ρ i x ≠ 0).card ≤ m + 1)
    (haff : ∀ t : Finset ι, t.card ≤ 2 * m + 2 →
      AffineIndependent ℝ (fun i : {i // i ∈ t} ↦ z i.1))
    (hdomain : ∀ i, ∀ x ∈ U i, ∀ y ∈ U i, dist x y < δ) :
    Set.MapsTo (Prod.map g g) {p : X × X | δ ≤ dist p.1 p.2} (Set.diagonal E)ᶜ := by
  classical
  rintro ⟨x, y⟩ hxy hgeq
  change g x = g y at hgeq
  let t := (Finset.univ.filter fun i ↦ ρ i x ≠ 0) ∪
    (Finset.univ.filter fun i ↦ ρ i y ≠ 0)
  have htcard : t.card ≤ 2 * m + 2 := by
    calc
      t.card ≤ _ := Finset.card_union_le _ _
      _ ≤ (m + 1) + (m + 1) := Nat.add_le_add (hactive x) (hactive y)
      _ = 2 * m + 2 := by omega
  have hx_support : ∀ i, ρ i x ≠ 0 → i ∈ t := by
    intro i hi
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  have hy_support : ∀ i, ρ i y ≠ 0 → i ∈ t := by
    intro i hi
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  -- Restrict both barycentric expressions to the active union and use affine
  -- independence to identify every coefficient.
  have hsum (a : X) (ha : ∀ i, ρ i a ≠ 0 → i ∈ t) :
      (∑ i : {i // i ∈ t}, ρ i.1 a) = 1 := by
    calc
      (∑ i : {i // i ∈ t}, ρ i.1 a) = ∑ i, ρ i a :=
        Fintype.sum_of_injective Subtype.val Subtype.val_injective _ _
          (by simpa using fun i hi ↦ not_ne_iff.mp (mt (ha i) hi)) (fun _ ↦ rfl)
      _ = 1 := by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ a)
  have hweighted_sum (a : X) (ha : ∀ i, ρ i a ≠ 0 → i ∈ t) :
      (∑ i : {i // i ∈ t}, ρ i.1 a • z i.1) = g a := by
    rw [hg a]
    exact Fintype.sum_of_injective Subtype.val Subtype.val_injective _ _
      (by simpa using fun i hi ↦ by simp [not_ne_iff.mp (mt (ha i) hi)]) (fun _ ↦ rfl)
  have hweighted :
      (∑ i : {i // i ∈ t}, ρ i.1 x • z i.1) =
        ∑ i : {i // i ∈ t}, ρ i.1 y • z i.1 := by
    rw [hweighted_sum x hx_support, hweighted_sum y hy_support, hgeq]
  have hcoeff_on_t : ∀ i : {i // i ∈ t}, ρ i.1 x = ρ i.1 y := by
    intro i
    exact (haff t htcard).eq_of_sum_eq_sum (s := Finset.univ)
      (by rw [hsum x hx_support, hsum y hy_support]) hweighted i (Finset.mem_univ i)
  -- A positive coefficient exists; its cover member contains both points.
  obtain ⟨i, hi⟩ := ρ.exists_pos (Set.mem_univ x)
  have hixU : x ∈ U i := hρ i (subset_tsupport (ρ i) (ne_of_gt hi))
  have hiyU : y ∈ U i := by
    have hiy : ρ i y ≠ 0 := hcoeff_on_t ⟨i, hx_support i (ne_of_gt hi)⟩ ▸ ne_of_gt hi
    exact hρ i (subset_tsupport (ρ i) hiy)
  exact (not_lt_of_ge hxy) (hdomain i x hixU y hiyU)

/-- Helper for Theorem 50.4: on a nonempty compact metric space of covering
dimension at most `m`, reciprocal-scale separating Euclidean maps are dense. -/
lemma dense_setOf_mapsTo_compl_diagonal_of_nonempty
    {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X]
    {m : ℕ} (hdim : HasCoveringDimensionLE X m) (n : ℕ) :
    Dense {f : C(X, EuclideanSpace ℝ (Fin (2 * m + 1))) |
      Set.MapsTo (Prod.map f f) {p : X × X | 1 / (n + 1 : ℝ) ≤ dist p.1 p.2}
        (Set.diagonal (EuclideanSpace ℝ (Fin (2 * m + 1))))ᶜ} := by
  rw [Metric.dense_iff]
  intro f r hr
  have hscale : 0 < 1 / (n + 1 : ℝ) := by positivity
  have hrhalf : 0 < r / 2 := by positivity
  -- First freeze one finite cover controlling both the separation scale and
  -- the image oscillation allowed by the target uniform ball.
  obtain ⟨s, hopen, hnonempty, hcover, hmult, hdomain, himage⟩ :=
    existsFiniteControlledOpenCover hdim f hscale hrhalf
  -- Use the cover-member subtype as the single finite index type for all
  -- subsequent representatives, vertices, and barycentric coefficients.
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun U : s ↦ U.1) (fun U ↦ hopen U.1 U.2)
    (by
      intro x _
      obtain ⟨U, hU, hxU⟩ := hcover x
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩)
  have hactive : ∀ x,
      (Finset.univ.filter fun i ↦ ρ i x ≠ 0).card ≤ m + 1 := by
    classical
    intro x
    refine le_trans (Finset.card_le_card_of_injOn Subtype.val ?_
      Subtype.val_injective.injOn) (hmult x)
    exact fun i hi ↦ Finset.mem_filter.mpr
      ⟨i.2, hρ i (subset_tsupport (ρ i) (Finset.mem_filter.mp hi).2)⟩
  classical
  -- Choose one representative in every nonempty cover member and perturb its
  -- image to the bounded affine-independent vertex family supplied above.
  let a : {U : Set X // U ∈ s} → X := fun i ↦ Classical.choose (hnonempty i.1 i.2)
  have ha_mem : ∀ i, a i ∈ i.1 := fun i ↦ Classical.choose_spec (hnonempty i.1 i.2)
  obtain ⟨z, hz_close, hz_affine⟩ :=
    existsNearbyBoundedAffineIndependentFamily (fun i ↦ f (a i)) hrhalf
  have hz_affine' : ∀ t : Finset {U : Set X // U ∈ s}, t.card ≤ 2 * m + 2 →
      AffineIndependent ℝ (fun i : {i // i ∈ t} ↦ z i.1) := by
    intro t ht
    apply hz_affine t
    omega
  -- Form the finite barycentric sum as a continuous map.
  let g : C(X, EuclideanSpace ℝ (Fin (2 * m + 1))) :=
    ⟨fun x ↦ ∑ i, ρ i x • z i,
      continuous_finsetSum _ fun i _ ↦ (ρ i).continuous.smul continuous_const⟩
  have hg : ∀ x, g x = ∑ i, ρ i x • z i := fun _ ↦ rfl
  -- An active coefficient places `x` in the same controlled cover member as
  -- its representative, so the vertex and `f x` are less than `r` apart.
  have hz_pointwise : ∀ i x, ρ i x ≠ 0 → dist (z i) (f x) < r := by
    intro i x hix
    have hxU : x ∈ i.1 :=
      hρ i (subset_tsupport (ρ i) hix)
    calc
      dist (z i) (f x) ≤ dist (z i) (f (a i)) + dist (f (a i)) (f x) :=
        dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add (hz_close i)
        (himage i.1 i.2 (a i) (ha_mem i) x hxU)
      _ = r := by ring
  refine ⟨g, Metric.mem_ball.mpr ?_, ?_⟩
  · -- The weighted-average estimate gives the required uniform approximation.
    apply ContinuousMap.dist_lt_of_nonempty
    intro x
    rw [hg x]
    simpa only [finsum_eq_sum_of_fintype, Metric.mem_ball] using
      ρ.finsum_smul_mem_convex (g := fun i _ ↦ z i) (Set.mem_univ x)
        (fun i hi ↦ Metric.mem_ball.mpr (hz_pointwise i x hi)) (convex_ball (f x) r)
  · -- Coefficient uniqueness on the union of two active supports gives scale separation.
    exact barycentricMap_mapsTo_compl_diagonal ρ (fun U ↦ U.1) hρ z g hg hactive hz_affine'
      (fun i ↦ hdomain i.1 i.2)

/-- Helper for Theorem 50.4: at every positive reciprocal scale, the separating
continuous maps form an open dense subset of the uniform-metric function space. -/
lemma isOpen_dense_setOf_mapsTo_compl_diagonal
    {X : Type u} [MetricSpace X] [CompactSpace X]
    {m : ℕ} (hdim : HasCoveringDimensionLE X m) (n : ℕ) :
    IsOpen {f : C(X, EuclideanSpace ℝ (Fin (2 * m + 1))) |
      Set.MapsTo (Prod.map f f) {p : X × X | 1 / (n + 1 : ℝ) ≤ dist p.1 p.2}
        (Set.diagonal (EuclideanSpace ℝ (Fin (2 * m + 1))))ᶜ} ∧
    Dense {f : C(X, EuclideanSpace ℝ (Fin (2 * m + 1))) |
      Set.MapsTo (Prod.map f f) {p : X × X | 1 / (n + 1 : ℝ) ≤ dist p.1 p.2}
        (Set.diagonal (EuclideanSpace ℝ (Fin (2 * m + 1))))ᶜ} := by
  -- The pairs at the prescribed scale form a compact set.
  constructor
  · exact isOpen_setOf_mapsTo_compl_diagonal
      (isClosed_le continuous_const continuous_dist).isCompact
  -- Density is vacuous on the empty domain and is the geometric approximation
  -- construction isolated in `dense_setOf_mapsTo_compl_diagonal_of_nonempty` otherwise.
  · cases isEmpty_or_nonempty X with
    | inl hX => simp [Set.MapsTo]
    | inr hX =>
      let _ : Nonempty X := hX
      exact dense_setOf_mapsTo_compl_diagonal_of_nonempty hdim n

/-- A compact metrizable space of covering dimension at most `m` embeds in
`EuclideanSpace ℝ (Fin (2 * m + 1))`. -/
theorem existsEuclideanEmbedding_of_hasCoveringDimensionLE
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace.MetrizableSpace X] {m : ℕ}
    (hdim : HasCoveringDimensionLE X m) :
    ∃ f : X → EuclideanSpace ℝ (Fin (2 * m + 1)), Topology.IsEmbedding f := by
  -- Use a compatible metric once, so compact continuous maps carry the uniform metric.
  let _ : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let separatingMaps : ℕ → Set C(X, EuclideanSpace ℝ (Fin (2 * m + 1))) :=
    fun n ↦ {f | Set.MapsTo (Prod.map f f)
      {p : X × X | 1 / (n + 1 : ℝ) ≤ dist p.1 p.2}
      (Set.diagonal (EuclideanSpace ℝ (Fin (2 * m + 1))))ᶜ}
  have hopen : ∀ n, IsOpen (separatingMaps n) := by
    intro n
    exact (isOpen_dense_setOf_mapsTo_compl_diagonal hdim n).1
  have hdense : ∀ n, Dense (separatingMaps n) := by
    intro n
    exact (isOpen_dense_setOf_mapsTo_compl_diagonal hdim n).2
  -- Baire's theorem supplies one continuous map separating at every reciprocal scale.
  obtain ⟨f, hf⟩ := (BaireSpace.baire_property separatingMaps hopen hdense).nonempty
  have hinj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (dist_pos.mpr hne)
    have hfn := Set.mem_iInter.mp hf n
    exact @hfn (x, y) hn.le hxy
  -- A continuous injection from a compact space to a Hausdorff space is an embedding.
  exact ⟨f, (f.continuous.isClosedEmbedding hinj).isEmbedding⟩

/-- Theorem 50.4. Every compact metrizable space of covering dimension `m` embeds in
`EuclideanSpace ℝ (Fin (2 * m + 1))`. -/
theorem existsEuclideanEmbedding_of_coveringDimension_eq
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace.MetrizableSpace X] (m : ℕ)
    (hdim : dim X = (m : ℕ∞)) :
    ∃ f : X → EuclideanSpace ℝ (Fin (2 * m + 1)), Topology.IsEmbedding f := by
  apply existsEuclideanEmbedding_of_hasCoveringDimensionLE
  rw [← coveringDimension_le_iff]
  exact le_of_eq hdim

/-! ### Finite covering dimension and Euclidean embeddings -/

/-- A compact space embedded in a finite-dimensional real Euclidean space has
finite covering dimension. -/
theorem finiteCoveringDimension_of_euclideanEmbedding
    {X : Type u} [TopologicalSpace X] [CompactSpace X] {N : ℕ}
    {f : X → EuclideanSpace ℝ (Fin N)} (hf : Topology.IsEmbedding f) :
    FiniteCoveringDimension X := by
  -- Bound the compact range by its Euclidean dimension, then transport the bound to `X`.
  rw [finiteCoveringDimension_iff]
  refine ⟨N, hf.toHomeomorph.symm.hasCoveringDimensionLE_of ?_⟩
  exact compactSubset_euclideanSpace_hasCoveringDimensionLE (Set.range f)
    (isCompact_range hf.continuous)

/-- A compact metrizable space of finite covering dimension embeds in some
finite-dimensional real Euclidean space. -/
theorem existsEuclideanEmbedding_of_finiteCoveringDimension
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace.MetrizableSpace X] (hdim : FiniteCoveringDimension X) :
    ∃ (N : ℕ) (f : X → EuclideanSpace ℝ (Fin N)), Topology.IsEmbedding f := by
  rw [finiteCoveringDimension_iff] at hdim
  obtain ⟨m, hm⟩ := hdim
  obtain ⟨f, hf⟩ := existsEuclideanEmbedding_of_hasCoveringDimensionLE hm
  exact ⟨2 * m + 1, f, hf⟩

/-- Corollary 50.9. A compact metrizable space embeds in some finite-dimensional real
Euclidean space if and only if it has finite covering dimension. -/
theorem existsEuclideanEmbedding_iff_finiteCoveringDimension
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace.MetrizableSpace X] :
    (∃ (N : ℕ) (f : X → EuclideanSpace ℝ (Fin N)), Topology.IsEmbedding f) ↔
      FiniteCoveringDimension X := by
  constructor
  · rintro ⟨N, f, hf⟩
    exact finiteCoveringDimension_of_euclideanEmbedding hf
  · exact existsEuclideanEmbedding_of_finiteCoveringDimension
