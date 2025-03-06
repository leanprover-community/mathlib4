/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Smooth manifolds with smooth boundary

Many manifolds coming up in differential geometry or applications have "nice" boundary,
i.e. the boundary is again a (smooth) manifold one dimension lower.
The definition `IsManifold` does not enforce this, in order to also include manifolds
with corners. In this file, we define a typeclass `HasNiceBoundary`, for smooth manifolds whose
boundary is again a smooth manifold such that the inclusion $∂M → M` is smooth.
We do *not* require that `M` or `∂M` be finite-dimensional
(nor that, in the finite case, `∂M` have co-dimension one).

## Main definitions and results

* `BoundaryManifoldData I E₀ H₀ I₀` encodes a smooth manifold `M` modelled on `I` having smooth
  boundary: this is encoded by a pair (M₀, f) of a `C^n` manifold `M₀` modelled on `I₀`
  over the pair `(E₀, H₀)` and a smooth embedding `f: M₀ → M` whose image is precisely `∂M`.

* `BoundaryManifoldData.of_boundaryless`: a boundaryless manifold has smooth boundary
  (namely, any empty type)
* `BoundaryManifoldData.Icc`: a real interval `[x, y]` (for `x < y`) has smooth boundary
* `BoundaryManifoldData.prod_of_boundaryless_left`: if `M` is boundaryless and `N` has smooth
  boundary, so does `M × N`
* `BoundaryManifoldData.prod_of_boundaryless_right`: if `M` has smooth boundary and `N` is
  boundaryless, `M × N` has smooth boundary
* `BoundaryManifoldData.sum`: if `M` and `N` are modelled on the same model `I` and have smooth
  boundary, so does their disjoint union `M ⊕ N`

## TODO
* `BoundaryManifoldData.euclideanHalfSpace_self`: n-dimensional Euclidean half-space has smooth
  boundary (e.g., `n-1`-dimensional Euclidean space)
* if `M` is `n`-dimensional and modelled on Euclidean half-space
  (such that the model is surjective),
  it has smooth boundary: this might require e.g. invariance of domain

-/

open scoped Manifold

-- Let M, M' and M'' be smooth manifolds *over the same space* `H`, with *the same* `model `I`.
variable {E E' E'' E''' H H' H'' H''' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E'']  [NormedSpace ℝ E'']
  [NormedAddCommGroup E'''] [NormedSpace ℝ E''']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H''] [TopologicalSpace H''']

variable {M : Type*} [TopologicalSpace M] [cm : ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ⊤ M]
  {M' : Type*} [TopologicalSpace M'] [cm': ChartedSpace H M'] [IsManifold I ⊤ M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H M'']
  {I'' : ModelWithCorners ℝ E H} [IsManifold I ⊤ M'']

/-- Let `M` be a `C^k` real manifold, modelled on the pair `(E, H)`. We say that `M` has nice
boundary if exist a smooth manifold `N` and a smooth embedding `φ : N ↪ M` with image `∂M`.

`BoundaryManifoldData` is a data-carrying structure which captures this: it consists of a smooth
manifold `N` and a smooth embedding `f : M₀ → M` such that `range f = I.boundary M`.

A priori, we could allow the model spaces `E` and `H` for `N`, as well as the model with corners
on it, to vary freely: for applications in bordism theory, this proves impractical.
To formalise the statement "The manifold `W` has smooth boundary `M \sqcup N`", we could like
to consider the disjoint union of two BoundaryManifoldData: this works best if we fix the model
spaces and model with corners as part of their type.
For this reason, the `ModelWithCorners` (and the underlying pair `(E, H)`)
are part of this structure's parameters.

The first version of this said "I.boundary M is a smooth manifold".
This proved hard to work with, as I.boundary M is a subset, and computing the boundary means
we'd like to rewrite by an equivalence of sets. This runs into DTT, equality of types is bad.

Second version: we prescribe a smooth manifold M₀, and ask for a smooth embedding of M₀ into M,
whose image is the boundary of M. This will allow rewriting the boundary.
A smooth embedding is characterised by having injective differential (being an immersion)
and being a topological embedding.
(Perhaps it's not good enough either, we'll see. Let's try!)

Is a pair `(M₀, f)` of a smooth manifold `M₀` modelled over `(E₀, H₀)` and an embedding
`f : M₀ → M` which is a smooth immersion, such that `range f = I.boundary M`.
-/
structure BoundaryManifoldData.{u} (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) (k : WithTop ℕ∞) [IsManifold I k M]
    {E₀ H₀: Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [TopologicalSpace H₀] (I₀ : ModelWithCorners ℝ E₀ H₀) where
  /-- A `C^k` manifold `M₀` which describes the boundary of `M` -/
  M₀: Type u
  /-- `M₀` is a topological space-/
  [topologicalSpace: TopologicalSpace M₀]
  /-- A chosen charted space structure on `M₀` on `H₀` -/
  [chartedSpace : ChartedSpace H₀ M₀]
  /-- `M₀` is a `C^k` manifold with corners w.r.t. `I₀` -/
  [isManifold : IsManifold I₀ k M₀]
  /-- A `C^k` map from the model manifold into `M`, which is required to be a smooth embedding,
  i.e. a `C^k` immersion which is also a topological embedding -/
  f: M₀ → M
  isEmbedding: Topology.IsEmbedding f
  contMDiff: ContMDiff I₀ I k f
  /-- If `f` is `C¹`, it is an immersion: this condition is vacuous for `C⁰` maps. -/
  isImmersion: (1 : WithTop ℕ∞) ≤ k → ∀ x, Function.Injective (mfderiv I₀ I f x)
  /-- `f` maps `M₀` surjectively to the boundary of `M`. -/
  range_eq_boundary: Set.range f = I.boundary M

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {k : WithTop ℕ∞}
  {I : ModelWithCorners ℝ E H} [IsManifold I k M]
  {E₀ H₀: Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
  [TopologicalSpace H₀] (I₀ : ModelWithCorners ℝ E₀ H₀)
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I k M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {J : ModelWithCorners ℝ E' H'} [IsManifold J k N]

instance (d : BoundaryManifoldData M I k I₀) : TopologicalSpace d.M₀ := d.topologicalSpace

instance (d : BoundaryManifoldData M I k I₀) : ChartedSpace H₀ d.M₀ := d.chartedSpace

instance (d : BoundaryManifoldData M I k I₀) : IsManifold I₀ k d.M₀ := d.isManifold

variable (M) in
/-- If `M` is boundaryless, its boundary manifold data is easy to construct. -/
-- We can just take the empty manifold, with a vacuously defined map.
def BoundaryManifoldData.of_boundaryless [BoundarylessManifold I M] :
    BoundaryManifoldData M I k I where
  M₀ := Empty
  chartedSpace := ChartedSpace.empty _ _
  f x := (IsEmpty.false x).elim
  isEmbedding := Topology.IsEmbedding.of_subsingleton _
  isManifold := by infer_instance
  isImmersion hk x := (IsEmpty.false x).elim
  range_eq_boundary := by
    have : I.boundary M = ∅ := by
      rw [ModelWithCorners.Boundaryless.iff_boundary_eq_empty]
      infer_instance
    rw [this]
    simp [Empty.instIsEmpty]
  contMDiff x := (IsEmpty.false x).elim

-- TODO: fill in these sorries (low priority)
/-- The `n`-dimensional Euclidean half-space (modelled on itself) has nice boundary
(which is an `n-1`-dimensional manifold). -/
noncomputable def BoundaryManifoldData.euclideanHalfSpace_self (n : ℕ) (k : WithTop ℕ∞) :
    BoundaryManifoldData (EuclideanHalfSpace (n+1)) (𝓡∂ (n + 1)) k (𝓡 n) where
  M₀ := EuclideanSpace ℝ (Fin n)
  isManifold := by infer_instance
  f x := ⟨fun i ↦ if h: i = 0 then 0 else x (Fin.pred i (by omega)), by simp⟩
  isEmbedding := sorry
  contMDiff := sorry
  isImmersion hk x := sorry
  range_eq_boundary := sorry

variable {X Y Z W : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [TopologicalSpace W]

open Topology

attribute [local instance] ChartedSpace.of_discreteTopology in
attribute [local instance] IsManifold.of_discreteTopology in
noncomputable def BoundaryManifoldData.Icc (k : WithTop ℕ∞) :
    BoundaryManifoldData (Set.Icc (0 : ℝ) 1) (𝓡∂ 1) k (𝓡 0) where
  M₀ := Fin 2
  f x := if h : x = 0 then ⊥ else ⊤
  isEmbedding := by
    apply IsClosedEmbedding.isEmbedding
    apply IsClosedEmbedding.of_continuous_injective_isClosedMap
      continuous_of_discreteTopology
    · intro x y h
      fin_cases x <;> fin_cases y <;> simp_all
    · exact fun K _ ↦ Set.Finite.isClosed (Finite.Set.finite_image K _)
  contMDiff := contMDiff_of_discreteTopology
  isImmersion hk x := by
    have : Subsingleton (TangentSpace (𝓡 0) x) := by
      change Subsingleton (EuclideanSpace ℝ (Fin 0))
      infer_instance
    exact Function.injective_of_subsingleton _
  range_eq_boundary := by
    rw [boundary_Icc]
    ext x; constructor <;> intro h
    · suffices x = ⊥ ∨ x = ⊤ by simpa
      choose y hy using h
      by_cases y = 0
      exacts [by left; simp_all, by right; simp_all]
    · obtain (hx | hx) := h
      exacts [⟨0, by simp [hx.symm]⟩, ⟨1, by simp [hx.symm]⟩]

-- missing lemma: mfderiv of Prod.map (know it's smooth)
-- mathlib has versions for Prod.mk, also with left and right constant
section PrereqsDiffGeo

variable  {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]

section

variable {E E' F F' : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
variable {H H' H'' H''' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace H''] [TopologicalSpace H''']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 F H''} {J' : ModelWithCorners 𝕜 F' H'''}
variable {M M' N N' : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N] [ChartedSpace H'' N] [TopologicalSpace N'] [ChartedSpace H''' N']
  {f : M → N} {g : M' → N'} {x : M} {x' : M'}

-- #check MDifferentiable.prod_map

lemma mfderiv_prodMap
    (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J' g x') :
    mfderiv (I.prod I') (J.prod J') (Prod.map f g) (x, x')
    = (mfderiv I J f x).prodMap (mfderiv I' J' g x') := sorry

-- and variations for within, etc

end

variable {N' : Type*} [TopologicalSpace N'] [ChartedSpace H' N']

@[simp, mfld_simps]
theorem mfderiv_sumMap_at_inl {f : M → N} (g : M' → N') {p : M} (hf : MDifferentiableAt I J f p) :
    mfderiv I J (Sum.map f g) (Sum.inl p) = mfderiv I J f p := sorry

@[simp, mfld_simps]
theorem mfderiv_sumMap_at_inr (f : M → N) {g : M' → N'} {p : M'} (hg : MDifferentiableAt I J g p) :
    mfderiv I J (Sum.map f g) (Sum.inr p) = mfderiv I J g p := sorry

-- and variations for within, etc

end PrereqsDiffGeo

open Topology Set

variable {I₀} (M I) in
/-- If `M` is boundaryless and `N` has nice boundary, so does `M × N`. -/
def BoundaryManifoldData.prod_of_boundaryless_left [BoundarylessManifold I M]
    (bd : BoundaryManifoldData N J k I₀) :
    BoundaryManifoldData (M × N) (I.prod J) k (I.prod I₀) where
  M₀ := M × bd.M₀
  f := Prod.map id bd.f
  isEmbedding := IsEmbedding.prodMap IsEmbedding.id bd.isEmbedding
  -- XXX: mathlib is currently renaming to prodMap and prodMk; update when that lands
  contMDiff := ContMDiff.prod_map contMDiff_id bd.contMDiff
  isImmersion hk x := by
    rw [mfderiv_prodMap mdifferentiableAt_id ((bd.contMDiff x.2).mdifferentiableAt hk)]
    apply Function.Injective.prodMap
    · rw [mfderiv_id]
      exact fun ⦃a₁ a₂⦄ a ↦ a
    · exact bd.isImmersion hk _
  range_eq_boundary := by
    rw [range_prod_map, ModelWithCorners.boundary_of_boundaryless_left, range_id]
    congr
    exact bd.range_eq_boundary

variable {I₀} (N J) in
/-- If `M` has nice boundary and `N` is boundaryless, `M × N` has nice boundary. -/
def BoundaryManifoldData.prod_of_boundaryless_right (bd : BoundaryManifoldData M I k I₀)
    [BoundarylessManifold J N] : BoundaryManifoldData (M × N) (I.prod J) k (I₀.prod J) where
  M₀ := bd.M₀ × N
  f := Prod.map bd.f id
  isEmbedding := IsEmbedding.prodMap bd.isEmbedding IsEmbedding.id
  contMDiff := ContMDiff.prod_map bd.contMDiff contMDiff_id
  isImmersion hk x := by
    rw [mfderiv_prodMap ((bd.contMDiff x.1).mdifferentiableAt hk) mdifferentiableAt_id]
    apply Function.Injective.prodMap
    · exact bd.isImmersion hk _
    · rw [mfderiv_id]
      exact fun ⦃a₁ a₂⦄ a ↦ a
  range_eq_boundary := by
    rw [range_prod_map, ModelWithCorners.boundary_of_boundaryless_right, range_id]
    congr
    exact bd.range_eq_boundary

/-- If `M` is an `n`-dimensional `C^k`-manifold modelled on finite-dimensional Euclidean half-space,
its boundary is an `n-1`-manifold.
TODO: this statement as-is is false, as its hypotheses are not strong enough; we also need that
M has boundary captured by the boundary of the half-space
(e.g., modelling a boundaryless manifold on the half-space should be excluded)

Proving this requires knowing homology groups of spheres (or similar). -/
def BoundaryManifoldData.of_Euclidean_halfSpace (n : ℕ) (k : WithTop ℕ∞)
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) k M] : BoundaryManifoldData M (𝓡∂ (n + 1)) k (𝓡 n) := sorry

-- Proven in #22137; we will omit the proof here
lemma Topology.IsEmbedding.sumElim_of_separatedNhds {f : X → Z} {g : Y → Z}
    (hf : IsEmbedding f) (hg : IsEmbedding g) (hsep : SeparatedNhds (range f) (range g)) :
    IsEmbedding (Sum.elim f g) := sorry

/-- If `M` and `M'` are modelled on the same model `I` and have nice boundary over `I₀`,
their disjoint union also does. -/
noncomputable def BoundaryManifoldData.sum
    (bd : BoundaryManifoldData M I k I₀) (bd' : BoundaryManifoldData M' I k I₀) :
    BoundaryManifoldData (M ⊕ M') I k I₀ where
  M₀ := bd.M₀ ⊕ bd'.M₀
  isManifold := by infer_instance
  f := Sum.map bd.f bd'.f
  isEmbedding := by
    apply IsEmbedding.sumElim_of_separatedNhds
    · exact IsEmbedding.inl.comp bd.isEmbedding
    · exact IsEmbedding.inr.comp bd'.isEmbedding
    · use Set.range (@Sum.inl M M'), Set.range (@Sum.inr M M')
      refine ⟨isOpen_range_inl, isOpen_range_inr, ?_, ?_, ?_⟩
      · rw [range_comp]; exact image_subset_range _ _
      · rw [range_comp]; exact image_subset_range _ _
      · rw [disjoint_iff]; ext; simp
  contMDiff := bd.contMDiff.sumMap bd'.contMDiff
  isImmersion hk p := by
    cases p with
    | inl x =>
      simp_rw [Sum.map_inl, mfderiv_sumMap_at_inl _ (bd.contMDiff.mdifferentiableAt hk)]
      exact bd.isImmersion hk x
    | inr x =>
      simp_rw [Sum.map_inr, mfderiv_sumMap_at_inr _ (bd'.contMDiff.mdifferentiableAt hk)]
      exact bd'.isImmersion hk x
  range_eq_boundary := by
    rw [Sum.range_eq, ModelWithCorners.boundary_disjointUnion]
    congr
    · have : Sum.map bd.f bd'.f ∘ Sum.inl = (@Sum.inl M M') ∘ bd.f := by
        ext; simp
      rw [this, range_comp, bd.range_eq_boundary]
    · have : Sum.map bd.f bd'.f ∘ Sum.inr = (@Sum.inr M M') ∘ bd'.f := by
        ext; simp
      rw [this, range_comp, bd'.range_eq_boundary]
