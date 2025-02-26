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
    (I : ModelWithCorners ℝ E H) (k : ℕ∞) [IsManifold I k M]
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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {k : ℕ∞}
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
noncomputable def BoundaryManifoldData.euclideanHalfSpace_self (n : ℕ) (k : ℕ∞) :
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

/- The following results are not used, but might be useful for mathlib
def Homeomorph.sumEquivBoolProd (X : Type*) [TopologicalSpace X] : X ⊕ X ≃ₜ Bool × X := by
  apply Homeomorph.homeomorphOfContinuousClosed (Equiv.boolProdEquivSum X).symm
  · show Continuous (Sum.elim (Prod.mk false) (Prod.mk true))
    fun_prop
  · show IsClosedMap (Sum.elim (Prod.mk false) (Prod.mk true))
    exact (isClosedMap_prodMk_left false).sum_elim (isClosedMap_prodMk_left true)

def Homeomorph.finTwo : Bool ≃ₜ Fin 2 where
  toEquiv := finTwoEquiv.symm

def Homeomorph.foo {X : Type*} [TopologicalSpace X] : X ⊕ X ≃ₜ X × Fin 2 :=
  letI b := Homeomorph.finTwo.symm.prodCongr (Homeomorph.refl X)
  ((Homeomorph.sumEquivBoolProd X).trans b.symm).trans (Homeomorph.prodComm _ _)

-- needs merging master, and perhaps further work,
-- until a ChartedSpace instance on M × Fin 2 is found
-- def Diffeomorph.foo : Diffeomorph I I (M ⊕ M) (M × Fin 2) ⊤ := sorry
-/

open Topology

attribute [local instance] ChartedSpace.of_discreteTopology in
attribute [local instance] IsManifold.of_discreteTopology in
noncomputable def BoundaryManifoldData.Icc (k : ℕ∞) :
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

lemma mfderiv_prod_map
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
  -- XXX: mathlib naming is inconsistent, prodMap vs prod_map; check if zulip consensus
  contMDiff := ContMDiff.prod_map contMDiff_id bd.contMDiff
  isImmersion hk x := by
    rw [mfderiv_prod_map mdifferentiableAt_id ((bd.contMDiff x.2).mdifferentiableAt hk)]
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
    rw [mfderiv_prod_map ((bd.contMDiff x.1).mdifferentiableAt hk) mdifferentiableAt_id]
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
def BoundaryManifoldData.of_Euclidean_halfSpace (n : ℕ) (k : ℕ∞)
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) k M] : BoundaryManifoldData M (𝓡∂ (n + 1)) k (𝓡 n):= sorry

-- This lemma (in a nicer phrasing) is proven in a dependent PR:
-- replace with the upstream version once that has landed.
lemma IsEmbedding.sum_elim_of_foo {f : X → Z} {g : Y → Z}
    (hf : IsEmbedding f) (hg : IsEmbedding g) (h : Function.Injective (Sum.elim f g))
    {U V : Set Z} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfU : Set.range f ⊆ U) (hgV : Set.range g ⊆ V) :
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
    -- The boundaries are contained in disjoint open sets, namely M and M' (as subsets of M ⊕ M').
    apply IsEmbedding.sum_elim_of_foo
      (U := Set.range (@Sum.inl M M')) (V := Set.range (@Sum.inr M M'))
    · exact IsEmbedding.inl.comp bd.isEmbedding
    · exact IsEmbedding.inr.comp bd'.isEmbedding
    · -- The overall function is injective: can this be simplified further?
      intro x y hxy
      cases x with
      | inl x' =>
        cases y with
        | inl y' =>
          simp_all
          exact bd.isEmbedding.injective hxy
        | inr y' => simp_all
      | inr x' =>
        cases y with
        | inl y' => simp_all
        | inr y' =>
          simp_all
          exact bd'.isEmbedding.injective hxy
    · exact isOpen_range_inl
    · exact isOpen_range_inr
    · sorry -- exact? inl and inr have disjoint range
    · rw [range_comp]; exact image_subset_range _ _
    · rw [range_comp]; exact image_subset_range _ _
  contMDiff := bd.contMDiff.sum_map bd'.contMDiff
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

-- TODO: move to InteriorBoundary
open Fact.Manifold

variable (k) in
-- FIXME: delete this, in favour of the boundary data instance on Icc and the product
noncomputable def BoundaryManifoldData.prod_Icc [BoundarylessManifold I M] :
    BoundaryManifoldData (M × (Set.Icc (0 : ℝ) 1)) (I.prod (𝓡∂ 1)) k I where
  M₀ := M ⊕ M
  f := Sum.elim (·, ⊥) (·, ⊤)
  isEmbedding := by
    apply IsClosedEmbedding.isEmbedding
    apply (IsClosedEmbedding.of_continuous_injective_isClosedMap)
    · fun_prop
    · intro x y hxy
      -- Can this be simplified further?
      cases x with
      | inl x' =>
        cases y with
        | inl y' => simp_all
        | inr y' => simp_all
      | inr x' =>
        cases y with
        | inl y' => simp_all
        | inr y' => simp_all
    · apply IsClosedMap.sum_elim <;> apply isClosedMap_prodMk_right
  contMDiff := (contMDiff_id.prod_mk contMDiff_const).sum_elim
    (contMDiff_id.prod_mk contMDiff_const)
  isImmersion hk p := by
    cases p with
    | inl x =>
      rw [MDifferentiableAt.mfderiv_prod]
      · sorry -- injectivity
      · -- argue: f coincides with the function which always does the same, then use prod
        have : MDifferentiableAt I (I.prod (𝓡∂ 1)) ((·, ⊥): M → M × (Set.Icc (0 :ℝ) 1)) x :=
          mdifferentiableAt_id.prod_mk mdifferentiableAt_const
        -- actually, want a more general lemma: Sum.elim should be MDifferentiableAt each point
        -- if the individual branches are
        sorry --apply MDifferentiableAt.congr_of_eventuallyEq this
        -- then argue these are EventuallyEq, so we're fine
      -- mfderiv I J f x "is" mfderiv I J (Sum.elim f g) (.inl x)
      have : Function.Injective (mfderiv I (I.prod (𝓡∂ 1))
          ((·, ⊥) : M → M × (Set.Icc (0 : ℝ) 1)) x) := by
        rw [mfderiv_prod_left]
        apply LinearMap.inl_injective
      sorry
    | inr x => sorry -- same argument as in the other case
  range_eq_boundary := by
    simp only [boundary_product, Set.Sum.elim_range, Set.prod, mem_univ, true_and]
    ext x
    sorry
    /- rw [mem_setOf]
    constructor
    · rintro (⟨x', hx'⟩ | ⟨x', hx'⟩) <;> rw [← hx'] <;> tauto
    · -- Can this be simplified?
      intro hx
      simp only [mem_insert_iff, mem_singleton_iff] at hx
      obtain (h | h) := hx
      exacts [Or.inl ⟨x.1, by rw [← h]⟩, Or.inr ⟨x.1, by rw [← h]⟩] -/

#exit

-- Old version of this code; can probably be deleted.

-- TODO: in this definition, E' and H' live in different universes, but only occur together:
-- naively constraining them to the same yields errors later... revisit and fix this!

/-- All data defining a smooth manifold structure on the boundary of a smooth manifold:
a charted space structure on the boundary, a model with corners and a smooth manifold structure.
This need not exist (say, if `M` has corners); if `M` has no boundary or boundary and no corners,
such a structure is in fact canonically induced.
(Proving this requires more advanced results than we currently have.)
-/
structure BoundaryManifoldData (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I ⊤ M] where
  /-- The Euclidean space the boundary is modelled on. -/
  E' : Type u
  [normedAddCommGroup : NormedAddCommGroup E']
  [normedSpace : NormedSpace ℝ E']
  /-- The topological space the boundary is a charted space on. -/
  H' : Type u
  [topologicalSpace : TopologicalSpace H']
  /-- A chosen charted space structure on `I.boundary M` on `H'` -/
  charts : ChartedSpace H' (I.boundary M)
  /-- A chosen model with corners for the boundary -/
  model : ModelWithCorners ℝ E' H'
  /-- `I.boundary M` is a smooth manifold with corners, w.r.t. our chosen model -/
  smoothManifold : IsManifold model ⊤ (I.boundary M)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ⊤ M]
  {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
  {J : ModelWithCorners ℝ E' H'} [IsManifold J ⊤ N]

instance (d : BoundaryManifoldData M I) : TopologicalSpace d.H' := d.topologicalSpace

instance (d : BoundaryManifoldData M I) : NormedAddCommGroup d.E' := d.normedAddCommGroup

instance (d : BoundaryManifoldData M I) : NormedSpace ℝ d.E' := d.normedSpace

instance (d : BoundaryManifoldData M I) : ChartedSpace d.H' (I.boundary M) := d.charts

instance (d : BoundaryManifoldData M I) : IsManifold d.model ⊤ (I.boundary M) :=
  d.smoothManifold

-- In general, constructing `BoundaryManifoldData` requires deep results: some cases and results
-- we can state already. Boundaryless manifolds have nice boundary, as do products.

variable (M) in
/-- If `M` is boundaryless, its boundary manifold data is easy to construct. -/
def BoundaryManifoldData.of_boundaryless [BoundarylessManifold I M] : BoundaryManifoldData M I where
  E' := E
  H' := E
  charts := ChartedSpace.empty E (I.boundary M : Set M)
  model := modelWithCornersSelf ℝ E
  smoothManifold := by
    -- as-is, this errors with "failed to synthesize ChartedSpace E ↑(I.boundary M)" (which is fair)
    -- adding this line errors with "tactic 'apply' failed, failed to assign synthesized instance"
    --haveI := ChartedSpace.empty E (I.boundary M : Set M)
    sorry -- apply SmoothManifoldWithCorners.empty

-- another trivial case: modelWithCornersSelf on euclidean half space!

variable (M I) in
/-- If `M` is boundaryless and `N` has nice boundary, so does `M × N`. -/
def BoundaryManifoldData.prod_of_boundaryless_left [BoundarylessManifold I M]
    (bd : BoundaryManifoldData N J) : BoundaryManifoldData (M × N) (I.prod J) where
  E' := E × bd.E'
  H' := ModelProd H bd.H'
  charts := by
    haveI := bd.charts
    convert prodChartedSpace H M bd.H' (J.boundary N)
    -- TODO: convert between these... mathematically equivalent...
    -- ChartedSpace (ModelProd H bd.H') ↑((I.prod J).boundary (M × N)) =
    --   ChartedSpace (ModelProd H bd.H') (M × ↑(J.boundary N))
    congr
    · -- TODO: this is close, but I want an equivality (or equivalence?) of types here!
      rw [ModelWithCorners.boundary_of_boundaryless_left]
      sorry
    · sorry -- this goal is sketchy!
  model := I.prod bd.model
  smoothManifold := by
    convert IsManifold.prod (n := ⊤) (I := I) (I' := bd.model) M (J.boundary N)
    -- same issue as above
    sorry

-- TODO: fix the details once I found a solution for the above
variable (N J) in
/-- If `M` has nice boundary and `N` is boundaryless, `M × N` has nice boundary. -/
def BoundaryManifoldData.prod_of_boundaryless_right (bd : BoundaryManifoldData M I)
    [BoundarylessManifold J N] : BoundaryManifoldData (M × N) (I.prod J) where
  E' := bd.E' × E'
  H' := ModelProd bd.H' H'
  charts := by
    haveI := bd.charts
    convert prodChartedSpace bd.H' (I.boundary M) H' N
    sorry -- same issue as above
  model := bd.model.prod J
  smoothManifold := sorry -- similar

lemma BoundaryManifoldData.prod_of_boundaryless_right_model
    (bd : BoundaryManifoldData M I) [BoundarylessManifold J N] :
  (BoundaryManifoldData.prod_of_boundaryless_right N J bd).model = bd.model.prod J := rfl

/-- If `M` is modelled on finite-dimensional Euclidean half-space, it has nice boundary.
Proving this requires knowing homology groups of spheres (or similar). -/
-- TODO: also prove that the boundary has dimension one lower
def BoundaryManifoldData.of_Euclidean_halfSpace (n : ℕ) [NeZero n]
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ⊤ M] : BoundaryManifoldData M (𝓡∂ n) :=
  sorry

-- Another example: if E is a half-space in a Banach space, defined by a linear functional,
-- the boundary of B is also nice: this is proven in Roig-Dominguez' textbook

-- TODO: can/should this be HasNiceBoundary M I J instead?
/--  We say a smooth manifold `M` *has nice boundary* if its boundary (as a subspace)
is a smooth manifold such that the inclusion is smooth. (This condition is *not* automatic, for
instance manifolds with corners violate it, but it is satisfied in most cases of interest.

`HasNiceBoundary d` formalises this: the boundary of the manifold `M` modelled on `I`
has a charted space structure and model (included in `d`) which makes it a smooth manifold,
such that the inclusion `∂M → M` is smooth. -/
class HasNiceBoundary (bd : BoundaryManifoldData M I) : Prop where
  /-- The inclusion of `∂M` into `M` is smooth w.r.t. `d`. -/
  smooth_inclusion : ContMDiff bd.model I 1 ((fun ⟨x, _⟩ ↦ x) : (I.boundary M) → M)

/-- A manifold without boundary (trivially) has nice boundary. -/
instance [BoundarylessManifold I M] :
    HasNiceBoundary (BoundaryManifoldData.of_boundaryless (I := I) (M := M)) where
  smooth_inclusion :=
    have : I.boundary M = ∅ := ModelWithCorners.Boundaryless.boundary_eq_empty
    fun p ↦ False.elim (IsEmpty.false p)

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace H'' M']
  {I' : ModelWithCorners ℝ E'' H''} [IsManifold I' ⊤ M']
  {N' : Type u} [TopologicalSpace N'] [ChartedSpace H''' N']
  {J' : ModelWithCorners ℝ E''' H'''} [IsManifold J' ⊤ N']

-- missing lemma in the library...
lemma missing {k : ℕ∞} {f : M → N} {g : M' → N'} (hf : ContMDiff I J k f) (hg : ContMDiff I' J' k g) :
    ContMDiff (I.prod I') (J.prod J') k (fun (x, y) ↦ (f x, g y)) := by
  refine ContMDiff.prod_mk ?hf ?hg
  · sorry -- convert hf should do it, missing API lemma
    -- maybe need to write this as a composition, and argue with a product?
  · sorry

-- missing lemma in mathlib: though I probably won't need it...
variable {f f₁ : M → M'} {n :ℕ } in
theorem contMDiff_congr (h₁ : ∀ y , f₁ y = f y) :
    ContMDiff I I' n f₁ ↔ ContMDiff I I' n f := by
  rw [← contMDiffOn_univ, contMDiffOn_congr (fun y _hy ↦ h₁ y), contMDiffOn_univ]

/-- If `M` has nice boundary and `N` is boundaryless, `M × N` also has nice boundary. -/
instance (bd : BoundaryManifoldData M I) [h : HasNiceBoundary bd] [BoundarylessManifold J N] :
    HasNiceBoundary (BoundaryManifoldData.prod_of_boundaryless_right N J bd) where
  smooth_inclusion := by
    let bd'' := BoundaryManifoldData.prod_of_boundaryless_right N J bd
    let I'' := bd''.model
    have : ContMDiff ((bd.model).prod J) (I.prod J) 1
        (fun (x, y) ↦ (Subtype.val x, y) : (I.boundary M) × N → M × N) :=
      missing h.smooth_inclusion contMDiff_id
    convert this
    rw [BoundaryManifoldData.prod_of_boundaryless_right_model]
    -- TODO: F and G have different domain; need to address this...
    let F : ↑((I.prod J).boundary (M × N)) → M × N := fun x ↦ match x with | ⟨x, property⟩ => x
    let G : ↑(I.boundary M) × N → M × N := fun x ↦ match x with | (x, y) => (↑x, y)
    -- apply contMDiff_congr (I := bd.model.prod J) (I' := I.prod J) (n := 1) (f := F) (f₁ := G)
    sorry

/-- If `M` is boundaryless and `N` has nice boundary, `M × N` also has nice boundary. -/
instance (bd : BoundaryManifoldData N J) [HasNiceBoundary bd] [BoundarylessManifold I M] :
    HasNiceBoundary (BoundaryManifoldData.prod_of_boundaryless_left (M := M) (I := I) bd) where
  smooth_inclusion := sorry
