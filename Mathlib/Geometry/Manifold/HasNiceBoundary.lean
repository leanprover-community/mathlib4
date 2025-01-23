/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.InteriorBoundary
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.MFDeriv.Defs

/-!
# Smooth manifolds with nice boundary

Many manifolds "in nature" have nice boundary, which is again a smooth manifold one dimension lower.
The definition `SmoothManifoldWithCorners` does not enforce this, to also include manifolds
with corners. In this file, we define a typeclass `HasNiceBoundary`, for smooth manifolds whose
boundary is again a smooth manifold such that the inclusion $∂M → M` is smooth.
We do *not* demand that `∂M` have dimension one lower than `M`,
nor that `M` be finite-dimensional, for that matter.

We mostly *do not prove* such instances (as this is more work and out of scope).
**TODO** this file has mostly definitions and sorried theorems; it remains to work out the
details and prove this definition is usable.

This file might get merged into `Manifolds/InteriorBoundary` then.

## TODO
* relax the notation of smoothness, and allow any C^n here
* we assume M, M' and M'' are manifolds over the same space `H` with the same model `I`.
Is this truly necessary, or can we allow something weaker? Would e.g. equivalent models suffice?

-/

open scoped Manifold

universe u
-- XXX: should M₀, E₀, H₀ have the same universe?

-- Let M, M' and M'' be smooth manifolds *over the same space* `H`, with *the same* `model `I`.
variable {E E' E'' E''' H H' H'' H''' : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E'']  [NormedSpace ℝ E'']
  [NormedAddCommGroup E'''] [NormedSpace ℝ E''']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H''] [TopologicalSpace H''']

variable {M : Type u} [TopologicalSpace M] [cm : ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ⊤ M]
  {M' : Type u} [TopologicalSpace M'] [cm': ChartedSpace H M'] [IsManifold I ⊤ M']
  {M'' : Type u} [TopologicalSpace M''] [ChartedSpace H M'']
  {I'' : ModelWithCorners ℝ E H} [IsManifold I ⊤ M'']

/-- Let `M` be a `C^k` real manifold, modelled on the pair `(E, H)`.
A smooth manifold has nice boundary if its boundary is a smooth manifold such that the inclusion
`∂M ↪ M` is a smooth embedding.

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
structure BoundaryManifoldData (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) (k : ℕ∞) [IsManifold I k M] where
  /-- TODO! -/
  M₀ : Type u
  /-- TODO! -/
  [topologicalSpaceM: TopologicalSpace M₀]
  /-- The Euclidean space the boundary is modelled on. -/
  {E₀ : Type u}
  /-- TODO! -/
  [normedAddCommGroup : NormedAddCommGroup E₀]
  /-- TODO! -/
  [normedSpace : NormedSpace ℝ E₀]
  /-- The topological space the boundary is a charted space on. -/
  {H₀ : Type u}
  /-- TODO! -/
  [topologicalSpace : TopologicalSpace H₀]
  /-- A chosen charted space structure on `M₀` on `H₀` -/
  [charts : ChartedSpace H₀ M₀]
  /-- A chosen model with corners for the boundary -/
  I₀ : ModelWithCorners ℝ E₀ H₀
  /-- `M₀` is a `C^k` manifold with corners, w.r.t. our chosen model -/
  [smoothManifold : IsManifold I₀ k M₀]
  /-- A `C^k` map from the model manifold into `M`, which is required to be an embedding -/
  f: M₀ → M
  isEmbedding: Topology.IsEmbedding f
  isSmooth: ContMDiff I₀ I k f
  isImmersion: ∀ x, Function.Injective (mfderiv I₀ I f x)
  /-- `f` maps `M₀` to the boundary of `M`. -/
  range_eq_boundary: Set.range f = I.boundary M

-- TODO: deal with universe polymorphism; I'm assuming the same universe for now!

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] {k : ℕ∞}
  {I : ModelWithCorners ℝ E H} [IsManifold I k M]
  {M' : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I k M]
  {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
  {J : ModelWithCorners ℝ E' H'} [IsManifold J ⊤ N]

instance (d : BoundaryManifoldData M I k) : TopologicalSpace d.H₀ := d.topologicalSpace

instance (d : BoundaryManifoldData M I k) : NormedAddCommGroup d.E₀ := d.normedAddCommGroup

instance (d : BoundaryManifoldData M I k) : NormedSpace ℝ d.E₀ := d.normedSpace

instance (d : BoundaryManifoldData M I k) : TopologicalSpace d.M₀ := d.topologicalSpaceM

instance (d : BoundaryManifoldData M I k) : ChartedSpace d.H₀ d.M₀ := d.charts

instance (d : BoundaryManifoldData M I k) : IsManifold d.I₀ k d.M₀ :=
  d.smoothManifold

-- In general, constructing `BoundaryManifoldData` requires deep results: some cases and results
-- we can state already. Boundaryless manifolds have nice boundary, as do products.

variable (M) in
/-- If `M` is boundaryless, its boundary manifold data is easy to construct. -/
-- We can just take the empty manifold, with a vacuously defined map.
def BoundaryManifoldData.of_boundaryless [BoundarylessManifold I M] :
    BoundaryManifoldData M I k where
  M₀ := ULift Empty
  E₀ := E
  H₀ := E
  charts := ChartedSpace.empty E (ULift Empty)
  I₀ := modelWithCornersSelf ℝ E
  f x := (IsEmpty.false x).elim
  isEmbedding := Topology.IsEmbedding.of_subsingleton _
  isSmooth x := (IsEmpty.false x).elim
  isImmersion x := (IsEmpty.false x).elim
  range_eq_boundary := by
    have : I.boundary M = ∅ := by
      rw [ModelWithCorners.Boundaryless.iff_boundary_eq_empty]
      infer_instance
    rw [this]
    simp [Empty.instIsEmpty]

/-- The `n`-dimensional Euclidean half-space (modelled on itself) has nice boundary
(which is an `n-1`-dimensional manifold). -/
noncomputable def BoundaryManifoldData.euclideanHalfSpace_self (n : ℕ) (k : ℕ∞) :
    BoundaryManifoldData (EuclideanHalfSpace (n+1)) (𝓡∂ (n + 1)) k where
  M₀ := EuclideanSpace ℝ (Fin n)
  E₀ := EuclideanSpace ℝ (Fin n)
  H₀ := EuclideanSpace ℝ (Fin n)
  I₀ := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  f x := ⟨fun i ↦ if h: i = 0 then 0 else x (Fin.pred i (by omega)), by simp⟩
  isEmbedding := sorry
  isSmooth := sorry
  isImmersion x := sorry
  range_eq_boundary := sorry

-- TODO: only interesting statement to prove below
@[fun_prop]
lemma Continuous.foo {X : Type*} [TopologicalSpace X] :
    Continuous (fun p ↦ p.1.casesOn (Sum.inl p.2) (Sum.inr p.2) : Bool × X → X ⊕ X) := by
  sorry

def Homeomorph.boolProdEquivSum (X : Type*) [TopologicalSpace X] : Bool × X ≃ₜ X ⊕ X where
  toEquiv := Equiv.boolProdEquivSum X
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def Homeomorph.finTwo : Bool ≃ₜ Fin 2 where
  toEquiv := finTwoEquiv.symm

def Homeomorph.foo {X : Type*} [TopologicalSpace X] : X ⊕ X ≃ₜ X × Fin 2 :=
  letI b := Homeomorph.finTwo.symm.prodCongr (Homeomorph.refl X)
  ((Homeomorph.boolProdEquivSum X).symm.trans b.symm).trans (Homeomorph.prodComm _ _)

-- def Diffeomorph.foo : M ⊕ M ≃ₘ^k⟮I, I⟯ M × Fin 2 := sorry

-- fails to infer a ChartedSpace instance on Fin 2: another time
-- noncomputable def BoundaryManifoldData.Icc (n : ℕ) (k : ℕ∞) :
--     BoundaryManifoldData (Set.Icc (0 : ℝ) 1) (𝓡∂ 1) k where
--   M₀ := Fin 2
--   E₀ := EuclideanSpace ℝ (Fin 0)
--   H₀ := EuclideanSpace ℝ (Fin 0)
--   I₀ := 𝓘(ℝ, EuclideanSpace ℝ (Fin 0))
--   f x := if h : x = 0 then ⊥ else ⊤
--   isEmbedding := sorry -- should follow from the above!
--   isSmooth := sorry
--   range_eq_boundary := sorry

open Set Topology Function

variable {X Y Z W : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [TopologicalSpace W]

-- missing lemma for Topology/Maps/Basic.lean
lemma isClosedEmbedding_iff_continuous_injective_isClosedMap {f : X → Y} :
    IsClosedEmbedding f ↔ Continuous f ∧ Injective f ∧ IsClosedMap f :=
  ⟨fun h => ⟨h.continuous, h.injective, h.isClosedMap⟩, fun h =>
    .of_continuous_injective_isClosedMap h.1 h.2.1 h.2.2⟩

-- missing in Topology/Constructions/Sum.lean

-- is this true?
-- theorem IsClosedMap.sumMap {f : X → Y} {g : Z → W} (hf : IsClosedMap f) (hg : IsClosedMap g) :
--     IsClosedMap (Sum.map f g) := by
--   exact isClosedMap_sum.2 ⟨isClosedMap_inl.comp hf,isClosedMap_inr.comp hg⟩

@[simp]
theorem isClosedMap_sum_elim {f : X → Z} {g : Y → Z} :
    IsClosedMap (Sum.elim f g) ↔ IsClosedMap f ∧ IsClosedMap g := by
  simp only [isClosedMap_sum, Sum.elim_inl, Sum.elim_inr]

theorem IsClosedMap.sum_elim {f : X → Z} {g : Y → Z} (hf : IsClosedMap f) (hg : IsClosedMap g) :
    IsClosedMap (Sum.elim f g) :=
  isClosedMap_sum_elim.2 ⟨hf, hg⟩

lemma IsOpenEmbedding.sum_elim
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Z} {g : Y → Z} (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g)
    (h : Injective (Sum.elim f g)):
    IsOpenEmbedding (Sum.elim f g) := by
  rw [isOpenEmbedding_iff_continuous_injective_isOpenMap] at hf hg ⊢
  obtain ⟨hcont, hinj, hopenEmb⟩ := hf
  obtain ⟨hcont', hinj', hopenEmb'⟩ := hg
  exact ⟨by fun_prop, h, hopenEmb.sum_elim hopenEmb'⟩

lemma IsClosedEmbedding.sum_elim
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Z} {g : Y → Z} (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (h : Injective (Sum.elim f g)) :
    IsClosedEmbedding (Sum.elim f g) := by
  rw [isClosedEmbedding_iff_continuous_injective_isClosedMap] at hf hg ⊢
  obtain ⟨hcont, hinj, hClosedEmb⟩ := hf
  obtain ⟨hcont', hinj', hClosedEmb'⟩ := hg
  exact ⟨by fun_prop, h, hClosedEmb.sum_elim hClosedEmb'⟩

-- missing lemma: mfderiv of Prod.map (know it's smooth)

variable (M I) in
/-- If `M` is boundaryless and `N` has nice boundary, so does `M × N`. -/
def BoundaryManifoldData.prod_of_boundaryless_left [BoundarylessManifold I M]
    (bd : BoundaryManifoldData N J k) : BoundaryManifoldData (M × N) (I.prod J) k where
  M₀ := M × bd.M₀
  E₀ := E × bd.E₀
  H₀ := ModelProd H bd.H₀
  I₀ := I.prod bd.I₀
  f := Prod.map id bd.f
  isEmbedding := IsEmbedding.prodMap IsEmbedding.id bd.isEmbedding
  -- XXX: mathlib naming is inconsistent, prodMap vs prod_map; check if zulip consensus
  isSmooth := ContMDiff.prod_map contMDiff_id bd.isSmooth
  -- add a predicate "IsImmersion", prove some basic API and show Prod.map respects this!
  isImmersion x := sorry -- TODO!
  range_eq_boundary := by
    rw [range_prod_map, ModelWithCorners.boundary_of_boundaryless_left, range_id]
    congr
    exact bd.range_eq_boundary

variable (N J) in
/-- If `M` has nice boundary and `N` is boundaryless, `M × N` has nice boundary. -/
def BoundaryManifoldData.prod_of_boundaryless_right (bd : BoundaryManifoldData M I k)
    [BoundarylessManifold J N] : BoundaryManifoldData (M × N) (I.prod J) k where
  M₀ := bd.M₀ × N
  E₀ := bd.E₀ × E'
  H₀ := ModelProd bd.H₀ H'
  I₀ := bd.I₀.prod J
  f := Prod.map bd.f id
  isEmbedding := IsEmbedding.prodMap bd.isEmbedding IsEmbedding.id
  isSmooth := ContMDiff.prod_map bd.isSmooth contMDiff_id
  isImmersion x := sorry -- TODO!
  range_eq_boundary := by
    rw [range_prod_map, ModelWithCorners.boundary_of_boundaryless_right, range_id]
    congr
    exact bd.range_eq_boundary

-- XXX: are these two lemmas useful?
lemma BoundaryManifoldData.prod_of_boundaryless_left_model
    [BoundarylessManifold I M] (bd : BoundaryManifoldData N J k) :
  (BoundaryManifoldData.prod_of_boundaryless_left M I bd).I₀ = I.prod bd.I₀ := rfl

lemma BoundaryManifoldData.prod_of_boundaryless_right_model
    (bd : BoundaryManifoldData M I k) [BoundarylessManifold J N] :
  (BoundaryManifoldData.prod_of_boundaryless_right N J bd).I₀ = bd.I₀.prod J := rfl

/-- If `M` is an `n`-dimensional `C^k`-manifold modelled on finite-dimensional Euclidean half-space,
its boundary is an `n-1`-manifold.
TODO: this is not strong enough; also need that M has boundary captured by the boundary
(i.e., modelling a boundaryless manifold on the half-space should be excluded)

Proving this requires knowing homology groups of spheres (or similar). -/
-- TODO: also prove that the boundary has dimension one lower
def BoundaryManifoldData.of_Euclidean_halfSpace (n : ℕ) (k : ℕ∞)
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) k M] : BoundaryManifoldData M (𝓡∂ (n + 1)) k := sorry

-- WIP definition; doesn't work yet
-- TODO: need bd and bd' to have the same data E₀ and H₀!
-- def BoundaryManifoldData.sum [Nonempty M] [Nonempty M'] [Nonempty H]
--     (bd : BoundaryManifoldData M I k) (bd' : BoundaryManifoldData M' I k) :
--     BoundaryManifoldData (M ⊕ M) I k where--:= sorry
--   M₀ := bd.M₀ ⊕ bd.M₀
--   E₀ := sorry
--   H₀ := sorry
--   I₀ := sorry -- should be either I₀
--   f := Sum.map bd.f bd'.f
--   isEmbedding := sorry -- should be in mathlib
--   isSmooth := by
--     --have : Nonempty H₀ := sorry
--     sorry -- works, except for nonemptiness apply ContMDiff.sum_map bd.isSmooth bd'.isSmooth
--   isImmersion := sorry
--   range_eq_boundary := sorry -- easy, using boundary_disjointUnion

-- TODO: move to InteriorBoundary
open Fact.Manifold
/-- A product `M × [x,y]` has boundary `M × {x,y}`. -/
lemma boundary_product {x y : ℝ} [Fact (x < y)] [BoundarylessManifold I M] :
    (I.prod (𝓡∂ 1)).boundary (M × (Set.Icc x y)) = Set.prod univ {⊥, ⊤} := by
  have : (𝓡∂ 1).boundary (Icc x y) = {⊥, ⊤} := by rw [boundary_iccChartedSpace]
  rw [I.boundary_of_boundaryless_left, boundary_iccChartedSpace]

variable (k) in
-- FIXME: delete this, in favour of the boundary data instance on Icc and the product
noncomputable def BoundaryManifoldData.prod_Icc [Nonempty H] [Nonempty M]
    [BoundarylessManifold I M] :
    BoundaryManifoldData (M × (Set.Icc (0 : ℝ) 1)) (I.prod (𝓡∂ 1)) k  where
  M₀ := M ⊕ M
  H₀ := H
  E₀ := E
  I₀ := I
  f := Sum.elim (·, ⊥) (·, ⊤)
  isEmbedding := by
    apply IsOpenEmbedding.isEmbedding
    apply (IsOpenEmbedding.of_continuous_injective_isOpenMap)
    · fun_prop
    · intro x y hxy
      -- this is a bit tedious... is there a nicer way?
      by_cases hx: x.isLeft
      · by_cases hy: y.isLeft
        · rw [Sum.eq_left_getLeft_of_isLeft hx, Sum.eq_left_getLeft_of_isLeft hy] at hxy ⊢
          simp only [Sum.elim_inl] at hxy
          have : x.getLeft hx = y.getLeft hy := congrArg Prod.fst hxy
          rw [this] -- xxx: why can't I inline this?
        · exfalso -- The second component is different: this cannot happen.
          replace hy := (Sum.not_isLeft.mp hy)
          rw [Sum.eq_left_getLeft_of_isLeft hx, Sum.eq_right_getRight_of_isRight hy] at hxy
          simp only [Sum.elim_inl, Sum.elim_inr] at hxy
          simp_all [bot_ne_top, congrArg Prod.snd hxy]
      · by_cases hy: y.isLeft
        · exfalso -- The second component is different: this cannot happen.
          replace hx := (Sum.not_isLeft.mp hx)
          rw [Sum.eq_left_getLeft_of_isLeft hy, Sum.eq_right_getRight_of_isRight hx] at hxy
          simp only [Sum.elim_inl, Sum.elim_inr] at hxy
          simp_all [bot_ne_top, congrArg Prod.snd hxy]
        · rw [Sum.eq_right_getRight_of_isRight (Sum.not_isLeft.mp hx),
            Sum.eq_right_getRight_of_isRight ((Sum.not_isLeft.mp hy))] at hxy ⊢
          simp only [Sum.elim_inr] at hxy
          have : x.getRight (Sum.not_isLeft.mp hx) = y.getRight (Sum.not_isLeft.mp hy) :=
            congrArg Prod.fst hxy
          rw [this]
    · apply IsOpenMap.sum_elim
      all_goals sorry -- should be easy!
  isSmooth := by
    -- future: improving the sum_elim result will make this sorry unnecessary
    have : Nonempty (ModelProd H (EuclideanHalfSpace 1)) := by rw [ModelProd]; infer_instance
    exact ContMDiff.sum_elim (contMDiff_id.prod_mk contMDiff_const)
      (contMDiff_id.prod_mk contMDiff_const)
  isImmersion p := by
    by_cases h: p.isLeft
    · let x := p.getLeft h
      rw [Sum.eq_left_getLeft_of_isLeft h]
      -- lemma: f: M → N, g: M' → N and x ∈ M, then
      -- mfderiv I J f x "is" mfderiv I J (Sum.elim f g) (.inl x)
      -- remaining detail: id has injective differential
      have : Injective (mfderiv I (I.prod (𝓡∂ 1)) ((·, ⊥) : M → M × (Set.Icc (0 : ℝ) 1)) x) := by
        -- is essentially id, so should work...
        sorry
      sorry
    · let x := p.getRight (Sum.not_isLeft.mp h)
      rw [Sum.eq_right_getRight_of_isRight (Sum.not_isLeft.mp h)]
      -- same argument as in the other case
      sorry
  range_eq_boundary := by
    simp only [boundary_product, Set.Sum.elim_range, Set.prod, mem_univ, true_and]
    ext x
    rw [mem_setOf]
    constructor
    · rintro (⟨x', hx'⟩ | ⟨x', hx'⟩) <;> rw [← hx'] <;> tauto
    · -- Can this be simplified?
      intro hx
      simp only [mem_insert_iff, mem_singleton_iff] at hx
      obtain (h | h) := hx
      exacts [Or.inl ⟨x.1, by rw [← h]⟩, Or.inr ⟨x.1, by rw [← h]⟩]

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
