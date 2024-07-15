/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Util.Superscript

/-!
# Unoriented bordism theory

In this file, we sketch the beginnings of unoriented bordism theory.
This is not ready for mathlib yet (as we still need the instance that the boundary
of a manifold is a manifold again, might might need some hypotheses to be true).
-/

open scoped Manifold
open Metric (sphere)
open FiniteDimensional

-- Some preliminaries, which should go in more basic files
section ClosedManifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners 𝕜 E H) [SmoothManifoldWithCorners I M]

/-- A topological manifold is called **closed** iff it is compact without boundary. -/
structure ClosedManifold [CompactSpace M] [I.Boundaryless]

/-- An **n-manifold** is a smooth `n`-dimensional manifold. -/
-- xxx: does this mention all data? is there a nicer way to do this?
structure NManifold (n : ℕ) [NormedAddCommGroup E]  [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {H : Type*} [TopologicalSpace H] (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners 𝕜 E H) [SmoothManifoldWithCorners I M] where
  hdim : finrank 𝕜 E = n

structure ClosedNManifold (n : ℕ) [CompactSpace M] [I.Boundaryless] [FiniteDimensional 𝕜 E]
    extends ClosedManifold M I where
  hdim : finrank 𝕜 E = n

end ClosedManifold

-- Let M, M' and W be smooth manifolds.
variable {E E' E'' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [NormedAddCommGroup E'']  [NormedSpace ℝ E'']
  {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']

/-- A **singular `n`-manifold** on a topological space `X` consists of a
closed smooth `n`-manifold `M` and a continuous map `f : M → X`. -/
structure SingularNManifold (X : Type*) [TopologicalSpace X] (n : ℕ)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [SmoothManifoldWithCorners I M]
    [CompactSpace M] [I.Boundaryless] [FiniteDimensional ℝ E] extends ClosedNManifold M I n where
  f : M → X
  hf : Continuous f

-- Declare afterwards, so I can fix the argument order above.
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {I' : ModelWithCorners ℝ E' H'} [SmoothManifoldWithCorners I' M'] {n : ℕ}
  [I.Boundaryless] [CompactSpace M] [FiniteDimensional ℝ E]

/-- If `M` is `n`-dimensional and closed, it is a singular `n`-manifold over itself. -/
noncomputable def SingularNManifold.refl (hdim : finrank ℝ E = n) : SingularNManifold M n M I where
  hdim := hdim
  f := id
  hf := continuous_id

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
-- functoriality: pre-step towards functoriality of the bordism groups
-- xxx: good name?
noncomputable def SingularNManifold.map (s : SingularNManifold X n M I)
    {φ : X → Y} (hφ : Continuous φ) : SingularNManifold Y n M I where
  hdim := s.hdim
  f := φ ∘ s.f
  hf := hφ.comp s.hf

-- lemma SingularNManifold.map_refl (s : SingularNManifold X n M I) :
--   (s.map (continuous_id)).f = s.refl s.hdim := sorry

lemma SingularNManifold.map_comp (s : SingularNManifold X n M I)
    {φ : X → Y} {ψ : Y → Z} (hφ : Continuous φ) (hψ : Continuous ψ):
    ((s.map hφ).map hψ).f = (s.map (hψ.comp hφ)).f := rfl
-- is this all I need to show functoriality?
-- -- xxx: good name? is functorial...
-- noncomputable def SingularNManifold.map_comp (s : SingularNManifold X n M I)
--     {φ : X → Y} {ψ : Y → Z} (hφ : Continuous φ) (hψ : Continuous ψ): SingularNManifold Z n M I where
--   hdim := s.hdim
--   f := (ψ ∘ φ) ∘ f
--   hf := sorry

variable [CompactSpace M'] [I'.Boundaryless] [FiniteDimensional ℝ E']

/-- An **unoriented cobordism** between two singular `n`-manifolds (M,f) and (N,g) on `X`
is a compact smooth `n`-manifold `W` with a continuous map `F: W→ X` whose boundary is diffeomorphic
to the disjoint union M ⊔ N such that F restricts to f resp. g in the obvious way. -/
structure UnorientedCobordism (s : SingularNManifold X n M I) (t : SingularNManifold X n M' I')
    (W : Type*) [TopologicalSpace W] [ChartedSpace H'' W]
    (J : ModelWithCorners ℝ E'' H'') [SmoothManifoldWithCorners J W] where
  hW : CompactSpace W
  hW' : finrank E'' = n + 1
  F : W → X
  hF : Continuous F
  -- φ : Diffeomorph (Boundary W) J-induced (disUnion) I.disjUnion I'
  -- hFf : F.restrict ... = s.f
  -- hFg : F.restrict (N) = t.f

open Set

instance : ChartedSpace (EuclideanHalfSpace 1) (Set.Icc 0 1) := by
  sorry -- apply IccManifold 0 1 almost does it!

-- instance : ChartedSpace (EuclideanHalfSpace (n + 1)) (M × (Set.Icc 0 1)) := sorry

instance Icc_smooth_manifold2 : SmoothManifoldWithCorners (𝓡∂ 1) (Icc 0 1) := by
  sorry -- apply Icc_smooth_manifold 0 1 errors with
  /- tactic 'apply' failed, failed to unify
  SmoothManifoldWithCorners (modelWithCornersEuclideanHalfSpace 1) ↑(Icc (@OfNat.ofNat ℝ 0 Zero.toOfNat0) 1)
with
  SmoothManifoldWithCorners (modelWithCornersEuclideanHalfSpace 1) ↑(Icc (@OfNat.ofNat ℕ 0 (instOfNatNat 0)) 1) -/

/-- Each singular `n`-manifold (M,f)` is cobordant to itself. -/
noncomputable def UnorientedCobordism.refl (s : SingularNManifold X n M I) :
    UnorientedCobordism s s (M × (Set.Icc 0 1)) (I.prod (𝓡∂ 1)) where
  hW := by infer_instance
  hW' := by sorry
    -- calc finrank (E × EuclideanSpace ℝ (Fin 1))
    --   _ = finrank E + (finrank (EuclideanSpace ℝ (Fin 1))) := sorry
    --   _ = n + (finrank (EuclideanSpace ℝ (Fin 1))) := sorry
    --   _ = n + 1 := sorry
      --let s := finrank_prod (R := ℝ) (M := E) (M' := EuclideanSpace ℝ (Fin 1))
    --rw [s]
    --sorry--apply? -- is n+1-dimensional
  F := s.f ∘ (fun p ↦ p.1)
  hF := s.hf.comp continuous_fst

variable (s : SingularNManifold X n M I) (t : SingularNManifold X n M' I')
  {W : Type*} [TopologicalSpace W] [ChartedSpace H'' W]
  {J : ModelWithCorners ℝ E'' H''} [SmoothManifoldWithCorners J W] {n : ℕ}

/-- Being cobordant is symmetric. -/
noncomputable def UnorientedCobordism.symm (φ : UnorientedCobordism s t W J) :
    UnorientedCobordism t s W J where
  hW := φ.hW
  hW' := φ.hW'
  F := φ.F
  hF := φ.hF
  -- TODO: boundary stuff...

-- next one: transitivity... will omit for now: really depends on boundary material,
-- and the collar neighbourhood theorem, which I don't want to formalise for now

-- how to encode this in Lean?
-- Two singular `n`-manifolds are cobordant iff there exists a smooth cobordism between them.
-- The unoriented `n`-bordism group `Ω_n^O(X)` of `X` is the set of all equivalence classes
-- of singular n-manifolds up to bordism.
-- then: functor between these...
