module

public import Mathlib.Geometry.Manifold.ContMDiff.Basic -- Constructions
public import Mathlib.Geometry.Manifold.OpenSmoothEmbedding

public section

open Set Function Filter ChartedSpace

open scoped Topology Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a charted space `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  -- declare a charted space `M'` over the pair `(E', H')`.
  {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  -- declare a charted space `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  -- declare a charted space `N'` over the pair `(F', G')`.
  {F' : Type*}
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type*} [TopologicalSpace G']
  {J' : ModelWithCorners 𝕜 F' G'} {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  -- declare a few vector spaces
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  -- declare functions, sets, points and smoothness indices
  {f : M → M'} {s : Set M} {x : M} {n : WithTop ℕ∞}

-- open immersions
open scoped ContDiff
open Manifold

/-- `Sum.inl` is an open smooth embedding -/
lemma OpenSmoothEmbedding.sumInl [IsManifold I n M] :
    IsOpenSmoothEmbedding I I n (@Sum.inl M M) :=
  IsOpenSmoothEmbedding.of_isSmoothEmbedding_of_isOpen IsSmoothEmbedding.sumInl isOpen_range_inl

-- alternative proof: TODO golf mathlib this way
-- (requires moving the disjoint union material around!)
lemma ContMDiff.inl' [IsManifold I n M] : ContMDiff I I n (@Sum.inl M M) :=
  IsImmersion.sumInl.contMDiff

#check contMDiff_of_contMDiffOn_iUnion_of_isOpen

-- goal: give a nicer, more conceptual proof of this lemma

--lemma ContMDiff.sumElim' {f : M → N} {g : M' → N}
--    (hf : ContMDiff I J n f) (hg : ContMDiff I J n g) : ContMDiff I J n (Sum.elim f g) := by
--  sorry
