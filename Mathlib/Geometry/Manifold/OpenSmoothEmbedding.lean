module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Topology.Sets.OpenCover

/-!
# Open smooth embeddings

correspond to open immersions in algebraic geometry

-/

open Topology TopologicalSpace Manifold
open scoped ContDiff

@[expose] public section -- TODO: think about exposing once this code has matured

-- M, N and M₀ are manifolds over (E, H), (E', H') and (F, H'') respectively
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {H'' : Type*} [TopologicalSpace H'']
  {I₀ : ModelWithCorners 𝕜 F H''} {M₀ : Type*} [TopologicalSpace M₀] [ChartedSpace H'' M₀]
  {m n : ℕ∞ω}

variable (I J n) in
def IsOpenSmoothEmbedding (f : M → N) : Prop :=
  ∃ U : Opens N, ∃ φ : Diffeomorph I J M U n, (Subtype.val ∘ φ) = f

namespace IsOpenSmoothEmbedding

variable {f : M → N}

lemma isImmersion (hf : IsOpenSmoothEmbedding I J n f) : IsImmersion I J n f := by
  obtain ⟨U, φ, rfl⟩ := hf
  -- apply post-composition lemma (PRed in #28865); Subtype.val is an immersion,
  -- and φ is an immersion since it's a diffeo (using the inverse function theorem)
  sorry

lemma isSmoothEmbedding (hf : IsOpenSmoothEmbedding I J n f) : IsSmoothEmbedding I J n f := by
  refine ⟨hf.isImmersion, ?_⟩
  obtain ⟨U, φ, rfl⟩ := hf
  rw [Topology.IsEmbedding.of_comp_iff IsEmbedding.subtypeVal]
  exact φ.toHomeomorph.isEmbedding

lemma isOpen_range (hf : IsOpenSmoothEmbedding I J n f) : IsOpen (Set.range f) := by
  obtain ⟨U, φ, rfl⟩ := hf
  simp [U.isOpen]

def range {f : M → N} (_hf : IsOpenSmoothEmbedding I J n f) : Opens N :=
  ⟨Set.range f, _hf.isOpen_range⟩

def of_isSmoothEmbedding_of_isOpen (hf : IsSmoothEmbedding I J n f) (hran : IsOpen (Set.range f)) :
    IsOpenSmoothEmbedding I J n f := by
  use ⟨Set.range f, hran⟩
  -- missing lemma: IsSmoothEmbedding is a diffeo to its range
  sorry

variable [IsManifold I n M] [IsManifold J n N] in -- remove after merging master
lemma contMDiff (hf : IsOpenSmoothEmbedding I J n f) : CMDiff n f := hf.isSmoothEmbedding.contMDiff

def _root_.Diffeomorph.of_le (φ : Diffeomorph I J M N n) (hmn : m ≤ n) :
    Diffeomorph I J M N m where
  toFun := φ
  invFun := φ.symm
  left_inv := φ.left_inv
  right_inv := φ.right_inv
  contMDiff_toFun := φ.contMDiff_toFun.of_le hmn
  contMDiff_invFun := φ.contMDiff_invFun.of_le hmn

@[simp]
lemma _root_.Diffeomorph.of_le_apply (Φ : Diffeomorph I J M N n) (hmn : m ≤ n) (x : M) :
    Φ.of_le hmn x = Φ x := rfl

@[simp]
lemma _root_.Diffeomorph.coe_of_le (Φ : Diffeomorph I J M N n) (hmn : m ≤ n) :
    (Φ.of_le hmn : _ → _) = Φ := rfl

lemma mono_n (hf : IsOpenSmoothEmbedding I J n f) (hmn : m ≤ n) : IsOpenSmoothEmbedding I J m f := by
  choose U φ hφ using hf
  exact ⟨U, φ.of_le hmn, by simp [hφ]⟩

end IsOpenSmoothEmbedding
