/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
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

open IsManifold in
lemma OpenPartialHomeomorph.diffeomorph_trans_mem_maximalAtlas [IsManifold I n M]
    (φ : OpenPartialHomeomorph M H) (hφ : φ ∈ maximalAtlas I n M) (Φ : Diffeomorph I I M M n) :
    Φ.toHomeomorph.toOpenPartialHomeomorph.symm.trans φ ∈ maximalAtlas I n M := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · exact (contMDiffOn_of_mem_maximalAtlas hφ).comp Φ.contMDiff_invFun.contMDiffOn (by simp)
  · exact Φ.contMDiff_toFun.contMDiffOn.comp (t := Set.univ)
      ((contMDiffOn_symm_of_mem_maximalAtlas hφ).mono (by simp)) (by simp)

-- TODO: once we have a better characterisation of local diffeomorphisms, replace this proof by
-- "mfderiv% Φ is invertible, hence has a left inverse, thus Φ is an immersion"
lemma Diffeomorph.isImmersionOfComplement [IsManifold I n M] (Φ : Diffeomorph I I M M n) :
    IsImmersionOfComplement Unit I I n Φ := by
  intro x
  let b : OpenPartialHomeomorph M H :=
    Φ.toHomeomorph.toOpenPartialHomeomorph.symm.trans (chartAt H x)
  apply IsImmersionAtOfComplement.mk_of_continuousAt (codChart := b) (equiv := (.prodUnique 𝕜 E _))
    _ _ (mem_chart_source H x) ?_ (IsManifold.chart_mem_maximalAtlas x)
  · simp [b, (chartAt H x).diffeomorph_trans_mem_maximalAtlas
      <| IsManifold.chart_mem_maximalAtlas x]
  · intro y hy
    have : I ((chartAt H x) ((chartAt H x).symm (I.symm y))) = y := by
      rw [(chartAt H x).right_inv (by simp_all), I.right_inv (by simp_all)]
    simpa [b]
  · exact Φ.contMDiff_toFun.continuous.continuousAt
  · simp [b]

lemma Diffeomorph.isSmoothEmbedding [IsManifold I n M] (Φ : Diffeomorph I I M M n) :
    IsSmoothEmbedding I I n Φ :=
  ⟨Φ.isImmersionOfComplement.isImmersion, Φ.toHomeomorph.isEmbedding⟩

namespace IsOpenSmoothEmbedding

variable {f : M → N}

lemma isImmersion (hf : IsOpenSmoothEmbedding I J n f) : IsImmersion I J n f := by
  obtain ⟨U, φ, rfl⟩ := hf
  -- apply post-composition lemma (PRed in #28865); Subtype.val is an immersion,
  -- and φ is an immersion/smooth embedding as above
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
