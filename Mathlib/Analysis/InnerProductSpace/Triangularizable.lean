/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Gordon Hsu
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Orthonormal triangularization

Gram–Schmidt on a `Fin`-indexed basis preserves each initial `Basis.flag` subspace.

## Main results

* `Module.Basis.flag_gramSchmidtOrthonormalBasis_toBasis`
* `Module.End.exists_orthonormalBasis_blockTriangular_toMatrix_finrank`
-/

@[expose] public section

open Set Submodule Module
open scoped InnerProductSpace

namespace InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

private theorem gramSchmidtOrthonormalBasis_toBasis_flag_le [FiniteDimensional 𝕜 E]
    {n : ℕ} (b : Basis (Fin n) 𝕜 E) (k : Fin (n + 1)) :
    (gramSchmidtOrthonormalBasis (Module.finrank_eq_card_basis b) b).toBasis.flag k ≤
      b.flag k := by
  let u := gramSchmidtOrthonormalBasis (Module.finrank_eq_card_basis b) b
  have hu (i : Fin n) : u i = gramSchmidtNormed 𝕜 b i :=
    gramSchmidtOrthonormalBasis_apply _ ((gramSchmidtNormed_linearIndependent
      (𝕜 := 𝕜) b.linearIndependent).ne_zero i)
  rw [Basis.flag_le_iff]
  intro i hi
  change u i ∈ b.flag k
  rw [hu i, gramSchmidtNormed]
  refine Submodule.smul_mem _ _ ?_
  rw [Basis.flag]
  exact span_mono (image_mono fun j hj =>
    lt_of_le_of_lt (Fin.castSucc_le_castSucc_iff.mpr hj) hi)
    (gramSchmidt_mem_span 𝕜 b le_rfl)

private theorem flag_le_gramSchmidtOrthonormalBasis_toBasis_flag [FiniteDimensional 𝕜 E]
    {n : ℕ} (b : Basis (Fin n) 𝕜 E) (k : Fin (n + 1)) :
    b.flag k ≤
      (gramSchmidtOrthonormalBasis (Module.finrank_eq_card_basis b) b).toBasis.flag k := by
  let u := gramSchmidtOrthonormalBasis (Module.finrank_eq_card_basis b) b
  have hu (i : Fin n) : u i = gramSchmidtNormed 𝕜 b i :=
    gramSchmidtOrthonormalBasis_apply _ ((gramSchmidtNormed_linearIndependent
      (𝕜 := 𝕜) b.linearIndependent).ne_zero i)
  rw [Basis.flag_le_iff]
  intro i hi
  rw [Basis.flag]
  have hb : b i ∈ span 𝕜 (gramSchmidtNormed 𝕜 b '' Set.Iic i) := by
    rw [span_gramSchmidtNormed, span_gramSchmidt_Iic]
    exact subset_span ⟨i, by simp, rfl⟩
  refine span_mono (Set.image_subset_iff.2 ?_) hb
  intro j hj
  change gramSchmidtNormed 𝕜 b j ∈ u.toBasis '' {i | i.castSucc < k}
  rw [← hu j]
  exact ⟨j, lt_of_le_of_lt (Fin.castSucc_le_castSucc_iff.mpr hj) hi, rfl⟩

/-- `gramSchmidtOrthonormalBasis` preserves each initial `Basis.flag`. -/
theorem _root_.Module.Basis.flag_gramSchmidtOrthonormalBasis_toBasis [FiniteDimensional 𝕜 E]
    {n : ℕ} (b : Basis (Fin n) 𝕜 E) (k : Fin (n + 1)) :
    (gramSchmidtOrthonormalBasis (Module.finrank_eq_card_basis b) b).toBasis.flag k =
      b.flag k :=
  le_antisymm (gramSchmidtOrthonormalBasis_toBasis_flag_le b k)
    (flag_le_gramSchmidtOrthonormalBasis_toBasis_flag b k)

end InnerProductSpace

namespace Module.End

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {n : ℕ} {f : End 𝕜 E}

/-- An invariant `Basis.flag` admits an orthonormal basis with the same invariant flags. -/
theorem exists_orthonormalBasis_forall_flag_mem_invtSubmodule_of_forall_flag_mem_invtSubmodule
    [FiniteDimensional 𝕜 E] (b : Basis (Fin n) 𝕜 E)
    (hb : ∀ k : Fin (n + 1), b.flag k ∈ f.invtSubmodule) :
    ∃ u : OrthonormalBasis (Fin n) 𝕜 E, ∀ k : Fin (n + 1),
      u.toBasis.flag k ∈ f.invtSubmodule := by
  let u := InnerProductSpace.gramSchmidtOrthonormalBasis (Module.finrank_eq_card_basis b) b
  refine ⟨u, fun k => ?_⟩
  rw [Module.Basis.flag_gramSchmidtOrthonormalBasis_toBasis b k]
  exact hb k

/-- `f` has a block-upper-triangular matrix in some orthonormal `finrank`-indexed basis. -/
theorem exists_orthonormalBasis_blockTriangular_toMatrix_finrank
    [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 E] (f : End 𝕜 E) :
    ∃ u : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E,
      (LinearMap.toMatrix u.toBasis u.toBasis f).BlockTriangular id := by
  obtain ⟨n, b, hb⟩ := exists_basis_forall_flag_mem_invtSubmodule f
  have hn : n = finrank 𝕜 E := by
    simpa [Fintype.card_fin] using (Module.finrank_eq_card_basis b).symm
  subst hn
  obtain ⟨u, hu⟩ :=
    exists_orthonormalBasis_forall_flag_mem_invtSubmodule_of_forall_flag_mem_invtSubmodule b hb
  exact ⟨u, forall_flag_mem_invtSubmodule_iff_blockTriangular_toMatrix.mp hu⟩

end Module.End
