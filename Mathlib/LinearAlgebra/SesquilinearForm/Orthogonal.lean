/-
Copyright © 2024 Frédéric Marbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Marbach
-/
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.SesquilinearForm

/-!
# Orthogonal complements for bilinear forms

This file establishes properties about orthogonal complements with respect to bilinear forms.

## Implementation notes

- This file is initially a copy-pasted version of results contained in the
`LinearAlgebra.BilinearForm.Orthogonal.lean` file, which where there stated for
`__root__.BilinForm`, to be deprecated. Here, we use the notion of `LinearMap.BilinForm`.

- Many related properties are contained in the `LinearAlgebra.SesquilinearForm.lean` file. However,
the properties stated below involve the notion of `Submodule.dualCoannihilator`, which is defined in
a file already requiring the main file on sesquilinear maps. We therefore extracted these properties
to avoid a dependency cycle.

## Tags

Bilinear form, Orthogonal
-/

namespace LinearMap.BilinForm

variable {V : Type*} {K : Type*} [Field K] [AddCommGroup V] [Module K V]

open Submodule

/-- Given a reflexive bilinear form `B` on `V` and a subspace `W ⊆ V`, the kernel of the restriction
of `B` (viewed as a linear map from `V` to linear forms over `V`) to `W` is `W ⊓ Vᗮ`, as subspaces
of `V`. -/
theorem toLin_restrict_ker_eq_inf_orthogonal (B : LinearMap.BilinForm K V) (W : Subspace K V)
    (b : B.IsRefl) : (B.domRestrict W).ker.map W.subtype = (W ⊓ (orthogonalBilin ⊤ B) : Subspace K V) := by
  ext x; constructor <;> intro hx
  · rcases hx with ⟨⟨x, hx⟩, hker, rfl⟩
    erw [LinearMap.mem_ker] at hker
    constructor
    · simp [hx]
    · intro y _
      rw [LinearMap.IsOrtho, b]
      change (B.domRestrict W) ⟨x, hx⟩ y = 0
      rw [hker]
      rfl
  · simp_rw [mem_map, LinearMap.mem_ker]
    refine' ⟨⟨x, hx.1⟩, _, rfl⟩
    ext y
    change B x y = 0
    rw [b]
    exact hx.2 _ mem_top

/-- Given a reflexive bilinear form `B` on `V` and a subspace `W ⊆ V`, the dual coannihilator of the
restriction of `B` (viewed as a linear map from `V` to linear forms over `V`) to `W` is `Wᗮ`. -/
theorem toLin_restrict_range_dualCoannihilator_eq_orthogonal (B : LinearMap.BilinForm K V)
    (W : Subspace K V) : (B.domRestrict W).range.dualCoannihilator = orthogonalBilin W B := by
  ext x; constructor <;> rw [mem_orthogonalBilin_iff] <;> intro hx
  · intro y hy
    rw [mem_dualCoannihilator] at hx
    exact hx (B.domRestrict W ⟨y, hy⟩) ⟨⟨y, hy⟩, rfl⟩
  · rw [mem_dualCoannihilator]
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    exact hx w hw

variable [FiniteDimensional K V]

open FiniteDimensional

/-- Given a reflexive bilinear form `B` on a vector space `V` of finite dimension, and a subspace
`W ⊆ V`, one has `dim(W) + dim(Wᗮ) = dim(V) + dim(W ⊓ Wᗮ)`. -/
theorem finrank_add_finrank_orthogonal {B : LinearMap.BilinForm K V} {W : Subspace K V} (b₁ : B.IsRefl) :
    finrank K W + finrank K (orthogonalBilin W B) =
      finrank K V + finrank K (W ⊓ (orthogonalBilin ⊤ B) : Subspace K V) := by
  rw [← toLin_restrict_ker_eq_inf_orthogonal _ _ b₁, ←
    toLin_restrict_range_dualCoannihilator_eq_orthogonal _ _, finrank_map_subtype_eq]
  conv_rhs =>
    rw [← @Subspace.finrank_add_finrank_dualCoannihilator_eq K V _ _ _ _
        (LinearMap.range (B.domRestrict W)),
      add_comm, ← add_assoc, add_comm (finrank K (LinearMap.ker (B.domRestrict W))),
      LinearMap.finrank_range_add_finrank_ker]

/-- In a finite dimensional setting, if the restriction of a reflexive bilinear form `B` on `V` to a
subspace `W ⊆ V` is nondegenerate, then `V = W ⊕ Wᗮ`. -/
theorem restrict_nondegenerate_of_isCompl_orthogonal {B : LinearMap.BilinForm K V} {W : Subspace K V}
    (b₁ : B.IsRefl) (b₂ : (restrictBilinear W B).Nondegenerate) : IsCompl W (orthogonalBilin W B) := by
  have : W ⊓ (orthogonalBilin W B) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := Submodule.mem_inf.1 hx
    refine' Subtype.mk_eq_mk.1 (b₂.1 ⟨x, hx₁⟩ _)
    rintro ⟨n, hn⟩
    rw [compl₁₂_apply, b₁]
    exact hx₂ n hn
  refine' IsCompl.of_eq this (Submodule.eq_top_of_finrank_eq <| (Submodule.finrank_le _).antisymm _)
  conv_rhs => rw [← add_zero (FiniteDimensional.finrank K _)]
  rw [← finrank_bot K V, ← this, Submodule.finrank_sup_add_finrank_inf_eq,
    finrank_add_finrank_orthogonal b₁]
  exact le_self_add

end LinearMap.BilinForm
