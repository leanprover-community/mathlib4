/-
Copyright (c) 2023 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import Mathlib.Analysis.NormedSpace.ProdLp
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# `L²` inner product space structure on products of inner product spaces

The `L²` norm on product of two inner product spaces is compatible with an inner product
$$
\langle x, y\rangle = \langle x_1, y_1 \rangle + \langle x_2, y_2 \rangle.
$$
This is recorded in this file as an inner product space instance on `WithLp 2 (E × F)`.
-/

namespace WithLp

variable {𝕜 : Type*} (E F : Type*)
variable [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F]

noncomputable instance instProdInnerProductSpace :
    InnerProductSpace 𝕜 (WithLp 2 (E × F)) where
  inner x y := inner x.fst y.fst + inner x.snd y.snd
  norm_sq_eq_inner x := by
    simp [prod_norm_sq_eq_of_L2, ← norm_sq_eq_inner]
  conj_symm x y := by
    simp
  add_left x y z := by
    simp only [add_fst, add_snd, inner_add_left]
    ring
  smul_left x y r := by
    simp only [smul_fst, inner_smul_left, smul_snd]
    ring

variable {E F}

@[simp]
theorem prod_inner_apply (x y : WithLp 2 (E × F)) :
    inner (𝕜 := 𝕜) x y = inner x.fst y.fst + inner x.snd y.snd := rfl
