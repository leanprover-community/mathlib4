/-
Copyright (c) 2023 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.NormedSpace.ProdLp

/-!
# `L²` inner product space structure on products of inner product spaces

The `L²` norm on product of two inner product spaces is compatible with an inner product
$$
\langle x, y\rangle = \langle x_1, y_1 \rangle + \langle x_2, y_2 \rangle.
$$
This is recorded in this file as an inner product space instance on `WithLp 2 (E × F)`.
-/

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

open Real ENNReal NNReal

namespace WithLp

section norm_of

variable {α β : Type*}
variable [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]

theorem prod_norm_eq_of_L2 (x : WithLp 2 (α × β)) : ‖x‖ = sqrt (‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2) := by
  rw [prod_norm_eq_of_nat 2 (by norm_cast) _, Real.sqrt_eq_rpow]
  norm_cast

theorem prod_nnnorm_eq_of_L2 (x : WithLp 2 (α × β)) :
    ‖x‖₊ = NNReal.sqrt (‖x.fst‖₊ ^ 2 + ‖x.snd‖₊ ^ 2) :=
  NNReal.eq <| by
    push_cast
    exact prod_norm_eq_of_L2 x

theorem prod_norm_sq_eq_of_L2 (x : WithLp 2 (α × β)) : ‖x‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 := by
  suffices ‖x‖₊ ^ 2 = ‖x.fst‖₊ ^ 2 + ‖x.snd‖₊ ^ 2 by
    simpa only [NNReal.coe_sum] using congr_arg ((↑) : ℝ≥0 → ℝ) this
  rw [prod_nnnorm_eq_of_L2, NNReal.sq_sqrt]

theorem prod_dist_eq_of_L2 (x y : WithLp 2 (α × β)) :
    dist x y = (dist x.fst y.fst ^ 2 + dist x.snd y.snd ^ 2).sqrt := by
  simp_rw [dist_eq_norm, prod_norm_eq_of_L2]
  rfl

theorem prod_nndist_eq_of_L2 (x y : WithLp 2 (α × β)) :
    nndist x y = NNReal.sqrt (nndist x.fst y.fst ^ 2 + nndist x.snd y.snd ^ 2) :=
  NNReal.eq <| by
    push_cast
    exact prod_dist_eq_of_L2 _ _

theorem prod_edist_eq_of_L2 (x y : WithLp 2 (α × β)) :
    edist x y = (edist x.fst y.fst ^ 2 + edist x.snd y.snd ^ 2) ^ (1 / 2 : ℝ) := by
  simp [prod_edist_eq_add]

end norm_of

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
