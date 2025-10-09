/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.NormedSpace.Alternating.Curry
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-!
# Uncurrying continuous alternating maps

Given a continuous function `f` which is linear in the first argument
and is alternating form in the other `n` arguments,
this file defines a continuous alternating form `ContinuousAlternatingMap.alternatizeUncurryFin f`
in `n + 1` arguments.

This function is given by
```
ContinuousAlternatingMap.alternatizeUncurryFin f v =
  ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • f (v i) (removeNth i v)
```

Given a continuous alternating map `f` of `n + 1` arguments,
each term in the sum above written for `f.curryLeft` equals the original map,
thus `f.curryLeft.alternatizeUncurryFin = (n + 1) • f`.

We do not multiply the result of `alternatizeUncurryFin` by `(n + 1)⁻¹`
so that the construction works for `𝕜`-multilinear maps over any normed field `𝕜`,
not only a field of characteristic zero.

## Main results

- `ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft`:
  the round-trip formula for currying/uncurrying, see above.

- `ContinuousAlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric`:
  If `f` is a symmetric bilinear map taking values in the space of continuous alternating maps,
  then the twice uncurried `f` is zero.

The latter theorem will be used
to prove that the second exterior derivative of a differential form is zero.
-/

open Fin Function

namespace ContinuousAlternatingMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ}

/-- If `f` is a continuous `(n + 1)`-multilinear alternating map, `x` is an element of the domain,
and `v` is an `n`-vector, then the value of `f` at `v` with `x` inserted at the `p`th place
equals `(-1) ^ p` times the value of `f` at `v` with `x` prepended. -/
theorem map_insertNth (f : E [⋀^Fin (n + 1)]→L[𝕜] F) (p : Fin (n + 1)) (x : E) (v : Fin n → E) :
    f (p.insertNth x v) = (-1) ^ (p : ℕ) • f (Matrix.vecCons x v) :=
  f.toAlternatingMap.map_insertNth p x v

theorem neg_one_pow_smul_map_insertNth (f : E [⋀^Fin (n + 1)]→L[𝕜] F) (p : Fin (n + 1)) (x : E)
    (v : Fin n → E) : (-1) ^ (p : ℕ) • f (p.insertNth x v) = f (Matrix.vecCons x v) :=
  f.toAlternatingMap.neg_one_pow_smul_map_insertNth p x v

/-- Let `v` be an `(n + 1)`-tuple with two equal elements `v i = v j`, `i ≠ j`.
Let `w i` (resp., `w j`) be the vector `v` with `i`th (resp., `j`th) element removed.
Then `(-1) ^ i • f (w i) + (-1) ^ j • f (w j) = 0`.
This follows from the fact that these two vectors differ by a permutation of sign `(-1) ^ (i + j)`.

These are the only two nonzero terms in the proof of `map_eq_zero_of_eq`
in the definition of `AlternatingMap.alternatizeUncurryFin`. -/
theorem neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq (f : E [⋀^Fin n]→L[𝕜] F)
    {v : Fin (n + 1) → E} {i j : Fin (n + 1)} (hvij : v i = v j) (hij : i ≠ j) :
    (-1) ^ (i : ℕ) • f (i.removeNth v) + (-1) ^ (j : ℕ) • f (j.removeNth v) = 0 :=
  f.toAlternatingMap.neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq hvij hij

private def alternatizeUncurryFinCLM.aux :
    (E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) →ₗ[𝕜] E [⋀^Fin (n + 1)]→ₗ[𝕜] F :=
  AlternatingMap.alternatizeUncurryFinLM ∘ₗ (toAlternatingMapLinear (R := 𝕜)).compRight (S := 𝕜) ∘ₗ
    ContinuousLinearMap.coeLM 𝕜

private lemma alternatizeUncurryFinCLM.aux_apply (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F)
    (v : Fin (n + 1) → E) :
    aux f v = ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • f (v i) (i.removeNth v) := by
  simp [aux, AlternatingMap.alternatizeUncurryFin_apply]

variable (𝕜 E F) in
/-- `AlternaringMap.alternatizeUncurryFin` as a continuous linear map. -/
@[irreducible]
noncomputable def alternatizeUncurryFinCLM :
    (E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) →L[𝕜] E [⋀^Fin (n + 1)]→L[𝕜] F :=
  AlternatingMap.mkContinuousLinear alternatizeUncurryFinCLM.aux (n + 1) fun f v ↦ calc
    ‖alternatizeUncurryFinCLM.aux f v‖ ≤ ∑ i : Fin (n + 1), ‖f‖ * ∏ i, ‖v i‖ := by
      rw [alternatizeUncurryFinCLM.aux_apply]
      refine norm_sum_le_of_le _ fun i hi ↦ ?_
      rw [norm_isUnit_zsmul _ (.pow _ isUnit_one.neg), i.prod_univ_succAbove, ← mul_assoc]
      apply (f (v i)).le_of_opNorm_le
      apply f.le_opNorm
    _ = (n + 1) * ‖f‖ * ∏ i, ‖v i‖ := by simp [mul_assoc]

lemma norm_alternatizeUncurryFinCLM_le : ‖alternatizeUncurryFinCLM (n := n) 𝕜 E F‖ ≤ n + 1 := by
  rw [alternatizeUncurryFinCLM]
  apply AlternatingMap.mkContinuousLinear_norm_le
  positivity

/-- Given a continuous function which is linear in the first argument
and is alternating in the other `n` arguments,
build a continuous alternating form in `n + 1` arguments.

The function is given by
```
alternatizeUncurryFin f v = ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • f (v i) (removeNth i v)
```

Note that the round-trip with `curryLeft` multiplies the form by `n + 1`,
since we want to avoid division in this definition. -/
noncomputable def alternatizeUncurryFin (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    E [⋀^Fin (n + 1)]→L[𝕜] F :=
  alternatizeUncurryFinCLM 𝕜 E F f

@[simp]
lemma alternatizeUncurryFinCLM_apply (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    alternatizeUncurryFinCLM 𝕜 E F f = alternatizeUncurryFin f :=
  rfl

lemma norm_alternatizeUncurryFin_le (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    ‖alternatizeUncurryFin f‖ ≤ (n + 1) * ‖f‖ :=
  (alternatizeUncurryFinCLM 𝕜 E F).le_of_opNorm_le norm_alternatizeUncurryFinCLM_le f

theorem alternatizeUncurryFin_apply (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) (v : Fin (n + 1) → E) :
    alternatizeUncurryFin f v = ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • f (v i) (removeNth i v) := by
  rw [alternatizeUncurryFin, alternatizeUncurryFinCLM]
  apply alternatizeUncurryFinCLM.aux_apply

lemma toAlternatingMap_alternatizeUncurryFin (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    (alternatizeUncurryFin f).toAlternatingMap =
      .alternatizeUncurryFin (toAlternatingMapLinear ∘ₗ (f : E →ₗ[𝕜] E [⋀^Fin n]→L[𝕜] F)) := by
  ext
  simp [alternatizeUncurryFin_apply, AlternatingMap.alternatizeUncurryFin_apply]

@[simp]
theorem alternatizeUncurryFin_add (f g : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    alternatizeUncurryFin (f + g) = alternatizeUncurryFin f + alternatizeUncurryFin g :=
  map_add (alternatizeUncurryFinCLM 𝕜 E F) f g

@[simp]
lemma alternatizeUncurryFin_curryLeft (f : E [⋀^Fin (n + 1)]→L[𝕜] F) :
    alternatizeUncurryFin (curryLeft f) = (n + 1) • f := by
  ext v
  simp [alternatizeUncurryFin_apply, ← map_insertNth]

@[simp]
theorem alternatizeUncurryFin_smul {S : Type*} [Monoid S] [DistribMulAction S F]
    [ContinuousConstSMul S F] [SMulCommClass 𝕜 S F] (c : S) (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    alternatizeUncurryFin (c • f) = c • alternatizeUncurryFin f := by
  ext v
  simp [alternatizeUncurryFin_apply, smul_comm _ c, Finset.smul_sum]

theorem alternatizeUncurryFin_constOfIsEmptyLIE_comp (f : E →L[𝕜] F) :
    alternatizeUncurryFin (constOfIsEmptyLIE 𝕜 E F (Fin 0) ∘L f) =
      ofSubsingleton _ _ _ (0 : Fin 1) f := by
  ext
  simp [alternatizeUncurryFin_apply]

/-- If `f` is a symmetric continuous bilinear map
taking values in the space of continuous alternating maps,
then the twice uncurried `f` is zero. -/
theorem alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric
    {f : E →L[𝕜] E →L[𝕜] E [⋀^Fin n]→L[𝕜] F}
    (hf : ∀ x y, f x y = f y x) :
    alternatizeUncurryFin (alternatizeUncurryFinCLM 𝕜 E F ∘L f) = 0 := by
  apply toAlternatingMap_injective
  rw [toAlternatingMap_zero,
    ← AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric
      (f := f.toLinearMap₁₂.compr₂ toAlternatingMapLinear)
      (fun x y ↦ congr($(hf x y) |>.toAlternatingMap))]
  rw [toAlternatingMap_alternatizeUncurryFin]
  congr 1
  ext
  simp [alternatizeUncurryFin_apply, AlternatingMap.alternatizeUncurryFin_apply]

end ContinuousAlternatingMap
