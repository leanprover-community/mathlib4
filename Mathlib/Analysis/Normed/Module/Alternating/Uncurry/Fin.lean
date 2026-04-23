/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Curry
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

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

@[expose] public section

open Fin Function

namespace ContinuousAlternatingMap

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
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

set_option backward.privateInPublic true in
private def alternatizeUncurryFinCLM.aux :
    (E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) →ₗ[𝕜] E [⋀^Fin (n + 1)]→ₗ[𝕜] F :=
  AlternatingMap.alternatizeUncurryFinLM ∘ₗ (toAlternatingMapLinear (R := 𝕜)).compRight (S := 𝕜) ∘ₗ
    ContinuousLinearMap.coeLM 𝕜

private lemma alternatizeUncurryFinCLM.aux_apply (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F)
    (v : Fin (n + 1) → E) :
    aux f v = ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • f (v i) (i.removeNth v) := by
  simp [aux, AlternatingMap.alternatizeUncurryFin_apply]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
variable (𝕜 E F) in
/-- `AlternatingMap.alternatizeUncurryFin` as a continuous linear map. -/
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

/-- If `f` is a continuous bilinear map taking values in the space of continuous alternating maps,
then evaluation of the twice uncurried `f` on a tuple of vectors `v`
can be represented as a sum of

$$
f(v_i, v_j; v_0, \dots, \hat{v_i}, \dots, \hat{v_j}, \dots, v_{n+1}) -
f(v_j, v_i; v_0, \dots, \hat{v_i}, \dots, \hat{v_j}, \dots, v_{n+1})
$$

over all `(i j : Fin (n + 2))`, `i < j`, taken with appropriate signs.
Here $\hat{v_i}$ and $\hat{v_j}$ mean that these vectors are removed from the tuple.

We use pairs of `i j : Fin (n + 1)`, `i ≤ j`,
to encode pairs `(i.castSucc : Fin (n + 2), j.succ : Fin (n + 2))`,
so the power of `-1` is off by one compared to the informal texts.

In particular, if `f` is symmetric in the first two arguments,
then the resulting alternating map is zero,
see `alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric` below.
-/
theorem alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_apply
    (f : E →L[𝕜] E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) (v : Fin (n + 2) → E) :
    alternatizeUncurryFin (alternatizeUncurryFinCLM 𝕜 E F ∘L f) v =
      ∑ (i : Fin (n + 1)), ∑ j ≥ i,
        (-1 : ℤ) ^ (i + j : ℕ) •
          (f (v i.castSucc) (v j.succ) (j.removeNth <| i.castSucc.removeNth v) -
            f (v j.succ) (v i.castSucc) (j.removeNth <| i.castSucc.removeNth v)) := by
  simpa [alternatizeUncurryFin_apply, AlternatingMap.alternatizeUncurryFin_apply]
    using AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply
      (R := 𝕜) (M := E) (N := F)
      (f.toLinearMap₁₂.compr₂ (toAlternatingMapLinear (R := 𝕜))) v

/-- If `f` is a symmetric continuous bilinear map
taking values in the space of continuous alternating maps,
then the twice uncurried `f` is zero. -/
theorem alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric
    {f : E →L[𝕜] E →L[𝕜] E [⋀^Fin n]→L[𝕜] F}
    (hf : ∀ x y, f x y = f y x) :
    alternatizeUncurryFin (alternatizeUncurryFinCLM 𝕜 E F ∘L f) = 0 := by
  ext v
  simp [alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_apply, hf]

/-- The derivative of `compContinuousLinearMap` can be represented
in terms of `alternatizeUncurryFinCLM`. -/
theorem fderivCompContinuousLinearMap_eq_alternatizeUncurryFin (f : F [⋀^Fin (n + 1)]→L[𝕜] G)
    (g : E →L[𝕜] F) :
    f.fderivCompContinuousLinearMap g = alternatizeUncurryFinCLM 𝕜 E G ∘L
      ((compContinuousLinearMapCLM g ∘L f.curryLeft).postcomp E) := by
  ext dg v
  have (i j : Fin (n + 1)) :
      i.insertNth (α := fun _ ↦ E →L[𝕜] F) dg (fun _ ↦ g) j (v j) =
        i.insertNth (α := fun _ ↦ F) (dg (v i)) (g ∘ i.removeNth v) j := by
    cases j using i.succAboveCases <;> simp [Fin.removeNth]
  simp [alternatizeUncurryFin_apply, ← Fin.insertNth_removeNth, Fin.removeNth_fun_const,
    ← map_insertNth, this]

/-- `alternatizeUncurryFin` of `fderivCompContinuousLinearMap f g`
composed with a symmetric bilinear map is zero. -/
theorem alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero (f : F [⋀^Fin n]→L[𝕜] G)
    (g : E →L[𝕜] F) {h : E →L[𝕜] E →L[𝕜] F} (hsymm : ∀ x y, h x y = h y x) :
    alternatizeUncurryFin (f.fderivCompContinuousLinearMap g ∘L h) = 0 := by
  cases n with
  | zero =>
    simp [fderivCompContinuousLinearMap_of_isEmpty, ← alternatizeUncurryFinCLM_apply]
  | succ n =>
    rw [fderivCompContinuousLinearMap_eq_alternatizeUncurryFin,
      ContinuousLinearMap.comp_assoc,
      alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric]
    intro x y
    ext v
    simp [hsymm]

end ContinuousAlternatingMap
