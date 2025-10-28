/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fin.Parity

/-!
# Uncurrying alternating maps

Given a function `f` which is linear in the first argument
and is alternating form in the other `n` arguments,
this file defines an alternating form `AlternatingMap.alternatizeUncurryFin f` in `n + 1` arguments.

This function is given by
```
AlternatingMap.alternatizeUncurryFin f v =
  ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • f (v i) (removeNth i v)
```

Given an alternating map `f` of `n + 1` arguments,
each term in the sum above written for `f.curryLeft` equals the original map,
thus `f.curryLeft.alternatizeUncurryFin = (n + 1) • f`.

We do not multiply the result of `alternatizeUncurryFin` by `(n + 1)⁻¹`
so that the construction works for `R`-multilinear maps over any commutative ring `R`,
not only a field of characteristic zero.

## Main results

- `AlternatingMap.alternatizeUncurryFin_curryLeft`:
  the round-trip formula for currying/uncurrying, see above.

- `AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric`:
  If `f` is a symmetric bilinear map taking values in the space of alternating maps,
  then the twice uncurried `f` is zero.

A version of the latter theorem for continuous alternating maps
will be used to prove that the second exterior derivative of a differential form is zero.
-/

open Fin Function

namespace AlternatingMap

variable {R : Type*} {M M₂ N N₂ : Type*} [CommRing R] [AddCommGroup M]
  [AddCommGroup M₂] [AddCommGroup N] [AddCommGroup N₂] [Module R M] [Module R M₂]
  [Module R N] [Module R N₂] {n : ℕ}

/-- If `f` is a `(n + 1)`-multilinear alternating map, `x` is an element of the domain,
and `v` is an `n`-vector, then the value of `f` at `v` with `x` inserted at the `p`th place
equals `(-1) ^ p` times the value of `f` at `v` with `x` prepended. -/
theorem map_insertNth (f : M [⋀^Fin (n + 1)]→ₗ[R] N) (p : Fin (n + 1)) (x : M) (v : Fin n → M) :
    f (p.insertNth x v) = (-1) ^ (p : ℕ) • f (Matrix.vecCons x v) := by
  rw [← cons_comp_cycleRange, map_perm, Matrix.vecCons]
  simp [Units.smul_def]

theorem neg_one_pow_smul_map_insertNth (f : M [⋀^Fin (n + 1)]→ₗ[R] N) (p : Fin (n + 1)) (x : M)
    (v : Fin n → M) :
    (-1) ^ (p : ℕ) • f (p.insertNth x v) = f (Matrix.vecCons x v) := by
  rw [map_insertNth, smul_smul, ← pow_add, Even.neg_one_pow, one_smul]
  use p

/-- Let `v` be an `(n + 1)`-tuple with two equal elements `v i = v j`, `i ≠ j`.
Let `w i` (resp., `w j`) be the vector `v` with `i`th (resp., `j`th) element removed.
Then `(-1) ^ i • f (w i) + (-1) ^ j • f (w j) = 0`.
This follows from the fact that these two vectors differ by a permutation of sign `(-1) ^ (i + j)`.

These are the only two nonzero terms in the proof of `map_eq_zero_of_eq`
in the definition of `alternatizeUncurryFin` below. -/
theorem neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq (f : M [⋀^Fin n]→ₗ[R] N)
    {v : Fin (n + 1) → M} {i j : Fin (n + 1)} (hvij : v i = v j) (hij : i ≠ j) :
    (-1) ^ (i : ℕ) • f (i.removeNth v) + (-1) ^ (j : ℕ) • f (j.removeNth v) = 0 := by
  rcases exists_succAbove_eq hij with ⟨i, rfl⟩
  obtain ⟨m, rfl⟩ : ∃ m, m + 1 = n := by simp [i.pos]
  rw [← (i.predAbove j).insertNth_self_removeNth (removeNth _ _), ← removeNth_removeNth_eq_swap,
    removeNth, succAbove_succAbove_predAbove, map_insertNth, ← neg_one_pow_smul_map_insertNth,
    insertNth_removeNth, update_eq_self_iff.2, smul_smul, ← pow_add,
    neg_one_pow_succAbove_add_predAbove, neg_smul, pow_add, mul_smul,
    smul_smul (_ ^ i.val), ← sq, ← pow_mul, pow_mul', neg_one_pow_two, one_pow, one_smul,
    neg_add_cancel]
  exact hvij.symm

/-- Given a function which is linear in the first argument
and is alternating in the other `n` arguments,
build an alternating form in `n + 1` arguments.

The function is given by
```
alternatizeUncurryFin f v = ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • f (v i) (removeNth i v)
```

Note that the round-trip with `curryFin` multiplies the form by `n + 1`,
since we want to avoid division in this definition. -/
def alternatizeUncurryFin (f : M →ₗ[R] M [⋀^Fin n]→ₗ[R] N) :
    M [⋀^Fin (n + 1)]→ₗ[R] N where
  toMultilinearMap :=
    ∑ p : Fin (n + 1), (-1) ^ (p : ℕ) • LinearMap.uncurryMid p (toMultilinearMapLM ∘ₗ f)
  map_eq_zero_of_eq' := by
    intro v i j hvij hij
    suffices ∑ k : Fin (n + 1), (-1) ^ (k : ℕ) • f (v k) (k.removeNth v) = 0 by simpa
    calc
      _ = (-1) ^ (i : ℕ) • f (v i) (i.removeNth v) + (-1) ^ (j : ℕ) • f (v j) (j.removeNth v) := by
        refine Fintype.sum_eq_add _ _ hij fun k ⟨hki, hkj⟩ ↦ ?_
        rcases exists_succAbove_eq hki.symm with ⟨i, rfl⟩
        rcases exists_succAbove_eq hkj.symm with ⟨j, rfl⟩
        rw [(f (v k)).map_eq_zero_of_eq _ hvij (ne_of_apply_ne _ hij), smul_zero]
      _ = 0 := by
        rw [hvij, neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq] <;> assumption

@[deprecated (since := "2025-09-30")]
alias uncurryFin := alternatizeUncurryFin

theorem alternatizeUncurryFin_apply (f : M →ₗ[R] M [⋀^Fin n]→ₗ[R] N) (v : Fin (n + 1) → M) :
    alternatizeUncurryFin f v = ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • f (v i) (removeNth i v) := by
  simp [alternatizeUncurryFin]

@[deprecated (since := "2025-09-30")]
alias uncurryFin_apply := alternatizeUncurryFin_apply

@[simp]
theorem alternatizeUncurryFin_add (f g : M →ₗ[R] M [⋀^Fin n]→ₗ[R] N) :
    alternatizeUncurryFin (f + g) = alternatizeUncurryFin f + alternatizeUncurryFin g := by
  ext
  simp [alternatizeUncurryFin_apply, Finset.sum_add_distrib]

@[deprecated (since := "2025-09-30")]
alias uncurryFin_add := alternatizeUncurryFin_add

@[simp]
lemma alternatizeUncurryFin_curryLeft (f : M [⋀^Fin (n + 1)]→ₗ[R] N) :
    alternatizeUncurryFin (curryLeft f) = (n + 1) • f := by
  ext v
  simp [alternatizeUncurryFin_apply, ← map_insertNth]

@[deprecated (since := "2025-09-30")]
alias uncurryFin_curryLeft := alternatizeUncurryFin_curryLeft

variable {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]

@[simp]
theorem alternatizeUncurryFin_smul (c : S) (f : M →ₗ[R] M [⋀^Fin n]→ₗ[R] N) :
    alternatizeUncurryFin (c • f) = c • alternatizeUncurryFin f := by
  ext v
  simp [alternatizeUncurryFin_apply, smul_comm _ c, Finset.smul_sum]

@[deprecated (since := "2025-09-30")]
alias uncurryFin_smul := alternatizeUncurryFin_smul

/-- `AlternatingMap.alternatizeUncurryFin` as a linear map. -/
@[simps! apply]
def alternatizeUncurryFinLM : (M →ₗ[R] M [⋀^Fin n]→ₗ[R] N) →ₗ[R] M [⋀^Fin (n + 1)]→ₗ[R] N where
  toFun := alternatizeUncurryFin
  map_add' := alternatizeUncurryFin_add
  map_smul' := alternatizeUncurryFin_smul

@[deprecated (since := "2025-09-30")]
alias uncurryFinLM := alternatizeUncurryFinLM

/-- If `f` is a bilinear map taking values in the space of alternating maps,
then evaluation of the twice uncurried `f` on a tuple of vectors `v`
can be represented as a sum of

$$
f(v_i, v_j; v_0, \dots, \hat{v_i}, \dots, \hat{v_j}-) -
f(v_j, v_i; v_0, \dots, \hat{v_i}, \dots, \hat{v_j}-)
$$

over all `(i j : Fin (n + 2))`, `i < j`, taken with appropriate signs.
Here $$\hat{v_i}$$ and $$\hat{v_j}$$ mean that these vectors are removed from the tuple.

We use pairs of `i j : Fin (n + 1)`, `i ≤ j`,
to encode pairs `(i.castSucc : Fin (n + 1), j.succ : Fin (n + 1))`,
so the power of `-1` is off by one compared to the informal texts.

In particular, if `f` is symmetric in the first two arguments,
then the resulting alternating map is zero,
see `alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric` below.
-/
theorem alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply
    (f : M →ₗ[R] M →ₗ[R] M [⋀^Fin n]→ₗ[R] N) (v : Fin (n + 2) → M) :
    alternatizeUncurryFin (alternatizeUncurryFinLM ∘ₗ f) v =
      ∑ (i : Fin (n + 1)), ∑ j ≥ i,
        (-1 : ℤ) ^ (i + j : ℕ) •
          (f (v i.castSucc) (v j.succ) (j.removeNth <| i.castSucc.removeNth v) -
            f (v j.succ) (v i.castSucc) (j.removeNth <| i.castSucc.removeNth v)) := by
  simp? [alternatizeUncurryFin_apply, Finset.smul_sum, sum_sum_eq_sum_triangle_add] says
    simp only [alternatizeUncurryFin_apply, Int.reduceNeg, LinearMap.coe_comp, comp_apply,
      alternatizeUncurryFinLM_apply, Finset.smul_sum, sum_sum_eq_sum_triangle_add, coe_castSucc,
      val_succ]
  refine Fintype.sum_congr _ _ fun i ↦ Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_Ici] at hj
  have H₁ : i.castSucc.removeNth v j = v j.succ := by
    simp [Fin.removeNth_apply, Fin.succAbove_of_le_castSucc, hj]
  have H₂ : j.succ.removeNth v i = v i.castSucc := by
    simp [Fin.removeNth_apply, Fin.succAbove_of_castSucc_lt, hj]
  simp only [pow_add, mul_smul, pow_one, neg_one_smul, smul_neg, smul_sub, ← sub_eq_add_neg,
    smul_comm ((-1 : ℤ) ^ (j : ℕ)), H₁, H₂]
  congr 4
  rw [removeNth_removeNth_eq_swap]
  simp [Fin.predAbove, hj, Fin.succAbove]

/-- If `f` is a symmetric bilinear map taking values in the space of alternating maps,
then the twice uncurried `f` is zero.

See also `alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply`
for a formula that does not assume `f` to be symmetric. -/
theorem alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric
    {f : M →ₗ[R] M →ₗ[R] M [⋀^Fin n]→ₗ[R] N} (hf : ∀ x y, f x y = f y x) :
    alternatizeUncurryFin (alternatizeUncurryFinLM ∘ₗ f) = 0 := by
  ext v
  simp [alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply, hf (v <| .castSucc _)]

@[deprecated (since := "2025-09-30")]
alias uncurryFin_uncurryFinLM_comp_of_symmetric :=
  alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric

end AlternatingMap
