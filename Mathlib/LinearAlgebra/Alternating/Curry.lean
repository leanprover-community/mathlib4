/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Yury Kudryashov
-/
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fin.Parity

/-!
# Currying alternating forms

In this file we define `AlternatingMap.curryLeft`
which interprets an alternating map in `n + 1` variables
as a linear map in the 0th variable taking values in the alternating maps in `n` variables.
-/

open Function Fin

namespace AlternatingMap

section CurryLeft

variable {R : Type*} {M M₂ N N₂ : Type*} [CommSemiring R] [AddCommMonoid M]
  [AddCommMonoid M₂] [AddCommMonoid N] [AddCommMonoid N₂] [Module R M] [Module R M₂]
  [Module R N] [Module R N₂] {n : ℕ}

/-- Given an alternating map `f` in `n+1` variables, split the first variable to obtain
a linear map into alternating maps in `n` variables, given by `x ↦ (m ↦ f (Matrix.vecCons x m))`.
It can be thought of as a map $Hom(\bigwedge^{n+1} M, N) \to Hom(M, Hom(\bigwedge^n M, N))$.

This is `MultilinearMap.curryLeft` for `AlternatingMap`. See also
`AlternatingMap.curryLeftLinearMap`. -/
@[simps apply_toMultilinearMap]
def curryLeft (f : M [⋀^Fin n.succ]→ₗ[R] N) : M →ₗ[R] M [⋀^Fin n]→ₗ[R] N where
  toFun m :=
    { f.toMultilinearMap.curryLeft m with
      map_eq_zero_of_eq' v i j hv hij :=
        f.map_eq_zero_of_eq _ (by simpa) ((Fin.succ_injective _).ne hij) }
  map_add' _ _ := ext fun _ => f.map_vecCons_add _ _ _
  map_smul' _ _ := ext fun _ => f.map_vecCons_smul _ _ _

@[simp]
theorem curryLeft_apply_apply (f : M [⋀^Fin n.succ]→ₗ[R] N) (x : M) (v : Fin n → M) :
    curryLeft f x v = f (Matrix.vecCons x v) :=
  rfl

@[simp]
theorem curryLeft_zero : curryLeft (0 : M [⋀^Fin n.succ]→ₗ[R] N) = 0 :=
  rfl

@[simp]
theorem curryLeft_add (f g : M [⋀^Fin n.succ]→ₗ[R] N) :
    curryLeft (f + g) = curryLeft f + curryLeft g :=
  rfl

@[simp]
theorem curryLeft_smul (r : R) (f : M [⋀^Fin n.succ]→ₗ[R] N) :
    curryLeft (r • f) = r • curryLeft f :=
  rfl

/-- `AlternatingMap.curryLeft` as a `LinearMap`. This is a separate definition as dot notation
does not work for this version. -/
@[simps]
def curryLeftLinearMap :
    (M [⋀^Fin n.succ]→ₗ[R] N) →ₗ[R] M →ₗ[R] M [⋀^Fin n]→ₗ[R] N where
  toFun f := f.curryLeft
  map_add' := curryLeft_add
  map_smul' := curryLeft_smul

/-- Currying with the same element twice gives the zero map. -/
@[simp]
theorem curryLeft_same (f : M [⋀^Fin n.succ.succ]→ₗ[R] N) (m : M) :
    (f.curryLeft m).curryLeft m = 0 :=
  ext fun _ => f.map_eq_zero_of_eq _ (by simp) Fin.zero_ne_one

@[simp]
theorem curryLeft_compAlternatingMap (g : N →ₗ[R] N₂)
    (f : M [⋀^Fin n.succ]→ₗ[R] N) (m : M) :
    (g.compAlternatingMap f).curryLeft m = g.compAlternatingMap (f.curryLeft m) :=
  rfl

@[simp]
theorem curryLeft_compLinearMap (g : M₂ →ₗ[R] M) (f : M [⋀^Fin n.succ]→ₗ[R] N) (m : M₂) :
    (f.compLinearMap g).curryLeft m = (f.curryLeft (g m)).compLinearMap g :=
  ext fun v ↦ congr_arg f <| funext fun i ↦ by cases i using Fin.cases <;> simp

end CurryLeft

variable {R : Type*} {M M₂ N N₂ : Type*} [CommRing R] [AddCommGroup M]
  [AddCommGroup M₂] [AddCommGroup N] [AddCommGroup N₂] [Module R M] [Module R M₂]
  [Module R N] [Module R N₂] {n : ℕ}

theorem map_insertNth (f : M [⋀^Fin (n + 1)]→ₗ[R] N) (p : Fin (n + 1)) (x : M) (v : Fin n → M) :
    f (p.insertNth x v) = (-1) ^ p.val • f (Matrix.vecCons x v) := by
  rw [← Fin.cons_comp_cycleRange, map_perm, Matrix.vecCons]
  simp [Units.smul_def]

theorem neg_one_pow_smul_map_insertNth (f : M [⋀^Fin (n + 1)]→ₗ[R] N) (p : Fin (n + 1)) (x : M)
    (v : Fin n → M) :
    (-1) ^ p.val • f (p.insertNth x v) = f (Matrix.vecCons x v) := by
  rw [map_insertNth, smul_smul, ← pow_add, Even.neg_one_pow, one_smul]
  use p

/-- Let `v` be an `(n + 1)`-tuple with two equal elements `v i = v j`, `i ≠ j`.
Let `w i` (resp., `w j`) be the vector `v` with `i`th (resp., `j`th) element removed.
Then `(-1) ^ i • f (w i) + (-1) ^ j • f (w j) = 0`.
This follows from the fact that these two vectors differ by a permutation of sign `(-1) ^ (i + j)`.

These are the only two nonzero terms in the proof of `map_eq_zero_of_eq`
in the definition of `uncurryFin` below. -/
theorem neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq (f : M [⋀^Fin n]→ₗ[R] N)
    {v : Fin (n + 1) → M} {i j : Fin (n + 1)} (hvij : v i = v j) (hij : i ≠ j) :
    (-1) ^ i.val • f (i.removeNth v) + (-1) ^ j.val • f (j.removeNth v) = 0 := by
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
and is alternating form in the other `n` arguments,
build an alternating form in `n + 1` arguments.

Note that the round-trip with `curryFin` multiplies the form by `n + 1`,
since we want to avoid division in this definition. -/
def uncurryFin (f : M →ₗ[R] M [⋀^Fin n]→ₗ[R] N) :
    M [⋀^Fin (n + 1)]→ₗ[R] N where
  toMultilinearMap :=
    ∑ p, (-1) ^ p.val • LinearMap.uncurryMid p ((toMultilinearMapLM (S := R)).comp f)
  map_eq_zero_of_eq' := by
    intro v i j hvij hij
    suffices ∑ k : Fin (n + 1), (-1) ^ k.val • f (v k) (k.removeNth v) = 0 by simpa
    calc
      _ = (-1) ^ i.val • f (v i) (i.removeNth v) + (-1) ^ j.val • f (v j) (j.removeNth v) := by
        refine Fintype.sum_eq_add _ _ hij fun k ⟨hki, hkj⟩ ↦ ?_
        rcases Fin.exists_succAbove_eq hki.symm with ⟨i, rfl⟩
        rcases Fin.exists_succAbove_eq hkj.symm with ⟨j, rfl⟩
        rw [(f (v k)).map_eq_zero_of_eq _ hvij (ne_of_apply_ne _ hij), smul_zero]
      _ = 0 := by
        rw [hvij, neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq] <;> assumption

theorem uncurryFin_apply (f : M →ₗ[R] M [⋀^Fin n]→ₗ[R] N) (v : Fin (n + 1) → M) :
    uncurryFin f v = ∑ i, (-1) ^ i.val • f (v i) (Fin.removeNth i v) := by
  simp [uncurryFin]

@[simp]
theorem uncurryFin_add (f g : M →ₗ[R] M [⋀^Fin n]→ₗ[R] N) :
    uncurryFin (f + g) = uncurryFin f + uncurryFin g := by
  ext
  simp [uncurryFin_apply, Finset.sum_add_distrib]

@[simp]
lemma uncurryFin_curryLeft (f : M [⋀^Fin (n + 1)]→ₗ[R] N) :
    uncurryFin (curryLeft f) = (n + 1) • f := by
  ext v
  simp [uncurryFin_apply, ← map_insertNth]

variable {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]

@[simp]
theorem uncurryFin_smul
    (c : S) (f : M →ₗ[R] M [⋀^Fin n]→ₗ[R] N) :
    uncurryFin (c • f) = c • uncurryFin f := by
  ext v
  simp [uncurryFin_apply, smul_comm _ c, Finset.smul_sum]

/-- `AlternaringMap.uncurryFin` as a linear map. -/
@[simps! apply]
def uncurryFinLM : (M →ₗ[R] M [⋀^Fin n]→ₗ[R] N) →ₗ[R] M [⋀^Fin (n + 1)]→ₗ[R] N where
  toFun := uncurryFin
  map_add' := uncurryFin_add
  map_smul' := uncurryFin_smul

/-- If `f` is a symmetric bilinear map taking values in the space of alternating maps,
then the twice uncurried `f` is zero. -/
theorem uncurryFin_uncurryFinLM_comp_of_symmetric {f : M →ₗ[R] M →ₗ[R] M [⋀^Fin n]→ₗ[R] N}
    (hf : ∀ x y, f x y = f y x) :
    uncurryFin (uncurryFinLM ∘ₗ f) = 0 := by
  ext v
  set a : Fin (n + 2) → Fin (n + 1) → N := fun i j ↦
    (-1) ^ (i + j : ℕ) • f (v i) (i.removeNth v j) (j.removeNth (i.removeNth v))
  suffices ∑ ij : Fin (n + 2) × Fin (n + 1), a ij.1 ij.2 = 0 by
    simpa [a, uncurryFin_apply, Finset.smul_sum, Fintype.sum_prod_type, mul_smul, pow_add]
      using this
  set g : Fin (n + 2) × Fin (n + 1) → Fin (n + 2) × Fin (n + 1) := fun (i, j) ↦
    (i.succAbove j, j.predAbove i)
  have hg_invol : g.Involutive := by
    intro (i, j)
    simp [g, succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]
  refine Finset.sum_ninvolution g ?_ (by simp [g, Fin.succAbove_ne]) (by simp) hg_invol
  intro (i, j)
  simp only [a]
  rw [hf (v i), ← Fin.removeNth_removeNth_eq_swap, Fin.removeNth_apply (i.succAbove j),
    Fin.succAbove_succAbove_predAbove, Fin.neg_one_pow_succAbove_add_predAbove, neg_smul,
    Fin.removeNth_apply, add_neg_cancel]

end AlternatingMap

