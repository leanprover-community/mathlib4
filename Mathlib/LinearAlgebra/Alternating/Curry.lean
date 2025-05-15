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
@[simps]
def curryLeft (f : M [⋀^Fin n.succ]→ₗ[R] N) :
    M →ₗ[R] M [⋀^Fin n]→ₗ[R] N where
  toFun m :=
    { f.toMultilinearMap.curryLeft m with
      toFun := fun v => f (Matrix.vecCons m v)
      map_eq_zero_of_eq' := fun v i j hv hij =>
        f.map_eq_zero_of_eq _ (by
          rwa [Matrix.cons_val_succ, Matrix.cons_val_succ]) ((Fin.succ_injective _).ne hij) }
  map_add' _ _ := ext fun _ => f.map_vecCons_add _ _ _
  map_smul' _ _ := ext fun _ => f.map_vecCons_smul _ _ _

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
  ext fun v => congr_arg f <| funext <| by
    refine Fin.cases ?_ ?_
    · rfl
    · simp

end CurryLeft

variable {R : Type*} {M M₂ N N₂ : Type*} [CommRing R] [AddCommGroup M]
  [AddCommGroup M₂] [AddCommGroup N] [AddCommGroup N₂] [Module R M] [Module R M₂]
  [Module R N] [Module R N₂] {n : ℕ}

theorem apply_insertNth (f : M [⋀^Fin (n + 1)]→ₗ[R] N) (p : Fin (n + 1)) (x : M) (v : Fin n → M) :
    f (p.insertNth x v) = (-1) ^ p.val • f (Fin.cons x v) := by
  rw [← Fin.cons_comp_cycleRange, map_perm]
  simp [Units.smul_def]

theorem neg_one_pow_smul_apply_removeNth_add_eq_zero_of_eq
    (f : M [⋀^Fin n]→ₗ[R] N) {v : Fin (n + 1) → M} {i j : Fin (n + 1)}
    (hvij : v i = v j) (hij : i ≠ j) :
    (-1) ^ i.val • f (i.removeNth v) + (-1) ^ j.val • f (j.removeNth v) = 0 := by
  rcases Fin.exists_succAbove_eq hij with ⟨i, rfl⟩
  obtain ⟨m, rfl⟩ : ∃ m, m + 1 = n := by simp [i.pos]
  set w := i.removeNth (j.removeNth v)
  have hw₁ : i.insertNth (v j) w = j.removeNth v := by
    rw [← hvij]
    apply Fin.insertNth_self_removeNth
  have hw₂ : (i.predAbove j).insertNth (v j) w = (j.succAbove i).removeNth v := by
    simp only [w]
    rw [Fin.removeNth_removeNth_eq_swap, Fin.insertNth_removeNth, update_eq_self_iff,
      Fin.removeNth, Fin.succAbove_succAbove_predAbove]
  have : (-1) ^ (j.succAbove i + i.predAbove j : ℕ) = (-1) ^ (j + i + 1 : ℕ) := by
    apply neg_one_pow_congr
    simp [Fin.even_succAbove_add_predAbove, Nat.even_add_one]
  simp only [← hw₁, ← hw₂, apply_insertNth, smul_smul, ← pow_add,
    this, pow_succ', neg_one_mul, neg_smul, neg_add_cancel]

/-- Given a function which is linear in the first argument
and is alternating form in the other `n` arguments,
build an alternating form in `n + 1` arguments.

Note that the round-trip with `curryFin` multiplies the form by `n + 1`,
since we want to avoid division in this definition. -/
def uncurryFin (f : M →ₗ[R] (M [⋀^Fin n]→ₗ[R] N)) :
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
        rw [hvij, neg_one_pow_smul_apply_removeNth_add_eq_zero_of_eq] <;> assumption

theorem uncurryFin_apply (f : M →ₗ[R] (M [⋀^Fin n]→ₗ[R] N)) (v : Fin (n + 1) → M) :
    uncurryFin f v = ∑ i, (-1) ^ i.val • f (v i) (Fin.removeNth i v) := by
  simp [uncurryFin]


end AlternatingMap

