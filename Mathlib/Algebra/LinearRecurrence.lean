/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Algebra.Polynomial.Eval
import Mathlib.LinearAlgebra.Dimension.Constructions

#align_import algebra.linear_recurrence from "leanprover-community/mathlib"@"039a089d2a4b93c761b234f3e5f5aeb752bac60f"

/-!
# Linear recurrence

Informally, a "linear recurrence" is an assertion of the form
`∀ n : ℕ, u (n + d) = a 0 * u n + a 1 * u (n+1) + ... + a (d-1) * u (n+d-1)`,
where `u` is a sequence, `d` is the *order* of the recurrence and the `a i`
are its *coefficients*.

In this file, we define the structure `LinearRecurrence` so that
`LinearRecurrence.mk d a` represents the above relation, and we call
a sequence `u` which verifies it a *solution* of the linear recurrence.

We prove a few basic lemmas about this concept, such as :

* the space of solutions is a submodule of `(ℕ → α)` (i.e a vector space if `α`
  is a field)
* the function that maps a solution `u` to its first `d` terms builds a `LinearEquiv`
  between the solution space and `Fin d → α`, aka `α ^ d`. As a consequence, two
  solutions are equal if and only if their first `d` terms are equals.
* a geometric sequence `q ^ n` is solution iff `q` is a root of a particular polynomial,
  which we call the *characteristic polynomial* of the recurrence

Of course, although we can inductively generate solutions (cf `mkSol`), the
interesting part would be to determinate closed-forms for the solutions.
This is currently *not implemented*, as we are waiting for definition and
properties of eigenvalues and eigenvectors.

-/


noncomputable section

open Finset

open Polynomial

/-- A "linear recurrence relation" over a commutative semiring is given by its
  order `n` and `n` coefficients. -/
structure LinearRecurrence (α : Type*) [CommSemiring α] where
  order : ℕ
  coeffs : Fin order → α
#align linear_recurrence LinearRecurrence

instance (α : Type*) [CommSemiring α] : Inhabited (LinearRecurrence α) :=
  ⟨⟨0, default⟩⟩

namespace LinearRecurrence

section CommSemiring

variable {α : Type*} [CommSemiring α] (E : LinearRecurrence α)

/-- We say that a sequence `u` is solution of `LinearRecurrence order coeffs` when we have
  `u (n + order) = ∑ i : Fin order, coeffs i * u (n + i)` for any `n`. -/
def IsSolution (u : ℕ → α) :=
  ∀ n, u (n + E.order) = ∑ i, E.coeffs i * u (n + i)
#align linear_recurrence.is_solution LinearRecurrence.IsSolution

/-- A solution of a `LinearRecurrence` which satisfies certain initial conditions.
  We will prove this is the only such solution. -/
def mkSol (init : Fin E.order → α) : ℕ → α
  | n =>
    if h : n < E.order then init ⟨n, h⟩
    else
      ∑ k : Fin E.order,
        have _ : n - E.order + k < n := by
          rw [add_comm, ← add_tsub_assoc_of_le (not_lt.mp h), tsub_lt_iff_left]
          · exact add_lt_add_right k.is_lt n
          · convert add_le_add (zero_le (k : ℕ)) (not_lt.mp h)
            simp only [zero_add]
        E.coeffs k * mkSol init (n - E.order + k)
#align linear_recurrence.mk_sol LinearRecurrence.mkSol

/-- `E.mkSol` indeed gives solutions to `E`. -/
theorem is_sol_mkSol (init : Fin E.order → α) : E.IsSolution (E.mkSol init) := by
  intro n
  rw [mkSol]
  simp
#align linear_recurrence.is_sol_mk_sol LinearRecurrence.is_sol_mkSol

/-- `E.mkSol init`'s first `E.order` terms are `init`. -/
theorem mkSol_eq_init (init : Fin E.order → α) : ∀ n : Fin E.order, E.mkSol init n = init n := by
  intro n
  rw [mkSol]
  simp only [n.is_lt, dif_pos, Fin.mk_val, Fin.eta]
#align linear_recurrence.mk_sol_eq_init LinearRecurrence.mkSol_eq_init

/-- If `u` is a solution to `E` and `init` designates its first `E.order` values,
  then `∀ n, u n = E.mkSol init n`. -/
theorem eq_mk_of_is_sol_of_eq_init {u : ℕ → α} {init : Fin E.order → α} (h : E.IsSolution u)
    (heq : ∀ n : Fin E.order, u n = init n) : ∀ n, u n = E.mkSol init n := by
  intro n
  rw [mkSol]
  split_ifs with h'
  · exact mod_cast heq ⟨n, h'⟩
  simp only
  rw [← tsub_add_cancel_of_le (le_of_not_lt h'), h (n - E.order)]
  congr with k
  have : n - E.order + k < n := by
    rw [add_comm, ← add_tsub_assoc_of_le (not_lt.mp h'), tsub_lt_iff_left]
    · exact add_lt_add_right k.is_lt n
    · convert add_le_add (zero_le (k : ℕ)) (not_lt.mp h')
      simp only [zero_add]
  rw [eq_mk_of_is_sol_of_eq_init h heq (n - E.order + k)]
  simp
#align linear_recurrence.eq_mk_of_is_sol_of_eq_init LinearRecurrence.eq_mk_of_is_sol_of_eq_init

/-- If `u` is a solution to `E` and `init` designates its first `E.order` values,
  then `u = E.mkSol init`. This proves that `E.mkSol init` is the only solution
  of `E` whose first `E.order` values are given by `init`. -/
theorem eq_mk_of_is_sol_of_eq_init' {u : ℕ → α} {init : Fin E.order → α} (h : E.IsSolution u)
    (heq : ∀ n : Fin E.order, u n = init n) : u = E.mkSol init :=
  funext (E.eq_mk_of_is_sol_of_eq_init h heq)
#align linear_recurrence.eq_mk_of_is_sol_of_eq_init' LinearRecurrence.eq_mk_of_is_sol_of_eq_init'

/-- The space of solutions of `E`, as a `Submodule` over `α` of the module `ℕ → α`. -/
def solSpace : Submodule α (ℕ → α) where
  carrier := { u | E.IsSolution u }
  zero_mem' n := by simp
  add_mem' {u v} hu hv n := by simp [mul_add, sum_add_distrib, hu n, hv n]
  smul_mem' a u hu n := by simp [hu n, mul_sum]; congr; ext; ac_rfl
#align linear_recurrence.sol_space LinearRecurrence.solSpace

/-- Defining property of the solution space : `u` is a solution
  iff it belongs to the solution space. -/
theorem is_sol_iff_mem_solSpace (u : ℕ → α) : E.IsSolution u ↔ u ∈ E.solSpace :=
  Iff.rfl
#align linear_recurrence.is_sol_iff_mem_sol_space LinearRecurrence.is_sol_iff_mem_solSpace

/-- The function that maps a solution `u` of `E` to its first
  `E.order` terms as a `LinearEquiv`. -/
def toInit : E.solSpace ≃ₗ[α] Fin E.order → α where
  toFun u x := (u : ℕ → α) x
  map_add' u v := by
    ext
    simp
  map_smul' a u := by
    ext
    simp
  invFun u := ⟨E.mkSol u, E.is_sol_mkSol u⟩
  left_inv u := by ext n; symm; apply E.eq_mk_of_is_sol_of_eq_init u.2; intro k; rfl
  right_inv u := Function.funext_iff.mpr fun n ↦ E.mkSol_eq_init u n
#align linear_recurrence.to_init LinearRecurrence.toInit

/-- Two solutions are equal iff they are equal on `range E.order`. -/
theorem sol_eq_of_eq_init (u v : ℕ → α) (hu : E.IsSolution u) (hv : E.IsSolution v) :
    u = v ↔ Set.EqOn u v ↑(range E.order) := by
  refine Iff.intro (fun h x _ ↦ h ▸ rfl) ?_
  intro h
  set u' : ↥E.solSpace := ⟨u, hu⟩
  set v' : ↥E.solSpace := ⟨v, hv⟩
  change u'.val = v'.val
  suffices h' : u' = v' from h' ▸ rfl
  rw [← E.toInit.toEquiv.apply_eq_iff_eq, LinearEquiv.coe_toEquiv]
  ext x
  exact mod_cast h (mem_range.mpr x.2)
#align linear_recurrence.sol_eq_of_eq_init LinearRecurrence.sol_eq_of_eq_init

/-! `E.tupleSucc` maps `![s₀, s₁, ..., sₙ]` to `![s₁, ..., sₙ, ∑ (E.coeffs i) * sᵢ]`,
  where `n := E.order`. This operation is quite useful for determining closed-form
  solutions of `E`. -/


/-- `E.tupleSucc` maps `![s₀, s₁, ..., sₙ]` to `![s₁, ..., sₙ, ∑ (E.coeffs i) * sᵢ]`,
  where `n := E.order`. -/
def tupleSucc : (Fin E.order → α) →ₗ[α] Fin E.order → α where
  toFun X i := if h : (i : ℕ) + 1 < E.order then X ⟨i + 1, h⟩ else ∑ i, E.coeffs i * X i
  map_add' x y := by
    ext i
    simp only
    split_ifs with h <;> simp [h, mul_add, sum_add_distrib]
  map_smul' x y := by
    ext i
    simp only
    split_ifs with h <;> simp [h, mul_sum]
    exact sum_congr rfl fun x _ ↦ by ac_rfl
#align linear_recurrence.tuple_succ LinearRecurrence.tupleSucc

end CommSemiring

section StrongRankCondition

-- note: `StrongRankCondition` is the same as `Nontrivial` on `CommRing`s, but that result,
-- `commRing_strongRankCondition`, is in a much later file.
variable {α : Type*} [CommRing α] [StrongRankCondition α] (E : LinearRecurrence α)

/-- The dimension of `E.solSpace` is `E.order`. -/
theorem solSpace_rank : Module.rank α E.solSpace = E.order :=
  letI := nontrivial_of_invariantBasisNumber α
  @rank_fin_fun α _ _ E.order ▸ E.toInit.rank_eq
#align linear_recurrence.sol_space_rank LinearRecurrence.solSpace_rank

end StrongRankCondition

section CommRing

variable {α : Type*} [CommRing α] (E : LinearRecurrence α)

/-- The characteristic polynomial of `E` is
`X ^ E.order - ∑ i : Fin E.order, (E.coeffs i) * X ^ i`. -/
def charPoly : α[X] :=
  Polynomial.monomial E.order 1 - ∑ i : Fin E.order, Polynomial.monomial i (E.coeffs i)
#align linear_recurrence.char_poly LinearRecurrence.charPoly

/-- The geometric sequence `q^n` is a solution of `E` iff
  `q` is a root of `E`'s characteristic polynomial. -/
theorem geom_sol_iff_root_charPoly (q : α) :
    (E.IsSolution fun n ↦ q ^ n) ↔ E.charPoly.IsRoot q := by
  rw [charPoly, Polynomial.IsRoot.def, Polynomial.eval]
  simp only [Polynomial.eval₂_finset_sum, one_mul, RingHom.id_apply, Polynomial.eval₂_monomial,
    Polynomial.eval₂_sub]
  constructor
  · intro h
    simpa [sub_eq_zero] using h 0
  · intro h n
    simp only [pow_add, sub_eq_zero.mp h, mul_sum]
    exact sum_congr rfl fun _ _ ↦ by ring
#align linear_recurrence.geom_sol_iff_root_char_poly LinearRecurrence.geom_sol_iff_root_charPoly

end CommRing

end LinearRecurrence
