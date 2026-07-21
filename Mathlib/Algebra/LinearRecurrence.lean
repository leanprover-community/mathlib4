/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

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
  solutions are equal if and only if their first `d` terms are equal.
* a geometric sequence `q ^ n` is solution iff `q` is a root of a particular polynomial,
  which we call the *characteristic polynomial* of the recurrence

Of course, although we can inductively generate solutions (cf `mkSol`), the
interesting part would be to determine closed-forms for the solutions.
This is currently *not implemented*, as we are waiting for definition and
properties of eigenvalues and eigenvectors.

-/

@[expose] public section

noncomputable section

open Finset

open Polynomial

/-- A "linear recurrence relation" over a commutative semiring is given by its
  order `n` and `n` coefficients. -/
@[wikidata Q364089]
structure LinearRecurrence (R : Type*) [CommSemiring R] where
  /-- Order of the linear recurrence -/
  order : ℕ
  /-- Coefficients of the linear recurrence -/
  coeffs : Fin order → R

instance (R : Type*) [CommSemiring R] : Inhabited (LinearRecurrence R) :=
  ⟨⟨0, default⟩⟩

namespace LinearRecurrence

section CommSemiring

variable {R : Type*} [CommSemiring R] (E : LinearRecurrence R)

/-- We say that a sequence `u` is solution of `LinearRecurrence order coeffs` when we have
  `u (n + order) = ∑ i : Fin order, coeffs i * u (n + i)` for any `n`. -/
def IsSolution (u : ℕ → R) :=
  ∀ n, u (n + E.order) = ∑ i, E.coeffs i * u (n + i)

/-- A solution of a `LinearRecurrence` which satisfies certain initial conditions.
  We will prove this is the only such solution. -/
def mkSol (init : Fin E.order → R) : ℕ → R
  | n =>
    if h : n < E.order then init ⟨n, h⟩
    else
      ∑ k : Fin E.order,
        have _ : n - E.order + k < n := by lia
        E.coeffs k * mkSol init (n - E.order + k)

/-- `E.mkSol` indeed gives solutions to `E`. -/
theorem is_sol_mkSol (init : Fin E.order → R) : E.IsSolution (E.mkSol init) := by
  intro n
  rw [mkSol]
  simp

/-- `E.mkSol init`'s first `E.order` terms are `init`. -/
theorem mkSol_eq_init (init : Fin E.order → R) : ∀ n : Fin E.order, E.mkSol init n = init n := by
  intro n
  rw [mkSol]
  simp only [n.is_lt, dif_pos, Fin.mk_val]

/-- If `u` is a solution to `E` and `init` designates its first `E.order` values,
  then `∀ n, u n = E.mkSol init n`. -/
theorem eq_mk_of_is_sol_of_eq_init {u : ℕ → R} {init : Fin E.order → R} (h : E.IsSolution u)
    (heq : ∀ n : Fin E.order, u n = init n) : ∀ n, u n = E.mkSol init n := by
  intro n
  rw [mkSol]
  split_ifs with h'
  · exact mod_cast heq ⟨n, h'⟩
  · dsimp only
    rw [← tsub_add_cancel_of_le (le_of_not_gt h'), h (n - E.order)]
    congr with k
    rw [eq_mk_of_is_sol_of_eq_init h heq (n - E.order + k)]
    simp

/-- If `u` is a solution to `E` and `init` designates its first `E.order` values,
  then `u = E.mkSol init`. This proves that `E.mkSol init` is the only solution
  of `E` whose first `E.order` values are given by `init`. -/
theorem eq_mk_of_is_sol_of_eq_init' {u : ℕ → R} {init : Fin E.order → R} (h : E.IsSolution u)
    (heq : ∀ n : Fin E.order, u n = init n) : u = E.mkSol init :=
  funext (E.eq_mk_of_is_sol_of_eq_init h heq)

/-- The space of solutions of `E`, as a `Submodule` over `R` of the module `ℕ → R`. -/
def solSpace : Submodule R (ℕ → R) where
  carrier := { u | E.IsSolution u }
  zero_mem' n := by simp
  add_mem' {u v} hu hv n := by simp [mul_add, sum_add_distrib, hu n, hv n]
  smul_mem' a u hu n := by simp [hu n, mul_sum]; ac_rfl

/-- Defining property of the solution space : `u` is a solution
  iff it belongs to the solution space. -/
theorem is_sol_iff_mem_solSpace (u : ℕ → R) : E.IsSolution u ↔ u ∈ E.solSpace :=
  Iff.rfl

/-- The function that maps a solution `u` of `E` to its first
  `E.order` terms as a `LinearEquiv`. -/
def toInit : E.solSpace ≃ₗ[R] Fin E.order → R where
  toFun u x := (u : ℕ → R) x
  map_add' u v := by
    ext
    simp
  map_smul' a u := by
    ext
    simp
  invFun u := ⟨E.mkSol u, E.is_sol_mkSol u⟩
  left_inv u := by ext n; symm; apply E.eq_mk_of_is_sol_of_eq_init u.2; intro k; rfl
  right_inv u := funext_iff.mpr fun n ↦ E.mkSol_eq_init u n

theorem mkSol_injective : E.mkSol.Injective :=
  Subtype.val_injective.comp E.toInit.symm.injective

/-- A basis of the solution space given by solutions whose initial conditions are the standard basis
vectors -/
def basis : Module.Basis (Fin E.order) R E.solSpace :=
  .ofEquivFun E.toInit

/-- The coordinates of a solution in the basis are its first `E.order` values -/
theorem repr_basis_eq (u : E.solSpace) :
    E.basis.repr u = .ofSupportFinite (u ∘ Fin.val) (Set.toFinite _) :=
  rfl

/-- The nth coordinate of a solution in the basis equals its nth value -/
@[simp]
theorem repr_basis_apply (u : E.solSpace) (n : Fin E.order) : E.basis.repr u n = u.val n :=
  rfl

/-- Two solutions are equal iff their initial conditions are equal. -/
theorem eq_iff_eqOn_range_order (u v : ℕ → R) (hu : E.IsSolution u) (hv : E.IsSolution v) :
    u = v ↔ Set.EqOn u v ↑(range E.order) := by
  replace hu : u ∈ E.solSpace := (is_sol_iff_mem_solSpace _ _).mp hu
  replace hv : v ∈ E.solSpace := (is_sol_iff_mem_solSpace _ _).mp hv
  rw [← Subtype.mk.injEq u hu v hv, ← E.basis.repr.injective.eq_iff]
  constructor
  · exact fun h n hn ↦ congr($h ⟨n, Finset.mem_range.mp hn⟩)
  · exact fun h ↦ Finsupp.ext fun n ↦ h <| Finset.mem_range.mpr n.prop

@[deprecated (since := "2026-04-16")] alias sol_eq_of_eq_init := eq_iff_eqOn_range_order

/-! `E.tupleSucc` maps `![s₀, s₁, ..., sₙ]` to `![s₁, ..., sₙ, ∑ (E.coeffs i) * sᵢ]`,
where `n := E.order`. This operation is quite useful for determining closed-form
solutions of `E`. -/

/-- `E.tupleSucc` maps `![s₀, s₁, ..., sₙ]` to `![s₁, ..., sₙ, ∑ (E.coeffs i) * sᵢ]`,
where `n := E.order`. -/
def tupleSucc : (Fin E.order → R) →ₗ[R] Fin E.order → R where
  toFun X i := if h : (i : ℕ) + 1 < E.order then X ⟨i + 1, h⟩ else ∑ i, E.coeffs i * X i
  map_add' x y := by
    ext i
    split_ifs with h <;> simp [h, mul_add, sum_add_distrib]
  map_smul' x y := by
    ext i
    split_ifs with h <;>
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, h, ↓reduceDIte, mul_sum]
    exact sum_congr rfl fun x _ ↦ by ac_rfl

end CommSemiring

section StrongRankCondition

-- note: `StrongRankCondition` is the same as `Nontrivial` on `CommRing`s, but that result,
-- `commRing_strongRankCondition`, is in a much later file.
variable {R : Type*} [CommRing R] [StrongRankCondition R] (E : LinearRecurrence R)

/-- The dimension of `E.solSpace` is `E.order`. -/
theorem solSpace_rank : Module.rank R E.solSpace = E.order := by
  simp [rank_eq_card_basis E.basis]

end StrongRankCondition

section CommRing

variable {R : Type*} [CommRing R] (E : LinearRecurrence R)

/-- The characteristic polynomial of `E` is
`X ^ E.order - ∑ i : Fin E.order, (E.coeffs i) * X ^ i`. -/
def charPoly : R[X] :=
  Polynomial.monomial E.order 1 - ∑ i : Fin E.order, Polynomial.monomial i (E.coeffs i)

@[simp]
theorem charPoly_degree_eq_order [Nontrivial R] : (charPoly E).degree = E.order := by
  rw [charPoly, degree_sub_eq_left_of_degree_lt]
    <;> rw [degree_monomial E.order one_ne_zero]
  simp_rw [← C_mul_X_pow_eq_monomial]
  exact degree_sum_fin_lt E.coeffs

theorem charPoly_monic : charPoly E |>.Monic := by
  nontriviality R
  rw [Monic, leadingCoeff, natDegree_eq_of_degree_eq_some <| charPoly_degree_eq_order _, charPoly,
    coeff_sub, coeff_monomial_same, finsetSum_coeff, sub_eq_self]
  refine sum_eq_zero fun _ _ ↦ coeff_eq_zero_of_degree_lt ?_
  grw [degree_monomial_le]
  simp

/-- The geometric sequence `q^n` is a solution of `E` iff
  `q` is a root of `E`'s characteristic polynomial. -/
theorem geom_sol_iff_root_charPoly (q : R) :
    (E.IsSolution fun n ↦ q ^ n) ↔ E.charPoly.IsRoot q := by
  rw [charPoly, Polynomial.IsRoot.def, Polynomial.eval]
  simp only [Polynomial.eval₂_finsetSum, one_mul, RingHom.id_apply, Polynomial.eval₂_monomial,
    Polynomial.eval₂_sub]
  constructor
  · intro h
    simpa [sub_eq_zero] using h 0
  · intro h n
    simp only [pow_add, sub_eq_zero.mp h, mul_sum]
    exact sum_congr rfl fun _ _ ↦ by ring

end CommRing

end LinearRecurrence
