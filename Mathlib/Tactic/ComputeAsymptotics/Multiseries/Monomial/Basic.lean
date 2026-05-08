/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Basis
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Monomial.Predicates

/-!

# Computing limits of monomials

In this file we define the `Monomial` structure, representing monomials in a basis, i.e.
`coef * b₁ ^ e₁ * ... * bₙ ^ eₙ` where `[b₁, ..., bₙ]` is a well-formed basis.

In the tactic implementation, we use `Monomial` to connect multiseries with real functions.
In this file we show how to find a limit of `Monomial` and how to asymptotically compare two
`Monomial`s.

## Main definitions

* `Monomial`: type to represent monomials.
* `UnitMonomial.toFun`/`Monomial.toFun`: converts structures to real functions.

-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

open Asymptotics Filter Topology Real

/-- Structure for representing monomials with coefficients. -/
structure Monomial where
  /-- Real coefficient of the monomial. -/
  coef : ℝ
  /-- Unit part of the monomial. -/
  unit : UnitMonomial

namespace UnitMonomial

/-- Function corresponding to a monomial. -/
noncomputable def toFun (m : UnitMonomial) (basis : Basis) : ℝ → ℝ :=
  fun x ↦ (m.zipWith (fun exp b ↦ (b x)^exp) basis).prod

/-- Logarithm of function represented by a monomial, i.e.
`m[0] * log basis[0] + ... + m[n] * log basis[n]`. -/
noncomputable def toLogFun (m : UnitMonomial) (basis : Basis) : ℝ → ℝ :=
  fun x ↦ (m.zipWith (fun exp b ↦ exp * log (b x)) basis).sum

@[simp]
theorem toFun_nil (basis : Basis) : (UnitMonomial.toFun [] basis) = 1 := by
  ext x
  simp [toFun]

@[simp]
theorem toFun_nil_basis (m : UnitMonomial) : (UnitMonomial.toFun m []) = 1 := by
  ext x
  simp [toFun]

@[simp]
theorem toFun_cons (exp : ℝ) (tl : UnitMonomial) (basis_hd : ℝ → ℝ) (basis_tl : Basis) :
    (UnitMonomial.toFun (exp :: tl) (basis_hd :: basis_tl)) =
    basis_hd ^ exp * tl.toFun basis_tl := by
  ext x
  simp [toFun]

@[simp]
theorem toLogFun_nil (basis : Basis) : (UnitMonomial.toLogFun [] basis) = 0 := by
  ext x
  simp [toLogFun]

@[simp]
theorem toLogFun_nil_basis (m : UnitMonomial) : (UnitMonomial.toLogFun m []) = 0 := by
  ext x
  simp [toLogFun]

@[simp]
theorem toLogFun_cons (exp : ℝ) (tl : UnitMonomial) (basis_hd : ℝ → ℝ) (basis_tl : Basis) :
    (UnitMonomial.toLogFun (exp :: tl) (basis_hd :: basis_tl)) =
    exp • Real.log ∘ basis_hd + UnitMonomial.toLogFun tl basis_tl := by
  ext x
  simp [toLogFun]

/-- Multiplication of unit monomials. -/
noncomputable def mul (m1 m2 : UnitMonomial) : UnitMonomial :=
  m1.zipWith (· + ·) m2

/-- Inversion of a unit monomial. -/
noncomputable def inv (m : UnitMonomial) : UnitMonomial :=
  m.map (-·)

theorem mul_length {m1 m2 : UnitMonomial} (h : m1.length = m2.length) :
    (mul m1 m2).length = m1.length := by
  simp [mul, h]

@[simp]
theorem inv_length (m : UnitMonomial) :
    (inv m).length = m.length := by
  simp [inv]

theorem mul_toFun {m1 m2 : UnitMonomial} {basis : Basis} (h_basis : WellFormedBasis basis)
    (h_length : m1.length = m2.length) :
    (m1.mul m2).toFun basis =ᶠ[atTop] m1.toFun basis * m2.toFun basis := by
  apply h_basis.eventually_pos.mono
  intro x h_pos
  simp only [toFun, mul, Pi.mul_apply]
  induction m1 generalizing m2 basis with
  | nil =>
    symm at h_length
    simp_all
  | cons exp1 exps1 ih =>
    cases m2 with
    | nil => simp at h_length
    | cons exp2 exps2 =>
    cases basis with
    | nil => simp
    | cons basis_hd basis_tl =>
      simp only [List.zipWith_cons_cons, List.prod_cons] at ih ⊢
      have h1 : exps1.length = exps2.length := by grind
      have h2 : ∀ f ∈ basis_tl, 0 < f x := by grind
      have h3 : 0 < basis_hd x := h_pos _ (by simp)
      rw [ih h_basis.tail h1 h2, Real.rpow_add h3]
      grind

theorem inv_toFun {m : UnitMonomial} {basis : Basis} (h_basis : WellFormedBasis basis) :
    m.inv.toFun basis =ᶠ[atTop] (m.toFun basis)⁻¹ := by
  eta_expand
  simp only [toFun, inv, Pi.inv_apply]
  induction m generalizing basis with
  | nil => simp
  | cons exp exps ih =>
    cases basis with
    | nil => simp
    | cons basis_hd basis_tl =>
      apply ((h_basis.head_eventually_pos).and (ih (h_basis.tail))).mono
      intro x ⟨h_pos, ih⟩
      simp only [List.map_cons, List.zipWith_cons_cons, List.prod_cons, mul_inv_rev]
      grind [Real.rpow_neg h_pos.le]

end UnitMonomial

namespace Monomial

/-- Converts `t : Monomial` to real function represented by the corresponding monomial, i.e.
`t.coef * basis[0]^t.exps[0] * basis[1]^t.exps[1] * ...`. It is always assumed that
`t.exps.length = basis.length`, but some theorems below do not require this assumption. -/
noncomputable def toFun (t : Monomial) (basis : Basis) : ℝ → ℝ :=
  t.coef • t.unit.toFun basis

@[simp]
theorem nil_toFun {coef : ℝ} {basis : Basis} :
    Monomial.toFun ⟨coef, []⟩ basis = fun _ ↦ coef := by
  ext x
  simp [toFun]

@[simp]
theorem cons_toFun {coef exp : ℝ} {m : UnitMonomial} {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    Monomial.toFun ⟨coef, exp :: m⟩ (basis_hd :: basis_tl) =
    basis_hd ^ exp * Monomial.toFun ⟨coef, m⟩ basis_tl := by
  ext x
  simp [toFun]
  ring

/-- If `t.coef = 0`, then `t.toFun` is zero. -/
theorem zero_coef_toFun {t : Monomial} (basis : Basis) (h_coef : t.coef = 0) :
    t.toFun basis = 0 := by
  simp [toFun, h_coef]

/-- If `t.coef = 0`, then `t.toFun` is zero. -/
theorem zero_coef_toFun' (basis : Basis) (exps : List ℝ) :
    Monomial.toFun ⟨0, exps⟩ basis = 0 := zero_coef_toFun _ rfl

/-- Negation of a monomial. -/
noncomputable def neg (t : Monomial) : Monomial :=
  ⟨-t.coef, t.unit⟩

/-- Multiplication of monomials. -/
noncomputable def mul (t1 t2 : Monomial) : Monomial :=
  ⟨t1.coef * t2.coef, t1.unit.mul t2.unit⟩

/-- Scales a monomial by a real factor `c`. -/
noncomputable def smul (t : Monomial) (c : ℝ) : Monomial :=
  ⟨c * t.coef, t.unit⟩

/-- Inversion operation for monomials. -/
noncomputable def inv (t : Monomial) : Monomial :=
  ⟨t.coef⁻¹, t.unit.inv⟩

/-- Flipping the sign of `coef` flips the sign of `toFun`. The theorem is stated in this form,
because it allows one to rewrite the `t.toFun basis` expression. It is used below in cases where we
want to reduce the case of `t.coef < 0` to `t.coef > 0`. -/
theorem neg_toFun {t : Monomial} {basis : Basis} :
    t.toFun basis = -t.neg.toFun basis := by
  ext x
  simp [neg, toFun]

theorem mul_toFun {t1 t2 : Monomial} {basis : Basis} (h_basis : WellFormedBasis basis)
    (h_length : t1.unit.length = t2.unit.length) :
    (mul t1 t2).toFun basis =ᶠ[atTop] t1.toFun basis * t2.toFun basis := by
  simp only [toFun, mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  grw [UnitMonomial.mul_toFun h_basis h_length]
  filter_upwards [] with t
  simp [Pi.smul_apply, Pi.mul_apply]
  ring

theorem smul_toFun {t : Monomial} {basis : Basis} (c : ℝ) :
    (smul t c).toFun basis = c • t.toFun basis := by
  ext x
  simp [smul, toFun]
  ring

theorem inv_toFun {t : Monomial} {basis : Basis} (h_basis : WellFormedBasis basis) :
    t.inv.toFun basis =ᶠ[atTop] (t.toFun basis)⁻¹ := by
  simp only [toFun, inv]
  grw [UnitMonomial.inv_toFun h_basis]
  filter_upwards [] with x
  simp [Pi.smul_apply, Pi.inv_apply]
  ring

@[simp]
theorem inv_length (t : Monomial) :
    t.inv.unit.length = t.unit.length := by
  simp [inv]

end Monomial

end Tactic.ComputeAsymptotics
