/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Quadratic Number Fields

This file defines the concept of a quadratic number field as a degree-2 extension of `ℚ`,
builds the concrete model `ℚ(√d)` as `QuadraticAlgebra ℚ d 0`, and proves basic properties
including norm, trace, field/number field instances, the `IsQuadraticField` predicate,
rescaling isomorphisms, normalization to squarefree integer parameters,
and uniqueness of the squarefree parameter.

## Main Definitions

* `IsQuadraticField K`: A predicate asserting that `K` is a quadratic extension of `ℚ`.
  This is defined as `Algebra.IsQuadraticExtension ℚ K`.
* `Qsqrtd d`: The quadratic algebra `QuadraticAlgebra ℚ d 0`, representing `ℚ(√d)`.
* `Qsqrtd.norm`: The norm `N(x) = x · x̄ = x.re² - d · x.im²`.

## Main Results

* `IsQuadraticField.instNumberField`: Any quadratic field is a number field.
* `Qsqrtd.instIsQuadraticExtension`: `ℚ(√d)/ℚ` is a degree-2 extension.
* `not_isSquare_ratCast_of_squarefree_ne_one`: squarefree integer parameters
  with `d ≠ 1` give genuine quadratic fields.
* `Qsqrtd.rescale`: `ℚ(√d) ≃ₐ[ℚ] ℚ(√(a²d))` for `a ≠ 0`.
* `Qsqrtd_iso_int_param`: every quadratic field is isomorphic to one with an
  integer parameter.
* `Qsqrtd_iso_squarefree_int_param`: every quadratic field is isomorphic to one
  with a squarefree integer parameter.
* `Qsqrtd.param_unique`: the squarefree integer parameter is unique.
-/

@[expose] public section

/-- A field `K` is a quadratic field if it is a quadratic extension of `ℚ`. -/
abbrev IsQuadraticField (K : Type*) [Field K] [Algebra ℚ K] : Prop :=
  Algebra.IsQuadraticExtension ℚ K

/-- A quadratic field is a number field: it has characteristic zero
and is finite-dimensional over `ℚ`. -/
instance IsQuadraticField.instNumberField (K : Type*) [Field K] [Algebra ℚ K]
    [IsQuadraticField K] : NumberField K where
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  to_finiteDimensional := by
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
    convert FiniteDimensional.of_finrank_pos (K := ℚ) (V := K) (by
      rw [Algebra.IsQuadraticExtension.finrank_eq_two (R := ℚ) (S := K)]; omega) using 1
    congr 1
    exact Subsingleton.elim _ _

/-- The quadratic field `ℚ(√d)` as a type alias for `QuadraticAlgebra ℚ d 0`. -/
abbrev Qsqrtd (d : ℚ) : Type := QuadraticAlgebra ℚ d 0

/-! ## Quadratic Extension Instances -/

/-- The `Module ℚ` instance from the `Field` algebra structure on `QuadraticAlgebra ℚ a b`
coincides with the `QuadraticAlgebra` module structure. This resolves the diamond between
the two `Algebra ℚ` instances (`DivisionRing.toRatAlgebra` vs `QuadraticAlgebra.instAlgebra`). -/
private theorem QuadraticAlgebra.module_eq (a b : ℚ) [Fact (∀ r : ℚ, r ^ 2 ≠ a + b * r)] :
    (Algebra.toModule : Module ℚ (QuadraticAlgebra ℚ a b)) =
      QuadraticAlgebra.instModule := by
  refine Module.ext' _ _ ?_
  intro r x
  simpa [Algebra.smul_def, QuadraticAlgebra.algebraMap_eq] using
    (QuadraticAlgebra.C_mul_eq_smul (R := ℚ) (a := a) (b := b) r x)

/-- Any `QuadraticAlgebra ℚ a b` that is a field is automatically a quadratic extension
of `ℚ`, i.e., a degree-2 extension. Combined with `IsQuadraticField.instNumberField`,
this gives `NumberField (QuadraticAlgebra ℚ a b)` for free. -/
instance QuadraticAlgebra.instIsQuadraticExtension (a b : ℚ)
    [Fact (∀ r : ℚ, r ^ 2 ≠ a + b * r)] :
    Algebra.IsQuadraticExtension ℚ (QuadraticAlgebra ℚ a b) where
  finrank_eq_two' := QuadraticAlgebra.module_eq a b ▸ QuadraticAlgebra.finrank_eq_two a b

/-! ## The Concrete Model `Qsqrtd` -/

namespace Qsqrtd

open QuadraticAlgebra

variable {d : ℚ}

/-- The trace in `Q(√d)` is `x.re + x̄.re`. -/
@[simp] theorem trace_eq_re_add_re_star (x : Qsqrtd d) :
    Algebra.trace ℚ (Qsqrtd d) x = x.re + (star x).re := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis d 0), leftMulMatrix_eq,
    Matrix.trace_fin_two_of]
  simp

/-- In the model `Q(√d) = QuadraticAlgebra ℚ d 0`, the trace is `2 * re`. -/
theorem trace_eq_two_re (x : Qsqrtd d) :
    Algebra.trace ℚ (Qsqrtd d) x = 2 * x.re := by
  rw [trace_eq_re_add_re_star]
  simp
  ring

/-- The norm of an element `x : Q(√d)`, defined as `N(x) = x · x̄ = x.re² - d · x.im²`. -/
abbrev norm {d : ℚ} (x : Qsqrtd d) : ℚ := QuadraticAlgebra.norm x

/-- `Q(√0)` is not reduced because `√0² = 0` but `√0 ≠ 0`. -/
lemma zero_not_isReduced : ¬ IsReduced (Qsqrtd (0 : ℚ)) := by
  intro ⟨h⟩
  have hnil : IsNilpotent (⟨0, 1⟩ : Qsqrtd 0) :=
    ⟨2, by ext <;> simp [pow_succ, pow_zero, QuadraticAlgebra.mk_mul_mk]⟩
  have hne : (⟨0, 1⟩ : Qsqrtd 0) ≠ 0 := by
    intro heq
    exact one_ne_zero (congr_arg QuadraticAlgebra.im heq)
  exact hne (h _ hnil)

/-- `Q(√0)` is not a field (it has nilpotents). -/
lemma zero_not_isField : ¬ IsField (Qsqrtd (0 : ℚ)) := by
  intro hF
  haveI := hF.isDomain
  exact zero_not_isReduced (inferInstance : IsReduced (Qsqrtd (0 : ℚ)))

/-- `Q(√1) ≅ ℚ × ℚ` is not a field (it has zero divisors). -/
lemma one_not_isField : ¬ IsField (Qsqrtd (1 : ℚ)) := by
  intro hF
  haveI := hF.isDomain
  have hprod : (⟨1, 1⟩ : Qsqrtd 1) * ⟨1, -1⟩ = 0 := by
    ext <;> simp
  have hne : (⟨1, 1⟩ : Qsqrtd 1) ≠ 0 := by
    intro h
    exact one_ne_zero (congr_arg QuadraticAlgebra.re h)
  have hne' : (⟨1, -1⟩ : Qsqrtd 1) ≠ 0 := by
    intro h
    exact one_ne_zero (congr_arg QuadraticAlgebra.re h)
  rcases mul_eq_zero.mp hprod with h | h <;> contradiction

/-- Bridge: `¬ IsSquare d` implies the technical `Fact` needed by
`QuadraticAlgebra.instField`. -/
instance instFact_of_not_isSquare (d : ℚ) [Fact (¬ IsSquare d)] :
    Fact (∀ r : ℚ, r ^ 2 ≠ d + 0 * r) :=
  ⟨by intro r hr; exact (Fact.out : ¬ IsSquare d) ⟨r, by nlinarith [hr]⟩⟩

end Qsqrtd

/-! ## Integer Parameter Lemmas -/

/-- For a squarefree integer `d ≠ 1`, `d` is not a perfect square in `ℤ`. -/
lemma not_isSquare_int_of_squarefree_ne_one {d : ℤ}
    (hd : Squarefree d) (h1 : d ≠ 1) : ¬ IsSquare d := by
  intro hsq
  apply h1
  rcases Int.isUnit_iff.mp (hd.isUnit_of_isSquare hsq) with rfl | rfl <;> simp_all

/-- For a squarefree integer `d ≠ 1`, `(d : ℚ)` is not a perfect square in `ℚ`. -/
lemma not_isSquare_ratCast_of_squarefree_ne_one {d : ℤ}
    (hd : Squarefree d) (h1 : d ≠ 1) : ¬ IsSquare ((d : ℤ) : ℚ) := by
  intro hsqQ
  exact not_isSquare_int_of_squarefree_ne_one hd h1 (Rat.isSquare_intCast_iff.mp hsqQ)

/-- Bridge squarefree integer parameters to the field-level non-square condition. -/
instance instFact_not_isSquare_ratCast_of_squarefree_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Fact (¬ IsSquare ((d : ℤ) : ℚ)) :=
  ⟨not_isSquare_ratCast_of_squarefree_ne_one
    (d := d) (Fact.out : Squarefree d) (Fact.out : d ≠ 1)⟩

/-! ## Rescaling Isomorphisms -/

/-- `ℚ(√d) ≃ₐ[ℚ] ℚ(√(a²d))` via `⟨r, s⟩ ↦ ⟨r, s·a⁻¹⟩`.

This shows that scaling the parameter by a rational square yields an
isomorphic quadratic field. -/
def Qsqrtd.rescale (d : ℚ) (a : ℚ) (ha : a ≠ 0) :
    Qsqrtd d ≃ₐ[ℚ] Qsqrtd (a ^ 2 * d) := by
  have h1d : (1 : Qsqrtd d) = ⟨1, 0⟩ := by ext <;> rfl
  have h1a : (1 : Qsqrtd (a ^ 2 * d)) = ⟨1, 0⟩ := by
    ext <;> rfl
  exact AlgEquiv.ofLinearEquiv
    { toFun := fun x => ⟨x.re, x.im * a⁻¹⟩
      invFun := fun y => ⟨y.re, y.im * a⟩
      map_add' := by intro x y; ext <;> simp [add_mul]
      map_smul' := by intro c x; ext <;> simp [mul_assoc]
      left_inv := by
        intro x; ext <;> simp [mul_assoc, inv_mul_cancel₀ ha]
      right_inv := by
        intro y; ext <;> simp [mul_assoc, mul_inv_cancel₀ ha] }
    (by simp [h1d, h1a])
    (by intro x y; ext <;> simp <;> field_simp)

/-- Every quadratic field `Q(√d)` is isomorphic to one with an integer parameter:
`∃ z ∈ ℤ, Q(√d) ≃ₐ[ℚ] Q(√z)`. -/
theorem Qsqrtd_iso_int_param (d : ℚ) :
    ∃ z : ℤ, Nonempty (Qsqrtd d ≃ₐ[ℚ] Qsqrtd (z : ℚ)) := by
  obtain ⟨m, n, hn0, hd⟩ : ∃ m n : ℤ, n ≠ 0 ∧ d = m / n := by
    have hd := ne_of_gt (Rat.den_pos d)
    exact ⟨d.num, d.den, Int.ofNat_ne_zero.mpr hd, (Rat.num_div_den d).symm⟩
  use m * n
  have ha : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  have hrescale : Qsqrtd d ≃ₐ[ℚ] Qsqrtd (n ^ 2 * d) := Qsqrtd.rescale d n ha
  have heq : (n : ℚ) ^ 2 * d = m * n := by
    rw [hd]
    field_simp [mul_assoc]
  have hcast : (m * n : ℚ) = (m * n : ℤ) := (Int.cast_mul m n).symm
  exact ⟨hrescale.trans (AlgEquiv.cast (by rw [heq, hcast]))⟩

/-- Every quadratic field `Q(√d)` is isomorphic to one with a squarefree integer
parameter: `∃ z ∈ ℤ, Squarefree z ∧ Q(√d) ≃ₐ[ℚ] Q(√z)`. -/
theorem Qsqrtd_iso_squarefree_int_param {d : ℤ} (hd : d ≠ 0) :
    ∃ z : ℤ, Squarefree z ∧ Nonempty (Qsqrtd (d : ℚ) ≃ₐ[ℚ] Qsqrtd (z : ℚ)) := by
  obtain ⟨a, b, heq, ha⟩ := Nat.sq_mul_squarefree d.natAbs
  have hb : b ≠ 0 := by
    intro hb
    subst hb
    simp at heq
    exact hd (Int.natAbs_eq_zero.mp heq.symm)
  refine ⟨d.sign * ↑a, ?_, ?_⟩
  · rw [← Int.squarefree_natAbs]
    rwa [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hd, Int.natAbs_natCast, one_mul]
  · have hbQ : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb
    have hrescale := Qsqrtd.rescale (↑d) (↑b)⁻¹ (inv_ne_zero hbQ)
    have hd_int : d = d.sign * (↑b ^ 2 * ↑a) := by
      conv_lhs => rw [(Int.sign_mul_natAbs d).symm]
      congr 1
      exact_mod_cast heq.symm
    have hkey : ((↑b : ℚ)⁻¹) ^ 2 * (↑d : ℚ) = ↑(d.sign * (↑a : ℤ)) := by
      have hd_rat : (d : ℚ) = (d.sign : ℚ) * ((b : ℚ) ^ 2 * (a : ℚ)) := by
        exact_mod_cast hd_int
      rw [hd_rat]
      field_simp
      push_cast
      rfl
    exact ⟨hrescale.trans
      (AlgEquiv.cast (A := fun d => QuadraticAlgebra ℚ d 0) hkey)⟩

/-! ## Helper Lemmas -/

/-- `-1` is not a square in `ℚ`. -/
lemma not_isSquare_neg_one_rat : ¬ IsSquare (- (1 : ℚ)) := by
  rintro ⟨r, hr⟩
  have hnonneg : 0 ≤ r ^ 2 := sq_nonneg r
  nlinarith [hr, hnonneg]

/-- A squarefree integer that is a perfect square must equal `1`. -/
lemma eq_one_of_squarefree_isSquare {m : ℤ}
    (hsm : Squarefree m) (hsq : IsSquare m) : m = 1 := by
  obtain ⟨r, rfl⟩ := hsq
  have hnonneg : 0 ≤ r * r := mul_self_nonneg r
  have hu := hsm.isUnit_of_isSquare ⟨r, rfl⟩
  rcases Int.isUnit_iff.mp hu with h | h
  · exact h
  · linarith

/-- A squarefree natural number that is a perfect square (as an integer) must equal `1`. -/
lemma nat_eq_one_of_squarefree_intcast_of_isSquare (m : ℕ)
    (hsm : Squarefree (m : ℤ)) (hsq : IsSquare (m : ℤ)) : m = 1 := by
  have hmz : (m : ℤ) = 1 :=
    eq_one_of_squarefree_isSquare hsm hsq
  exact_mod_cast hmz

/-- If `d₁/d₂` is a rational square and `d₂` is squarefree, then `d₂ ∣ d₁`. -/
lemma int_dvd_of_ratio_square (d₁ d₂ : ℤ) (hd₂ : d₂ ≠ 0)
    (hsq_d₂ : Squarefree d₂) (hr : IsSquare ((d₁ : ℚ) / (d₂ : ℚ))) : d₂ ∣ d₁ := by
  have hsq_den_nat : IsSquare (((d₁ : ℚ) / (d₂ : ℚ)).den) := (Rat.isSquare_iff.mp hr).2
  have hsq_den_int : IsSquare ((((d₁ : ℚ) / (d₂ : ℚ)).den : ℤ)) := by
    rcases hsq_den_nat with ⟨n, hn⟩
    refine ⟨(n : ℤ), by exact_mod_cast hn⟩
  have hden_dvd : ((((d₁ : ℚ) / (d₂ : ℚ)).den : ℤ)) ∣ d₂ := by
    simpa [← Rat.divInt_eq_div] using (Rat.den_dvd d₁ d₂)
  have hsqf_den_int : Squarefree ((((d₁ : ℚ) / (d₂ : ℚ)).den : ℤ)) :=
    Squarefree.squarefree_of_dvd hden_dvd hsq_d₂
  have hden1_nat : ((d₁ : ℚ) / (d₂ : ℚ)).den = 1 :=
    nat_eq_one_of_squarefree_intcast_of_isSquare _ hsqf_den_int hsq_den_int
  exact (Rat.den_div_intCast_eq_one_iff d₁ d₂ hd₂).1 hden1_nat

/-- If two squarefree integers are related by `d₁ = d₂ · r²` for rational `r`,
then `d₁ = d₂`. -/
lemma squarefree_eq_of_rat_sq_mul {d₁ d₂ : ℤ}
    (hd₁ : Squarefree d₁) (hd₂ : Squarefree d₂)
    {r : ℚ} (hr : (d₁ : ℚ) = d₂ * r ^ 2) : d₁ = d₂ := by
  have hd₁0 : d₁ ≠ 0 := Squarefree.ne_zero hd₁
  have hd₂0 : d₂ ≠ 0 := Squarefree.ne_zero hd₂
  have hd₁Q : (d₁ : ℚ) ≠ 0 := by exact_mod_cast hd₁0
  have hd₂Q : (d₂ : ℚ) ≠ 0 := by exact_mod_cast hd₂0
  have hratio : IsSquare ((d₁ : ℚ) / (d₂ : ℚ)) := by
    refine ⟨r, ?_⟩
    calc
      (d₁ : ℚ) / (d₂ : ℚ) = ((d₂ : ℚ) * r ^ 2) / (d₂ : ℚ) := by simp [hr]
      _ = r ^ 2 := by field_simp [hd₂Q]
      _ = r * r := by ring
  have hratio' : IsSquare ((d₂ : ℚ) / (d₁ : ℚ)) := by
    rcases hratio with ⟨s, hs⟩
    refine ⟨s⁻¹, ?_⟩
    calc
      (d₂ : ℚ) / (d₁ : ℚ) = ((d₁ : ℚ) / (d₂ : ℚ))⁻¹ := by field_simp [hd₁Q, hd₂Q]
      _ = (s * s)⁻¹ := by simp [hs]
      _ = s⁻¹ * s⁻¹ := by
        have hs0 : s ≠ 0 := by
          intro hs0
          have : ((d₁ : ℚ) / (d₂ : ℚ)) = 0 := by simpa [hs0] using hs
          have hd10 : (d₁ : ℚ) = 0 := by
            field_simp [hd₂Q] at this
            simpa [mul_zero] using this
          exact hd₁Q hd10
        field_simp [hs0]
  have hd21 : d₂ ∣ d₁ := int_dvd_of_ratio_square d₁ d₂ hd₂0 hd₂ hratio
  have hd12 : d₁ ∣ d₂ := int_dvd_of_ratio_square d₂ d₁ hd₁0 hd₁ hratio'
  have hassoc : Associated d₁ d₂ := associated_of_dvd_dvd hd12 hd21
  rcases (Int.associated_iff.mp hassoc) with hEq | hNeg
  · exact hEq
  · have : ((d₁ : ℚ) / d₂) = -1 := by
      rw [hNeg]
      push_cast
      field_simp [hd₂Q]
    exfalso
    exact not_isSquare_neg_one_rat (by rwa [this] at hratio)

/-! ## Parameter Uniqueness -/

section ParamLevel

variable (d₁ d₂ : ℤ) [Fact (Squarefree d₁)] [Fact (d₁ ≠ 1)]
  [Fact (Squarefree d₂)] [Fact (d₂ ≠ 1)]

/-- The squarefree integer parameter of a quadratic field is unique:
    `ℚ(√d₁) ≃ₐ[ℚ] ℚ(√d₂)` with both squarefree and `≠ 1` implies `d₁ = d₂`. -/
theorem Qsqrtd.param_unique (φ : Qsqrtd (d₁ : ℚ) ≃ₐ[ℚ] Qsqrtd (d₂ : ℚ)) : d₁ = d₂ := by
  have hsf₁ : Squarefree d₁ := Fact.out
  have h1₁ : d₁ ≠ 1 := Fact.out
  have hsf₂ : Squarefree d₂ := Fact.out
  have _h1₂ : d₂ ≠ 1 := Fact.out
  set a := (φ ⟨0, 1⟩).re
  set b := (φ ⟨0, 1⟩).im
  have hε_sq : (⟨0, 1⟩ : Qsqrtd (d₁ : ℚ)) * ⟨0, 1⟩ = ⟨(d₁ : ℚ), 0⟩ := by
    ext <;> simp [QuadraticAlgebra.mk_mul_mk]
  have hφ_sq : φ ⟨0, 1⟩ * φ ⟨0, 1⟩ = ⟨(d₁ : ℚ), 0⟩ := by
    rw [← map_mul, hε_sq]
    show φ ⟨(d₁ : ℚ), 0⟩ = ⟨(d₁ : ℚ), 0⟩
    have hleft : (⟨(d₁ : ℚ), 0⟩ : Qsqrtd (d₁ : ℚ)) =
        algebraMap ℚ (Qsqrtd (d₁ : ℚ)) (d₁ : ℚ) := by
      ext <;> simp
    have hright : (⟨(d₁ : ℚ), 0⟩ : Qsqrtd (d₂ : ℚ)) =
        algebraMap ℚ (Qsqrtd (d₂ : ℚ)) (d₁ : ℚ) := by
      ext <;> simp
    rw [hleft, hright]
    exact φ.commutes (d₁ : ℚ)
  have hφ_eta : φ ⟨0, 1⟩ = ⟨a, b⟩ := by ext <;> rfl
  have hre : a ^ 2 + (d₂ : ℚ) * b ^ 2 = d₁ := by
    have := congr_arg QuadraticAlgebra.re hφ_sq
    rw [hφ_eta, QuadraticAlgebra.mk_mul_mk] at this; simp at this; nlinarith
  have him : 2 * a * b = 0 := by
    have := congr_arg QuadraticAlgebra.im hφ_sq
    rw [hφ_eta, QuadraticAlgebra.mk_mul_mk] at this; simp at this; linarith
  have hb : b ≠ 0 := by
    intro hb0; simp [hb0] at hre
    have : IsSquare ((d₁ : ℤ) : ℚ) := ⟨a, by nlinarith⟩
    exact not_isSquare_int_of_squarefree_ne_one hsf₁ h1₁
      (Rat.isSquare_intCast_iff.mp this)
  have ha : a = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact (mul_eq_zero.mp h).resolve_left (by norm_num)
    · exact absurd h hb
  have hr : (d₁ : ℚ) = d₂ * b ^ 2 := by nlinarith [hre, ha]
  exact squarefree_eq_of_rat_sq_mul hsf₁ hsf₂ hr

end ParamLevel
