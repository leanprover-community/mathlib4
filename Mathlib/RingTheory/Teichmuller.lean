/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.LinearAlgebra.SModEq.Prime
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Perfection

/-! # Teichmüller map

Let `R` be an `I`-adically complete ring, and `p` be a prime number with `p ∈ I`.

Then there is a canonical map `Perfection (R ⧸ I) p →*₀ R` that we shall call
`Perfection.teichmuller`, such that it composed with the quotient map `R →+* R ⧸ I` is the
"0-th coefficient" map `Perfection (R ⧸ I) p →+* R ⧸ I`.

-/

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] {I : Ideal R} [CharP (R ⧸ I) p]

namespace Ring.Perfection

open _root_.Perfection

/-- An auxiliary sequence to define the Teichmüller map. The `(n + 1)`-st term is the `p^n`-th
power of an arbitrary lift in `R` of the `n`-th component from the perfection of `R ⧸ I`. -/
noncomputable def teichmullerAux (x : Perfection (R ⧸ I) p) : ℕ → R
  | 0 => 1
  | n+1 => (coeff _ p n x).out ^ p ^ n

theorem teichmullerAux_sModEq (x : Perfection (R ⧸ I) p) (m : ℕ) :
    x.teichmullerAux (m + 1) ≡ x.teichmullerAux m [SMOD I ^ m] := by
  obtain _ | m := m
  · simp
  rw [teichmullerAux, pow_succ' p, pow_mul]
  exact .pow_prime_pow (CharP.mem p I) <| by simp [SModEq.ideal, coeff_pow_p']

variable [IsAdicComplete I R]

theorem exists_teichmullerFun (x : Perfection (R ⧸ I) p) :
    ∃ y : R, ∀ n, x.teichmullerAux n ≡ y [SMOD I ^ n • (⊤ : Ideal R)] := by
  refine IsPrecomplete.exists_limit_of_succ _ fun m ↦ ?_
  simpa using teichmullerAux_sModEq x m

/-- Given an `I`-adically complete ring `R`, where `p ∈ I`, this is the underlying function of the
Teichmüller map. It is defined as the limit of `p^n`-th powers of arbitrary lifts in `R` of the
`n`-th component from the perfection of `R ⧸ I`. -/
noncomputable def teichmullerFun (x : Perfection (R ⧸ I) p) : R :=
  (exists_teichmullerFun x).choose

theorem teichmullerFun_sModEq {x : Perfection (R ⧸ I) p} {y : R} {n : ℕ}
    (h : Ideal.Quotient.mk I y = coeff _ p n x) :
    teichmullerFun x ≡ y ^ p ^ n [SMOD I ^ (n + 1)] := by
  have := (exists_teichmullerFun x).choose_spec (n + 1)
  rw [smul_eq_mul, Ideal.mul_top] at this
  exact this.symm.trans <| SModEq.pow_prime_pow (CharP.mem p I) <| by simp [SModEq.ideal, h]

theorem teichmullerFun_spec {x : Perfection (R ⧸ I) p} {y : R}
    (h : ∃ N, ∀ n ≥ N, ∃ z, Ideal.Quotient.mk I z = coeff _ p n x ∧
      z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]) :
    teichmullerFun x = y := by
  obtain ⟨N, h⟩ := h
  refine (IsHausdorff.eq_iff_smodEq (I := I)).mpr fun n ↦ ?_
  rw [smul_eq_mul, Ideal.mul_top]
  obtain hn | hn := le_total n N
  · obtain ⟨z, hz₁, hz₂⟩ := h N le_rfl
    exact ((teichmullerFun_sModEq hz₁).trans hz₂).mono <| Ideal.pow_le_pow_right (by omega)
  · obtain ⟨z, hz₁, hz₂⟩ := h n hn
    exact ((teichmullerFun_sModEq hz₁).trans hz₂).mono <| Ideal.pow_le_pow_right (by omega)

variable (p I) in
/-- Given an `I`-adically complete ring `R`, and a prime number `p` with `p ∈ I`, this is the
multiplicative map from `Perfection (R ⧸ I) p` to `R` itself. Specifically, it is defined as the
limit of `p^n`-th powers of arbitrary lifts in `R` of the `n`-th component from the perfection of
`R ⧸ I`. -/
noncomputable def teichmuller : Perfection (R ⧸ I) p →* R where
  toFun := teichmullerFun
  map_one' := teichmullerFun_spec ⟨0, fun _ _ ↦ ⟨1, by simp; rfl⟩⟩
  map_mul' x y := by
    refine teichmullerFun_spec ⟨0, fun n _ ↦ ?_⟩
    refine ⟨(coeff _ p n x).out * (coeff _ p n y).out, by simp, ?_⟩
    rw [mul_pow]
    refine (teichmullerFun_sModEq ?_).symm.mul (teichmullerFun_sModEq ?_).symm <;> simp

theorem teichmuller_sModEq {x : Perfection (R ⧸ I) p} {y : R} {n : ℕ}
    (h : Ideal.Quotient.mk I y = coeff _ p n x) :
    teichmuller p I x ≡ y ^ p ^ n [SMOD I ^ (n + 1)] :=
  teichmullerFun_sModEq h

theorem teichmuller_spec {x : Perfection (R ⧸ I) p} {y : R}
    (h : ∃ N, ∀ n ≥ N, ∃ z, Ideal.Quotient.mk I z = coeff _ p n x ∧
      z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]) :
    teichmuller p I x = y :=
  teichmullerFun_spec h

@[simp] theorem teichmuller_zero : teichmuller p I 0 = 0 :=
  have : p ≠ 0 := Nat.Prime.ne_zero Fact.out
  teichmuller_spec ⟨0, fun n _ ↦ ⟨0, by simp [zero_pow (pow_ne_zero n this)]; rfl⟩⟩

theorem mk_teichmuller (x : Perfection (R ⧸ I) p) :
    Ideal.Quotient.mk I (teichmuller p I x) = coeff _ p 0 x := by
  have := teichmuller_sModEq <| Ideal.Quotient.mk_out <| coeff _ p 0 x
  simp_rw [zero_add, pow_one] at this
  simpa [SModEq.ideal] using this

variable (p I) in
theorem mk_comp_teichmuller :
    (Ideal.Quotient.mk I : _ →* _).comp (teichmuller p I) =
      (MonoidHomClass.toMonoidHom <| coeff (R ⧸ I) p 0) :=
  MonoidHom.ext mk_teichmuller

variable (p I) in
theorem mk_comp_teichmuller' :
    Ideal.Quotient.mk I ∘ (teichmuller p I) = coeff (R ⧸ I) p 0 :=
  funext mk_teichmuller

end Ring.Perfection
