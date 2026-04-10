/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.LinearAlgebra.SModEq.Basic
public import Mathlib.LinearAlgebra.SModEq.Pow
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Perfection

/-! # Teichmüller map

Let `R` be an `I`-adically complete ring, and `p` be a prime number with `p ∈ I`.

Then there is a canonical map `Perfection (R ⧸ I) p →*₀ R` that we shall call
`Perfection.teichmuller`, such that it composed with the quotient map `R →+* R ⧸ I` is the
"0-th coefficient" map `Perfection (R ⧸ I) p →+* R ⧸ I`.

-/

@[expose] public section

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] {I : Ideal R} [CharP (R ⧸ I) p]

namespace Perfection

/-- An auxiliary sequence to define the Teichmüller map. The `(n + 1)`-st term is the `p^n`-th
power of an arbitrary lift in `R` of the `n`-th component from the perfection of `R ⧸ I`. -/
noncomputable def teichmullerAux (x : Perfection (R ⧸ I) p) : ℕ → R
  | 0 => 1
  | n+1 => (coeff _ p n x).out ^ p ^ n

theorem teichmullerAux_sModEq (x : Perfection (R ⧸ I) p) (m : ℕ) :
    teichmullerAux x m ≡ teichmullerAux x (m + 1) [SMOD I ^ m] := by
  obtain _ | m := m
  · simp
  symm
  rw [teichmullerAux, pow_succ' p, pow_mul]
  exact .pow_pow_add_one (I.natCast_mem_of_charP_quotient p) (m := m) <| by
    simp [SModEq.idealQuotientMk, coeff_pow_p']

/-- `teichmullerAux` as an adic Cauchy sequence. -/
noncomputable def teichmullerCauchy (x : Perfection (R ⧸ I) p) :
    AdicCompletion.AdicCauchySequence I R :=
  .mk _ _ (teichmullerAux x) <| by simpa using teichmullerAux_sModEq x

section IsPrecomplete
variable [IsPrecomplete I R]

theorem exists_teichmullerFun (x : Perfection (R ⧸ I) p) :
    ∃ y : R, ∀ n, teichmullerAux x n ≡ y [SMOD I ^ n • (⊤ : Ideal R)] :=
  IsPrecomplete.prec' _ (teichmullerCauchy x).2

/-- Given an `I`-adically **pre**complete ring `R`, where `p ∈ I`, this is the underlying function
of the Teichmüller map. It is defined as the limit of `p^n`-th powers of arbitrary lifts in `R` of
the `n`-th component from the perfection of `R ⧸ I`.

The simp NF is `teichmuller₀` when `R` is `I`-adically complete. -/
noncomputable def teichmullerFun (x : Perfection (R ⧸ I) p) : R :=
  (exists_teichmullerFun x).choose

theorem teichmullerFun_sModEq {x : Perfection (R ⧸ I) p} {y : R} {n : ℕ}
    (h : Ideal.Quotient.mk I y = coeff _ p n x) :
    teichmullerFun x ≡ y ^ p ^ n [SMOD I ^ (n + 1)] := by
  have := (exists_teichmullerFun x).choose_spec (n + 1)
  rw [smul_eq_mul, Ideal.mul_top] at this
  exact this.symm.trans <| .pow_pow_add_one (I.natCast_mem_of_charP_quotient p) (m := n) <| by
    simp [SModEq.idealQuotientMk, h]

end IsPrecomplete

variable [IsAdicComplete I R]

theorem teichmullerFun_spec' {x : Perfection (R ⧸ I) p} {y : R}
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

theorem teichmullerFun_spec {x : Perfection (R ⧸ I) p} {y : R}
    (h : ∀ n, ∃ z, Ideal.Quotient.mk I z = coeff _ p n x ∧ z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]) :
    teichmullerFun x = y :=
  teichmullerFun_spec' ⟨0, fun n _ ↦ h n⟩

variable (p I) in
/-- Given an `I`-adically complete ring `R`, and a prime number `p` with `p ∈ I`, this is the
multiplicative map from `Perfection (R ⧸ I) p` to `R` itself. Specifically, it is defined as the
limit of `p^n`-th powers of arbitrary lifts in `R` of the `n`-th component from the perfection of
`R ⧸ I`.

The simp NF is `teichmuller₀`. -/
noncomputable def teichmuller : Perfection (R ⧸ I) p →* R where
  toFun := teichmullerFun
  map_one' := teichmullerFun_spec fun _ ↦ ⟨1, by simp⟩
  map_mul' x y := by
    refine teichmullerFun_spec fun n ↦ ?_
    refine ⟨(coeff _ p n x).out * (coeff _ p n y).out, by simp, ?_⟩
    rw [mul_pow]
    refine (teichmullerFun_sModEq ?_).symm.mul (teichmullerFun_sModEq ?_).symm <;> simp

theorem teichmuller_sModEq {x : Perfection (R ⧸ I) p} {y : R} {n : ℕ}
    (h : Ideal.Quotient.mk I y = coeff _ p n x) :
    teichmuller p I x ≡ y ^ p ^ n [SMOD I ^ (n + 1)] :=
  teichmullerFun_sModEq h

theorem teichmuller_spec' {x : Perfection (R ⧸ I) p} {y : R}
    (h : ∃ N, ∀ n ≥ N, ∃ z, Ideal.Quotient.mk I z = coeff _ p n x ∧
      z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]) :
    teichmuller p I x = y :=
  teichmullerFun_spec' h

theorem teichmuller_spec {x : Perfection (R ⧸ I) p} {y : R}
    (h : ∀ n, ∃ z, Ideal.Quotient.mk I z = coeff _ p n x ∧ z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]) :
    teichmuller p I x = y :=
  teichmullerFun_spec h

theorem teichmuller_zero : teichmuller p I 0 = 0 :=
  have : p ≠ 0 := Nat.Prime.ne_zero Fact.out
  teichmuller_spec fun n ↦ ⟨0, by simp [zero_pow (pow_ne_zero n this)]⟩

variable (p I) in
/-- `teichmuller` as a `MonoidWithZeroHom`. This is the simp NF. -/
noncomputable def teichmuller₀ : Perfection (R ⧸ I) p →*₀ R where
  __ := teichmuller p I
  map_zero' := teichmuller_zero

@[simp] lemma teichmuller_eq_teichmuller₀_toMonoidHom :
    teichmuller p I = (teichmuller₀ p I).toMonoidHom := rfl

@[simp] lemma coe_teichmuller_eq_teichmuller₀ :
    ⇑(teichmuller p I) = teichmuller₀ p I := rfl

@[simp] lemma teichmullerFun_eq_teichmuller₀ :
    teichmullerFun = teichmuller₀ p I := rfl

theorem teichmuller₀_sModEq {x : Perfection (R ⧸ I) p} {y : R} {n : ℕ}
    (h : Ideal.Quotient.mk I y = coeff _ p n x) :
    teichmuller₀ p I x ≡ y ^ p ^ n [SMOD I ^ (n + 1)] :=
  teichmullerFun_sModEq h

theorem teichmuller₀_spec' {x : Perfection (R ⧸ I) p} {y : R}
    (h : ∃ N, ∀ n ≥ N, ∃ z, Ideal.Quotient.mk I z = coeff _ p n x ∧
      z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]) :
    teichmuller₀ p I x = y :=
  teichmullerFun_spec' h

theorem teichmuller₀_spec {x : Perfection (R ⧸ I) p} {y : R}
    (h : ∀ n, ∃ z, Ideal.Quotient.mk I z = coeff _ p n x ∧ z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]) :
    teichmuller₀ p I x = y :=
  teichmullerFun_spec h

@[simp] theorem teichmuller₀_mapMonoidHom_idealQuotientMk {x : Perfection R p} :
    teichmuller₀ p I (mapMonoidHom p (Ideal.Quotient.mk I) x) = coeffMonoidHom R p 0 x :=
  teichmuller₀_spec fun n ↦ ⟨coeffMonoidHom R p n x, by simp⟩

theorem mk_teichmuller (x : Perfection (R ⧸ I) p) :
    Ideal.Quotient.mk I (teichmuller p I x) = coeff _ p 0 x := by
  have := teichmuller_sModEq <| Ideal.Quotient.mk_out <| coeff _ p 0 x
  simp_rw [zero_add, pow_one] at this
  simpa [SModEq.idealQuotientMk] using this

@[simp] theorem mk_teichmuller₀ (x : Perfection (R ⧸ I) p) :
    Ideal.Quotient.mk I (teichmuller₀ p I x) = coeff _ p 0 x := mk_teichmuller _

variable (p I) in
theorem mk_comp_teichmuller :
    (Ideal.Quotient.mk I : _ →* _).comp (teichmuller p I) =
      (coeff (R ⧸ I) p 0 : Perfection (R ⧸ I) p →* R ⧸ I) :=
  MonoidHom.ext mk_teichmuller

variable (p I) in
theorem mk_comp_teichmuller₀ :
    (Ideal.Quotient.mk I : _ →*₀ _).comp (teichmuller₀ p I) =
      (coeff (R ⧸ I) p 0 : Perfection (R ⧸ I) p →*₀ R ⧸ I) :=
  MonoidWithZeroHom.ext mk_teichmuller

variable (p I) in
theorem mk_comp_teichmuller' :
    Ideal.Quotient.mk I ∘ (teichmuller p I) = coeff (R ⧸ I) p 0 :=
  funext mk_teichmuller

/-- If `R` is `I`-adically complete and `R ⧸ I` has characteristic `p`, then
`Perfection R p` and `Perfection (R ⧸ I) p` are isomorphic as monoids.

Note that `Perfection R p` is generally not a ring, and the forward map is induced by
the quotient map, and the backwards map is constructed using the Teichmüller map. -/
noncomputable def quotientMulEquiv (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] (I : Ideal R) [CharP (R ⧸ I) p] [IsAdicComplete I R] :
    Perfection R p ≃* Perfection (R ⧸ I) p := MonoidHom.toMulEquiv
  (mapMonoidHom _ <| Ideal.Quotient.mk I)
  (liftMonoidHom p _ _ <| teichmuller p I)
  ((liftMonoidHom p _ _).symm.injective <| by ext; simp)
  ((liftMonoidHom p _ _).symm.injective <| by ext; simp)

@[simp] theorem coeff_quotientMulEquiv (x : Perfection R p) (n : ℕ) :
    coeff (R ⧸ I) p n (quotientMulEquiv p I x) = Ideal.Quotient.mk I (coeffMonoidHom R p n x) := rfl

@[simp] theorem coeff_zero_symm_quotientMulEquiv (x : Perfection (R ⧸ I) p) :
    coeffMonoidHom R p 0 (quotientMulEquiv p I |>.symm x) = teichmuller₀ p I x := by
  simp [quotientMulEquiv]

end Perfection
