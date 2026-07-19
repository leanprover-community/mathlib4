/-
Copyright (c) 2026 Junji Hashimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junji Hashimoto
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Complex.Module

/-!
# The Clifford algebra of Euclidean `n`-space and its complex structure

We study `Cl(n,0)`, the Clifford algebra of `EuclideanSpace ℝ (Fin n)` with the quadratic
form `x ↦ ⟪x, x⟫_ℝ`.

The pseudoscalar `ω = e₀ * ⋯ * eₙ₋₁` satisfies `ω * ω = (-1) ^ (n.choose 2)` and commutes
with every element up to the sign `(-1) ^ (n - 1)`. Consequently, for odd `n` it is
*central*, and for `n ≡ 3 [MOD 4]` it is moreover a square root of `-1`, hence by
`Complex.liftAux` it induces an `Algebra ℂ` structure on the Clifford algebra. This complex
structure is what makes the Clifford–Fourier transform (Ebling–Scheuermann) an instance of
the ordinary vector-valued Fourier transform; this is used in a follow-up PR to derive
Plancherel's theorem for it from the vector-valued `L²` Fourier theory.

## Main definitions

* `CliffordAlgebra.Euclidean.Q`: the norm-squared quadratic form on `EuclideanSpace ℝ (Fin n)`.
* `CliffordAlgebra.Euclidean.pseudoscalar`: the pseudoscalar `ω`.
* `CliffordAlgebra.Euclidean.instAlgebraComplex`: for `n ≡ 3 [MOD 4]` (as a `Fact`), the
  `Algebra ℂ` structure induced by `ω` (a scoped instance).

## Main statements

* `CliffordAlgebra.Euclidean.pseudoscalar_mul_pseudoscalar'`:
  `ω * ω = (-1) ^ (n.choose 2)`.
* `CliffordAlgebra.Euclidean.pseudoscalar_mul_pseudoscalar`: `ω * ω = -1` for
  `n ≡ 3 [MOD 4]`.
* `CliffordAlgebra.Euclidean.commute_pseudoscalar`: `ω` is central for odd `n`.

-/

@[expose] public section

noncomputable section

open CliffordAlgebra
open scoped RealInnerProductSpace

namespace CliffordAlgebra.Euclidean

variable (n : ℕ)

/-- The norm-squared quadratic form on Euclidean `n`-space. -/
def Q : QuadraticForm ℝ (EuclideanSpace ℝ (Fin n)) :=
  LinearMap.BilinMap.toQuadraticMap (innerₗ _)

@[simp] theorem Q_apply (x : EuclideanSpace ℝ (Fin n)) : Q n x = ⟪x, x⟫ := rfl

variable {n}

/-- The `i`-th standard generator of Euclidean `n`-space. -/
def e (i : Fin n) : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1

theorem inner_e_e_of_ne {i j : Fin n} (h : i ≠ j) : ⟪e i, e j⟫ = 0 := by
  simp [e, EuclideanSpace.inner_single_left, h.symm]

@[simp] theorem Q_e (i : Fin n) : Q n (e i) = 1 := by
  simp [e]

theorem isOrtho_e {i j : Fin n} (h : i ≠ j) : (Q n).IsOrtho (e i) (e j) := by
  rw [QuadraticMap.isOrtho_def]
  simp only [Q_apply, real_inner_add_add_self, inner_e_e_of_ne h]
  ring

/-- The `i`-th standard generator of the Clifford algebra `Cl(n,0)`. -/
def γ (i : Fin n) : CliffordAlgebra (Q n) := ι (Q n) (e i)

@[simp] theorem γ_mul_γ_self (i : Fin n) : γ i * γ i = 1 := by
  rw [γ, ι_sq_scalar, Q_e, map_one]

theorem γ_mul_γ_of_ne {i j : Fin n} (h : i ≠ j) : γ i * γ j = -(γ j * γ i) :=
  ι_mul_ι_comm_of_isOrtho (isOrtho_e h)

@[simp] theorem γ_mul_γ_cancel (i : Fin n) (x : CliffordAlgebra (Q n)) :
    γ i * (γ i * x) = x := by
  rw [← mul_assoc, γ_mul_γ_self, one_mul]

/-! ### Sign computations

Moving a generator through a product of `k` distinct other generators produces the
sign `(-1) ^ k`. -/

theorem γ_mul_prod (i : Fin n) {l : List (Fin n)} (h : i ∉ l) :
    γ i * (l.map γ).prod = ((-1 : ℝ) ^ l.length) • ((l.map γ).prod * γ i) := by
  induction l with
  | nil => simp
  | cons j t ih =>
    have hij : i ≠ j := fun hf => h (hf ▸ List.mem_cons_self ..)
    have hit : i ∉ t := fun hm => h (List.mem_cons_of_mem _ hm)
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    calc γ i * (γ j * (t.map γ).prod)
        = (γ i * γ j) * (t.map γ).prod := by rw [mul_assoc]
      _ = -(γ j * (γ i * (t.map γ).prod)) := by
          rw [γ_mul_γ_of_ne hij, neg_mul, mul_assoc]
      _ = -(γ j * (((-1 : ℝ) ^ t.length) • ((t.map γ).prod * γ i))) := by rw [ih hit]
      _ = ((-1 : ℝ) ^ (t.length + 1)) • (γ j * ((t.map γ).prod * γ i)) := by
          rw [mul_smul_comm, ← neg_smul, pow_succ, mul_neg_one]
      _ = ((-1 : ℝ) ^ (t.length + 1)) • (γ j * (t.map γ).prod * γ i) := by
          rw [mul_assoc]

theorem prod_mul_γ (i : Fin n) {l : List (Fin n)} (h : i ∉ l) :
    (l.map γ).prod * γ i = ((-1 : ℝ) ^ l.length) • (γ i * (l.map γ).prod) := by
  rw [γ_mul_prod i h, smul_smul, ← pow_add, Even.neg_one_pow ⟨l.length, rfl⟩, one_smul]

/-- The square of a product of distinct generators. -/
theorem prod_sq {l : List (Fin n)} (h : l.Nodup) :
    (l.map γ).prod * (l.map γ).prod = ((-1 : ℝ) ^ l.length.choose 2) • 1 := by
  induction l with
  | nil => simp
  | cons j t ih =>
    obtain ⟨hjt, ht⟩ := List.nodup_cons.mp h
    simp only [List.map_cons, List.prod_cons]
    calc (γ j * (t.map γ).prod) * (γ j * (t.map γ).prod)
        = γ j * (((t.map γ).prod * γ j) * (t.map γ).prod) := by
          rw [mul_assoc, ← mul_assoc (t.map γ).prod]
      _ = γ j * ((((-1 : ℝ) ^ t.length) • (γ j * (t.map γ).prod)) * (t.map γ).prod) := by
          rw [prod_mul_γ j hjt]
      _ = ((-1 : ℝ) ^ t.length) • ((t.map γ).prod * (t.map γ).prod) := by
          rw [smul_mul_assoc, mul_smul_comm, mul_assoc, γ_mul_γ_cancel]
      _ = ((-1 : ℝ) ^ (t.length + t.length.choose 2)) • 1 := by
          rw [ih ht, smul_smul, ← pow_add]
      _ = ((-1 : ℝ) ^ (j :: t).length.choose 2) • 1 := by
          rw [List.length_cons, show (2 : ℕ) = 1 + 1 from rfl,
            Nat.choose_succ_succ' t.length 1, Nat.choose_one_right]

/-- Moving a generator through a product of distinct generators *containing it*
produces the sign `(-1) ^ (length - 1)`. -/
theorem γ_mul_prod_mem (i : Fin n) {l : List (Fin n)} (hnd : l.Nodup) (him : i ∈ l) :
    γ i * (l.map γ).prod = ((-1 : ℝ) ^ (l.length - 1)) • ((l.map γ).prod * γ i) := by
  induction l with
  | nil => simp at him
  | cons j t ih =>
    obtain ⟨hjt, ht⟩ := List.nodup_cons.mp hnd
    simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.add_sub_cancel]
    rcases List.mem_cons.mp him with rfl | hit
    · -- `i = j`: cancellation on both sides
      rw [γ_mul_γ_cancel, mul_assoc, prod_mul_γ i hjt, mul_smul_comm, γ_mul_γ_cancel,
        smul_smul, ← pow_add, Even.neg_one_pow ⟨t.length, rfl⟩, one_smul]
    · -- `i ≠ j`, `i ∈ t`
      have hij : i ≠ j := fun hf => hjt (hf ▸ hit)
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (List.length_pos_of_mem hit).ne'
      calc γ i * (γ j * (t.map γ).prod)
          = -(γ j * (γ i * (t.map γ).prod)) := by
            rw [← mul_assoc, γ_mul_γ_of_ne hij, neg_mul, mul_assoc]
        _ = -(γ j * (((-1 : ℝ) ^ (t.length - 1)) • ((t.map γ).prod * γ i))) := by
            rw [ih ht hit]
        _ = ((-1 : ℝ) ^ t.length) • (γ j * ((t.map γ).prod * γ i)) := by
            rw [mul_smul_comm, ← neg_smul, hm, Nat.succ_sub_one, Nat.succ_eq_add_one,
              pow_succ, mul_neg_one]
        _ = ((-1 : ℝ) ^ t.length) • (γ j * (t.map γ).prod * γ i) := by rw [mul_assoc]

/-! ### The pseudoscalar -/

variable (n) in
/-- The pseudoscalar `ω = e₀ ⋯ eₙ₋₁` of `Cl(n,0)`. -/
def pseudoscalar : CliffordAlgebra (Q n) := ((List.finRange n).map γ).prod

/-- The square of the pseudoscalar of `Cl(n,0)` is `(-1) ^ (n.choose 2)`. -/
theorem pseudoscalar_mul_pseudoscalar' :
    pseudoscalar n * pseudoscalar n = ((-1 : ℝ) ^ n.choose 2) • 1 := by
  simpa [pseudoscalar] using prod_sq (List.nodup_finRange n)

theorem γ_mul_pseudoscalar (i : Fin n) :
    γ i * pseudoscalar n = ((-1 : ℝ) ^ (n - 1)) • (pseudoscalar n * γ i) := by
  simpa [pseudoscalar] using
    γ_mul_prod_mem i (List.nodup_finRange n) (List.mem_finRange i)

/-- For odd `n`, the pseudoscalar commutes with every generator. -/
theorem commute_pseudoscalar_γ (hn : Odd n) (i : Fin n) :
    Commute (pseudoscalar n) (γ i) := by
  have h := γ_mul_pseudoscalar i
  rw [Even.neg_one_pow (Nat.Odd.sub_odd hn odd_one), one_smul] at h
  exact h.symm

theorem commute_pseudoscalar_ι (hn : Odd n) (x : EuclideanSpace ℝ (Fin n)) :
    Commute (pseudoscalar n) (ι (Q n) x) := by
  have hx : (∑ i, x i • e i) = x := by
    simpa only [e, PiLp.basisFun_repr, PiLp.basisFun_apply]
      using (PiLp.basisFun 2 ℝ (Fin n)).sum_repr x
  rw [← hx, map_sum]
  exact Commute.sum_right _ _ _ fun i _ => by
    rw [map_smul]
    exact (commute_pseudoscalar_γ hn i).smul_right (x i)

/-- For odd `n`, the pseudoscalar of `Cl(n,0)` is central. -/
theorem commute_pseudoscalar (hn : Odd n) (a : CliffordAlgebra (Q n)) :
    Commute (pseudoscalar n) a := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => exact Algebra.commute_algebraMap_right r _
  | ι x => exact commute_pseudoscalar_ι hn x
  | mul a b ha hb => exact ha.mul_right hb
  | add a b ha hb => exact ha.add_right hb

/-! ### The complex structure for `n ≡ 2, 3 [MOD 4]`

For `n ≡ 2, 3 [MOD 4]` the pseudoscalar squares to `-1`, so *left multiplication* by
it is a complex structure, making `Cl(n,0)` a complex vector space with
`z • a = complexLift n z * a`. No commutation hypothesis is needed for a module
structure (in contrast to an `Algebra ℂ` structure); this covers the non-central case
`n ≡ 2 [MOD 4]` — e.g. the two-dimensional Clifford–Fourier transform — where the
pseudoscalar anticommutes with vectors. -/

instance factOr_of_factTwo [h : Fact (n % 4 = 2)] : Fact (n % 4 = 2 ∨ n % 4 = 3) :=
  ⟨Or.inl h.out⟩

instance factOr_of_factThree [h : Fact (n % 4 = 3)] : Fact (n % 4 = 2 ∨ n % 4 = 3) :=
  ⟨Or.inr h.out⟩

section SquareRootNegOne

variable [hn4 : Fact (n % 4 = 2 ∨ n % 4 = 3)]

theorem odd_choose_two : Odd (n.choose 2) := by
  rcases hn4.out with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 2 := ⟨n / 4, by omega⟩
    have h2 : (4 * k + 2) * (4 * k + 2 - 1) = ((2 * k + 1) * (4 * k + 1)) * 2 := by
      rw [show 4 * k + 2 - 1 = 4 * k + 1 by omega]; ring
    rw [Nat.choose_two_right, h2, Nat.mul_div_cancel _ two_pos]
    exact Nat.odd_mul.mpr ⟨⟨k, by ring⟩, ⟨2 * k, by ring⟩⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
    have h2 : (4 * k + 3) * (4 * k + 3 - 1) = ((4 * k + 3) * (2 * k + 1)) * 2 := by
      rw [show 4 * k + 3 - 1 = 4 * k + 2 by omega]; ring
    rw [Nat.choose_two_right, h2, Nat.mul_div_cancel _ two_pos]
    exact Nat.odd_mul.mpr ⟨⟨2 * k + 1, by ring⟩, ⟨k, by ring⟩⟩

/-- For `n ≡ 2, 3 [MOD 4]`, the pseudoscalar of `Cl(n,0)` is a square root of `-1`. -/
@[simp] theorem pseudoscalar_mul_pseudoscalar :
    pseudoscalar n * pseudoscalar n = -1 := by
  rw [pseudoscalar_mul_pseudoscalar', (odd_choose_two (n := n)).neg_one_pow, neg_smul, one_smul]

variable (n) in
/-- The real-algebra morphism `ℂ →ₐ[ℝ] Cl(n,0)` sending `I` to the pseudoscalar,
for `n ≡ 2, 3 [MOD 4]`. Its image is the commutative subalgebra `ℝ[ω]`, so no
centrality is needed. -/
def complexLift : ℂ →ₐ[ℝ] CliffordAlgebra (Q n) :=
  Complex.liftAux (pseudoscalar n) pseudoscalar_mul_pseudoscalar

theorem complexLift_apply (z : ℂ) :
    complexLift n z = algebraMap ℝ _ z.re + z.im • pseudoscalar n :=
  Complex.liftAux_apply _ _ z

/-- For `n ≡ 2, 3 [MOD 4]`, `Cl(n,0)` is a complex vector space, `I` acting by left
multiplication by the pseudoscalar. For `n ≡ 2 [MOD 4]` the pseudoscalar is *not*
central and this module structure does not extend to an `Algebra ℂ` structure
(see `CliffordAlgebra.Euclidean.algebraComplex` for `n ≡ 3 [MOD 4]`).

This is a scoped instance since it involves the choice of a pseudoscalar
(i.e. an orientation of `ℝⁿ`). -/
scoped instance instModuleComplex : Module ℂ (CliffordAlgebra (Q n)) :=
  Module.compHom _ (complexLift n).toRingHom

/-- The complex scalar action on `Cl(n,0)` is left multiplication by `complexLift`. -/
theorem complex_smul_def (z : ℂ) (a : CliffordAlgebra (Q n)) :
    z • a = complexLift n z * a := rfl

scoped instance : IsScalarTower ℝ ℂ (CliffordAlgebra (Q n)) :=
  ⟨fun r z a => by
    rw [complex_smul_def, complex_smul_def, map_smul, smul_mul_assoc]⟩

scoped instance : SMulCommClass ℂ ℂ (CliffordAlgebra (Q n)) :=
  ⟨fun z w a => by
    rw [complex_smul_def, complex_smul_def, complex_smul_def, complex_smul_def,
      ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, mul_comm z w]⟩

end SquareRootNegOne

/-! ### The `Algebra ℂ` structure for `n ≡ 3 [MOD 4]` -/

section Mod4Three

variable [hn3 : Fact (n % 4 = 3)]

theorem odd_of_fact_mod_four : Odd n := Nat.odd_iff.mpr (by have := hn3.out; omega)

variable (n) in
/-- For `n ≡ 3 [MOD 4]` the pseudoscalar is moreover *central*, so the complex module
structure `CliffordAlgebra.Euclidean.instModuleComplex` extends to an `Algebra ℂ`
structure. This is not an instance, to keep a single uniform `Module ℂ` path for
`n ≡ 2, 3 [MOD 4]`; activate it with `letI` where needed. -/
@[instance_reducible]
def algebraComplex : Algebra ℂ (CliffordAlgebra (Q n)) :=
  ((complexLift n).toRingHom).toAlgebra' fun z a => by
    have h : Commute (complexLift n z) a := by
      rw [complexLift_apply]
      exact (Algebra.commute_algebraMap_left _ _).add_left
        (((commute_pseudoscalar odd_of_fact_mod_four a)).smul_left z.im)
    exact h

end Mod4Three

end CliffordAlgebra.Euclidean
