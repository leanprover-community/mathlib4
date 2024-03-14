/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Data.Polynomial.Laurent
import Mathlib.Data.MvPolynomial.Basic

open MvPolynomial BigOperators Function AddMonoidAlgebra Finsupp
set_option autoImplicit false

noncomputable section

variable {σ R : Type*}

namespace MvPolynomial

def toFinsuppIso (σ R : Type*) [CommSemiring R] :
    MvPolynomial σ R ≃+* AddMonoidAlgebra R (σ →₀ ℕ) :=
  RingEquiv.refl _

end MvPolynomial

/-- The semiring of Laurent MvPolynomials with coefficients in the semiring `R`.
We denote it by `R[σ;T;T⁻¹]`.
The ring homomorphism `C : R →+* R[σ;T;T⁻¹]` includes `R` as the constant MvPolynomials. -/
abbrev MvLaurentPolynomial (σ R : Type*) [CommSemiring R] :=
  AddMonoidAlgebra R (σ →₀ ℤ)

@[nolint docBlame]
scoped[MvLaurentPolynomial] notation:9000 R "[" σ ";T;T⁻¹]" => MvLaurentPolynomial σ R

open MvLaurentPolynomial

-- Porting note: `ext` no longer applies `Finsupp.ext` automatically
@[ext]
theorem MvLaurentPolynomial.ext [CommSemiring R] {p q : R[σ;T;T⁻¹]} (h : ∀ a, p a = q a) : p = q :=
  Finsupp.ext h

/-- The ring homomorphism, taking a MvPolynomial with coefficients in `R` to a Laurent MvPolynomial
with coefficients in `R`. -/
def MvPolynomial.toLaurent [CommSemiring R] : MvPolynomial σ R →+* R[σ;T;T⁻¹] :=
  mapDomainRingHom R (Finsupp.mapRange.addMonoidHom Int.ofNatHom)

/-- This is not a simp lemma, as it is usually preferable to use the lemmas about `C` and `X`
instead. -/
theorem MvPolynomial.toLaurent_apply [CommSemiring R] (p : MvPolynomial σ R) :
    toLaurent p = Finsupp.mapDomain (Finsupp.mapRange Int.ofNat rfl) p :=
  rfl

/-- The `R`-algebra map, taking a MvPolynomial with coefficients in `R` to a Laurent MvPolynomial
with coefficients in `R`. -/
def MvPolynomial.toLaurentAlg [CommSemiring R] : MvPolynomial σ R →ₐ[R] R[σ;T;T⁻¹] :=
  mapDomainAlgHom R R (Finsupp.mapRange.addMonoidHom Int.ofNatHom)

@[simp] lemma MvPolynomial.coe_toLaurentAlg [CommSemiring R] :
    (toLaurentAlg : MvPolynomial σ R → R[σ;T;T⁻¹]) = toLaurent :=
  rfl

theorem MvPolynomial.toLaurentAlg_apply [CommSemiring R] (f : MvPolynomial σ R) :
    toLaurentAlg f = toLaurent f :=
  rfl

namespace MvLaurentPolynomial

section Semiring

variable [CommSemiring R]

theorem single_zero_one_eq_one : (Finsupp.single 0 1 : R[σ;T;T⁻¹]) = (1 : R[σ;T;T⁻¹]) :=
  rfl

/-!  ### The functions `C` and `T`. -/


/-- The ring homomorphism `C`, including `R` into the ring of Laurent MvPolynomials over `R` as
the constant Laurent MvPolynomials. -/
def C : R →+* R[σ;T;T⁻¹] :=
  singleZeroRingHom

theorem algebraMap_apply {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (r : R) :
    algebraMap R (MvLaurentPolynomial σ A) r = C (algebraMap R A r) :=
  rfl

/-- When we have `[CommSemiring R]`, the function `C` is the same as `algebraMap R R[σ;T;T⁻¹]`.
(But note that `C` is defined when `R` is not necessarily commutative, in which case
`algebraMap` is not available.)
-/
theorem C_eq_algebraMap {R : Type*} [CommSemiring R] (r : R) : C r = algebraMap R R[σ;T;T⁻¹] r :=
  rfl

theorem single_eq_C (r : R) : Finsupp.single (0 : σ →₀ ℤ) r = C r := rfl

/-@[simp] lemma C_apply (t : R) (n : ℤ) : C t n = if n = 0 then t else 0 := by
  rw [← single_eq_C, Finsupp.single_apply]; aesop-/

def T (i : σ) (n : ℤ) : R[σ;T;T⁻¹] := Finsupp.single (Finsupp.single i n) 1

/-@[simp] lemma T_apply (m n : ℤ) : (T n : R[σ;T;T⁻¹]) m = if n = m then 1 else 0 :=
  Finsupp.single_apply-/

@[simp]
theorem T_zero (i : σ) : (T i 0 : R[σ;T;T⁻¹]) = 1 := by
  simp only [T, Finsupp.single_zero]
  rfl

theorem T_add (i : σ) (m n : ℤ) : (T i (m + n) : R[σ;T;T⁻¹]) = T i m * T i n := by
  simp [T, single_mul_single]

theorem T_sub (i : σ) (m n : ℤ) : (T i (m - n) : R[σ;T;T⁻¹]) = T i m * T i (-n) := by
  rw [← T_add, sub_eq_add_neg]

@[simp]
theorem T_pow (i : σ) (m : ℤ) (n : ℕ) : (T i m ^ n : R[σ;T;T⁻¹]) = T i (n * m) := by
  rw [T, T, single_pow n, one_pow, Finsupp.smul_single, nsmul_eq_mul]

/-- The `simp` version of `mul_assoc`, in the presence of `T`'s. -/
@[simp]
theorem mul_T_assoc (i : σ) (f : R[σ;T;T⁻¹]) (m n : ℤ) : f * T i m * T i n = f * T i (m + n) := by
  simp [← T_add, mul_assoc]

@[simp]
theorem single_eq_C_mul_T (i : σ) (r : R) (n : ℤ) :
    (Finsupp.single (Finsupp.single i n) r : R[σ;T;T⁻¹]) = (C r * T i n : R[σ;T;T⁻¹]) := by
  simp [C, T, single_mul_single]

/-- `monomial s a` is the monomial with coefficient `a` and exponents given by `s`  -/
def monomial (s : σ →₀ ℤ) : R →ₗ[R] R[σ;T;T⁻¹] :=
  lsingle s

theorem single_eq_monomial (s : σ →₀ ℤ) (a : R) : Finsupp.single s a = monomial s a :=
  rfl

theorem mul_def (p q : R[σ;T;T⁻¹]) :
    p * q = p.sum fun m a => q.sum fun n b => monomial (m + n) (a * b) :=
  rfl

theorem C_mul_monomial (s : σ →₀ ℤ) (a a' : R) : C a * monomial s a' = monomial s (a * a') := by
  -- porting note: this `show` feels like defeq abuse, but I can't find the appropriate lemmas
  show AddMonoidAlgebra.single _ _ * AddMonoidAlgebra.single _ _ = AddMonoidAlgebra.single _ _
  simp [C_apply, single_mul_single]

theorem monomial_pow (s : σ →₀ ℤ) (a : R) (e : ℕ) : monomial s a ^ e = monomial (e • s) (a ^ e) :=
  AddMonoidAlgebra.single_pow e

@[simp]
theorem monomial_mul {s s' : σ →₀ ℤ} {a b : R} :
    monomial s a * monomial s' b = monomial (s + s') (a * b) :=
  AddMonoidAlgebra.single_mul_single

theorem T_eq_monomial (i : σ) (n : ℤ) :
    T i n = monomial (Finsupp.single i n) (1 : R) := rfl

theorem C_eq_monomial (r : R) :
    C r = monomial (0 : σ →₀ ℤ) r := rfl

theorem monomial_add_single {s : σ →₀ ℤ} {i : σ} {n : ℤ} {r : R} :
    monomial (s + Finsupp.single i n) r = monomial s r * T i n := by
  rw [T_eq_monomial, monomial_mul, mul_one]

theorem monomial_single_add {s : σ →₀ ℤ} {i : σ} {n : ℤ} {r : R} :
    monomial (Finsupp.single i n + s) r = T i n * monomial s r := by
  rw [T_eq_monomial, monomial_mul, one_mul]

theorem C_mul_T_eq_monomial {s : σ} {a : R} {n : ℤ} :
    C a * T s n = monomial (Finsupp.single s n) a := by
  rw [← zero_add (Finsupp.single s n), monomial_add_single]
  rfl

-- porting note: `simp` can prove this
theorem monomial_zero {s : σ →₀ ℤ} : monomial s (0 : R) = 0 :=
  Finsupp.single_zero _

/-@[simp]
theorem monomial_zero' : (monomial (0 : σ →₀ ℕ) : R → MvPolynomial σ R) = C :=
  rfl
#align mv_polynomial.monomial_zero' MvPolynomial.monomial_zero'
-/
@[simp]
theorem monomial_eq_zero {s : σ →₀ ℤ} {b : R} : monomial s b = 0 ↔ b = 0 :=
  Finsupp.single_eq_zero

@[simp]
theorem _root_.MvPolynomial.toLaurent_C_mul_T (n : σ →₀ ℕ) (r : R) :
    (toLaurent (MvPolynomial.monomial n r) : R[σ;T;T⁻¹])
      = monomial (Finsupp.mapRange Int.ofNat rfl n) r := by
  show Finsupp.mapDomain (Finsupp.mapRange Int.ofNat rfl) (Finsupp.single _ _) = _
  rw [Finsupp.mapDomain_single]
  rfl

@[simp]
theorem _root_.MvPolynomial.toLaurent_C (r : R) : toLaurent (σ := σ) (MvPolynomial.C r) = C r := by
  convert MvPolynomial.toLaurent_C_mul_T 0 r

/-@[simp]
theorem _root_.Polynomial.toLaurent_comp_C : toLaurent (R := R) ∘ MvPolynomial.C = C :=
  funext MvPolynomial.toLaurent_C-/

@[simp]
theorem _root_.MvPolynomial.toLaurent_X (n : σ) :
   (toLaurent (MvPolynomial.X n) : R[σ;T;T⁻¹]) = T n 1 := by
  show Finsupp.mapDomain _ (Finsupp.single _ _) = _
  rw [Finsupp.mapDomain_single]
  simp only [mapRange.addMonoidHom_apply, AddMonoidHom.coe_coe, mapRange_single, map_one,
    single_eq_C_mul_T, one_mul]
/-
-- @[simp] -- Porting note: simp can prove this
theorem _root_.Polynomial.toLaurent_one : (Polynomial.toLaurent : MvPolynomial σ R → R[σ;T;T⁻¹]) 1 = 1 :=
  map_one MvPolynomial.toLaurent
#align MvPolynomial.to_laurent_one MvPolynomial.toLaurent_one

-- @[simp] -- Porting note: simp can prove this
theorem _root_.Polynomial.toLaurent_C_mul_eq (r : R) (f : MvPolynomial σ R) :
    toLaurent (Polynomial.C r * f) = C r * toLaurent f := by
  simp only [_root_.map_mul, MvPolynomial.toLaurent_C]
set_option linter.uppercaseLean3 false in
#align MvPolynomial.to_laurent_C_mul_eq MvPolynomial.toLaurent_C_mul_eq

-- @[simp] -- Porting note: simp can prove this
theorem _root_.Polynomial.toLaurent_X_pow (n : ℕ) : toLaurent (X ^ n : MvPolynomial σ R) = T n := by
  simp only [map_pow, MvPolynomial.toLaurent_X, T_pow, mul_one]
set_option linter.uppercaseLean3 false in
#align MvPolynomial.to_laurent_X_pow MvPolynomial.toLaurent_X_pow

-- @[simp] -- Porting note: simp can prove this
theorem _root_.Polynomial.toLaurent_C_mul_X_pow (n : ℕ) (r : R) :
    toLaurent (Polynomial.C r * X ^ n) = C r * T n := by
  simp only [_root_.map_mul, MvPolynomial.toLaurent_C, MvPolynomial.toLaurent_X_pow]
set_option linter.uppercaseLean3 false in
#align MvPolynomial.to_laurent_C_mul_X_pow MvPolynomial.toLaurent_C_mul_X_pow
-/
instance invertibleT (i : σ) (n : ℤ) : Invertible (T i n : R[σ;T;T⁻¹]) where
  invOf := T i (-n)
  invOf_mul_self := by rw [← T_add, add_left_neg, T_zero]
  mul_invOf_self := by rw [← T_add, add_right_neg, T_zero]

@[simp]
theorem invOf_T (i : σ) (n : ℤ) : ⅟ (T i n : R[σ;T;T⁻¹]) = T i (-n) :=
  rfl

theorem isUnit_T (i : σ) (n : ℤ) : IsUnit (T i n : R[σ;T;T⁻¹]) :=
  isUnit_of_invertible _

instance invertibleMonomial (s : σ →₀ ℤ) (r : R) [Invertible r] :
    Invertible (monomial s r) where
  invOf := monomial (-s) ⅟ r
  invOf_mul_self := by
    simp only [monomial_mul, add_left_neg, invOf_mul_self']
    rfl
  mul_invOf_self := by
    simp only [monomial_mul, add_right_neg, mul_invOf_self']
    rfl

theorem induction_on_monomial {M : R[σ;T;T⁻¹] → Prop} (h_C : ∀ a, M (C a))
    (h_T : ∀ p i n, M p → M (p * T i n)) : ∀ s a, M (monomial s a) := by
  intro s a
  apply @Finsupp.induction σ ℤ _ _ s
  · show M (monomial 0 a)
    exact h_C a
  · intro n e p _hpn _he ih
    have : ∀ e : ℤ, M (monomial p a * T n e) := by
      intro e
      induction e
      · simp_all only [Finsupp.mem_support_iff, ne_eq, not_not, Int.ofNat_eq_coe]
      · simp_all only [Finsupp.mem_support_iff, ne_eq, not_not]
    simp [add_comm, monomial_add_single, this]

@[elab_as_elim]
theorem induction_on' {P : R[σ;T;T⁻¹] → Prop} (p : R[σ;T;T⁻¹])
    (h1 : ∀ (u : σ →₀ ℤ) (a : R), P (monomial u a))
    (h2 : ∀ p q : R[σ;T;T⁻¹], P p → P q → P (p + q)) : P p :=
  Finsupp.induction p
    (suffices P (monomial 0 0) by rwa [monomial_zero] at this
    show P (monomial 0 0) from h1 0 0)
    fun a b f _ha _hb hPf => h2 _ _ (h1 _ _) hPf

@[elab_as_elim]
theorem induction_on'' {P : R[σ;T;T⁻¹] → Prop} (p : R[σ;T;T⁻¹])
    (h0 : ∀ r : R, P (C r)) (h1 : ∀ (i : σ) (n : ℤ), P (T i n))
    (h2 : ∀ x y, P x → P y → P (x * y))
    (h3 : ∀ x y, P x → P y → P (x + y))  : P p := by
  refine' induction_on' p _ _
  · intro u
    induction' u using Finsupp.induction with i n f _ _ hP
    · exact h0
    · intro a
      rw [monomial_single_add]
      exact h2 _ _ (h1 i n) (hP a)
  · exact h3

theorem exists_monomial_ermm (f : R[σ;T;T⁻¹]) :
    ∃ (n : σ →₀ ℕ) (f' : MvPolynomial σ R),
      toLaurent f' = f * monomial (n.mapRange Int.ofNat rfl) 1 := by
  refine f.induction_on'' ?_ ?_ ?_ ?_
  · intro r
    use 0, MvPolynomial.C r
    simp only [toLaurent_C, mapRange_zero]
    exact (mul_one _).symm
  · intro i n
    induction' n with n n
    · use 0, X i ^ n
      simp only [map_pow, toLaurent_X, T_pow, mul_one, Int.ofNat_eq_coe, mapRange_zero]
      exact (mul_one _).symm
    · use (Finsupp.single i (n + 1)), 1
      simp only [map_one, T_eq_monomial, Finsupp.single_add, monomial_mul, mul_one]
      show monomial 0 1 = _
      rw [← (Finsupp.single_eq_zero (a := i) (b := 0)).2 rfl]
      rw [mapRange_add, mapRange_single, mapRange_single,
        ← Finsupp.single_add, ← Finsupp.single_add]
      · congr
        simp only [Int.negSucc_coe, Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg, Int.ofNat_eq_coe]
        ring
      · intros
        rfl
  · rintro x y ⟨n, f, hf⟩ ⟨m, g, hg⟩
    use m + n, f * g
    simp only [hf, map_mul, hg, mul_mul_mul_comm]
    congr
    simp only [monomial_mul, mul_one]
    congr
    rw [mapRange_add, add_comm]
    · intros; rfl
  · rintro x y ⟨n, f, hf⟩ ⟨m, g, hg⟩
    refine' ⟨m + n, f * MvPolynomial.monomial m 1
      + g * MvPolynomial.monomial n 1, _⟩
    simp_all only [map_add, map_mul, toLaurent_C_mul_T, mul_assoc, monomial_mul, mul_one, add_mul]
    congr
    rw [add_comm]
    all_goals {rw [mapRange_add]; intros; rfl}

end Semiring
end MvLaurentPolynomial
