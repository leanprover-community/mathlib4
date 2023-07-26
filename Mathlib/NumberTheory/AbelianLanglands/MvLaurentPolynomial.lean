import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Polynomial.Laurent
noncomputable section

open BigOperators

open Set Function Finsupp AddMonoidAlgebra

open BigOperators

universe u v w x z

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

/-- Multivariate polynomial, where `σ` is the index set of the variables and
  `R` is the coefficient ring -/
def MvLaurentPolynomial (σ : Type _) (R : Type _) [CommSemiring R] :=
  AddMonoidAlgebra R (σ →₀ ℤ)

local notation:9000 R "["σ"]" => MvPolynomial σ R
local notation:9000 R "["σ";"σ"⁻¹]" => MvLaurentPolynomial σ R

namespace MvLaurentPolynomial
-- porting note: because of `MvLaurentPolynomial.C` and `MvLaurentPolynomial.T` this linter throws
-- tons of warnings in this file, and it's easier to just disable them globally in the file
set_option linter.uppercaseLean3 false

variable {σ : Type _} {a a' a₁ a₂ : R} {e : ℤ} {n m : σ} {s : σ →₀ ℤ}

section CommSemiring

section Instances

instance decidableEqMvLaurentPolynomial [CommSemiring R] [DecidableEq σ] [DecidableEq R] :
    DecidableEq R[σ;σ⁻¹] :=
  Finsupp.decidableEq

instance commSemiring [CommSemiring R] : CommSemiring (R[σ;σ⁻¹]) :=
  AddMonoidAlgebra.commSemiring

instance inhabited [CommSemiring R] : Inhabited R[σ;σ⁻¹] :=
  ⟨0⟩

instance distribuMulAction [Monoid R] [CommSemiring S₁] [DistribMulAction R S₁] :
    DistribMulAction R (MvLaurentPolynomial σ S₁) :=
  AddMonoidAlgebra.distribMulAction

instance smulZeroClass [CommSemiring S₁] [SMulZeroClass R S₁] :
    SMulZeroClass R (MvLaurentPolynomial σ S₁) :=
  AddMonoidAlgebra.smulZeroClass

instance faithfulSMul [CommSemiring S₁] [SMulZeroClass R S₁] [FaithfulSMul R S₁] :
    FaithfulSMul R (MvLaurentPolynomial σ S₁) :=
  AddMonoidAlgebra.faithfulSMul

instance module [Semiring R] [CommSemiring S₁] [Module R S₁] : Module R (MvLaurentPolynomial σ S₁) :=
  AddMonoidAlgebra.module

instance isScalarTower [CommSemiring S₂] [SMul R S₁] [SMulZeroClass R S₂] [SMulZeroClass S₁ S₂]
    [IsScalarTower R S₁ S₂] : IsScalarTower R S₁ (MvLaurentPolynomial σ S₂) :=
  AddMonoidAlgebra.isScalarTower

instance smulCommClass [CommSemiring S₂] [SMulZeroClass R S₂] [SMulZeroClass S₁ S₂]
    [SMulCommClass R S₁ S₂] : SMulCommClass R S₁ (MvLaurentPolynomial σ S₂) :=
  AddMonoidAlgebra.smulCommClass

instance isCentralScalar [CommSemiring S₁] [SMulZeroClass R S₁] [SMulZeroClass Rᵐᵒᵖ S₁]
    [IsCentralScalar R S₁] : IsCentralScalar R (MvLaurentPolynomial σ S₁) :=
  AddMonoidAlgebra.isCentralScalar

instance algebra [CommSemiring R] [CommSemiring S₁] [Algebra R S₁] :
    Algebra R (MvLaurentPolynomial σ S₁) :=
  AddMonoidAlgebra.algebra

instance isScalarTower_right [CommSemiring S₁] [DistribSMul R S₁] [IsScalarTower R S₁ S₁] :
    IsScalarTower R (MvLaurentPolynomial σ S₁) (MvLaurentPolynomial σ S₁) :=
  AddMonoidAlgebra.isScalarTower_self _

instance smulCommClass_right [CommSemiring S₁] [DistribSMul R S₁] [SMulCommClass R S₁ S₁] :
    SMulCommClass R (MvLaurentPolynomial σ S₁) (MvLaurentPolynomial σ S₁) :=
  AddMonoidAlgebra.smulCommClass_self _

/-- If `R` is a subsingleton, then `R[σ;σ⁻¹]` has a unique element -/
instance unique [CommSemiring R] [Subsingleton R] : Unique R[σ;σ⁻¹] :=
  AddMonoidAlgebra.unique

instance commRing [CommRing R] : CommRing R[σ;σ⁻¹] :=
  AddMonoidAlgebra.commRing


end Instances

variable [CommSemiring R] [CommSemiring S₁] {p q : R[σ;σ⁻¹]}

/-- `monomial s a` is the monomial with coefficient `a` and exponents given by `s`  -/
def monomial (s : σ →₀ ℤ) : R →ₗ[R] R[σ;σ⁻¹] :=
  lsingle s

theorem single_eq_monomial (s : σ →₀ ℤ) (a : R) : Finsupp.single s a = monomial s a :=
  rfl

theorem mul_def : p * q = p.sum fun m a => q.sum fun n b => monomial (m + n) (a * b) :=
  rfl

/-- `C a` is the constant polynomial with value `a` -/
def C : R →+* R[σ;σ⁻¹] :=
  { singleZeroRingHom with toFun := monomial 0 }

variable (R σ)

theorem algebraMap_eq : algebraMap R R[σ;σ⁻¹] = C :=
  rfl

variable {R σ}
/-- The ring homomorphism, taking a polynomial with coefficients in `R` to a Laurent polynomial
with coefficients in `R`. -/
def Polynomial.toLaurent [CommSemiring R] : R[σ] →+* MvLaurentPolynomial σ R :=
  mapDomainRingHom R (Finsupp.mapRange.addMonoidHom (α := σ) Int.ofNatHom.toAddMonoidHom)

set_option autoImplicit false

namespace MvLaurentPolynomial

variable [CommSemiring R]

theorem monomial_zero_one_eq_one :
    (monomial (0 : σ →₀ ℤ) (1 : R) : R[σ;σ⁻¹]) = (1 : R[σ;σ⁻¹]) :=
  rfl

/-!  ### The functions `C` and `T`. -/


/-- The ring homomorphism `C`, including `R` into the ring of Laurent polynomials over `R` as
the constant Laurent polynomials. -/
def C : R →+* R[σ;σ⁻¹] :=
  singleZeroRingHom

theorem algebraMap_apply {R A : Type _} [CommSemiring R] [CommSemiring A] [Algebra R A] (r : R) :
    algebraMap R A[σ;σ⁻¹] r = C (algebraMap R A r) :=
  rfl

theorem monomial_eq_C (r : R) : monomial (0 : σ →₀ ℤ) r = C r := rfl

def T (n : σ) (r : ℤ) : R[σ;σ⁻¹] :=
  monomial (Finsupp.single n r) 1

@[simp]
theorem T_zero : (T n 0 : R[σ;σ⁻¹]) = 1 := by
  rw [T, monomial, Finsupp.single_zero]
  rfl

theorem T_add (i j : ℤ) : (T n (i + j) : R[σ;σ⁻¹]) = T n i * T n j := by
  show AddMonoidAlgebra.single _ _ = AddMonoidAlgebra.single _ _ * AddMonoidAlgebra.single _ _
  rw [single_mul_single, one_mul, Finsupp.single_add]

theorem T_sub (i j : ℤ) : (T n (i - j) : R[σ;σ⁻¹]) = T n i * T n (-j) := by
  rw [← T_add, sub_eq_add_neg]

@[simp]
theorem T_pow (i : ℤ) (j : ℕ) : (T n i ^ j : R[σ;σ⁻¹]) = T n (j * i) := by
  show AddMonoidAlgebra.single _ _ ^ _ = AddMonoidAlgebra.single _ _
  rw [single_pow j, one_pow, smul_single, nsmul_eq_mul]

/-- The `simp` version of `mul_assoc`, in the presence of `T`'s. -/
@[simp]
theorem mul_T_assoc (f : R[σ;σ⁻¹]) (i j : ℤ) :
    f * T n i * T n j = f * T n (i + j) := by
  simp [← T_add, mul_assoc]

/-@[simp]
theorem single_eq_C_mul_T (r : R) (i : ℤ) :
    (AddMonoidAlgebra.single (Finsupp.single n i) r : R[σ;σ⁻¹]) = (C r * T n i : R[σ;σ⁻¹]) := by
  sorry-/

instance invertibleT (i : ℤ) : Invertible (T n i : R[σ;σ⁻¹]) where
  invOf := T n (-i)
  invOf_mul_self := by rw [← T_add, add_left_neg, T_zero]
  mul_invOf_self := by rw [← T_add, add_right_neg, T_zero]

@[simp]
theorem invOf_T (i : ℤ) : ⅟ (T n i : R[σ;σ⁻¹]) = T n (-i) :=
  rfl

theorem isUnit_T (i : ℤ) : IsUnit (T n i : R[σ;σ⁻¹]) :=
  isUnit_of_invertible _

end MvLaurentPolynomial
/-exit
@[elab_as_elim]
protected theorem induction_on {M : R[T;T⁻¹] → Prop} (p : R[T;T⁻¹]) (h_C : ∀ a, M (C a))
    (h_add : ∀ {p q}, M p → M q → M (p + q))
    (h_C_mul_T : ∀ (n : ℕ) (a : R), M (C a * T n) → M (C a * T (n + 1)))
    (h_C_mul_T_Z : ∀ (n : ℕ) (a : R), M (C a * T (-n)) → M (C a * T (-n - 1))) : M p := by
  have A : ∀ {n : ℤ} {a : R}, M (C a * T n) := by
    intro n a
    refine Int.induction_on n ?_ ?_ ?_
    · simpa only [T_zero, mul_one] using h_C a
    · exact fun m => h_C_mul_T m a
    · exact fun m => h_C_mul_T_Z m a
  have B : ∀ s : Finset ℤ, M (s.sum fun n : ℤ => C (p.toFun n) * T n) := by
    apply Finset.induction
    · convert h_C 0
      simp only [Finset.sum_empty, _root_.map_zero]
    · intro n s ns ih
      rw [Finset.sum_insert ns]
      exact h_add A ih
  convert B p.support
  ext a
  simp_rw [← single_eq_C_mul_T]
  -- Porting note: did not make progress in `simp_rw`
  rw [Finset.sum_apply']
  simp_rw [Finsupp.single_apply, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact Finsupp.not_mem_support_iff.mp h
#align laurent_polynomial.induction_on LaurentPolynomial.induction_on

/-- To prove something about Laurent polynomials, it suffices to show that
* the condition is closed under taking sums, and
* it holds for monomials.
-/
@[elab_as_elim]
protected theorem induction_on' {M : R[T;T⁻¹] → Prop} (p : R[T;T⁻¹])
    (h_add : ∀ p q, M p → M q → M (p + q)) (h_C_mul_T : ∀ (n : ℤ) (a : R), M (C a * T n)) :
    M p := by
  refine' p.induction_on (fun a => _) (fun {p q} => h_add p q) _ _ <;>
      try exact fun n f _ => h_C_mul_T _ f
  convert h_C_mul_T 0 a
  exact (mul_one _).symm
#align laurent_polynomial.induction_on' LaurentPolynomial.induction_on'

theorem commute_T (n : ℤ) (f : R[T;T⁻¹]) : Commute (T n) f :=
  f.induction_on' (fun p q Tp Tq => Commute.add_right Tp Tq) fun m a =>
    show T n * _ = _ by
      rw [T, T, ← single_eq_C, single_mul_single, single_mul_single, single_mul_single]
      simp [add_comm]
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.commute_T LaurentPolynomial.commute_T

@[simp]
theorem T_mul (n : ℤ) (f : R[T;T⁻¹]) : T n * f = f * T n :=
  (commute_T n f).eq
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.T_mul LaurentPolynomial.T_mul

/-- `trunc : R[T;T⁻¹] →+ R[X]` maps a Laurent polynomial `f` to the polynomial whose terms of
nonnegative degree coincide with the ones of `f`.  The terms of negative degree of `f` "vanish".
`trunc` is a left-inverse to `Polynomial.toLaurent`. -/
def trunc : R[T;T⁻¹] →+ R[X] :=
  (toFinsuppIso R).symm.toAddMonoidHom.comp <| comapDomain.addMonoidHom fun _ _ => Int.ofNat.inj
#align laurent_polynomial.trunc LaurentPolynomial.trunc

@[simp]
theorem trunc_C_mul_T (n : ℤ) (r : R) : trunc (C r * T n) = ite (0 ≤ n) (monomial n.toNat r) 0 := by
  -- Porting note: added. Should move elsewhere after the port.
  have : Function.Injective Int.ofNat := fun x y h => Int.ofNat_inj.mp h
  apply (toFinsuppIso R).injective
  rw [← single_eq_C_mul_T, trunc, AddMonoidHom.coe_comp, Function.comp_apply]
  -- Porting note: was `rw`
  erw [comapDomain.addMonoidHom_apply this]
  rw [toFinsuppIso_apply]
  -- Porting note: rewrote proof below relative to mathlib3.
  by_cases n0 : 0 ≤ n
  · lift n to ℕ using n0
    erw [comapDomain_single]
    simp only [Nat.cast_nonneg, Int.toNat_ofNat, ite_true, toFinsupp_monomial]
  · lift -n to ℕ using (neg_pos.mpr (not_le.mp n0)).le with m
    rw [toFinsupp_inj, if_neg n0]
    ext a
    have := ((not_le.mp n0).trans_le (Int.ofNat_zero_le a)).ne
    simp only [coeff_ofFinsupp, comapDomain_apply, Int.ofNat_eq_coe, coeff_zero,
      single_eq_of_ne this]
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.trunc_C_mul_T LaurentPolynomial.trunc_C_mul_T

@[simp]
theorem leftInverse_trunc_toLaurent :
    Function.LeftInverse (trunc : R[T;T⁻¹] → R[X]) Polynomial.toLaurent := by
  refine' fun f => f.induction_on' _ _
  · intro f g hf hg
    simp only [hf, hg, _root_.map_add]
  · intro n r
    simp only [Polynomial.toLaurent_C_mul_T, trunc_C_mul_T, Int.coe_nat_nonneg, Int.toNat_coe_nat,
      if_true]
#align laurent_polynomial.left_inverse_trunc_to_laurent LaurentPolynomial.leftInverse_trunc_toLaurent

@[simp]
theorem _root_.Polynomial.trunc_toLaurent (f : R[X]) : trunc (toLaurent f) = f :=
  leftInverse_trunc_toLaurent _
#align polynomial.trunc_to_laurent Polynomial.trunc_toLaurent

theorem _root_.Polynomial.toLaurent_injective :
    Function.Injective (Polynomial.toLaurent : R[X] → R[T;T⁻¹]) :=
  leftInverse_trunc_toLaurent.injective
#align polynomial.to_laurent_injective Polynomial.toLaurent_injective

@[simp]
theorem _root_.Polynomial.toLaurent_inj (f g : R[X]) : toLaurent f = toLaurent g ↔ f = g :=
  ⟨fun h => Polynomial.toLaurent_injective h, congr_arg _⟩
#align polynomial.to_laurent_inj Polynomial.toLaurent_inj

theorem _root_.Polynomial.toLaurent_ne_zero {f : R[X]} : f ≠ 0 ↔ toLaurent f ≠ 0 :=
  (map_ne_zero_iff _ Polynomial.toLaurent_injective).symm
#align polynomial.to_laurent_ne_zero Polynomial.toLaurent_ne_zero

theorem exists_T_pow (f : R[T;T⁻¹]) : ∃ (n : ℕ) (f' : R[X]), toLaurent f' = f * T n := by
  refine f.induction_on' ?_ fun n a => ?_ <;> clear f
  · rintro f g ⟨m, fn, hf⟩ ⟨n, gn, hg⟩
    refine' ⟨m + n, fn * X ^ n + gn * X ^ m, _⟩
    simp only [hf, hg, add_mul, add_comm (n : ℤ), map_add, map_mul, Polynomial.toLaurent_X_pow,
      mul_T_assoc, Int.ofNat_add]
  · cases' n with n n
    · exact ⟨0, Polynomial.C a * X ^ n, by simp⟩
    · refine' ⟨n + 1, Polynomial.C a, _⟩
      simp only [Int.negSucc_eq, Polynomial.toLaurent_C, Int.ofNat_succ, mul_T_assoc, add_left_neg,
        T_zero, mul_one]
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.exists_T_pow LaurentPolynomial.exists_T_pow

/-- This is a version of `exists_T_pow` stated as an induction principle. -/
@[elab_as_elim]
theorem induction_on_mul_T {Q : R[T;T⁻¹] → Prop} (f : R[T;T⁻¹])
    (Qf : ∀ {f : R[X]} {n : ℕ}, Q (toLaurent f * T (-n))) : Q f := by
  rcases f.exists_T_pow with ⟨n, f', hf⟩
  rw [← mul_one f, ← T_zero, ← Nat.cast_zero, ← Nat.sub_self n, Nat.cast_sub rfl.le, T_sub,
    ← mul_assoc, ← hf]
  exact Qf
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.induction_on_mul_T LaurentPolynomial.induction_on_mul_T

/-- Suppose that `Q` is a statement about Laurent polynomials such that
* `Q` is true on *ordinary* polynomials;
* `Q (f * T)` implies `Q f`;
it follow that `Q` is true on all Laurent polynomials. -/
theorem reduce_to_polynomial_of_mul_T (f : R[T;T⁻¹]) {Q : R[T;T⁻¹] → Prop}
    (Qf : ∀ f : R[X], Q (toLaurent f)) (QT : ∀ f, Q (f * T 1) → Q f) : Q f := by
  induction' f using LaurentPolynomial.induction_on_mul_T with f n
  induction' n with n hn
  · simpa only [Nat.zero_eq, Nat.cast_zero, neg_zero, T_zero, mul_one] using Qf _
  · convert QT _ _
    simpa using hn
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.reduce_to_polynomial_of_mul_T LaurentPolynomial.reduce_to_polynomial_of_mul_T

section Support

theorem support_C_mul_T (a : R) (n : ℤ) : Finsupp.support (C a * T n) ⊆ {n} := by
  -- Porting note: was
  -- simpa only [← single_eq_C_mul_T] using support_single_subset
  rw [← single_eq_C_mul_T]
  exact support_single_subset
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.support_C_mul_T LaurentPolynomial.support_C_mul_T

theorem support_C_mul_T_of_ne_zero {a : R} (a0 : a ≠ 0) (n : ℤ) :
    Finsupp.support (C a * T n) = {n} := by
  rw [← single_eq_C_mul_T]
  exact support_single_ne_zero _ a0
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.support_C_mul_T_of_ne_zero LaurentPolynomial.support_C_mul_T_of_ne_zero

/-- The support of a polynomial `f` is a finset in `ℕ`.  The lemma `toLaurent_support f`
shows that the support of `f.toLaurent` is the same finset, but viewed in `ℤ` under the natural
inclusion `ℕ ↪ ℤ`. -/
theorem toLaurent_support (f : R[X]) : f.toLaurent.support = f.support.map Nat.castEmbedding := by
  generalize hd : f.support = s
  revert f
  refine' Finset.induction_on s _ _ <;> clear s
  · simp (config := { contextual := true }) only [Polynomial.support_eq_empty, map_zero,
      Finsupp.support_zero, eq_self_iff_true, imp_true_iff, Finset.map_empty,
      Finsupp.support_eq_empty]
  · intro a s as hf f fs
    have : (erase a f).toLaurent.support = s.map Nat.castEmbedding := by
      refine' hf (f.erase a) _
      simp only [fs, Finset.erase_eq_of_not_mem as, Polynomial.support_erase,
        Finset.erase_insert_eq_erase]
    rw [← monomial_add_erase f a, Finset.map_insert, ← this, map_add, Polynomial.toLaurent_C_mul_T,
      support_add_eq, Finset.insert_eq]
    · congr
      exact support_C_mul_T_of_ne_zero (Polynomial.mem_support_iff.mp (by simp [fs])) _
    · rw [this]
      exact Disjoint.mono_left (support_C_mul_T _ _) (by simpa)
#align laurent_polynomial.to_laurent_support LaurentPolynomial.toLaurent_support

end Support

section Degrees

/-- The degree of a Laurent polynomial takes values in `WithBot ℤ`.
If `f : R[T;T⁻¹]` is a Laurent polynomial, then `f.degree` is the maximum of its support of `f`,
or `⊥`, if `f = 0`. -/
def degree (f : R[T;T⁻¹]) : WithBot ℤ :=
  f.support.max
#align laurent_polynomial.degree LaurentPolynomial.degree

@[simp]
theorem degree_zero : degree (0 : R[T;T⁻¹]) = ⊥ :=
  rfl
#align laurent_polynomial.degree_zero LaurentPolynomial.degree_zero

@[simp]
theorem degree_eq_bot_iff {f : R[T;T⁻¹]} : f.degree = ⊥ ↔ f = 0 := by
  refine' ⟨fun h => _, fun h => by rw [h, degree_zero]⟩
  rw [degree, Finset.max_eq_sup_withBot] at h
  ext n
  refine' not_not.mp fun f0 => _
  simp_rw [Finset.sup_eq_bot_iff, Finsupp.mem_support_iff, Ne.def, WithBot.coe_ne_bot] at h
  exact h n f0
#align laurent_polynomial.degree_eq_bot_iff LaurentPolynomial.degree_eq_bot_iff

section ExactDegrees

open Classical

@[simp]
theorem degree_C_mul_T (n : ℤ) (a : R) (a0 : a ≠ 0) : degree (C a * T n) = n := by
  rw [degree]
  -- Porting note: was `convert Finset.max_singleton`
  have : Finsupp.support (C a * T n) = {n} := by
    refine' support_eq_singleton.mpr _
    rw [← single_eq_C_mul_T]
    simp only [single_eq_same, a0, Ne.def, not_false_iff, eq_self_iff_true, and_self_iff]
  rw [this]
  exact Finset.max_singleton
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.degree_C_mul_T LaurentPolynomial.degree_C_mul_T

theorem degree_C_mul_T_ite (n : ℤ) (a : R) : degree (C a * T n) = ite (a = 0) ⊥ ↑n := by
  split_ifs with h <;>
    simp only [h, map_zero, MulZeroClass.zero_mul, degree_zero, degree_C_mul_T, Ne.def,
      not_false_iff]
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.degree_C_mul_T_ite LaurentPolynomial.degree_C_mul_T_ite

@[simp]
theorem degree_T [Nontrivial R] (n : ℤ) : (T n : R[T;T⁻¹]).degree = n := by
  rw [← one_mul (T n), ← map_one C]
  exact degree_C_mul_T n 1 (one_ne_zero : (1 : R) ≠ 0)
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.degree_T LaurentPolynomial.degree_T

theorem degree_C {a : R} (a0 : a ≠ 0) : (C a).degree = 0 := by
  rw [← mul_one (C a), ← T_zero]
  exact degree_C_mul_T 0 a a0
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.degree_C LaurentPolynomial.degree_C

theorem degree_C_ite (a : R) : (C a).degree = ite (a = 0) ⊥ 0 := by
  split_ifs with h <;> simp only [h, map_zero, degree_zero, degree_C, Ne.def, not_false_iff]
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.degree_C_ite LaurentPolynomial.degree_C_ite

end ExactDegrees

section DegreeBounds

theorem degree_C_mul_T_le (n : ℤ) (a : R) : degree (C a * T n) ≤ n := by
  by_cases a0 : a = 0
  · simp only [a0, map_zero, MulZeroClass.zero_mul, degree_zero, bot_le]
  · exact (degree_C_mul_T n a a0).le
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.degree_C_mul_T_le LaurentPolynomial.degree_C_mul_T_le

theorem degree_T_le (n : ℤ) : (T n : R[T;T⁻¹]).degree ≤ n :=
  (le_of_eq (by rw [map_one, one_mul])).trans (degree_C_mul_T_le n (1 : R))
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.degree_T_le LaurentPolynomial.degree_T_le

theorem degree_C_le (a : R) : (C a).degree ≤ 0 :=
  (le_of_eq (by rw [T_zero, mul_one])).trans (degree_C_mul_T_le 0 a)
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.degree_C_le LaurentPolynomial.degree_C_le

end DegreeBounds

end Degrees

instance : Module R[X] R[T;T⁻¹] :=
  Module.compHom _ Polynomial.toLaurent

instance (R : Type _) [Semiring R] : IsScalarTower R[X] R[X] R[T;T⁻¹] where
  smul_assoc x y z := by simp only [(· • ·), SMul.smul, SMul.comp.smul, map_mul, mul_assoc]

end Semiring

section CommSemiring

variable [CommSemiring R]

instance algebraPolynomial (R : Type _) [CommSemiring R] : Algebra R[X] R[T;T⁻¹] :=
  { Polynomial.toLaurent with
    commutes' := fun f l => by simp [mul_comm]
    smul_def' := fun f l => rfl }
#align laurent_polynomial.algebra_polynomial LaurentPolynomial.algebraPolynomial

theorem algebraMap_X_pow (n : ℕ) : algebraMap R[X] R[T;T⁻¹] (X ^ n) = T n :=
  Polynomial.toLaurent_X_pow n
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.algebra_map_X_pow LaurentPolynomial.algebraMap_X_pow

@[simp]
theorem algebraMap_eq_toLaurent (f : R[X]) : algebraMap R[X] R[T;T⁻¹] f = toLaurent f :=
  rfl
#align laurent_polynomial.algebra_map_eq_to_laurent LaurentPolynomial.algebraMap_eq_toLaurent

theorem isLocalization : IsLocalization (Submonoid.closure ({X} : Set R[X])) R[T;T⁻¹] :=
  { map_units' := fun t => by
      cases' t with t ht
      rcases Submonoid.mem_closure_singleton.mp ht with ⟨n, rfl⟩
      simp only [isUnit_T n, algebraMap_eq_toLaurent, Polynomial.toLaurent_X_pow]
    surj' := fun f => by
      induction' f using LaurentPolynomial.induction_on_mul_T with f n
      have := (Submonoid.closure ({X} : Set R[X])).pow_mem Submonoid.mem_closure_singleton_self n
      refine' ⟨(f, ⟨_, this⟩), _⟩
      simp only [algebraMap_eq_toLaurent, Polynomial.toLaurent_X_pow, mul_T_assoc,
        add_left_neg, T_zero, mul_one]
    eq_iff_exists' := fun {f g} => by
      rw [algebraMap_eq_toLaurent, algebraMap_eq_toLaurent, Polynomial.toLaurent_inj]
      refine' ⟨_, _⟩
      · rintro rfl
        exact ⟨1, rfl⟩
      · rintro ⟨⟨h, hX⟩, h⟩
        rcases Submonoid.mem_closure_singleton.mp hX with ⟨n, rfl⟩
        exact mul_X_pow_injective n h }
#align laurent_polynomial.is_localization LaurentPolynomial.isLocalization

end CommSemiring

end LaurentPolynomial

/-- `T n` is the degree `1` monomial $T_n$. -/
def T (n : σ) : R[σ;σ⁻¹] :=
  monomial (Finsupp.single n 1) 1

theorem monomial_left_injective {r : R} (hr : r ≠ 0) :
    Function.Injective fun s : σ →₀ ℤ => monomial s r :=
  Finsupp.single_left_injective hr

@[simp]
theorem monomial_left_inj {s t : σ →₀ ℤ} {r : R} (hr : r ≠ 0) :
    monomial s r = monomial t r ↔ s = t :=
  Finsupp.single_left_inj hr

theorem C_apply : (C a : R[σ;σ⁻¹]) = monomial 0 a :=
  rfl

-- porting note: `simp` can prove this
theorem C_0 : C 0 = (0 : R[σ;σ⁻¹]) := map_zero _

-- porting note: `simp` can prove this
theorem C_1 : C 1 = (1 : R[σ;σ⁻¹]) :=
  rfl

theorem C_mul_monomial : C a * monomial s a' = monomial s (a * a') := by
  -- porting note: this `show` feels like defeq abuse, but I can't find the appropriate lemmas
  show AddMonoidAlgebra.single _ _ * AddMonoidAlgebra.single _ _ = AddMonoidAlgebra.single _ _
  simp [C_apply, single_mul_single]

-- porting note: `simp` can prove this
theorem C_add : (C (a + a') : R[σ;σ⁻¹]) = C a + C a' :=
  Finsupp.single_add _ _ _

-- porting note: `simp` can prove this
theorem C_mul : (C (a * a') : R[σ;σ⁻¹]) = C a * C a' :=
  C_mul_monomial.symm

-- porting note: `simp` can prove this
theorem C_pow (a : R) (n : ℕ) : (C (a ^ n) : R[σ;σ⁻¹]) = C a ^ n :=
  map_pow _ _ _

theorem C_injective (σ : Type _) (R : Type _) [CommSemiring R] :
    Function.Injective (C : R → R[σ;σ⁻¹]) :=
  Finsupp.single_injective _

theorem C_surjective {R : Type _} [CommSemiring R] (σ : Type _) [IsEmpty σ] :
    Function.Surjective (C : R → R[σ;σ⁻¹]) := by
  refine' fun p => ⟨p.toFun 0, Finsupp.ext fun a => _⟩
  simp only [C_apply, ←single_eq_monomial, (Finsupp.ext isEmptyElim (α := σ) : a = 0),
    single_eq_same]
  rfl

@[simp]
theorem C_inj {σ : Type _} (R : Type _) [CommSemiring R] (r s : R) :
    (C r : R[σ;σ⁻¹]) = C s ↔ r = s :=
  (C_injective σ R).eq_iff

instance infinite_of_infinite (σ : Type _) (R : Type _) [CommSemiring R] [Infinite R] :
    Infinite R[σ;σ⁻¹] :=
  Infinite.of_injective C (C_injective _ _)

instance infinite_of_nonempty (σ : Type _) (R : Type _) [Nonempty σ] [CommSemiring R]
    [Nontrivial R] : Infinite R[σ;σ⁻¹] :=
  Infinite.of_injective ((fun s : σ →₀ ℤ => monomial s 1) ∘ Finsupp.single (Classical.arbitrary σ))
    <| (monomial_left_injective one_ne_zero).comp (Finsupp.single_injective _)

theorem C_eq_coe_nat (n : ℕ) : (C ↑n : R[σ;σ⁻¹]) = n := by
  induction n <;> simp [Nat.succ_eq_add_one, *]

theorem C_mul' : MvLaurentPolynomial.C a * p = a • p :=
  (Algebra.smul_def a p).symm

theorem smul_eq_C_mul (p : R[σ;σ⁻¹]) (a : R) : a • p = C a * p :=
  C_mul'.symm

theorem C_eq_smul_one : (C a : R[σ;σ⁻¹]) = a • (1 : R[σ;σ⁻¹]) := by
  rw [← C_mul', mul_one]

theorem smul_monomial {S₁ : Type _} [SMulZeroClass S₁ R] (r : S₁) :
    r • monomial s a = monomial s (r • a) :=
  Finsupp.smul_single _ _ _

theorem T_injective [Nontrivial R] : Function.Injective (T : σ → R[σ;σ⁻¹]) :=
  (monomial_left_injective one_ne_zero).comp (Finsupp.single_left_injective one_ne_zero)

@[simp]
theorem T_inj [Nontrivial R] (m n : σ) : T m = (T n : R[σ;σ⁻¹]) ↔ m = n :=
  T_injective.eq_iff

theorem monomial_pow (e : ℕ) : monomial s a ^ e = monomial (e • s) (a ^ e) :=
  AddMonoidAlgebra.single_pow e

@[simp]
theorem monomial_mul {s s' : σ →₀ ℤ} {a b : R} :
    monomial s a * monomial s' b = monomial (s + s') (a * b) :=
  AddMonoidAlgebra.single_mul_single

variable (R)

instance T_invertible (n : σ) : Invertible (T (R := R) n) where
  invOf := _
  invOf_mul_self := _
  mul_invOf_self := _
def TasUnit (n : σ) : R[σ;σ⁻¹]ˣ := unitOfInvertible (T n)
lemma T_is_unit (n : σ) : IsUnit (T (R := R) n) := (TasUnit R n).isUnit

def TZPow (n : σ) (e : ℤ) : R[σ;σ⁻¹] := IsUnit.unit (T_is_unit R n) ^ e

variable (σ)

/-- `fun s ↦ monomial s 1` as a homomorphism. -/
def monomialOneHom : Multiplicative (σ →₀ ℤ) →* R[σ;σ⁻¹] :=
  AddMonoidAlgebra.of _ _

variable {σ R}

@[simp]
theorem monomialOneHom_apply : monomialOneHom R σ s = (monomial s 1 : R[σ;σ⁻¹]) :=
  rfl

theorem T_pow_eq_monomial (e : ℕ) : T n ^ e = monomial (Finsupp.single n e) (1 : R) := by
  simp [T, monomial_pow]

theorem monomial_add_single (e : ℕ) :
    monomial (s + Finsupp.single n (e : ℤ)) a = monomial s a * T n ^ e := by
  rw [T_pow_eq_monomial, monomial_mul, mul_one]

theorem monomial_single_add (e : ℕ) :
    monomial (Finsupp.single n (e : ℤ) + s) a = T n ^ e * monomial s a := by
  rw [T_pow_eq_monomial, monomial_mul, one_mul]

theorem C_mul_T_pow_eq_monomial {s : σ} {a : R} {n : ℕ} :
  C a * T s ^ n = monomial (Finsupp.single s n) a :=
  by rw [← zero_add (Finsupp.single s (n : ℤ)), monomial_add_single, C_apply]

theorem C_mul_T_eq_monomial {s : σ} {a : R} : C a * T s = monomial (Finsupp.single s 1) a := by
  rw [←pow_one (T s), C_mul_T_pow_eq_monomial]; rfl

-- porting note: `simp` can prove this
theorem monomial_zero {s : σ →₀ ℤ} : monomial s (0 : R) = 0 :=
  Finsupp.single_zero _

@[simp]
theorem monomial_zero' : (monomial (0 : σ →₀ ℤ) : R → R[σ;σ⁻¹]) = C :=
  rfl

@[simp]
theorem monomial_eq_zero {s : σ →₀ ℤ} {b : R} : monomial s b = 0 ↔ b = 0 :=
  Finsupp.single_eq_zero

@[simp]
theorem sum_monomial_eq {A : Type _} [AddCommMonoid A] {u : σ →₀ ℤ} {r : R} {b : (σ →₀ ℤ) → R → A}
    (w : b u 0 = 0) : sum (monomial u r) b = b u r :=
  Finsupp.sum_single_index w

@[simp]
theorem sum_C {A : Type _} [AddCommMonoid A] {b : (σ →₀ ℤ) → R → A} (w : b 0 0 = 0) :
    sum (C a) b = b 0 a :=
  sum_monomial_eq w

theorem monomial_sum_one {α : Type _} (s : Finset α) (f : α → σ →₀ ℤ) :
    (monomial (∑ i in s, f i) 1 : R[σ;σ⁻¹]) = ∏ i in s, monomial (f i) 1 :=
  (monomialOneHom R σ).map_prod (fun i => Multiplicative.ofAdd (f i)) s

theorem monomial_sum_index {α : Type _} (s : Finset α) (f : α → σ →₀ ℤ) (a : R) :
    monomial (∑ i in s, f i) a = C a * ∏ i in s, monomial (f i) 1 := by
  rw [← monomial_sum_one, C_mul', ← (monomial _).map_smul, smul_eq_mul, mul_one]

theorem monomial_finsupp_sum_index {α β : Type _} [Zero β] (f : α →₀ β) (g : α → β → σ →₀ ℤ)
    (a : R) : monomial (f.sum g) a = C a * f.prod fun a b => monomial (g a b) 1 :=
  monomial_sum_index _ _ _

theorem monomial_eq_monomial_iff {α : Type _} (a₁ a₂ : α →₀ ℤ) (b₁ b₂ : R) :
    monomial a₁ b₁ = monomial a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0 :=
  Finsupp.single_eq_single_iff _ _ _ _

/-theorem monomial_eq : monomial s a =
    C a * (s.prod fun n (e : ℕ) => T n ^ e : R[σ;σ⁻¹]) := by
  simp only [T_pow_eq_monomial, ← monomial_finsupp_sum_index, Finsupp.sum_single]
-/
theorem induction_on_monomial {M : R[σ;σ⁻¹] → Prop} (h_C : ∀ a, M (C a))
    (h_T : ∀ p n, M p → M (p * T n)) : ∀ s a, M (monomial s a) := by
  intro s a
  apply @Finsupp.induction σ ℤ _ _ s
  · show M (monomial 0 a)
    exact h_C a
  · intro n e p _hpn _he ih
    have : ∀ e : ℤ, M (monomial p a * T n ^ e) := by
      intro e
      induction e with
      | zero => simp [ih]
      | succ e e_ih => simp [ih, pow_succ', (mul_assoc _ _ _).symm, h_T, e_ih]
    simp [add_comm, monomial_add_single, this]

/-- Analog of `Polynomial.induction_on'`.
To prove something about mv_polynomials,
it suffices to show the condition is closed under taking sums,
and it holds for monomials. -/
@[elab_as_elim]
theorem induction_on' {P : R[σ;σ⁻¹] → Prop} (p : R[σ;σ⁻¹])
    (h1 : ∀ (u : σ →₀ ℤ) (a : R), P (monomial u a))
    (h2 : ∀ p q : R[σ;σ⁻¹], P p → P q → P (p + q)) : P p :=
  Finsupp.induction p
    (suffices P (monomial 0 0) by rwa [monomial_zero] at this
    show P (monomial 0 0) from h1 0 0)
    fun a b f _ha _hb hPf => h2 _ _ (h1 _ _) hPf

/-- Similar to `MvLaurentPolynomial.induction_on` but only a weak form of `h_add` is required.-/
theorem induction_on''' {M : R[σ;σ⁻¹] → Prop} (p : R[σ;σ⁻¹]) (h_C : ∀ a, M (C a))
    (h_add_weak :
      ∀ (a : σ →₀ ℤ) (b : R) (f : (σ →₀ ℤ) →₀ R),
        a ∉ f.support → b ≠ 0 → M f → M ((show (σ →₀ ℤ) →₀ R from monomial a b) + f)) :
    M p :=
    -- porting note: I had to add the `show ... from ...` above, a type ascription was insufficient.
  Finsupp.induction p (C_0.rec <| h_C 0) h_add_weak

/-- Similar to `MvLaurentPolynomial.induction_on` but only a yet weaker form of `h_add` is required.-/
theorem induction_on'' {M : R[σ;σ⁻¹] → Prop} (p : R[σ;σ⁻¹]) (h_C : ∀ a, M (C a))
    (h_add_weak :
      ∀ (a : σ →₀ ℤ) (b : R) (f : (σ →₀ ℤ) →₀ R),
        a ∉ f.support → b ≠ 0 → M f → M (monomial a b) →
          M ((show (σ →₀ ℤ) →₀ R from monomial a b) + f))
    (h_T : ∀ (p : R[σ;σ⁻¹]) (n : σ), M p → M (p * MvLaurentPolynomial.T n)) : M p :=
    -- porting note: I had to add the `show ... from ...` above, a type ascription was insufficient.
  induction_on''' p h_C fun a b f ha hb hf =>
    h_add_weak a b f ha hb hf <| induction_on_monomial h_C h_T a b

/-- Analog of `Polynomial.induction_on`.-/
@[recursor 5]
theorem induction_on {M : R[σ;σ⁻¹] → Prop} (p : R[σ;σ⁻¹]) (h_C : ∀ a, M (C a))
    (h_add : ∀ p q, M p → M q → M (p + q)) (h_T : ∀ p n, M p → M (p * T n)) : M p :=
  induction_on'' p h_C (fun a b f _ha _hb hf hm => h_add (monomial a b) f hm hf) h_T

theorem ringHom_ext {A : Type _} [Semiring A] {f g : R[σ;σ⁻¹] →+* A}
    (hC : ∀ r, f (C r) = g (C r)) (hT : ∀ i, f (T i) = g (T i)) : f = g := by
  refine AddMonoidAlgebra.ringHom_ext' ?_ ?_
  -- porting note: this has high priority, but Lean still chooses `RingHom.ext`, why?
  -- probably because of the type synonym
  · ext x
    exact hC _
  · apply Finsupp.mulHom_ext'; intros x
    -- porting note: `Finsupp.mulHom_ext'` needs to have increased priority
    apply MonoidHom.ext_mnat
    exact hT _

/-- See note [partially-applied ext lemmas]. -/
@[ext 1100]
theorem ringHom_ext' {A : Type _} [Semiring A] {f g : R[σ;σ⁻¹] →+* A}
    (hC : f.comp C = g.comp C) (hT : ∀ i, f (T i) = g (T i)) : f = g :=
  ringHom_ext (RingHom.ext_iff.1 hC) hT

theorem hom_eq_hom [Semiring S₂] (f g : R[σ;σ⁻¹] →+* S₂) (hC : f.comp C = g.comp C)
    (hT : ∀ n : σ, f (T n) = g (T n)) (p : R[σ;σ⁻¹]) : f p = g p :=
  RingHom.congr_fun (ringHom_ext' hC hT) p

theorem is_id (f : R[σ;σ⁻¹] →+* R[σ;σ⁻¹]) (hC : f.comp C = C)
    (hT : ∀ n : σ, f (T n) = T n) (p : R[σ;σ⁻¹]) : f p = p :=
  hom_eq_hom f (RingHom.id _) hC hT p

@[ext 1100]
theorem algHom_ext' {A B : Type _} [CommSemiring A] [CommSemiring B] [Algebra R A] [Algebra R B]
    {f g : MvLaurentPolynomial σ A →ₐ[R] B}
    (h₁ :
      f.comp (IsScalarTower.toAlgHom R A (MvLaurentPolynomial σ A)) =
        g.comp (IsScalarTower.toAlgHom R A (MvLaurentPolynomial σ A)))
    (h₂ : ∀ i, f (T i) = g (T i)) : f = g :=
  AlgHom.coe_ringHom_injective (MvLaurentPolynomial.ringHom_ext' (congr_arg AlgHom.toRingHom h₁) h₂)

@[ext 1200]
theorem algHom_ext {A : Type _} [Semiring A] [Algebra R A] {f g : R[σ;σ⁻¹] →ₐ[R] A}
    (hf : ∀ i : σ, f (T i) = g (T i)) : f = g :=
  AddMonoidAlgebra.algHom_ext' (mulHom_ext' fun T : σ => MonoidHom.ext_mnat (hf T))

@[simp]
theorem algHom_C (f : R[σ;σ⁻¹] →ₐ[R] R[σ;σ⁻¹]) (r : R) : f (C r) = C r :=
  f.commutes r
-/
