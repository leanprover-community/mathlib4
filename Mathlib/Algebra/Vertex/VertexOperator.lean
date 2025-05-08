/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Vertex.HVertexOperator
import Mathlib.RingTheory.LaurentSeries

/-!
# Vertex operators
In this file we introduce vertex operators as linear maps to Laurent series.

## Definitions
* VertexOperator : An `R`-linear map from an `R`-module `V` to `LaurentSeries V`.
* HasseDerivative : A divided-power derivative.
* Locality : A weak form of commutativity.
* Residue products : A family of products on `VertexOperator R V` parametrized by integers.

## Main results
* Composition rule for Hasse derivatives.
* Comparison between Hasse derivatives and iterated derivatives.
* locality at order `≤ n` implies locality at order `≤ n + 1`.
* Boundedness lemmas for defining residue products

## To do:
* residue products with identity give Hasse derivatives.
* Dong's lemma : pairwise locality implies locality with residue products.
* API for SMul by integer powers of suitable MVPolynomials, like `(X i) - (X j)`

## References
* G. Mason `Vertex rings and Pierce bundles` ArXiv 1707.00328
* A. Matsuo, K. Nagatomo `On axioms for a vertex algebra and locality of quantum fields`
  arXiv:hep-th/9706118
* H. Li's paper on local systems?
-/

noncomputable section

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- A vertex operator over a commutative ring `R` is an `R`-linear map from an `R`-module `V` to
Laurent series with coefficients in `V`.  We write this as a specialization of the heterogeneous
case. -/
abbrev VertexOperator (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V]
    [Module R V] := HVertexOperator ℤ R V V

namespace VertexOperator

open HVertexOperator

@[ext]
theorem ext (A B : VertexOperator R V) (h : ∀ v : V, A v = B v) :
    A = B := LinearMap.ext h

/-- The coefficient of a vertex operator under normalized indexing. -/
def ncoeff {R} [CommRing R] [AddCommGroup V] [Module R V] (A : VertexOperator R V) (n : ℤ) :
    Module.End R V := HVertexOperator.coeff A (-n - 1)

/-- In the literature, the `n`th normalized coefficient of a vertex operator `A` is written as
either `Aₙ` or `A(n)`. -/
scoped[VertexOperator] notation A "[[" n "]]" => ncoeff A n

@[simp]
theorem coeff_eq_ncoeff (A : VertexOperator R V)
    (n : ℤ) : HVertexOperator.coeff A n = A [[-n - 1]] := by
  rw [ncoeff, neg_sub, sub_neg_eq_add, add_sub_cancel_left]

@[simp]
theorem ncoeff_add (A B : VertexOperator R V) (n : ℤ) :
    (A + B) [[n]] = A [[n]] + B [[n]] := by
  rw [ncoeff, ncoeff, ncoeff, coeff_add, Pi.add_apply]

@[simp]
theorem ncoeff_smul (A : VertexOperator R V) (r : R) (n : ℤ) :
    (r • A) [[n]] = r • (A [[n]]) := by
  rw [ncoeff, ncoeff, coeff_smul, Pi.smul_apply]

theorem ncoeff_eq_zero_of_lt_order (A : VertexOperator R V) (n : ℤ) (x : V)
    (h : -n - 1 < HahnSeries.order (A x)) : (A [[n]]) x = 0 := by
  simp only [ncoeff, HVertexOperator.coeff, LinearMap.coe_mk, AddHom.coe_mk]
  exact HahnSeries.coeff_eq_zero_of_lt_order h

theorem coeff_eq_zero_of_lt_order (A : VertexOperator R V) (n : ℤ) (x : V)
    (h : n < HahnSeries.order (A x)) : HVertexOperator.coeff A n x = 0 := by
  rw [coeff_eq_ncoeff, ncoeff_eq_zero_of_lt_order A (-n - 1) x]
  omega

/-- Given an endomorphism-valued formal power series satisfying a pointwise bounded-pole condition,
we produce a vertex operator. -/
noncomputable def of_coeff (f : ℤ → Module.End R V)
    (hf : ∀(x : V), ∃(n : ℤ), ∀(m : ℤ), m < n → (f m) x = 0) : VertexOperator R V :=
  HVertexOperator.of_coeff f
    (fun x => HahnSeries.suppBddBelow_supp_PWO (fun n => (f n) x)
      (HahnSeries.forallLTEqZero_supp_BddBelow (fun n => (f n) x)
        (Exists.choose (hf x)) (Exists.choose_spec (hf x))))

@[simp]
theorem of_coeff_apply_coeff (f : ℤ → Module.End R V)
    (hf : ∀ (x : V), ∃ n, ∀ m < n, (f m) x = 0) (x : V) (n : ℤ) :
    ((HahnModule.of R).symm ((of_coeff f hf) x)).coeff n = (f n) x := by
  rfl

@[simp]
theorem ncoeff_of_coeff (f : ℤ → Module.End R V)
    (hf : ∀ (x : V), ∃ (n : ℤ), ∀ (m : ℤ), m < n → (f m) x = 0) (n : ℤ) :
    (of_coeff f hf) [[n]] = f (-n - 1) := by
  ext v
  rw [ncoeff, coeff_apply, of_coeff_apply_coeff]

noncomputable instance [CommRing R] [AddCommGroup V] [Module R V] : One (VertexOperator R V) :=
  {
    one := (HahnModule.lof R (Γ := ℤ) (V := V)) ∘ₗ HahnSeries.single.linearMap (0 : ℤ)
  }

@[simp]
theorem one_apply (x : V) :
    (1 : VertexOperator R V) x = HahnModule.of R (HahnSeries.single 0 x) := by
  rfl

@[simp]
theorem one_ncoeff_neg_one : (1 : VertexOperator R V) [[-1]] = LinearMap.id := by
  ext
  rw [show -1 = - 0 - 1 by omega, ← coeff_eq_ncoeff, coeff_apply, one_apply, Equiv.symm_apply_apply,
    HahnSeries.coeff_single_same, LinearMap.id_apply]

theorem one_coeff_zero : HVertexOperator.coeff (1 : VertexOperator R V) 0 = LinearMap.id := by
  ext; simp

@[simp]
theorem one_ncoeff_ne_neg_one {n : ℤ} (hn : n ≠ -1) :
    (1 : VertexOperator R V) [[n]] = 0 := by
  ext
  rw [LinearMap.zero_apply, show n = -(-n - 1) - 1 by omega, ← coeff_eq_ncoeff, coeff_apply,
    one_apply, Equiv.symm_apply_apply, HahnSeries.coeff_single_of_ne (show -n - 1 ≠ 0 by omega)]

theorem one_coeff_of_ne {n : ℤ} (hn : n ≠ 0) :
    HVertexOperator.coeff (1 : VertexOperator R V) n = 0 := by
  simp [(show -n - 1 ≠ -1 by omega)]

section HasseDerivative

/-- The `k`th Hasse derivative of a vertex operator `∑ A_i X^i` is `∑ (i.choose k) A_i X^(i-k)`.
That is, it sends a vector to the `k`th Hasse derivative of the corresponding Laurent series.
It satisfies `k! * (hasseDeriv k A) = derivative^[k] A`. -/
@[simps]
def hasseDeriv (k : ℕ) : VertexOperator R V →ₗ[R] VertexOperator R V where
  toFun A :=
    { toFun := fun (x : V) => HahnModule.of R
        (LaurentSeries.hasseDeriv R k ((HahnModule.of R).symm (A x)))
      map_add' := by
        intros
        simp
      map_smul' := by
        intros
        simp }
  map_add' A B := by
    ext v n
    simp
  map_smul' r A := by
    ext
    simp

theorem hasseDeriv_coeff (k : ℕ) (A : VertexOperator R V) (n : ℤ) :
    HVertexOperator.coeff (hasseDeriv k A) n =
      (Ring.choose (n + k) k) • HVertexOperator.coeff A (n + k) :=
  rfl

theorem hasseDeriv_ncoeff (k : ℕ) (A : VertexOperator R V) (n : ℤ) :
    (hasseDeriv k A) [[n]] = (Ring.choose (-n - 1 + k) k) • A [[n - k]] := by
  simp only [ncoeff, hasseDeriv_coeff, show -n - 1 + k = -(n - k) - 1 by omega]

@[simp]
theorem hasseDeriv_zero : hasseDeriv 0 = LinearMap.id (M := VertexOperator R V) := by
  ext
  simp

theorem hasseDeriv_one_coeff (A : VertexOperator R V) (n : ℤ) :
    HVertexOperator.coeff (hasseDeriv 1 A) n = (n + 1) • HVertexOperator.coeff A (n + 1) := by
  rw [hasseDeriv_coeff 1, Nat.cast_one, Ring.choose_one_right]

/-- The derivative of a vertex operator is the first Hasse derivative, taking `∑ A_n X^n` to
`∑ n A_n X^{n-1}`, or `∑ A_n X^{-n-1}` to `∑ (-n-1) A_{n-1} X^{-n-1}` -/
def derivative (R : Type*) [CommRing R] [Module R V] :
    VertexOperator R V →ₗ[R] VertexOperator R V :=
  hasseDeriv 1

theorem derivative_apply (A : VertexOperator R V) : derivative R A = hasseDeriv 1 A :=
  rfl

@[simp]
theorem hasseDeriv_one : hasseDeriv 1 = derivative R (V := V) :=
  rfl

theorem hasseDeriv_apply_one (k : ℕ) (hk : 0 < k) : hasseDeriv k (1 : VertexOperator R V) = 0 := by
  ext n v
  simp [Ring.choose_zero_pos ℤ hk]

@[simp]
theorem hasseDeriv_comp (k l : ℕ) (A : VertexOperator R V) :
    (hasseDeriv k) (hasseDeriv l A) = (k + l).choose k • (hasseDeriv (k + l) A) := by
  ext
  simp

@[simp]
theorem hasseDeriv_comp_linear (k l : ℕ) : (hasseDeriv k).comp
    (hasseDeriv l) = (k + l).choose k • hasseDeriv (k + l) (R := R) (V := V) := by
  ext
  simp

theorem factorial_smul_hasseDeriv (k : ℕ) (A : VertexOperator R V) :
    k.factorial • hasseDeriv k A = ((derivative R) ^ k) A := by
  induction k generalizing A with
  | zero => ext; simp
  | succ k ih =>
    rw [Module.End.iterate_succ, LinearMap.comp_apply, ← ih, derivative_apply, hasseDeriv_comp,
      Nat.choose_symm_add, Nat.choose_one_right, Nat.factorial, mul_nsmul]

theorem factorial_smul_hasseDeriv_linear (k : ℕ) :
    k.factorial • hasseDeriv k (V := V) = (derivative R) ^ k := by
  ext A : 1
  exact factorial_smul_hasseDeriv k A

end HasseDerivative

section Binomial

/-- subtraction of monomials. Maybe put this in HahnSeries folder. -/
def unitSub {σ : Type*} [LinearOrder σ] {i j : σ} : HahnSeries (σ → ℤ) R :=
  HahnSeries.single (fun k ↦ if k = i then 1 else 0) 1 -
    HahnSeries.single (fun k ↦ if k = j then 1 else 0) 1



/-!
Given a totally ordered fintype `σ`, we consider binomials in `HahnSeries (PiLex σ Z) R`.
Define binomials `X i - X j` as `varMinus hij` for `hij : i < j`.
Need to add API for comparing `varMinus i j` with `varMinus j i`(and their ℕ-powers) under permuted
order and associativity equivalences. Binomials are also Finsupps, so we can make a
function to MvPolynomial, and compare them that way.

-/

end Binomial

section Local

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (A B : VertexOperator R V)

open HVertexOperator

/-- Two vertex operators commute if composition in the opposite order yields switched
coefficients. This should be replaced with locality at order zero. -/
def Commute : Prop := commutor_equiv (comp A B).coeff = (comp B A).coeff

lemma commute_symm : Commute A B ↔ Commute B A := by
  simp only [Commute, commutor_equiv, comp, LinearEquiv.coe_mk]
  constructor
  · intro h
    ext g u
    rw [funext_iff] at h
    specialize h (g.2, g.1)
    rw [LinearMap.ext_iff] at h
    specialize h u
    simp_all only [Prod.mk.eta, coeff_apply, LinearMap.coe_mk, AddHom.coe_mk,
      Equiv.symm_apply_apply]
  · intro h
    ext g u
    rw [funext_iff] at h
    specialize h (g.2, g.1)
    rw [LinearMap.ext_iff] at h
    specialize h u
    simp_all only [Prod.mk.eta, coeff_apply, LinearMap.coe_mk, AddHom.coe_mk,
      Equiv.symm_apply_apply]
/-!
/-- Locality to order `≤ n` means `(x-y)^n[A(x),B(y)] = 0`.  We write this condition as
vanishing of the `x^k y^l` term, for all integers `k` and `l`, but we have to switch coordinates,
since `BA` takes values in the opposite-order Hahn series. -/
def IsLocalToOrderLeq (n : ℕ) : Prop :=
  ∀ (k l : ℤ), ((subLeft R)^n • (comp A B)).coeff (toLex (k, l)) =
    ((subRight R)^n • (comp B A)).coeff (toLex (l, k))

theorem isLocalToOrderLeqAdd (m n : ℕ) (h : IsLocalToOrderLeq A B n) :
    IsLocalToOrderLeq A B (n + m) := by
  induction m with
  | zero => exact h
  | succ m ih =>
    intro k l
    rw [← add_assoc, pow_succ', mul_smul, subLeft_smul_eq, coeff_subLeft_smul, pow_succ', mul_smul,
      coeff_subRight_smul, ih, ih]

theorem toLex_zero_one_lt : (toLex (0, 1) : ℤ ×ₗ ℤ) < (toLex (1, 0)) := by
  exact lex_basis_lt

/-- Locality to order `≤ n` means `(x-y)^n[A(x),B(y)] = 0`.  We write this condition as
vanishing of the `x^k y^l` term, for all integers `k` and `l`, but we have to switch coordinates,
since `B(y)A(x)` takes values in the opposite-lex-order Hahn series. -/
def IsLocalToOrderLeq' (n : ℕ) : Prop :=
  ∀ (k l : ℤ),
    ((HahnSeries.binomialPow (Γ := ℤ ×ₗ ℤ) R (lex_basis_lt) (n : ℤ)) •
      (comp A B)).coeff (toLex (k, l)) =
    Int.negOnePow n • ((HahnSeries.binomialPow (Γ := ℤ ×ₗ ℤ) R (lex_basis_lt) (n : ℤ)) •
      (comp B A)).coeff (toLex (l, k))


theorem isLocalToOrderLeq_add (m n : ℕ) (h : IsLocalToOrderLeq' A B n) :
    IsLocalToOrderLeq' A B (n + m) := by
  induction m with
  | zero => exact h
  | succ m ih =>
    intro k l
    rw [← add_assoc, add_comm, Nat.cast_add, ← HahnSeries.binomialPow_add (Nat.cast (R := ℤ) 1),
      mul_smul, subLeft_smul_eq, coeff_subLeft_smul, pow_succ', mul_smul,
      coeff_subRight_smul, ih, ih]

I need to add API about permutations on the indexing set of PiLex!
def isLocal_symm (h : IsLocalToOrderLeq R V A B n) : IsLocalToOrderLeq R V B A n := by
  intro k l

  sorry

theorem isLocal_with_hasseDeriv_left (m : ℕ) (h : IsLocalToOrderLeq R V A B n) :
    IsLocalToOrderLeq R V (hasseDeriv m A) B (n + m) := by
  sorry
-/
--show `A` and `B` local to order `n` implies `∂^[k]A` and `B` are local to order `n+k`.
--show any vertex operator is local with identity.


end Local

/-!
section Composite

-- Change this section to use HetComp!

/-- This is a summand in the sum defining `composite.ncoeff`.  It is a scalar multiple of
`A_{m+n-i}B_{k+i}x`.  More specifically, it is the summand of fixed `i` for the
`x^{-n-1}y^{-k-1}` term in `g(x,y)A(x)B(y)` for `g(x,y) = ∑ f(i) x^{m-i}y^i`. -/
def composite_summand (A B : VertexOperator R V) (m n k : ℤ) (i : ℕ) (f : ℕ → ℤ) :
    Module.End R V where
  toFun := fun x => (f i) • (ncoeff A (m + n - i)) (ncoeff B (k + i) x)
  map_add' := by
    simp only [map_add, smul_add, forall_const]
  map_smul' := by
    intro r x
    simp only [map_smul, RingHom.id_apply]
    rw [smul_algebra_smul_comm (f i) r]

theorem composite_summand_eq_zero_of_lt_order_right (A B : VertexOperator R V) (m n k : ℤ) (i : ℕ)
    (f : ℕ → ℤ) (x : V) (h : Int.toNat (-k - HahnSeries.order (B x)) ≤ i) :
    (composite_summand A B m n k i f) x = 0 := by
  simp_all only [composite_summand, LinearMap.coe_mk, AddHom.coe_mk, Int.toNat_le,
    tsub_le_iff_right, ncoeff, coeff]
  have hi : (- (k + i) - 1) < HahnSeries.order (B x) := by omega
  rw [HahnSeries.coeff_eq_zero_of_lt_order hi, LinearMap.map_zero, HahnSeries.zero_coeff, smul_zero]


theorem composite_summand_eq_zero_of_lt_order_left (A B : VertexOperator R V) (m n k : ℤ) (i : ℕ)
    (f : ℤ → ℕ → ℤ) (x : V)
    (h : Int.toNat (-m + i - HahnSeries.order (A (ncoeff B (k + i) x))) ≤ n) :
    (composite_summand A B m n k i f) x = 0 := by
  sorry


theorem composite_summand_smul (A B : VertexOperator R V) (m n k : ℤ) (i : ℕ) (f : ℕ → ℤ)
    (r : R) (x : V) : r • composite_summand A B m n k i f x =
    composite_summand A B m n k i f (r • x) := by
  unfold composite_summand
  simp only [LinearMap.coe_mk, AddHom.coe_mk, map_smul]

/-- This is the `x^{-n-1}y^{-k-1}` term in `g(x,y)A(x)B(y)` where `g(x,y) = ∑ f(m,i) x^{m-i}y^i`.-/
noncomputable def composite_ncoeff (A B : VertexOperator R V) (m n k : ℤ) (f : ℕ → ℤ) (x : V) :
  V := Finset.sum (Finset.range (Int.toNat (-k - HahnSeries.order (B x))))
  fun i => composite_summand A B m n k i f x

theorem eventually_constant_sum_add {M : Type*} [AddCommMonoid M] {N : Type*} [AddCommMonoid N]
    (bd : M → ℕ) (f : ℕ → (M →+ N)) (h : ∀(m : M) (n : ℕ), bd m ≤ n → f n m = 0) (a b : M) :
    Finset.sum (Finset.range (bd (a + b))) (fun i => f i (a + b)) =
    Finset.sum (Finset.range (bd a)) (fun i => f i a) +
    Finset.sum (Finset.range (bd b)) (fun i => f i b) := by
  have hm : ∀(k : ℕ), max (bd a) (bd b) ≤ k → f k (a + b) = 0 := by
    intro k hk
    rw [map_add, h a k (le_of_max_le_left hk), h b k (le_of_max_le_right hk), zero_add]
  have hmm : ∀(k : ℕ), min (bd (a + b)) (max (bd a) (bd b)) ≤ k → f k (a + b) = 0 := by
    intro k hk
    rw [min_le_iff] at hk
    cases hk with
    | inl h' => exact h (a+b) k h'
    | inr h' => exact hm k h'
  rw [(Finset.eventually_constant_sum (h a) (Nat.le_max_left (bd a) (bd b))).symm]
  rw [(Finset.eventually_constant_sum (h b) (Nat.le_max_right (bd a) (bd b))).symm]
  rw [Finset.eventually_constant_sum hmm (Nat.min_le_left (bd (a + b)) (max (bd a) (bd b)))]
  rw [(Finset.eventually_constant_sum hmm (Nat.min_le_right (bd (a + b)) (max (bd a) (bd b)))).symm]
  simp only [← @Finset.sum_add_distrib, map_add]

theorem composite_ncoeff_add (A B : VertexOperator R V) (m n k : ℤ) (f : ℕ → ℤ) (x y : V) :
    composite_ncoeff A B m n k f (x + y) = (composite_ncoeff A B m n k f x) +
    (composite_ncoeff A B m n k f y) := by
  unfold composite_ncoeff
  refine @eventually_constant_sum_add V _ V _
    (fun (x : V) => Int.toNat (-k - HahnSeries.order (B x)))
    (fun i => composite_summand A B m n k i f) ?_ x y
  intro z i hi
  simp_all only [AddMonoidHom.coe_coe]
  exact @composite_summand_eq_zero_of_lt_order_right R V _ _ _ A B m n k i f z hi

theorem composite_ncoeff_smul (A B : VertexOperator R V) (m n k : ℤ) (f : ℕ → ℤ) (r : R)
    (x : V) : composite_ncoeff A B m n k f (r • x) = r • composite_ncoeff A B m n k f x := by
  simp only [composite_ncoeff, Finset.smul_sum, composite_summand_smul]
  by_cases h₂ : B (r • x) = 0
  · simp only [composite_summand, LinearMap.coe_mk, AddHom.coe_mk, ncoeff, coeff]
    simp only [h₂]
    simp only [HahnSeries.zero_coeff, map_zero, smul_zero, Finset.sum_const_zero]
  · have h₃ : HahnSeries.order (B x) ≤ HahnSeries.order (B (r • x)) := by
      rw [@LinearMap.map_smul]
      refine HahnSeries.le_order_smul r (B x) ?_
      simp_all only [map_smul, forall_const, ne_eq, not_false_eq_true]
    have h₄ : Int.toNat (-k - HahnSeries.order (B (r • x))) ≤
        Int.toNat (-k - HahnSeries.order (B x)) := by
      have h₅ : -k - HahnSeries.order (B (r • x)) ≤ -k - HahnSeries.order (B x) := by omega
      exact Int.toNat_le_toNat h₅
    rw [Finset.eventually_constant_sum
      (fun i => composite_summand_eq_zero_of_lt_order_right A B m n k i f (r • x)) h₄]

/-- The coefficient of a composite of vertex operators as a linear map. -/
noncomputable def composite_ncoeff.linearMap (A B : VertexOperator R V) (m n k : ℤ) (f : ℕ → ℤ) :
    Module.End R V where
  toFun := fun x => composite_ncoeff A B m n k f x
  map_add' := by
    intro x y
    simp only [map_add, smul_add]
    exact composite_ncoeff_add A B m n k f x y
  map_smul' := by
    intro r x
    simp only [RingHom.id_apply]
    exact composite_ncoeff_smul A B m n k f r x

theorem composite_bdd_below_right (A B : VertexOperator R V) (m n : ℤ) (f : ℕ → ℤ) (x : V) (k : ℤ)
    (hk : - HahnSeries.order (B x) < k) : composite_ncoeff A B m n k f x = 0 := by
  unfold composite_ncoeff
  have h : Int.toNat (-k - HahnSeries.order (B x)) = 0 := by
    refine Int.toNat_eq_zero.mpr ?_
    omega
  rw [h, Finset.sum_range_zero]

theorem composite_bdd_below_left (A B : VertexOperator R V) (m k : ℤ) (f : ℕ → ℤ) (x : V) :
    ∃(z : ℤ), ∀(n : ℤ), z - m < n → composite_ncoeff.linearMap A B m n k f x = 0 := by
  let bd : ℕ → ℤ := fun i => i - (HahnSeries.order (A (ncoeff B (k + i) x)))
  have hbd: ∀(i : ℕ) (n : ℤ), (bd i) ≤ m + n → (ncoeff A (m + n - i)) (ncoeff B (k + i) x) = 0 := by
    intro i n hn
    simp_all only [tsub_le_iff_right]
    refine ncoeff_eq_zero_of_lt_order A (m + n - i) (ncoeff B (k + i) x) ?_
    omega
  use Nat.cast (Finset.sup (Finset.range (Int.toNat (-k - HahnSeries.order (B x))))
    (fun i => Int.toNat (bd i)))
  intro n hn
  unfold composite_ncoeff.linearMap composite_ncoeff composite_summand
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_eq_zero ?_
  intro i hi
  rw [hbd i n ?_, smul_zero]
  have h : Int.toNat (bd i) < m + n := by
    rw [sub_lt_iff_lt_add, add_comm] at hn
    refine lt_of_le_of_lt ?_ hn
    rw [Nat.cast_le]
    exact @Finset.le_sup ℕ ℕ _ _ (Finset.range (Int.toNat (-k - HahnSeries.order (B x))))
      (fun i => Int.toNat (bd i)) i hi
  exact le_trans (Int.le_add_one (Int.self_le_toNat (bd i))) h

end Composite

/-- Locality to order `≤ N` means `(x-y)^N[A(x),B(y)] = 0`.  We write this condition as
vanishing of all coefficients.  -/
def isLocalToOrderLeq' (A B : VertexOperator R V) (N : ℕ) : Prop :=
  ∀ (k l : ℤ) (x : V), (composite_ncoeff A B N k l
  (fun i => (-1)^i • (Nat.choose N i)) x) =
  (composite_ncoeff B A N l k (fun i => (-1)^i • (Nat.choose N i)) x)

/-- Locality to order `≤ n` means `(x-y)^n[A(x),B(y)] = 0`.  We write this condition as
vanishing of the `x^k y^l` term, for all integers `k` and `l`. -/
def isLocalToOrderLeq (R: Type*) (V : Type*) [CommRing R] [AddCommGroup V] [Module R V]
    (A B : VertexOperator R V) (n : ℕ) : Prop := ∀ (k l : ℤ) (x : V), Finset.sum
    (Finset.antidiagonal n) (fun m => (-1)^(m.2) • (Nat.choose n m.2) •
    coeff A (k - m.1) (coeff B (l - m.2) x)) = Finset.sum (Finset.antidiagonal n)
    (fun m => (-1)^(m.2) • (Nat.choose n m.2) • coeff B (l - m.2) (coeff A (k - m.1) x))

/-- Two fields are local if they are local to order `≤ n` for some `n`. -/
def isLocal (R: Type*) (V : Type*) [CommRing R] [AddCommGroup V] [Module R V]
    (A B : VertexOperator R V) : Prop := ∃(n : ℕ), isLocalToOrderLeq R V A B n
-/
section ResidueProduct

open HVertexOperator
/-!
/-- The left side of the `m`-th residue product, given by the residue of `(x-y)^m A(x)B(y)` at
`x=0`, where we formally expand `(x-y)^m` as `x^m(1-y/x)^m` in `R((x))((y))` using binomials. -/
noncomputable def res_prod_left (A B : VertexOperator R V) (m : ℤ) : VertexOperator R V :=
  ResRight ((subLeft R) ^ m • comp A B) (-1 : ℤ)

/-- The right side of the `m`-th residue product, given by the residue of `(x-y)^m B(x)A(y)` at
`x=0`, where we formally expand `(x-y)^m` as `(-y)^m(1-x/y)^m` using binomials (i.e., in the domain
where `x` is big). -/
noncomputable def res_prod_right (A B : VertexOperator R V) (m : ℤ) : VertexOperator R V :=
  ResRight ((subRight R) ^ m • comp B A) (-1 : ℤ)

/-- The the `m`-th residue product of vertex operators -/
noncomputable def res_prod (A B : VertexOperator R V) (m : ℤ) : VertexOperator R V :=
  res_prod_left A B m + res_prod_right A B m

theorem subLeft_smul_HComp_one_left_eq (A : VertexOperator R V) {m : ℤ} {k n : ℕ} :
    HVertexOperator.coeff ((subLeft R ^ k) • comp (1 : VertexOperator R V) A)
      (toLex (m, Int.negSucc n)) = 0 := by
  induction k generalizing m n with
  | zero => simp
  | succ k ih => simp [pow_succ', mul_smul, ih]

/-!
theorem coeff_res_prod_left (A B : VertexOperator R V) (m k : ℤ) :
    (res_prod_left A B m).coeff k = sum i?
-/

theorem res_prod_left_one_nat (A : VertexOperator R V) (m : ℕ) : res_prod_left 1 A m = 0 := by
  ext
  rw [res_prod_left, ResRight, zpow_natCast, of_coeff_apply, Equiv.symm_apply_apply,
    show -1 = Int.negSucc 0 by exact rfl]
  simp_rw [subLeft_smul_HComp_one_left_eq]
  simp


theorem res_prod_neg_one_one_left (A : VertexOperator R V) : res_prod 1 A (-1) = A := by
  ext x n

  sorry

--residue products with 1, interaction with Hasse derivatives.

/-- A(x)B(y)C(z) - B(y)A(x)C(z) = C(z)A(x)B(y) - C(z)B(y)A(x). For any integers k,l,m, and any
n satisfying (k₀ - k) + (l₀ - l) + (m₀ - m) - 1 ≤ n, the previous equation times
(x-y)^m(y-z)^l(x-z)^k(y-z)^n holds.  Here, k₀ is locality order of AC, l₀ is order of BC, m₀ is
order of AB. -/
lemma comp_local (A B C : VertexOperator R V) (n : ℤ) (k l m : ℕ)
    (hAB : isLocaltoOrderLeq A B k) (hAC : isLocaltoOrderLeq A C l)
    (hBC : isLocaltoOrderLeq B C m) :
    (X_A - X_B)^{k-n} (X_B - X_C)^m (X_A - X_C)^l (X_A - X_B)^n comp (comp A B) C =
    (X_A - X_B)^{k-n} (X_B - X_C)^m (X_A - X_C)^l (X_A - X_B)^n comp C (comp A B) := by


/-- Dong's Lemma: if vertex operators `A` `B` `C` are pairwise local, then `A` is local to `B_n C`
for all integers `n`. -/
theorem local_residue_product (A B C : VertexOperator R V) (n : ℤ) (k l m : ℕ)
    (hAB : isLocaltoOrderLeq A B k) (hAC : isLocaltoOrderLeq A C l)
    (hBC : isLocaltoOrderLeq B C m) : isLocaltoOrderLeq (resProd A B n) C (k + l + m - n + 3) := by
  sorry  -- suffices to show triple products are equal after multiplying by
  --`(X_A - X_B)^{k-n} (X_B - X_C)^m (X_A - X_C)^l`

Cauchy-Jacobi : `[A(x),[B(y),C(z)]] + [B(y),[C(z),A(x)]] + [C(z),[A(x),B(y)]] = 0`.  This means, for
any k,l,m ∈ ℤ, the `x^k y^l z^m` coefficient vanishes, or equivalently, the usual Jacobi for
`A.coeff k`, `B.coeff l`, and `C.coeff m`. We expand the 12 terms as cancelling Hahn series, and
multiply by integer powers of `(x-y)`, `(x-z)`, and `(y-z)`.

It may be better to work on the level of coefficient functions for locality. Then, commutators are
just formal functions, and we can multiply by Finsupps.  So IsLocal means commutator is annihilated
by a power of `(X-Y)`.



-/

end ResidueProduct

end VertexOperator
