/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/

import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Module.LinearMap
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.LaurentSeries

/-!
# Vertex operators

In this file we introduce vertex operators using Laurent series.

## Definitions

* VertexOperator : This is an `R`-linear map from an `R`-module `V` to `LaurentSeries V`.
* HasseDerivative : This is a divided-power derivative.
* Locality : This is a weak form of commutativity.
* Residue product parts : This is a family of products parametrized by integers.

## Main results

* Composition rule for Hasse derivatives.
* Comparison between Hasse derivatives and iterated derivatives.

## To do:

* locality at order `≤ n` implies locality at order `≤ n + 1`.
* residue products are fields
* residue products with identity give Hasse derivatives.
* Dong's lemma : pairwise locality implies locality with residue products.

## References

* G. Mason `Vertex rings and Pierce bundles` ArXiv 1707.00328
* A. Matsuo, K. Nagatomo `On axioms for a vertex algebra and locality of quantum fields`
  arXiv:hep-th/9706118
* H. Li's paper on local systems?

-/

variable {R : Type*} {V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- A vertex operator over a commutative ring `R` is an `R`-linear map from an `R`-module `V` to
Laurent series with coefficients in `V`. -/

abbrev VertexOperator (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V]
    [Module R V] := V →ₗ[R] LaurentSeries V

namespace VertexAlg

--theorem VertexOperator_add (A B : VertexOperator R V) (x : V) : (A + B) x = (A x) + (B x) := rfl

/-- The coefficient of a vertex operator, viewed as a formal power series with coefficients in
linear endomorphisms. -/
def coeff [CommRing R] [AddCommGroup V] [Module R V] (A : VertexOperator R V) (n : ℤ) :
    Module.End R V :=
  {
    toFun := fun (x : V) => (A x).coeff n
    map_add' := by simp only [map_add, HahnSeries.add_coeff', Pi.add_apply, forall_const]
    map_smul' := by simp only [map_smul, HahnSeries.smul_coeff, RingHom.id_apply, forall_const]
  }

/-- We write `ncoef` instead of `coefficient of a vertex operator under normalized indexing`.
Alternative suggestions welcome.  Also, should this be an abbrev? -/
def ncoef [CommRing R] [AddCommGroup V] [Module R V] (A : VertexOperator R V) (n : ℤ) :
    Module.End R V := coeff A (-n - 1)

theorem coeff_eq_ncoef (A : VertexOperator R V)
    (n : ℤ) : coeff A n = ncoef A (-n - 1) := by
  rw [ncoef, neg_sub, sub_neg_eq_add, add_sub_cancel']

/-- The normal convention for the normalized coefficient of a vertex operator is either `Aₙ` or
`A(n)`.  We choose a notation that looks like the TeX input. -/
scoped[VertexAlg] notation A "_{" n "}" => ncoef A n

/-- Given an endomorphism-valued formal power series satisfying a pointwise bounded-pole condition,
we produce a vertex operator. -/
noncomputable def VertexOperatorFromCoeff (f : ℤ → Module.End R V)
    (hf : ∀(x : V), ∃(n : ℤ), ∀(m : ℤ), m < n → (f m) x = 0) : VertexOperator R V where
  toFun := fun x => LaurentSeries.LaurentFromSuppBddBelow
    (fun n => (f n) x) (Exists.choose (hf x)) (Exists.choose_spec (hf x))
  map_add' := by
    intros
    simp only [map_add]
    exact rfl
  map_smul' := by
    intros
    simp only [map_smul, RingHom.id_apply]
    exact rfl

noncomputable instance [CommRing R] [AddCommGroup V] [Module R V] : One (VertexOperator R V) :=
  {
    one := HahnSeries.single.linearMap 0
  }

theorem one : (1 : VertexOperator R V) = HahnSeries.single.linearMap 0 := by
  exact rfl

theorem one_coeff_ite (x : V) (n : ℤ) : @coeff R V _ _ _ 1 n x = if n = 0 then x else 0 := by
  rw [one]
  unfold HahnSeries.single.linearMap HahnSeries.single.addMonoidHom HahnSeries.single Pi.single
    Function.update
  simp_all only [eq_rec_constant, Pi.zero_apply, dite_eq_ite]
  exact rfl

theorem one_coeff_zero' (x : V) : @coeff R V _ _ _ 1 0 x = x := by
  rw [one_coeff_ite, if_pos rfl]

theorem one_coeff_ne (x : V) (n : ℤ) (hn : n ≠ 0): @coeff R V _ _ _ 1 n x = 0 := by
  rw [one_coeff_ite, if_neg hn]

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

section HasseDerivative

/-- The `k`th Hasse derivative of a vertex operator `∑ A_i X^i` is `∑ (i.choose k) A_i X^(i-k)`.
That is, it sends a vector to the `k`th Hasse derivative of the corresponding Laurent series.
It satisfies `k! * (hasseDeriv k A) = derivative^[k] A`. -/
def hasseDeriv (k : ℕ) (A : VertexOperator R V) : VertexOperator R V :=
  {
    toFun := fun (x : V) => LaurentSeries.hasseDeriv k (A x)
    map_add' := by
      intros
      simp only [map_add, LaurentSeries.hasseDeriv_add]
    map_smul' := by
      intros
      simp only [map_smul, RingHom.id_apply, LaurentSeries.hasseDeriv_smul]
  }

theorem hasseDeriv_add (k : ℕ) (A B : VertexOperator R V) : hasseDeriv k (A + B) =
    hasseDeriv k A + hasseDeriv k B := by
  ext
  simp only [LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk, HahnSeries.add_coeff, hasseDeriv,
    LaurentSeries.hasseDeriv_add]

theorem hasseDeriv_smul (k : ℕ) (A : VertexOperator R V) (r : R) :
    hasseDeriv k (r • A) = r • hasseDeriv k A := by
  ext
  simp only [LinearMap.smul_apply, HahnSeries.smul_coeff, hasseDeriv, LaurentSeries.hasseDeriv_smul,
    LinearMap.coe_mk, AddHom.coe_mk]

/-- The Hasse derivative as a linear map on vertex operators. -/
def hasseDeriv.linearMap (k : ℕ) : VertexOperator R V →ₗ[R] VertexOperator R V :=
  {
    toFun := fun A => hasseDeriv k A
    map_add' := by
      intros
      simp only [hasseDeriv_add]
    map_smul' := by
      intros
      simp only [hasseDeriv_smul, RingHom.id_apply]
  }

@[simp]
theorem hasseDeriv_apply (k : ℕ) (A : VertexOperator R V) :
    hasseDeriv.linearMap k A = hasseDeriv k A := by
  exact rfl

theorem hasseDeriv_coeff (k : ℕ) (A : VertexOperator R V) (n : ℤ) :
    coeff (hasseDeriv k A) n = (Ring.choose (n + k) k) • coeff A (n + k) := by
  exact rfl

theorem hasseDeriv_ncoef (k : ℕ) (A : VertexOperator R V) (n : ℤ) :
    ncoef (hasseDeriv k A) n = (Ring.choose (-n - 1 + k) k) • ncoef A (n - k) := by
  simp only [ncoef, hasseDeriv_coeff]
  rw [show -n - 1 + k = -(n - k) - 1 by omega]

theorem hasseDeriv_zero' (A : VertexOperator R V) : hasseDeriv 0 A = A := by
  ext x n
  simp only [hasseDeriv, LaurentSeries.hasseDeriv_zero', LinearMap.coe_mk, AddHom.coe_mk]

@[simp]
theorem hasseDeriv_zero : @hasseDeriv.linearMap R V _ _ _ 0 = LinearMap.id := by
  exact LinearMap.ext <| hasseDeriv_zero'

theorem hasseDeriv_one_coeff (A : VertexOperator R V) (n : ℤ) :
    coeff (hasseDeriv 1 A) n = (n + 1) • coeff A (n + 1) := by
  rw [hasseDeriv_coeff 1, Nat.cast_one, @Ring.choose_one_right ℤ _ _ _ _ _]

/-- The derivative of a vertex operator is the first Hasse derivative, taking `∑ A_n X^n` to
`∑ n A_n X^{n-1}`, or `∑ A_n X^{-n-1}` to `∑ (-n-1) A_{n-1} X^{-n-1}` -/
def derivative : VertexOperator R V →ₗ[R] VertexOperator R V := hasseDeriv.linearMap 1

theorem derivative_apply (A : VertexOperator R V) : derivative A = hasseDeriv 1 A := by
  exact rfl

@[simp]
theorem hasseDeriv_one : hasseDeriv.linearMap 1 = @derivative R V _ _ _ := rfl

theorem hasseDeriv_apply_one (k : ℕ) (hk : 0 < k) : hasseDeriv k (1 : VertexOperator R V) = 0 := by
  ext x n
  rw [LinearMap.zero_apply, HahnSeries.zero_coeff, one]
  unfold HahnSeries.single.linearMap HahnSeries.single.addMonoidHom hasseDeriv
  simp only [ZeroHom.toFun_eq_coe, LinearMap.coe_mk, AddHom.coe_mk]
  rw [LaurentSeries.hasseDeriv_single, Ring.choose_zero_pos ℤ k hk, zero_smul,
    HahnSeries.single_eq_zero]
  exact rfl

theorem hasseDeriv_comp_coeff (k l : ℕ) (A : VertexOperator R V) (x : V) (n : ℤ) :
    HahnSeries.coeff ((hasseDeriv k (hasseDeriv l A)) x) n =
    HahnSeries.coeff ((Nat.choose (k + l) k • hasseDeriv (k + l) A) x) n := by
  rw [hasseDeriv, hasseDeriv]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply]
  rw [@LaurentSeries.hasseDeriv_comp' R]
  exact rfl

theorem hasseDeriv_comp' (k l : ℕ) (A : VertexOperator R V) :
    (@hasseDeriv R V _ _ _ k) (hasseDeriv l A) = (k + l).choose k • (hasseDeriv (k + l) A) := by
  ext x n
  exact @hasseDeriv_comp_coeff R V _ _ _ k l A x n

set_option synthInstance.maxHeartbeats 40000 -- Is there something I can do to make this faster?

theorem hasseDeriv_comp (k l : ℕ) : (@hasseDeriv.linearMap R V _ _ _ k).comp
    (hasseDeriv.linearMap l) = (k + l).choose k • hasseDeriv.linearMap (k + l) := by
  ext A x n
  simp only [LinearMap.coe_comp, Function.comp_apply, hasseDeriv_apply, hasseDeriv_comp_coeff]
  exact rfl

theorem factorial_smul_hasseDeriv' (k : ℕ) (A : VertexOperator R V) :
    k.factorial • hasseDeriv k A = (@derivative R V _ _ _)^[k] A := by
  induction k generalizing A with
  | zero =>
    rw [Nat.zero_eq, Nat.factorial_zero, one_smul, Function.iterate_zero, id_eq, hasseDeriv_zero']
  | succ k ih =>
    rw [Function.iterate_succ, Function.comp_apply,  ← ih, derivative_apply,
      @hasseDeriv_comp' R, Nat.choose_symm_add, Nat.choose_one_right, Nat.factorial, mul_nsmul]

theorem factorial_smul_hasseDeriv (k : ℕ) :
    k.factorial • @hasseDeriv.linearMap R V _ _ _ k = (@derivative R V _ _ _)^[k] := by
  ext A : 1
  simp_all only [Pi.smul_apply, hasseDeriv_apply]
  exact factorial_smul_hasseDeriv' k A

end HasseDerivative

section ResidueProduct

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

/-- The function defining a coefficient in the left sum of the residue product. -/
def res_prod_left_summand (A B : VertexOperator R V) (m k : ℤ) (i : ℕ) : Module.End R V where
  toFun := fun x => (-1)^i • (Ring.choose m i) • (ncoef A (m - i)) (ncoef B (k + i) x)
  map_add' := by
    simp only [map_add, smul_add, forall_const]
  map_smul' := by
    intro r x
    simp only [map_smul, RingHom.id_apply]
    rw [smul_algebra_smul_comm ((-1)^i) r, smul_algebra_smul_comm (Ring.choose m i) r]

theorem res_prod_left_summand_vanish (A B : VertexOperator R V) (m k : ℤ) (i : ℕ) (x : V)
    (h : Int.toNat (-k - HahnSeries.order (B x)) ≤ i) :
    (res_prod_left_summand A B m k i) x = 0 := by
  simp_all only [res_prod_left_summand, LinearMap.coe_mk, AddHom.coe_mk, Int.toNat_le,
    tsub_le_iff_right, ncoef, coeff]
  have hi : (- (k + i) - 1) < HahnSeries.order (B x) := by omega
  rw [HahnSeries.coeff_eq_zero_of_lt_order hi, LinearMap.map_zero, HahnSeries.zero_coeff, smul_zero,
    smul_zero]

/-- The `k`-th normalized coefficient in the left sum of the `m`-th residue product of `A` and `B`.
-/
noncomputable def res_prod_left_ncoef (A B : VertexOperator R V) (m k : ℤ) (x : V) : V :=
  Finset.sum (Finset.range (Int.toNat (-k - HahnSeries.order (B x))))
  fun i => res_prod_left_summand A B m k i x

theorem res_prod_left_ncoef_add (A B : VertexOperator R V) (m k : ℤ) (x y : V) :
    res_prod_left_ncoef A B m k (x + y) = res_prod_left_ncoef A B m k x +
    res_prod_left_ncoef A B m k y := by
  unfold res_prod_left_ncoef
  have h : ∀(z : V) (i : ℕ), (res_prod_left_summand A B m k i) z =
      (@AddMonoidHomClass.toAddMonoidHom V V (Module.End R V) AddMonoid.toAddZeroClass
      AddMonoid.toAddZeroClass (DistribMulActionHomClass.toAddMonoidHomClass R)
      (res_prod_left_summand A B m k i)) z := by
    exact fun z i ↦ rfl
  simp_rw [h x, h y]
  refine @eventually_constant_sum_add V _ V _
    (fun (x : V) => Int.toNat (-k - HahnSeries.order (B x)))
    (fun i => res_prod_left_summand A B m k i) ?_ x y
  intro z i hi
  simp_all only [AddMonoidHom.coe_coe]
  exact @res_prod_left_summand_vanish R V _ _ _ A B m k i z hi

theorem res_prod_left_ncoef_smul (A B : VertexOperator R V) (m k : ℤ) (r : R) (x : V) :
    res_prod_left_ncoef A B m k (r • x) = r • res_prod_left_ncoef A B m k x := by
  simp only [res_prod_left_ncoef, Finset.smul_sum]
  have h₁ : ∀(i : ℕ),
      r • res_prod_left_summand A B m k i x = res_prod_left_summand A B m k i (r • x) := by
    intro i
    unfold res_prod_left_summand
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_smul]
  by_cases h₂ : B (r • x) = 0
  · simp only [h₁]
    simp only [res_prod_left_summand, LinearMap.coe_mk, AddHom.coe_mk, ncoef, coeff]
    simp only [h₂]
    simp only [HahnSeries.zero_coeff, map_zero, smul_zero, Finset.sum_const_zero]
  · have h₃ : HahnSeries.order (B x) ≤ HahnSeries.order (B (r • x)) := by
      rw [@LinearMap.map_smul]
      refine HahnSeries.smul_order_leq r (B x) ?_
      simp_all only [map_smul, forall_const, ne_eq, not_false_eq_true]
    have h₄ : Int.toNat (-k - HahnSeries.order (B (r • x))) ≤
        Int.toNat (-k - HahnSeries.order (B x)) := by
      have h₅ : -k - HahnSeries.order (B (r • x)) ≤ -k - HahnSeries.order (B x) := by
        omega
      exact Int.toNat_le_toNat h₅
    simp only [h₁]
    rw [Finset.eventually_constant_sum (fun n => res_prod_left_summand_vanish A B m k n (r • x)) h₄]

/-- The `k`-th normalized coefficient in the left sum of the `m`-th residue product of `A` and `B`,
as a linear map.
-/
noncomputable def res_prod_left_ncoef.linearMap (A B : VertexOperator R V) (m k : ℤ) :
    Module.End R V where
  toFun := fun x => res_prod_left_ncoef A B m k x
  map_add' := by
    intro x y
    simp only [map_add, smul_add]
    exact res_prod_left_ncoef_add A B m k x y
  map_smul' := by
    intro r x
    simp only [RingHom.id_apply]
    exact res_prod_left_ncoef_smul A B m k r x

/-!
theorem res_prod_left_bdd_below (A B : VertexOperator R V) (m : ℤ) : ∃(k : ℤ), ∀(n : ℤ),
    k ≤ n → res_prod_left_ncoef.linearMap A B m n = 0 := by
  sorry

/-- The left sum of the `m`-th residue product `A(z)_m B(z)`, given by the residue of
`(x-y)^m A(x)B(y)` at `|x| > |y|`. -/
def res_prod_left (A B : VertexOperator R V) (m : ℤ) : VertexOperator R V :=
  VertexOperator_from_coeff (fun n => res_prod_left_coeff A B m (-k-1))
  {
    toMap := res_prod_left_coeff

  }

/-- The `k`-th coefficient in the right sum of the `m`-th residue product of `A` and `B`. -/
def res_prod_right_coeff (A B : VertexOperator R V) (m k : ℤ) : Module.End R V :=
  ∑ i (-1)^(m + i) • (Ring.choose m i) • (ncoef A (m - i)) (ncoef B (n + i))

/-- The right sum of the `m`-th residue product `A(z)_m B(z)`, given by the residue of
`(x-y)^m B(y)A(x)` at `|y| > |x|`. -/
def res_prod_right (A B : VertexOperator R V) (m : ℤ)

/-- The `m`-th residue product `A(z)_n B(z)` -/
residue products: to show that the residue product is a vertex operator, we need

/-- Dong's Lemma: if vertex operators `A` `B` `C` are pairwise local, then `A` is local to `B_n C`
for all integers `n`. -/
theorem local_to_residue_product (A B C : VertexOperator R V) (n : ℤ) (hAB : ) (hAC : ) (hBC : ) :
    isLocaltoOrderLeq

-/

end ResidueProduct

end VertexAlg
