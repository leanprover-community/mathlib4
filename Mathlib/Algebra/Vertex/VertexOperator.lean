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
* Residue products : This is a family of products on `VertexOperator R V` parametrized by integers.
## Main results
* Composition rule for Hasse derivatives.
* Comparison between Hasse derivatives and iterated derivatives.
* Boundedness lemmas for defining residue products
## To do:
* Write iterated vertex operators as Hahn series on lex order product.
* Write iterated Laurent series `V((X))((Y))` as Hahn series - make API for variables.
* locality at order `≤ n` implies locality at order `≤ n + 1`.
* residue products with identity give Hasse derivatives.
* Dong's lemma : pairwise locality implies locality with residue products.
## References
* G. Mason `Vertex rings and Pierce bundles` ArXiv 1707.00328
* A. Matsuo, K. Nagatomo `On axioms for a vertex algebra and locality of quantum fields`
  arXiv:hep-th/9706118
* H. Li's paper on local systems?
-/

variable {Γ : Type*} [PartialOrder Γ] {R : Type*} {V W : Type*} [CommRing R] [AddCommGroup V]
  [Module R V] [AddCommGroup W] [Module R W]

/-- A heterogeneous `Γ`-vertex operator over a commutator ring `R` is an `R`-linear map from an
`R`-module `V` to `Γ`-Hahn series with coefficients in an `R`-module `W`.-/
abbrev HetVertexOperator (Γ : Type*) (R : Type*) (V : Type*) (W : Type*) [PartialOrder Γ]
[CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] := V →ₗ[R] HahnSeries Γ W

/-- A vertex operator over a commutative ring `R` is an `R`-linear map from an `R`-module `V` to
Laurent series with coefficients in `V`. -/
abbrev VertexOperator (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V]
    [Module R V] := V →ₗ[R] LaurentSeries V

namespace VertexAlg

/-- The coefficient of a heterogeneous vertex operator, viewed as a formal power series with
coefficients in linear maps. -/
@[simps]
def coeff (A : HetVertexOperator Γ R V W) (n : Γ) :
    V →ₗ[R] W :=
  {
    toFun := fun (x : V) => (A x).coeff n
    map_add' := by simp only [map_add, HahnSeries.add_coeff', Pi.add_apply, forall_const]
    map_smul' := by simp only [map_smul, HahnSeries.smul_coeff, RingHom.id_apply, forall_const]
  }

/-- We write `ncoef` instead of `coefficient of a vertex operator under normalized indexing`.
Alternative suggestions welcome. -/
def ncoef [CommRing R] [AddCommGroup V] [Module R V] (A : VertexOperator R V) (n : ℤ) :
    Module.End R V := coeff A (-n - 1)

theorem coeff_eq_ncoef (A : VertexOperator R V)
    (n : ℤ) : coeff A n = ncoef A (-n - 1) := by
  rw [ncoef, neg_sub, sub_neg_eq_add, add_sub_cancel']

/-- The normal convention for the normalized coefficient of a vertex operator is either `Aₙ` or
`A(n)`.  We choose a notation that looks a bit like the TeX input. -/
scoped[VertexAlg] notation A "_[" n "]" => ncoef A n

theorem ncoef_eq_zero_of_lt_order (A : VertexOperator R V) (n : ℤ) (x : V)
    (h : -n - 1 < HahnSeries.order (A x)) : ncoef A n x = 0 := by
  simp only [ncoef, coeff, LinearMap.coe_mk, AddHom.coe_mk]
  exact HahnSeries.coeff_eq_zero_of_lt_order h

theorem coeff_eq_zero_of_lt_order (A : VertexOperator R V) (n : ℤ) (x : V)
    (h : n < HahnSeries.order (A x)) : coeff A n x = 0 := by
  rw [coeff_eq_ncoef, ncoef_eq_zero_of_lt_order A (-n - 1) x]
  omega

theorem ncoef_ofForallLTEqZero (f : ℤ → V) (n : ℤ) (h : ∀(m : ℤ), n < m → f m = 0) : ∀(m : ℤ),
    m < (-n - 1) → f (-m - 1) = 0 := by
  intro m' hm'
  have h' : n < (-m' - 1) := by omega
  apply h (-m' - 1) h'

/-- Given a coefficient function valued in linear maps satisfying a partially well-ordered support
condition, we produce a heterogeneous vertex operator. -/
noncomputable def HetVertexOperator.of_coeff (f : Γ → V →ₗ[R] W)
    (hf : ∀(x : V), (Function.support (fun g => f g x)).IsPWO) : HetVertexOperator Γ R V W where
  toFun := fun x => {
    coeff := fun g => f g x
    isPWO_support' := hf x
  }
  map_add' := by
    intros
    simp only [map_add]
    exact rfl
  map_smul' := by
    intros
    simp only [map_smul, RingHom.id_apply]
    exact rfl

/-- Given an endomorphism-valued formal power series satisfying a pointwise bounded-pole condition,
we produce a vertex operator. -/
noncomputable def VertexOperator.of_coeff (f : ℤ → Module.End R V)
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

theorem one_ncoef_neg_one (x : V) : @ncoef R V _ _ _ 1 (-1) x = x := by
  rw [one]
  unfold ncoef HahnSeries.single.linearMap HahnSeries.single.addMonoidHom HahnSeries.single
    Pi.single Function.update
  simp_all only [eq_rec_constant, Pi.zero_apply, dite_eq_ite]
  exact rfl

theorem one_ncoef_ne_neg_one (x : V) (n : ℤ) (hn : n ≠ -1): @ncoef R V _ _ _ 1 n x = 0 := by
  rw [one]
  unfold ncoef HahnSeries.single.linearMap HahnSeries.single.addMonoidHom HahnSeries.single
    Pi.single Function.update
  simp_all only [ne_eq, eq_rec_constant, Pi.zero_apply, dite_eq_ite, coeff_apply, LinearMap.coe_mk]
  simp_all only [AddHom.coe_mk, ite_eq_right_iff]
  have h' : ¬ -n-1 = 0 := by omega
  exact fun a ↦ (h' a).elim

theorem one_ncoef_ite (x : V) (n : ℤ) : @ncoef R V _ _ _ 1 n x = if n = (-1) then x else 0 := by
  by_cases h : n = -1
  · simp_all only [ite_true]
    exact one_ncoef_neg_one x
  · simp_all only [ite_false]
    exact one_ncoef_ne_neg_one x n h

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

section Composite

/-- This is a summand in the sum defining `composite.ncoef`.  It is a scalar multiple of
`A_{m+n-i}B_{k+i}x`.  More specifically, it is the summand of fixed `i` for the
`x^{-n-1}y^{-k-1}` term in `g(x,y)A(x)B(y)` for `g(x,y) = ∑ f(i) x^{m-i}y^i`. -/
def composite_summand (A B : VertexOperator R V) (m n k : ℤ) (i : ℕ) (f : ℕ → ℤ) :
    Module.End R V where
  toFun := fun x => (f i) • (ncoef A (m + n - i)) (ncoef B (k + i) x)
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
    tsub_le_iff_right, ncoef, coeff]
  have hi : (- (k + i) - 1) < HahnSeries.order (B x) := by omega
  rw [HahnSeries.coeff_eq_zero_of_lt_order hi, LinearMap.map_zero, HahnSeries.zero_coeff, smul_zero]

/-!
theorem composite_summand_eq_zero_of_lt_order_left (A B : VertexOperator R V) (m n k : ℤ) (i : ℕ)
    (f : ℤ → ℕ → ℤ) (x : V)
    (h : Int.toNat (-m + i - HahnSeries.order (A (ncoef B (k + i) x))) ≤ n) :
    (composite_summand A B m n k i f) x = 0 := by
  sorry
-/

theorem composite_summand_smul (A B : VertexOperator R V) (m n k : ℤ) (i : ℕ) (f : ℕ → ℤ)
    (r : R) (x : V) : r • composite_summand A B m n k i f x =
    composite_summand A B m n k i f (r • x) := by
  unfold composite_summand
  simp only [LinearMap.coe_mk, AddHom.coe_mk, map_smul]

/-- This is the `x^{-n-1}y^{-k-1}` term in `g(x,y)A(x)B(y)` where `g(x,y) = ∑ f(m,i) x^{m-i}y^i`.-/
noncomputable def composite_ncoef (A B : VertexOperator R V) (m n k : ℤ) (f : ℕ → ℤ) (x : V) :
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

theorem composite_ncoef_add (A B : VertexOperator R V) (m n k : ℤ) (f : ℕ → ℤ) (x y : V) :
    composite_ncoef A B m n k f (x + y) = (composite_ncoef A B m n k f x) +
    (composite_ncoef A B m n k f y) := by
  unfold composite_ncoef
  refine @eventually_constant_sum_add V _ V _
    (fun (x : V) => Int.toNat (-k - HahnSeries.order (B x)))
    (fun i => composite_summand A B m n k i f) ?_ x y
  intro z i hi
  simp_all only [AddMonoidHom.coe_coe]
  exact @composite_summand_eq_zero_of_lt_order_right R V _ _ _ A B m n k i f z hi

theorem composite_ncoef_smul (A B : VertexOperator R V) (m n k : ℤ) (f : ℕ → ℤ) (r : R)
    (x : V) : composite_ncoef A B m n k f (r • x) = r • composite_ncoef A B m n k f x := by
  simp only [composite_ncoef, Finset.smul_sum, composite_summand_smul]
  by_cases h₂ : B (r • x) = 0
  · simp only [composite_summand, LinearMap.coe_mk, AddHom.coe_mk, ncoef, coeff]
    simp only [h₂]
    simp only [HahnSeries.zero_coeff, map_zero, smul_zero, Finset.sum_const_zero]
  · have h₃ : HahnSeries.order (B x) ≤ HahnSeries.order (B (r • x)) := by
      rw [@LinearMap.map_smul]
      refine HahnSeries.smul_order_leq r (B x) ?_
      simp_all only [map_smul, forall_const, ne_eq, not_false_eq_true]
    have h₄ : Int.toNat (-k - HahnSeries.order (B (r • x))) ≤
        Int.toNat (-k - HahnSeries.order (B x)) := by
      have h₅ : -k - HahnSeries.order (B (r • x)) ≤ -k - HahnSeries.order (B x) := by omega
      exact Int.toNat_le_toNat h₅
    rw [Finset.eventually_constant_sum
      (fun i => composite_summand_eq_zero_of_lt_order_right A B m n k i f (r • x)) h₄]

/-- The coefficient of a composite of vertex operators as a linear map. -/
noncomputable def composite_ncoef.linearMap (A B : VertexOperator R V) (m n k : ℤ) (f : ℕ → ℤ) :
    Module.End R V where
  toFun := fun x => composite_ncoef A B m n k f x
  map_add' := by
    intro x y
    simp only [map_add, smul_add]
    exact composite_ncoef_add A B m n k f x y
  map_smul' := by
    intro r x
    simp only [RingHom.id_apply]
    exact composite_ncoef_smul A B m n k f r x

theorem composite_bdd_below_right (A B : VertexOperator R V) (m n : ℤ) (f : ℕ → ℤ) (x : V) (k : ℤ)
    (hk : - HahnSeries.order (B x) < k) : composite_ncoef A B m n k f x = 0 := by
  unfold composite_ncoef
  have h : Int.toNat (-k - HahnSeries.order (B x)) = 0 := by
    refine Int.toNat_eq_zero.mpr ?_
    omega
  rw [h, Finset.sum_range_zero]

theorem composite_bdd_below_left (A B : VertexOperator R V) (m k : ℤ) (f : ℕ → ℤ) (x : V) :
    ∃(z : ℤ), ∀(n : ℤ), z - m < n → composite_ncoef.linearMap A B m n k f x = 0 := by
  let bd : ℕ → ℤ := fun i => i - (HahnSeries.order (A (ncoef B (k + i) x)))
  have hbd: ∀(i : ℕ) (n : ℤ), (bd i) ≤ m + n → (ncoef A (m + n - i)) (ncoef B (k + i) x) = 0 := by
    intro i n hn
    simp_all only [tsub_le_iff_right]
    refine ncoef_eq_zero_of_lt_order A (m + n - i) (ncoef B (k + i) x) ?_
    omega
  use Nat.cast (Finset.sup (Finset.range (Int.toNat (-k - HahnSeries.order (B x))))
    (fun i => Int.toNat (bd i)))
  intro n hn
  unfold composite_ncoef.linearMap composite_ncoef composite_summand
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
  ∀ (k l : ℤ) (x : V), (composite_ncoef A B N k l
  (fun i => (-1)^i • (Nat.choose N i)) x) =
  (composite_ncoef B A N l k (fun i => (-1)^i • (Nat.choose N i)) x)

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

section ResidueProduct

theorem res_prod_left_bound (A B : VertexOperator R V) (m : ℤ): ∀(x : V), ∃(n : ℤ), ∀(k : ℤ),
    k < n → composite_ncoef.linearMap A B m 0 (-k - 1)
    (fun i ↦ (-1) ^ i • Ring.choose m i) x = 0 := by
  intro x
  use HahnSeries.order (B x) - 1
  intro k hk
  have h : - HahnSeries.order (B x) < (-k - 1) := by omega
  exact composite_bdd_below_right A B m 0 (fun i => (-1)^i • Ring.choose m i) x (-k - 1) h

/-- The left side of the `m`-th residue product, given by the residue of `(x-y)^m A(x)B(y)` at
`x=0`, where we formally expand `(x-y)^m` as `x^m(1-y/x)^m` using binomials. -/
noncomputable def res_prod_left (A B : VertexOperator R V) (m : ℤ) : VertexOperator R V :=
  VertexOperator.of_coeff (fun n => composite_ncoef.linearMap A B m 0 (-n - 1)
  (fun i => (-1)^i • Ring.choose m i)) (res_prod_left_bound A B m)

theorem res_prod_right_bound (A B : VertexOperator R V) (m : ℤ): ∀(x : V), ∃(N : ℤ), ∀(k : ℤ),
    k < N → composite_ncoef.linearMap A B m (-k - 1) 0
    (fun i ↦ (-1 : ℤˣ)^(m + i) • Ring.choose m i) x = 0 := by
  intro x
  use (-Exists.choose
    (composite_bdd_below_left A B m 0 (fun i ↦ (-1 : ℤˣ)^(m + i) • Ring.choose m i) x)) + m - 1
  intro k hk
  refine (Exists.choose_spec
    (composite_bdd_below_left A B m 0 (fun i ↦ (-1 : ℤˣ)^(m + i) • Ring.choose m i) x)) (-k - 1) ?_
  omega

/-- The right side of the `m`-th residue product, given by the residue of `(x-y)^m B(x)A(y)` at
`x=0`, where we formally expand `(x-y)^m` as `(-y)^m(1-x/y)^m` using binomials (i.e., in the domain
where `x` is big). -/
noncomputable def res_prod_right (A B : VertexOperator R V) (m : ℤ) : VertexOperator R V :=
  VertexOperator.of_coeff (fun n => composite_ncoef.linearMap B A m (-n - 1) 0
  (fun i => (-1 : ℤˣ)^(m + i) • Ring.choose m i)) (res_prod_right_bound B A m)

/-- The the `m`-th residue product of vertex operators -/
noncomputable def res_prod (A B : VertexOperator R V) (m : ℤ) : VertexOperator R V :=
  res_prod_left A B m + res_prod_right A B m
/-!
theorem res_prod_neg_one_one_left (A : VertexOperator R V) : res_prod 1 A (-1) = A := by
  ext x n
  unfold res_prod res_prod_left res_prod_right composite_ncoef.linearMap composite_ncoef
  unfold composite_summand
  simp only [neg_sub, sub_neg_eq_add, smul_eq_mul, add_zero, LinearMap.coe_mk, AddHom.coe_mk,
    neg_zero, zero_sub, zero_add, smul_assoc, LinearMap.add_apply, HahnSeries.add_coeff',
    Pi.add_apply]

  sorry

residue products with 1, interaction with Hasse derivatives.

/-- Dong's Lemma: if vertex operators `A` `B` `C` are pairwise local, then `A` is local to `B_n C`
for all integers `n`. -/
theorem local_to_residue_product (A B C : VertexOperator R V) (n : ℤ) (k l m : ℕ)
    (hAB : isLocaltoOrderLeq A B k) (hAC : isLocaltoOrderLeq A C l)
    (hBC : isLocaltoOrderLeq B C m) : isLocaltoOrderLeq (k + l + m) := by
  sorry
-/

end ResidueProduct

end VertexAlg
