/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Vertex.HVertexOperator
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.HahnSeries.Binomial
import Mathlib.RingTheory.LaurentSeries

/-!
# Vertex operators
In this file we introduce vertex operators as linear maps to Laurent series.

## Definitions
* `VertexOperator` is an `R`-linear map from an `R`-module `V` to `LaurentSeries V`.
* `VertexOperator.ncoeff` is the coefficient of a vertex operator under normalized indexing.

## TODO
* `HasseDerivative` : A divided-power derivative.
* `Locality` : A weak form of commutativity.
* `Residue products` : A family of products on `VertexOperator R V` parametrized by integers.

## References
* [G. Mason, *Vertex rings and Pierce bundles*][mason2017]
* [A. Matsuo, K. Nagatomo, *On axioms for a vertex algebra and locality of quantum
  fields*][matsuo1997]
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
def ncoeff : VertexOperator R V →ₗ[R] ℤ → Module.End R V where
  toFun A n := HVertexOperator.coeff A (-n - 1)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

theorem ncoeff_apply (A : VertexOperator R V) (n : ℤ) : ncoeff A n = coeff A (-n - 1) :=
  rfl

/-- In the literature, the `n`th normalized coefficient of a vertex operator `A` is written as
either `Aₙ` or `A(n)`. -/
scoped[VertexOperator] notation A "[[" n "]]" => ncoeff A n

@[simp]
theorem coeff_eq_ncoeff (A : VertexOperator R V)
    (n : ℤ) : HVertexOperator.coeff A n = A [[-n - 1]] := by
  rw [ncoeff_apply, neg_sub, Int.sub_neg, add_sub_cancel_left]

@[deprecated (since := "2025-08-30")] alias ncoeff_add := map_add
@[deprecated (since := "2025-08-30")] alias ncoeff_smul := map_smul

theorem ncoeff_eq_zero_of_lt_order (A : VertexOperator R V) (n : ℤ) (x : V)
    (h : -n - 1 < HahnSeries.order ((HahnModule.of R).symm (A x))) : (A [[n]]) x = 0 := by
  simp only [ncoeff, HVertexOperator.coeff, LinearMap.coe_mk, AddHom.coe_mk]
  exact HahnSeries.coeff_eq_zero_of_lt_order h

theorem coeff_eq_zero_of_lt_order (A : VertexOperator R V) (n : ℤ) (x : V)
    (h : n < HahnSeries.order ((HahnModule.of R).symm (A x))) : coeff A n x = 0 := by
  rw [coeff_eq_ncoeff, ncoeff_eq_zero_of_lt_order A (-n - 1) x]
  omega

/-- Given an endomorphism-valued function on integers satisfying a pointwise bounded-pole condition,
we produce a vertex operator. -/
noncomputable def of_coeff (f : ℤ → Module.End R V)
    (hf : ∀ x : V, ∃ n : ℤ, ∀ m : ℤ, m < n → f m x = 0) : VertexOperator R V :=
  HVertexOperator.of_coeff f
    (fun x => HahnSeries.suppBddBelow_supp_PWO (fun n => f n x)
      (HahnSeries.forallLTEqZero_supp_BddBelow (fun n => f n x)
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
  rw [ncoeff_apply, coeff_apply_apply, of_coeff_apply_coeff]

instance [CommRing R] [AddCommGroup V] [Module R V] : One (VertexOperator R V) where
  one := {
    toFun v := HahnModule.of R (HahnSeries.single 0 v)
    map_add' _ _ := by simp
    map_smul' _ _ := by simp [← HahnModule.of_smul] }

@[simp]
theorem one_apply (x : V) :
    (1 : VertexOperator R V) x = HahnModule.of R (HahnSeries.single 0 x) := by
  rfl

@[simp]
theorem one_ncoeff_neg_one : (1 : VertexOperator R V) [[-1]] = LinearMap.id := by
  ext
  rw [show -1 = - 0 - 1 by omega, ← coeff_eq_ncoeff, coeff_apply_apply, one_apply,
    Equiv.symm_apply_apply, HahnSeries.coeff_single_same, LinearMap.id_apply]

theorem one_coeff_zero : HVertexOperator.coeff (1 : VertexOperator R V) 0 = LinearMap.id := by
  ext; simp

@[simp]
theorem one_ncoeff_ne_neg_one {n : ℤ} (hn : n ≠ -1) :
    (1 : VertexOperator R V) [[n]] = 0 := by
  ext
  rw [LinearMap.zero_apply, show n = -(-n - 1) - 1 by omega, ← coeff_eq_ncoeff, coeff_apply_apply,
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
  dsimp [ncoeff]
  rw [hasseDeriv_coeff, show -n - 1 + k = -(n - k) - 1 by omega]

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
  simp only [hasseDeriv_apply_apply, Equiv.symm_apply_apply, LaurentSeries.hasseDeriv_comp,
    HahnSeries.coeff_smul, LaurentSeries.hasseDeriv_coeff, Nat.cast_add, LinearMap.smul_apply]
  exact rfl

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

section BinomComp

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (A B : VertexOperator R V)

open HVertexOperator

/-- `(X - Y)^n A(X) B(Y)` as a linear map from `V` to `V((X))((Y))` -/
def binomCompLeft (n : ℤ) : HVertexOperator (ℤ ×ₗ ℤ) R V V :=
  HahnSeries.binomialPow R (toLex (0, 1) : ℤ ×ₗ ℤ) (toLex (1, 0)) (-1 : R) n • (lexComp A B)

@[simp]
theorem binomialPow_smul_binomCompLeft (m n : ℤ) :
    HahnSeries.binomialPow R (toLex (0, 1) : ℤ ×ₗ ℤ) (toLex (1, 0)) (-1 : R) m •
      binomCompLeft A B n = binomCompLeft A B (m + n) := by
  rw [binomCompLeft, binomCompLeft, ← mul_smul, HahnSeries.binomialPow_add]

theorem binomCompLeft_apply_coeff (k l n : ℤ) (v : V) :
    (binomCompLeft A B n).coeff (toLex (k, l)) v =
      ∑ᶠ (m : ℕ), Int.negOnePow m • Ring.choose n m • A.coeff (l - n + m) (B.coeff (k - m) v) := by
  rw [binomCompLeft, coeff_apply_apply, LinearMap.smul_apply, binomialPow_smul_coeff _
    (compareOfLessAndEq_eq_lt.mp rfl)]
  exact finsum_congr fun _ ↦ by congr 2; simp; abel_nf

-- TODO : replace 2nd term on right with a version of Ring.choose that takes integer inputs.
theorem binomCompLeft_one_left_nat_coeff (n : ℕ) (g : ℤ ×ₗ ℤ) :
    (binomCompLeft 1 B n).coeff g =
      (Int.negOnePow (n - (ofLex g).2)) •
      (if (ofLex g).2 ≤ n then Ring.choose (n : ℤ) (n - (ofLex g).2).toNat else 0) •
      B.coeff ((ofLex g).1 - n + (ofLex g).2) := by
  ext v
  rw [show g = toLex ((ofLex g).1, (ofLex g).2) by rfl, binomCompLeft_apply_coeff]
  simp only [coeff_apply_apply, one_apply, Equiv.symm_apply_apply, Prod.mk.eta, toLex_ofLex]
  rw [finsum_eq_single _ ((n : ℤ) - (ofLex g).2).toNat]
  · by_cases h : (ofLex g).2 - n + (n - (ofLex g).2).toNat = 0
    · rw [h, HahnSeries.coeff_single_same 0]
      have : (n - (ofLex g).2).toNat = n - (ofLex g).2 := by omega
      have hng : (ofLex g).2 ≤ n := by omega
      simp only [this, hng, ↓reduceIte]
      congr 1
      simp only [zsmul_eq_mul, Module.End.mul_apply, Module.End.intCast_apply, coeff_apply_apply]
      abel_nf
    · rw [HahnSeries.coeff_single_of_ne h]
      simp [show ¬ (ofLex g).2 ≤ n by omega]
  · intro i hi
    have : (ofLex g).2 - n + i ≠ 0 := by omega
    rw [HahnSeries.coeff_single_of_ne this, smul_zero, smul_zero]

/-- `(X - Y)^n B(Y) A(X)` as a linear map from `V` to `V((Y))((X))` -/
def binomCompRight (n : ℤ) : HVertexOperator (ℤ ×ₗ ℤ) R V V :=
  (Int.negOnePow n : R) •
    HahnSeries.binomialPow R (toLex (0, 1) : ℤ ×ₗ ℤ) (toLex (1, 0)) (-1) n • (lexComp B A)

@[simp]
theorem binomialPow_smul_binomCompRight (m n : ℤ) :
    (Int.negOnePow m : R) • HahnSeries.binomialPow R (toLex (0, 1) : ℤ ×ₗ ℤ) (toLex (1, 0)) (-1) m •
      binomCompRight A B n = binomCompRight A B (m + n) := by
  rw [binomCompRight, binomCompRight, SMulCommClass.smul_comm, smul_smul, ← Int.cast_mul,
    ← Units.val_mul, ← Int.negOnePow_add, ← SMulCommClass.smul_comm, smul_smul,
    HahnSeries.binomialPow_add]

theorem binomCompRight_apply_coeff (k l n : ℤ) (v : V) :
    (binomCompRight A B n).coeff (toLex (k, l)) v =
      Int.negOnePow n • ∑ᶠ (m : ℕ),
        Int.negOnePow m • Ring.choose n m • B.coeff (l - n + m) (A.coeff (k - m) v) := by
  rw [binomCompRight, coeff_apply_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    HahnModule.of_symm_smul, HahnSeries.coeff_smul, binomialPow_smul_coeff _
    (compareOfLessAndEq_eq_lt.mp rfl), Int.cast_smul_eq_zsmul, Units.smul_def]
  congr 1
  refine finsum_congr fun m ↦ by congr 2; simp; abel_nf

end BinomComp

section ResidueProduct

open HVertexOperator

/-- The left side of the `m`-th residue product, given by the residue of `(x-y)^m A(x)B(y) dx` at
`x = 0`, where we formally expand `(x-y)^m` as `x^m(1-y/x)^m` in `R((x))((y))` using binomials
(i.e., in the domain where `x` is big). -/
noncomputable def resProdLeft (m : ℤ) (A B : VertexOperator R V) : VertexOperator R V :=
  ResRight (-1 : ℤ) (binomCompLeft A B m)

theorem coeff_resProdLeft_apply (A B : VertexOperator R V) (m n : ℤ) (v : V) :
    (A.resProdLeft m B).coeff n v =
      ∑ᶠ i : ℕ, Int.negOnePow i • Ring.choose m i •
        (coeff A (-1 - m + i)) ((coeff B (n - i)) v) := by
  simp only [resProdLeft, ResRight, Int.reduceNeg]
  rw [← binomCompLeft_apply_coeff A B n (-1) m]
  exact rfl

@[simp]
theorem resProdLeft_apply_ncoeff (A B : VertexOperator R V) (m n : ℤ) (v : V) :
    ((A.resProdLeft m B)[[n]]) v =
      ∑ᶠ i : ℕ, Int.negOnePow i • Ring.choose m i •
        (A[[m - i]] • (B[[n + i]] • v)) := by
  have : (A.resProdLeft m B)[[n]] = (A.resProdLeft m B).coeff (-n - 1) := rfl
  rw [this, coeff_resProdLeft_apply]
  refine finsum_congr ?_
  intro i
  congr 3
  · rw [coeff_eq_ncoeff, show (-(-1 - m + i) - 1) = (m - i) by omega]
  · rw [coeff_eq_ncoeff, show -(-n - 1 - i) - 1 = n + i by omega, Module.End.smul_def]

theorem finite_supp_ncoeff_ncoeff (m n : ℤ) (A B : VertexOperator R V) (v : V) :
    (Function.support fun (i : ℕ) ↦ (Int.negOnePow i) • Ring.choose n i •
      (ncoeff A (n - i)) ((ncoeff B (-m - 1 + i)) v)).Finite := by
  refine BddAbove.finite <| bddAbove_def.mpr ?_
  use (-((HahnModule.of R).symm (B v)).order + m).toNat
  intro j hj
  contrapose! hj
  suffices (ncoeff B (-m - 1 + j)) v = 0 by simp [this]
  have (i : ℕ) := ncoeff_eq_zero_of_lt_order B (-m - 1 + i) v
  apply this j
  omega

@[simp]
theorem resProdLeft_add_right (n : ℤ) (A B C : VertexOperator R V) :
    A.resProdLeft n (B + C) = A.resProdLeft n B + A.resProdLeft n C := by
  ext v m
  simp only [← coeff_apply_apply, coeff_eq_ncoeff, resProdLeft_apply_ncoeff, map_add, Pi.add_apply,
    Module.End.smul_def, LinearMap.add_apply, smul_add, HahnModule.of_symm_add,
    HahnSeries.coeff_add']
  exact finsum_add_distrib (finite_supp_ncoeff_ncoeff m n A B v)
    (finite_supp_ncoeff_ncoeff m n A C v)

@[simp]
theorem resProdLeft_add_left (n : ℤ) (A B C : VertexOperator R V) :
    (A + B).resProdLeft n C = A.resProdLeft n C + B.resProdLeft n C := by
  ext v m
  simp only [← coeff_apply_apply, coeff_eq_ncoeff, resProdLeft_apply_ncoeff, map_add, Pi.add_apply,
    Module.End.smul_def, LinearMap.add_apply, smul_add, HahnModule.of_symm_add,
    HahnSeries.coeff_add']
  exact finsum_add_distrib (finite_supp_ncoeff_ncoeff m n A C v)
    (finite_supp_ncoeff_ncoeff m n B C v)

@[simp]
theorem resProdLeft_smul_right (n : ℤ) (A B : VertexOperator R V) (r : R) :
    A.resProdLeft n (r • B) = r • (A.resProdLeft n B) := by
  ext v m
  simp only [← coeff_apply_apply, coeff_eq_ncoeff, resProdLeft_apply_ncoeff, map_smul,
    Pi.smul_apply, smul_assoc, Module.End.smul_def, LinearMap.smul_apply, HahnModule.of_symm_smul,
    HahnSeries.coeff_smul]
  simp_rw [smul_comm _ r]
  rw [smul_finsum' (M := V) r (finite_supp_ncoeff_ncoeff m n A B v)]

@[simp]
theorem resProdLeft_smul_left (n : ℤ) (A B : VertexOperator R V) (r : R) :
    (r • A).resProdLeft n B = r • (A.resProdLeft n B) := by
  ext v m
  simp only [← coeff_apply_apply, coeff_eq_ncoeff, resProdLeft_apply_ncoeff, map_smul,
    Pi.smul_apply, Module.End.smul_def, smul_assoc, LinearMap.smul_apply, HahnModule.of_symm_smul,
    HahnSeries.coeff_smul]
  simp_rw [smul_comm _ r]
  rw [smul_finsum' (M := V) r (finite_supp_ncoeff_ncoeff m n A B v)]

@[simp]
theorem resProdLeft_ne_neg_one_one_left {n : ℤ} (hn : n ≠ -1) (A : VertexOperator R V) :
    resProdLeft n 1 A = 0 := by
  ext
  rw [← coeff_apply_apply, coeff_eq_ncoeff, resProdLeft_apply_ncoeff]
  refine finsum_eq_zero_of_forall_eq_zero ?_
  intro i
  by_cases h : n ≥ 0
  · by_cases hni : n < i
    · set m : ℕ := n.toNat
      have : n = m := by omega
      have hmi : m < i := by omega
      rw [this, Ring.choose_natCast, (Nat.choose_eq_zero_iff).mpr hmi]
      simp
    · rw [one_ncoeff_ne_neg_one (by omega)]
      simp
  · rw [one_ncoeff_ne_neg_one (by omega)]
    simp

@[simp]
theorem resProdLeft_neg_one_one_left (A : VertexOperator R V) : resProdLeft (-1 : ℤ) 1 A  = A := by
  ext
  simp only [← coeff_apply_apply, coeff_eq_ncoeff, resProdLeft_apply_ncoeff]
  rw [finsum_eq_single _ 0 fun _ _ ↦ (by rw [one_ncoeff_ne_neg_one (by omega)]; simp)]
  simp

@[simp]
lemma resProdLeft_hasseDeriv_left (m : ℕ) (k : ℤ) (A B : VertexOperator R V) :
    (A.hasseDeriv m).resProdLeft k B =
      Int.negOnePow m • Ring.choose k m • A.resProdLeft (k - m) B := by
  ext v n
  rw [← coeff_apply_apply, ← coeff_apply_apply, show
    (coeff ((m : ℤ).negOnePow • Ring.choose k m • resProdLeft (k - m) A B) n) =
    (m : ℤ).negOnePow • Ring.choose k m • (coeff (resProdLeft (k - m) A B) n) by rfl]
  simp only [coeff_eq_ncoeff, resProdLeft_apply_ncoeff, Module.End.smul_def, zsmul_eq_mul,
    LinearMap.smul_apply, Module.End.mul_apply, Module.End.intCast_apply]
  rw [← smul_assoc (Int.negOnePow m), smul_finsum', finsum_congr]
  · intro r
    rw [hasseDeriv_ncoeff, smul_comm _ (Int.negOnePow r), smul_assoc (Int.negOnePow m),
      ← smul_assoc (Ring.choose k m), smul_eq_mul (Ring.choose k m),
      ← Ring.choose_add_smul_choose_add, smul_comm (Int.negOnePow m)]
    congr 1
    rw [show -(k - r) - 1 + m = -(k - r + 1 - m) by omega, Ring.choose_neg,
      show k - r + 1 - m + m - 1 = k - r by omega]
    simp only [smul_assoc, zsmul_eq_mul, LinearMap.smul_apply, Module.End.mul_apply,
      Module.End.intCast_apply, nsmul_eq_mul]
    rw [smul_comm (Int.negOnePow m), ← smul_assoc (Ring.choose k r), smul_eq_mul, tsub_right_comm]
    congr 1
    rw [← Ring.choose_add_smul_choose_add, add_comm r m, Int.nsmul_eq_mul, Nat.choose_symm_add]
  · have _ : Finite (Function.support fun (i : ℕ) ↦ (i : ℤ).negOnePow • Ring.choose (k - m) i •
        (ncoeff A (k - m - i)) ((ncoeff B (-n - 1 + i)) v)) :=
      finite_supp_ncoeff_ncoeff n (k - m) A B v
    refine Finite.Set.subset (Function.support fun (i : ℕ) ↦ (i : ℤ).negOnePow •
      Ring.choose (k - ↑m) i • (ncoeff A (k - ↑m - ↑i)) ((ncoeff B (-n - 1 + ↑i)) v)) ?_
    intro i hi
    simp only [Function.mem_support, ne_eq] at ⊢ hi
    contrapose! hi
    simp [hi]

/-- The right side of the `m`-th residue product, given by the residue of `(x-y)^m B(x)A(y) dx` at
`x = 0`, where we formally expand `(x-y)^m` as `(-y)^m(1-x/y)^m` using binomials (i.e., in the
domain where `x` is big). -/
noncomputable def resProdRight (m : ℤ) (A B : VertexOperator R V) : VertexOperator R V :=
  ResLeft (-1 : ℤ) (binomCompRight A B m)

theorem coeff_resProdRight_apply (A B : VertexOperator R V) (m n : ℤ) (v : V) :
    (A.resProdRight m B).coeff n v =
      (Int.negOnePow m) • ∑ᶠ i : ℕ, Int.negOnePow i • Ring.choose m i •
        (coeff B (n - m + i)) ((coeff A (-1 - i)) v) := by
  dsimp only [resProdRight, ResLeft, Int.reduceNeg, coeff_of_coeff]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, coeff_of_coeff, binomCompRight_apply_coeff]

@[simp]
theorem resProdRight_apply_ncoeff (A B : VertexOperator R V) (m n : ℤ) (v : V) :
    ((A.resProdRight m B)[[n]]) v =
      (Int.negOnePow m) • ∑ᶠ i : ℕ, Int.negOnePow i • Ring.choose m i •
        (B[[m + n - i]] • (A[[i]] • v)) := by
  have : (A.resProdRight m B)[[n]] = (A.resProdRight m B).coeff (-n - 1) := rfl
  rw [this, coeff_resProdRight_apply]
  congr 1
  refine finsum_congr ?_
  intro i
  congr 3
  · rw [coeff_eq_ncoeff, show -(-n - 1 - m + i) - 1 = (m + n - i) by omega]
  · rw [coeff_eq_ncoeff, show -((-1 : ℤ) - i) - 1 = i by omega, Module.End.smul_def]

theorem finite_supp_ncoeff_ncoeff_right (m n : ℤ) (A B : VertexOperator R V) (v : V) :
    (Function.support fun (i : ℕ) ↦ (Int.negOnePow i) • Ring.choose n i •
      (ncoeff B (n + (-m - 1) - i)) ((ncoeff A i) v)).Finite := by
  refine BddAbove.finite <| bddAbove_def.mpr ?_
  use (-((HahnModule.of R).symm (A v)).order - 1).toNat
  intro j hj
  contrapose! hj
  suffices (ncoeff A j) v = 0 by simp [this]
  apply ncoeff_eq_zero_of_lt_order A j v
  omega

@[simp]
theorem resProdRight_add_right (n : ℤ) (A B C : VertexOperator R V) :
    A.resProdRight n (B + C) = A.resProdRight n B + A.resProdRight n C := by
  ext v m
  simp only [← coeff_apply_apply, coeff_eq_ncoeff, resProdRight_apply_ncoeff, map_add, Pi.add_apply,
    Module.End.smul_def, LinearMap.add_apply, smul_add, HahnModule.of_symm_add,
    HahnSeries.coeff_add']
  rw [← smul_add]
  congr 1
  exact finsum_add_distrib (M := V) (finite_supp_ncoeff_ncoeff_right m n A B v)
    (finite_supp_ncoeff_ncoeff_right m n A C v)

@[simp]
theorem resProdRight_add_left (n : ℤ) (A B C : VertexOperator R V) :
    (A + B).resProdRight n C = A.resProdRight n C + B.resProdRight n C := by
  ext v m
  simp only [← coeff_apply_apply, coeff_eq_ncoeff, resProdRight_apply_ncoeff, map_add, Pi.add_apply,
    Module.End.smul_def, LinearMap.add_apply, smul_add, HahnModule.of_symm_add,
    HahnSeries.coeff_add']
  rw [← smul_add]
  congr 1
  exact finsum_add_distrib (M := V) (finite_supp_ncoeff_ncoeff_right m n A C v)
    (finite_supp_ncoeff_ncoeff_right m n B C v)

@[simp]
theorem resProdRight_smul_right (n : ℤ) (A B : VertexOperator R V) (r : R) :
    A.resProdRight n (r • B) = r • (A.resProdRight n B) := by
  ext v m
  simp only [← coeff_apply_apply, coeff_eq_ncoeff, resProdRight_apply_ncoeff, map_smul,
    Pi.smul_apply, Module.End.smul_def, smul_assoc, LinearMap.smul_apply, HahnModule.of_symm_smul,
    HahnSeries.coeff_smul]
  rw [smul_comm]
  congr 1
  simp_rw [smul_comm _ r]
  rw [smul_finsum' (M := V) r (finite_supp_ncoeff_ncoeff_right m n A B v)]

@[simp]
theorem resProdRight_smul_left (n : ℤ) (A B : VertexOperator R V) (r : R) :
    (r • A).resProdRight n B = r • (A.resProdRight n B) := by
  ext v m
  simp only [← coeff_apply_apply, coeff_eq_ncoeff, resProdRight_apply_ncoeff, map_smul,
    Pi.smul_apply, smul_assoc, Module.End.smul_def, LinearMap.smul_apply, HahnModule.of_symm_smul,
    HahnSeries.coeff_smul]
  rw [smul_comm]
  congr 1
  simp_rw [smul_comm _ r]
  rw [smul_finsum' (M := V) r (finite_supp_ncoeff_ncoeff_right m n A B v)]

@[simp]
theorem resProdRight_one_left (n : ℤ) (A : VertexOperator R V) :
    resProdRight n 1 A  = 0 := by
  ext
  simp only [← coeff_apply_apply, coeff_eq_ncoeff, resProdRight_apply_ncoeff]
  rw [smul_eq_zero_of_right]
  · simp [← coeff_eq_ncoeff]
  · refine finsum_eq_zero_of_forall_eq_zero ?_
    intro i
    rw [one_ncoeff_ne_neg_one (by omega)]
    simp

@[simp]
lemma resProdRight_hasseDeriv_left (m : ℕ) (k : ℤ) (A B : VertexOperator R V) :
    (A.hasseDeriv m).resProdRight k B =
      Int.negOnePow m • Ring.choose k m • A.resProdRight (k - m) B := by
  ext v n
  rw [← coeff_apply_apply, ← coeff_apply_apply, show
    (coeff ((m : ℤ).negOnePow • Ring.choose k m • resProdRight (k - m) A B) n) =
    (m : ℤ).negOnePow • Ring.choose k m • (coeff (resProdRight (k - m) A B) n) by rfl]
  simp only [coeff_eq_ncoeff, resProdRight_apply_ncoeff, Module.End.smul_def, zsmul_eq_mul,
    LinearMap.smul_apply, Module.End.mul_apply, map_zsmul_unit, Module.End.intCast_apply]
  rw [← finsum_mem_univ, finsum_mem_inter_support_eq _ (s := Set.univ) (t := Set.Ici (0 + m))]
  · have : Set.Ici (0 + m) = (fun (i : ℕ) ↦ i + m)'' Set.univ := by
      rw [← Set.image_add_const_Ici]
      exact (Set.image_eq_image (add_left_injective m)).mpr (by aesop)
    rw [this, finsum_mem_image (g := fun (i : ℕ) ↦ i + m) (by simp), finsum_mem_univ,
      ← smul_assoc _ (k - m).negOnePow, Units.smul_eq_mul, ← Int.negOnePow_add, add_sub_cancel]
    congr 1
    rw [smul_finsum' _ (finite_supp_ncoeff_ncoeff_right n (k - m) A B v), finsum_congr]
    intro i
    simp only [hasseDeriv_ncoeff, zsmul_eq_mul, Module.End.mul_apply, Module.End.intCast_apply,
      LinearMap.map_smul_of_tower]
    rw [show -(i + m : ℕ) - 1 + (m : ℤ) = - (i + 1) by omega, Ring.choose_neg, show
      (i : ℤ) + 1 + m - 1 = (m + i : ℕ) by omega, smul_comm (Ring.choose k (i + m)), smul_assoc,
      ← smul_assoc (Ring.choose _ m), Ring.choose_natCast, add_comm m i, natCast_zsmul,
      Ring.choose_add_smul_choose_add, smul_comm (Ring.choose k m), ← smul_assoc, Units.smul_eq_mul,
      ← Int.negOnePow_sub, Nat.cast_add, Int.add_sub_cancel, ← smul_assoc (Ring.choose k m)]
    congr 2
    abel_nf
  · simp only [Set.univ_inter, zero_add, Set.right_eq_inter, Function.support_subset_iff, ne_eq,
    Set.mem_Ici]
    intro i hi
    contrapose! hi
    rw [hasseDeriv_ncoeff, show -(i : ℤ) - 1 + m = -(i + 1 - m) by omega, Ring.choose_neg,
      show (i : ℤ) + 1 - m + m - 1 = i by omega, Ring.choose_natCast,
      Nat.choose_eq_zero_of_lt hi]
    simp

/-- The the `m`-th residue product of vertex operators, as a bilinear map. -/
@[simps]
def resProd (m : ℤ) :
    VertexOperator R V →ₗ[R] VertexOperator R V →ₗ[R] VertexOperator R V where
  toFun A := {
    toFun B := resProdLeft m A B - resProdRight m A B
    map_add' B C := by ext; simp; abel
    map_smul' r B := by ext; simp [smul_sub] }
  map_add' A B := by ext; simp; abel
  map_smul' r A := by ext; simp [smul_sub]

theorem resProd_neg_one_one_left (A : VertexOperator R V) : resProd (-1 : ℤ) 1 A = A := by
  rw [resProd_apply_apply, resProdLeft_neg_one_one_left, resProdRight_one_left, sub_zero]

theorem resProd_ne_neg_one_one_left {n : ℤ} (hn : n ≠ -1) (A : VertexOperator R V) :
    resProd n 1 A = 0 := by
  simp [hn]

theorem resProd_nat_one_right_apply (n : ℕ) (A : VertexOperator R V) :
    resProd n A 1 = 0 := by
  ext v m
  rw [resProd_apply_apply, ← coeff_apply_apply, ← coeff_apply_apply, coeff_eq_ncoeff, map_sub,
    Pi.sub_apply, LinearMap.sub_apply, resProdLeft_apply_ncoeff]
  rw [finsum_eq_single _ m.toNat fun _ _ ↦ (by rw [one_ncoeff_ne_neg_one (by omega)]; simp)]
  by_cases h : m ≥ 0
  · rw [show -m - 1 + m.toNat = -1 by omega, one_ncoeff_neg_one, resProdRight_apply_ncoeff]
    rw [finsum_eq_single _ (n - m).toNat fun _ _ ↦ (by rw [one_ncoeff_ne_neg_one (by omega)]; simp)]
    by_cases hmn : m ≤ n
    · rw [show n + (-m - 1) - (n - m).toNat = -1 by omega, one_ncoeff_neg_one, LinearMap.map_zero,
        Pi.zero_apply, LinearMap.zero_apply, sub_eq_zero, ← smul_assoc (n : ℤ).negOnePow]
      congr 2
      · rw [Units.ext_iff, Units.val_smul, Units.smul_def, zsmul_eq_mul', Int.cast_eq,
          ← Units.val_mul, ← Int.negOnePow_sub]
        simp [h, hmn]
      · rw [Ring.choose_natCast, Ring.choose_natCast]
        refine Int.ofNat_inj.mpr ?_
        rw [← Nat.choose_symm (by omega), show (n - m).toNat = n - m.toNat by omega]
      · simp [h, hmn]
    · rw [Ring.choose_natCast, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega),
        one_ncoeff_ne_neg_one (by omega)]
      simp [-coeff_eq_ncoeff]
  · rw [one_ncoeff_ne_neg_one (by omega), resProdRight_apply_ncoeff,
      finsum_eq_single _ (n - m).toNat fun _ _ ↦ (by rw [one_ncoeff_ne_neg_one (by omega)]; simp),
      Ring.choose_natCast n (n - m).toNat, Nat.choose_eq_zero_of_lt (by omega)]
    simp [-coeff_eq_ncoeff]

lemma resProd_hasseDeriv_left (m : ℕ) (k : ℤ) (A B : VertexOperator R V) :
    (A.hasseDeriv m).resProd k B = Int.negOnePow m • Ring.choose k m • A.resProd (k - m) B := by
  ext v n
  dsimp only [resProd]
  simp [smul_sub]

end ResidueProduct

end VertexOperator
