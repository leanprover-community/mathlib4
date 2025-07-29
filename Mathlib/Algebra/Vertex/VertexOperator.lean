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
 * `VertexOperator` : An `R`-linear map from an `R`-module `V` to `LaurentSeries V`.
 * `VertexOperator.hasseDeriv` : A divided-power derivative.
 * `VertexOperator.IsLocalToOrderLeq` : Locality is a weak form of commutativity.
 * `VertexOperator.resProd` : Residue products on `VertexOperator R V` are binary operations
   parametrized by integers.

## Main results
 * Composition rule for Hasse derivatives.
 * Comparison between Hasse derivatives and iterated derivatives.
 * locality at order `≤ n` implies locality at order `≤ n + m`.
 * Basic results on residue products

## TODO:
* residue products with identity give Hasse derivatives.
* Dong's lemma : pairwise locality implies locality with residue products.
* API for SMul by integer powers of suitable MVPolynomials, like `(X i) - (X j)`

## References
* [G. Mason *Vertex rings and Pierce bundles*][mason2017]
* [A. Matsuo, K. Nagatomo, *On axioms for a vertex algebra and locality of quantum
  fields*][matsuo1997]
* H. Li's paper on local systems?
-/

noncomputable section

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- A vertex operator over a commutative ring `R` is an `R`-linear map from an `R`-module `V` to
Laurent series with coefficients in `V`.  We write this as a specialization of the heterogeneous
case. -/
abbrev VertexOperator (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V] [Module R V] :=
  HVertexOperator ℤ R V V

namespace VertexOperator

open HVertexOperator

@[ext]
theorem ext (A B : VertexOperator R V) (h : ∀ v : V, A v = B v) :
    A = B := LinearMap.ext h

/-- The coefficient of a vertex operator under normalized indexing. -/
def ncoeff {R} [CommRing R] [AddCommGroup V] [Module R V] :
    VertexOperator R V →ₗ[R] ℤ → Module.End R V where
  toFun A n := HVertexOperator.coeff A (-n - 1)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- In the literature, the `n`th normalized coefficient of a vertex operator `A` is written as
either `Aₙ` or `A(n)`. -/
scoped[VertexOperator] notation A "[[" n "]]" => ncoeff A n

@[simp] -- simp normal form for coefficients uses ncoeff.
theorem coeff_eq_ncoeff (A : VertexOperator R V)
    (n : ℤ) : HVertexOperator.coeff A n = A [[-n - 1]] := by
  simp [ncoeff]

theorem ncoeff_eq_zero_of_lt_order (A : VertexOperator R V) (n : ℤ) (x : V)
    (h : -n - 1 < HahnSeries.order ((HahnModule.of R).symm (A x))) : (A [[n]]) x = 0 := by
  simp only [ncoeff, HVertexOperator.coeff, LinearMap.coe_mk, AddHom.coe_mk]
  exact HahnSeries.coeff_eq_zero_of_lt_order h

theorem coeff_eq_zero_of_lt_order (A : VertexOperator R V) (n : ℤ) (x : V)
    (h : n < HahnSeries.order ((HahnModule.of R).symm (A x))) :
    HVertexOperator.coeff A n x = 0 := by
  rw [coeff_eq_ncoeff, ncoeff_eq_zero_of_lt_order A (-n - 1) x]
  omega

/-- Given an endomorphism-valued formal power series satisfying a pointwise bounded-pole condition,
we produce a vertex operator. -/
noncomputable def of_coeff (f : ℤ → Module.End R V)
    (hf : ∀ x : V, ∃ n : ℤ, ∀ m : ℤ, m < n → (f m) x = 0) : VertexOperator R V :=
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
  dsimp only [ncoeff, LinearMap.coe_mk, AddHom.coe_mk, coeff_apply_apply]
  simp

instance [CommRing R] [AddCommGroup V] [Module R V] : One (VertexOperator R V) :=
  ⟨(HahnModule.lof R (Γ := ℤ) (V := V)) ∘ₗ HahnSeries.single.linearMap (0 : ℤ)⟩

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
(2025-7-29) Use Finsupp.
For weak associativity, use Y(Y(a,x)b,y)c, multiply by a suitable power of xy(x-y), compare
to Y(a,x)Y(b,y)c, after multiplying by a suitable power of xy(x-y) and a substitution.


(old)
Given a totally ordered fintype `σ`, we consider binomials in `HahnSeries (PiLex σ Z) R`.
Define binomials `X i - X j` as `varMinus hij` for `hij : i < j`.
Need to add API for comparing `varMinus i j` with `varMinus j i`(and their ℕ-powers) under permuted
order and associativity equivalences. Binomials are also Finsupps, so we can make a
function to MvPolynomial, and compare them that way.


-/

end Binomial

section BinomComp

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (A B : VertexOperator R V)

open HVertexOperator

/-- `(X - Y)^n A(X) B(Y)` as a linear map from `V` to `V((X))((Y))` -/
def binomCompLeft (n : ℤ) : HVertexOperator (ℤ ×ₗ ℤ) R V V :=
  HahnSeries.binomialPow R (toLex (0, 1) : ℤ ×ₗ ℤ) (toLex (1, 0)) n • (lexComp A B)

@[simp]
theorem binomialPow_smul_binomCompLeft (m n : ℤ) :
    HahnSeries.binomialPow R (toLex (0, 1) : ℤ ×ₗ ℤ) (toLex (1, 0)) m • binomCompLeft A B n =
      binomCompLeft A B (m + n) := by
  rw [binomCompLeft, binomCompLeft, ← mul_smul, HahnSeries.binomialPow_add]

theorem binomCompLeft_apply_coeff (k l n : ℤ) (v : V) :
    (binomCompLeft A B n).coeff (toLex (k, l)) v =
      ∑ᶠ (m : ℕ), Int.negOnePow m • Ring.choose n m • A.coeff (l - n + m) (B.coeff (k - m) v) := by
  rw [binomCompLeft, coeff_apply_apply, LinearMap.smul_apply, binomialPow_smul_coeff _ lex_basis_lt]
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
    HahnSeries.binomialPow R (toLex (0, 1) : ℤ ×ₗ ℤ) (toLex (1, 0)) n • (lexComp B A)

@[simp]
theorem binomialPow_smul_binomCompRight (m n : ℤ) :
    (Int.negOnePow m : R) • HahnSeries.binomialPow R (toLex (0, 1) : ℤ ×ₗ ℤ) (toLex (1, 0)) m •
      binomCompRight A B n = binomCompRight A B (m + n) := by
  rw [binomCompRight, binomCompRight, SMulCommClass.smul_comm, smul_smul, ← Int.cast_mul,
    ← Units.val_mul, ← Int.negOnePow_add, ← SMulCommClass.smul_comm, smul_smul,
    HahnSeries.binomialPow_add]

theorem binomCompRight_apply_coeff (k l n : ℤ) (v : V) :
    (binomCompRight A B n).coeff (toLex (k, l)) v =
      Int.negOnePow n • ∑ᶠ (m : ℕ),
        Int.negOnePow m • Ring.choose n m • B.coeff (l - n + m) (A.coeff (k - m) v) := by
  rw [binomCompRight, coeff_apply_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    HahnModule.of_symm_smul, HahnSeries.coeff_smul, binomialPow_smul_coeff _ lex_basis_lt,
    Int.cast_smul_eq_zsmul, Units.smul_def]
  congr 1
  refine finsum_congr fun m ↦ by congr 2; simp; abel_nf

end BinomComp

section Local

/-! 2025-7-20
I need some API for dealing with embeddings of the form `V((z))((w)) ↪ V⟦z, z⁻¹, w, w⁻¹⟧` and three-
variable variants, so I can compare coefficients in, e.g., Dong's Lemma efficiently. I think a
potentially good way is an `embDomain` function, like `HahnSeries.embDomain`, but replacing the
order-preserving requirement with an algebraic condition. For example, commuting two operators
should allow me to commute in all domains with a fixed embedding of `ℤ × ℤ`. I need:
 * a way to strip order off `A.coeff` (or just ask for an injective group hom)
 * functions to permute variables, or just embed.
 * Commutators of vertex operators as bare functions.
 * Scalar multiplication by Finsupps.
 * Translation from embedded positive `binomialPow` to `Finsupp`.
 * Comparison of commutator with usual composition
How do I express weak associativity in terms of power series? This seems to require a substitution.
-/
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (A B : VertexOperator R V)


/-- Two vertex operators commute if composition in the opposite order yields switched
coefficients. This should be replaced with locality at order zero. -/
def Commute : Prop :=
  swapEquiv (R := R) ((lexComp A B).coeff ∘ toLex) = (lexComp B A).coeff ∘ toLex

lemma Commute_iff :
    Commute A B ↔ ∀ (m n : ℤ), A[[n]] ∘ₗ B[[m]] = B[[m]] ∘ₗ A[[n]] := by
  simp only [Commute, swapEquiv, lexComp, coeff_eq_ncoeff, LinearMap.coe_mk, AddHom.coe_mk,
    coeff_of_coeff, LinearEquiv.coe_mk, Function.comp_apply, ofLex_toLex]
  constructor
  · intro h m n
    rw [funext_iff] at h
    specialize h (-1 - n, -1 - m)
    simpa using h
  · intro h
    ext1 g
    simp [h (-g.2 - 1) (-g.1 - 1)]

lemma commute_symm : Commute A B ↔ Commute B A := by
  rw [Commute_iff, Commute_iff]
  exact ⟨fun h m n ↦ (h n m).symm, fun h m n ↦ (h n m).symm⟩

/-- Locality to order `≤ n` means `(x-y)^n[A(x),B(y)] = 0`.  We write this condition as
vanishing of the `x^k y^l` term, for all integers `k` and `l`, but we have to switch coordinates,
since `BA` takes values in the opposite-order Hahn series. -/
def IsLocalToOrderLeq (n : ℕ) : Prop :=
  ∀ (k l : ℤ), (binomCompLeft A B n).coeff (toLex (k, l)) =
    (binomCompRight A B n).coeff (toLex (l, k))

theorem isLocalToOrderLeqAdd (m n : ℕ) (h : IsLocalToOrderLeq A B n) :
    IsLocalToOrderLeq A B (n + m) := by
  induction m with
  | zero => exact h
  | succ m ih =>
    intro k l
    rw [IsLocalToOrderLeq] at ih
    rw [← add_assoc, add_comm _ 1, Nat.cast_add, ← binomialPow_smul_binomCompLeft,
      ← binomialPow_smul_binomCompRight, HahnSeries.binomialPow_one R lex_basis_lt, sub_smul,
      LinearMap.map_sub, Pi.sub_apply]
    simp_rw [coeff_single_smul, one_smul, vadd_eq_add, neg_add_eq_sub, ← toLex_sub, Prod.mk_sub_mk,
      Int.sub_zero]
    rw [ih k (l-1), ih (k-1) l, coeff_smul, sub_smul]
    simp [coeff_single_smul, neg_add_eq_sub, ← toLex_sub]

theorem isLocal_symm (n : ℕ) (h : IsLocalToOrderLeq A B n) : IsLocalToOrderLeq B A n := by
  intro k l
  dsimp [IsLocalToOrderLeq, binomCompLeft, binomCompRight] at *
  rw [coeff_smul _ (Int.negOnePow n : R), Pi.smul_apply, h l k]
  simp [smul_smul, ← Int.cast_mul]

--show any vertex operator is local with identity.

/-!
theorem isLocal_with_hasseDeriv_left (m n : ℕ) (h : IsLocalToOrderLeq A B n) :
    IsLocalToOrderLeq (hasseDeriv m A) B (n + m) := by
  dsimp [IsLocalToOrderLeq] at *
  intro k l
  ext v
  rw [binomCompLeft_apply_coeff, binomCompRight_apply_coeff]
  simp_rw [hasseDeriv_coeff]
  sorry
-/

end Local

section ResidueProduct

open HVertexOperator

/-- The left side of the `m`-th residue product, given by the residue of `(x-y)^m A(x)B(y) dx` at
`x = 0`, where we formally expand `(x-y)^m` as `x^m(1-y/x)^m` in `R((x))((y))` using binomials
(i.e., in the domain where `x` is big). -/
noncomputable def resProdLeft (m : ℤ) (A B : VertexOperator R V) : VertexOperator R V :=
  LexResRight (binomCompLeft A B m) (-1 : ℤ)

theorem coeff_resProdLeft_apply (A B : VertexOperator R V) (m n : ℤ) (v : V) :
    (A.resProdLeft m B).coeff n v =
      ∑ᶠ i : ℕ, Int.negOnePow i • Ring.choose m i •
        (coeff A (-1 - m + i)) ((coeff B (n - i)) v) := by
  dsimp only [resProdLeft, LexResRight, Int.reduceNeg, coeff_of_coeff]
  rw [binomCompLeft_apply_coeff]

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
    Pi.smul_apply, Module.End.smul_def, LinearMap.smul_apply, HahnModule.of_symm_smul,
    HahnSeries.coeff_smul']
  simp_rw [smul_comm _ r]
  rw [smul_finsum' (M := V) r (finite_supp_ncoeff_ncoeff m n A B v)]

@[simp]
theorem resProdLeft_smul_left (n : ℤ) (A B : VertexOperator R V) (r : R) :
    (r • A).resProdLeft n B = r • (A.resProdLeft n B) := by
  ext v m
  simp only [← coeff_apply_apply, coeff_eq_ncoeff, resProdLeft_apply_ncoeff, map_smul,
    Pi.smul_apply, Module.End.smul_def, LinearMap.smul_apply, HahnModule.of_symm_smul,
    HahnSeries.coeff_smul']
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
      rw [this, Ring.choose_eq_nat_choose, (Nat.choose_eq_zero_iff).mpr hmi]
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
  rw [← coeff_apply_apply, ← coeff_apply_apply]
  simp only [coeff_eq_ncoeff, resProdLeft_apply_ncoeff, Module.End.smul_def, map_zsmul_unit,
    LinearMap.map_smul_of_tower, zsmul_eq_mul, Pi.smul_apply, Pi.mul_apply, Pi.intCast_apply,
    LinearMap.smul_apply, Module.End.mul_apply, Module.End.intCast_apply]
  rw [← smul_assoc (Int.negOnePow m), smul_finsum', finsum_congr]
  · intro r
    rw [hasseDeriv_ncoeff, smul_comm _ (Int.negOnePow r), smul_assoc (Int.negOnePow m),
      ← smul_assoc (Ring.choose k m), smul_eq_mul (Ring.choose k m), ← Ring.choose_add_smul_choose,
      smul_comm (Int.negOnePow m)]
    congr 1
    rw [show -(k - r) - 1 + m = -(k - r + 1 - m) by omega, Ring.choose_neg,
      show k - r + 1 - m + m - 1 = k - r by omega]
    simp only [smul_assoc, zsmul_eq_mul, LinearMap.smul_apply, Module.End.mul_apply,
      Module.End.intCast_apply, nsmul_eq_mul]
    rw [smul_comm (Int.negOnePow m), ← smul_assoc (Ring.choose k r), smul_eq_mul,
      ← Ring.choose_add_smul_choose]
    congr 2
    · rw [add_comm m r, Nat.choose_symm_add]
    · rw [add_comm m r]
    · rw [tsub_right_comm]
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
  LexResLeft (-1 : ℤ) (binomCompRight A B m)

theorem coeff_resProdRight_apply (A B : VertexOperator R V) (m n : ℤ) (v : V) :
    (A.resProdRight m B).coeff n v =
      (Int.negOnePow m) • ∑ᶠ i : ℕ, Int.negOnePow i • Ring.choose m i •
        (coeff B (n - m + i)) ((coeff A (-1 - i)) v) := by
  dsimp only [resProdRight, LexResLeft, Int.reduceNeg, coeff_of_coeff]
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
    Module.End.smul_def, LinearMap.add_apply, HahnModule.of_symm_add, HahnSeries.coeff_add']
  rw [← smul_add]
  congr 1
  simp only [smul_add]
  exact finsum_add_distrib (M := V) (finite_supp_ncoeff_ncoeff_right m n A B v)
    (finite_supp_ncoeff_ncoeff_right m n A C v)

@[simp]
theorem resProdRight_add_left (n : ℤ) (A B C : VertexOperator R V) :
    (A + B).resProdRight n C = A.resProdRight n C + B.resProdRight n C := by
  ext v m
  simp only [← coeff_apply_apply, coeff_eq_ncoeff, resProdRight_apply_ncoeff, map_add, Pi.add_apply,
    Module.End.smul_def, LinearMap.add_apply, HahnModule.of_symm_add, HahnSeries.coeff_add']
  rw [← smul_add]
  congr 1
  simp only [smul_add]
  exact finsum_add_distrib (M := V) (finite_supp_ncoeff_ncoeff_right m n A C v)
    (finite_supp_ncoeff_ncoeff_right m n B C v)

@[simp]
theorem resProdRight_smul_right (n : ℤ) (A B : VertexOperator R V) (r : R) :
    A.resProdRight n (r • B) = r • (A.resProdRight n B) := by
  ext v m
  simp only [← coeff_apply_apply, coeff_eq_ncoeff, resProdRight_apply_ncoeff, map_smul,
    Pi.smul_apply, Module.End.smul_def, LinearMap.smul_apply, HahnModule.of_symm_smul,
    HahnSeries.coeff_smul']
  rw [smul_comm]
  congr 1
  simp_rw [smul_comm _ r]
  rw [smul_finsum' (M := V) r (finite_supp_ncoeff_ncoeff_right m n A B v)]

@[simp]
theorem resProdRight_smul_left (n : ℤ) (A B : VertexOperator R V) (r : R) :
    (r • A).resProdRight n B = r • (A.resProdRight n B) := by
  ext v m
  simp only [← coeff_apply_apply, coeff_eq_ncoeff, resProdRight_apply_ncoeff, map_smul,
    Pi.smul_apply, Module.End.smul_def, LinearMap.smul_apply, HahnModule.of_symm_smul,
    HahnSeries.coeff_smul']
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
  · simp
  · refine finsum_eq_zero_of_forall_eq_zero ?_
    intro i
    rw [one_ncoeff_ne_neg_one (by omega)]
    simp

@[simp]
lemma resProdRight_hasseDeriv_left (m : ℕ) (k : ℤ) (A B : VertexOperator R V) :
    (A.hasseDeriv m).resProdRight k B =
      Int.negOnePow m • Ring.choose k m • A.resProdRight (k - m) B := by
  ext v n
  rw [← coeff_apply_apply, coeff_eq_ncoeff, resProdRight_apply_ncoeff, ← finsum_mem_univ,
    finsum_mem_inter_support_eq _ (s := Set.univ) (t := Set.Ici (0 + m))]
  · have : Set.Ici (0 + m) = (fun (i : ℕ) ↦ i + m)'' Set.univ := by
      rw [← Set.image_add_const_Ici]
      exact (Set.image_eq_image (add_left_injective m)).mpr (by aesop)
    rw [this, finsum_mem_image (g := fun (i : ℕ) ↦ i + m) (by field_simp), finsum_mem_univ,
      ← coeff_apply_apply, coeff_eq_ncoeff]
    simp only [Module.End.smul_def, map_zsmul_unit, LinearMap.map_smul_of_tower,
      zsmul_eq_mul, Pi.smul_apply, Pi.mul_apply, Pi.intCast_apply, LinearMap.smul_apply,
      Module.End.mul_apply, resProdRight_apply_ncoeff, Module.End.intCast_apply]
    rw [← smul_assoc _ (k - m).negOnePow, Int.negOnePow_smul, ← Int.negOnePow_add, add_sub_cancel]
    congr 1
    rw [smul_finsum' _ (finite_supp_ncoeff_ncoeff_right n (k - m) A B v), finsum_congr]
    intro i
    simp only [hasseDeriv_ncoeff, zsmul_eq_mul, Module.End.mul_apply, Module.End.intCast_apply,
      LinearMap.map_smul_of_tower]
    rw [show -(i + m : ℕ) - 1 + (m : ℤ) = - (i + 1) by omega, Ring.choose_neg, show
      (i : ℤ) + 1 + m - 1 = (m + i : ℕ) by omega, smul_comm (Ring.choose k (i + m)), smul_assoc,
      ← smul_assoc (Ring.choose _ m), Ring.choose_eq_nat_choose, add_comm m i, natCast_zsmul,
      Ring.choose_add_smul_choose, smul_comm (Ring.choose k m), ← smul_assoc, Int.negOnePow_smul,
      ← Int.negOnePow_sub, Nat.cast_add, Int.add_sub_cancel, ← smul_assoc (Ring.choose k m)]
    congr 2
    abel_nf
  · simp only [Module.End.smul_def, Set.univ_inter, Set.right_eq_inter, ne_eq, Set.mem_Ici,
      Function.support_subset_iff]
    intro i hi
    contrapose! hi
    rw [hasseDeriv_ncoeff, show -(i : ℤ) - 1 + m = -(i + 1 - m) by omega, Ring.choose_neg,
      show (i : ℤ) + 1 - m + m - 1 = i by omega, Ring.choose_eq_nat_choose,
      Nat.choose_eq_zero_of_lt (lt_of_lt_of_eq hi (zero_add m))]
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
  rw [resProd_apply_apply, ← coeff_apply_apply, ← coeff_apply_apply, coeff_eq_ncoeff,
    map_sub, Pi.sub_apply, LinearMap.sub_apply, resProdLeft_apply_ncoeff]
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
      · rw [Ring.choose_eq_nat_choose, Ring.choose_eq_nat_choose]
        refine Int.ofNat_inj.mpr ?_
        rw [← Nat.choose_symm (by omega), show (n - m).toNat = n - m.toNat by omega]
      · simp [h, hmn]
    · rw [Ring.choose_eq_nat_choose, Ring.choose_eq_nat_choose, Nat.choose_eq_zero_of_lt (by omega),
        one_ncoeff_ne_neg_one (by omega)]
      simp
  · rw [one_ncoeff_ne_neg_one (by omega), resProdRight_apply_ncoeff,
      finsum_eq_single _ (n - m).toNat fun _ _ ↦ (by rw [one_ncoeff_ne_neg_one (by omega)]; simp),
      Ring.choose_eq_nat_choose n (n - m).toNat, Nat.choose_eq_zero_of_lt (by omega)]
    simp

lemma resProd_hasseDeriv_left (m : ℕ) (k : ℤ) (A B : VertexOperator R V) :
    (A.hasseDeriv m).resProd k B = Int.negOnePow m • Ring.choose k m • A.resProd (k - m) B := by
  ext v n
  dsimp only [resProd]
  simp [smul_sub]

-- locality: If `A.IsLocalToOrderLeq B n`, then `A.resProd k B = 0` when `n ≤ k`.

/-- A product of integer powers of three binomials. -/
abbrev tripleProductLeft (p q r : ℤ) : HahnSeries ((ℤ ×ₗ ℤ) ×ₗ ℤ) R :=
    HahnSeries.binomialPow R (toLex (toLex (1, 0), 0) : (ℤ ×ₗ ℤ) ×ₗ ℤ) (toLex (toLex (0, 1), 0)) p *
    HahnSeries.binomialPow R (toLex (toLex (0, 1), 0) : (ℤ ×ₗ ℤ) ×ₗ ℤ) (toLex (toLex (0, 1), 0)) q *
    HahnSeries.binomialPow R (toLex (toLex (1, 0), 0) : (ℤ ×ₗ ℤ) ×ₗ ℤ) (toLex (toLex (0, 0), 1)) r

/-- A product of integer powers of three binomials. -/
abbrev tripleProductRight (p q r : ℤ) : HahnSeries (ℤ ×ₗ (ℤ ×ₗ ℤ)) R :=
    HahnSeries.binomialPow R (toLex (1, toLex (0, 0)) : ℤ ×ₗ (ℤ ×ₗ ℤ)) (toLex (0, toLex (1, 0))) p *
    HahnSeries.binomialPow R (toLex (0, toLex (1, 0)) : ℤ ×ₗ (ℤ ×ₗ ℤ)) (toLex (0, toLex (0, 1))) q *
    HahnSeries.binomialPow R (toLex (1, toLex (0, 0)) : ℤ ×ₗ (ℤ ×ₗ ℤ)) (toLex (0, toLex (0, 1))) r
/-!
lemma triple_product_left_nat (k l m : ℕ) (p q r : ℤ) :
    (tripleProductLeft k l m).coeff (toLex (toLex (p, q), r)) =
    (tripleProductRight (R := R) k l m).coeff (toLex (p, toLex (q, r))) := by
  simp [tripleProductLeft, tripleProductRight]
  sorry

/-!
`A(x)B(y)C(z)` is `lexComp A (lexComp B C)`, but coefficients of
`B(y)A(x)C(z) = lexComp B (lexComp A C)` are switched, so I need to multiply by a different Hahn
Hahn series.
C(z)A(x)B(y) - C(z)B(y)A(x)
-/

/-- Lemma 1.5.4 of Matsuo-Nagatomo. If `A(x)`, `B(y)`, and `C(z)` are mutually local vertex
operators, then `A(x)B(y)C(z) - B(y)A(x)C(z) = C(z)A(x)B(y) - C(z)B(y)A(x)` holds after
multiplication by a suitable polynomial of the form `(x-y)^m(y-z)^l(x-z)^k`.  In particular, if the
orders of locality are `nAB`, `nAC`, and `nBC`, then for any integers k,l,m, and any
`n` satisfying `(nAC - k) + (nBC - l) + (nAB - m) - 1 ≤ n`, the previous equation times
`(x-y)^m(y-z)^l(x-z)^k(y-z)^n` holds. -/
lemma comp_local (A B C : VertexOperator R V) (n p q r : ℤ) (k l m : ℕ)
    (hAB : IsLocalToOrderLeq A B k) (hAC : IsLocalToOrderLeq A C l)
    (hBC : IsLocalToOrderLeq B C m) :
    (HahnSeries.binomialPow R (toLex (1, toLex (0, 0)) : ℤ ×ₗ (ℤ ×ₗ ℤ))
      (toLex (0, toLex (1, 0))) (k - n : ℤ) •
    HahnSeries.binomialPow R (toLex (0, toLex (1, 0)) : ℤ ×ₗ (ℤ ×ₗ ℤ))
      (toLex (0, toLex (0, 1))) (m : ℤ) •
    HahnSeries.binomialPow R (toLex (1, toLex (0, 0)) : ℤ ×ₗ (ℤ ×ₗ ℤ))
      (toLex (0, toLex (0, 1))) (l : ℤ) •
    HahnSeries.binomialPow R (toLex (1, toLex (0, 0)) : ℤ ×ₗ (ℤ ×ₗ ℤ)) (toLex (0, toLex (1, 0))) n •
    lexComp (lexComp A B) C).coeff (toLex (p, toLex (q, r))) =
    (HahnSeries.binomialPow R (toLex (toLex (1, 0), 0) : (ℤ ×ₗ ℤ) ×ₗ ℤ)
      (toLex (toLex (0, 1), 0)) (k - n : ℤ) •
    HahnSeries.binomialPow R (toLex (toLex (0, 1), 0) : (ℤ ×ₗ ℤ) ×ₗ ℤ)
      (toLex (toLex (0, 1), 0)) (m : ℤ) •
    HahnSeries.binomialPow R (toLex (toLex (1, 0), 0) : (ℤ ×ₗ ℤ) ×ₗ ℤ)
      (toLex (toLex (0, 0), 1)) (l : ℤ) •
    HahnSeries.binomialPow R (toLex (toLex (1, 0), 0) : (ℤ ×ₗ ℤ) ×ₗ ℤ) (toLex (toLex (0, 1), 0)) n •
    lexComp A (lexComp B C)).coeff (toLex (toLex (p, q), r)) := by
  sorry


/-- Dong's Lemma (Matsuo-Nagatomo Lemma 1.5.5): if vertex operators `A` `B` `C` are pairwise local,
then `A` is local to `B_n C`　for all integers `n`. -/
theorem local_residue_product (A B C : VertexOperator R V) (n : ℤ) (k l m : ℕ)
    (hAB : IsLocalToOrderLeq A B k) (hAC : IsLocalToOrderLeq A C l)
    (hBC : IsLocalToOrderLeq B C m) :
    IsLocalToOrderLeq (resProd n A B) C (k + l + m - n + 3).toNat := by
  sorry  -- suffices to show triple products are equal after multiplying by
  --`(X_A - X_B)^{k-n} (X_B - X_C)^m (X_A - X_C)^l` -- follows from previous lemma


Cauchy-Jacobi : `[A(x),[B(y),C(z)]] + [B(y),[C(z),A(x)]] + [C(z),[A(x),B(y)]] = 0`.  This means, for
any k,l,m ∈ ℤ, the `x^k y^l z^m` coefficient vanishes, or equivalently, the usual Jacobi for
`A.coeff k`, `B.coeff l`, and `C.coeff m`. We expand the 12 terms as cancelling Hahn series, and
multiply by integer powers of `(x-y)`, `(x-z)`, and `(y-z)`.

It may be better to work on the level of coefficient functions for locality. Then, commutators are
just formal functions, and we can multiply by Finsupps.  So IsLocal means commutator is annihilated
by a power of `(X-Y)`.

-/

end ResidueProduct

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

end VertexOperator
