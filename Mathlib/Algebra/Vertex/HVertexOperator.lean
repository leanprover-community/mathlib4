/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.RingTheory.HahnSeries.Binomial

/-!
# Heterogeneous vertex operators
In this file we introduce heterogeneous vertex operators using Hahn series.  When `R = ℂ`, `V = W`,
and `Γ = ℤ`, then this is the usual notion of "meromorphic left-moving 2D field".  The notion we use
here allows us to consider composites and scalar-multiply by multivariable Laurent series.

## Definitions
* `HVertexOperator` : An `R`-linear map from an `R`-module `V` to `HahnModule Γ W`.
* The coefficient function as an `R`-linear map.
* Composition of heterogeneous vertex operators - values are Hahn series on lex order product.

## Main results
* `HahnSeries Γ R`-module structure on `HVertexOperator Γ R V W`.  This means we can consider
  products of the form `(X-Y)^n A(X)B(Y)` for all integers `n`, where `(X-Y)^n` is expanded as
  `X^n(1-Y/X)^n` in `R((X))((Y))`

## TODO
* curry for tensor product inputs
* more API to make ext comparisons easier.
* formal variable API, e.g., like the `T` function for Laurent polynomials.
## References

* [R. Borcherds, *Vertex Algebras, Kac-Moody Algebras, and the Monster*][borcherds1986vertex]
* G. Mason `Vertex rings and Pierce bundles` ArXiv 1707.00328
* A. Matsuo, K. Nagatomo `On axioms for a vertex algebra and locality of quantum fields`
  arXiv:hep-th/9706118
* H. Li's paper on local systems?
-/

noncomputable section

variable {Γ Γ₁ Γ₂ R U V W X Y : Type*}

/-- A heterogeneous `Γ`-vertex operator over a commutator ring `R` is an `R`-linear map from an
`R`-module `V` to `Γ`-Hahn series with coefficients in an `R`-module `W`. -/
abbrev HVertexOperator (Γ : Type*) [PartialOrder Γ] (R : Type*) [CommRing R]
    (V : Type*) (W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] :=
  V →ₗ[R] (HahnModule Γ R W)

namespace HVertexOperator

section Coeff

open HahnModule

variable [PartialOrder Γ] [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

@[ext]
theorem ext (A B : HVertexOperator Γ R V W) (h : ∀ v : V, A v = B v) :
    A = B := LinearMap.ext h

/-- The coefficient of a heterogeneous vertex operator, viewed as a formal power series with
coefficients in linear maps. -/
@[simps]
def coeff (A : HVertexOperator Γ R V W) (n : Γ) : V →ₗ[R] W where
  toFun v := ((of R).symm (A v)).coeff n
  map_add' _ _ := by simp
  map_smul' _ _ := by
    simp only [map_smul, RingHom.id_apply, of_symm_smul, HahnSeries.coeff_smul]

theorem coeff_isPWOsupport (A : HVertexOperator Γ R V W) (v : V) :
    ((of R).symm (A v)).coeff.support.IsPWO :=
  ((of R).symm (A v)).isPWO_support'

@[ext]
theorem coeff_inj : Function.Injective (coeff : HVertexOperator Γ R V W → Γ → (V →ₗ[R] W)) := by
  intro _ _ h
  ext v n
  exact congrFun (congrArg DFunLike.coe (congrFun h n)) v

/-- Given a coefficient function valued in linear maps satisfying a partially well-ordered support
condition, we produce a heterogeneous vertex operator. -/
@[simps]
def of_coeff (f : Γ → V →ₗ[R] W)
    (hf : ∀ x : V , (Function.support (f · x)).IsPWO) : HVertexOperator Γ R V W where
  toFun x := (of R) { coeff := fun g => f g x, isPWO_support' := hf x }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[deprecated (since := "2024-06-18")] alias _root_.VertexAlg.HetVertexOperator.of_coeff := of_coeff

@[simp]
theorem coeff_of_coeff (f : Γ → V →ₗ[R] W)
    (hf : ∀(x : V), (Function.support (fun g => f g x)).IsPWO) : (of_coeff f hf).coeff = f :=
  rfl

@[simp]
theorem zero_coeff : (0 : HVertexOperator Γ R V W).coeff = 0 :=
  rfl

@[simp]
theorem coeff_add (A B : HVertexOperator Γ R V W) : (A + B).coeff = A.coeff + B.coeff := by
  ext
  simp

@[deprecated (since := "2025-01-31")] alias add_coeff := coeff_add

@[simp]
theorem coeff_smul (A : HVertexOperator Γ R V W) (r : R) : (r • A).coeff = r • (A.coeff) := by
  ext
  simp

@[simp]
theorem nsmul_coeff (A : HVertexOperator Γ R V W) {n : ℕ} : (n • A).coeff = n • (A.coeff) := by
  induction n with
  | zero => ext; simp
  | succ n ih => ext; simp [ih]

end Coeff

section Module

variable [OrderedCancelAddCommMonoid Γ] [PartialOrder Γ₁] [AddAction Γ Γ₁]
  [IsOrderedCancelVAdd Γ Γ₁] {R : Type*} [CommRing R] {V W : Type*} [AddCommGroup V]
  [Module R V] [AddCommGroup W] [Module R W]

/-- The scalar multiplication of Hahn series on heterogeneous vertex operators. -/
def HahnSMul (x : HahnSeries Γ R) (A : HVertexOperator Γ₁ R V W) :
    HVertexOperator Γ₁ R V W where
  toFun v := x • (A v)
  map_add' u v := by simp only [map_add, smul_add]
  map_smul' r v := by
    simp only [map_smul, RingHom.id_apply]
    exact (HahnModule.smul_comm r x (A v)).symm

instance instHahnModule : Module (HahnSeries Γ R) (HVertexOperator Γ₁ R V W) where
  smul x A := HahnSMul x A
  one_smul _ := by
    ext _ _
    simp only [one_smul]
  mul_smul _ _ _ := by
    ext _ _
    simp only [LinearMap.smul_apply, mul_smul]
  smul_zero _ := by
    ext _ _
    simp only [smul_zero, LinearMap.zero_apply, HahnModule.of_symm_zero, HahnSeries.zero_coeff]
  smul_add _ _ _ := by
    ext _ _
    simp only [smul_add, LinearMap.add_apply, LinearMap.smul_apply, HahnModule.of_symm_add,
      HahnSeries.add_coeff', Pi.add_apply]
  add_smul _ _ _ := by
    ext _ _
    simp only [coeff_apply, LinearMap.smul_apply, LinearMap.add_apply, HahnSeries.add_coeff']
    rw [HahnModule.add_smul Module.add_smul]
  zero_smul _ := by
    ext _ _
    simp only [zero_smul, LinearMap.zero_apply, HahnModule.of_symm_zero, HahnSeries.zero_coeff]

@[simp]
theorem smul_eq {x : HahnSeries Γ R} {A : HVertexOperator Γ₁ R V W} {v : V} :
    (x • A) v = x • (A v) :=
  rfl

end  Module

section CoeffOps

variable [CommRing R] {V W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- The commutor on functions on a product. -/
@[simps!]
def commutor_equiv : ((Γ₁ × Γ) → V →ₗ[R] W) ≃ₗ[R] ((Γ × Γ₁) → V →ₗ[R] W) where
  toFun A g := A (g.2, g.1)
  map_add' A B := by ext; simp only [Pi.add_apply, LinearMap.add_apply]
  map_smul' r A := by ext; simp only [Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply]
  invFun A g := A (g.2, g.1)
  left_inv A := by simp only [Prod.mk.eta]
  right_inv A := by simp only [Prod.mk.eta]

/-- The commutator of two formal series of endomorphisms. -/
def commutator (A : Γ → V →ₗ[R] V) (B : Γ₁ → V →ₗ[R] V) : (Γ × Γ₁) → V →ₗ[R] V :=
  fun g ↦ (A g.1) * (B g.2) - (B g.2) * (A g.1)

theorem Jacobi (A : Γ → V →ₗ[R] V) (B : Γ₁ → V →ₗ[R] V) (C : Γ₂ → V →ₗ[R] V) (g : Γ) (g₁ : Γ₁)
    (g₂ : Γ₂) :
    (commutator (commutator A B) C ((g, g₁), g₂)) +
    (commutator (commutator B C) A ((g₁, g₂), g)) +
    (commutator (commutator C A) B ((g₂, g), g₁)) = 0 := by
  simp [commutator, sub_mul, mul_sub, mul_assoc]
  abel

/-- The associator on functions on a triple product. -/
@[simps!]
def assoc_equiv : ((Γ × Γ₁) × Γ₂ → V →ₗ[R] W) ≃ₗ[R] (Γ × (Γ₁ × Γ₂) → V →ₗ[R] W) where
  toFun A g := A ((g.1, g.2.1), g.2.2)
  map_add' A B := by ext; simp
  map_smul' r A := by ext; simp
  invFun A g := A (g.1.1, (g.1.2, g.2))
  left_inv A := by simp
  right_inv A := by simp

-- scalar action by finsupps.

end CoeffOps

section Products

variable [OrderedCancelAddCommMonoid Γ] [OrderedCancelAddCommMonoid Γ₁]
  [CommRing R] [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

open HahnModule

/-- The composite of two heterogeneous vertex operators acting on a vector, as an iterated Hahn
  series.-/
@[simps]
def compHahnSeries (A : HVertexOperator Γ R V W) (B : HVertexOperator Γ₁ R U V) (u : U) :
    HahnSeries Γ₁ (HahnSeries Γ W) where
  coeff g' := A (coeff B g' u)
  isPWO_support' := by
    refine Set.IsPWO.mono (((of R).symm (B u)).isPWO_support') ?_
    simp_all only [coeff_apply, Function.support_subset_iff, ne_eq, Function.mem_support]
    exact fun g' hg' hAB => hg' (by simp [hAB])

@[simp]
theorem compHahnSeries.add (A : HVertexOperator Γ R V W) (B : HVertexOperator Γ₁ R U V) (u v : U) :
    compHahnSeries A B (u + v) = compHahnSeries A B u + compHahnSeries A B v := by
  ext
  simp only [compHahnSeries_coeff, map_add, coeff_apply, HahnSeries.add_coeff', Pi.add_apply]
  rw [← @HahnSeries.add_coeff]

@[simp]
theorem compHahnSeries.smul (A : HVertexOperator Γ R V W) (B : HVertexOperator Γ₁ R U V) (r : R)
    (u : U) : compHahnSeries A B (r • u) = r • compHahnSeries A B u := by
  ext
  rw [HahnSeries.smul_coeff]
  simp only [compHahnSeries_coeff, LinearMapClass.map_smul, coeff_apply]

/-- The composite of two heterogeneous vertex operators, as a heterogeneous vertex operator. -/
@[simps]
def comp (A : HVertexOperator Γ R V W) (B : HVertexOperator Γ₁ R U V) :
    HVertexOperator (Γ₁ ×ₗ Γ) R U W where
  toFun u := HahnModule.of R (HahnSeries.ofIterate (compHahnSeries A B u))
  map_add' u v := by
    ext g
    simp only [HahnSeries.ofIterate, compHahnSeries.add, Equiv.symm_apply_apply,
      HahnModule.of_symm_add, HahnSeries.add_coeff', Pi.add_apply]
  map_smul' r x := by
    ext g
    simp only [HahnSeries.ofIterate, compHahnSeries.smul, Equiv.symm_apply_apply, RingHom.id_apply,
      HahnSeries.smul_coeff, compHahnSeries_coeff, coeff_apply]
    exact rfl

@[simp]
theorem comp_coeff (A : HVertexOperator Γ R V W) (B : HVertexOperator Γ₁ R U V) (g : Γ₁ ×ₗ Γ) :
    (comp A B).coeff g = A.coeff (ofLex g).2 ∘ₗ B.coeff (ofLex g).1 := by
  rfl

-- TODO: comp_assoc

/-- The restriction of a heterogeneous vertex operator on a lex product to an element of the left
factor. -/
def ResLeft (A : HVertexOperator (Γ₁ ×ₗ Γ) R V W) (g' : Γ₁):  HVertexOperator Γ R V W :=
  HVertexOperator.of_coeff (fun g => coeff A (toLex (g', g)))
    (fun v => Set.PartiallyWellOrderedOn.fiberProdLex (A v).isPWO_support' _)

theorem coeff_ResLeft (A : HVertexOperator (Γ₁ ×ₗ Γ) R V W) (g' : Γ₁) (g : Γ) :
    coeff (ResLeft A g') g = coeff A (toLex (g', g)) :=
  rfl

/-- The left residue as a linear map. -/
@[simps]
def ResLeft.linearMap (g' : Γ₁):
    HVertexOperator (Γ₁ ×ₗ Γ) R V W →ₗ[R] HVertexOperator Γ R V W where
  toFun A := ResLeft A g'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coeff_left_lex_supp.isPWO (A : HVertexOperator (Γ ×ₗ Γ₁) R V W) (g' : Γ₁) (v : V) :
    (Function.support (fun (g : Γ) => (coeff A (toLex (g, g'))) v)).IsPWO := by
  refine Set.IsPWO.mono (Set.PartiallyWellOrderedOn.imageProdLex (A v).isPWO_support') ?_
  simp_all only [coeff_apply, Function.support_subset_iff, ne_eq, Set.mem_image,
    Function.mem_support]
  exact fun x a ↦ Exists.intro (toLex (x, g')) { left := a, right := rfl }

/-- The restriction of a heterogeneous vertex operator on a lex product to an element of the right
factor. -/
def ResRight (A : HVertexOperator (Γ ×ₗ Γ₁) R V W) (g' : Γ₁) : HVertexOperator Γ R V W :=
  HVertexOperator.of_coeff (fun g => coeff A (toLex (g, g')))
    (fun v => coeff_left_lex_supp.isPWO A g' v)

theorem coeff_ResRight (A : HVertexOperator (Γ ×ₗ Γ₁) R V W) (g' : Γ₁) (g : Γ) :
    coeff (ResRight A g') g = coeff A (toLex (g, g')) := rfl

/-- The right residue as a linear map. -/
@[simps]
def ResRight.linearMap (g' : Γ₁) :
    HVertexOperator (Γ ×ₗ Γ₁) R V W →ₗ[R] HVertexOperator Γ R V W where
  toFun A := ResRight A g'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Products

section PiLex -- Order.PiLex

/-! We consider permutations on Lex Pi types. We need this for the following situation:
To describe locality of vertex operators, we want to say that
`(X - Y) ^ N • A(X) B(Y) = (X - Y) ^ N • B(Y) A(X)`. However, the left side naturally lies in
`V →ₗ[R] V((X))((Y))` while the right side lies in `V →ₗ[R] V((Y))((X))`. We can compare them by
forgetting the Hahn series structure, and showing that the coefficient functions are equal after
switching variables. One way to phrase this is that applying `(HahnModule.of R).symm` then
`HahnSeries.coeff`, we get functions to `ℤ ×ₗ ℤ`. Composing with `ofLex` yields functions `ℤ × ℤ`.

One way to look at locality is that for any `u ∈ V`, we have `Y ^ k • A(X)B(Y)u ∈ V((X))[[Y]]` for
suitably large `k`, and `X ^ m • B(Y)A(X)u ∈ V((Y))[[X]]` for suitably large `m`.  We conclude that
locality means there are `k,m,N` such that both `X ^ m * Y ^ k * (X - Y) ^ N • A(X) B(Y) u` and
`X ^ m * Y ^ k * (X - Y) ^ N • B(Y) A(X) u` lie in `V[[X,Y]]`, and are equal there.

One problem is that I want to say that `(X - Y) ^ N` expanded in `R((X))((Y))` is the same as
`(X - Y) ^ N` expanded in `R((Y))((X))`. Thus, I would like some API for transferring polynomials
along variable permutations. Switching variables on `(X - Y) ^ N` is the same as multiplying by
`(-1) ^ N`, but when we have more variables, a permutation yields more than just a sign change.

Perhaps it is best to have lemmas identifying UnitBinomial with HahnSeries finsupps, so that
permutations still yield Hahn series.  I think we only need 3 variables most of the time, so
permutations on `(X - Y) ^ k * (X - Z) ^ m * (Y - Z) ^ n` may be enough. For Dong's Lemma, I need
to use the fact that `(X - Z) = (X - Y) + (Y - Z)`.

So, maybe I should make a notation `X i` for the variable, and the field `A (X i)` a type synonym
for `A`, so Hahn series on `ℤ ×ₗ ⋯ ×ₗ ℤ` are given by `V((X 1)) ⋯ ((X n))`.

See Algebra.MvPolynomial.Basic:

def MvPolynomial (σ : Type*) (R : Type*) [CommSemiring R] :=
  AddMonoidAlgebra R (σ →₀ ℕ)

def X (n : σ) : MvPolynomial σ R :=
  monomial (Finsupp.single n 1) 1

def rename (f : σ → τ) : MvPolynomial σ R →ₐ[R] MvPolynomial τ R :=
  aeval (X ∘ f)

@[simps apply]
def renameEquiv (f : σ ≃ τ) : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R :=
  { rename f with
    toFun := rename f
    invFun := rename f.symm
    left_inv := fun p => by rw [rename_rename, f.symm_comp_self, rename_id]
    right_inv := fun p => by rw [rename_rename, f.self_comp_symm, rename_id] }

Wrong: Define a vertex operator as `HVertexOperator (σ → ℤ) R V V` for a singleton type `σ`?

Composition gives ProdLex types, so composite types in general should be PiLex, using an ordered
version of `consPiProdEquiv`. Comparison should take place using `rename` along permutations.
Associativity is delicate: we have `Γ₁ ×ₗ (Γ₂ ×ₗ Γ₃)` and `(Γ₁ ×ₗ Γ₂) ×ₗ Γ₃`, so we need something
like a `LexAssoc` operation.  We say two `VertexOperators` `Commute` if transposition yields an
identity on coefficients, and they are `IsLocal` if they `Commute` after multiplying by transposed
binomials. We say two `VertexOperators` `IsAssociate` if their coefficients match (need a variable
change from `X` to `X + Y` here?), and `IsWeakAssociate` if they associate after multiplying by
suitable binomials.  In general, associativity of intertwining operators needs some analytic input,
like from differential equations?



theorem `Pi.lex_desc` {α} [Preorder ι] [DecidableEq ι] [Preorder α] {f : ι → α} {i j : ι}
    (h₁ : i ≤ j) (h₂ : f j < f i) : toLex (f ∘ Equiv.swap i j) < toLex f := sorry

Define binomials `X i - X j` as `varMinus i j` for `i j : σ`.  Or maybe `varMinus hij` for
`hij : i < j`. This might make it hard to compare `varMinus i j` with `varMinus j i` for
a permuted order. Binomials are also Finsupps, so we can make a function to MvPolynomial, and
compare them that way. Since this is special to vertex operators, perhaps this should go in the
vertex operator file.

-/

variable {ι : Type*} {β : ι → Type*} (r : ι → ι → Prop) (s : ∀ {i}, β i → β i → Prop)

/-- The lexicographic relation on `Π i : ι, β i`, where `ι` is ordered by `r`,
  and each `β i` is ordered by `s`. -/
def Lexx (x y : ∀ i, β i) : Prop :=
  ∃ i, (∀ j, r j i → x j = y j) ∧ s (x i) (y i)

theorem xxx (x y : ∀ i, β i) : Lexx r s x y ↔ Pi.Lex r s x y := Iff.rfl



theorem lex_basis_lt : (toLex (0,1) : ℤ ×ₗ ℤ) < (toLex (1,0) : ℤ ×ₗ ℤ) := by decide
--#find_home! lex_basis_lt --[Mathlib.Data.Prod.Lex]

end PiLex

section Binomial -- delete this. Important adaptations go to VertexOperator.lean

theorem toLex_vAdd_of_sub (k l m n : ℤ) :
    toLex ((m : ℤ) , (n : ℤ)) +ᵥ toLex (k - m, l - n) = toLex (k, l) := by
  rw [vadd_eq_add, ← toLex_add, Prod.mk_add_mk, Int.add_comm, Int.sub_add_cancel, Int.add_comm,
    Int.sub_add_cancel]
--#find_home! toLex_vAdd_of_sub --[Mathlib.RingTheory.HahnSeries.Multiplication]

variable [OrderedCancelAddCommMonoid Γ] {R : Type*} {V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- `-Y + X` as a unit of `R((X))((Y))` -/
def subLeft (R : Type*) [CommRing R] : (HahnSeries (ℤ ×ₗ ℤ) R)ˣ :=
  HahnSeries.UnitBinomial (AddGroup.isAddUnit (toLex (0,1))) lex_basis_lt (isUnit_neg_one (α := R))
    (1 : R)

theorem subLeft_eq : (subLeft R).val = HahnSeries.single (toLex (1,0)) 1 +
    HahnSeries.single (toLex (0,1)) (-1 : R) := by
  rw [subLeft, HahnSeries.unitBinomial_eq_single_add_single, add_comm]

@[simp]
theorem subLeft_smul_eq {A : HVertexOperator (ℤ ×ₗ ℤ) R V W} :
    subLeft R • A = (subLeft R).val • A :=
  rfl

@[simp]
theorem subLeft_leadingCoeff [Nontrivial R] : (subLeft R).val.leadingCoeff = (-1 : R) := by
  rw [subLeft_eq, add_comm, HahnSeries.leadingCoeff_single_add_single lex_basis_lt (by simp)]

theorem subLeft_order [Nontrivial R] : (subLeft R).val.order = toLex (0,1) := by
  rw [subLeft_eq, add_comm, HahnSeries.order_single_add_single lex_basis_lt (by simp)]

@[simp]
theorem subLeft_smul_coeff (A : HVertexOperator (ℤ ×ₗ ℤ) R V W) (k l : ℤ) :
    ((subLeft R).val • A).coeff (toLex (k, l)) =
      A.coeff (toLex (k - 1, l)) - A.coeff (toLex (k, l - 1)) := by
  rw [subLeft_eq, add_smul, add_coeff, Pi.add_apply]
  ext v
  simp only [LinearMap.add_apply, coeff_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq]
  nth_rw 1 [← toLex_vAdd_of_sub k l 1 0]
  rw [sub_zero, HahnModule.single_smul_coeff_add, one_smul, ← toLex_vAdd_of_sub k l 0 1,
    sub_zero, HahnModule.single_smul_coeff_add, neg_one_smul, ← sub_eq_add_neg]

/-!
--describe coefficients of powers
theorem subLeft_pow_smul_coeff (A : HVertexOperator (ℤ ×ₗ ℤ) R V W) (k l n : ℤ) :
    ((subLeft R) ^ n • A).coeff (toLex (k, l)) = ∑??
-/

/-- `X - Y` as a unit of `R((Y))((X))`.  This is `-1` times subLeft, so it may be superfluous. -/
def subRight (R : Type*) [CommRing R] : (HahnSeries (ℤ ×ₗ ℤ) R)ˣ :=
    HahnSeries.UnitBinomial (AddGroup.isAddUnit (toLex (0,1))) lex_basis_lt (isUnit_one (M := R))
    (-1 : R)

theorem subRight_eq : (subRight R).val = HahnSeries.single (toLex (1,0)) (-1 : R) +
    HahnSeries.single (toLex (0,1)) (1 : R) := by
  rw [subRight, HahnSeries.unitBinomial_eq_single_add_single, add_comm]

theorem subRight_leadingCoeff [Nontrivial R] : (subRight R).val.leadingCoeff = (1 : R) := by
  rw [subRight_eq, add_comm, HahnSeries.leadingCoeff_single_add_single lex_basis_lt one_ne_zero]

theorem subRight_order [Nontrivial R] : (subRight R).val.order = toLex (0,1) := by
  rw [subRight_eq, add_comm, HahnSeries.order_single_add_single lex_basis_lt one_ne_zero]

theorem subRight_smul_eq (A : HVertexOperator (ℤ ×ₗ ℤ) R V W) :
    (subRight R) • A = (subRight R).val • A :=
  rfl

theorem subRight_smul_coeff (A : HVertexOperator (ℤ ×ₗ ℤ) R V W) (k l : ℤ) :
    ((subRight R) • A).coeff (toLex (k, l)) =
      A.coeff (toLex (k, l - 1)) - A.coeff (toLex (k - 1, l)) := by
  rw [subRight_smul_eq, subRight_eq, add_smul, add_coeff, Pi.add_apply]
  ext v
  simp only [LinearMap.add_apply, coeff_apply, LinearMap.sub_apply, smul_eq]
  nth_rw 1 [← toLex_vAdd_of_sub k l 1 0]
  rw [sub_zero, HahnModule.single_smul_coeff_add, neg_one_smul, ← toLex_vAdd_of_sub k l 0 1,
    sub_zero, HahnModule.single_smul_coeff_add, one_smul, neg_add_eq_sub]

--describe coefficients of powers

theorem subLeft_smul_eq_subRight_smul (A B : HVertexOperator (ℤ ×ₗ ℤ) R V W)
    (h : ∀ (k l : ℤ), A.coeff (toLex (k, l)) = B.coeff (toLex (l, k))) (k l : ℤ) :
    ((subLeft R) • A).coeff (toLex (k, l)) = ((subRight R) • B).coeff (toLex (l, k)) := by
  rw [subLeft_smul_eq, subLeft_smul_coeff, subRight_smul_coeff, h k (l-1), h (k-1) l]

end Binomial

/-! A heterogeneous state-field map is a linear map from a vector space `U` to the space of
heterogeneous fields (or vertex operators) from `V` to `W`.  Equivalently, it is a bilinear map
`U →ₗ[R] V →ₗ[R] HahnModule Γ R W`.  When `Γ = ℤ` and `U = V = W`, then the multiplication map in a
vertex algebra has this form, but in other cases, we use this for module structures and intertwining
operators. -/

-- Can I just use `curry` to say this is a HVertexOperator Γ R (U ⊗[R] V) W?  So, the multiplication
-- in a vertex algebra is just HVertexOperator ℤ R (V ⊗[R] V) V?
-- Then composition is easier.

open TensorProduct

variable [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
/-- The standard equivalence between heterogeneous state field maps and heterogeneous vertex
operators on the tensor product. May be unnecessary. -/
def uncurry [PartialOrder Γ] [AddCommGroup U] [Module R U] :
    (U →ₗ[R] HVertexOperator Γ R V W) ≃ₗ[R] HVertexOperator Γ R (U ⊗[R] V) W :=
  lift.equiv R U V (HahnModule Γ R W)

@[simp]
theorem uncurry_apply [PartialOrder Γ] [AddCommGroup U] [Module R U]
    (A : U →ₗ[R] HVertexOperator Γ R V W) (u : U) (v : V) : uncurry A (u ⊗ₜ v) = A u v :=
  rfl

@[simp]
theorem uncurry_symm_apply [PartialOrder Γ] [AddCommGroup U] [Module R U]
    (A : HVertexOperator Γ R (U ⊗[R] V) W) (u : U) (v : V) : uncurry.symm A u v = A (u ⊗ₜ v) :=
  rfl

section Composition

/-! Given heterogeneous vertex operators `Y_{UV}^W : U ⊗ V → W((z))` and
`Y_{WX}^Y : W ⊗ X → Y((w))`, we wish to compose them to get a heterogeneous vertex operator
`U ⊗ V ⊗ X → Y((w))((z))`.

-/

variable [PartialOrder Γ] [PartialOrder Γ₁] [AddCommGroup U] [Module R U] [AddCommGroup X]
[Module R X]  [AddCommGroup Y] [Module R Y]

/-- Left iterated vertex operator. -/
def leftTensorComp (A : HVertexOperator Γ R (U ⊗[R] V) X)
    (B : HVertexOperator Γ₁ R (X ⊗[R] W) Y) :
    ((U ⊗[R] V) ⊗[R] W) →ₗ[R] HahnModule Γ R (HahnModule Γ₁ R Y) :=
  (HahnModule.map B) ∘ₗ HahnModule.rightTensorMap ∘ₗ (TensorProduct.map A LinearMap.id)

/-!
`simps!` yields
((A.leftTensorComp B) a).coeff g =
  B (((HahnModule.of R).symm (HahnModule.rightTensorMap
    ((TensorProduct.map A LinearMap.id) a))).coeff g)

 Iterate starting with `Y_{UV}^W : U ⊗ V → W((z))` and `Y_{WX}^Y : W ⊗ X → Y((w))`, make
`leftTensorComp`: `Y_{UVX}^Y (t_1, t_2) : U ⊗ V ⊗ X → W((z)) ⊗ X → (W ⊗ X)((z)) → Y((w))((z))`.
First: `Y_{UV}^W ⊗ id X : U ⊗ V ⊗ X → W((z)) ⊗ X`
Second: `W((z)) ⊗ X → (W ⊗ X)((z))` is `HahnModule.rightTensorMap`.
Third: `(W ⊗ X)((z)) → Y((w))((z))` is `HahnModule.map` applied to `Y_{WX}^Y`.

`rightTensorComp`: `Y_{XW}^Y (x, t_0) Y_{UV}^W (u, t_1) v`

Define things like order of a pair, creativity?

-/

end Composition

end HVertexOperator
