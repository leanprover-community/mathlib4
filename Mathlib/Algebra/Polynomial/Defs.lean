/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Data.Finset.Sort

/-!
# Theory of univariate polynomials: ring structure

This file defines `Polynomial R`, the type of univariate polynomials over the semiring `R` and
builds a semiring structure on it.

## Main definitions

* `Polynomial.semiring`, `Polynomial.ring`: (semi)ring structure on `R[X]`
* `Polynomial.coeff p n`: the coefficient of `X^n` in `p`
* `Polynomial.support p`: the finite set of nonzero coefficients of `p`
* Notation to refer to `Polynomial R`, as `R[X]` or `R[t]`.

## Main results

* `Polynomial.ext`: two polynomials are equal when all their coefficients coincide

## Implementation

Polynomials are defined using `R[ℕ]`, where `R` is a semiring.
The variable `X` commutes with every polynomial `p`: lemma `X_mul` proves the identity
`X * p = p * X`.  The relationship to `R[ℕ]` is through a structure
to make polynomials irreducible from the point of view of the kernel. Most operations
are irreducible since Lean can not compute anyway with `AddMonoidAlgebra`. There are two
exceptions that we make semireducible:
* The zero polynomial, so that its coefficients are definitionally equal to `0`.
* The scalar action, to permit typeclass search to unfold it to resolve potential instance
  diamonds (see `Mathlib/Algebra/Polynomial/Module.lean`).

The raw implementation of the equivalence between `R[X]` and `R[ℕ]` is
done through `ofFinsupp` and `toFinsupp` (or, equivalently, `rcases p` when `p` is a polynomial
gives an element `q` of `R[ℕ]`, and conversely `⟨q⟩` gives back `p`). The
equivalence is also registered as a ring equiv in `Polynomial.toFinsuppIso`. These should
in general not be used once the basic API for polynomials is constructed.
-/

assert_not_exists Module

noncomputable section

/-- `Polynomial R` is the type of univariate polynomials over `R`.

Polynomials should be seen as (semi-)rings with the additional constructor `X`.
The embedding from `R` is called `C`. -/
structure Polynomial (R : Type*) [Semiring R] where ofFinsupp ::
  toFinsupp : AddMonoidAlgebra R ℕ

@[inherit_doc] scoped[Polynomial] notation:9000 R "[X]" => Polynomial R

open AddMonoidAlgebra Finset
open Finsupp hiding single
open Function hiding Commute

namespace Polynomial

universe u

variable {R : Type u} {a b : R} {m n : ℕ}

section Semiring

variable [Semiring R] {p q : R[X]}

theorem forall_iff_forall_finsupp (P : R[X] → Prop) :
    (∀ p, P p) ↔ ∀ q : R[ℕ], P ⟨q⟩ :=
  ⟨fun h q => h ⟨q⟩, fun h ⟨p⟩ => h p⟩

theorem exists_iff_exists_finsupp (P : R[X] → Prop) :
    (∃ p, P p) ↔ ∃ q : R[ℕ], P ⟨q⟩ :=
  ⟨fun ⟨⟨p⟩, hp⟩ => ⟨p, hp⟩, fun ⟨q, hq⟩ => ⟨⟨q⟩, hq⟩⟩

@[simp]
theorem eta (f : R[X]) : Polynomial.ofFinsupp f.toFinsupp = f := by cases f; rfl

/-! ### Conversions to and from `AddMonoidAlgebra`

Since `R[X]` is not defeq to `R[ℕ]`, but instead is a structure wrapping
it, we have to copy across all the arithmetic operators manually, along with the lemmas about how
they unfold around `Polynomial.ofFinsupp` and `Polynomial.toFinsupp`.
-/


section AddMonoidAlgebra

private irreducible_def add : R[X] → R[X] → R[X]
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

private irreducible_def neg {R : Type u} [Ring R] : R[X] → R[X]
  | ⟨a⟩ => ⟨-a⟩

private irreducible_def mul : R[X] → R[X] → R[X]
  | ⟨a⟩, ⟨b⟩ => ⟨a * b⟩

instance zero : Zero R[X] :=
  ⟨⟨0⟩⟩

instance one : One R[X] :=
  ⟨⟨1⟩⟩

instance add' : Add R[X] :=
  ⟨add⟩

instance neg' {R : Type u} [Ring R] : Neg R[X] :=
  ⟨neg⟩

instance sub {R : Type u} [Ring R] : Sub R[X] :=
  ⟨fun a b => a + -b⟩

instance mul' : Mul R[X] :=
  ⟨mul⟩

-- If the private definitions are accidentally exposed, simplify them away.
@[simp] theorem add_eq_add : add p q = p + q := rfl
@[simp] theorem mul_eq_mul : mul p q = p * q := rfl

instance instNSMul : SMul ℕ R[X] where
  smul r p := ⟨r • p.toFinsupp⟩

-- to avoid a bug in the `ring` tactic
instance (priority := 1) pow : Pow R[X] ℕ where pow p n := npowRec n p

@[simp]
theorem ofFinsupp_zero : (⟨0⟩ : R[X]) = 0 :=
  rfl

@[simp]
theorem ofFinsupp_one : (⟨1⟩ : R[X]) = 1 :=
  rfl

@[simp]
theorem ofFinsupp_add {a b} : (⟨a + b⟩ : R[X]) = ⟨a⟩ + ⟨b⟩ :=
  show _ = add _ _ by rw [add_def]

@[simp]
theorem ofFinsupp_neg {R : Type u} [Ring R] {a} : (⟨-a⟩ : R[X]) = -⟨a⟩ :=
  show _ = neg _ by rw [neg_def]

@[simp]
theorem ofFinsupp_sub {R : Type u} [Ring R] {a b} : (⟨a - b⟩ : R[X]) = ⟨a⟩ - ⟨b⟩ := by
  rw [sub_eq_add_neg, ofFinsupp_add, ofFinsupp_neg]
  rfl

@[simp]
theorem ofFinsupp_mul (a b) : (⟨a * b⟩ : R[X]) = ⟨a⟩ * ⟨b⟩ :=
  show _ = mul _ _ by rw [mul_def]

@[simp]
theorem ofFinsupp_nsmul (a : ℕ) (b) :
    (⟨a • b⟩ : R[X]) = (a • ⟨b⟩ : R[X]) :=
  rfl

@[simp]
theorem ofFinsupp_pow (a) (n : ℕ) : (⟨a ^ n⟩ : R[X]) = ⟨a⟩ ^ n := by
  change _ = npowRec n _
  induction n with
  | zero        => simp [npowRec]
  | succ n n_ih => simp [npowRec, n_ih, pow_succ]

@[simp]
theorem toFinsupp_zero : (0 : R[X]).toFinsupp = 0 :=
  rfl

@[simp]
theorem toFinsupp_one : (1 : R[X]).toFinsupp = 1 :=
  rfl

@[simp]
theorem toFinsupp_add (a b : R[X]) : (a + b).toFinsupp = a.toFinsupp + b.toFinsupp := by
  cases a
  cases b
  rw [← ofFinsupp_add]

@[simp]
theorem toFinsupp_neg {R : Type u} [Ring R] (a : R[X]) : (-a).toFinsupp = -a.toFinsupp := by
  cases a
  rw [← ofFinsupp_neg]

@[simp]
theorem toFinsupp_sub {R : Type u} [Ring R] (a b : R[X]) :
    (a - b).toFinsupp = a.toFinsupp - b.toFinsupp := by
  rw [sub_eq_add_neg, ← toFinsupp_neg, ← toFinsupp_add]
  rfl

@[simp]
theorem toFinsupp_mul (a b : R[X]) : (a * b).toFinsupp = a.toFinsupp * b.toFinsupp := by
  cases a
  cases b
  rw [← ofFinsupp_mul]

@[simp]
theorem toFinsupp_nsmul (a : ℕ) (b : R[X]) :
    (a • b).toFinsupp = a • b.toFinsupp :=
  rfl

@[simp]
theorem toFinsupp_pow (a : R[X]) (n : ℕ) : (a ^ n).toFinsupp = a.toFinsupp ^ n := by
  cases a
  rw [← ofFinsupp_pow]

theorem toFinsupp_injective : Function.Injective (toFinsupp : R[X] → AddMonoidAlgebra _ _) :=
  fun ⟨_x⟩ ⟨_y⟩ => congr_arg _

@[simp]
theorem toFinsupp_inj {a b : R[X]} : a.toFinsupp = b.toFinsupp ↔ a = b :=
  toFinsupp_injective.eq_iff

@[simp]
theorem toFinsupp_eq_zero {a : R[X]} : a.toFinsupp = 0 ↔ a = 0 := by
  rw [← toFinsupp_zero, toFinsupp_inj]

@[simp]
theorem toFinsupp_eq_one {a : R[X]} : a.toFinsupp = 1 ↔ a = 1 := by
  rw [← toFinsupp_one, toFinsupp_inj]

/-- A more convenient spelling of `Polynomial.ofFinsupp.injEq` in terms of `Iff`. -/
theorem ofFinsupp_inj {a b} : (⟨a⟩ : R[X]) = ⟨b⟩ ↔ a = b :=
  iff_of_eq (ofFinsupp.injEq _ _)

@[simp]
theorem ofFinsupp_eq_zero {a} : (⟨a⟩ : R[X]) = 0 ↔ a = 0 := by
  rw [← ofFinsupp_zero, ofFinsupp_inj]

@[simp]
theorem ofFinsupp_eq_one {a} : (⟨a⟩ : R[X]) = 1 ↔ a = 1 := by rw [← ofFinsupp_one, ofFinsupp_inj]

instance inhabited : Inhabited R[X] :=
  ⟨0⟩

instance instNatCast : NatCast R[X] where natCast n := ofFinsupp n

instance semiring : Semiring R[X] :=
  --TODO: add reference to library note in PR https://github.com/leanprover-community/mathlib4/pull/7432
  { Function.Injective.semiring toFinsupp toFinsupp_injective toFinsupp_zero toFinsupp_one
      toFinsupp_add toFinsupp_mul (fun _ _ => toFinsupp_nsmul _ _) toFinsupp_pow fun _ => rfl with
    toAdd := Polynomial.add'
    toMul := Polynomial.mul'
    toZero := Polynomial.zero
    toOne := Polynomial.one
    nsmul := (· • ·)
    npow := fun n x => (x ^ n) }

variable (R)

/-- Ring isomorphism between `R[X]` and `R[ℕ]`. This is just an
implementation detail, but it can be useful to transfer results from `Finsupp` to polynomials. -/
@[simps apply symm_apply]
def toFinsuppIso : R[X] ≃+* R[ℕ] where
  toFun := toFinsupp
  invFun := ofFinsupp
  left_inv := fun ⟨_p⟩ => rfl
  right_inv _p := rfl
  map_mul' := toFinsupp_mul
  map_add' := toFinsupp_add

instance [DecidableEq R] : DecidableEq R[X] :=
  @Equiv.decidableEq R[X] _ (toFinsuppIso R).toEquiv (Finsupp.instDecidableEq)

end AddMonoidAlgebra

theorem ofFinsupp_sum {ι : Type*} (s : Finset ι) (f : ι → R[ℕ]) :
    (⟨∑ i ∈ s, f i⟩ : R[X]) = ∑ i ∈ s, ⟨f i⟩ :=
  map_sum (toFinsuppIso R).symm f s

theorem toFinsupp_sum {ι : Type*} (s : Finset ι) (f : ι → R[X]) :
    (∑ i ∈ s, f i : R[X]).toFinsupp = ∑ i ∈ s, (f i).toFinsupp :=
  map_sum (toFinsuppIso R) f s

/-- The set of all `n` such that `X^n` has a non-zero coefficient.
-/
-- @[simp] -- Porting note: The original generated theorem is same to `support_ofFinsupp` and
           --               the new generated theorem is different, so this attribute should be
           --               removed.
def support : R[X] → Finset ℕ
  | ⟨p⟩ => p.support

@[simp]
theorem support_ofFinsupp (p) : support (⟨p⟩ : R[X]) = p.support := by rw [support]

theorem support_toFinsupp (p : R[X]) : p.toFinsupp.support = p.support := by rw [support]

@[simp]
theorem support_zero : (0 : R[X]).support = ∅ :=
  rfl

@[simp]
theorem support_eq_empty : p.support = ∅ ↔ p = 0 := by
  rcases p with ⟨⟩
  simp [support]

@[simp] lemma support_nonempty : p.support.Nonempty ↔ p ≠ 0 :=
  Finset.nonempty_iff_ne_empty.trans support_eq_empty.not

theorem card_support_eq_zero : #p.support = 0 ↔ p = 0 := by simp

theorem support_add : (p + q).support ⊆ p.support ∪ q.support := by
  simpa [support] using Finsupp.support_add

/-- `coeff p n` (often denoted `p.coeff n`) is the coefficient of `X^n` in `p`. -/
-- @[simp] -- Porting note: The original generated theorem is same to `coeff_ofFinsupp` and
           --               the new generated theorem is different, so this attribute should be
           --               removed.
def coeff : R[X] → ℕ → R
  | ⟨p⟩ => p

@[simp]
theorem coeff_ofFinsupp (p) : coeff (⟨p⟩ : R[X]) = p := by rw [coeff]

theorem coeff_injective : Injective (coeff : R[X] → ℕ → R) := by
  rintro ⟨p⟩ ⟨q⟩
  -- Porting note: `ofFinsupp.injEq` is required.
  simp only [coeff, DFunLike.coe_fn_eq, imp_self, ofFinsupp.injEq]

@[simp]
theorem coeff_inj : p.coeff = q.coeff ↔ p = q :=
  coeff_injective.eq_iff

theorem toFinsupp_apply (f : R[X]) (i) : f.toFinsupp i = f.coeff i := by cases f; rfl

@[simp]
theorem coeff_zero (n : ℕ) : coeff (0 : R[X]) n = 0 :=
  rfl

@[simp]
theorem mem_support_iff : n ∈ p.support ↔ p.coeff n ≠ 0 := by
  rcases p with ⟨⟩
  simp

theorem not_mem_support_iff : n ∉ p.support ↔ p.coeff n = 0 := by simp

theorem ext_iff {p q : R[X]} : p = q ↔ ∀ n, coeff p n = coeff q n := by
  rcases p with ⟨f : ℕ →₀ R⟩
  rcases q with ⟨g : ℕ →₀ R⟩
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10745): was `simp [coeff, DFunLike.ext_iff]`
  simpa [coeff] using DFunLike.ext_iff (f := f) (g := g)

@[ext]
theorem ext {p q : R[X]} : (∀ n, coeff p n = coeff q n) → p = q :=
  ext_iff.2

theorem natCast_mul (n : ℕ) (p : R[X]) : (n : R[X]) * p = n • p :=
  (nsmul_eq_mul _ _).symm

@[deprecated (since := "2024-04-17")]
alias nat_cast_mul := natCast_mul

end Semiring

section CommSemiring

variable [CommSemiring R]

instance commSemiring : CommSemiring R[X] :=
  { Function.Injective.commSemigroup toFinsupp toFinsupp_injective toFinsupp_mul with
    toSemiring := Polynomial.semiring }

end CommSemiring

section Ring

variable [Ring R]

instance instZSMul : SMul ℤ R[X] where
  smul r p := ⟨r • p.toFinsupp⟩

@[simp]
theorem ofFinsupp_zsmul (a : ℤ) (b) :
    (⟨a • b⟩ : R[X]) = (a • ⟨b⟩ : R[X]) :=
  rfl

@[simp]
theorem toFinsupp_zsmul (a : ℤ) (b : R[X]) :
    (a • b).toFinsupp = a • b.toFinsupp :=
  rfl

instance instIntCast : IntCast R[X] where intCast n := ofFinsupp n

instance ring : Ring R[X] :=
  --TODO: add reference to library note in PR https://github.com/leanprover-community/mathlib4/pull/7432
  { Function.Injective.ring toFinsupp toFinsupp_injective (toFinsupp_zero (R := R))
      toFinsupp_one toFinsupp_add
      toFinsupp_mul toFinsupp_neg toFinsupp_sub (fun _ _ => toFinsupp_nsmul _ _)
      (fun _ _ => toFinsupp_zsmul _ _) toFinsupp_pow (fun _ => rfl) fun _ => rfl with
    toSemiring := Polynomial.semiring,
    toNeg := Polynomial.neg'
    toSub := Polynomial.sub
    zsmul := ((· • ·) : ℤ → R[X] → R[X]) }

@[simp]
theorem coeff_neg (p : R[X]) (n : ℕ) : coeff (-p) n = -coeff p n := by
  rcases p with ⟨⟩
  rw [← ofFinsupp_neg, coeff, coeff, Finsupp.neg_apply]

@[simp]
theorem support_neg {p : R[X]} : (-p).support = p.support := by
  rcases p with ⟨⟩
  rw [← ofFinsupp_neg, support, support, Finsupp.support_neg]

@[simp]
theorem coeff_sub (p q : R[X]) (n : ℕ) : coeff (p - q) n = coeff p n - coeff q n := by
  rcases p with ⟨⟩
  rcases q with ⟨⟩
  rw [← ofFinsupp_sub, coeff, coeff, coeff, Finsupp.sub_apply]

end Ring

instance commRing [CommRing R] : CommRing R[X] :=
  --TODO: add reference to library note in PR https://github.com/leanprover-community/mathlib4/pull/7432
  { toRing := Polynomial.ring
    mul_comm := mul_comm }

section NonzeroSemiring

variable [Semiring R]

instance nontrivial [Nontrivial R] : Nontrivial R[X] := by
  have h : Nontrivial R[ℕ] := by infer_instance
  rcases h.exists_pair_ne with ⟨x, y, hxy⟩
  refine ⟨⟨⟨x⟩, ⟨y⟩, ?_⟩⟩
  simp [hxy]

end NonzeroSemiring

section repr

variable [Semiring R]

protected instance repr [Repr R] [DecidableEq R] : Repr R[X] :=
  ⟨fun p prec =>
    let termPrecAndReprs : List (WithTop ℕ × Lean.Format) :=
      List.map (fun
        | 0 => (max_prec, "C " ++ reprArg (coeff p 0))
        | 1 => if coeff p 1 = 1
          then (⊤, "X")
          else (70, "C " ++ reprArg (coeff p 1) ++ " * X")
        | n =>
          if coeff p n = 1
          then (80, "X ^ " ++ Nat.repr n)
          else (70, "C " ++ reprArg (coeff p n) ++ " * X ^ " ++ Nat.repr n))
      (p.support.sort (· ≤ ·))
    match termPrecAndReprs with
    | [] => "0"
    | [(tprec, t)] => if prec ≥ tprec then Lean.Format.paren t else t
    | ts =>
      -- multiple terms, use `+` precedence
      (if prec ≥ 65 then Lean.Format.paren else id)
      (Lean.Format.fill
        (Lean.Format.joinSep (ts.map Prod.snd) (" +" ++ Lean.Format.line)))⟩

end repr

end Polynomial
