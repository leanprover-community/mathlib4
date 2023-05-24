/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module field_theory.ratfunc
! leanprover-community/mathlib commit ec80bb1545ee17237ac0961a91bb2072780643c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.EuclideanDomain
import Mathbin.RingTheory.LaurentSeries
import Mathbin.RingTheory.Localization.FractionRing
import Mathbin.RingTheory.Polynomial.Content

/-!
# The field of rational functions

This file defines the field `ratfunc K` of rational functions over a field `K`,
and shows it is the field of fractions of `K[X]`.

## Main definitions

Working with rational functions as polynomials:
 - `ratfunc.field` provides a field structure
 - `ratfunc.C` is the constant polynomial
 - `ratfunc.X` is the indeterminate
 - `ratfunc.eval` evaluates a rational function given a value for the indeterminate
You can use `is_fraction_ring` API to treat `ratfunc` as the field of fractions of polynomials:
 * `algebra_map K[X] (ratfunc K)` maps polynomials to rational functions
 * `is_fraction_ring.alg_equiv` maps other fields of fractions of `K[X]` to `ratfunc K`,
    in particular:
 * `fraction_ring.alg_equiv K[X] (ratfunc K)` maps the generic field of
    fraction construction to `ratfunc K`. Combine this with `alg_equiv.restrict_scalars` to change
    the `fraction_ring K[X] ≃ₐ[K[X]] ratfunc K` to
    `fraction_ring K[X] ≃ₐ[K] ratfunc K`.

Working with rational functions as fractions:
 - `ratfunc.num` and `ratfunc.denom` give the numerator and denominator.
   These values are chosen to be coprime and such that `ratfunc.denom` is monic.

Embedding of rational functions into Laurent series, provided as a coercion, utilizing
the underlying `ratfunc.coe_alg_hom`.

Lifting homomorphisms of polynomials to other types, by mapping and dividing, as long
as the homomorphism retains the non-zero-divisor property:
  - `ratfunc.lift_monoid_with_zero_hom` lifts a `K[X] →*₀ G₀` to
      a `ratfunc K →*₀ G₀`, where `[comm_ring K] [comm_group_with_zero G₀]`
  - `ratfunc.lift_ring_hom` lifts a `K[X] →+* L` to a `ratfunc K →+* L`,
      where `[comm_ring K] [field L]`
  - `ratfunc.lift_alg_hom` lifts a `K[X] →ₐ[S] L` to a `ratfunc K →ₐ[S] L`,
      where `[comm_ring K] [field L] [comm_semiring S] [algebra S K[X]] [algebra S L]`
This is satisfied by injective homs.
We also have lifting homomorphisms of polynomials to other polynomials,
with the same condition on retaining the non-zero-divisor property across the map:
  - `ratfunc.map` lifts `K[X] →* R[X]` when `[comm_ring K] [comm_ring R]`
  - `ratfunc.map_ring_hom` lifts `K[X] →+* R[X]` when `[comm_ring K] [comm_ring R]`
  - `ratfunc.map_alg_hom` lifts `K[X] →ₐ[S] R[X]` when
    `[comm_ring K] [is_domain K] [comm_ring R] [is_domain R]`

We also have a set of recursion and induction principles:
 - `ratfunc.lift_on`: define a function by mapping a fraction of polynomials `p/q` to `f p q`,
   if `f` is well-defined in the sense that `p/q = p'/q' → f p q = f p' q'`.
 - `ratfunc.lift_on'`: define a function by mapping a fraction of polynomials `p/q` to `f p q`,
   if `f` is well-defined in the sense that `f (a * p) (a * q) = f p' q'`.
 - `ratfunc.induction_on`: if `P` holds on `p / q` for all polynomials `p q`, then `P` holds on all
   rational functions

We define the degree of a rational function, with values in `ℤ`:
 - `int_degree` is the degree of a rational function, defined as the difference between the
   `nat_degree` of its numerator and the `nat_degree` of its denominator. In particular,
   `int_degree 0 = 0`.

## Implementation notes

To provide good API encapsulation and speed up unification problems,
`ratfunc` is defined as a structure, and all operations are `@[irreducible] def`s

We need a couple of maps to set up the `field` and `is_fraction_ring` structure,
namely `ratfunc.of_fraction_ring`, `ratfunc.to_fraction_ring`, `ratfunc.mk` and
`ratfunc.to_fraction_ring_ring_equiv`.
All these maps get `simp`ed to bundled morphisms like `algebra_map K[X] (ratfunc K)`
and `is_localization.alg_equiv`.

There are separate lifts and maps of homomorphisms, to provide routes of lifting even when
the codomain is not a field or even an integral domain.

## References

* [Kleiman, *Misconceptions about $K_X$*][kleiman1979]
* https://freedommathdance.blogspot.com/2012/11/misconceptions-about-kx.html
* https://stacks.math.columbia.edu/tag/01X1

-/


noncomputable section

open Classical

open nonZeroDivisors Polynomial

universe u v

variable (K : Type u) [hring : CommRing K] [hdomain : IsDomain K]

include hring

/-- `ratfunc K` is `K(x)`, the field of rational functions over `K`.

The inclusion of polynomials into `ratfunc` is `algebra_map K[X] (ratfunc K)`,
the maps between `ratfunc K` and another field of fractions of `K[X]`,
especially `fraction_ring K[X]`, are given by `is_localization.algebra_equiv`.
-/
structure Ratfunc : Type u where of_fraction_ring ::
  toFractionRing : FractionRing K[X]
#align ratfunc Ratfunc

namespace Ratfunc

variable {K}

section Rec

/-! ### Constructing `ratfunc`s and their induction principles -/


theorem of_fraction_ring_injective : Function.Injective (of_fraction_ring : _ → Ratfunc K) :=
  fun x y => of_fraction_ring.inj
#align ratfunc.of_fraction_ring_injective Ratfunc.of_fraction_ring_injective

theorem toFractionRing_injective : Function.Injective (toFractionRing : _ → FractionRing K[X])
  | ⟨x⟩, ⟨y⟩, rfl => rfl
#align ratfunc.to_fraction_ring_injective Ratfunc.toFractionRing_injective

/-- Non-dependent recursion principle for `ratfunc K`:
To construct a term of `P : Sort*` out of `x : ratfunc K`,
it suffices to provide a constructor `f : Π (p q : K[X]), P`
and a proof that `f p q = f p' q'` for all `p q p' q'` such that `q' * p = q * p'` where
both `q` and `q'` are not zero divisors, stated as `q ∉ K[X]⁰`, `q' ∉ K[X]⁰`.

If considering `K` as an integral domain, this is the same as saying that
we construct a value of `P` for such elements of `ratfunc K` by setting
`lift_on (p / q) f _ = f p q`.

When `[is_domain K]`, one can use `ratfunc.lift_on'`, which has the stronger requirement
of `∀ {p q a : K[X]} (hq : q ≠ 0) (ha : a ≠ 0), f (a * p) (a * q) = f p q)`.
-/
protected irreducible_def liftOn {P : Sort v} (x : Ratfunc K) (f : ∀ p q : K[X], P)
  (H : ∀ {p q p' q'} (hq : q ∈ K[X]⁰) (hq' : q' ∈ K[X]⁰), q' * p = q * p' → f p q = f p' q') : P :=
  Localization.liftOn (to_fraction_ring x)
    (-- Fix timeout by manipulating elaboration order
    fun p q => f p q)
    fun p p' q q' h =>
    H q.2 q'.2
      (let ⟨⟨c, hc⟩, mul_eq⟩ := Localization.r_iff_exists.mp h
      mul_cancel_left_coe_nonZeroDivisors.mp mul_eq)
#align ratfunc.lift_on Ratfunc.liftOn

theorem liftOn_of_fraction_ring_mk {P : Sort v} (n : K[X]) (d : K[X]⁰) (f : ∀ p q : K[X], P)
    (H : ∀ {p q p' q'} (hq : q ∈ K[X]⁰) (hq' : q' ∈ K[X]⁰), q' * p = q * p' → f p q = f p' q') :
    Ratfunc.liftOn (of_fraction_ring (Localization.mk n d)) f @H = f n d :=
  by
  unfold Ratfunc.liftOn
  exact Localization.liftOn_mk _ _ _ _
#align ratfunc.lift_on_of_fraction_ring_mk Ratfunc.liftOn_of_fraction_ring_mk

include hdomain

/-- `ratfunc.mk (p q : K[X])` is `p / q` as a rational function.

If `q = 0`, then `mk` returns 0.

This is an auxiliary definition used to define an `algebra` structure on `ratfunc`;
the `simp` normal form of `mk p q` is `algebra_map _ _ p / algebra_map _ _ q`.
-/
protected irreducible_def mk (p q : K[X]) : Ratfunc K :=
  of_fraction_ring (algebraMap _ _ p / algebraMap _ _ q)
#align ratfunc.mk Ratfunc.mk

theorem mk_eq_div' (p q : K[X]) :
    Ratfunc.mk p q = of_fraction_ring (algebraMap _ _ p / algebraMap _ _ q) := by unfold Ratfunc.mk
#align ratfunc.mk_eq_div' Ratfunc.mk_eq_div'

theorem mk_zero (p : K[X]) : Ratfunc.mk p 0 = of_fraction_ring 0 := by
  rw [mk_eq_div', RingHom.map_zero, div_zero]
#align ratfunc.mk_zero Ratfunc.mk_zero

theorem mk_coe_def (p : K[X]) (q : K[X]⁰) :
    Ratfunc.mk p q = of_fraction_ring (IsLocalization.mk' _ p q) := by
  simp only [mk_eq_div', ← Localization.mk_eq_mk', FractionRing.mk_eq_div]
#align ratfunc.mk_coe_def Ratfunc.mk_coe_def

theorem mk_def_of_mem (p : K[X]) {q} (hq : q ∈ K[X]⁰) :
    Ratfunc.mk p q = of_fraction_ring (IsLocalization.mk' _ p ⟨q, hq⟩) := by
  simp only [← mk_coe_def, [anonymous]]
#align ratfunc.mk_def_of_mem Ratfunc.mk_def_of_mem

theorem mk_def_of_ne (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    Ratfunc.mk p q =
      of_fraction_ring (IsLocalization.mk' _ p ⟨q, mem_nonZeroDivisors_iff_ne_zero.mpr hq⟩) :=
  mk_def_of_mem p _
#align ratfunc.mk_def_of_ne Ratfunc.mk_def_of_ne

theorem mk_eq_localization_mk (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    Ratfunc.mk p q =
      of_fraction_ring (Localization.mk p ⟨q, mem_nonZeroDivisors_iff_ne_zero.mpr hq⟩) :=
  by rw [mk_def_of_ne, Localization.mk_eq_mk']
#align ratfunc.mk_eq_localization_mk Ratfunc.mk_eq_localization_mk

theorem mk_one' (p : K[X]) : Ratfunc.mk p 1 = of_fraction_ring (algebraMap _ _ p) := by
  rw [← IsLocalization.mk'_one (FractionRing K[X]) p, ← mk_coe_def, Submonoid.coe_one]
#align ratfunc.mk_one' Ratfunc.mk_one'

theorem mk_eq_mk {p q p' q' : K[X]} (hq : q ≠ 0) (hq' : q' ≠ 0) :
    Ratfunc.mk p q = Ratfunc.mk p' q' ↔ p * q' = p' * q := by
  rw [mk_def_of_ne _ hq, mk_def_of_ne _ hq', of_fraction_ring_injective.eq_iff,
    IsLocalization.mk'_eq_iff_eq', [anonymous], [anonymous],
    (IsFractionRing.injective K[X] (FractionRing K[X])).eq_iff]
#align ratfunc.mk_eq_mk Ratfunc.mk_eq_mk

theorem liftOn_mk {P : Sort v} (p q : K[X]) (f : ∀ p q : K[X], P) (f0 : ∀ p, f p 0 = f 0 1)
    (H' : ∀ {p q p' q'} (hq : q ≠ 0) (hq' : q' ≠ 0), q' * p = q * p' → f p q = f p' q')
    (H : ∀ {p q p' q'} (hq : q ∈ K[X]⁰) (hq' : q' ∈ K[X]⁰), q' * p = q * p' → f p q = f p' q' :=
      fun p q p' q' hq hq' h => H' (nonZeroDivisors.ne_zero hq) (nonZeroDivisors.ne_zero hq') h) :
    (Ratfunc.mk p q).liftOn f @H = f p q :=
  by
  by_cases hq : q = 0
  · subst hq
    simp only [mk_zero, f0, ← Localization.mk_zero 1, Localization.liftOn_mk,
      lift_on_of_fraction_ring_mk, Submonoid.coe_one]
  ·
    simp only [mk_eq_localization_mk _ hq, Localization.liftOn_mk, lift_on_of_fraction_ring_mk,
      [anonymous]]
#align ratfunc.lift_on_mk Ratfunc.liftOn_mk

omit hdomain

theorem lift_on_condition_of_lift_on'_condition {P : Sort v} {f : ∀ p q : K[X], P}
    (H : ∀ {p q a} (hq : q ≠ 0) (ha : a ≠ 0), f (a * p) (a * q) = f p q) ⦃p q p' q' : K[X]⦄
    (hq : q ≠ 0) (hq' : q' ≠ 0) (h : q' * p = q * p') : f p q = f p' q' :=
  calc
    f p q = f (q' * p) (q' * q) := (H hq hq').symm
    _ = f (q * p') (q * q') := by rw [h, mul_comm q']
    _ = f p' q' := H hq' hq
    
#align ratfunc.lift_on_condition_of_lift_on'_condition Ratfunc.lift_on_condition_of_lift_on'_condition

include hdomain

/-- Non-dependent recursion principle for `ratfunc K`: if `f p q : P` for all `p q`,
such that `f (a * p) (a * q) = f p q`, then we can find a value of `P`
for all elements of `ratfunc K` by setting `lift_on' (p / q) f _ = f p q`.

The value of `f p 0` for any `p` is never used and in principle this may be anything,
although many usages of `lift_on'` assume `f p 0 = f 0 1`.
-/
protected irreducible_def liftOn' {P : Sort v} (x : Ratfunc K) (f : ∀ p q : K[X], P)
  (H : ∀ {p q a} (hq : q ≠ 0) (ha : a ≠ 0), f (a * p) (a * q) = f p q) : P :=
  x.liftOn f fun p q p' q' hq hq' =>
    lift_on_condition_of_lift_on'_condition (@H) (nonZeroDivisors.ne_zero hq)
      (nonZeroDivisors.ne_zero hq')
#align ratfunc.lift_on' Ratfunc.liftOn'

theorem liftOn'_mk {P : Sort v} (p q : K[X]) (f : ∀ p q : K[X], P) (f0 : ∀ p, f p 0 = f 0 1)
    (H : ∀ {p q a} (hq : q ≠ 0) (ha : a ≠ 0), f (a * p) (a * q) = f p q) :
    (Ratfunc.mk p q).liftOn' f @H = f p q :=
  by
  rw [Ratfunc.liftOn', Ratfunc.liftOn_mk _ _ _ f0]
  exact lift_on_condition_of_lift_on'_condition @H
#align ratfunc.lift_on'_mk Ratfunc.liftOn'_mk

/- ./././Mathport/Syntax/Translate/Command.lean:322:38: unsupported irreducible non-definition -/
/-- Induction principle for `ratfunc K`: if `f p q : P (ratfunc.mk p q)` for all `p q`,
then `P` holds on all elements of `ratfunc K`.

See also `induction_on`, which is a recursion principle defined in terms of `algebra_map`.
-/
protected irreducible_def induction_on' {P : Ratfunc K → Prop} :
  ∀ (x : Ratfunc K) (f : ∀ (p q : K[X]) (hq : q ≠ 0), P (Ratfunc.mk p q)), P x
  | ⟨x⟩, f =>
    Localization.induction_on x fun ⟨p, q⟩ => by
      simpa only [mk_coe_def, Localization.mk_eq_mk'] using
        f p q (mem_non_zero_divisors_iff_ne_zero.mp q.2)
#align ratfunc.induction_on' Ratfunc.induction_on'

end Rec

section Field

/-! ### Defining the field structure -/


/-- The zero rational function. -/
protected irreducible_def zero : Ratfunc K :=
  ⟨0⟩
#align ratfunc.zero Ratfunc.zero

instance : Zero (Ratfunc K) :=
  ⟨Ratfunc.zero⟩

theorem of_fraction_ring_zero : (of_fraction_ring 0 : Ratfunc K) = 0 := by
  unfold Zero.zero Ratfunc.zero
#align ratfunc.of_fraction_ring_zero Ratfunc.of_fraction_ring_zero

/-- Addition of rational functions. -/
protected irreducible_def add : Ratfunc K → Ratfunc K → Ratfunc K
  | ⟨p⟩, ⟨q⟩ => ⟨p + q⟩
#align ratfunc.add Ratfunc.add

instance : Add (Ratfunc K) :=
  ⟨Ratfunc.add⟩

theorem of_fraction_ring_add (p q : FractionRing K[X]) :
    of_fraction_ring (p + q) = of_fraction_ring p + of_fraction_ring q := by
  unfold Add.add Ratfunc.add
#align ratfunc.of_fraction_ring_add Ratfunc.of_fraction_ring_add

/-- Subtraction of rational functions. -/
protected irreducible_def sub : Ratfunc K → Ratfunc K → Ratfunc K
  | ⟨p⟩, ⟨q⟩ => ⟨p - q⟩
#align ratfunc.sub Ratfunc.sub

instance : Sub (Ratfunc K) :=
  ⟨Ratfunc.sub⟩

theorem of_fraction_ring_sub (p q : FractionRing K[X]) :
    of_fraction_ring (p - q) = of_fraction_ring p - of_fraction_ring q := by
  unfold Sub.sub Ratfunc.sub
#align ratfunc.of_fraction_ring_sub Ratfunc.of_fraction_ring_sub

/-- Additive inverse of a rational function. -/
protected irreducible_def neg : Ratfunc K → Ratfunc K
  | ⟨p⟩ => ⟨-p⟩
#align ratfunc.neg Ratfunc.neg

instance : Neg (Ratfunc K) :=
  ⟨Ratfunc.neg⟩

theorem of_fraction_ring_neg (p : FractionRing K[X]) :
    of_fraction_ring (-p) = -of_fraction_ring p := by unfold Neg.neg Ratfunc.neg
#align ratfunc.of_fraction_ring_neg Ratfunc.of_fraction_ring_neg

/-- The multiplicative unit of rational functions. -/
protected irreducible_def one : Ratfunc K :=
  ⟨1⟩
#align ratfunc.one Ratfunc.one

instance : One (Ratfunc K) :=
  ⟨Ratfunc.one⟩

theorem of_fraction_ring_one : (of_fraction_ring 1 : Ratfunc K) = 1 := by unfold One.one Ratfunc.one
#align ratfunc.of_fraction_ring_one Ratfunc.of_fraction_ring_one

/-- Multiplication of rational functions. -/
protected irreducible_def mul : Ratfunc K → Ratfunc K → Ratfunc K
  | ⟨p⟩, ⟨q⟩ => ⟨p * q⟩
#align ratfunc.mul Ratfunc.mul

instance : Mul (Ratfunc K) :=
  ⟨Ratfunc.mul⟩

theorem of_fraction_ring_mul (p q : FractionRing K[X]) :
    of_fraction_ring (p * q) = of_fraction_ring p * of_fraction_ring q := by
  unfold Mul.mul Ratfunc.mul
#align ratfunc.of_fraction_ring_mul Ratfunc.of_fraction_ring_mul

include hdomain

/-- Division of rational functions. -/
protected irreducible_def div : Ratfunc K → Ratfunc K → Ratfunc K
  | ⟨p⟩, ⟨q⟩ => ⟨p / q⟩
#align ratfunc.div Ratfunc.div

instance : Div (Ratfunc K) :=
  ⟨Ratfunc.div⟩

theorem of_fraction_ring_div (p q : FractionRing K[X]) :
    of_fraction_ring (p / q) = of_fraction_ring p / of_fraction_ring q := by
  unfold Div.div Ratfunc.div
#align ratfunc.of_fraction_ring_div Ratfunc.of_fraction_ring_div

/-- Multiplicative inverse of a rational function. -/
protected irreducible_def inv : Ratfunc K → Ratfunc K
  | ⟨p⟩ => ⟨p⁻¹⟩
#align ratfunc.inv Ratfunc.inv

instance : Inv (Ratfunc K) :=
  ⟨Ratfunc.inv⟩

theorem of_fraction_ring_inv (p : FractionRing K[X]) :
    of_fraction_ring p⁻¹ = (of_fraction_ring p)⁻¹ := by unfold Inv.inv Ratfunc.inv
#align ratfunc.of_fraction_ring_inv Ratfunc.of_fraction_ring_inv

-- Auxiliary lemma for the `field` instance
theorem mul_inv_cancel : ∀ {p : Ratfunc K} (hp : p ≠ 0), p * p⁻¹ = 1
  | ⟨p⟩, h => by
    have : p ≠ 0 := fun hp => h <| by rw [hp, of_fraction_ring_zero]
    simpa only [← of_fraction_ring_inv, ← of_fraction_ring_mul, ← of_fraction_ring_one] using
      _root_.mul_inv_cancel this
#align ratfunc.mul_inv_cancel Ratfunc.mul_inv_cancel

section SMul

omit hdomain

variable {R : Type _}

/-- Scalar multiplication of rational functions. -/
protected irreducible_def smul [SMul R (FractionRing K[X])] : R → Ratfunc K → Ratfunc K
  | r, ⟨p⟩ => ⟨r • p⟩
#align ratfunc.smul Ratfunc.smul

-- cannot reproduce
@[nolint fails_quickly]
instance [SMul R (FractionRing K[X])] : SMul R (Ratfunc K) :=
  ⟨Ratfunc.smul⟩

theorem of_fraction_ring_smul [SMul R (FractionRing K[X])] (c : R) (p : FractionRing K[X]) :
    of_fraction_ring (c • p) = c • of_fraction_ring p := by unfold SMul.smul Ratfunc.smul
#align ratfunc.of_fraction_ring_smul Ratfunc.of_fraction_ring_smul

theorem toFractionRing_smul [SMul R (FractionRing K[X])] (c : R) (p : Ratfunc K) :
    toFractionRing (c • p) = c • toFractionRing p :=
  by
  cases p
  rw [← of_fraction_ring_smul]
#align ratfunc.to_fraction_ring_smul Ratfunc.toFractionRing_smul

theorem smul_eq_c_smul (x : Ratfunc K) (r : K) : r • x = Polynomial.C r • x :=
  by
  cases x
  induction x
  ·
    rw [← of_fraction_ring_smul, ← of_fraction_ring_smul, Localization.smul_mk,
      Localization.smul_mk, smul_eq_mul, Polynomial.smul_eq_C_mul]
  · simp only
#align ratfunc.smul_eq_C_smul Ratfunc.smul_eq_c_smul

include hdomain

variable [Monoid R] [DistribMulAction R K[X]]

variable [htower : IsScalarTower R K[X] K[X]]

include htower

theorem mk_smul (c : R) (p q : K[X]) : Ratfunc.mk (c • p) q = c • Ratfunc.mk p q :=
  by
  by_cases hq : q = 0
  · rw [hq, mk_zero, mk_zero, ← of_fraction_ring_smul, smul_zero]
  ·
    rw [mk_eq_localization_mk _ hq, mk_eq_localization_mk _ hq, ← Localization.smul_mk, ←
      of_fraction_ring_smul]
#align ratfunc.mk_smul Ratfunc.mk_smul

instance : IsScalarTower R K[X] (Ratfunc K) :=
  ⟨fun c p q => q.inductionOn' fun q r _ => by rw [← mk_smul, smul_assoc, mk_smul, mk_smul]⟩

end SMul

variable (K)

omit hdomain

instance [Subsingleton K] : Subsingleton (Ratfunc K) :=
  toFractionRing_injective.Subsingleton

instance : Inhabited (Ratfunc K) :=
  ⟨0⟩

instance [Nontrivial K] : Nontrivial (Ratfunc K) :=
  of_fraction_ring_injective.Nontrivial

/-- `ratfunc K` is isomorphic to the field of fractions of `K[X]`, as rings.

This is an auxiliary definition; `simp`-normal form is `is_localization.alg_equiv`.
-/
@[simps apply]
def toFractionRingRingEquiv : Ratfunc K ≃+* FractionRing K[X]
    where
  toFun := toFractionRing
  invFun := of_fraction_ring
  left_inv := fun ⟨_⟩ => rfl
  right_inv _ := rfl
  map_add' := fun ⟨_⟩ ⟨_⟩ => by simp [← of_fraction_ring_add]
  map_mul' := fun ⟨_⟩ ⟨_⟩ => by simp [← of_fraction_ring_mul]
#align ratfunc.to_fraction_ring_ring_equiv Ratfunc.toFractionRingRingEquiv

omit hring

/- ./././Mathport/Syntax/Translate/Expr.lean:330:4: warning: unsupported (TODO): `[tacs] -/
/-- Solve equations for `ratfunc K` by working in `fraction_ring K[X]`. -/
unsafe def frac_tac : tactic Unit :=
  sorry
#align ratfunc.frac_tac ratfunc.frac_tac

/- ./././Mathport/Syntax/Translate/Expr.lean:330:4: warning: unsupported (TODO): `[tacs] -/
/-- Solve equations for `ratfunc K` by applying `ratfunc.induction_on`. -/
unsafe def smul_tac : tactic Unit :=
  sorry
#align ratfunc.smul_tac ratfunc.smul_tac

include hring

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ratfunc.frac_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ratfunc.frac_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ratfunc.frac_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ratfunc.frac_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ratfunc.frac_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ratfunc.frac_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ratfunc.frac_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ratfunc.frac_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ratfunc.frac_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ratfunc.frac_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ratfunc.frac_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ratfunc.frac_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ratfunc.smul_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ratfunc.smul_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ratfunc.smul_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ratfunc.smul_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ratfunc.smul_tac -/
instance : CommRing (Ratfunc K) where
  add := (· + ·)
  add_assoc := by
    run_tac
      frac_tac
  add_comm := by
    run_tac
      frac_tac
  zero := 0
  zero_add := by
    run_tac
      frac_tac
  add_zero := by
    run_tac
      frac_tac
  neg := Neg.neg
  add_left_neg := by
    run_tac
      frac_tac
  sub := Sub.sub
  sub_eq_add_neg := by
    run_tac
      frac_tac
  mul := (· * ·)
  mul_assoc := by
    run_tac
      frac_tac
  mul_comm := by
    run_tac
      frac_tac
  left_distrib := by
    run_tac
      frac_tac
  right_distrib := by
    run_tac
      frac_tac
  one := 1
  one_mul := by
    run_tac
      frac_tac
  mul_one := by
    run_tac
      frac_tac
  nsmul := (· • ·)
  nsmul_zero := by
    run_tac
      smul_tac
  nsmul_succ _ := by
    run_tac
      smul_tac
  zsmul := (· • ·)
  zsmul_zero' := by
    run_tac
      smul_tac
  zsmul_succ' _ := by
    run_tac
      smul_tac
  zsmul_neg' _ := by
    run_tac
      smul_tac
  npow := npowRec

variable {K}

section LiftHom

variable {G₀ L R S F : Type _} [CommGroupWithZero G₀] [Field L] [CommRing R] [CommRing S]

omit hring

/-- Lift a monoid homomorphism that maps polynomials `φ : R[X] →* S[X]`
to a `ratfunc R →* ratfunc S`,
on the condition that `φ` maps non zero divisors to non zero divisors,
by mapping both the numerator and denominator and quotienting them. -/
def map [MonoidHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) : Ratfunc R →* Ratfunc S
    where
  toFun f :=
    Ratfunc.liftOn f
      (fun n d => if h : φ d ∈ S[X]⁰ then of_fraction_ring (Localization.mk (φ n) ⟨φ d, h⟩) else 0)
      fun p q p' q' hq hq' h =>
      by
      rw [dif_pos, dif_pos, of_fraction_ring.inj_eq, Localization.mk_eq_mk_iff]
      rotate_left
      · exact hφ hq'
      · exact hφ hq
      refine' Localization.r_of_eq _
      simpa only [map_mul] using congr_arg φ h
  map_one' :=
    by
    rw [← of_fraction_ring_one, ← Localization.mk_one, lift_on_of_fraction_ring_mk, dif_pos]
    · simpa using of_fraction_ring_one
    · simpa using Submonoid.one_mem _
  map_mul' x y := by
    cases x; cases y; induction' x with p q; induction' y with p' q'
    · have hq : φ q ∈ S[X]⁰ := hφ q.prop
      have hq' : φ q' ∈ S[X]⁰ := hφ q'.prop
      have hqq' : φ ↑(q * q') ∈ S[X]⁰ := by simpa using Submonoid.mul_mem _ hq hq'
      simp_rw [← of_fraction_ring_mul, Localization.mk_mul, lift_on_of_fraction_ring_mk, dif_pos hq,
        dif_pos hq', dif_pos hqq', ← of_fraction_ring_mul, Submonoid.coe_mul, map_mul,
        Localization.mk_mul, Submonoid.mk_mul_mk]
    · rfl
    · rfl
#align ratfunc.map Ratfunc.map

theorem map_apply_of_fraction_ring_mk [MonoidHomClass F R[X] S[X]] (φ : F)
    (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) (n : R[X]) (d : R[X]⁰) :
    map φ hφ (of_fraction_ring (Localization.mk n d)) =
      of_fraction_ring (Localization.mk (φ n) ⟨φ d, hφ d.Prop⟩) :=
  by
  convert lift_on_of_fraction_ring_mk _ _ _ _
  rw [dif_pos]
#align ratfunc.map_apply_of_fraction_ring_mk Ratfunc.map_apply_of_fraction_ring_mk

theorem map_injective [MonoidHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ ≤ S[X]⁰.comap φ)
    (hf : Function.Injective φ) : Function.Injective (map φ hφ) :=
  by
  rintro ⟨x⟩ ⟨y⟩ h; induction x; induction y
  ·
    simpa only [map_apply_of_fraction_ring_mk, of_fraction_ring_injective.eq_iff,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists, mul_cancel_left_coe_nonZeroDivisors,
      exists_const, [anonymous], ← map_mul, hf.eq_iff] using h
  · rfl
  · rfl
#align ratfunc.map_injective Ratfunc.map_injective

/-- Lift a ring homomorphism that maps polynomials `φ : R[X] →+* S[X]`
to a `ratfunc R →+* ratfunc S`,
on the condition that `φ` maps non zero divisors to non zero divisors,
by mapping both the numerator and denominator and quotienting them. -/
def mapRingHom [RingHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) :
    Ratfunc R →+* Ratfunc S :=
  {
    map φ
      hφ with
    map_zero' := by
      simp_rw [MonoidHom.toFun_eq_coe, ← of_fraction_ring_zero, ← Localization.mk_zero (1 : R[X]⁰),
        ← Localization.mk_zero (1 : S[X]⁰), map_apply_of_fraction_ring_mk, map_zero,
        Localization.mk_eq_mk', IsLocalization.mk'_zero]
    map_add' := by
      rintro ⟨x⟩ ⟨y⟩; induction x; induction y
      ·
        simp only [← of_fraction_ring_add, Localization.add_mk, map_add, [anonymous], map_mul,
          MonoidHom.toFun_eq_coe, map_apply_of_fraction_ring_mk, Submonoid.mk_mul_mk,
          Submonoid.coe_mul]
      · rfl
      · rfl }
#align ratfunc.map_ring_hom Ratfunc.mapRingHom

theorem coe_mapRingHom_eq_coe_map [RingHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) :
    (mapRingHom φ hφ : Ratfunc R → Ratfunc S) = map φ hφ :=
  rfl
#align ratfunc.coe_map_ring_hom_eq_coe_map Ratfunc.coe_mapRingHom_eq_coe_map

-- TODO: Generalize to `fun_like` classes,
/-- Lift an monoid with zero homomorphism `R[X] →*₀ G₀` to a `ratfunc R →*₀ G₀`
on the condition that `φ` maps non zero divisors to non zero divisors,
by mapping both the numerator and denominator and quotienting them. -/
def liftMonoidWithZeroHom (φ : R[X] →*₀ G₀) (hφ : R[X]⁰ ≤ G₀⁰.comap φ) : Ratfunc R →*₀ G₀
    where
  toFun f :=
    Ratfunc.liftOn f (fun p q => φ p / φ q) fun p q p' q' hq hq' h =>
      by
      cases subsingleton_or_nontrivial R
      · rw [Subsingleton.elim p q, Subsingleton.elim p' q, Subsingleton.elim q' q]
      rw [div_eq_div_iff, ← map_mul, mul_comm p, h, map_mul, mul_comm] <;>
        exact nonZeroDivisors.ne_zero (hφ ‹_›)
  map_one' :=
    by
    rw [← of_fraction_ring_one, ← Localization.mk_one, lift_on_of_fraction_ring_mk]
    simp only [map_one, Submonoid.coe_one, div_one]
  map_mul' x y := by
    cases x
    cases y
    induction' x with p q
    induction' y with p' q'
    · rw [← of_fraction_ring_mul, Localization.mk_mul]
      simp only [lift_on_of_fraction_ring_mk, div_mul_div_comm, map_mul, Submonoid.coe_mul]
    · rfl
    · rfl
  map_zero' :=
    by
    rw [← of_fraction_ring_zero, ← Localization.mk_zero (1 : R[X]⁰), lift_on_of_fraction_ring_mk]
    simp only [map_zero, zero_div]
#align ratfunc.lift_monoid_with_zero_hom Ratfunc.liftMonoidWithZeroHom

theorem liftMonoidWithZeroHom_apply_of_fraction_ring_mk (φ : R[X] →*₀ G₀) (hφ : R[X]⁰ ≤ G₀⁰.comap φ)
    (n : R[X]) (d : R[X]⁰) :
    liftMonoidWithZeroHom φ hφ (of_fraction_ring (Localization.mk n d)) = φ n / φ d :=
  liftOn_of_fraction_ring_mk _ _ _ _
#align ratfunc.lift_monoid_with_zero_hom_apply_of_fraction_ring_mk Ratfunc.liftMonoidWithZeroHom_apply_of_fraction_ring_mk

theorem liftMonoidWithZeroHom_injective [Nontrivial R] (φ : R[X] →*₀ G₀) (hφ : Function.Injective φ)
    (hφ' : R[X]⁰ ≤ G₀⁰.comap φ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hφ) :
    Function.Injective (liftMonoidWithZeroHom φ hφ') :=
  by
  rintro ⟨x⟩ ⟨y⟩; induction x; induction y
  · simp_rw [lift_monoid_with_zero_hom_apply_of_fraction_ring_mk, Localization.mk_eq_mk_iff]
    intro h
    refine' Localization.r_of_eq _
    have := mul_eq_mul_of_div_eq_div _ _ _ _ h
    rwa [← map_mul, ← map_mul, hφ.eq_iff, mul_comm, mul_comm y_a] at this
    all_goals exact map_ne_zero_of_mem_nonZeroDivisors _ hφ (SetLike.coe_mem _)
  · exact fun _ => rfl
  · exact fun _ => rfl
#align ratfunc.lift_monoid_with_zero_hom_injective Ratfunc.liftMonoidWithZeroHom_injective

/-- Lift an injective ring homomorphism `R[X] →+* L` to a `ratfunc R →+* L`
by mapping both the numerator and denominator and quotienting them. -/
def liftRingHom (φ : R[X] →+* L) (hφ : R[X]⁰ ≤ L⁰.comap φ) : Ratfunc R →+* L :=
  { liftMonoidWithZeroHom φ.toMonoidWithZeroHom hφ with
    map_add' := fun x y => by
      simp only [MonoidWithZeroHom.toFun_eq_coe]
      cases subsingleton_or_nontrivial R
      · rw [Subsingleton.elim (x + y) y, Subsingleton.elim x 0, map_zero, zero_add]
      cases x
      cases y
      induction' x with p q
      induction' y with p' q'
      · rw [← of_fraction_ring_add, Localization.add_mk]
        simp only [RingHom.toMonoidWithZeroHom_eq_coe,
          lift_monoid_with_zero_hom_apply_of_fraction_ring_mk]
        rw [div_add_div, div_eq_div_iff]
        · rw [mul_comm _ p, mul_comm _ p', mul_comm _ (φ p'), add_comm]
          simp only [map_add, map_mul, Submonoid.coe_mul]
        all_goals
          try simp only [← map_mul, ← Submonoid.coe_mul]
          exact nonZeroDivisors.ne_zero (hφ (SetLike.coe_mem _))
      · rfl
      · rfl }
#align ratfunc.lift_ring_hom Ratfunc.liftRingHom

theorem liftRingHom_apply_of_fraction_ring_mk (φ : R[X] →+* L) (hφ : R[X]⁰ ≤ L⁰.comap φ) (n : R[X])
    (d : R[X]⁰) : liftRingHom φ hφ (of_fraction_ring (Localization.mk n d)) = φ n / φ d :=
  liftMonoidWithZeroHom_apply_of_fraction_ring_mk _ _ _ _
#align ratfunc.lift_ring_hom_apply_of_fraction_ring_mk Ratfunc.liftRingHom_apply_of_fraction_ring_mk

theorem liftRingHom_injective [Nontrivial R] (φ : R[X] →+* L) (hφ : Function.Injective φ)
    (hφ' : R[X]⁰ ≤ L⁰.comap φ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hφ) :
    Function.Injective (liftRingHom φ hφ') :=
  liftMonoidWithZeroHom_injective _ hφ
#align ratfunc.lift_ring_hom_injective Ratfunc.liftRingHom_injective

end LiftHom

variable (K)

include hdomain

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ratfunc.frac_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ratfunc.frac_tac -/
instance : Field (Ratfunc K) :=
  { Ratfunc.commRing K,
    Ratfunc.nontrivial K with
    inv := Inv.inv
    inv_zero := by
      run_tac
        frac_tac
    div := (· / ·)
    div_eq_mul_inv := by
      run_tac
        frac_tac
    mul_inv_cancel := fun _ => mul_inv_cancel
    zpow := zpowRec }

end Field

section IsFractionRing

/-! ### `ratfunc` as field of fractions of `polynomial` -/


include hdomain

instance (R : Type _) [CommSemiring R] [Algebra R K[X]] : Algebra R (Ratfunc K)
    where
  toFun x := Ratfunc.mk (algebraMap _ _ x) 1
  map_add' x y := by simp only [mk_one', RingHom.map_add, of_fraction_ring_add]
  map_mul' x y := by simp only [mk_one', RingHom.map_mul, of_fraction_ring_mul]
  map_one' := by simp only [mk_one', RingHom.map_one, of_fraction_ring_one]
  map_zero' := by simp only [mk_one', RingHom.map_zero, of_fraction_ring_zero]
  smul := (· • ·)
  smul_def' c x :=
    x.inductionOn' fun p q hq => by
      simp_rw [mk_one', ← mk_smul, mk_def_of_ne (c • p) hq, mk_def_of_ne p hq, ←
        of_fraction_ring_mul, IsLocalization.mul_mk'_eq_mk'_of_mul, Algebra.smul_def]
  commutes' c x := mul_comm _ _

variable {K}

theorem mk_one (x : K[X]) : Ratfunc.mk x 1 = algebraMap _ _ x :=
  rfl
#align ratfunc.mk_one Ratfunc.mk_one

theorem of_fraction_ring_algebraMap (x : K[X]) :
    of_fraction_ring (algebraMap _ (FractionRing K[X]) x) = algebraMap _ _ x := by
  rw [← mk_one, mk_one']
#align ratfunc.of_fraction_ring_algebra_map Ratfunc.of_fraction_ring_algebraMap

@[simp]
theorem mk_eq_div (p q : K[X]) : Ratfunc.mk p q = algebraMap _ _ p / algebraMap _ _ q := by
  simp only [mk_eq_div', of_fraction_ring_div, of_fraction_ring_algebra_map]
#align ratfunc.mk_eq_div Ratfunc.mk_eq_div

@[simp]
theorem div_smul {R} [Monoid R] [DistribMulAction R K[X]] [IsScalarTower R K[X] K[X]] (c : R)
    (p q : K[X]) :
    algebraMap _ (Ratfunc K) (c • p) / algebraMap _ _ q =
      c • (algebraMap _ _ p / algebraMap _ _ q) :=
  by rw [← mk_eq_div, mk_smul, mk_eq_div]
#align ratfunc.div_smul Ratfunc.div_smul

theorem algebraMap_apply {R : Type _} [CommSemiring R] [Algebra R K[X]] (x : R) :
    algebraMap R (Ratfunc K) x = algebraMap _ _ (algebraMap R K[X] x) / algebraMap K[X] _ 1 :=
  by
  rw [← mk_eq_div]
  rfl
#align ratfunc.algebra_map_apply Ratfunc.algebraMap_apply

theorem map_apply_div_ne_zero {R F : Type _} [CommRing R] [IsDomain R] [MonoidHomClass F K[X] R[X]]
    (φ : F) (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) (p q : K[X]) (hq : q ≠ 0) :
    map φ hφ (algebraMap _ _ p / algebraMap _ _ q) = algebraMap _ _ (φ p) / algebraMap _ _ (φ q) :=
  by
  have hq' : φ q ≠ 0 := nonZeroDivisors.ne_zero (hφ (mem_non_zero_divisors_iff_ne_zero.mpr hq))
  simp only [← mk_eq_div, mk_eq_localization_mk _ hq, map_apply_of_fraction_ring_mk,
    mk_eq_localization_mk _ hq', [anonymous]]
#align ratfunc.map_apply_div_ne_zero Ratfunc.map_apply_div_ne_zero

@[simp]
theorem map_apply_div {R F : Type _} [CommRing R] [IsDomain R] [MonoidWithZeroHomClass F K[X] R[X]]
    (φ : F) (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) (p q : K[X]) :
    map φ hφ (algebraMap _ _ p / algebraMap _ _ q) = algebraMap _ _ (φ p) / algebraMap _ _ (φ q) :=
  by
  rcases eq_or_ne q 0 with (rfl | hq)
  · have : (0 : Ratfunc K) = algebraMap K[X] _ 0 / algebraMap K[X] _ 1 := by simp
    rw [map_zero, map_zero, map_zero, div_zero, div_zero, this, map_apply_div_ne_zero, map_one,
      map_one, div_one, map_zero, map_zero]
    exact one_ne_zero
  exact map_apply_div_ne_zero _ _ _ _ hq
#align ratfunc.map_apply_div Ratfunc.map_apply_div

@[simp]
theorem liftMonoidWithZeroHom_apply_div {L : Type _} [CommGroupWithZero L]
    (φ : MonoidWithZeroHom K[X] L) (hφ : K[X]⁰ ≤ L⁰.comap φ) (p q : K[X]) :
    liftMonoidWithZeroHom φ hφ (algebraMap _ _ p / algebraMap _ _ q) = φ p / φ q :=
  by
  rcases eq_or_ne q 0 with (rfl | hq)
  · simp only [div_zero, map_zero]
  simpa only [← mk_eq_div, mk_eq_localization_mk _ hq,
    lift_monoid_with_zero_hom_apply_of_fraction_ring_mk]
#align ratfunc.lift_monoid_with_zero_hom_apply_div Ratfunc.liftMonoidWithZeroHom_apply_div

@[simp]
theorem liftRingHom_apply_div {L : Type _} [Field L] (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ)
    (p q : K[X]) : liftRingHom φ hφ (algebraMap _ _ p / algebraMap _ _ q) = φ p / φ q :=
  liftMonoidWithZeroHom_apply_div _ _ _ _
#align ratfunc.lift_ring_hom_apply_div Ratfunc.liftRingHom_apply_div

variable (K)

theorem of_fraction_ring_comp_algebraMap :
    of_fraction_ring ∘ algebraMap K[X] (FractionRing K[X]) = algebraMap _ _ :=
  funext of_fraction_ring_algebraMap
#align ratfunc.of_fraction_ring_comp_algebra_map Ratfunc.of_fraction_ring_comp_algebraMap

theorem algebraMap_injective : Function.Injective (algebraMap K[X] (Ratfunc K)) :=
  by
  rw [← of_fraction_ring_comp_algebra_map]
  exact of_fraction_ring_injective.comp (IsFractionRing.injective _ _)
#align ratfunc.algebra_map_injective Ratfunc.algebraMap_injective

@[simp]
theorem algebraMap_eq_zero_iff {x : K[X]} : algebraMap K[X] (Ratfunc K) x = 0 ↔ x = 0 :=
  ⟨(injective_iff_map_eq_zero _).mp (algebraMap_injective K) _, fun hx => by
    rw [hx, RingHom.map_zero]⟩
#align ratfunc.algebra_map_eq_zero_iff Ratfunc.algebraMap_eq_zero_iff

variable {K}

theorem algebraMap_ne_zero {x : K[X]} (hx : x ≠ 0) : algebraMap K[X] (Ratfunc K) x ≠ 0 :=
  mt (algebraMap_eq_zero_iff K).mp hx
#align ratfunc.algebra_map_ne_zero Ratfunc.algebraMap_ne_zero

section LiftAlgHom

variable {L R S : Type _} [Field L] [CommRing R] [IsDomain R] [CommSemiring S] [Algebra S K[X]]
  [Algebra S L] [Algebra S R[X]] (φ : K[X] →ₐ[S] L) (hφ : K[X]⁰ ≤ L⁰.comap φ)

/-- Lift an algebra homomorphism that maps polynomials `φ : K[X] →ₐ[S] R[X]`
to a `ratfunc K →ₐ[S] ratfunc R`,
on the condition that `φ` maps non zero divisors to non zero divisors,
by mapping both the numerator and denominator and quotienting them. -/
def mapAlgHom (φ : K[X] →ₐ[S] R[X]) (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) : Ratfunc K →ₐ[S] Ratfunc R :=
  { mapRingHom φ hφ with
    commutes' := fun r => by
      simp_rw [RingHom.toFun_eq_coe, coe_map_ring_hom_eq_coe_map, algebraMap_apply r, map_apply_div,
        map_one, AlgHom.commutes] }
#align ratfunc.map_alg_hom Ratfunc.mapAlgHom

theorem coe_mapAlgHom_eq_coe_map (φ : K[X] →ₐ[S] R[X]) (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) :
    (mapAlgHom φ hφ : Ratfunc K → Ratfunc R) = map φ hφ :=
  rfl
#align ratfunc.coe_map_alg_hom_eq_coe_map Ratfunc.coe_mapAlgHom_eq_coe_map

/-- Lift an injective algebra homomorphism `K[X] →ₐ[S] L` to a `ratfunc K →ₐ[S] L`
by mapping both the numerator and denominator and quotienting them. -/
def liftAlgHom : Ratfunc K →ₐ[S] L :=
  { liftRingHom φ.toRingHom hφ with
    commutes' := fun r => by
      simp_rw [RingHom.toFun_eq_coe, AlgHom.toRingHom_eq_coe, algebraMap_apply r,
        lift_ring_hom_apply_div, AlgHom.coe_toRingHom, map_one, div_one, AlgHom.commutes] }
#align ratfunc.lift_alg_hom Ratfunc.liftAlgHom

theorem liftAlgHom_apply_of_fraction_ring_mk (n : K[X]) (d : K[X]⁰) :
    liftAlgHom φ hφ (of_fraction_ring (Localization.mk n d)) = φ n / φ d :=
  liftMonoidWithZeroHom_apply_of_fraction_ring_mk _ _ _ _
#align ratfunc.lift_alg_hom_apply_of_fraction_ring_mk Ratfunc.liftAlgHom_apply_of_fraction_ring_mk

theorem liftAlgHom_injective (φ : K[X] →ₐ[S] L) (hφ : Function.Injective φ)
    (hφ' : K[X]⁰ ≤ L⁰.comap φ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hφ) :
    Function.Injective (liftAlgHom φ hφ') :=
  liftMonoidWithZeroHom_injective _ hφ
#align ratfunc.lift_alg_hom_injective Ratfunc.liftAlgHom_injective

@[simp]
theorem liftAlgHom_apply_div (p q : K[X]) :
    liftAlgHom φ hφ (algebraMap _ _ p / algebraMap _ _ q) = φ p / φ q :=
  liftMonoidWithZeroHom_apply_div _ _ _ _
#align ratfunc.lift_alg_hom_apply_div Ratfunc.liftAlgHom_apply_div

end LiftAlgHom

variable (K)

omit hdomain

include hdomain

/-- `ratfunc K` is the field of fractions of the polynomials over `K`. -/
instance : IsFractionRing K[X] (Ratfunc K)
    where
  map_units y := by
    rw [← of_fraction_ring_algebra_map] <;>
      exact (to_fraction_ring_ring_equiv K).symm.toRingHom.isUnit_map (IsLocalization.map_units _ y)
  eq_iff_exists x y := by
    rw [← of_fraction_ring_algebra_map, ← of_fraction_ring_algebra_map] <;>
      exact
        (to_fraction_ring_ring_equiv K).symm.Injective.eq_iff.trans
          (IsLocalization.eq_iff_exists _ _)
  surj := by
    rintro ⟨z⟩
    convert IsLocalization.surj K[X]⁰ z
    ext ⟨x, y⟩
    simp only [← of_fraction_ring_algebra_map, Function.comp_apply, ← of_fraction_ring_mul]

variable {K}

@[simp]
theorem liftOn_div {P : Sort v} (p q : K[X]) (f : ∀ p q : K[X], P) (f0 : ∀ p, f p 0 = f 0 1)
    (H' : ∀ {p q p' q'} (hq : q ≠ 0) (hq' : q' ≠ 0), q' * p = q * p' → f p q = f p' q')
    (H : ∀ {p q p' q'} (hq : q ∈ K[X]⁰) (hq' : q' ∈ K[X]⁰), q' * p = q * p' → f p q = f p' q' :=
      fun p q p' q' hq hq' h => H' (nonZeroDivisors.ne_zero hq) (nonZeroDivisors.ne_zero hq') h) :
    (algebraMap _ (Ratfunc K) p / algebraMap _ _ q).liftOn f @H = f p q := by
  rw [← mk_eq_div, lift_on_mk _ _ f f0 @H']
#align ratfunc.lift_on_div Ratfunc.liftOn_div

@[simp]
theorem liftOn'_div {P : Sort v} (p q : K[X]) (f : ∀ p q : K[X], P) (f0 : ∀ p, f p 0 = f 0 1) (H) :
    (algebraMap _ (Ratfunc K) p / algebraMap _ _ q).liftOn' f @H = f p q :=
  by
  rw [Ratfunc.liftOn', lift_on_div _ _ _ f0]
  exact lift_on_condition_of_lift_on'_condition @H
#align ratfunc.lift_on'_div Ratfunc.liftOn'_div

/-- Induction principle for `ratfunc K`: if `f p q : P (p / q)` for all `p q : K[X]`,
then `P` holds on all elements of `ratfunc K`.

See also `induction_on'`, which is a recursion principle defined in terms of `ratfunc.mk`.
-/
protected theorem induction_on {P : Ratfunc K → Prop} (x : Ratfunc K)
    (f : ∀ (p q : K[X]) (hq : q ≠ 0), P (algebraMap _ (Ratfunc K) p / algebraMap _ _ q)) : P x :=
  x.inductionOn' fun p q hq => by simpa using f p q hq
#align ratfunc.induction_on Ratfunc.induction_on

theorem of_fraction_ring_mk' (x : K[X]) (y : K[X]⁰) :
    of_fraction_ring (IsLocalization.mk' _ x y) = IsLocalization.mk' (Ratfunc K) x y := by
  rw [IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div, ← mk_eq_div', ← mk_eq_div]
#align ratfunc.of_fraction_ring_mk' Ratfunc.of_fraction_ring_mk'

@[simp]
theorem of_fraction_ring_eq :
    (of_fraction_ring : FractionRing K[X] → Ratfunc K) = IsLocalization.algEquiv K[X]⁰ _ _ :=
  funext fun x =>
    Localization.induction_on x fun x => by
      simp only [IsLocalization.algEquiv_apply, IsLocalization.ringEquivOfRingEquiv_apply,
        [anonymous], Localization.mk_eq_mk'_apply, IsLocalization.map_mk', of_fraction_ring_mk',
        RingEquiv.coe_toRingHom, RingEquiv.refl_apply, SetLike.eta]
#align ratfunc.of_fraction_ring_eq Ratfunc.of_fraction_ring_eq

@[simp]
theorem toFractionRing_eq :
    (toFractionRing : Ratfunc K → FractionRing K[X]) = IsLocalization.algEquiv K[X]⁰ _ _ :=
  funext fun ⟨x⟩ =>
    Localization.induction_on x fun x => by
      simp only [Localization.mk_eq_mk'_apply, of_fraction_ring_mk', IsLocalization.algEquiv_apply,
        [anonymous], IsLocalization.ringEquivOfRingEquiv_apply, IsLocalization.map_mk',
        RingEquiv.coe_toRingHom, RingEquiv.refl_apply, SetLike.eta]
#align ratfunc.to_fraction_ring_eq Ratfunc.toFractionRing_eq

@[simp]
theorem toFractionRingRingEquiv_symm_eq :
    (toFractionRingRingEquiv K).symm = (IsLocalization.algEquiv K[X]⁰ _ _).toRingEquiv :=
  by
  ext x
  simp [to_fraction_ring_ring_equiv, of_fraction_ring_eq, AlgEquiv.coe_ringEquiv']
#align ratfunc.to_fraction_ring_ring_equiv_symm_eq Ratfunc.toFractionRingRingEquiv_symm_eq

end IsFractionRing

section NumDenom

/-! ### Numerator and denominator -/


open GCDMonoid Polynomial

omit hring

variable [hfield : Field K]

include hfield

/-- `ratfunc.num_denom` are numerator and denominator of a rational function over a field,
normalized such that the denominator is monic. -/
def numDenom (x : Ratfunc K) : K[X] × K[X] :=
  x.liftOn'
    (fun p q =>
      if q = 0 then ⟨0, 1⟩
      else
        let r := gcd p q
        ⟨Polynomial.C (q / r).leadingCoeff⁻¹ * (p / r),
          Polynomial.C (q / r).leadingCoeff⁻¹ * (q / r)⟩)
    (by
      intro p q a hq ha
      rw [if_neg hq, if_neg (mul_ne_zero ha hq)]
      have hpq : gcd p q ≠ 0 := mt (And.right ∘ (gcd_eq_zero_iff _ _).mp) hq
      have ha' : a.leading_coeff ≠ 0 := polynomial.leading_coeff_ne_zero.mpr ha
      have hainv : a.leading_coeff⁻¹ ≠ 0 := inv_ne_zero ha'
      simp only [Prod.ext_iff, gcd_mul_left, normalize_apply, Polynomial.coe_normUnit, mul_assoc,
        CommGroupWithZero.coe_normUnit _ ha']
      have hdeg : (gcd p q).degree ≤ q.degree := degree_gcd_le_right _ hq
      have hdeg' : (Polynomial.C a.leading_coeff⁻¹ * gcd p q).degree ≤ q.degree :=
        by
        rw [Polynomial.degree_mul, Polynomial.degree_C hainv, zero_add]
        exact hdeg
      have hdivp : Polynomial.C a.leading_coeff⁻¹ * gcd p q ∣ p :=
        (C_mul_dvd hainv).mpr (gcd_dvd_left p q)
      have hdivq : Polynomial.C a.leading_coeff⁻¹ * gcd p q ∣ q :=
        (C_mul_dvd hainv).mpr (gcd_dvd_right p q)
      rw [EuclideanDomain.mul_div_mul_cancel ha hdivp, EuclideanDomain.mul_div_mul_cancel ha hdivq,
        leading_coeff_div hdeg, leading_coeff_div hdeg', Polynomial.leadingCoeff_mul,
        Polynomial.leadingCoeff_C, div_C_mul, div_C_mul, ← mul_assoc, ← Polynomial.C_mul, ←
        mul_assoc, ← Polynomial.C_mul]
      constructor <;> congr <;>
        rw [inv_div, mul_comm, mul_div_assoc, ← mul_assoc, inv_inv, _root_.mul_inv_cancel ha',
          one_mul, inv_div])
#align ratfunc.num_denom Ratfunc.numDenom

@[simp]
theorem numDenom_div (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    numDenom (algebraMap _ _ p / algebraMap _ _ q) =
      (Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q),
        Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (q / gcd p q)) :=
  by
  rw [num_denom, lift_on'_div, if_neg hq]
  intro p
  rw [if_pos rfl, if_neg (one_ne_zero' K[X])]
  simp
#align ratfunc.num_denom_div Ratfunc.numDenom_div

/-- `ratfunc.num` is the numerator of a rational function,
normalized such that the denominator is monic. -/
def num (x : Ratfunc K) : K[X] :=
  x.num_den.1
#align ratfunc.num Ratfunc.num

private theorem num_div' (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    num (algebraMap _ _ p / algebraMap _ _ q) =
      Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q) :=
  by rw [Num, num_denom_div _ hq]
#align ratfunc.num_div' ratfunc.num_div'

@[simp]
theorem num_zero : num (0 : Ratfunc K) = 0 := by convert num_div' (0 : K[X]) one_ne_zero <;> simp
#align ratfunc.num_zero Ratfunc.num_zero

@[simp]
theorem num_div (p q : K[X]) :
    num (algebraMap _ _ p / algebraMap _ _ q) =
      Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q) :=
  by
  by_cases hq : q = 0
  · simp [hq]
  · exact num_div' p hq
#align ratfunc.num_div Ratfunc.num_div

@[simp]
theorem num_one : num (1 : Ratfunc K) = 1 := by convert num_div (1 : K[X]) 1 <;> simp
#align ratfunc.num_one Ratfunc.num_one

@[simp]
theorem num_algebraMap (p : K[X]) : num (algebraMap _ _ p) = p := by convert num_div p 1 <;> simp
#align ratfunc.num_algebra_map Ratfunc.num_algebraMap

theorem num_div_dvd (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    num (algebraMap _ _ p / algebraMap _ _ q) ∣ p :=
  by
  rw [num_div _ q, C_mul_dvd]
  · exact EuclideanDomain.div_dvd_of_dvd (gcd_dvd_left p q)
  · simpa only [Ne.def, inv_eq_zero, Polynomial.leadingCoeff_eq_zero] using right_div_gcd_ne_zero hq
#align ratfunc.num_div_dvd Ratfunc.num_div_dvd

/-- A version of `num_div_dvd` with the LHS in simp normal form -/
@[simp]
theorem num_div_dvd' (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q) ∣ p := by simpa using num_div_dvd p hq
#align ratfunc.num_div_dvd' Ratfunc.num_div_dvd'

/-- `ratfunc.denom` is the denominator of a rational function,
normalized such that it is monic. -/
def denom (x : Ratfunc K) : K[X] :=
  x.num_den.2
#align ratfunc.denom Ratfunc.denom

@[simp]
theorem denom_div (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    denom (algebraMap _ _ p / algebraMap _ _ q) =
      Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (q / gcd p q) :=
  by rw [denom, num_denom_div _ hq]
#align ratfunc.denom_div Ratfunc.denom_div

theorem monic_denom (x : Ratfunc K) : (denom x).Monic :=
  x.inductionOn fun p q hq => by
    rw [denom_div p hq, mul_comm]
    exact Polynomial.monic_mul_leadingCoeff_inv (right_div_gcd_ne_zero hq)
#align ratfunc.monic_denom Ratfunc.monic_denom

theorem denom_ne_zero (x : Ratfunc K) : denom x ≠ 0 :=
  (monic_denom x).NeZero
#align ratfunc.denom_ne_zero Ratfunc.denom_ne_zero

@[simp]
theorem denom_zero : denom (0 : Ratfunc K) = 1 := by
  convert denom_div (0 : K[X]) one_ne_zero <;> simp
#align ratfunc.denom_zero Ratfunc.denom_zero

@[simp]
theorem denom_one : denom (1 : Ratfunc K) = 1 := by
  convert denom_div (1 : K[X]) one_ne_zero <;> simp
#align ratfunc.denom_one Ratfunc.denom_one

@[simp]
theorem denom_algebraMap (p : K[X]) : denom (algebraMap _ (Ratfunc K) p) = 1 := by
  convert denom_div p one_ne_zero <;> simp
#align ratfunc.denom_algebra_map Ratfunc.denom_algebraMap

@[simp]
theorem denom_div_dvd (p q : K[X]) : denom (algebraMap _ _ p / algebraMap _ _ q) ∣ q :=
  by
  by_cases hq : q = 0
  · simp [hq]
  rw [denom_div _ hq, C_mul_dvd]
  · exact EuclideanDomain.div_dvd_of_dvd (gcd_dvd_right p q)
  · simpa only [Ne.def, inv_eq_zero, Polynomial.leadingCoeff_eq_zero] using right_div_gcd_ne_zero hq
#align ratfunc.denom_div_dvd Ratfunc.denom_div_dvd

@[simp]
theorem num_div_denom (x : Ratfunc K) : algebraMap _ _ (num x) / algebraMap _ _ (denom x) = x :=
  x.inductionOn fun p q hq =>
    by
    have q_div_ne_zero := right_div_gcd_ne_zero hq
    rw [num_div p q, denom_div p hq, RingHom.map_mul, RingHom.map_mul, mul_div_mul_left,
      div_eq_div_iff, ← RingHom.map_mul, ← RingHom.map_mul, mul_comm _ q, ←
      EuclideanDomain.mul_div_assoc, ← EuclideanDomain.mul_div_assoc, mul_comm]
    · apply gcd_dvd_right
    · apply gcd_dvd_left
    · exact algebra_map_ne_zero q_div_ne_zero
    · exact algebra_map_ne_zero hq
    · refine' algebra_map_ne_zero (mt polynomial.C_eq_zero.mp _)
      exact inv_ne_zero (polynomial.leading_coeff_ne_zero.mpr q_div_ne_zero)
#align ratfunc.num_div_denom Ratfunc.num_div_denom

@[simp]
theorem num_eq_zero_iff {x : Ratfunc K} : num x = 0 ↔ x = 0 :=
  ⟨fun h => by rw [← num_div_denom x, h, RingHom.map_zero, zero_div], fun h => h.symm ▸ num_zero⟩
#align ratfunc.num_eq_zero_iff Ratfunc.num_eq_zero_iff

theorem num_ne_zero {x : Ratfunc K} (hx : x ≠ 0) : num x ≠ 0 :=
  mt num_eq_zero_iff.mp hx
#align ratfunc.num_ne_zero Ratfunc.num_ne_zero

theorem num_mul_eq_mul_denom_iff {x : Ratfunc K} {p q : K[X]} (hq : q ≠ 0) :
    x.num * q = p * x.den ↔ x = algebraMap _ _ p / algebraMap _ _ q :=
  by
  rw [← (algebra_map_injective K).eq_iff, eq_div_iff (algebra_map_ne_zero hq)]
  conv_rhs => rw [← num_div_denom x]
  rw [RingHom.map_mul, RingHom.map_mul, div_eq_mul_inv, mul_assoc, mul_comm (Inv.inv _), ←
    mul_assoc, ← div_eq_mul_inv, div_eq_iff]
  exact algebra_map_ne_zero (denom_ne_zero x)
#align ratfunc.num_mul_eq_mul_denom_iff Ratfunc.num_mul_eq_mul_denom_iff

theorem num_denom_add (x y : Ratfunc K) :
    (x + y).num * (x.den * y.den) = (x.num * y.den + x.den * y.num) * (x + y).den :=
  (num_mul_eq_mul_denom_iff (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))).mpr <|
    by
    conv_lhs => rw [← num_div_denom x, ← num_div_denom y]
    rw [div_add_div, RingHom.map_mul, RingHom.map_add, RingHom.map_mul, RingHom.map_mul]
    · exact algebra_map_ne_zero (denom_ne_zero x)
    · exact algebra_map_ne_zero (denom_ne_zero y)
#align ratfunc.num_denom_add Ratfunc.num_denom_add

theorem num_denom_neg (x : Ratfunc K) : (-x).num * x.den = -x.num * (-x).den := by
  rw [num_mul_eq_mul_denom_iff (denom_ne_zero x), _root_.map_neg, neg_div, num_div_denom]
#align ratfunc.num_denom_neg Ratfunc.num_denom_neg

theorem num_denom_mul (x y : Ratfunc K) :
    (x * y).num * (x.den * y.den) = x.num * y.num * (x * y).den :=
  (num_mul_eq_mul_denom_iff (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))).mpr <| by
    conv_lhs =>
      rw [← num_div_denom x, ← num_div_denom y, div_mul_div_comm, ← RingHom.map_mul, ←
        RingHom.map_mul]
#align ratfunc.num_denom_mul Ratfunc.num_denom_mul

theorem num_dvd {x : Ratfunc K} {p : K[X]} (hp : p ≠ 0) :
    num x ∣ p ↔ ∃ (q : K[X])(hq : q ≠ 0), x = algebraMap _ _ p / algebraMap _ _ q :=
  by
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨hx, hq⟩ := mul_ne_zero_iff.mp hp
    use denom x * q
    rw [RingHom.map_mul, RingHom.map_mul, ← div_mul_div_comm, div_self, mul_one, num_div_denom]
    · exact ⟨mul_ne_zero (denom_ne_zero x) hq, rfl⟩
    · exact algebra_map_ne_zero hq
  · rintro ⟨q, hq, rfl⟩
    exact num_div_dvd p hq
#align ratfunc.num_dvd Ratfunc.num_dvd

theorem denom_dvd {x : Ratfunc K} {q : K[X]} (hq : q ≠ 0) :
    denom x ∣ q ↔ ∃ p : K[X], x = algebraMap _ _ p / algebraMap _ _ q :=
  by
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨hx, hp⟩ := mul_ne_zero_iff.mp hq
    use Num x * p
    rw [RingHom.map_mul, RingHom.map_mul, ← div_mul_div_comm, div_self, mul_one, num_div_denom]
    · exact algebra_map_ne_zero hp
  · rintro ⟨p, rfl⟩
    exact denom_div_dvd p q
#align ratfunc.denom_dvd Ratfunc.denom_dvd

theorem num_mul_dvd (x y : Ratfunc K) : num (x * y) ∣ num x * num y :=
  by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [num_dvd (mul_ne_zero (num_ne_zero hx) (num_ne_zero hy))]
  refine' ⟨x.denom * y.denom, mul_ne_zero (denom_ne_zero x) (denom_ne_zero y), _⟩
  rw [RingHom.map_mul, RingHom.map_mul, ← div_mul_div_comm, num_div_denom, num_div_denom]
#align ratfunc.num_mul_dvd Ratfunc.num_mul_dvd

theorem denom_mul_dvd (x y : Ratfunc K) : denom (x * y) ∣ denom x * denom y :=
  by
  rw [denom_dvd (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))]
  refine' ⟨x.num * y.num, _⟩
  rw [RingHom.map_mul, RingHom.map_mul, ← div_mul_div_comm, num_div_denom, num_div_denom]
#align ratfunc.denom_mul_dvd Ratfunc.denom_mul_dvd

theorem denom_add_dvd (x y : Ratfunc K) : denom (x + y) ∣ denom x * denom y :=
  by
  rw [denom_dvd (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))]
  refine' ⟨x.num * y.denom + x.denom * y.num, _⟩
  rw [RingHom.map_mul, RingHom.map_add, RingHom.map_mul, RingHom.map_mul, ← div_add_div,
    num_div_denom, num_div_denom]
  · exact algebra_map_ne_zero (denom_ne_zero x)
  · exact algebra_map_ne_zero (denom_ne_zero y)
#align ratfunc.denom_add_dvd Ratfunc.denom_add_dvd

theorem map_denom_ne_zero {L F : Type _} [Zero L] [ZeroHomClass F K[X] L] (φ : F)
    (hφ : Function.Injective φ) (f : Ratfunc K) : φ f.den ≠ 0 := fun H =>
  (denom_ne_zero f) ((map_eq_zero_iff φ hφ).mp H)
#align ratfunc.map_denom_ne_zero Ratfunc.map_denom_ne_zero

theorem map_apply {R F : Type _} [CommRing R] [IsDomain R] [MonoidHomClass F K[X] R[X]] (φ : F)
    (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) (f : Ratfunc K) :
    map φ hφ f = algebraMap _ _ (φ f.num) / algebraMap _ _ (φ f.den) :=
  by
  rw [← num_div_denom f, map_apply_div_ne_zero, num_div_denom f]
  exact denom_ne_zero _
#align ratfunc.map_apply Ratfunc.map_apply

theorem liftMonoidWithZeroHom_apply {L : Type _} [CommGroupWithZero L] (φ : K[X] →*₀ L)
    (hφ : K[X]⁰ ≤ L⁰.comap φ) (f : Ratfunc K) : liftMonoidWithZeroHom φ hφ f = φ f.num / φ f.den :=
  by rw [← num_div_denom f, lift_monoid_with_zero_hom_apply_div, num_div_denom]
#align ratfunc.lift_monoid_with_zero_hom_apply Ratfunc.liftMonoidWithZeroHom_apply

theorem liftRingHom_apply {L : Type _} [Field L] (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ)
    (f : Ratfunc K) : liftRingHom φ hφ f = φ f.num / φ f.den :=
  liftMonoidWithZeroHom_apply _ _ _
#align ratfunc.lift_ring_hom_apply Ratfunc.liftRingHom_apply

theorem liftAlgHom_apply {L S : Type _} [Field L] [CommSemiring S] [Algebra S K[X]] [Algebra S L]
    (φ : K[X] →ₐ[S] L) (hφ : K[X]⁰ ≤ L⁰.comap φ) (f : Ratfunc K) :
    liftAlgHom φ hφ f = φ f.num / φ f.den :=
  liftMonoidWithZeroHom_apply _ _ _
#align ratfunc.lift_alg_hom_apply Ratfunc.liftAlgHom_apply

theorem num_mul_denom_add_denom_mul_num_ne_zero {x y : Ratfunc K} (hxy : x + y ≠ 0) :
    x.num * y.den + x.den * y.num ≠ 0 := by
  intro h_zero
  have h := num_denom_add x y
  rw [h_zero, MulZeroClass.zero_mul] at h
  exact (mul_ne_zero (num_ne_zero hxy) (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)) h
#align ratfunc.num_mul_denom_add_denom_mul_num_ne_zero Ratfunc.num_mul_denom_add_denom_mul_num_ne_zero

end NumDenom

section Eval

/-! ### Polynomial structure: `C`, `X`, `eval` -/


include hdomain

/-- `ratfunc.C a` is the constant rational function `a`. -/
def c : K →+* Ratfunc K :=
  algebraMap _ _
#align ratfunc.C Ratfunc.c

@[simp]
theorem algebraMap_eq_c : algebraMap K (Ratfunc K) = c :=
  rfl
#align ratfunc.algebra_map_eq_C Ratfunc.algebraMap_eq_c

@[simp]
theorem algebraMap_c (a : K) : algebraMap K[X] (Ratfunc K) (Polynomial.C a) = c a :=
  rfl
#align ratfunc.algebra_map_C Ratfunc.algebraMap_c

@[simp]
theorem algebraMap_comp_c : (algebraMap K[X] (Ratfunc K)).comp Polynomial.C = c :=
  rfl
#align ratfunc.algebra_map_comp_C Ratfunc.algebraMap_comp_c

theorem smul_eq_c_mul (r : K) (x : Ratfunc K) : r • x = c r * x := by
  rw [Algebra.smul_def, algebra_map_eq_C]
#align ratfunc.smul_eq_C_mul Ratfunc.smul_eq_c_mul

/-- `ratfunc.X` is the polynomial variable (aka indeterminate). -/
def x : Ratfunc K :=
  algebraMap K[X] (Ratfunc K) Polynomial.X
#align ratfunc.X Ratfunc.x

@[simp]
theorem algebraMap_x : algebraMap K[X] (Ratfunc K) Polynomial.X = x :=
  rfl
#align ratfunc.algebra_map_X Ratfunc.algebraMap_x

omit hring hdomain

variable [hfield : Field K]

include hfield

@[simp]
theorem num_c (c : K) : num (c c) = Polynomial.C c :=
  num_algebraMap _
#align ratfunc.num_C Ratfunc.num_c

@[simp]
theorem denom_c (c : K) : denom (c c) = 1 :=
  denom_algebraMap _
#align ratfunc.denom_C Ratfunc.denom_c

@[simp]
theorem num_x : num (x : Ratfunc K) = Polynomial.X :=
  num_algebraMap _
#align ratfunc.num_X Ratfunc.num_x

@[simp]
theorem denom_x : denom (x : Ratfunc K) = 1 :=
  denom_algebraMap _
#align ratfunc.denom_X Ratfunc.denom_x

theorem x_ne_zero : (Ratfunc.x : Ratfunc K) ≠ 0 :=
  Ratfunc.algebraMap_ne_zero Polynomial.X_ne_zero
#align ratfunc.X_ne_zero Ratfunc.x_ne_zero

variable {L : Type _} [Field L]

/-- Evaluate a rational function `p` given a ring hom `f` from the scalar field
to the target and a value `x` for the variable in the target.

Fractions are reduced by clearing common denominators before evaluating:
`eval id 1 ((X^2 - 1) / (X - 1)) = eval id 1 (X + 1) = 2`, not `0 / 0 = 0`.
-/
def eval (f : K →+* L) (a : L) (p : Ratfunc K) : L :=
  (num p).eval₂ f a / (denom p).eval₂ f a
#align ratfunc.eval Ratfunc.eval

variable {f : K →+* L} {a : L}

theorem eval_eq_zero_of_eval₂_denom_eq_zero {x : Ratfunc K}
    (h : Polynomial.eval₂ f a (denom x) = 0) : eval f a x = 0 := by rw [eval, h, div_zero]
#align ratfunc.eval_eq_zero_of_eval₂_denom_eq_zero Ratfunc.eval_eq_zero_of_eval₂_denom_eq_zero

theorem eval₂_denom_ne_zero {x : Ratfunc K} (h : eval f a x ≠ 0) :
    Polynomial.eval₂ f a (denom x) ≠ 0 :=
  mt eval_eq_zero_of_eval₂_denom_eq_zero h
#align ratfunc.eval₂_denom_ne_zero Ratfunc.eval₂_denom_ne_zero

variable (f a)

@[simp]
theorem eval_c {c : K} : eval f a (c c) = f c := by simp [eval]
#align ratfunc.eval_C Ratfunc.eval_c

@[simp]
theorem eval_x : eval f a x = a := by simp [eval]
#align ratfunc.eval_X Ratfunc.eval_x

@[simp]
theorem eval_zero : eval f a 0 = 0 := by simp [eval]
#align ratfunc.eval_zero Ratfunc.eval_zero

@[simp]
theorem eval_one : eval f a 1 = 1 := by simp [eval]
#align ratfunc.eval_one Ratfunc.eval_one

@[simp]
theorem eval_algebraMap {S : Type _} [CommSemiring S] [Algebra S K[X]] (p : S) :
    eval f a (algebraMap _ _ p) = (algebraMap _ K[X] p).eval₂ f a := by
  simp [eval, IsScalarTower.algebraMap_apply S K[X] (Ratfunc K)]
#align ratfunc.eval_algebra_map Ratfunc.eval_algebraMap

/-- `eval` is an additive homomorphism except when a denominator evaluates to `0`.

Counterexample: `eval _ 1 (X / (X-1)) + eval _ 1 (-1 / (X-1)) = 0`
`... ≠ 1 = eval _ 1 ((X-1) / (X-1))`.

See also `ratfunc.eval₂_denom_ne_zero` to make the hypotheses simpler but less general.
-/
theorem eval_add {x y : Ratfunc K} (hx : Polynomial.eval₂ f a (denom x) ≠ 0)
    (hy : Polynomial.eval₂ f a (denom y) ≠ 0) : eval f a (x + y) = eval f a x + eval f a y :=
  by
  unfold eval
  by_cases hxy : Polynomial.eval₂ f a (denom (x + y)) = 0
  · have := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f a (denom_add_dvd x y) hxy
    rw [Polynomial.eval₂_mul] at this
    cases mul_eq_zero.mp this <;> contradiction
  rw [div_add_div _ _ hx hy, eq_div_iff (mul_ne_zero hx hy), div_eq_mul_inv, mul_right_comm, ←
    div_eq_mul_inv, div_eq_iff hxy]
  simp only [← Polynomial.eval₂_mul, ← Polynomial.eval₂_add]
  congr 1
  apply num_denom_add
#align ratfunc.eval_add Ratfunc.eval_add

/-- `eval` is a multiplicative homomorphism except when a denominator evaluates to `0`.

Counterexample: `eval _ 0 X * eval _ 0 (1/X) = 0 ≠ 1 = eval _ 0 1 = eval _ 0 (X * 1/X)`.

See also `ratfunc.eval₂_denom_ne_zero` to make the hypotheses simpler but less general.
-/
theorem eval_mul {x y : Ratfunc K} (hx : Polynomial.eval₂ f a (denom x) ≠ 0)
    (hy : Polynomial.eval₂ f a (denom y) ≠ 0) : eval f a (x * y) = eval f a x * eval f a y :=
  by
  unfold eval
  by_cases hxy : Polynomial.eval₂ f a (denom (x * y)) = 0
  · have := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f a (denom_mul_dvd x y) hxy
    rw [Polynomial.eval₂_mul] at this
    cases mul_eq_zero.mp this <;> contradiction
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hx hy), div_eq_mul_inv, mul_right_comm, ←
    div_eq_mul_inv, div_eq_iff hxy]
  repeat' rw [← Polynomial.eval₂_mul]
  congr 1
  apply num_denom_mul
#align ratfunc.eval_mul Ratfunc.eval_mul

end Eval

section IntDegree

open Polynomial

omit hring

variable [Field K]

/-- `int_degree x` is the degree of the rational function `x`, defined as the difference between
the `nat_degree` of its numerator and the `nat_degree` of its denominator. In particular,
`int_degree 0 = 0`. -/
def intDegree (x : Ratfunc K) : ℤ :=
  natDegree x.num - natDegree x.den
#align ratfunc.int_degree Ratfunc.intDegree

@[simp]
theorem intDegree_zero : intDegree (0 : Ratfunc K) = 0 := by
  rw [int_degree, num_zero, nat_degree_zero, denom_zero, nat_degree_one, sub_self]
#align ratfunc.int_degree_zero Ratfunc.intDegree_zero

@[simp]
theorem intDegree_one : intDegree (1 : Ratfunc K) = 0 := by
  rw [int_degree, num_one, denom_one, sub_self]
#align ratfunc.int_degree_one Ratfunc.intDegree_one

@[simp]
theorem intDegree_c (k : K) : intDegree (Ratfunc.c k) = 0 := by
  rw [int_degree, num_C, nat_degree_C, denom_C, nat_degree_one, sub_self]
#align ratfunc.int_degree_C Ratfunc.intDegree_c

@[simp]
theorem intDegree_x : intDegree (x : Ratfunc K) = 1 := by
  rw [int_degree, Ratfunc.num_x, Polynomial.natDegree_X, Ratfunc.denom_x, Polynomial.natDegree_one,
    Int.ofNat_one, Int.ofNat_zero, sub_zero]
#align ratfunc.int_degree_X Ratfunc.intDegree_x

@[simp]
theorem intDegree_polynomial {p : K[X]} : intDegree (algebraMap K[X] (Ratfunc K) p) = natDegree p :=
  by
  rw [int_degree, Ratfunc.num_algebraMap, Ratfunc.denom_algebraMap, Polynomial.natDegree_one,
    Int.ofNat_zero, sub_zero]
#align ratfunc.int_degree_polynomial Ratfunc.intDegree_polynomial

theorem intDegree_mul {x y : Ratfunc K} (hx : x ≠ 0) (hy : y ≠ 0) :
    intDegree (x * y) = intDegree x + intDegree y :=
  by
  simp only [int_degree, add_sub, sub_add, sub_sub_eq_add_sub, sub_sub, sub_eq_sub_iff_add_eq_add]
  norm_cast
  rw [← Polynomial.natDegree_mul x.denom_ne_zero y.denom_ne_zero, ←
    Polynomial.natDegree_mul (Ratfunc.num_ne_zero (mul_ne_zero hx hy))
      (mul_ne_zero x.denom_ne_zero y.denom_ne_zero),
    ← Polynomial.natDegree_mul (Ratfunc.num_ne_zero hx) (Ratfunc.num_ne_zero hy), ←
    Polynomial.natDegree_mul (mul_ne_zero (Ratfunc.num_ne_zero hx) (Ratfunc.num_ne_zero hy))
      (x * y).den_nz,
    Ratfunc.num_denom_mul]
#align ratfunc.int_degree_mul Ratfunc.intDegree_mul

@[simp]
theorem intDegree_neg (x : Ratfunc K) : intDegree (-x) = intDegree x :=
  by
  by_cases hx : x = 0
  · rw [hx, neg_zero]
  · rw [int_degree, int_degree, ← nat_degree_neg x.num]
    exact
      nat_degree_sub_eq_of_prod_eq (num_ne_zero (neg_ne_zero.mpr hx)) (denom_ne_zero (-x))
        (neg_ne_zero.mpr (num_ne_zero hx)) (denom_ne_zero x) (num_denom_neg x)
#align ratfunc.int_degree_neg Ratfunc.intDegree_neg

theorem intDegree_add {x y : Ratfunc K} (hxy : x + y ≠ 0) :
    (x + y).intDegree = (x.num * y.den + x.den * y.num).natDegree - (x.den * y.den).natDegree :=
  natDegree_sub_eq_of_prod_eq (num_ne_zero hxy) (x + y).den_nz
    (num_mul_denom_add_denom_mul_num_ne_zero hxy) (mul_ne_zero x.den_nz y.den_nz)
    (num_denom_add x y)
#align ratfunc.int_degree_add Ratfunc.intDegree_add

theorem natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree {x : Ratfunc K}
    (hx : x ≠ 0) {s : K[X]} (hs : s ≠ 0) :
    ((x.num * s).natDegree : ℤ) - (s * x.den).natDegree = x.intDegree :=
  by
  apply
    nat_degree_sub_eq_of_prod_eq (mul_ne_zero (num_ne_zero hx) hs) (mul_ne_zero hs x.denom_ne_zero)
      (num_ne_zero hx) x.denom_ne_zero
  rw [mul_assoc]
#align ratfunc.nat_degree_num_mul_right_sub_nat_degree_denom_mul_left_eq_int_degree Ratfunc.natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree

theorem intDegree_add_le {x y : Ratfunc K} (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    intDegree (x + y) ≤ max (intDegree x) (intDegree y) :=
  by
  by_cases hx : x = 0
  · simp [hx] at *
  rw [int_degree_add hxy, ←
    nat_degree_num_mul_right_sub_nat_degree_denom_mul_left_eq_int_degree hx y.denom_ne_zero,
    mul_comm y.denom, ←
    nat_degree_num_mul_right_sub_nat_degree_denom_mul_left_eq_int_degree hy x.denom_ne_zero,
    le_max_iff, sub_le_sub_iff_right, Int.ofNat_le, sub_le_sub_iff_right, Int.ofNat_le, ←
    le_max_iff, mul_comm y.num]
  exact nat_degree_add_le _ _
#align ratfunc.int_degree_add_le Ratfunc.intDegree_add_le

end IntDegree

section LaurentSeries

open PowerSeries LaurentSeries HahnSeries

omit hring

variable {F : Type u} [Field F] (p q : F[X]) (f g : Ratfunc F)

/-- The coercion `ratfunc F → laurent_series F` as bundled alg hom. -/
def coeAlgHom (F : Type u) [Field F] : Ratfunc F →ₐ[F[X]] LaurentSeries F :=
  liftAlgHom (Algebra.ofId _ _) <|
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ <|
      Polynomial.algebraMap_hahnSeries_injective _
#align ratfunc.coe_alg_hom Ratfunc.coeAlgHom

instance coeToLaurentSeries : Coe (Ratfunc F) (LaurentSeries F) :=
  ⟨coeAlgHom F⟩
#align ratfunc.coe_to_laurent_series Ratfunc.coeToLaurentSeries

theorem coe_def : (f : LaurentSeries F) = coeAlgHom F f :=
  rfl
#align ratfunc.coe_def Ratfunc.coe_def

theorem coe_num_denom : (f : LaurentSeries F) = f.num / f.den :=
  liftAlgHom_apply _ _ f
#align ratfunc.coe_num_denom Ratfunc.coe_num_denom

theorem coe_injective : Function.Injective (coe : Ratfunc F → LaurentSeries F) :=
  liftAlgHom_injective _ (Polynomial.algebraMap_hahnSeries_injective _)
#align ratfunc.coe_injective Ratfunc.coe_injective

@[simp, norm_cast]
theorem coe_apply : coeAlgHom F f = f :=
  rfl
#align ratfunc.coe_apply Ratfunc.coe_apply

@[simp, norm_cast]
theorem coe_zero : ((0 : Ratfunc F) : LaurentSeries F) = 0 :=
  (coeAlgHom F).map_zero
#align ratfunc.coe_zero Ratfunc.coe_zero

@[simp, norm_cast]
theorem coe_one : ((1 : Ratfunc F) : LaurentSeries F) = 1 :=
  (coeAlgHom F).map_one
#align ratfunc.coe_one Ratfunc.coe_one

@[simp, norm_cast]
theorem coe_add : ((f + g : Ratfunc F) : LaurentSeries F) = f + g :=
  (coeAlgHom F).map_add _ _
#align ratfunc.coe_add Ratfunc.coe_add

@[simp, norm_cast]
theorem coe_sub : ((f - g : Ratfunc F) : LaurentSeries F) = f - g :=
  (coeAlgHom F).map_sub _ _
#align ratfunc.coe_sub Ratfunc.coe_sub

@[simp, norm_cast]
theorem coe_neg : ((-f : Ratfunc F) : LaurentSeries F) = -f :=
  (coeAlgHom F).map_neg _
#align ratfunc.coe_neg Ratfunc.coe_neg

@[simp, norm_cast]
theorem coe_mul : ((f * g : Ratfunc F) : LaurentSeries F) = f * g :=
  (coeAlgHom F).map_mul _ _
#align ratfunc.coe_mul Ratfunc.coe_mul

@[simp, norm_cast]
theorem coe_pow (n : ℕ) : ((f ^ n : Ratfunc F) : LaurentSeries F) = f ^ n :=
  (coeAlgHom F).map_pow _ _
#align ratfunc.coe_pow Ratfunc.coe_pow

@[simp, norm_cast]
theorem coe_div :
    ((f / g : Ratfunc F) : LaurentSeries F) = (f : LaurentSeries F) / (g : LaurentSeries F) :=
  map_div₀ (coeAlgHom F) _ _
#align ratfunc.coe_div Ratfunc.coe_div

@[simp, norm_cast]
theorem coe_c (r : F) : ((c r : Ratfunc F) : LaurentSeries F) = HahnSeries.C r := by
  rw [coe_num_denom, num_C, denom_C, coe_coe, Polynomial.coe_C, coe_C, coe_coe, Polynomial.coe_one,
    PowerSeries.coe_one, div_one]
#align ratfunc.coe_C Ratfunc.coe_c

-- TODO: generalize over other modules
@[simp, norm_cast]
theorem coe_smul (r : F) : ((r • f : Ratfunc F) : LaurentSeries F) = r • f := by
  rw [smul_eq_C_mul, ← C_mul_eq_smul, coe_mul, coe_C]
#align ratfunc.coe_smul Ratfunc.coe_smul

@[simp, norm_cast]
theorem coe_x : ((x : Ratfunc F) : LaurentSeries F) = single 1 1 := by
  rw [coe_num_denom, num_X, denom_X, coe_coe, Polynomial.coe_X, coe_X, coe_coe, Polynomial.coe_one,
    PowerSeries.coe_one, div_one]
#align ratfunc.coe_X Ratfunc.coe_x

instance : Algebra (Ratfunc F) (LaurentSeries F) :=
  RingHom.toAlgebra (coeAlgHom F).toRingHom

theorem algebraMap_apply_div :
    algebraMap (Ratfunc F) (LaurentSeries F) (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap F[X] (LaurentSeries F) p / algebraMap _ _ q :=
  by
  convert coe_div _ _ <;>
    rw [← mk_one, coe_def, coe_alg_hom, mk_eq_div, lift_alg_hom_apply_div, map_one, div_one,
      Algebra.ofId_apply]
#align ratfunc.algebra_map_apply_div Ratfunc.algebraMap_apply_div

instance : IsScalarTower F[X] (Ratfunc F) (LaurentSeries F) :=
  ⟨fun x y z => by
    ext
    simp⟩

end LaurentSeries

end Ratfunc

