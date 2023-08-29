/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Content

#align_import field_theory.ratfunc from "leanprover-community/mathlib"@"bf9bbbcf0c1c1ead18280b0d010e417b10abb1b6"

/-!
# The field of rational functions

This file defines the field `RatFunc K` of rational functions over a field `K`,
and shows it is the field of fractions of `K[X]`.

## Main definitions

Working with rational functions as polynomials:
 - `RatFunc.field` provides a field structure
 - `RatFunc.C` is the constant polynomial
 - `RatFunc.X` is the indeterminate
 - `RatFunc.eval` evaluates a rational function given a value for the indeterminate
You can use `IsFractionRing` API to treat `RatFunc` as the field of fractions of polynomials:
 * `algebraMap K[X] (RatFunc K)` maps polynomials to rational functions
 * `IsFractionRing.algEquiv` maps other fields of fractions of `K[X]` to `RatFunc K`,
in particular:
 * `FractionRing.algEquiv K[X] (RatFunc K)` maps the generic field of
    fraction construction to `RatFunc K`. Combine this with `AlgEquiv.restrictScalars` to change
    the `FractionRing K[X] ≃ₐ[K[X]] RatFunc K` to
    `FractionRing K[X] ≃ₐ[K] RatFunc K`.

Working with rational functions as fractions:
 - `RatFunc.num` and `RatFunc.denom` give the numerator and denominator.
   These values are chosen to be coprime and such that `RatFunc.denom` is monic.

Embedding of rational functions into Laurent series, provided as a coercion, utilizing
the underlying `RatFunc.coeAlgHom`.

Lifting homomorphisms of polynomials to other types, by mapping and dividing, as long
as the homomorphism retains the non-zero-divisor property:
  - `RatFunc.liftMonoidWithZeroHom` lifts a `K[X] →*₀ G₀` to
      a `RatFunc K →*₀ G₀`, where `[CommRing K] [CommGroupWithZero G₀]`
  - `RatFunc.liftRingHom` lifts a `K[X] →+* L` to a `RatFunc K →+* L`,
      where `[CommRing K] [Field L]`
  - `RatFunc.liftAlgHom` lifts a `K[X] →ₐ[S] L` to a `RatFunc K →ₐ[S] L`,
      where `[CommRing K] [Field L] [CommSemiring S] [Algebra S K[X]] [Algebra S L]`
This is satisfied by injective homs.
We also have lifting homomorphisms of polynomials to other polynomials,
with the same condition on retaining the non-zero-divisor property across the map:
  - `RatFunc.map` lifts `K[X] →* R[X]` when `[CommRing K] [CommRing R]`
  - `RatFunc.mapRingHom` lifts `K[X] →+* R[X]` when `[CommRing K] [CommRing R]`
  - `RatFunc.mapAlgHom` lifts `K[X] →ₐ[S] R[X]` when
    `[CommRing K] [IsDomain K] [CommRing R] [IsDomain R]`

We also have a set of recursion and induction principles:
 - `RatFunc.liftOn`: define a function by mapping a fraction of polynomials `p/q` to `f p q`,
   if `f` is well-defined in the sense that `p/q = p'/q' → f p q = f p' q'`.
 - `RatFunc.liftOn'`: define a function by mapping a fraction of polynomials `p/q` to `f p q`,
   if `f` is well-defined in the sense that `f (a * p) (a * q) = f p' q'`.
 - `RatFunc.induction_on`: if `P` holds on `p / q` for all polynomials `p q`, then `P` holds on all
   rational functions

We define the degree of a rational function, with values in `ℤ`:
 - `intDegree` is the degree of a rational function, defined as the difference between the
   `natDegree` of its numerator and the `natDegree` of its denominator. In particular,
   `intDegree 0 = 0`.

## Implementation notes

To provide good API encapsulation and speed up unification problems,
`RatFunc` is defined as a structure, and all operations are `@[irreducible] def`s

We need a couple of maps to set up the `Field` and `IsFractionRing` structure,
namely `RatFunc.ofFractionRing`, `RatFunc.toFractionRing`, `RatFunc.mk` and
`RatFunc.toFractionRingRingEquiv`.
All these maps get `simp`ed to bundled morphisms like `algebraMap K[X] (RatFunc K)`
and `IsLocalization.algEquiv`.

There are separate lifts and maps of homomorphisms, to provide routes of lifting even when
the codomain is not a field or even an integral domain.

## References

* [Kleiman, *Misconceptions about $K_X$*][kleiman1979]
* https://freedommathdance.blogspot.com/2012/11/misconceptions-about-kx.html
* https://stacks.math.columbia.edu/tag/01X1

-/

noncomputable section

open scoped Classical

open scoped nonZeroDivisors Polynomial

universe u v

variable (K : Type u)

/-- `RatFunc K` is `K(X)`, the field of rational functions over `K`.

The inclusion of polynomials into `RatFunc` is `algebraMap K[X] (RatFunc K)`,
the maps between `RatFunc K` and another field of fractions of `K[X]`,
especially `FractionRing K[X]`, are given by `is_localization.algebra_equiv`.
-/
structure RatFunc [CommRing K] : Type u where ofFractionRing ::
  toFractionRing : FractionRing K[X]
#align ratfunc RatFunc
#align ratfunc.of_fraction_ring RatFunc.ofFractionRing
#align ratfunc.to_fraction_ring RatFunc.toFractionRing

namespace RatFunc

section CommRing

variable {K}

variable [CommRing K]

section Rec

/-! ### Constructing `RatFunc`s and their induction principles -/

theorem ofFractionRing_injective : Function.Injective (ofFractionRing : _ → RatFunc K) :=
  fun _ _ => ofFractionRing.inj
#align ratfunc.of_fraction_ring_injective RatFunc.ofFractionRing_injective

theorem toFractionRing_injective : Function.Injective (toFractionRing : _ → FractionRing K[X])
  -- porting note: the `xy` input was `rfl` and then there was no need for the `subst`
  | ⟨x⟩, ⟨y⟩, xy => by subst xy; rfl
                       -- ⊢ { toFractionRing := x } = { toFractionRing := { toFractionRing := x }.toFrac …
                                 -- 🎉 no goals
#align ratfunc.to_fraction_ring_injective RatFunc.toFractionRing_injective

/-- Non-dependent recursion principle for `RatFunc K`:
To construct a term of `P : Sort*` out of `x : RatFunc K`,
it suffices to provide a constructor `f : Π (p q : K[X]), P`
and a proof that `f p q = f p' q'` for all `p q p' q'` such that `q' * p = q * p'` where
both `q` and `q'` are not zero divisors, stated as `q ∉ K[X]⁰`, `q' ∉ K[X]⁰`.

If considering `K` as an integral domain, this is the same as saying that
we construct a value of `P` for such elements of `RatFunc K` by setting
`lift_on (p / q) f _ = f p q`.

When `[IsDomain K]`, one can use `RatFunc.liftOn'`, which has the stronger requirement
of `∀ {p q a : K[X]} (hq : q ≠ 0) (ha : a ≠ 0), f (a * p) (a * q) = f p q)`.
-/
protected irreducible_def liftOn {P : Sort v} (x : RatFunc K) (f : ∀ _p _q : K[X], P)
    (H : ∀ {p q p' q'} (_hq : q ∈ K[X]⁰) (_hq' : q' ∈ K[X]⁰), q' * p = q * p' → f p q = f p' q') :
    P := by
  refine Localization.liftOn (toFractionRing x) (fun p q => f p q) ?_
  -- ⊢ ∀ {a c : K[X]} {b d : { x // x ∈ K[X]⁰ }}, ↑(Localization.r K[X]⁰) (a, b) (c …
  intros p p' q q' h
  -- ⊢ (fun p q => f p ↑q) p q = (fun p q => f p ↑q) p' q'
  exact H q.2 q'.2 (let ⟨⟨c, hc⟩, mul_eq⟩ := Localization.r_iff_exists.mp h
    mul_cancel_left_coe_nonZeroDivisors.mp mul_eq)
-- porting note: the definition above was as follows
--    (-- Fix timeout by manipulating elaboration order
--    fun p q => f p q)
--    fun p p' q q' h => by
--    exact H q.2 q'.2
--      (let ⟨⟨c, hc⟩, mul_eq⟩ := Localization.r_iff_exists.mp h
--      mul_cancel_left_coe_nonZeroDivisors.mp mul_eq)
#align ratfunc.lift_on RatFunc.liftOn

theorem liftOn_ofFractionRing_mk {P : Sort v} (n : K[X]) (d : K[X]⁰) (f : ∀ _p _q : K[X], P)
    (H : ∀ {p q p' q'} (_hq : q ∈ K[X]⁰) (_hq' : q' ∈ K[X]⁰), q' * p = q * p' → f p q = f p' q') :
    RatFunc.liftOn (ofFractionRing (Localization.mk n d)) f @H = f n d := by
  rw [RatFunc.liftOn]
  -- ⊢ Localization.liftOn { toFractionRing := Localization.mk n d }.toFractionRing …
  exact Localization.liftOn_mk _ _ _ _
  -- 🎉 no goals
#align ratfunc.lift_on_of_fraction_ring_mk RatFunc.liftOn_ofFractionRing_mk

theorem lift_on_condition_of_lift_on'_condition {P : Sort v} {f : ∀ _p _q : K[X], P}
    (H : ∀ {p q a} (hq : q ≠ 0) (_ha : a ≠ 0), f (a * p) (a * q) = f p q) ⦃p q p' q' : K[X]⦄
    (hq : q ≠ 0) (hq' : q' ≠ 0) (h : q' * p = q * p') : f p q = f p' q' :=
  calc
    f p q = f (q' * p) (q' * q) := (H hq hq').symm
    _ = f (q * p') (q * q') := by rw [h, mul_comm q']
                                  -- 🎉 no goals
    _ = f p' q' := H hq' hq
#align ratfunc.lift_on_condition_of_lift_on'_condition RatFunc.lift_on_condition_of_lift_on'_condition

section IsDomain

variable [IsDomain K]

/-- `RatFunc.mk (p q : K[X])` is `p / q` as a rational function.

If `q = 0`, then `mk` returns 0.

This is an auxiliary definition used to define an `Algebra` structure on `RatFunc`;
the `simp` normal form of `mk p q` is `algebraMap _ _ p / algebraMap _ _ q`.
-/
protected irreducible_def mk (p q : K[X]) : RatFunc K :=
  ofFractionRing (algebraMap _ _ p / algebraMap _ _ q)
#align ratfunc.mk RatFunc.mk

theorem mk_eq_div' (p q : K[X]) :
    RatFunc.mk p q = ofFractionRing (algebraMap _ _ p / algebraMap _ _ q) := by rw [RatFunc.mk]
                                                                                -- 🎉 no goals
#align ratfunc.mk_eq_div' RatFunc.mk_eq_div'

theorem mk_zero (p : K[X]) : RatFunc.mk p 0 = ofFractionRing (0 : FractionRing K[X]) := by
  rw [mk_eq_div', RingHom.map_zero, div_zero]
  -- 🎉 no goals
#align ratfunc.mk_zero RatFunc.mk_zero

theorem mk_coe_def (p : K[X]) (q : K[X]⁰) :
    -- porting note: filled in `(FractionRing K[X])` that was an underscore.
    RatFunc.mk p q = ofFractionRing (IsLocalization.mk' (FractionRing K[X]) p q) := by
  simp only [mk_eq_div', ← Localization.mk_eq_mk', FractionRing.mk_eq_div]
  -- 🎉 no goals
#align ratfunc.mk_coe_def RatFunc.mk_coe_def

theorem mk_def_of_mem (p : K[X]) {q} (hq : q ∈ K[X]⁰) :
    RatFunc.mk p q = ofFractionRing (IsLocalization.mk' (FractionRing K[X]) p ⟨q, hq⟩) := by
  -- porting note: there was an `[anonymous]` in the simp set
  simp only [← mk_coe_def]
  -- 🎉 no goals
#align ratfunc.mk_def_of_mem RatFunc.mk_def_of_mem

theorem mk_def_of_ne (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    RatFunc.mk p q =
      ofFractionRing (IsLocalization.mk' (FractionRing K[X]) p
        ⟨q, mem_nonZeroDivisors_iff_ne_zero.mpr hq⟩) :=
  mk_def_of_mem p _
#align ratfunc.mk_def_of_ne RatFunc.mk_def_of_ne

theorem mk_eq_localization_mk (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    RatFunc.mk p q =
      ofFractionRing (Localization.mk p ⟨q, mem_nonZeroDivisors_iff_ne_zero.mpr hq⟩) :=
  -- porting note: the original proof, did not need `<;> exact hq`
  by rw [mk_def_of_ne, Localization.mk_eq_mk'] <;> exact hq
     -- ⊢ q ≠ 0
                                                   -- 🎉 no goals
#align ratfunc.mk_eq_localization_mk RatFunc.mk_eq_localization_mk

--  porting note: replaced `algebraMap _ _` with `algebraMap K[X] (FractionRing K[X])`
theorem mk_one' (p : K[X]) :
    RatFunc.mk p 1 = ofFractionRing (algebraMap K[X] (FractionRing K[X]) p) := by
  -- Porting note: had to hint `M := K[X]⁰` below
  rw [← IsLocalization.mk'_one (M := K[X]⁰) (FractionRing K[X]) p, ← mk_coe_def, Submonoid.coe_one]
  -- 🎉 no goals
#align ratfunc.mk_one' RatFunc.mk_one'

theorem mk_eq_mk {p q p' q' : K[X]} (hq : q ≠ 0) (hq' : q' ≠ 0) :
    RatFunc.mk p q = RatFunc.mk p' q' ↔ p * q' = p' * q := by
  rw [mk_def_of_ne _ hq, mk_def_of_ne _ hq', ofFractionRing_injective.eq_iff,
    IsLocalization.mk'_eq_iff_eq', -- porting note: removed `[anonymous], [anonymous]`
    (IsFractionRing.injective K[X] (FractionRing K[X])).eq_iff]
#align ratfunc.mk_eq_mk RatFunc.mk_eq_mk

theorem liftOn_mk {P : Sort v} (p q : K[X]) (f : ∀ _p _q : K[X], P) (f0 : ∀ p, f p 0 = f 0 1)
    (H' : ∀ {p q p' q'} (_hq : q ≠ 0) (_hq' : q' ≠ 0), q' * p = q * p' → f p q = f p' q')
    (H : ∀ {p q p' q'} (_hq : q ∈ K[X]⁰) (_hq' : q' ∈ K[X]⁰), q' * p = q * p' → f p q = f p' q' :=
      fun {p q p' q'} hq hq' h => H' (nonZeroDivisors.ne_zero hq) (nonZeroDivisors.ne_zero hq') h) :
    (RatFunc.mk p q).liftOn f @H = f p q := by
  by_cases hq : q = 0
  -- ⊢ RatFunc.liftOn (RatFunc.mk p q) f H = f p q
  · subst hq
    -- ⊢ RatFunc.liftOn (RatFunc.mk p 0) f H = f p 0
    simp only [mk_zero, f0, ← Localization.mk_zero 1, Localization.liftOn_mk,
      liftOn_ofFractionRing_mk, Submonoid.coe_one]
  · simp only [mk_eq_localization_mk _ hq, Localization.liftOn_mk, liftOn_ofFractionRing_mk]
    -- 🎉 no goals
#align ratfunc.lift_on_mk RatFunc.liftOn_mk

/-- Non-dependent recursion principle for `RatFunc K`: if `f p q : P` for all `p q`,
such that `f (a * p) (a * q) = f p q`, then we can find a value of `P`
for all elements of `RatFunc K` by setting `lift_on' (p / q) f _ = f p q`.

The value of `f p 0` for any `p` is never used and in principle this may be anything,
although many usages of `lift_on'` assume `f p 0 = f 0 1`.
-/
protected irreducible_def liftOn' {P : Sort v} (x : RatFunc K) (f : ∀ _p _q : K[X], P)
  (H : ∀ {p q a} (_hq : q ≠ 0) (_ha : a ≠ 0), f (a * p) (a * q) = f p q) : P :=
  x.liftOn f fun {_p _q _p' _q'} hq hq' =>
    lift_on_condition_of_lift_on'_condition (@H) (nonZeroDivisors.ne_zero hq)
      (nonZeroDivisors.ne_zero hq')
#align ratfunc.lift_on' RatFunc.liftOn'

theorem liftOn'_mk {P : Sort v} (p q : K[X]) (f : ∀ _p _q : K[X], P) (f0 : ∀ p, f p 0 = f 0 1)
    (H : ∀ {p q a} (_hq : q ≠ 0) (_ha : a ≠ 0), f (a * p) (a * q) = f p q) :
    (RatFunc.mk p q).liftOn' f @H = f p q := by
  rw [RatFunc.liftOn', RatFunc.liftOn_mk _ _ _ f0]
  -- ⊢ ∀ {p q p' q' : K[X]}, q ≠ 0 → q' ≠ 0 → q' * p = q * p' → f p q = f p' q'
  apply lift_on_condition_of_lift_on'_condition H
  -- 🎉 no goals
#align ratfunc.lift_on'_mk RatFunc.liftOn'_mk

/- ./././Mathport/Syntax/Translate/Command.lean:322:38: unsupported irreducible non-definition -/
/-- Induction principle for `RatFunc K`: if `f p q : P (RatFunc.mk p q)` for all `p q`,
then `P` holds on all elements of `RatFunc K`.

See also `induction_on`, which is a recursion principle defined in terms of `algebraMap`.
-/
protected theorem induction_on' {P : RatFunc K → Prop} :
  ∀ (x : RatFunc K) (_pq : ∀ (p q : K[X]) (_ : q ≠ 0), P (RatFunc.mk p q)), P x
  | ⟨x⟩, f =>
    Localization.induction_on x fun ⟨p, q⟩ => by
      simpa only [mk_coe_def, Localization.mk_eq_mk'] using
        f p q (mem_nonZeroDivisors_iff_ne_zero.mp q.2)
#align ratfunc.induction_on' RatFunc.induction_on'

end IsDomain

end Rec

section Field

/-! ### Defining the field structure -/

/-- The zero rational function. -/
protected irreducible_def zero : RatFunc K :=
  ⟨0⟩
#align ratfunc.zero RatFunc.zero

instance : Zero (RatFunc K) :=
  ⟨RatFunc.zero⟩

-- porting note: added `OfNat.ofNat`.  using `simp?` produces `simp only [zero_def]`
-- that does not close the goal
theorem ofFractionRing_zero : (ofFractionRing 0 : RatFunc K) = 0 := by
  simp only [Zero.zero, OfNat.ofNat, RatFunc.zero]
  -- 🎉 no goals
#align ratfunc.of_fraction_ring_zero RatFunc.ofFractionRing_zero

/-- Addition of rational functions. -/
protected irreducible_def add : RatFunc K → RatFunc K → RatFunc K
  | ⟨p⟩, ⟨q⟩ => ⟨p + q⟩
#align ratfunc.add RatFunc.add

instance : Add (RatFunc K) :=
  ⟨RatFunc.add⟩

-- porting note: added `HAdd.hAdd`.  using `simp?` produces `simp only [add_def]`
-- that does not close the goal
theorem ofFractionRing_add (p q : FractionRing K[X]) :
    ofFractionRing (p + q) = ofFractionRing p + ofFractionRing q := by
  simp only [HAdd.hAdd, Add.add, RatFunc.add]
  -- 🎉 no goals
#align ratfunc.of_fraction_ring_add RatFunc.ofFractionRing_add

/-- Subtraction of rational functions. -/
protected irreducible_def sub : RatFunc K → RatFunc K → RatFunc K
  | ⟨p⟩, ⟨q⟩ => ⟨p - q⟩
#align ratfunc.sub RatFunc.sub

instance : Sub (RatFunc K) :=
  ⟨RatFunc.sub⟩

-- porting note: added `HSub.hSub`.  using `simp?` produces `simp only [sub_def]`
-- that does not close the goal
theorem ofFractionRing_sub (p q : FractionRing K[X]) :
    ofFractionRing (p - q) = ofFractionRing p - ofFractionRing q := by
  simp only [Sub.sub, HSub.hSub, RatFunc.sub]
  -- 🎉 no goals
#align ratfunc.of_fraction_ring_sub RatFunc.ofFractionRing_sub

/-- Additive inverse of a rational function. -/
protected irreducible_def neg : RatFunc K → RatFunc K
  | ⟨p⟩ => ⟨-p⟩
#align ratfunc.neg RatFunc.neg

instance : Neg (RatFunc K) :=
  ⟨RatFunc.neg⟩

theorem ofFractionRing_neg (p : FractionRing K[X]) :
    ofFractionRing (-p) = -ofFractionRing p := by simp only [Neg.neg, RatFunc.neg]
                                                  -- 🎉 no goals
#align ratfunc.of_fraction_ring_neg RatFunc.ofFractionRing_neg

/-- The multiplicative unit of rational functions. -/
protected irreducible_def one : RatFunc K :=
  ⟨1⟩
#align ratfunc.one RatFunc.one

instance : One (RatFunc K) :=
  ⟨RatFunc.one⟩

-- porting note: added `OfNat.ofNat`.  using `simp?` produces `simp only [one_def]`
-- that does not close the goal
theorem ofFractionRing_one : (ofFractionRing 1 : RatFunc K) = 1 := by
  simp only [One.one, OfNat.ofNat, RatFunc.one]
  -- 🎉 no goals
#align ratfunc.of_fraction_ring_one RatFunc.ofFractionRing_one

/-- Multiplication of rational functions. -/
protected irreducible_def mul : RatFunc K → RatFunc K → RatFunc K
  | ⟨p⟩, ⟨q⟩ => ⟨p * q⟩
#align ratfunc.mul RatFunc.mul

instance : Mul (RatFunc K) :=
  ⟨RatFunc.mul⟩

-- porting note: added `HMul.hMul`.  using `simp?` produces `simp only [mul_def]`
-- that does not close the goal
theorem ofFractionRing_mul (p q : FractionRing K[X]) :
    ofFractionRing (p * q) = ofFractionRing p * ofFractionRing q := by
  simp only [Mul.mul, HMul.hMul, RatFunc.mul]
  -- 🎉 no goals
#align ratfunc.of_fraction_ring_mul RatFunc.ofFractionRing_mul

section IsDomain

variable [IsDomain K]

/-- Division of rational functions. -/
protected irreducible_def div : RatFunc K → RatFunc K → RatFunc K
  | ⟨p⟩, ⟨q⟩ => ⟨p / q⟩
#align ratfunc.div RatFunc.div

instance : Div (RatFunc K) :=
  ⟨RatFunc.div⟩

-- porting note: added `HDiv.hDiv`.  using `simp?` produces `simp only [div_def]`
-- that does not close the goal
theorem ofFractionRing_div (p q : FractionRing K[X]) :
    ofFractionRing (p / q) = ofFractionRing p / ofFractionRing q := by
  simp only [Div.div, HDiv.hDiv, RatFunc.div]
  -- 🎉 no goals
#align ratfunc.of_fraction_ring_div RatFunc.ofFractionRing_div

/-- Multiplicative inverse of a rational function. -/
protected irreducible_def inv : RatFunc K → RatFunc K
  | ⟨p⟩ => ⟨p⁻¹⟩
#align ratfunc.inv RatFunc.inv

instance : Inv (RatFunc K) :=
  ⟨RatFunc.inv⟩

theorem ofFractionRing_inv (p : FractionRing K[X]) :
    ofFractionRing p⁻¹ = (ofFractionRing p)⁻¹ := by
  simp only [Inv.inv, RatFunc.inv]
  -- 🎉 no goals
#align ratfunc.of_fraction_ring_inv RatFunc.ofFractionRing_inv

-- Auxiliary lemma for the `Field` instance
theorem mul_inv_cancel : ∀ {p : RatFunc K} (_hp : p ≠ 0), p * p⁻¹ = 1
  | ⟨p⟩, h => by
    have : p ≠ 0 := fun hp => h <| by rw [hp, ofFractionRing_zero]
    -- ⊢ { toFractionRing := p } * { toFractionRing := p }⁻¹ = 1
    simpa only [← ofFractionRing_inv, ← ofFractionRing_mul, ← ofFractionRing_one,
      ofFractionRing.injEq] using  -- porting note: `ofFractionRing.injEq` was not present
      _root_.mul_inv_cancel this
#align ratfunc.mul_inv_cancel RatFunc.mul_inv_cancel

end IsDomain

section SMul

variable {R : Type*}

/-- Scalar multiplication of rational functions. -/
protected irreducible_def smul [SMul R (FractionRing K[X])] : R → RatFunc K → RatFunc K
  | r, ⟨p⟩ => ⟨r • p⟩
#align ratfunc.smul RatFunc.smul

-- cannot reproduce
--@[nolint fails_quickly]  -- porting note: `linter 'fails_quickly' not found`
instance [SMul R (FractionRing K[X])] : SMul R (RatFunc K) :=
  ⟨RatFunc.smul⟩

-- porting note: added `SMul.hSMul`.  using `simp?` produces `simp only [smul_def]`
-- that does not close the goal
theorem ofFractionRing_smul [SMul R (FractionRing K[X])] (c : R) (p : FractionRing K[X]) :
    ofFractionRing (c • p) = c • ofFractionRing p := by
  simp only [SMul.smul, HSMul.hSMul, RatFunc.smul]
  -- 🎉 no goals
#align ratfunc.of_fraction_ring_smul RatFunc.ofFractionRing_smul

theorem toFractionRing_smul [SMul R (FractionRing K[X])] (c : R) (p : RatFunc K) :
    toFractionRing (c • p) = c • toFractionRing p := by
  cases p
  -- ⊢ (c • { toFractionRing := toFractionRing✝ }).toFractionRing = c • { toFractio …
  rw [← ofFractionRing_smul]
  -- 🎉 no goals
#align ratfunc.to_fraction_ring_smul RatFunc.toFractionRing_smul

theorem smul_eq_C_smul (x : RatFunc K) (r : K) : r • x = Polynomial.C r • x := by
  cases' x with x
  -- ⊢ r • { toFractionRing := x } = ↑Polynomial.C r • { toFractionRing := x }
  -- Porting note: had to specify the induction principle manually
  induction x using Localization.induction_on
  -- ⊢ r • { toFractionRing := Localization.mk y✝.fst y✝.snd } = ↑Polynomial.C r •  …
  · rw [← ofFractionRing_smul, ← ofFractionRing_smul, Localization.smul_mk,
      Localization.smul_mk, smul_eq_mul, Polynomial.smul_eq_C_mul]
set_option linter.uppercaseLean3 false in
#align ratfunc.smul_eq_C_smul RatFunc.smul_eq_C_smul

section IsDomain

variable [IsDomain K]

variable [Monoid R] [DistribMulAction R K[X]]

variable [IsScalarTower R K[X] K[X]]

theorem mk_smul (c : R) (p q : K[X]) : RatFunc.mk (c • p) q = c • RatFunc.mk p q := by
  by_cases hq : q = 0
  -- ⊢ RatFunc.mk (c • p) q = c • RatFunc.mk p q
  · rw [hq, mk_zero, mk_zero, ← ofFractionRing_smul, smul_zero]
    -- 🎉 no goals
  · rw [mk_eq_localization_mk _ hq, mk_eq_localization_mk _ hq, ← Localization.smul_mk, ←
      ofFractionRing_smul]
#align ratfunc.mk_smul RatFunc.mk_smul

-- porting note: was term-mode.  `exact` instead of `apply` does not work.
instance : IsScalarTower R K[X] (RatFunc K) := ⟨by
  intros c p q
  -- ⊢ (c • p) • q = c • p • q
  apply q.induction_on' fun q r _ => by rw [← mk_smul, smul_assoc, mk_smul, mk_smul]⟩
  -- 🎉 no goals

end IsDomain

end SMul

variable (K)

instance [Subsingleton K] : Subsingleton (RatFunc K) :=
  toFractionRing_injective.subsingleton

instance : Inhabited (RatFunc K) :=
  ⟨0⟩

instance instNontrivial [Nontrivial K] : Nontrivial (RatFunc K) :=
  ofFractionRing_injective.nontrivial
#align ratfunc.nontrivial RatFunc.instNontrivial

/-- `RatFunc K` is isomorphic to the field of fractions of `K[X]`, as rings.

This is an auxiliary definition; `simp`-normal form is `IsLocalization.algEquiv`.
-/
@[simps apply]
def toFractionRingRingEquiv : RatFunc K ≃+* FractionRing K[X] where
  toFun := toFractionRing
  invFun := ofFractionRing
  left_inv := fun ⟨_⟩ => rfl
  right_inv _ := rfl
  map_add' := fun ⟨_⟩ ⟨_⟩ => by simp [← ofFractionRing_add]
                                -- 🎉 no goals
                                -- 🎉 no goals
  map_mul' := fun ⟨_⟩ ⟨_⟩ => by simp [← ofFractionRing_mul]
#align ratfunc.to_fraction_ring_ring_equiv RatFunc.toFractionRingRingEquiv

end Field

section TacticInterlude

-- porting note: reimplemented the `frac_tac` and `smul_tac` as close to the originals as I could
/-- Solve equations for `RatFunc K` by working in `FractionRing K[X]`. -/
macro "frac_tac" : tactic => `(tactic| repeat (rintro (⟨⟩ : RatFunc _)) <;>
  try simp only [← ofFractionRing_zero, ← ofFractionRing_add, ← ofFractionRing_sub,
    ← ofFractionRing_neg, ← ofFractionRing_one, ← ofFractionRing_mul, ← ofFractionRing_div,
    ← ofFractionRing_inv,
    add_assoc, zero_add, add_zero, mul_assoc, mul_zero, mul_one, mul_add, inv_zero,
    add_comm, add_left_comm, mul_comm, mul_left_comm, sub_eq_add_neg, div_eq_mul_inv,
    add_mul, zero_mul, one_mul, neg_mul, mul_neg, add_right_neg])

/-- Solve equations for `RatFunc K` by applying `RatFunc.induction_on`. -/
macro "smul_tac" : tactic => `(tactic|
    repeat
      (first
        | rintro (⟨⟩ : RatFunc _)
        | intro) <;>
    simp_rw [←ofFractionRing_smul] <;>
    simp only [add_comm, mul_comm, zero_smul, succ_nsmul, zsmul_eq_mul, mul_add, mul_one, mul_zero,
      neg_add, mul_neg,
      Int.ofNat_eq_coe, Int.cast_zero, Int.cast_add, Int.cast_one,
      Int.cast_negSucc, Int.cast_ofNat, Nat.cast_succ,
      Localization.mk_zero, Localization.add_mk_self, Localization.neg_mk,
      ofFractionRing_zero, ← ofFractionRing_add, ← ofFractionRing_neg])

end TacticInterlude

variable (K)

-- Porting note: split the CommRing instance up into multiple defs because it was hard to see
-- if the big instance declaration made any progress.
/-- `RatFunc K` is a commutative monoid.

This is an intermediate step on the way to the full instance `RatFunc.instCommRing`.
-/
def instCommMonoid : CommMonoid (RatFunc K) where
  mul := (· * ·)
  mul_assoc := by frac_tac
                  -- 🎉 no goals
  mul_comm := by frac_tac
                 -- 🎉 no goals
  one := 1
                -- 🎉 no goals
  one_mul := by frac_tac
                -- 🎉 no goals
  mul_one := by frac_tac
  npow := npowRec

/-- `RatFunc K` is an additive commutative group.

This is an intermediate step on the way to the full instance `RatFunc.instCommRing`.
-/
def instAddCommGroup : AddCommGroup (RatFunc K) where
  add := (· + ·)
  add_assoc := by frac_tac
                  -- 🎉 no goals
 -- porting note: `by frac_tac` didn't work:
  add_comm := by repeat rintro (⟨⟩ : RatFunc _) <;> simp only [← ofFractionRing_add, add_comm]
                 -- 🎉 no goals
  zero := 0
                 -- 🎉 no goals
  zero_add := by frac_tac
                 -- 🎉 no goals
  add_zero := by frac_tac
  neg := Neg.neg
                     -- 🎉 no goals
  add_left_neg := by frac_tac
                       -- 🎉 no goals
  sub := Sub.sub
                   -- 🎉 no goals
  sub_eq_add_neg := by frac_tac
                     -- 🎉 no goals
  nsmul := (· • ·)
  nsmul_zero := by smul_tac
  nsmul_succ _ := by smul_tac
                    -- 🎉 no goals
  zsmul := (· • ·)
                      -- 🎉 no goals
  zsmul_zero' := by smul_tac
                     -- 🎉 no goals
  zsmul_succ' _ := by smul_tac
  zsmul_neg' _ := by smul_tac

instance instCommRing : CommRing (RatFunc K) :=
  { instCommMonoid K, instAddCommGroup K with
    add := (· + ·)
    zero := 0
    neg := Neg.neg
    sub := Sub.sub
    mul := (· * ·)
    zero_mul := by frac_tac
                   -- 🎉 no goals
    mul_zero := by frac_tac
                       -- 🎉 no goals
                   -- 🎉 no goals
                        -- 🎉 no goals
    left_distrib := by frac_tac
    right_distrib := by frac_tac
    one := 1
    nsmul := (· • ·)
    zsmul := (· • ·)
    npow := npowRec }
#align ratfunc.comm_ring RatFunc.instCommRing

variable {K}

section LiftHom

variable {G₀ L R S F : Type*} [CommGroupWithZero G₀] [Field L] [CommRing R] [CommRing S]

/-- Lift a monoid homomorphism that maps polynomials `φ : R[X] →* S[X]`
to a `RatFunc R →* RatFunc S`,
on the condition that `φ` maps non zero divisors to non zero divisors,
by mapping both the numerator and denominator and quotienting them. -/
def map [MonoidHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) : RatFunc R →* RatFunc S
    where
  toFun f :=
    RatFunc.liftOn f
      (fun n d => if h : φ d ∈ S[X]⁰ then ofFractionRing (Localization.mk (φ n) ⟨φ d, h⟩) else 0)
      fun {p q p' q'} hq hq' h => by
      dsimp only -- porting note: force the function to be applied
      -- ⊢ (if h : ↑φ q ∈ S[X]⁰ then { toFractionRing := Localization.mk (↑φ p) { val : …
      rw [dif_pos, dif_pos]
      congr 1 -- porting note: this was a `rw [ofFractionRing.inj_eq]` which was overkill anyway
      rw [Localization.mk_eq_mk_iff]
      rotate_left
      · exact hφ hq
        -- 🎉 no goals
      · exact hφ hq'
        -- 🎉 no goals
      refine' Localization.r_of_eq _
      -- ⊢ ↑(↑φ p', { val := ↑φ q', property := (_ : q' ∈ Submonoid.comap φ S[X]⁰) }).s …
      simpa only [map_mul] using congr_arg φ h
      -- 🎉 no goals
  map_one' := by
    dsimp only -- porting note: force the function to be applied
    -- ⊢ RatFunc.liftOn 1 (fun n d => if h : ↑φ d ∈ S[X]⁰ then { toFractionRing := Lo …
    rw [← ofFractionRing_one, ← Localization.mk_one, liftOn_ofFractionRing_mk, dif_pos]
    -- ⊢ { toFractionRing := Localization.mk (↑φ 1) { val := ↑φ ↑1, property := ?hc } …
    · simpa using ofFractionRing_one
      -- 🎉 no goals
    · simpa using Submonoid.one_mem _
      -- 🎉 no goals
  map_mul' x y := by
    dsimp only -- porting note: force the function to be applied
    -- ⊢ RatFunc.liftOn (x * y) (fun n d => if h : ↑φ d ∈ S[X]⁰ then { toFractionRing …
    cases' x with x; cases' y with y
    -- ⊢ RatFunc.liftOn ({ toFractionRing := x } * y) (fun n d => if h : ↑φ d ∈ S[X]⁰ …
                     -- ⊢ RatFunc.liftOn ({ toFractionRing := x } * { toFractionRing := y }) (fun n d  …
    -- porting note: added `using Localization.rec` (`Localization.induction_on` didn't work)
    induction' x using Localization.rec with p q
    -- ⊢ RatFunc.liftOn ({ toFractionRing := Localization.mk p q } * { toFractionRing …
    induction' y using Localization.rec with p' q'
    · have hq : φ q ∈ S[X]⁰ := hφ q.prop
      -- ⊢ RatFunc.liftOn ({ toFractionRing := Localization.mk p q } * { toFractionRing …
      have hq' : φ q' ∈ S[X]⁰ := hφ q'.prop
      -- ⊢ RatFunc.liftOn ({ toFractionRing := Localization.mk p q } * { toFractionRing …
      have hqq' : φ ↑(q * q') ∈ S[X]⁰ := by simpa using Submonoid.mul_mem _ hq hq'
      -- ⊢ RatFunc.liftOn ({ toFractionRing := Localization.mk p q } * { toFractionRing …
      simp_rw [← ofFractionRing_mul, Localization.mk_mul, liftOn_ofFractionRing_mk, dif_pos hq,
        dif_pos hq', dif_pos hqq', ← ofFractionRing_mul, Submonoid.coe_mul, map_mul,
        Localization.mk_mul, Submonoid.mk_mul_mk]
    · rfl
      -- 🎉 no goals
    · rfl
      -- 🎉 no goals
#align ratfunc.map RatFunc.map

theorem map_apply_ofFractionRing_mk [MonoidHomClass F R[X] S[X]] (φ : F)
    (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) (n : R[X]) (d : R[X]⁰) :
    map φ hφ (ofFractionRing (Localization.mk n d)) =
      ofFractionRing (Localization.mk (φ n) ⟨φ d, hφ d.prop⟩) := by
  -- porting note: replaced `convert` with `refine Eq.trans`
  refine (liftOn_ofFractionRing_mk n _ _ _).trans ?_
  -- ⊢ (if h : ↑φ ↑d ∈ S[X]⁰ then { toFractionRing := Localization.mk (↑φ n) { val  …
  rw [dif_pos]
  -- 🎉 no goals
#align ratfunc.map_apply_of_fraction_ring_mk RatFunc.map_apply_ofFractionRing_mk

theorem map_injective [MonoidHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ ≤ S[X]⁰.comap φ)
    (hf : Function.Injective φ) : Function.Injective (map φ hφ) := by
  rintro ⟨x⟩ ⟨y⟩ h
  -- ⊢ { toFractionRing := x } = { toFractionRing := y }
  -- porting note: had to hint `induction` which induction principle to use
  induction x using Localization.induction_on
  -- ⊢ { toFractionRing := Localization.mk y✝.fst y✝.snd } = { toFractionRing := y }
  induction y using Localization.induction_on
  -- ⊢ { toFractionRing := Localization.mk y✝¹.fst y✝¹.snd } = { toFractionRing :=  …
  · simpa only [map_apply_ofFractionRing_mk, ofFractionRing_injective.eq_iff,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists, mul_cancel_left_coe_nonZeroDivisors,
      exists_const, ← map_mul, hf.eq_iff] using h
#align ratfunc.map_injective RatFunc.map_injective

/-- Lift a ring homomorphism that maps polynomials `φ : R[X] →+* S[X]`
to a `RatFunc R →+* RatFunc S`,
on the condition that `φ` maps non zero divisors to non zero divisors,
by mapping both the numerator and denominator and quotienting them. -/
def mapRingHom [RingHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) :
    RatFunc R →+* RatFunc S :=
  { map φ hφ with
    map_zero' := by
      simp_rw [MonoidHom.toFun_eq_coe, ← ofFractionRing_zero, ← Localization.mk_zero (1 : R[X]⁰),
        ← Localization.mk_zero (1 : S[X]⁰), map_apply_ofFractionRing_mk, map_zero,
        Localization.mk_eq_mk', IsLocalization.mk'_zero]
    map_add' := by
      rintro ⟨x⟩ ⟨y⟩
      -- ⊢ OneHom.toFun (↑{ toOneHom := ↑src✝, map_mul' := (_ : ∀ (x y : RatFunc R), On …
      -- porting note: had to hint `induction` which induction principle to use
      induction x using Localization.rec
      -- ⊢ OneHom.toFun (↑{ toOneHom := ↑src✝, map_mul' := (_ : ∀ (x y : RatFunc R), On …
      induction y using Localization.rec
      · simp only [← ofFractionRing_add, Localization.add_mk, map_add, map_mul,
          MonoidHom.toFun_eq_coe, map_apply_ofFractionRing_mk, Submonoid.coe_mul]
        -- Porting note: `Submonoid.mk_mul_mk` couldn't be applied: motive incorrect,
        -- even though it is a rfl lemma.
        rfl
        -- 🎉 no goals
      · rfl
        -- 🎉 no goals
      · rfl }
        -- 🎉 no goals
#align ratfunc.map_ring_hom RatFunc.mapRingHom

theorem coe_mapRingHom_eq_coe_map [RingHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) :
    (mapRingHom φ hφ : RatFunc R → RatFunc S) = map φ hφ :=
  rfl
#align ratfunc.coe_map_ring_hom_eq_coe_map RatFunc.coe_mapRingHom_eq_coe_map

-- TODO: Generalize to `FunLike` classes,
/-- Lift a monoid with zero homomorphism `R[X] →*₀ G₀` to a `RatFunc R →*₀ G₀`
on the condition that `φ` maps non zero divisors to non zero divisors,
by mapping both the numerator and denominator and quotienting them. -/
def liftMonoidWithZeroHom (φ : R[X] →*₀ G₀) (hφ : R[X]⁰ ≤ G₀⁰.comap φ) : RatFunc R →*₀ G₀ where
  toFun f :=
    RatFunc.liftOn f (fun p q => φ p / φ q) fun {p q p' q'} hq hq' h => by
      cases subsingleton_or_nontrivial R
      -- ⊢ (fun p q => ↑φ p / ↑φ q) p q = (fun p q => ↑φ p / ↑φ q) p' q'
      · rw [Subsingleton.elim p q, Subsingleton.elim p' q, Subsingleton.elim q' q]
        -- 🎉 no goals
      rw [div_eq_div_iff, ← map_mul, mul_comm p, h, map_mul, mul_comm] <;>
      -- ⊢ ↑φ q ≠ 0
        exact nonZeroDivisors.ne_zero (hφ ‹_›)
        -- 🎉 no goals
        -- 🎉 no goals
  map_one' := by
    dsimp only -- porting note: force the function to be applied
    -- ⊢ RatFunc.liftOn 1 (fun p q => ↑φ p / ↑φ q) (_ : ∀ {p q p' q' : R[X]}, q ∈ R[X …
    rw [← ofFractionRing_one, ← Localization.mk_one, liftOn_ofFractionRing_mk]
    -- ⊢ ↑φ 1 / ↑φ ↑1 = 1
    simp only [map_one, Submonoid.coe_one, div_one]
    -- 🎉 no goals
  map_mul' x y := by
    cases' x with x
    -- ⊢ ZeroHom.toFun { toFun := fun f => RatFunc.liftOn f (fun p q => ↑φ p / ↑φ q)  …
    cases' y with y
    -- ⊢ ZeroHom.toFun { toFun := fun f => RatFunc.liftOn f (fun p q => ↑φ p / ↑φ q)  …
    induction' x using Localization.rec with p q
    -- ⊢ ZeroHom.toFun { toFun := fun f => RatFunc.liftOn f (fun p q => ↑φ p / ↑φ q)  …
    induction' y using Localization.rec with p' q'
    -- ⊢ RatFunc.liftOn 0 (fun p q => ↑φ p / ↑φ q) (_ : ∀ {p q p' q' : R[X]}, q ∈ R[X …
    · rw [← ofFractionRing_mul, Localization.mk_mul]
    -- ⊢ ↑φ 0 / ↑φ ↑1 = 0
      -- ⊢ ZeroHom.toFun { toFun := fun f => RatFunc.liftOn f (fun p q => ↑φ p / ↑φ q)  …
    -- 🎉 no goals
      simp only [liftOn_ofFractionRing_mk, div_mul_div_comm, map_mul, Submonoid.coe_mul]
      -- 🎉 no goals
    · rfl
      -- 🎉 no goals
    · rfl
      -- 🎉 no goals
  map_zero' := by
    dsimp only -- porting note: force the function to be applied
    rw [← ofFractionRing_zero, ← Localization.mk_zero (1 : R[X]⁰), liftOn_ofFractionRing_mk]
    simp only [map_zero, zero_div]
#align ratfunc.lift_monoid_with_zero_hom RatFunc.liftMonoidWithZeroHom

theorem liftMonoidWithZeroHom_apply_ofFractionRing_mk (φ : R[X] →*₀ G₀) (hφ : R[X]⁰ ≤ G₀⁰.comap φ)
    (n : R[X]) (d : R[X]⁰) :
    liftMonoidWithZeroHom φ hφ (ofFractionRing (Localization.mk n d)) = φ n / φ d :=
  liftOn_ofFractionRing_mk _ _ _ _
#align ratfunc.lift_monoid_with_zero_hom_apply_of_fraction_ring_mk RatFunc.liftMonoidWithZeroHom_apply_ofFractionRing_mk

theorem liftMonoidWithZeroHom_injective [Nontrivial R] (φ : R[X] →*₀ G₀) (hφ : Function.Injective φ)
    (hφ' : R[X]⁰ ≤ G₀⁰.comap φ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hφ) :
    Function.Injective (liftMonoidWithZeroHom φ hφ') := by
  rintro ⟨x⟩ ⟨y⟩
  -- ⊢ ↑(liftMonoidWithZeroHom φ hφ') { toFractionRing := x } = ↑(liftMonoidWithZer …
  induction' x using Localization.induction_on with a
  -- ⊢ ↑(liftMonoidWithZeroHom φ hφ') { toFractionRing := Localization.mk a.fst a.s …
  induction' y using Localization.induction_on with a'
  -- ⊢ ↑(liftMonoidWithZeroHom φ hφ') { toFractionRing := Localization.mk a.fst a.s …
  · simp_rw [liftMonoidWithZeroHom_apply_ofFractionRing_mk]
    -- ⊢ ↑φ a.fst / ↑φ ↑a.snd = ↑φ a'.fst / ↑φ ↑a'.snd → { toFractionRing := Localiza …
    intro h
    -- ⊢ { toFractionRing := Localization.mk a.fst a.snd } = { toFractionRing := Loca …
    congr 1
    -- ⊢ Localization.mk a.fst a.snd = Localization.mk a'.fst a'.snd
    refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (M := R[X]) ?_)
    -- ⊢ ↑(a'.fst, a'.snd).snd * (a.fst, a.snd).fst = ↑(a.fst, a.snd).snd * (a'.fst,  …
    have := mul_eq_mul_of_div_eq_div _ _ ?_ ?_ h
    rwa [← map_mul, ← map_mul, hφ.eq_iff, mul_comm, mul_comm a'.fst] at this
    -- ⊢ ↑φ ↑a.snd ≠ 0
    all_goals exact map_ne_zero_of_mem_nonZeroDivisors _ hφ (SetLike.coe_mem _)
    -- 🎉 no goals
#align ratfunc.lift_monoid_with_zero_hom_injective RatFunc.liftMonoidWithZeroHom_injective

/-- Lift an injective ring homomorphism `R[X] →+* L` to a `RatFunc R →+* L`
by mapping both the numerator and denominator and quotienting them. -/
def liftRingHom (φ : R[X] →+* L) (hφ : R[X]⁰ ≤ L⁰.comap φ) : RatFunc R →+* L :=
  { liftMonoidWithZeroHom φ.toMonoidWithZeroHom hφ with
    map_add' := fun x y => by
      -- porting note: used to invoke `MonoidWithZeroHom.toFun_eq_coe`
      simp only [ZeroHom.toFun_eq_coe, MonoidWithZeroHom.toZeroHom_coe]
      -- ⊢ ↑(liftMonoidWithZeroHom (RingHom.toMonoidWithZeroHom φ) hφ) (x + y) = ↑(lift …
      cases subsingleton_or_nontrivial R
      -- ⊢ ↑(liftMonoidWithZeroHom (RingHom.toMonoidWithZeroHom φ) hφ) (x + y) = ↑(lift …
      · rw [Subsingleton.elim (x + y) y, Subsingleton.elim x 0, map_zero, zero_add]
        -- 🎉 no goals
      cases' x with x
      -- ⊢ ↑(liftMonoidWithZeroHom (RingHom.toMonoidWithZeroHom φ) hφ) ({ toFractionRin …
      cases' y with y
      -- ⊢ ↑(liftMonoidWithZeroHom (RingHom.toMonoidWithZeroHom φ) hφ) ({ toFractionRin …
      -- Porting note: had to add the recursor explicitly below
      induction' x using Localization.rec with p q
      -- ⊢ ↑(liftMonoidWithZeroHom (RingHom.toMonoidWithZeroHom φ) hφ) ({ toFractionRin …
      induction' y using Localization.rec with p' q'
      · rw [← ofFractionRing_add, Localization.add_mk]
        -- ⊢ ↑(liftMonoidWithZeroHom (RingHom.toMonoidWithZeroHom φ) hφ) { toFractionRing …
        simp only [RingHom.toMonoidWithZeroHom_eq_coe,
          liftMonoidWithZeroHom_apply_ofFractionRing_mk]
        rw [div_add_div, div_eq_div_iff]
        · rw [mul_comm _ p, mul_comm _ p', mul_comm _ (φ p'), add_comm]
          -- ⊢ ↑φ (p * ↑q' + p' * ↑q) * (↑φ ↑q * ↑φ ↑q') = (↑φ p * ↑φ ↑q' + ↑φ p' * ↑φ ↑q)  …
          simp only [map_add, map_mul, Submonoid.coe_mul]
          -- 🎉 no goals
        all_goals
          try simp only [← map_mul, ← Submonoid.coe_mul]
          exact nonZeroDivisors.ne_zero (hφ (SetLike.coe_mem _))
      · rfl
        -- 🎉 no goals
      · rfl }
        -- 🎉 no goals
#align ratfunc.lift_ring_hom RatFunc.liftRingHom

theorem liftRingHom_apply_ofFractionRing_mk (φ : R[X] →+* L) (hφ : R[X]⁰ ≤ L⁰.comap φ) (n : R[X])
    (d : R[X]⁰) : liftRingHom φ hφ (ofFractionRing (Localization.mk n d)) = φ n / φ d :=
  liftMonoidWithZeroHom_apply_ofFractionRing_mk _ hφ _ _
#align ratfunc.lift_ring_hom_apply_of_fraction_ring_mk RatFunc.liftRingHom_apply_ofFractionRing_mk

theorem liftRingHom_injective [Nontrivial R] (φ : R[X] →+* L) (hφ : Function.Injective φ)
    (hφ' : R[X]⁰ ≤ L⁰.comap φ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hφ) :
    Function.Injective (liftRingHom φ hφ') :=
  liftMonoidWithZeroHom_injective _ hφ
#align ratfunc.lift_ring_hom_injective RatFunc.liftRingHom_injective

end LiftHom

variable (K)

instance [IsDomain K] : Field (RatFunc K) :=
  { RatFunc.instCommRing K, RatFunc.instNontrivial K with
    inv := Inv.inv
    -- porting note: used to be `by frac_tac`
    inv_zero := by rw [← ofFractionRing_zero, ← ofFractionRing_inv, inv_zero]
                   -- 🎉 no goals
    div := (· / ·)
                         -- 🎉 no goals
    div_eq_mul_inv := by frac_tac
    mul_inv_cancel := fun _ => mul_inv_cancel
    zpow := zpowRec }

section IsFractionRing

/-! ### `RatFunc` as field of fractions of `Polynomial` -/

section IsDomain

variable [IsDomain K]

instance (R : Type*) [CommSemiring R] [Algebra R K[X]] : Algebra R (RatFunc K) where
  toFun x := RatFunc.mk (algebraMap _ _ x) 1
  map_add' x y := by simp only [mk_one', RingHom.map_add, ofFractionRing_add]
                     -- 🎉 no goals
                     -- 🎉 no goals
                 -- 🎉 no goals
  map_mul' x y := by simp only [mk_one', RingHom.map_mul, ofFractionRing_mul]
  map_one' := by simp only [mk_one', RingHom.map_one, ofFractionRing_one]
                  -- 🎉 no goals
  map_zero' := by simp only [mk_one', RingHom.map_zero, ofFractionRing_zero]
  smul := (· • ·)
  smul_def' c x := by
    induction' x using RatFunc.induction_on' with p q hq
    -- ⊢ c • RatFunc.mk p q = ↑{ toMonoidHom := { toOneHom := { toFun := fun x => Rat …
      -- porting note: the first `rw [...]` was not needed
    · rw [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
      -- ⊢ c • RatFunc.mk p q = RatFunc.mk (↑(algebraMap R K[X]) c) 1 * RatFunc.mk p q
      rw [mk_one', ← mk_smul, mk_def_of_ne (c • p) hq, mk_def_of_ne p hq, ←
        ofFractionRing_mul, IsLocalization.mul_mk'_eq_mk'_of_mul, Algebra.smul_def]
  commutes' c x := mul_comm _ _

variable {K}

theorem mk_one (x : K[X]) : RatFunc.mk x 1 = algebraMap _ _ x :=
  rfl
#align ratfunc.mk_one RatFunc.mk_one

theorem ofFractionRing_algebraMap (x : K[X]) :
    ofFractionRing (algebraMap _ (FractionRing K[X]) x) = algebraMap _ _ x := by
  rw [← mk_one, mk_one']
  -- 🎉 no goals
#align ratfunc.of_fraction_ring_algebra_map RatFunc.ofFractionRing_algebraMap

@[simp]
theorem mk_eq_div (p q : K[X]) : RatFunc.mk p q = algebraMap _ _ p / algebraMap _ _ q := by
  simp only [mk_eq_div', ofFractionRing_div, ofFractionRing_algebraMap]
  -- 🎉 no goals
#align ratfunc.mk_eq_div RatFunc.mk_eq_div

@[simp]
theorem div_smul {R} [Monoid R] [DistribMulAction R K[X]] [IsScalarTower R K[X] K[X]] (c : R)
    (p q : K[X]) :
    algebraMap _ (RatFunc K) (c • p) / algebraMap _ _ q =
      c • (algebraMap _ _ p / algebraMap _ _ q) :=
  by rw [← mk_eq_div, mk_smul, mk_eq_div]
     -- 🎉 no goals
#align ratfunc.div_smul RatFunc.div_smul

theorem algebraMap_apply {R : Type*} [CommSemiring R] [Algebra R K[X]] (x : R) :
    algebraMap R (RatFunc K) x = algebraMap _ _ (algebraMap R K[X] x) / algebraMap K[X] _ 1 := by
  rw [← mk_eq_div]
  -- ⊢ ↑(algebraMap R (RatFunc K)) x = RatFunc.mk (↑(algebraMap R K[X]) x) 1
  rfl
  -- 🎉 no goals
#align ratfunc.algebra_map_apply RatFunc.algebraMap_apply

theorem map_apply_div_ne_zero {R F : Type*} [CommRing R] [IsDomain R] [MonoidHomClass F K[X] R[X]]
    (φ : F) (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) (p q : K[X]) (hq : q ≠ 0) :
    map φ hφ (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap _ _ (φ p) / algebraMap _ _ (φ q) := by
  have hq' : φ q ≠ 0 := nonZeroDivisors.ne_zero (hφ (mem_nonZeroDivisors_iff_ne_zero.mpr hq))
  -- ⊢ ↑(map φ hφ) (↑(algebraMap K[X] (RatFunc K)) p / ↑(algebraMap K[X] (RatFunc K …
  simp only [← mk_eq_div, mk_eq_localization_mk _ hq, map_apply_ofFractionRing_mk,
    mk_eq_localization_mk _ hq']
#align ratfunc.map_apply_div_ne_zero RatFunc.map_apply_div_ne_zero

@[simp]
theorem map_apply_div {R F : Type*} [CommRing R] [IsDomain R] [MonoidWithZeroHomClass F K[X] R[X]]
    (φ : F) (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) (p q : K[X]) :
    map φ hφ (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap _ _ (φ p) / algebraMap _ _ (φ q) := by
  rcases eq_or_ne q 0 with (rfl | hq)
  -- ⊢ ↑(map φ hφ) (↑(algebraMap K[X] (RatFunc K)) p / ↑(algebraMap K[X] (RatFunc K …
  · have : (0 : RatFunc K) = algebraMap K[X] _ 0 / algebraMap K[X] _ 1 := by simp
    -- ⊢ ↑(map φ hφ) (↑(algebraMap K[X] (RatFunc K)) p / ↑(algebraMap K[X] (RatFunc K …
    rw [map_zero, map_zero, map_zero, div_zero, div_zero, this, map_apply_div_ne_zero, map_one,
      map_one, div_one, map_zero, map_zero]
    simp only [map_zero, map_one, div_one]  -- porting note: this `simp` was not needed
    -- ⊢ 1 ≠ 0
    exact one_ne_zero
    -- 🎉 no goals
  exact map_apply_div_ne_zero _ _ _ _ hq
  -- 🎉 no goals
#align ratfunc.map_apply_div RatFunc.map_apply_div

theorem liftMonoidWithZeroHom_apply_div {L : Type*} [CommGroupWithZero L]
    (φ : MonoidWithZeroHom K[X] L) (hφ : K[X]⁰ ≤ L⁰.comap φ) (p q : K[X]) :
    liftMonoidWithZeroHom φ hφ (algebraMap _ _ p / algebraMap _ _ q) = φ p / φ q := by
  rcases eq_or_ne q 0 with (rfl | hq)
  -- ⊢ ↑(liftMonoidWithZeroHom φ hφ) (↑(algebraMap K[X] (RatFunc K)) p / ↑(algebraM …
  · simp only [div_zero, map_zero]
    -- 🎉 no goals
  simp only [← mk_eq_div, mk_eq_localization_mk _ hq,
    liftMonoidWithZeroHom_apply_ofFractionRing_mk]
#align ratfunc.lift_monoid_with_zero_hom_apply_div RatFunc.liftMonoidWithZeroHom_apply_div

-- Porting note: added `simpNF` form of `liftMonoidWithZeroHom_apply_div`
@[simp]
theorem liftMonoidWithZeroHom_apply_div' {L : Type*} [CommGroupWithZero L]
    (φ : MonoidWithZeroHom K[X] L) (hφ : K[X]⁰ ≤ L⁰.comap φ) (p q : K[X]) :
    liftMonoidWithZeroHom φ hφ (algebraMap _ _ p) / liftMonoidWithZeroHom φ hφ (algebraMap _ _ q) =
      φ p / φ q :=
  by rw [← map_div₀, liftMonoidWithZeroHom_apply_div]
     -- 🎉 no goals

theorem liftRingHom_apply_div {L : Type*} [Field L] (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ)
    (p q : K[X]) : liftRingHom φ hφ (algebraMap _ _ p / algebraMap _ _ q) = φ p / φ q :=
  liftMonoidWithZeroHom_apply_div _ hφ _ _  -- porting note: gave explicitly the `hφ`
#align ratfunc.lift_ring_hom_apply_div RatFunc.liftRingHom_apply_div

-- Porting note: added `simpNF` form of `liftRingHom_apply_div`
@[simp]
theorem liftRingHom_apply_div' {L : Type*} [Field L] (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ)
    (p q : K[X]) : liftRingHom φ hφ (algebraMap _ _ p) / liftRingHom φ hφ (algebraMap _ _ q) =
      φ p / φ q :=
  liftMonoidWithZeroHom_apply_div' _ hφ _ _  -- porting note: gave explicitly the `hφ`

variable (K)

theorem ofFractionRing_comp_algebraMap :
    ofFractionRing ∘ algebraMap K[X] (FractionRing K[X]) = algebraMap _ _ :=
  funext ofFractionRing_algebraMap
#align ratfunc.of_fraction_ring_comp_algebra_map RatFunc.ofFractionRing_comp_algebraMap

theorem algebraMap_injective : Function.Injective (algebraMap K[X] (RatFunc K)) := by
  rw [← ofFractionRing_comp_algebraMap]
  -- ⊢ Function.Injective (ofFractionRing ∘ ↑(algebraMap K[X] (FractionRing K[X])))
  exact ofFractionRing_injective.comp (IsFractionRing.injective _ _)
  -- 🎉 no goals
#align ratfunc.algebra_map_injective RatFunc.algebraMap_injective

@[simp]
theorem algebraMap_eq_zero_iff {x : K[X]} : algebraMap K[X] (RatFunc K) x = 0 ↔ x = 0 :=
  ⟨(injective_iff_map_eq_zero _).mp (algebraMap_injective K) _, fun hx => by
    rw [hx, RingHom.map_zero]⟩
    -- 🎉 no goals
#align ratfunc.algebra_map_eq_zero_iff RatFunc.algebraMap_eq_zero_iff

variable {K}

theorem algebraMap_ne_zero {x : K[X]} (hx : x ≠ 0) : algebraMap K[X] (RatFunc K) x ≠ 0 :=
  mt (algebraMap_eq_zero_iff K).mp hx
#align ratfunc.algebra_map_ne_zero RatFunc.algebraMap_ne_zero

section LiftAlgHom

variable {L R S : Type*} [Field L] [CommRing R] [IsDomain R] [CommSemiring S] [Algebra S K[X]]
  [Algebra S L] [Algebra S R[X]] (φ : K[X] →ₐ[S] L) (hφ : K[X]⁰ ≤ L⁰.comap φ)

/-- Lift an algebra homomorphism that maps polynomials `φ : K[X] →ₐ[S] R[X]`
to a `RatFunc K →ₐ[S] RatFunc R`,
on the condition that `φ` maps non zero divisors to non zero divisors,
by mapping both the numerator and denominator and quotienting them. -/
def mapAlgHom (φ : K[X] →ₐ[S] R[X]) (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) : RatFunc K →ₐ[S] RatFunc R :=
  { mapRingHom φ hφ with
    commutes' := fun r => by
      simp_rw [RingHom.toFun_eq_coe, coe_mapRingHom_eq_coe_map, algebraMap_apply r, map_apply_div,
        map_one, AlgHom.commutes] }
#align ratfunc.map_alg_hom RatFunc.mapAlgHom

theorem coe_mapAlgHom_eq_coe_map (φ : K[X] →ₐ[S] R[X]) (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) :
    (mapAlgHom φ hφ : RatFunc K → RatFunc R) = map φ hφ :=
  rfl
#align ratfunc.coe_map_alg_hom_eq_coe_map RatFunc.coe_mapAlgHom_eq_coe_map

/-- Lift an injective algebra homomorphism `K[X] →ₐ[S] L` to a `RatFunc K →ₐ[S] L`
by mapping both the numerator and denominator and quotienting them. -/
def liftAlgHom : RatFunc K →ₐ[S] L :=
  { liftRingHom φ.toRingHom hφ with
    commutes' := fun r => by
      simp_rw [RingHom.toFun_eq_coe, AlgHom.toRingHom_eq_coe, algebraMap_apply r,
        liftRingHom_apply_div, AlgHom.coe_toRingHom, map_one, div_one, AlgHom.commutes] }
#align ratfunc.lift_alg_hom RatFunc.liftAlgHom

theorem liftAlgHom_apply_ofFractionRing_mk (n : K[X]) (d : K[X]⁰) :
    liftAlgHom φ hφ (ofFractionRing (Localization.mk n d)) = φ n / φ d :=
  liftMonoidWithZeroHom_apply_ofFractionRing_mk _ hφ _ _ -- porting note: gave explicitly the `hφ`
#align ratfunc.lift_alg_hom_apply_of_fraction_ring_mk RatFunc.liftAlgHom_apply_ofFractionRing_mk

theorem liftAlgHom_injective (φ : K[X] →ₐ[S] L) (hφ : Function.Injective φ)
    (hφ' : K[X]⁰ ≤ L⁰.comap φ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hφ) :
    Function.Injective (liftAlgHom φ hφ') :=
  liftMonoidWithZeroHom_injective _ hφ
#align ratfunc.lift_alg_hom_injective RatFunc.liftAlgHom_injective

-- Porting note: added `simpNF` form of `liftAlgHom_apply_div`
@[simp]
theorem liftAlgHom_apply_div' (p q : K[X]) :
    liftAlgHom φ hφ (algebraMap _ _ p) / liftAlgHom φ hφ (algebraMap _ _ q) = φ p / φ q :=
  liftMonoidWithZeroHom_apply_div' _ hφ _ _  -- porting note: gave explicitly the `hφ`

theorem liftAlgHom_apply_div (p q : K[X]) :
    liftAlgHom φ hφ (algebraMap _ _ p / algebraMap _ _ q) = φ p / φ q :=
  liftMonoidWithZeroHom_apply_div _ hφ _ _  -- porting note: gave explicitly the `hφ`
#align ratfunc.lift_alg_hom_apply_div RatFunc.liftAlgHom_apply_div

end LiftAlgHom

variable (K)

/-- `RatFunc K` is the field of fractions of the polynomials over `K`. -/
instance : IsFractionRing K[X] (RatFunc K) where
  map_units' y := by
    rw [← ofFractionRing_algebraMap]
    -- ⊢ IsUnit { toFractionRing := ↑(algebraMap K[X] (FractionRing K[X])) ↑y }
    exact (toFractionRingRingEquiv K).symm.toRingHom.isUnit_map (IsLocalization.map_units _ y)
    -- 🎉 no goals
  eq_iff_exists' {x y} := by
    rw [← ofFractionRing_algebraMap, ← ofFractionRing_algebraMap]
    -- ⊢ { toFractionRing := ↑(algebraMap K[X] (FractionRing K[X])) x } = { toFractio …
    exact (toFractionRingRingEquiv K).symm.injective.eq_iff.trans
      (IsLocalization.eq_iff_exists _ _)
  surj' := by
    -- ⊢ ∃ x, { toFractionRing := z } * ↑(algebraMap K[X] (RatFunc K)) ↑x.snd = ↑(alg …
    rintro ⟨z⟩
    -- ⊢ { toFractionRing := z } * ↑(algebraMap K[X] (RatFunc K)) ↑x✝.snd = ↑(algebra …
    convert IsLocalization.surj K[X]⁰ z
    -- porting note: `ext ⟨x, y⟩` no longer necessary
    -- ⊢ { toFractionRing := z * ↑(algebraMap K[X] (FractionRing K[X])) ↑x✝.snd } = { …
    simp only [← ofFractionRing_algebraMap, Function.comp_apply, ← ofFractionRing_mul]
    -- 🎉 no goals
    rw [ofFractionRing.injEq]  -- porting note: added

variable {K}

@[simp]
theorem liftOn_div {P : Sort v} (p q : K[X]) (f : ∀ _p _q : K[X], P) (f0 : ∀ p, f p 0 = f 0 1)
    (H' : ∀ {p q p' q'} (_hq : q ≠ 0) (_hq' : q' ≠ 0), q' * p = q * p' → f p q = f p' q')
    (H : ∀ {p q p' q'} (_hq : q ∈ K[X]⁰) (_hq' : q' ∈ K[X]⁰), q' * p = q * p' → f p q = f p' q' :=
      fun {p q p' q'} hq hq' h => H' (nonZeroDivisors.ne_zero hq) (nonZeroDivisors.ne_zero hq') h) :
    (RatFunc.liftOn (algebraMap _ (RatFunc K) p / algebraMap _ _ q)) f @H = f p q := by
  rw [← mk_eq_div, liftOn_mk _ _ f f0 @H']
  -- 🎉 no goals
#align ratfunc.lift_on_div RatFunc.liftOn_div

@[simp]
theorem liftOn'_div {P : Sort v} (p q : K[X]) (f : ∀ _p _q : K[X], P) (f0 : ∀ p, f p 0 = f 0 1)
    (H) :
    (RatFunc.liftOn' (algebraMap _ (RatFunc K) p / algebraMap _ _ q)) f @H = f p q := by
  rw [RatFunc.liftOn', liftOn_div _ _ _ f0]
  -- ⊢ ∀ {p q p' q' : K[X]}, q ≠ 0 → q' ≠ 0 → q' * p = q * p' → f p q = f p' q'
  apply lift_on_condition_of_lift_on'_condition H -- porting note: `exact` did not work.  Also,
  -- 🎉 no goals
                                                  -- was `@H` that still works, but is not needed.
#align ratfunc.lift_on'_div RatFunc.liftOn'_div

/-- Induction principle for `RatFunc K`: if `f p q : P (p / q)` for all `p q : K[X]`,
then `P` holds on all elements of `RatFunc K`.

See also `induction_on'`, which is a recursion principle defined in terms of `RatFunc.mk`.
-/
protected theorem induction_on {P : RatFunc K → Prop} (x : RatFunc K)
    (f : ∀ (p q : K[X]) (hq : q ≠ 0), P (algebraMap _ (RatFunc K) p / algebraMap _ _ q)) : P x :=
  x.induction_on' fun p q hq => by simpa using f p q hq
                                   -- 🎉 no goals
#align ratfunc.induction_on RatFunc.induction_on

theorem ofFractionRing_mk' (x : K[X]) (y : K[X]⁰) :
    -- porting note: I gave explicitly the argument `(FractionRing K[X])`
    ofFractionRing (IsLocalization.mk' (FractionRing K[X]) x y) =
      IsLocalization.mk' (RatFunc K) x y := by
  rw [IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div, ← mk_eq_div', ← mk_eq_div]
  -- 🎉 no goals
#align ratfunc.of_fraction_ring_mk' RatFunc.ofFractionRing_mk'

@[simp]
theorem ofFractionRing_eq :
    (ofFractionRing : FractionRing K[X] → RatFunc K) = IsLocalization.algEquiv K[X]⁰ _ _ :=
  funext fun x =>
    Localization.induction_on x fun x => by
      simp only [IsLocalization.algEquiv_apply, IsLocalization.ringEquivOfRingEquiv_apply,
        Localization.mk_eq_mk'_apply, IsLocalization.map_mk', ofFractionRing_mk',
        RingEquiv.coe_toRingHom, RingEquiv.refl_apply, SetLike.eta]
      -- porting note: added following `simp`.  The previous one can be squeezed.
      simp only [IsFractionRing.mk'_eq_div, RingHom.id_apply, Subtype.coe_eta]
      -- 🎉 no goals

#align ratfunc.of_fraction_ring_eq RatFunc.ofFractionRing_eq

@[simp]
theorem toFractionRing_eq :
    (toFractionRing : RatFunc K → FractionRing K[X]) = IsLocalization.algEquiv K[X]⁰ _ _ :=
  funext fun ⟨x⟩ =>
    Localization.induction_on x fun x => by
      simp only [Localization.mk_eq_mk'_apply, ofFractionRing_mk', IsLocalization.algEquiv_apply,
        IsLocalization.ringEquivOfRingEquiv_apply, IsLocalization.map_mk',
        RingEquiv.coe_toRingHom, RingEquiv.refl_apply, SetLike.eta]
      -- porting note: added following `simp`.  The previous one can be squeezed.
      simp only [IsFractionRing.mk'_eq_div, RingHom.id_apply, Subtype.coe_eta]
      -- 🎉 no goals
#align ratfunc.to_fraction_ring_eq RatFunc.toFractionRing_eq

@[simp]
theorem toFractionRingRingEquiv_symm_eq :
    (toFractionRingRingEquiv K).symm = (IsLocalization.algEquiv K[X]⁰ _ _).toRingEquiv := by
  ext x
  -- ⊢ ↑(RingEquiv.symm (toFractionRingRingEquiv K)) x = ↑(AlgEquiv.toRingEquiv (Is …
  simp [toFractionRingRingEquiv, ofFractionRing_eq, AlgEquiv.coe_ringEquiv']
  -- 🎉 no goals
#align ratfunc.to_fraction_ring_ring_equiv_symm_eq RatFunc.toFractionRingRingEquiv_symm_eq

end IsDomain

end IsFractionRing

end CommRing

variable {K}

section NumDenom

/-! ### Numerator and denominator -/

open GCDMonoid Polynomial

variable [Field K]

/-- `RatFunc.numDenom` are numerator and denominator of a rational function over a field,
normalized such that the denominator is monic. -/
def numDenom (x : RatFunc K) : K[X] × K[X] :=
  x.liftOn'
    (fun p q =>
      if q = 0 then ⟨0, 1⟩
      else
        let r := gcd p q
        ⟨Polynomial.C (q / r).leadingCoeff⁻¹ * (p / r),
          Polynomial.C (q / r).leadingCoeff⁻¹ * (q / r)⟩)
  (by
      intros p q a hq ha
      -- ⊢ (fun p q =>
      dsimp
      -- ⊢ (if a * q = 0 then (0, 1) else (↑C (leadingCoeff (a * q / gcd (a * p) (a * q …
      rw [if_neg hq, if_neg (mul_ne_zero ha hq)]
      -- ⊢ (↑C (leadingCoeff (a * q / gcd (a * p) (a * q)))⁻¹ * (a * p / gcd (a * p) (a …
      have ha' : a.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr ha
      -- ⊢ (↑C (leadingCoeff (a * q / gcd (a * p) (a * q)))⁻¹ * (a * p / gcd (a * p) (a …
      have hainv : a.leadingCoeff⁻¹ ≠ 0 := inv_ne_zero ha'
      -- ⊢ (↑C (leadingCoeff (a * q / gcd (a * p) (a * q)))⁻¹ * (a * p / gcd (a * p) (a …
      simp only [Prod.ext_iff, gcd_mul_left, normalize_apply, Polynomial.coe_normUnit, mul_assoc,
        CommGroupWithZero.coe_normUnit _ ha']
      have hdeg : (gcd p q).degree ≤ q.degree := degree_gcd_le_right _ hq
      -- ⊢ ↑C (leadingCoeff (a * q / (↑normalize a * gcd p q)))⁻¹ * (a * p / (↑normaliz …
      have hdeg' : (Polynomial.C a.leadingCoeff⁻¹ * gcd p q).degree ≤ q.degree := by
        rw [Polynomial.degree_mul, Polynomial.degree_C hainv, zero_add]
        exact hdeg
      have hdivp : Polynomial.C a.leadingCoeff⁻¹ * gcd p q ∣ p :=
        (C_mul_dvd hainv).mpr (gcd_dvd_left p q)
      have hdivq : Polynomial.C a.leadingCoeff⁻¹ * gcd p q ∣ q :=
        (C_mul_dvd hainv).mpr (gcd_dvd_right p q)
      -- porting note: added `simp only [...]` and `rw [mul_assoc]`
      -- porting note: note the unfolding of `normalize` and `normUnit`!
      simp only [normalize, normUnit, coe_normUnit, leadingCoeff_eq_zero, MonoidWithZeroHom.coe_mk,
        ZeroHom.coe_mk, ha, dite_false, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [mul_assoc]
      -- ⊢ ↑C (leadingCoeff (a * q / (a * (↑C (leadingCoeff a)⁻¹ * gcd p q))))⁻¹ * (a * …
      rw [EuclideanDomain.mul_div_mul_cancel ha hdivp, EuclideanDomain.mul_div_mul_cancel ha hdivq,
        leadingCoeff_div hdeg, leadingCoeff_div hdeg', Polynomial.leadingCoeff_mul,
        Polynomial.leadingCoeff_C, div_C_mul, div_C_mul, ← mul_assoc, ← Polynomial.C_mul, ←
        mul_assoc, ← Polynomial.C_mul]
      constructor <;> congr <;>
      -- ⊢ ↑C ((leadingCoeff q / ((leadingCoeff a)⁻¹ * leadingCoeff (gcd p q)))⁻¹ * (le …
                      -- ⊢ (leadingCoeff q / ((leadingCoeff a)⁻¹ * leadingCoeff (gcd p q)))⁻¹ * (leadin …
                      -- ⊢ (leadingCoeff q / ((leadingCoeff a)⁻¹ * leadingCoeff (gcd p q)))⁻¹ * (leadin …
        rw [inv_div, mul_comm, mul_div_assoc, ← mul_assoc, inv_inv, _root_.mul_inv_cancel ha',
          one_mul, inv_div])
#align ratfunc.num_denom RatFunc.numDenom

@[simp]
theorem numDenom_div (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    numDenom (algebraMap _ _ p / algebraMap _ _ q) =
      (Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q),
        Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (q / gcd p q)) := by
  rw [numDenom, liftOn'_div, if_neg hq]
  -- ⊢ ∀ (p : K[X]),
  intro p
  -- ⊢ (if 0 = 0 then (0, 1)
  rw [if_pos rfl, if_neg (one_ne_zero' K[X])]
  -- ⊢ (0, 1) =
  simp
  -- 🎉 no goals
#align ratfunc.num_denom_div RatFunc.numDenom_div

/-- `RatFunc.num` is the numerator of a rational function,
normalized such that the denominator is monic. -/
def num (x : RatFunc K) : K[X] :=
  x.numDenom.1
#align ratfunc.num RatFunc.num

private theorem num_div' (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    num (algebraMap _ _ p / algebraMap _ _ q) =
      Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q) := by
  rw [num, numDenom_div _ hq]
  -- 🎉 no goals

@[simp]
theorem num_zero : num (0 : RatFunc K) = 0 := by convert num_div' (0 : K[X]) one_ne_zero <;> simp
                                                 -- ⊢ 0 = ↑(algebraMap K[X] (RatFunc K)) 0 / ↑(algebraMap K[X] (RatFunc K)) 1
                                                                                             -- 🎉 no goals
                                                                                             -- 🎉 no goals
#align ratfunc.num_zero RatFunc.num_zero

@[simp]
theorem num_div (p q : K[X]) :
    num (algebraMap _ _ p / algebraMap _ _ q) =
      Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q) := by
  by_cases hq : q = 0
  -- ⊢ num (↑(algebraMap K[X] (RatFunc K)) p / ↑(algebraMap K[X] (RatFunc K)) q) =  …
  · simp [hq]
    -- 🎉 no goals
  · exact num_div' p hq
    -- 🎉 no goals
#align ratfunc.num_div RatFunc.num_div

@[simp]
theorem num_one : num (1 : RatFunc K) = 1 := by convert num_div (1 : K[X]) 1 <;> simp
                                                -- ⊢ 1 = ↑(algebraMap K[X] (RatFunc K)) 1 / ↑(algebraMap K[X] (RatFunc K)) 1
                                                                                 -- 🎉 no goals
                                                                                 -- 🎉 no goals
#align ratfunc.num_one RatFunc.num_one

@[simp]
theorem num_algebraMap (p : K[X]) : num (algebraMap _ _ p) = p := by convert num_div p 1 <;> simp
                                                                     -- ⊢ ↑(algebraMap K[X] (RatFunc K)) p = ↑(algebraMap K[X] (RatFunc K)) p / ↑(alge …
                                                                                             -- 🎉 no goals
                                                                                             -- 🎉 no goals
#align ratfunc.num_algebra_map RatFunc.num_algebraMap

theorem num_div_dvd (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    num (algebraMap _ _ p / algebraMap _ _ q) ∣ p := by
  rw [num_div _ q, C_mul_dvd]
  -- ⊢ p / gcd p q ∣ p
  · exact EuclideanDomain.div_dvd_of_dvd (gcd_dvd_left p q)
    -- 🎉 no goals
  · simpa only [Ne.def, inv_eq_zero, Polynomial.leadingCoeff_eq_zero] using right_div_gcd_ne_zero hq
    -- 🎉 no goals
#align ratfunc.num_div_dvd RatFunc.num_div_dvd

/-- A version of `num_div_dvd` with the LHS in simp normal form -/
@[simp]
theorem num_div_dvd' (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q) ∣ p := by simpa using num_div_dvd p hq
                                                             -- 🎉 no goals
#align ratfunc.num_div_dvd' RatFunc.num_div_dvd'

/-- `RatFunc.denom` is the denominator of a rational function,
normalized such that it is monic. -/
def denom (x : RatFunc K) : K[X] :=
  x.numDenom.2
#align ratfunc.denom RatFunc.denom

@[simp]
theorem denom_div (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    denom (algebraMap _ _ p / algebraMap _ _ q) =
      Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (q / gcd p q) :=
  by rw [denom, numDenom_div _ hq]
     -- 🎉 no goals
#align ratfunc.denom_div RatFunc.denom_div

theorem monic_denom (x : RatFunc K) : (denom x).Monic := by
  induction x using RatFunc.induction_on with
    | f p q hq =>
      rw [denom_div p hq, mul_comm]
      exact Polynomial.monic_mul_leadingCoeff_inv (right_div_gcd_ne_zero hq)
#align ratfunc.monic_denom RatFunc.monic_denom

theorem denom_ne_zero (x : RatFunc K) : denom x ≠ 0 :=
  (monic_denom x).ne_zero
#align ratfunc.denom_ne_zero RatFunc.denom_ne_zero

@[simp]
theorem denom_zero : denom (0 : RatFunc K) = 1 := by
  convert denom_div (0 : K[X]) one_ne_zero <;> simp
  -- ⊢ 0 = ↑(algebraMap K[X] (RatFunc K)) 0 / ↑(algebraMap K[X] (RatFunc K)) 1
                                               -- 🎉 no goals
                                               -- 🎉 no goals
#align ratfunc.denom_zero RatFunc.denom_zero

@[simp]
theorem denom_one : denom (1 : RatFunc K) = 1 := by
  convert denom_div (1 : K[X]) one_ne_zero <;> simp
  -- ⊢ 1 = ↑(algebraMap K[X] (RatFunc K)) 1 / ↑(algebraMap K[X] (RatFunc K)) 1
                                               -- 🎉 no goals
                                               -- 🎉 no goals
#align ratfunc.denom_one RatFunc.denom_one

@[simp]
theorem denom_algebraMap (p : K[X]) : denom (algebraMap _ (RatFunc K) p) = 1 := by
  convert denom_div p one_ne_zero <;> simp
  -- ⊢ ↑(algebraMap K[X] (RatFunc K)) p = ↑(algebraMap K[X] (RatFunc K)) p / ↑(alge …
                                      -- 🎉 no goals
                                      -- 🎉 no goals
#align ratfunc.denom_algebra_map RatFunc.denom_algebraMap

@[simp]
theorem denom_div_dvd (p q : K[X]) : denom (algebraMap _ _ p / algebraMap _ _ q) ∣ q := by
  by_cases hq : q = 0
  -- ⊢ denom (↑(algebraMap K[X] (RatFunc K)) p / ↑(algebraMap K[X] (RatFunc K)) q)  …
  · simp [hq]
    -- 🎉 no goals
  rw [denom_div _ hq, C_mul_dvd]
  -- ⊢ q / gcd p q ∣ q
  · exact EuclideanDomain.div_dvd_of_dvd (gcd_dvd_right p q)
    -- 🎉 no goals
  · simpa only [Ne.def, inv_eq_zero, Polynomial.leadingCoeff_eq_zero] using right_div_gcd_ne_zero hq
    -- 🎉 no goals
#align ratfunc.denom_div_dvd RatFunc.denom_div_dvd

@[simp]
theorem num_div_denom (x : RatFunc K) : algebraMap _ _ (num x) / algebraMap _ _ (denom x) = x := by
  induction' x using RatFunc.induction_on with p q hq
  -- ⊢ ↑(algebraMap K[X] (RatFunc K)) (num (↑(algebraMap K[X] (RatFunc K)) p / ↑(al …
  -- porting note: had to hint the type of this `have`
  have q_div_ne_zero : q / gcd p q ≠ 0 := right_div_gcd_ne_zero hq
  -- ⊢ ↑(algebraMap K[X] (RatFunc K)) (num (↑(algebraMap K[X] (RatFunc K)) p / ↑(al …
  dsimp only
  -- ⊢ ↑(algebraMap K[X] (RatFunc K)) (num (↑(algebraMap K[X] (RatFunc K)) p / ↑(al …
  rw [num_div p q, denom_div p hq, RingHom.map_mul, RingHom.map_mul, mul_div_mul_left,
    div_eq_div_iff, ← RingHom.map_mul, ← RingHom.map_mul, mul_comm _ q, ←
    EuclideanDomain.mul_div_assoc, ← EuclideanDomain.mul_div_assoc, mul_comm]
  · apply gcd_dvd_right
    -- 🎉 no goals
  · apply gcd_dvd_left
    -- 🎉 no goals
  · exact algebraMap_ne_zero q_div_ne_zero
    -- 🎉 no goals
  · exact algebraMap_ne_zero hq
    -- 🎉 no goals
  · refine' algebraMap_ne_zero (mt Polynomial.C_eq_zero.mp _)
    -- ⊢ ¬(leadingCoeff (q / gcd p q))⁻¹ = 0
    exact inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr q_div_ne_zero)
    -- 🎉 no goals
#align ratfunc.num_div_denom RatFunc.num_div_denom

theorem isCoprime_num_denom (x : RatFunc K) : IsCoprime x.num x.denom := by
  induction' x using RatFunc.induction_on with p q hq
  -- ⊢ IsCoprime (num (↑(algebraMap K[X] (RatFunc K)) p / ↑(algebraMap K[X] (RatFun …
  rw [num_div, denom_div _ hq]
  -- ⊢ IsCoprime (↑C (leadingCoeff (q / gcd p q))⁻¹ * (p / gcd p q)) (↑C (leadingCo …
  exact (isCoprime_mul_unit_left
    ((leadingCoeff_ne_zero.2 <| right_div_gcd_ne_zero hq).isUnit.inv.map C) _ _).2
      (isCoprime_div_gcd_div_gcd hq)
#align ratfunc.is_coprime_num_denom RatFunc.isCoprime_num_denom

@[simp]
theorem num_eq_zero_iff {x : RatFunc K} : num x = 0 ↔ x = 0 :=
  ⟨fun h => by rw [← num_div_denom x, h, RingHom.map_zero, zero_div], fun h => h.symm ▸ num_zero⟩
               -- 🎉 no goals
#align ratfunc.num_eq_zero_iff RatFunc.num_eq_zero_iff

theorem num_ne_zero {x : RatFunc K} (hx : x ≠ 0) : num x ≠ 0 :=
  mt num_eq_zero_iff.mp hx
#align ratfunc.num_ne_zero RatFunc.num_ne_zero

theorem num_mul_eq_mul_denom_iff {x : RatFunc K} {p q : K[X]} (hq : q ≠ 0) :
    x.num * q = p * x.denom ↔ x = algebraMap _ _ p / algebraMap _ _ q := by
  rw [← (algebraMap_injective K).eq_iff, eq_div_iff (algebraMap_ne_zero hq)]
  -- ⊢ ↑(algebraMap K[X] (RatFunc K)) (num x * q) = ↑(algebraMap K[X] (RatFunc K))  …
  conv_rhs => rw [← num_div_denom x]
  -- ⊢ ↑(algebraMap K[X] (RatFunc K)) (num x * q) = ↑(algebraMap K[X] (RatFunc K))  …
  rw [RingHom.map_mul, RingHom.map_mul, div_eq_mul_inv, mul_assoc, mul_comm (Inv.inv _), ←
    mul_assoc, ← div_eq_mul_inv, div_eq_iff]
  exact algebraMap_ne_zero (denom_ne_zero x)
  -- 🎉 no goals
#align ratfunc.num_mul_eq_mul_denom_iff RatFunc.num_mul_eq_mul_denom_iff

theorem num_denom_add (x y : RatFunc K) :
    (x + y).num * (x.denom * y.denom) = (x.num * y.denom + x.denom * y.num) * (x + y).denom :=
  (num_mul_eq_mul_denom_iff (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))).mpr <| by
    conv_lhs => rw [← num_div_denom x, ← num_div_denom y]
    -- ⊢ ↑(algebraMap K[X] (RatFunc K)) (num x) / ↑(algebraMap K[X] (RatFunc K)) (den …
    rw [div_add_div, RingHom.map_mul, RingHom.map_add, RingHom.map_mul, RingHom.map_mul]
    -- ⊢ ↑(algebraMap K[X] (RatFunc K)) (denom x) ≠ 0
    · exact algebraMap_ne_zero (denom_ne_zero x)
      -- 🎉 no goals
    · exact algebraMap_ne_zero (denom_ne_zero y)
      -- 🎉 no goals
#align ratfunc.num_denom_add RatFunc.num_denom_add

theorem num_denom_neg (x : RatFunc K) : (-x).num * x.denom = -x.num * (-x).denom := by
  rw [num_mul_eq_mul_denom_iff (denom_ne_zero x), _root_.map_neg, neg_div, num_div_denom]
  -- 🎉 no goals
#align ratfunc.num_denom_neg RatFunc.num_denom_neg

theorem num_denom_mul (x y : RatFunc K) :
    (x * y).num * (x.denom * y.denom) = x.num * y.num * (x * y).denom :=
  (num_mul_eq_mul_denom_iff (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))).mpr <| by
    conv_lhs =>
      rw [← num_div_denom x, ← num_div_denom y, div_mul_div_comm, ← RingHom.map_mul, ←
        RingHom.map_mul]
#align ratfunc.num_denom_mul RatFunc.num_denom_mul

theorem num_dvd {x : RatFunc K} {p : K[X]} (hp : p ≠ 0) :
    num x ∣ p ↔ ∃ (q : K[X]) (hq : q ≠ 0), x = algebraMap _ _ p / algebraMap _ _ q := by
  constructor
  -- ⊢ num x ∣ p → ∃ q hq, x = ↑(algebraMap K[X] (RatFunc K)) p / ↑(algebraMap K[X] …
  · rintro ⟨q, rfl⟩
    -- ⊢ ∃ q_1 hq, x = ↑(algebraMap K[X] (RatFunc K)) (num x * q) / ↑(algebraMap K[X] …
    obtain ⟨_hx, hq⟩ := mul_ne_zero_iff.mp hp
    -- ⊢ ∃ q_1 hq, x = ↑(algebraMap K[X] (RatFunc K)) (num x * q) / ↑(algebraMap K[X] …
    use denom x * q
    -- ⊢ ∃ hq, x = ↑(algebraMap K[X] (RatFunc K)) (num x * q) / ↑(algebraMap K[X] (Ra …
    rw [RingHom.map_mul, RingHom.map_mul, ← div_mul_div_comm, div_self, mul_one, num_div_denom]
    -- ⊢ ∃ hq, x = x
    · exact ⟨mul_ne_zero (denom_ne_zero x) hq, rfl⟩
      -- 🎉 no goals
    · exact algebraMap_ne_zero hq
      -- 🎉 no goals
  · rintro ⟨q, hq, rfl⟩
    -- ⊢ num (↑(algebraMap K[X] (RatFunc K)) p / ↑(algebraMap K[X] (RatFunc K)) q) ∣ p
    exact num_div_dvd p hq
    -- 🎉 no goals
#align ratfunc.num_dvd RatFunc.num_dvd

theorem denom_dvd {x : RatFunc K} {q : K[X]} (hq : q ≠ 0) :
    denom x ∣ q ↔ ∃ p : K[X], x = algebraMap _ _ p / algebraMap _ _ q := by
  constructor
  -- ⊢ denom x ∣ q → ∃ p, x = ↑(algebraMap K[X] (RatFunc K)) p / ↑(algebraMap K[X]  …
  · rintro ⟨p, rfl⟩
    -- ⊢ ∃ p_1, x = ↑(algebraMap K[X] (RatFunc K)) p_1 / ↑(algebraMap K[X] (RatFunc K …
    obtain ⟨_hx, hp⟩ := mul_ne_zero_iff.mp hq
    -- ⊢ ∃ p_1, x = ↑(algebraMap K[X] (RatFunc K)) p_1 / ↑(algebraMap K[X] (RatFunc K …
    use num x * p
    -- ⊢ x = ↑(algebraMap K[X] (RatFunc K)) (num x * p) / ↑(algebraMap K[X] (RatFunc  …
    rw [RingHom.map_mul, RingHom.map_mul, ← div_mul_div_comm, div_self, mul_one, num_div_denom]
    -- ⊢ ↑(algebraMap K[X] (RatFunc K)) p ≠ 0
    · exact algebraMap_ne_zero hp
      -- 🎉 no goals
  · rintro ⟨p, rfl⟩
    -- ⊢ denom (↑(algebraMap K[X] (RatFunc K)) p / ↑(algebraMap K[X] (RatFunc K)) q)  …
    exact denom_div_dvd p q
    -- 🎉 no goals
#align ratfunc.denom_dvd RatFunc.denom_dvd

theorem num_mul_dvd (x y : RatFunc K) : num (x * y) ∣ num x * num y := by
  by_cases hx : x = 0
  -- ⊢ num (x * y) ∣ num x * num y
  · simp [hx]
    -- 🎉 no goals
  by_cases hy : y = 0
  -- ⊢ num (x * y) ∣ num x * num y
  · simp [hy]
    -- 🎉 no goals
  rw [num_dvd (mul_ne_zero (num_ne_zero hx) (num_ne_zero hy))]
  -- ⊢ ∃ q hq, x * y = ↑(algebraMap K[X] (RatFunc K)) (num x * num y) / ↑(algebraMa …
  refine' ⟨x.denom * y.denom, mul_ne_zero (denom_ne_zero x) (denom_ne_zero y), _⟩
  -- ⊢ x * y = ↑(algebraMap K[X] (RatFunc K)) (num x * num y) / ↑(algebraMap K[X] ( …
  rw [RingHom.map_mul, RingHom.map_mul, ← div_mul_div_comm, num_div_denom, num_div_denom]
  -- 🎉 no goals
#align ratfunc.num_mul_dvd RatFunc.num_mul_dvd

theorem denom_mul_dvd (x y : RatFunc K) : denom (x * y) ∣ denom x * denom y := by
  rw [denom_dvd (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))]
  -- ⊢ ∃ p, x * y = ↑(algebraMap K[X] (RatFunc K)) p / ↑(algebraMap K[X] (RatFunc K …
  refine' ⟨x.num * y.num, _⟩
  -- ⊢ x * y = ↑(algebraMap K[X] (RatFunc K)) (num x * num y) / ↑(algebraMap K[X] ( …
  rw [RingHom.map_mul, RingHom.map_mul, ← div_mul_div_comm, num_div_denom, num_div_denom]
  -- 🎉 no goals
#align ratfunc.denom_mul_dvd RatFunc.denom_mul_dvd

theorem denom_add_dvd (x y : RatFunc K) : denom (x + y) ∣ denom x * denom y := by
  rw [denom_dvd (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))]
  -- ⊢ ∃ p, x + y = ↑(algebraMap K[X] (RatFunc K)) p / ↑(algebraMap K[X] (RatFunc K …
  refine' ⟨x.num * y.denom + x.denom * y.num, _⟩
  -- ⊢ x + y = ↑(algebraMap K[X] (RatFunc K)) (num x * denom y + denom x * num y) / …
  rw [RingHom.map_mul, RingHom.map_add, RingHom.map_mul, RingHom.map_mul, ← div_add_div,
    num_div_denom, num_div_denom]
  · exact algebraMap_ne_zero (denom_ne_zero x)
    -- 🎉 no goals
  · exact algebraMap_ne_zero (denom_ne_zero y)
    -- 🎉 no goals
#align ratfunc.denom_add_dvd RatFunc.denom_add_dvd

theorem map_denom_ne_zero {L F : Type*} [Zero L] [ZeroHomClass F K[X] L] (φ : F)
    (hφ : Function.Injective φ) (f : RatFunc K) : φ f.denom ≠ 0 := fun H =>
  (denom_ne_zero f) ((map_eq_zero_iff φ hφ).mp H)
#align ratfunc.map_denom_ne_zero RatFunc.map_denom_ne_zero

theorem map_apply {R F : Type*} [CommRing R] [IsDomain R] [MonoidHomClass F K[X] R[X]] (φ : F)
    (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) (f : RatFunc K) :
    map φ hφ f = algebraMap _ _ (φ f.num) / algebraMap _ _ (φ f.denom) := by
  rw [← num_div_denom f, map_apply_div_ne_zero, num_div_denom f]
  -- ⊢ denom f ≠ 0
  exact denom_ne_zero _
  -- 🎉 no goals
#align ratfunc.map_apply RatFunc.map_apply

theorem liftMonoidWithZeroHom_apply {L : Type*} [CommGroupWithZero L] (φ : K[X] →*₀ L)
    (hφ : K[X]⁰ ≤ L⁰.comap φ) (f : RatFunc K) :
    liftMonoidWithZeroHom φ hφ f = φ f.num / φ f.denom :=
  by rw [← num_div_denom f, liftMonoidWithZeroHom_apply_div, num_div_denom]
     -- 🎉 no goals
#align ratfunc.lift_monoid_with_zero_hom_apply RatFunc.liftMonoidWithZeroHom_apply

theorem liftRingHom_apply {L : Type*} [Field L] (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ)
    (f : RatFunc K) : liftRingHom φ hφ f = φ f.num / φ f.denom :=
  liftMonoidWithZeroHom_apply _ hφ _  -- porting note: added explicit `hφ`
#align ratfunc.lift_ring_hom_apply RatFunc.liftRingHom_apply

theorem liftAlgHom_apply {L S : Type*} [Field L] [CommSemiring S] [Algebra S K[X]] [Algebra S L]
    (φ : K[X] →ₐ[S] L) (hφ : K[X]⁰ ≤ L⁰.comap φ) (f : RatFunc K) :
    liftAlgHom φ hφ f = φ f.num / φ f.denom :=
  liftMonoidWithZeroHom_apply _ hφ _  -- porting note: added explicit `hφ`
#align ratfunc.lift_alg_hom_apply RatFunc.liftAlgHom_apply

theorem num_mul_denom_add_denom_mul_num_ne_zero {x y : RatFunc K} (hxy : x + y ≠ 0) :
    x.num * y.denom + x.denom * y.num ≠ 0 := by
  intro h_zero
  -- ⊢ False
  have h := num_denom_add x y
  -- ⊢ False
  rw [h_zero, zero_mul] at h
  -- ⊢ False
  exact (mul_ne_zero (num_ne_zero hxy) (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)) h
  -- 🎉 no goals
#align ratfunc.num_mul_denom_add_denom_mul_num_ne_zero RatFunc.num_mul_denom_add_denom_mul_num_ne_zero

end NumDenom

section Eval

/-! ### Polynomial structure: `C`, `X`, `eval` -/

section Domain

variable [CommRing K] [IsDomain K]

/-- `RatFunc.C a` is the constant rational function `a`. -/
def C : K →+* RatFunc K :=
  algebraMap _ _
set_option linter.uppercaseLean3 false in
#align ratfunc.C RatFunc.C

@[simp]
theorem algebraMap_eq_C : algebraMap K (RatFunc K) = C :=
  rfl
set_option linter.uppercaseLean3 false in
#align ratfunc.algebra_map_eq_C RatFunc.algebraMap_eq_C

@[simp]
theorem algebraMap_C (a : K) : algebraMap K[X] (RatFunc K) (Polynomial.C a) = C a :=
  rfl
set_option linter.uppercaseLean3 false in
#align ratfunc.algebra_map_C RatFunc.algebraMap_C

@[simp]
theorem algebraMap_comp_C : (algebraMap K[X] (RatFunc K)).comp Polynomial.C = C :=
  rfl
set_option linter.uppercaseLean3 false in
#align ratfunc.algebra_map_comp_C RatFunc.algebraMap_comp_C

theorem smul_eq_C_mul (r : K) (x : RatFunc K) : r • x = C r * x := by
  rw [Algebra.smul_def, algebraMap_eq_C]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align ratfunc.smul_eq_C_mul RatFunc.smul_eq_C_mul

/-- `RatFunc.X` is the polynomial variable (aka indeterminate). -/
def X : RatFunc K :=
  algebraMap K[X] (RatFunc K) Polynomial.X
set_option linter.uppercaseLean3 false in
#align ratfunc.X RatFunc.X

@[simp]
theorem algebraMap_X : algebraMap K[X] (RatFunc K) Polynomial.X = X :=
  rfl
set_option linter.uppercaseLean3 false in
#align ratfunc.algebra_map_X RatFunc.algebraMap_X

end Domain

section Field

variable [Field K]

@[simp]
theorem num_C (c : K) : num (C c) = Polynomial.C c :=
  num_algebraMap _
set_option linter.uppercaseLean3 false in
#align ratfunc.num_C RatFunc.num_C

@[simp]
theorem denom_C (c : K) : denom (C c) = 1 :=
  denom_algebraMap _
set_option linter.uppercaseLean3 false in
#align ratfunc.denom_C RatFunc.denom_C

@[simp]
theorem num_X : num (X : RatFunc K) = Polynomial.X :=
  num_algebraMap _
set_option linter.uppercaseLean3 false in
#align ratfunc.num_X RatFunc.num_X

@[simp]
theorem denom_X : denom (X : RatFunc K) = 1 :=
  denom_algebraMap _
set_option linter.uppercaseLean3 false in
#align ratfunc.denom_X RatFunc.denom_X

theorem X_ne_zero : (RatFunc.X : RatFunc K) ≠ 0 :=
  RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
set_option linter.uppercaseLean3 false in
#align ratfunc.X_ne_zero RatFunc.X_ne_zero

variable {L : Type*} [Field L]

/-- Evaluate a rational function `p` given a ring hom `f` from the scalar field
to the target and a value `x` for the variable in the target.

Fractions are reduced by clearing common denominators before evaluating:
`eval id 1 ((X^2 - 1) / (X - 1)) = eval id 1 (X + 1) = 2`, not `0 / 0 = 0`.
-/
def eval (f : K →+* L) (a : L) (p : RatFunc K) : L :=
  (num p).eval₂ f a / (denom p).eval₂ f a
#align ratfunc.eval RatFunc.eval

variable {f : K →+* L} {a : L}

theorem eval_eq_zero_of_eval₂_denom_eq_zero {x : RatFunc K}
    (h : Polynomial.eval₂ f a (denom x) = 0) : eval f a x = 0 := by rw [eval, h, div_zero]
                                                                    -- 🎉 no goals
#align ratfunc.eval_eq_zero_of_eval₂_denom_eq_zero RatFunc.eval_eq_zero_of_eval₂_denom_eq_zero

theorem eval₂_denom_ne_zero {x : RatFunc K} (h : eval f a x ≠ 0) :
    Polynomial.eval₂ f a (denom x) ≠ 0 :=
  mt eval_eq_zero_of_eval₂_denom_eq_zero h
#align ratfunc.eval₂_denom_ne_zero RatFunc.eval₂_denom_ne_zero

variable (f a)

@[simp]
theorem eval_C {c : K} : eval f a (C c) = f c := by simp [eval]
                                                    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align ratfunc.eval_C RatFunc.eval_C

@[simp]
theorem eval_X : eval f a X = a := by simp [eval]
                                      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align ratfunc.eval_X RatFunc.eval_X

@[simp]
theorem eval_zero : eval f a 0 = 0 := by simp [eval]
                                         -- 🎉 no goals
#align ratfunc.eval_zero RatFunc.eval_zero

@[simp]
theorem eval_one : eval f a 1 = 1 := by simp [eval]
                                        -- 🎉 no goals
#align ratfunc.eval_one RatFunc.eval_one

@[simp]
theorem eval_algebraMap {S : Type*} [CommSemiring S] [Algebra S K[X]] (p : S) :
    eval f a (algebraMap _ _ p) = (algebraMap _ K[X] p).eval₂ f a := by
  simp [eval, IsScalarTower.algebraMap_apply S K[X] (RatFunc K)]
  -- 🎉 no goals
#align ratfunc.eval_algebra_map RatFunc.eval_algebraMap

/-- `eval` is an additive homomorphism except when a denominator evaluates to `0`.

Counterexample: `eval _ 1 (X / (X-1)) + eval _ 1 (-1 / (X-1)) = 0`
`... ≠ 1 = eval _ 1 ((X-1) / (X-1))`.

See also `RatFunc.eval₂_denom_ne_zero` to make the hypotheses simpler but less general.
-/
theorem eval_add {x y : RatFunc K} (hx : Polynomial.eval₂ f a (denom x) ≠ 0)
    (hy : Polynomial.eval₂ f a (denom y) ≠ 0) : eval f a (x + y) = eval f a x + eval f a y := by
  unfold eval
  -- ⊢ Polynomial.eval₂ f a (num (x + y)) / Polynomial.eval₂ f a (denom (x + y)) =  …
  by_cases hxy : Polynomial.eval₂ f a (denom (x + y)) = 0
  -- ⊢ Polynomial.eval₂ f a (num (x + y)) / Polynomial.eval₂ f a (denom (x + y)) =  …
  · have := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f a (denom_add_dvd x y) hxy
    -- ⊢ Polynomial.eval₂ f a (num (x + y)) / Polynomial.eval₂ f a (denom (x + y)) =  …
    rw [Polynomial.eval₂_mul] at this
    -- ⊢ Polynomial.eval₂ f a (num (x + y)) / Polynomial.eval₂ f a (denom (x + y)) =  …
    cases mul_eq_zero.mp this <;> contradiction
    -- ⊢ Polynomial.eval₂ f a (num (x + y)) / Polynomial.eval₂ f a (denom (x + y)) =  …
                                  -- 🎉 no goals
                                  -- 🎉 no goals
  rw [div_add_div _ _ hx hy, eq_div_iff (mul_ne_zero hx hy), div_eq_mul_inv, mul_right_comm, ←
    div_eq_mul_inv, div_eq_iff hxy]
  simp only [← Polynomial.eval₂_mul, ← Polynomial.eval₂_add]
  -- ⊢ Polynomial.eval₂ f a (num (x + y) * (denom x * denom y)) = Polynomial.eval₂  …
  congr 1
  -- ⊢ num (x + y) * (denom x * denom y) = (num x * denom y + denom x * num y) * de …
  apply num_denom_add
  -- 🎉 no goals
#align ratfunc.eval_add RatFunc.eval_add

/-- `eval` is a multiplicative homomorphism except when a denominator evaluates to `0`.

Counterexample: `eval _ 0 X * eval _ 0 (1/X) = 0 ≠ 1 = eval _ 0 1 = eval _ 0 (X * 1/X)`.

See also `RatFunc.eval₂_denom_ne_zero` to make the hypotheses simpler but less general.
-/
theorem eval_mul {x y : RatFunc K} (hx : Polynomial.eval₂ f a (denom x) ≠ 0)
    (hy : Polynomial.eval₂ f a (denom y) ≠ 0) : eval f a (x * y) = eval f a x * eval f a y := by
  unfold eval
  -- ⊢ Polynomial.eval₂ f a (num (x * y)) / Polynomial.eval₂ f a (denom (x * y)) =  …
  by_cases hxy : Polynomial.eval₂ f a (denom (x * y)) = 0
  -- ⊢ Polynomial.eval₂ f a (num (x * y)) / Polynomial.eval₂ f a (denom (x * y)) =  …
  · have := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f a (denom_mul_dvd x y) hxy
    -- ⊢ Polynomial.eval₂ f a (num (x * y)) / Polynomial.eval₂ f a (denom (x * y)) =  …
    rw [Polynomial.eval₂_mul] at this
    -- ⊢ Polynomial.eval₂ f a (num (x * y)) / Polynomial.eval₂ f a (denom (x * y)) =  …
    cases mul_eq_zero.mp this <;> contradiction
    -- ⊢ Polynomial.eval₂ f a (num (x * y)) / Polynomial.eval₂ f a (denom (x * y)) =  …
                                  -- 🎉 no goals
                                  -- 🎉 no goals
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hx hy), div_eq_mul_inv, mul_right_comm, ←
    div_eq_mul_inv, div_eq_iff hxy]
  simp only [← Polynomial.eval₂_mul]  -- porting note: was `repeat' rw [← Polynomial.eval₂_mul]`
  -- ⊢ Polynomial.eval₂ f a (num (x * y) * (denom x * denom y)) = Polynomial.eval₂  …
  congr 1
  -- ⊢ num (x * y) * (denom x * denom y) = num x * num y * denom (x * y)
  apply num_denom_mul
  -- 🎉 no goals
#align ratfunc.eval_mul RatFunc.eval_mul

end Field

end Eval

section IntDegree

open Polynomial

variable [Field K]

/-- `int_degree x` is the degree of the rational function `x`, defined as the difference between
the `nat_degree` of its numerator and the `nat_degree` of its denominator. In particular,
`int_degree 0 = 0`. -/
def intDegree (x : RatFunc K) : ℤ :=
  natDegree x.num - natDegree x.denom
#align ratfunc.int_degree RatFunc.intDegree

@[simp]
theorem intDegree_zero : intDegree (0 : RatFunc K) = 0 := by
  rw [intDegree, num_zero, natDegree_zero, denom_zero, natDegree_one, sub_self]
  -- 🎉 no goals
#align ratfunc.int_degree_zero RatFunc.intDegree_zero

@[simp]
theorem intDegree_one : intDegree (1 : RatFunc K) = 0 := by
  rw [intDegree, num_one, denom_one, sub_self]
  -- 🎉 no goals
#align ratfunc.int_degree_one RatFunc.intDegree_one

@[simp]
theorem intDegree_C (k : K) : intDegree (RatFunc.C k) = 0 := by
  rw [intDegree, num_C, natDegree_C, denom_C, natDegree_one, sub_self]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align ratfunc.int_degree_C RatFunc.intDegree_C

@[simp]
theorem intDegree_X : intDegree (X : RatFunc K) = 1 := by
  rw [intDegree, RatFunc.num_X, Polynomial.natDegree_X, RatFunc.denom_X, Polynomial.natDegree_one,
    Int.ofNat_one, Int.ofNat_zero, sub_zero]
set_option linter.uppercaseLean3 false in
#align ratfunc.int_degree_X RatFunc.intDegree_X

@[simp]
theorem intDegree_polynomial {p : K[X]} :
    intDegree (algebraMap K[X] (RatFunc K) p) = natDegree p := by
  rw [intDegree, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, Polynomial.natDegree_one,
    Int.ofNat_zero, sub_zero]
#align ratfunc.int_degree_polynomial RatFunc.intDegree_polynomial

theorem intDegree_mul {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0) :
    intDegree (x * y) = intDegree x + intDegree y := by
  simp only [intDegree, add_sub, sub_add, sub_sub_eq_add_sub, sub_sub, sub_eq_sub_iff_add_eq_add]
  -- ⊢ ↑(natDegree (num (x * y))) + (↑(natDegree (denom x)) + ↑(natDegree (denom y) …
  norm_cast
  -- ⊢ natDegree (num (x * y)) + (natDegree (denom x) + natDegree (denom y)) = natD …
  rw [← Polynomial.natDegree_mul x.denom_ne_zero y.denom_ne_zero, ←
    Polynomial.natDegree_mul (RatFunc.num_ne_zero (mul_ne_zero hx hy))
      (mul_ne_zero x.denom_ne_zero y.denom_ne_zero),
    ← Polynomial.natDegree_mul (RatFunc.num_ne_zero hx) (RatFunc.num_ne_zero hy), ←
    Polynomial.natDegree_mul (mul_ne_zero (RatFunc.num_ne_zero hx) (RatFunc.num_ne_zero hy))
      (x * y).denom_ne_zero,
    RatFunc.num_denom_mul]
#align ratfunc.int_degree_mul RatFunc.intDegree_mul

@[simp]
theorem intDegree_neg (x : RatFunc K) : intDegree (-x) = intDegree x := by
  by_cases hx : x = 0
  -- ⊢ intDegree (-x) = intDegree x
  · rw [hx, neg_zero]
    -- 🎉 no goals
  · rw [intDegree, intDegree, ← natDegree_neg x.num]
    -- ⊢ ↑(natDegree (num (-x))) - ↑(natDegree (denom (-x))) = ↑(natDegree (-num x))  …
    exact
      natDegree_sub_eq_of_prod_eq (num_ne_zero (neg_ne_zero.mpr hx)) (denom_ne_zero (-x))
        (neg_ne_zero.mpr (num_ne_zero hx)) (denom_ne_zero x) (num_denom_neg x)
#align ratfunc.int_degree_neg RatFunc.intDegree_neg

theorem intDegree_add {x y : RatFunc K} (hxy : x + y ≠ 0) :
    (x + y).intDegree =
      (x.num * y.denom + x.denom * y.num).natDegree - (x.denom * y.denom).natDegree :=
  natDegree_sub_eq_of_prod_eq (num_ne_zero hxy) (x + y).denom_ne_zero
    (num_mul_denom_add_denom_mul_num_ne_zero hxy) (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)
    (num_denom_add x y)
#align ratfunc.int_degree_add RatFunc.intDegree_add

theorem natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree {x : RatFunc K}
    (hx : x ≠ 0) {s : K[X]} (hs : s ≠ 0) :
    ((x.num * s).natDegree : ℤ) - (s * x.denom).natDegree = x.intDegree := by
  apply natDegree_sub_eq_of_prod_eq (mul_ne_zero (num_ne_zero hx) hs)
    (mul_ne_zero hs x.denom_ne_zero) (num_ne_zero hx) x.denom_ne_zero
  rw [mul_assoc]
  -- 🎉 no goals
#align ratfunc.nat_degree_num_mul_right_sub_nat_degree_denom_mul_left_eq_int_degree RatFunc.natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree

theorem intDegree_add_le {x y : RatFunc K} (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    intDegree (x + y) ≤ max (intDegree x) (intDegree y) := by
  by_cases hx : x = 0
  -- ⊢ intDegree (x + y) ≤ max (intDegree x) (intDegree y)
  · simp [hx] at hxy
    -- ⊢ intDegree (x + y) ≤ max (intDegree x) (intDegree y)
    simp [hx, hxy]
    -- 🎉 no goals
  rw [intDegree_add hxy, ←
    natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree hx y.denom_ne_zero,
    mul_comm y.denom, ←
    natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree hy x.denom_ne_zero,
    le_max_iff, sub_le_sub_iff_right, Int.ofNat_le, sub_le_sub_iff_right, Int.ofNat_le, ←
    le_max_iff, mul_comm y.num]
  exact natDegree_add_le _ _
  -- 🎉 no goals
#align ratfunc.int_degree_add_le RatFunc.intDegree_add_le

end IntDegree

section LaurentSeries

open PowerSeries LaurentSeries HahnSeries

variable {F : Type u} [Field F] (p q : F[X]) (f g : RatFunc F)

/-- The coercion `RatFunc F → LaurentSeries F` as bundled alg hom. -/
def coeAlgHom (F : Type u) [Field F] : RatFunc F →ₐ[F[X]] LaurentSeries F :=
  liftAlgHom (Algebra.ofId _ _) <|
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ <|
      Polynomial.algebraMap_hahnSeries_injective _
#align ratfunc.coe_alg_hom RatFunc.coeAlgHom

/-- The coercion `RatFunc F → LaurentSeries F` as a function.

This is the implementation of `coeToLaurentSeries`.
-/
@[coe]
def coeToLaurentSeries_fun {F : Type u} [Field F] : RatFunc F → LaurentSeries F :=
  coeAlgHom F

instance coeToLaurentSeries : Coe (RatFunc F) (LaurentSeries F) :=
  ⟨coeToLaurentSeries_fun⟩
#align ratfunc.coe_to_laurent_series RatFunc.coeToLaurentSeries

theorem coe_def : (f : LaurentSeries F) = coeAlgHom F f :=
  rfl
#align ratfunc.coe_def RatFunc.coe_def

theorem coe_num_denom : (f : LaurentSeries F) = f.num / f.denom :=
  liftAlgHom_apply _ _ f
#align ratfunc.coe_num_denom RatFunc.coe_num_denom

theorem coe_injective : Function.Injective ((↑) : RatFunc F → LaurentSeries F) :=
  liftAlgHom_injective _ (Polynomial.algebraMap_hahnSeries_injective _)
#align ratfunc.coe_injective RatFunc.coe_injective

-- porting note: removed the `norm_cast` tag:
-- `norm_cast: badly shaped lemma, rhs can't start with coe `↑(coeAlgHom F) f`
@[simp]
theorem coe_apply : coeAlgHom F f = f :=
  rfl
#align ratfunc.coe_apply RatFunc.coe_apply

@[simp, norm_cast]
theorem coe_zero : ((0 : RatFunc F) : LaurentSeries F) = 0 :=
  (coeAlgHom F).map_zero
#align ratfunc.coe_zero RatFunc.coe_zero

@[simp, norm_cast]
theorem coe_one : ((1 : RatFunc F) : LaurentSeries F) = 1 :=
  (coeAlgHom F).map_one
#align ratfunc.coe_one RatFunc.coe_one

@[simp, norm_cast]
theorem coe_add : ((f + g : RatFunc F) : LaurentSeries F) = f + g :=
  (coeAlgHom F).map_add _ _
#align ratfunc.coe_add RatFunc.coe_add

@[simp, norm_cast]
theorem coe_sub : ((f - g : RatFunc F) : LaurentSeries F) = f - g :=
  (coeAlgHom F).map_sub _ _
#align ratfunc.coe_sub RatFunc.coe_sub

@[simp, norm_cast]
theorem coe_neg : ((-f : RatFunc F) : LaurentSeries F) = -f :=
  (coeAlgHom F).map_neg _
#align ratfunc.coe_neg RatFunc.coe_neg

@[simp, norm_cast]
theorem coe_mul : ((f * g : RatFunc F) : LaurentSeries F) = f * g :=
  (coeAlgHom F).map_mul _ _
#align ratfunc.coe_mul RatFunc.coe_mul

@[simp, norm_cast]
theorem coe_pow (n : ℕ) : ((f ^ n : RatFunc F) : LaurentSeries F) = (f : LaurentSeries F) ^ n :=
  (coeAlgHom F).map_pow _ _
#align ratfunc.coe_pow RatFunc.coe_pow

@[simp, norm_cast]
theorem coe_div :
    ((f / g : RatFunc F) : LaurentSeries F) = (f : LaurentSeries F) / (g : LaurentSeries F) :=
  map_div₀ (coeAlgHom F) _ _
#align ratfunc.coe_div RatFunc.coe_div

@[simp, norm_cast]
theorem coe_C (r : F) : ((C r : RatFunc F) : LaurentSeries F) = HahnSeries.C r := by
  rw [coe_num_denom, num_C, denom_C, Polynomial.coe_C, -- porting note: removed `coe_C`
    Polynomial.coe_one,
    PowerSeries.coe_one, div_one]
  simp only [algebraMap_eq_C, ofPowerSeries_C, C_apply]  -- porting note: added
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align ratfunc.coe_C RatFunc.coe_C

-- TODO: generalize over other modules
@[simp, norm_cast]
theorem coe_smul (r : F) : ((r • f : RatFunc F) : LaurentSeries F) = r • (f : LaurentSeries F) :=
  by rw [smul_eq_C_mul, ← C_mul_eq_smul, coe_mul, coe_C]
     -- 🎉 no goals
#align ratfunc.coe_smul RatFunc.coe_smul

-- Porting note: removed `norm_cast` because "badly shaped lemma, rhs can't start with coe"
-- even though `single 1 1` is a bundled function application, not a "real" coercion
@[simp]
theorem coe_X : ((X : RatFunc F) : LaurentSeries F) = single 1 1 := by
  rw [coe_num_denom, num_X, denom_X, Polynomial.coe_X, -- porting note: removed `coe_C`
     Polynomial.coe_one,
     PowerSeries.coe_one, div_one]
  simp only [ofPowerSeries_X]  -- porting note: added
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align ratfunc.coe_X RatFunc.coe_X

instance : Algebra (RatFunc F) (LaurentSeries F) :=
  RingHom.toAlgebra (coeAlgHom F).toRingHom

theorem algebraMap_apply_div :
    algebraMap (RatFunc F) (LaurentSeries F) (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap F[X] (LaurentSeries F) p / algebraMap _ _ q := by
  -- porting note: had to supply implicit arguments to `convert`
  convert coe_div (algebraMap F[X] (RatFunc F) p) (algebraMap F[X] (RatFunc F) q) <;>
  -- ⊢ ↑(algebraMap F[X] (LaurentSeries F)) p = ↑(↑(algebraMap F[X] (RatFunc F)) p)
    rw [← mk_one, coe_def, coeAlgHom, mk_eq_div, liftAlgHom_apply_div, map_one, div_one,
      Algebra.ofId_apply]
#align ratfunc.algebra_map_apply_div RatFunc.algebraMap_apply_div

instance : IsScalarTower F[X] (RatFunc F) (LaurentSeries F) :=
  ⟨fun x y z => by
    ext
    -- ⊢ HahnSeries.coeff ((x • y) • z) x✝ = HahnSeries.coeff (x • y • z) x✝
    simp⟩
    -- 🎉 no goals

end LaurentSeries

end RatFunc
