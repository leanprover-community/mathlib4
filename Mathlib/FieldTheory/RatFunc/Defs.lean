/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The field of rational functions

Files in this folder define the field `RatFunc K` of rational functions over a field `K`, show it
is the field of fractions of `K[X]` and provide the main results concerning it. This file contains
the basic definition.

For connections with Laurent Series, see `Mathlib/RingTheory/LaurentSeries.lean`.

## Main definitions
We provide a set of recursion and induction principles:
- `RatFunc.liftOn`: define a function by mapping a fraction of polynomials `p/q` to `f p q`,
  if `f` is well-defined in the sense that `p/q = p'/q' → f p q = f p' q'`.
- `RatFunc.liftOn'`: define a function by mapping a fraction of polynomials `p/q` to `f p q`,
  if `f` is well-defined in the sense that `f (a * p) (a * q) = f p' q'`.
- `RatFunc.induction_on`: if `P` holds on `p / q` for all polynomials `p q`, then `P` holds on all
  rational functions

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

open scoped nonZeroDivisors Polynomial

universe u v

variable (K : Type u)

/-- `RatFunc K` is `K(X)`, the field of rational functions over `K`.

The inclusion of polynomials into `RatFunc` is `algebraMap K[X] (RatFunc K)`,
the maps between `RatFunc K` and another field of fractions of `K[X]`,
especially `FractionRing K[X]`, are given by `IsLocalization.algEquiv`.
-/
structure RatFunc [CommRing K] : Type u where ofFractionRing ::
/-- the coercion to the fraction ring of the polynomial ring -/
  toFractionRing : FractionRing K[X]

namespace RatFunc

section CommRing

variable {K}
variable [CommRing K]

section Rec

/-! ### Constructing `RatFunc`s and their induction principles -/

theorem ofFractionRing_injective : Function.Injective (ofFractionRing : _ → RatFunc K) :=
  fun _ _ => ofFractionRing.inj

theorem toFractionRing_injective : Function.Injective (toFractionRing : _ → FractionRing K[X])
  | ⟨x⟩, ⟨y⟩, xy => by subst xy; rfl

@[simp] lemma toFractionRing_inj {x y : RatFunc K} :
    toFractionRing x = toFractionRing y ↔ x = y :=
  toFractionRing_injective.eq_iff

@[deprecated (since := "2024-12-29")] alias toFractionRing_eq_iff := toFractionRing_inj

/-- Non-dependent recursion principle for `RatFunc K`:
To construct a term of `P : Sort*` out of `x : RatFunc K`,
it suffices to provide a constructor `f : Π (p q : K[X]), P`
and a proof that `f p q = f p' q'` for all `p q p' q'` such that `q' * p = q * p'` where
both `q` and `q'` are not zero divisors, stated as `q ∉ K[X]⁰`, `q' ∉ K[X]⁰`.

If considering `K` as an integral domain, this is the same as saying that
we construct a value of `P` for such elements of `RatFunc K` by setting
`liftOn (p / q) f _ = f p q`.

When `[IsDomain K]`, one can use `RatFunc.liftOn'`, which has the stronger requirement
of `∀ {p q a : K[X]} (hq : q ≠ 0) (ha : a ≠ 0), f (a * p) (a * q) = f p q)`.
-/
protected irreducible_def liftOn {P : Sort v} (x : RatFunc K) (f : K[X] → K[X] → P)
    (H : ∀ {p q p' q'} (_hq : q ∈ K[X]⁰) (_hq' : q' ∈ K[X]⁰), q' * p = q * p' → f p q = f p' q') :
    P :=
  Localization.liftOn (toFractionRing x) (fun p q => f p q) fun {_ _ q q'} h =>
    H q.2 q'.2 (let ⟨⟨_, _⟩, mul_eq⟩ := Localization.r_iff_exists.mp h
      mul_cancel_left_coe_nonZeroDivisors.mp mul_eq)

theorem liftOn_ofFractionRing_mk {P : Sort v} (n : K[X]) (d : K[X]⁰) (f : K[X] → K[X] → P)
    (H : ∀ {p q p' q'} (_hq : q ∈ K[X]⁰) (_hq' : q' ∈ K[X]⁰), q' * p = q * p' → f p q = f p' q') :
    RatFunc.liftOn (ofFractionRing (Localization.mk n d)) f @H = f n d := by
  rw [RatFunc.liftOn]
  exact Localization.liftOn_mk _ _ _ _

theorem liftOn_condition_of_liftOn'_condition {P : Sort v} {f : K[X] → K[X] → P}
    (H : ∀ {p q a} (_ : q ≠ 0) (_ha : a ≠ 0), f (a * p) (a * q) = f p q) ⦃p q p' q' : K[X]⦄
    (hq : q ≠ 0) (hq' : q' ≠ 0) (h : q' * p = q * p') : f p q = f p' q' :=
  calc
    f p q = f (q' * p) (q' * q) := (H hq hq').symm
    _ = f (q * p') (q * q') := by rw [h, mul_comm q']
    _ = f p' q' := H hq' hq

section IsDomain

variable [IsDomain K]

/-- `RatFunc.mk (p q : K[X])` is `p / q` as a rational function.

If `q = 0`, then `mk` returns 0.

This is an auxiliary definition used to define an `Algebra` structure on `RatFunc`;
the `simp` normal form of `mk p q` is `algebraMap _ _ p / algebraMap _ _ q`.
-/
protected irreducible_def mk (p q : K[X]) : RatFunc K :=
  ofFractionRing (algebraMap _ _ p / algebraMap _ _ q)

theorem mk_eq_div' (p q : K[X]) :
    RatFunc.mk p q = ofFractionRing (algebraMap _ _ p / algebraMap _ _ q) := by rw [RatFunc.mk]

theorem mk_zero (p : K[X]) : RatFunc.mk p 0 = ofFractionRing (0 : FractionRing K[X]) := by
  rw [mk_eq_div', RingHom.map_zero, div_zero]

theorem mk_coe_def (p : K[X]) (q : K[X]⁰) :
    RatFunc.mk p q = ofFractionRing (IsLocalization.mk' _ p q) := by
  simp only [mk_eq_div', ← Localization.mk_eq_mk', FractionRing.mk_eq_div]

theorem mk_def_of_mem (p : K[X]) {q} (hq : q ∈ K[X]⁰) :
    RatFunc.mk p q = ofFractionRing (IsLocalization.mk' (FractionRing K[X]) p ⟨q, hq⟩) := by
  simp only [← mk_coe_def]

theorem mk_def_of_ne (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    RatFunc.mk p q =
      ofFractionRing (IsLocalization.mk' (FractionRing K[X]) p
        ⟨q, mem_nonZeroDivisors_iff_ne_zero.mpr hq⟩) :=
  mk_def_of_mem p _

theorem mk_eq_localization_mk (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    RatFunc.mk p q =
      ofFractionRing (Localization.mk p ⟨q, mem_nonZeroDivisors_iff_ne_zero.mpr hq⟩) := by
  rw [mk_def_of_ne _ hq, Localization.mk_eq_mk']

theorem mk_one' (p : K[X]) :
    RatFunc.mk p 1 = ofFractionRing (algebraMap _ _ p) := by
  rw [← IsLocalization.mk'_one (M := K[X]⁰) (FractionRing K[X]) p, ← mk_coe_def, Submonoid.coe_one]

theorem mk_eq_mk {p q p' q' : K[X]} (hq : q ≠ 0) (hq' : q' ≠ 0) :
    RatFunc.mk p q = RatFunc.mk p' q' ↔ p * q' = p' * q := by
  rw [mk_def_of_ne _ hq, mk_def_of_ne _ hq', ofFractionRing_injective.eq_iff,
    IsLocalization.mk'_eq_iff_eq',
    (IsFractionRing.injective K[X] (FractionRing K[X])).eq_iff]

theorem liftOn_mk {P : Sort v} (p q : K[X]) (f : K[X] → K[X] → P) (f0 : ∀ p, f p 0 = f 0 1)
    (H' : ∀ {p q p' q'} (_hq : q ≠ 0) (_hq' : q' ≠ 0), q' * p = q * p' → f p q = f p' q')
    (H : ∀ {p q p' q'} (_hq : q ∈ K[X]⁰) (_hq' : q' ∈ K[X]⁰), q' * p = q * p' → f p q = f p' q' :=
      fun {_ _ _ _} hq hq' h => H' (nonZeroDivisors.ne_zero hq) (nonZeroDivisors.ne_zero hq') h) :
    (RatFunc.mk p q).liftOn f @H = f p q := by
  by_cases hq : q = 0
  · subst hq
    simp only [mk_zero, f0, ← Localization.mk_zero 1, Localization.liftOn_mk,
      liftOn_ofFractionRing_mk, Submonoid.coe_one]
  · simp only [mk_eq_localization_mk _ hq, Localization.liftOn_mk, liftOn_ofFractionRing_mk]

/-- Non-dependent recursion principle for `RatFunc K`: if `f p q : P` for all `p q`,
such that `f (a * p) (a * q) = f p q`, then we can find a value of `P`
for all elements of `RatFunc K` by setting `lift_on' (p / q) f _ = f p q`.

The value of `f p 0` for any `p` is never used and in principle this may be anything,
although many usages of `lift_on'` assume `f p 0 = f 0 1`.
-/
protected irreducible_def liftOn' {P : Sort v} (x : RatFunc K) (f : K[X] → K[X] → P)
  (H : ∀ {p q a} (_hq : q ≠ 0) (_ha : a ≠ 0), f (a * p) (a * q) = f p q) : P :=
  x.liftOn f fun {_p _q _p' _q'} hq hq' =>
    liftOn_condition_of_liftOn'_condition (@H) (nonZeroDivisors.ne_zero hq)
      (nonZeroDivisors.ne_zero hq')

theorem liftOn'_mk {P : Sort v} (p q : K[X]) (f : K[X] → K[X] → P) (f0 : ∀ p, f p 0 = f 0 1)
    (H : ∀ {p q a} (_hq : q ≠ 0) (_ha : a ≠ 0), f (a * p) (a * q) = f p q) :
    (RatFunc.mk p q).liftOn' f @H = f p q := by
  rw [RatFunc.liftOn', RatFunc.liftOn_mk _ _ _ f0]
  apply liftOn_condition_of_liftOn'_condition H

/-- Induction principle for `RatFunc K`: if `f p q : P (RatFunc.mk p q)` for all `p q`,
then `P` holds on all elements of `RatFunc K`.

See also `induction_on`, which is a recursion principle defined in terms of `algebraMap`.
-/
@[elab_as_elim]
protected theorem induction_on' {P : RatFunc K → Prop} :
    ∀ (x : RatFunc K) (_pq : ∀ (p q : K[X]) (_ : q ≠ 0), P (RatFunc.mk p q)), P x
  | ⟨x⟩, f =>
    Localization.induction_on x fun ⟨p, q⟩ => by
      simpa only [mk_coe_def, Localization.mk_eq_mk'] using
        f p q (mem_nonZeroDivisors_iff_ne_zero.mp q.2)

end IsDomain

end Rec

end CommRing

end RatFunc
