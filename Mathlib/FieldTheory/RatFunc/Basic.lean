/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.FieldTheory.RatFunc.Defs
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Content

#align_import field_theory.ratfunc from "leanprover-community/mathlib"@"bf9bbbcf0c1c1ead18280b0d010e417b10abb1b6"

/-!
# The field structure of rational functions

## Main definitions
Working with rational functions as polynomials:
 - `RatFunc.instField` provides a field structure
You can use `IsFractionRing` API to treat `RatFunc` as the field of fractions of polynomials:
 * `algebraMap K[X] (RatFunc K)` maps polynomials to rational functions
 * `IsFractionRing.algEquiv` maps other fields of fractions of `K[X]` to `RatFunc K`,
in particular:
 * `FractionRing.algEquiv K[X] (RatFunc K)` maps the generic field of
    fraction construction to `RatFunc K`. Combine this with `AlgEquiv.restrictScalars` to change
    the `FractionRing K[X] ≃ₐ[K[X]] RatFunc K` to `FractionRing K[X] ≃ₐ[K] RatFunc K`.

Working with rational functions as fractions:
- `RatFunc.num` and `RatFunc.denom` give the numerator and denominator.
  These values are chosen to be coprime and such that `RatFunc.denom` is monic.

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
-/

universe u v

noncomputable section

open scoped Classical

open scoped nonZeroDivisors Polynomial

variable {K : Type u}

namespace RatFunc

section Field

variable [CommRing K]

/-- The zero rational function. -/
protected irreducible_def zero : RatFunc K :=
  ⟨0⟩
#align ratfunc.zero RatFunc.zero

instance : Zero (RatFunc K) :=
  ⟨RatFunc.zero⟩

-- Porting note: added `OfNat.ofNat`.  using `simp?` produces `simp only [zero_def]`
-- that does not close the goal
theorem ofFractionRing_zero : (ofFractionRing 0 : RatFunc K) = 0 := by
  simp only [Zero.zero, OfNat.ofNat, RatFunc.zero]
#align ratfunc.of_fraction_ring_zero RatFunc.ofFractionRing_zero

/-- Addition of rational functions. -/
protected irreducible_def add : RatFunc K → RatFunc K → RatFunc K
  | ⟨p⟩, ⟨q⟩ => ⟨p + q⟩
#align ratfunc.add RatFunc.add

instance : Add (RatFunc K) :=
  ⟨RatFunc.add⟩

-- Porting note: added `HAdd.hAdd`.  using `simp?` produces `simp only [add_def]`
-- that does not close the goal
theorem ofFractionRing_add (p q : FractionRing K[X]) :
    ofFractionRing (p + q) = ofFractionRing p + ofFractionRing q := by
  simp only [HAdd.hAdd, Add.add, RatFunc.add]
#align ratfunc.of_fraction_ring_add RatFunc.ofFractionRing_add

/-- Subtraction of rational functions. -/
protected irreducible_def sub : RatFunc K → RatFunc K → RatFunc K
  | ⟨p⟩, ⟨q⟩ => ⟨p - q⟩
#align ratfunc.sub RatFunc.sub

instance : Sub (RatFunc K) :=
  ⟨RatFunc.sub⟩

-- Porting note: added `HSub.hSub`.  using `simp?` produces `simp only [sub_def]`
-- that does not close the goal
theorem ofFractionRing_sub (p q : FractionRing K[X]) :
    ofFractionRing (p - q) = ofFractionRing p - ofFractionRing q := by
  simp only [Sub.sub, HSub.hSub, RatFunc.sub]
#align ratfunc.of_fraction_ring_sub RatFunc.ofFractionRing_sub

/-- Additive inverse of a rational function. -/
protected irreducible_def neg : RatFunc K → RatFunc K
  | ⟨p⟩ => ⟨-p⟩
#align ratfunc.neg RatFunc.neg

instance : Neg (RatFunc K) :=
  ⟨RatFunc.neg⟩

theorem ofFractionRing_neg (p : FractionRing K[X]) :
    ofFractionRing (-p) = -ofFractionRing p := by simp only [Neg.neg, RatFunc.neg]
#align ratfunc.of_fraction_ring_neg RatFunc.ofFractionRing_neg

/-- The multiplicative unit of rational functions. -/
protected irreducible_def one : RatFunc K :=
  ⟨1⟩
#align ratfunc.one RatFunc.one

instance : One (RatFunc K) :=
  ⟨RatFunc.one⟩

-- Porting note: added `OfNat.ofNat`.  using `simp?` produces `simp only [one_def]`
-- that does not close the goal
theorem ofFractionRing_one : (ofFractionRing 1 : RatFunc K) = 1 := by
  simp only [One.one, OfNat.ofNat, RatFunc.one]
#align ratfunc.of_fraction_ring_one RatFunc.ofFractionRing_one

/-- Multiplication of rational functions. -/
protected irreducible_def mul : RatFunc K → RatFunc K → RatFunc K
  | ⟨p⟩, ⟨q⟩ => ⟨p * q⟩
#align ratfunc.mul RatFunc.mul

instance : Mul (RatFunc K) :=
  ⟨RatFunc.mul⟩

-- Porting note: added `HMul.hMul`.  using `simp?` produces `simp only [mul_def]`
-- that does not close the goal
theorem ofFractionRing_mul (p q : FractionRing K[X]) :
    ofFractionRing (p * q) = ofFractionRing p * ofFractionRing q := by
  simp only [Mul.mul, HMul.hMul, RatFunc.mul]
#align ratfunc.of_fraction_ring_mul RatFunc.ofFractionRing_mul

section IsDomain

variable [IsDomain K]

/-- Division of rational functions. -/
protected irreducible_def div : RatFunc K → RatFunc K → RatFunc K
  | ⟨p⟩, ⟨q⟩ => ⟨p / q⟩
#align ratfunc.div RatFunc.div

instance : Div (RatFunc K) :=
  ⟨RatFunc.div⟩

-- Porting note: added `HDiv.hDiv`.  using `simp?` produces `simp only [div_def]`
-- that does not close the goal
theorem ofFractionRing_div (p q : FractionRing K[X]) :
    ofFractionRing (p / q) = ofFractionRing p / ofFractionRing q := by
  simp only [Div.div, HDiv.hDiv, RatFunc.div]
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
#align ratfunc.of_fraction_ring_inv RatFunc.ofFractionRing_inv

-- Auxiliary lemma for the `Field` instance
theorem mul_inv_cancel : ∀ {p : RatFunc K}, p ≠ 0 → p * p⁻¹ = 1
  | ⟨p⟩, h => by
    have : p ≠ 0 := fun hp => h <| by rw [hp, ofFractionRing_zero]
    simpa only [← ofFractionRing_inv, ← ofFractionRing_mul, ← ofFractionRing_one,
      ofFractionRing.injEq] using  -- Porting note: `ofFractionRing.injEq` was not present
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
--@[nolint fails_quickly]  -- Porting note: `linter 'fails_quickly' not found`
instance [SMul R (FractionRing K[X])] : SMul R (RatFunc K) :=
  ⟨RatFunc.smul⟩

-- Porting note: added `SMul.hSMul`.  using `simp?` produces `simp only [smul_def]`
-- that does not close the goal
theorem ofFractionRing_smul [SMul R (FractionRing K[X])] (c : R) (p : FractionRing K[X]) :
    ofFractionRing (c • p) = c • ofFractionRing p := by
  simp only [SMul.smul, HSMul.hSMul, RatFunc.smul]
#align ratfunc.of_fraction_ring_smul RatFunc.ofFractionRing_smul

theorem toFractionRing_smul [SMul R (FractionRing K[X])] (c : R) (p : RatFunc K) :
    toFractionRing (c • p) = c • toFractionRing p := by
  cases p
  rw [← ofFractionRing_smul]
#align ratfunc.to_fraction_ring_smul RatFunc.toFractionRing_smul

theorem smul_eq_C_smul (x : RatFunc K) (r : K) : r • x = Polynomial.C r • x := by
  cases' x with x
  -- Porting note: had to specify the induction principle manually
  induction x using Localization.induction_on
  rw [← ofFractionRing_smul, ← ofFractionRing_smul, Localization.smul_mk,
    Localization.smul_mk, smul_eq_mul, Polynomial.smul_eq_C_mul]
set_option linter.uppercaseLean3 false in
#align ratfunc.smul_eq_C_smul RatFunc.smul_eq_C_smul

section IsDomain

variable [IsDomain K]
variable [Monoid R] [DistribMulAction R K[X]]
variable [IsScalarTower R K[X] K[X]]

theorem mk_smul (c : R) (p q : K[X]) : RatFunc.mk (c • p) q = c • RatFunc.mk p q := by
  by_cases hq : q = 0
  · rw [hq, mk_zero, mk_zero, ← ofFractionRing_smul, smul_zero]
  · rw [mk_eq_localization_mk _ hq, mk_eq_localization_mk _ hq, ← Localization.smul_mk, ←
      ofFractionRing_smul]
#align ratfunc.mk_smul RatFunc.mk_smul

instance : IsScalarTower R K[X] (RatFunc K) :=
  ⟨fun c p q => q.induction_on' fun q r _ => by rw [← mk_smul, smul_assoc, mk_smul, mk_smul]⟩

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
  map_mul' := fun ⟨_⟩ ⟨_⟩ => by simp [← ofFractionRing_mul]
#align ratfunc.to_fraction_ring_ring_equiv RatFunc.toFractionRingRingEquiv

end Field

section TacticInterlude

-- Porting note: reimplemented the `frac_tac` and `smul_tac` as close to the originals as I could
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
    simp_rw [← ofFractionRing_smul] <;>
    simp only [add_comm, mul_comm, zero_smul, succ_nsmul, zsmul_eq_mul, mul_add, mul_one, mul_zero,
      neg_add, mul_neg,
      Int.ofNat_eq_coe, Int.cast_zero, Int.cast_add, Int.cast_one,
      Int.cast_negSucc, Int.cast_natCast, Nat.cast_succ,
      Localization.mk_zero, Localization.add_mk_self, Localization.neg_mk,
      ofFractionRing_zero, ← ofFractionRing_add, ← ofFractionRing_neg])

end TacticInterlude

section CommRing

variable (K) [CommRing K]

-- Porting note: split the CommRing instance up into multiple defs because it was hard to see
-- if the big instance declaration made any progress.
/-- `RatFunc K` is a commutative monoid.

This is an intermediate step on the way to the full instance `RatFunc.instCommRing`.
-/
def instCommMonoid : CommMonoid (RatFunc K) where
  mul := (· * ·)
  mul_assoc := by frac_tac
  mul_comm := by frac_tac
  one := 1
  one_mul := by frac_tac
  mul_one := by frac_tac
  npow := npowRec

/-- `RatFunc K` is an additive commutative group.

This is an intermediate step on the way to the full instance `RatFunc.instCommRing`.
-/
def instAddCommGroup : AddCommGroup (RatFunc K) where
  add := (· + ·)
  add_assoc := by frac_tac
 -- Porting note: `by frac_tac` didn't work:
  add_comm := by repeat rintro (⟨⟩ : RatFunc _) <;> simp only [← ofFractionRing_add, add_comm]
  zero := 0
  zero_add := by frac_tac
  add_zero := by frac_tac
  neg := Neg.neg
  add_left_neg := by frac_tac
  sub := Sub.sub
  sub_eq_add_neg := by frac_tac
  nsmul := (· • ·)
  nsmul_zero := by smul_tac
  nsmul_succ _ := by smul_tac
  zsmul := (· • ·)
  zsmul_zero' := by smul_tac
  zsmul_succ' _ := by smul_tac
  zsmul_neg' _ := by smul_tac

instance instCommRing : CommRing (RatFunc K) :=
  { instCommMonoid K, instAddCommGroup K with
    zero := 0
    sub := Sub.sub
    zero_mul := by frac_tac
    mul_zero := by frac_tac
    left_distrib := by frac_tac
    right_distrib := by frac_tac
    one := 1
    nsmul := (· • ·)
    zsmul := (· • ·)
    npow := npowRec }
#align ratfunc.comm_ring RatFunc.instCommRing

variable {K}

section LiftHom

open RatFunc

variable {G₀ L R S F : Type*} [CommGroupWithZero G₀] [Field L] [CommRing R] [CommRing S]
variable [FunLike F R[X] S[X]]
/-- Lift a monoid homomorphism that maps polynomials `φ : R[X] →* S[X]`
to a `RatFunc R →* RatFunc S`,
on the condition that `φ` maps non zero divisors to non zero divisors,
by mapping both the numerator and denominator and quotienting them. -/

def map [MonoidHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) :
    RatFunc R →* RatFunc S where
  toFun f :=
    RatFunc.liftOn f
      (fun n d => if h : φ d ∈ S[X]⁰ then ofFractionRing (Localization.mk (φ n) ⟨φ d, h⟩) else 0)
      fun {p q p' q'} hq hq' h => by
      beta_reduce -- Porting note(#12129): force the function to be applied
      rw [dif_pos, dif_pos]
      on_goal 1 =>
        congr 1 -- Porting note: this was a `rw [ofFractionRing.inj_eq]` which was overkill anyway
        rw [Localization.mk_eq_mk_iff]
      rotate_left
      · exact hφ hq
      · exact hφ hq'
      refine Localization.r_of_eq ?_
      simpa only [map_mul] using congr_arg φ h
  map_one' := by
    beta_reduce -- Porting note(#12129): force the function to be applied
    rw [← ofFractionRing_one, ← Localization.mk_one, liftOn_ofFractionRing_mk, dif_pos]
    · simpa using ofFractionRing_one
    · simpa using Submonoid.one_mem _
  map_mul' x y := by
    beta_reduce -- Porting note(#12129): force the function to be applied
    cases' x with x; cases' y with y
    -- Porting note: added `using Localization.rec` (`Localization.induction_on` didn't work)
    induction' x using Localization.rec with p q
    · induction' y using Localization.rec with p' q'
      · have hq : φ q ∈ S[X]⁰ := hφ q.prop
        have hq' : φ q' ∈ S[X]⁰ := hφ q'.prop
        have hqq' : φ ↑(q * q') ∈ S[X]⁰ := by simpa using Submonoid.mul_mem _ hq hq'
        simp_rw [← ofFractionRing_mul, Localization.mk_mul, liftOn_ofFractionRing_mk, dif_pos hq,
          dif_pos hq', dif_pos hqq', ← ofFractionRing_mul, Submonoid.coe_mul, map_mul,
          Localization.mk_mul, Submonoid.mk_mul_mk]
      · rfl
    · rfl
#align ratfunc.map RatFunc.map

theorem map_apply_ofFractionRing_mk [MonoidHomClass F R[X] S[X]] (φ : F)
    (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) (n : R[X]) (d : R[X]⁰) :
    map φ hφ (ofFractionRing (Localization.mk n d)) =
      ofFractionRing (Localization.mk (φ n) ⟨φ d, hφ d.prop⟩) := by
  -- Porting note: replaced `convert` with `refine Eq.trans`
  refine (liftOn_ofFractionRing_mk n _ _ _).trans ?_
  rw [dif_pos]
#align ratfunc.map_apply_of_fraction_ring_mk RatFunc.map_apply_ofFractionRing_mk

set_option backward.synthInstance.canonInstances false in -- See https://github.com/leanprover-community/mathlib4/issues/12532
theorem map_injective [MonoidHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ ≤ S[X]⁰.comap φ)
    (hf : Function.Injective φ) : Function.Injective (map φ hφ) := by
  rintro ⟨x⟩ ⟨y⟩ h
  -- Porting note: had to hint `induction` which induction principle to use
  induction x using Localization.induction_on
  induction y using Localization.induction_on
  simpa only [map_apply_ofFractionRing_mk, ofFractionRing_injective.eq_iff,
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
      -- Porting note: had to hint `induction` which induction principle to use
      induction x using Localization.rec
      induction y using Localization.rec
      · simp only [← ofFractionRing_add, Localization.add_mk, map_add, map_mul,
          MonoidHom.toFun_eq_coe, map_apply_ofFractionRing_mk, Submonoid.coe_mul]
        -- Porting note: `Submonoid.mk_mul_mk` couldn't be applied: motive incorrect,
        -- even though it is a rfl lemma.
        rfl
      · rfl
      · rfl }
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
      · rw [Subsingleton.elim p q, Subsingleton.elim p' q, Subsingleton.elim q' q]
      rw [div_eq_div_iff, ← map_mul, mul_comm p, h, map_mul, mul_comm] <;>
        exact nonZeroDivisors.ne_zero (hφ ‹_›)
  map_one' := by
    dsimp only -- Porting note: force the function to be applied (not just beta reduction!)
    rw [← ofFractionRing_one, ← Localization.mk_one, liftOn_ofFractionRing_mk]
    simp only [map_one, OneMemClass.coe_one, div_one]
  map_mul' x y := by
    cases' x with x
    cases' y with y
    induction' x using Localization.rec with p q
    · induction' y using Localization.rec with p' q'
      · rw [← ofFractionRing_mul, Localization.mk_mul]
        simp only [liftOn_ofFractionRing_mk, div_mul_div_comm, map_mul, Submonoid.coe_mul]
      · rfl
    · rfl
  map_zero' := by
    beta_reduce -- Porting note(#12129): force the function to be applied
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
  induction' x using Localization.induction_on with a
  induction' y using Localization.induction_on with a'
  simp_rw [liftMonoidWithZeroHom_apply_ofFractionRing_mk]
  intro h
  congr 1
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (M := R[X]) ?_)
  have := mul_eq_mul_of_div_eq_div _ _ ?_ ?_ h
  · rwa [← map_mul, ← map_mul, hφ.eq_iff, mul_comm, mul_comm a'.fst] at this
  all_goals exact map_ne_zero_of_mem_nonZeroDivisors _ hφ (SetLike.coe_mem _)
#align ratfunc.lift_monoid_with_zero_hom_injective RatFunc.liftMonoidWithZeroHom_injective

/-- Lift an injective ring homomorphism `R[X] →+* L` to a `RatFunc R →+* L`
by mapping both the numerator and denominator and quotienting them. -/
def liftRingHom (φ : R[X] →+* L) (hφ : R[X]⁰ ≤ L⁰.comap φ) : RatFunc R →+* L :=
  { liftMonoidWithZeroHom φ.toMonoidWithZeroHom hφ with
    map_add' := fun x y => by
      -- Porting note: used to invoke `MonoidWithZeroHom.toFun_eq_coe`
      simp only [ZeroHom.toFun_eq_coe, MonoidWithZeroHom.toZeroHom_coe]
      cases subsingleton_or_nontrivial R
      · rw [Subsingleton.elim (x + y) y, Subsingleton.elim x 0, map_zero, zero_add]
      cases' x with x
      cases' y with y
      -- Porting note: had to add the recursor explicitly below
      induction' x using Localization.rec with p q
      · induction' y using Localization.rec with p' q'
        · rw [← ofFractionRing_add, Localization.add_mk]
          simp only [RingHom.toMonoidWithZeroHom_eq_coe,
            liftMonoidWithZeroHom_apply_ofFractionRing_mk]
          rw [div_add_div, div_eq_div_iff]
          · rw [mul_comm _ p, mul_comm _ p', mul_comm _ (φ p'), add_comm]
            simp only [map_add, map_mul, Submonoid.coe_mul]
          all_goals
            try simp only [← map_mul, ← Submonoid.coe_mul]
            exact nonZeroDivisors.ne_zero (hφ (SetLike.coe_mem _))
        · rfl
      · rfl }
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

instance instField [IsDomain K] : Field (RatFunc K) where
  -- Porting note: used to be `by frac_tac`
  inv_zero := by rw [← ofFractionRing_zero, ← ofFractionRing_inv, inv_zero]
  div := (· / ·)
  div_eq_mul_inv := by frac_tac
  mul_inv_cancel _ := mul_inv_cancel
  zpow := zpowRec
  nnqsmul := _
  qsmul := _

section IsFractionRing

/-! ### `RatFunc` as field of fractions of `Polynomial` -/

section IsDomain

variable [IsDomain K]

instance (R : Type*) [CommSemiring R] [Algebra R K[X]] : Algebra R (RatFunc K) where
  toFun x := RatFunc.mk (algebraMap _ _ x) 1
  map_add' x y := by simp only [mk_one', RingHom.map_add, ofFractionRing_add]
  map_mul' x y := by simp only [mk_one', RingHom.map_mul, ofFractionRing_mul]
  map_one' := by simp only [mk_one', RingHom.map_one, ofFractionRing_one]
  map_zero' := by simp only [mk_one', RingHom.map_zero, ofFractionRing_zero]
  smul := (· • ·)
  smul_def' c x := by
    induction' x using RatFunc.induction_on' with p q hq
      -- Porting note: the first `rw [...]` was not needed
    rw [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [mk_one', ← mk_smul, mk_def_of_ne (c • p) hq, mk_def_of_ne p hq, ←
      ofFractionRing_mul, IsLocalization.mul_mk'_eq_mk'_of_mul, Algebra.smul_def]
  commutes' c x := mul_comm _ _

variable {K}

/-- The coercion from polynomials to rational functions, implemented as the algebra map from a
domain to its field of fractions -/
@[coe]
def coePolynomial (P : Polynomial K) : RatFunc K := algebraMap _ _ P

instance : Coe (Polynomial K) (RatFunc K) := ⟨coePolynomial⟩

theorem mk_one (x : K[X]) : RatFunc.mk x 1 = algebraMap _ _ x :=
  rfl
#align ratfunc.mk_one RatFunc.mk_one

theorem ofFractionRing_algebraMap (x : K[X]) :
    ofFractionRing (algebraMap _ (FractionRing K[X]) x) = algebraMap _ _ x := by
  rw [← mk_one, mk_one']
#align ratfunc.of_fraction_ring_algebra_map RatFunc.ofFractionRing_algebraMap

@[simp]
theorem mk_eq_div (p q : K[X]) : RatFunc.mk p q = algebraMap _ _ p / algebraMap _ _ q := by
  simp only [mk_eq_div', ofFractionRing_div, ofFractionRing_algebraMap]
#align ratfunc.mk_eq_div RatFunc.mk_eq_div

@[simp]
theorem div_smul {R} [Monoid R] [DistribMulAction R K[X]] [IsScalarTower R K[X] K[X]] (c : R)
    (p q : K[X]) :
    algebraMap _ (RatFunc K) (c • p) / algebraMap _ _ q =
      c • (algebraMap _ _ p / algebraMap _ _ q) := by
  rw [← mk_eq_div, mk_smul, mk_eq_div]
#align ratfunc.div_smul RatFunc.div_smul

theorem algebraMap_apply {R : Type*} [CommSemiring R] [Algebra R K[X]] (x : R) :
    algebraMap R (RatFunc K) x = algebraMap _ _ (algebraMap R K[X] x) / algebraMap K[X] _ 1 := by
  rw [← mk_eq_div]
  rfl
#align ratfunc.algebra_map_apply RatFunc.algebraMap_apply

theorem map_apply_div_ne_zero {R F : Type*} [CommRing R] [IsDomain R]
    [FunLike F K[X] R[X]] [MonoidHomClass F K[X] R[X]]
    (φ : F) (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) (p q : K[X]) (hq : q ≠ 0) :
    map φ hφ (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap _ _ (φ p) / algebraMap _ _ (φ q) := by
  have hq' : φ q ≠ 0 := nonZeroDivisors.ne_zero (hφ (mem_nonZeroDivisors_iff_ne_zero.mpr hq))
  simp only [← mk_eq_div, mk_eq_localization_mk _ hq, map_apply_ofFractionRing_mk,
    mk_eq_localization_mk _ hq']
#align ratfunc.map_apply_div_ne_zero RatFunc.map_apply_div_ne_zero

@[simp]
theorem map_apply_div {R F : Type*} [CommRing R] [IsDomain R]
    [FunLike F K[X] R[X]] [MonoidWithZeroHomClass F K[X] R[X]]
    (φ : F) (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) (p q : K[X]) :
    map φ hφ (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap _ _ (φ p) / algebraMap _ _ (φ q) := by
  rcases eq_or_ne q 0 with (rfl | hq)
  · have : (0 : RatFunc K) = algebraMap K[X] _ 0 / algebraMap K[X] _ 1 := by simp
    rw [map_zero, map_zero, map_zero, div_zero, div_zero, this, map_apply_div_ne_zero, map_one,
      map_one, div_one, map_zero, map_zero]
    exact one_ne_zero
  exact map_apply_div_ne_zero _ _ _ _ hq
#align ratfunc.map_apply_div RatFunc.map_apply_div

theorem liftMonoidWithZeroHom_apply_div {L : Type*} [CommGroupWithZero L]
    (φ : MonoidWithZeroHom K[X] L) (hφ : K[X]⁰ ≤ L⁰.comap φ) (p q : K[X]) :
    liftMonoidWithZeroHom φ hφ (algebraMap _ _ p / algebraMap _ _ q) = φ p / φ q := by
  rcases eq_or_ne q 0 with (rfl | hq)
  · simp only [div_zero, map_zero]
  simp only [← mk_eq_div, mk_eq_localization_mk _ hq,
    liftMonoidWithZeroHom_apply_ofFractionRing_mk]
#align ratfunc.lift_monoid_with_zero_hom_apply_div RatFunc.liftMonoidWithZeroHom_apply_div

@[simp]
theorem liftMonoidWithZeroHom_apply_div' {L : Type*} [CommGroupWithZero L]
    (φ : MonoidWithZeroHom K[X] L) (hφ : K[X]⁰ ≤ L⁰.comap φ) (p q : K[X]) :
    liftMonoidWithZeroHom φ hφ (algebraMap _ _ p) / liftMonoidWithZeroHom φ hφ (algebraMap _ _ q) =
      φ p / φ q := by
  rw [← map_div₀, liftMonoidWithZeroHom_apply_div]

theorem liftRingHom_apply_div {L : Type*} [Field L] (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ)
    (p q : K[X]) : liftRingHom φ hφ (algebraMap _ _ p / algebraMap _ _ q) = φ p / φ q :=
  liftMonoidWithZeroHom_apply_div _ hφ _ _  -- Porting note: gave explicitly the `hφ`
#align ratfunc.lift_ring_hom_apply_div RatFunc.liftRingHom_apply_div

@[simp]
theorem liftRingHom_apply_div' {L : Type*} [Field L] (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ)
    (p q : K[X]) : liftRingHom φ hφ (algebraMap _ _ p) / liftRingHom φ hφ (algebraMap _ _ q) =
      φ p / φ q :=
  liftMonoidWithZeroHom_apply_div' _ hφ _ _  -- Porting note: gave explicitly the `hφ`

variable (K)

theorem ofFractionRing_comp_algebraMap :
    ofFractionRing ∘ algebraMap K[X] (FractionRing K[X]) = algebraMap _ _ :=
  funext ofFractionRing_algebraMap
#align ratfunc.of_fraction_ring_comp_algebra_map RatFunc.ofFractionRing_comp_algebraMap

theorem algebraMap_injective : Function.Injective (algebraMap K[X] (RatFunc K)) := by
  rw [← ofFractionRing_comp_algebraMap]
  exact ofFractionRing_injective.comp (IsFractionRing.injective _ _)
#align ratfunc.algebra_map_injective RatFunc.algebraMap_injective

@[simp]
theorem algebraMap_eq_zero_iff {x : K[X]} : algebraMap K[X] (RatFunc K) x = 0 ↔ x = 0 :=
  ⟨(injective_iff_map_eq_zero _).mp (algebraMap_injective K) _, fun hx => by
    rw [hx, RingHom.map_zero]⟩
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
  liftMonoidWithZeroHom_apply_ofFractionRing_mk _ hφ _ _ -- Porting note: gave explicitly the `hφ`
#align ratfunc.lift_alg_hom_apply_of_fraction_ring_mk RatFunc.liftAlgHom_apply_ofFractionRing_mk

theorem liftAlgHom_injective (φ : K[X] →ₐ[S] L) (hφ : Function.Injective φ)
    (hφ' : K[X]⁰ ≤ L⁰.comap φ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hφ) :
    Function.Injective (liftAlgHom φ hφ') :=
  liftMonoidWithZeroHom_injective _ hφ
#align ratfunc.lift_alg_hom_injective RatFunc.liftAlgHom_injective

@[simp]
theorem liftAlgHom_apply_div' (p q : K[X]) :
    liftAlgHom φ hφ (algebraMap _ _ p) / liftAlgHom φ hφ (algebraMap _ _ q) = φ p / φ q :=
  liftMonoidWithZeroHom_apply_div' _ hφ _ _  -- Porting note: gave explicitly the `hφ`

theorem liftAlgHom_apply_div (p q : K[X]) :
    liftAlgHom φ hφ (algebraMap _ _ p / algebraMap _ _ q) = φ p / φ q :=
  liftMonoidWithZeroHom_apply_div _ hφ _ _  -- Porting note: gave explicitly the `hφ`
#align ratfunc.lift_alg_hom_apply_div RatFunc.liftAlgHom_apply_div

end LiftAlgHom

variable (K)

/-- `RatFunc K` is the field of fractions of the polynomials over `K`. -/
instance : IsFractionRing K[X] (RatFunc K) where
  map_units' y := by
    rw [← ofFractionRing_algebraMap]
    exact (toFractionRingRingEquiv K).symm.toRingHom.isUnit_map (IsLocalization.map_units _ y)
  exists_of_eq {x y} := by
    rw [← ofFractionRing_algebraMap, ← ofFractionRing_algebraMap]
    exact fun h ↦ IsLocalization.exists_of_eq ((toFractionRingRingEquiv K).symm.injective h)
  surj' := by
    rintro ⟨z⟩
    convert IsLocalization.surj K[X]⁰ z
    -- Porting note: `ext ⟨x, y⟩` no longer necessary
    simp only [← ofFractionRing_algebraMap, Function.comp_apply, ← ofFractionRing_mul]
    rw [ofFractionRing.injEq]  -- Porting note: added

variable {K}

@[simp]
theorem liftOn_div {P : Sort v} (p q : K[X]) (f : K[X] → K[X] → P) (f0 : ∀ p, f p 0 = f 0 1)
    (H' : ∀ {p q p' q'} (_hq : q ≠ 0) (_hq' : q' ≠ 0), q' * p = q * p' → f p q = f p' q')
    (H : ∀ {p q p' q'} (_hq : q ∈ K[X]⁰) (_hq' : q' ∈ K[X]⁰), q' * p = q * p' → f p q = f p' q' :=
      fun {p q p' q'} hq hq' h => H' (nonZeroDivisors.ne_zero hq) (nonZeroDivisors.ne_zero hq') h) :
    (RatFunc.liftOn (algebraMap _ (RatFunc K) p / algebraMap _ _ q)) f @H = f p q := by
  rw [← mk_eq_div, liftOn_mk _ _ f f0 @H']
#align ratfunc.lift_on_div RatFunc.liftOn_div

@[simp]
theorem liftOn'_div {P : Sort v} (p q : K[X]) (f : K[X] → K[X] → P) (f0 : ∀ p, f p 0 = f 0 1)
    (H) :
    (RatFunc.liftOn' (algebraMap _ (RatFunc K) p / algebraMap _ _ q)) f @H = f p q := by
  rw [RatFunc.liftOn', liftOn_div _ _ _ f0]
  apply liftOn_condition_of_liftOn'_condition H -- Porting note: `exact` did not work.  Also,
                                                  -- was `@H` that still works, but is not needed.
#align ratfunc.lift_on'_div RatFunc.liftOn'_div

/-- Induction principle for `RatFunc K`: if `f p q : P (p / q)` for all `p q : K[X]`,
then `P` holds on all elements of `RatFunc K`.

See also `induction_on'`, which is a recursion principle defined in terms of `RatFunc.mk`.
-/
protected theorem induction_on {P : RatFunc K → Prop} (x : RatFunc K)
    (f : ∀ (p q : K[X]) (hq : q ≠ 0), P (algebraMap _ (RatFunc K) p / algebraMap _ _ q)) : P x :=
  x.induction_on' fun p q hq => by simpa using f p q hq
#align ratfunc.induction_on RatFunc.induction_on

theorem ofFractionRing_mk' (x : K[X]) (y : K[X]⁰) :
    -- Porting note: I gave explicitly the argument `(FractionRing K[X])`
    ofFractionRing (IsLocalization.mk' (FractionRing K[X]) x y) =
      IsLocalization.mk' (RatFunc K) x y := by
  rw [IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div, ← mk_eq_div', ← mk_eq_div]
#align ratfunc.of_fraction_ring_mk' RatFunc.ofFractionRing_mk'

@[simp]
theorem ofFractionRing_eq :
    (ofFractionRing : FractionRing K[X] → RatFunc K) = IsLocalization.algEquiv K[X]⁰ _ _ :=
  funext fun x =>
    Localization.induction_on x fun x => by
      simp only [IsLocalization.algEquiv_apply, IsLocalization.ringEquivOfRingEquiv_apply,
        Localization.mk_eq_mk'_apply, IsLocalization.map_mk', ofFractionRing_mk',
        RingEquiv.coe_toRingHom, RingEquiv.refl_apply, SetLike.eta]
      -- Porting note: added following `simp`.  The previous one can be squeezed.
      simp only [IsFractionRing.mk'_eq_div, RingHom.id_apply, Subtype.coe_eta]
#align ratfunc.of_fraction_ring_eq RatFunc.ofFractionRing_eq

@[simp]
theorem toFractionRing_eq :
    (toFractionRing : RatFunc K → FractionRing K[X]) = IsLocalization.algEquiv K[X]⁰ _ _ :=
  funext fun ⟨x⟩ =>
    Localization.induction_on x fun x => by
      simp only [Localization.mk_eq_mk'_apply, ofFractionRing_mk', IsLocalization.algEquiv_apply,
        IsLocalization.ringEquivOfRingEquiv_apply, IsLocalization.map_mk',
        RingEquiv.coe_toRingHom, RingEquiv.refl_apply, SetLike.eta]
      -- Porting note: added following `simp`.  The previous one can be squeezed.
      simp only [IsFractionRing.mk'_eq_div, RingHom.id_apply, Subtype.coe_eta]
#align ratfunc.to_fraction_ring_eq RatFunc.toFractionRing_eq

@[simp]
theorem toFractionRingRingEquiv_symm_eq :
    (toFractionRingRingEquiv K).symm = (IsLocalization.algEquiv K[X]⁰ _ _).toRingEquiv := by
  ext x
  simp [toFractionRingRingEquiv, ofFractionRing_eq, AlgEquiv.coe_ringEquiv']
#align ratfunc.to_fraction_ring_ring_equiv_symm_eq RatFunc.toFractionRingRingEquiv_symm_eq

end IsDomain

end IsFractionRing

end CommRing

section NumDenom

/-! ### Numerator and denominator -/

open GCDMonoid Polynomial

variable [Field K]

set_option tactic.skipAssignedInstances false in
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
      dsimp
      rw [if_neg hq, if_neg (mul_ne_zero ha hq)]
      have ha' : a.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr ha
      have hainv : a.leadingCoeff⁻¹ ≠ 0 := inv_ne_zero ha'
      simp only [Prod.ext_iff, gcd_mul_left, normalize_apply, Polynomial.coe_normUnit, mul_assoc,
        CommGroupWithZero.coe_normUnit _ ha']
      have hdeg : (gcd p q).degree ≤ q.degree := degree_gcd_le_right _ hq
      have hdeg' : (Polynomial.C a.leadingCoeff⁻¹ * gcd p q).degree ≤ q.degree := by
        rw [Polynomial.degree_mul, Polynomial.degree_C hainv, zero_add]
        exact hdeg
      have hdivp : Polynomial.C a.leadingCoeff⁻¹ * gcd p q ∣ p :=
        (C_mul_dvd hainv).mpr (gcd_dvd_left p q)
      have hdivq : Polynomial.C a.leadingCoeff⁻¹ * gcd p q ∣ q :=
        (C_mul_dvd hainv).mpr (gcd_dvd_right p q)
      -- Porting note: added `simp only [...]` and `rw [mul_assoc]`
      -- Porting note: note the unfolding of `normalize` and `normUnit`!
      simp only [normalize, normUnit, coe_normUnit, leadingCoeff_eq_zero, MonoidWithZeroHom.coe_mk,
        ZeroHom.coe_mk, ha, dite_false, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [mul_assoc]
      rw [EuclideanDomain.mul_div_mul_cancel ha hdivp, EuclideanDomain.mul_div_mul_cancel ha hdivq,
        leadingCoeff_div hdeg, leadingCoeff_div hdeg', Polynomial.leadingCoeff_mul,
        Polynomial.leadingCoeff_C, div_C_mul, div_C_mul, ← mul_assoc, ← Polynomial.C_mul, ←
        mul_assoc, ← Polynomial.C_mul]
      constructor <;> congr <;>
        rw [inv_div, mul_comm, mul_div_assoc, ← mul_assoc, inv_inv, _root_.mul_inv_cancel ha',
          one_mul, inv_div])
#align ratfunc.num_denom RatFunc.numDenom

@[simp]
theorem numDenom_div (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    numDenom (algebraMap _ _ p / algebraMap _ _ q) =
      (Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q),
        Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (q / gcd p q)) := by
  rw [numDenom, liftOn'_div, if_neg hq]
  intro p
  rw [if_pos rfl, if_neg (one_ne_zero' K[X])]
  simp
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

@[simp]
theorem num_zero : num (0 : RatFunc K) = 0 := by convert num_div' (0 : K[X]) one_ne_zero <;> simp
#align ratfunc.num_zero RatFunc.num_zero

@[simp]
theorem num_div (p q : K[X]) :
    num (algebraMap _ _ p / algebraMap _ _ q) =
      Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q) := by
  by_cases hq : q = 0
  · simp [hq]
  · exact num_div' p hq
#align ratfunc.num_div RatFunc.num_div

@[simp]
theorem num_one : num (1 : RatFunc K) = 1 := by convert num_div (1 : K[X]) 1 <;> simp
#align ratfunc.num_one RatFunc.num_one

@[simp]
theorem num_algebraMap (p : K[X]) : num (algebraMap _ _ p) = p := by convert num_div p 1 <;> simp
#align ratfunc.num_algebra_map RatFunc.num_algebraMap

theorem num_div_dvd (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    num (algebraMap _ _ p / algebraMap _ _ q) ∣ p := by
  rw [num_div _ q, C_mul_dvd]
  · exact EuclideanDomain.div_dvd_of_dvd (gcd_dvd_left p q)
  · simpa only [Ne, inv_eq_zero, Polynomial.leadingCoeff_eq_zero] using right_div_gcd_ne_zero hq
#align ratfunc.num_div_dvd RatFunc.num_div_dvd

/-- A version of `num_div_dvd` with the LHS in simp normal form -/
@[simp]
theorem num_div_dvd' (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q) ∣ p := by simpa using num_div_dvd p hq
#align ratfunc.num_div_dvd' RatFunc.num_div_dvd'

/-- `RatFunc.denom` is the denominator of a rational function,
normalized such that it is monic. -/
def denom (x : RatFunc K) : K[X] :=
  x.numDenom.2
#align ratfunc.denom RatFunc.denom

@[simp]
theorem denom_div (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    denom (algebraMap _ _ p / algebraMap _ _ q) =
      Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (q / gcd p q) := by
  rw [denom, numDenom_div _ hq]
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
#align ratfunc.denom_zero RatFunc.denom_zero

@[simp]
theorem denom_one : denom (1 : RatFunc K) = 1 := by
  convert denom_div (1 : K[X]) one_ne_zero <;> simp
#align ratfunc.denom_one RatFunc.denom_one

@[simp]
theorem denom_algebraMap (p : K[X]) : denom (algebraMap _ (RatFunc K) p) = 1 := by
  convert denom_div p one_ne_zero <;> simp
#align ratfunc.denom_algebra_map RatFunc.denom_algebraMap

@[simp]
theorem denom_div_dvd (p q : K[X]) : denom (algebraMap _ _ p / algebraMap _ _ q) ∣ q := by
  by_cases hq : q = 0
  · simp [hq]
  rw [denom_div _ hq, C_mul_dvd]
  · exact EuclideanDomain.div_dvd_of_dvd (gcd_dvd_right p q)
  · simpa only [Ne, inv_eq_zero, Polynomial.leadingCoeff_eq_zero] using right_div_gcd_ne_zero hq
#align ratfunc.denom_div_dvd RatFunc.denom_div_dvd

@[simp]
theorem num_div_denom (x : RatFunc K) : algebraMap _ _ (num x) / algebraMap _ _ (denom x) = x := by
  induction' x using RatFunc.induction_on with p q hq
  -- Porting note: had to hint the type of this `have`
  have q_div_ne_zero : q / gcd p q ≠ 0 := right_div_gcd_ne_zero hq
  rw [num_div p q, denom_div p hq, RingHom.map_mul, RingHom.map_mul, mul_div_mul_left,
    div_eq_div_iff, ← RingHom.map_mul, ← RingHom.map_mul, mul_comm _ q, ←
    EuclideanDomain.mul_div_assoc, ← EuclideanDomain.mul_div_assoc, mul_comm]
  · apply gcd_dvd_right
  · apply gcd_dvd_left
  · exact algebraMap_ne_zero q_div_ne_zero
  · exact algebraMap_ne_zero hq
  · refine algebraMap_ne_zero (mt Polynomial.C_eq_zero.mp ?_)
    exact inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr q_div_ne_zero)
#align ratfunc.num_div_denom RatFunc.num_div_denom

theorem isCoprime_num_denom (x : RatFunc K) : IsCoprime x.num x.denom := by
  induction' x using RatFunc.induction_on with p q hq
  rw [num_div, denom_div _ hq]
  exact (isCoprime_mul_unit_left
    ((leadingCoeff_ne_zero.2 <| right_div_gcd_ne_zero hq).isUnit.inv.map C) _ _).2
      (isCoprime_div_gcd_div_gcd hq)
#align ratfunc.is_coprime_num_denom RatFunc.isCoprime_num_denom

@[simp]
theorem num_eq_zero_iff {x : RatFunc K} : num x = 0 ↔ x = 0 :=
  ⟨fun h => by rw [← num_div_denom x, h, RingHom.map_zero, zero_div], fun h => h.symm ▸ num_zero⟩
#align ratfunc.num_eq_zero_iff RatFunc.num_eq_zero_iff

theorem num_ne_zero {x : RatFunc K} (hx : x ≠ 0) : num x ≠ 0 :=
  mt num_eq_zero_iff.mp hx
#align ratfunc.num_ne_zero RatFunc.num_ne_zero

theorem num_mul_eq_mul_denom_iff {x : RatFunc K} {p q : K[X]} (hq : q ≠ 0) :
    x.num * q = p * x.denom ↔ x = algebraMap _ _ p / algebraMap _ _ q := by
  rw [← (algebraMap_injective K).eq_iff, eq_div_iff (algebraMap_ne_zero hq)]
  conv_rhs => rw [← num_div_denom x]
  rw [RingHom.map_mul, RingHom.map_mul, div_eq_mul_inv, mul_assoc, mul_comm (Inv.inv _), ←
    mul_assoc, ← div_eq_mul_inv, div_eq_iff]
  exact algebraMap_ne_zero (denom_ne_zero x)
#align ratfunc.num_mul_eq_mul_denom_iff RatFunc.num_mul_eq_mul_denom_iff

theorem num_denom_add (x y : RatFunc K) :
    (x + y).num * (x.denom * y.denom) = (x.num * y.denom + x.denom * y.num) * (x + y).denom :=
  (num_mul_eq_mul_denom_iff (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))).mpr <| by
    conv_lhs => rw [← num_div_denom x, ← num_div_denom y]
    rw [div_add_div, RingHom.map_mul, RingHom.map_add, RingHom.map_mul, RingHom.map_mul]
    · exact algebraMap_ne_zero (denom_ne_zero x)
    · exact algebraMap_ne_zero (denom_ne_zero y)
#align ratfunc.num_denom_add RatFunc.num_denom_add

theorem num_denom_neg (x : RatFunc K) : (-x).num * x.denom = -x.num * (-x).denom := by
  rw [num_mul_eq_mul_denom_iff (denom_ne_zero x), _root_.map_neg, neg_div, num_div_denom]
#align ratfunc.num_denom_neg RatFunc.num_denom_neg

theorem num_denom_mul (x y : RatFunc K) :
    (x * y).num * (x.denom * y.denom) = x.num * y.num * (x * y).denom :=
  (num_mul_eq_mul_denom_iff (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))).mpr <| by
    conv_lhs =>
      rw [← num_div_denom x, ← num_div_denom y, div_mul_div_comm, ← RingHom.map_mul, ←
        RingHom.map_mul]
#align ratfunc.num_denom_mul RatFunc.num_denom_mul

theorem num_dvd {x : RatFunc K} {p : K[X]} (hp : p ≠ 0) :
    num x ∣ p ↔ ∃ q : K[X], q ≠ 0 ∧ x = algebraMap _ _ p / algebraMap _ _ q := by
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨_hx, hq⟩ := mul_ne_zero_iff.mp hp
    use denom x * q
    rw [RingHom.map_mul, RingHom.map_mul, ← div_mul_div_comm, div_self, mul_one, num_div_denom]
    · exact ⟨mul_ne_zero (denom_ne_zero x) hq, rfl⟩
    · exact algebraMap_ne_zero hq
  · rintro ⟨q, hq, rfl⟩
    exact num_div_dvd p hq
#align ratfunc.num_dvd RatFunc.num_dvd

theorem denom_dvd {x : RatFunc K} {q : K[X]} (hq : q ≠ 0) :
    denom x ∣ q ↔ ∃ p : K[X], x = algebraMap _ _ p / algebraMap _ _ q := by
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨_hx, hp⟩ := mul_ne_zero_iff.mp hq
    use num x * p
    rw [RingHom.map_mul, RingHom.map_mul, ← div_mul_div_comm, div_self, mul_one, num_div_denom]
    exact algebraMap_ne_zero hp
  · rintro ⟨p, rfl⟩
    exact denom_div_dvd p q
#align ratfunc.denom_dvd RatFunc.denom_dvd

theorem num_mul_dvd (x y : RatFunc K) : num (x * y) ∣ num x * num y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [num_dvd (mul_ne_zero (num_ne_zero hx) (num_ne_zero hy))]
  refine ⟨x.denom * y.denom, mul_ne_zero (denom_ne_zero x) (denom_ne_zero y), ?_⟩
  rw [RingHom.map_mul, RingHom.map_mul, ← div_mul_div_comm, num_div_denom, num_div_denom]
#align ratfunc.num_mul_dvd RatFunc.num_mul_dvd

theorem denom_mul_dvd (x y : RatFunc K) : denom (x * y) ∣ denom x * denom y := by
  rw [denom_dvd (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))]
  refine ⟨x.num * y.num, ?_⟩
  rw [RingHom.map_mul, RingHom.map_mul, ← div_mul_div_comm, num_div_denom, num_div_denom]
#align ratfunc.denom_mul_dvd RatFunc.denom_mul_dvd

theorem denom_add_dvd (x y : RatFunc K) : denom (x + y) ∣ denom x * denom y := by
  rw [denom_dvd (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))]
  refine ⟨x.num * y.denom + x.denom * y.num, ?_⟩
  rw [RingHom.map_mul, RingHom.map_add, RingHom.map_mul, RingHom.map_mul, ← div_add_div,
    num_div_denom, num_div_denom]
  · exact algebraMap_ne_zero (denom_ne_zero x)
  · exact algebraMap_ne_zero (denom_ne_zero y)
#align ratfunc.denom_add_dvd RatFunc.denom_add_dvd

theorem map_denom_ne_zero {L F : Type*} [Zero L] [FunLike F K[X] L] [ZeroHomClass F K[X] L]
    (φ : F) (hφ : Function.Injective φ) (f : RatFunc K) : φ f.denom ≠ 0 := fun H =>
  (denom_ne_zero f) ((map_eq_zero_iff φ hφ).mp H)
#align ratfunc.map_denom_ne_zero RatFunc.map_denom_ne_zero

theorem map_apply {R F : Type*} [CommRing R] [IsDomain R]
    [FunLike F K[X] R[X]] [MonoidHomClass F K[X] R[X]] (φ : F)
    (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) (f : RatFunc K) :
    map φ hφ f = algebraMap _ _ (φ f.num) / algebraMap _ _ (φ f.denom) := by
  rw [← num_div_denom f, map_apply_div_ne_zero, num_div_denom f]
  exact denom_ne_zero _
#align ratfunc.map_apply RatFunc.map_apply

theorem liftMonoidWithZeroHom_apply {L : Type*} [CommGroupWithZero L] (φ : K[X] →*₀ L)
    (hφ : K[X]⁰ ≤ L⁰.comap φ) (f : RatFunc K) :
    liftMonoidWithZeroHom φ hφ f = φ f.num / φ f.denom := by
  rw [← num_div_denom f, liftMonoidWithZeroHom_apply_div, num_div_denom]
#align ratfunc.lift_monoid_with_zero_hom_apply RatFunc.liftMonoidWithZeroHom_apply

theorem liftRingHom_apply {L : Type*} [Field L] (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ)
    (f : RatFunc K) : liftRingHom φ hφ f = φ f.num / φ f.denom :=
  liftMonoidWithZeroHom_apply _ hφ _  -- Porting note: added explicit `hφ`
#align ratfunc.lift_ring_hom_apply RatFunc.liftRingHom_apply

theorem liftAlgHom_apply {L S : Type*} [Field L] [CommSemiring S] [Algebra S K[X]] [Algebra S L]
    (φ : K[X] →ₐ[S] L) (hφ : K[X]⁰ ≤ L⁰.comap φ) (f : RatFunc K) :
    liftAlgHom φ hφ f = φ f.num / φ f.denom :=
  liftMonoidWithZeroHom_apply _ hφ _  -- Porting note: added explicit `hφ`
#align ratfunc.lift_alg_hom_apply RatFunc.liftAlgHom_apply

theorem num_mul_denom_add_denom_mul_num_ne_zero {x y : RatFunc K} (hxy : x + y ≠ 0) :
    x.num * y.denom + x.denom * y.num ≠ 0 := by
  intro h_zero
  have h := num_denom_add x y
  rw [h_zero, zero_mul] at h
  exact (mul_ne_zero (num_ne_zero hxy) (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)) h
#align ratfunc.num_mul_denom_add_denom_mul_num_ne_zero RatFunc.num_mul_denom_add_denom_mul_num_ne_zero

end NumDenom
