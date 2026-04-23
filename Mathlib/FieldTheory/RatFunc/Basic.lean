/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.RatFunc.Defs
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# The field structure of rational functions

## Main definitions
Working with rational functions as polynomials:
- `RatFunc.instField` provides a field structure

You can use `IsFractionRing` API to treat `RatFunc` as the field of fractions of polynomials:
* `algebraMap K[X] K⟮X⟯` maps polynomials to rational functions
* `IsFractionRing.algEquiv` maps other fields of fractions of `K[X]` to `K⟮X⟯`.

In particular:
* `FractionRing.algEquiv K[X] K⟮X⟯` maps the generic field of
  fraction construction to `K⟮X⟯`. Combine this with `AlgEquiv.restrictScalars` to change
  the `FractionRing K[X] ≃ₐ[K[X]] K⟮X⟯` to `FractionRing K[X] ≃ₐ[K] K⟮X⟯`.

Working with rational functions as fractions:
- `RatFunc.num` and `RatFunc.denom` give the numerator and denominator.
  These values are chosen to be coprime and such that `RatFunc.denom` is monic.

Lifting homomorphisms of polynomials to other types, by mapping and dividing, as long
as the homomorphism retains the non-zero-divisor property:
- `RatFunc.liftMonoidWithZeroHom` lifts a `K[X] →*₀ G₀` to
  a `K⟮X⟯ →*₀ G₀`, where `[CommRing K] [CommGroupWithZero G₀]`
- `RatFunc.liftRingHom` lifts a `K[X] →+* L` to a `K⟮X⟯ →+* L`,
  where `[CommRing K] [Field L]`
- `RatFunc.liftAlgHom` lifts a `K[X] →ₐ[S] L` to a `K⟮X⟯ →ₐ[S] L`,
  where `[CommRing K] [Field L] [CommSemiring S] [Algebra S K[X]] [Algebra S L]`

This is satisfied by injective homs.

We also have lifting homomorphisms of polynomials to other polynomials,
with the same condition on retaining the non-zero-divisor property across the map:
- `RatFunc.map` lifts `K[X] →* R[X]` when `[CommRing K] [CommRing R]`
- `RatFunc.mapRingHom` lifts `K[X] →+* R[X]` when `[CommRing K] [CommRing R]`
- `RatFunc.mapAlgHom` lifts `K[X] →ₐ[S] R[X]` when
  `[CommRing K] [IsDomain K] [CommRing R] [IsDomain R]`
-/

@[expose] public section

universe u v

noncomputable section

open scoped nonZeroDivisors Polynomial

variable {K : Type u}

namespace RatFunc

section Field

variable [CommRing K]

/-- The zero rational function. -/
protected irreducible_def zero : K⟮X⟯ :=
  ⟨0⟩

instance : Zero K⟮X⟯ :=
  ⟨RatFunc.zero⟩

theorem ofFractionRing_zero : (ofFractionRing 0 : K⟮X⟯) = 0 :=
  zero_def.symm

/-- Addition of rational functions. -/
protected irreducible_def add : K⟮X⟯ → K⟮X⟯ → K⟮X⟯
  | ⟨p⟩, ⟨q⟩ => ⟨p + q⟩

instance : Add K⟮X⟯ :=
  ⟨RatFunc.add⟩

theorem ofFractionRing_add (p q : FractionRing K[X]) :
    ofFractionRing (p + q) = ofFractionRing p + ofFractionRing q :=
  (add_def _ _).symm

/-- Subtraction of rational functions. -/
protected irreducible_def sub : K⟮X⟯ → K⟮X⟯ → K⟮X⟯
  | ⟨p⟩, ⟨q⟩ => ⟨p - q⟩

instance : Sub K⟮X⟯ :=
  ⟨RatFunc.sub⟩

theorem ofFractionRing_sub (p q : FractionRing K[X]) :
    ofFractionRing (p - q) = ofFractionRing p - ofFractionRing q :=
  (sub_def _ _).symm

/-- Additive inverse of a rational function. -/
protected irreducible_def neg : K⟮X⟯ → K⟮X⟯
  | ⟨p⟩ => ⟨-p⟩

instance : Neg K⟮X⟯ :=
  ⟨RatFunc.neg⟩

theorem ofFractionRing_neg (p : FractionRing K[X]) :
    ofFractionRing (-p) = -ofFractionRing p :=
  (neg_def _).symm

/-- The multiplicative unit of rational functions. -/
protected irreducible_def one : K⟮X⟯ :=
  ⟨1⟩

instance : One K⟮X⟯ :=
  ⟨RatFunc.one⟩

theorem ofFractionRing_one : (ofFractionRing 1 : K⟮X⟯) = 1 :=
  one_def.symm

/-- Multiplication of rational functions. -/
protected irreducible_def mul : K⟮X⟯ → K⟮X⟯ → K⟮X⟯
  | ⟨p⟩, ⟨q⟩ => ⟨p * q⟩

instance : Mul K⟮X⟯ :=
  ⟨RatFunc.mul⟩

theorem ofFractionRing_mul (p q : FractionRing K[X]) :
    ofFractionRing (p * q) = ofFractionRing p * ofFractionRing q :=
  (mul_def _ _).symm

section IsDomain

variable [IsDomain K]

/-- Division of rational functions. -/
protected irreducible_def div : K⟮X⟯ → K⟮X⟯ → K⟮X⟯
  | ⟨p⟩, ⟨q⟩ => ⟨p / q⟩

instance : Div K⟮X⟯ :=
  ⟨RatFunc.div⟩

theorem ofFractionRing_div (p q : FractionRing K[X]) :
    ofFractionRing (p / q) = ofFractionRing p / ofFractionRing q :=
  (div_def _ _).symm

/-- Multiplicative inverse of a rational function. -/
protected irreducible_def inv : K⟮X⟯ → K⟮X⟯
  | ⟨p⟩ => ⟨p⁻¹⟩

instance : Inv K⟮X⟯ :=
  ⟨RatFunc.inv⟩

theorem ofFractionRing_inv (p : FractionRing K[X]) :
    ofFractionRing p⁻¹ = (ofFractionRing p)⁻¹ :=
  (inv_def _).symm

-- Auxiliary lemma for the `Field` instance
theorem mul_inv_cancel : ∀ {p : K⟮X⟯}, p ≠ 0 → p * p⁻¹ = 1
  | ⟨p⟩, h => by
    have : p ≠ 0 := fun hp => h <| by rw [hp, ofFractionRing_zero]
    simpa only [← ofFractionRing_inv, ← ofFractionRing_mul, ← ofFractionRing_one,
        ofFractionRing.injEq] using
      mul_inv_cancel₀ this

end IsDomain

section SMul

variable {R : Type*}

/-- Scalar multiplication of rational functions. -/
protected irreducible_def smul [SMul R (FractionRing K[X])] : R → K⟮X⟯ → K⟮X⟯
  | r, ⟨p⟩ => ⟨r • p⟩

instance [SMul R (FractionRing K[X])] : SMul R K⟮X⟯ :=
  ⟨RatFunc.smul⟩

theorem ofFractionRing_smul [SMul R (FractionRing K[X])] (c : R) (p : FractionRing K[X]) :
    ofFractionRing (c • p) = c • ofFractionRing p :=
  (smul_def _ _).symm

theorem toFractionRing_smul [SMul R (FractionRing K[X])] (c : R) (p : K⟮X⟯) :
    toFractionRing (c • p) = c • toFractionRing p := by
  cases p
  rw [← ofFractionRing_smul]

theorem smul_eq_C_smul (x : K⟮X⟯) (r : K) : r • x = Polynomial.C r • x := by
  obtain ⟨x⟩ := x
  induction x using Localization.induction_on
  rw [← ofFractionRing_smul, ← ofFractionRing_smul, Localization.smul_mk,
    Localization.smul_mk, smul_eq_mul, Polynomial.smul_eq_C_mul]

section IsDomain

variable [IsDomain K]
variable [Monoid R] [DistribMulAction R K[X]]
variable [IsScalarTower R K[X] K[X]]

theorem mk_smul (c : R) (p q : K[X]) : RatFunc.mk (c • p) q = c • RatFunc.mk p q := by
  letI : SMulZeroClass R (FractionRing K[X]) := inferInstance
  by_cases hq : q = 0
  · rw [hq, mk_zero, mk_zero, ← ofFractionRing_smul, smul_zero]
  · rw [mk_eq_localization_mk _ hq, mk_eq_localization_mk _ hq, ← Localization.smul_mk, ←
      ofFractionRing_smul]

instance : IsScalarTower R K[X] K⟮X⟯ :=
  ⟨fun c p q => q.induction_on' fun q r _ => by rw [← mk_smul, smul_assoc, mk_smul, mk_smul]⟩

end IsDomain

end SMul

variable (K)

instance [Subsingleton K] : Subsingleton K⟮X⟯ :=
  toFractionRing_injective.subsingleton

instance : Inhabited K⟮X⟯ :=
  ⟨0⟩

instance instNontrivial [Nontrivial K] : Nontrivial K⟮X⟯ :=
  ofFractionRing_injective.nontrivial

/-- `K⟮X⟯` is isomorphic to the field of fractions of `K[X]`, as rings.

This is an auxiliary definition; `simp`-normal form is `IsLocalization.algEquiv`.
-/
@[simps apply]
def toFractionRingRingEquiv : K⟮X⟯ ≃+* FractionRing K[X] where
  toFun := toFractionRing
  invFun := ofFractionRing
  map_add' := fun ⟨_⟩ ⟨_⟩ => by simp [← ofFractionRing_add]
  map_mul' := fun ⟨_⟩ ⟨_⟩ => by simp [← ofFractionRing_mul]

end Field

section TacticInterlude

/-- Solve equations for `K⟮X⟯` by working in `FractionRing K[X]`. -/
macro "frac_tac" : tactic => `(tactic|
  · repeat (rintro (⟨⟩ : _⟮X⟯))
    try simp only [← ofFractionRing_zero, ← ofFractionRing_add, ← ofFractionRing_sub,
      ← ofFractionRing_neg, ← ofFractionRing_one, ← ofFractionRing_mul, ← ofFractionRing_div,
      ← ofFractionRing_inv,
      add_assoc, zero_add, add_zero, mul_assoc, mul_zero, mul_one, mul_add, inv_zero,
      add_comm, add_left_comm, mul_comm, mul_left_comm, sub_eq_add_neg, div_eq_mul_inv,
      add_mul, zero_mul, one_mul, neg_mul, mul_neg, add_neg_cancel])

/-- Solve equations for `K⟮X⟯` by applying `RatFunc.induction_on`. -/
macro "smul_tac" : tactic => `(tactic|
    repeat
      (first
        | rintro (⟨⟩ : _⟮X⟯)
        | intro) <;>
    simp_rw [← ofFractionRing_smul] <;>
    simp only [add_comm, mul_comm, zero_smul, succ_nsmul, zsmul_eq_mul, mul_add, mul_one, mul_zero,
      neg_add, mul_neg,
      Int.cast_zero, Int.cast_add, Int.cast_one,
      Int.cast_negSucc, Int.cast_natCast, Nat.cast_succ,
      Localization.mk_zero, Localization.add_mk_self, Localization.neg_mk,
      ofFractionRing_zero, ← ofFractionRing_add, ← ofFractionRing_neg])

end TacticInterlude

section CommRing

variable (K) [CommRing K]
/-- `K⟮X⟯` is a commutative monoid.

This is an intermediate step on the way to the full instance `RatFunc.instCommRing`.
-/
@[implicit_reducible]
def instCommMonoid : CommMonoid K⟮X⟯ where
  mul_assoc := by frac_tac
  mul_comm := by frac_tac
  one_mul := by frac_tac
  mul_one := by frac_tac
  npow := npowRec

/-- `K⟮X⟯` is an additive commutative group.

This is an intermediate step on the way to the full instance `RatFunc.instCommRing`.
-/
@[implicit_reducible]
def instAddCommGroup : AddCommGroup K⟮X⟯ where
  add_assoc := by frac_tac
  add_comm := by frac_tac
  zero_add := by frac_tac
  add_zero := by frac_tac
  neg_add_cancel := by frac_tac
  sub_eq_add_neg := by frac_tac
  nsmul := (· • ·)
  nsmul_zero := by smul_tac
  nsmul_succ _ := by smul_tac
  zsmul := (· • ·)
  zsmul_zero' := by smul_tac
  zsmul_succ' _ := by smul_tac
  zsmul_neg' _ := by smul_tac

instance instCommRing : CommRing K⟮X⟯ :=
  { instCommMonoid K, instAddCommGroup K with
    zero_mul := by frac_tac
    mul_zero := by frac_tac
    left_distrib := by frac_tac
    right_distrib := by frac_tac
    npow := npowRec }

variable {K}

section LiftHom

open RatFunc

variable {G₀ L R S F : Type*} [CommGroupWithZero G₀] [Field L] [CommRing R] [CommRing S]
variable [FunLike F R[X] S[X]]

open scoped Classical in
/-- Lift a monoid homomorphism that maps polynomials `φ : R[X] →* S[X]`
to a `R⟮X⟯ →* S⟮X⟯`,
on the condition that `φ` maps non-zero-divisors to non-zero-divisors,
by mapping both the numerator and denominator and quotienting them. -/
def map [MonoidHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) :
    R⟮X⟯ →* S⟮X⟯ where
  toFun f :=
    RatFunc.liftOn f
      (fun n d => if h : φ d ∈ S[X]⁰ then ofFractionRing (Localization.mk (φ n) ⟨φ d, h⟩) else 0)
      fun {p q p' q'} hq hq' h => by
      simp only [Submonoid.mem_comap.mp (hφ hq), Submonoid.mem_comap.mp (hφ hq'),
        dif_pos, ofFractionRing.injEq, Localization.mk_eq_mk_iff]
      refine Localization.r_of_eq ?_
      simpa only [map_mul] using congr_arg φ h
  map_one' := by
    simp_rw [← ofFractionRing_one, ← Localization.mk_one, liftOn_ofFractionRing_mk,
      OneMemClass.coe_one, map_one, OneMemClass.one_mem, dite_true, ofFractionRing.injEq,
      Localization.mk_one, Localization.mk_eq_monoidOf_mk', Submonoid.LocalizationMap.mk'_self]
  map_mul' x y := by
    obtain ⟨x⟩ := x; obtain ⟨y⟩ := y
    cases x using Localization.induction_on with | _ pq
    cases y using Localization.induction_on with | _ p'q'
    obtain ⟨p, q⟩ := pq
    obtain ⟨p', q'⟩ := p'q'
    have hq : φ q ∈ S[X]⁰ := hφ q.prop
    have hq' : φ q' ∈ S[X]⁰ := hφ q'.prop
    have hqq' : φ ↑(q * q') ∈ S[X]⁰ := by simpa using Submonoid.mul_mem _ hq hq'
    simp_rw [← ofFractionRing_mul, Localization.mk_mul, liftOn_ofFractionRing_mk, dif_pos hq,
      dif_pos hq', dif_pos hqq', ← ofFractionRing_mul, Submonoid.coe_mul, map_mul,
      Localization.mk_mul, Submonoid.mk_mul_mk]

theorem map_apply_ofFractionRing_mk [MonoidHomClass F R[X] S[X]] (φ : F)
    (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) (n : R[X]) (d : R[X]⁰) :
    map φ hφ (ofFractionRing (Localization.mk n d)) =
      ofFractionRing (Localization.mk (φ n) ⟨φ d, hφ d.prop⟩) := by
  simp only [map, MonoidHom.coe_mk, OneHom.coe_mk, liftOn_ofFractionRing_mk,
    Submonoid.mem_comap.mp (hφ d.2), ↓reduceDIte]

theorem map_injective [MonoidHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ ≤ S[X]⁰.comap φ)
    (hf : Function.Injective φ) : Function.Injective (map φ hφ) := by
  rintro ⟨x⟩ ⟨y⟩ h
  induction x using Localization.induction_on
  induction y using Localization.induction_on
  simpa only [map_apply_ofFractionRing_mk, ofFractionRing_injective.eq_iff,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists, mul_cancel_left_coe_nonZeroDivisors,
    exists_const, ← map_mul, hf.eq_iff] using h

/-- Lift a ring homomorphism that maps polynomials `φ : R[X] →+* S[X]`
to a `R⟮X⟯ →+* S⟮X⟯`,
on the condition that `φ` maps non-zero-divisors to non-zero-divisors,
by mapping both the numerator and denominator and quotienting them. -/
def mapRingHom [RingHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) :
    R⟮X⟯ →+* S⟮X⟯ :=
  { map φ hφ with
    map_zero' := by
      simp_rw [MonoidHom.toFun_eq_coe, ← ofFractionRing_zero, ← Localization.mk_zero (1 : R[X]⁰),
        ← Localization.mk_zero (1 : S[X]⁰), map_apply_ofFractionRing_mk, map_zero,
        Localization.mk_eq_mk', IsLocalization.mk'_zero]
    map_add' := by
      rintro ⟨x⟩ ⟨y⟩
      induction x using Localization.induction_on
      induction y using Localization.induction_on
      · simp only [← ofFractionRing_add, Localization.add_mk, map_add, map_mul,
          MonoidHom.toFun_eq_coe, map_apply_ofFractionRing_mk, Submonoid.coe_mul,
          -- We have to specify `S[X]⁰` to `mk_mul_mk`, otherwise it will try to rewrite
          -- the wrong occurrence.
          Submonoid.mk_mul_mk S[X]⁰] }

theorem coe_mapRingHom_eq_coe_map [RingHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) :
    (mapRingHom φ hφ : R⟮X⟯ → S⟮X⟯) = map φ hφ :=
  rfl

-- TODO: Generalize to `FunLike` classes,
/-- Lift a monoid with zero homomorphism `R[X] →*₀ G₀` to a `R⟮X⟯ →*₀ G₀`
on the condition that `φ` maps non-zero-divisors to non-zero-divisors,
by mapping both the numerator and denominator and quotienting them. -/
def liftMonoidWithZeroHom (φ : R[X] →*₀ G₀) (hφ : R[X]⁰ ≤ G₀⁰.comap φ) : R⟮X⟯ →*₀ G₀ where
  toFun f :=
    RatFunc.liftOn f (fun p q => φ p / φ q) fun {p q p' q'} hq hq' h => by
      cases subsingleton_or_nontrivial R
      · rw [Subsingleton.elim p q, Subsingleton.elim p' q, Subsingleton.elim q' q]
      rw [div_eq_div_iff, ← map_mul, mul_comm p, h, map_mul, mul_comm] <;>
        exact nonZeroDivisors.ne_zero (hφ ‹_›)
  map_one' := by
    simp_rw [← ofFractionRing_one, ← Localization.mk_one, liftOn_ofFractionRing_mk,
      OneMemClass.coe_one, map_one, div_one]
  map_mul' x y := by
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    cases x using Localization.induction_on
    cases y using Localization.induction_on
    rw [← ofFractionRing_mul, Localization.mk_mul]
    simp only [liftOn_ofFractionRing_mk, div_mul_div_comm, map_mul, Submonoid.coe_mul]
  map_zero' := by
    simp_rw [← ofFractionRing_zero, ← Localization.mk_zero (1 : R[X]⁰), liftOn_ofFractionRing_mk,
      map_zero, zero_div]

theorem liftMonoidWithZeroHom_apply_ofFractionRing_mk (φ : R[X] →*₀ G₀) (hφ : R[X]⁰ ≤ G₀⁰.comap φ)
    (n : R[X]) (d : R[X]⁰) :
    liftMonoidWithZeroHom φ hφ (ofFractionRing (Localization.mk n d)) = φ n / φ d :=
  liftOn_ofFractionRing_mk _ _ _ _

theorem liftMonoidWithZeroHom_injective [Nontrivial R] (φ : R[X] →*₀ G₀) (hφ : Function.Injective φ)
    (hφ' : R[X]⁰ ≤ G₀⁰.comap φ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hφ) :
    Function.Injective (liftMonoidWithZeroHom φ hφ') := by
  rintro ⟨x⟩ ⟨y⟩
  cases x using Localization.induction_on
  cases y using Localization.induction_on with | _ a'
  simp_rw [liftMonoidWithZeroHom_apply_ofFractionRing_mk]
  intro h
  congr 1
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (M := R[X]) ?_)
  have := mul_eq_mul_of_div_eq_div _ _ ?_ ?_ h
  · rwa [← map_mul, ← map_mul, hφ.eq_iff, mul_comm, mul_comm a'.fst] at this
  all_goals exact map_ne_zero_of_mem_nonZeroDivisors _ hφ (SetLike.coe_mem _)

/-- Lift an injective ring homomorphism `R[X] →+* L` to a `R⟮X⟯ →+* L`
by mapping both the numerator and denominator and quotienting them. -/
def liftRingHom (φ : R[X] →+* L) (hφ : R[X]⁰ ≤ L⁰.comap φ) : R⟮X⟯ →+* L :=
  { liftMonoidWithZeroHom φ.toMonoidWithZeroHom hφ with
    map_add' := fun x y => by
      simp only [ZeroHom.toFun_eq_coe, MonoidWithZeroHom.toZeroHom_coe]
      cases subsingleton_or_nontrivial R
      · rw [Subsingleton.elim (x + y) y, Subsingleton.elim x 0, map_zero, zero_add]
      obtain ⟨x⟩ := x
      obtain ⟨y⟩ := y
      cases x using Localization.induction_on with | _ pq
      cases y using Localization.induction_on with | _ p'q'
      obtain ⟨p, q⟩ := pq
      obtain ⟨p', q'⟩ := p'q'
      rw [← ofFractionRing_add, Localization.add_mk]
      simp only [RingHom.toMonoidWithZeroHom_eq_coe,
        liftMonoidWithZeroHom_apply_ofFractionRing_mk]
      rw [div_add_div, div_eq_div_iff]
      · rw [mul_comm _ p, mul_comm _ p', mul_comm _ (φ p'), add_comm]
        simp only [map_add, map_mul, Submonoid.coe_mul]
      all_goals
        try simp only [← map_mul, ← Submonoid.coe_mul]
        exact nonZeroDivisors.ne_zero (hφ (SetLike.coe_mem _)) }

theorem liftRingHom_apply_ofFractionRing_mk (φ : R[X] →+* L) (hφ : R[X]⁰ ≤ L⁰.comap φ) (n : R[X])
    (d : R[X]⁰) : liftRingHom φ hφ (ofFractionRing (Localization.mk n d)) = φ n / φ d :=
  liftMonoidWithZeroHom_apply_ofFractionRing_mk _ hφ _ _

@[simp]
lemma liftRingHom_ofFractionRing_algebraMap
    (φ : R[X] →+* L) (hφ : R[X]⁰ ≤ L⁰.comap φ) (x : R[X]) :
    RatFunc.liftRingHom φ hφ (ofFractionRing <| algebraMap R[X] _ x) = φ x := by
  rw [← Localization.mk_one_eq_algebraMap, liftRingHom_apply_ofFractionRing_mk]
  simp

theorem liftRingHom_injective [Nontrivial R] (φ : R[X] →+* L) (hφ : Function.Injective φ)
    (hφ' : R[X]⁰ ≤ L⁰.comap φ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hφ) :
    Function.Injective (liftRingHom φ hφ') :=
  liftMonoidWithZeroHom_injective _ hφ

end LiftHom

variable (K)

@[stacks 09FK]
instance instField [IsDomain K] : Field K⟮X⟯ where
  inv_zero := by frac_tac
  div_eq_mul_inv := by frac_tac
  mul_inv_cancel _ := mul_inv_cancel
  zpow := zpowRec
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

section IsFractionRing

/-! ### `RatFunc` as field of fractions of `Polynomial` -/

section IsDomain

variable [IsDomain K]

instance (R : Type*) [CommSemiring R] [Algebra R K[X]] : Algebra R K⟮X⟯ where
  algebraMap :=
  { toFun x := RatFunc.mk (algebraMap _ _ x) 1
    map_add' x y := by simp only [mk_one', map_add, ofFractionRing_add]
    map_mul' x y := by simp only [mk_one', map_mul, ofFractionRing_mul]
    map_one' := by simp only [mk_one', map_one, ofFractionRing_one]
    map_zero' := by simp only [mk_one', map_zero, ofFractionRing_zero] }
  smul_def' c x := by
    induction x using RatFunc.induction_on' with | _ p q hq
    rw [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, mk_one', ← mk_smul,
      mk_def_of_ne (c • p) hq, mk_def_of_ne p hq, ← ofFractionRing_mul,
      IsLocalization.mul_mk'_eq_mk'_of_mul, Algebra.smul_def]
  commutes' _ _ := mul_comm _ _

variable {K}

/-- The coercion from polynomials to rational functions, implemented as the algebra map from a
domain to its field of fractions -/
@[coe]
def coePolynomial (P : Polynomial K) : K⟮X⟯ := algebraMap _ _ P

instance : Coe (Polynomial K) K⟮X⟯ := ⟨coePolynomial⟩

theorem mk_one (x : K[X]) : RatFunc.mk x 1 = algebraMap _ _ x :=
  rfl

theorem ofFractionRing_algebraMap (x : K[X]) :
    ofFractionRing (algebraMap _ (FractionRing K[X]) x) = algebraMap _ _ x := by
  rw [← mk_one, mk_one']

variable (K) in
/--
The equivalence between `K⟮X⟯` and the field of fractions of `K[X]`
-/
@[simps! apply]
def toFractionRingAlgEquiv (R : Type*) [CommSemiring R] [Algebra R K[X]] :
    K⟮X⟯ ≃ₐ[R] FractionRing K[X] where
  __ := RatFunc.toFractionRingRingEquiv K
  commutes' r := by
    change (RatFunc.mk (algebraMap R K[X] r) 1).toFractionRing = _
    rw [mk_one']; rfl

@[simp]
theorem mk_eq_div (p q : K[X]) : RatFunc.mk p q = algebraMap _ _ p / algebraMap _ _ q := by
  simp only [mk_eq_div', ofFractionRing_div, ofFractionRing_algebraMap]

@[simp]
theorem div_smul {R} [Monoid R] [DistribMulAction R K[X]] [IsScalarTower R K[X] K[X]] (c : R)
    (p q : K[X]) :
    algebraMap _ K⟮X⟯ (c • p) / algebraMap _ _ q =
      c • (algebraMap _ _ p / algebraMap _ _ q) := by
  rw [← mk_eq_div, mk_smul, mk_eq_div]

theorem algebraMap_apply {R : Type*} [CommSemiring R] [Algebra R K[X]] (x : R) :
    algebraMap R K⟮X⟯ x = algebraMap _ _ (algebraMap R K[X] x) / algebraMap K[X] _ 1 := by
  rw [← mk_eq_div]
  rfl

theorem map_apply_div_ne_zero {R F : Type*} [CommRing R] [IsDomain R]
    [FunLike F K[X] R[X]] [MonoidHomClass F K[X] R[X]]
    (φ : F) (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) (p q : K[X]) (hq : q ≠ 0) :
    map φ hφ (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap _ _ (φ p) / algebraMap _ _ (φ q) := by
  have hq' : φ q ≠ 0 := nonZeroDivisors.ne_zero (hφ (mem_nonZeroDivisors_iff_ne_zero.mpr hq))
  simp only [← mk_eq_div, mk_eq_localization_mk _ hq, map_apply_ofFractionRing_mk,
    mk_eq_localization_mk _ hq']

@[simp]
theorem map_apply_div {R F : Type*} [CommRing R] [IsDomain R]
    [FunLike F K[X] R[X]] [MonoidWithZeroHomClass F K[X] R[X]]
    (φ : F) (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) (p q : K[X]) :
    map φ hφ (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap _ _ (φ p) / algebraMap _ _ (φ q) := by
  rcases eq_or_ne q 0 with (rfl | hq)
  · have : (0 : K⟮X⟯) = algebraMap K[X] _ 0 / algebraMap K[X] _ 1 := by simp
    rw [map_zero, map_zero, map_zero, div_zero, div_zero, this, map_apply_div_ne_zero, map_one,
      map_one, div_one, map_zero, map_zero]
    exact one_ne_zero
  exact map_apply_div_ne_zero _ _ _ _ hq

theorem liftMonoidWithZeroHom_apply_div {L : Type*} [CommGroupWithZero L]
    (φ : MonoidWithZeroHom K[X] L) (hφ : K[X]⁰ ≤ L⁰.comap φ) (p q : K[X]) :
    liftMonoidWithZeroHom φ hφ (algebraMap _ _ p / algebraMap _ _ q) = φ p / φ q := by
  rcases eq_or_ne q 0 with (rfl | hq)
  · simp only [div_zero, map_zero]
  simp only [← mk_eq_div, mk_eq_localization_mk _ hq,
    liftMonoidWithZeroHom_apply_ofFractionRing_mk]

@[simp]
theorem liftMonoidWithZeroHom_apply_div' {L : Type*} [CommGroupWithZero L]
    (φ : MonoidWithZeroHom K[X] L) (hφ : K[X]⁰ ≤ L⁰.comap φ) (p q : K[X]) :
    liftMonoidWithZeroHom φ hφ (algebraMap _ _ p) / liftMonoidWithZeroHom φ hφ (algebraMap _ _ q) =
      φ p / φ q := by
  rw [← map_div₀, liftMonoidWithZeroHom_apply_div]

theorem liftRingHom_apply_div {L : Type*} [Field L] (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ)
    (p q : K[X]) : liftRingHom φ hφ (algebraMap _ _ p / algebraMap _ _ q) = φ p / φ q :=
  liftMonoidWithZeroHom_apply_div _ hφ _ _

theorem liftRingHom_apply_div' {L : Type*} [Field L] (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ)
    (p q : K[X]) : liftRingHom φ hφ (algebraMap _ _ p) / liftRingHom φ hφ (algebraMap _ _ q) =
      φ p / φ q :=
  liftMonoidWithZeroHom_apply_div' _ hφ _ _

@[simp]
lemma liftRingHom_algebraMap {L : Type*} [Field L] (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ)
    (x : K[X]) : liftRingHom φ hφ (algebraMap K[X] _ x) = φ x := by
  simpa using liftRingHom_apply_div' φ hφ x 1

@[simp]
lemma liftRingHom_comp_algebraMap {L : Type*} [Field L] (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ) :
    (liftRingHom φ hφ).comp (algebraMap K[X] _) = φ :=
  RingHom.ext fun _ ↦ liftRingHom_algebraMap _ hφ _

variable (K)

theorem ofFractionRing_comp_algebraMap :
    ofFractionRing ∘ algebraMap K[X] (FractionRing K[X]) = algebraMap _ _ :=
  funext ofFractionRing_algebraMap

theorem algebraMap_injective : Function.Injective (algebraMap K[X] K⟮X⟯) := by
  rw [← ofFractionRing_comp_algebraMap]
  exact ofFractionRing_injective.comp (IsFractionRing.injective _ _)

variable {K}

section LiftAlgHom

variable {L R S : Type*} [Field L] [CommRing R] [IsDomain R] [CommSemiring S] [Algebra S K[X]]
  [Algebra S L] [Algebra S R[X]] (φ : K[X] →ₐ[S] L) (hφ : K[X]⁰ ≤ L⁰.comap φ)

/-- Lift an algebra homomorphism that maps polynomials `φ : K[X] →ₐ[S] R[X]`
to a `K⟮X⟯ →ₐ[S] R⟮X⟯`,
on the condition that `φ` maps non-zero-divisors to non-zero-divisors,
by mapping both the numerator and denominator and quotienting them. -/
def mapAlgHom (φ : K[X] →ₐ[S] R[X]) (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) : K⟮X⟯ →ₐ[S] R⟮X⟯ :=
  { mapRingHom φ hφ with
    commutes' := fun r => by
      simp_rw [RingHom.toFun_eq_coe, coe_mapRingHom_eq_coe_map, algebraMap_apply r, map_apply_div,
        map_one, AlgHom.commutesₛₐ, RingHom.id_apply, div_one, ← IsScalarTower.algebraMap_apply] }

theorem coe_mapAlgHom_eq_coe_map (φ : K[X] →ₐ[S] R[X]) (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) :
    (mapAlgHom φ hφ : K⟮X⟯ → R⟮X⟯) = map φ hφ :=
  rfl

/-- Lift an injective algebra homomorphism `K[X] →ₐ[S] L` to a `K⟮X⟯ →ₐ[S] L`
by mapping both the numerator and denominator and quotienting them. -/
def liftAlgHom : K⟮X⟯ →ₐ[S] L :=
  { liftRingHom φ.toRingHom hφ with
    commutes' := fun r => by
      simp_rw [RingHom.toFun_eq_coe, AlgHom.toRingHom_eq_coe, algebraMap_apply r,
        liftRingHom_apply_div, AlgHom.coe_toRingHom, map_one, div_one, AlgHom.commutesₛₐ] }

theorem liftAlgHom_apply_ofFractionRing_mk (n : K[X]) (d : K[X]⁰) :
    liftAlgHom φ hφ (ofFractionRing (Localization.mk n d)) = φ n / φ d :=
  liftMonoidWithZeroHom_apply_ofFractionRing_mk _ hφ _ _

theorem liftAlgHom_injective (φ : K[X] →ₐ[S] L) (hφ : Function.Injective φ)
    (hφ' : K[X]⁰ ≤ L⁰.comap φ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hφ) :
    Function.Injective (liftAlgHom φ hφ') :=
  liftMonoidWithZeroHom_injective _ hφ

@[simp]
theorem liftAlgHom_apply_div' (p q : K[X]) :
    liftAlgHom φ hφ (algebraMap _ _ p) / liftAlgHom φ hφ (algebraMap _ _ q) = φ p / φ q :=
  liftMonoidWithZeroHom_apply_div' _ hφ _ _

theorem liftAlgHom_apply_div (p q : K[X]) :
    liftAlgHom φ hφ (algebraMap _ _ p / algebraMap _ _ q) = φ p / φ q :=
  liftMonoidWithZeroHom_apply_div _ hφ _ _

end LiftAlgHom

variable (K)

/-- `K⟮X⟯` is the field of fractions of the polynomials over `K`. -/
instance : IsFractionRing K[X] K⟮X⟯ where
  map_units y := by
    rw [← ofFractionRing_algebraMap]
    exact (toFractionRingRingEquiv K).symm.toRingHom.isUnit_map (IsLocalization.map_units _ y)
  exists_of_eq {x y} := by
    rw [← ofFractionRing_algebraMap, ← ofFractionRing_algebraMap]
    exact fun h ↦ IsLocalization.exists_of_eq ((toFractionRingRingEquiv K).symm.injective h)
  surj := by
    rintro ⟨z⟩
    convert IsLocalization.surj K[X]⁰ z
    simp only [← ofFractionRing_algebraMap, ← ofFractionRing_mul,
      ofFractionRing.injEq]

variable {K}

theorem algebraMap_ne_zero {x : K[X]} (hx : x ≠ 0) : algebraMap K[X] K⟮X⟯ x ≠ 0 := by
  simpa

@[simp]
theorem liftOn_div {P : Sort v} (p q : K[X]) (f : K[X] → K[X] → P) (f0 : ∀ p, f p 0 = f 0 1)
    (H' : ∀ {p q p' q'} (_hq : q ≠ 0) (_hq' : q' ≠ 0), q' * p = q * p' → f p q = f p' q')
    (H : ∀ {p q p' q'} (_hq : q ∈ K[X]⁰) (_hq' : q' ∈ K[X]⁰), q' * p = q * p' → f p q = f p' q' :=
      fun {_ _ _ _} hq hq' h => H' (nonZeroDivisors.ne_zero hq) (nonZeroDivisors.ne_zero hq') h) :
    (RatFunc.liftOn (algebraMap _ K⟮X⟯ p / algebraMap _ _ q)) f @H = f p q := by
  rw [← mk_eq_div, liftOn_mk _ _ f f0 @H']

@[simp]
theorem liftOn'_div {P : Sort v} (p q : K[X]) (f : K[X] → K[X] → P) (f0 : ∀ p, f p 0 = f 0 1)
    (H) :
    (RatFunc.liftOn' (algebraMap _ K⟮X⟯ p / algebraMap _ _ q)) f @H = f p q := by
  rw [RatFunc.liftOn', liftOn_div _ _ _ f0]
  apply liftOn_condition_of_liftOn'_condition H

/-- Induction principle for `K⟮X⟯`: if `f p q : P (p / q)` for all `p q : K[X]`,
then `P` holds on all elements of `K⟮X⟯`.

See also `induction_on'`, which is a recursion principle defined in terms of `RatFunc.mk`.
-/
protected theorem induction_on {P : K⟮X⟯ → Prop} (x : K⟮X⟯)
    (f : ∀ (p q : K[X]) (_ : q ≠ 0), P (algebraMap _ K⟮X⟯ p / algebraMap _ _ q)) : P x :=
  x.induction_on' fun p q hq => by simpa using f p q hq

theorem ofFractionRing_mk' (x : K[X]) (y : K[X]⁰) :
    ofFractionRing (IsLocalization.mk' _ x y) =
      IsLocalization.mk' K⟮X⟯ x y := by
  rw [IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div, ← mk_eq_div', ← mk_eq_div]

theorem mk_eq_mk' (f : Polynomial K) {g : Polynomial K} (hg : g ≠ 0) :
    RatFunc.mk f g = IsLocalization.mk' K⟮X⟯ f
      ⟨g, mem_nonZeroDivisors_iff_ne_zero.2 hg⟩ := by
  simp only [mk_eq_div, IsFractionRing.mk'_eq_div]

@[simp]
theorem ofFractionRing_eq :
    (ofFractionRing : FractionRing K[X] → K⟮X⟯) = IsLocalization.algEquiv K[X]⁰ _ _ :=
  funext fun x =>
    Localization.induction_on x fun x => by
      simp only [Localization.mk_eq_mk'_apply, ofFractionRing_mk', IsLocalization.algEquiv_apply,
        IsLocalization.map_mk', RingHom.id_apply]

@[simp]
theorem toFractionRing_eq :
    (toFractionRing : K⟮X⟯ → FractionRing K[X]) = IsLocalization.algEquiv K[X]⁰ _ _ :=
  funext fun ⟨x⟩ =>
    Localization.induction_on x fun x => by
      simp only [Localization.mk_eq_mk'_apply, ofFractionRing_mk', IsLocalization.algEquiv_apply,
        IsLocalization.map_mk', RingHom.id_apply]

@[simp]
theorem toFractionRingRingEquiv_symm_eq :
    (toFractionRingRingEquiv K).symm = (IsLocalization.algEquiv K[X]⁰ _ _).toRingEquiv := by
  ext x
  simp [toFractionRingRingEquiv, ofFractionRing_eq]

section lift

/-
As `R⟮X⟯` is a one-field-struct, we need to specialize the following instances of
`FractionRing`.
-/

variable (R L : Type*) [CommRing R] [Field L] [IsDomain R] [Algebra R[X] L] [FaithfulSMul R[X] L]

/-- `FractionRing.liftAlgebra` specialized to `R⟮X⟯`.

This is a scoped instance because it creates a diamond when `L = R⟮X⟯`. -/
scoped instance liftAlgebra : Algebra R⟮X⟯ L :=
  RingHom.toAlgebra (IsFractionRing.lift (FaithfulSMul.algebraMap_injective R[X] _))

/-- `FractionRing.isScalarTower_liftAlgebra` specialized to `R⟮X⟯`. -/
instance isScalarTower_liftAlgebra :
    IsScalarTower R[X] R⟮X⟯ L :=
  IsScalarTower.of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap (FaithfulSMul.algebraMap_injective R[X] L) x).symm

attribute [local instance] Polynomial.algebra

/-- `FractionRing.instFaithfulSMul` specialized to `R⟮X⟯`. -/
instance faithfulSMul (K E : Type*) [Field K] [Field E] [Algebra K E]
    [FaithfulSMul K E] : FaithfulSMul K[X] E⟮X⟯ :=
  (faithfulSMul_iff_algebraMap_injective ..).mpr <|
    (IsFractionRing.injective E[X] _).comp
      (Polynomial.map_injective _ <| FaithfulSMul.algebraMap_injective K E)

section rank

attribute [local instance] Polynomial.algebra

variable (k K : Type*) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]

theorem rank_ratFunc_ratFunc : Module.rank k⟮X⟯ K⟮X⟯ = Module.rank k K := by
  rw [Algebra.IsAlgebraic.rank_of_isFractionRing k[X] k⟮X⟯ K[X] K⟮X⟯,
    rank_polynomial_polynomial]

theorem finrank_ratFunc_ratFunc : Module.finrank k⟮X⟯ K⟮X⟯ = Module.finrank k K := by
  by_cases hf : Module.Finite k⟮X⟯ K⟮X⟯
  · have hrank := rank_ratFunc_ratFunc k K
    rw [← Module.finrank_eq_rank] at hrank
    exact (Module.finrank_eq_of_rank_eq hrank.symm).symm
  · have hf' : ¬ Module.Finite k K := by
      rwa [← Module.rank_lt_aleph0_iff, ← rank_ratFunc_ratFunc, Module.rank_lt_aleph0_iff]
    rw [Module.finrank_of_not_finite hf, Module.finrank_of_not_finite hf']

end rank

end lift

section IsScalarTower

/-- Let `A⟮X⟯ / A[X] / R / R₀` be a tower. If `A[X] / R / R₀` is a scalar tower
then so is `A⟮X⟯ / R / R₀`. -/
instance (R₀ R A : Type*) [CommSemiring R₀] [CommSemiring R] [CommRing A] [IsDomain A]
    [Algebra R₀ A[X]] [SMul R₀ R] [Algebra R A[X]] [IsScalarTower R₀ R A[X]] :
    IsScalarTower R₀ R A⟮X⟯ := IsScalarTower.to₁₂₄ _ _ A[X] _

/-- Let `K / A⟮X⟯ / A[X] / R` be a tower. If `K / A[X] / R` is a scalar tower
then so is `K / A⟮X⟯ / R`. -/
instance (R A K : Type*) [CommRing A] [IsDomain A] [Field K] [Algebra A[X] K]
    [FaithfulSMul A[X] K] [CommSemiring R] [Algebra R A[X]] [SMul R K] [IsScalarTower R A[X] K] :
    IsScalarTower R A⟮X⟯ K :=
  IsScalarTower.to₁₃₄ _ A[X] _ _

/-- Let `K / k / A⟮X⟯ / A[X]` be a tower. If `K / k / A[X]` is a scalar tower
then so is `K / k / A⟮X⟯`. -/
instance (A k K : Type*) [CommRing A] [IsDomain A] [Field k] [Field K] [Algebra A[X] k]
    [Algebra A[X] K] [SMul k K] [FaithfulSMul A[X] k] [FaithfulSMul A[X] K]
    [IsScalarTower A[X] k K] : IsScalarTower A⟮X⟯ k K where
  smul_assoc a b c := by
    induction a using RatFunc.induction_on with | f p q hq =>
    rw [← smul_right_inj hq]
    simp_rw [← smul_assoc, Algebra.smul_def q]
    field_simp [hq]
    simp

end IsScalarTower

end IsDomain

end IsFractionRing

end CommRing

section NumDenom

/-! ### Numerator and denominator -/

open GCDMonoid Polynomial

variable [Field K]

open scoped Classical in
/-- `RatFunc.numDenom` are numerator and denominator of a rational function over a field,
normalized such that the denominator is monic. -/
def numDenom (x : K⟮X⟯) : K[X] × K[X] :=
  x.liftOn'
    (fun p q =>
      if q = 0 then ⟨0, 1⟩
      else
        let r := gcd p q
        ⟨Polynomial.C (q / r).leadingCoeff⁻¹ * (p / r),
          Polynomial.C (q / r).leadingCoeff⁻¹ * (q / r)⟩)
  (by
      intro p q a hq ha
      dsimp
      rw [if_neg hq, if_neg (mul_ne_zero ha hq)]
      have ha' : a.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr ha
      have hainv : a.leadingCoeff⁻¹ ≠ 0 := inv_ne_zero ha'
      simp only [Prod.ext_iff, gcd_mul_left, normalize_apply a, Polynomial.coe_normUnit, mul_assoc,
        CommGroupWithZero.coe_normUnit _ ha']
      have hdeg : (gcd p q).degree ≤ q.degree := degree_gcd_le_right _ hq
      have hdeg' : (Polynomial.C a.leadingCoeff⁻¹ * gcd p q).degree ≤ q.degree := by
        rw [Polynomial.degree_mul, Polynomial.degree_C hainv, zero_add]
        exact hdeg
      have hdivp : Polynomial.C a.leadingCoeff⁻¹ * gcd p q ∣ p :=
        (C_mul_dvd hainv).mpr (gcd_dvd_left p q)
      have hdivq : Polynomial.C a.leadingCoeff⁻¹ * gcd p q ∣ q :=
        (C_mul_dvd hainv).mpr (gcd_dvd_right p q)
      rw [EuclideanDomain.mul_div_mul_cancel ha hdivp, EuclideanDomain.mul_div_mul_cancel ha hdivq,
        leadingCoeff_div hdeg, leadingCoeff_div hdeg', Polynomial.leadingCoeff_mul,
        Polynomial.leadingCoeff_C, div_C_mul, div_C_mul, ← mul_assoc, ← Polynomial.C_mul, ←
        mul_assoc, ← Polynomial.C_mul]
      constructor <;> congr <;>
        rw [inv_div, mul_comm, mul_div_assoc, ← mul_assoc, inv_inv, mul_inv_cancel₀ ha',
          one_mul, inv_div])

open scoped Classical in
@[simp]
theorem numDenom_div (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    numDenom (algebraMap _ _ p / algebraMap _ _ q) =
      (Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q),
        Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (q / gcd p q)) := by
  rw [numDenom, liftOn'_div, if_neg hq]
  intro p
  rw [if_pos rfl, if_neg (one_ne_zero' K[X])]
  simp

/-- `RatFunc.num` is the numerator of a rational function,
normalized such that the denominator is monic. -/
def num (x : K⟮X⟯) : K[X] :=
  x.numDenom.1

open scoped Classical in
private theorem num_div' (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    num (algebraMap _ _ p / algebraMap _ _ q) =
      Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q) := by
  rw [num, numDenom_div _ hq]

@[simp]
theorem num_zero : num (0 : K⟮X⟯) = 0 := by convert num_div' (0 : K[X]) one_ne_zero <;> simp

open scoped Classical in
@[simp]
theorem num_div (p q : K[X]) :
    num (algebraMap _ _ p / algebraMap _ _ q) =
      Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q) := by
  by_cases hq : q = 0
  · simp [hq]
  · exact num_div' p hq

@[simp]
theorem num_one : num (1 : K⟮X⟯) = 1 := by convert num_div (1 : K[X]) 1 <;> simp

@[simp]
theorem num_algebraMap (p : K[X]) : num (algebraMap _ _ p) = p := by convert num_div p 1 <;> simp

theorem num_div_dvd (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    num (algebraMap _ _ p / algebraMap _ _ q) ∣ p := by
  classical
  rw [num_div _ q, C_mul_dvd]
  · exact EuclideanDomain.div_dvd_of_dvd (gcd_dvd_left p q)
  · simpa only [Ne, inv_eq_zero, Polynomial.leadingCoeff_eq_zero] using right_div_gcd_ne_zero hq

open scoped Classical in
/-- A version of `num_div_dvd` with the LHS in simp normal form -/
@[simp]
theorem num_div_dvd' (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q) ∣ p := by simpa using num_div_dvd p hq

/-- `RatFunc.denom` is the denominator of a rational function,
normalized such that it is monic. -/
def denom (x : K⟮X⟯) : K[X] :=
  x.numDenom.2

open scoped Classical in
@[simp]
theorem denom_div (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    denom (algebraMap _ _ p / algebraMap _ _ q) =
      Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (q / gcd p q) := by
  rw [denom, numDenom_div _ hq]

theorem monic_denom (x : K⟮X⟯) : (denom x).Monic := by
  classical
  induction x using RatFunc.induction_on with
  | f p q hq =>
    rw [denom_div p hq, mul_comm]
    exact Polynomial.monic_mul_leadingCoeff_inv (right_div_gcd_ne_zero hq)

theorem denom_ne_zero (x : K⟮X⟯) : denom x ≠ 0 :=
  (monic_denom x).ne_zero

@[simp]
theorem denom_zero : denom (0 : K⟮X⟯) = 1 := by
  convert denom_div (0 : K[X]) one_ne_zero <;> simp

@[simp]
theorem denom_one : denom (1 : K⟮X⟯) = 1 := by
  convert denom_div (1 : K[X]) one_ne_zero <;> simp

@[simp]
theorem denom_algebraMap (p : K[X]) : denom (algebraMap _ K⟮X⟯ p) = 1 := by
  convert denom_div p one_ne_zero <;> simp

@[simp]
theorem denom_div_dvd (p q : K[X]) : denom (algebraMap _ _ p / algebraMap _ _ q) ∣ q := by
  classical
  by_cases hq : q = 0
  · simp [hq]
  rw [denom_div _ hq, C_mul_dvd]
  · exact EuclideanDomain.div_dvd_of_dvd (gcd_dvd_right p q)
  · simpa only [Ne, inv_eq_zero, Polynomial.leadingCoeff_eq_zero] using right_div_gcd_ne_zero hq

@[simp]
theorem num_div_denom (x : K⟮X⟯) : algebraMap _ _ (num x) / algebraMap _ _ (denom x) = x := by
  classical
  induction x using RatFunc.induction_on with | _ p q hq
  have q_div_ne_zero : q / gcd p q ≠ 0 := right_div_gcd_ne_zero hq
  rw [num_div p q, denom_div p hq, map_mul, map_mul, mul_div_mul_left,
    div_eq_div_iff, ← map_mul, ← map_mul, mul_comm _ q, ←
    EuclideanDomain.mul_div_assoc, ← EuclideanDomain.mul_div_assoc, mul_comm]
  · apply gcd_dvd_right
  · apply gcd_dvd_left
  · exact algebraMap_ne_zero q_div_ne_zero
  · exact algebraMap_ne_zero hq
  · refine algebraMap_ne_zero (mt Polynomial.C_eq_zero.mp ?_)
    exact inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr q_div_ne_zero)

theorem isCoprime_num_denom (x : K⟮X⟯) : IsCoprime x.num x.denom := by
  classical
  induction x using RatFunc.induction_on with | _ p q hq
  rw [num_div, denom_div _ hq]
  exact (isCoprime_mul_unit_left
    ((leadingCoeff_ne_zero.2 <| right_div_gcd_ne_zero hq).isUnit.inv.map C) _ _).2
      (isCoprime_div_gcd_div_gcd hq)

@[simp]
theorem num_eq_zero_iff {x : K⟮X⟯} : num x = 0 ↔ x = 0 :=
  ⟨fun h => by rw [← num_div_denom x, h, map_zero, zero_div], fun h => h.symm ▸ num_zero⟩

theorem num_ne_zero {x : K⟮X⟯} (hx : x ≠ 0) : num x ≠ 0 :=
  mt num_eq_zero_iff.mp hx

theorem num_mul_eq_mul_denom_iff {x : K⟮X⟯} {p q : K[X]} (hq : q ≠ 0) :
    x.num * q = p * x.denom ↔ x = algebraMap _ _ p / algebraMap _ _ q := by
  rw [← (algebraMap_injective K).eq_iff, eq_div_iff (algebraMap_ne_zero hq)]
  conv_rhs => rw [← num_div_denom x]
  rw [map_mul, map_mul, div_eq_mul_inv, mul_assoc, mul_comm (Inv.inv _), ←
    mul_assoc, ← div_eq_mul_inv, div_eq_iff]
  exact algebraMap_ne_zero (denom_ne_zero x)

theorem num_denom_add (x y : K⟮X⟯) :
    (x + y).num * (x.denom * y.denom) = (x.num * y.denom + x.denom * y.num) * (x + y).denom :=
  (num_mul_eq_mul_denom_iff (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))).mpr <| by
    conv_lhs => rw [← num_div_denom x, ← num_div_denom y]
    rw [div_add_div, map_mul, map_add, map_mul, map_mul]
    · exact algebraMap_ne_zero (denom_ne_zero x)
    · exact algebraMap_ne_zero (denom_ne_zero y)

theorem num_denom_neg (x : K⟮X⟯) : (-x).num * x.denom = -x.num * (-x).denom := by
  rw [num_mul_eq_mul_denom_iff (denom_ne_zero x), map_neg, neg_div, num_div_denom]

theorem num_denom_mul (x y : K⟮X⟯) :
    (x * y).num * (x.denom * y.denom) = x.num * y.num * (x * y).denom :=
  (num_mul_eq_mul_denom_iff (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))).mpr <| by
    conv_lhs =>
      rw [← num_div_denom x, ← num_div_denom y, div_mul_div_comm, ← map_mul, ← map_mul]

theorem num_dvd {x : K⟮X⟯} {p : K[X]} (hp : p ≠ 0) :
    num x ∣ p ↔ ∃ q : K[X], q ≠ 0 ∧ x = algebraMap _ _ p / algebraMap _ _ q := by
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨_hx, hq⟩ := mul_ne_zero_iff.mp hp
    use denom x * q
    rw [map_mul, map_mul, ← div_mul_div_comm, div_self, mul_one, num_div_denom]
    · exact ⟨mul_ne_zero (denom_ne_zero x) hq, rfl⟩
    · exact algebraMap_ne_zero hq
  · rintro ⟨q, hq, rfl⟩
    exact num_div_dvd p hq

theorem denom_dvd {x : K⟮X⟯} {q : K[X]} (hq : q ≠ 0) :
    denom x ∣ q ↔ ∃ p : K[X], x = algebraMap _ _ p / algebraMap _ _ q := by
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨_hx, hp⟩ := mul_ne_zero_iff.mp hq
    use num x * p
    rw [map_mul, map_mul, ← div_mul_div_comm, div_self, mul_one, num_div_denom]
    exact algebraMap_ne_zero hp
  · rintro ⟨p, rfl⟩
    exact denom_div_dvd p q

theorem num_mul_dvd (x y : K⟮X⟯) : num (x * y) ∣ num x * num y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [num_dvd (mul_ne_zero (num_ne_zero hx) (num_ne_zero hy))]
  refine ⟨x.denom * y.denom, mul_ne_zero (denom_ne_zero x) (denom_ne_zero y), ?_⟩
  rw [map_mul, map_mul, ← div_mul_div_comm, num_div_denom, num_div_denom]

theorem denom_mul_dvd (x y : K⟮X⟯) : denom (x * y) ∣ denom x * denom y := by
  rw [denom_dvd (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))]
  refine ⟨x.num * y.num, ?_⟩
  rw [map_mul, map_mul, ← div_mul_div_comm, num_div_denom, num_div_denom]

theorem denom_add_dvd (x y : K⟮X⟯) : denom (x + y) ∣ denom x * denom y := by
  rw [denom_dvd (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))]
  refine ⟨x.num * y.denom + x.denom * y.num, ?_⟩
  rw [map_mul, map_add, map_mul, map_mul, ← div_add_div, num_div_denom, num_div_denom]
  · exact algebraMap_ne_zero (denom_ne_zero x)
  · exact algebraMap_ne_zero (denom_ne_zero y)

theorem num_inv_dvd {x : K⟮X⟯} (hx : x ≠ 0) : num x⁻¹ ∣ denom x := by
  rw [num_dvd x.denom_ne_zero]
  refine ⟨x.num, num_ne_zero hx, ?_⟩
  nth_rw 1 [← x.num_div_denom]
  rw [inv_div]

theorem denom_inv_dvd {x : K⟮X⟯} (hx : x ≠ 0) : denom x⁻¹ ∣ num x := by
  rw [denom_dvd (num_ne_zero hx)]
  refine ⟨x.denom, ?_⟩
  nth_rw 1 [← x.num_div_denom]
  rw [inv_div]

theorem associated_num_inv {x : K⟮X⟯} (hx : x ≠ 0) : Associated (num x⁻¹) (denom x) := by
  apply associated_of_dvd_dvd (num_inv_dvd hx)
  convert denom_inv_dvd (inv_ne_zero hx)
  rw [inv_inv]

theorem associated_denom_inv {x : K⟮X⟯} (hx : x ≠ 0) : Associated (denom x⁻¹) (num x) := by
  apply Associated.symm
  convert associated_num_inv (inv_ne_zero hx)
  rw [inv_inv]

theorem map_denom_ne_zero {L F : Type*} [Zero L] [FunLike F K[X] L] [ZeroHomClass F K[X] L]
    (φ : F) (hφ : Function.Injective φ) (f : K⟮X⟯) : φ f.denom ≠ 0 := fun H =>
  (denom_ne_zero f) ((map_eq_zero_iff φ hφ).mp H)

theorem map_apply {R F : Type*} [CommRing R] [IsDomain R]
    [FunLike F K[X] R[X]] [MonoidHomClass F K[X] R[X]] (φ : F)
    (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) (f : K⟮X⟯) :
    map φ hφ f = algebraMap _ _ (φ f.num) / algebraMap _ _ (φ f.denom) := by
  rw [← num_div_denom f, map_apply_div_ne_zero, num_div_denom f]
  exact denom_ne_zero _

theorem liftMonoidWithZeroHom_apply {L : Type*} [CommGroupWithZero L] (φ : K[X] →*₀ L)
    (hφ : K[X]⁰ ≤ L⁰.comap φ) (f : K⟮X⟯) :
    liftMonoidWithZeroHom φ hφ f = φ f.num / φ f.denom := by
  rw [← num_div_denom f, liftMonoidWithZeroHom_apply_div, num_div_denom]

theorem liftRingHom_apply {L : Type*} [Field L] (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ)
    (f : K⟮X⟯) : liftRingHom φ hφ f = φ f.num / φ f.denom :=
  liftMonoidWithZeroHom_apply _ hφ _

theorem liftAlgHom_apply {L S : Type*} [Field L] [CommSemiring S] [Algebra S K[X]] [Algebra S L]
    (φ : K[X] →ₐ[S] L) (hφ : K[X]⁰ ≤ L⁰.comap φ) (f : K⟮X⟯) :
    liftAlgHom φ hφ f = φ f.num / φ f.denom :=
  liftMonoidWithZeroHom_apply _ hφ _

theorem num_mul_denom_add_denom_mul_num_ne_zero {x y : K⟮X⟯} (hxy : x + y ≠ 0) :
    x.num * y.denom + x.denom * y.num ≠ 0 := by
  intro h_zero
  have h := num_denom_add x y
  rw [h_zero, zero_mul] at h
  exact (mul_ne_zero (num_ne_zero hxy) (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)) h

end NumDenom

section Char

instance [Field K] {p : ℕ} [CharP K p] : CharP K⟮X⟯ p :=
  charP_of_injective_algebraMap' K p

instance [Field K] {p : ℕ} [ExpChar K p] : ExpChar K⟮X⟯ p :=
  ExpChar.of_injective_algebraMap' K p

instance [Field K] [CharZero K] : CharZero K⟮X⟯ :=
  Algebra.charZero_of_charZero K _

end Char

end RatFunc
