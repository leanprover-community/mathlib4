/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Wieser, Jujian Zhang
-/
import Mathlib.Algebra.Divisibility.Prod
import Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# A homogeneous ideal that is homogeneously prime but not prime

In `Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem`, we assumed that the underlying grading
is indexed by a `LinearOrderedCancelAddCommMonoid` to prove that a homogeneous ideal is prime
if and only if it is homogeneously prime. This file shows that even if this assumption isn't
strictly necessary, the assumption of "being cancellative" is. We construct a counterexample where
the underlying indexing set is a `LinearOrderedAddCommMonoid` but is not cancellative and the
statement is false.

We achieve this by considering the ring `R=ℤ/4ℤ`. We first give the two element set `ι = {0, 1}` a
structure of linear ordered additive commutative monoid by setting `0 + 0 = 0` and `_ + _ = 1` and
`0 < 1`. Then we use `ι` to grade `R²` by setting `{(a, a) | a ∈ R}` to have grade `0`; and
`{(0, b) | b ∈ R}` to have grade 1. Then the ideal `I = span {(2, 2)} ⊆ ℤ/4ℤ × ℤ/4ℤ` is homogeneous
and not prime. But it is homogeneously prime, i.e. if `(a, b), (c, d)` are two homogeneous elements
then `(a, b) * (c, d) ∈ I` implies either `(a, b) ∈ I` or `(c, d) ∈ I`.


## Tags

homogeneous, prime
-/


namespace Counterexample

namespace CounterexampleNotPrimeButHomogeneousPrime

open DirectSum

-- attribute [local reducible] WithZero

abbrev Two :=
  WithZero Unit

instance Two.instLinearOrder : LinearOrder Two :=
  inferInstance

instance Two.instAddCommMonoid : AddCommMonoid Two :=
  inferInstance

instance : LinearOrderedAddCommMonoid Two :=
  { Two.instLinearOrder, Two.instAddCommMonoid with
    add_le_add_left := by
      delta Two WithZero; decide }
section

variable (R : Type*) [CommRing R]

/-- The grade 0 part of `R²` is `{(a, a) | a ∈ R}`. -/
def submoduleZ : Submodule R (R × R) where
  carrier := {zz | zz.1 = zz.2}
  zero_mem' := rfl
  add_mem' := @fun _ _ ha hb => congr_arg₂ (· + ·) ha hb
  smul_mem' a _ hb := congr_arg (a * ·) hb

/-- The grade 1 part of `R²` is `{(0, b) | b ∈ R}`. -/
def submoduleO : Submodule R (R × R) :=
  LinearMap.ker (LinearMap.fst R R R)

/-- Given the above grading (see `submoduleZ` and `submoduleO`),
  we turn `R²` into a graded ring. -/
def grading : Two → Submodule R (R × R)
  | 0 => submoduleZ R
  | 1 => submoduleO R

theorem grading.one_mem : (1 : R × R) ∈ grading R 0 :=
  Eq.refl (1, 1).fst

theorem grading.mul_mem :
    ∀ ⦃i j : Two⦄ {a b : R × R} (_ : a ∈ grading R i) (_ : b ∈ grading R j),
      a * b ∈ grading R (i + j)
  | 0, 0, a, b, (ha : a.1 = a.2), (hb : b.1 = b.2) => show a.1 * b.1 = a.2 * b.2 by rw [ha, hb]
  | 0, 1, a, b, (_ : a.1 = a.2), (hb : b.1 = 0) =>
    show a.1 * b.1 = 0 by rw [hb, mul_zero]
  | 1, 0, a, b, (ha : a.1 = 0), _ => show a.1 * b.1 = 0 by rw [ha, zero_mul]
  | 1, 1, a, b, (ha : a.1 = 0), _ => show a.1 * b.1 = 0 by rw [ha, zero_mul]

end

local notation "R" => ZMod 4

/-- `R² ≅ {(a, a) | a ∈ R} ⨁ {(0, b) | b ∈ R}` by `(x, y) ↦ (x, x) + (0, y - x)`. -/
def grading.decompose : R × R →+ DirectSum Two fun i => grading R i where
  toFun zz :=
    of (grading R ·) 0 ⟨(zz.1, zz.1), rfl⟩ +
    of (grading R ·) 1 ⟨(0, zz.2 - zz.1), rfl⟩
  map_zero' := by
    refine DFinsupp.ext (fun (i : Two) =>
        Option.casesOn i ?_ (fun (i_1 : Unit) => PUnit.casesOn i_1 ?_)) <;> rfl
  map_add' := by
    rintro ⟨a1, b1⟩ ⟨a2, b2⟩
    rw [add_add_add_comm, ← map_add, ← map_add]
    dsimp only [Prod.mk_add_mk]
    simp_rw [add_sub_add_comm]
    congr

theorem grading.right_inv : Function.RightInverse (coeLinearMap (grading R)) grading.decompose :=
  fun zz => by
  induction' zz using DirectSum.induction_on with i zz d1 d2 ih1 ih2
  · simp only [map_zero]
  · rcases i with (_ | ⟨⟨⟩⟩) <;> rcases zz with ⟨⟨a, b⟩, hab : _ = _⟩ <;> dsimp at hab <;>
      -- Porting note: proof was `decide` (without reverting any free variables).
      cases hab <;> decide +revert
  · simp only [map_add, ih1, ih2]

theorem grading.left_inv : Function.LeftInverse (coeLinearMap (grading R)) grading.decompose :=
  fun zz => by
  cases' zz with a b
  unfold grading.decompose
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_add, coeLinearMap_of, Prod.mk_add_mk,
    add_zero, add_sub_cancel]

instance : GradedAlgebra (grading R) where
  one_mem := grading.one_mem R
  mul_mem := grading.mul_mem R
  decompose' := grading.decompose
  left_inv := by convert grading.left_inv
  right_inv := by convert grading.right_inv


/-- The counterexample is the ideal `I = span {(2, 2)}`. -/
def I : Ideal (R × R) :=
  Ideal.span {((2, 2) : R × R)}

theorem I_not_prime : ¬I.IsPrime := by
  rintro ⟨rid1, rid2⟩
  apply rid1; clear rid1
  -- Porting note: proof was:
  -- `revert rid2; simp only [Ideal.mem_span_singleton, Ideal.eq_top_iff_one]; tauto`
  specialize @rid2 (1,2) (2,1)
  simpa only [I, Ideal.mem_span_singleton, Ideal.eq_top_iff_one, prod_dvd_iff, and_self, and_imp,
    Prod.fst_mul, Prod.snd_mul, Prod.forall, Prod.fst_one, Prod.snd_one, one_mul, mul_one,
    dvd_refl, and_true, true_and, or_self, forall_true_left] using rid2

theorem I_isHomogeneous : Ideal.IsHomogeneous (grading R) I := by
  rw [Ideal.IsHomogeneous.iff_exists]
  refine ⟨{⟨(2, 2), ⟨0, rfl⟩⟩}, ?_⟩
  rw [Set.image_singleton]
  rfl

theorem homogeneous_mem_or_mem {x y : R × R} (hx : SetLike.Homogeneous (grading R) x)
    (hy : SetLike.Homogeneous (grading R) y) (hxy : x * y ∈ I) : x ∈ I ∨ y ∈ I := by
  -- Porting note: added `h2` for later use; the proof is hideous
  have h2 : Prime (2:R) := by
    unfold Prime
    refine ⟨by decide, by decide, ?_⟩
    intro a b
    have aux2 : (Fin.mk 2 _ : R) = 2 := rfl
    have aux3 : (Fin.mk 3 _ : R) = -1 := rfl
    fin_cases a <;>
      simp +contextual only
        [Fin.mk_zero, zero_mul, dvd_zero, true_or, or_true, implies_true, forall_true_left,
          Fin.mk_one, one_mul, aux2, dvd_refl]
    fin_cases b <;>
      simp +contextual only
        [Fin.mk_zero, zero_mul, dvd_zero, true_or, or_true, implies_true, forall_true_left,
          Fin.mk_one, mul_one, aux2, dvd_refl, aux3, or_self, neg_one_mul, neg_neg, dvd_neg]
  simp only [I, Ideal.mem_span_singleton] at hxy ⊢
  cases' x; cases' y
  obtain ⟨_ | ⟨⟨⟩⟩, hx : _ = _⟩ := hx <;> obtain ⟨_ | ⟨⟨⟩⟩, hy : _ = _⟩ := hy <;>
    dsimp at hx hy <;>
    cases hx <;>
    cases hy <;>
    -- Porting note: proof was `tauto`
    simp only [prod_dvd_iff, dvd_zero, true_and, and_self,
      Prod.mk_mul_mk, mul_zero, zero_mul] at hxy ⊢ <;>
    apply h2.dvd_or_dvd hxy

end CounterexampleNotPrimeButHomogeneousPrime

end Counterexample
