/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Order.GroupWithZero.Synonym
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

/-! # Structures involving `*` and `0` on `WithTop` and `WithBot`
-/

assert_not_exists OrderedCommMonoid

variable {α : Type*}

namespace WithTop

variable [DecidableEq α]

section MulZeroClass
variable [MulZeroClass α] {a b : WithTop α}

instance instMulZeroClass : MulZeroClass (WithTop α) where
  zero := 0
  mul a b := match a, b with
    | (a : α), (b : α) => ↑(a * b)
    | (a : α), ⊤ => if a = 0 then 0 else ⊤
    | ⊤, (b : α) => if b = 0 then 0 else ⊤
    | ⊤, ⊤ => ⊤
  mul_zero a := match a with
    | (a : α) => congr_arg some <| mul_zero _
    | ⊤ => if_pos rfl
  zero_mul b := match b with
    | (b : α) => congr_arg some <| zero_mul _
    | ⊤ => if_pos rfl

@[simp, norm_cast] lemma coe_mul (a b : α) : (↑(a * b) : WithTop α) = a * b := rfl

lemma mul_top' : ∀ (a : WithTop α), a * ⊤ = if a = 0 then 0 else ⊤
  | (a : α) => if_congr coe_eq_zero.symm rfl rfl
  | ⊤ => (if_neg top_ne_zero).symm

@[simp] lemma mul_top (h : a ≠ 0) : a * ⊤ = ⊤ := by rw [mul_top', if_neg h]

lemma top_mul' : ∀ (b : WithTop α), ⊤ * b = if b = 0 then 0 else ⊤
  | (b : α) => if_congr coe_eq_zero.symm rfl rfl
  | ⊤ => (if_neg top_ne_zero).symm

@[simp] lemma top_mul (hb : b ≠ 0) : ⊤ * b = ⊤ := by rw [top_mul', if_neg hb]

@[simp] lemma top_mul_top : (⊤ * ⊤ : WithTop α) = ⊤ := rfl

lemma mul_def (a b : WithTop α) :
    a * b = if a = 0 ∨ b = 0 then 0 else WithTop.map₂ (· * ·) a b := by
  cases a <;> cases b <;> aesop

lemma mul_eq_top_iff : a * b = ⊤ ↔ a ≠ 0 ∧ b = ⊤ ∨ a = ⊤ ∧ b ≠ 0 := by rw [mul_def]; aesop

lemma mul_coe_eq_bind {b : α} (hb : b ≠ 0) : ∀ a, (a * b : WithTop α) = a.bind fun a ↦ ↑(a * b)
  | ⊤ => by simp [top_mul, hb]; rfl
  | (a : α) => rfl

lemma coe_mul_eq_bind {a : α} (ha : a ≠ 0) : ∀ b, (a * b : WithTop α) = b.bind fun b ↦ ↑(a * b)
  | ⊤ => by simp [top_mul, ha]; rfl
  | (b : α) => rfl

@[simp] lemma untop'_zero_mul (a b : WithTop α) : (a * b).untop' 0 = a.untop' 0 * b.untop' 0 := by
  by_cases ha : a = 0; · rw [ha, zero_mul, ← coe_zero, untop'_coe, zero_mul]
  by_cases hb : b = 0; · rw [hb, mul_zero, ← coe_zero, untop'_coe, mul_zero]
  induction a; · rw [top_mul hb, untop'_top, zero_mul]
  induction b; · rw [mul_top ha, untop'_top, mul_zero]
  rw [← coe_mul, untop'_coe, untop'_coe, untop'_coe]

theorem mul_lt_top' [LT α] {a b : WithTop α} (ha : a < ⊤) (hb : b < ⊤) : a * b < ⊤ := by
  rw [WithTop.lt_top_iff_ne_top] at *
  simp only [Ne, mul_eq_top_iff, *, and_false, false_and, or_self, not_false_eq_true]

theorem mul_lt_top [LT α] {a b : WithTop α} (ha : a ≠ ⊤) (hb : b ≠ ⊤) : a * b < ⊤ :=
  mul_lt_top' (WithTop.lt_top_iff_ne_top.2 ha) (WithTop.lt_top_iff_ne_top.2 hb)

instance instNoZeroDivisors [NoZeroDivisors α] : NoZeroDivisors (WithTop α) := by
  refine ⟨fun h₁ => Decidable.by_contradiction fun h₂ => ?_⟩
  rw [mul_def, if_neg h₂] at h₁
  rcases Option.mem_map₂_iff.1 h₁ with ⟨a, b, (rfl : _ = _), (rfl : _ = _), hab⟩
  exact h₂ ((eq_zero_or_eq_zero_of_mul_eq_zero hab).imp (congr_arg some) (congr_arg some))

end MulZeroClass

/-- `Nontrivial α` is needed here as otherwise we have `1 * ⊤ = ⊤` but also `0 * ⊤ = 0`. -/
instance instMulZeroOneClass [MulZeroOneClass α] [Nontrivial α] : MulZeroOneClass (WithTop α) where
  __ := instMulZeroClass
  one_mul a := match a with
    | ⊤ => mul_top (mt coe_eq_coe.1 one_ne_zero)
    | (a : α) => by rw [← coe_one, ← coe_mul, one_mul]
  mul_one a := match a with
    | ⊤ => top_mul (mt coe_eq_coe.1 one_ne_zero)
    | (a : α) => by rw [← coe_one, ← coe_mul, mul_one]

/-- A version of `WithTop.map` for `MonoidWithZeroHom`s. -/
@[simps (config := .asFn)]
protected def _root_.MonoidWithZeroHom.withTopMap {R S : Type*} [MulZeroOneClass R] [DecidableEq R]
    [Nontrivial R] [MulZeroOneClass S] [DecidableEq S] [Nontrivial S] (f : R →*₀ S)
    (hf : Function.Injective f) : WithTop R →*₀ WithTop S :=
  { f.toZeroHom.withTopMap, f.toMonoidHom.toOneHom.withTopMap with
    toFun := WithTop.map f
    map_mul' := fun x y => by
      have : ∀ z, map f z = 0 ↔ z = 0 := fun z =>
        (Option.map_injective hf).eq_iff' f.toZeroHom.withTopMap.map_zero
      rcases Decidable.eq_or_ne x 0 with (rfl | hx)
      · simp
      rcases Decidable.eq_or_ne y 0 with (rfl | hy)
      · simp
      induction' x with x
      · simp [hy, this]
      induction' y with y
      · have : (f x : WithTop S) ≠ 0 := by simpa [hf.eq_iff' (map_zero f)] using hx
        simp [mul_top hx, mul_top this]
      · -- Porting note (#11215): TODO: `simp [← coe_mul]` times out
        simp only [map_coe, ← coe_mul, map_mul] }

instance instSemigroupWithZero [SemigroupWithZero α] [NoZeroDivisors α] :
    SemigroupWithZero (WithTop α) where
  __ := instMulZeroClass
  mul_assoc a b c := by
    rcases eq_or_ne a 0 with (rfl | ha); · simp only [zero_mul]
    rcases eq_or_ne b 0 with (rfl | hb); · simp only [zero_mul, mul_zero]
    rcases eq_or_ne c 0 with (rfl | hc); · simp only [mul_zero]
  -- Porting note: below needed to be rewritten due to changed `simp` behaviour for `coe`
    induction' a with a; · simp [hb, hc]
    induction' b with b; · simp [mul_top ha, top_mul hc]
    induction' c with c
    · rw [mul_top hb, mul_top ha]
      rw [← coe_zero, ne_eq, coe_eq_coe] at ha hb
      simp [ha, hb]
    simp only [← coe_mul, mul_assoc]

section MonoidWithZero
variable [MonoidWithZero α] [NoZeroDivisors α] [Nontrivial α]

instance instMonoidWithZero : MonoidWithZero (WithTop α) where
  __ := instMulZeroOneClass
  __ := instSemigroupWithZero
  npow n a := match a, n with
    | (a : α), n => ↑(a ^ n)
    | ⊤, 0 => 1
    | ⊤, _n + 1 => ⊤
  npow_zero a := by cases a <;> simp
  npow_succ n a := by cases n <;> cases a <;> simp [pow_succ]

@[simp, norm_cast] lemma coe_pow (a : α) (n : ℕ) : (↑(a ^ n) : WithTop α) = a ^ n := rfl

theorem top_pow {n : ℕ} (n_pos : 0 < n) : (⊤ : WithTop α) ^ n = ⊤ :=
  Nat.le_induction (pow_one _) (fun m _ hm => by rw [pow_succ, hm, top_mul_top]) _
    (Nat.succ_le_of_lt n_pos)

end MonoidWithZero

instance instCommMonoidWithZero [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] :
    CommMonoidWithZero (WithTop α) where
  __ := instMonoidWithZero
  mul_comm a b := by simp_rw [mul_def]; exact if_congr or_comm rfl (Option.map₂_comm mul_comm)

theorem left_distrib_of_add_eq_zero [CommSemiring α] {a b c : WithTop α}
    (h : a + b = 0 ↔ a = 0 ∧ b = 0) : (a + b) * c = a * c + b * c := by
  induction' c with c
  · by_cases ha : a = 0 <;> simp [ha, h]
  · by_cases hc : c = 0
    · simp [hc]
    simp only [mul_coe_eq_bind hc]
    cases a <;> cases b
    repeat' first | rfl |exact congr_arg some (add_mul _ _ _)

/--
`WithTop α` is a `CommSemiring` if `α` is a `CommSemiring` with no zero divisors,
`α` is nontrivial, and `a + b = 0` implies `a = 0` and `b = 0`. This is more flexible
than assuming `α` is a `CanonicallyOrderedCommSemiring` since it applies to cones
and makes no reference to orders.

See library note [reducible non-instances].
-/
@[reducible]
def commSemiringOfAddEqZero [CommSemiring α] [NoZeroDivisors α] [Nontrivial α]
    (h : ∀ {a b : WithTop α}, a + b = 0 → a = 0 ∧ b = 0) : CommSemiring (WithTop α) :=
  { addCommMonoidWithOne, instCommMonoidWithZero with
    right_distrib := fun _ _ _ => left_distrib_of_add_eq_zero ⟨h, fun h' => by
      simp [h'.1, h'.2]⟩
    left_distrib := fun a b c => by
      rw [mul_comm, left_distrib_of_add_eq_zero ⟨h, _⟩, mul_comm b, mul_comm c]
      intro h'
      simp [h'.1, h'.2] }

end WithTop
