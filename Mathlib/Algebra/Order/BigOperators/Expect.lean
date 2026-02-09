/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Algebra.Order.Module.Rat
public import Mathlib.Tactic.GCongr

import Mathlib.Algebra.Module.Torsion.Field

/-!
# Order properties of the average over a finset
-/

public section

open Function
open Fintype (card)
open scoped BigOperators Pointwise NNRat

variable {ι α R : Type*}

local notation a " /ℚ " q => (q : ℚ≥0)⁻¹ • a

namespace Finset
section OrderedAddCommMonoid
variable [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] [Module ℚ≥0 α]
  {s : Finset ι} {f g : ι → α}

lemma expect_eq_zero_iff_of_nonneg (hf : ∀ i ∈ s, 0 ≤ f i) :
    𝔼 i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0 := by
  simp +contextual [expect, sum_eq_zero_iff_of_nonneg hf]

lemma expect_eq_zero_iff_of_nonpos (hf : ∀ i ∈ s, f i ≤ 0) :
    𝔼 i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0 := by
  simp +contextual [expect, sum_eq_zero_iff_of_nonpos hf]

section PosSMulMono
variable [PosSMulMono ℚ≥0 α] {a : α}

@[gcongr]
lemma expect_le_expect (hfg : ∀ i ∈ s, f i ≤ g i) : 𝔼 i ∈ s, f i ≤ 𝔼 i ∈ s, g i :=
  smul_le_smul_of_nonneg_left (sum_le_sum hfg) <| by positivity

lemma expect_le (hs : s.Nonempty) (h : ∀ x ∈ s, f x ≤ a) : 𝔼 i ∈ s, f i ≤ a :=
  (inv_smul_le_iff_of_pos <| mod_cast hs.card_pos).2 <| by
    rw [Nat.cast_smul_eq_nsmul]; exact sum_le_card_nsmul _ _ _ h

lemma le_expect (hs : s.Nonempty) (h : ∀ x ∈ s, a ≤ f x) : a ≤ 𝔼 i ∈ s, f i :=
  (le_inv_smul_iff_of_pos <| mod_cast hs.card_pos).2 <| by
    rw [Nat.cast_smul_eq_nsmul]; exact card_nsmul_le_sum _ _ _ h

lemma expect_nonneg (hf : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ 𝔼 i ∈ s, f i :=
  smul_nonneg (by positivity) <| sum_nonneg hf

end PosSMulMono

section PosSMulMono
variable {M N : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
  [AddCommMonoid N] [PartialOrder N] [IsOrderedAddMonoid N] [Module ℚ≥0 N]
  [PosSMulMono ℚ≥0 N] {m : M → N} {p : M → Prop} {f : ι → M} {s : Finset ι}

/-- Let `{a | p a}` be an additive subsemigroup of an additive commutative monoid `M`. If `m` is a
subadditive function (`m (a + b) ≤ m a + m b`) preserved under division by a natural, `f` is a
function valued in that subsemigroup and `s` is a nonempty set, then
`m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i)`. -/
lemma le_expect_nonempty_of_subadditive_on_pred (h_add : ∀ a b, p a → p b → m (a + b) ≤ m a + m b)
    (hp_add : ∀ a b, p a → p b → p (a + b)) (h_div : ∀ (n : ℕ) a, p a → m (a /ℚ n) = m a /ℚ n)
    (hs_nonempty : s.Nonempty) (hs : ∀ i ∈ s, p (f i)) :
    m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i) := by
  simp only [expect, h_div _ _ (sum_induction_nonempty _ _ hp_add hs_nonempty hs)]
  exact smul_le_smul_of_nonneg_left
    (le_sum_nonempty_of_subadditive_on_pred _ _ h_add hp_add _ _ hs_nonempty hs) <| by positivity

/-- Let `{a | p a}` be a subsemigroup of a commutative monoid `M`. If `m` is a subadditive function
(`m (x + y) ≤ m x + m y`, `m 0 = 0`) preserved under division by a natural and `f` is a function
valued in that subsemigroup, then `m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i)`. -/
lemma le_expect_of_subadditive_on_pred (h_zero : m 0 = 0)
    (h_add : ∀ a b, p a → p b → m (a + b) ≤ m a + m b) (hp_add : ∀ a b, p a → p b → p (a + b))
    (h_div : ∀ (n : ℕ) a, p a → m (a /ℚ n) = m a /ℚ n)
    (hs : ∀ i ∈ s, p (f i)) : m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i) := by
  obtain rfl | hs_nonempty := s.eq_empty_or_nonempty
  · simp [h_zero]
  · exact le_expect_nonempty_of_subadditive_on_pred h_add hp_add h_div hs_nonempty hs

-- TODO: Contribute back better docstring to `le_prod_of_submultiplicative`
/-- If `m` is a subadditive function (`m (x + y) ≤ m x + m y`) preserved under division
by a natural, then `m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i)`. -/
lemma le_expect_of_subadditive (h_add : ∀ a b, m (a + b) ≤ m a + m b)
    (h_div : ∀ (n : ℕ) a, m (a /ℚ n) = m a /ℚ n) : m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i) :=
  le_expect_of_subadditive_on_pred (p := fun _ ↦ True) (by convert h_div 0 0 <;> simp)
    (by simpa) (by simp) (by simpa) (by simp)

end PosSMulMono
end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid
variable [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α] [Module ℚ≥0 α]
  {a : α} {s : Finset ι} {f g : ι → α}
section PosSMulStrictMono
variable [PosSMulStrictMono ℚ≥0 α]

lemma expect_lt_expect (hle : ∀ i ∈ s, f i ≤ g i) (hlt : ∃ i ∈ s, f i < g i)
    : 𝔼 i ∈ s, f i < 𝔼 i ∈ s, g i := by
  apply smul_lt_smul_of_pos_left (sum_lt_sum hle hlt)
  rw [inv_pos, Nat.cast_pos, card_pos]
  exact hlt.imp (fun _ => And.left)

lemma expect_lt (hle : ∀ x ∈ s, f x ≤ a) (hlt : ∃ x ∈ s, f x < a)
    : 𝔼 i ∈ s, f i < a := by
  rw [←expect_const (hlt.imp (fun _ => And.left)) a]
  exact expect_lt_expect hle hlt

lemma lt_expect (hle : ∀ x ∈ s, a ≤ f x) (hlt : ∃ x ∈ s, a < f x)
    : a < 𝔼 i ∈ s, f i := by
  rw [←expect_const (hlt.imp (fun _ => And.left)) a]
  exact expect_lt_expect hle hlt

lemma expect_pos (hf : ∀ i ∈ s, 0 < f i) (hs : s.Nonempty) : 0 < 𝔼 i ∈ s, f i :=
  smul_pos (inv_pos.2 <| mod_cast hs.card_pos) <| sum_pos hf hs

end PosSMulStrictMono
end OrderedCancelAddCommMonoid

section LinearOrderedAddCommMonoid
variable [AddCommMonoid α] [LinearOrder α] [IsOrderedAddMonoid α] [Module ℚ≥0 α]
  [PosSMulMono ℚ≥0 α] {s : Finset ι}
  {f g : ι → α} {a : α}

lemma exists_lt_of_expect_lt_expect (h : 𝔼 i ∈ s, g i < 𝔼 i ∈ s, f i)
    : ∃ x ∈ s, g x < f x := by
  contrapose! h; exact expect_le_expect h

lemma exists_lt_of_lt_expect (hs : s.Nonempty) (h : a < 𝔼 i ∈ s, f i) : ∃ x ∈ s, a < f x := by
  contrapose! h; exact expect_le hs h

lemma exists_lt_of_expect_lt (hs : s.Nonempty) (h : 𝔼 i ∈ s, f i < a) : ∃ x ∈ s, f x < a := by
  contrapose! h; exact le_expect hs h

end LinearOrderedAddCommMonoid

section LinearOrderedCancelAddMonoid
variable [AddCommMonoid α] [LinearOrder α] [IsOrderedCancelAddMonoid α] [Module ℚ≥0 α]
  [PosSMulStrictMono ℚ≥0 α] {a : α} {s : Finset ι} {f g : ι → α}

lemma exists_le_of_expect_le_expect (hs : s.Nonempty) (h : 𝔼 i ∈ s, g i ≤ 𝔼 i ∈ s, f i)
    : ∃ x ∈ s, g x ≤ f x := by
  obtain ⟨_, hx⟩ := hs
  contrapose! h
  exact expect_lt_expect (fun _ hx ↦ le_of_lt (h _ hx)) ⟨_, ⟨hx, h _ hx⟩⟩

lemma exists_le_of_le_expect (hs : s.Nonempty) (h : a ≤ 𝔼 i ∈ s, f i) : ∃ x ∈ s, a ≤ f x :=
  exists_le_of_expect_le_expect hs (by rwa [expect_const hs _])

lemma exists_le_of_expect_le (hs : s.Nonempty) (h : 𝔼 i ∈ s, f i ≤ a) : ∃ x ∈ s, f x ≤ a :=
  exists_le_of_expect_le_expect hs (by rwa [expect_const hs _])

end LinearOrderedCancelAddMonoid

section LinearOrderedAddCommGroup
variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [Module ℚ≥0 α] [PosSMulMono ℚ≥0 α]

lemma abs_expect_le (s : Finset ι) (f : ι → α) : |𝔼 i ∈ s, f i| ≤ 𝔼 i ∈ s, |f i| :=
  le_expect_of_subadditive abs_add_le (fun _ ↦ abs_nnqsmul _)

end LinearOrderedAddCommGroup

section LinearOrderedCommSemiring
variable [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R] [Module ℚ≥0 R]
  [PosSMulMono ℚ≥0 R]

/-- **Cauchy-Schwarz inequality** in terms of `Finset.expect`. -/
lemma expect_mul_sq_le_sq_mul_sq (s : Finset ι) (f g : ι → R) :
    (𝔼 i ∈ s, f i * g i) ^ 2 ≤ (𝔼 i ∈ s, f i ^ 2) * 𝔼 i ∈ s, g i ^ 2 := by
  simp only [expect, smul_pow, inv_pow, smul_mul_smul_comm, ← sq]
  gcongr
  exact sum_mul_sq_le_sq_mul_sq ..

end LinearOrderedCommSemiring
end Finset

open Finset

namespace Fintype
variable [Fintype ι]

section OrderedAddCommMonoid
variable [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] [Module ℚ≥0 α] {f : ι → α}

lemma expect_eq_zero_iff_of_nonneg (hf : 0 ≤ f) : 𝔼 i, f i = 0 ↔ f = 0 := by
  rw [Finset.expect_eq_zero_iff_of_nonneg (by aesop)]
  aesop

lemma expect_eq_zero_iff_of_nonpos (hf : f ≤ 0) : 𝔼 i, f i = 0 ↔ f = 0 := by
  rw [Finset.expect_eq_zero_iff_of_nonpos (by aesop)]
  aesop

end OrderedAddCommMonoid
end Fintype

open Finset

namespace Mathlib.Meta.Positivity
open Qq Lean Meta Finset
open scoped BigOperators

attribute [local instance] monadLiftOptionMetaM in
/-- Positivity extension for `Finset.expect`. -/
@[positivity Finset.expect _ _]
meta def evalFinsetExpect : PositivityExt where eval {u α} zα pα e := do
  match e with
  | ~q(@Finset.expect $ι _ $instα $instmod $s $f) =>
    let i : Q($ι) ← mkFreshExprMVarQ q($ι) .syntheticOpaque
    have body : Q($α) := .betaRev f #[i]
    let rbody ← core zα pα body
    let p_pos : Option Q(0 < $e) := ← (do
      let .positive pbody := rbody | pure none -- Fail if the body is not provably positive
      let some ps ← proveFinsetNonempty s | pure none
      let .some pα' ← trySynthInstanceQ q(IsOrderedCancelAddMonoid $α) | pure none
      let .some instαordsmul ← trySynthInstanceQ q(PosSMulStrictMono ℚ≥0 $α) | pure none
      assumeInstancesCommute
      let pr : Q(∀ i, 0 < $f i) ← mkLambdaFVars #[i] pbody
      return some
        q(@expect_pos $ι $α $instα $pα $pα' $instmod $s $f $instαordsmul (fun i _ ↦ $pr i) $ps))
    -- Try to show that the sum is positive
    if let some p_pos := p_pos then
      return .positive p_pos
    -- Fall back to showing that the sum is nonnegative
    else
      let pbody ← rbody.toNonneg
      let pr : Q(∀ i, 0 ≤ $f i) ← mkLambdaFVars #[i] pbody
      let instαordmon ← synthInstanceQ q(IsOrderedAddMonoid $α)
      let instαordsmul ← synthInstanceQ q(PosSMulMono ℚ≥0 $α)
      assumeInstancesCommute
      return .nonnegative
        q(@expect_nonneg $ι $α $instα $pα $instαordmon $instmod $s $f $instαordsmul fun i _ ↦ $pr i)
  | _ => throwError "not Finset.expect"

example (n : ℕ) (a : ℕ → ℚ) : 0 ≤ 𝔼 j ∈ range n, a j ^ 2 := by positivity
example (a : ULift.{2} ℕ → ℚ) (s : Finset (ULift.{2} ℕ)) : 0 ≤ 𝔼 j ∈ s, a j ^ 2 := by positivity
example (n : ℕ) (a : ℕ → ℚ) : 0 ≤ 𝔼 j : Fin 8, 𝔼 i ∈ range n, (a j ^ 2 + i ^ 2) := by positivity
example (n : ℕ) (a : ℕ → ℚ) : 0 < 𝔼 j : Fin (n + 1), (a j ^ 2 + 1) := by positivity
example (a : ℕ → ℚ) : 0 < 𝔼 j ∈ ({1} : Finset ℕ), (a j ^ 2 + 1) := by positivity

end Mathlib.Meta.Positivity
