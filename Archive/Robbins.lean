/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Tactic.Common

/-!
# The Robbins conjecture

Herbert Robbins asked in 1933 whether the following three axioms,
with `⊔` and `ᶜ` as in `BooleanAlgebra`, yield an algebra equivalent to Boolean algebra:

* `⊔` is commutative and associative
* For all `a` and `b`, `((a ⊔ b)ᶜ ⊔ (a ⊔ bᶜ)ᶜ)ᶜ = a`

This conjecture was only proved in 1997 by an early automated theorem prover
under the direction of William McCune by deriving Huntington's equation:

* For all `a` and `b`, `(aᶜ ⊔ bᶜ)ᶜ ⊔ (aᶜ ⊔ b)ᶜ = a`

With the axioms on `⊔` this had been shown by Edward Huntington to be equivalent to Boolean algebra,
just before Robbins made his conjecture.

The formalisation in this file largely follows Matthew Wampler-Doty's [Isabelle formalisation](https://www.isa-afp.org/entries/Robbins-Conjecture.html),
which in turn follows Allen L. Mann's [A Complete Proof of the Robbins Conjecture](https://math.colgate.edu/~amann/MA/robbins_complete.pdf).
Some differences include:

* For ease of typing and clarity around negations, algebraic notation is used for Robbins algebras:
  `- + 0 1` instead of `ᶜ ⊔ ⊥ ⊤`.
* After deriving Huntington's equation we derive the `BooleanAlgebra` instance directly.
  Wampler-Doty went through an axiomatisation with 9 axioms found in a textbook.
* To make the manipulations in Mann's presentation explicit, we do not automate proofs with `grind`,
  only `ac_rfl` for rearranging terms and `lia` for numeric comparisons.
  Wampler-Doty relies heavily on `metis`, a rough Isabelle equivalent of `grind`.
-/

public section

/-- The type of Robbins algebras. -/
class RobbinsAlgebra (α) extends Inhabited α, AddCommSemigroup α, Neg α where
  /-- Robbins's axiom -/
  robbins (a b : α) : -(-(a + b) + -(a + -b)) = a

variable {α : Type*}

/-- Derive a Robbins algebra from a Boolean algebra. -/
@[instance_reducible]
def BooleanAlgebra.robbinsAlgebra [BooleanAlgebra α] : RobbinsAlgebra α where
  default := ⊥
  add := (· ⊔ ·)
  add_comm := sup_comm
  add_assoc := sup_assoc
  neg := (·ᶜ)
  robbins a b := by
    change ((a ⊔ b)ᶜ ⊔ (a ⊔ bᶜ)ᶜ)ᶜ = a
    rw [compl_sup, compl_compl, compl_compl, ← sup_inf_left, inf_compl_self, sup_bot_eq]

namespace RobbinsAlgebra

variable [RobbinsAlgebra α] (a b c d : α)

private instance : Std.Associative (α := α) (· + ·) := ⟨add_assoc⟩

/-- Sum a number of copies of an element. Not intended to be used for 0 copies (although the
ultimately correct value of `-(a + -a)` is included for completeness). -/
def smul : ℕ → α → α
  | 0, a => -(a + -a)
  | 1, a => a
  | k + 2, a => smul (k + 1) a + a

instance : SMul ℕ α where smul := smul

private lemma smul1 : 1 • a = a := rfl
private lemma smul2 : 2 • a = a + a := rfl
private lemma smul3 : 3 • a = a + a + a := rfl
private lemma smul4 : 4 • a = a + a + a + a := rfl
private lemma smul5 : 5 • a = a + a + a + a + a := rfl

lemma smul_succ {k : ℕ} {a : α} (hk : 1 ≤ k) : (k + 1) • a = k • a + a := by
  induction k, hk using Nat.le_induction <;> rfl

lemma mann_44 : -(-(-(a + b) + -a + b) + b) = -(a + b) := by
  nth_rw 2 [← robbins (-(a + b)) (-a + b)]
  nth_rw 3 [← robbins b a]
  congr 2 <;> ac_rfl

lemma mann_45 : -(-(-(-a + b) + a + b) + b) = -(-a + b) := by
  nth_rw 2 [← robbins (-(-a + b)) (a + b)]
  nth_rw 3 [← robbins b a]
  ac_rfl

lemma mann_46 : -(-(-(-a + b) + a + b + b) + -(-a + b)) = b := by
  conv_rhs => rw [← robbins b (-(-a + b) + a + b)]
  nth_rw 2 [← mann_45 a b]
  ac_rfl

lemma mann_47 : -(-(-(-(-a + b) + a + b + b) + -(-a + b) + c) + -(b + c)) = c := by
  set w := -(-(-a + b) + a + b + b) + -(-a + b)
  nth_rw 3 [← robbins c w]
  rw [mann_46 a b]
  ac_rfl

lemma mann_48 : -(-(-(-(-a + b) + a + b + b) + -(-a + b) + -(b + c) + c) + c) = -(b + c) := by
  have key := robbins (-(b + c)) (-(-(-a + b) + a + b + b) + -(-a + b) + c)
  set q := -(-(-(-a + b) + a + b + b) + -(-a + b) + c)
  conv_rhs => rw [← key, add_comm _ q, mann_47]
  ac_rfl

lemma mann_49 :
    -(-(-(-(-(-a + b) + a + b + b) + -(-a + b) + -(b + c) + c) + c + d) + -(-(b + c) + d)) = d := by
  set w := -(-(-(-a + b) + a + b + b) + -(-a + b) + -(b + c) + c) + c
  nth_rw 3 [← robbins d w]
  rw [mann_48 a b c]
  ac_rfl

/-- A common subexpression occurring in `mann_50` to `winker`. -/
def q : α := -(-(3 • a) + a)

lemma mann_50 : -(-(q a + -(3 • a)) + -(q a + 5 • a)) = q a := by
  have k₁ := mann_44 (3 • a) (q a + 2 • a)
  have rearr₁ : -(-(3 • a + (q a + 2 • a)) + -(3 • a) + (q a + 2 • a)) + (q a + 2 • a) =
      -(-(q a + 5 • a) + -(3 • a) + (q a + 2 • a)) + 2 • a + q a := by
    rw [smul2, smul3, smul5]
    ac_rfl
  rw [rearr₁] at k₁
  have k₂ : -(-(-(-(q a + 3 • a + a + a) + q a + -(a + 2 • a) + 2 • a) + 2 • a + q a) +
      -(-(a + 2 • a) + q a)) = q a := mann_49 (3 • a) a (2 • a) (q a)
  have rearr₂ : (-(q a + 3 • a + a + a) + q a + -(a + 2 • a) + 2 • a) =
      -(q a + 5 • a) + -(3 • a) + (q a + 2 • a) := by
    simp_rw [smul2, smul3, smul5, ← add_assoc]
    congr 2
    simp_rw [add_assoc]
    congr 1
    rw [add_comm]
  rw [rearr₂, k₁] at k₂
  convert k₂ using 2
  rw [smul2, smul3, smul5]
  ac_rfl

lemma mann_51 : -(q a + 5 • a) = -(3 • a) := by
  have k₁ := robbins (-(q a + 5 • a)) (q a + -(3 • a))
  have k₂ : -(-(q a + -(3 • a)) + -(q a + 5 • a)) = q a := mann_50 a
  have k₃ : -(-(-(q a + 3 • a + a + a) + q a + -(3 • a)) + q a) = -(3 • a) := by
    convert! mann_47 (3 • a) a (-(3 • a)) using 3
    rw [q, add_comm]
  rw [← k₃, ← k₁, ← add_comm (-(q a + _)), k₂]
  simp_rw [smul3, smul5, ← add_assoc]

lemma mann_52 : -(-(q a + -(3 • a) + 2 • a) + -(3 • a)) = q a + 2 • a := by
  have key := robbins (q a + 2 • a) (3 • a)
  have rearr : q a + 2 • a + 3 • a = q a + 5 • a := by
    rw [smul2, smul3, smul5]
    ac_rfl
  rw [← key, rearr, mann_51]
  ac_rfl

lemma mann_53 : -(q a + -(3 • a)) = a := by
  have k₁ := robbins a (q a + 4 • a)
  have rearr : a + (q a + 4 • a) = q a + 5 • a := by
    rw [smul4, smul5]
    ac_rfl
  rw [rearr, mann_51] at k₁
  have k₂ : -(-(q a + 3 • a + a) + a) = q a := mann_45 (3 • a) a
  have rearr₂ : -(q a + 3 • a + a) + a = a + -(q a + 4 • a) := by
    rw [smul3, smul4]
    ac_rfl
  rw [rearr₂] at k₂
  rw [k₂] at k₁
  rwa [add_comm]

lemma mann_54 : -(-(q a + -(3 • a) + b) + -(a + b)) = b := by
  conv_rhs => rw [← robbins b (q a + -(3 • a)), mann_53]
  ac_rfl

/-- **Winker's first condition**,
proved in 1997 by the automated theorem prover EQP to be derivable in Robbins algebras. -/
theorem winker : ∃ x y : α, x + y = y := by
  refine ⟨q default, 2 • default, ?_⟩
  conv_lhs => rw [← mann_52]
  conv_rhs => rw [← mann_54 default (2 • default)]
  simp_rw [smul2, smul3, ← add_assoc]

section Idempotence

variable {a b c} {k : ℕ}

lemma mann_33 (h : -(a + -(b + c)) = -(a + b + -c)) : a + b = a := by
  rw [← robbins (a + b) c, ← h, add_assoc, robbins]

lemma mann_34 (h : -(a + -(b + c)) = -(b + -(a + c))) : a = b := by
  rw [← robbins a (b + c), h, show a + (b + c) = b + (a + c) by ac_rfl, robbins]

lemma mann_35 (h : -(a + -b) = c) : -(-(a + b) + c) = a := by
  rw [← h, robbins]

lemma mann_36 (hk : 1 ≤ k) (h : -(a + -b) = c) : -(a + -(b + k • (a + c))) = c := by
  induction k, hk using Nat.le_induction with
  | base =>
    nth_rw 1 [smul1, ← mann_35 h]
    conv_rhs => rw [← robbins c (a + b)]
    ac_rfl
  | succ k lk ih =>
    nth_rw 1 [smul_succ lk, ← mann_35 ih]
    conv_rhs => rw [← robbins c (a + b + k • (a + c))]
    rw [add_comm]
    congr 2 <;> ac_rfl

lemma mann_37 (hk : 1 ≤ k) (h : -(-(a + -b) + -b) = a) : -(b + k • (a + -(a + -b))) = -b := by
  set c := -(a + -b)
  have aux := mann_36 hk h
  rw [add_comm c a] at aux
  set bk := b + k • (a + c)
  apply mann_34 (c := c)
  rw [add_comm (-b), h, add_comm _ c, aux, add_comm _ a, mann_36 hk rfl, add_comm]

lemma mann_38 (hk : 1 ≤ k) (h : -(a + b) = -b) : -(b + k • (a + -(a + -b))) = -b := by
  apply mann_37 hk
  nth_rw 2 [← robbins a b, ← h]
  ac_rfl

lemma mann_39 (h₂ : -(2 • a + b) = -b) (h₃ : -(3 • a + b) = -b) : 2 • a + b = 3 • a + b := by
  conv_rhs at h₃ => rw [← h₂]
  rw [smul_succ (by lia), show 2 • a + a + b = a + (2 • a + b) by ac_rfl] at h₃
  have e₁ := mann_38 le_rfl h₂
  have e₂ := mann_38 le_rfl h₃
  rw [smul1] at e₁ e₂
  rw [show b + (2 • a + -(2 • a + -b)) = 2 • a + b + -(a + (a + -b)) by rw [smul2]; ac_rfl] at e₁
  rw [h₂] at e₂
  conv_rhs at e₁ => rw [← e₂, ← add_assoc]
  rw [← mann_33 e₁]
  rw [smul2, smul3]
  ac_rfl

lemma mann_40 (h : -(a + b) = -b ∨ -(-(a + -b) + -b) = a) :
    b + 2 • (a + -(a + -b)) = b + 3 • (a + -(a + -b)) := by
  suffices -(b + 2 • (a + -(a + -b))) = -b ∧ -(b + 3 • (a + -(a + -b))) = -b by
    rw [add_comm b, add_comm b] at this
    replace this := mann_39 this.1 this.2
    rwa [add_comm b, add_comm b]
  rcases h with h | h
  · exact ⟨mann_38 (by lia) h, mann_38 (by lia) h⟩
  · exact ⟨mann_37 (by lia) h, mann_37 (by lia) h⟩

theorem exists_idempotent : ∃ x : α, x + x = x := by
  obtain ⟨a, b, h⟩ := winker (α := α)
  let c := b + 2 • -(a + -b)
  have k₁ : a + c = c := by
    unfold c
    rw [← add_assoc, h]
  have k₂ : -b = -c := by
    rw [← mann_38 (show 1 ≤ 2 by lia) (congrArg (-·) h), smul2,
      show b + (a + -(a + -b) + (a + -(a + -b))) = a + (a + b) + (-(a + -b) + -(a + -b)) by ac_rfl,
      h, h, ← smul2]
  have k₃ : c + -(a + -c) = c := by
    rw [← k₂]
    conv_lhs => simp only [c]
    nth_rw 1 [add_assoc, smul2, ← h, ← h, ← h,
      show a + (a + (a + b)) + (-(a + -b) + -(a + -b) + -(a + -b)) =
        b + ((a + -(a + -b)) + (a + -(a + -b)) + (a + -(a + -b))) by ac_rfl,
      ← smul3, ← mann_40 (.inl (by rw [h])), smul2,
      show b + (a + -(a + -b) + (a + -(a + -b))) =
        a + (a + b) + (-(a + -b) + -(a + -b)) by ac_rfl, ← smul2, h, h]
  have k₄ : -(-(c + -c) + -c) = c := by
    nth_rw 4 [← robbins c (a + -c)]
    nth_rw 3 [← k₃]
    nth_rw 1 [← k₁]
    ac_rfl
  replace k₄ := mann_40 (.inr k₄)
  set d := c + -(c + -c)
  have fin : 3 • d + d = 2 • d + d := by
    change _ + (c + -(c + -c)) = _ + (c + -(c + -c))
    simp_rw [← add_assoc]
    rw [add_comm (2 • d), k₄, add_comm (3 • d)]
  use 3 • d
  nth_rw 2 [smul3]
  rw [← add_assoc, ← add_assoc _ d]
  iterate 3 rw [fin, ← smul_succ (by lia)]

end Idempotence

theorem exists_zero : ∃ z : α, ∀ a, a + z = a := by
  obtain ⟨a, ha⟩ := exists_idempotent (α := α)
  refine ⟨-(a + -a), fun x ↦ ?_⟩
  set z := -(a + -a)
  have k₁ : a = -(-a + z) := by nth_rw 1 [← robbins a a, ha]
  have k₂ (x) : a + x = -(-(a + x) + -(a + x + -a)) := by
    nth_rw 1 [← robbins (a + x) a, show a + x + a = a + a + x by ac_rfl, ha]
  have k₃ (x) : x = -(-(x + -a + z) + -(x + a)) := by
    nth_rw 1 [← robbins x (-a + z), ← k₁, add_assoc]
  have k₄ : -a = -(-(a + -a + -a) + a) := by
    nth_rw 1 [← robbins (-a) (a + -a), ← k₁]
    ac_rfl
  have k₅ : a = -(-(a + -a + z) + -a) := by nth_rw 1 [k₃ a, ha]
  have k₆ : a = -(-(a + -a + -a) + -a) := by
    nth_rw 1 [← robbins a (a + -a + -a), add_comm a (-(_ + _)), ← k₄, ← add_assoc, ← add_assoc, ha]
  have k₇ : -(a + -a + -a) = z := by rw [← robbins (-(a + -a + -a)) a, ← k₄, ← k₆, add_comm]
  have k₈ : -a = -(a + z) := by rw [k₄, k₇, add_comm]
  have k₉ : a + z = a := by
    rw [k₂ z, ← k₈]
    conv_rhs => rw [k₅]
    ac_rfl
  nth_rw 2 [k₃ x]
  rw [← robbins (x + z) a, add_assoc, add_comm z, k₉]
  ac_rfl

theorem neg_neg : - -a = a := by
  obtain ⟨z, hz⟩ := exists_zero (α := α)
  have k₁ (x) : z = -(-x + - -x) := by rw [← robbins z x, add_comm z, hz, add_comm z, hz]
  have k₂ (x : α) : -x = - -(-x + - - -x) := by
    nth_rw 1 [← robbins (-x) (- -x), ← k₁, add_comm z, hz]
  have k₃ (x : α) : - - -x = -x := by
    nth_rw 1 [← robbins (- - -x) (-x), add_comm _ (- -x), ← k₁ (-x), hz, add_comm, ← k₂]
  simpa only [robbins] using k₃ (-(a + z) + -(a + -z))

theorem huntington : -(-a + -b) + -(-a + b) = a := by
  conv_rhs => rw [← neg_neg a, ← robbins (-a) b, neg_neg, add_comm]

instance : Zero α where zero := -(default + -default)
instance : One α where one := default + -default

lemma add_neg_self_const : a + -a = b + -b := by
  nth_rw 1 [← huntington (-b) (-a), ← huntington b (-a),
    ← huntington (-a) (-b), ← huntington a (-b)]
  ac_rfl

lemma neg_zero : -(0 : α) = 1 := neg_neg _
lemma neg_one : -(1 : α) = 0 := rfl
lemma add_neg_self : a + -a = 1 := add_neg_self_const ..

lemma add_zero : a + 0 = a := by
  have l₀ := huntington (0 : α) 0
  rw [add_comm _ 0, add_neg_self, neg_zero, ← neg_one] at l₀
  have l₁ := add_neg_self (1 : α)
  rw [← l₀, add_comm, add_assoc, add_comm (-1), add_neg_self] at l₁
  have s₁ := add_neg_self (1 + 1 : α)
  rw [add_assoc, add_comm _ (-_), l₁] at s₁
  have s₀ := neg_one (α := α)
  rw [← l₀, s₁, neg_one] at s₀
  rw [← huntington a a, add_comm _ a, add_neg_self, neg_one, add_assoc, s₀]

lemma add_self : a + a = a := by
  conv_rhs => rw [← neg_neg a, ← huntington (-a) (-a)]
  rw [add_comm _ (-a), add_neg_self, neg_one, add_zero, neg_neg, neg_neg]

lemma min_add_left : -(-a + -b) + a = a := by
  nth_rw 2 [← huntington a b]
  rw [← add_assoc, add_self, huntington]

lemma min_add_distrib : -(-a + -(b + c)) = -(-a + -b) + -(-a + -c) := by
  nth_rw 1 [← huntington (-_) b, neg_neg, add_assoc, ← neg_neg b, ← neg_neg c, min_add_left,
    ← huntington (-_) c, ← huntington (-(_ + b)) c]
  have l₁ := huntington (-(-a + -b)) c
  have l₂ := huntington (-(-a + -c)) b
  simp only [neg_neg] at l₁ l₂ ⊢
  rw [show -a + -(b + c) + b + -c = -a + b + (-(c + b) + -c) by ac_rfl,
    show -a + -(b + c) + b + c = -a + ((b + c) + -(b + c)) by ac_rfl]
  conv_lhs => enter [2, 1, 1, 2, 1]; rw [← neg_neg b, ← neg_neg c]
  rw [min_add_left, add_neg_self_const _ a, show -a + (a + -a) = a + (-a + -a) by ac_rfl, add_self,
    add_neg_self, neg_one, add_zero, ← add_self (-_), add_assoc (-_), l₁, ← l₂]
  ac_rfl

lemma add_min_distrib : a + -(-b + -c) = -(-(a + b) + -(a + c)) := by
  simpa [neg_neg] using congr(-$(min_add_distrib (-a) (-b) (-c)))

instance : Lattice α where
  le a b := a + b = b
  le_refl := add_self
  le_trans _ _ _ h₁ h₂ := by rw [← h₂, ← add_assoc, h₁]
  le_antisymm _ _ h₁ h₂ := by rwa [← h₂, add_comm]
  sup a b := a + b
  le_sup_left _ _ := by rw [← add_assoc, add_self]
  le_sup_right _ _ := by rw [add_comm, add_assoc, add_self]
  sup_le _ _ _ h₁ h₂ := by rw [add_assoc, h₂, h₁]
  inf a b := -(-a + -b)
  inf_le_left := min_add_left
  inf_le_right a b := add_comm (-b) _ ▸ min_add_left ..
  le_inf _ _ _ h₁ h₂ := by rw [add_min_distrib, h₁, h₂]

/-- Derive a Boolean algebra from a Robbins algebra. -/
instance : BooleanAlgebra α where
  compl := (-·)
  top := 1
  bot := 0
  inf_compl_le_bot _ := by
    change -(_ + _) + _ = _
    rw [add_zero, add_neg_self, neg_one]
  top_le_sup_compl _ := by
    change _ + (_ + _) = (_ + _)
    rw [add_neg_self, add_self]
  le_top _ := by
    change _ + _ = _
    nth_rw 1 [← add_neg_self, ← add_assoc, add_self, add_neg_self]
  bot_le _ := by
    change _ + _ = _
    rw [add_comm, add_zero]
  le_sup_inf _ _ _ := by
    change -(-(_ + _) + -(_ + _)) + _ = _
    rw [← add_min_distrib]
    exact add_self _

end RobbinsAlgebra
