/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Tactic.NthRewrite

/-!
# Minimal Sheffer stroke axioms for Boolean algebra

The Sheffer stroke `a | b` is `(a ⊓ b)ᶜ`, i.e. the NAND gate on `Bool`.
All functions with `Bool` inputs and outputs can be expressed using only this operator.

This file shows that for non-empty magmas whose operator is the Sheffer stroke,
satisfying either of two axiom sets is equivalent to being a Boolean algebra.
The first set, with two axioms, was proven equivalent by Robert Veroff:
1. `|` is commutative
2. `∀ a b c, a | b | (a | (b | c)) = a`

Instead of deriving Sheffer's 1913 axioms as done in [the original paper](veroff),
we derive a `BooleanAlgebra` instance directly: `aᶜ := a | a`, `a ≤ b := aᶜ = a | b`,
`a ⊔ b := aᶜ | bᶜ`, `a ⊓ b = (a | b)ᶜ`, `⊤ = a | aᶜ` and `⊥ = ⊤ᶜ`.

The second set consists of just the single axiom `∀ a b c, a | (b | a | a) | (b | (c | a)) = b`.
Its equivalence was conjectured by Stephen Wolfram and proved by William McCune et al.
shortly after Veroff's result. We reduce to Veroff's axioms rather than Sheffer's 1913 axioms,
following [the original paper's](mccune) Otter derivation of commutativity closely
(with certain steps condensed), after which the other axiom becomes very easy to derive.

Both axiom sets are minimal in the sense that for any set using fewer total Sheffer strokes,
non-Boolean algebra models exist.
-/

/-- Veroff's two axioms for Boolean algebra. -/
class VeroffAlgebra (α : Type*) extends Inhabited α where
  /-- The Sheffer stroke function -/
  f : α → α → α
  /-- The Sheffer stroke is commutative -/
  comm (a b : α) : f a b = f b a
  /-- Veroff's axiom -/
  veroff (a b c : α) : f (f a b) (f a (f b c)) = a

@[inherit_doc] scoped[VeroffAlgebra] infixl:70 " | " => VeroffAlgebra.f

variable {α : Type*}

/-- Derive a Veroff algebra from a Boolean algebra. -/
def BooleanAlgebra.veroffAlgebra [BooleanAlgebra α] : VeroffAlgebra α where
  default := ⊥
  f a b := (a ⊓ b)ᶜ
  comm a b := by rw [inf_comm]
  veroff a b c := by
    rw [← compl_sup, compl_compl, ← inf_sup_left, compl_inf, ← sup_assoc, sup_compl_eq_top,
      top_sup_eq, inf_top_eq]

namespace VeroffAlgebra

variable [VeroffAlgebra α] (a b c : α)

instance : Compl α where compl a := a | a

lemma compl_def : aᶜ = a | a := rfl

lemma meredith : a | b | aᶜ = a := by
  have l1 := veroff (a | b) a (b | a)
  rw [veroff a b a, comm _ a, comm _ a] at l1
  have l2 := veroff a a (a | b)
  rwa [l1, comm] at l2

lemma compl_compl : aᶜᶜ = a := meredith a a

lemma ababc : a | (b | (a | (b | c))) = a | (b | c) := by
  have l1 := veroff a (b | c) bᶜ
  rw [meredith, comm _ b] at l1
  have l2 := veroff (a | (b | c)) b a
  rwa [l1, comm, comm _ b] at l2

lemma abba : a | b | b | a = aᶜ := by
  have l1 := (ababc a (a | b) b).symm
  rwa [comm _ b, veroff, comm a, comm b] at l1

lemma aba_abb : a | (b | a) = a | bᶜ := by
  rw [← ababc, comm b, comm _ (b | a), abba]

lemma sheffer : a | (b | bᶜ) = aᶜ := by
  have l1 := veroff a (b | b | b) b
  rw [abba, ← aba_abb, ← compl_def, comm _ (b | a), comm b] at l1
  have l2 := veroff (a | (b | bᶜ)) (a | (b | bᶜ | (b | (bᶜ | b)))) a
  nth_rw 1 [veroff a, veroff, comm _ bᶜ, l1] at l2
  exact l2.symm

instance : PartialOrder α where
  le a b := aᶜ = a | b
  le_refl a := rfl
  le_trans a b c h₁ h₂ := by
    have h₁' : aᶜ | bᶜ = b := by rw [h₁, comm a, meredith]
    have h₂' : bᶜ | cᶜ = c := by rw [h₂, comm b, meredith]
    have l1 := veroff (a | aᶜ) (a | (aᶜ | bᶜ)) bᶜ
    nth_rw 1 [veroff a, h₁', comm _ b, meredith, comm _ aᶜ, h₁, comm a b, abba] at l1
    have l2 := veroff a bᶜ cᶜ
    rw [l1, h₂', comm _ aᶜ, comm] at l2
    have l3 := veroff (a | c) aᶜ a
    rwa [meredith, l2] at l3
  le_antisymm a b h₁ h₂ := by rw [← compl_compl a, h₁, comm, ← h₂, compl_compl]

lemma le_def : a ≤ b ↔ aᶜ = a | b := Iff.rfl

lemma le_sup_left : a ≤ aᶜ | bᶜ := by
  rw [le_def]
  have l1 := (meredith aᶜ bᶜ).symm
  rwa [compl_compl, comm] at l1

lemma inf_le_left : (a | b)ᶜ ≤ a := by
  rw [le_def, compl_compl]
  have l2 := (meredith (a | b) aᶜ).symm
  rwa [meredith a, comm _ _ᶜ] at l2

lemma sup_le (h₁ : a ≤ c) (h₂ : b ≤ c) : aᶜ | bᶜ ≤ c := by
  rw [h₂]
  have l1 := (abba (aᶜ | (b | c)) (b | c | c)).symm
  rw [comm _ (aᶜ | _), ← le_def] at l1
  convert l1 using 1
  have l2 := veroff (b | c) c a
  rw [comm _ a, ← h₁, comm, comm _ aᶜ] at l2
  nth_rw 1 [l2, comm (b | c) c, comm b, veroff]

lemma compl_le_compl (h : a ≤ b) : bᶜ ≤ aᶜ := by
  rw [le_def, compl_compl]
  have l1 := (meredith b a).symm
  rwa [comm b, ← h, comm] at l1

lemma compl_le_compl_iff_le : aᶜ ≤ bᶜ ↔ b ≤ a where
  mp h := by simpa only [compl_compl] using compl_le_compl _ _ h
  mpr h := compl_le_compl _ _ h

instance : Lattice α where
  sup a b := aᶜ | bᶜ
  le_sup_left := le_sup_left
  le_sup_right a b := comm aᶜ bᶜ ▸ le_sup_left b a
  sup_le := sup_le
  inf a b := (a | b)ᶜ
  inf_le_left := inf_le_left
  inf_le_right a b := comm a b ▸ inf_le_left b a
  le_inf a b c h₁ h₂ := by
    rw [← compl_le_compl_iff_le] at h₁ h₂ ⊢
    simpa only [compl_compl] using sup_le _ _ _ h₁ h₂

lemma sup_def : a ⊔ b = aᶜ | bᶜ := rfl

lemma inf_def : a ⊓ b = (a | b)ᶜ := rfl

/-- The top element, equal to `a | aᶜ` for any `a`. -/
def top : α :=
  default | defaultᶜ

lemma f_compl_const : a | aᶜ = b | bᶜ := by
  have l1 := meredith (b | bᶜ) a
  rwa [← sheffer (b | bᶜ) a, comm _ (a | aᶜ), sheffer, ← compl_compl (_ | a),
    ← sheffer (_ | a)ᶜ a, comm _ (a | aᶜ), meredith] at l1

lemma sup_compl_eq_top : a ⊔ aᶜ = top := f_compl_const aᶜ default

lemma compl_inf : (a ⊓ b)ᶜ = aᶜ ⊔ bᶜ := by simp_rw [inf_def, sup_def, compl_compl]

lemma le_iff_compl_sup : a ≤ b ↔ aᶜ ⊔ b = top := by
  rw [le_def, sup_def, compl_compl]
  constructor <;> intro h
  · have l1 : a | aᶜ = a | (a | b) := congrArg (a | ·) h
    rw [f_compl_const a default, comm _ b, aba_abb] at l1
    exact l1.symm
  · rw [← sup_compl_eq_top a, sup_def, compl_compl] at h
    have l1 := veroff (a | b) aᶜ a
    rwa [meredith, ← h, compl_def, veroff] at l1

/-- Derive a Boolean algebra from a Veroff algebra. -/
instance : BooleanAlgebra α where
  top := top
  bot := topᶜ
  inf_compl_le_bot a := by
    rw [← compl_compl (_ ⊓ _), compl_le_compl_iff_le, compl_inf, compl_compl, sup_comm]
    exact (sup_compl_eq_top a).symm.le
  top_le_sup_compl a := (sup_compl_eq_top a).symm.le
  le_top a := by rw [le_def, ← sup_compl_eq_top a, sup_def, compl_compl, comm aᶜ, sheffer]
  bot_le a := by
    rw [← compl_le_compl_iff_le, compl_compl, le_def, ← sup_compl_eq_top a, sup_def, sheffer]
  le_sup_inf a b c := by
    rw [le_iff_compl_sup, compl_inf, ← sup_assoc, sup_comm, ← compl_compl (b ⊓ c), compl_inf,
      ← le_iff_compl_sup]
    nth_rw 3 [← sup_idem a]
    rw [sup_sup_sup_comm]
    apply sup_le_sup <;>
    rw [le_iff_compl_sup, compl_compl, sup_left_comm, sup_comm, sup_comm a, sup_compl_eq_top]

end VeroffAlgebra

/-- The single-axiom algebra shown to be equivalent to Boolean algebra by McCune et al. -/
class SingleShefferAlgebra (α : Type*) extends Inhabited α where
  /-- The Sheffer stroke function -/
  f : α → α → α
  /-- The single axiom of this algebra -/
  rule (a b c : α) : f (f a (f (f b a) a)) (f b (f c a)) = b

@[inherit_doc] scoped[SingleShefferAlgebra] infixl:70 " | " => SingleShefferAlgebra.f

variable {α : Type*}

/-- Derive a `SingleShefferAlgebra` from a Boolean algebra. -/
def BooleanAlgebra.singleShefferAlgebra [BooleanAlgebra α] : SingleShefferAlgebra α where
  default := ⊥
  f a b := (a ⊓ b)ᶜ
  rule a b c := by
    rw [← compl_sup, compl_compl, compl_inf, compl_compl, inf_sup_left, inf_compl_eq_bot,
      sup_bot_eq, inf_of_le_right inf_le_right, ← inf_sup_left, compl_inf, sup_left_comm,
      sup_compl_eq_top, sup_top_eq, inf_top_eq]

namespace SingleShefferAlgebra

variable [SingleShefferAlgebra α] (a b c : α)

lemma eq74 : a | (a | a | a) = a | a := by
  have l1 := rule (a | (a | a | a)) (a | (a | a | a)) a
  have l2 := rule a a (a | a | a | (a | (a | a | a) | (a | a | a) | (a | a | a)))
  have l3 := rule (a | a | a) (a | (a | a | a)) a
  rw [rule a a (a | a)] at l1 l3
  rw [l3] at l2
  rwa [l2, eq_comm] at l1

lemma eq75 : a | (a | a | a) | (a | a) = a := by
  have := rule a a (a | a)
  nth_rw 2 [eq74 a] at this
  exact this

lemma eq76 : a | a | (a | (b | a)) = a := by
  have := rule a a b
  rwa [eq74 a] at this

lemma eq77 : a | (b | b | a | a) | b = b | b := by
  have l1 := rule a (b | b) (a | b | (b | (a | b | b) | (a | b) | (a | b)))
  have l2 := rule (a | b) (b | (a | b | b)) a
  rw [rule b a a] at l2
  rwa [l2, eq76 b (a | b)] at l1

lemma eq79 : a | (b | a | (b | a) | a | a) = b | a := by
  have := rule (b | a) (a | (b | a | (b | a) | a | a)) (b | a | (b | a))
  rwa [rule a (b | a | (b | a)) b, eq77 a (b | a), eq75 (b | a), eq_comm] at this

lemma eq80 : a | a | (b | a) = a := by
  have := eq76 a (b | a | (b | a) | a)
  rwa [eq79 a b] at this

lemma eq84 : a | b | (a | b) | b = a | b := by
  have := eq80 (a | b) (b | b)
  rwa [eq80 b a] at this

lemma eq85 : a | (b | a | a) = b | a := by
  have := eq79 a b
  rwa [eq84 b a] at this

lemma eq89 : a | (a | b | (c | b)) = a | b := by
  have l1 := rule (a | (c | b)) (a | b) (c | b | (c | b))
  have l2 := rule b a c
  rw [eq85 b a] at l2
  rwa [eq85 (a | (c | b)) (a | b), l2, eq80 (c | b) a] at l1

lemma eq91 : a | (b | a | a) = a | b := by
  have := (eq89 a (b | a | a) b).symm
  rwa [rule a b (b | a)] at this

theorem comm : a | b = b | a := eq91 a b ▸ eq85 a b

/-- Derive a Veroff (and hence Boolean) algebra from a `SingleShefferAlgebra`. -/
instance : VeroffAlgebra α where
  f := f
  comm := comm
  veroff a b c := by
    have := rule b a c
    rwa [eq91, comm b, comm c] at this

end SingleShefferAlgebra
