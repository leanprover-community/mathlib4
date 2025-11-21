/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.PNat.Notation

/-!
# Huntington and Robbins algebras

A Huntington algebra is a type endowed with a commutative
semigroup, together with a complement operator such that
`(xᶜ + yᶜ)ᶜ + (xᶜ + y)ᶜ = x`.

A Robbins algebra is a type endowed with a commutative
semigroup, together with a complement operator such that
`((x + y)ᶜ + (x + yᶜ)ᶜ)ᶜ = x`.


They are equivalent to Boolean algebras.

-/

@[expose] public section

namespace PNat

variable {α : Type*}

def smulAux [Add α] (x : α) : ℕ → α
  | 0 => x
  | 1 => x
  | n + 2 => smulAux x (n + 1) + x

instance [Add α] : HSMul ℕ+ α α where
  hSMul n x := smulAux x n.val

theorem one_smul [Add α] (x : α) : (1 : ℕ+) • x = x := rfl

theorem add_one_smul [Add α] (n : ℕ+) (x : α) : (n + 1) • x = n • x + x := by
  induction n with
  | one => simp [HSMul.hSMul, smulAux]
  | succ n => simp [HSMul.hSMul, Nat.add_assoc, smulAux]

theorem add_smul [AddSemigroup α] (m n : ℕ+) (x : α) :
    (m + n) • x = m • x + n • x := by
  induction n with
  | one => rw [add_one_smul, one_smul]
  | succ n hind => simp [← add_assoc, add_one_smul, hind]

theorem smul_smul [AddSemigroup α] (m n : ℕ+) (x : α) :
    m • n • x = (m * n) • x := by
  induction m generalizing x with
  | one => simp [one_smul, one_mul]
  | succ m hind => simp [add_one_mul, hind, add_smul, one_smul]

end PNat

/-- Huntington algebras -/
class HuntingtonAlgebra (α : Type*) extends AddCommSemigroup α, HasCompl α where
  /-- The Robbins equation -/
  huntington (a b : α) : (aᶜ + b)ᶜ + (aᶜ + bᶜ)ᶜ = a

/-- Robbins algebras -/
class RobbinsAlgebra (α : Type*) extends AddCommSemigroup α, HasCompl α where
  /-- The Robbins equation -/
  robbins (a b : α) : ((aᶜ + b)ᶜ + (a + b)ᶜ)ᶜ = b

def BooleanAlgebra.huntingtonAlgebra (α : Type*) [BooleanAlgebra α] :
    HuntingtonAlgebra α where
  add x y := x ⊔ y
  add_comm x y := sup_comm x y
  add_assoc := sup_assoc
  huntington x y := by
    change (xᶜ ⊔ y)ᶜ ⊔ (xᶜ ⊔ yᶜ)ᶜ = x
    simp only [compl_sup, compl_compl]
    rw [sup_comm, sup_inf_inf_compl]

def BooleanAlgebra.robbinsAlgebra (α : Type*) [BooleanAlgebra α] :
    RobbinsAlgebra α where
  add x y := x ⊔ y
  add_comm x y := sup_comm x y
  add_assoc := sup_assoc
  robbins x y := by
    change ((xᶜ ⊔ y)ᶜ ⊔ (x ⊔ y)ᶜ)ᶜ = y
    rw [isCompl_compl.symm.compl_eq_iff]
    simp only [compl_sup, compl_compl, inf_comm x, inf_comm xᶜ,
      sup_inf_inf_compl]

namespace HuntingtonAlgebra

variable {α : Type*} [HuntingtonAlgebra α]

@[simp] theorem add_compl_eq_compl_add_compl_compl (a : α) :
    aᶜ + aᶜᶜ = a + aᶜ := by
  nth_rewrite 1 [← huntington aᶜᶜ aᶜ]
  nth_rewrite 1 [← huntington aᶜ aᶜ]
  rw [eq_comm]
  nth_rewrite 1 [← huntington aᶜ aᶜᶜ]
  nth_rewrite 1 [← huntington a aᶜᶜ]
  simp only [add_assoc]
  apply congr_arg₂
  · rw [add_comm]
  simp only [← add_assoc]
  apply congr_arg₂
  · rw [add_comm, add_comm aᶜ]
  · rw [add_comm]

theorem compl_compl (a : α) : aᶜᶜ = a := by
  rw [← huntington aᶜᶜ aᶜ, eq_comm]
  nth_rewrite 1 [← huntington a aᶜᶜ]
  rw [add_comm aᶜᶜᶜ aᶜᶜ, add_comm aᶜᶜᶜ aᶜ]
  simp only [add_compl_eq_compl_add_compl_compl]
  rw [add_comm]

theorem add_compl (a b : α) : a + aᶜ = b + bᶜ := by
  rw [← huntington aᶜ bᶜ]
  nth_rewrite 1 [← huntington a bᶜ]
  rw [eq_comm]
  nth_rewrite 1 [← huntington bᶜ aᶜ]
  nth_rewrite 1 [← huntington b aᶜ]
  simp only [← add_assoc]
  apply congr_arg₂
  · rw [add_comm bᶜ]
    simp only [add_assoc]
    apply congr_arg₂ _ rfl
    rw [add_comm]
    apply congr_arg₂ <;>
    rw [add_comm]
  rw [add_comm]

theorem compl_eq_iff (a b : α) : aᶜ = b ↔ a = bᶜ := by
  suffices ∀ {a b : α} (h : aᶜ = b), a = bᶜ by
    exact ⟨this, fun h ↦ (this h.symm).symm⟩
  intro a b h
  rw [← h, compl_compl]

theorem compl_eq_compl_iff (a b : α) : aᶜ = bᶜ ↔ a = b := by
  constructor
  · intro h
    rw [← compl_compl a, h, compl_compl]
  · intro h
    rw [h]

variable [Inhabited α]

def univ : α := default + defaultᶜ

theorem add_compl' (a : α) : a + aᶜ = univ :=
  add_compl a default

theorem add_univ_compl (a : α) : a + univᶜ = a := by
  have ha : (univ : α) ᶜ = (univ + univ)ᶜ + univᶜ := by
    simpa [compl_compl, add_compl', eq_comm] using
      huntington univᶜ (univ : α)
  have ha' : (univ : α) = univ + (univ + univ)ᶜ := by
    calc univ = univ + univᶜ := (add_compl' _).symm
        _ = univ + (univ + univ)ᶜ + univᶜ := by
          nth_rewrite 1 [ha]; simp only [add_assoc]
        _ = univ + univᶜ + (univ + univ)ᶜ := add_right_comm _ _ _
        _ = univ + (univ + univ)ᶜ := by rw [add_compl']
  have hb : (univ : α) + univ = univ := by
    calc (univ : α) + univ = univ + (univ + (univ + univ)ᶜ) := by
          nth_rewrite 2 [ha']
          simp only
        _ = (univ + univ) + (univ + univ)ᶜ := by rw [add_assoc]
        _ = univ := by
          rw [add_compl']
  rw [hb, eq_comm] at ha
  nth_rewrite 1 [← huntington a a]
  rw [add_comm aᶜ, add_compl', add_comm, ← add_assoc, ha, ← add_compl' a, add_comm a, huntington]

theorem add_self_eq (a : α) : a + a = a := by
  rw [← compl_compl (a + a), ← add_univ_compl (a + a)ᶜ,
    ← add_compl' a]
  have := huntington aᶜ a
  simp only [compl_compl] at this
  rw [this, compl_compl]

abbrev inf (a b : α) := (aᶜ + bᶜ)ᶜ

example (a b : α) : inf a b + inf a bᶜ = a :=
  huntington a bᶜ

/- in a boolean algebra, a ≤ b means that a ⊔ b = b or a ⊓ b = b,
while ⊔ = + and ⊓ = * -/

example (a : α) : inf a univ = a := by
  unfold inf
  rw [add_univ_compl, compl_compl]

example (a : α) : inf a aᶜ = univᶜ := by
  unfold inf
  rw [add_compl']

example (a b c : α) : inf (inf a b) c = inf a (inf b c) := by
  unfold inf
  simp only [compl_compl, add_assoc]

example (a b : α) : a + b = (inf aᶜ bᶜ)ᶜ := by
  unfold inf
  simp [compl_compl]

example (a : α) : inf a a = a := by
  unfold inf
  simp [add_self_eq, compl_compl]

example (a : α) :  a + univ = univ := by
  rw [← add_compl' a, ← add_assoc, add_self_eq]

example (a : α) : inf a univᶜ = univᶜ := by
  unfold inf
  simp only [compl_compl, ← add_compl' aᶜ, ← add_assoc, add_self_eq]

example (a b : α) : a + inf a b = a := by
  unfold inf
  nth_rewrite 1 [← huntington a bᶜ]
  rw [add_comm, ← add_assoc, add_self_eq, huntington]

example (a b : α) : inf a (a + b) = a := by
  unfold inf
  rw [compl_eq_iff]
  nth_rewrite 2 [← compl_compl a]
  nth_rewrite 1 [← compl_compl b]
  nth_rewrite 1 [← huntington aᶜ]
  rw [add_comm, ← add_assoc, add_self_eq, huntington]

theorem add_eq_iff_compl_add_compl_eq (a b : α) :
    a + b = b ↔ aᶜ + bᶜ = aᶜ := by
  suffices ∀ {a b : α} (h : a + b = b), aᶜ + bᶜ = aᶜ by
    refine ⟨this, fun h ↦ ?_⟩
    rw [← compl_compl a, ← compl_compl b, add_comm]
    apply this
    rwa [add_comm] at h
  intro a b h
  rw [← compl_eq_compl_iff, ← compl_compl a] at h
  nth_rewrite 1 [← compl_compl b] at h
  rw [← h]
  nth_rewrite 1 [← huntington aᶜ _]
  rw [add_comm, ← add_assoc, add_self_eq, huntington]

def booleanAlgebra' : BooleanAlgebra α := {
  le a b := (a + b = b)
  le_refl := add_self_eq
  le_trans a b c h h' := by rw [← h', ← add_assoc, h]
  le_antisymm a b h h' := by rw [← h', add_comm, h]
  sup x y := x + y
  le_sup_left a b := by rw [← add_assoc, add_self_eq]
  le_sup_right a b := by rw [add_comm, add_assoc, add_self_eq]
  sup_le a b c h h' := by rw [add_assoc, h', h]
  inf x y := (xᶜ + yᶜ)ᶜ
  inf_le_left a b := by
    rw [add_eq_iff_compl_add_compl_eq, compl_compl,
      add_comm, ← add_assoc, add_self_eq]
  inf_le_right a b := by
    rw [add_eq_iff_compl_add_compl_eq, compl_compl,
      add_assoc, add_self_eq]
  le_inf a b c h h' := by
    rw [add_eq_iff_compl_add_compl_eq] at h h' ⊢
    rw [compl_compl, ← add_assoc, h, h']
  le_sup_inf a b c := by
    -- (a ⊔ b) ⊓ (a ⊔ c) + a ⊔ b ⊓ c = a ⊔ b ⊓ c
    change inf (a + b) (a + c) + (a + inf b c) = a + inf b c
    unfold inf
    sorry
  top := univ
  bot := univᶜ
  inf_compl_le_bot a := by
    change inf a aᶜ + univᶜ = univᶜ
    unfold inf
    rw [compl_compl, add_comm aᶜ, add_compl', add_univ_compl]
  top_le_sup_compl a := by
    change univ + (a + aᶜ) = (a + aᶜ)
    rw [add_compl', add_self_eq]
  le_top a := by
    rw [← add_compl' a, ← add_assoc, add_self_eq]
  bot_le a := by
    rw [add_comm, add_univ_compl] }

end HuntingtonAlgebra

namespace RobbinsAlgebra

open PNat

variable {α : Type*} [RobbinsAlgebra α]

section Winker

/-- A Robbins algebra where every element is idempotent is a Huntington algebra -/
def huntingtonAlgebra_of_compl_compl_eq (h : ∀ a : α, aᶜᶜ = a) :
    HuntingtonAlgebra α where
  huntington a b := by
    have := robbins bᶜ aᶜ
    rw [h, add_comm b, add_comm bᶜ] at this
    rw [← h (_ + _), this, h]


end Winker

section Dahn

/-- A useful notation -/
abbrev δ (x y : α) := (xᶜ + y)ᶜ

theorem delta_add_delta (x y : α) :
    δ (x + y) (δ x y) = y := by
  rw [δ, add_comm, robbins x y]

theorem delta_compl_add_add (x y z : α) :
    δ (xᶜ + y) z = ((δ x y) + z)ᶜ := by
  rw [δ]

theorem delta_compl_right (x y : α) :
    δ x yᶜ = δ y xᶜ := by
  rw [δ, δ, add_comm]

theorem delta_eq_of_left_compl_eq {x x' : α} (h : xᶜ = x'ᶜ) (y : α) :
    δ x y = δ x' y := by
  simp only [δ, h]

/-- The Dahn function -/
def dahn (x : α) : ℕ → α
  | 0 => (xᶜ + x)ᶜ
  | n + 1 => dahn x n + x

@[inherit_doc] infix:100 " @ " => dahn

theorem dahn_zero (x : α) : x @ 0 = (xᶜ + x)ᶜ := rfl

theorem dahn_succ (x : α) (n : ℕ) :
    x @ (n + 1) = x @ n + x := rfl

theorem dahn_add_coe_PNat (x : α) (m : ℕ) (n : ℕ+) :
    x @ (m + n) = x @ m + n • x := by
  induction n with
  | one => simp [dahn_succ, one_smul]
  | succ n hind =>
    simp only [add_coe, val_ofNat, ← add_assoc, dahn_succ, hind,
      add_one_smul]

theorem dahn_PNat (x : α) (n : ℕ+) :
    dahn x n = x @ 0 + n • x := by
  rw [← zero_add (n : ℕ), dahn_add_coe_PNat]

theorem dahn_add_dahn (x : α) {m n p q : ℕ} (h : m + n = p + q) :
    x @ m + x @ n = x @ p + x @ q := sorry

theorem dahn_of_one_add_of_three (x : α) :
    (x @ 1 + x @ 3)ᶜ = (x @ 3)ᶜ := sorry

theorem dahn_one (x : α) : x @ 1 = x := by
  simp only [dahn_succ, dahn_zero]
  change δ x x + x = x

theorem winker {α : Type*} [RobbinsAlgebra α] (x : α) :
    ∃ y, (x + y)ᶜ = yᶜ := by
  use dahn x 3
  conv_rhs => rw [← dahn_of_one_add_of_three]
  congr
  simp [dahn_succ, dahn_zero]


def booleanAlgebra (α : Type*) [RobbinsAlgebra α] :
    BooleanRing α := sorry

end Dahn

#min_imports
