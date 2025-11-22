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

-- Huntington, 4.9
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

-- Huntington 4.10
@[simp] theorem compl_compl (a : α) : aᶜᶜ = a := by
  rw [← huntington aᶜᶜ aᶜ, eq_comm]
  nth_rewrite 1 [← huntington a aᶜᶜ]
  rw [add_comm aᶜᶜᶜ aᶜᶜ, add_comm aᶜᶜᶜ aᶜ]
  simp only [add_compl_eq_compl_add_compl_compl]
  rw [add_comm]

-- Huntington 4.11
theorem add_compl' (a b : α) : a + aᶜ = b + bᶜ := by
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
  rw [← h, compl_compl a]

theorem compl_eq_compl_iff (a b : α) : aᶜ = bᶜ ↔ a = b := by
  constructor
  · intro h
    rw [← compl_compl a, h, compl_compl]
  · intro h
    rw [h]

instance : Mul α where
  mul a b := (aᶜ + bᶜ)ᶜ

-- Huntington 4.7
theorem mul_def (a b : α) : a * b = (aᶜ + bᶜ)ᶜ := rfl

--
theorem mul_comm (a b : α) : a * b = b * a := by
  simp only [mul_def, add_comm]

-- Huntington 4.8
theorem add_mul_mul_compl (a b : α) : a * b + a * bᶜ = a :=
  huntington a bᶜ

-- Huntington 4.19
theorem mul_assoc (a b c : α) : a * b * c = a * (b * c) := by
  simp [mul_def, compl_compl, add_assoc]

-- Huntington 4.20
theorem add_eq_compl_mul (a b : α) : a + b = (aᶜ * bᶜ)ᶜ := by
  simp [mul_def, compl_compl]

variable [Inhabited α]

-- Huntington 4.12
instance : One α := ⟨default + defaultᶜ⟩

-- Huntington 4.12
@[simp] theorem add_compl (a : α) : a + aᶜ = 1 :=
  add_compl' a default

-- Huntington 4.12
theorem one_def (a : α) : 1 = a + aᶜ :=
  (add_compl a).symm

-- Huntington 4.13
instance : Zero α := ⟨1ᶜ⟩

@[simp] theorem one_compl : (1 : α)ᶜ = 0 := rfl

@[simp] theorem zero_compl : (0 : α)ᶜ = 1 := by
  rw [← one_compl, compl_compl]

-- Huntington 4.15
@[simp] theorem add_zero (a : α) : a + 0 = a := by
  have ha : (1 : α) ᶜ = (1 + 1)ᶜ + 1ᶜ := by
    simpa only [compl_compl, add_compl, eq_comm] using
      huntington 1ᶜ (1 : α)
  have ha' : (1 : α) = 1 + (1 + 1)ᶜ := by
    calc (1 : α) = 1 + 1ᶜ := (add_compl _).symm
        _ = 1 + (1 + 1)ᶜ + 1ᶜ := by
          nth_rewrite 1 [ha]; simp only [add_assoc]
        _ = 1 + 1ᶜ + (1 + 1)ᶜ := add_right_comm _ _ _
        _ = 1 + (1 + 1)ᶜ := by rw [add_compl]
  have hb : (1 : α) + 1 = 1 := by
    calc (1 : α) + 1 = 1 + (1 + (1 + 1)ᶜ) := by
          nth_rewrite 2 [ha']
          simp only
        _ = (1 + 1) + (1 + 1)ᶜ := by rw [add_assoc]
        _ = 1 := by
          rw [add_compl]
  rw [hb, eq_comm, one_compl] at ha
  rw [← huntington a a]
  rw [add_comm aᶜ, add_compl, one_compl]
  rw [add_comm 0, add_assoc, ha]

@[simp] theorem zero_add (a : α) : 0 + a = a := by
  rw [add_comm, add_zero]

-- Huntington 4.5, correction
@[simp] theorem add_self_eq (a : α) : a + a = a := by
  have := huntington aᶜ a
  simp only [compl_compl] at this
  rw [← compl_compl (a + a), ← add_zero (a + a)ᶜ, ← one_compl,
    ← add_compl a, this, compl_compl]

/- in a boolean algebra, a ≤ b means that a ⊔ b = b or a ⊓ b = b,
while ⊔ = + and ⊓ = * -/

-- Huntington 4.16
@[simp] theorem mul_one (a : α) : a * 1 = a := by
  simp [mul_def]

-- Huntington 4.17
@[simp] theorem mul_compl (a : α) : a * aᶜ = 0 := by
  rw [mul_def, ← one_def, one_compl]

-- Huntington 4.21
@[simp] theorem mul_self (a : α) : a * a = a := by
  rw [mul_def, add_self_eq, compl_compl]

-- Huntington 4.22
@[simp] theorem add_one (a : α) :  a + 1 = 1 := by
  rw [one_def a, ← add_assoc, add_self_eq]

-- Huntington 4.23
@[simp] theorem mul_zero (a : α) : a * 0 = 0 := by
  simp only [← one_compl, mul_def, compl_compl, one_def aᶜ, ← add_assoc, add_self_eq]

@[simp] theorem zero_mul (a : α) : 0 * a = 0 := by
  rw [mul_comm, mul_zero]

-- Huntington 4.24
theorem add_mul_self_left (a b : α) : a + a * b = a := by
  simp only [mul_def]
  nth_rewrite 1 [← huntington a bᶜ]
  rw [add_comm, ← add_assoc, add_self_eq, huntington]

-- Huntington 4.25
theorem mul_add_self_left (a b : α) : a * (a + b) = a := by
  simp only [mul_def, compl_eq_iff]
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

-- Huntington 4.26
theorem eq_of_add_compl_eq {a b : α} (h : aᶜ + b = 1) (h' : bᶜ + a = 1) :
    a = b := by
  rw [← huntington a b]
  conv_rhs => rw [← huntington b a]
  simp [h, h', add_comm aᶜ]

-- Huntington 4.27
theorem eq_compl_iff {a b : α} :
    a = bᶜ ↔ (a + b = 1 ∧ a * b = 0) := by
  constructor
  · intro h
    simp [h, add_comm bᶜ, mul_comm bᶜ]
  · rintro ⟨h, h'⟩
    apply eq_of_add_compl_eq
    · rw [← compl_eq_compl_iff]; exact h'
    · rw [compl_compl, add_comm, h]

-- Huntington 4.28
theorem mul_mul_compl_add (a b c : α) :
    a * b * c + a * b * cᶜ + a * bᶜ * c + a * bᶜ * cᶜ +
      aᶜ * b * c + aᶜ * b * cᶜ + aᶜ * bᶜ * c + aᶜ * bᶜ * cᶜ = 1 := by
  simp only [add_mul_mul_compl, add_assoc, add_compl]

-- Huntington 4.30
theorem add_mul_self (a b c : α) :
    a * b + a * c = a * b * c + a * b * cᶜ + a * bᶜ * c := by
  nth_rewrite 1 [← add_mul_mul_compl (a * b) c, ← add_mul_mul_compl (a * c) b]
  rw [mul_assoc a c b, mul_comm c b, ← mul_assoc]
  rw [mul_assoc a c bᶜ, mul_comm c bᶜ, ← mul_assoc]
  rw [add_add_add_comm, add_self_eq, ← add_assoc]

-- Huntington, 4.31
theorem mul_add_compl (a b c : α) :
    (a * (b + c))ᶜ = a * bᶜ * cᶜ + aᶜ * b * c + aᶜ * b * cᶜ + aᶜ * bᶜ * c + aᶜ * bᶜ * cᶜ := by
  have : (a * (b + c))ᶜ = aᶜ + bᶜ * cᶜ := by
    simp [mul_def a (b + c), compl_compl, mul_def bᶜ, compl_compl]
  rw [this]
  nth_rewrite 1 [← add_mul_mul_compl aᶜ b,
    ← add_mul_mul_compl (aᶜ * b) cᶜ, compl_compl,
    ← add_mul_mul_compl (aᶜ * bᶜ) c]
  have : bᶜ * cᶜ = a * bᶜ * cᶜ + aᶜ * bᶜ * cᶜ := by
    nth_rewrite 1 [← add_mul_mul_compl (bᶜ * cᶜ) a]
    rw [mul_comm _ a, ← mul_assoc]
    rw [mul_comm _ aᶜ, ← mul_assoc]
  rw [this]
  simp only [← add_assoc, mul_assoc, ← add_comm (a * _)]
  simp only [add_assoc]
  apply congr_arg₂ _ rfl
  simp only [← add_assoc, ← add_comm (aᶜ * (b * c))]
  simp only [add_assoc, add_self_eq]

-- Huntington 4.32
theorem add_eq_one (a b c : α) :
    (a * b + a * c) + (a * (b + c))ᶜ = 1 := by
  rw [mul_add_compl, add_mul_self]
  simp only [← add_assoc]
  exact mul_mul_compl_add a b c

lemma mul_add_eq_zero (a b c : α) (hab : a * b = 0) (hac : a * c = 0) :
    a * (b + c) = 0 := by
  rw [← compl_eq_compl_iff, zero_compl, ← zero_add (_)ᶜ, ← hab,
    ← add_zero (a * b), ← hac, add_eq_one]

set_option linter.style.multiGoal false in
-- Huntington 4.33
theorem add_mul_mul_mul_add_compl (a b c : α) :
    (a * b + a * c) * (a * (b + c))ᶜ = 0 := by
  rw [add_mul_self, mul_add_compl]
  set A := a * b * c
  set B := a * b * cᶜ
  set C := a * bᶜ * c
  set D := a * bᶜ * cᶜ
  set E := aᶜ * b * c
  set F := aᶜ * b * cᶜ
  set G := aᶜ * bᶜ * c
  set H := aᶜ * bᶜ * cᶜ
  have hA : A * (D + E + F + G + H) = 0 := by
    apply mul_add_eq_zero
    apply mul_add_eq_zero
    apply mul_add_eq_zero
    apply mul_add_eq_zero
    any_goals
      simp only [A, D, E, F, G, H, mul_assoc]
      rw [mul_comm c, mul_comm b]
      simp [← mul_assoc]
    · simp only [mul_assoc]
      simp [← mul_assoc, mul_comm _ c]
  have hB : B * (D + E + F + G + H) = 0 := by
    apply mul_add_eq_zero
    apply mul_add_eq_zero
    apply mul_add_eq_zero
    apply mul_add_eq_zero
    any_goals
      simp only [B, D, E, F, G, H, mul_assoc]
      rw [mul_comm b, mul_comm cᶜ]
      simp [← mul_assoc]
    · simp only [mul_self, mul_assoc]
      simp [mul_comm bᶜ, mul_assoc]
  have hC : C * (D + E + F + G + H) = 0 := by
    apply mul_add_eq_zero
    apply mul_add_eq_zero
    apply mul_add_eq_zero
    apply mul_add_eq_zero
    any_goals
      simp only [C, D, E, F, G, H, mul_assoc]
      rw [mul_comm bᶜ, mul_comm c]
      simp [← mul_assoc]
    · simp only [mul_assoc]
      simp [← mul_assoc, mul_comm _ c]
  rw [mul_comm]
  apply mul_add_eq_zero
  apply mul_add_eq_zero
  all_goals
    simp [mul_comm, hA, hB, hC]

-- Huntington 4.34
theorem mul_add (a b c : α) :
    a * (b + c) = a * b + a * c := by
  rw [← compl_eq_compl_iff, eq_compl_iff,
    add_comm, add_eq_one, mul_comm, add_mul_mul_mul_add_compl]
  simp

theorem add_mul (a b c : α) :
    (a + b) * c = a * c + b * c := by
  rw [mul_comm, mul_add, mul_comm c, mul_comm c]

-- Huntington 4.35
theorem add_mul' (a b c : α) :
    a + b * c = (a + b) * (a + c) := by
  nth_rewrite 1 [← compl_compl a, mul_def]
  rw [← compl_eq_compl_iff, ← mul_def]
  conv_rhs =>
    rw [mul_def, ← compl_compl a, ← compl_compl b, ← compl_compl c]
    rw [← mul_def aᶜ, ← mul_def aᶜ, compl_compl]
  rw [mul_add]

/-- Any Huntington algebra is a boolean algebra. -/
def booleanAlgebra : BooleanAlgebra α where
  le a b := (a + b = b)
  le_refl := add_self_eq
  le_trans a b c h h' := by rw [← h', ← add_assoc, h]
  le_antisymm a b h h' := by rw [← h', add_comm, h]
  sup x y := x + y
  le_sup_left a b := by rw [← add_assoc, add_self_eq]
  le_sup_right a b := by rw [add_comm, add_assoc, add_self_eq]
  sup_le a b c h h' := by rw [add_assoc, h', h]
  inf x y := x * y
  inf_le_left a b := by
    rw [add_comm, add_mul_self_left]
  inf_le_right a b := by
    rw [add_comm, mul_comm, add_mul_self_left]
  le_inf a b c h h' := by
    rw [add_mul', h, h']
  le_sup_inf a b c := by
    -- (a ⊔ b) ⊓ (a ⊔ c) + a ⊔ b ⊓ c = a ⊔ b ⊓ c
    change (a + b) * (a + c) + (a + b * c) = a + b * c
    rw [add_mul', add_self_eq]
  top := 1
  bot := 0
  inf_compl_le_bot a := by
    change a * aᶜ + 0 = 0
    simp
  top_le_sup_compl a := by
    change 1 + (a + aᶜ) = a + aᶜ
    simp
  le_top a := by
    simp
  bot_le a := by
    simp

end HuntingtonAlgebra

namespace RobbinsAlgebra

open PNat

variable {α : Type*} [RobbinsAlgebra α]

abbrev isHuntington (α : Type*) [AddCommSemigroup α] [HasCompl α] : Prop :=
  ∀ (a b : α), (aᶜ + b)ᶜ + (aᶜ + bᶜ)ᶜ = a

section Winker

/-- A Robbins algebra where every element is idempotent is a Huntington algebra.

Winker, Lemma 2.1. -/
theorem isHuntington_of_compl_compl_eq (h : ∀ a : α, aᶜᶜ = a) :
    isHuntington α := fun a b ↦ by
  have := robbins bᶜ aᶜ
  rw [h, add_comm b, add_comm bᶜ] at this
  rw [← h (_ + _), this, h]

/-- A Robbins algebra where the addition has a zero is a Huntington algebra.

Winker, Lemma 2.2. -/
theorem isHuntington_of_add_zero (h : ∃ z : α, ∀ a, a + z = a) :
    isHuntington α := by
  apply isHuntington_of_compl_compl_eq
  obtain ⟨z, hz⟩ := h
  have h1 (a) := robbins a z
  simp only [hz] at h1
  have h2 (a : α) := robbins aᶜᶜ aᶜ
  simp_rw [h1, hz] at h2
  intro a
  rw [← robbins a a]
  generalize (aᶜ + a)ᶜ + (a + a)ᶜ = b
  have hr := robbins bᶜ bᶜᶜᶜ
  rwa [eq_comm, add_comm bᶜᶜ, h1, add_comm z, hz,
      add_comm, h2] at hr

/-- A Robbins algebra with a zero and a one such that 0 + 0 = 0,
0 = 1ᶜ and 0 + 1 = 1 is a Huntington algebra.

Winker, Lemma 2.3. -/
theorem isHuntington_of_zero_and_one (h : ∃ (u : α),
    uᶜ + u = u ∧ uᶜ + uᶜ = uᶜ) :
    isHuntington α := by
  apply isHuntington_of_add_zero
  obtain ⟨u, h1, h0⟩ := h
  set z := uᶜ with hz
  use z
  intro a
  have h := robbins u (a + z)
  have h' := robbins u a
  rw [← hz] at h h'
  rw [add_comm u, add_assoc, h1, add_comm a u] at h
  rw [add_comm z, add_assoc, h0, add_comm  a z] at h
  rw [add_comm a, ← h, h']

/-- A Robbins algebra that contains some idempotent element is a Huntington algebra.

Winker, Lemma 2.4, Corollary 1.5. -/
theorem isHuntington_of_exists_idempotent (h : ∃ (e : α), e + e = e) :
    isHuntington α := by
  obtain ⟨e, he⟩ := h
  set u := e + eᶜ with hu
  apply isHuntington_of_zero_and_one
  use u
  set z := uᶜ with hz
  have h3 : u + e = u := by
    rw [hu, add_comm, ← add_assoc, he]
  have h4 : u + eᶜ = u + u := by
    rw [hu, add_add_add_comm, he, add_assoc]
  have h5 : (eᶜ + z)ᶜ = e := by
    have := robbins e e
    rwa [he, add_comm eᶜ e, ← hu, ← hz, add_comm] at this
  have h6 : ((u + u)ᶜ + e)ᶜ = eᶜ := by
    have := robbins u eᶜ
    rwa [← hz, add_comm z, h4, h5, add_comm e] at this
  have h7 : ((u + u)ᶜ + eᶜ)ᶜ = e := by
    have := robbins (u + u) e
    rwa [h6, ← h4, add_assoc, add_comm eᶜ e, ← hu, add_comm] at this
  have h8 : z = (u + u)ᶜ := by
    have := robbins e (u + u)ᶜ
    rwa [add_comm eᶜ, h7, add_comm e (u + u)ᶜ, h6, ← hu, ← hz] at this
  have h9 : (e + z)ᶜ = eᶜ := by
    rw [← h6, add_comm e, h8]
  have h10 : (eᶜ + (e + z + eᶜ)ᶜ)ᶜ = e + z := by
    have := robbins e (e + z)
    rw [← add_assoc, ← add_assoc, he, add_comm eᶜ, ← hu, h9, add_comm] at this
    convert this using 4
    rw [add_assoc, add_comm z, ← add_assoc, ← hu]
  have h11 : e + z = e := by
    have := robbins (z + eᶜ) e
    rw [add_comm z, h5, he] at this
    rw [← h10]
    conv_rhs => rw [← this]
    congr 3
    rw [add_comm e, add_comm eᶜ, add_assoc, add_assoc, add_comm e]
  have h12 : u + z = u := by
    rw [hu, add_comm e, add_assoc, h11]
  simp only [add_comm, h12, true_and]
  have h13 : ((eᶜ + eᶜ + z)ᶜ + z)ᶜ = eᶜ := by
    have := robbins (z + eᶜ) eᶜ
    rwa [add_comm z, h5, ← hu, ← hz, add_comm z, ← add_comm eᶜ, ← add_assoc] at this
  have h14 : eᶜ = z + eᶜ := by
    have := robbins e (z + eᶜ)
    rwa [add_comm z, ← add_assoc e, ← hu, h12, ← hz, ← add_assoc, h13, add_comm] at this
  have := robbins e (z + z)
  rwa [← add_assoc, add_comm eᶜ, ← h14, add_comm eᶜ,
    add_comm z, h5,
    ← add_assoc, h11, h11, ← hu, ← hz, eq_comm] at this

variable {a b c : α}

-- Winker, lemma 3.1
theorem add_eq_left (h : (a + (b + c)ᶜ)ᶜ = (a + b + cᶜ)ᶜ) :
    a + b = a := by
  have := robbins c (a + b)
  rwa [add_comm cᶜ, ← h, add_comm a, add_comm c, add_assoc, add_comm a, robbins, eq_comm] at this

-- Winker, lemma 3.2
theorem eq_of_eq (h : (a + (b + c)ᶜ)ᶜ = (b + (a + c)ᶜ)ᶜ) :
    a = b := by
  have := robbins (b + c) a
  have _ := robbins (c + a) b
  rwa [add_comm _ a, h, add_comm a, add_comm b,
    add_assoc, add_comm b, robbins, eq_comm] at this

theorem eq_compl_add_compl_add (h : (a + bᶜ)ᶜ = c) :
    (c + (b + a)ᶜ)ᶜ = a := by
  have := robbins b a
  rwa [add_comm _ a, h] at this

theorem eq_compl_add_compl_smul_add (n : ℕ+) (h : (a + bᶜ)ᶜ = c) :
    (a + (b + n • (a + c))ᶜ)ᶜ = c := by
  induction n with
  | one =>
    rw [one_smul, ← add_assoc]
    nth_rewrite 1 [← eq_compl_add_compl_add h]
    rw [add_comm c, robbins]
  | succ n hind =>
    set d := b + n • (a + c) + a with hd
    rw [add_one_smul, ← add_assoc, ← add_assoc, ← hd, ← eq_compl_add_compl_add hind,
      add_comm c, robbins]

theorem ad_compl_add_compl_add (h : (a + b)ᶜ = c) :
    (c + (bᶜ +a)ᶜ)ᶜ = a := by
  have _ := robbins b a
  rw [← h, add_comm, add_comm a, robbins]

theorem compl_eq_compl_add_smul_compl_add
    (n : ℕ+) (h : (bᶜ + (a + bᶜ)ᶜ)ᶜ = a) :
    (b + n • (a + (a + bᶜ)ᶜ))ᶜ = bᶜ := by
  set b' := b + n • (a + (a + bᶜ)ᶜ) with hb'
  set c := (a + bᶜ)ᶜ with hc
  have hc1 := eq_compl_add_compl_smul_add n hc
  rw [← hc, ← hb'] at hc1
  rw [add_comm] at h
  have hc2 := eq_compl_add_compl_smul_add n h
  rw [add_comm c a, ← hb'] at hc2
  apply eq_of_eq (c := c)
  rw [add_comm bᶜ, h, add_comm _ a, hc1, add_comm _ c, hc2, add_comm, ← hc]

theorem compl_eq_compl_add_smul_compl_add'
    (n : ℕ+) (h : (a + b)ᶜ = bᶜ) :
    (b + n • (a + (a + bᶜ)ᶜ))ᶜ = bᶜ := by
  apply compl_eq_compl_add_smul_compl_add
  nth_rewrite 1 [← h]
  rw [add_comm, add_comm a, add_comm a, robbins]


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
