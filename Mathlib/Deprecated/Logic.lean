/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
import Batteries.Tactic.Alias
import Mathlib.Init

/-!
# Note about deprecated files

This file is deprecated, and is no longer imported by anything in mathlib other than other
deprecated files, and test files. You should not need to import it.
-/

set_option linter.deprecated false

universe u v
variable {α : Sort u}

section Binary

variable {α : Type u} {β : Type v} (f : α → α → α) (inv : α → α) (one : α)

/-- Local notation for `f`, high priority to avoid ambiguity with `HMul.hMul`. -/
local infix:70 (priority := high) " * " => f

/-- Local notation for `inv`, high priority to avoid ambiguity with `Inv.inv`. -/
local postfix:100 (priority := high) "⁻¹" => inv

variable (g : α → α → α)

/-- Local notation for `g`, high priority to avoid ambiguity with `HAdd.hAdd`. -/
local infix:65 (priority := high) " + " => g

@[deprecated Std.Commutative (since := "2024-09-13")]
def Commutative       := ∀ a b, a * b = b * a
@[deprecated Std.Associative (since := "2024-09-13")]
def Associative       := ∀ a b c, (a * b) * c = a * (b * c)
@[deprecated (since := "2024-09-03")] -- unused in Mathlib
def LeftIdentity      := ∀ a, one * a = a
@[deprecated (since := "2024-09-03")] -- unused in Mathlib
def RightIdentity     := ∀ a, a * one = a
@[deprecated (since := "2024-09-03")] -- unused in Mathlib
def RightInverse      := ∀ a, a * a⁻¹ = one
@[deprecated (since := "2024-09-03")] -- unused in Mathlib
def LeftCancelative   := ∀ a b c, a * b = a * c → b = c
@[deprecated (since := "2024-09-03")] -- unused in Mathlib
def RightCancelative  := ∀ a b c, a * b = c * b → a = c
@[deprecated (since := "2024-09-03")] -- unused in Mathlib
def LeftDistributive  := ∀ a b c, a * (b + c) = a * b + a * c
@[deprecated (since := "2024-09-03")] -- unused in Mathlib
def RightDistributive := ∀ a b c, (a + b) * c = a * c + b * c

end Binary

@[deprecated (since := "2024-09-03")] alias not_of_eq_false := of_eq_false
@[deprecated (since := "2024-09-03")] -- unused in Mathlib
theorem cast_proof_irrel {β : Sort u} (h₁ h₂ : α = β) (a : α) : cast h₁ a = cast h₂ a := rfl
@[deprecated (since := "2024-09-03")] alias eq_rec_heq := eqRec_heq
@[deprecated (since := "2024-09-03")] alias heq_prop := proof_irrel_heq

@[deprecated (since := "2024-09-03")] -- unused in Mathlib
theorem heq_of_eq_rec_left {φ : α → Sort v} {a a' : α} {p₁ : φ a} {p₂ : φ a'} :
    (e : a = a') → (h₂ : Eq.rec (motive := fun a _ ↦ φ a) p₁ e = p₂) → HEq p₁ p₂
  | rfl, rfl => HEq.rfl

@[deprecated (since := "2024-09-03")] -- unused in Mathlib
theorem heq_of_eq_rec_right {φ : α → Sort v} {a a' : α} {p₁ : φ a} {p₂ : φ a'} :
    (e : a' = a) → (h₂ : p₁ = Eq.rec (motive := fun a _ ↦ φ a) p₂ e) → HEq p₁ p₂
  | rfl, rfl => HEq.rfl

@[deprecated (since := "2024-09-03")] -- unused in Mathlib
theorem of_heq_true {a : Prop} (h : HEq a True) : a := of_eq_true (eq_of_heq h)

@[deprecated (since := "2024-09-03")]
theorem eq_rec_compose {α β φ : Sort u} :
    ∀ (p₁ : β = φ) (p₂ : α = β) (a : α),
      (Eq.recOn p₁ (Eq.recOn p₂ a : β) : φ) = Eq.recOn (Eq.trans p₂ p₁) a
  | rfl, rfl, _ => rfl

-- unused in Mathlib
@[deprecated (since := "2024-09-11")] alias ⟨not_of_not_not_not, _⟩ := not_not_not

variable {a : Prop} (p : Prop)

@[deprecated and_true (since := "2024-09-12")]
theorem and_true_iff : p ∧ True ↔ p := iff_of_eq (and_true _)
@[deprecated true_and (since := "2024-09-12")]
theorem true_and_iff : True ∧ p ↔ p := iff_of_eq (true_and _)
@[deprecated and_false (since := "2024-09-12")]
theorem and_false_iff : p ∧ False ↔ False := iff_of_eq (and_false _)
@[deprecated false_and (since := "2024-09-12")]
theorem false_and_iff : False ∧ p ↔ False := iff_of_eq (false_and _)
@[deprecated or_true (since := "2024-09-12")]
theorem or_true_iff : p ∨ True ↔ True := iff_of_eq (or_true _)
@[deprecated true_or (since := "2024-09-12")]
theorem true_or_iff : True ∨ p ↔ True := iff_of_eq (true_or _)
@[deprecated or_false (since := "2024-09-12")]
theorem or_false_iff : p ∨ False ↔ p := iff_of_eq (or_false _)
@[deprecated false_or (since := "2024-09-12")]
theorem false_or_iff : False ∨ p ↔ p := iff_of_eq (false_or _)
@[deprecated iff_true (since := "2024-09-12")]
theorem iff_true_iff : (a ↔ True) ↔ a := iff_of_eq (iff_true _)
@[deprecated true_iff (since := "2024-09-12")]
theorem true_iff_iff : (True ↔ a) ↔ a := iff_of_eq (true_iff _)
@[deprecated iff_false (since := "2024-09-12")]
theorem iff_false_iff : (a ↔ False) ↔ ¬a := iff_of_eq (iff_false _)
@[deprecated false_iff (since := "2024-09-12")]
theorem false_iff_iff : (False ↔ a) ↔ ¬a := iff_of_eq (false_iff _)
@[deprecated iff_self (since := "2024-09-12")]
theorem iff_self_iff (a : Prop) : (a ↔ a) ↔ True := iff_of_eq (iff_self _)
@[deprecated (since := "2024-09-12")] alias not_or_of_not := not_or_intro

/- decidable -/

@[deprecated (since := "2024-09-03")] -- unused in Mathlib
theorem decide_True' (h : Decidable True) : decide True = true := by simp

@[deprecated (since := "2024-09-03")] -- unused in Mathlib
theorem decide_False' (h : Decidable False) : decide False = false := by simp

namespace Decidable

@[deprecated (since := "2024-09-03")] -- unused in Mathlib
def recOn_true [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u}
    (h₃ : p) (h₄ : h₁ h₃) : Decidable.recOn h h₂ h₁ :=
  cast (by match h with | .isTrue _ => rfl) h₄

@[deprecated (since := "2024-09-03")] -- unused in Mathlib
def recOn_false [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u} (h₃ : ¬p) (h₄ : h₂ h₃) :
    Decidable.recOn h h₂ h₁ :=
  cast (by match h with | .isFalse _ => rfl) h₄

@[deprecated (since := "2024-09-03")] alias by_cases := byCases
@[deprecated (since := "2024-09-03")] alias by_contradiction := byContradiction
@[deprecated (since := "2024-07-27")] alias not_not_iff := not_not

end Decidable

@[deprecated (since := "2024-09-03")] alias Or.decidable := instDecidableOr
@[deprecated (since := "2024-09-03")] alias And.decidable := instDecidableAnd
@[deprecated (since := "2024-09-03")] alias Not.decidable := instDecidableNot
@[deprecated (since := "2024-09-03")] alias Iff.decidable := instDecidableIff
@[deprecated (since := "2024-09-03")] alias decidableTrue := instDecidableTrue
@[deprecated (since := "2024-09-03")] alias decidableFalse := instDecidableFalse

@[deprecated (since := "2024-09-03")] -- unused in Mathlib
def IsDecEq {α : Sort u} (p : α → α → Bool) : Prop := ∀ ⦃x y : α⦄, p x y = true → x = y
@[deprecated (since := "2024-09-03")] -- unused in Mathlib
def IsDecRefl {α : Sort u} (p : α → α → Bool) : Prop := ∀ x, p x x = true

@[deprecated (since := "2024-09-03")] -- unused in Mathlib
def decidableEq_of_bool_pred {α : Sort u} {p : α → α → Bool} (h₁ : IsDecEq p)
    (h₂ : IsDecRefl p) : DecidableEq α
  | x, y =>
    if hp : p x y = true then isTrue (h₁ hp)
    else isFalse (fun hxy : x = y ↦ absurd (h₂ y) (by rwa [hxy] at hp))

@[deprecated (since := "2024-09-03")] -- unused in Mathlib
theorem decidableEq_inl_refl {α : Sort u} [h : DecidableEq α] (a : α) :
    h a a = isTrue (Eq.refl a) :=
  match h a a with
  | isTrue _ => rfl

@[deprecated (since := "2024-09-03")] -- unused in Mathlib
theorem decidableEq_inr_neg {α : Sort u} [h : DecidableEq α] {a b : α}
    (n : a ≠ b) : h a b = isFalse n :=
  match h a b with
  | isFalse _ => rfl

/- subsingleton -/

@[deprecated (since := "2024-09-03")] -- unused in Mathlib
theorem rec_subsingleton {p : Prop} [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u}
    [h₃ : ∀ h : p, Subsingleton (h₁ h)] [h₄ : ∀ h : ¬p, Subsingleton (h₂ h)] :
    Subsingleton (Decidable.recOn h h₂ h₁) :=
  match h with
  | isTrue h => h₃ h
  | isFalse h => h₄ h

@[deprecated (since := "2024-09-03")] -- unused in Mathlib
theorem imp_of_if_pos {c t e : Prop} [Decidable c] (h : ite c t e) (hc : c) : t :=
  (if_pos hc ▸ h :)

@[deprecated (since := "2024-09-03")] -- unused in Mathlib
theorem imp_of_if_neg {c t e : Prop} [Decidable c] (h : ite c t e) (hnc : ¬c) : e :=
  (if_neg hnc ▸ h :)

@[deprecated (since := "2024-09-11")]
theorem dif_ctx_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
    {x : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}
    (h_c : b ↔ c) (h_t : ∀ h : c, x (Iff.mpr h_c h) = u h)
    (h_e : ∀ h : ¬c, y (Iff.mpr (not_congr h_c) h) = v h) :
    @dite α b dec_b x y = @dite α c dec_c u v :=
  match dec_b, dec_c with
  | isFalse _, isFalse h₂ => h_e h₂
  | isTrue _, isTrue h₂ => h_t h₂
  | isFalse h₁, isTrue h₂ => absurd h₂ (Iff.mp (not_congr h_c) h₁)
  | isTrue h₁, isFalse h₂ => absurd h₁ (Iff.mpr (not_congr h_c) h₂)

@[deprecated (since := "2024-09-03")] -- unused in Mathlib
theorem if_ctx_congr_prop {b c x y u v : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
    (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) : ite b x y ↔ ite c u v :=
  match dec_b, dec_c with
  | isFalse _,  isFalse h₂ => h_e h₂
  | isTrue _,   isTrue h₂  => h_t h₂
  | isFalse h₁, isTrue h₂  => absurd h₂ (Iff.mp (not_congr h_c) h₁)
  | isTrue h₁,  isFalse h₂ => absurd h₁ (Iff.mpr (not_congr h_c) h₂)

-- @[congr]
@[deprecated (since := "2024-09-03")] -- unused in Mathlib
theorem if_congr_prop {b c x y u v : Prop} [Decidable b] [Decidable c] (h_c : b ↔ c) (h_t : x ↔ u)
    (h_e : y ↔ v) : ite b x y ↔ ite c u v :=
  if_ctx_congr_prop h_c (fun _ ↦ h_t) (fun _ ↦ h_e)

@[deprecated (since := "2024-09-03")] -- unused in Mathlib
theorem if_ctx_simp_congr_prop {b c x y u v : Prop} [Decidable b] (h_c : b ↔ c) (h_t : c → (x ↔ u))
    -- FIXME: after https://github.com/leanprover/lean4/issues/1867 is fixed,
    -- this should be changed back to:
    -- (h_e : ¬c → (y ↔ v)) : ite b x y ↔ ite c (h := decidable_of_decidable_of_iff h_c) u v :=
    (h_e : ¬c → (y ↔ v)) : ite b x y ↔ @ite _ c (decidable_of_decidable_of_iff h_c) u v :=
  if_ctx_congr_prop (dec_c := decidable_of_decidable_of_iff h_c) h_c h_t h_e

@[deprecated (since := "2024-09-03")] -- unused in Mathlib
theorem if_simp_congr_prop {b c x y u v : Prop} [Decidable b] (h_c : b ↔ c) (h_t : x ↔ u)
    -- FIXME: after https://github.com/leanprover/lean4/issues/1867 is fixed,
    -- this should be changed back to:
    -- (h_e : y ↔ v) : ite b x y ↔ (ite c (h := decidable_of_decidable_of_iff h_c) u v) :=
    (h_e : y ↔ v) : ite b x y ↔ (@ite _ c (decidable_of_decidable_of_iff h_c) u v) :=
  if_ctx_simp_congr_prop h_c (fun _ ↦ h_t) (fun _ ↦ h_e)

@[deprecated (since := "2024-09-03")] -- unused in Mathlib
theorem dif_ctx_simp_congr {α : Sort u} {b c : Prop} [Decidable b]
    {x : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}
    (h_c : b ↔ c) (h_t : ∀ h : c, x (Iff.mpr h_c h) = u h)
    (h_e : ∀ h : ¬c, y (Iff.mpr (not_congr h_c) h) = v h) :
    -- FIXME: after https://github.com/leanprover/lean4/issues/1867 is fixed,
    -- this should be changed back to:
    -- dite b x y = dite c (h := decidable_of_decidable_of_iff h_c) u v :=
    dite b x y = @dite _ c (decidable_of_decidable_of_iff h_c) u v :=
  dif_ctx_congr (dec_c := decidable_of_decidable_of_iff h_c) h_c h_t h_e

@[deprecated (since := "2024-09-03")]
def AsTrue (c : Prop) [Decidable c] : Prop := if c then True else False

@[deprecated (since := "2024-09-03")] -- unused in Mathlib
def AsFalse (c : Prop) [Decidable c] : Prop := if c then False else True

@[deprecated (since := "2024-09-03")]
theorem AsTrue.get {c : Prop} [h₁ : Decidable c] (_ : AsTrue c) : c :=
  match h₁ with
  | isTrue h_c => h_c

/- Equalities for rewriting let-expressions -/
@[deprecated (since := "2024-09-03")] -- unused in Mathlib
theorem let_value_eq {α : Sort u} {β : Sort v} {a₁ a₂ : α} (b : α → β)
    (h : a₁ = a₂) : (let x : α := a₁; b x) = (let x : α := a₂; b x) := congrArg b h

@[deprecated (since := "2024-09-03")] -- unused in Mathlib
theorem let_value_heq {α : Sort v} {β : α → Sort u} {a₁ a₂ : α} (b : ∀ x : α, β x)
    (h : a₁ = a₂) : HEq (let x : α := a₁; b x) (let x : α := a₂; b x) := by cases h; rfl

@[deprecated (since := "2024-09-03")] -- unused in Mathlib
theorem let_body_eq {α : Sort v} {β : α → Sort u} (a : α) {b₁ b₂ : ∀ x : α, β x}
    (h : ∀ x, b₁ x = b₂ x) : (let x : α := a; b₁ x) = (let x : α := a; b₂ x) := by exact h _ ▸ rfl

@[deprecated (since := "2024-09-03")] -- unused in Mathlib
theorem let_eq {α : Sort v} {β : Sort u} {a₁ a₂ : α} {b₁ b₂ : α → β}
    (h₁ : a₁ = a₂) (h₂ : ∀ x, b₁ x = b₂ x) :
    (let x : α := a₁; b₁ x) = (let x : α := a₂; b₂ x) := by simp [h₁, h₂]
