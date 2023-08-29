/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.Init.Logic
import Mathlib.Init.Function
import Mathlib.Init.Algebra.Classes
import Mathlib.Tactic.Basic
import Mathlib.Tactic.LeftRight
import Std.Util.LibraryNote
import Std.Tactic.Lint.Basic

#align_import logic.basic from "leanprover-community/mathlib"@"48fb5b5280e7c81672afc9524185ae994553ebf4"

/-!
# Basic logic properties

This file is one of the earliest imports in mathlib.

## Implementation notes

Theorems that require decidability hypotheses are in the namespace `Decidable`.
Classical versions are in the namespace `Classical`.
-/

set_option autoImplicit true

open Function
attribute [local instance 10] Classical.propDecidable

section Miscellany

-- Porting note: the following `inline` attributes have been omitted,
-- on the assumption that this issue has been dealt with properly in Lean 4.
-- /- We add the `inline` attribute to optimize VM computation using these declarations.
--    For example, `if p ∧ q then ... else ...` will not evaluate the decidability
--    of `q` if `p` is false. -/
-- attribute [inline]
--   And.decidable Or.decidable Decidable.false Xor.decidable Iff.decidable Decidable.true
--   Implies.decidable Not.decidable Ne.decidable Bool.decidableEq Decidable.toBool

attribute [simp] cast_eq cast_heq

/-- An identity function with its main argument implicit. This will be printed as `hidden` even
if it is applied to a large term, so it can be used for elision,
as done in the `elide` and `unelide` tactics. -/
@[reducible] def hidden {α : Sort*} {a : α} := a
#align hidden hidden

instance (priority := 10) decidableEq_of_subsingleton [Subsingleton α] : DecidableEq α :=
  fun a b ↦ isTrue (Subsingleton.elim a b)
#align decidable_eq_of_subsingleton decidableEq_of_subsingleton

instance (α : Sort*) [Subsingleton α] (p : α → Prop) : Subsingleton (Subtype p) :=
  ⟨fun ⟨x, _⟩ ⟨y, _⟩ ↦ by cases Subsingleton.elim x y; rfl⟩
                          -- ⊢ { val := x, property := property✝¹ } = { val := x, property := property✝ }
                                                       -- 🎉 no goals

#align pempty PEmpty

theorem congr_heq {α β γ : Sort _} {f : α → γ} {g : β → γ} {x : α} {y : β}
    (h₁ : HEq f g) (h₂ : HEq x y) : f x = g y := by
  cases h₂; cases h₁; rfl
  -- ⊢ f x = g x
            -- ⊢ f x = f x
                      -- 🎉 no goals
#align congr_heq congr_heq

theorem congr_arg_heq {α} {β : α → Sort*} (f : ∀ a, β a) :
    ∀ {a₁ a₂ : α}, a₁ = a₂ → HEq (f a₁) (f a₂)
  | _, _, rfl => HEq.rfl
#align congr_arg_heq congr_arg_heq

theorem ULift.down_injective {α : Sort _} : Function.Injective (@ULift.down α)
  | ⟨a⟩, ⟨b⟩, _ => by congr
                      -- 🎉 no goals
#align ulift.down_injective ULift.down_injective

@[simp] theorem ULift.down_inj {α : Sort _} {a b : ULift α} : a.down = b.down ↔ a = b :=
  ⟨fun h ↦ ULift.down_injective h, fun h ↦ by rw [h]⟩
                                              -- 🎉 no goals
#align ulift.down_inj ULift.down_inj

theorem PLift.down_injective {α : Sort*} : Function.Injective (@PLift.down α)
  | ⟨a⟩, ⟨b⟩, _ => by congr
                      -- 🎉 no goals
#align plift.down_injective PLift.down_injective

@[simp] theorem PLift.down_inj {α : Sort*} {a b : PLift α} : a.down = b.down ↔ a = b :=
  ⟨fun h ↦ PLift.down_injective h, fun h ↦ by rw [h]⟩
                                              -- 🎉 no goals
#align plift.down_inj PLift.down_inj

@[simp] theorem eq_iff_eq_cancel_left {b c : α} : (∀ {a}, a = b ↔ a = c) ↔ b = c :=
  ⟨fun h ↦ by rw [← h], fun h a ↦ by rw [h]⟩
              -- 🎉 no goals
                                     -- 🎉 no goals
#align eq_iff_eq_cancel_left eq_iff_eq_cancel_left

@[simp] theorem eq_iff_eq_cancel_right {a b : α} : (∀ {c}, a = c ↔ b = c) ↔ a = b :=
  ⟨fun h ↦ by rw [h], fun h a ↦ by rw [h]⟩
              -- 🎉 no goals
                                   -- 🎉 no goals
#align eq_iff_eq_cancel_right eq_iff_eq_cancel_right

lemma ne_and_eq_iff_right {α : Sort*} {a b c : α} (h : b ≠ c) : a ≠ b ∧ a = c ↔ a = c :=
  and_iff_right_of_imp (fun h2 => h2.symm ▸ h.symm)
#align ne_and_eq_iff_right ne_and_eq_iff_right

/-- Wrapper for adding elementary propositions to the type class systems.
Warning: this can easily be abused. See the rest of this docstring for details.

Certain propositions should not be treated as a class globally,
but sometimes it is very convenient to be able to use the type class system
in specific circumstances.

For example, `ZMod p` is a field if and only if `p` is a prime number.
In order to be able to find this field instance automatically by type class search,
we have to turn `p.prime` into an instance implicit assumption.

On the other hand, making `Nat.prime` a class would require a major refactoring of the library,
and it is questionable whether making `Nat.prime` a class is desirable at all.
The compromise is to add the assumption `[Fact p.prime]` to `ZMod.field`.

In particular, this class is not intended for turning the type class system
into an automated theorem prover for first order logic. -/
class Fact (p : Prop) : Prop where
  /-- `Fact.out` contains the unwrapped witness for the fact represented by the instance of
  `Fact p`. -/
  out : p
#align fact Fact

library_note "fact non-instances"/--
In most cases, we should not have global instances of `Fact`; typeclass search only reads the head
symbol and then tries any instances, which means that adding any such instance will cause slowdowns
everywhere. We instead make them as lemmata and make them local instances as required.
-/

theorem Fact.elim {p : Prop} (h : Fact p) : p := h.1
theorem fact_iff {p : Prop} : Fact p ↔ p := ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩
#align fact_iff fact_iff
#align fact.elim Fact.elim

/-- Swaps two pairs of arguments to a function. -/
@[reducible] def Function.swap₂ {κ₁ : ι₁ → Sort*} {κ₂ : ι₂ → Sort*}
    {φ : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Sort*} (f : ∀ i₁ j₁ i₂ j₂, φ i₁ j₁ i₂ j₂)
    (i₂ j₂ i₁ j₁) : φ i₁ j₁ i₂ j₂ := f i₁ j₁ i₂ j₂
#align function.swap₂ Function.swap₂

-- Porting note: these don't work as intended any more
-- /-- If `x : α . tac_name` then `x.out : α`. These are definitionally equal, but this can
-- nevertheless be useful for various reasons, e.g. to apply further projection notation or in an
-- argument to `simp`. -/
-- def autoParam'.out {α : Sort*} {n : Name} (x : autoParam' α n) : α := x

-- /-- If `x : α := d` then `x.out : α`. These are definitionally equal, but this can
-- nevertheless be useful for various reasons, e.g. to apply further projection notation or in an
-- argument to `simp`. -/
-- def optParam.out {α : Sort*} {d : α} (x : α := d) : α := x

end Miscellany

open Function

/-!
### Declarations about propositional connectives
-/

section Propositional

/-! ### Declarations about `implies` -/

instance : IsRefl Prop Iff := ⟨Iff.refl⟩

instance : IsTrans Prop Iff := ⟨fun _ _ _ ↦ Iff.trans⟩

alias Iff.imp := imp_congr
#align iff.imp Iff.imp

@[simp] theorem eq_true_eq_id : Eq True = id := by
  funext _; simp only [true_iff, id.def, eq_iff_iff]
  -- ⊢ (True = x✝) = id x✝
            -- 🎉 no goals
#align eq_true_eq_id eq_true_eq_id

#align imp_and_distrib imp_and
#align imp_iff_right imp_iff_rightₓ -- reorder implicits
#align imp_iff_not imp_iff_notₓ -- reorder implicits

@[simp] theorem imp_iff_right_iff : (a → b ↔ b) ↔ a ∨ b := Decidable.imp_iff_right_iff
#align imp_iff_right_iff imp_iff_right_iff

@[simp] theorem and_or_imp : a ∧ b ∨ (a → c) ↔ a → b ∨ c := Decidable.and_or_imp
#align and_or_imp and_or_imp

/-- Provide modus tollens (`mt`) as dot notation for implications. -/
protected theorem Function.mt : (a → b) → ¬b → ¬a := mt
#align function.mt Function.mt

/-! ### Declarations about `not` -/

alias dec_em := Decidable.em
#align dec_em dec_em

theorem dec_em' (p : Prop) [Decidable p] : ¬p ∨ p := (dec_em p).symm
#align dec_em' dec_em'

alias em := Classical.em
#align em em

theorem em' (p : Prop) : ¬p ∨ p := (em p).symm
#align em' em'

theorem or_not {p : Prop} : p ∨ ¬p := em _
#align or_not or_not

theorem Decidable.eq_or_ne (x y : α) [Decidable (x = y)] : x = y ∨ x ≠ y := dec_em <| x = y
#align decidable.eq_or_ne Decidable.eq_or_ne

theorem Decidable.ne_or_eq (x y : α) [Decidable (x = y)] : x ≠ y ∨ x = y := dec_em' <| x = y
#align decidable.ne_or_eq Decidable.ne_or_eq

theorem eq_or_ne (x y : α) : x = y ∨ x ≠ y := em <| x = y
#align eq_or_ne eq_or_ne

theorem ne_or_eq (x y : α) : x ≠ y ∨ x = y := em' <| x = y
#align ne_or_eq ne_or_eq

theorem by_contradiction : (¬p → False) → p := Decidable.by_contradiction
#align classical.by_contradiction by_contradiction
#align by_contradiction by_contradiction

theorem by_cases {q : Prop} (hpq : p → q) (hnpq : ¬p → q) : q :=
if hp : p then hpq hp else hnpq hp
#align classical.by_cases by_cases

alias by_contra := by_contradiction
#align by_contra by_contra

library_note "decidable namespace"/--
In most of mathlib, we use the law of excluded middle (LEM) and the axiom of choice (AC) freely.
The `Decidable` namespace contains versions of lemmas from the root namespace that explicitly
attempt to avoid the axiom of choice, usually by adding decidability assumptions on the inputs.

You can check if a lemma uses the axiom of choice by using `#print axioms foo` and seeing if
`Classical.choice` appears in the list.
-/

library_note "decidable arguments"/--
As mathlib is primarily classical,
if the type signature of a `def` or `lemma` does not require any `Decidable` instances to state,
it is preferable not to introduce any `Decidable` instances that are needed in the proof
as arguments, but rather to use the `classical` tactic as needed.

In the other direction, when `Decidable` instances do appear in the type signature,
it is better to use explicitly introduced ones rather than allowing Lean to automatically infer
classical ones, as these may cause instance mismatch errors later.
-/

export Classical (not_not)
attribute [simp] not_not
#align not_not Classical.not_not

theorem of_not_not : ¬¬a → a := by_contra
#align of_not_not of_not_not

theorem not_ne_iff : ¬a ≠ b ↔ a = b := not_not
#align not_ne_iff not_ne_iff

theorem of_not_imp {a b : Prop} : ¬(a → b) → a := Decidable.of_not_imp
#align of_not_imp of_not_imp

alias Not.decidable_imp_symm := Decidable.not_imp_symm
#align not.decidable_imp_symm Not.decidable_imp_symm

theorem Not.imp_symm : (¬a → b) → ¬b → a := Not.decidable_imp_symm
#align not.imp_symm Not.imp_symm

theorem not_imp_comm : ¬a → b ↔ ¬b → a := Decidable.not_imp_comm
#align not_imp_comm not_imp_comm

@[simp] theorem not_imp_self : ¬a → a ↔ a := Decidable.not_imp_self
#align not_imp_self not_imp_self

theorem Imp.swap : a → b → c ↔ b → a → c := ⟨Function.swap, Function.swap⟩
#align imp.swap Imp.swap

alias Iff.not := not_congr
#align iff.not Iff.not

theorem Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b := h.not.trans not_not
#align iff.not_left Iff.not_left

theorem Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b := not_not.symm.trans h.not
#align iff.not_right Iff.not_right

/-! ### Declarations about `Xor'` -/

@[simp] theorem xor_true : Xor' True = Not := by simp [Xor']
                                                 -- 🎉 no goals
#align xor_true xor_true

@[simp] theorem xor_false : Xor' False = id := by ext; simp [Xor']
                                                  -- ⊢ Xor' False x✝ ↔ id x✝
                                                       -- 🎉 no goals
#align xor_false xor_false

theorem xor_comm (a b) : Xor' a b = Xor' b a := by simp [Xor', and_comm, or_comm]
                                                   -- 🎉 no goals
#align xor_comm xor_comm

instance : IsCommutative Prop Xor' := ⟨xor_comm⟩

@[simp] theorem xor_self (a : Prop) : Xor' a a = False := by simp [Xor']
                                                             -- 🎉 no goals
#align xor_self xor_self

@[simp] theorem xor_not_left : Xor' (¬a) b ↔ (a ↔ b) := by by_cases a <;> simp [*]
                                                           -- ⊢ Xor' (¬a) b ↔ (a ↔ b)
                                                           -- ⊢ Xor' (¬a) b ↔ (a ↔ b)
                                                                          -- 🎉 no goals
                                                                          -- 🎉 no goals
#align xor_not_left xor_not_left

@[simp] theorem xor_not_right : Xor' a (¬b) ↔ (a ↔ b) := by by_cases a <;> simp [*]
                                                            -- ⊢ Xor' a ¬b ↔ (a ↔ b)
                                                            -- ⊢ Xor' a ¬b ↔ (a ↔ b)
                                                                           -- 🎉 no goals
                                                                           -- 🎉 no goals
#align xor_not_right xor_not_right

theorem xor_not_not : Xor' (¬a) (¬b) ↔ Xor' a b := by simp [Xor', or_comm, and_comm]
                                                      -- 🎉 no goals
#align xor_not_not xor_not_not

protected theorem Xor'.or (h : Xor' a b) : a ∨ b := h.imp And.left And.left
#align xor.or Xor'.or

/-! ### Declarations about `and` -/

alias Iff.and := and_congr
#align iff.and Iff.and
#align and_congr_left and_congr_leftₓ -- reorder implicits
#align and_congr_right' and_congr_right'ₓ -- reorder implicits
#align and.right_comm and_right_comm
#align and_and_distrib_left and_and_left
#align and_and_distrib_right and_and_right
alias ⟨And.rotate, _⟩ := and_rotate
#align and.rotate And.rotate
#align and.congr_right_iff and_congr_right_iff
#align and.congr_left_iff and_congr_left_iffₓ -- reorder implicits

theorem and_symm_right (a b : α) (p : Prop) : p ∧ a = b ↔ p ∧ b = a := by simp [eq_comm]
                                                                          -- 🎉 no goals
theorem and_symm_left (a b : α) (p : Prop) : a = b ∧ p ↔ b = a ∧ p := by simp [eq_comm]
                                                                         -- 🎉 no goals

/-! ### Declarations about `or` -/

alias Iff.or := or_congr
#align iff.or Iff.or
#align or_congr_left' or_congr_left
#align or_congr_right' or_congr_rightₓ -- reorder implicits
#align or.right_comm or_right_comm
alias ⟨Or.rotate, _⟩ := or_rotate
#align or.rotate Or.rotate

@[deprecated Or.imp]
theorem or_of_or_of_imp_of_imp (h₁ : a ∨ b) (h₂ : a → c) (h₃ : b → d) : c ∨ d := Or.imp h₂ h₃ h₁
#align or_of_or_of_imp_of_imp or_of_or_of_imp_of_imp

@[deprecated Or.imp_left]
theorem or_of_or_of_imp_left (h₁ : a ∨ c) (h : a → b) : b ∨ c := Or.imp_left h h₁
#align or_of_or_of_imp_left or_of_or_of_imp_left

@[deprecated Or.imp_right]
theorem or_of_or_of_imp_right (h₁ : c ∨ a) (h : a → b) : c ∨ b := Or.imp_right h h₁
#align or_of_or_of_imp_right or_of_or_of_imp_right

theorem Or.elim3 {d : Prop} (h : a ∨ b ∨ c) (ha : a → d) (hb : b → d) (hc : c → d) : d :=
  Or.elim h ha fun h₂ ↦ Or.elim h₂ hb hc
#align or.elim3 Or.elim3

theorem Or.imp3 (had : a → d) (hbe : b → e) (hcf : c → f) : a ∨ b ∨ c → d ∨ e ∨ f :=
  Or.imp had <| Or.imp hbe hcf
#align or.imp3 Or.imp3

#align or_imp_distrib or_imp

theorem or_iff_not_imp_left : a ∨ b ↔ ¬a → b := Decidable.or_iff_not_imp_left
#align or_iff_not_imp_left or_iff_not_imp_left

theorem or_iff_not_imp_right : a ∨ b ↔ ¬b → a := Decidable.or_iff_not_imp_right
#align or_iff_not_imp_right or_iff_not_imp_right

theorem not_or_of_imp : (a → b) → ¬a ∨ b := Decidable.not_or_of_imp
#align not_or_of_imp not_or_of_imp

-- See Note [decidable namespace]
protected theorem Decidable.or_not_of_imp [Decidable a] (h : a → b) : b ∨ ¬a :=
  dite _ (Or.inl ∘ h) Or.inr
#align decidable.or_not_of_imp Decidable.or_not_of_imp

theorem or_not_of_imp : (a → b) → b ∨ ¬a := Decidable.or_not_of_imp
#align or_not_of_imp or_not_of_imp

theorem imp_iff_not_or : a → b ↔ ¬a ∨ b := Decidable.imp_iff_not_or
#align imp_iff_not_or imp_iff_not_or

theorem imp_iff_or_not : b → a ↔ a ∨ ¬b := Decidable.imp_iff_or_not
#align imp_iff_or_not imp_iff_or_not

theorem not_imp_not : ¬a → ¬b ↔ b → a := Decidable.not_imp_not
#align not_imp_not not_imp_not

/-- Provide the reverse of modus tollens (`mt`) as dot notation for implications. -/
protected theorem Function.mtr : (¬a → ¬b) → b → a := not_imp_not.mp
#align function.mtr Function.mtr

#align decidable.or_congr_left Decidable.or_congr_left'
#align decidable.or_congr_right Decidable.or_congr_right'
#align decidable.or_iff_not_imp_right Decidable.or_iff_not_imp_rightₓ -- reorder implicits
#align decidable.imp_iff_or_not Decidable.imp_iff_or_notₓ -- reorder implicits

theorem or_congr_left' (h : ¬c → (a ↔ b)) : a ∨ c ↔ b ∨ c := Decidable.or_congr_left' h
#align or_congr_left or_congr_left'

theorem or_congr_right' (h : ¬a → (b ↔ c)) : a ∨ b ↔ a ∨ c := Decidable.or_congr_right' h
#align or_congr_right or_congr_right'ₓ -- reorder implicits

#align or_iff_left or_iff_leftₓ -- reorder implicits

/-! ### Declarations about distributivity -/

#align and_or_distrib_left and_or_left
#align or_and_distrib_right or_and_right
#align or_and_distrib_left or_and_left
#align and_or_distrib_right and_or_right

/-! Declarations about `iff` -/

alias Iff.iff := iff_congr
#align iff.iff Iff.iff

-- @[simp] -- FIXME simp ignores proof rewrites
theorem iff_mpr_iff_true_intro (h : P) : Iff.mpr (iff_true_intro h) True.intro = h := rfl
#align iff_mpr_iff_true_intro iff_mpr_iff_true_intro

#align decidable.imp_or_distrib Decidable.imp_or

theorem imp_or {a b c : Prop} : a → b ∨ c ↔ (a → b) ∨ (a → c) := Decidable.imp_or
#align imp_or_distrib imp_or

#align decidable.imp_or_distrib' Decidable.imp_or'

theorem imp_or' : a → b ∨ c ↔ (a → b) ∨ (a → c) := Decidable.imp_or'
#align imp_or_distrib' imp_or'ₓ -- universes

theorem not_imp : ¬(a → b) ↔ a ∧ ¬b := Decidable.not_imp
#align not_imp not_imp

theorem peirce (a b : Prop) : ((a → b) → a) → a := Decidable.peirce _ _
#align peirce peirce

theorem not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b) := Decidable.not_iff_not
#align not_iff_not not_iff_not

theorem not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a) := Decidable.not_iff_comm
#align not_iff_comm not_iff_comm

theorem not_iff : ¬(a ↔ b) ↔ (¬a ↔ b) := Decidable.not_iff
#align not_iff not_iff

theorem iff_not_comm : (a ↔ ¬b) ↔ (b ↔ ¬a) := Decidable.iff_not_comm
#align iff_not_comm iff_not_comm

theorem iff_iff_and_or_not_and_not : (a ↔ b) ↔ a ∧ b ∨ ¬a ∧ ¬b :=
  Decidable.iff_iff_and_or_not_and_not
#align iff_iff_and_or_not_and_not iff_iff_and_or_not_and_not

theorem iff_iff_not_or_and_or_not : (a ↔ b) ↔ (¬a ∨ b) ∧ (a ∨ ¬b) :=
  Decidable.iff_iff_not_or_and_or_not
#align iff_iff_not_or_and_or_not iff_iff_not_or_and_or_not

theorem not_and_not_right : ¬(a ∧ ¬b) ↔ a → b := Decidable.not_and_not_right
#align not_and_not_right not_and_not_right

#align decidable_of_iff decidable_of_iff
#align decidable_of_iff' decidable_of_iff'
#align decidable_of_bool decidable_of_bool

/-! ### De Morgan's laws -/

#align decidable.not_and_distrib Decidable.not_and
#align decidable.not_and_distrib' Decidable.not_and'

/-- One of de Morgan's laws: the negation of a conjunction is logically equivalent to the
disjunction of the negations. -/
theorem not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b := Decidable.not_and
#align not_and_distrib not_and_or

#align not_or_distrib not_or

theorem or_iff_not_and_not : a ∨ b ↔ ¬(¬a ∧ ¬b) := Decidable.or_iff_not_and_not
#align or_iff_not_and_not or_iff_not_and_not

theorem and_iff_not_or_not : a ∧ b ↔ ¬(¬a ∨ ¬b) := Decidable.and_iff_not_or_not
#align and_iff_not_or_not and_iff_not_or_not

@[simp] theorem not_xor (P Q : Prop) : ¬Xor' P Q ↔ (P ↔ Q) := by
  simp only [not_and, Xor', not_or, not_not, ← iff_iff_implies_and_implies]
  -- 🎉 no goals
#align not_xor not_xor

theorem xor_iff_not_iff (P Q : Prop) : Xor' P Q ↔ ¬ (P ↔ Q) := (not_xor P Q).not_right
#align xor_iff_not_iff xor_iff_not_iff

theorem xor_iff_iff_not : Xor' a b ↔ (a ↔ ¬b) := by simp only [← @xor_not_right a, not_not]
                                                    -- 🎉 no goals
#align xor_iff_iff_not xor_iff_iff_not

theorem xor_iff_not_iff' : Xor' a b ↔ (¬a ↔ b) := by simp only [← @xor_not_left _ b, not_not]
                                                     -- 🎉 no goals
#align xor_iff_not_iff' xor_iff_not_iff'

end Propositional

/-! ### Declarations about equality -/

alias Membership.mem.ne_of_not_mem := ne_of_mem_of_not_mem
alias Membership.mem.ne_of_not_mem' := ne_of_mem_of_not_mem'

#align has_mem.mem.ne_of_not_mem Membership.mem.ne_of_not_mem
#align has_mem.mem.ne_of_not_mem' Membership.mem.ne_of_not_mem'

section Equality

-- todo: change name
theorem ball_cond_comm {α} {s : α → Prop} {p : α → α → Prop} :
    (∀ a, s a → ∀ b, s b → p a b) ↔ ∀ a b, s a → s b → p a b :=
  ⟨fun h a b ha hb ↦ h a ha b hb, fun h a ha b hb ↦ h a b ha hb⟩
#align ball_cond_comm ball_cond_comm

theorem ball_mem_comm {α β} [Membership α β] {s : β} {p : α → α → Prop} :
    (∀ a (_ : a ∈ s) b (_ : b ∈ s), p a b) ↔ ∀ a b, a ∈ s → b ∈ s → p a b :=
  ball_cond_comm
#align ball_mem_comm ball_mem_comm

theorem ne_of_apply_ne {α β : Sort*} (f : α → β) {x y : α} (h : f x ≠ f y) : x ≠ y :=
  fun w : x = y ↦ h (congr_arg f w)
#align ne_of_apply_ne ne_of_apply_ne

theorem eq_equivalence : Equivalence (@Eq α) :=
  ⟨Eq.refl, @Eq.symm _, @Eq.trans _⟩
#align eq_equivalence eq_equivalence

@[simp] theorem eq_mp_eq_cast (h : α = β) : Eq.mp h = cast h := rfl
#align eq_mp_eq_cast eq_mp_eq_cast

@[simp] theorem eq_mpr_eq_cast (h : α = β) : Eq.mpr h = cast h.symm := rfl
#align eq_mpr_eq_cast eq_mpr_eq_cast

@[simp] theorem cast_cast : ∀ (ha : α = β) (hb : β = γ) (a : α),
    cast hb (cast ha a) = cast (ha.trans hb) a
  | rfl, rfl, _ => rfl
#align cast_cast cast_cast

-- @[simp] -- FIXME simp ignores proof rewrites
theorem congr_refl_left (f : α → β) {a b : α} (h : a = b) :
    congr (Eq.refl f) h = congr_arg f h := rfl
#align congr_refl_left congr_refl_left

-- @[simp] -- FIXME simp ignores proof rewrites
theorem congr_refl_right {f g : α → β} (h : f = g) (a : α) :
    congr h (Eq.refl a) = congr_fun h a := rfl
#align congr_refl_right congr_refl_right

-- @[simp] -- FIXME simp ignores proof rewrites
theorem congr_arg_refl (f : α → β) (a : α) : congr_arg f (Eq.refl a) = Eq.refl (f a) := rfl
#align congr_arg_refl congr_arg_refl

-- @[simp] -- FIXME simp ignores proof rewrites
theorem congr_fun_rfl (f : α → β) (a : α) : congr_fun (Eq.refl f) a = Eq.refl (f a) := rfl
#align congr_fun_rfl congr_fun_rfl

-- @[simp] -- FIXME simp ignores proof rewrites
theorem congr_fun_congr_arg (f : α → β → γ) {a a' : α} (p : a = a') (b : β) :
    congr_fun (congr_arg f p) b = congr_arg (fun a ↦ f a b) p := rfl
#align congr_fun_congr_arg congr_fun_congr_arg

theorem heq_of_cast_eq : ∀ (e : α = β) (_ : cast e a = a'), HEq a a'
  | rfl, h => Eq.recOn h (HEq.refl _)
#align heq_of_cast_eq heq_of_cast_eq

theorem cast_eq_iff_heq : cast e a = a' ↔ HEq a a' :=
  ⟨heq_of_cast_eq _, fun h ↦ by cases h; rfl⟩
                                -- ⊢ cast e a = a
                                         -- 🎉 no goals
#align cast_eq_iff_heq cast_eq_iff_heq

--Porting note: new theorem. More general version of `eqRec_heq`
theorem eqRec_heq' {α : Sort u_1} {a' : α} {motive : (a : α) → a' = a → Sort u}
    (p : motive a' (rfl : a' = a')) {a : α} (t : a' = a) :
    HEq (@Eq.rec α a' motive p a t) p :=
  by subst t; rfl
     -- ⊢ HEq ((_ : a' = a') ▸ p) p
              -- 🎉 no goals

theorem rec_heq_of_heq {C : α → Sort*} {x : C a} {y : β} (e : a = b) (h : HEq x y) :
    HEq (e ▸ x) y := by subst e; exact h
                        -- ⊢ HEq ((_ : a = a) ▸ x) y
                                 -- 🎉 no goals
#align rec_heq_of_heq rec_heq_of_heq

theorem rec_heq_iff_heq {C : α → Sort*} {x : C a} {y : β} {e : a = b} :
    HEq (e ▸ x) y ↔ HEq x y := by subst e; rfl
                                  -- ⊢ HEq ((_ : a = a) ▸ x) y ↔ HEq x y
                                           -- 🎉 no goals
#align rec_heq_iff_heq rec_heq_iff_heq

theorem heq_rec_iff_heq {C : α → Sort*} {x : β} {y : C a} {e : a = b} :
    HEq x (e ▸ y) ↔ HEq x y := by subst e; rfl
                                  -- ⊢ HEq x ((_ : a = a) ▸ y) ↔ HEq x y
                                           -- 🎉 no goals
#align heq_rec_iff_heq heq_rec_iff_heq

protected theorem Eq.congr (h₁ : x₁ = y₁) (h₂ : x₂ = y₂) : x₁ = x₂ ↔ y₁ = y₂ := by
  subst h₁; subst h₂; rfl
  -- ⊢ x₁ = x₂ ↔ x₁ = y₂
            -- ⊢ x₁ = x₂ ↔ x₁ = x₂
                      -- 🎉 no goals
#align eq.congr Eq.congr

theorem Eq.congr_left {x y z : α} (h : x = y) : x = z ↔ y = z := by rw [h]
                                                                    -- 🎉 no goals
#align eq.congr_left Eq.congr_left

theorem Eq.congr_right {x y z : α} (h : x = y) : z = x ↔ z = y := by rw [h]
                                                                     -- 🎉 no goals
#align eq.congr_right Eq.congr_right

alias congr_arg₂ := congrArg₂
#align congr_arg2 congr_arg₂

variable {β : α → Sort*} {γ : ∀ a, β a → Sort*} {δ : ∀ a b, γ a b → Sort*}

theorem congr_fun₂ {f g : ∀ a b, γ a b} (h : f = g) (a : α) (b : β a) : f a b = g a b :=
  congr_fun (congr_fun h _) _
#align congr_fun₂ congr_fun₂

theorem congr_fun₃ {f g : ∀ a b c, δ a b c} (h : f = g) (a : α) (b : β a) (c : γ a b) :
    f a b c = g a b c :=
  congr_fun₂ (congr_fun h _) _ _
#align congr_fun₃ congr_fun₃

theorem funext₂ {f g : ∀ a b, γ a b} (h : ∀ a b, f a b = g a b) : f = g :=
  funext fun _ ↦ funext <| h _
#align funext₂ funext₂

theorem funext₃ {f g : ∀ a b c, δ a b c} (h : ∀ a b c, f a b c = g a b c) : f = g :=
  funext fun _ ↦ funext₂ <| h _
#align funext₃ funext₃

end Equality

/-! ### Declarations about quantifiers -/


section Quantifiers
section Dependent

variable {β : α → Sort*} {γ : ∀ a, β a → Sort*} {δ : ∀ a b, γ a b → Sort*}
  {ε : ∀ a b c, δ a b c → Sort*}

theorem pi_congr {β' : α → Sort _} (h : ∀ a, β a = β' a) : (∀ a, β a) = ∀ a, β' a :=
  (funext h : β = β') ▸ rfl
#align pi_congr pi_congr

-- Porting note: some higher order lemmas such as `forall₂_congr` and `exists₂_congr`
-- were moved to `Std4`

theorem forall₂_imp {p q : ∀ a, β a → Prop} (h : ∀ a b, p a b → q a b) :
    (∀ a b, p a b) → ∀ a b, q a b :=
  forall_imp fun i ↦ forall_imp <| h i
#align forall₂_imp forall₂_imp

theorem forall₃_imp {p q : ∀ a b, γ a b → Prop} (h : ∀ a b c, p a b c → q a b c) :
    (∀ a b c, p a b c) → ∀ a b c, q a b c :=
  forall_imp fun a ↦ forall₂_imp <| h a
#align forall₃_imp forall₃_imp

theorem Exists₂.imp {p q : ∀ a, β a → Prop} (h : ∀ a b, p a b → q a b) :
    (∃ a b, p a b) → ∃ a b, q a b :=
  Exists.imp fun a ↦ Exists.imp <| h a
#align Exists₂.imp Exists₂.imp

theorem Exists₃.imp {p q : ∀ a b, γ a b → Prop} (h : ∀ a b c, p a b c → q a b c) :
    (∃ a b c, p a b c) → ∃ a b c, q a b c :=
  Exists.imp fun a ↦ Exists₂.imp <| h a
#align Exists₃.imp Exists₃.imp

end Dependent

variable {κ : ι → Sort*} {p q : α → Prop}

#align exists_imp_exists' Exists.imp'

theorem forall_swap {p : α → β → Prop} : (∀ x y, p x y) ↔ ∀ y x, p x y := ⟨swap, swap⟩
#align forall_swap forall_swap

theorem forall₂_swap {κ₁ : ι₁ → Sort*} {κ₂ : ι₂ → Sort*} {p : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Prop} :
    (∀ i₁ j₁ i₂ j₂, p i₁ j₁ i₂ j₂) ↔ ∀ i₂ j₂ i₁ j₁, p i₁ j₁ i₂ j₂ := ⟨swap₂, swap₂⟩
#align forall₂_swap forall₂_swap

/-- We intentionally restrict the type of `α` in this lemma so that this is a safer to use in simp
than `forall_swap`. -/
theorem imp_forall_iff {α : Type*} {p : Prop} {q : α → Prop} : (p → ∀ x, q x) ↔ ∀ x, p → q x :=
  forall_swap
#align imp_forall_iff imp_forall_iff

theorem exists_swap {p : α → β → Prop} : (∃ x y, p x y) ↔ ∃ y x, p x y :=
  ⟨fun ⟨x, y, h⟩ ↦ ⟨y, x, h⟩, fun ⟨y, x, h⟩ ↦ ⟨x, y, h⟩⟩
#align exists_swap exists_swap

#align forall_exists_index forall_exists_index

#align exists_imp_distrib exists_imp
alias ⟨_, not_exists_of_forall_not⟩ := exists_imp
#align not_exists_of_forall_not not_exists_of_forall_not

#align Exists.some Exists.choose
#align Exists.some_spec Exists.choose_spec

-- See Note [decidable namespace]
protected theorem Decidable.not_forall {p : α → Prop} [Decidable (∃ x, ¬p x)]
    [∀ x, Decidable (p x)] : (¬∀ x, p x) ↔ ∃ x, ¬p x :=
  ⟨Not.decidable_imp_symm fun nx x ↦ nx.decidable_imp_symm fun h ↦ ⟨x, h⟩,
   not_forall_of_exists_not⟩
#align decidable.not_forall Decidable.not_forall

@[simp]
theorem not_forall {p : α → Prop} : (¬∀ x, p x) ↔ ∃ x, ¬p x :=
  Decidable.not_forall
#align not_forall not_forall

-- See Note [decidable namespace]
protected theorem Decidable.not_forall_not [Decidable (∃ x, p x)] : (¬∀ x, ¬p x) ↔ ∃ x, p x :=
  (@Decidable.not_iff_comm _ _ _ (decidable_of_iff (¬∃ x, p x) not_exists)).1 not_exists
#align decidable.not_forall_not Decidable.not_forall_not

theorem not_forall_not : (¬∀ x, ¬p x) ↔ ∃ x, p x := Decidable.not_forall_not
#align not_forall_not not_forall_not

-- See Note [decidable namespace]
protected theorem Decidable.not_exists_not [∀ x, Decidable (p x)] : (¬∃ x, ¬p x) ↔ ∀ x, p x := by
  simp only [not_exists, Decidable.not_not]
  -- 🎉 no goals
#align decidable.not_exists_not Decidable.not_exists_not

theorem not_exists_not : (¬∃ x, ¬p x) ↔ ∀ x, p x := Decidable.not_exists_not
#align not_exists_not not_exists_not

theorem forall_imp_iff_exists_imp [ha : Nonempty α] : (∀ x, p x) → b ↔ ∃ x, p x → b := by
  let ⟨a⟩ := ha
  -- ⊢ (∀ (x : α), p x) → b ↔ ∃ x, p x → b
  refine ⟨fun h ↦ not_forall_not.1 fun h' ↦ ?_, fun ⟨x, hx⟩ h ↦ hx (h x)⟩
  -- ⊢ False
  exact if hb : b then h' a fun _ ↦ hb else hb <| h fun x ↦ (not_imp.1 (h' x)).1
  -- 🎉 no goals
#align forall_imp_iff_exists_imp forall_imp_iff_exists_imp

@[mfld_simps]
theorem forall_true_iff : (α → True) ↔ True := imp_true_iff _
#align forall_true_iff forall_true_iff

-- Unfortunately this causes simp to loop sometimes, so we
-- add the 2 and 3 cases as simp lemmas instead
theorem forall_true_iff' (h : ∀ a, p a ↔ True) : (∀ a, p a) ↔ True :=
  iff_true_intro fun _ ↦ of_iff_true (h _)
#align forall_true_iff' forall_true_iff'

-- This is not marked `@[simp]` because `implies_true : (α → True) = True` works
theorem forall₂_true_iff {β : α → Sort*} : (∀ a, β a → True) ↔ True := by simp
                                                                          -- 🎉 no goals
#align forall_2_true_iff forall₂_true_iff

-- This is not marked `@[simp]` because `implies_true : (α → True) = True` works
theorem forall₃_true_iff {β : α → Sort*} {γ : ∀ a, β a → Sort*} :
    (∀ (a) (b : β a), γ a b → True) ↔ True := by simp
                                                 -- 🎉 no goals
#align forall_3_true_iff forall₃_true_iff

@[simp] theorem exists_unique_iff_exists [Subsingleton α] {p : α → Prop} :
    (∃! x, p x) ↔ ∃ x, p x :=
  ⟨fun h ↦ h.exists, Exists.imp fun x hx ↦ ⟨hx, fun y _ ↦ Subsingleton.elim y x⟩⟩
#align exists_unique_iff_exists exists_unique_iff_exists

-- forall_forall_const is no longer needed

@[simp] theorem exists_const (α) [i : Nonempty α] : (∃ _ : α, b) ↔ b :=
  ⟨fun ⟨_, h⟩ ↦ h, i.elim Exists.intro⟩
#align exists_const exists_const

theorem exists_unique_const (α) [i : Nonempty α] [Subsingleton α] :
    (∃! _ : α, b) ↔ b := by simp
                            -- 🎉 no goals
#align exists_unique_const exists_unique_const

#align forall_and_distrib forall_and
#align exists_or_distrib exists_or

#align exists_and_distrib_left exists_and_left
#align exists_and_distrib_right exists_and_right

theorem Decidable.and_forall_ne [DecidableEq α] (a : α) {p : α → Prop} :
    (p a ∧ ∀ b, b ≠ a → p b) ↔ ∀ b, p b := by
  simp only [← @forall_eq _ p a, ← forall_and, ← or_imp, Decidable.em, forall_const]
  -- 🎉 no goals
#align decidable.and_forall_ne Decidable.and_forall_ne

theorem and_forall_ne (a : α) : (p a ∧ ∀ b, b ≠ a → p b) ↔ ∀ b, p b :=
  Decidable.and_forall_ne a
#align and_forall_ne and_forall_ne

theorem Ne.ne_or_ne {x y : α} (z : α) (h : x ≠ y) : x ≠ z ∨ y ≠ z :=
  not_and_or.1 <| mt (and_imp.2 (· ▸ ·)) h.symm
#align ne.ne_or_ne Ne.ne_or_ne

@[simp] theorem exists_unique_eq {a' : α} : ∃! a, a = a' := by
  simp only [eq_comm, ExistsUnique, and_self, forall_eq', exists_eq']
  -- 🎉 no goals
#align exists_unique_eq exists_unique_eq

@[simp] theorem exists_unique_eq' {a' : α} : ∃! a, a' = a := by
  simp only [ExistsUnique, and_self, forall_eq', exists_eq']
  -- 🎉 no goals
#align exists_unique_eq' exists_unique_eq'

-- @[simp] -- FIXME simp does not apply this lemma for some reason
theorem exists_apply_eq_apply' (f : α → β) (a' : α) : ∃ a, f a' = f a := ⟨a', rfl⟩
#align exists_apply_eq_apply' exists_apply_eq_apply'

-- porting note: an alternative workaround theorem:
theorem exists_apply_eq (a : α) (b : β) : ∃ f : α → β, f a = b := ⟨fun _ ↦ b, rfl⟩

@[simp] theorem exists_exists_and_eq_and {f : α → β} {p : α → Prop} {q : β → Prop} :
    (∃ b, (∃ a, p a ∧ f a = b) ∧ q b) ↔ ∃ a, p a ∧ q (f a) :=
  ⟨fun ⟨_, ⟨a, ha, hab⟩, hb⟩ ↦ ⟨a, ha, hab.symm ▸ hb⟩, fun ⟨a, hp, hq⟩ ↦ ⟨f a, ⟨a, hp, rfl⟩, hq⟩⟩
#align exists_exists_and_eq_and exists_exists_and_eq_and

@[simp] theorem exists_exists_eq_and {f : α → β} {p : β → Prop} :
    (∃ b, (∃ a, f a = b) ∧ p b) ↔ ∃ a, p (f a) :=
  ⟨fun ⟨_, ⟨a, ha⟩, hb⟩ ↦ ⟨a, ha.symm ▸ hb⟩, fun ⟨a, ha⟩ ↦ ⟨f a, ⟨a, rfl⟩, ha⟩⟩
#align exists_exists_eq_and exists_exists_eq_and

@[simp] theorem exists_or_eq_left (y : α) (p : α → Prop) : ∃ x : α, x = y ∨ p x := ⟨y, .inl rfl⟩
#align exists_or_eq_left exists_or_eq_left

@[simp] theorem exists_or_eq_right (y : α) (p : α → Prop) : ∃ x : α, p x ∨ x = y := ⟨y, .inr rfl⟩
#align exists_or_eq_right exists_or_eq_right

@[simp] theorem exists_or_eq_left' (y : α) (p : α → Prop) : ∃ x : α, y = x ∨ p x := ⟨y, .inl rfl⟩
#align exists_or_eq_left' exists_or_eq_left'

@[simp] theorem exists_or_eq_right' (y : α) (p : α → Prop) : ∃ x : α, p x ∨ y = x := ⟨y, .inr rfl⟩
#align exists_or_eq_right' exists_or_eq_right'

theorem forall_apply_eq_imp_iff {f : α → β} {p : β → Prop} :
    (∀ a b, f a = b → p b) ↔ ∀ a, p (f a) := by simp
                                                -- 🎉 no goals
#align forall_apply_eq_imp_iff forall_apply_eq_imp_iff

@[simp] theorem forall_apply_eq_imp_iff' {f : α → β} {p : β → Prop} :
    (∀ b a, f a = b → p b) ↔ ∀ a, p (f a) := by simp [forall_swap]
                                                -- 🎉 no goals
#align forall_apply_eq_imp_iff' forall_apply_eq_imp_iff'

theorem forall_eq_apply_imp_iff {f : α → β} {p : β → Prop} :
    (∀ a b, b = f a → p b) ↔ ∀ a, p (f a) := by simp
                                                -- 🎉 no goals
#align forall_eq_apply_imp_iff forall_eq_apply_imp_iff

@[simp] theorem forall_eq_apply_imp_iff' {f : α → β} {p : β → Prop} :
    (∀ b a, b = f a → p b) ↔ ∀ a, p (f a) := by simp [forall_swap]
                                                -- 🎉 no goals
#align forall_eq_apply_imp_iff' forall_eq_apply_imp_iff'

@[simp] theorem forall_apply_eq_imp_iff₂ {f : α → β} {p : α → Prop} {q : β → Prop} :
    (∀ b a, p a → f a = b → q b) ↔ ∀ a, p a → q (f a) :=
  ⟨fun h a ha ↦ h (f a) a ha rfl, fun h _ a ha hb ↦ hb ▸ h a ha⟩
#align forall_apply_eq_imp_iff₂ forall_apply_eq_imp_iff₂

@[simp] theorem exists_eq_right' {a' : α} : (∃ a, p a ∧ a' = a) ↔ p a' := by simp [@eq_comm _ a']
                                                                             -- 🎉 no goals
#align exists_eq_right' exists_eq_right'

#align exists_comm exists_comm

theorem exists₂_comm {κ₁ : ι₁ → Sort*} {κ₂ : ι₂ → Sort*} {p : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Prop} :
    (∃ i₁ j₁ i₂ j₂, p i₁ j₁ i₂ j₂) ↔ ∃ i₂ j₂ i₁ j₁, p i₁ j₁ i₂ j₂ := by
  simp only [@exists_comm (κ₁ _), @exists_comm ι₁]
  -- 🎉 no goals
#align exists₂_comm exists₂_comm

theorem And.exists {p q : Prop} {f : p ∧ q → Prop} : (∃ h, f h) ↔ ∃ hp hq, f ⟨hp, hq⟩ :=
  ⟨fun ⟨h, H⟩ ↦ ⟨h.1, h.2, H⟩, fun ⟨hp, hq, H⟩ ↦ ⟨⟨hp, hq⟩, H⟩⟩
#align and.exists And.exists

theorem forall_or_of_or_forall (h : b ∨ ∀ x, p x) (x) : b ∨ p x := h.imp_right fun h₂ ↦ h₂ x
#align forall_or_of_or_forall forall_or_of_or_forall

-- See Note [decidable namespace]
protected theorem Decidable.forall_or_left {q : Prop} {p : α → Prop} [Decidable q] :
    (∀ x, q ∨ p x) ↔ q ∨ ∀ x, p x :=
  ⟨fun h ↦ if hq : q then Or.inl hq else
    Or.inr fun x ↦ (h x).resolve_left hq, forall_or_of_or_forall⟩
#align decidable.forall_or_distrib_left Decidable.forall_or_left

theorem forall_or_left {q} {p : α → Prop} : (∀ x, q ∨ p x) ↔ q ∨ ∀ x, p x :=
  Decidable.forall_or_left
#align forall_or_distrib_left forall_or_left

-- See Note [decidable namespace]
protected theorem Decidable.forall_or_right {q} {p : α → Prop} [Decidable q] :
    (∀ x, p x ∨ q) ↔ (∀ x, p x) ∨ q := by simp [or_comm, Decidable.forall_or_left]
                                          -- 🎉 no goals
#align decidable.forall_or_distrib_right Decidable.forall_or_right

theorem forall_or_right {q} {p : α → Prop} : (∀ x, p x ∨ q) ↔ (∀ x, p x) ∨ q :=
  Decidable.forall_or_right
#align forall_or_distrib_right forall_or_right

theorem exists_unique_prop {p q : Prop} : (∃! _ : p, q) ↔ p ∧ q := by simp
                                                                      -- 🎉 no goals
#align exists_unique_prop exists_unique_prop

@[simp] theorem exists_unique_false : ¬∃! _ : α, False := fun ⟨_, h, _⟩ ↦ h
#align exists_unique_false exists_unique_false

theorem Exists.fst {b : Prop} {p : b → Prop} : Exists p → b
  | ⟨h, _⟩ => h
#align Exists.fst Exists.fst

theorem Exists.snd {b : Prop} {p : b → Prop} : ∀ h : Exists p, p h.fst
  | ⟨_, h⟩ => h
#align Exists.snd Exists.snd

theorem Prop.exists_iff {p : Prop → Prop} : (∃ h, p h) ↔ p False ∨ p True :=
  ⟨fun ⟨h₁, h₂⟩ ↦ by_cases (fun H : h₁ ↦ .inr <| by simpa only [H] using h₂)
                                                    -- 🎉 no goals
    (fun H ↦ .inl <| by simpa only [H] using h₂), fun h ↦ h.elim (.intro _) (.intro _)⟩
                        -- 🎉 no goals

theorem Prop.forall_iff {p : Prop → Prop} : (∀ h, p h) ↔ p False ∧ p True :=
  ⟨fun H ↦ ⟨H _, H _⟩, fun ⟨h₁, h₂⟩ h ↦ by by_cases H : h <;> simpa only [H]⟩
                                           -- ⊢ p h
                                                              -- 🎉 no goals
                                                              -- 🎉 no goals

theorem exists_prop_of_true {p : Prop} {q : p → Prop} (h : p) : (∃ h' : p, q h') ↔ q h :=
  @exists_const (q h) p ⟨h⟩
#align exists_prop_of_true exists_prop_of_true

theorem exists_iff_of_forall {p : Prop} {q : p → Prop} (h : ∀ h, q h) : (∃ h, q h) ↔ p :=
  ⟨Exists.fst, fun H ↦ ⟨H, h H⟩⟩
#align exists_iff_of_forall exists_iff_of_forall

theorem exists_unique_prop_of_true {p : Prop} {q : p → Prop} (h : p) : (∃! h' : p, q h') ↔ q h :=
  @exists_unique_const (q h) p ⟨h⟩ _
#align exists_unique_prop_of_true exists_unique_prop_of_true

theorem forall_prop_of_false {p : Prop} {q : p → Prop} (hn : ¬p) : (∀ h' : p, q h') ↔ True :=
  iff_true_intro fun h ↦ hn.elim h
#align forall_prop_of_false forall_prop_of_false

theorem exists_prop_of_false {p : Prop} {q : p → Prop} : ¬p → ¬∃ h' : p, q h' :=
  mt Exists.fst
#align exists_prop_of_false exists_prop_of_false

@[congr]
theorem exists_prop_congr {p p' : Prop} {q q' : p → Prop} (hq : ∀ h, q h ↔ q' h) (hp : p ↔ p') :
    Exists q ↔ ∃ h : p', q' (hp.2 h) :=
  ⟨fun ⟨_, _⟩ ↦ ⟨hp.1 ‹_›, (hq _).1 ‹_›⟩, fun ⟨_, _⟩ ↦ ⟨_, (hq _).2 ‹_›⟩⟩
#align exists_prop_congr exists_prop_congr

@[congr]
theorem exists_prop_congr' {p p' : Prop} {q q' : p → Prop} (hq : ∀ h, q h ↔ q' h) (hp : p ↔ p') :
    Exists q = ∃ h : p', q' (hp.2 h) :=
  propext (exists_prop_congr hq hp)
#align exists_prop_congr' exists_prop_congr'

/-- See `IsEmpty.exists_iff` for the `False` version. -/
@[simp] theorem exists_true_left (p : True → Prop) : (∃ x, p x) ↔ p True.intro :=
  exists_prop_of_true _
#align exists_true_left exists_true_left

-- Porting note: `@[congr]` commented out for now.
-- @[congr]
theorem forall_prop_congr {p p' : Prop} {q q' : p → Prop} (hq : ∀ h, q h ↔ q' h) (hp : p ↔ p') :
    (∀ h, q h) ↔ ∀ h : p', q' (hp.2 h) :=
  ⟨fun h1 h2 ↦ (hq _).1 (h1 (hp.2 h2)), fun h1 h2 ↦ (hq _).2 (h1 (hp.1 h2))⟩
#align forall_prop_congr forall_prop_congr

-- Porting note: `@[congr]` commented out for now.
-- @[congr]
theorem forall_prop_congr' {p p' : Prop} {q q' : p → Prop} (hq : ∀ h, q h ↔ q' h) (hp : p ↔ p') :
    (∀ h, q h) = ∀ h : p', q' (hp.2 h) :=
  propext (forall_prop_congr hq hp)
#align forall_prop_congr' forall_prop_congr'

/-- See `IsEmpty.forall_iff` for the `False` version. -/
@[simp] theorem forall_true_left (p : True → Prop) : (∀ x, p x) ↔ p True.intro :=
  forall_prop_of_true _
#align forall_true_left forall_true_left

theorem ExistsUnique.elim₂ {α : Sort*} {p : α → Sort*} [∀ x, Subsingleton (p x)]
    {q : ∀ (x) (_ : p x), Prop} {b : Prop} (h₂ : ∃! (x : _) (h : p x), q x h)
    (h₁ : ∀ (x) (h : p x), q x h → (∀ (y) (hy : p y), q y hy → y = x) → b) : b := by
  simp only [exists_unique_iff_exists] at h₂
  -- ⊢ b
  apply h₂.elim
  -- ⊢ ∀ (x : α), (∃ h, q x h) → (∀ (y : α), (∃ h, q y h) → y = x) → b
  exact fun x ⟨hxp, hxq⟩ H ↦ h₁ x hxp hxq fun y hyp hyq ↦ H y ⟨hyp, hyq⟩
  -- 🎉 no goals
#align exists_unique.elim2 ExistsUnique.elim₂

theorem ExistsUnique.intro₂ {α : Sort*} {p : α → Sort*} [∀ x, Subsingleton (p x)]
    {q : ∀ (x : α) (_ : p x), Prop} (w : α) (hp : p w) (hq : q w hp)
    (H : ∀ (y) (hy : p y), q y hy → y = w) : ∃! (x : _) (hx : p x), q x hx := by
  simp only [exists_unique_iff_exists]
  -- ⊢ ∃! x, ∃ hx, q x hx
  exact ExistsUnique.intro w ⟨hp, hq⟩ fun y ⟨hyp, hyq⟩ ↦ H y hyp hyq
  -- 🎉 no goals
#align exists_unique.intro2 ExistsUnique.intro₂

theorem ExistsUnique.exists₂ {α : Sort*} {p : α → Sort*} {q : ∀ (x : α) (_ : p x), Prop}
    (h : ∃! (x : _) (hx : p x), q x hx) : ∃ (x : _) (hx : p x), q x hx :=
  h.exists.imp fun _ hx ↦ hx.exists
#align exists_unique.exists2 ExistsUnique.exists₂

theorem ExistsUnique.unique₂ {α : Sort*} {p : α → Sort*} [∀ x, Subsingleton (p x)]
    {q : ∀ (x : α) (_ : p x), Prop} (h : ∃! (x : _) (hx : p x), q x hx) {y₁ y₂ : α}
    (hpy₁ : p y₁) (hqy₁ : q y₁ hpy₁) (hpy₂ : p y₂) (hqy₂ : q y₂ hpy₂) : y₁ = y₂ := by
  simp only [exists_unique_iff_exists] at h
  -- ⊢ y₁ = y₂
  exact h.unique ⟨hpy₁, hqy₁⟩ ⟨hpy₂, hqy₂⟩
  -- 🎉 no goals
#align exists_unique.unique2 ExistsUnique.unique₂

end Quantifiers

/-! ### Classical lemmas -/

namespace Classical
variable {p : α → Prop}

-- use shortened names to avoid conflict when classical namespace is open.
/-- Any prop `p` is decidable classically. A shorthand for `classical.prop_decidable`. -/
noncomputable def dec (p : Prop) : Decidable p := by infer_instance
                                                     -- 🎉 no goals
#align classical.dec Classical.dec

/-- Any predicate `p` is decidable classically. -/
noncomputable def decPred (p : α → Prop) : DecidablePred p := by infer_instance
                                                                 -- 🎉 no goals
#align classical.dec_pred Classical.decPred

/-- Any relation `p` is decidable classically. -/
noncomputable def decRel (p : α → α → Prop) : DecidableRel p := by infer_instance
                                                                   -- 🎉 no goals
#align classical.dec_rel Classical.decRel

/-- Any type `α` has decidable equality classically. -/
noncomputable def decEq (α : Sort u) : DecidableEq α := by infer_instance
                                                           -- 🎉 no goals
#align classical.dec_eq Classical.decEq

/-- Construct a function from a default value `H0`, and a function to use if there exists a value
satisfying the predicate. -/
-- @[elab_as_elim] -- FIXME
noncomputable def existsCases (H0 : C) (H : ∀ a, p a → C) : C :=
  if h : ∃ a, p a then H (Classical.choose h) (Classical.choose_spec h) else H0
#align classical.exists_cases Classical.existsCases

theorem some_spec₂ {α : Sort*} {p : α → Prop} {h : ∃ a, p a} (q : α → Prop)
    (hpq : ∀ a, p a → q a) : q (choose h) := hpq _ <| choose_spec _
#align classical.some_spec2 Classical.some_spec₂

/-- A version of `Classical.indefiniteDescription` which is definitionally equal to a pair -/
noncomputable def subtype_of_exists {α : Type*} {P : α → Prop} (h : ∃ x, P x) : { x // P x } :=
  ⟨Classical.choose h, Classical.choose_spec h⟩
#align classical.subtype_of_exists Classical.subtype_of_exists

/-- A version of `byContradiction` that uses types instead of propositions. -/
protected noncomputable def byContradiction' {α : Sort*} (H : ¬(α → False)) : α :=
  Classical.choice <| (peirce _ False) fun h ↦ (H fun a ↦ h ⟨a⟩).elim
#align classical.by_contradiction' Classical.byContradiction'

/-- `classical.byContradiction'` is equivalent to lean's axiom `classical.choice`. -/
def choice_of_byContradiction' {α : Sort*} (contra : ¬(α → False) → α) : Nonempty α → α :=
  fun H ↦ contra H.elim
#align classical.choice_of_by_contradiction' Classical.choice_of_byContradiction'

end Classical

/-- This function has the same type as `Exists.recOn`, and can be used to case on an equality,
but `Exists.recOn` can only eliminate into Prop, while this version eliminates into any universe
using the axiom of choice. -/
-- @[elab_as_elim] -- FIXME
noncomputable def Exists.classicalRecOn {p : α → Prop} (h : ∃ a, p a) {C} (H : ∀ a, p a → C) : C :=
  H (Classical.choose h) (Classical.choose_spec h)
#align exists.classical_rec_on Exists.classicalRecOn

/-! ### Declarations about bounded quantifiers -/

section BoundedQuantifiers
variable {r p q : α → Prop} {P Q : ∀ x, p x → Prop} {b : Prop}

theorem bex_def : (∃ (x : _) (_ : p x), q x) ↔ ∃ x, p x ∧ q x :=
  ⟨fun ⟨x, px, qx⟩ ↦ ⟨x, px, qx⟩, fun ⟨x, px, qx⟩ ↦ ⟨x, px, qx⟩⟩
#align bex_def bex_def

theorem BEx.elim {b : Prop} : (∃ x h, P x h) → (∀ a h, P a h → b) → b
  | ⟨a, h₁, h₂⟩, h' => h' a h₁ h₂
#align bex.elim BEx.elim

theorem BEx.intro (a : α) (h₁ : p a) (h₂ : P a h₁) : ∃ (x : _) (h : p x), P x h :=
  ⟨a, h₁, h₂⟩
#align bex.intro BEx.intro

theorem ball_congr (H : ∀ x h, P x h ↔ Q x h) : (∀ x h, P x h) ↔ ∀ x h, Q x h :=
  forall_congr' fun x ↦ forall_congr' (H x)
#align ball_congr ball_congr

theorem bex_congr (H : ∀ x h, P x h ↔ Q x h) : (∃ x h, P x h) ↔ ∃ x h, Q x h :=
  exists_congr fun x ↦ exists_congr (H x)
#align bex_congr bex_congr

theorem bex_eq_left {a : α} : (∃ (x : _) (_ : x = a), p x) ↔ p a := by
  simp only [exists_prop, exists_eq_left]
  -- 🎉 no goals
#align bex_eq_left bex_eq_left

theorem BAll.imp_right (H : ∀ x h, P x h → Q x h) (h₁ : ∀ x h, P x h) (x h) : Q x h :=
  H _ _ <| h₁ _ _
#align ball.imp_right BAll.imp_right

theorem BEx.imp_right (H : ∀ x h, P x h → Q x h) : (∃ x h, P x h) → ∃ x h, Q x h
  | ⟨_, _, h'⟩ => ⟨_, _, H _ _ h'⟩
#align bex.imp_right BEx.imp_right

theorem BAll.imp_left (H : ∀ x, p x → q x) (h₁ : ∀ x, q x → r x) (x) (h : p x) : r x :=
  h₁ _ <| H _ h
#align ball.imp_left BAll.imp_left

theorem BEx.imp_left (H : ∀ x, p x → q x) : (∃ (x : _) (_ : p x), r x) → ∃ (x : _) (_ : q x), r x
  | ⟨x, hp, hr⟩ => ⟨x, H _ hp, hr⟩
#align bex.imp_left BEx.imp_left

theorem ball_of_forall (h : ∀ x, p x) (x) : p x := h x
#align ball_of_forall ball_of_forall

theorem forall_of_ball (H : ∀ x, p x) (h : ∀ x, p x → q x) (x) : q x := h x <| H x
#align forall_of_ball forall_of_ball

theorem bex_of_exists (H : ∀ x, p x) : (∃ x, q x) → ∃ (x : _) (_ : p x), q x
  | ⟨x, hq⟩ => ⟨x, H x, hq⟩
#align bex_of_exists bex_of_exists

theorem exists_of_bex : (∃ (x : _) (_ : p x), q x) → ∃ x, q x
  | ⟨x, _, hq⟩ => ⟨x, hq⟩
#align exists_of_bex exists_of_bex

theorem bex_imp : (∃ x h, P x h) → b ↔ ∀ x h, P x h → b := by simp
                                                              -- 🎉 no goals
#align bex_imp_distrib bex_imp

theorem not_bex : (¬∃ x h, P x h) ↔ ∀ x h, ¬P x h := bex_imp
#align not_bex not_bex

theorem not_ball_of_bex_not : (∃ x h, ¬P x h) → ¬∀ x h, P x h
  | ⟨x, h, hp⟩, al => hp <| al x h
#align not_ball_of_bex_not not_ball_of_bex_not

-- See Note [decidable namespace]
protected theorem Decidable.not_ball [Decidable (∃ x h, ¬P x h)] [∀ x h, Decidable (P x h)] :
    (¬∀ x h, P x h) ↔ ∃ x h, ¬P x h :=
  ⟨Not.decidable_imp_symm fun nx x h ↦ nx.decidable_imp_symm
    fun h' ↦ ⟨x, h, h'⟩, not_ball_of_bex_not⟩
#align decidable.not_ball Decidable.not_ball

theorem not_ball : (¬∀ x h, P x h) ↔ ∃ x h, ¬P x h := Decidable.not_ball
#align not_ball not_ball

theorem ball_true_iff (p : α → Prop) : (∀ x, p x → True) ↔ True :=
  iff_true_intro fun _ _ ↦ trivial
#align ball_true_iff ball_true_iff

theorem ball_and : (∀ x h, P x h ∧ Q x h) ↔ (∀ x h, P x h) ∧ ∀ x h, Q x h :=
  Iff.trans (forall_congr' fun _ ↦ forall_and) forall_and
#align ball_and_distrib ball_and

theorem bex_or : (∃ x h, P x h ∨ Q x h) ↔ (∃ x h, P x h) ∨ ∃ x h, Q x h :=
  Iff.trans (exists_congr fun _ ↦ exists_or) exists_or
#align bex_or_distrib bex_or

theorem ball_or_left : (∀ x, p x ∨ q x → r x) ↔ (∀ x, p x → r x) ∧ ∀ x, q x → r x :=
  Iff.trans (forall_congr' fun _ ↦ or_imp) forall_and
#align ball_or_left_distrib ball_or_left

theorem bex_or_left :
    (∃ (x : _) (_ : p x ∨ q x), r x) ↔ (∃ (x : _) (_ : p x), r x) ∨ ∃ (x : _) (_ : q x), r x := by
  simp only [exists_prop]
  -- ⊢ (∃ x, (p x ∨ q x) ∧ r x) ↔ (∃ x, p x ∧ r x) ∨ ∃ x, q x ∧ r x
  exact Iff.trans (exists_congr fun x ↦ or_and_right) exists_or
  -- 🎉 no goals
#align bex_or_left_distrib bex_or_left

end BoundedQuantifiers

#align classical.not_ball not_ball

section ite

variable {σ : α → Sort*} (f : α → β) {P Q : Prop} [Decidable P] [Decidable Q]
  {a b c : α} {A : P → α} {B : ¬P → α}

theorem dite_eq_iff : dite P A B = c ↔ (∃ h, A h = c) ∨ ∃ h, B h = c := by
  by_cases P <;> simp [*, exists_prop_of_true, exists_prop_of_false]
  -- ⊢ dite P A B = c ↔ (∃ h, A h = c) ∨ ∃ h, B h = c
  -- ⊢ dite P A B = c ↔ (∃ h, A h = c) ∨ ∃ h, B h = c
                 -- 🎉 no goals
                 -- 🎉 no goals
#align dite_eq_iff dite_eq_iff

theorem ite_eq_iff : ite P a b = c ↔ P ∧ a = c ∨ ¬P ∧ b = c :=
  dite_eq_iff.trans <| by simp only; rw [exists_prop, exists_prop]
                          -- ⊢ ((∃ h, a = c) ∨ ∃ h, b = c) ↔ P ∧ a = c ∨ ¬P ∧ b = c
                                     -- 🎉 no goals
#align ite_eq_iff ite_eq_iff

theorem eq_ite_iff : a = ite P b c ↔ P ∧ a = b ∨ ¬P ∧ a = c :=
  eq_comm.trans <| ite_eq_iff.trans <| (Iff.rfl.and eq_comm).or (Iff.rfl.and eq_comm)

theorem dite_eq_iff' : dite P A B = c ↔ (∀ h, A h = c) ∧ ∀ h, B h = c :=
  ⟨fun he ↦ ⟨fun h ↦ (dif_pos h).symm.trans he, fun h ↦ (dif_neg h).symm.trans he⟩, fun he ↦
    (em P).elim (fun h ↦ (dif_pos h).trans <| he.1 h) fun h ↦ (dif_neg h).trans <| he.2 h⟩
#align dite_eq_iff' dite_eq_iff'

theorem ite_eq_iff' : ite P a b = c ↔ (P → a = c) ∧ (¬P → b = c) := dite_eq_iff'
#align ite_eq_iff' ite_eq_iff'

@[simp] theorem dite_eq_left_iff : dite P (fun _ ↦ a) B = a ↔ ∀ h, B h = a := by
  by_cases P <;> simp [*, forall_prop_of_true, forall_prop_of_false]
  -- ⊢ dite P (fun x => a) B = a ↔ ∀ (h : ¬P), B h = a
  -- ⊢ dite P (fun x => a) B = a ↔ ∀ (h : ¬P), B h = a
                 -- 🎉 no goals
                 -- 🎉 no goals
#align dite_eq_left_iff dite_eq_left_iff

@[simp] theorem dite_eq_right_iff : (dite P A fun _ ↦ b) = b ↔ ∀ h, A h = b := by
  by_cases P <;> simp [*, forall_prop_of_true, forall_prop_of_false]
  -- ⊢ (dite P A fun x => b) = b ↔ ∀ (h : P), A h = b
  -- ⊢ (dite P A fun x => b) = b ↔ ∀ (h : P), A h = b
                 -- 🎉 no goals
                 -- 🎉 no goals
#align dite_eq_right_iff dite_eq_right_iff

@[simp] theorem ite_eq_left_iff : ite P a b = a ↔ ¬P → b = a := dite_eq_left_iff
#align ite_eq_left_iff ite_eq_left_iff

@[simp] theorem ite_eq_right_iff : ite P a b = b ↔ P → a = b := dite_eq_right_iff
#align ite_eq_right_iff ite_eq_right_iff

theorem dite_ne_left_iff : dite P (fun _ ↦ a) B ≠ a ↔ ∃ h, a ≠ B h := by
  rw [Ne.def, dite_eq_left_iff, not_forall]
  -- ⊢ (∃ x, ¬B x = a) ↔ ∃ h, a ≠ B h
  exact exists_congr fun h ↦ by rw [ne_comm]
  -- 🎉 no goals
#align dite_ne_left_iff dite_ne_left_iff

theorem dite_ne_right_iff : (dite P A fun _ ↦ b) ≠ b ↔ ∃ h, A h ≠ b := by
  simp only [Ne.def, dite_eq_right_iff, not_forall]
  -- 🎉 no goals
#align dite_ne_right_iff dite_ne_right_iff

theorem ite_ne_left_iff : ite P a b ≠ a ↔ ¬P ∧ a ≠ b :=
  dite_ne_left_iff.trans <| by simp only; rw [exists_prop]
                               -- ⊢ (∃ h, a ≠ b) ↔ ¬P ∧ a ≠ b
                                          -- 🎉 no goals
#align ite_ne_left_iff ite_ne_left_iff

theorem ite_ne_right_iff : ite P a b ≠ b ↔ P ∧ a ≠ b :=
  dite_ne_right_iff.trans <| by simp only; rw [exists_prop]
                                -- ⊢ (∃ h, a ≠ b) ↔ P ∧ a ≠ b
                                           -- 🎉 no goals
#align ite_ne_right_iff ite_ne_right_iff

protected theorem Ne.dite_eq_left_iff (h : ∀ h, a ≠ B h) : dite P (fun _ ↦ a) B = a ↔ P :=
  dite_eq_left_iff.trans ⟨fun H ↦ of_not_not fun h' ↦ h h' (H h').symm, fun h H ↦ (H h).elim⟩
#align ne.dite_eq_left_iff Ne.dite_eq_left_iff

protected theorem Ne.dite_eq_right_iff (h : ∀ h, A h ≠ b) : (dite P A fun _ ↦ b) = b ↔ ¬P :=
  dite_eq_right_iff.trans ⟨fun H h' ↦ h h' (H h'), fun h' H ↦ (h' H).elim⟩
#align ne.dite_eq_right_iff Ne.dite_eq_right_iff

protected theorem Ne.ite_eq_left_iff (h : a ≠ b) : ite P a b = a ↔ P :=
  Ne.dite_eq_left_iff fun _ ↦ h
#align ne.ite_eq_left_iff Ne.ite_eq_left_iff

protected theorem Ne.ite_eq_right_iff (h : a ≠ b) : ite P a b = b ↔ ¬P :=
  Ne.dite_eq_right_iff fun _ ↦ h
#align ne.ite_eq_right_iff Ne.ite_eq_right_iff

protected theorem Ne.dite_ne_left_iff (h : ∀ h, a ≠ B h) : dite P (fun _ ↦ a) B ≠ a ↔ ¬P :=
  dite_ne_left_iff.trans <| exists_iff_of_forall h
#align ne.dite_ne_left_iff Ne.dite_ne_left_iff

protected theorem Ne.dite_ne_right_iff (h : ∀ h, A h ≠ b) : (dite P A fun _ ↦ b) ≠ b ↔ P :=
  dite_ne_right_iff.trans <| exists_iff_of_forall h
#align ne.dite_ne_right_iff Ne.dite_ne_right_iff

protected theorem Ne.ite_ne_left_iff (h : a ≠ b) : ite P a b ≠ a ↔ ¬P :=
  Ne.dite_ne_left_iff fun _ ↦ h
#align ne.ite_ne_left_iff Ne.ite_ne_left_iff

protected theorem Ne.ite_ne_right_iff (h : a ≠ b) : ite P a b ≠ b ↔ P :=
  Ne.dite_ne_right_iff fun _ ↦ h
#align ne.ite_ne_right_iff Ne.ite_ne_right_iff

variable (P Q a b)

/-- A `dite` whose results do not actually depend on the condition may be reduced to an `ite`. -/
@[simp] theorem dite_eq_ite : (dite P (fun _ ↦ a) fun _ ↦ b) = ite P a b := rfl
#align dite_eq_ite dite_eq_ite

theorem dite_eq_or_eq : (∃ h, dite P A B = A h) ∨ ∃ h, dite P A B = B h :=
  if h : _ then .inl ⟨h, dif_pos h⟩ else .inr ⟨h, dif_neg h⟩
#align dite_eq_or_eq dite_eq_or_eq

theorem ite_eq_or_eq : ite P a b = a ∨ ite P a b = b :=
  if h : _ then .inl (if_pos h) else .inr (if_neg h)
#align ite_eq_or_eq ite_eq_or_eq

/-- A two-argument function applied to two `dite`s is a `dite` of that two-argument function
applied to each of the branches. -/
theorem apply_dite₂ (f : α → β → γ) (P : Prop) [Decidable P] (a : P → α) (b : ¬P → α)
    (c : P → β) (d : ¬P → β) :
    f (dite P a b) (dite P c d) = dite P (fun h ↦ f (a h) (c h)) fun h ↦ f (b h) (d h) := by
  by_cases h : P <;> simp [h]
  -- ⊢ f (dite P a b) (dite P c d) = if h : P then f (a h) (c h) else f (b h) (d h)
                     -- 🎉 no goals
                     -- 🎉 no goals
#align apply_dite2 apply_dite₂

/-- A two-argument function applied to two `ite`s is a `ite` of that two-argument function
applied to each of the branches. -/
theorem apply_ite₂ (f : α → β → γ) (P : Prop) [Decidable P] (a b : α) (c d : β) :
    f (ite P a b) (ite P c d) = ite P (f a c) (f b d) :=
  apply_dite₂ f P (fun _ ↦ a) (fun _ ↦ b) (fun _ ↦ c) fun _ ↦ d
#align apply_ite2 apply_ite₂

/-- A 'dite' producing a `Pi` type `Π a, σ a`, applied to a value `a : α` is a `dite` that applies
either branch to `a`. -/
theorem dite_apply (f : P → ∀ a, σ a) (g : ¬P → ∀ a, σ a) (a : α) :
    (dite P f g) a = dite P (fun h ↦ f h a) fun h ↦ g h a := by by_cases h:P <;> simp [h]
                                                                -- ⊢ dite P f g a = if h : P then f h a else g h a
                                                                                 -- 🎉 no goals
                                                                                 -- 🎉 no goals
#align dite_apply dite_apply

/-- A 'ite' producing a `Pi` type `Π a, σ a`, applied to a value `a : α` is a `ite` that applies
either branch to `a`. -/
theorem ite_apply (f g : ∀ a, σ a) (a : α) : (ite P f g) a = ite P (f a) (g a) :=
  dite_apply P (fun _ ↦ f) (fun _ ↦ g) a
#align ite_apply ite_apply

theorem ite_and : ite (P ∧ Q) a b = ite P (ite Q a b) b := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]
  -- ⊢ (if P ∧ Q then a else b) = if P then if Q then a else b else b
                      -- ⊢ (if P ∧ Q then a else b) = if P then if Q then a else b else b
                      -- ⊢ (if P ∧ Q then a else b) = if P then if Q then a else b else b
                                          -- 🎉 no goals
                                          -- 🎉 no goals
                                          -- 🎉 no goals
                                          -- 🎉 no goals
#align ite_and ite_and

theorem dite_dite_comm {B : Q → α} {C : ¬P → ¬Q → α} (h : P → ¬Q) :
    (if p : P then A p else if q : Q then B q else C p q) =
     if q : Q then B q else if p : P then A p else C p q :=
  dite_eq_iff'.2 ⟨
    fun p ↦ by rw [dif_neg (h p), dif_pos p],
               -- 🎉 no goals
    fun np ↦ by congr; funext _; rw [dif_neg np]⟩
                -- ⊢ (fun q => C np q) = fun q => if p : P then A p else C p q
                       -- ⊢ C np x✝ = if p : P then A p else C p x✝
                                 -- 🎉 no goals
#align dite_dite_comm dite_dite_comm

theorem ite_ite_comm (h : P → ¬Q) :
    (if P then a else if Q then b else c) =
     if Q then b else if P then a else c :=
  dite_dite_comm P Q h
#align ite_ite_comm ite_ite_comm

end ite
