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
import Mathlib.Tactic.SimpTrace
import Std.Util.LibraryNote
import Std.Tactic.Lint.Basic

/-!
# Basic logic properties

This file is one of the earliest imports in mathlib.

## Implementation notes

Theorems that require decidability hypotheses are in the namespace "decidable".
Classical versions are in the namespace "classical".
-/

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
@[reducible] def hidden {α : Sort _} {a : α} := a

instance (priority := 10) decidableEq_of_subsingleton [Subsingleton α] : DecidableEq α :=
  fun a b => isTrue (Subsingleton.elim a b)
#align decidable_eq_of_subsingleton decidableEq_of_subsingleton

instance (α : Sort _) [Subsingleton α] (p : α → Prop) : Subsingleton (Subtype p) :=
  ⟨fun ⟨x, _⟩ ⟨y, _⟩ => by cases Subsingleton.elim x y; rfl⟩

-- Porting note: I suspect we don't need the following lemmas anymore, since we don't
-- have a separate `coe_fn` anymore.

-- Porting note: The following simp lemma has `Coe` and `CoeTC` switched because `coeTrans` in
-- `Init.Coe` as the transitive closure on the other position.
-- /-- Add an instance to "undo" coercion transitivity into a chain of coercions, because
--     most simp lemmas are stated with respect to simple coercions and will not match when
--     part of a chain. -/
--  @[simp] theorem coe_coe [CoeTC α β] [Coe β γ] (a : α) : @CoeTC.coe α γ _ a = (a : β) := rfl

-- theorem coe_fn_coe_trans {α β γ δ} [Coe α β] [HasCoeTCAux β γ] [CoeFun γ δ] (x : α) :
--     @coeFn α _ _ x = @coeFn β _ _ x :=
--   rfl

-- /-- Non-dependent version of `coe_fn_coe_trans`, helps `rw` figure out the argument. -/
-- theorem coe_fn_coe_trans' {α β γ} {δ : outParam <| _} [Coe α β] [HasCoeTAux β γ]
--     [CoeFun γ fun _ => δ] (x : α) : @coeFn α _ _ x = @coeFn β _ _ x :=
--   rfl

-- @[simp] theorem coe_fn_coe_base {α β γ} [Coe α β] [CoeFun β γ] (x : α) :
--    coe α _ _ x = @coeFn β _ _ x :=
--  rfl

-- /-- Non-dependent version of `coe_fn_coe_base`, helps `rw` figure out the argument. -/
-- theorem coe_fn_coe_base' {α β} {γ : outParam <| _} [Coe α β] [CoeFun β fun _ => γ] (x : α) :
--     @coeFn α _ _ x = @coeFn β _ _ x :=
--   rfl

-- -- This instance should have low priority, to ensure we follow the chain
-- -- `set_like → has_coe_to_sort`
-- attribute [instance] coeSortTrans

-- theorem coe_sort_coe_trans {α β γ δ} [Coe α β] [HasCoeTAux β γ] [CoeSort γ δ] (x : α) :
--     @coeSort α _ _ x = @coeSort β _ _ x :=
--   rfl

library_note "function coercion" /--
Many structures such as bundled morphisms coerce to functions so that you can
transparently apply them to arguments. For example, if `e : α ≃ β` and `a : α`
then you can write `e a` and this is elaborated as `⇑e a`. This type of
coercion is implemented using the `has_coe_to_fun` type class. There is one
important consideration:

If a type coerces to another type which in turn coerces to a function,
then it **must** implement `has_coe_to_fun` directly:
```lean
structure sparkling_equiv (α β) extends α ≃ β

-- if we add a `has_coe` instance,
instance {α β} : has_coe (sparkling_equiv α β) (α ≃ β) :=
⟨sparkling_equiv.to_equiv⟩

-- then a `has_coe_to_fun` instance **must** be added as well:
instance {α β} : has_coe_to_fun (sparkling_equiv α β) :=
⟨λ _, α → β, λ f, f.to_equiv.to_fun⟩
```

(Rationale: if we do not declare the direct coercion, then `⇑e a` is not in
simp-normal form. The lemma `coe_fn_coe_base` will unfold it to `⇑↑e a`. This
often causes loops in the simplifier.)
-/

-- @[simp]
-- theorem coe_sort_coe_base {α β γ} [Coe α β] [CoeSort β γ] (x : α) :
--     @coeSort α _ _ x = @coeSort β _ _ x :=
--   rfl

#align pempty PEmpty

theorem congr_heq {α β γ : Sort _} {f : α → γ} {g : β → γ} {x : α} {y : β}
    (h₁ : HEq f g) (h₂ : HEq x y) : f x = g y := by
  cases h₂; cases h₁; rfl

theorem congr_arg_heq {α} {β : α → Sort _} (f : ∀ a, β a) :
    ∀ {a₁ a₂ : α}, a₁ = a₂ → HEq (f a₁) (f a₂)
  | _, _, rfl => HEq.rfl

theorem ULift.down_injective {α : Sort _} : Function.Injective (@ULift.down α)
  | ⟨a⟩, ⟨b⟩, _ => by congr

@[simp] theorem ULift.down_inj {α : Sort _} {a b : ULift α} : a.down = b.down ↔ a = b :=
  ⟨fun h => ULift.down_injective h, fun h => by rw [h]⟩

theorem PLift.down_injective {α : Sort _} : Function.Injective (@PLift.down α)
  | ⟨a⟩, ⟨b⟩, _ => by congr

@[simp] theorem PLift.down_inj {α : Sort _} {a b : PLift α} : a.down = b.down ↔ a = b :=
  ⟨fun h => PLift.down_injective h, fun h => by rw [h]⟩

@[simp] theorem eq_iff_eq_cancel_left {b c : α} : (∀ {a}, a = b ↔ a = c) ↔ b = c :=
  ⟨fun h => by rw [← h], fun h a => by rw [h]⟩

@[simp] theorem eq_iff_eq_cancel_right {a b : α} : (∀ {c}, a = c ↔ b = c) ↔ a = b :=
  ⟨fun h => by rw [h], fun h a => by rw [h]⟩

/-- Wrapper for adding elementary propositions to the type class systems.
Warning: this can easily be abused. See the rest of this docstring for details.

Certain propositions should not be treated as a class globally,
but sometimes it is very convenient to be able to use the type class system
in specific circumstances.

For example, `Zmod p` is a field if and only if `p` is a prime number.
In order to be able to find this field instance automatically by type class search,
we have to turn `p.prime` into an instance implicit assumption.

On the other hand, making `Nat.prime` a class would require a major refactoring of the library,
and it is questionable whether making `Nat.prime` a class is desirable at all.
The compromise is to add the assumption `[Fact p.prime]` to `Zmod.field`.

In particular, this class is not intended for turning the type class system
into an automated theorem prover for first order logic. -/
class Fact (p : Prop) : Prop where
  /-- `Fact.out` contains the unwrapped witness for the fact represented by the instance of
  `Fact p`. -/
  out : p

library_note "fact non-instances"/--
In most cases, we should not have global instances of `Fact`; typeclass search only reads the head
symbol and then tries any instances, which means that adding any such instance will cause slowdowns
everywhere. We instead make them as lemmata and make them local instances as required.
-/

theorem Fact.elim {p : Prop} (h : Fact p) : p := h.1
theorem fact_iff {p : Prop} : Fact p ↔ p := ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- Swaps two pairs of arguments to a function. -/
@[reducible] def Function.swap₂ {κ₁ : ι₁ → Sort _} {κ₂ : ι₂ → Sort _}
    {φ : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Sort _} (f : ∀ i₁ j₁ i₂ j₂, φ i₁ j₁ i₂ j₂)
    (i₂ j₂ i₁ j₁) : φ i₁ j₁ i₂ j₂ := f i₁ j₁ i₂ j₂

-- Porting note: these don't work as intended any more
-- /-- If `x : α . tac_name` then `x.out : α`. These are definitionally equal, but this can
-- nevertheless be useful for various reasons, e.g. to apply further projection notation or in an
-- argument to `simp`. -/
-- def autoParam'.out {α : Sort _} {n : Name} (x : autoParam' α n) : α := x

-- /-- If `x : α := d` then `x.out : α`. These are definitionally equal, but this can
-- nevertheless be useful for various reasons, e.g. to apply further projection notation or in an
-- argument to `simp`. -/
-- def optParam.out {α : Sort _} {d : α} (x : α := d) : α := x

end Miscellany

open Function

/-!
### Declarations about propositional connectives
-/

section Propositional

/-! ### Declarations about `implies` -/

instance : IsRefl Prop Iff := ⟨Iff.refl⟩

instance : IsTrans Prop Iff := ⟨fun _ _ _ => Iff.trans⟩

alias imp_congr ← Iff.imp

@[simp] theorem eq_true_eq_id : Eq True = id := by
  funext _; simp only [true_iff, id.def, eq_iff_iff]

#align imp_and_distrib imp_and
#align imp_iff_right imp_iff_rightₓ -- reorder implicits
#align imp_iff_not imp_iff_notₓ -- reorder implicits

@[simp] theorem imp_iff_right_iff : (a → b ↔ b) ↔ a ∨ b := Decidable.imp_iff_right_iff

@[simp] theorem and_or_imp : a ∧ b ∨ (a → c) ↔ a → b ∨ c := Decidable.and_or_imp

/-- Provide modus tollens (`mt`) as dot notation for implications. -/
protected theorem Function.mt : (a → b) → ¬b → ¬a := mt

/-! ### Declarations about `not` -/

alias Decidable.em ← dec_em

theorem dec_em' (p : Prop) [Decidable p] : ¬p ∨ p := (dec_em p).symm

alias Classical.em ← em

theorem em' (p : Prop) : ¬p ∨ p := (em p).symm

theorem or_not {p : Prop} : p ∨ ¬p := em _

theorem Decidable.eq_or_ne (x y : α) [Decidable (x = y)] : x = y ∨ x ≠ y := dec_em <| x = y

theorem Decidable.ne_or_eq (x y : α) [Decidable (x = y)] : x ≠ y ∨ x = y := dec_em' <| x = y

theorem eq_or_ne (x y : α) : x = y ∨ x ≠ y := em <| x = y

theorem ne_or_eq (x y : α) : x ≠ y ∨ x = y := em' <| x = y

theorem by_contradiction : (¬p → False) → p := Decidable.by_contradiction

alias by_contradiction ← by_contra

library_note "decidable namespace"/--
In most of mathlib, we use the law of excluded middle (LEM) and the axiom of choice (AC) freely.
The `decidable` namespace contains versions of lemmas from the root namespace that explicitly
attempt to avoid the axiom of choice, usually by adding decidability assumptions on the inputs.

You can check if a lemma uses the axiom of choice by using `#print axioms foo` and seeing if
`classical.choice` appears in the list.
-/

library_note "decidable arguments"/--
As mathlib is primarily classical,
if the type signature of a `def` or `lemma` does not require any `decidable` instances to state,
it is preferable not to introduce any `decidable` instances that are needed in the proof
as arguments, but rather to use the `classical` tactic as needed.

In the other direction, when `decidable` instances do appear in the type signature,
it is better to use explicitly introduced ones rather than allowing Lean to automatically infer
classical ones, as these may cause instance mismatch errors later.
-/

/-- The Double Negation Theorem: `¬ ¬ P` is equivalent to `P`.
The left-to-right direction, double negation elimination (DNE),
is classically true but not constructively. -/
@[simp] theorem not_not : ¬¬a ↔ a := Decidable.not_not

theorem of_not_not : ¬¬a → a := by_contra

theorem not_ne_iff : ¬a ≠ b ↔ a = b := not_not

theorem of_not_imp {a b : Prop} : ¬(a → b) → a := Decidable.of_not_imp

alias Decidable.not_imp_symm ← Not.decidable_imp_symm

theorem Not.imp_symm : (¬a → b) → ¬b → a := Not.decidable_imp_symm

theorem not_imp_comm : ¬a → b ↔ ¬b → a := Decidable.not_imp_comm

@[simp] theorem not_imp_self : ¬a → a ↔ a := Decidable.not_imp_self

theorem Imp.swap : a → b → c ↔ b → a → c := ⟨Function.swap, Function.swap⟩

alias not_congr ← Iff.not
theorem Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b := h.not.trans not_not
theorem Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b := not_not.symm.trans h.not

/-! ### Declarations about `xor` -/

@[simp] theorem xor_true : Xor' True = Not := by simp [Xor']

@[simp] theorem xor_false : Xor' False = id := by ext; simp [Xor']

theorem xor_comm (a b) : Xor' a b = Xor' b a := by simp [Xor', and_comm, or_comm]

instance : IsCommutative Prop Xor' := ⟨xor_comm⟩

@[simp] theorem xor_self (a : Prop) : Xor' a a = False := by simp [Xor']

/-! ### Declarations about `and` -/

alias and_congr ← Iff.and
#align and_congr_left and_congr_leftₓ -- reorder implicits
#align and_congr_right' and_congr_right'ₓ -- reorder implicits
#align and.right_comm and_right_comm
#align and_and_distrib_left and_and_left
#align and_and_distrib_right and_and_right
alias and_rotate ↔ And.rotate _
#align and.congr_right_iff and_congr_right_iff
#align and.congr_left_iff and_congr_left_iffₓ -- reorder implicits

theorem and_symm_right (a b : α) (p : Prop) : p ∧ a = b ↔ p ∧ b = a := by simp [eq_comm]
theorem and_symm_left (a b : α) (p : Prop) : a = b ∧ p ↔ b = a ∧ p := by simp [eq_comm]

/-! ### Declarations about `or` -/

alias or_congr ← Iff.or
#align or_congr_left' or_congr_left
#align or_congr_right' or_congr_rightₓ -- reorder implicits
#align or.right_comm or_right_comm
alias or_rotate ↔ Or.rotate _

@[deprecated Or.imp]
theorem or_of_or_of_imp_of_imp (h₁ : a ∨ b) (h₂ : a → c) (h₃ : b → d) : c ∨ d := Or.imp h₂ h₃ h₁

@[deprecated Or.imp_left]
theorem or_of_or_of_imp_left (h₁ : a ∨ c) (h : a → b) : b ∨ c := Or.imp_left h h₁

@[deprecated Or.imp_right]
theorem or_of_or_of_imp_right (h₁ : c ∨ a) (h : a → b) : c ∨ b := Or.imp_right h h₁

theorem Or.elim3 {d : Prop} (h : a ∨ b ∨ c) (ha : a → d) (hb : b → d) (hc : c → d) : d :=
  Or.elim h ha fun h₂ => Or.elim h₂ hb hc

theorem Or.imp3 (had : a → d) (hbe : b → e) (hcf : c → f) : a ∨ b ∨ c → d ∨ e ∨ f :=
  Or.imp had <| Or.imp hbe hcf

#align or_imp_distrib or_imp

theorem or_iff_not_imp_left : a ∨ b ↔ ¬a → b := Decidable.or_iff_not_imp_left

theorem or_iff_not_imp_right : a ∨ b ↔ ¬b → a := Decidable.or_iff_not_imp_right

theorem not_or_of_imp : (a → b) → ¬a ∨ b := Decidable.not_or_of_imp

-- See Note [decidable namespace]
protected theorem Decidable.or_not_of_imp [Decidable a] (h : a → b) : b ∨ ¬a :=
  dite _ (Or.inl ∘ h) Or.inr

theorem or_not_of_imp : (a → b) → b ∨ ¬a := Decidable.or_not_of_imp

theorem imp_iff_not_or : a → b ↔ ¬a ∨ b := Decidable.imp_iff_not_or

theorem imp_iff_or_not : b → a ↔ a ∨ ¬b := Decidable.imp_iff_or_not

theorem not_imp_not : ¬a → ¬b ↔ b → a := Decidable.not_imp_not

/-- Provide the reverse of modus tollens (`mt`) as dot notation for implications. -/
protected theorem Function.mtr : (¬a → ¬b) → b → a := not_imp_not.mp

#align decidable.or_congr_left Decidable.or_congr_left'
#align decidable.or_congr_right Decidable.or_congr_right'
#align decidable.or_iff_not_imp_right Decidable.or_iff_not_imp_rightₓ -- reorder implicits
#align decidable.imp_iff_or_not Decidable.imp_iff_or_notₓ -- reorder implicits
#align or_congr_left or_congr_left'
#align or_congr_right or_congr_right'ₓ -- reorder implicits
#align or_iff_left or_iff_leftₓ -- reorder implicits

/-! ### Declarations about distributivity -/

#align and_or_distrib_left and_or_left
#align or_and_distrib_right or_and_right
#align or_and_distrib_left or_and_left
#align and_or_distrib_right and_or_right

/-! Declarations about `iff` -/

alias iff_congr ← Iff.iff

-- @[simp] -- FIXME simp ignores proof rewrites
theorem iff_mpr_iff_true_intro (h : P) : Iff.mpr (iff_true_intro h) True.intro = h := rfl

#align decidable.imp_or_distrib Decidable.imp_or

theorem imp_or {a b c : Prop} : a → b ∨ c ↔ (a → b) ∨ (a → c) := Decidable.imp_or
#align imp_or_distrib imp_or

#align decidable.imp_or_distrib' Decidable.imp_or'

theorem imp_or' : a → b ∨ c ↔ (a → b) ∨ (a → c) := Decidable.imp_or'
#align imp_or_distrib' imp_or'ₓ -- universes

theorem not_imp : ¬(a → b) ↔ a ∧ ¬b := Decidable.not_imp

theorem peirce (a b : Prop) : ((a → b) → a) → a := Decidable.peirce _ _

theorem not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b) := Decidable.not_iff_not

theorem not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a) := Decidable.not_iff_comm

theorem not_iff : ¬(a ↔ b) ↔ (¬a ↔ b) := Decidable.not_iff

theorem iff_not_comm : (a ↔ ¬b) ↔ (b ↔ ¬a) := Decidable.iff_not_comm

theorem iff_iff_and_or_not_and_not : (a ↔ b) ↔ a ∧ b ∨ ¬a ∧ ¬b :=
  Decidable.iff_iff_and_or_not_and_not

theorem iff_iff_not_or_and_or_not : (a ↔ b) ↔ (¬a ∨ b) ∧ (a ∨ ¬b) :=
  Decidable.iff_iff_not_or_and_or_not

theorem not_and_not_right : ¬(a ∧ ¬b) ↔ a → b := Decidable.not_and_not_right

#align decidable_of_iff decidable_of_iff
#align decidable_of_iff' decidable_of_iff'
#align decidable_of_bool decidable_of_bool

/-! ### De Morgan's laws -/

#align Decidable.not_and_distrib Decidable.not_and
#align Decidable.not_and_distrib' Decidable.not_and'

/-- One of de Morgan's laws: the negation of a conjunction is logically equivalent to the
disjunction of the negations. -/
theorem not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b := Decidable.not_and
#align not_and_distrib not_and_or

#align not_or_distrib not_or

theorem or_iff_not_and_not : a ∨ b ↔ ¬(¬a ∧ ¬b) := Decidable.or_iff_not_and_not

theorem and_iff_not_or_not : a ∧ b ↔ ¬(¬a ∨ ¬b) := Decidable.and_iff_not_or_not

@[simp] theorem not_xor (P Q : Prop) : ¬Xor' P Q ↔ (P ↔ Q) := by
  simp only [not_and, Xor', not_or, not_not, ← iff_iff_implies_and_implies, iff_self]

theorem xor_iff_not_iff (P Q : Prop) : Xor' P Q ↔ ¬(P ↔ Q) := by rw [iff_not_comm, not_xor]

end Propositional

/-! ### Declarations about equality -/

alias ne_of_mem_of_not_mem ← Membership.Mem.ne_of_not_mem
alias ne_of_mem_of_not_mem' ← Membership.Mem.ne_of_not_mem'

section Equality

-- todo: change name
theorem ball_cond_comm {α} {s : α → Prop} {p : α → α → Prop} :
    (∀ a, s a → ∀ b, s b → p a b) ↔ ∀ a b, s a → s b → p a b :=
  ⟨fun h a b ha hb => h a ha b hb, fun h a ha b hb => h a b ha hb⟩

theorem ball_mem_comm {α β} [Membership α β] {s : β} {p : α → α → Prop} :
    (∀ a (_ : a ∈ s) b (_ : b ∈ s), p a b) ↔ ∀ a b, a ∈ s → b ∈ s → p a b :=
  ball_cond_comm

theorem ne_of_apply_ne {α β : Sort _} (f : α → β) {x y : α} (h : f x ≠ f y) : x ≠ y :=
  fun w : x = y => h (congr_arg f w)

theorem eq_equivalence : Equivalence (@Eq α) :=
  ⟨Eq.refl, @Eq.symm _, @Eq.trans _⟩

@[simp] theorem eq_mp_eq_cast (h : α = β) : Eq.mp h = cast h := rfl

@[simp] theorem eq_mpr_eq_cast (h : α = β) : Eq.mpr h = cast h.symm := rfl

@[simp] theorem cast_cast : ∀ (ha : α = β) (hb : β = γ) (a : α),
    cast hb (cast ha a) = cast (ha.trans hb) a
  | rfl, rfl, _ => rfl

-- @[simp] -- FIXME simp ignores proof rewrites
theorem congr_refl_left (f : α → β) {a b : α} (h : a = b) :
    congr (Eq.refl f) h = congr_arg f h := rfl

-- @[simp] -- FIXME simp ignores proof rewrites
theorem congr_refl_right {f g : α → β} (h : f = g) (a : α) :
    congr h (Eq.refl a) = congr_fun h a := rfl

-- @[simp] -- FIXME simp ignores proof rewrites
theorem congr_arg_refl (f : α → β) (a : α) : congr_arg f (Eq.refl a) = Eq.refl (f a) := rfl

-- @[simp] -- FIXME simp ignores proof rewrites
theorem congr_fun_rfl (f : α → β) (a : α) : congr_fun (Eq.refl f) a = Eq.refl (f a) := rfl

-- @[simp] -- FIXME simp ignores proof rewrites
theorem congr_fun_congr_arg (f : α → β → γ) {a a' : α} (p : a = a') (b : β) :
    congr_fun (congr_arg f p) b = congr_arg (fun a => f a b) p := rfl

theorem heq_of_cast_eq : ∀ (e : α = β) (_ : cast e a = a'), HEq a a'
  | rfl, h => Eq.recOn h (HEq.refl _)

theorem cast_eq_iff_heq : cast e a = a' ↔ HEq a a' :=
  ⟨heq_of_cast_eq _, fun h => by cases h <;> rfl⟩

theorem rec_heq_of_heq {C : α → Sort _} {x : C a} {y : β} (e : a = b) (h : HEq x y) :
    HEq (@Eq.ndrec α a C x b e) y := by subst e <;> exact h

protected theorem Eq.congr (h₁ : x₁ = y₁) (h₂ : x₂ = y₂) : x₁ = x₂ ↔ y₁ = y₂ := by
  subst h₁; subst h₂; rfl

theorem Eq.congr_left {x y z : α} (h : x = y) : x = z ↔ y = z := by rw [h]

theorem Eq.congr_right {x y z : α} (h : x = y) : z = x ↔ z = y := by rw [h]

alias congrArg₂ ← congr_arg₂
#align congr_arg2 congr_arg₂

variable {β : α → Sort _} {γ : ∀ a, β a → Sort _} {δ : ∀ a b, γ a b → Sort _}

theorem congr_fun₂ {f g : ∀ a b, γ a b} (h : f = g) (a : α) (b : β a) : f a b = g a b :=
  congr_fun (congr_fun h _) _

theorem congr_fun₃ {f g : ∀ a b c, δ a b c} (h : f = g) (a : α) (b : β a) (c : γ a b) :
    f a b c = g a b c :=
  congr_fun₂ (congr_fun h _) _ _

theorem funext₂ {f g : ∀ a b, γ a b} (h : ∀ a b, f a b = g a b) : f = g :=
  funext fun _ => funext <| h _

theorem funext₃ {f g : ∀ a b c, δ a b c} (h : ∀ a b c, f a b c = g a b c) : f = g :=
  funext fun _ => funext₂ <| h _

end Equality

/-! ### Declarations about quantifiers -/


section Quantifiers
section Dependent

variable {β : α → Sort _} {γ : ∀ a, β a → Sort _} {δ : ∀ a b, γ a b → Sort _}
  {ε : ∀ a b c, δ a b c → Sort _}

theorem pi_congr {β' : α → Sort _} (h : ∀ a, β a = β' a) : (∀ a, β a) = ∀ a, β' a :=
  (funext h : β = β') ▸ rfl

-- Porting note: some higher order lemmas such as `forall₂_congr` and `exists₂_congr`
-- were moved to `Std4`

theorem forall₂_imp {p q : ∀ a, β a → Prop} (h : ∀ a b, p a b → q a b) :
    (∀ a b, p a b) → ∀ a b, q a b :=
  forall_imp fun i => forall_imp <| h i

theorem forall₃_imp {p q : ∀ a b, γ a b → Prop} (h : ∀ a b c, p a b c → q a b c) :
    (∀ a b c, p a b c) → ∀ a b c, q a b c :=
  forall_imp fun a => forall₂_imp <| h a

theorem Exists₂.imp {p q : ∀ a, β a → Prop} (h : ∀ a b, p a b → q a b) :
    (∃ a b, p a b) → ∃ a b, q a b :=
  Exists.imp fun a => Exists.imp <| h a

theorem Exists₃.imp {p q : ∀ a b, γ a b → Prop} (h : ∀ a b c, p a b c → q a b c) :
    (∃ a b c, p a b c) → ∃ a b c, q a b c :=
  Exists.imp fun a => Exists₂.imp <| h a

end Dependent

variable {κ : ι → Sort _} {p q : α → Prop}

#align exists_imp_exists' Exists.imp'

theorem forall_swap {p : α → β → Prop} : (∀ x y, p x y) ↔ ∀ y x, p x y := ⟨swap, swap⟩

theorem forall₂_swap {κ₁ : ι₁ → Sort _} {κ₂ : ι₂ → Sort _} {p : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Prop} :
    (∀ i₁ j₁ i₂ j₂, p i₁ j₁ i₂ j₂) ↔ ∀ i₂ j₂ i₁ j₁, p i₁ j₁ i₂ j₂ := ⟨swap₂, swap₂⟩

/-- We intentionally restrict the type of `α` in this lemma so that this is a safer to use in simp
than `forall_swap`. -/
theorem imp_forall_iff {α : Type _} {p : Prop} {q : α → Prop} : (p → ∀ x, q x) ↔ ∀ x, p → q x :=
  forall_swap

theorem exists_swap {p : α → β → Prop} : (∃ x y, p x y) ↔ ∃ y x, p x y :=
  ⟨fun ⟨x, y, h⟩ => ⟨y, x, h⟩, fun ⟨y, x, h⟩ => ⟨x, y, h⟩⟩

@[simp] theorem forall_exists_index {q : (∃ x, p x) → Prop} :
    (∀ h, q h) ↔ ∀ x (h : p x), q ⟨x, h⟩ :=
  ⟨fun h x hpx => h ⟨x, hpx⟩, fun h ⟨x, hpx⟩ => h x hpx⟩

#align exists_imp_distrib exists_imp
alias exists_imp ↔ _ not_exists_of_forall_not

#align Exists.some Exists.choose
#align Exists.some_spec Exists.choose_spec

-- See Note [decidable namespace]
protected theorem Decidable.not_forall {p : α → Prop} [Decidable (∃ x, ¬p x)]
    [∀ x, Decidable (p x)] : (¬∀ x, p x) ↔ ∃ x, ¬p x :=
  ⟨Not.decidable_imp_symm fun nx x => nx.decidable_imp_symm fun h => ⟨x, h⟩,
   not_forall_of_exists_not⟩

@[simp]
theorem not_forall {p : α → Prop} : (¬∀ x, p x) ↔ ∃ x, ¬p x :=
  Decidable.not_forall

-- See Note [decidable namespace]
protected theorem Decidable.not_forall_not [Decidable (∃ x, p x)] : (¬∀ x, ¬p x) ↔ ∃ x, p x :=
  (@Decidable.not_iff_comm _ _ _ (decidable_of_iff (¬∃ x, p x) not_exists)).1 not_exists

theorem not_forall_not : (¬∀ x, ¬p x) ↔ ∃ x, p x := Decidable.not_forall_not

-- See Note [decidable namespace]
protected theorem Decidable.not_exists_not [∀ x, Decidable (p x)] : (¬∃ x, ¬p x) ↔ ∀ x, p x := by
  simp only [not_exists, Decidable.not_not, iff_self]

theorem not_exists_not : (¬∃ x, ¬p x) ↔ ∀ x, p x := Decidable.not_exists_not

theorem forall_imp_iff_exists_imp [ha : Nonempty α] : (∀ x, p x) → b ↔ ∃ x, p x → b := by
  let ⟨a⟩ := ha
  refine ⟨fun h => not_forall_not.1 fun h' => ?_, fun ⟨x, hx⟩ h => hx (h x)⟩
  exact if hb : b then h' a fun _ => hb else hb <| h fun x => (not_imp.1 (h' x)).1

theorem forall_true_iff : (α → True) ↔ True := imp_true_iff _

-- Unfortunately this causes simp to loop sometimes, so we
-- add the 2 and 3 cases as simp lemmas instead
theorem forall_true_iff' (h : ∀ a, p a ↔ True) : (∀ a, p a) ↔ True :=
  iff_true_intro fun _ => of_iff_true (h _)

-- This is not marked `@[simp]` because `implies_true : (α → True) = True` works
theorem forall₂_true_iff {β : α → Sort _} : (∀ a, β a → True) ↔ True := by simp
#align forall_2_true_iff forall₂_true_iff

-- This is not marked `@[simp]` because `implies_true : (α → True) = True` works
theorem forall₃_true_iff {β : α → Sort _} {γ : ∀ a, β a → Sort _} :
    (∀ (a) (b : β a), γ a b → True) ↔ True := by simp
#align forall_3_true_iff forall₃_true_iff

@[simp] theorem exists_unique_iff_exists [Subsingleton α] {p : α → Prop} :
    (∃! x, p x) ↔ ∃ x, p x :=
  ⟨fun h => h.exists, Exists.imp fun x hx => ⟨hx, fun y _ => Subsingleton.elim y x⟩⟩

-- forall_forall_const is no longer needed

@[simp] theorem exists_const (α) [i : Nonempty α] : (∃ _ : α, b) ↔ b :=
  ⟨fun ⟨_, h⟩ => h, i.elim Exists.intro⟩

theorem exists_unique_const (α) [i : Nonempty α] [Subsingleton α] :
    (∃! _ : α, b) ↔ b := by simp

#align forall_and_distrib forall_and
#align exists_or_distrib exists_or

#align exists_and_distrib_left exists_and_left
#align exists_and_distrib_right exists_and_right

theorem and_forall_ne (a : α) : (p a ∧ ∀ (b) (_ : b ≠ a), p b) ↔ ∀ b, p b := by
  simp only [← @forall_eq _ p a, ← forall_and, ← or_imp, Classical.em, forall_const, iff_self]

theorem Ne.ne_or_ne {x y : α} (z : α) (h : x ≠ y) : x ≠ z ∨ y ≠ z :=
  not_and_or.1 <| mt (and_imp.2 Eq.substr) h.symm

@[simp] theorem exists_unique_eq {a' : α} : ∃! a, a = a' := by
  simp only [eq_comm, ExistsUnique, and_self, forall_eq', exists_eq']

@[simp] theorem exists_unique_eq' {a' : α} : ∃! a, a' = a := by
  simp only [ExistsUnique, and_self, forall_eq', exists_eq']

-- @[simp] -- FIXME simp does not apply this lemma for some reason
theorem exists_apply_eq_apply' (f : α → β) (a' : α) : ∃ a, f a' = f a := ⟨a', rfl⟩

@[simp] theorem exists_exists_and_eq_and {f : α → β} {p : α → Prop} {q : β → Prop} :
    (∃ b, (∃ a, p a ∧ f a = b) ∧ q b) ↔ ∃ a, p a ∧ q (f a) :=
  ⟨fun ⟨_, ⟨a, ha, hab⟩, hb⟩ => ⟨a, ha, hab.symm ▸ hb⟩, fun ⟨a, hp, hq⟩ => ⟨f a, ⟨a, hp, rfl⟩, hq⟩⟩

@[simp] theorem exists_exists_eq_and {f : α → β} {p : β → Prop} :
    (∃ b, (∃ a, f a = b) ∧ p b) ↔ ∃ a, p (f a) :=
  ⟨fun ⟨_, ⟨a, ha⟩, hb⟩ => ⟨a, ha.symm ▸ hb⟩, fun ⟨a, ha⟩ => ⟨f a, ⟨a, rfl⟩, ha⟩⟩

@[simp] theorem exists_or_eq_left (y : α) (p : α → Prop) : ∃ x : α, x = y ∨ p x := ⟨y, .inl rfl⟩

@[simp] theorem exists_or_eq_right (y : α) (p : α → Prop) : ∃ x : α, p x ∨ x = y := ⟨y, .inr rfl⟩

@[simp] theorem exists_or_eq_left' (y : α) (p : α → Prop) : ∃ x : α, y = x ∨ p x := ⟨y, .inl rfl⟩

@[simp] theorem exists_or_eq_right' (y : α) (p : α → Prop) : ∃ x : α, p x ∨ y = x := ⟨y, .inr rfl⟩

theorem forall_apply_eq_imp_iff {f : α → β} {p : β → Prop} :
    (∀ a b, f a = b → p b) ↔ ∀ a, p (f a) := by simp

@[simp] theorem forall_apply_eq_imp_iff' {f : α → β} {p : β → Prop} :
    (∀ b a, f a = b → p b) ↔ ∀ a, p (f a) := by simp [forall_swap]

theorem forall_eq_apply_imp_iff {f : α → β} {p : β → Prop} :
    (∀ a b, b = f a → p b) ↔ ∀ a, p (f a) := by simp

@[simp] theorem forall_eq_apply_imp_iff' {f : α → β} {p : β → Prop} :
    (∀ b a, b = f a → p b) ↔ ∀ a, p (f a) := by simp [forall_swap]

@[simp] theorem forall_apply_eq_imp_iff₂ {f : α → β} {p : α → Prop} {q : β → Prop} :
    (∀ b a, p a → f a = b → q b) ↔ ∀ a, p a → q (f a) :=
  ⟨fun h a ha => h (f a) a ha rfl, fun h _ a ha hb => hb ▸ h a ha⟩

@[simp] theorem exists_eq_right' {a' : α} : (∃ a, p a ∧ a' = a) ↔ p a' := by simp [@eq_comm _ a']

theorem exists_comm {p : α → β → Prop} : (∃ a b, p a b) ↔ ∃ b a, p a b :=
  ⟨fun ⟨a, b, h⟩ => ⟨b, a, h⟩, fun ⟨b, a, h⟩ => ⟨a, b, h⟩⟩

theorem exists₂_comm {κ₁ : ι₁ → Sort _} {κ₂ : ι₂ → Sort _} {p : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Prop} :
    (∃ i₁ j₁ i₂ j₂, p i₁ j₁ i₂ j₂) ↔ ∃ i₂ j₂ i₁ j₁, p i₁ j₁ i₂ j₂ := by
  simp only [@exists_comm (κ₁ _), @exists_comm ι₁, iff_self]

theorem And.exists {p q : Prop} {f : p ∧ q → Prop} : (∃ h, f h) ↔ ∃ hp hq, f ⟨hp, hq⟩ :=
  ⟨fun ⟨h, H⟩ => ⟨h.1, h.2, H⟩, fun ⟨hp, hq, H⟩ => ⟨⟨hp, hq⟩, H⟩⟩

theorem forall_or_of_or_forall (h : b ∨ ∀ x, p x) (x) : b ∨ p x := h.imp_right fun h₂ => h₂ x

-- See Note [decidable namespace]
protected theorem Decidable.forall_or_left {q : Prop} {p : α → Prop} [Decidable q] :
    (∀ x, q ∨ p x) ↔ q ∨ ∀ x, p x :=
  ⟨fun h => if hq : q then Or.inl hq else
    Or.inr fun x => (h x).resolve_left hq, forall_or_of_or_forall⟩
#align decidable.forall_or_distrib_left Decidable.forall_or_left

theorem forall_or_left {q} {p : α → Prop} : (∀ x, q ∨ p x) ↔ q ∨ ∀ x, p x :=
  Decidable.forall_or_left
#align forall_or_distrib_left forall_or_left

-- See Note [decidable namespace]
protected theorem Decidable.forall_or_distrib_right {q} {p : α → Prop} [Decidable q] :
    (∀ x, p x ∨ q) ↔ (∀ x, p x) ∨ q := by simp [or_comm, Decidable.forall_or_left]
#align decidable.forall_or_distrib_right Decidable.forall_or_right

theorem forall_or_distrib_right {q} {p : α → Prop} : (∀ x, p x ∨ q) ↔ (∀ x, p x) ∨ q :=
  Decidable.forall_or_distrib_right
#align forall_or_distrib_right forall_or_right

theorem exists_unique_prop {p q : Prop} : (∃! _ : p, q) ↔ p ∧ q := by simp

@[simp] theorem exists_unique_false : ¬∃! _ : α, False := fun ⟨_, h, _⟩ => h

theorem Exists.fst {b : Prop} {p : b → Prop} : Exists p → b
  | ⟨h, _⟩ => h

theorem Exists.snd {b : Prop} {p : b → Prop} : ∀ h : Exists p, p h.fst
  | ⟨_, h⟩ => h

theorem exists_prop_of_true {p : Prop} {q : p → Prop} (h : p) : (∃ h' : p, q h') ↔ q h :=
  @exists_const (q h) p ⟨h⟩

theorem exists_iff_of_forall {p : Prop} {q : p → Prop} (h : ∀ h, q h) : (∃ h, q h) ↔ p :=
  ⟨Exists.fst, fun H => ⟨H, h H⟩⟩

theorem exists_unique_prop_of_true {p : Prop} {q : p → Prop} (h : p) : (∃! h' : p, q h') ↔ q h :=
  @exists_unique_const (q h) p ⟨h⟩ _

theorem forall_prop_of_false {p : Prop} {q : p → Prop} (hn : ¬p) : (∀ h' : p, q h') ↔ True :=
  iff_true_intro fun h => hn.elim h

theorem exists_prop_of_false {p : Prop} {q : p → Prop} : ¬p → ¬∃ h' : p, q h' :=
  mt Exists.fst

-- Porting note: `[congr]` now only expects equalities
-- @[congr]
theorem exists_prop_congr {p p' : Prop} {q q' : p → Prop} (hq : ∀ h, q h ↔ q' h) (hp : p ↔ p') :
    Exists q ↔ ∃ h : p', q' (hp.2 h) :=
  ⟨fun ⟨_, _⟩ => ⟨hp.1 ‹_›, (hq _).1 ‹_›⟩, fun ⟨_, _⟩ => ⟨_, (hq _).2 ‹_›⟩⟩

@[congr]
theorem exists_prop_congr' {p p' : Prop} {q q' : p → Prop} (hq : ∀ h, q h ↔ q' h) (hp : p ↔ p') :
    Exists q = ∃ h : p', q' (hp.2 h) :=
  propext (exists_prop_congr hq hp)

/-- See `is_empty.exists_iff` for the `false` version. -/
@[simp] theorem exists_true_left (p : True → Prop) : (∃ x, p x) ↔ p True.intro :=
  exists_prop_of_true _

-- Porting note: `@[congr]` commented out for now.
-- @[congr]
theorem forall_prop_congr {p p' : Prop} {q q' : p → Prop} (hq : ∀ h, q h ↔ q' h) (hp : p ↔ p') :
    (∀ h, q h) ↔ ∀ h : p', q' (hp.2 h) :=
  ⟨fun h1 h2 => (hq _).1 (h1 (hp.2 h2)), fun h1 h2 => (hq _).2 (h1 (hp.1 h2))⟩

-- Porting note: `@[congr]` commented out for now.
-- @[congr]
theorem forall_prop_congr' {p p' : Prop} {q q' : p → Prop} (hq : ∀ h, q h ↔ q' h) (hp : p ↔ p') :
    (∀ h, q h) = ∀ h : p', q' (hp.2 h) :=
  propext (forall_prop_congr hq hp)

/-- See `is_empty.forall_iff` for the `false` version. -/
@[simp] theorem forall_true_left (p : True → Prop) : (∀ x, p x) ↔ p True.intro :=
  forall_prop_of_true _

theorem ExistsUnique.elim₂ {α : Sort _} {p : α → Sort _} [∀ x, Subsingleton (p x)]
    {q : ∀ (x) (_ : p x), Prop} {b : Prop} (h₂ : ∃! (x : _) (h : p x), q x h)
    (h₁ : ∀ (x) (h : p x), q x h → (∀ (y) (hy : p y), q y hy → y = x) → b) : b := by
  simp only [exists_unique_iff_exists] at h₂
  apply h₂.elim
  exact fun x ⟨hxp, hxq⟩ H => h₁ x hxp hxq fun y hyp hyq => H y ⟨hyp, hyq⟩
#align exists_unique.elim2 ExistsUnique.elim₂

theorem ExistsUnique.intro2 {α : Sort _} {p : α → Sort _} [∀ x, Subsingleton (p x)]
    {q : ∀ (x : α) (_ : p x), Prop} (w : α) (hp : p w) (hq : q w hp)
    (H : ∀ (y) (hy : p y), q y hy → y = w) : ∃! (x : _) (hx : p x), q x hx := by
  simp only [exists_unique_iff_exists]
  exact ExistsUnique.intro w ⟨hp, hq⟩ fun y ⟨hyp, hyq⟩ => H y hyp hyq
#align exists_unique.intro2 ExistsUnique.intro₂

theorem ExistsUnique.exists₂ {α : Sort _} {p : α → Sort _} {q : ∀ (x : α) (_ : p x), Prop}
    (h : ∃! (x : _) (hx : p x), q x hx) : ∃ (x : _) (hx : p x), q x hx :=
  h.exists.imp fun _ hx => hx.exists
#align exists_unique.exists2 ExistsUnique.exists₂

theorem ExistsUnique.unique2 {α : Sort _} {p : α → Sort _} [∀ x, Subsingleton (p x)]
    {q : ∀ (x : α) (_ : p x), Prop} (h : ∃! (x : _) (hx : p x), q x hx) {y₁ y₂ : α}
    (hpy₁ : p y₁) (hqy₁ : q y₁ hpy₁) (hpy₂ : p y₂) (hqy₂ : q y₂ hpy₂) : y₁ = y₂ := by
  simp only [exists_unique_iff_exists] at h
  exact h.unique ⟨hpy₁, hqy₁⟩ ⟨hpy₂, hqy₂⟩
#align exists_unique.unique2 ExistsUnique.unique₂

end Quantifiers

/-! ### Classical lemmas -/

namespace Classical
variable {p : α → Prop}

-- use shortened names to avoid conflict when classical namespace is open.
/-- Any prop `p` is decidable classically. A shorthand for `classical.prop_decidable`. -/
noncomputable def dec (p : Prop) : Decidable p := by infer_instance

/-- Any predicate `p` is decidable classically. -/
noncomputable def decPred (p : α → Prop) : DecidablePred p := by infer_instance

/-- Any relation `p` is decidable classically. -/
noncomputable def decRel (p : α → α → Prop) : DecidableRel p := by infer_instance

/-- Any type `α` has decidable equality classically. -/
noncomputable def decEq (α : Sort _) : DecidableEq α := by infer_instance

/-- Construct a function from a default value `H0`, and a function to use if there exists a value
satisfying the predicate. -/
-- @[elab_as_elim] -- FIXME
noncomputable def existsCases (H0 : C) (H : ∀ a, p a → C) : C :=
  if h : ∃ a, p a then H (Classical.choose h) (Classical.choose_spec h) else H0

theorem some_spec₂ {α : Sort _} {p : α → Prop} {h : ∃ a, p a} (q : α → Prop)
    (hpq : ∀ a, p a → q a) : q (choose h) := hpq _ <| choose_spec _
#align classical.some_spec2 Classical.some_spec₂

/-- A version of `Classical.indefiniteDescription` which is definitionally equal to a pair -/
noncomputable def subtype_of_exists {α : Type _} {P : α → Prop} (h : ∃ x, P x) : { x // P x } :=
  ⟨Classical.choose h, Classical.choose_spec h⟩
#align classical.subtype_of_exists Classical.subtype_of_exists

/-- A version of `byContradiction` that uses types instead of propositions. -/
protected noncomputable def byContradiction' {α : Sort _} (H : ¬(α → False)) : α :=
  Classical.choice <| (peirce _ False) fun h => (H fun a => h ⟨a⟩).elim

/-- `classical.byContradiction'` is equivalent to lean's axiom `classical.choice`. -/
def choice_of_byContradiction' {α : Sort _} (contra : ¬(α → False) → α) : Nonempty α → α :=
  fun H => contra H.elim
#align classical.choice_of_by_contradiction' choice_of_byContradiction'

end Classical

/-- This function has the same type as `Exists.recOn`, and can be used to case on an equality,
but `Exists.recOn` can only eliminate into Prop, while this version eliminates into any universe
using the axiom of choice. -/
-- @[elab_as_elim] -- FIXME
noncomputable def Exists.classicalRecOn {p : α → Prop} (h : ∃ a, p a) {C} (H : ∀ a, p a → C) : C :=
  H (Classical.choose h) (Classical.choose_spec h)

/-! ### Declarations about bounded quantifiers -/

section BoundedQuantifiers
variable {r p q : α → Prop} {P Q : ∀ x, p x → Prop} {b : Prop}

theorem bex_def : (∃ (x : _) (_ : p x), q x) ↔ ∃ x, p x ∧ q x :=
  ⟨fun ⟨x, px, qx⟩ => ⟨x, px, qx⟩, fun ⟨x, px, qx⟩ => ⟨x, px, qx⟩⟩

theorem BEx.elim {b : Prop} : (∃ x h, P x h) → (∀ a h, P a h → b) → b
  | ⟨a, h₁, h₂⟩, h' => h' a h₁ h₂
#align bex.elim BEx.elim

theorem BEx.intro (a : α) (h₁ : p a) (h₂ : P a h₁) : ∃ (x : _) (h : p x), P x h :=
  ⟨a, h₁, h₂⟩
#align bex.intro BEx.intro

theorem ball_congr (H : ∀ x h, P x h ↔ Q x h) : (∀ x h, P x h) ↔ ∀ x h, Q x h :=
  forall_congr' fun x => forall_congr' (H x)

theorem bex_congr (H : ∀ x h, P x h ↔ Q x h) : (∃ x h, P x h) ↔ ∃ x h, Q x h :=
  exists_congr fun x => exists_congr (H x)

theorem bex_eq_left {a : α} : (∃ (x : _) (_ : x = a), p x) ↔ p a := by
  simp only [exists_prop, exists_eq_left]; rfl

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

theorem forall_of_ball (H : ∀ x, p x) (h : ∀ x, p x → q x) (x) : q x := h x <| H x

theorem bex_of_exists (H : ∀ x, p x) : (∃ x, q x) → ∃ (x : _) (_ : p x), q x
  | ⟨x, hq⟩ => ⟨x, H x, hq⟩

theorem exists_of_bex : (∃ (x : _) (_ : p x), q x) → ∃ x, q x
  | ⟨x, _, hq⟩ => ⟨x, hq⟩

theorem bex_imp : (∃ x h, P x h) → b ↔ ∀ x h, P x h → b := by simp
#align bex_imp_distrib bex_imp

theorem not_bex : (¬∃ x h, P x h) ↔ ∀ x h, ¬P x h := bex_imp

theorem not_ball_of_bex_not : (∃ x h, ¬P x h) → ¬∀ x h, P x h
  | ⟨x, h, hp⟩, al => hp <| al x h

-- See Note [decidable namespace]
protected theorem Decidable.not_ball [Decidable (∃ x h, ¬P x h)] [∀ x h, Decidable (P x h)] :
    (¬∀ x h, P x h) ↔ ∃ x h, ¬P x h :=
  ⟨Not.decidable_imp_symm fun nx x h => nx.decidable_imp_symm
    fun h' => ⟨x, h, h'⟩, not_ball_of_bex_not⟩

theorem not_ball : (¬∀ x h, P x h) ↔ ∃ x h, ¬P x h := Decidable.not_ball

theorem ball_true_iff (p : α → Prop) : (∀ x, p x → True) ↔ True :=
  iff_true_intro fun _ _ => trivial

theorem ball_and_distrib : (∀ x h, P x h ∧ Q x h) ↔ (∀ x h, P x h) ∧ ∀ x h, Q x h :=
  Iff.trans (forall_congr' fun _ => forall_and) forall_and
#align ball_and_distrib ball_and

theorem bex_or : (∃ x h, P x h ∨ Q x h) ↔ (∃ x h, P x h) ∨ ∃ x h, Q x h :=
  Iff.trans (exists_congr fun _ => exists_or) exists_or
#align bex_or_distrib bex_or

theorem ball_or_left : (∀ x, p x ∨ q x → r x) ↔ (∀ x, p x → r x) ∧ ∀ x, q x → r x :=
  Iff.trans (forall_congr' fun _ => or_imp) forall_and
#align ball_or_left_distrib ball_or_left

theorem bex_or_left :
    (∃ (x : _) (_ : p x ∨ q x), r x) ↔ (∃ (x : _) (_ : p x), r x) ∨ ∃ (x : _) (_ : q x), r x := by
  simp only [exists_prop]
  exact Iff.trans (exists_congr fun x => or_and_right) exists_or
#align bex_or_left_distrib bex_or_left

end BoundedQuantifiers

#align classical.not_ball not_ball

section ite

variable {σ : α → Sort _} (f : α → β) {P Q : Prop} [Decidable P] [Decidable Q]
  {a b c : α} {A : P → α} {B : ¬P → α}

theorem dite_eq_iff : dite P A B = c ↔ (∃ h, A h = c) ∨ ∃ h, B h = c := by
  by_cases P <;> simp [*, exists_prop_of_true, exists_prop_of_false]

theorem ite_eq_iff : ite P a b = c ↔ P ∧ a = c ∨ ¬P ∧ b = c :=
  dite_eq_iff.trans <| by simp only; rw [exists_prop, exists_prop]

theorem dite_eq_iff' : dite P A B = c ↔ (∀ h, A h = c) ∧ ∀ h, B h = c :=
  ⟨fun he => ⟨fun h => (dif_pos h).symm.trans he, fun h => (dif_neg h).symm.trans he⟩, fun he =>
    (em P).elim (fun h => (dif_pos h).trans <| he.1 h) fun h => (dif_neg h).trans <| he.2 h⟩

theorem ite_eq_iff' : ite P a b = c ↔ (P → a = c) ∧ (¬P → b = c) := dite_eq_iff'

@[simp] theorem dite_eq_left_iff : dite P (fun _ => a) B = a ↔ ∀ h, B h = a := by
  by_cases P <;> simp [*, forall_prop_of_true, forall_prop_of_false]

@[simp] theorem dite_eq_right_iff : (dite P A fun _ => b) = b ↔ ∀ h, A h = b := by
  by_cases P <;> simp [*, forall_prop_of_true, forall_prop_of_false]

@[simp] theorem ite_eq_left_iff : ite P a b = a ↔ ¬P → b = a := dite_eq_left_iff
@[simp] theorem ite_eq_right_iff : ite P a b = b ↔ P → a = b := dite_eq_right_iff

theorem dite_ne_left_iff : dite P (fun _ => a) B ≠ a ↔ ∃ h, a ≠ B h := by
  rw [Ne.def, dite_eq_left_iff, not_forall]
  exact exists_congr fun h => by rw [ne_comm]

theorem dite_ne_right_iff : (dite P A fun _ => b) ≠ b ↔ ∃ h, A h ≠ b := by
  simp only [Ne.def, dite_eq_right_iff, not_forall]; rfl

theorem ite_ne_left_iff : ite P a b ≠ a ↔ ¬P ∧ a ≠ b :=
  dite_ne_left_iff.trans <| by simp only; rw [exists_prop]

theorem ite_ne_right_iff : ite P a b ≠ b ↔ P ∧ a ≠ b :=
  dite_ne_right_iff.trans <| by simp only; rw [exists_prop]

protected theorem Ne.dite_eq_left_iff (h : ∀ h, a ≠ B h) : dite P (fun _ => a) B = a ↔ P :=
  dite_eq_left_iff.trans ⟨fun H => of_not_not fun h' => h h' (H h').symm, fun h H => (H h).elim⟩

protected theorem Ne.dite_eq_right_iff (h : ∀ h, A h ≠ b) : (dite P A fun _ => b) = b ↔ ¬P :=
  dite_eq_right_iff.trans ⟨fun H h' => h h' (H h'), fun h' H => (h' H).elim⟩

protected theorem Ne.ite_eq_left_iff (h : a ≠ b) : ite P a b = a ↔ P :=
  Ne.dite_eq_left_iff fun _ => h

protected theorem Ne.ite_eq_right_iff (h : a ≠ b) : ite P a b = b ↔ ¬P :=
  Ne.dite_eq_right_iff fun _ => h

protected theorem Ne.dite_ne_left_iff (h : ∀ h, a ≠ B h) : dite P (fun _ => a) B ≠ a ↔ ¬P :=
  dite_ne_left_iff.trans <| exists_iff_of_forall h

protected theorem Ne.dite_ne_right_iff (h : ∀ h, A h ≠ b) : (dite P A fun _ => b) ≠ b ↔ P :=
  dite_ne_right_iff.trans <| exists_iff_of_forall h

protected theorem Ne.ite_ne_left_iff (h : a ≠ b) : ite P a b ≠ a ↔ ¬P :=
  Ne.dite_ne_left_iff fun _ => h

protected theorem Ne.ite_ne_right_iff (h : a ≠ b) : ite P a b ≠ b ↔ P :=
  Ne.dite_ne_right_iff fun _ => h

variable (P Q a b)

/-- A `dite` whose results do not actually depend on the condition may be reduced to an `ite`. -/
@[simp] theorem dite_eq_ite : (dite P (fun _ => a) fun _ => b) = ite P a b := rfl

theorem dite_eq_or_eq : (∃ h, dite P A B = A h) ∨ ∃ h, dite P A B = B h :=
  if h : _ then .inl ⟨h, dif_pos h⟩ else .inr ⟨h, dif_neg h⟩

theorem ite_eq_or_eq : ite P a b = a ∨ ite P a b = b :=
  if h : _ then .inl (if_pos h) else .inr (if_neg h)

/-- A two-argument function applied to two `dite`s is a `dite` of that two-argument function
applied to each of the branches. -/
theorem apply_dite₂ (f : α → β → γ) (P : Prop) [Decidable P] (a : P → α) (b : ¬P → α)
    (c : P → β) (d : ¬P → β) :
    f (dite P a b) (dite P c d) = dite P (fun h => f (a h) (c h)) fun h => f (b h) (d h) := by
  by_cases h : P <;> simp [h]
#align apply_dite2 apply_dite₂

/-- A two-argument function applied to two `ite`s is a `ite` of that two-argument function
applied to each of the branches. -/
theorem apply_ite₂ (f : α → β → γ) (P : Prop) [Decidable P] (a b : α) (c d : β) :
    f (ite P a b) (ite P c d) = ite P (f a c) (f b d) :=
  apply_dite₂ f P (fun _ => a) (fun _ => b) (fun _ => c) fun _ => d
#align apply_ite2 apply_ite₂

/-- A 'dite' producing a `Pi` type `Π a, σ a`, applied to a value `a : α` is a `dite` that applies
either branch to `a`. -/
theorem dite_apply (f : P → ∀ a, σ a) (g : ¬P → ∀ a, σ a) (a : α) :
    (dite P f g) a = dite P (fun h => f h a) fun h => g h a := by by_cases h:P <;> simp [h]

/-- A 'ite' producing a `Pi` type `Π a, σ a`, applied to a value `a : α` is a `ite` that applies
either branch to `a`. -/
theorem ite_apply (f g : ∀ a, σ a) (a : α) : (ite P f g) a = ite P (f a) (g a) :=
  dite_apply P (fun _ => f) (fun _ => g) a

theorem ite_and : ite (P ∧ Q) a b = ite P (ite Q a b) b := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

theorem dite_dite_comm {B : Q → α} {C : ¬P → ¬Q → α} (h : P → ¬Q) :
    (if p : P then A p else if q : Q then B q else C p q) =
     if q : Q then B q else if p : P then A p else C p q :=
  dite_eq_iff'.2 ⟨
    fun p => by rw [dif_neg (h p), dif_pos p],
    fun np => by congr; funext _; rw [dif_neg np]⟩

theorem ite_ite_comm (h : P → ¬Q) :
    (if P then a else if Q then b else c) =
     if Q then b else if P then a else c :=
  dite_dite_comm P Q h

end ite
