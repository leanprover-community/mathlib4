/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Logic.IsEmpty
import Mathlib.Init.Logic
import Mathlib.Init.Data.Fin.Basic
import Mathlib.Tactic.Inhabit

/-!
# Types with a unique term

In this file we define a typeclass `Unique`,
which expresses that a type has a unique term.
In other words, a type that is `Inhabited` and a `Subsingleton`.

## Main declaration

* `Unique`: a typeclass that expresses that a type has a unique term.

## Main statements

* `Unique.mk'`: an inhabited subsingleton type is `Unique`. This can not be an instance because it
  would lead to loops in typeclass inference.

* `Function.Surjective.unique`: if the domain of a surjective function is `Unique`, then its
  codomain is `unique` as well.

* `Function.Injective.subsingleton`: if the codomain of an injective function is `Subsingleton`,
  then its domain is `Subsingleton` as well.

* `Function.Injective.unique`: if the codomain of an injective function is `Subsingleton` and its
  domain is `Inhabited`, then its domain is `Unique`.

## Implementation details

The typeclass `Unique α` is implemented as a type,
rather than a `Prop`-valued predicate,
for good definitional properties of the default term.

-/


universe u v w

/-- `Unique α` expresses that `α` is a type with a unique term `default`.

This is implemented as a type, rather than a `Prop`-valued predicate,
for good definitional properties of the default term. -/
@[ext]
structure Unique (α : Sort u) extends Inhabited α where
  /-- In a `Unique` type, every term is equal to the default element (from `Inhabited`). -/
  uniq : ∀ a : α, a = default

attribute [class] Unique
-- The simplifier can already prove this using `eq_iff_true_of_subsingleton`
attribute [nolint simpNF] Unique.mk.injEq

theorem unique_iff_exists_unique (α : Sort u) : Nonempty (Unique α) ↔ ∃! _ : α, True :=
  ⟨fun ⟨u⟩ => ⟨u.default, trivial, fun a _ => u.uniq a⟩,
   fun ⟨a, _, h⟩ => ⟨⟨⟨a⟩, fun _ => h _ trivial⟩⟩⟩

theorem unique_subtype_iff_exists_unique {α} (p : α → Prop) :
    Nonempty (Unique (Subtype p)) ↔ ∃! a, p a :=
  ⟨fun ⟨u⟩ => ⟨u.default.1, u.default.2, fun a h => congr_arg Subtype.val (u.uniq ⟨a, h⟩)⟩,
   fun ⟨a, ha, he⟩ => ⟨⟨⟨⟨a, ha⟩⟩, fun ⟨b, hb⟩ => by
      congr
      exact he b hb⟩⟩⟩

/-- Given an explicit `a : α` with `Subsingleton α`, we can construct
a `Unique α` instance. This is a def because the typeclass search cannot
arbitrarily invent the `a : α` term. Nevertheless, these instances are all
equivalent by `Unique.Subsingleton.unique`.

See note [reducible non-instances]. -/
@[reducible]
def uniqueOfSubsingleton {α : Sort _} [Subsingleton α] (a : α) : Unique α where
  default := a
  uniq _ := Subsingleton.elim _ _

instance PUnit.unique : Unique PUnit.{u} where
  default := PUnit.unit
  uniq x := subsingleton x _

-- Porting note:
-- This should not require a nolint,
-- but it is currently failing due to a problem in the linter discussed at
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/.60simpNF.60.20error.20.22unknown.20metavariable.22
@[simp, nolint simpNF]
theorem PUnit.default_eq_unit : (default : PUnit) = PUnit.unit :=
  rfl

#align punit.default_eq_star PUnit.default_eq_unit

/-- Every provable proposition is unique, as all proofs are equal. -/
def uniqueProp {p : Prop} (h : p) : Unique p where
  default := h
  uniq _ := rfl

instance : Unique True :=
  uniqueProp trivial

theorem Fin.eq_zero : ∀ n : Fin 1, n = 0
  | ⟨_, hn⟩ => Fin.eq_of_veq (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hn))

instance {n : ℕ} : Inhabited (Fin n.succ) :=
  ⟨0⟩

instance inhabitedFinOneAdd (n : ℕ) : Inhabited (Fin (1 + n)) :=
  ⟨⟨0, by rw [Nat.add_comm]; exact Nat.zero_lt_succ _⟩⟩

@[simp]
theorem Fin.default_eq_zero (n : ℕ) : (default : Fin n.succ) = 0 :=
  rfl

instance Fin.unique : Unique (Fin 1) where
  uniq := Fin.eq_zero

namespace Unique

open Function

section

variable [Unique α]

-- see Note [lower instance priority]
instance (priority := 100) : Inhabited α :=
  toInhabited ‹Unique α›

theorem eq_default (a : α) : a = default :=
  uniq _ a

theorem default_eq (a : α) : default = a :=
  (uniq _ a).symm

-- see Note [lower instance priority]
instance (priority := 100) : Subsingleton α :=
  subsingleton_of_forall_eq _ eq_default

theorem forall_iff {p : α → Prop} : (∀ a, p a) ↔ p default :=
  ⟨fun h => h _, fun h x => by rwa [Unique.eq_default x]⟩

theorem exists_iff {p : α → Prop} : Exists p ↔ p default :=
  ⟨fun ⟨a, ha⟩ => eq_default a ▸ ha, Exists.intro default⟩

end

@[ext]
protected theorem subsingleton_unique' : ∀ h₁ h₂ : Unique α, h₁ = h₂
  | ⟨⟨x⟩, h⟩, ⟨⟨y⟩, _⟩ => by congr; rw [h x, h y]

instance subsingleton_unique : Subsingleton (Unique α) :=
  ⟨Unique.subsingleton_unique'⟩

/-- Construct `Unique` from `Inhabited` and `Subsingleton`. Making this an instance would create
a loop in the class inheritance graph. -/
@[reducible]
def mk' (α : Sort u) [h₁ : Inhabited α] [Subsingleton α] : Unique α :=
  { h₁ with uniq := fun _ => Subsingleton.elim _ _ }

end Unique

theorem unique_iff_subsingleton_and_nonempty (α : Sort u) :
    Nonempty (Unique α) ↔ Subsingleton α ∧ Nonempty α :=
  ⟨fun ⟨u⟩ => by constructor <;> exact inferInstance,
   fun ⟨hs, hn⟩ => ⟨by inhabit α; exact Unique.mk' α⟩⟩

@[simp]
theorem Pi.default_def {β : α → Sort v} [∀ a, Inhabited (β a)] :
    @default (∀ a, β a) _ = fun a : α => @default (β a) _ :=
  rfl

theorem Pi.default_apply {β : α → Sort v} [∀ a, Inhabited (β a)] (a : α) :
    @default (∀ a, β a) _ a = default :=
  rfl

instance Pi.unique {β : α → Sort v} [∀ a, Unique (β a)] : Unique (∀ a, β a) where
  uniq := fun _ => funext fun _ => Unique.eq_default _

/-- There is a unique function on an empty domain. -/
instance Pi.uniqueOfIsEmpty [IsEmpty α] (β : α → Sort v) : Unique (∀ a, β a) where
  default := isEmptyElim
  uniq _ := funext isEmptyElim

theorem eq_const_of_unique [Unique α] (f : α → β) : f = Function.const α (f default) := by
  ext x
  rw [Subsingleton.elim x default]
  rfl

theorem heq_const_of_unique [Unique α] {β : α → Sort v} (f : ∀ a, β a) :
    HEq f (Function.const α (f default)) :=
  (Function.hfunext rfl) fun i _ _ => by rw [Subsingleton.elim i default]; rfl

namespace Function

variable {f : α → β}

/-- If the codomain of an injective function is a subsingleton, then the domain
is a subsingleton as well. -/
protected theorem Injective.subsingleton (hf : Injective f) [Subsingleton β] : Subsingleton α :=
  ⟨fun _ _ => hf <| Subsingleton.elim _ _⟩

/-- If the domain of a surjective function is a subsingleton, then the codomain is a subsingleton as
well. -/
protected theorem Surjective.subsingleton [Subsingleton α] (hf : Surjective f) : Subsingleton β :=
  ⟨hf.forall₂.2 fun x y => congr_arg f <| Subsingleton.elim x y⟩

/-- If the domain of a surjective function is a singleton,
then the codomain is a singleton as well. -/
protected def Surjective.unique (hf : Surjective f) [Unique α] : Unique β :=
  @Unique.mk' _ ⟨f default⟩ hf.subsingleton

/-- If `α` is inhabited and admits an injective map to a subsingleton type, then `α` is `Unique`. -/
protected def Injective.unique [Inhabited α] [Subsingleton β] (hf : Injective f) : Unique α :=
  @Unique.mk' _ _ hf.subsingleton

/-- If a constant function is surjective, then the codomain is a singleton. -/
def Surjective.uniqueOfSurjectiveConst (α : Type _) {β : Type _} (b : β)
    (h : Function.Surjective (Function.const α b)) : Unique β :=
  @uniqueOfSubsingleton _ (subsingleton_of_forall_eq b <| h.forall.mpr fun _ => rfl) b

end Function

-- TODO: Mario turned this off as a simp lemma in Std, wanting to profile it.
attribute [simp] eq_iff_true_of_subsingleton in
theorem Unique.bijective {A B} [Unique A] [Unique B] {f : A → B} : Function.Bijective f := by
  rw [Function.bijective_iff_has_inverse]
  refine' ⟨default, _, _⟩ <;> intro x <;> simp

namespace Option

/-- `option α` is a `subsingleton` if and only if `α` is empty. -/
theorem subsingleton_iff_isEmpty {α : Type u} : Subsingleton (Option α) ↔ IsEmpty α :=
  ⟨fun h => ⟨fun x => Option.noConfusion <| @Subsingleton.elim _ h x none⟩,
   fun h => ⟨fun x y =>
     Option.casesOn x (Option.casesOn y rfl fun x => h.elim x) fun x => h.elim x⟩⟩
#align option.subsingleton_iff_is_empty Option.subsingleton_iff_isEmpty

instance {α} [IsEmpty α] : Unique (Option α) :=
  @Unique.mk' _ _ (subsingleton_iff_isEmpty.2 ‹_›)

end Option

section Subtype
variable {α : Sort u}

instance Unique.subtypeEq (y : α) : Unique { x // x = y } where
  default := ⟨y, rfl⟩
  uniq := fun ⟨x, hx⟩ => by congr

instance Unique.subtypeEq' (y : α) : Unique { x // y = x } where
  default := ⟨y, rfl⟩
  uniq := fun ⟨x, hx⟩ => by subst hx; congr

end Subtype
