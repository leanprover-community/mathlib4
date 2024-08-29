/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Yury Kudryashov
-/
import Mathlib.Order.Notation
import Mathlib.Data.Nat.Notation

/-!
# Order-related type synonyms

In this file we define `WithBot`, `WithTop`, `ENat`, and `PNat`.
The definitions were moved to this file without any theory
so that, e.g., `Data/Countable/Basic` can prove `Countable ENat`
without exploding its imports.
-/

variable {α : Type*}

/-- Attach `⊥` to a type. -/
def WithBot (α : Type*) := Option α

namespace WithBot

instance [Repr α] : Repr (WithBot α) :=
  ⟨fun o _ =>
    match o with
    | none => "⊥"
    | some a => "↑" ++ repr a⟩

/-- The canonical map from `α` into `WithBot α` -/
@[coe, match_pattern] def some : α → WithBot α :=
  Option.some

-- Porting note: changed this from `CoeTC` to `Coe` but I am not 100% confident that's correct.
instance coe : Coe α (WithBot α) :=
  ⟨some⟩

instance bot : Bot (WithBot α) :=
  ⟨none⟩

instance inhabited : Inhabited (WithBot α) :=
  ⟨⊥⟩

/-- Recursor for `WithBot` using the preferred forms `⊥` and `↑a`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
def recBotCoe {C : WithBot α → Sort*} (bot : C ⊥) (coe : ∀ a : α, C a) : ∀ n : WithBot α, C n
  | ⊥ => bot
  | (a : α) => coe a

@[simp]
theorem recBotCoe_bot {C : WithBot α → Sort*} (d : C ⊥) (f : ∀ a : α, C a) :
    @recBotCoe _ C d f ⊥ = d :=
  rfl

@[simp]
theorem recBotCoe_coe {C : WithBot α → Sort*} (d : C ⊥) (f : ∀ a : α, C a) (x : α) :
    @recBotCoe _ C d f ↑x = f x :=
  rfl

end WithBot

--TODO(Mario): Construct using order dual on `WithBot`
/-- Attach `⊤` to a type. -/
def WithTop (α : Type*) :=
  Option α

namespace WithTop

instance [Repr α] : Repr (WithTop α) :=
  ⟨fun o _ =>
    match o with
    | none => "⊤"
    | some a => "↑" ++ repr a⟩

/-- The canonical map from `α` into `WithTop α` -/
@[coe, match_pattern] def some : α → WithTop α :=
  Option.some

instance coeTC : CoeTC α (WithTop α) :=
  ⟨some⟩

instance top : Top (WithTop α) :=
  ⟨none⟩

instance inhabited : Inhabited (WithTop α) :=
  ⟨⊤⟩

/-- Recursor for `WithTop` using the preferred forms `⊤` and `↑a`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
def recTopCoe {C : WithTop α → Sort*} (top : C ⊤) (coe : ∀ a : α, C a) : ∀ n : WithTop α, C n
  | none => top
  | Option.some a => coe a

@[simp]
theorem recTopCoe_top {C : WithTop α → Sort*} (d : C ⊤) (f : ∀ a : α, C a) :
    @recTopCoe _ C d f ⊤ = d :=
  rfl

@[simp]
theorem recTopCoe_coe {C : WithTop α → Sort*} (d : C ⊤) (f : ∀ a : α, C a) (x : α) :
    @recTopCoe _ C d f ↑x = f x :=
  rfl

end WithTop

/-- Extended natural numbers `ℕ∞ = WithTop ℕ`. -/
def ENat : Type := WithTop ℕ deriving Top, Inhabited

@[inherit_doc] notation "ℕ∞" => ENat

namespace ENat

instance instNatCast : NatCast ℕ∞ := ⟨WithTop.some⟩

-- Porting note (#11445): new definition copied from `WithTop`
/-- Recursor for `ENat` using the preferred forms `⊤` and `↑a`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
def recTopCoe {C : ℕ∞ → Sort*} (top : C ⊤) (coe : ∀ a : ℕ, C a) : ∀ n : ℕ∞, C n
  | none => top
  | Option.some a => coe a

@[simp]
theorem recTopCoe_top {C : ℕ∞ → Sort*} (d : C ⊤) (f : ∀ a : ℕ, C a) :
    @recTopCoe C d f ⊤ = d :=
  rfl

@[simp]
theorem recTopCoe_coe {C : ℕ∞ → Sort*} (d : C ⊤) (f : ∀ a : ℕ, C a) (x : ℕ) :
    @recTopCoe C d f ↑x = f x :=
  rfl

end ENat

/-- `ℕ+` is the type of positive natural numbers. It is defined as a subtype,
  and the VM representation of `ℕ+` is the same as `ℕ` because the proof
  is not stored. -/
def PNat := { n : ℕ // 0 < n } deriving DecidableEq

@[inherit_doc]
notation "ℕ+" => PNat

/-- The underlying natural number -/
@[coe]
def PNat.val : ℕ+ → ℕ := Subtype.val

instance coePNatNat : Coe ℕ+ ℕ :=
  ⟨PNat.val⟩

instance : Repr ℕ+ :=
  ⟨fun n n' => reprPrec n.1 n'⟩
