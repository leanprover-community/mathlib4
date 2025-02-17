/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Count
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Perm.Lattice
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.Set.List
import Mathlib.Order.Hom.Basic
import Mathlib.Order.MinMax

/-!
# Multisets

Multisets are finite sets with duplicates allowed. They are implemented here as the quotient of
lists by permutation. This gives them computational content.

## Notation

* `0`: The empty multiset.
* `{a}`: The multiset containing a single occurrence of `a`.
* `a ::ₘ s`: The multiset containing one more occurrence of `a` than `s` does.
* `s + t`: The multiset for which the number of occurrences of each `a` is the sum of the
  occurrences of `a` in `s` and `t`.
* `s - t`: The multiset for which the number of occurrences of each `a` is the difference of the
  occurrences of `a` in `s` and `t`.
* `s ∪ t`: The multiset for which the number of occurrences of each `a` is the max of the
  occurrences of `a` in `s` and `t`.
* `s ∩ t`: The multiset for which the number of occurrences of each `a` is the min of the
  occurrences of `a` in `s` and `t`.
-/

-- No algebra should be required
assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

/-- `Multiset α` is the quotient of `List α` by list permutation. The result
  is a type of finite sets with duplicates allowed. -/
def Multiset.{u} (α : Type u) : Type u :=
  Quotient (List.isSetoid α)

namespace Multiset

-- Porting note: new
/-- The quotient map from `List α` to `Multiset α`. -/
@[coe]
def ofList : List α → Multiset α :=
  Quot.mk _

instance : Coe (List α) (Multiset α) :=
  ⟨ofList⟩

@[simp]
theorem quot_mk_to_coe (l : List α) : @Eq (Multiset α) ⟦l⟧ l :=
  rfl

@[simp]
theorem quot_mk_to_coe' (l : List α) : @Eq (Multiset α) (Quot.mk (· ≈ ·) l) l :=
  rfl

@[simp]
theorem quot_mk_to_coe'' (l : List α) : @Eq (Multiset α) (Quot.mk Setoid.r l) l :=
  rfl

@[simp]
theorem lift_coe {α β : Type*} (x : List α) (f : List α → β)
    (h : ∀ a b : List α, a ≈ b → f a = f b) : Quotient.lift f h (x : Multiset α) = f x :=
  Quotient.lift_mk _ _ _

@[simp]
theorem coe_eq_coe {l₁ l₂ : List α} : (l₁ : Multiset α) = l₂ ↔ l₁ ~ l₂ :=
  Quotient.eq

-- Porting note: new instance;
-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: move to better place
instance [DecidableEq α] (l₁ l₂ : List α) : Decidable (l₁ ≈ l₂) :=
  inferInstanceAs (Decidable (l₁ ~ l₂))

instance [DecidableEq α] (l₁ l₂ : List α) : Decidable (isSetoid α l₁ l₂) :=
  inferInstanceAs (Decidable (l₁ ~ l₂))

-- Porting note: `Quotient.recOnSubsingleton₂ s₁ s₂` was in parens which broke elaboration
instance decidableEq [DecidableEq α] : DecidableEq (Multiset α)
  | s₁, s₂ => Quotient.recOnSubsingleton₂ s₁ s₂ fun _ _ => decidable_of_iff' _ Quotient.eq_iff_equiv

/-- defines a size for a multiset by referring to the size of the underlying list -/
protected
def sizeOf [SizeOf α] (s : Multiset α) : ℕ :=
  (Quot.liftOn s SizeOf.sizeOf) fun _ _ => Perm.sizeOf_eq_sizeOf

instance [SizeOf α] : SizeOf (Multiset α) :=
  ⟨Multiset.sizeOf⟩

/-! ### Empty multiset -/


/-- `0 : Multiset α` is the empty set -/
protected def zero : Multiset α :=
  @nil α

instance : Zero (Multiset α) :=
  ⟨Multiset.zero⟩

instance : EmptyCollection (Multiset α) :=
  ⟨0⟩

instance inhabitedMultiset : Inhabited (Multiset α) :=
  ⟨0⟩

instance [IsEmpty α] : Unique (Multiset α) where
  default := 0
  uniq := by rintro ⟨_ | ⟨a, l⟩⟩; exacts [rfl, isEmptyElim a]

@[simp]
theorem coe_nil : (@nil α : Multiset α) = 0 :=
  rfl

@[simp]
theorem empty_eq_zero : (∅ : Multiset α) = 0 :=
  rfl

@[simp]
theorem coe_eq_zero (l : List α) : (l : Multiset α) = 0 ↔ l = [] :=
  Iff.trans coe_eq_coe perm_nil

theorem coe_eq_zero_iff_isEmpty (l : List α) : (l : Multiset α) = 0 ↔ l.isEmpty :=
  Iff.trans (coe_eq_zero l) isEmpty_iff.symm

/-! ### `Multiset.cons` -/

/-- `cons a s` is the multiset which contains `s` plus one more instance of `a`. -/
def cons (a : α) (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (a :: l : Multiset α)) fun _ _ p => Quot.sound (p.cons a)

@[inherit_doc Multiset.cons]
infixr:67 " ::ₘ " => Multiset.cons

instance : Insert α (Multiset α) :=
  ⟨cons⟩

@[simp]
theorem insert_eq_cons (a : α) (s : Multiset α) : insert a s = a ::ₘ s :=
  rfl

@[simp]
theorem cons_coe (a : α) (l : List α) : (a ::ₘ l : Multiset α) = (a :: l : List α) :=
  rfl

@[simp]
theorem cons_inj_left {a b : α} (s : Multiset α) : a ::ₘ s = b ::ₘ s ↔ a = b :=
  ⟨Quot.inductionOn s fun l e =>
      have : [a] ++ l ~ [b] ++ l := Quotient.exact e
      singleton_perm_singleton.1 <| (perm_append_right_iff _).1 this,
    congr_arg (· ::ₘ _)⟩

@[simp]
theorem cons_inj_right (a : α) : ∀ {s t : Multiset α}, a ::ₘ s = a ::ₘ t ↔ s = t := by
  rintro ⟨l₁⟩ ⟨l₂⟩; simp

@[elab_as_elim]
protected theorem induction {p : Multiset α → Prop} (empty : p 0)
    (cons : ∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) : ∀ s, p s := by
  rintro ⟨l⟩; induction l with | nil => exact empty | cons _ _ ih => exact cons _ _ ih

@[elab_as_elim]
protected theorem induction_on {p : Multiset α → Prop} (s : Multiset α) (empty : p 0)
    (cons : ∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) : p s :=
  Multiset.induction empty cons s

theorem cons_swap (a b : α) (s : Multiset α) : a ::ₘ b ::ₘ s = b ::ₘ a ::ₘ s :=
  Quot.inductionOn s fun _ => Quotient.sound <| Perm.swap _ _ _

section Rec

variable {C : Multiset α → Sort*}

/-- Dependent recursor on multisets.
TODO: should be @[recursor 6], but then the definition of `Multiset.pi` fails with a stack
overflow in `whnf`.
-/
protected
def rec (C_0 : C 0) (C_cons : ∀ a m, C m → C (a ::ₘ m))
    (C_cons_heq :
      ∀ a a' m b, HEq (C_cons a (a' ::ₘ m) (C_cons a' m b)) (C_cons a' (a ::ₘ m) (C_cons a m b)))
    (m : Multiset α) : C m :=
  Quotient.hrecOn m (@List.rec α (fun l => C ⟦l⟧) C_0 fun a l b => C_cons a ⟦l⟧ b) fun _ _ h =>
    h.rec_heq
      (fun hl _ ↦ by congr 1; exact Quot.sound hl)
      (C_cons_heq _ _ ⟦_⟧ _)

/-- Companion to `Multiset.rec` with more convenient argument order. -/
@[elab_as_elim]
protected
def recOn (m : Multiset α) (C_0 : C 0) (C_cons : ∀ a m, C m → C (a ::ₘ m))
    (C_cons_heq :
      ∀ a a' m b, HEq (C_cons a (a' ::ₘ m) (C_cons a' m b)) (C_cons a' (a ::ₘ m) (C_cons a m b))) :
    C m :=
  Multiset.rec C_0 C_cons C_cons_heq m

variable {C_0 : C 0} {C_cons : ∀ a m, C m → C (a ::ₘ m)}
  {C_cons_heq :
    ∀ a a' m b, HEq (C_cons a (a' ::ₘ m) (C_cons a' m b)) (C_cons a' (a ::ₘ m) (C_cons a m b))}

@[simp]
theorem recOn_0 : @Multiset.recOn α C (0 : Multiset α) C_0 C_cons C_cons_heq = C_0 :=
  rfl

@[simp]
theorem recOn_cons (a : α) (m : Multiset α) :
    (a ::ₘ m).recOn C_0 C_cons C_cons_heq = C_cons a m (m.recOn C_0 C_cons C_cons_heq) :=
  Quotient.inductionOn m fun _ => rfl

end Rec

section Mem

/-- `a ∈ s` means that `a` has nonzero multiplicity in `s`. -/
def Mem (s : Multiset α) (a : α) : Prop :=
  Quot.liftOn s (fun l => a ∈ l) fun l₁ l₂ (e : l₁ ~ l₂) => propext <| e.mem_iff

instance : Membership α (Multiset α) :=
  ⟨Mem⟩

@[simp]
theorem mem_coe {a : α} {l : List α} : a ∈ (l : Multiset α) ↔ a ∈ l :=
  Iff.rfl

instance decidableMem [DecidableEq α] (a : α) (s : Multiset α) : Decidable (a ∈ s) :=
  Quot.recOnSubsingleton s fun l ↦ inferInstanceAs (Decidable (a ∈ l))

@[simp]
theorem mem_cons {a b : α} {s : Multiset α} : a ∈ b ::ₘ s ↔ a = b ∨ a ∈ s :=
  Quot.inductionOn s fun _ => List.mem_cons

theorem mem_cons_of_mem {a b : α} {s : Multiset α} (h : a ∈ s) : a ∈ b ::ₘ s :=
  mem_cons.2 <| Or.inr h

theorem mem_cons_self (a : α) (s : Multiset α) : a ∈ a ::ₘ s :=
  mem_cons.2 (Or.inl rfl)

theorem forall_mem_cons {p : α → Prop} {a : α} {s : Multiset α} :
    (∀ x ∈ a ::ₘ s, p x) ↔ p a ∧ ∀ x ∈ s, p x :=
  Quotient.inductionOn' s fun _ => List.forall_mem_cons

theorem exists_cons_of_mem {s : Multiset α} {a : α} : a ∈ s → ∃ t, s = a ::ₘ t :=
  Quot.inductionOn s fun l (h : a ∈ l) =>
    let ⟨l₁, l₂, e⟩ := append_of_mem h
    e.symm ▸ ⟨(l₁ ++ l₂ : List α), Quot.sound perm_middle⟩

@[simp]
theorem not_mem_zero (a : α) : a ∉ (0 : Multiset α) :=
  List.not_mem_nil _

theorem eq_zero_of_forall_not_mem {s : Multiset α} : (∀ x, x ∉ s) → s = 0 :=
  Quot.inductionOn s fun l H => by rw [eq_nil_iff_forall_not_mem.mpr H]; rfl

theorem eq_zero_iff_forall_not_mem {s : Multiset α} : s = 0 ↔ ∀ a, a ∉ s :=
  ⟨fun h => h.symm ▸ fun _ => not_mem_zero _, eq_zero_of_forall_not_mem⟩

theorem exists_mem_of_ne_zero {s : Multiset α} : s ≠ 0 → ∃ a : α, a ∈ s :=
  Quot.inductionOn s fun l hl =>
    match l, hl with
    | [], h => False.elim <| h rfl
    | a :: l, _ => ⟨a, by simp⟩

theorem empty_or_exists_mem (s : Multiset α) : s = 0 ∨ ∃ a, a ∈ s :=
  or_iff_not_imp_left.mpr Multiset.exists_mem_of_ne_zero

@[simp]
theorem zero_ne_cons {a : α} {m : Multiset α} : 0 ≠ a ::ₘ m := fun h =>
  have : a ∈ (0 : Multiset α) := h.symm ▸ mem_cons_self _ _
  not_mem_zero _ this

@[simp]
theorem cons_ne_zero {a : α} {m : Multiset α} : a ::ₘ m ≠ 0 :=
  zero_ne_cons.symm

theorem cons_eq_cons {a b : α} {as bs : Multiset α} :
    a ::ₘ as = b ::ₘ bs ↔ a = b ∧ as = bs ∨ a ≠ b ∧ ∃ cs, as = b ::ₘ cs ∧ bs = a ::ₘ cs := by
  haveI : DecidableEq α := Classical.decEq α
  constructor
  · intro eq
    by_cases h : a = b
    · subst h
      simp_all
    · have : a ∈ b ::ₘ bs := eq ▸ mem_cons_self _ _
      have : a ∈ bs := by simpa [h]
      rcases exists_cons_of_mem this with ⟨cs, hcs⟩
      simp only [h, hcs, false_and, ne_eq, not_false_eq_true, cons_inj_right, exists_eq_right',
        true_and, false_or]
      have : a ::ₘ as = b ::ₘ a ::ₘ cs := by simp [eq, hcs]
      have : a ::ₘ as = a ::ₘ b ::ₘ cs := by rwa [cons_swap]
      simpa using this
  · intro h
    rcases h with (⟨eq₁, eq₂⟩ | ⟨_, cs, eq₁, eq₂⟩)
    · simp [*]
    · simp [*, cons_swap a b]

end Mem

/-! ### Singleton -/


instance : Singleton α (Multiset α) :=
  ⟨fun a => a ::ₘ 0⟩

instance : LawfulSingleton α (Multiset α) :=
  ⟨fun _ => rfl⟩

@[simp]
theorem cons_zero (a : α) : a ::ₘ 0 = {a} :=
  rfl

@[simp, norm_cast]
theorem coe_singleton (a : α) : ([a] : Multiset α) = {a} :=
  rfl

@[simp]
theorem mem_singleton {a b : α} : b ∈ ({a} : Multiset α) ↔ b = a := by
  simp only [← cons_zero, mem_cons, iff_self, or_false, not_mem_zero]

theorem mem_singleton_self (a : α) : a ∈ ({a} : Multiset α) := by
  rw [← cons_zero]
  exact mem_cons_self _ _

@[simp]
theorem singleton_inj {a b : α} : ({a} : Multiset α) = {b} ↔ a = b := by
  simp_rw [← cons_zero]
  exact cons_inj_left _

@[simp, norm_cast]
theorem coe_eq_singleton {l : List α} {a : α} : (l : Multiset α) = {a} ↔ l = [a] := by
  rw [← coe_singleton, coe_eq_coe, List.perm_singleton]

@[simp]
theorem singleton_eq_cons_iff {a b : α} (m : Multiset α) : {a} = b ::ₘ m ↔ a = b ∧ m = 0 := by
  rw [← cons_zero, cons_eq_cons]
  simp [eq_comm]

theorem pair_comm (x y : α) : ({x, y} : Multiset α) = {y, x} :=
  cons_swap x y 0

/-! ### `Multiset.Subset` -/


section Subset
variable {s : Multiset α} {a : α}

/-- `s ⊆ t` is the lift of the list subset relation. It means that any
  element with nonzero multiplicity in `s` has nonzero multiplicity in `t`,
  but it does not imply that the multiplicity of `a` in `s` is less or equal than in `t`;
  see `s ≤ t` for this relation. -/
protected def Subset (s t : Multiset α) : Prop :=
  ∀ ⦃a : α⦄, a ∈ s → a ∈ t

instance : HasSubset (Multiset α) :=
  ⟨Multiset.Subset⟩

instance : HasSSubset (Multiset α) :=
  ⟨fun s t => s ⊆ t ∧ ¬t ⊆ s⟩

instance instIsNonstrictStrictOrder : IsNonstrictStrictOrder (Multiset α) (· ⊆ ·) (· ⊂ ·) where
  right_iff_left_not_left _ _ := Iff.rfl

@[simp]
theorem coe_subset {l₁ l₂ : List α} : (l₁ : Multiset α) ⊆ l₂ ↔ l₁ ⊆ l₂ :=
  Iff.rfl

@[simp]
theorem Subset.refl (s : Multiset α) : s ⊆ s := fun _ h => h

theorem Subset.trans {s t u : Multiset α} : s ⊆ t → t ⊆ u → s ⊆ u := fun h₁ h₂ _ m => h₂ (h₁ m)

theorem subset_iff {s t : Multiset α} : s ⊆ t ↔ ∀ ⦃x⦄, x ∈ s → x ∈ t :=
  Iff.rfl

theorem mem_of_subset {s t : Multiset α} {a : α} (h : s ⊆ t) : a ∈ s → a ∈ t :=
  @h _

@[simp]
theorem zero_subset (s : Multiset α) : 0 ⊆ s := fun a => (not_mem_nil a).elim

theorem subset_cons (s : Multiset α) (a : α) : s ⊆ a ::ₘ s := fun _ => mem_cons_of_mem

theorem ssubset_cons {s : Multiset α} {a : α} (ha : a ∉ s) : s ⊂ a ::ₘ s :=
  ⟨subset_cons _ _, fun h => ha <| h <| mem_cons_self _ _⟩

@[simp]
theorem cons_subset {a : α} {s t : Multiset α} : a ::ₘ s ⊆ t ↔ a ∈ t ∧ s ⊆ t := by
  simp [subset_iff, or_imp, forall_and]

theorem cons_subset_cons {a : α} {s t : Multiset α} : s ⊆ t → a ::ₘ s ⊆ a ::ₘ t :=
  Quotient.inductionOn₂ s t fun _ _ => List.cons_subset_cons _

theorem eq_zero_of_subset_zero {s : Multiset α} (h : s ⊆ 0) : s = 0 :=
  eq_zero_of_forall_not_mem fun _ hx ↦ not_mem_zero _ (h hx)

@[simp] lemma subset_zero : s ⊆ 0 ↔ s = 0 :=
  ⟨eq_zero_of_subset_zero, fun xeq => xeq.symm ▸ Subset.refl 0⟩

@[simp] lemma zero_ssubset : 0 ⊂ s ↔ s ≠ 0 := by simp [ssubset_iff_subset_not_subset]

@[simp] lemma singleton_subset : {a} ⊆ s ↔ a ∈ s := by simp [subset_iff]

theorem induction_on' {p : Multiset α → Prop} (S : Multiset α) (h₁ : p 0)
    (h₂ : ∀ {a s}, a ∈ S → s ⊆ S → p s → p (insert a s)) : p S :=
  @Multiset.induction_on α (fun T => T ⊆ S → p T) S (fun _ => h₁)
    (fun _ _ hps hs =>
      let ⟨hS, sS⟩ := cons_subset.1 hs
      h₂ hS sS (hps sS))
    (Subset.refl S)

end Subset

/-! ### `Multiset.toList` -/


section ToList

/-- Produces a list of the elements in the multiset using choice. -/
noncomputable def toList (s : Multiset α) :=
  s.out

@[simp, norm_cast]
theorem coe_toList (s : Multiset α) : (s.toList : Multiset α) = s :=
  s.out_eq'

@[simp]
theorem toList_eq_nil {s : Multiset α} : s.toList = [] ↔ s = 0 := by
  rw [← coe_eq_zero, coe_toList]

theorem empty_toList {s : Multiset α} : s.toList.isEmpty ↔ s = 0 := by simp

@[simp]
theorem toList_zero : (Multiset.toList 0 : List α) = [] :=
  toList_eq_nil.mpr rfl

@[simp]
theorem mem_toList {a : α} {s : Multiset α} : a ∈ s.toList ↔ a ∈ s := by
  rw [← mem_coe, coe_toList]

@[simp]
theorem toList_eq_singleton_iff {a : α} {m : Multiset α} : m.toList = [a] ↔ m = {a} := by
  rw [← perm_singleton, ← coe_eq_coe, coe_toList, coe_singleton]

@[simp]
theorem toList_singleton (a : α) : ({a} : Multiset α).toList = [a] :=
  Multiset.toList_eq_singleton_iff.2 rfl

end ToList

/-! ### Partial order on `Multiset`s -/


/-- `s ≤ t` means that `s` is a sublist of `t` (up to permutation).
  Equivalently, `s ≤ t` means that `count a s ≤ count a t` for all `a`. -/
protected def Le (s t : Multiset α) : Prop :=
  (Quotient.liftOn₂ s t (· <+~ ·)) fun _ _ _ _ p₁ p₂ =>
    propext (p₂.subperm_left.trans p₁.subperm_right)

instance : PartialOrder (Multiset α) where
  le := Multiset.Le
  le_refl := by rintro ⟨l⟩; exact Subperm.refl _
  le_trans := by rintro ⟨l₁⟩ ⟨l₂⟩ ⟨l₃⟩; exact @Subperm.trans _ _ _ _
  le_antisymm := by rintro ⟨l₁⟩ ⟨l₂⟩ h₁ h₂; exact Quot.sound (Subperm.antisymm h₁ h₂)

instance decidableLE [DecidableEq α] : DecidableRel ((· ≤ ·) : Multiset α → Multiset α → Prop) :=
  fun s t => Quotient.recOnSubsingleton₂ s t List.decidableSubperm

section

variable {s t : Multiset α} {a : α}

theorem subset_of_le : s ≤ t → s ⊆ t :=
  Quotient.inductionOn₂ s t fun _ _ => Subperm.subset

alias Le.subset := subset_of_le

theorem mem_of_le (h : s ≤ t) : a ∈ s → a ∈ t :=
  mem_of_subset (subset_of_le h)

theorem not_mem_mono (h : s ⊆ t) : a ∉ t → a ∉ s :=
  mt <| @h _

@[simp]
theorem coe_le {l₁ l₂ : List α} : (l₁ : Multiset α) ≤ l₂ ↔ l₁ <+~ l₂ :=
  Iff.rfl

@[elab_as_elim]
theorem leInductionOn {C : Multiset α → Multiset α → Prop} {s t : Multiset α} (h : s ≤ t)
    (H : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → C l₁ l₂) : C s t :=
  Quotient.inductionOn₂ s t (fun l₁ _ ⟨l, p, s⟩ => (show ⟦l⟧ = ⟦l₁⟧ from Quot.sound p) ▸ H s) h

theorem zero_le (s : Multiset α) : 0 ≤ s :=
  Quot.inductionOn s fun l => (nil_sublist l).subperm

instance : OrderBot (Multiset α) where
  bot := 0
  bot_le := zero_le

/-- This is a `rfl` and `simp` version of `bot_eq_zero`. -/
@[simp]
theorem bot_eq_zero : (⊥ : Multiset α) = 0 :=
  rfl

theorem le_zero : s ≤ 0 ↔ s = 0 :=
  le_bot_iff

theorem lt_cons_self (s : Multiset α) (a : α) : s < a ::ₘ s :=
  Quot.inductionOn s fun l =>
    suffices l <+~ a :: l ∧ ¬l ~ a :: l by simpa [lt_iff_le_and_ne]
    ⟨(sublist_cons_self _ _).subperm,
      fun p => _root_.ne_of_lt (lt_succ_self (length l)) p.length_eq⟩

theorem le_cons_self (s : Multiset α) (a : α) : s ≤ a ::ₘ s :=
  le_of_lt <| lt_cons_self _ _

theorem cons_le_cons_iff (a : α) : a ::ₘ s ≤ a ::ₘ t ↔ s ≤ t :=
  Quotient.inductionOn₂ s t fun _ _ => subperm_cons a

theorem cons_le_cons (a : α) : s ≤ t → a ::ₘ s ≤ a ::ₘ t :=
  (cons_le_cons_iff a).2

@[simp] lemma cons_lt_cons_iff : a ::ₘ s < a ::ₘ t ↔ s < t :=
  lt_iff_lt_of_le_iff_le' (cons_le_cons_iff _) (cons_le_cons_iff _)

lemma cons_lt_cons (a : α) (h : s < t) : a ::ₘ s < a ::ₘ t := cons_lt_cons_iff.2 h

theorem le_cons_of_not_mem (m : a ∉ s) : s ≤ a ::ₘ t ↔ s ≤ t := by
  refine ⟨?_, fun h => le_trans h <| le_cons_self _ _⟩
  suffices ∀ {t'}, s ≤ t' → a ∈ t' → a ::ₘ s ≤ t' by
    exact fun h => (cons_le_cons_iff a).1 (this h (mem_cons_self _ _))
  introv h
  revert m
  refine leInductionOn h ?_
  introv s m₁ m₂
  rcases append_of_mem m₂ with ⟨r₁, r₂, rfl⟩
  exact
    perm_middle.subperm_left.2
      ((subperm_cons _).2 <| ((sublist_or_mem_of_sublist s).resolve_right m₁).subperm)

theorem cons_le_of_not_mem (hs : a ∉ s) : a ::ₘ s ≤ t ↔ a ∈ t ∧ s ≤ t := by
  apply Iff.intro (fun h ↦ ⟨subset_of_le h (mem_cons_self a s), le_trans (le_cons_self s a) h⟩)
  rintro ⟨h₁, h₂⟩; rcases exists_cons_of_mem h₁ with ⟨_, rfl⟩
  exact cons_le_cons _ ((le_cons_of_not_mem hs).mp h₂)

@[simp]
theorem singleton_ne_zero (a : α) : ({a} : Multiset α) ≠ 0 :=
  ne_of_gt (lt_cons_self _ _)

@[simp]
theorem zero_ne_singleton (a : α) : 0 ≠ ({a} : Multiset α) := singleton_ne_zero _ |>.symm

@[simp]
theorem singleton_le {a : α} {s : Multiset α} : {a} ≤ s ↔ a ∈ s :=
  ⟨fun h => mem_of_le h (mem_singleton_self _), fun h =>
    let ⟨_t, e⟩ := exists_cons_of_mem h
    e.symm ▸ cons_le_cons _ (zero_le _)⟩

@[simp] lemma le_singleton : s ≤ {a} ↔ s = 0 ∨ s = {a} :=
  Quot.induction_on s fun l ↦ by simp only [cons_zero, ← coe_singleton, quot_mk_to_coe'', coe_le,
    coe_eq_zero, coe_eq_coe, perm_singleton, subperm_singleton_iff]

@[simp] lemma lt_singleton : s < {a} ↔ s = 0 := by
  simp only [lt_iff_le_and_ne, le_singleton, or_and_right, Ne, and_not_self, or_false,
    and_iff_left_iff_imp]
  rintro rfl
  exact (singleton_ne_zero _).symm

@[simp] lemma ssubset_singleton_iff : s ⊂ {a} ↔ s = 0 := by
  refine ⟨fun hs ↦ eq_zero_of_subset_zero fun b hb ↦ (hs.2 ?_).elim, ?_⟩
  · obtain rfl := mem_singleton.1 (hs.1 hb)
    rwa [singleton_subset]
  · rintro rfl
    simp

end

/-! ### Additive monoid -/

section add
variable {s t u : Multiset α}

/-- The sum of two multisets is the lift of the list append operation.
  This adds the multiplicities of each element,
  i.e. `count a (s + t) = count a s + count a t`. -/
protected def add (s₁ s₂ : Multiset α) : Multiset α :=
  (Quotient.liftOn₂ s₁ s₂ fun l₁ l₂ => ((l₁ ++ l₂ : List α) : Multiset α)) fun _ _ _ _ p₁ p₂ =>
    Quot.sound <| p₁.append p₂

instance : Add (Multiset α) :=
  ⟨Multiset.add⟩

@[simp]
theorem coe_add (s t : List α) : (s + t : Multiset α) = (s ++ t : List α) :=
  rfl

@[simp]
theorem singleton_add (a : α) (s : Multiset α) : {a} + s = a ::ₘ s :=
  rfl

protected lemma add_le_add_iff_left : s + t ≤ s + u ↔ t ≤ u :=
  Quotient.inductionOn₃ s t u fun _ _ _ => subperm_append_left _

protected lemma add_le_add_iff_right : s + u ≤ t + u ↔ s ≤ t :=
  Quotient.inductionOn₃ s t u fun _ _ _ => subperm_append_right _

protected alias ⟨le_of_add_le_add_left, add_le_add_left⟩ := Multiset.add_le_add_iff_left
protected alias ⟨le_of_add_le_add_right, add_le_add_right⟩ := Multiset.add_le_add_iff_right

protected lemma add_comm (s t : Multiset α) : s + t = t + s :=
  Quotient.inductionOn₂ s t fun _ _ ↦ Quot.sound perm_append_comm

protected lemma add_assoc (s t u : Multiset α) : s + t + u = s + (t + u) :=
  Quotient.inductionOn₃ s t u fun _ _ _ ↦ congr_arg _ <| append_assoc ..

@[simp, nolint simpNF] -- We want to use this lemma earlier than `zero_add`
protected lemma zero_add (s : Multiset α) : 0 + s = s := Quotient.inductionOn s fun _ ↦ rfl

@[simp, nolint simpNF] -- We want to use this lemma earlier than `add_zero`
protected lemma add_zero (s : Multiset α) : s + 0 = s :=
  Quotient.inductionOn s fun l ↦ congr_arg _ <| append_nil l

lemma le_add_right (s t : Multiset α) : s ≤ s + t := by
  simpa using Multiset.add_le_add_left (zero_le t)

lemma le_add_left (s t : Multiset α) : s ≤ t + s := by
  simpa using Multiset.add_le_add_right (zero_le t)

lemma subset_add_left {s t : Multiset α} : s ⊆ s + t := subset_of_le <| le_add_right s t

lemma subset_add_right {s t : Multiset α} : s ⊆ t + s := subset_of_le <| le_add_left s t

theorem le_iff_exists_add {s t : Multiset α} : s ≤ t ↔ ∃ u, t = s + u :=
  ⟨fun h =>
    leInductionOn h fun s =>
      let ⟨l, p⟩ := s.exists_perm_append
      ⟨l, Quot.sound p⟩,
    fun ⟨_u, e⟩ => e.symm ▸ le_add_right _ _⟩

@[simp]
theorem cons_add (a : α) (s t : Multiset α) : a ::ₘ s + t = a ::ₘ (s + t) := by
  rw [← singleton_add, ← singleton_add, Multiset.add_assoc]

@[simp]
theorem add_cons (a : α) (s t : Multiset α) : s + a ::ₘ t = a ::ₘ (s + t) := by
  rw [Multiset.add_comm, cons_add, Multiset.add_comm]

@[simp]
theorem mem_add {a : α} {s t : Multiset α} : a ∈ s + t ↔ a ∈ s ∨ a ∈ t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => mem_append

end add

/-! ### Cardinality -/


/-- The cardinality of a multiset is the sum of the multiplicities
  of all its elements, or simply the length of the underlying list. -/
def card : Multiset α → ℕ := Quot.lift length fun _l₁ _l₂ => Perm.length_eq

@[simp]
theorem coe_card (l : List α) : card (l : Multiset α) = length l :=
  rfl

@[simp]
theorem length_toList (s : Multiset α) : s.toList.length = card s := by
  rw [← coe_card, coe_toList]

@[simp]
theorem card_zero : @card α 0 = 0 :=
  rfl

@[simp]
theorem card_add (s t : Multiset α) : card (s + t) = card s + card t :=
  Quotient.inductionOn₂ s t length_append

@[simp]
theorem card_cons (a : α) (s : Multiset α) : card (a ::ₘ s) = card s + 1 :=
  Quot.inductionOn s fun _l => rfl

@[simp]
theorem card_singleton (a : α) : card ({a} : Multiset α) = 1 := by
  simp only [← cons_zero, card_zero, eq_self_iff_true, Multiset.zero_add, card_cons]

theorem card_pair (a b : α) : card {a, b} = 2 := by
  rw [insert_eq_cons, card_cons, card_singleton]

theorem card_eq_one {s : Multiset α} : card s = 1 ↔ ∃ a, s = {a} :=
  ⟨Quot.inductionOn s fun _l h => (List.length_eq_one.1 h).imp fun _a => congr_arg _,
    fun ⟨_a, e⟩ => e.symm ▸ rfl⟩

theorem card_le_card {s t : Multiset α} (h : s ≤ t) : card s ≤ card t :=
  leInductionOn h Sublist.length_le

@[mono]
theorem card_mono : Monotone (@card α) := fun _a _b => card_le_card

theorem eq_of_le_of_card_le {s t : Multiset α} (h : s ≤ t) : card t ≤ card s → s = t :=
  leInductionOn h fun s h₂ => congr_arg _ <| s.eq_of_length_le h₂

theorem card_lt_card {s t : Multiset α} (h : s < t) : card s < card t :=
  lt_of_not_ge fun h₂ => _root_.ne_of_lt h <| eq_of_le_of_card_le (le_of_lt h) h₂

lemma card_strictMono : StrictMono (card : Multiset α → ℕ) := fun _ _ ↦ card_lt_card

theorem lt_iff_cons_le {s t : Multiset α} : s < t ↔ ∃ a, a ::ₘ s ≤ t :=
  ⟨Quotient.inductionOn₂ s t fun _l₁ _l₂ h =>
      Subperm.exists_of_length_lt (le_of_lt h) (card_lt_card h),
    fun ⟨_a, h⟩ => lt_of_lt_of_le (lt_cons_self _ _) h⟩

@[simp]
theorem card_eq_zero {s : Multiset α} : card s = 0 ↔ s = 0 :=
  ⟨fun h => (eq_of_le_of_card_le (zero_le _) (le_of_eq h)).symm, fun e => by simp [e]⟩

theorem card_pos {s : Multiset α} : 0 < card s ↔ s ≠ 0 :=
  Nat.pos_iff_ne_zero.trans <| not_congr card_eq_zero

theorem card_pos_iff_exists_mem {s : Multiset α} : 0 < card s ↔ ∃ a, a ∈ s :=
  Quot.inductionOn s fun _l => length_pos_iff_exists_mem

theorem card_eq_two {s : Multiset α} : card s = 2 ↔ ∃ x y, s = {x, y} :=
  ⟨Quot.inductionOn s fun _l h =>
      (List.length_eq_two.mp h).imp fun _a => Exists.imp fun _b => congr_arg _,
    fun ⟨_a, _b, e⟩ => e.symm ▸ rfl⟩

theorem card_eq_three {s : Multiset α} : card s = 3 ↔ ∃ x y z, s = {x, y, z} :=
  ⟨Quot.inductionOn s fun _l h =>
      (List.length_eq_three.mp h).imp fun _a =>
        Exists.imp fun _b => Exists.imp fun _c => congr_arg _,
    fun ⟨_a, _b, _c, e⟩ => e.symm ▸ rfl⟩

/-! ### Induction principles -/

/-- The strong induction principle for multisets. -/
@[elab_as_elim]
def strongInductionOn {p : Multiset α → Sort*} (s : Multiset α) (ih : ∀ s, (∀ t < s, p t) → p s) :
    p s :=
    (ih s) fun t _h =>
      strongInductionOn t ih
termination_by card s
decreasing_by exact card_lt_card _h

theorem strongInductionOn_eq {p : Multiset α → Sort*} (s : Multiset α) (H) :
    @strongInductionOn _ p s H = H s fun t _h => @strongInductionOn _ p t H := by
  rw [strongInductionOn]

@[elab_as_elim]
theorem case_strongInductionOn {p : Multiset α → Prop} (s : Multiset α) (h₀ : p 0)
    (h₁ : ∀ a s, (∀ t ≤ s, p t) → p (a ::ₘ s)) : p s :=
  Multiset.strongInductionOn s fun s =>
    Multiset.induction_on s (fun _ => h₀) fun _a _s _ ih =>
      (h₁ _ _) fun _t h => ih _ <| lt_of_le_of_lt h <| lt_cons_self _ _

/-- Suppose that, given that `p t` can be defined on all supersets of `s` of cardinality less than
`n`, one knows how to define `p s`. Then one can inductively define `p s` for all multisets `s` of
cardinality less than `n`, starting from multisets of card `n` and iterating. This
can be used either to define data, or to prove properties. -/
def strongDownwardInduction {p : Multiset α → Sort*} {n : ℕ}
    (H : ∀ t₁, (∀ {t₂ : Multiset α}, card t₂ ≤ n → t₁ < t₂ → p t₂) → card t₁ ≤ n → p t₁)
    (s : Multiset α) :
    card s ≤ n → p s :=
  H s fun {t} ht _h =>
    strongDownwardInduction H t ht
termination_by n - card s
decreasing_by simp_wf; have := (card_lt_card _h); omega
-- Porting note: reorderd universes

theorem strongDownwardInduction_eq {p : Multiset α → Sort*} {n : ℕ}
    (H : ∀ t₁, (∀ {t₂ : Multiset α}, card t₂ ≤ n → t₁ < t₂ → p t₂) → card t₁ ≤ n → p t₁)
    (s : Multiset α) :
    strongDownwardInduction H s = H s fun ht _hst => strongDownwardInduction H _ ht := by
  rw [strongDownwardInduction]

/-- Analogue of `strongDownwardInduction` with order of arguments swapped. -/
@[elab_as_elim]
def strongDownwardInductionOn {p : Multiset α → Sort*} {n : ℕ} :
    ∀ s : Multiset α,
      (∀ t₁, (∀ {t₂ : Multiset α}, card t₂ ≤ n → t₁ < t₂ → p t₂) → card t₁ ≤ n → p t₁) →
        card s ≤ n → p s :=
  fun s H => strongDownwardInduction H s

theorem strongDownwardInductionOn_eq {p : Multiset α → Sort*} (s : Multiset α) {n : ℕ}
    (H : ∀ t₁, (∀ {t₂ : Multiset α}, card t₂ ≤ n → t₁ < t₂ → p t₂) → card t₁ ≤ n → p t₁) :
    s.strongDownwardInductionOn H = H s fun {t} ht _h => t.strongDownwardInductionOn H ht := by
  dsimp only [strongDownwardInductionOn]
  rw [strongDownwardInduction]

/-- Another way of expressing `strongInductionOn`: the `(<)` relation is well-founded. -/
instance instWellFoundedLT : WellFoundedLT (Multiset α) :=
  ⟨Subrelation.wf Multiset.card_lt_card (measure Multiset.card).2⟩

/-! ### `Multiset.replicate` -/

/-- `replicate n a` is the multiset containing only `a` with multiplicity `n`. -/
def replicate (n : ℕ) (a : α) : Multiset α :=
  List.replicate n a

theorem coe_replicate (n : ℕ) (a : α) : (List.replicate n a : Multiset α) = replicate n a := rfl

@[simp] theorem replicate_zero (a : α) : replicate 0 a = 0 := rfl

@[simp] theorem replicate_succ (a : α) (n) : replicate (n + 1) a = a ::ₘ replicate n a := rfl

theorem replicate_add (m n : ℕ) (a : α) : replicate (m + n) a = replicate m a + replicate n a :=
  congr_arg _ <| List.replicate_add ..

theorem replicate_one (a : α) : replicate 1 a = {a} := rfl

@[simp] theorem card_replicate (n) (a : α) : card (replicate n a) = n :=
  length_replicate n a

theorem mem_replicate {a b : α} {n : ℕ} : b ∈ replicate n a ↔ n ≠ 0 ∧ b = a :=
  List.mem_replicate

theorem eq_of_mem_replicate {a b : α} {n} : b ∈ replicate n a → b = a :=
  List.eq_of_mem_replicate

theorem eq_replicate_card {a : α} {s : Multiset α} : s = replicate (card s) a ↔ ∀ b ∈ s, b = a :=
  Quot.inductionOn s fun _l => coe_eq_coe.trans <| perm_replicate.trans eq_replicate_length

alias ⟨_, eq_replicate_of_mem⟩ := eq_replicate_card

theorem eq_replicate {a : α} {n} {s : Multiset α} :
    s = replicate n a ↔ card s = n ∧ ∀ b ∈ s, b = a :=
  ⟨fun h => h.symm ▸ ⟨card_replicate _ _, fun _b => eq_of_mem_replicate⟩,
    fun ⟨e, al⟩ => e ▸ eq_replicate_of_mem al⟩

theorem replicate_right_injective {n : ℕ} (hn : n ≠ 0) : Injective (@replicate α n) :=
  fun _ _ h => (eq_replicate.1 h).2 _ <| mem_replicate.2 ⟨hn, rfl⟩

@[simp] theorem replicate_right_inj {a b : α} {n : ℕ} (h : n ≠ 0) :
    replicate n a = replicate n b ↔ a = b :=
  (replicate_right_injective h).eq_iff

theorem replicate_left_injective (a : α) : Injective (replicate · a) :=
  -- Porting note: was `fun m n h => by rw [← (eq_replicate.1 h).1, card_replicate]`
  LeftInverse.injective (card_replicate · a)

theorem replicate_subset_singleton (n : ℕ) (a : α) : replicate n a ⊆ {a} :=
  List.replicate_subset_singleton n a

theorem replicate_le_coe {a : α} {n} {l : List α} : replicate n a ≤ l ↔ List.replicate n a <+ l :=
  ⟨fun ⟨_l', p, s⟩ => perm_replicate.1 p ▸ s, Sublist.subperm⟩

theorem replicate_le_replicate (a : α) {k n : ℕ} : replicate k a ≤ replicate n a ↔ k ≤ n :=
  _root_.trans (by rw [← replicate_le_coe, coe_replicate]) (List.replicate_sublist_replicate a)

@[gcongr]
theorem replicate_mono (a : α) {k n : ℕ} (h : k ≤ n) : replicate k a ≤ replicate n a :=
  (replicate_le_replicate a).2 h

theorem le_replicate_iff {m : Multiset α} {a : α} {n : ℕ} :
    m ≤ replicate n a ↔ ∃ k ≤ n, m = replicate k a :=
  ⟨fun h => ⟨card m, (card_mono h).trans_eq (card_replicate _ _),
      eq_replicate_card.2 fun _ hb => eq_of_mem_replicate <| subset_of_le h hb⟩,
    fun ⟨_, hkn, hm⟩ => hm.symm ▸ (replicate_le_replicate _).2 hkn⟩

theorem lt_replicate_succ {m : Multiset α} {x : α} {n : ℕ} :
    m < replicate (n + 1) x ↔ m ≤ replicate n x := by
  rw [lt_iff_cons_le]
  constructor
  · rintro ⟨x', hx'⟩
    have := eq_of_mem_replicate (mem_of_le hx' (mem_cons_self _ _))
    rwa [this, replicate_succ, cons_le_cons_iff] at hx'
  · intro h
    rw [replicate_succ]
    exact ⟨x, cons_le_cons _ h⟩

/-! ### Erasing one copy of an element -/

section Erase

variable [DecidableEq α] {s t : Multiset α} {a b : α}

/-- `erase s a` is the multiset that subtracts 1 from the multiplicity of `a`. -/
def erase (s : Multiset α) (a : α) : Multiset α :=
  Quot.liftOn s (fun l => (l.erase a : Multiset α)) fun _l₁ _l₂ p => Quot.sound (p.erase a)

@[simp]
theorem coe_erase (l : List α) (a : α) : erase (l : Multiset α) a = l.erase a :=
  rfl

@[simp]
theorem erase_zero (a : α) : (0 : Multiset α).erase a = 0 :=
  rfl

@[simp]
theorem erase_cons_head (a : α) (s : Multiset α) : (a ::ₘ s).erase a = s :=
  Quot.inductionOn s fun l => congr_arg _ <| List.erase_cons_head a l

@[simp]
theorem erase_cons_tail {a b : α} (s : Multiset α) (h : b ≠ a) :
    (b ::ₘ s).erase a = b ::ₘ s.erase a :=
  Quot.inductionOn s fun _ => congr_arg _ <| List.erase_cons_tail (not_beq_of_ne h)

@[simp]
theorem erase_singleton (a : α) : ({a} : Multiset α).erase a = 0 :=
  erase_cons_head a 0

@[simp]
theorem erase_of_not_mem {a : α} {s : Multiset α} : a ∉ s → s.erase a = s :=
  Quot.inductionOn s fun _l h => congr_arg _ <| List.erase_of_not_mem h

@[simp]
theorem cons_erase {s : Multiset α} {a : α} : a ∈ s → a ::ₘ s.erase a = s :=
  Quot.inductionOn s fun _l h => Quot.sound (perm_cons_erase h).symm

theorem erase_cons_tail_of_mem (h : a ∈ s) :
    (b ::ₘ s).erase a = b ::ₘ s.erase a := by
  rcases eq_or_ne a b with rfl | hab
  · simp [cons_erase h]
  · exact s.erase_cons_tail hab.symm

theorem le_cons_erase (s : Multiset α) (a : α) : s ≤ a ::ₘ s.erase a :=
  if h : a ∈ s then le_of_eq (cons_erase h).symm
  else by rw [erase_of_not_mem h]; apply le_cons_self

theorem add_singleton_eq_iff {s t : Multiset α} {a : α} : s + {a} = t ↔ a ∈ t ∧ s = t.erase a := by
  rw [Multiset.add_comm, singleton_add]
  constructor
  · rintro rfl
    exact ⟨s.mem_cons_self a, (s.erase_cons_head a).symm⟩
  · rintro ⟨h, rfl⟩
    exact cons_erase h

theorem erase_add_left_pos {a : α} {s : Multiset α} (t) : a ∈ s → (s + t).erase a = s.erase a + t :=
  Quotient.inductionOn₂ s t fun _l₁ l₂ h => congr_arg _ <| erase_append_left l₂ h

theorem erase_add_right_pos {a : α} (s) (h : a ∈ t) : (s + t).erase a = s + t.erase a := by
  rw [Multiset.add_comm, erase_add_left_pos s h, Multiset.add_comm]

theorem erase_add_right_neg {a : α} {s : Multiset α} (t) :
    a ∉ s → (s + t).erase a = s + t.erase a :=
  Quotient.inductionOn₂ s t fun _l₁ l₂ h => congr_arg _ <| erase_append_right l₂ h

theorem erase_add_left_neg {a : α} (s) (h : a ∉ t) : (s + t).erase a = s.erase a + t := by
  rw [Multiset.add_comm, erase_add_right_neg s h, Multiset.add_comm]

theorem erase_le (a : α) (s : Multiset α) : s.erase a ≤ s :=
  Quot.inductionOn s fun l => (erase_sublist a l).subperm

@[simp]
theorem erase_lt {a : α} {s : Multiset α} : s.erase a < s ↔ a ∈ s :=
  ⟨fun h => not_imp_comm.1 erase_of_not_mem (ne_of_lt h), fun h => by
    simpa [h] using lt_cons_self (s.erase a) a⟩

theorem erase_subset (a : α) (s : Multiset α) : s.erase a ⊆ s :=
  subset_of_le (erase_le a s)

theorem mem_erase_of_ne {a b : α} {s : Multiset α} (ab : a ≠ b) : a ∈ s.erase b ↔ a ∈ s :=
  Quot.inductionOn s fun _l => List.mem_erase_of_ne ab

theorem mem_of_mem_erase {a b : α} {s : Multiset α} : a ∈ s.erase b → a ∈ s :=
  mem_of_subset (erase_subset _ _)

theorem erase_comm (s : Multiset α) (a b : α) : (s.erase a).erase b = (s.erase b).erase a :=
  Quot.inductionOn s fun l => congr_arg _ <| l.erase_comm a b

instance : RightCommutative erase (α := α) := ⟨erase_comm⟩

@[gcongr]
theorem erase_le_erase {s t : Multiset α} (a : α) (h : s ≤ t) : s.erase a ≤ t.erase a :=
  leInductionOn h fun h => (h.erase _).subperm

theorem erase_le_iff_le_cons {s t : Multiset α} {a : α} : s.erase a ≤ t ↔ s ≤ a ::ₘ t :=
  ⟨fun h => le_trans (le_cons_erase _ _) (cons_le_cons _ h), fun h =>
    if m : a ∈ s then by rw [← cons_erase m] at h; exact (cons_le_cons_iff _).1 h
    else le_trans (erase_le _ _) ((le_cons_of_not_mem m).1 h)⟩

@[simp]
theorem card_erase_of_mem {a : α} {s : Multiset α} : a ∈ s → card (s.erase a) = pred (card s) :=
  Quot.inductionOn s fun _l => length_erase_of_mem

@[simp]
theorem card_erase_add_one {a : α} {s : Multiset α} : a ∈ s → card (s.erase a) + 1 = card s :=
  Quot.inductionOn s fun _l => length_erase_add_one

theorem card_erase_lt_of_mem {a : α} {s : Multiset α} : a ∈ s → card (s.erase a) < card s :=
  fun h => card_lt_card (erase_lt.mpr h)

theorem card_erase_le {a : α} {s : Multiset α} : card (s.erase a) ≤ card s :=
  card_le_card (erase_le a s)

theorem card_erase_eq_ite {a : α} {s : Multiset α} :
    card (s.erase a) = if a ∈ s then pred (card s) else card s := by
  by_cases h : a ∈ s
  · rwa [card_erase_of_mem h, if_pos]
  · rwa [erase_of_not_mem h, if_neg]

end Erase

@[simp]
theorem coe_reverse (l : List α) : (reverse l : Multiset α) = l :=
  Quot.sound <| reverse_perm _

/-! ### `Multiset.map` -/


/-- `map f s` is the lift of the list `map` operation. The multiplicity
  of `b` in `map f s` is the number of `a ∈ s` (counting multiplicity)
  such that `f a = b`. -/
def map (f : α → β) (s : Multiset α) : Multiset β :=
  Quot.liftOn s (fun l : List α => (l.map f : Multiset β)) fun _l₁ _l₂ p => Quot.sound (p.map f)

@[congr]
theorem map_congr {f g : α → β} {s t : Multiset α} :
    s = t → (∀ x ∈ t, f x = g x) → map f s = map g t := by
  rintro rfl h
  induction s using Quot.inductionOn
  exact congr_arg _ (List.map_congr_left h)

theorem map_hcongr {β' : Type v} {m : Multiset α} {f : α → β} {f' : α → β'} (h : β = β')
    (hf : ∀ a ∈ m, HEq (f a) (f' a)) : HEq (map f m) (map f' m) := by
  subst h; simp at hf
  simp [map_congr rfl hf]

theorem forall_mem_map_iff {f : α → β} {p : β → Prop} {s : Multiset α} :
    (∀ y ∈ s.map f, p y) ↔ ∀ x ∈ s, p (f x) :=
  Quotient.inductionOn' s fun _L => List.forall_mem_map

@[simp, norm_cast] lemma map_coe (f : α → β) (l : List α) : map f l = l.map f := rfl

@[simp]
theorem map_zero (f : α → β) : map f 0 = 0 :=
  rfl

@[simp]
theorem map_cons (f : α → β) (a s) : map f (a ::ₘ s) = f a ::ₘ map f s :=
  Quot.inductionOn s fun _l => rfl

theorem map_comp_cons (f : α → β) (t) : map f ∘ cons t = cons (f t) ∘ map f := by
  ext
  simp

@[simp]
theorem map_singleton (f : α → β) (a : α) : ({a} : Multiset α).map f = {f a} :=
  rfl

@[simp]
theorem map_replicate (f : α → β) (k : ℕ) (a : α) : (replicate k a).map f = replicate k (f a) := by
  simp only [← coe_replicate, map_coe, List.map_replicate]

@[simp]
theorem map_add (f : α → β) (s t) : map f (s + t) = map f s + map f t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => congr_arg _ <| map_append _ _ _

/-- If each element of `s : Multiset α` can be lifted to `β`, then `s` can be lifted to
`Multiset β`. -/
instance canLift (c) (p) [CanLift α β c p] :
    CanLift (Multiset α) (Multiset β) (map c) fun s => ∀ x ∈ s, p x where
  prf := by
    rintro ⟨l⟩ hl
    lift l to List β using hl
    exact ⟨l, map_coe _ _⟩

@[simp]
theorem mem_map {f : α → β} {b : β} {s : Multiset α} : b ∈ map f s ↔ ∃ a, a ∈ s ∧ f a = b :=
  Quot.inductionOn s fun _l => List.mem_map

@[simp]
theorem card_map (f : α → β) (s) : card (map f s) = card s :=
  Quot.inductionOn s fun _l => length_map _ _

@[simp]
theorem map_eq_zero {s : Multiset α} {f : α → β} : s.map f = 0 ↔ s = 0 := by
  rw [← Multiset.card_eq_zero, Multiset.card_map, Multiset.card_eq_zero]

theorem mem_map_of_mem (f : α → β) {a : α} {s : Multiset α} (h : a ∈ s) : f a ∈ map f s :=
  mem_map.2 ⟨_, h, rfl⟩

theorem map_eq_singleton {f : α → β} {s : Multiset α} {b : β} :
    map f s = {b} ↔ ∃ a : α, s = {a} ∧ f a = b := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ : ∃ a, s = {a} := by rw [← card_eq_one, ← card_map, h, card_singleton]
    refine ⟨a, ha, ?_⟩
    rw [← mem_singleton, ← h, ha, map_singleton, mem_singleton]
  · rintro ⟨a, rfl, rfl⟩
    simp

theorem map_eq_cons [DecidableEq α] (f : α → β) (s : Multiset α) (t : Multiset β) (b : β) :
    (∃ a ∈ s, f a = b ∧ (s.erase a).map f = t) ↔ s.map f = b ::ₘ t := by
  constructor
  · rintro ⟨a, ha, rfl, rfl⟩
    rw [← map_cons, Multiset.cons_erase ha]
  · intro h
    have : b ∈ s.map f := by
      rw [h]
      exact mem_cons_self _ _
    obtain ⟨a, h1, rfl⟩ := mem_map.mp this
    obtain ⟨u, rfl⟩ := exists_cons_of_mem h1
    rw [map_cons, cons_inj_right] at h
    refine ⟨a, mem_cons_self _ _, rfl, ?_⟩
    rw [Multiset.erase_cons_head, h]

-- The simpNF linter says that the LHS can be simplified via `Multiset.mem_map`.
-- However this is a higher priority lemma.
-- https://github.com/leanprover/std4/issues/207
@[simp 1100, nolint simpNF]
theorem mem_map_of_injective {f : α → β} (H : Function.Injective f) {a : α} {s : Multiset α} :
    f a ∈ map f s ↔ a ∈ s :=
  Quot.inductionOn s fun _l => List.mem_map_of_injective H

@[simp]
theorem map_map (g : β → γ) (f : α → β) (s : Multiset α) : map g (map f s) = map (g ∘ f) s :=
  Quot.inductionOn s fun _l => congr_arg _ <| List.map_map _ _ _

theorem map_id (s : Multiset α) : map id s = s :=
  Quot.inductionOn s fun _l => congr_arg _ <| List.map_id _

@[simp]
theorem map_id' (s : Multiset α) : map (fun x => x) s = s :=
  map_id s

-- Porting note: was a `simp` lemma in mathlib3
theorem map_const (s : Multiset α) (b : β) : map (const α b) s = replicate (card s) b :=
  Quot.inductionOn s fun _ => congr_arg _ <| List.map_const' _ _

-- Porting note: was not a `simp` lemma in mathlib3 because `Function.const` was reducible
@[simp] theorem map_const' (s : Multiset α) (b : β) : map (fun _ ↦ b) s = replicate (card s) b :=
  map_const _ _

theorem eq_of_mem_map_const {b₁ b₂ : β} {l : List α} (h : b₁ ∈ map (Function.const α b₂) l) :
    b₁ = b₂ :=
  eq_of_mem_replicate (n := card (l : Multiset α)) <| by rwa [map_const] at h

@[simp, gcongr]
theorem map_le_map {f : α → β} {s t : Multiset α} (h : s ≤ t) : map f s ≤ map f t :=
  leInductionOn h fun h => (h.map f).subperm

@[simp, gcongr]
theorem map_lt_map {f : α → β} {s t : Multiset α} (h : s < t) : s.map f < t.map f := by
  refine (map_le_map h.le).lt_of_not_le fun H => h.ne <| eq_of_le_of_card_le h.le ?_
  rw [← s.card_map f, ← t.card_map f]
  exact card_le_card H

theorem map_mono (f : α → β) : Monotone (map f) := fun _ _ => map_le_map

theorem map_strictMono (f : α → β) : StrictMono (map f) := fun _ _ => map_lt_map

@[simp, gcongr]
theorem map_subset_map {f : α → β} {s t : Multiset α} (H : s ⊆ t) : map f s ⊆ map f t := fun _b m =>
  let ⟨a, h, e⟩ := mem_map.1 m
  mem_map.2 ⟨a, H h, e⟩

theorem map_erase [DecidableEq α] [DecidableEq β] (f : α → β) (hf : Function.Injective f) (x : α)
    (s : Multiset α) : (s.erase x).map f = (s.map f).erase (f x) := by
  induction' s using Multiset.induction_on with y s ih
  · simp
  by_cases hxy : y = x
  · cases hxy
    simp
  · rw [s.erase_cons_tail hxy, map_cons, map_cons, (s.map f).erase_cons_tail (hf.ne hxy), ih]

theorem map_erase_of_mem [DecidableEq α] [DecidableEq β] (f : α → β)
    (s : Multiset α) {x : α} (h : x ∈ s) : (s.erase x).map f = (s.map f).erase (f x) := by
  induction' s using Multiset.induction_on with y s ih
  · simp
  rcases eq_or_ne y x with rfl | hxy
  · simp
  replace h : x ∈ s := by simpa [hxy.symm] using h
  rw [s.erase_cons_tail hxy, map_cons, map_cons, ih h, erase_cons_tail_of_mem (mem_map_of_mem f h)]

theorem map_surjective_of_surjective {f : α → β} (hf : Function.Surjective f) :
    Function.Surjective (map f) := by
  intro s
  induction' s using Multiset.induction_on with x s ih
  · exact ⟨0, map_zero _⟩
  · obtain ⟨y, rfl⟩ := hf x
    obtain ⟨t, rfl⟩ := ih
    exact ⟨y ::ₘ t, map_cons _ _ _⟩

/-! ### `Multiset.fold` -/


section foldl

/-- `foldl f H b s` is the lift of the list operation `foldl f b l`,
  which folds `f` over the multiset. It is well defined when `f` is right-commutative,
  that is, `f (f b a₁) a₂ = f (f b a₂) a₁`. -/
def foldl (f : β → α → β) [RightCommutative f] (b : β) (s : Multiset α) : β :=
  Quot.liftOn s (fun l => List.foldl f b l) fun _l₁ _l₂ p => p.foldl_eq b

variable (f : β → α → β) [RightCommutative f]

@[simp]
theorem foldl_zero (b) : foldl f b 0 = b :=
  rfl

@[simp]
theorem foldl_cons (b a s) : foldl f b (a ::ₘ s) = foldl f (f b a) s :=
  Quot.inductionOn s fun _l => rfl

@[simp]
theorem foldl_add (b s t) : foldl f b (s + t) = foldl f (foldl f b s) t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => foldl_append _ _ _ _

end foldl

section foldr

/-- `foldr f H b s` is the lift of the list operation `foldr f b l`,
  which folds `f` over the multiset. It is well defined when `f` is left-commutative,
  that is, `f a₁ (f a₂ b) = f a₂ (f a₁ b)`. -/
def foldr (f : α → β → β) [LeftCommutative f] (b : β) (s : Multiset α) : β :=
  Quot.liftOn s (fun l => List.foldr f b l) fun _l₁ _l₂ p => p.foldr_eq b

variable (f : α → β → β) [LeftCommutative f]

@[simp]
theorem foldr_zero (b) : foldr f b 0 = b :=
  rfl

@[simp]
theorem foldr_cons (b a s) : foldr f b (a ::ₘ s) = f a (foldr f b s) :=
  Quot.inductionOn s fun _l => rfl

@[simp]
theorem foldr_singleton (b a) : foldr f b ({a} : Multiset α) = f a b :=
  rfl

@[simp]
theorem foldr_add (b s t) : foldr f b (s + t) = foldr f (foldr f b t) s :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => foldr_append _ _ _ _

end foldr

@[simp]
theorem coe_foldr (f : α → β → β) [LeftCommutative f] (b : β) (l : List α) :
    foldr f b l = l.foldr f b :=
  rfl

@[simp]
theorem coe_foldl (f : β → α → β) [RightCommutative f] (b : β) (l : List α) :
    foldl f b l = l.foldl f b :=
  rfl

theorem coe_foldr_swap (f : α → β → β) [LeftCommutative f] (b : β) (l : List α) :
    foldr f b l = l.foldl (fun x y => f y x) b :=
  (congr_arg (foldr f b) (coe_reverse l)).symm.trans <| foldr_reverse _ _ _

theorem foldr_swap (f : α → β → β) [LeftCommutative f] (b : β) (s : Multiset α) :
    foldr f b s = foldl (fun x y => f y x) b s :=
  Quot.inductionOn s fun _l => coe_foldr_swap _ _ _

theorem foldl_swap (f : β → α → β) [RightCommutative f] (b : β) (s : Multiset α) :
    foldl f b s = foldr (fun x y => f y x) b s :=
  (foldr_swap _ _ _).symm

theorem foldr_induction' (f : α → β → β) [LeftCommutative f] (x : β) (q : α → Prop)
    (p : β → Prop) (s : Multiset α) (hpqf : ∀ a b, q a → p b → p (f a b)) (px : p x)
    (q_s : ∀ a ∈ s, q a) : p (foldr f x s) := by
  induction s using Multiset.induction with
  | empty => simpa
  | cons a s ihs =>
    simp only [forall_mem_cons, foldr_cons] at q_s ⊢
    exact hpqf _ _ q_s.1 (ihs q_s.2)

theorem foldr_induction (f : α → α → α) [LeftCommutative f] (x : α) (p : α → Prop)
    (s : Multiset α) (p_f : ∀ a b, p a → p b → p (f a b)) (px : p x) (p_s : ∀ a ∈ s, p a) :
    p (foldr f x s) :=
  foldr_induction' f x p p s p_f px p_s

theorem foldl_induction' (f : β → α → β) [RightCommutative f] (x : β) (q : α → Prop)
    (p : β → Prop) (s : Multiset α) (hpqf : ∀ a b, q a → p b → p (f b a)) (px : p x)
    (q_s : ∀ a ∈ s, q a) : p (foldl f x s) := by
  rw [foldl_swap]
  exact foldr_induction' (fun x y => f y x) x q p s hpqf px q_s

theorem foldl_induction (f : α → α → α) [RightCommutative f] (x : α) (p : α → Prop)
    (s : Multiset α) (p_f : ∀ a b, p a → p b → p (f b a)) (px : p x) (p_s : ∀ a ∈ s, p a) :
    p (foldl f x s) :=
  foldl_induction' f x p p s p_f px p_s

/-! ### Map for partial functions -/


/-- Lift of the list `pmap` operation. Map a partial function `f` over a multiset
  `s` whose elements are all in the domain of `f`. -/
nonrec def pmap {p : α → Prop} (f : ∀ a, p a → β) (s : Multiset α) : (∀ a ∈ s, p a) → Multiset β :=
  Quot.recOn s (fun l H => ↑(pmap f l H)) fun l₁ l₂ (pp : l₁ ~ l₂) =>
    funext fun H₂ : ∀ a ∈ l₂, p a =>
      have H₁ : ∀ a ∈ l₁, p a := fun a h => H₂ a (pp.subset h)
      have : ∀ {s₂ e H}, @Eq.ndrec (Multiset α) l₁ (fun s => (∀ a ∈ s, p a) → Multiset β)
          (fun _ => ↑(pmap f l₁ H₁)) s₂ e H = ↑(pmap f l₁ H₁) := by
        intro s₂ e _; subst e; rfl
      this.trans <| Quot.sound <| pp.pmap f

@[simp]
theorem coe_pmap {p : α → Prop} (f : ∀ a, p a → β) (l : List α) (H : ∀ a ∈ l, p a) :
    pmap f l H = l.pmap f H :=
  rfl

@[simp]
theorem pmap_zero {p : α → Prop} (f : ∀ a, p a → β) (h : ∀ a ∈ (0 : Multiset α), p a) :
    pmap f 0 h = 0 :=
  rfl

@[simp]
theorem pmap_cons {p : α → Prop} (f : ∀ a, p a → β) (a : α) (m : Multiset α) :
    ∀ h : ∀ b ∈ a ::ₘ m, p b,
      pmap f (a ::ₘ m) h =
        f a (h a (mem_cons_self a m)) ::ₘ pmap f m fun a ha => h a <| mem_cons_of_mem ha :=
  Quotient.inductionOn m fun _l _h => rfl

/-- "Attach" a proof that `a ∈ s` to each element `a` in `s` to produce
  a multiset on `{x // x ∈ s}`. -/
def attach (s : Multiset α) : Multiset { x // x ∈ s } :=
  pmap Subtype.mk s fun _a => id

@[simp]
theorem coe_attach (l : List α) : @Eq (Multiset { x // x ∈ l }) (@attach α l) l.attach :=
  rfl

set_option linter.deprecated false in
@[deprecated "Deprecated without replacement." (since := "2025-02-07")]
theorem sizeOf_lt_sizeOf_of_mem [SizeOf α] {x : α} {s : Multiset α} (hx : x ∈ s) :
    SizeOf.sizeOf x < SizeOf.sizeOf s := by
  induction' s using Quot.inductionOn with l a b
  exact List.sizeOf_lt_sizeOf_of_mem hx

theorem pmap_eq_map (p : α → Prop) (f : α → β) (s : Multiset α) :
    ∀ H, @pmap _ _ p (fun a _ => f a) s H = map f s :=
  Quot.inductionOn s fun l H => congr_arg _ <| List.pmap_eq_map p f l H

theorem pmap_congr {p q : α → Prop} {f : ∀ a, p a → β} {g : ∀ a, q a → β} (s : Multiset α) :
    ∀ {H₁ H₂}, (∀ a ∈ s, ∀ (h₁ h₂), f a h₁ = g a h₂) → pmap f s H₁ = pmap g s H₂ :=
  @(Quot.inductionOn s (fun l _H₁ _H₂ h => congr_arg _ <| List.pmap_congr_left l h))

theorem map_pmap {p : α → Prop} (g : β → γ) (f : ∀ a, p a → β) (s) :
    ∀ H, map g (pmap f s H) = pmap (fun a h => g (f a h)) s H :=
  Quot.inductionOn s fun l H => congr_arg _ <| List.map_pmap g f l H

theorem pmap_eq_map_attach {p : α → Prop} (f : ∀ a, p a → β) (s) :
    ∀ H, pmap f s H = s.attach.map fun x => f x.1 (H _ x.2) :=
  Quot.inductionOn s fun l H => congr_arg _ <| List.pmap_eq_map_attach f l H

-- @[simp] -- Porting note: Left hand does not simplify
theorem attach_map_val' (s : Multiset α) (f : α → β) : (s.attach.map fun i => f i.val) = s.map f :=
  Quot.inductionOn s fun l => congr_arg _ <| List.attach_map_coe l f

@[simp]
theorem attach_map_val (s : Multiset α) : s.attach.map Subtype.val = s :=
  (attach_map_val' _ _).trans s.map_id

@[simp]
theorem mem_attach (s : Multiset α) : ∀ x, x ∈ s.attach :=
  Quot.inductionOn s fun _l => List.mem_attach _

@[simp]
theorem mem_pmap {p : α → Prop} {f : ∀ a, p a → β} {s H b} :
    b ∈ pmap f s H ↔ ∃ (a : _) (h : a ∈ s), f a (H a h) = b :=
  Quot.inductionOn s (fun _l _H => List.mem_pmap) H

@[simp]
theorem card_pmap {p : α → Prop} (f : ∀ a, p a → β) (s H) : card (pmap f s H) = card s :=
  Quot.inductionOn s (fun _l _H => length_pmap) H

@[simp]
theorem card_attach {m : Multiset α} : card (attach m) = card m :=
  card_pmap _ _ _

@[simp]
theorem attach_zero : (0 : Multiset α).attach = 0 :=
  rfl

theorem attach_cons (a : α) (m : Multiset α) :
    (a ::ₘ m).attach =
      ⟨a, mem_cons_self a m⟩ ::ₘ m.attach.map fun p => ⟨p.1, mem_cons_of_mem p.2⟩ :=
  Quotient.inductionOn m fun l =>
    congr_arg _ <|
      congr_arg (List.cons _) <| by
        rw [List.map_pmap]; exact List.pmap_congr_left _ fun _ _ _ _ => Subtype.eq rfl

section DecidablePiExists

variable {m : Multiset α}

/-- If `p` is a decidable predicate,
so is the predicate that all elements of a multiset satisfy `p`. -/
protected def decidableForallMultiset {p : α → Prop} [∀ a, Decidable (p a)] :
    Decidable (∀ a ∈ m, p a) :=
  Quotient.recOnSubsingleton m fun l => decidable_of_iff (∀ a ∈ l, p a) <| by simp

instance decidableDforallMultiset {p : ∀ a ∈ m, Prop} [_hp : ∀ (a) (h : a ∈ m), Decidable (p a h)] :
    Decidable (∀ (a) (h : a ∈ m), p a h) :=
  @decidable_of_iff _ _
    (Iff.intro (fun h a ha => h ⟨a, ha⟩ (mem_attach _ _)) fun h ⟨_a, _ha⟩ _ => h _ _)
    (@Multiset.decidableForallMultiset _ m.attach (fun a => p a.1 a.2) _)

/-- decidable equality for functions whose domain is bounded by multisets -/
instance decidableEqPiMultiset {β : α → Type*} [∀ a, DecidableEq (β a)] :
    DecidableEq (∀ a ∈ m, β a) := fun f g =>
  decidable_of_iff (∀ (a) (h : a ∈ m), f a h = g a h) (by simp [funext_iff])

/-- If `p` is a decidable predicate,
so is the existence of an element in a multiset satisfying `p`. -/
protected def decidableExistsMultiset {p : α → Prop} [DecidablePred p] : Decidable (∃ x ∈ m, p x) :=
  Quotient.recOnSubsingleton m fun l => decidable_of_iff (∃ a ∈ l, p a) <| by simp

instance decidableDexistsMultiset {p : ∀ a ∈ m, Prop} [_hp : ∀ (a) (h : a ∈ m), Decidable (p a h)] :
    Decidable (∃ (a : _) (h : a ∈ m), p a h) :=
  @decidable_of_iff _ _
    (Iff.intro (fun ⟨⟨a, ha₁⟩, _, ha₂⟩ => ⟨a, ha₁, ha₂⟩) fun ⟨a, ha₁, ha₂⟩ =>
      ⟨⟨a, ha₁⟩, mem_attach _ _, ha₂⟩)
    (@Multiset.decidableExistsMultiset { a // a ∈ m } m.attach (fun a => p a.1 a.2) _)

end DecidablePiExists

/-! ### `Multiset.filter` -/


section

variable (p : α → Prop) [DecidablePred p]

/-- `Filter p s` returns the elements in `s` (with the same multiplicities)
  which satisfy `p`, and removes the rest. -/
def filter (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (List.filter p l : Multiset α)) fun _l₁ _l₂ h => Quot.sound <| h.filter p

@[simp, norm_cast] lemma filter_coe (l : List α) : filter p l = l.filter p := rfl

@[simp]
theorem filter_zero : filter p 0 = 0 :=
  rfl

@[congr]
theorem filter_congr {p q : α → Prop} [DecidablePred p] [DecidablePred q] {s : Multiset α} :
    (∀ x ∈ s, p x ↔ q x) → filter p s = filter q s :=
  Quot.inductionOn s fun _l h => congr_arg ofList <| List.filter_congr <| by simpa using h

@[simp]
theorem filter_add (s t : Multiset α) : filter p (s + t) = filter p s + filter p t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => congr_arg ofList <| filter_append _ _

@[simp]
theorem filter_le (s : Multiset α) : filter p s ≤ s :=
  Quot.inductionOn s fun _l => (filter_sublist _).subperm

@[simp]
theorem filter_subset (s : Multiset α) : filter p s ⊆ s :=
  subset_of_le <| filter_le _ _

@[gcongr]
theorem filter_le_filter {s t} (h : s ≤ t) : filter p s ≤ filter p t :=
  leInductionOn h fun h => (h.filter (p ·)).subperm

theorem monotone_filter_left : Monotone (filter p) := fun _s _t => filter_le_filter p

theorem monotone_filter_right (s : Multiset α) ⦃p q : α → Prop⦄ [DecidablePred p] [DecidablePred q]
    (h : ∀ b, p b → q b) :
    s.filter p ≤ s.filter q :=
  Quotient.inductionOn s fun l => (l.monotone_filter_right <| by simpa using h).subperm

variable {p}

@[simp]
theorem filter_cons_of_pos {a : α} (s) : p a → filter p (a ::ₘ s) = a ::ₘ filter p s :=
  Quot.inductionOn s fun _ h => congr_arg ofList <| List.filter_cons_of_pos <| by simpa using h

@[simp]
theorem filter_cons_of_neg {a : α} (s) : ¬p a → filter p (a ::ₘ s) = filter p s :=
  Quot.inductionOn s fun _ h => congr_arg ofList <| List.filter_cons_of_neg <| by simpa using h

@[simp]
theorem mem_filter {a : α} {s} : a ∈ filter p s ↔ a ∈ s ∧ p a :=
  Quot.inductionOn s fun _l => by simp

theorem of_mem_filter {a : α} {s} (h : a ∈ filter p s) : p a :=
  (mem_filter.1 h).2

theorem mem_of_mem_filter {a : α} {s} (h : a ∈ filter p s) : a ∈ s :=
  (mem_filter.1 h).1

theorem mem_filter_of_mem {a : α} {l} (m : a ∈ l) (h : p a) : a ∈ filter p l :=
  mem_filter.2 ⟨m, h⟩

theorem filter_eq_self {s} : filter p s = s ↔ ∀ a ∈ s, p a :=
  Quot.inductionOn s fun _l =>
    Iff.trans ⟨fun h => (filter_sublist _).eq_of_length (congr_arg card h),
      congr_arg ofList⟩ <| by simp

theorem filter_eq_nil {s} : filter p s = 0 ↔ ∀ a ∈ s, ¬p a :=
  Quot.inductionOn s fun _l =>
    Iff.trans ⟨fun h => eq_nil_of_length_eq_zero (congr_arg card h), congr_arg ofList⟩ (by simp)

theorem le_filter {s t} : s ≤ filter p t ↔ s ≤ t ∧ ∀ a ∈ s, p a :=
  ⟨fun h => ⟨le_trans h (filter_le _ _), fun _a m => of_mem_filter (mem_of_le h m)⟩, fun ⟨h, al⟩ =>
    filter_eq_self.2 al ▸ filter_le_filter p h⟩

theorem filter_cons {a : α} (s : Multiset α) :
    filter p (a ::ₘ s) = (if p a then {a} else 0) + filter p s := by
  split_ifs with h
  · rw [filter_cons_of_pos _ h, singleton_add]
  · rw [filter_cons_of_neg _ h, Multiset.zero_add]

theorem filter_singleton {a : α} (p : α → Prop) [DecidablePred p] :
    filter p {a} = if p a then {a} else ∅ := by
  simp only [singleton, filter_cons, filter_zero, Multiset.add_zero, empty_eq_zero]

variable (p)

@[simp]
theorem filter_filter (q) [DecidablePred q] (s : Multiset α) :
    filter p (filter q s) = filter (fun a => p a ∧ q a) s :=
  Quot.inductionOn s fun l => by simp

lemma filter_comm (q) [DecidablePred q] (s : Multiset α) :
    filter p (filter q s) = filter q (filter p s) := by simp [and_comm]

theorem filter_add_filter (q) [DecidablePred q] (s : Multiset α) :
    filter p s + filter q s = filter (fun a => p a ∨ q a) s + filter (fun a => p a ∧ q a) s :=
  Multiset.induction_on s rfl fun a s IH => by by_cases p a <;> by_cases q a <;> simp [*]

theorem filter_add_not (s : Multiset α) : filter p s + filter (fun a => ¬p a) s = s := by
  rw [filter_add_filter, filter_eq_self.2, filter_eq_nil.2]
  · simp only [Multiset.add_zero]
  · simp [Decidable.em, -Bool.not_eq_true, -not_and, not_and_or, or_comm]
  · simp only [Bool.not_eq_true, decide_eq_true_eq, Bool.eq_false_or_eq_true,
      decide_true, implies_true, Decidable.em]

theorem filter_map (f : β → α) (s : Multiset β) : filter p (map f s) = map f (filter (p ∘ f) s) :=
  Quot.inductionOn s fun l => by simp [List.filter_map]; rfl

-- TODO: rename to `map_filter` when the deprecated alias above is removed.
lemma map_filter' {f : α → β} (hf : Injective f) (s : Multiset α)
    [DecidablePred fun b => ∃ a, p a ∧ f a = b] :
    (s.filter p).map f = (s.map f).filter fun b => ∃ a, p a ∧ f a = b := by
  simp [comp_def, filter_map, hf.eq_iff]

lemma card_filter_le_iff (s : Multiset α) (P : α → Prop) [DecidablePred P] (n : ℕ) :
    card (s.filter P) ≤ n ↔ ∀ s' ≤ s, n < card s' → ∃ a ∈ s', ¬ P a := by
  fconstructor
  · intro H s' hs' s'_card
    by_contra! rid
    have card := card_le_card (monotone_filter_left P hs') |>.trans H
    exact s'_card.not_le (filter_eq_self.mpr rid ▸ card)
  · contrapose!
    exact fun H ↦ ⟨s.filter P, filter_le _ _, H, fun a ha ↦ (mem_filter.mp ha).2⟩

/-! ### Simultaneously filter and map elements of a multiset -/


/-- `filterMap f s` is a combination filter/map operation on `s`.
  The function `f : α → Option β` is applied to each element of `s`;
  if `f a` is `some b` then `b` is added to the result, otherwise
  `a` is removed from the resulting multiset. -/
def filterMap (f : α → Option β) (s : Multiset α) : Multiset β :=
  Quot.liftOn s (fun l => (List.filterMap f l : Multiset β))
    fun _l₁ _l₂ h => Quot.sound <| h.filterMap f

@[simp, norm_cast]
lemma filterMap_coe (f : α → Option β) (l : List α) : filterMap f l = l.filterMap f := rfl

@[simp]
theorem filterMap_zero (f : α → Option β) : filterMap f 0 = 0 :=
  rfl

@[simp]
theorem filterMap_cons_none {f : α → Option β} (a : α) (s : Multiset α) (h : f a = none) :
    filterMap f (a ::ₘ s) = filterMap f s :=
  Quot.inductionOn s fun _ => congr_arg ofList <| List.filterMap_cons_none h

@[simp]
theorem filterMap_cons_some (f : α → Option β) (a : α) (s : Multiset α) {b : β}
    (h : f a = some b) : filterMap f (a ::ₘ s) = b ::ₘ filterMap f s :=
  Quot.inductionOn s fun _ => congr_arg ofList <| List.filterMap_cons_some h

theorem filterMap_eq_map (f : α → β) : filterMap (some ∘ f) = map f :=
  funext fun s =>
    Quot.inductionOn s fun l => congr_arg ofList <| congr_fun (List.filterMap_eq_map f) l

theorem filterMap_eq_filter : filterMap (Option.guard p) = filter p :=
  funext fun s =>
    Quot.inductionOn s fun l => congr_arg ofList <| by
      rw [← List.filterMap_eq_filter]
      congr; funext a; simp

theorem filterMap_filterMap (f : α → Option β) (g : β → Option γ) (s : Multiset α) :
    filterMap g (filterMap f s) = filterMap (fun x => (f x).bind g) s :=
  Quot.inductionOn s fun l => congr_arg ofList <| List.filterMap_filterMap f g l

theorem map_filterMap (f : α → Option β) (g : β → γ) (s : Multiset α) :
    map g (filterMap f s) = filterMap (fun x => (f x).map g) s :=
  Quot.inductionOn s fun l => congr_arg ofList <| List.map_filterMap f g l

theorem filterMap_map (f : α → β) (g : β → Option γ) (s : Multiset α) :
    filterMap g (map f s) = filterMap (g ∘ f) s :=
  Quot.inductionOn s fun l => congr_arg ofList <| List.filterMap_map f g l

theorem filter_filterMap (f : α → Option β) (p : β → Prop) [DecidablePred p] (s : Multiset α) :
    filter p (filterMap f s) = filterMap (fun x => (f x).filter p) s :=
  Quot.inductionOn s fun l => congr_arg ofList <| List.filter_filterMap f p l

theorem filterMap_filter (f : α → Option β) (s : Multiset α) :
    filterMap f (filter p s) = filterMap (fun x => if p x then f x else none) s :=
  Quot.inductionOn s fun l => congr_arg ofList <| by simpa using List.filterMap_filter p f l

@[simp]
theorem filterMap_some (s : Multiset α) : filterMap some s = s :=
  Quot.inductionOn s fun l => congr_arg ofList <| List.filterMap_some l

@[simp]
theorem mem_filterMap (f : α → Option β) (s : Multiset α) {b : β} :
    b ∈ filterMap f s ↔ ∃ a, a ∈ s ∧ f a = some b :=
  Quot.inductionOn s fun _ => List.mem_filterMap

theorem map_filterMap_of_inv (f : α → Option β) (g : β → α) (H : ∀ x : α, (f x).map g = some x)
    (s : Multiset α) : map g (filterMap f s) = s :=
  Quot.inductionOn s fun l => congr_arg ofList <| List.map_filterMap_of_inv f g H l

@[gcongr]
theorem filterMap_le_filterMap (f : α → Option β) {s t : Multiset α} (h : s ≤ t) :
    filterMap f s ≤ filterMap f t :=
  leInductionOn h fun h => (h.filterMap _).subperm

/-! ### countP -/


/-- `countP p s` counts the number of elements of `s` (with multiplicity) that
  satisfy `p`. -/
def countP (s : Multiset α) : ℕ :=
  Quot.liftOn s (List.countP p) fun _l₁ _l₂ => Perm.countP_eq (p ·)

@[simp]
theorem coe_countP (l : List α) : countP p l = l.countP p :=
  rfl

@[simp]
theorem countP_zero : countP p 0 = 0 :=
  rfl

variable {p}

@[simp]
theorem countP_cons_of_pos {a : α} (s) : p a → countP p (a ::ₘ s) = countP p s + 1 :=
  Quot.inductionOn s <| by simpa using List.countP_cons_of_pos (p ·)

@[simp]
theorem countP_cons_of_neg {a : α} (s) : ¬p a → countP p (a ::ₘ s) = countP p s :=
  Quot.inductionOn s <| by simpa using List.countP_cons_of_neg (p ·)

variable (p)

theorem countP_cons (b : α) (s) : countP p (b ::ₘ s) = countP p s + if p b then 1 else 0 :=
  Quot.inductionOn s <| by simp [List.countP_cons]

theorem countP_eq_card_filter (s) : countP p s = card (filter p s) :=
  Quot.inductionOn s fun l => l.countP_eq_length_filter (p ·)

theorem countP_le_card (s) : countP p s ≤ card s :=
  Quot.inductionOn s fun _l => countP_le_length (p ·)

@[simp]
theorem countP_add (s t) : countP p (s + t) = countP p s + countP p t := by
  simp [countP_eq_card_filter]

theorem card_eq_countP_add_countP (s) : card s = countP p s + countP (fun x => ¬p x) s :=
  Quot.inductionOn s fun l => by simp [l.length_eq_countP_add_countP p]

@[gcongr]
theorem countP_le_of_le {s t} (h : s ≤ t) : countP p s ≤ countP p t := by
  simpa [countP_eq_card_filter] using card_le_card (filter_le_filter p h)

@[simp]
theorem countP_filter (q) [DecidablePred q] (s : Multiset α) :
    countP p (filter q s) = countP (fun a => p a ∧ q a) s := by simp [countP_eq_card_filter]

theorem countP_eq_countP_filter_add (s) (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    countP p s = (filter q s).countP p + (filter (fun a => ¬q a) s).countP p :=
  Quot.inductionOn s fun l => by
    convert l.countP_eq_countP_filter_add (p ·) (q ·)
    simp [countP_filter]

@[simp]
theorem countP_True {s : Multiset α} : countP (fun _ => True) s = card s :=
  Quot.inductionOn s fun _l => congrFun List.countP_true _

@[simp]
theorem countP_False {s : Multiset α} : countP (fun _ => False) s = 0 :=
  Quot.inductionOn s fun _l => congrFun List.countP_false _

theorem countP_map (f : α → β) (s : Multiset α) (p : β → Prop) [DecidablePred p] :
    countP p (map f s) = card (s.filter fun a => p (f a)) := by
  refine Multiset.induction_on s ?_ fun a t IH => ?_
  · rw [map_zero, countP_zero, filter_zero, card_zero]
  · rw [map_cons, countP_cons, IH, filter_cons, card_add, apply_ite card, card_zero, card_singleton,
      Nat.add_comm]

-- Porting note: `Lean.Internal.coeM` forces us to type-ascript `{a // a ∈ s}`
lemma countP_attach (s : Multiset α) : s.attach.countP (fun a : {a // a ∈ s} ↦ p a) = s.countP p :=
  Quotient.inductionOn s fun l => by
    simp only [quot_mk_to_coe, coe_countP]
    -- Porting note: was
    -- rw [quot_mk_to_coe, coe_attach, coe_countP]
    -- exact List.countP_attach _ _
    rw [coe_attach]
    refine (coe_countP _ _).trans ?_
    convert List.countP_attach _ _
    rfl

lemma filter_attach (s : Multiset α) (p : α → Prop) [DecidablePred p] :
    (s.attach.filter fun a : {a // a ∈ s} ↦ p ↑a) =
      (s.filter p).attach.map (Subtype.map id fun _ ↦ Multiset.mem_of_mem_filter) :=
  Quotient.inductionOn s fun l ↦ congr_arg _ (List.filter_attach l p)

variable {p}

theorem countP_pos {s} : 0 < countP p s ↔ ∃ a ∈ s, p a :=
  Quot.inductionOn s fun _l => by simp

theorem countP_eq_zero {s} : countP p s = 0 ↔ ∀ a ∈ s, ¬p a :=
  Quot.inductionOn s fun _l => by simp [List.countP_eq_zero]

theorem countP_eq_card {s} : countP p s = card s ↔ ∀ a ∈ s, p a :=
  Quot.inductionOn s fun _l => by simp [List.countP_eq_length]

theorem countP_pos_of_mem {s a} (h : a ∈ s) (pa : p a) : 0 < countP p s :=
  countP_pos.2 ⟨_, h, pa⟩

@[congr]
theorem countP_congr {s s' : Multiset α} (hs : s = s')
    {p p' : α → Prop} [DecidablePred p] [DecidablePred p']
    (hp : ∀ x ∈ s, p x = p' x) : s.countP p = s'.countP p' := by
  revert hs hp
  exact Quot.induction_on₂ s s'
    (fun l l' hs hp => by
      simp only [quot_mk_to_coe'', coe_eq_coe] at hs
      apply hs.countP_congr
      simpa using hp)

end

/-! ### Multiplicity of an element -/


section

variable [DecidableEq α] {s t u : Multiset α}

/-- `count a s` is the multiplicity of `a` in `s`. -/
def count (a : α) : Multiset α → ℕ :=
  countP (a = ·)

@[simp]
theorem coe_count (a : α) (l : List α) : count a (ofList l) = l.count a := by
  simp_rw [count, List.count, coe_countP (a = ·) l, @eq_comm _ a]
  rfl

@[simp]
theorem count_zero (a : α) : count a 0 = 0 :=
  rfl

@[simp]
theorem count_cons_self (a : α) (s : Multiset α) : count a (a ::ₘ s) = count a s + 1 :=
  countP_cons_of_pos _ <| rfl

@[simp]
theorem count_cons_of_ne {a b : α} (h : a ≠ b) (s : Multiset α) : count a (b ::ₘ s) = count a s :=
  countP_cons_of_neg _ <| h

theorem count_le_card (a : α) (s) : count a s ≤ card s :=
  countP_le_card _ _

@[gcongr]
theorem count_le_of_le (a : α) {s t} : s ≤ t → count a s ≤ count a t :=
  countP_le_of_le _

theorem count_le_count_cons (a b : α) (s : Multiset α) : count a s ≤ count a (b ::ₘ s) :=
  count_le_of_le _ (le_cons_self _ _)

theorem count_cons (a b : α) (s : Multiset α) :
    count a (b ::ₘ s) = count a s + if a = b then 1 else 0 :=
  countP_cons (a = ·) _ _

theorem count_singleton_self (a : α) : count a ({a} : Multiset α) = 1 :=
  count_eq_one_of_mem (nodup_singleton a) <| mem_singleton_self a

theorem count_singleton (a b : α) : count a ({b} : Multiset α) = if a = b then 1 else 0 := by
  simp only [count_cons, ← cons_zero, count_zero, Nat.zero_add]

@[simp]
theorem count_add (a : α) : ∀ s t, count a (s + t) = count a s + count a t :=
  countP_add _

@[simp]
lemma count_attach (a : {x // x ∈ s}) : s.attach.count a = s.count ↑a :=
  Eq.trans (countP_congr rfl fun _ _ => by simp [Subtype.ext_iff]) <| countP_attach _ _

theorem count_pos {a : α} {s : Multiset α} : 0 < count a s ↔ a ∈ s := by simp [count, countP_pos]

theorem one_le_count_iff_mem {a : α} {s : Multiset α} : 1 ≤ count a s ↔ a ∈ s := by
  rw [succ_le_iff, count_pos]

@[simp]
theorem count_eq_zero_of_not_mem {a : α} {s : Multiset α} (h : a ∉ s) : count a s = 0 :=
  by_contradiction fun h' => h <| count_pos.1 (Nat.pos_of_ne_zero h')

lemma count_ne_zero {a : α} : count a s ≠ 0 ↔ a ∈ s := Nat.pos_iff_ne_zero.symm.trans count_pos

@[simp] lemma count_eq_zero {a : α} : count a s = 0 ↔ a ∉ s := count_ne_zero.not_right

theorem count_eq_card {a : α} {s} : count a s = card s ↔ ∀ x ∈ s, a = x := by
  simp [countP_eq_card, count, @eq_comm _ a]

@[simp]
theorem count_replicate_self (a : α) (n : ℕ) : count a (replicate n a) = n := by
  convert List.count_replicate_self a n
  rw [← coe_count, coe_replicate]

theorem count_replicate (a b : α) (n : ℕ) : count a (replicate n b) = if b = a then n else 0 := by
  convert List.count_replicate a b n
  · rw [← coe_count, coe_replicate]
  · simp

@[simp]
theorem count_erase_self (a : α) (s : Multiset α) : count a (erase s a) = count a s - 1 :=
  Quotient.inductionOn s fun l => by
    convert List.count_erase_self a l <;> rw [← coe_count] <;> simp

@[simp]
theorem count_erase_of_ne {a b : α} (ab : a ≠ b) (s : Multiset α) :
    count a (erase s b) = count a s :=
  Quotient.inductionOn s fun l => by
    convert List.count_erase_of_ne ab l <;> rw [← coe_count] <;> simp

theorem le_count_iff_replicate_le {a : α} {s : Multiset α} {n : ℕ} :
    n ≤ count a s ↔ replicate n a ≤ s :=
  Quot.inductionOn s fun _l => by
    simp only [quot_mk_to_coe'', mem_coe, coe_count]
    exact le_count_iff_replicate_sublist.trans replicate_le_coe.symm

@[simp]
theorem count_filter_of_pos {p} [DecidablePred p] {a} {s : Multiset α} (h : p a) :
    count a (filter p s) = count a s :=
  Quot.inductionOn s fun _l => by
    simp only [quot_mk_to_coe'', filter_coe, mem_coe, coe_count, decide_eq_true_eq]
    apply count_filter
    simpa using h

@[simp]
theorem count_filter_of_neg {p} [DecidablePred p] {a} {s : Multiset α} (h : ¬p a) :
    count a (filter p s) = 0 :=
  Multiset.count_eq_zero_of_not_mem fun t => h (of_mem_filter t)

theorem count_filter {p} [DecidablePred p] {a} {s : Multiset α} :
    count a (filter p s) = if p a then count a s else 0 := by
  split_ifs with h
  · exact count_filter_of_pos h
  · exact count_filter_of_neg h

theorem ext {s t : Multiset α} : s = t ↔ ∀ a, count a s = count a t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => Quotient.eq.trans <| by
    simp only [quot_mk_to_coe, filter_coe, mem_coe, coe_count, decide_eq_true_eq]
    apply perm_iff_count

@[ext]
theorem ext' {s t : Multiset α} : (∀ a, count a s = count a t) → s = t :=
  ext.2

lemma count_injective : Injective fun (s : Multiset α) a ↦ s.count a :=
  fun _s _t hst ↦ ext' <| congr_fun hst

theorem le_iff_count {s t : Multiset α} : s ≤ t ↔ ∀ a, count a s ≤ count a t :=
  Quotient.inductionOn₂ s t fun _ _ ↦ by simp [subperm_iff_count]

theorem count_map {α β : Type*} (f : α → β) (s : Multiset α) [DecidableEq β] (b : β) :
    count b (map f s) = card (s.filter fun a => b = f a) := by
  simp [Bool.beq_eq_decide_eq, eq_comm, count, countP_map]

/-- `Multiset.map f` preserves `count` if `f` is injective on the set of elements contained in
the multiset -/
theorem count_map_eq_count [DecidableEq β] (f : α → β) (s : Multiset α)
    (hf : Set.InjOn f { x : α | x ∈ s }) (x) (H : x ∈ s) : (s.map f).count (f x) = s.count x := by
  suffices (filter (fun a : α => f x = f a) s).count x = card (filter (fun a : α => f x = f a) s) by
    rw [count, countP_map, ← this]
    exact count_filter_of_pos <| rfl
  · rw [eq_replicate_card.2 fun b hb => (hf H (mem_filter.1 hb).left _).symm]
    · simp only [count_replicate, eq_self_iff_true, if_true, card_replicate]
    · simp only [mem_filter, beq_iff_eq, and_imp, @eq_comm _ (f x), imp_self, implies_true]

/-- `Multiset.map f` preserves `count` if `f` is injective -/
theorem count_map_eq_count' [DecidableEq β] (f : α → β) (s : Multiset α) (hf : Function.Injective f)
    (x : α) : (s.map f).count (f x) = s.count x := by
  by_cases H : x ∈ s
  · exact count_map_eq_count f _ hf.injOn _ H
  · rw [count_eq_zero_of_not_mem H, count_eq_zero, mem_map]
    rintro ⟨k, hks, hkx⟩
    rw [hf hkx] at hks
    contradiction

theorem filter_eq' (s : Multiset α) (b : α) : s.filter (· = b) = replicate (count b s) b :=
  Quotient.inductionOn s fun l => by
    simp only [quot_mk_to_coe, filter_coe, mem_coe, coe_count]
    rw [List.filter_eq l b, coe_replicate]

theorem filter_eq (s : Multiset α) (b : α) : s.filter (Eq b) = replicate (count b s) b := by
  simp_rw [← filter_eq', eq_comm]

lemma erase_attach_map_val (s : Multiset α) (x : {x // x ∈ s}) :
    (s.attach.erase x).map (↑) = s.erase x := by
  rw [Multiset.map_erase _ val_injective, attach_map_val]

lemma erase_attach_map (s : Multiset α) (f : α → β) (x : {x // x ∈ s}) :
    (s.attach.erase x).map (fun j : {x // x ∈ s} ↦ f j) = (s.erase x).map f := by
  simp only [← Function.comp_apply (f := f)]
  rw [← map_map, erase_attach_map_val]

omit [DecidableEq α] in
protected lemma add_left_inj : s + u = t + u ↔ s = t := by classical simp [Multiset.ext]

omit [DecidableEq α] in
protected lemma add_right_inj : s + t = s + u ↔ t = u := by classical simp [Multiset.ext]

end

/-! ### Subtraction -/

section sub
variable [DecidableEq α] {s t u : Multiset α} {a : α}

/-- `s - t` is the multiset such that `count a (s - t) = count a s - count a t` for all `a`.
(note that it is truncated subtraction, so `count a (s - t) = 0` if `count a s ≤ count a t`). -/
protected def sub (s t : Multiset α) : Multiset α :=
  (Quotient.liftOn₂ s t fun l₁ l₂ => (l₁.diff l₂ : Multiset α)) fun _v₁ _v₂ _w₁ _w₂ p₁ p₂ =>
    Quot.sound <| p₁.diff p₂

instance : Sub (Multiset α) := ⟨.sub⟩

@[simp]
lemma coe_sub (s t : List α) : (s - t : Multiset α) = s.diff t :=
  rfl

/-- This is a special case of `tsub_zero`, which should be used instead of this.
This is needed to prove `OrderedSub (Multiset α)`. -/
@[simp, nolint simpNF] -- We want to use this lemma earlier than the lemma simp can prove it with
protected lemma sub_zero (s : Multiset α) : s - 0 = s :=
  Quot.inductionOn s fun _l => rfl

@[simp]
lemma sub_cons (a : α) (s t : Multiset α) : s - a ::ₘ t = s.erase a - t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => congr_arg _ <| diff_cons _ _ _

protected lemma zero_sub (t : Multiset α) : 0 - t = 0 :=
  Multiset.induction_on t rfl fun a s ih => by simp [ih]

@[simp]
lemma countP_sub {s t : Multiset α} :
    t ≤ s → ∀ (p : α → Prop) [DecidablePred p], countP p (s - t) = countP p s - countP p t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ hl _ _ ↦ List.countP_diff hl _

@[simp]
lemma count_sub (a : α) (s t : Multiset α) : count a (s - t) = count a s - count a t :=
  Quotient.inductionOn₂ s t <| by simp [List.count_diff]

/-- This is a special case of `tsub_le_iff_right`, which should be used instead of this.
This is needed to prove `OrderedSub (Multiset α)`. -/
protected lemma sub_le_iff_le_add : s - t ≤ u ↔ s ≤ u + t := by
  induction t using Multiset.induction_on generalizing s with
  | empty => simp [Multiset.sub_zero]
  | cons a s IH => simp [IH, erase_le_iff_le_cons]

/-- This is a special case of `tsub_le_iff_left`, which should be used instead of this. -/
protected lemma sub_le_iff_le_add' : s - t ≤ u ↔ s ≤ t + u := by
  rw [Multiset.sub_le_iff_le_add, Multiset.add_comm]

protected theorem sub_le_self (s t : Multiset α) : s - t ≤ s := by
  rw [Multiset.sub_le_iff_le_add]
  exact le_add_right _ _

protected lemma add_sub_assoc (hut : u ≤ t) : s + t - u = s + (t - u) := by
  ext a; simp [Nat.add_sub_assoc <| count_le_of_le _ hut]

protected lemma add_sub_cancel (hts : t ≤ s) : s - t + t = s := by
  ext a; simp [Nat.sub_add_cancel <| count_le_of_le _ hts]

protected lemma sub_add_cancel (hts : t ≤ s) : s - t + t = s := by
  ext a; simp [Nat.sub_add_cancel <| count_le_of_le _ hts]

protected lemma sub_add_eq_sub_sub : s - (t + u) = s - t - u := by ext; simp [Nat.sub_add_eq]

protected lemma le_sub_add : s ≤ s - t + t := Multiset.sub_le_iff_le_add.1 le_rfl
protected lemma le_add_sub : s ≤ t + (s - t) := Multiset.sub_le_iff_le_add'.1 le_rfl

protected lemma sub_le_sub_right (hst : s ≤ t) : s - u ≤ t - u :=
  Multiset.sub_le_iff_le_add'.mpr <| hst.trans Multiset.le_add_sub

protected lemma add_sub_cancel_right : s + t - t = s := by ext a; simp

protected lemma eq_sub_of_add_eq (hstu : s + t = u) : s = u - t := by
  rw [← hstu, Multiset.add_sub_cancel_right]

@[simp]
lemma filter_sub (p : α → Prop) [DecidablePred p] (s t : Multiset α) :
    filter p (s - t) = filter p s - filter p t := by
  revert s; refine Multiset.induction_on t (by simp) fun a t IH s => ?_
  rw [sub_cons, IH]
  by_cases h : p a
  · rw [filter_cons_of_pos _ h, sub_cons]
    congr
    by_cases m : a ∈ s
    · rw [← cons_inj_right a, ← filter_cons_of_pos _ h, cons_erase (mem_filter_of_mem m h),
        cons_erase m]
    · rw [erase_of_not_mem m, erase_of_not_mem (mt mem_of_mem_filter m)]
  · rw [filter_cons_of_neg _ h]
    by_cases m : a ∈ s
    · rw [(by rw [filter_cons_of_neg _ h] : filter p (erase s a) = filter p (a ::ₘ erase s a)),
        cons_erase m]
    · rw [erase_of_not_mem m]

@[simp]
lemma sub_filter_eq_filter_not (p : α → Prop) [DecidablePred p] (s : Multiset α) :
    s - s.filter p = s.filter fun a ↦ ¬ p a := by ext a; by_cases h : p a <;> simp [h]

lemma cons_sub_of_le (a : α) {s t : Multiset α} (h : t ≤ s) : a ::ₘ s - t = a ::ₘ (s - t) := by
  rw [← singleton_add, ← singleton_add, Multiset.add_sub_assoc h]

lemma sub_eq_fold_erase (s t : Multiset α) : s - t = foldl erase s t :=
  Quotient.inductionOn₂ s t fun l₁ l₂ => by
    show ofList (l₁.diff l₂) = foldl erase l₁ l₂
    rw [diff_eq_foldl l₁ l₂]
    symm
    exact foldl_hom _ _ _ _ _ fun x y => rfl

@[simp]
lemma card_sub {s t : Multiset α} (h : t ≤ s) : card (s - t) = card s - card t :=
  Nat.eq_sub_of_add_eq <| by rw [← card_add, Multiset.sub_add_cancel h]

/-! ### Union -/

/-- `s ∪ t` is the multiset such that the multiplicity of each `a` in it is the maximum of the
multiplicity of `a` in `s` and `t`. This is the supremum of multisets. -/
def union (s t : Multiset α) : Multiset α := s - t + t

instance : Union (Multiset α) :=
  ⟨union⟩

lemma union_def (s t : Multiset α) : s ∪ t = s - t + t := rfl

lemma le_union_left : s ≤ s ∪ t := Multiset.le_sub_add
lemma le_union_right : t ≤ s ∪ t := le_add_left _ _
lemma eq_union_left : t ≤ s → s ∪ t = s := Multiset.sub_add_cancel

@[gcongr]
lemma union_le_union_right (h : s ≤ t) (u) : s ∪ u ≤ t ∪ u :=
  Multiset.add_le_add_right <| Multiset.sub_le_sub_right h

lemma union_le (h₁ : s ≤ u) (h₂ : t ≤ u) : s ∪ t ≤ u := by
  rw [← eq_union_left h₂]; exact union_le_union_right h₁ t

@[simp]
lemma mem_union : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t :=
  ⟨fun h => (mem_add.1 h).imp_left (mem_of_le <| Multiset.sub_le_self _ _),
    (Or.elim · (mem_of_le le_union_left) (mem_of_le le_union_right))⟩

@[simp]
lemma map_union [DecidableEq β] {f : α → β} (finj : Function.Injective f) {s t : Multiset α} :
    map f (s ∪ t) = map f s ∪ map f t :=
  Quotient.inductionOn₂ s t fun l₁ l₂ =>
    congr_arg ofList (by rw [List.map_append f, List.map_diff finj])

@[simp] lemma zero_union : 0 ∪ s = s := by simp [union_def, Multiset.zero_sub]
@[simp] lemma union_zero : s ∪ 0 = s := by simp [union_def]

@[simp]
lemma count_union (a : α) (s t : Multiset α) : count a (s ∪ t) = max (count a s) (count a t) := by
  simp [(· ∪ ·), union, Nat.sub_add_eq_max]

@[simp] lemma filter_union (p : α → Prop) [DecidablePred p] (s t : Multiset α) :
    filter p (s ∪ t) = filter p s ∪ filter p t := by simp [(· ∪ ·), union]

/-! ### Intersection -/

/-- `s ∩ t` is the multiset such that the multiplicity of each `a` in it is the minimum of the
multiplicity of `a` in `s` and `t`. This is the infimum of multisets. -/
def inter (s t : Multiset α) : Multiset α :=
  Quotient.liftOn₂ s t (fun l₁ l₂ => (l₁.bagInter l₂ : Multiset α)) fun _v₁ _v₂ _w₁ _w₂ p₁ p₂ =>
    Quot.sound <| p₁.bagInter p₂

instance : Inter (Multiset α) := ⟨inter⟩

@[simp] lemma inter_zero (s : Multiset α) : s ∩ 0 = 0 :=
  Quot.inductionOn s fun l => congr_arg ofList l.bagInter_nil

@[simp] lemma zero_inter (s : Multiset α) : 0 ∩ s = 0 :=
  Quot.inductionOn s fun l => congr_arg ofList l.nil_bagInter

@[simp]
lemma cons_inter_of_pos (s : Multiset α) : a ∈ t → (a ::ₘ s) ∩ t = a ::ₘ s ∩ t.erase a :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ h => congr_arg ofList <| cons_bagInter_of_pos _ h

@[simp]
lemma cons_inter_of_neg (s : Multiset α) : a ∉ t → (a ::ₘ s) ∩ t = s ∩ t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ h => congr_arg ofList <| cons_bagInter_of_neg _ h

lemma inter_le_left : s ∩ t ≤ s :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => (bagInter_sublist_left _ _).subperm

lemma inter_le_right : s ∩ t ≤ t := by
  induction' s using Multiset.induction_on with a s IH generalizing t
  · exact (zero_inter t).symm ▸ zero_le _
  by_cases h : a ∈ t
  · simpa [h] using cons_le_cons a (IH (t := t.erase a))
  · simp [h, IH]

lemma le_inter (h₁ : s ≤ t) (h₂ : s ≤ u) : s ≤ t ∩ u := by
  revert s u; refine @(Multiset.induction_on t ?_ fun a t IH => ?_) <;> intros s u h₁ h₂
  · simpa only [zero_inter] using h₁
  by_cases h : a ∈ u
  · rw [cons_inter_of_pos _ h, ← erase_le_iff_le_cons]
    exact IH (erase_le_iff_le_cons.2 h₁) (erase_le_erase _ h₂)
  · rw [cons_inter_of_neg _ h]
    exact IH ((le_cons_of_not_mem <| mt (mem_of_le h₂) h).1 h₁) h₂

@[simp]
lemma mem_inter : a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t :=
  ⟨fun h => ⟨mem_of_le inter_le_left h, mem_of_le inter_le_right h⟩, fun ⟨h₁, h₂⟩ => by
    rw [← cons_erase h₁, cons_inter_of_pos _ h₂]; apply mem_cons_self⟩

instance instLattice : Lattice (Multiset α) where
  sup := (· ∪ ·)
  sup_le _ _ _ := union_le
  le_sup_left _ _ := le_union_left
  le_sup_right _ _ := le_union_right
  inf := (· ∩ ·)
  le_inf _ _ _ := le_inter
  inf_le_left _ _ := inter_le_left
  inf_le_right _ _ := inter_le_right

@[simp] lemma sup_eq_union (s t : Multiset α) : s ⊔ t = s ∪ t := rfl
@[simp] lemma inf_eq_inter (s t : Multiset α) : s ⊓ t = s ∩ t := rfl

@[simp] lemma le_inter_iff : s ≤ t ∩ u ↔ s ≤ t ∧ s ≤ u := le_inf_iff
@[simp] lemma union_le_iff : s ∪ t ≤ u ↔ s ≤ u ∧ t ≤ u := sup_le_iff

lemma union_comm (s t : Multiset α) : s ∪ t = t ∪ s := sup_comm ..
lemma inter_comm (s t : Multiset α) : s ∩ t = t ∩ s := inf_comm ..

lemma eq_union_right (h : s ≤ t) : s ∪ t = t := by rw [union_comm, eq_union_left h]

@[gcongr] lemma union_le_union_left (h : s ≤ t) (u) : u ∪ s ≤ u ∪ t := sup_le_sup_left h _

lemma union_le_add (s t : Multiset α) : s ∪ t ≤ s + t := union_le (le_add_right ..) (le_add_left ..)

lemma union_add_distrib (s t u : Multiset α) : s ∪ t + u = s + u ∪ (t + u) := by
  simpa [(· ∪ ·), union, eq_comm, Multiset.add_assoc, Multiset.add_left_inj] using
    show s + u - (t + u) = s - t by
      rw [t.add_comm, Multiset.sub_add_eq_sub_sub, Multiset.add_sub_cancel_right]

lemma add_union_distrib (s t u : Multiset α) : s + (t ∪ u) = s + t ∪ (s + u) := by
  rw [Multiset.add_comm, union_add_distrib, s.add_comm, s.add_comm]

lemma cons_union_distrib (a : α) (s t : Multiset α) : a ::ₘ (s ∪ t) = a ::ₘ s ∪ a ::ₘ t := by
  simpa using add_union_distrib (a ::ₘ 0) s t

lemma inter_add_distrib (s t u : Multiset α) : s ∩ t + u = (s + u) ∩ (t + u) := by
  by_contra! h
  obtain ⟨a, ha⟩ := lt_iff_cons_le.1 <| h.lt_of_le <| le_inter
    (Multiset.add_le_add_right inter_le_left) (Multiset.add_le_add_right inter_le_right)
  rw [← cons_add] at ha
  exact (lt_cons_self (s ∩ t) a).not_le <| le_inter
    (Multiset.le_of_add_le_add_right (ha.trans inter_le_left))
    (Multiset.le_of_add_le_add_right (ha.trans inter_le_right))

lemma add_inter_distrib (s t u : Multiset α) : s + t ∩ u = (s + t) ∩ (s + u) := by
  rw [Multiset.add_comm, inter_add_distrib, s.add_comm, s.add_comm]

lemma cons_inter_distrib (a : α) (s t : Multiset α) : a ::ₘ s ∩ t = (a ::ₘ s) ∩ (a ::ₘ t) := by
  simp

lemma union_add_inter (s t : Multiset α) : s ∪ t + s ∩ t = s + t := by
  apply _root_.le_antisymm
  · rw [union_add_distrib]
    refine union_le (Multiset.add_le_add_left inter_le_right) ?_
    rw [Multiset.add_comm]
    exact Multiset.add_le_add_right inter_le_left
  · rw [Multiset.add_comm, add_inter_distrib]
    refine le_inter (Multiset.add_le_add_right le_union_right) ?_
    rw [Multiset.add_comm]
    exact Multiset.add_le_add_right le_union_left

lemma sub_add_inter (s t : Multiset α) : s - t + s ∩ t = s := by
  rw [inter_comm]
  revert s; refine Multiset.induction_on t (by simp) fun a t IH s => ?_
  by_cases h : a ∈ s
  · rw [cons_inter_of_pos _ h, sub_cons, add_cons, IH, cons_erase h]
  · rw [cons_inter_of_neg _ h, sub_cons, erase_of_not_mem h, IH]

lemma sub_inter (s t : Multiset α) : s - s ∩ t = s - t :=
  (Multiset.eq_sub_of_add_eq <| sub_add_inter ..).symm

@[simp]
lemma count_inter (a : α) (s t : Multiset α) : count a (s ∩ t) = min (count a s) (count a t) := by
  apply @Nat.add_left_cancel (count a (s - t))
  rw [← count_add, sub_add_inter, count_sub, Nat.sub_add_min_cancel]

@[simp]
lemma coe_inter (s t : List α) : (s ∩ t : Multiset α) = (s.bagInter t : List α) := by ext; simp

instance instDistribLattice : DistribLattice (Multiset α) where
  le_sup_inf s t u := ge_of_eq <| ext.2 fun a ↦ by
    simp only [max_min_distrib_left, Multiset.count_inter, Multiset.sup_eq_union,
      Multiset.count_union, Multiset.inf_eq_inter]

@[simp] lemma filter_inter (p : α → Prop) [DecidablePred p] (s t : Multiset α) :
    filter p (s ∩ t) = filter p s ∩ filter p t :=
  le_antisymm (le_inter (filter_le_filter _ inter_le_left) (filter_le_filter _ inter_le_right)) <|
    le_filter.2 ⟨inf_le_inf (filter_le _ _) (filter_le _ _), fun _a h =>
      of_mem_filter (mem_of_le inter_le_left h)⟩

@[simp]
theorem replicate_inter (n : ℕ) (x : α) (s : Multiset α) :
    replicate n x ∩ s = replicate (min n (s.count x)) x := by
  ext y
  rw [count_inter, count_replicate, count_replicate]
  by_cases h : x = y
  · simp only [h, if_true]
  · simp only [h, if_false, Nat.zero_min]

@[simp]
theorem inter_replicate (s : Multiset α) (n : ℕ) (x : α) :
    s ∩ replicate n x = replicate (min (s.count x) n) x := by
  rw [inter_comm, replicate_inter, min_comm]

end sub

section Embedding

@[simp]
theorem map_le_map_iff {f : α → β} (hf : Function.Injective f) {s t : Multiset α} :
    s.map f ≤ t.map f ↔ s ≤ t := by
  classical
    refine ⟨fun h => le_iff_count.mpr fun a => ?_, map_le_map⟩
    simpa [count_map_eq_count' f _ hf] using le_iff_count.mp h (f a)

/-- Associate to an embedding `f` from `α` to `β` the order embedding that maps a multiset to its
image under `f`. -/
@[simps!]
def mapEmbedding (f : α ↪ β) : Multiset α ↪o Multiset β :=
  OrderEmbedding.ofMapLEIff (map f) fun _ _ => map_le_map_iff f.inj'

end Embedding

theorem count_eq_card_filter_eq [DecidableEq α] (s : Multiset α) (a : α) :
    s.count a = card (s.filter (a = ·)) := by rw [count, countP_eq_card_filter]

/--
Mapping a multiset through a predicate and counting the `True`s yields the cardinality of the set
filtered by the predicate. Note that this uses the notion of a multiset of `Prop`s - due to the
decidability requirements of `count`, the decidability instance on the LHS is different from the
RHS. In particular, the decidability instance on the left leaks `Classical.decEq`.
See [here](https://github.com/leanprover-community/mathlib/pull/11306#discussion_r782286812)
for more discussion.
-/
@[simp]
theorem map_count_True_eq_filter_card (s : Multiset α) (p : α → Prop) [DecidablePred p] :
    (s.map p).count True = card (s.filter p) := by
  simp only [count_eq_card_filter_eq, filter_map, card_map, Function.id_comp,
    eq_true_eq_id, Function.comp_apply]

@[simp] theorem sub_singleton [DecidableEq α] (a : α) (s : Multiset α) : s - {a} = s.erase a := by
  ext
  simp only [count_sub, count_singleton]
  split <;> simp_all

theorem mem_sub [DecidableEq α] {a : α} {s t : Multiset α} :
    a ∈ s - t ↔ t.count a < s.count a := by
  rw [← count_pos, count_sub, Nat.sub_pos_iff_lt]

theorem inter_add_sub_of_add_eq_add [DecidableEq α] {M N P Q : Multiset α} (h : M + N = P + Q) :
    (N ∩ Q) + (P - M) = N := by
  ext x
  rw [Multiset.count_add, Multiset.count_inter, Multiset.count_sub]
  have h0 : M.count x + N.count x = P.count x + Q.count x := by
    rw [Multiset.ext] at h
    simp_all only [Multiset.mem_add, Multiset.count_add]
  omega

/-! ### Lift a relation to `Multiset`s -/


section Rel

/-- `Rel r s t` -- lift the relation `r` between two elements to a relation between `s` and `t`,
s.t. there is a one-to-one mapping between elements in `s` and `t` following `r`. -/
@[mk_iff]
inductive Rel (r : α → β → Prop) : Multiset α → Multiset β → Prop
  | zero : Rel r 0 0
  | cons {a b as bs} : r a b → Rel r as bs → Rel r (a ::ₘ as) (b ::ₘ bs)

variable {δ : Type*} {r : α → β → Prop} {p : γ → δ → Prop}

private theorem rel_flip_aux {s t} (h : Rel r s t) : Rel (flip r) t s :=
  Rel.recOn h Rel.zero fun h₀ _h₁ ih => Rel.cons h₀ ih

theorem rel_flip {s t} : Rel (flip r) s t ↔ Rel r t s :=
  ⟨rel_flip_aux, rel_flip_aux⟩

theorem rel_refl_of_refl_on {m : Multiset α} {r : α → α → Prop} : (∀ x ∈ m, r x x) → Rel r m m := by
  refine m.induction_on ?_ ?_
  · intros
    apply Rel.zero
  · intro a m ih h
    exact Rel.cons (h _ (mem_cons_self _ _)) (ih fun _ ha => h _ (mem_cons_of_mem ha))

theorem rel_eq_refl {s : Multiset α} : Rel (· = ·) s s :=
  rel_refl_of_refl_on fun _x _hx => rfl

theorem rel_eq {s t : Multiset α} : Rel (· = ·) s t ↔ s = t := by
  constructor
  · intro h
    induction h <;> simp [*]
  · intro h
    subst h
    exact rel_eq_refl

theorem Rel.mono {r p : α → β → Prop} {s t} (hst : Rel r s t)
    (h : ∀ a ∈ s, ∀ b ∈ t, r a b → p a b) : Rel p s t := by
  induction hst with
  | zero => exact Rel.zero
  | @cons a b s t hab _hst ih =>
    apply Rel.cons (h a (mem_cons_self _ _) b (mem_cons_self _ _) hab)
    exact ih fun a' ha' b' hb' h' => h a' (mem_cons_of_mem ha') b' (mem_cons_of_mem hb') h'

theorem Rel.add {s t u v} (hst : Rel r s t) (huv : Rel r u v) : Rel r (s + u) (t + v) := by
  induction hst with
  | zero => simpa using huv
  | cons hab hst ih => simpa using ih.cons hab

theorem rel_flip_eq {s t : Multiset α} : Rel (fun a b => b = a) s t ↔ s = t :=
  show Rel (flip (· = ·)) s t ↔ s = t by rw [rel_flip, rel_eq, eq_comm]

@[simp]
theorem rel_zero_left {b : Multiset β} : Rel r 0 b ↔ b = 0 := by rw [rel_iff]; simp

@[simp]
theorem rel_zero_right {a : Multiset α} : Rel r a 0 ↔ a = 0 := by rw [rel_iff]; simp

theorem rel_cons_left {a as bs} :
    Rel r (a ::ₘ as) bs ↔ ∃ b bs', r a b ∧ Rel r as bs' ∧ bs = b ::ₘ bs' := by
  constructor
  · generalize hm : a ::ₘ as = m
    intro h
    induction h generalizing as with
    | zero => simp at hm
    | @cons a' b as' bs ha'b h ih =>
      rcases cons_eq_cons.1 hm with (⟨eq₁, eq₂⟩ | ⟨_h, cs, eq₁, eq₂⟩)
      · subst eq₁
        subst eq₂
        exact ⟨b, bs, ha'b, h, rfl⟩
      · rcases ih eq₂.symm with ⟨b', bs', h₁, h₂, eq⟩
        exact ⟨b', b ::ₘ bs', h₁, eq₁.symm ▸ Rel.cons ha'b h₂, eq.symm ▸ cons_swap _ _ _⟩
  · exact fun ⟨b, bs', hab, h, Eq⟩ => Eq.symm ▸ Rel.cons hab h

theorem rel_cons_right {as b bs} :
    Rel r as (b ::ₘ bs) ↔ ∃ a as', r a b ∧ Rel r as' bs ∧ as = a ::ₘ as' := by
  rw [← rel_flip, rel_cons_left]
  refine exists₂_congr fun a as' => ?_
  rw [rel_flip, flip]

theorem rel_add_left {as₀ as₁} :
    ∀ {bs}, Rel r (as₀ + as₁) bs ↔ ∃ bs₀ bs₁, Rel r as₀ bs₀ ∧ Rel r as₁ bs₁ ∧ bs = bs₀ + bs₁ :=
  @(Multiset.induction_on as₀ (by simp) fun a s ih bs ↦ by
      simp only [ih, cons_add, rel_cons_left]
      constructor
      · intro h
        rcases h with ⟨b, bs', hab, h, rfl⟩
        rcases h with ⟨bs₀, bs₁, h₀, h₁, rfl⟩
        exact ⟨b ::ₘ bs₀, bs₁, ⟨b, bs₀, hab, h₀, rfl⟩, h₁, by simp⟩
      · intro h
        rcases h with ⟨bs₀, bs₁, h, h₁, rfl⟩
        rcases h with ⟨b, bs, hab, h₀, rfl⟩
        exact ⟨b, bs + bs₁, hab, ⟨bs, bs₁, h₀, h₁, rfl⟩, by simp⟩)

theorem rel_add_right {as bs₀ bs₁} :
    Rel r as (bs₀ + bs₁) ↔ ∃ as₀ as₁, Rel r as₀ bs₀ ∧ Rel r as₁ bs₁ ∧ as = as₀ + as₁ := by
  rw [← rel_flip, rel_add_left]; simp [rel_flip]

theorem rel_map_left {s : Multiset γ} {f : γ → α} :
    ∀ {t}, Rel r (s.map f) t ↔ Rel (fun a b => r (f a) b) s t :=
  @(Multiset.induction_on s (by simp) (by simp +contextual [rel_cons_left]))

theorem rel_map_right {s : Multiset α} {t : Multiset γ} {f : γ → β} :
    Rel r s (t.map f) ↔ Rel (fun a b => r a (f b)) s t := by
  rw [← rel_flip, rel_map_left, ← rel_flip]; rfl

theorem rel_map {s : Multiset α} {t : Multiset β} {f : α → γ} {g : β → δ} :
    Rel p (s.map f) (t.map g) ↔ Rel (fun a b => p (f a) (g b)) s t :=
  rel_map_left.trans rel_map_right

theorem card_eq_card_of_rel {r : α → β → Prop} {s : Multiset α} {t : Multiset β} (h : Rel r s t) :
    card s = card t := by induction h <;> simp [*]

theorem exists_mem_of_rel_of_mem {r : α → β → Prop} {s : Multiset α} {t : Multiset β}
    (h : Rel r s t) : ∀ {a : α}, a ∈ s → ∃ b ∈ t, r a b := by
  induction' h with x y s t hxy _hst ih
  · simp
  · intro a ha
    rcases mem_cons.1 ha with ha | ha
    · exact ⟨y, mem_cons_self _ _, ha.symm ▸ hxy⟩
    · rcases ih ha with ⟨b, hbt, hab⟩
      exact ⟨b, mem_cons.2 (Or.inr hbt), hab⟩

theorem rel_of_forall {m1 m2 : Multiset α} {r : α → α → Prop} (h : ∀ a b, a ∈ m1 → b ∈ m2 → r a b)
    (hc : card m1 = card m2) : m1.Rel r m2 := by
  revert m1
  refine @(m2.induction_on ?_ ?_)
  · intro m _h hc
    rw [rel_zero_right, ← card_eq_zero, hc, card_zero]
  · intro a t ih m h hc
    rw [card_cons] at hc
    obtain ⟨b, hb⟩ := card_pos_iff_exists_mem.1 (show 0 < card m from hc.symm ▸ Nat.succ_pos _)
    obtain ⟨m', rfl⟩ := exists_cons_of_mem hb
    refine rel_cons_right.mpr ⟨b, m', h _ _ hb (mem_cons_self _ _), ih ?_ ?_, rfl⟩
    · exact fun _ _ ha hb => h _ _ (mem_cons_of_mem ha) (mem_cons_of_mem hb)
    · simpa using hc

theorem rel_replicate_left {m : Multiset α} {a : α} {r : α → α → Prop} {n : ℕ} :
    (replicate n a).Rel r m ↔ card m = n ∧ ∀ x, x ∈ m → r a x :=
  ⟨fun h =>
    ⟨(card_eq_card_of_rel h).symm.trans (card_replicate _ _), fun x hx => by
      obtain ⟨b, hb1, hb2⟩ := exists_mem_of_rel_of_mem (rel_flip.2 h) hx
      rwa [eq_of_mem_replicate hb1] at hb2⟩,
    fun h =>
    rel_of_forall (fun _ _ hx hy => (eq_of_mem_replicate hx).symm ▸ h.2 _ hy)
      (Eq.trans (card_replicate _ _) h.1.symm)⟩

theorem rel_replicate_right {m : Multiset α} {a : α} {r : α → α → Prop} {n : ℕ} :
    m.Rel r (replicate n a) ↔ card m = n ∧ ∀ x, x ∈ m → r x a :=
  rel_flip.trans rel_replicate_left

protected nonrec -- Porting note: added
theorem Rel.trans (r : α → α → Prop) [IsTrans α r] {s t u : Multiset α} (r1 : Rel r s t)
    (r2 : Rel r t u) : Rel r s u := by
  induction' t using Multiset.induction_on with x t ih generalizing s u
  · rw [rel_zero_right.mp r1, rel_zero_left.mp r2, rel_zero_left]
  · obtain ⟨a, as, ha1, ha2, rfl⟩ := rel_cons_right.mp r1
    obtain ⟨b, bs, hb1, hb2, rfl⟩ := rel_cons_left.mp r2
    exact Multiset.Rel.cons (_root_.trans ha1 hb1) (ih ha2 hb2)

theorem Rel.countP_eq (r : α → α → Prop) [IsTrans α r] [IsSymm α r] {s t : Multiset α} (x : α)
    [DecidablePred (r x)] (h : Rel r s t) : countP (r x) s = countP (r x) t := by
  induction' s using Multiset.induction_on with y s ih generalizing t
  · rw [rel_zero_left.mp h]
  · obtain ⟨b, bs, hb1, hb2, rfl⟩ := rel_cons_left.mp h
    rw [countP_cons, countP_cons, ih hb2]
    simp only [decide_eq_true_eq, Nat.add_right_inj]
    exact (if_congr ⟨fun h => _root_.trans h hb1, fun h => _root_.trans h (symm hb1)⟩ rfl rfl)

end Rel

section Map

theorem map_eq_map {f : α → β} (hf : Function.Injective f) {s t : Multiset α} :
    s.map f = t.map f ↔ s = t := by
  rw [← rel_eq, ← rel_eq, rel_map]
  simp only [hf.eq_iff]

theorem map_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective (Multiset.map f) := fun _x _y => (map_eq_map hf).1

lemma filter_attach' (s : Multiset α) (p : {a // a ∈ s} → Prop) [DecidableEq α]
    [DecidablePred p] :
    s.attach.filter p =
      (s.filter fun x ↦ ∃ h, p ⟨x, h⟩).attach.map (Subtype.map id fun _ ↦ mem_of_mem_filter) := by
  classical
  refine Multiset.map_injective Subtype.val_injective ?_
  rw [map_filter' _ Subtype.val_injective]
  simp only [Function.comp, Subtype.exists, coe_mk, Subtype.map,
    exists_and_right, exists_eq_right, attach_map_val, map_map, map_coe, id]

end Map

section Quot

theorem map_mk_eq_map_mk_of_rel {r : α → α → Prop} {s t : Multiset α} (hst : s.Rel r t) :
    s.map (Quot.mk r) = t.map (Quot.mk r) :=
  Rel.recOn hst rfl fun hab _hst ih => by simp [ih, Quot.sound hab]

theorem exists_multiset_eq_map_quot_mk {r : α → α → Prop} (s : Multiset (Quot r)) :
    ∃ t : Multiset α, s = t.map (Quot.mk r) :=
  Multiset.induction_on s ⟨0, rfl⟩ fun a _s ⟨t, ht⟩ =>
    Quot.inductionOn a fun a => ht.symm ▸ ⟨a ::ₘ t, (map_cons _ _ _).symm⟩

theorem induction_on_multiset_quot {r : α → α → Prop} {p : Multiset (Quot r) → Prop}
    (s : Multiset (Quot r)) : (∀ s : Multiset α, p (s.map (Quot.mk r))) → p s :=
  match s, exists_multiset_eq_map_quot_mk s with
  | _, ⟨_t, rfl⟩ => fun h => h _

end Quot

/-! ### Disjoint multisets -/


/-- `Disjoint s t` means that `s` and `t` have no elements in common. -/
@[deprecated _root_.Disjoint (since := "2024-11-01")]
protected def Disjoint (s t : Multiset α) : Prop :=
  ∀ ⦃a⦄, a ∈ s → a ∈ t → False

theorem disjoint_left {s t : Multiset α} : Disjoint s t ↔ ∀ {a}, a ∈ s → a ∉ t := by
  refine ⟨fun h a hs ht ↦ ?_, fun h u hs ht ↦ ?_⟩
  · simpa using h (singleton_le.mpr hs) (singleton_le.mpr ht)
  · rw [le_bot_iff, bot_eq_zero, eq_zero_iff_forall_not_mem]
    exact fun a ha ↦ h (subset_of_le hs ha) (subset_of_le ht ha)

@[simp, norm_cast]
theorem coe_disjoint (l₁ l₂ : List α) : Disjoint (l₁ : Multiset α) l₂ ↔ l₁.Disjoint l₂ :=
  disjoint_left

@[deprecated (since := "2024-11-01")] protected alias Disjoint.symm := _root_.Disjoint.symm
@[deprecated (since := "2024-11-01")] protected alias disjoint_comm := _root_.disjoint_comm

theorem disjoint_right {s t : Multiset α} : Disjoint s t ↔ ∀ {a}, a ∈ t → a ∉ s :=
  disjoint_comm.trans disjoint_left

theorem disjoint_iff_ne {s t : Multiset α} : Disjoint s t ↔ ∀ a ∈ s, ∀ b ∈ t, a ≠ b := by
  simp [disjoint_left, imp_not_comm]

theorem disjoint_of_subset_left {s t u : Multiset α} (h : s ⊆ u) (d : Disjoint u t) :
    Disjoint s t :=
  disjoint_left.mpr fun ha ↦ disjoint_left.mp d <| h ha

theorem disjoint_of_subset_right {s t u : Multiset α} (h : t ⊆ u) (d : Disjoint s u) :
    Disjoint s t :=
  (disjoint_of_subset_left h d.symm).symm

@[deprecated (since := "2024-11-01")] protected alias disjoint_of_le_left := Disjoint.mono_left
@[deprecated (since := "2024-11-01")] protected alias disjoint_of_le_right := Disjoint.mono_right

@[simp]
theorem zero_disjoint (l : Multiset α) : Disjoint 0 l := disjoint_bot_left

@[simp]
theorem singleton_disjoint {l : Multiset α} {a : α} : Disjoint {a} l ↔ a ∉ l := by
  simp [disjoint_left]

@[simp]
theorem disjoint_singleton {l : Multiset α} {a : α} : Disjoint l {a} ↔ a ∉ l := by
  rw [_root_.disjoint_comm, singleton_disjoint]

@[simp]
theorem disjoint_add_left {s t u : Multiset α} :
    Disjoint (s + t) u ↔ Disjoint s u ∧ Disjoint t u := by simp [disjoint_left, or_imp, forall_and]

@[simp]
theorem disjoint_add_right {s t u : Multiset α} :
    Disjoint s (t + u) ↔ Disjoint s t ∧ Disjoint s u := by
  rw [_root_.disjoint_comm, disjoint_add_left]; tauto

@[simp]
theorem disjoint_cons_left {a : α} {s t : Multiset α} :
    Disjoint (a ::ₘ s) t ↔ a ∉ t ∧ Disjoint s t :=
  (@disjoint_add_left _ {a} s t).trans <| by rw [singleton_disjoint]

@[simp]
theorem disjoint_cons_right {a : α} {s t : Multiset α} :
    Disjoint s (a ::ₘ t) ↔ a ∉ s ∧ Disjoint s t := by
  rw [_root_.disjoint_comm, disjoint_cons_left]; tauto

theorem inter_eq_zero_iff_disjoint [DecidableEq α] {s t : Multiset α} :
    s ∩ t = 0 ↔ Disjoint s t := by rw [← subset_zero]; simp [subset_iff, disjoint_left]

@[simp]
theorem disjoint_union_left [DecidableEq α] {s t u : Multiset α} :
    Disjoint (s ∪ t) u ↔ Disjoint s u ∧ Disjoint t u :=  disjoint_sup_left

@[simp]
theorem disjoint_union_right [DecidableEq α] {s t u : Multiset α} :
    Disjoint s (t ∪ u) ↔ Disjoint s t ∧ Disjoint s u := disjoint_sup_right

theorem add_eq_union_iff_disjoint [DecidableEq α] {s t : Multiset α} :
    s + t = s ∪ t ↔ Disjoint s t := by
  simp_rw [← inter_eq_zero_iff_disjoint, ext, count_add, count_union, count_inter, count_zero,
    Nat.min_eq_zero_iff, Nat.add_eq_max_iff]

lemma add_eq_union_left_of_le [DecidableEq α] {s t u : Multiset α} (h : t ≤ s) :
    u + s = u ∪ t ↔ Disjoint u s ∧ s = t := by
  rw [← add_eq_union_iff_disjoint]
  refine ⟨fun h0 ↦ ?_, ?_⟩
  · rw [and_iff_right_of_imp]
    · exact (Multiset.le_of_add_le_add_left <| h0.trans_le <| union_le_add u t).antisymm h
    · rintro rfl
      exact h0
  · rintro ⟨h0, rfl⟩
    exact h0

lemma add_eq_union_right_of_le [DecidableEq α] {x y z : Multiset α} (h : z ≤ y) :
    x + y = x ∪ z ↔ y = z ∧ Disjoint x y := by
  simpa only [and_comm] using add_eq_union_left_of_le h

theorem disjoint_map_map {f : α → γ} {g : β → γ} {s : Multiset α} {t : Multiset β} :
    Disjoint (s.map f) (t.map g) ↔ ∀ a ∈ s, ∀ b ∈ t, f a ≠ g b := by
  simp [disjoint_iff_ne]

/-- `Pairwise r m` states that there exists a list of the elements s.t. `r` holds pairwise on this
list. -/
def Pairwise (r : α → α → Prop) (m : Multiset α) : Prop :=
  ∃ l : List α, m = l ∧ l.Pairwise r

@[simp]
theorem pairwise_zero (r : α → α → Prop) : Multiset.Pairwise r 0 :=
  ⟨[], rfl, List.Pairwise.nil⟩

theorem pairwise_coe_iff {r : α → α → Prop} {l : List α} :
    Multiset.Pairwise r l ↔ ∃ l' : List α, l ~ l' ∧ l'.Pairwise r :=
  exists_congr <| by simp

theorem pairwise_coe_iff_pairwise {r : α → α → Prop} (hr : Symmetric r) {l : List α} :
    Multiset.Pairwise r l ↔ l.Pairwise r :=
  Iff.intro (fun ⟨_l', Eq, h⟩ => ((Quotient.exact Eq).pairwise_iff @hr).2 h) fun h => ⟨l, rfl, h⟩

theorem map_set_pairwise {f : α → β} {r : β → β → Prop} {m : Multiset α}
    (h : { a | a ∈ m }.Pairwise fun a₁ a₂ => r (f a₁) (f a₂)) : { b | b ∈ m.map f }.Pairwise r :=
  fun b₁ h₁ b₂ h₂ hn => by
    obtain ⟨⟨a₁, H₁, rfl⟩, a₂, H₂, rfl⟩ := Multiset.mem_map.1 h₁, Multiset.mem_map.1 h₂
    exact h H₁ H₂ (mt (congr_arg f) hn)

end Multiset

namespace Multiset

section Choose

variable (p : α → Prop) [DecidablePred p] (l : Multiset α)

/-- Given a proof `hp` that there exists a unique `a ∈ l` such that `p a`, `chooseX p l hp` returns
that `a` together with proofs of `a ∈ l` and `p a`. -/
def chooseX : ∀ _hp : ∃! a, a ∈ l ∧ p a, { a // a ∈ l ∧ p a } :=
  Quotient.recOn l (fun l' ex_unique => List.chooseX p l' (ExistsUnique.exists ex_unique))
    (by
      intros a b _
      funext hp
      suffices all_equal : ∀ x y : { t // t ∈ b ∧ p t }, x = y by
        apply all_equal
      rintro ⟨x, px⟩ ⟨y, py⟩
      rcases hp with ⟨z, ⟨_z_mem_l, _pz⟩, z_unique⟩
      congr
      calc
        x = z := z_unique x px
        _ = y := (z_unique y py).symm
        )

/-- Given a proof `hp` that there exists a unique `a ∈ l` such that `p a`, `choose p l hp` returns
that `a`. -/
def choose (hp : ∃! a, a ∈ l ∧ p a) : α :=
  chooseX p l hp

theorem choose_spec (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
  (chooseX p l hp).property

theorem choose_mem (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l :=
  (choose_spec _ _ _).1

theorem choose_property (hp : ∃! a, a ∈ l ∧ p a) : p (choose p l hp) :=
  (choose_spec _ _ _).2

end Choose

variable (α)

/-- The equivalence between lists and multisets of a subsingleton type. -/
def subsingletonEquiv [Subsingleton α] : List α ≃ Multiset α where
  toFun := ofList
  invFun :=
    (Quot.lift id) fun (a b : List α) (h : a ~ b) =>
      (List.ext_get h.length_eq) fun _ _ _ => Subsingleton.elim _ _
  left_inv _ := rfl
  right_inv m := Quot.inductionOn m fun _ => rfl

variable {α}

@[simp]
theorem coe_subsingletonEquiv [Subsingleton α] :
    (subsingletonEquiv α : List α → Multiset α) = ofList :=
  rfl

end Multiset

set_option linter.style.longFile 2800
