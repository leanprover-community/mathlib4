/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.Quot
import Mathlib.Order.Monotone.Defs
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Monotonicity.Attr
import Mathlib.Util.AssertExists

/-!
# Multisets

Multisets are finite sets with duplicates allowed. They are implemented here as the quotient of
lists by permutation. This gives them computational content.

This file contains the definition of `Multiset` and the basic predicates. Most operations
have been split off into their own files. The goal is that we can define `Finset` with only
importing `Multiset.Defs`.

## Main definitions

* `Multiset`: the type of finite sets with duplicates allowed.

* `Coe (List α) (Multiset α)`: turn a list into a multiset by forgetting the order.
* `Multiset.pmap`: map a partial function defined on a superset of the multiset's elements.
* `Multiset.attach`: add a proof of membership to the elements of the multiset.
* `Multiset.card`: number of elements of a multiset (counted with repetition).

* `Membership α (Multiset α)` instance: `x ∈ s` if `x` has multiplicity at least one in `s`.
* `Subset (Multiset α)` instance: `s ⊆ t` if every `x ∈ s` also enjoys `x ∈ t`.
* `PartialOrder (Multiset α)` instance: `s ≤ t` if all `x` have multiplicity in
  `s` less than their multiplicity in `t`.
* `Multiset.Pairwise`: `Pairwise r s` holds iff there exists a list of elements
  of `s` such that `r` holds pairwise.
* `Multiset.Nodup`: `Nodup s` holds if the multiplicity of any element is at most 1.

## Notation (defined later)

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
assert_not_exists Monoid OrderHom

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

/-- `Multiset α` is the quotient of `List α` by list permutation. The result
  is a type of finite sets with duplicates allowed. -/
def Multiset.{u} (α : Type u) : Type u :=
  Quotient (List.isSetoid α)

namespace Multiset

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

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: move to better place
-- (upstream to Batteries?)
instance [DecidableEq α] (l₁ l₂ : List α) : Decidable (l₁ ≈ l₂) :=
  inferInstanceAs (Decidable (l₁ ~ l₂))

instance [DecidableEq α] (l₁ l₂ : List α) : Decidable (isSetoid α l₁ l₂) :=
  inferInstanceAs (Decidable (l₁ ~ l₂))

instance decidableEq [DecidableEq α] : DecidableEq (Multiset α)
  | s₁, s₂ => Quotient.recOnSubsingleton₂ s₁ s₂ fun _ _ => decidable_of_iff' _ Quotient.eq_iff_equiv

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

end Mem

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

end Subset

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

instance decidableLE [DecidableEq α] : DecidableLE (Multiset α) :=
  fun s t => Quotient.recOnSubsingleton₂ s t List.decidableSubperm

section

variable {s t : Multiset α} {a : α}

theorem subset_of_le : s ≤ t → s ⊆ t :=
  Quotient.inductionOn₂ s t fun _ _ => Subperm.subset

alias Le.subset := subset_of_le

theorem mem_of_le (h : s ≤ t) : a ∈ s → a ∈ t :=
  mem_of_subset (subset_of_le h)

theorem notMem_mono (h : s ⊆ t) : a ∉ t → a ∉ s :=
  mt <| @h _

@[deprecated (since := "2025-05-23")] alias not_mem_mono := notMem_mono

@[simp]
theorem coe_le {l₁ l₂ : List α} : (l₁ : Multiset α) ≤ l₂ ↔ l₁ <+~ l₂ :=
  Iff.rfl

@[elab_as_elim]
theorem leInductionOn {C : Multiset α → Multiset α → Prop} {s t : Multiset α} (h : s ≤ t)
    (H : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → C l₁ l₂) : C s t :=
  Quotient.inductionOn₂ s t (fun l₁ _ ⟨l, p, s⟩ => (show ⟦l⟧ = ⟦l₁⟧ from Quot.sound p) ▸ H s) h

end

/-! ### Cardinality -/


/-- The cardinality of a multiset is the sum of the multiplicities
  of all its elements, or simply the length of the underlying list. -/
def card : Multiset α → ℕ := Quot.lift length fun _l₁ _l₂ => Perm.length_eq

@[simp]
theorem coe_card (l : List α) : card (l : Multiset α) = length l :=
  rfl

@[gcongr]
theorem card_le_card {s t : Multiset α} (h : s ≤ t) : card s ≤ card t :=
  leInductionOn h Sublist.length_le

theorem eq_of_le_of_card_le {s t : Multiset α} (h : s ≤ t) : card t ≤ card s → s = t :=
  leInductionOn h fun s h₂ => congr_arg _ <| s.eq_of_length_le h₂

@[gcongr]
theorem card_lt_card {s t : Multiset α} (h : s < t) : card s < card t :=
  lt_of_not_ge fun h₂ => _root_.ne_of_lt h <| eq_of_le_of_card_le (le_of_lt h) h₂

@[mono]
theorem card_mono : Monotone (@card α) := fun _a _b => card_le_card

lemma card_strictMono : StrictMono (card : Multiset α → ℕ) := fun _ _ ↦ card_lt_card

/-- Another way of expressing `strongInductionOn`: the `(<)` relation is well-founded. -/
instance instWellFoundedLT : WellFoundedLT (Multiset α) :=
  ⟨Subrelation.wf Multiset.card_lt_card (measure Multiset.card).2⟩

@[simp]
theorem coe_reverse (l : List α) : (reverse l : Multiset α) = l :=
  Quot.sound <| reverse_perm _

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

theorem pmap_congr {p q : α → Prop} {f : ∀ a, p a → β} {g : ∀ a, q a → β} (s : Multiset α) :
    ∀ {H₁ H₂}, (∀ a ∈ s, ∀ (h₁ h₂), f a h₁ = g a h₂) → pmap f s H₁ = pmap g s H₂ :=
  @(Quot.inductionOn s (fun l _H₁ _H₂ h => congr_arg _ <| List.pmap_congr_left l h))

@[simp]
theorem mem_pmap {p : α → Prop} {f : ∀ a, p a → β} {s H b} :
    b ∈ pmap f s H ↔ ∃ (a : _) (h : a ∈ s), f a (H a h) = b :=
  Quot.inductionOn s (fun _l _H => List.mem_pmap) H

@[simp]
theorem card_pmap {p : α → Prop} (f : ∀ a, p a → β) (s H) : card (pmap f s H) = card s :=
  Quot.inductionOn s (fun _l _H => length_pmap) H

/-- "Attach" a proof that `a ∈ s` to each element `a` in `s` to produce
  a multiset on `{x // x ∈ s}`. -/
def attach (s : Multiset α) : Multiset { x // x ∈ s } :=
  pmap Subtype.mk s fun _a => id

@[simp]
theorem coe_attach (l : List α) : @Eq (Multiset { x // x ∈ l }) (@attach α l) l.attach :=
  rfl

@[simp]
theorem mem_attach (s : Multiset α) : ∀ x, x ∈ s.attach :=
  Quot.inductionOn s fun _l => List.mem_attach _

@[simp]
theorem card_attach {m : Multiset α} : card (attach m) = card m :=
  card_pmap _ _ _

section Decidable

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

end Decidable

/-- `Pairwise r m` states that there exists a list of the elements s.t. `r` holds pairwise on this
list. -/
def Pairwise (r : α → α → Prop) (m : Multiset α) : Prop :=
  ∃ l : List α, m = l ∧ l.Pairwise r

theorem pairwise_coe_iff {r : α → α → Prop} {l : List α} :
    Multiset.Pairwise r l ↔ ∃ l' : List α, l ~ l' ∧ l'.Pairwise r :=
  exists_congr <| by simp

theorem pairwise_coe_iff_pairwise {r : α → α → Prop} (hr : Symmetric r) {l : List α} :
    Multiset.Pairwise r l ↔ l.Pairwise r :=
  Iff.intro (fun ⟨_l', Eq, h⟩ => ((Quotient.exact Eq).pairwise_iff @hr).2 h) fun h => ⟨l, rfl, h⟩

section Nodup

/-- `Nodup s` means that `s` has no duplicates, i.e. the multiplicity of
  any element is at most 1. -/
def Nodup (s : Multiset α) : Prop :=
  Quot.liftOn s List.Nodup fun _ _ p => propext p.nodup_iff

@[simp]
theorem coe_nodup {l : List α} : @Nodup α l ↔ l.Nodup :=
  Iff.rfl

theorem Nodup.ext {s t : Multiset α} : Nodup s → Nodup t → (s = t ↔ ∀ a, a ∈ s ↔ a ∈ t) :=
  Quotient.inductionOn₂ s t fun _ _ d₁ d₂ => Quotient.eq.trans <| perm_ext_iff_of_nodup d₁ d₂

theorem le_iff_subset {s t : Multiset α} : Nodup s → (s ≤ t ↔ s ⊆ t) :=
  Quotient.inductionOn₂ s t fun _ _ d => ⟨subset_of_le, d.subperm⟩

theorem nodup_of_le {s t : Multiset α} (h : s ≤ t) : Nodup t → Nodup s :=
  Multiset.leInductionOn h fun {_ _} => Nodup.sublist

instance nodupDecidable [DecidableEq α] (s : Multiset α) : Decidable (Nodup s) :=
  Quotient.recOnSubsingleton s fun l => l.nodupDecidable

end Nodup

section SizeOf

/-- Defines a size for a multiset by referring to the size of the underlying list.

This has to be defined before the definition of `Finset`, otherwise its automatically generated
`SizeOf` instance will be wrong.
-/
protected
def sizeOf [SizeOf α] (s : Multiset α) : ℕ :=
  (Quot.liftOn s SizeOf.sizeOf) fun _ _ => Perm.sizeOf_eq_sizeOf

instance [SizeOf α] : SizeOf (Multiset α) :=
  ⟨Multiset.sizeOf⟩

end SizeOf

end Multiset
