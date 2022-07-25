/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Perm
import Mathlib.Algebra.Group.Defs

/-!
# Multisets
These are implemented as the quotient of a List by permutations.
## Notation
We define the global infix notation `::ₘ` for `Multiset.cons`.
-/

open List Subtype Nat

/-- `Multiset α` is the quotient of `List α` by List permutation. The result
  is a type of finite sets with duplicates allowed.  -/
def Multiset (α : Type u) : Type u :=
  Quotient (instSetoidList α)

namespace Multiset

instance : Coe (List α) (Multiset α) := ⟨Quot.mk _⟩

@[simp] theorem quot_mk_to_coe (l : List α) : @Eq (Multiset α) (Quotient.mk' l) l := rfl

@[simp] theorem quot_mk_to_coe' (l : List α) : @Eq (Multiset α) (Quot.mk (·≈·) l) l := rfl

@[simp] theorem quot_mk_to_coe'' (l : List α) : @Eq (Multiset α) (Quot.mk Setoid.r l) l := rfl

@[simp] theorem coe_eq_coe {l₁ l₂ : List α} : (l₁ : Multiset α) = (l₂ : Multiset α) ↔ l₁ ~ l₂ :=
  ⟨Quotient.exact, Quot.sound⟩

instance [DecidableEq α] : DecidableEq (Multiset α) :=
  fun s₁ s₂ => sorry
  -- Quotient.rec_on_subsingleton₂ s₁ s₂ $ λ l₁ l₂ =>
  --   decidable_of_iff' _ quotient.eq

/-- defines a size for a Multiset by referring to the size of the underlying List -/
protected def SizeOfAux [SizeOf α] (s : Multiset α) : ℕ := sorry
-- Quot.liftOn s sizeof $ λ l₁ l₂ => perm.sizeof_eq_sizeof

instance SizeOf [SizeOf α] : SizeOf (Multiset α) := ⟨Multiset.SizeOfAux⟩

/-! ### Empty Multiset -/

/-- `0 : Multiset α` is the empty set -/
protected def zero : Multiset α := @nil α

instance : Zero (Multiset α)   := ⟨Multiset.zero⟩
-- instance : has_emptyc (Multiset α) := ⟨0⟩
instance inhabited_Multiset : Inhabited (Multiset α)  := ⟨0⟩

@[simp] theorem coe_nil_eq_zero : (@nil α : Multiset α) = (0 : Multiset α) := rfl
-- @[simp] theorem empty_eq_zero : (∅ : Multiset α) = 0 := rfl

@[simp] theorem coe_eq_zero (l : List α) : (l : Multiset α) = (0 : Multiset α) ↔ l = [] :=
Iff.trans coe_eq_coe perm_nil

/-! ### `Multiset.cons` -/

/-- `cons a s` is the Multiset which contains `s` plus one more
  instance of `a`. -/
def cons (a : α) (s : Multiset α) : Multiset α :=
  Quot.liftOn s (λ l => (a :: l : Multiset α)) (λ _ _ p => Quot.sound (p.cons a))

infixr:67 " ::ₘ " => Multiset.cons

-- instance : has_insert α (Multiset α) := ⟨cons⟩

-- @[simp] theorem insert_eq_cons (a : α) (s : Multiset α) :
--   insert a s = a ::ₘ s := rfl

@[simp] theorem cons_coe (a : α) (l : List α) :
  (a ::ₘ l : Multiset α) = (a::l : List α) := rfl

theorem singleton_coe (a : α) : (a ::ₘ 0 : Multiset α) = ([a] : List α) := rfl

-- @[simp] theorem cons_inj_left {a b : α} (s : Multiset α) :
--   a ::ₘ s = b ::ₘ s ↔ a = b :=
-- ⟨Quot.induction s $ λ l e =>
--   have [a] ++ l ~ [b] ++ l, from quotient.exact e,
--   singleton_perm_singleton.1 $ (perm_append_right_iff _).1 this, congr_arg _⟩

-- @[simp] theorem cons_inj_right (a : α) : ∀{s t : Multiset α}, a ::ₘ s = a ::ₘ t ↔ s = t :=
-- by rintro ⟨l₁⟩ ⟨l₂⟩; simp

section mem

/-- `a ∈ s` means that `a` has nonzero multiplicity in `s`. -/
def mem (a : α) (s : Multiset α) : Prop :=
Quot.liftOn s (λ l => a ∈ l) (λ l₁ l₂ (e : l₁ ~ l₂) => propext $ e.mem_iff)

instance : Membership α (Multiset α) := ⟨mem⟩

@[simp] lemma mem_coe {a : α} {l : List α} :
  Membership.mem (γ := Multiset α) a (l : Multiset α) ↔ a ∈ l := Iff.rfl

instance [DecidableEq α] (a : α) (s : Multiset α) : Decidable (a ∈ s) := sorry
-- Quot.rec_on_subsingleton s $ List.decidable_mem a

-- @[simp] theorem mem_cons {a b : α} {s : Multiset α} : a ∈ b ::ₘ s ↔ a = b ∨ a ∈ s :=
-- quot.induction_on s $ λ l, iff.rfl

-- lemma mem_cons_of_mem {a b : α} {s : Multiset α} (h : a ∈ s) : a ∈ b ::ₘ s :=
-- mem_cons.2 $ or.inr h

-- @[simp] theorem mem_cons_self (a : α) (s : Multiset α) : a ∈ a ::ₘ s :=
-- mem_cons.2 (or.inl rfl)

-- theorem forall_mem_cons {p : α → Prop} {a : α} {s : Multiset α} :
--   (∀ x ∈ (a ::ₘ s), p x) ↔ p a ∧ ∀ x ∈ s, p x :=
-- quotient.induction_on' s $ λ L, List.forall_mem_cons

-- theorem exists_cons_of_mem {s : Multiset α} {a : α} : a ∈ s → ∃ t, s = a ::ₘ t :=
-- quot.induction_on s $ λ l (h : a ∈ l),
-- let ⟨l₁, l₂, e⟩ := mem_split h in
-- e.symm ▸ ⟨(l₁++l₂ : List α), quot.sound perm_middle⟩

-- @[simp] theorem not_mem_zero (a : α) : a ∉ (0 : Multiset α) := id

-- theorem eq_zero_of_forall_not_mem {s : Multiset α} : (∀x, x ∉ s) → s = 0 :=
-- quot.induction_on s $ λ l H, by rw eq_nil_iff_forall_not_mem.mpr H; refl

-- theorem eq_zero_iff_forall_not_mem {s : Multiset α} : s = 0 ↔ ∀ a, a ∉ s :=
-- ⟨λ h, h.symm ▸ λ _, not_false, eq_zero_of_forall_not_mem⟩

-- theorem exists_mem_of_ne_zero {s : Multiset α} : s ≠ 0 → ∃ a : α, a ∈ s :=
-- quot.induction_on s $ assume l hl,
--   match l, hl with
--   | [] := assume h, false.elim $ h rfl
--   | (a :: l) := assume _, ⟨a, by simp⟩
--   end

-- lemma empty_or_exists_mem (s : Multiset α) : s = 0 ∨ ∃ a, a ∈ s :=
-- or_iff_not_imp_left.mpr Multiset.exists_mem_of_ne_zero

-- @[simp] lemma zero_ne_cons {a : α} {m : Multiset α} : 0 ≠ a ::ₘ m :=
-- assume h, have a ∈ (0:Multiset α), from h.symm ▸ mem_cons_self _ _, not_mem_zero _ this

-- @[simp] lemma cons_ne_zero {a : α} {m : Multiset α} : a ::ₘ m ≠ 0 := zero_ne_cons.symm

-- lemma cons_eq_cons {a b : α} {as bs : Multiset α} :
--   a ::ₘ as = b ::ₘ bs ↔ ((a = b ∧ as = bs) ∨ (a ≠ b ∧ ∃cs, as = b ::ₘ cs ∧ bs = a ::ₘ cs)) :=
-- begin
--   haveI : DecidableEq α := classical.dec_eq α,
--   split,
--   { assume eq,
--     by_cases a = b,
--     { subst h, simp * at * },
--     { have : a ∈ b ::ₘ bs, from eq ▸ mem_cons_self _ _,
--       have : a ∈ bs, by simpa [h],
--       rcases exists_cons_of_mem this with ⟨cs, hcs⟩,
--       simp [h, hcs],
--       have : a ::ₘ as = b ::ₘ a ::ₘ cs, by simp [eq, hcs],
--       have : a ::ₘ as = a ::ₘ b ::ₘ cs, by rwa [cons_swap],
--       simpa using this } },
--   { assume h,
--     rcases h with ⟨eq₁, eq₂⟩ | ⟨h, cs, eq₁, eq₂⟩,
--     { simp * },
--     { simp [*, cons_swap a b] } }
-- end

end mem
