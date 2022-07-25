import Mathlib.Data.Multiset.EraseDup

open Multiset Subtype Nat

/-- `Finset α` is the type of finite sets of elements of `α`. It is implemented
  as a multiset (a list up to permutation) which has no duplicate elements. -/
structure Finset (α : Type u) :=
  val : Multiset α
  nodup : Nodup val

namespace Finset

theorem eq_of_veq : ∀ {s t : Finset α}, s.1 = t.1 → s = t := by
  rintro ⟨s, _⟩ ⟨t, _⟩ rfl; rfl

@[simp] theorem val_inj {s t : Finset α} : s.1 = t.1 ↔ s = t :=
⟨eq_of_veq, congr_arg _⟩

@[simp] theorem dedup_eq_self [DecidableEq α] (s : Finset α) : eraseDup s.1 = s.1 :=
  s.2.eraseDup

instance DecidableEq [DecidableEq α] : DecidableEq (Finset α) :=
  fun _ _ => decidable_of_iff _ val_inj

/-! ### membership -/

instance : Membership α (Finset α) := ⟨λ a s => a ∈ s.1⟩

theorem mem_def {a : α} {s : Finset α} : a ∈ s ↔ a ∈ s.1 := Iff.rfl

@[simp] theorem mem_mk {a : α} {s nd} : a ∈ @Finset.mk α s nd ↔ a ∈ s := Iff.rfl

-- instance Decidable_mem [h : DecidableEq α] (a : α) (s : Finset α) : Decidable (a ∈ s) :=
-- multiset.DecidableMem _ _

-- /-! ### set coercion -/

-- /-- Convert a Finset to a set in the natural way. -/
-- instance : has_coe_t (Finset α) (set α) := ⟨λ s, {x | x ∈ s}⟩

-- @[simp, norm_cast] lemma mem_coe {a : α} {s : Finset α} : a ∈ (s : set α) ↔ a ∈ s := Iff.rfl

-- @[simp] lemma set_of_mem {α} {s : Finset α} : {a | a ∈ s} = s := rfl

-- @[simp] lemma coe_mem {s : Finset α} (x : (s : set α)) : ↑x ∈ s := x.2

-- @[simp] lemma mk_coe {s : Finset α} (x : (s : set α)) {h} :
--   (⟨x, h⟩ : (s : set α)) = x :=
-- subtype.coe_eta _ _

-- instance Decidable_mem' [DecidableEq α] (a : α) (s : Finset α) :
--   Decidable (a ∈ (s : set α)) := s.Decidable_mem _

-- /-! ### extensionality -/
-- theorem ext_Iff {s₁ s₂ : Finset α} : s₁ = s₂ ↔ ∀ a, a ∈ s₁ ↔ a ∈ s₂ :=
-- val_inj.symm.trans $ s₁.nodup.ext s₂.nodup

-- @[ext]
-- theorem ext {s₁ s₂ : Finset α} : (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂ :=
-- ext_Iff.2
