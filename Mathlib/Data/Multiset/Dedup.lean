/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Multiset.Nodup

#align_import data.multiset.dedup from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# Erasing duplicates in a multiset.
-/


namespace Multiset

open List

variable {α β : Type*} [DecidableEq α]

/-! ### dedup -/


/-- `dedup s` removes duplicates from `s`, yielding a `nodup` multiset. -/
def dedup (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (l.dedup : Multiset α)) fun _ _ p => Quot.sound p.dedup

@[simp]
theorem coe_dedup (l : List α) : @dedup α _ l = l.dedup :=
  rfl

@[simp]
theorem dedup_zero : @dedup α _ 0 = 0 :=
  rfl

@[simp]
theorem mem_dedup {a : α} {s : Multiset α} : a ∈ dedup s ↔ a ∈ s :=
  Quot.induction_on s fun _ => List.mem_dedup

@[simp]
theorem dedup_cons_of_mem {a : α} {s : Multiset α} : a ∈ s → dedup (a ::ₘ s) = dedup s :=
  Quot.induction_on s fun _ m => @congr_arg _ _ _ _ ofList <| List.dedup_cons_of_mem m

@[simp]
theorem dedup_cons_of_not_mem {a : α} {s : Multiset α} : a ∉ s → dedup (a ::ₘ s) = a ::ₘ dedup s :=
  Quot.induction_on s fun _ m => congr_arg ofList <| List.dedup_cons_of_not_mem m

theorem dedup_le (s : Multiset α) : dedup s ≤ s :=
  Quot.induction_on s fun _ => (dedup_sublist _).subperm

theorem dedup_subset (s : Multiset α) : dedup s ⊆ s :=
  subset_of_le <| dedup_le _

theorem subset_dedup (s : Multiset α) : s ⊆ dedup s := fun _ => mem_dedup.2

@[simp]
theorem dedup_subset' {s t : Multiset α} : dedup s ⊆ t ↔ s ⊆ t :=
  ⟨Subset.trans (subset_dedup _), Subset.trans (dedup_subset _)⟩

@[simp]
theorem subset_dedup' {s t : Multiset α} : s ⊆ dedup t ↔ s ⊆ t :=
  ⟨fun h => Subset.trans h (dedup_subset _), fun h => Subset.trans h (subset_dedup _)⟩

@[simp]
theorem nodup_dedup (s : Multiset α) : Nodup (dedup s) :=
  Quot.induction_on s List.nodup_dedup

theorem dedup_eq_self {s : Multiset α} : dedup s = s ↔ Nodup s :=
  ⟨fun e => e ▸ nodup_dedup s, Quot.induction_on s fun _ h => congr_arg ofList h.dedup⟩

alias ⟨_, Nodup.dedup⟩ := dedup_eq_self

theorem count_dedup (m : Multiset α) (a : α) : m.dedup.count a = if a ∈ m then 1 else 0 :=
  Quot.induction_on m fun _ => by
    simp only [quot_mk_to_coe'', coe_dedup, mem_coe, List.mem_dedup, coe_nodup, coe_count]
    apply List.count_dedup _ _

@[simp]
theorem dedup_idem {m : Multiset α} : m.dedup.dedup = m.dedup :=
  Quot.induction_on m fun _ => @congr_arg _ _ _ _ ofList List.dedup_idem

@[simp]
theorem dedup_bind_dedup [DecidableEq β] (m : Multiset α) (f : α → Multiset β) :
    (m.dedup.bind f).dedup = (m.bind f).dedup := by
  ext x
  -- Porting note: was `simp_rw [count_dedup, mem_bind, mem_dedup]`
  simp_rw [count_dedup]
  refine if_congr ?_ rfl rfl
  simp

theorem dedup_eq_zero {s : Multiset α} : dedup s = 0 ↔ s = 0 :=
  ⟨fun h => eq_zero_of_subset_zero <| h ▸ subset_dedup _, fun h => h.symm ▸ dedup_zero⟩

@[simp]
theorem dedup_singleton {a : α} : dedup ({a} : Multiset α) = {a} :=
  (nodup_singleton _).dedup

theorem le_dedup {s t : Multiset α} : s ≤ dedup t ↔ s ≤ t ∧ Nodup s :=
  ⟨fun h => ⟨le_trans h (dedup_le _), nodup_of_le h (nodup_dedup _)⟩,
   fun ⟨l, d⟩ => (le_iff_subset d).2 <| Subset.trans (subset_of_le l) (subset_dedup _)⟩

theorem le_dedup_self {s : Multiset α} : s ≤ dedup s ↔ Nodup s := by
  rw [le_dedup, and_iff_right le_rfl]

theorem dedup_ext {s t : Multiset α} : dedup s = dedup t ↔ ∀ a, a ∈ s ↔ a ∈ t := by
  simp [Nodup.ext]

theorem dedup_map_dedup_eq [DecidableEq β] (f : α → β) (s : Multiset α) :
    dedup (map f (dedup s)) = dedup (map f s) := by
  simp [dedup_ext]

@[simp]
theorem dedup_nsmul {s : Multiset α} {n : ℕ} (h0 : n ≠ 0) : (n • s).dedup = s.dedup := by
  ext a
  by_cases h : a ∈ s <;> simp [h, h0]

theorem Nodup.le_dedup_iff_le {s t : Multiset α} (hno : s.Nodup) : s ≤ t.dedup ↔ s ≤ t := by
  simp [le_dedup, hno]

end Multiset

theorem Multiset.Nodup.le_nsmul_iff_le {α : Type*} {s t : Multiset α} {n : ℕ} (h : s.Nodup)
    (hn : n ≠ 0) : s ≤ n • t ↔ s ≤ t := by
  classical
    rw [← h.le_dedup_iff_le, Iff.comm, ← h.le_dedup_iff_le]
    simp [hn]
