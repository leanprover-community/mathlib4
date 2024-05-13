/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Group.Fin
import Mathlib.Data.List.Basic

#align_import data.array.lemmas from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
Porting note:
Following the discussion on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/287929-
mathlib4/topic/porting.20.60.2Earray.60.20files.20whose.20PR's.20were.20closed.3F), these
will wait until Batteries has finalized `DArray` and `Array'` types so we can translates
apples to apples.

`align` for lemmas about lean3/mathlib3 versions of d_array and array with mathport output
-/

universe u v w

namespace DArray

-- variable {n : ℕ} {α : Fin n → Type u}

-- instance [∀ i, Inhabited (α i)] : Inhabited (DArray n α) :=
--   ⟨⟨default⟩⟩

end DArray

namespace Array'

-- instance {n α} [Inhabited α] : Inhabited (Array' n α) :=
--   DArray.inhabited

-- theorem toList_of_hEq {n₁ n₂ α} {a₁ : Array' n₁ α} {a₂ : Array' n₂ α} (hn : n₁ = n₂)
--     (ha : HEq a₁ a₂) : a₁.toList = a₂.toList := by congr <;> assumption
#noalign array.to_list_of_heq

-- rev_list
section RevList

-- variable {n : ℕ} {α : Type u} {a : Array' n α}

-- theorem rev_list_reverse_aux :
--     ∀ (i) (h : i ≤ n) (t : List α),
--       (a.iterateAux (fun _ => (· :: ·)) i h []).reverseAux t =
--         a.revIterateAux (fun _ => (· :: ·)) i h t
--   | 0, h, t => rfl
--   | i + 1, h, t => rev_list_reverse_aux i _ _
#noalign array.rev_list_reverse_aux -- Array'.rev_list_reverse_aux

-- @[simp]
-- theorem revList_reverse : a.revList.reverse = a.toList :=
--   rev_list_reverse_aux _ _ _
#noalign array.rev_list_reverse -- Array'.revList_reverse

-- @[simp]
-- theorem toList_reverse : a.toList.reverse = a.revList := by
--   rw [← rev_list_reverse, List.reverse_reverse]
#noalign array.to_list_reverse -- Array'.toList_reverse

end RevList

-- mem
section Mem

-- variable {n : ℕ} {α : Type u} {v : α} {a : Array' n α}

-- theorem Mem.def : v ∈ a ↔ ∃ i, a.read i = v :=
--   Iff.rfl
#noalign array.mem.def --Array'.Mem.def

-- theorem mem_rev_list_aux :
--     ∀ {i} (h : i ≤ n),
--       (∃ j : Fin n, (j : ℕ) < i ∧ read a j = v) ↔ v ∈ a.iterateAux (fun _ => (· :: ·)) i h []
--   | 0, _ => ⟨fun ⟨i, n, _⟩ => absurd n i.val.not_lt_zero, False.elim⟩
--   | i + 1, h =>
--     let IH := mem_rev_list_aux (le_of_lt h)
--     ⟨fun ⟨j, ji1, e⟩ =>
--       Or.elim (lt_or_eq_of_le <| Nat.le_of_succ_le_succ ji1)
--         (fun ji => List.mem_cons_of_mem _ <| IH.1 ⟨j, ji, e⟩) fun je => by
--         simp [DArray.iterateAux] <;> apply Or.inl <;> unfold read at e <;>
--             have H : j = ⟨i, h⟩ := Fin.eq_of_veq je <;>
--           rwa [← H, e],
--       fun m => by
--       simp [DArray.iterateAux, List.Mem] at m
--       cases' m with e m'
--       exact ⟨⟨i, h⟩, Nat.lt_succ_self _, Eq.symm e⟩
--       exact
--         let ⟨j, ji, e⟩ := IH.2 m'
--         ⟨j, Nat.le_succ_of_le ji, e⟩⟩
#noalign array.mem_rev_list_aux --Array'.mem_rev_list_aux

-- @[simp]
-- theorem mem_revList : v ∈ a.revList ↔ v ∈ a :=
--   Iff.symm <|
--     Iff.trans
--       (exists_congr fun j =>
--         Iff.symm <| show j.1 < n ∧ read a j = v ↔ read a j = v from and_iff_right j.2)
--       (mem_rev_list_aux _)
#noalign array.mem_rev_list --Array'.mem_revList

-- @[simp]
-- theorem mem_toList : v ∈ a.toList ↔ v ∈ a := by
--   rw [← rev_list_reverse] <;> exact list.mem_reverse.trans mem_rev_list
#noalign array.mem_to_list --Array'.mem_toList

end Mem

-- foldr
section Foldr

-- variable {n : ℕ} {α : Type u} {β : Type w} {b : β} {f : α → β → β} {a : Array' n α}

-- theorem rev_list_foldr_aux :
--     ∀ {i} (h : i ≤ n),
--       (DArray.iterateAux a (fun _ => (· :: ·)) i h []).foldr f b =
--         DArray.iterateAux a (fun _ => f) i h b
--   | 0, h => rfl
--   | j + 1, h => congr_arg (f (read a ⟨j, h⟩)) (rev_list_foldr_aux _)
#noalign array.rev_list_foldr_aux --Array'.rev_list_foldr_aux

-- theorem revList_foldr : a.revList.foldr f b = a.foldl b f :=
--   rev_list_foldr_aux _
#noalign array.rev_list_foldr --Array'.revList_foldr

end Foldr

-- foldl
section Foldl

-- variable {n : ℕ} {α : Type u} {β : Type w} {b : β} {f : β → α → β} {a : Array' n α}

-- theorem toList_foldl : a.toList.foldl f b = a.foldl b (Function.swap f) := by
--   rw [← rev_list_reverse, List.foldl_reverse, rev_list_foldr]
#noalign array.to_list_foldl --Array'.toList_foldl


end Foldl

-- length
section Length

-- variable {n : ℕ} {α : Type u}

-- theorem rev_list_length_aux (a : Array' n α) (i h) :
--     (a.iterateAux (fun _ => (· :: ·)) i h []).length = i := by
--   induction i <;> simp [*, DArray.iterateAux]
#noalign array.rev_list_length_aux -- Array'.rev_list_length_aux

-- @[simp]
-- theorem revList_length (a : Array' n α) : a.revList.length = n :=
--   rev_list_length_aux a _ _
#noalign array.rev_list_length --Array'.revList_length

-- @[simp]
-- theorem toList_length (a : Array' n α) : a.toList.length = n := by
--   rw [← rev_list_reverse, List.length_reverse, rev_list_length]
#noalign array.to_list_length --Array'.toList_length

end Length

-- nth
section Nth

-- variable {n : ℕ} {α : Type u} {a : Array' n α}

-- theorem to_list_nthLe_aux (i : ℕ) (ih : i < n) :
--     ∀ (j) {jh t h'},
--       (∀ k tl, j + k = i → List.nthLe t k tl = a.read ⟨i, ih⟩) →
--         (a.revIterateAux (fun _ => (· :: ·)) j jh t).nthLe i h' = a.read ⟨i, ih⟩
--   | 0, _, _, _, al => al i _ <| zero_add _
--   | j + 1, jh, t, h', al =>
--     to_list_nth_le_aux j fun k tl hjk =>
--       show List.nthLe (a.read ⟨j, jh⟩ :: t) k tl = a.read ⟨i, ih⟩ from
--         match k, hjk, tl with
--         | 0, e, tl =>
--           match i, e, ih with
--           | _, rfl, _ => rfl
--         | k' + 1, _, tl => by
--           simp [List.nthLe] <;> exact al _ _ (by simp [add_comm, add_assoc, *] <;> cc)
#noalign array.to_list_nth_le_aux --Array'.to_list_nthLe_aux

-- theorem toList_nthLe (i : ℕ) (h h') : List.nthLe a.toList i h' = a.read ⟨i, h⟩ :=
--   to_list_nthLe_aux _ _ _ fun k tl => absurd tl k.not_lt_zero
#noalign array.to_list_nth_le --Array'.toList_nthLe

-- @[simp]
-- theorem toList_nth_le' (a : Array' n α) (i : Fin n) (h') : List.nthLe a.toList i h'
--    = a.read i := by
--   cases i <;> apply to_list_nth_le
#noalign array.to_list_nth_le' -- Array'.toList_nth_le'

-- theorem toList_get? {i v} : List.get? a.toList i = some v ↔ ∃ h, a.read ⟨i, h⟩ = v := by
--   rw [List.get?_eq_some']
--   have ll := to_list_length a
--   constructor <;> intro h <;> cases' h with h e <;> subst v
--   · exact ⟨ll ▸ h, (to_list_nth_le _ _ _).symm⟩
--   · exact ⟨ll.symm ▸ h, to_list_nth_le _ _ _⟩
#noalign array.to_list_nth --Array'.toList_get?

-- theorem write_toList {i v} : (a.write i v).toList = a.toList.set i v :=
--   List.ext_nthLe (by simp) fun j h₁ h₂ => by
--     have h₃ : j < n := by simpa using h₁
--     rw [to_list_nth_le _ h₃]
--     refine'
--       let ⟨_, e⟩ := List.get?_eq_some'.1 _
--       e.symm
--     by_cases ij : (i : ℕ) = j
--     · subst j
--       rw [show (⟨(i : ℕ), h₃⟩ : Fin _) = i from Fin.eq_of_veq rfl, Array'.read_write,
--         List.get?_set_eq_of_lt]
--       simp [h₃]
--     · rw [List.get?_set_ne _ _ ij, a.read_write_of_ne, to_list_nth.2 ⟨h₃, rfl⟩]
--       exact Fin.ne_of_vne ij
#noalign array.write_to_list --Array'.write_toList

end Nth

-- enum
section Enum

-- variable {n : ℕ} {α : Type u} {a : Array' n α}

-- theorem mem_toList_enum {i v} : (i, v) ∈ a.toList.enum ↔ ∃ h, a.read ⟨i, h⟩ = v := by
--   simp [List.mem_iff_get?, to_list_nth, and_comm, and_assoc, and_left_comm]
#noalign array.mem_to_list_enum --Array'.mem_toList_enum

end Enum

-- to_array
section ToArray

-- variable {n : ℕ} {α : Type u}

-- @[simp]
-- theorem toList_toArray (a : Array' n α) : HEq a.toList.toArray a :=
--   hEq_of_hEq_of_eq
--       (@Eq.drecOn
--         (fun m (e : a.toList.length = m) =>
--           HEq (DArray.mk fun v => a.toList.nthLe v.1 v.2)
--             (@DArray.mk m (fun _ => α) fun v => a.toList.nthLe v.1 <| e.symm ▸ v.2))
--         a.toList_length HEq.rfl) <|
--     DArray.ext fun ⟨i, h⟩ => toList_nthLe i h _
#noalign array.to_list_to_array --Array'.toList_toArray

-- @[simp]
-- theorem toArray_toList (l : List α) : l.toArray.toList = l :=
--   List.ext_nthLe (toList_length _) fun n h1 h2 => toList_nthLe _ h2 _
#noalign array.to_array_to_list --Array'.toArray_toList

end ToArray

-- push_back
section PushBack

-- variable {n : ℕ} {α : Type u} {v : α} {a : Array' n α}

-- theorem pushBack_rev_list_aux :
--     ∀ i h h',
--       DArray.iterateAux (a.pushBack v) (fun _ => (· :: ·)) i h [] =
--         DArray.iterateAux a (fun _ => (· :: ·)) i h' []
--   | 0, h, h' => rfl
--   | i + 1, h, h' => by
--     simp [DArray.iterateAux]
--     refine' ⟨_, push_back_rev_list_aux _ _ _⟩
--     dsimp [read, DArray.read, push_back]
--     rw [dif_neg]; rfl
--     exact ne_of_lt h'
#noalign array.push_back_rev_list_aux -- Array'.pushBack_rev_list_aux

-- @[simp]
-- theorem pushBack_revList : (a.pushBack v).revList = v :: a.revList := by
--   unfold push_back rev_list foldl iterate DArray.iterate
--   dsimp [DArray.iterateAux, read, DArray.read, push_back]
--   rw [dif_pos (Eq.refl n)]
--   apply congr_arg
--   apply push_back_rev_list_aux
#noalign array.push_back_rev_list -- Array'.pushBack_revList

-- @[simp]
-- theorem pushBack_toList : (a.pushBack v).toList = a.toList ++ [v] := by
--   rw [← rev_list_reverse, ← rev_list_reverse, push_back_rev_list, List.reverse_cons]
#noalign array.push_back_to_list -- Array'.pushBack_toList

-- @[simp]
-- theorem read_pushBack_left (i : Fin n) : (a.pushBack v).read i.cast_succ = a.read i := by
--   cases' i with i hi
--   have : ¬i = n := ne_of_lt hi
--   simp [push_back, this, Fin.castSucc, Fin.castAdd, Fin.castLe, Fin.castLt, read, DArray.read]
#noalign array.read_push_back_left -- Array'.read_pushBack_left

-- @[simp]
-- theorem read_pushBack_right : (a.pushBack v).read (Fin.last _) = v := by
--   cases' hn : Fin.last n with k hk
--   have : k = n := by simpa [Fin.ext_iff] using hn.symm
--   simp [push_back, this, Fin.castSucc, Fin.castAdd, Fin.castLe, Fin.castLt, read, DArray.read]
#noalign array.read_push_back_right -- Array'.read_pushBack_right

end PushBack

-- foreach
section Foreach

-- variable {n : ℕ} {α : Type u} {β : Type v} {i : Fin n} {f : Fin n → α → β} {a : Array' n α}
--
-- @[simp]
-- theorem read_foreach : (foreach a f).read i = f i (a.read i) :=
--   rfl
#noalign array.read_foreach -- Array'.read_foreach

end Foreach

-- map
section Map

-- variable {n : ℕ} {α : Type u} {β : Type v} {i : Fin n} {f : α → β} {a : Array' n α}
--
-- theorem read_map : (a.map f).read i = f (a.read i) :=
--   read_foreach
#noalign array.read_map -- Array'.read_map

end Map

-- map₂
section Map₂

-- variable {n : ℕ} {α : Type u} {i : Fin n} {f : α → α → α} {a₁ a₂ : Array' n α}
--
-- @[simp]
-- theorem read_map₂ : (map₂ f a₁ a₂).read i = f (a₁.read i) (a₂.read i) :=
--   read_foreach
#noalign array.read_map₂ --Array'.read_map₂

end Map₂

end Array'
