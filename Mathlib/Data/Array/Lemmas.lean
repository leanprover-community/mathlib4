/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro

! This file was ported from Lean 3 source module data.array.lemmas
! leanprover-community/mathlib commit 78314d08d707a6338079f00094bbdb90bf11fc41
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Control.Traversable.Equiv
import Mathlib.Data.Vector.Basic
import Mathlib.Init.Data.Array.Basic
universe u v w

namespace DArray

variable {n : ℕ} {α : Fin n → Type u}

instance [∀ i, Inhabited (α i)] : Inhabited (DArray n α) :=
  ⟨⟨default⟩⟩

end DArray

namespace Array'

instance {n α} [Inhabited α] : Inhabited (Array' n α) := DArray.instInhabitedDArray

theorem toList_of_hEq {n₁ n₂ α} {a₁ : Array' n₁ α} {a₂ : Array' n₂ α} (hn : n₁ = n₂)
    (ha : HEq a₁ a₂) : a₁.toList = a₂.toList := by
  congr
#align array.to_list_of_heq Array'.toList_of_hEq

-- rev_list
section RevList

variable {n : ℕ} {α : Type u} {a : Array' n α}

theorem rev_list_reverse_aux : ∀ (i) (h : i ≤ n) (t : List α),
    (a.iterateAux (fun _ ↦ (· :: ·)) i h []).reverseAux t = a.revIterateAux (fun _ ↦ (· :: ·)) i h t
  | 0, _, _ => rfl
  | i + 1, _, _ => rev_list_reverse_aux i _ _
#align array.rev_list_reverse_aux Array'.rev_list_reverse_aux

@[simp]
theorem revList_reverse : a.revList.reverse = a.toList :=
  rev_list_reverse_aux _ _ _
#align array.rev_list_reverse Array'.revList_reverse

@[simp]
theorem toList_reverse : a.toList.reverse = a.revList := by
  rw [← revList_reverse, List.reverse_reverse]
#align array.to_list_reverse Array'.toList_reverse

end RevList

-- mem
section Mem

variable {n : ℕ} {α : Type u} {v : α} {a : Array' n α}

theorem Mem.def : v ∈ a ↔ ∃ i, a.read i = v :=
  Iff.rfl
#align array.mem.def Array'.Mem.def

theorem mem_rev_list_aux : ∀ {i} (h : i ≤ n),
    (∃ j : Fin n, j < i ∧ read a j = v) ↔ v ∈ a.iterateAux (fun _ ↦ (· :: ·)) i h []
  | 0, _ => ⟨fun ⟨i, n, _⟩ ↦ absurd n i.val.not_lt_zero, fun h ↦ by cases h⟩
  | i + 1, h =>
    let IH := mem_rev_list_aux (le_of_lt h)
    ⟨fun ⟨j, ji1, e⟩ ↦
      Or.elim (lt_or_eq_of_le <| Nat.le_of_succ_le_succ ji1)
        (fun ji ↦ List.mem_cons_of_mem _ <| IH.1 ⟨j, ji, e⟩) fun je ↦ by
          simp only [DArray.iterateAux, Nat.add_eq, add_zero, List.mem_cons]
          apply Or.inl
          unfold read at e
          have H : j = ⟨i, h⟩ := Fin.eq_of_veq je
          rw [← H, e],
      fun m ↦ by
        simp only [DArray.iterateAux, Nat.add_eq, add_zero, List.mem_cons] at m
        cases' m with e m'
        exact ⟨⟨i, h⟩, Nat.lt_succ_self _, Eq.symm e⟩
        exact
          let ⟨j, ji, e⟩ := IH.2 m'
          ⟨j, Nat.le_succ_of_le ji, e⟩⟩
#align array.mem_rev_list_aux Array'.mem_rev_list_aux

@[simp]
theorem mem_revList : v ∈ a.revList ↔ v ∈ a :=
  Iff.symm <| Iff.trans
    (exists_congr fun j ↦
      Iff.symm <| show j.1 < n ∧ read a j = v ↔ read a j = v from and_iff_right j.2)
    (mem_rev_list_aux _)
#align array.mem_rev_list Array'.mem_revList

@[simp]
theorem mem_toList : v ∈ a.toList ↔ v ∈ a := by
  rw [← revList_reverse, List.mem_reverse, mem_revList]
#align array.mem_to_list Array'.mem_toList

end Mem

-- foldr
section Foldr

variable {n : ℕ} {α : Type u} {β : Type w} {b : β} {f : α → β → β} {a : Array' n α}

theorem rev_list_foldr_aux : ∀ {i} (h : i ≤ n),
    (DArray.iterateAux a (fun _ ↦ (· :: ·)) i h []).foldr f b =
      DArray.iterateAux a (fun _ ↦ f) i h b
  | 0, _ => rfl
  | j + 1, h => congr_arg (f (read a ⟨j, h⟩)) (rev_list_foldr_aux _)
#align array.rev_list_foldr_aux Array'.rev_list_foldr_aux

theorem revList_foldr : a.revList.foldr f b = a.foldl b f :=
  rev_list_foldr_aux _
#align array.rev_list_foldr Array'.revList_foldr

end Foldr

-- foldl
section Foldl

variable {n : ℕ} {α : Type u} {β : Type w} {b : β} {f : β → α → β} {a : Array' n α}

theorem toList_foldl : a.toList.foldl f b = a.foldl b (Function.swap f) := by
  rw [← revList_reverse, List.foldl_reverse, revList_foldr]
#align array.to_list_foldl Array'.toList_foldl

end Foldl

-- length
section Length

variable {n : ℕ} {α : Type u}

theorem rev_list_length_aux (a : Array' n α) (i h) :
    (a.iterateAux (fun _ ↦ (· :: ·)) i h []).length = i := by
  induction i <;> simp [*, DArray.iterateAux]
#align array.rev_list_length_aux Array'.rev_list_length_aux

@[simp]
theorem revList_length (a : Array' n α) : a.revList.length = n :=
  rev_list_length_aux a _ _
#align array.rev_list_length Array'.revList_length

@[simp]
theorem toList_length (a : Array' n α) : a.toList.length = n := by
  rw [← revList_reverse, List.length_reverse, revList_length]
#align array.to_list_length Array'.toList_length

end Length

-- nth
section Nth

variable {n : ℕ} {α : Type u} {a : Array' n α}

theorem toList_get_aux (i : ℕ) (ih : i < n) :
    ∀ (j) {jh t h'},
      (∀ k tl, j + k = i → List.get t ⟨k, tl⟩ = a.read ⟨i, ih⟩) →
        (a.revIterateAux (fun _ ↦ (· :: ·)) j jh t).get ⟨i, h'⟩ = a.read ⟨i, ih⟩
  | 0, _, _, _, al => al i _ <| zero_add _
  | j + 1, jh, t, h', al =>
    toList_get_aux i ih j fun k tl hjk ↦
      show List.get (a.read ⟨j, jh⟩ :: t) ⟨k, tl⟩ = a.read ⟨i, ih⟩ from
        match k, hjk, tl with
        | 0, e, tl =>
          match i, e, ih with
          | _, rfl, _ => rfl
        | k' + 1, _, tl => by
          simp only [List.get, Nat.add_eq, add_zero]
          exact al _ _ (by rwa [add_assoc, add_comm 1 k'])
#align array.to_list_nth_le_aux Array'.toList_get_aux

theorem toList_get (i : ℕ) (h h') : List.get a.toList ⟨i, h'⟩ = a.read ⟨i, h⟩ :=
  toList_get_aux _ _ _ fun k tl ↦ absurd tl k.not_lt_zero
#align array.to_list_nth_le Array'.toList_get

@[simp]
theorem toList_get' (a : Array' n α) (i : Fin n) (h') : List.get a.toList ⟨i, h'⟩ = a.read i := by
  apply toList_get
#align array.to_list_nth_le' Array'.toList_get'

theorem toList_get? {i v} : List.get? a.toList i = some v ↔ ∃ h, a.read ⟨i, h⟩ = v := by
  rw [List.get?_eq_some]
  have ll := toList_length a
  constructor <;> intro ⟨h, e⟩ <;> subst v
  · exact ⟨ll ▸ h, (toList_get _ _ _).symm⟩
  · exact ⟨ll.symm ▸ h, toList_get _ _ _⟩
#align array.to_list_nth Array'.toList_get?

theorem write_toList {i v} : (a.write i v).toList = a.toList.set i v :=
  List.ext_get (by simp) fun j h₁ h₂ ↦ by
    have h₃ : j < n := by simpa using h₁
    rw [toList_get _ h₃]
    refine'
      let ⟨_, e⟩ := List.get?_eq_some.1 _
      e.symm
    by_cases ij : (i : ℕ) = j
    · subst j
      rw [show (⟨(i : ℕ), h₃⟩ : Fin _) = i from Fin.eq_of_veq rfl, Array'.read_write,
        List.get?_set_eq_of_lt]
      simp [h₃]
    · rw [List.get?_set_ne _ _ ij, a.read_write_of_ne, toList_get?.2 ⟨h₃, rfl⟩]
      exact Fin.ne_of_vne ij
#align array.write_to_list Array'.write_toList

end Nth

-- enum
section Enum

variable {n : ℕ} {α : Type u} {a : Array' n α}

theorem mem_toList_enum {i v} : (i, v) ∈ a.toList.enum ↔ ∃ h, a.read ⟨i, h⟩ = v := by
  simp [List.mem_iff_get?, toList_get?, and_comm, and_assoc, and_left_comm]
#align array.mem_to_list_enum Array'.mem_toList_enum

end Enum

-- to_array
section ToArray

variable {n : ℕ} {α : Type u}

@[simp]
theorem toList_toArray (a : Array' n α) : HEq a.toList.toArray' a :=
  heq_of_heq_of_eq
      (@Eq.recOn _ _
        (fun m (e : a.toList.length = m) ↦
          HEq (DArray.mk fun v ↦ a.toList.get v)
            (@DArray.mk m (fun _ ↦ α) fun v ↦ a.toList.get ⟨v.val, e.symm ▸ v.prop⟩))
        _ a.toList_length HEq.rfl) <|
    DArray.ext fun ⟨i, h⟩ ↦ toList_get i h _
#align array.to_list_to_array Array'.toList_toArray

@[simp]
theorem toArray'_toList (l : List α) : l.toArray'.toList = l :=
  List.ext_get (toList_length _) fun _ _ h2 => toList_get _ h2 _
#align array.to_array_to_list Array'.toArray'_toList

end ToArray

-- push_back
section PushBack

variable {n : ℕ} {α : Type u} {v : α} {a : Array' n α}

theorem pushBack_revList_aux :
    ∀ i h h',
      DArray.iterateAux (a.pushBack v) (fun _ ↦ (· :: ·)) i h [] =
        DArray.iterateAux a (fun _ ↦ (· :: ·)) i h' []
  | 0, h, _ => rfl
  | i + 1, h, h' => by
    simp only [DArray.iterateAux, List.cons.injEq]
    refine' ⟨_, pushBack_revList_aux _ _ _⟩
    dsimp only [read, DArray.read, pushBack]
    rw [dif_neg]
    exact ne_of_lt h'
#align array.push_back_rev_list_aux Array'.pushBack_revList_aux

@[simp]
theorem pushBack_revList : (a.pushBack v).revList = v :: a.revList := by
  unfold pushBack revList foldl iterate DArray.iterate
  dsimp only [DArray.iterateAux, read, DArray.read, pushBack]
  simp_rw [Nat.add_eq, add_zero]
  apply congr_arg
  apply pushBack_revList_aux
#align array.push_back_rev_list Array'.pushBack_revList

@[simp]
theorem pushBack_toList : (a.pushBack v).toList = a.toList ++ [v] := by
  rw [← revList_reverse, ← revList_reverse, pushBack_revList, List.reverse_cons]
#align array.push_back_to_list Array'.pushBack_toList

@[simp]
theorem read_pushBack_left (i : Fin n) : (a.pushBack v).read i = a.read i := by
  have : ¬i = n := ne_of_lt i.2
  simp [pushBack, this, Fin.castSucc, Fin.castAdd, Fin.castLe, Fin.castLt, read, DArray.read]
#align array.read_push_back_left Array'.read_pushBack_left

@[simp]
theorem read_pushBack_right : (a.pushBack v).read (Fin.last _) = v := by
  cases' hn : Fin.last n with k hk
  have : k = n := by simpa [Fin.eq_iff_veq] using hn.symm
  simp [pushBack, this, Fin.castSucc, Fin.castAdd, Fin.castLe, Fin.castLt, read, DArray.read]
#align array.read_push_back_right Array'.read_pushBack_right

end PushBack

-- foreach
section Foreach

variable {n : ℕ} {α : Type u} {β : Type v} {i : Fin n} {f : Fin n → α → β} {a : Array' n α}

@[simp]
theorem read_foreach : (foreach a f).read i = f i (a.read i) :=
  rfl
#align array.read_foreach Array'.read_foreach

end Foreach

-- map
section Map

variable {n : ℕ} {α : Type u} {β : Type v} {i : Fin n} {f : α → β} {a : Array' n α}

theorem read_map : (a.map f).read i = f (a.read i) :=
  read_foreach
#align array.read_map Array'.read_map

end Map

-- map₂
section Map₂

variable {n : ℕ} {α : Type u} {i : Fin n} {f : α → α → α} {a₁ a₂ : Array' n α}

@[simp]
theorem read_map₂ : (map₂ f a₁ a₂).read i = f (a₁.read i) (a₂.read i) :=
  read_foreach
#align array.read_map₂ Array'.read_map₂

end Map₂

end Array'
