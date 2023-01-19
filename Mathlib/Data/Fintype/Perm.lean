/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fintype.perm
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Card
import Mathbin.GroupTheory.Perm.Basic

/-!
# fintype instances for `equiv` and `perm`

Main declarations:
* `perms_of_finset s`: The finset of permutations of the finset `s`.

-/


open Function

open Nat

universe u v

variable {α β γ : Type _}

open Finset Function List Equiv Equiv.Perm

variable [DecidableEq α] [DecidableEq β]

/-- Given a list, produce a list of all permutations of its elements. -/
def permsOfList : List α → List (Perm α)
  | [] => [1]
  | a :: l => permsOfList l ++ l.bind fun b => (permsOfList l).map fun f => swap a b * f
#align perms_of_list permsOfList

theorem length_perms_of_list : ∀ l : List α, length (permsOfList l) = l.length !
  | [] => rfl
  | a :: l => by
    rw [length_cons, Nat.factorial_succ]
    simp [permsOfList, length_bind, length_perms_of_list, Function.comp, Nat.succ_mul]
    cc
#align length_perms_of_list length_perms_of_list

theorem mem_perms_of_list_of_mem {l : List α} {f : Perm α} (h : ∀ x, f x ≠ x → x ∈ l) :
    f ∈ permsOfList l := by
  induction' l with a l IH generalizing f h
  · exact List.mem_singleton.2 (Equiv.ext fun x => Decidable.by_contradiction <| h _)
  by_cases hfa : f a = a
  · refine' mem_append_left _ (IH fun x hx => mem_of_ne_of_mem _ (h x hx))
    rintro rfl
    exact hx hfa
  have hfa' : f (f a) ≠ f a := mt (fun h => f.injective h) hfa
  have : ∀ x : α, (swap a (f a) * f) x ≠ x → x ∈ l :=
    by
    intro x hx
    have hxa : x ≠ a := by
      rintro rfl
      apply hx
      simp only [mul_apply, swap_apply_right]
    refine' List.mem_of_ne_of_mem hxa (h x fun h => _)
    simp only [h, mul_apply, swap_apply_def, mul_apply, Ne.def, apply_eq_iff_eq] at hx <;>
      split_ifs  at hx
    exacts[hxa (h.symm.trans h_1), hx h]
  suffices f ∈ permsOfList l ∨ ∃ b ∈ l, ∃ g ∈ permsOfList l, swap a b * g = f by
    simpa only [permsOfList, exists_prop, List.mem_map', mem_append, List.mem_bind]
  refine' or_iff_not_imp_left.2 fun hfl => ⟨f a, _, swap a (f a) * f, IH this, _⟩
  · exact mem_of_ne_of_mem hfa (h _ hfa')
  · rw [← mul_assoc, mul_def (swap a (f a)) (swap a (f a)), swap_swap, ← perm.one_def, one_mul]
#align mem_perms_of_list_of_mem mem_perms_of_list_of_mem

theorem mem_of_mem_perms_of_list :
    ∀ {l : List α} {f : Perm α}, f ∈ permsOfList l → ∀ {x}, f x ≠ x → x ∈ l
  | [], f, h => by
    have : f = 1 := by simpa [permsOfList] using h
    rw [this] <;> simp
  | a :: l, f, h =>
    (mem_append.1 h).elim (fun h x hx => mem_cons_of_mem _ (mem_of_mem_perms_of_list h hx))
      fun h x hx =>
      let ⟨y, hy, hy'⟩ := List.mem_bind.1 h
      let ⟨g, hg₁, hg₂⟩ := List.mem_map'.1 hy'
      if hxa : x = a then by simp [hxa]
      else
        if hxy : x = y then mem_cons_of_mem _ <| by rwa [hxy]
        else
          mem_cons_of_mem _ <|
            mem_of_mem_perms_of_list hg₁ <| by
              rw [eq_inv_mul_iff_mul_eq.2 hg₂, mul_apply, swap_inv, swap_apply_def] <;>
                  split_ifs <;>
                [exact Ne.symm hxy, exact Ne.symm hxa, exact hx]
#align mem_of_mem_perms_of_list mem_of_mem_perms_of_list

theorem mem_perms_of_list_iff {l : List α} {f : Perm α} :
    f ∈ permsOfList l ↔ ∀ {x}, f x ≠ x → x ∈ l :=
  ⟨mem_of_mem_perms_of_list, mem_perms_of_list_of_mem⟩
#align mem_perms_of_list_iff mem_perms_of_list_iff

theorem nodup_perms_of_list : ∀ {l : List α} (hl : l.Nodup), (permsOfList l).Nodup
  | [], hl => by simp [permsOfList]
  | a :: l, hl => by
    have hl' : l.Nodup := hl.of_cons
    have hln' : (permsOfList l).Nodup := nodup_perms_of_list hl'
    have hmeml : ∀ {f : Perm α}, f ∈ permsOfList l → f a = a := fun f hf =>
      not_not.1 (mt (mem_of_mem_perms_of_list hf) (nodup_cons.1 hl).1)
    rw [permsOfList, List.nodup_append, List.nodup_bind, pairwise_iff_nth_le] <;>
      exact
        ⟨hln',
          ⟨fun _ _ => hln'.map fun _ _ => mul_left_cancel, fun i j hj hij x hx₁ hx₂ =>
            let ⟨f, hf⟩ := List.mem_map'.1 hx₁
            let ⟨g, hg⟩ := List.mem_map'.1 hx₂
            have hix : x a = nth_le l i (lt_trans hij hj) := by
              rw [← hf.2, mul_apply, hmeml hf.1, swap_apply_left]
            have hiy : x a = nth_le l j hj := by rw [← hg.2, mul_apply, hmeml hg.1, swap_apply_left]
            absurd (hf.2.trans hg.2.symm) fun h =>
              ne_of_lt hij <|
                nodup_iff_nth_le_inj.1 hl' i j (lt_trans hij hj) hj <| by rw [← hix, hiy]⟩,
          fun f hf₁ hf₂ =>
          let ⟨x, hx, hx'⟩ := List.mem_bind.1 hf₂
          let ⟨g, hg⟩ := List.mem_map'.1 hx'
          have hgxa : g⁻¹ x = a := f.Injective <| by rw [hmeml hf₁, ← hg.2] <;> simp
          have hxa : x ≠ a := fun h => (List.nodup_cons.1 hl).1 (h ▸ hx)
          (List.nodup_cons.1 hl).1 <|
            hgxa ▸ mem_of_mem_perms_of_list hg.1 (by rwa [apply_inv_self, hgxa])⟩
#align nodup_perms_of_list nodup_perms_of_list

/-- Given a finset, produce the finset of all permutations of its elements. -/
def permsOfFinset (s : Finset α) : Finset (Perm α) :=
  Quotient.hrecOn s.1 (fun l hl => ⟨permsOfList l, nodup_perms_of_list hl⟩)
    (fun a b hab =>
      hfunext (congr_arg _ (Quotient.sound hab)) fun ha hb _ =>
        heq_of_eq <| Finset.ext <| by simp [mem_perms_of_list_iff, hab.mem_iff])
    s.2
#align perms_of_finset permsOfFinset

theorem mem_perms_of_finset_iff :
    ∀ {s : Finset α} {f : Perm α}, f ∈ permsOfFinset s ↔ ∀ {x}, f x ≠ x → x ∈ s := by
  rintro ⟨⟨l⟩, hs⟩ f <;> exact mem_perms_of_list_iff
#align mem_perms_of_finset_iff mem_perms_of_finset_iff

theorem card_perms_of_finset : ∀ s : Finset α, (permsOfFinset s).card = s.card ! := by
  rintro ⟨⟨l⟩, hs⟩ <;> exact length_perms_of_list l
#align card_perms_of_finset card_perms_of_finset

/-- The collection of permutations of a fintype is a fintype. -/
def fintypePerm [Fintype α] : Fintype (Perm α) :=
  ⟨permsOfFinset (@Finset.univ α _), by simp [mem_perms_of_finset_iff]⟩
#align fintype_perm fintypePerm

instance [Fintype α] [Fintype β] : Fintype (α ≃ β) :=
  if h : Fintype.card β = Fintype.card α then
    Trunc.recOnSubsingleton (Fintype.truncEquivFin α) fun eα =>
      Trunc.recOnSubsingleton (Fintype.truncEquivFin β) fun eβ =>
        @Fintype.ofEquiv _ (Perm α) fintypePerm
          (equivCongr (Equiv.refl α) (eα.trans (Eq.recOn h eβ.symm)) : α ≃ α ≃ (α ≃ β))
  else ⟨∅, fun x => False.elim (h (Fintype.card_eq.2 ⟨x.symm⟩))⟩

theorem Fintype.card_perm [Fintype α] : Fintype.card (Perm α) = (Fintype.card α)! :=
  Subsingleton.elim (@fintypePerm α _ _) (@Equiv.fintype α α _ _ _ _) ▸ card_perms_of_finset _
#align fintype.card_perm Fintype.card_perm

theorem Fintype.card_equiv [Fintype α] [Fintype β] (e : α ≃ β) :
    Fintype.card (α ≃ β) = (Fintype.card α)! :=
  Fintype.card_congr (equivCongr (Equiv.refl α) e) ▸ Fintype.card_perm
#align fintype.card_equiv Fintype.card_equiv

