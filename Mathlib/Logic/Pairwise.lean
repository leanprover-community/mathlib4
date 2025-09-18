/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Defs

/-!
# Relations holding pairwise

This file defines pairwise relations.

## Main declarations

* `Pairwise`: `Pairwise r` states that `r i j` for all `i ≠ j`.
* `Set.Pairwise`: `s.Pairwise r` states that `r i j` for all `i ≠ j` with `i, j ∈ s`.
-/

open Function

variable {α β ι : Type*} {r p : α → α → Prop}

section Pairwise

variable {f : ι → α} {s : Set α} {a b : α}

/-- A relation `r` holds pairwise if `r i j` for all `i ≠ j`. -/
def Pairwise (r : α → α → Prop) :=
  ∀ ⦃i j⦄, i ≠ j → r i j

theorem Pairwise.mono (hr : Pairwise r) (h : ∀ ⦃i j⦄, r i j → p i j) : Pairwise p :=
  fun _i _j hij => h <| hr hij

protected theorem Pairwise.eq (h : Pairwise r) : ¬r a b → a = b :=
  not_imp_comm.1 <| @h _ _

@[simp]
protected lemma Subsingleton.pairwise [Subsingleton α] : Pairwise r :=
  fun _ _ h ↦ False.elim <| h.elim <| Subsingleton.elim _ _

theorem Function.injective_iff_pairwise_ne : Injective f ↔ Pairwise ((· ≠ ·) on f) :=
  forall₂_congr fun _i _j => not_imp_not.symm

alias ⟨Function.Injective.pairwise_ne, _⟩ := Function.injective_iff_pairwise_ne

lemma Pairwise.comp_of_injective (hr : Pairwise r) {f : β → α} (hf : Injective f) :
    Pairwise (r on f) :=
  fun _ _ h ↦ hr <| hf.ne h

lemma Pairwise.of_comp_of_surjective {f : β → α} (hr : Pairwise (r on f)) (hf : Surjective f) :
    Pairwise r := hf.forall₂.2 fun _ _ h ↦ hr <| ne_of_apply_ne f h

lemma Function.Bijective.pairwise_comp_iff {f : β → α} (hf : Bijective f) :
    Pairwise (r on f) ↔ Pairwise r :=
  ⟨fun hr ↦ hr.of_comp_of_surjective hf.surjective, fun hr ↦ hr.comp_of_injective hf.injective⟩

theorem pairwise_fin_succ_iff {n : ℕ} {R : Fin n.succ → Fin n.succ → Prop} :
    Pairwise R ↔
      (∀ i, R (Fin.succ i) 0) ∧ (∀ j, R 0 (Fin.succ j)) ∧
      Pairwise fun i j => R (Fin.succ i) (Fin.succ j) where
  mp h := ⟨
    fun _ => h (Fin.succ_ne_zero _), fun _ => h (Fin.succ_ne_zero _).symm,
    fun _i _j hij => h <| Fin.succ_inj.not.2 hij⟩
  mpr
  | ⟨hi, hj, h⟩ =>
    Fin.cases
      (Fin.cases nofun fun j _ => hj j)
      (fun i => Fin.cases (fun _ => hi i) fun _j hij => h (ne_of_apply_ne _ hij))

theorem pairwise_fin_succ_iff_of_isSymm {n : ℕ} {R : Fin n.succ → Fin n.succ → Prop} [IsSymm _ R] :
    Pairwise R ↔ (∀ j, R 0 (Fin.succ j)) ∧ Pairwise fun i j => R (Fin.succ i) (Fin.succ j) := by
  simp only [pairwise_fin_succ_iff, comm (b := 0) (r := R), and_self_left]

namespace Set

/-- The relation `r` holds pairwise on the set `s` if `r x y` for all *distinct* `x y ∈ s`. -/
protected def Pairwise (s : Set α) (r : α → α → Prop) :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → r x y

theorem pairwise_of_forall (s : Set α) (r : α → α → Prop) (h : ∀ a b, r a b) : s.Pairwise r :=
  fun a _ b _ _ => h a b

theorem Pairwise.imp_on (h : s.Pairwise r) (hrp : s.Pairwise fun ⦃a b : α⦄ => r a b → p a b) :
    s.Pairwise p :=
  fun _a ha _b hb hab => hrp ha hb hab <| h ha hb hab

theorem Pairwise.imp (h : s.Pairwise r) (hpq : ∀ ⦃a b : α⦄, r a b → p a b) : s.Pairwise p :=
  h.imp_on <| pairwise_of_forall s _ hpq

protected theorem Pairwise.eq (hs : s.Pairwise r) (ha : a ∈ s) (hb : b ∈ s) (h : ¬r a b) : a = b :=
  of_not_not fun hab => h <| hs ha hb hab

theorem _root_.Reflexive.set_pairwise_iff (hr : Reflexive r) :
    s.Pairwise r ↔ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → r a b :=
  forall₄_congr fun a _ _ _ => or_iff_not_imp_left.symm.trans <| or_iff_right_of_imp <| Eq.ndrec <|
    hr a

theorem Pairwise.on_injective (hs : s.Pairwise r) (hf : Function.Injective f) (hfs : ∀ x, f x ∈ s) :
    Pairwise (r on f) := fun i j hij => hs (hfs i) (hfs j) (hf.ne hij)

end Set

theorem Pairwise.set_pairwise (h : Pairwise r) (s : Set α) : s.Pairwise r := fun _ _ _ _ w => h w

end Pairwise
