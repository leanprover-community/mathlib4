/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fintype.Basic

#align_import data.fintype.quotient from "leanprover-community/mathlib"@"d78597269638367c3863d40d45108f52207e03cf"

/-!
# Quotients of families indexed by a finite type

This file provides `Quotient.finChoice`, a mechanism to go from a finite family of quotients
to a quotient of finite families.

## Main definitions

* `Quotient.finChoice`

-/


/-- An auxiliary function for `Quotient.finChoice`.  Given a
collection of setoids indexed by a type `ι`, a (finite) list `l` of
indices, and a function that for each `i ∈ l` gives a term of the
corresponding quotient type, then there is a corresponding term in the
quotient of the product of the setoids indexed by `l`. -/
def Quotient.finChoiceAux {ι : Type*} [DecidableEq ι] {α : ι → Type*} [S : ∀ i, Setoid (α i)] :
    ∀ l : List ι, (∀ i ∈ l, Quotient (S i)) → @Quotient (∀ i ∈ l, α i) (by infer_instance)
  | [], _ => ⟦fun i h => nomatch List.not_mem_nil _ h⟧
  | i :: l, f => by
    refine Quotient.liftOn₂ (f i (List.mem_cons_self _ _))
        (Quotient.finChoiceAux l fun j h => f j (List.mem_cons_of_mem _ h)) ?_ ?_
    · exact fun a l => ⟦fun j h =>
        if e : j = i then by rw [e]; exact a else l _ ((List.mem_cons.1 h).resolve_left e)⟧
    refine fun a₁ l₁ a₂ l₂ h₁ h₂ => Quotient.sound fun j h => ?_
    by_cases e : j = i <;> simp [e]
    · subst j
      exact h₁
    · exact h₂ _ _
#align quotient.fin_choice_aux Quotient.finChoiceAux

theorem Quotient.finChoiceAux_eq {ι : Type*} [DecidableEq ι] {α : ι → Type*}
    [S : ∀ i, Setoid (α i)] :
    ∀ (l : List ι) (f : ∀ i ∈ l, α i), (Quotient.finChoiceAux l fun i h => ⟦f i h⟧) = ⟦f⟧
  | [], f => Quotient.sound fun i h => nomatch List.not_mem_nil _ h
  | i :: l, f => by
    simp only [finChoiceAux, Quotient.finChoiceAux_eq l, eq_mpr_eq_cast, lift_mk]
    refine Quotient.sound fun j h => ?_
    by_cases e : j = i <;> simp [e] <;> try exact Setoid.refl _
    subst j; exact Setoid.refl _
#align quotient.fin_choice_aux_eq Quotient.finChoiceAux_eq

/-- Given a collection of setoids indexed by a fintype `ι` and a
function that for each `i : ι` gives a term of the corresponding
quotient type, then there is corresponding term in the quotient of the
product of the setoids. -/
def Quotient.finChoice {ι : Type*} [DecidableEq ι] [Fintype ι] {α : ι → Type*}
    [S : ∀ i, Setoid (α i)] (f : ∀ i, Quotient (S i)) : @Quotient (∀ i, α i) (by infer_instance) :=
  Quotient.liftOn
    (@Quotient.recOn _ _ (fun l : Multiset ι => @Quotient (∀ i ∈ l, α i) (by infer_instance))
      Finset.univ.1 (fun l => Quotient.finChoiceAux l fun i _ => f i) (fun a b h => by
      have := fun a => Quotient.finChoiceAux_eq a fun i _ => Quotient.out (f i)
      simp? [Quotient.out_eq] at this says simp only [out_eq] at this
      simp only [Multiset.quot_mk_to_coe, this]
      let g := fun a : Multiset ι =>
        (⟦fun (i : ι) (_ : i ∈ a) => Quotient.out (f i)⟧ : Quotient (by infer_instance))
      apply eq_of_heq
      trans (g a)
      · exact eq_rec_heq (φ := fun l : Multiset ι => @Quotient (∀ i ∈ l, α i) (by infer_instance))
          (Quotient.sound h) (g a)
      · change HEq (g a) (g b); congr 1; exact Quotient.sound h))
    (fun f => ⟦fun i => f i (Finset.mem_univ _)⟧) (fun a b h => Quotient.sound fun i => by apply h)
#align quotient.fin_choice Quotient.finChoice

theorem Quotient.finChoice_eq {ι : Type*} [DecidableEq ι] [Fintype ι] {α : ι → Type*}
    [∀ i, Setoid (α i)] (f : ∀ i, α i) : (Quotient.finChoice fun i => ⟦f i⟧) = ⟦f⟧ := by
  dsimp only [Quotient.finChoice]
  conv_lhs =>
    enter [1]
    tactic =>
      change _ = ⟦fun i _ => f i⟧
      exact Quotient.inductionOn (@Finset.univ ι _).1 fun l => Quotient.finChoiceAux_eq _ _
  rfl
#align quotient.fin_choice_eq Quotient.finChoice_eq

/-- Given a function that for each `i : ι` gives a term of the corresponding
truncation type, then there is corresponding term in the truncation of the product. -/
def Trunc.finChoice {ι : Type*} [DecidableEq ι] [Fintype ι] {α : ι → Type*}
    (f : ∀ i, Trunc (α i)) : Trunc (∀ i, α i) :=
  Quotient.map' id (fun _ _ _ => trivial)
    (Quotient.finChoice f (S := fun _ => trueSetoid))

theorem Trunc.finChoice_eq {ι : Type*} [DecidableEq ι] [Fintype ι] {α : ι → Type*}
    (f : ∀ i, α i) : (Trunc.finChoice fun i => Trunc.mk (f i)) = Trunc.mk f :=
  Subsingleton.elim _ _
