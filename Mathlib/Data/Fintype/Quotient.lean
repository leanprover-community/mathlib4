/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yuyang Zhao
-/
import Mathlib.Data.List.Pi
import Mathlib.Data.Fintype.Basic

#align_import data.fintype.quotient from "leanprover-community/mathlib"@"d78597269638367c3863d40d45108f52207e03cf"

/-!
# Quotients of families indexed by a finite type

This file proves some basic facts and defines lifting and recursion principle for quotients indexed
by a finite type.

## Main definitions

* `Quotient.finChoice`: Given a function `f : Π i, Quotient (S i)` on a fintype `ι`, returns the
  class of functions `Π i, α i` sending each `i` to an element of the class `f i`.
* `Quotient.finChoiceEquiv`: A finite family of quotients is equivalent to a quotient of
  finite families.
* `Quotient.finLiftOn`: Given a fintype `ι`. A function on `Π i : ι, α i` which respects
  setoid `S i` for each `i` can be lifted to a function on `Π i : ι, Quotient (S i)`.
* `Quotient.finRecOn`: Recursion principle for quotients indexed by a finite type. It is the
  dependent version of `Quotient.finLiftOn`.

-/


namespace Quotient

section List
variable {ι : Type _} [DecidableEq ι] {α : ι → Sort _} [S : ∀ i, Setoid (α i)] {β : Sort _}

/-- Given a collection of setoids indexed by a type `ι`, a list `l` of indices, and a function that
  for each `i ∈ l` gives a term of the corresponding quotient type, then there is a corresponding
  term in the quotient of the product of the setoids indexed by `l`. -/
def listChoice {l : List ι} (q : ∀ i ∈ l, Quotient (S i)) : @Quotient (∀ i ∈ l, α i) piSetoid :=
  match l with
  |     [] => ⟦fun.⟧
  | i :: _ => Quotient.liftOn₂ (List.Pi.head (i := i) q)
    (listChoice (List.Pi.tail q))
    (⟦List.Pi.cons · ·⟧)
    (fun _ _ _ _ ha hl ↦ Quotient.sound (List.Pi.forall_rel_cons_ext ha hl))

theorem listChoice_mk {l : List ι} (a : ∀ i ∈ l, α i) : listChoice (⟦a · ·⟧) = ⟦a⟧ :=
  match l with
  |     [] => Quotient.sound fun.
  | i :: l => by
    rw [listChoice]
    dsimp [List.Pi.tail]
    rw [listChoice_mk]
    exact congrArg (⟦·⟧) (List.Pi.cons_eta a)

/-- Choice-free induction principle for quotients indexed by a `List`. -/
@[elab_as_elim]
lemma list_ind {l : List ι} {C : (∀ i ∈ l, Quotient (S i)) → Prop}
    (f : ∀ a : ∀ i ∈ l, α i, C (⟦a · ·⟧)) (q : ∀ i ∈ l, Quotient (S i)) : C q :=
  match l with
  |     [] => cast (congr_arg _ (funext₂ fun.)) (f fun.)
  | i :: l => by
    rw [← List.Pi.cons_eta q]
    induction' List.Pi.head q using Quotient.ind with a
    refine @list_ind _ (fun q ↦ C (List.Pi.cons ⟦a⟧ q)) ?_ (List.Pi.tail q)
    intro as
    rw [List.Pi.cons_map a as (fun i ↦ Quotient.mk (S i))]
    exact f _

end List

section Fintype
variable {ι : Type _} [Fintype ι] [DecidableEq ι] {α : ι → Sort _} [S : ∀ i, Setoid (α i)]
  {β : Sort _}

/-- Choice-free induction principle for quotients indexed by a finite type.
  See `Quotient.induction_on_pi` for the general version assuming `Classical.choice`. -/
@[elab_as_elim]
lemma fin_ind {C : (∀ i, Quotient (S i)) → Prop}
    (f : ∀ a : ∀ i, α i, C (⟦a ·⟧)) (q : ∀ i, Quotient (S i)) : C q := by
  have : ∀ {m : Multiset ι} (C : (∀ i ∈ m, Quotient (S i)) → Prop)
    (_ : ∀ a : ∀ i ∈ m, α i, C (⟦a · ·⟧)) (q : ∀ i ∈ m, Quotient (S i)), C q
  · intro m C
    induction m using Quotient.ind
    exact list_ind (S := S)
  exact this (fun q ↦ C (q · (Finset.mem_univ _))) (fun _ ↦ f _) (fun i _ ↦ q i)

/-- Choice-free induction principle for quotients indexed by a finite type.
  See `Quotient.induction_on_pi` for the general version assuming `Classical.choice`. -/
@[elab_as_elim]
lemma fin_induction_on {C : (∀ i, Quotient (S i)) → Prop}
    (q : ∀ i, Quotient (S i)) (f : ∀ a : ∀ i, α i, C (⟦a ·⟧)) : C q :=
  fin_ind f q

/-- Given a collection of setoids indexed by a fintype `ι` and a function that for each `i : ι`
  gives a term of the corresponding quotient type, then there is corresponding term in the quotient
  of the product of the setoids.
  See `Quotient.choice` for the noncomputable general version. -/
def finChoice (q : ∀ i, Quotient (S i)) :
    @Quotient (∀ i, α i) piSetoid := by
  let e := Equiv.subtypeQuotientEquivQuotientSubtype (fun l : List ι ↦ ∀ i, i ∈ l)
    (fun s : Multiset ι ↦ ∀ i, i ∈ s) (fun i ↦ Iff.rfl) (fun _ _ ↦ Iff.rfl) ⟨_, Finset.mem_univ⟩
  refine e.liftOn
    (fun l ↦ (listChoice (fun i _ ↦ q i)).map (fun a i ↦ a i (l.2 i)) ?_) ?_
  · exact fun _ _ h i ↦ h i _
  intro _ _ _
  refine fin_ind (fun a ↦ ?_) q
  simp_rw [listChoice_mk, Quotient.map_mk]
#align quotient.fin_choice Quotient.finChoice

theorem finChoice_eq (a : ∀ i, α i) :
    finChoice (⟦a ·⟧) = ⟦a⟧ := by
  dsimp [finChoice]
  obtain ⟨l, hl⟩ := (Finset.univ.val : Multiset ι).exists_rep
  simp_rw [← hl, Equiv.subtypeQuotientEquivQuotientSubtype, listChoice_mk]
  rfl
#align quotient.fin_choice_eq Quotient.finChoice_eq

/-- Lift a function on `∀ i, α i` to a function on `∀ i, Quotient (S i)`. -/
def finLiftOn (q : ∀ i, Quotient (S i)) (f : (∀ i, α i) → β)
    (h : ∀ (a b : ∀ i, α i), (∀ i, a i ≈ b i) → f a = f b) : β :=
  Quotient.lift f h (finChoice q)

@[simp]
lemma finLiftOn_empty [e : IsEmpty ι] (q : ∀ i, Quotient (S i)) :
    @finLiftOn _ _ _ _ _ β q = fun f _ ↦ f e.elim := by
  ext f h
  dsimp [finLiftOn]
  induction finChoice q using Quotient.ind
  exact h _ _ e.elim

@[simp]
lemma finLiftOn_mk (a : ∀ i, α i) :
    @finLiftOn _ _ _ _ _ β (⟦a ·⟧) = fun f _ ↦ f a := by
  ext f h
  dsimp [finLiftOn]
  rw [finChoice_eq]
  rfl

/-- `finChoice` as an equivalence. -/
@[simps]
def finChoiceEquiv :
    (∀ i, Quotient (S i)) ≃ @Quotient (∀ i, α i) piSetoid where
  toFun := finChoice
  invFun q i := q.map (· i) (fun _ _ ha ↦ ha i : _)
  left_inv q := by
    refine fin_induction_on q (fun a ↦ ?_)
    rw [finChoice_eq]
    rfl
  right_inv q := by
    induction q using Quotient.ind
    exact finChoice_eq _

section finRec
variable {C : (∀ i, Quotient (S i)) → Sort _} (f : ∀ a : ∀ i, α i, C (⟦a ·⟧))

@[reducible]
private def finRec.indep (a : ∀ i, α i) : PSigma C :=
  ⟨(⟦a ·⟧), f a⟩

variable (h : ∀ (a b : ∀ i, α i) (h : ∀ i, a i ≈ b i),
  Eq.ndrec (f a) (funext fun i ↦ Quotient.sound (h i)) = f b)

private lemma finRec.indep_coherent :
    ∀ a b : ∀ i, α i, (∀ i, a i ≈ b i) →
      finRec.indep f a = finRec.indep f b :=
  fun a b e ↦ PSigma.eta (funext fun i ↦ Quotient.sound (e i)) (h a b e)

private lemma finRec.lift_indep_pr1 (q : ∀ i, Quotient (S i)) :
    (finLiftOn q (finRec.indep f) (finRec.indep_coherent f h)).1 = q :=
  fin_ind (fun a ↦ funext fun i ↦ by rw [finLiftOn_mk]) q

end finRec

/-- Recursion principle for quotients indexed by a finite type. -/
@[elab_as_elim]
def finRec {C : (∀ i, Quotient (S i)) → Sort _}
    (f : ∀ a : ∀ i, α i, C (⟦a ·⟧))
    (h : ∀ (a b : ∀ i, α i) (h : ∀ i, a i ≈ b i),
      Eq.ndrec (f a) (funext fun i ↦ Quotient.sound (h i)) = f b)
    (q : ∀ i, Quotient (S i)) : C q :=
  Eq.ndrecOn (finRec.lift_indep_pr1 f h q)
    ((finLiftOn q (finRec.indep f) (finRec.indep_coherent f h)).2)

/-- Recursion principle for quotients indexed by a finite type. -/
@[elab_as_elim]
def finRecOn {C : (∀ i, Quotient (S i)) → Sort _}
    (q : ∀ i, Quotient (S i))
    (f : ∀ a : ∀ i, α i, C (⟦a ·⟧))
    (h : ∀ (a b : ∀ i, α i) (h : ∀ i, a i ≈ b i),
      Eq.ndrec (f a) (funext fun i ↦ Quotient.sound (h i)) = f b) :
    C q :=
  finRec f h q

/-- Recursion principle for quotients indexed by a finite type. -/
@[elab_as_elim]
def finHRecOn {C : (∀ i, Quotient (S i)) → Sort _}
    (q : ∀ i, Quotient (S i))
    (f : ∀ a : ∀ i, α i, C (⟦a ·⟧))
    (h : ∀ (a b : ∀ i, α i), (∀ i, a i ≈ b i) → HEq (f a) (f b)) :
    C q :=
  finRecOn q f (fun a b p ↦ eq_of_heq ((eq_rec_heq _ (f a)).trans (h a b p)))

@[simp]
lemma finRec_mk {C : (∀ i, Quotient (S i)) → Sort _}
    (f h) (a : ∀ i, α i) :
    finRec (C := C) f h (⟦a ·⟧) = f a := by
  dsimp [finRecOn]
  refine eq_of_heq ((eq_rec_heq _ _).trans ?_)
  rw [finLiftOn_mk a]

@[simp]
lemma finRecOn_mk {C : (∀ i, Quotient (S i)) → Sort _}
    (a : ∀ i, α i) :
    finRecOn (C := C) (⟦a ·⟧) = fun f _ ↦ f a := by
  ext f h
  exact finRec_mk _ _ _

@[simp]
lemma finHRecOn_mk {C : (∀ i, Quotient (S i)) → Sort _}
    (a : ∀ i, α i) :
    finHRecOn (C := C) (⟦a ·⟧) = fun f _ ↦ f a := by
  dsimp [finHRecOn]
  rw [finRecOn_mk]

end Fintype

end Quotient
