/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yuyang Zhao
-/
import Mathlib.Data.List.Pi
import Mathlib.Data.Fintype.Defs

/-!
# Quotients of families indexed by a finite type

This file proves some basic facts and defines lifting and recursion principle for quotients indexed
by a finite type.

## Main definitions

* `Quotient.finChoice`: Given a function `f : Π i, Quotient (S i)` on a fintype `ι`, returns the
  class of functions `Π i, α i` sending each `i` to an element of the class `f i`.
* `Quotient.finChoiceEquiv`: A finite family of quotients is equivalent to a quotient of
  finite families.
* `Quotient.finLiftOn`: Given a fintype `ι`. A function on `Π i, α i` which respects
  setoid `S i` for each `i` can be lifted to a function on `Π i, Quotient (S i)`.
* `Quotient.finRecOn`: Recursion principle for quotients indexed by a finite type. It is the
  dependent version of `Quotient.finLiftOn`.

-/


namespace Quotient

section List
variable {ι : Type*} [DecidableEq ι] {α : ι → Sort*} {S : ∀ i, Setoid (α i)} {β : Sort*}

/-- Given a collection of setoids indexed by a type `ι`, a list `l` of indices, and a function that
  for each `i ∈ l` gives a term of the corresponding quotient type, then there is a corresponding
  term in the quotient of the product of the setoids indexed by `l`. -/
def listChoice {l : List ι} (q : ∀ i ∈ l, Quotient (S i)) : @Quotient (∀ i ∈ l, α i) piSetoid :=
  match l with
  |     [] => ⟦nofun⟧
  | i :: _ => Quotient.liftOn₂ (List.Pi.head (i := i) q)
    (listChoice (List.Pi.tail q))
    (⟦List.Pi.cons _ _ · ·⟧)
    (fun _ _ _ _ ha hl ↦ Quotient.sound (List.Pi.forall_rel_cons_ext ha hl))

theorem listChoice_mk {l : List ι} (a : ∀ i ∈ l, α i) : listChoice (S := S) (⟦a · ·⟧) = ⟦a⟧ :=
  match l with
  |     [] => Quotient.sound nofun
  | i :: l => by
    unfold listChoice List.Pi.tail
    rw [listChoice_mk]
    exact congrArg (⟦·⟧) (List.Pi.cons_eta a)

/-- Choice-free induction principle for quotients indexed by a `List`. -/
@[elab_as_elim]
lemma list_ind {l : List ι} {C : (∀ i ∈ l, Quotient (S i)) → Prop}
    (f : ∀ a : ∀ i ∈ l, α i, C (⟦a · ·⟧)) (q : ∀ i ∈ l, Quotient (S i)) : C q :=
  match l with
  |     [] => cast (congr_arg _ (funext₂ nofun)) (f nofun)
  | i :: l => by
    rw [← List.Pi.cons_eta q]
    induction List.Pi.head q using Quotient.ind with | _ a
    refine @list_ind _ (fun q ↦ C (List.Pi.cons _ _ ⟦a⟧ q)) ?_ (List.Pi.tail q)
    intro as
    rw [List.Pi.cons_map a as (fun i ↦ Quotient.mk (S i))]
    exact f _

end List

section Fintype
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Sort*} {S : ∀ i, Setoid (α i)} {β : Sort*}

/-- Choice-free induction principle for quotients indexed by a finite type.
  See `Quotient.induction_on_pi` for the general version assuming `Classical.choice`. -/
@[elab_as_elim]
lemma ind_fintype_pi {C : (∀ i, Quotient (S i)) → Prop}
    (f : ∀ a : ∀ i, α i, C (⟦a ·⟧)) (q : ∀ i, Quotient (S i)) : C q := by
  have {m : Multiset ι} (C : (∀ i ∈ m, Quotient (S i)) → Prop) :
      ∀ (_ : ∀ a : ∀ i ∈ m, α i, C (⟦a · ·⟧)) (q : ∀ i ∈ m, Quotient (S i)), C q := by
    induction m using Quotient.ind
    exact list_ind
  exact this (fun q ↦ C (q · (Finset.mem_univ _))) (fun _ ↦ f _) (fun i _ ↦ q i)

/-- Choice-free induction principle for quotients indexed by a finite type.
  See `Quotient.induction_on_pi` for the general version assuming `Classical.choice`. -/
@[elab_as_elim]
lemma induction_on_fintype_pi {C : (∀ i, Quotient (S i)) → Prop}
    (q : ∀ i, Quotient (S i)) (f : ∀ a : ∀ i, α i, C (⟦a ·⟧)) : C q :=
  ind_fintype_pi f q

/-- Given a collection of setoids indexed by a fintype `ι` and a function that for each `i : ι`
  gives a term of the corresponding quotient type, then there is corresponding term in the quotient
  of the product of the setoids.
  See `Quotient.choice` for the noncomputable general version. -/
def finChoice (q : ∀ i, Quotient (S i)) :
    @Quotient (∀ i, α i) piSetoid := by
  let e := Equiv.subtypeQuotientEquivQuotientSubtype (fun l : List ι ↦ ∀ i, i ∈ l)
    (fun s : Multiset ι ↦ ∀ i, i ∈ s) (fun i ↦ Iff.rfl) (fun _ _ ↦ Iff.rfl) ⟨_, Finset.mem_univ⟩
  refine e.liftOn
    (fun l ↦ (listChoice fun i _ ↦ q i).map (fun a i ↦ a i (l.2 i)) ?_) ?_
  · exact fun _ _ h i ↦ h i _
  intro _ _ _
  refine ind_fintype_pi (fun a ↦ ?_) q
  simp_rw [listChoice_mk, Quotient.map_mk]

theorem finChoice_eq (a : ∀ i, α i) :
    finChoice (S := S) (⟦a ·⟧) = ⟦a⟧ := by
  dsimp [finChoice]
  obtain ⟨l, hl⟩ := (Finset.univ.val : Multiset ι).exists_rep
  simp_rw [← hl, Equiv.subtypeQuotientEquivQuotientSubtype, listChoice_mk]
  rfl

lemma eval_finChoice (f : ∀ i, Quotient (S i)) :
    eval (finChoice f) = f :=
  induction_on_fintype_pi f (fun a ↦ by rw [finChoice_eq]; rfl)

/-- Lift a function on `∀ i, α i` to a function on `∀ i, Quotient (S i)`. -/
def finLiftOn (q : ∀ i, Quotient (S i)) (f : (∀ i, α i) → β)
    (h : ∀ (a b : ∀ i, α i), (∀ i, a i ≈ b i) → f a = f b) : β :=
  (finChoice q).liftOn f h

@[simp]
lemma finLiftOn_empty [e : IsEmpty ι] (q : ∀ i, Quotient (S i)) :
    finLiftOn (β := β) q = fun f _ ↦ f e.elim := by
  ext f h
  dsimp [finLiftOn]
  induction finChoice q using Quotient.ind
  exact h _ _ e.elim

@[simp]
lemma finLiftOn_mk (a : ∀ i, α i) :
    finLiftOn (S := S) (β := β) (⟦a ·⟧) = fun f _ ↦ f a := by
  ext f h
  dsimp [finLiftOn]
  rw [finChoice_eq]
  rfl

/-- `Quotient.finChoice` as an equivalence. -/
@[simps]
def finChoiceEquiv :
    (∀ i, Quotient (S i)) ≃ @Quotient (∀ i, α i) piSetoid where
  toFun := finChoice
  invFun := eval
  left_inv q := by
    refine induction_on_fintype_pi q (fun a ↦ ?_)
    rw [finChoice_eq]
    rfl
  right_inv q := by
    induction q using Quotient.ind
    exact finChoice_eq _

/-- Recursion principle for quotients indexed by a finite type. -/
@[elab_as_elim]
def finHRecOn {C : (∀ i, Quotient (S i)) → Sort*}
    (q : ∀ i, Quotient (S i))
    (f : ∀ a : ∀ i, α i, C (⟦a ·⟧))
    (h : ∀ (a b : ∀ i, α i), (∀ i, a i ≈ b i) → f a ≍ f b) :
    C q :=
  eval_finChoice q ▸ (finChoice q).hrecOn f h

/-- Recursion principle for quotients indexed by a finite type. -/
@[elab_as_elim]
def finRecOn {C : (∀ i, Quotient (S i)) → Sort*}
    (q : ∀ i, Quotient (S i))
    (f : ∀ a : ∀ i, α i, C (⟦a ·⟧))
    (h : ∀ (a b : ∀ i, α i) (h : ∀ i, a i ≈ b i),
      Eq.ndrec (f a) (funext fun i ↦ Quotient.sound (h i)) = f b) :
    C q :=
  finHRecOn q f (eqRec_heq_iff_heq.mp <| heq_of_eq <| h · · ·)

@[simp]
lemma finHRecOn_mk {C : (∀ i, Quotient (S i)) → Sort*}
    (a : ∀ i, α i) :
    finHRecOn (C := C) (⟦a ·⟧) = fun f _ ↦ f a := by
  ext f h
  refine eq_of_heq ((eqRec_heq _ _).trans ?_)
  rw [finChoice_eq]
  rfl

@[simp]
lemma finRecOn_mk {C : (∀ i, Quotient (S i)) → Sort*}
    (a : ∀ i, α i) :
    finRecOn (C := C) (⟦a ·⟧) = fun f _ ↦ f a := by
  unfold finRecOn
  simp

end Fintype

end Quotient

namespace Trunc
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {α : ι → Sort*} {β : Sort*}

/-- Given a function that for each `i : ι` gives a term of the corresponding
truncation type, then there is corresponding term in the truncation of the product. -/
def finChoice (q : ∀ i, Trunc (α i)) : Trunc (∀ i, α i) :=
  Quotient.map' id (fun _ _ _ => trivial) (Quotient.finChoice q)

theorem finChoice_eq (f : ∀ i, α i) : (Trunc.finChoice fun i => Trunc.mk (f i)) = Trunc.mk f :=
  Subsingleton.elim _ _

/-- Lift a function on `∀ i, α i` to a function on `∀ i, Trunc (α i)`. -/
def finLiftOn (q : ∀ i, Trunc (α i)) (f : (∀ i, α i) → β) (h : ∀ (a b : ∀ i, α i), f a = f b) : β :=
  Quotient.finLiftOn q f (fun _ _ _ ↦ h _ _)

@[simp]
lemma finLiftOn_empty [e : IsEmpty ι] (q : ∀ i, Trunc (α i)) :
    finLiftOn (β := β) q = fun f _ ↦ f e.elim :=
  funext₂ fun _ _ ↦ congrFun₂ (Quotient.finLiftOn_empty q) _ _

@[simp]
lemma finLiftOn_mk (a : ∀ i, α i) :
    finLiftOn (β := β) (⟦a ·⟧) = fun f _ ↦ f a :=
  funext₂ fun _ _ ↦ congrFun₂ (Quotient.finLiftOn_mk a) _ _

/-- `Trunc.finChoice` as an equivalence. -/
@[simps]
def finChoiceEquiv : (∀ i, Trunc (α i)) ≃ Trunc (∀ i, α i) where
  toFun := finChoice
  invFun q i := q.map (· i)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- Recursion principle for `Trunc`s indexed by a finite type. -/
@[elab_as_elim]
def finRecOn {C : (∀ i, Trunc (α i)) → Sort*}
    (q : ∀ i, Trunc (α i))
    (f : ∀ a : ∀ i, α i, C (mk <| a ·))
    (h : ∀ (a b : ∀ i, α i), (Eq.ndrec (f a) (funext fun _ ↦ Trunc.eq _ _)) = f b) :
    C q :=
  Quotient.finRecOn q (f ·) (fun _ _ _ ↦ h _ _)

@[simp]
lemma finRecOn_mk {C : (∀ i, Trunc (α i)) → Sort*}
    (a : ∀ i, α i) :
    finRecOn (C := C) (⟦a ·⟧) = fun f _ ↦ f a := by
  unfold finRecOn
  simp

end Trunc
