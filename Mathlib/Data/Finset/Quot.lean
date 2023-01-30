/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Quot

/-!
# Quotients indexed by a `Finset`

In this file, we define lifting and recursion principle for quotients indexed by a `Finset`.

## Main definitions

* `Finset.quotientLift`: Given `s : Finset ι`. A function on `∀ i ∈ s, α i` which respects setoid
  `S i` for each `i` in `s` can be lifted to a function on `∀ i ∈ s, Quotient (S i)`.
* `Finset.quotientRec`: Recursion principle for quotients indexed by a `Finset`. It is the
  dependent version of `Finset.quotientLift`.
-/

namespace Finset
variable {ι : Type _} [DecidableEq ι] {α : ι → Sort _} [S : ∀ i, Setoid (α i)] {β : Sort _}

/-- Given a collection of setoids indexed by a type `ι`, a Finset `s` of indices, and a function
  that for each `i ∈ s` gives a term of the corresponding quotient type, then there is a
  corresponding term in the quotient of the product of the setoids indexed by `s`. -/
def quotientChoice {s : Finset ι} (q : ∀ i ∈ s, Quotient (S i)) :
    @Quotient (∀ i ∈ s, α i) piSetoid :=
  Multiset.quotientChoice q
#align finset.quotient_choice Finset.quotientChoice

theorem quotientChoice_mk {s : Finset ι} (a : ∀ i ∈ s, α i) :
    quotientChoice (fun i h ↦ ⟦a i h⟧) = ⟦a⟧ :=
  Multiset.quotientChoice_mk a
#align finset.quotient_choice_mk Finset.quotientChoice_mk

/-- Lift a function on `∀ i ∈ s, α i` to a function on `∀ i ∈ s, Quotient (S i)`. -/
def quotientLiftOn {s : Finset ι} (q : ∀ i ∈ s, Quotient (S i)) (f : (∀ i ∈ s, α i) → β)
    (h : ∀ (a b : ∀ i ∈ s, α i), (∀ i (hi : i ∈ s), a i hi ≈ b i hi) → f a = f b) : β :=
  Multiset.quotientLiftOn q f h
#align finset.quotient_lift_on Finset.quotientLiftOn

/-- Lift a function on `∀ i ∈ s, α i` to a function on `∀ i ∈ s, Quotient (S i)`. -/
def quotientLift {s : Finset ι} (f : (∀ i ∈ s, α i) → β)
    (h : ∀ (a b : ∀ i ∈ s, α i), (∀ i (hi : i ∈ s), a i hi ≈ b i hi) → f a = f b)
    (q : ∀ i ∈ s, Quotient (S i)) : β :=
  quotientLiftOn q f h
#align finset.quotient_lift Finset.quotientLift

@[simp] lemma quotientLiftOn_empty (q : ∀ i ∈ (∅ : Finset ι), Quotient (S i)) :
    @quotientLiftOn _ _ _ _ β _ q = fun f _ ↦ f fun. :=
  rfl
#align finset.quotient_lift_on_empty Finset.quotientLiftOn_empty

@[simp] lemma quotientLiftOn_mk {s : Finset ι} (a : ∀ i ∈ s, α i) :
    @quotientLiftOn _ _ _ _ β _ (fun i hi ↦ ⟦a i hi⟧) = fun f _ ↦ f a :=
  Multiset.quotientLiftOn_mk a
#align finset.quotient_lift_on_mk Finset.quotientLiftOn_mk

@[simp] lemma quotientLift_empty (f : (∀ i ∈ (∅ : Finset ι), α i) → β) (h) :
    quotientLift f h = (fun _ ↦ f fun.) :=
  rfl
#align finset.quotient_lift_empty Finset.quotientLift_empty

@[simp] lemma quotientLift_mk {s : Finset ι} (f : (∀ i ∈ s, α i) → β)
    (h : ∀ (a b : ∀ i ∈ s, α i), (∀ i (hi : i ∈ s), a i hi ≈ b i hi) → f a = f b)
    (a : ∀ i ∈ s, α i) : quotientLift f h (fun i hi ↦ ⟦a i hi⟧) = f a :=
  Multiset.quotientLift_mk f h a
#align finset.quotient_lift_mk Finset.quotientLift_mk

-- Porting note: no `decidable_classical` linter
-- `@[nolint decidable_classical]`
/-- Choice-free induction principle for quotients indexed by a `Finset`. -/
@[elab_as_elim]
  lemma quotient_ind {s : Finset ι} {C : (∀ i ∈ s, Quotient (S i)) → Prop}
    (f : ∀ a : ∀ i ∈ s, α i, C (fun i hi ↦ ⟦a i hi⟧)) (q : ∀ i ∈ s, Quotient (S i)) : C q :=
  Multiset.quotient_ind f q
#align finset.quotient_ind Finset.quotient_ind

-- Porting note: no `decidable_classical` linter
-- `@[nolint decidable_classical]`
/-- Choice-free induction principle for quotients indexed by a `Finset`. -/
@[elab_as_elim]
lemma quotient_induction_on {s : Finset ι}
    {C : (∀ i ∈ s, Quotient (S i)) → Prop}
    (q : ∀ i ∈ s, Quotient (S i)) (f : ∀ a : ∀ i ∈ s, α i, C (fun i hi ↦ ⟦a i hi⟧)) :
    C q :=
  quotient_ind f q
#align finset.quotient_induction_on Finset.quotient_induction_on

/-- Recursion principle for quotients indexed by a `Finset`. -/
@[elab_as_elim] def quotientRecOn {s : Finset ι}
    {C : (∀ i ∈ s, Quotient (S i)) → Sort _}
    (q : ∀ i ∈ s, Quotient (S i))
    (f : ∀ a : ∀ i ∈ s, α i, C (fun i hi ↦ ⟦a i hi⟧))
    (h : ∀ (a b : ∀ i ∈ s, α i) (h : ∀ i hi, a i hi ≈ b i hi),
      Eq.ndrec (f a) (funext₂ fun i hi ↦ Quotient.sound (h i hi)) = f b) :
    C q :=
  Multiset.quotientRecOn q f h
#align finset.quotient_rec_on Finset.quotientRecOn

/-- Recursion principle for quotients indexed by a `Finset`. -/
@[elab_as_elim] def quotientRec {s : Finset ι} {C : (∀ i ∈ s, Quotient (S i)) → Sort _}
    (f : ∀ a : ∀ i ∈ s, α i, C (fun i hi ↦ ⟦a i hi⟧))
    (h : ∀ (a b : ∀ i ∈ s, α i) (h : ∀ i hi, a i hi ≈ b i hi),
      Eq.ndrec (f a) (funext₂ fun i hi ↦ Quotient.sound (h i hi)) = f b)
    (q : ∀ i ∈ s, Quotient (S i)) :
    C q :=
  quotientRecOn q f h
#align finset.quotient_rec Finset.quotientRec

/-- Recursion principle for quotients indexed by a `Finset`. -/
@[elab_as_elim] def quotientHRecOn {s : Finset ι} {C : (∀ i ∈ s, Quotient (S i)) → Sort _}
    (q : ∀ i ∈ s, Quotient (S i))
    (f : ∀ a : ∀ i ∈ s, α i, C (fun i hi ↦ ⟦a i hi⟧))
    (h : ∀ (a b : ∀ i ∈ s, α i), (∀ i hi, a i hi ≈ b i hi) → HEq (f a) (f b)) :
    C q :=
  quotientRecOn q f (fun a b p ↦ eq_of_heq ((eq_rec_heq _ (f a)).trans (h a b p)))
#align finset.quotient_hrec_on Finset.quotientHRecOn

@[simp] lemma quotientRec_mk {s : Finset ι} {C : (∀ i ∈ s, Quotient (S i)) → Sort _}
    (f : ∀ a : ∀ i ∈ s, α i, C (fun i hi ↦ ⟦a i hi⟧))
    (h) (a : ∀ i ∈ s, α i) :
    @quotientRec _ _ _ _ _ C f h (fun i hi ↦ ⟦a i hi⟧) = f a :=
  Multiset.quotientRec_mk f h a
#align finset.quotient_rec_mk Finset.quotientRec_mk

@[simp] lemma quotientRecOn_mk {s : Finset ι} {C : (∀ i ∈ s, Quotient (S i)) → Sort _}
    (a : ∀ i ∈ s, α i) :
    @quotientRecOn _ _ _ _ _ C (fun i hi ↦ ⟦a i hi⟧) = fun f _ ↦ f a :=
  Multiset.quotientRecOn_mk a
#align finset.quotient_rec_on_mk Finset.quotientRecOn_mk

end Finset
