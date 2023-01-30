/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Data.List.Quot
import Mathlib.Data.Multiset.Basic

/-!
# Quotients indexed by a `Multiset`

In this file, we define lifting and recursion principle for quotients indexed by a `Multiset`.

## Main definitions

* `Multiset.quotientLift`: Given `m : Multiset ι`. A function on `∀ i ∈ m, α i` which respects
  setoid `S i` for each `i` in `m` can be lifted to a function on `∀ i ∈ m, Quotient (S i)`.
* `Multiset.quotientRec`: Recursion principle for quotients indexed by a `Multiset`. It is the
  dependent version of `Multiset.quotientLift`.
-/

namespace Multiset
variable {ι : Type _} [DecidableEq ι] {α : ι → Sort _} [S : ∀ i, Setoid (α i)] {β : Sort _}

/-- Given a collection of setoids indexed by a type `ι`, a multiset `m` of indices, and a function
  that for each `i ∈ m` gives a term of the corresponding quotient type, then there is a
  corresponding term in the quotient of the product of the setoids indexed by `m`. -/
def quotientChoice {m : Multiset ι} :
    (∀ i ∈ m, Quotient (S i)) → @Quotient (∀ i ∈ m, α i) piSetoid :=
  Quotient.hrecOn m (fun _ ↦ List.quotientChoice)
    (fun _ _ hl ↦ List.quotientChoice_heq (fun _ ↦ List.Perm.mem_iff hl))
#align multiset.quotient_choice Multiset.quotientChoice

theorem quotientChoice_mk {m : Multiset ι} (a : ∀ i ∈ m, α i) :
    quotientChoice (fun i h ↦ ⟦a i h⟧) = ⟦a⟧ := by
  induction m using Quotient.ind
  exact List.quotientChoice_mk a
#align multiset.quotient_choice_mk Multiset.quotientChoice_mk

/-- Lift a function on `∀ i ∈ m, α i` to a function on `∀ i ∈ m, Quotient (S i)`. -/
def quotientLiftOn {m : Multiset ι} : ∀ (_ : ∀ i ∈ m, Quotient (S i)) (f : (∀ i ∈ m, α i) → β),
    (∀ (a b : ∀ i ∈ m, α i), (∀ i (hi : i ∈ m), a i hi ≈ b i hi) → f a = f b) → β :=
  Quotient.hrecOn m (fun _ ↦ List.quotientLiftOn)
    (fun _ _ hl ↦ List.quotientLiftOn_heq (fun _ ↦ List.Perm.mem_iff hl))
#align multiset.quotient_lift_on Multiset.quotientLiftOn

/-- Lift a function on `∀ i ∈ m, α i` to a function on `∀ i ∈ m, Quotient (S i)`. -/
def quotientLift {m : Multiset ι} (f : (∀ i ∈ m, α i) → β)
    (h : ∀ (a b : ∀ i ∈ m, α i), (∀ i (hi : i ∈ m), a i hi ≈ b i hi) → f a = f b)
    (q : ∀ i ∈ m, Quotient (S i)) : β :=
  quotientLiftOn q f h
#align multiset.quotient_lift Multiset.quotientLift

@[simp] lemma quotientLiftOn_empty (q : ∀ i ∈ (∅ : Multiset ι), Quotient (S i)) :
    @quotientLiftOn _ _ _ _ β _ q = fun f _ ↦ f fun. :=
  rfl
#align multiset.quotient_lift_on_empty Multiset.quotientLiftOn_empty

@[simp] lemma quotientLiftOn_mk {m : Multiset ι} (a : ∀ i ∈ m, α i) :
    @quotientLiftOn _ _ _ _ β _ (fun i hi ↦ ⟦a i hi⟧) = fun f _ ↦ f a := by
  induction m using Quotient.ind
  exact List.quotientLiftOn_mk a
#align multiset.quotient_lift_on_mk Multiset.quotientLiftOn_mk

@[simp] lemma quotientLift_empty (f : (∀ i ∈ (∅ : Multiset ι), α i) → β) (h) :
    quotientLift f h = (fun _ ↦ f fun.) :=
  rfl
#align multiset.quotient_lift_empty Multiset.quotientLift_empty

@[simp] lemma quotientLift_mk {m : Multiset ι} (f : (∀ i ∈ m, α i) → β)
    (h : ∀ (a b : ∀ i ∈ m, α i), (∀ i (hi : i ∈ m), a i hi ≈ b i hi) → f a = f b)
    (a : ∀ i ∈ m, α i) : quotientLift f h (fun i hi ↦ ⟦a i hi⟧) = f a :=
  congr_fun (congr_fun (quotientLiftOn_mk a) f) h
#align multiset.quotient_lift_mk Multiset.quotientLift_mk

-- Porting note: no `decidable_classical` linter
-- `@[nolint decidable_classical]`
/-- Choice-free induction principle for quotients indexed by a `Multiset`. -/
@[elab_as_elim]
lemma quotient_ind {m : Multiset ι} {C : (∀ i ∈ m, Quotient (S i)) → Prop}
    (f : ∀ a : ∀ i ∈ m, α i, C (fun i hi ↦ ⟦a i hi⟧)) (q : ∀ i ∈ m, Quotient (S i)) : C q := by
  induction m using Quotient.ind
  exact List.quotient_ind f q
#align multiset.quotient_ind Multiset.quotient_ind

-- Porting note: no `decidable_classical` linter
-- `@[nolint decidable_classical]`
/-- Choice-free induction principle for quotients indexed by a `Multiset`. -/
@[elab_as_elim]
lemma quotient_induction_on {m : Multiset ι}
    {C : (∀ i ∈ m, Quotient (S i)) → Prop}
    (q : ∀ i ∈ m, Quotient (S i)) (f : ∀ a : ∀ i ∈ m, α i, C (fun i hi ↦ ⟦a i hi⟧)) :
    C q :=
  quotient_ind f q
#align multiset.quotient_induction_on Multiset.quotient_induction_on

/-- Recursion principle for quotients indexed by a `Multiset`. -/
@[elab_as_elim] def quotientRecOn {m : Multiset ι} :
    ∀ {C : (∀ i ∈ m, Quotient (S i)) → Sort _}
    (q : ∀ i ∈ m, Quotient (S i))
    (f : ∀ a : ∀ i ∈ m, α i, C (fun i hi ↦ ⟦a i hi⟧))
    (_ : ∀ (a b : ∀ i ∈ m, α i) (h : ∀ i hi, a i hi ≈ b i hi),
      Eq.ndrec (f a) (funext₂ fun i hi ↦ Quotient.sound (h i hi)) = f b),
    C q :=
  @fun C ↦ Quotient.hrecOn m (@List.quotientRecOn _ _ _ _)
    (fun _ _ hl ↦ List.quotientRecOn_heq (fun _ ↦ List.Perm.mem_iff hl)) C
#align multiset.quotient_rec_on Multiset.quotientRecOn

/-- Recursion principle for quotients indexed by a `Multiset`. -/
@[elab_as_elim] def quotientRec {m : Multiset ι} {C : (∀ i ∈ m, Quotient (S i)) → Sort _}
    (f : ∀ a : ∀ i ∈ m, α i, C (fun i hi ↦ ⟦a i hi⟧))
    (h : ∀ (a b : ∀ i ∈ m, α i) (h : ∀ i hi, a i hi ≈ b i hi),
      Eq.ndrec (f a) (funext₂ fun i hi ↦ Quotient.sound (h i hi)) = f b)
    (q : ∀ i ∈ m, Quotient (S i)) :
    C q :=
  quotientRecOn q f h
#align multiset.quotient_rec Multiset.quotientRec

/-- Recursion principle for quotients indexed by a `Multiset`. -/
@[elab_as_elim] def quotientHRecOn {m : Multiset ι} {C : (∀ i ∈ m, Quotient (S i)) → Sort _}
    (q : ∀ i ∈ m, Quotient (S i))
    (f : ∀ a : ∀ i ∈ m, α i, C (fun i hi ↦ ⟦a i hi⟧))
    (h : ∀ (a b : ∀ i ∈ m, α i), (∀ i hi, a i hi ≈ b i hi) → HEq (f a) (f b)) :
    C q :=
  quotientRecOn q f (fun a b p ↦ eq_of_heq ((eq_rec_heq _ (f a)).trans (h a b p)))
#align multiset.quotient_hrec_on Multiset.quotientHRecOn

@[simp] lemma quotientRec_mk {m : Multiset ι} {C : (∀ i ∈ m, Quotient (S i)) → Sort _}
    (f : ∀ a : ∀ i ∈ m, α i, C (fun i hi ↦ ⟦a i hi⟧))
    (h) (a : ∀ i ∈ m, α i) :
    @quotientRec _ _ _ _ _ C f h (fun i hi ↦ ⟦a i hi⟧) = f a := by
  induction m using Quotient.ind
  exact List.quotientRec_mk f h a
#align multiset.quotient_rec_mk Multiset.quotientRec_mk

@[simp] lemma quotientRecOn_mk {m : Multiset ι} {C : (∀ i ∈ m, Quotient (S i)) → Sort _}
    (a : ∀ i ∈ m, α i) :
    @quotientRecOn _ _ _ _ _ C (fun i hi ↦ ⟦a i hi⟧) = fun f _ ↦ f a := by
  ext f h
  exact quotientRec_mk _ _ _
#align multiset.quotient_rec_on_mk Multiset.quotientRecOn_mk

end Multiset
