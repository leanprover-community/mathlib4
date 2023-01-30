/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Data.Finset.Quot
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.GeneralizeProofs

/-!
# Quotients indexed by a finite type

In this file, we define lifting and recursion principle for quotients indexed by a finite type.

## Main definitions

* `Fintype.quotientLift`: Given a fintype `ι`. A function on `∀ i : ι, α i` which respects setoid
  `S i` for each `i` can be lifted to a function on `∀ i : ι, Quotient (S i)`.
* `Fintype.quotientRec`: Recursion principle for quotients indexed by a finite type. It is the
  dependent version of `Fintype.quotientLift`.
-/

namespace Fintype
variable {ι : Type _} [Fintype ι] [DecidableEq ι] {α : ι → Sort _} [S : ∀ i, Setoid (α i)]
  {β : Sort _}

/-- Given a collection of setoids indexed by a fintype `ι` and a function that for each `i : ι`
  gives a term of the corresponding quotient type, then there is corresponding term in the quotient
  of the product of the setoids. -/
def quotientChoice (q : ∀ i, Quotient (S i)) :
    @Quotient (∀ i, α i) piSetoid :=
  Finset.quotientLiftOn (fun i _ ↦ q i) (fun a ↦ ⟦fun i ↦ a i (Finset.mem_univ _)⟧)
    (fun _ _ ha ↦ Quotient.sound (fun i ↦ ha i _))
#align fintype.quotient_choice Fintype.quotientChoice

theorem quotientChoice_mk (a : ∀ i, α i) :
    quotientChoice (fun i ↦ ⟦a i⟧) = ⟦a⟧ := by
  dsimp [quotientChoice]
  rw [Finset.quotientLiftOn_mk (fun i _ ↦ a i)]
#align fintype.quotient_choice_mk Fintype.quotientChoice_mk

alias quotientChoice ← _root_.Quotient.finChoice
#align quotient.fin_choice Quotient.finChoice

lemma _root_.Quotient.finChoice_eq (a : ∀ i, α i) :
    Quotient.finChoice (fun i ↦ ⟦a i⟧) = ⟦a⟧ :=
  quotientChoice_mk a
#align quotient.fin_choice_eq Quotient.finChoice_eq

/-- Lift a function on `∀ i, α i` to a function on `∀ i, Quotient (S i)`. -/
def quotientLiftOn (q : ∀ i, Quotient (S i)) (f : (∀ i, α i) → β)
    (h : ∀ (a b : ∀ i, α i), (∀ i, a i ≈ b i) → f a = f b) : β :=
  Finset.quotientLiftOn (fun i _ ↦ q i) (fun a ↦ f (fun i ↦ a i (Finset.mem_univ _)))
    (fun _ _ ha ↦ h _ _ (fun i ↦ ha i _))
#align fintype.quotient_lift_on Fintype.quotientLiftOn

/-- Lift a function on `∀ i, α i` to a function on `∀ i, Quotient (S i)`. -/
def quotientLift (f : (∀ i, α i) → β)
    (h : ∀ (a b : ∀ i, α i), (∀ i, a i ≈ b i) → f a = f b)
    (q : ∀ i, Quotient (S i)) : β :=
  quotientLiftOn q f h
#align fintype.quotient_lift Fintype.quotientLift

@[simp] lemma quotientLiftOn_empty [e : IsEmpty ι] (q : ∀ i, Quotient (S i)) :
    @quotientLiftOn _ _ _ _ _ β q = fun f _ ↦ f e.elim := by
  ext f h; dsimp [quotientLiftOn]
  trans Finset.quotientLiftOn (fun i _ ↦ q i)
      (fun (_ : ∀ i ∈ ∅, α i) ↦ f (fun i ↦ e.elim i)) (fun _ _ _ ↦ rfl)
  · congr
    · exact Finset.univ_eq_empty
    · rw [Finset.univ_eq_empty]
    · rw [← Finset.univ_eq_empty, heq_iff_eq]
      ext a; congr
      exact Subsingleton.elim _ _ -- Porting note: `congr` can do this in mathlib3
    · exact proof_irrel_heq _ _ -- Porting note: `congr'` can do this in mathlib3
  · rw [Finset.quotientLiftOn_empty]
#align fintype.quotient_lift_on_empty Fintype.quotientLiftOn_empty

@[simp] lemma quotientLiftOn_mk (a : ∀ i, α i) :
    @quotientLiftOn _ _ _ _ _ β (fun i ↦ ⟦a i⟧) = fun f _ ↦ f a := by
  ext f h; dsimp [quotientLiftOn]
  rw [Finset.quotientLiftOn_mk]
#align fintype.quotient_lift_on_mk Fintype.quotientLiftOn_mk

@[simp] lemma quotientLift_empty [e : IsEmpty ι] (f : (∀ i ∈ (∅ : Finset ι), α i) → β) (h) :
    quotientLift f h = (fun _ ↦ f e.elim) := by
  ext f h; dsimp [quotientLift]
  rw [quotientLiftOn_empty]
#align fintype.quotient_lift_empty Fintype.quotientLift_empty

@[simp] lemma quotientLift_mk (f : (∀ i, α i) → β)
    (h : ∀ (a b : ∀ i, α i), (∀ i, a i ≈ b i) → f a = f b)
    (a : ∀ i, α i) : quotientLift f h (fun i ↦ ⟦a i⟧) = f a := by
  dsimp [quotientLift]
  rw [quotientLiftOn_mk]
#align fintype.quotient_lift_mk Fintype.quotientLift_mk

-- Porting note: no `decidable_classical` `fintype_finite` linter
-- `@[nolint decidable_classical fintype_finite]`
/-- Choice-free induction principle for quotients indexed by a finite type.
  See `Quotient.induction_on_pi` for the general version assuming `classical.choice`. -/
@[elab_as_elim]
lemma quotient_ind {C : (∀ i, Quotient (S i)) → Prop}
    (f : ∀ a : ∀ i, α i, C (fun i ↦ ⟦a i⟧)) (q : ∀ i, Quotient (S i)) : C q :=
  @Finset.quotient_ind _ _ _ _ _ (fun q ↦ C (fun i ↦ q i (Finset.mem_univ _))) (fun _ ↦ f _)
    (fun i _ ↦ q i)
#align fintype.quotient_ind Fintype.quotient_ind

-- Porting note: no `decidable_classical` `fintype_finite` linter
-- `@[nolint decidable_classical fintype_finite]`
/-- Choice-free induction principle for quotients indexed by a finite type.
  See `Quotient.induction_on_pi` for the general version assuming `classical.choice`. -/
@[elab_as_elim]
lemma quotient_induction_on {C : (∀ i, Quotient (S i)) → Prop}
    (q : ∀ i, Quotient (S i)) (f : ∀ a : ∀ i, α i, C (fun i ↦ ⟦a i⟧)) :
    C q :=
  quotient_ind f q
#align fintype.quotient_induction_on Fintype.quotient_induction_on

/-- Recursion principle for quotients indexed by a finite type. -/
@[elab_as_elim] def quotientRecOn {C : (∀ i, Quotient (S i)) → Sort uC}
    (q : ∀ i, Quotient (S i))
    (f : ∀ a : ∀ i, α i, C (fun i ↦ ⟦a i⟧))
    (h : ∀ (a b : ∀ i, α i) (h : ∀ i, a i ≈ b i),
      Eq.ndrec (f a) (funext fun i ↦ Quotient.sound (h i)) = f b) :
    C q :=
  @Finset.quotientRecOn _ _ _ _ _ (fun q ↦ C (fun i ↦ q i (Finset.mem_univ _)))
    (fun i _ ↦ q i) (fun a ↦ f (fun i ↦ a i _))
    (fun a b H ↦ by
      simp_rw [← h _ _ (fun i ↦ H i (Finset.mem_univ _))]
      -- exact eq_of_heq ((eqRec_heq _ _).trans (eqRec_heq _ _).symm)
      generalize_proofs H
      exact eq_of_heq ((eqRec_heq (φ := fun q ↦ C (fun i ↦ q i (Finset.mem_univ _)))
        H _).trans (eqRec_heq _ _).symm) -- Porting note: why it's needed to tell lean the motive?
    )
#align fintype.quotient_rec_on Fintype.quotientRecOn

/-- Recursion principle for quotients indexed by a finite type. -/
@[elab_as_elim] def quotientRec {C : (∀ i, Quotient (S i)) → Sort _}
    (f : ∀ a : ∀ i, α i, C (fun i ↦ ⟦a i⟧))
    (h : ∀ (a b : ∀ i, α i) (h : ∀ i, a i ≈ b i),
      Eq.ndrec (f a) (funext fun i ↦ Quotient.sound (h i)) = f b)
    (q : ∀ i, Quotient (S i)) :
    C q :=
  quotientRecOn q f h
#align fintype.quotient_rec Fintype.quotientRec

/-- Recursion principle for quotients indexed by a finite type. -/
@[elab_as_elim] def quotientHRecOn {C : (∀ i, Quotient (S i)) → Sort _}
    (q : ∀ i, Quotient (S i))
    (f : ∀ a : ∀ i, α i, C (fun i ↦ ⟦a i⟧))
    (h : ∀ (a b : ∀ i, α i), (∀ i, a i ≈ b i) → HEq (f a) (f b)) :
    C q :=
  quotientRecOn q f (fun a b p ↦ eq_of_heq ((eq_rec_heq _ (f a)).trans (h a b p)))
#align fintype.quotient_hrec_on Fintype.quotientHRecOn

@[simp] lemma quotientRec_mk {C : (∀ i, Quotient (S i)) → Sort _}
    (f : ∀ a : ∀ i, α i, C (fun i ↦ ⟦a i⟧))
    (h) (a : ∀ i, α i) :
    @quotientRec _ _ _ _ _ C f h (fun i ↦ ⟦a i⟧) = f a :=
  Finset.quotientRec_mk _ _ _
#align fintype.quotient_rec_mk Fintype.quotientRec_mk

@[simp] lemma quotientRecOn_mk {C : (∀ i, Quotient (S i)) → Sort _}
    (a : ∀ i, α i) :
    @quotientRecOn _ _ _ _ _ C (fun i ↦ ⟦a i⟧) = fun f _ ↦ f a := by
  ext f h
  exact quotientRec_mk _ _ _
#align fintype.quotient_rec_on_mk Fintype.quotientRecOn_mk

end Fintype
