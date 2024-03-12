/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Heather Macbeth, Frédéric Dupuis
-/

import Mathlib.Logic.Equiv.PartialEquiv

private axiom test_sorry : ∀ {α}, α
/-!
This is a test file for the tactic `mfld_set_tac`. Because this tactic applies a simp-set which
mostly contains lemmas in advanced parts of mathlib, it is currently impossible to truly test it
in realistic conditions. Instead, we create stub definitions and lemmas on objects such as
`PartialHomeomorph`, label them with `mfld_simps` and run tests on those.
-/

open Lean Meta Elab Tactic

/-! ## Syntax of objects and lemmas needed for testing `MfldSetTac` -/

set_option autoImplicit true
section stub_lemmas

structure PartialHomeomorph (α : Type u) (β : Type u) extends PartialEquiv α β

noncomputable
instance PartialHomeomorph.has_coe_to_fun : CoeFun (PartialHomeomorph α β) (fun _ ↦ α → β) := test_sorry

noncomputable
def PartialHomeomorph.symm (_e : PartialHomeomorph α β) : PartialHomeomorph β α := test_sorry

@[mfld_simps] lemma PartialHomeomorph.left_inv (e : PartialHomeomorph α β) {x : α}
  (_h : x ∈ e.toPartialEquiv.source) :
  e.symm (e x) = x :=
test_sorry

@[mfld_simps] theorem PartialHomeomorph.symm_to_PartialEquiv (e : PartialHomeomorph α β) :
  e.symm.toPartialEquiv = e.toPartialEquiv.symm :=
test_sorry

@[mfld_simps] lemma PartialHomeomorph.coe_coe (e : PartialHomeomorph α β) :
  (e.toPartialEquiv : α → β) = e :=
test_sorry

@[mfld_simps] lemma PartialHomeomorph.coe_coe_symm (e : PartialHomeomorph α β) :
  (e.toPartialEquiv.symm : β → α) = (e.symm : β → α) :=
test_sorry

structure ModelWithCorners (𝕜 E H : Type u) extends PartialEquiv H E :=
  (source_eq : source = Set.univ)

attribute [mfld_simps] ModelWithCorners.source_eq

noncomputable
def ModelWithCorners.symm (_I : ModelWithCorners 𝕜 E H) : PartialEquiv E H := test_sorry

noncomputable
instance ModelWithCorners.has_coe_to_fun : CoeFun (ModelWithCorners 𝕜 E H) (fun _ ↦ H → E) := test_sorry

@[mfld_simps] lemma ModelWithCorners.left_inv (I : ModelWithCorners 𝕜 E H) (x : H) :
  I.symm (I x) = x :=
test_sorry

@[mfld_simps] lemma ModelWithCorners.to_local_equiv_coe (I : ModelWithCorners 𝕜 E H) :
  (I.toPartialEquiv : H → E) = I :=
test_sorry

@[mfld_simps] lemma ModelWithCorners.to_local_equiv_coe_symm (I : ModelWithCorners 𝕜 E H) :
  (I.toPartialEquiv.symm : E → H) = I.symm :=
test_sorry

end stub_lemmas


/-! ## Tests for `MfldSetTac` -/
section tests

example (e : PartialEquiv α β) (e' : PartialEquiv β γ) :
  (e.trans e').source = e.source ∩ Set.preimage e (e.target ∩ e'.source) := by
  mfld_set_tac

example (e : PartialEquiv α β) : (e.trans e.symm).source = e.source := by mfld_set_tac

example (s : Set α) (f : PartialHomeomorph α β) :
  f.symm.toPartialEquiv.source ∩ (f.toPartialEquiv.target ∩ Set.preimage f.symm s)
  = f.symm.toPartialEquiv.source ∩ Set.preimage f.symm s := by mfld_set_tac

example
  {I : ModelWithCorners 𝕜 E H}
  {I' : ModelWithCorners 𝕜 E' H'}
  {I'' : ModelWithCorners 𝕜 E'' H''}
  (e₁ : PartialHomeomorph M H)
  (e₂ : PartialHomeomorph M' H')
  (e₃ : PartialHomeomorph M'' H'')
  {f : M → M'}
  {g : M' → M''} :
  (Set.preimage (f ∘ ((e₁.toPartialEquiv.trans I.toPartialEquiv).symm))
      (e₂.toPartialEquiv.trans I'.toPartialEquiv).source) ⊆
    {y : E |
    ((e₃.toPartialEquiv.trans I''.toPartialEquiv) ∘
          (g ∘ f) ∘ ((e₁.toPartialEquiv.trans I.toPartialEquiv).symm)) y
    = (((e₃.toPartialEquiv.trans I''.toPartialEquiv : M'' → E'') ∘
             g ∘ ((e₂.toPartialEquiv.trans I'.toPartialEquiv).symm)) ∘
          (e₂.toPartialEquiv.trans I'.toPartialEquiv : M' → E') ∘
            f ∘ ((e₁.toPartialEquiv.trans I.toPartialEquiv).symm)) y} := by
  mfld_set_tac

end tests
