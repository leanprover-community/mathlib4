/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.ModelTheory.Algebra.Field.Basic
import Mathlib.RingTheory.FreeCommRing

namespace FirstOrder

namespace Language

namespace field

@[simp]
def freeCommRingRingStructure (α : Type u) :
    Language.ring.Structure (FreeCommRing α) :=
  { funMap := fun {n} f =>
      match n, f with
      | _, .add => fun x => x 0 + x 1
      | _, .mul => fun x => x 0 * x 1
      | _, .neg => fun x => - x 0
      | _, .zero => fun _ => 0
      | _, .one => fun _ => 1,
    RelMap := fun f => by cases f }

variable {α : Type u}

section

attribute [local instance] freeCommRingRingStructure

private theorem exists_term_realize_eq_freeCommRing (p : FreeCommRing α) :
    ∃ t : Language.ring.Term α,
      (t.realize FreeCommRing.of : FreeCommRing α) = p :=
  FreeCommRing.induction_on p
    ⟨-1, by simp [Term.realize]⟩
    (fun a => ⟨Term.var a, by simp [Term.realize]⟩)
    (fun x y ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ =>
      ⟨t₁ + t₂, by simp_all [Term.realize]⟩)
    (fun x y ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ =>
      ⟨t₁ * t₂, by simp_all [Term.realize]⟩)

end

noncomputable def termOfFreeCommRing (p : FreeCommRing α) : Language.field.Term α :=
  field.ofRing.onTerm <| Classical.choose (exists_term_realize_eq_freeCommRing p)

variable {K : Type v} [CompatibleField K]

@[simp]
theorem realize_termOfFreeCommRing (p : FreeCommRing α) (v : α → K) :
    (termOfFreeCommRing p).realize v = FreeCommRing.lift v p := by
  letI := Language.field.freeCommRingRingStructure α
  rw [termOfFreeCommRing, ofRing]
  conv_rhs => rw [← Classical.choose_spec (field.exists_term_realize_eq_freeCommRing p)]
  induction Classical.choose (field.exists_term_realize_eq_freeCommRing p) with
  | var _ => simp [Term.realize]
  | func f a ih =>
    cases f <;>
    simp [Term.realize, ih, ofRing, LHom.onTerm]

end field

end Language

end FirstOrder
