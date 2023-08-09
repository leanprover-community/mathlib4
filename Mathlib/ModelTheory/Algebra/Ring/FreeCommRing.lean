/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.RingTheory.FreeCommRing

namespace FirstOrder

namespace Language

namespace ring

theorem exists_term_realize_eq_freeCommRing (p : FreeCommRing α) :
    ∃ t : Language.ring.Term α,
      (t.realize FreeCommRing.of : FreeCommRing α) = p :=
  FreeCommRing.induction_on p
    ⟨-1, by simp [Term.realize]⟩
    (fun a => ⟨Term.var a, by simp [Term.realize]⟩)
    (fun x y ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ =>
      ⟨t₁ + t₂, by simp_all [Term.realize]⟩)
    (fun x y ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ =>
      ⟨t₁ * t₂, by simp_all [Term.realize]⟩)

noncomputable def termOfFreeCommRing (p : FreeCommRing α) : Language.ring.Term α :=
  Classical.choose (exists_term_realize_eq_freeCommRing p)

variable {R : Type _} [CommRing R]

@[simp]
theorem realize_termOfFreeCommRing (p : FreeCommRing α) (v : α → R) :
    (termOfFreeCommRing p).realize v = FreeCommRing.lift v p := by
  have : (termOfFreeCommRing p).realize FreeCommRing.of = p :=
    Classical.choose_spec (exists_term_realize_eq_freeCommRing p)
  conv_rhs => rw [← this]
  induction termOfFreeCommRing p with
  | var _ => simp
  | func f _ ih => cases f <;> simp_all

end ring

end Language

end FirstOrder
