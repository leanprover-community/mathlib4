/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.ModelTheory.Algebra.Ring.FreeCommRing
import Mathlib.ModelTheory.Algebra.Field.Basic

namespace FirstOrder

namespace Language

namespace field

noncomputable def termOfFreeCommRing (p : FreeCommRing α) : Language.field.Term α :=
  field.ofRing.onTerm (ring.termOfFreeCommRing p)

variable {K : Type _} [CompatibleField K]

@[simp]
theorem realize_termOfFreeCommRing (p : FreeCommRing α) (v : α → K) :
    (termOfFreeCommRing p).realize v = FreeCommRing.lift v p := by
  letI := Language.ring.freeCommRingRingStructure α
  have : (ring.termOfFreeCommRing p).realize FreeCommRing.of = p :=
    Classical.choose_spec (ring.exists_term_realize_eq_freeCommRing p)
  conv_rhs => rw [← this]
  simp only [termOfFreeCommRing]
  induction ring.termOfFreeCommRing p with
  | var _ => simp [termOfFreeCommRing, Term.realize]
  | func f _ ih => cases f <;> simp_all [Term.realize, field.ofRing]

end field

end Language

end FirstOrder
