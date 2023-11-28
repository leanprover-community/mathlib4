/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import Mathlib.CategoryTheory.PUnit
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

#align_import algebraic_topology.fundamental_groupoid.punit from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Fundamental groupoid of punit

The fundamental groupoid of punit is naturally isomorphic to `CategoryTheory.Discrete PUnit`
-/


noncomputable section

open CategoryTheory

universe u v

namespace Path

instance : Subsingleton (Path PUnit.unit PUnit.unit) :=
  ⟨fun x y => by ext⟩

end Path

namespace FundamentalGroupoid

instance {x y : FundamentalGroupoid PUnit} : Subsingleton (x ⟶ y) := by
  convert_to Subsingleton (Path.Homotopic.Quotient PUnit.unit PUnit.unit)
  apply Quotient.instSubsingletonQuotient

/-- Equivalence of groupoids between fundamental groupoid of punit and punit -/
def punitEquivDiscretePUnit : FundamentalGroupoid PUnit.{u + 1} ≌ Discrete PUnit.{v + 1} :=
  CategoryTheory.Equivalence.mk
    (Functor.star _)
    ((CategoryTheory.Functor.const _).obj ⟨PUnit.unit⟩)
    -- Porting note: was `by decide`
    (NatIso.ofComponents fun _ => eqToIso (by simp))
    (Functor.punitExt _ _)
#align fundamental_groupoid.punit_equiv_discrete_punit FundamentalGroupoid.punitEquivDiscretePUnit

end FundamentalGroupoid
