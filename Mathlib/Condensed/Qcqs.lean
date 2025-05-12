/-
Copyright (c) 2025 Benoît Guillemet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benoît Guillemet
-/
import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Sites.Qcqs
import Mathlib.Condensed.Functors
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.ConcreteSheafification

/-!
# Quasicompact and quasiseparated condensed sets

We give properties of quasicompact, quasiseparated and qcqs condensed sets.

-/

universe u w

open CategoryTheory

namespace Condensed

lemma useless : HasSheafify (coherentTopology CompHaus.{u}) (Type (u + 1)) :=
  @instHasSheafifyOfHasFiniteLimits _ _ (coherentTopology CompHaus.{u}) (Type (u + 1)) _ _ _ _ _
    Types.instFunLike
    Types.instConcreteCategory
    (fun _ => Limits.id_preservesColimitsOfSize.preservesColimitsOfShape)
    Limits.id_preservesLimitsOfSize
    (Functor.FullyFaithful.reflectsIsomorphisms (Functor.FullyFaithful.id _)) _

theorem isQuasicompact_iff_compHaus_cover (X : CondensedSet.{u}) :
    have := useless
    Sheaf.Quasicompact X ↔ ∃ S : CompHaus.{u}, ∃ f : compHausToCondensed.obj S ⟶ X, Epi f :=
  sorry
