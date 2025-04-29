/-
Copyright (c) 2025 Benoît Guillemet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benoît Guillemet
-/
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Quasicompact and quasiseparated sheaves

Given a site `(C, J)`, we define a predicate `isQuasicompact F`.

## Main definitions

* `CategoryTheory.Sheaf.IsQuasicompact` is the predicate saying a sheaf is quasicompact.
* `CategoryTheory.Sheaf.IsQuasiseparated` is the predicate saying a sheaf is quasiseparated.
* `CategoryTheory.Sheaf.IsQcqs` is the predicate saying a sheaf is qcqs, ie both quasicompact and
quasiseparated.


-/

universe u v u' v'

namespace CategoryTheory

open Category

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A] [HasWeakSheafify J A] [Limits.HasColimits A]

section Quasicompact

-- class Quasicompact (F : Sheaf J A) : Prop where ???

def IsQuasicompact (F : Sheaf J A) : Prop :=
  ∀ (I : Type v') (G : I → Sheaf J A) (f : ∐ G ⟶ F),
  Epi f → ∃ J : Finset I, Epi ((Limits.Sigma.map' Subtype.val (fun (j : J) => 𝟙 (G j))) ≫ f)

end Quasicompact

variable [Limits.HasPullbacks A]

section Quasiseparated

def IsQuasicompactMorphism {F G : Sheaf J A} (g : G ⟶ F) : Prop :=
  ∀ (F' : Sheaf J A) (f : F' ⟶ F), IsQuasicompact F' → IsQuasicompact (Limits.pullback f g)

def IsQuasiseparated (F : Sheaf J A) : Prop :=
  ∀ (F' : Sheaf J A) (f : F' ⟶ F), IsQuasicompact F' → IsQuasicompactMorphism f

end Quasiseparated

section Qcqs

def IsQcqs (F : Sheaf J A) : Prop :=
  IsQuasicompact F ∧ IsQuasiseparated F

end Qcqs

end Sheaf

end CategoryTheory
