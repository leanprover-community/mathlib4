/-
Copyright (c) 2025 Benoît Guillemet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benoît Guillemet
-/
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Quasicompact and quasiseparated sheaves

Given a site `(C, J)`, we define a predicates for a sheaf on it being quasicompact, quasiseparated
or qcqs.

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

/-- A sheaf `F` is quasicompact if any cover `∐ G ⟶ F` admits a finite subcover. -/
def IsQuasicompact (F : Sheaf J A) : Prop :=
  ∀ (I : Type v') (G : I → Sheaf J A) (f : ∐ G ⟶ F),
  Epi f → ∃ J : Finset I, Epi ((Limits.Sigma.map' Subtype.val (fun (j : J) => 𝟙 (G j))) ≫ f)

end Quasicompact

variable [Limits.HasPullbacks A]

section Quasiseparated

/-- A morphism of sheaves `g : G ⟶ F` is quasicompact if the pullback of any morphism `F' ⟶ F`
  with quasicompact source is again quasicompact. -/
def IsQuasicompactMap {F G : Sheaf J A} (g : G ⟶ F) : Prop :=
  ∀ (F' : Sheaf J A) (f : F' ⟶ F), IsQuasicompact F' → IsQuasicompact (Limits.pullback f g)

/-- A sheaf `F` is quasiseparated if any morphism `F' ⟶ F` with quasicompact source is
  quasicompact. -/
def IsQuasiseparated (F : Sheaf J A) : Prop :=
  ∀ (F' : Sheaf J A) (f : F' ⟶ F), IsQuasicompact F' → IsQuasicompactMap f

end Quasiseparated

section Qcqs

/-- A sheaf `F` is qcqs if it is both quasicompact and quasiseparated. -/
def IsQcqs (F : Sheaf J A) : Prop :=
  IsQuasicompact F ∧ IsQuasiseparated F

end Qcqs

end Sheaf

end CategoryTheory
