/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Sheaf
/-!

# Sheafification

Given a site `(C, J)` we define a typeclass `HasSheaf J A` saying that the inclusion functor from
`A`-valued sheaves on `C` to presheaves admits a left adjoint (sheafification).
-/

namespace CategoryTheory

variable {C : Type*} [Category C] (J : GrothendieckTopology C)
variable (A : Type*) [Category A]

/--
`HasSheafify` means that the inclusion functor from sheaves to presheaves admits a left adjiont
(sheafification).

Note: we do not require the sheafification functor to be left exact in the definition of this
typeclass. In the standard setting of a concrete category whose forgetful functor commutes with
certain colimits and limits, we have the sheafification functor is left exact, see
`Mathlib/CategoryTheory/Sites/LeftExact`.
-/
class HasSheafify : Prop where
  /-- `sheafToPresheaf` is a right adjoint -/
  isRightAdjoint : Nonempty <| IsRightAdjoint (sheafToPresheaf J A)

noncomputable section

instance [HasSheafify J A] : IsRightAdjoint (sheafToPresheaf J A) := HasSheafify.isRightAdjoint.some

/-- The sheafification functor, left adjoint to the inclusion. -/
def presheafToSheaf [HasSheafify J A] : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A :=
  leftAdjoint (sheafToPresheaf J A)

/-- The sheafification-inclusion adjunction. -/
def sheafificationAdjunction [HasSheafify J A] : presheafToSheaf J A ⊣ sheafToPresheaf J A :=
  HasSheafify.isRightAdjoint.some.adj

instance [HasSheafify J A] : IsLeftAdjoint <| presheafToSheaf J A where
  right := sheafToPresheaf J A
  adj := sheafificationAdjunction J A

end

end CategoryTheory
