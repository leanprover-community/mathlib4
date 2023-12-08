/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Limits.Preserves.Finite
/-!

# Sheafification

Given a site `(C, J)` we define a typeclass `HasSheaf J A` saying that the inclusion functor from
`A`-valued sheaves on `C` to presheaves admits a left adjoint (sheafification).
-/

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C] (J : GrothendieckTopology C)
variable (A : Type*) [Category A]

/--
`HasWeakSheafify` means that the inclusion functor from sheaves to presheaves admits a
left adjiont.
-/
class HasWeakSheafify : Prop where
  /-- `sheafToPresheaf` is a right adjoint -/
  isRightAdjoint : Nonempty <| IsRightAdjoint (sheafToPresheaf J A)

/--
`HasSheafify` means that the inclusion functor from sheaves to presheaves admits a left exact
left adjiont (sheafification).
-/
class HasSheafify extends HasWeakSheafify J A where
  isLeftExact : letI := isRightAdjoint.some
    Nonempty <| PreservesFiniteLimits (leftAdjoint (sheafToPresheaf J A))

theorem HasSheafify.mk' {F : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A} (adj : F ⊣ sheafToPresheaf J A)
    [PreservesFiniteLimits F] : HasSheafify J A where
  isRightAdjoint := ⟨⟨F, adj⟩⟩
  isLeftExact :=
    have h : Nonempty (IsRightAdjoint (sheafToPresheaf J A)) := ⟨⟨F, adj⟩⟩
    letI := h.some
    let i : F ≅ leftAdjoint (sheafToPresheaf J A) :=
      adj.leftAdjointUniq (Adjunction.ofRightAdjoint (sheafToPresheaf J A))
    ⟨⟨fun _ ↦ preservesLimitsOfShapeOfNatIso i⟩⟩

noncomputable section

instance [HasWeakSheafify J A] : IsRightAdjoint (sheafToPresheaf J A) :=
  HasWeakSheafify.isRightAdjoint.some

/-- The sheafification functor, left adjoint to the inclusion. -/
def presheafToSheaf [HasWeakSheafify J A] : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A :=
  leftAdjoint (sheafToPresheaf J A)

instance [HasSheafify J A] : PreservesFiniteLimits (presheafToSheaf J A) :=
  HasSheafify.isLeftExact.some

/-- The sheafification-inclusion adjunction. -/
def sheafificationAdjunction [HasWeakSheafify J A] : presheafToSheaf J A ⊣ sheafToPresheaf J A :=
  HasWeakSheafify.isRightAdjoint.some.adj

instance [HasWeakSheafify J A] : IsLeftAdjoint <| presheafToSheaf J A where
  right := sheafToPresheaf J A
  adj := sheafificationAdjunction J A

end

end CategoryTheory
