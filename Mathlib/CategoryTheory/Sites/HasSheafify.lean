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

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
variable (A : Type u₂) [Category.{v₂} A]

/--
A proposition saying that the inclusion functor from sheaves to presheaves admits a left adjoint.
-/
abbrev HasWeakSheafify := Nonempty (IsRightAdjoint (sheafToPresheaf J A))

/--
`HasSheafify` means that the inclusion functor from sheaves to presheaves admits a left exact
left adjiont (sheafification).
-/
class HasSheafify : Prop where
  isRightAdjoint : HasWeakSheafify J A
  isLeftExact : letI := isRightAdjoint.some
    Nonempty (PreservesFiniteLimits (leftAdjoint (sheafToPresheaf J A)))

instance [HasSheafify J A] : HasWeakSheafify J A := HasSheafify.isRightAdjoint

instance [IsRightAdjoint <| sheafToPresheaf J A] : HasWeakSheafify J A := ⟨inferInstance⟩

noncomputable section

instance [h : HasWeakSheafify J A] : IsRightAdjoint (sheafToPresheaf J A) := h.some

instance [HasSheafify J A] : PreservesFiniteLimits (leftAdjoint (sheafToPresheaf J A)) :=
  HasSheafify.isLeftExact.some

theorem HasSheafify.mk' {F : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A} (adj : F ⊣ sheafToPresheaf J A)
    [PreservesFiniteLimits F] : HasSheafify J A where
  isRightAdjoint := ⟨⟨F, adj⟩⟩
  isLeftExact :=
    let i : (h : IsRightAdjoint (sheafToPresheaf J A) := ⟨F, adj⟩) →
      F ≅ leftAdjoint (sheafToPresheaf J A) := fun _ ↦
      adj.leftAdjointUniq (Adjunction.ofRightAdjoint (sheafToPresheaf J A))
    ⟨⟨fun _ ↦ preservesLimitsOfShapeOfNatIso (i _)⟩⟩

/-- The sheafification functor, left adjoint to the inclusion. -/
def presheafToSheaf [HasWeakSheafify J A] : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A :=
  leftAdjoint (sheafToPresheaf J A)

instance [HasSheafify J A] : PreservesFiniteLimits (presheafToSheaf J A) :=
  HasSheafify.isLeftExact.some

/-- The sheafification-inclusion adjunction. -/
def sheafificationAdjunction [HasWeakSheafify J A] :
    presheafToSheaf J A ⊣ sheafToPresheaf J A := IsRightAdjoint.adj

instance [HasWeakSheafify J A] : IsLeftAdjoint <| presheafToSheaf J A where
  adj := sheafificationAdjunction J A

end

end CategoryTheory
