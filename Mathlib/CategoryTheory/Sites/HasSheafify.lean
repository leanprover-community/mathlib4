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

-- /--
-- `HasWeakSheafify` means that the inclusion functor from sheaves to presheaves admits a
-- left adjiont.
-- -/
-- class HasWeakSheafify where
--   /-- `sheafToPresheaf` is a right adjoint -/
--   isRightAdjoint : IsRightAdjoint (sheafToPresheaf J A)

-- attribute [instance] HasWeakSheafify.isRightAdjoint

-- /--
-- `HasSheafify` means that the inclusion functor from sheaves to presheaves admits a left exact
-- left adjiont (sheafification).
-- -/
-- class HasSheafify extends HasWeakSheafify J A where
--   isLeftExact : PreservesFiniteLimits (leftAdjoint (sheafToPresheaf J A))

-- attribute [instance] HasSheafify.isLeftExact

-- /-- An instance `HasSheafify J A` given an adjunction `F ⊣ sheafToPresheaf J A` such that `F`
-- preserves finite limits -/
-- def HasSheafify.mk' {F : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A} (adj : F ⊣ sheafToPresheaf J A)
--     [PreservesFiniteLimits F] : HasSheafify J A where
--   isRightAdjoint := ⟨F, adj⟩
--   isLeftExact :=
--     let i : (h : IsRightAdjoint (sheafToPresheaf J A) := ⟨F, adj⟩) →
--       F ≅ leftAdjoint (sheafToPresheaf J A) := fun _ ↦
--       adj.leftAdjointUniq (Adjunction.ofRightAdjoint (sheafToPresheaf J A))
--     ⟨fun _ ↦ preservesLimitsOfShapeOfNatIso (i _)⟩

-- noncomputable section

-- /-- The sheafification functor, left adjoint to the inclusion. -/
-- def presheafToSheaf [HasWeakSheafify J A] : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A :=
--   leftAdjoint (sheafToPresheaf J A)

-- instance [HasSheafify J A] : PreservesFiniteLimits (presheafToSheaf J A) := HasSheafify.isLeftExact

-- /-- The sheafification-inclusion adjunction. -/
-- def sheafificationAdjunction [HasWeakSheafify J A] : presheafToSheaf J A ⊣ sheafToPresheaf J A :=
--   HasWeakSheafify.isRightAdjoint.adj

-- instance [HasWeakSheafify J A] : IsLeftAdjoint <| presheafToSheaf J A where
--   right := sheafToPresheaf J A
--   adj := sheafificationAdjunction J A

-- end

/--
`HasSheafify` means that the inclusion functor from sheaves to presheaves admits a left exact
left adjiont (sheafification).
-/
class HasSheafify : Prop where
  isRightAdjoint : Nonempty (IsRightAdjoint (sheafToPresheaf J A))
  isLeftExact : letI := isRightAdjoint.some
    Nonempty (PreservesFiniteLimits (leftAdjoint (sheafToPresheaf J A)))

noncomputable section

instance [HasSheafify J A] : IsRightAdjoint (sheafToPresheaf J A) :=
  HasSheafify.isRightAdjoint.some

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
def presheafToSheaf [IsRightAdjoint <| sheafToPresheaf J A] : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A :=
  leftAdjoint (sheafToPresheaf J A)

instance [HasSheafify J A] : PreservesFiniteLimits (presheafToSheaf J A) :=
  HasSheafify.isLeftExact.some

/-- The sheafification-inclusion adjunction. -/
def sheafificationAdjunction [IsRightAdjoint <| sheafToPresheaf J A] :
    presheafToSheaf J A ⊣ sheafToPresheaf J A := IsRightAdjoint.adj

instance [IsRightAdjoint <| sheafToPresheaf J A] : IsLeftAdjoint <| presheafToSheaf J A where
  adj := sheafificationAdjunction J A

end

end CategoryTheory
