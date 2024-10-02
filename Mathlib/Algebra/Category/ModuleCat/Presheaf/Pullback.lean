/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward

/-!
# Pullback of presheaves of modules

Let `F : C ⥤ D` be a functor, `R : Dᵒᵖ ⥤ RingCat` and `S : Cᵒᵖ ⥤ RingCat` be presheaves
of rings, and `φ : S ⟶ F.op ⋙ R` be a morphism of presheaves of rings,
we introduce the pullback functor `pullback : PresheafOfModules S ⥤ PresheafOfModules R`
as the left adjoint of `pushforward : PresheafOfModules R ⥤ PresheafOfModules S`.
The existence of this left adjoint functor is obtained under suitable universe assumptions (TODO).

-/

universe v v₁ v₂ u₁ u₂ u

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace PresheafOfModules

variable {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

section

variable [(pushforward.{v} φ).IsRightAdjoint]

/-- The pullback functor `PresheafOfModules S ⥤ PresheafOfModules R` induced by
a morphism of presheaves of rings `S ⟶ F.op ⋙ R`, defined as the left adjoint
functor to the pushforward, when it exists. -/
noncomputable def pullback : PresheafOfModules.{v} S ⥤ PresheafOfModules.{v} R :=
  (pushforward.{v} φ).leftAdjoint

/-- Given a morphism of presheaves of rings `S ⟶ F.op ⋙ R`, this is the adjunction
between associated pullback and pushforward functors on the categories
of presheaves of modules. -/
noncomputable def pullbackPushforwardAdjunction : pullback.{v} φ ⊣ pushforward.{v} φ :=
  Adjunction.ofIsRightAdjoint (pushforward φ)

end

-- Strategy for the existence of `pullback`:
-- it is easy to guess its value on `(free _).obj (yoneda.obj X)`
-- then it is also defined on coproducts of such objects
-- any presheaf of modules is a cokernel of a map between such coproducts

end PresheafOfModules
