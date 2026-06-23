/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardLaxMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Monoidal

/-!
# ...

-/

@[expose] public section

universe w v u

namespace SheafOfModules

open CategoryTheory Functor Limits

variable {C D : Type*} [Category* C] [Category* D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  [Functor.IsContinuous F J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat)]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat)]
  [K.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat)]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}]
  [(W.{u} R).IsMonoidal] [(W.{u} S).IsMonoidal]
  (φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj R)

noncomputable abbrev pushforwardOfCommRing :
    SheafOfModules.{u} ((sheafCompose K (forget₂ _ _)).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ _ _)).obj S) :=
  pushforward ((sheafCompose J (forget₂ _ RingCat)).map φ)

set_option backward.isDefEq.respectTransparency false in
noncomputable instance : (pushforwardOfCommRing φ).LaxMonoidal := by
  let e :
    forgetOfCommRing _ ⋙ PresheafOfModules.pushforwardOfCommRing.{u}
      ((sheafToPresheaf _ _).map φ) ⋙
        PresheafOfModules.sheafificationOfCommRing.{u} S ≅
        (pushforwardOfCommRing φ) := sorry
  letI := monoidalSheafificationOfCommRing S
  exact Functor.LaxMonoidal.ofIso e

noncomputable instance [IsIso (Functor.LaxMonoidal.ε (pushforwardOfCommRing φ))]
    [∀ F G, IsIso (Functor.LaxMonoidal.μ (pushforwardOfCommRing φ) F G)]
    : (pushforwardOfCommRing φ).Monoidal :=
  .ofLaxMonoidal _

end SheafOfModules
