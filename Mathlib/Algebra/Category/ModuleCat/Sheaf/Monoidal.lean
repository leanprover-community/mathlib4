/-
Copyright (c) 2026 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided

/-!
# The monoidal structure on sheaves of modules
-/

universe u

open CategoryTheory MonoidalCategory

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}

namespace PresheafOfModules

variable {R : Cᵒᵖ ⥤ CommRingCat.{u}} {M N P : PresheafOfModules.{u} (R ⋙ forget₂ ..)} {f : M ⟶ N}
variable [(J.W (A := Ab.{u})).IsMonoidal]

theorem W_toPresheaf_whiskerLeft (hf : J.W ((toPresheaf _).map f)) :
    J.W ((toPresheaf _).map (P ◁ f)) := by
  let pf := (toPresheaf _).map f
  refine ObjectProperty.isLocal_of_colimitCocone _ (colimitCoconeAb ..) (colimitCoconeAb ..)
    (Limits.parallelPairHomMk (_ ◁ pf) (_ ◁ pf) ?_ ?_) _ ?_ ?_
  · ext U : 3; exact TensorProduct.extₗ fun _ _ _ ↦ rfl
  · ext U : 3; exact TensorProduct.extₗ fun p (r : R.obj U) m ↦ by
      exact congr(p ⊗ₜ $((f.app U).hom.map_smul r m))
  · ext (_ | _) U : 5
    · exact TensorProduct.extₗ fun _ _ _ ↦ rfl
    · exact TensorProduct.ext' fun _ _ ↦ rfl
  · rintro (_ | _) <;> exact J.W.whiskerLeft_mem _ _ hf

theorem W_toPresheaf_whiskerRight (hf : J.W ((toPresheaf _).map f)) :
    J.W ((toPresheaf _).map (f ▷ P)) := by
  refine (J.W.arrow_mk_iso_iff <| Arrow.isoMk ((toPresheaf _).mapIso (β_ M P))
    ((toPresheaf _).mapIso (β_ N P)) ?_).2 (W_toPresheaf_whiskerLeft (P := P) hf)
  simp_rw [Arrow.mk, Arrow.hom, Functor.mapIso_hom]
  refine (Functor.map_comp ..).symm.trans (.trans ?_ (Functor.map_comp ..))
  congr 1; simp

instance : (J.W.inverseImage (toPresheaf (R ⋙ forget₂ ..))).IsMonoidal where
  whiskerLeft _ _ _ _ := W_toPresheaf_whiskerLeft
  whiskerRight _ h _ := W_toPresheaf_whiskerRight h

end PresheafOfModules

namespace SheafOfModules

variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] (R : Sheaf J CommRingCat.{u})
  [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}] [HasWeakSheafify J Ab.{u}]

/-- The monoidal structure on the category of sheaves of modules over a sheaf of commutative
rings, obtained by localizing the monoidal category of presheaves of modules. -/
noncomputable instance monoidalCategory :
    MonoidalCategory (SheafOfModules.{u} ((sheafCompose J (forget₂ ..)).obj R)) :=
  inferInstanceAs <| MonoidalCategory <| LocalizedMonoidal
    (PresheafOfModules.sheafificationCommId R)
    (J.W.inverseImage (PresheafOfModules.toPresheaf _))
    (.refl _)

noncomputable instance symmetricCategory :
    letI := monoidalCategory R
    SymmetricCategory (SheafOfModules.{u} ((sheafCompose J (forget₂ ..)).obj R)) :=
  inferInstanceAs <| SymmetricCategory <| LocalizedMonoidal
    (PresheafOfModules.sheafificationCommId R)
    (J.W.inverseImage (PresheafOfModules.toPresheaf _))
    (.refl _)

end SheafOfModules
