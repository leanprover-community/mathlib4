/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module topology.sheaves.operations
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Category.Ring.Instances
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Topology.Sheaves.Stalks

/-!

# Operations on sheaves

## Main definition

- `SubmonoidPresheaf` : A subpresheaf with a submonoid structure on each of the components.
- `LocalizationPresheaf` : The localization of a presheaf of commrings at a `SubmonoidPresheaf`.
- `TotalQuotientPresheaf` : The presheaf of total quotient rings.

-/

-- Porting note: all aligns here start with `Top.`
set_option linter.uppercaseLean3 false

open scoped nonZeroDivisors

open TopologicalSpace Opposite CategoryTheory

universe v u w

-- Porting note: [TODO] It does not find these instances :(
instance hack₁ (X : CommRingCat) : CommRing ((forget CommRingCat).obj X) :=
  X.commRing

-- Porting note: [TODO] It does not find these instances :(
instance hack₂ (X Y : CommRingCat) :
  MonoidHomClass (X ⟶ Y) ((forget CommRingCat).obj X) ((forget CommRingCat).obj Y) :=
  @RingHomClass.toMonoidHomClass (X ⟶ Y) ((forget CommRingCat).obj X)
    ((forget CommRingCat).obj Y) _ _ (@RingHom.ringHomClass _ _ _ _)

namespace TopCat

namespace Presheaf

variable {X : TopCat.{w}} {C : Type u} [Category.{v} C] [ConcreteCategory C]

attribute [local instance 1000] ConcreteCategory.hasCoeToSort

/-- A subpresheaf with a submonoid structure on each of the components. -/
structure SubmonoidPresheaf [∀ X : C, MulOneClass X] [∀ X Y : C, MonoidHomClass (X ⟶ Y) X Y]
    (F : X.Presheaf C) where
  obj : ∀ U, Submonoid (F.obj U)
  map : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), obj U ≤ (obj V).comap (F.map i)
#align Top.presheaf.submonoid_presheaf TopCat.Presheaf.SubmonoidPresheaf

variable {F : X.Presheaf CommRingCat.{w}} (G : F.SubmonoidPresheaf)

/-- The localization of a presheaf of `CommRing`s with respect to a `SubmonoidPresheaf`. -/
protected noncomputable def SubmonoidPresheaf.localizationPresheaf : X.Presheaf CommRingCat where
  obj U := CommRingCat.of <| Localization (G.obj U)
  map {U V} i := CommRingCat.ofHom <| IsLocalization.map _ (F.map i) (G.map i)
  map_id U := by
    apply IsLocalization.ringHom_ext (G.obj U)
    any_goals dsimp; infer_instance
    refine' (IsLocalization.map_comp _).trans _
    rw [F.map_id]
    rfl
  map_comp {U V W} i j := by
    refine' Eq.trans _ (IsLocalization.map_comp_map _ _).symm
    ext; dsimp; congr; rw [F.map_comp]; rfl
#align Top.presheaf.submonoid_presheaf.localization_presheaf TopCat.Presheaf.SubmonoidPresheaf.localizationPresheaf

/-- The map into the localization presheaf. -/
def SubmonoidPresheaf.toLocalizationPresheaf : F ⟶ G.localizationPresheaf where
  app U := CommRingCat.ofHom <| algebraMap (F.obj U) (Localization <| G.obj U)
  naturality {U V} i := (IsLocalization.map_comp (G.map i)).symm
#align Top.presheaf.submonoid_presheaf.to_localization_presheaf TopCat.Presheaf.SubmonoidPresheaf.toLocalizationPresheaf

instance : Epi G.toLocalizationPresheaf :=
  @NatTrans.epi_of_epi_app _ _ G.toLocalizationPresheaf fun U => Localization.epi' (G.obj U)

variable (F)

/-- Given a submonoid at each of the stalks, we may define a submonoid presheaf consisting of
sections whose restriction onto each stalk falls in the given submonoid. -/
@[simps]
noncomputable def submonoidPresheafOfStalk (S : ∀ x : X, Submonoid (F.stalk x)) :
    F.SubmonoidPresheaf where
  obj U := ⨅ x : unop U, Submonoid.comap (F.germ x) (S x)
  map {U V} i := by
    intro s hs
    simp only [Submonoid.mem_comap, Submonoid.mem_iInf] at hs ⊢
    intro x
    change (F.map i.unop.op ≫ F.germ x) s ∈ _
    rw [F.germ_res]
    exact hs _
#align Top.presheaf.submonoid_presheaf_of_stalk TopCat.Presheaf.submonoidPresheafOfStalk

noncomputable instance : Inhabited F.SubmonoidPresheaf :=
  ⟨F.submonoidPresheafOfStalk fun _ => ⊥⟩

/-- The localization of a presheaf of `CommRing`s at locally non-zero-divisor sections. -/
noncomputable def totalQuotientPresheaf : X.Presheaf CommRingCat.{w} :=
  (F.submonoidPresheafOfStalk fun x => (F.stalk x)⁰).localizationPresheaf
#align Top.presheaf.total_quotient_presheaf TopCat.Presheaf.totalQuotientPresheaf

/-- The map into the presheaf of total quotient rings -/
noncomputable def toTotalQuotientPresheaf : F ⟶ F.totalQuotientPresheaf :=
  SubmonoidPresheaf.toLocalizationPresheaf _
deriving Epi
#align Top.presheaf.to_total_quotient_presheaf TopCat.Presheaf.toTotalQuotientPresheaf

instance (F : X.Sheaf CommRingCat.{w}) : Mono F.Presheaf.toTotalQuotientPresheaf := by
  apply (config := { synthAssignedInstances := false }) NatTrans.mono_of_mono_app
  intro U
  apply concrete_category.mono_of_injective
  apply IsLocalization.injective _
  pick_goal 3; · exact Localization.isLocalization
  intro s hs t e
  apply section_ext F (unop U)
  intro x
  rw [map_zero]
  apply submonoid.mem_infi.mp hs x
  rw [← map_mul, e, map_zero]

end Presheaf

end TopCat
