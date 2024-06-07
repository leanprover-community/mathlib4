/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Category.Ring.Instances
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Topology.Sheaves.Stalks

#align_import topology.sheaves.operations from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

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

namespace TopCat

namespace Presheaf

variable {X : TopCat.{w}} {C : Type u} [Category.{v} C] [ConcreteCategory C]

attribute [local instance 1000] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike

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
    simp_rw [F.map_id]
    ext x
    -- Porting note: `M` and `S` needs to be specified manually
    exact IsLocalization.map_id (M := G.obj U) (S := Localization (G.obj U)) x
  map_comp {U V W} i j := by
    delta CommRingCat.ofHom CommRingCat.of Bundled.of
    simp_rw [F.map_comp, CommRingCat.comp_eq_ring_hom_comp]
    rw [IsLocalization.map_comp_map]
#align Top.presheaf.submonoid_presheaf.localization_presheaf TopCat.Presheaf.SubmonoidPresheaf.localizationPresheaf

-- Porting note: this instance can't be synthesized
instance (U) : Algebra ((forget CommRingCat).obj (F.obj U)) (G.localizationPresheaf.obj U) :=
  show Algebra _ (Localization (G.obj U)) from inferInstance

-- Porting note: this instance can't be synthesized
instance (U) : IsLocalization (G.obj U) (G.localizationPresheaf.obj U) :=
  show IsLocalization (G.obj U) (Localization (G.obj U)) from inferInstance

/-- The map into the localization presheaf. -/
@[simps app]
def SubmonoidPresheaf.toLocalizationPresheaf : F ⟶ G.localizationPresheaf where
  app U := CommRingCat.ofHom <| algebraMap (F.obj U) (Localization <| G.obj U)
  naturality {_ _} i := (IsLocalization.map_comp (G.map i)).symm
#align Top.presheaf.submonoid_presheaf.to_localization_presheaf TopCat.Presheaf.SubmonoidPresheaf.toLocalizationPresheaf

instance epi_toLocalizationPresheaf : Epi G.toLocalizationPresheaf :=
  @NatTrans.epi_of_epi_app _ _ _ _ _ _ G.toLocalizationPresheaf fun U => Localization.epi' (G.obj U)

variable (F)

/-- Given a submonoid at each of the stalks, we may define a submonoid presheaf consisting of
sections whose restriction onto each stalk falls in the given submonoid. -/
@[simps]
noncomputable def submonoidPresheafOfStalk (S : ∀ x : X, Submonoid (F.stalk x)) :
    F.SubmonoidPresheaf where
  obj U := ⨅ x : U.unop, Submonoid.comap (F.germ x) (S x)
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
#align Top.presheaf.to_total_quotient_presheaf TopCat.Presheaf.toTotalQuotientPresheaf

-- Porting note: deriving `Epi` failed
instance : Epi (toTotalQuotientPresheaf F) := epi_toLocalizationPresheaf _

instance (F : X.Sheaf CommRingCat.{w}) : Mono F.presheaf.toTotalQuotientPresheaf := by
  -- Porting note: was an `apply (config := { instances := false })`
  -- See https://github.com/leanprover/lean4/issues/2273
  suffices ∀ (U : (Opens ↑X)ᵒᵖ), Mono (F.presheaf.toTotalQuotientPresheaf.app U) from
    NatTrans.mono_of_mono_app _
  intro U
  apply ConcreteCategory.mono_of_injective
  dsimp [toTotalQuotientPresheaf, CommRingCat.ofHom]
  -- Porting note: this is a hack to make the `refine` below works
  set m := _
  change Function.Injective (algebraMap _ (Localization m))
  change Function.Injective (algebraMap (F.presheaf.obj U) _)
  haveI : IsLocalization _ (Localization m) := Localization.isLocalization
  -- Porting note: `M` and `S` need to be specified manually, so used a hack to save some typing
  refine IsLocalization.injective (M := m) (S := Localization m) ?_
  intro s hs t e
  apply section_ext F (unop U)
  intro x
  rw [map_zero]
  apply Submonoid.mem_iInf.mp hs x
  -- Porting note: added `dsimp` to make `rw [← map_mul]` work
  dsimp
  rw [← map_mul, e, map_zero]

end Presheaf

end TopCat
