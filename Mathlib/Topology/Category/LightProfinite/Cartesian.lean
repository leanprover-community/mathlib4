import Mathlib.Topology.Category.CompHausLike.Cartesian
import Mathlib.Topology.Category.LightProfinite.Basic

import Mathlib.Condensed.Light.CartesianClosed
import Mathlib.Condensed.Light.Functors
import Mathlib.Condensed.Light.TopCatAdjunction
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Spectral.Prespectral

universe u

open CategoryTheory Limits CompHausLike

namespace LightProfinite

noncomputable instance : CartesianMonoidalCategory LightProfinite.{u} :=
  cartesianMonoidalCategory

instance {J : Type} [SmallCategory J] [CountableCategory J] : PreservesLimitsOfShape J
    lightProfiniteToLightCondSet.{u} := by
  have : Functor.IsRightAdjoint topCatToLightCondSet.{u} :=
    LightCondSet.topCatAdjunction.isRightAdjoint
  haveI : PreservesLimitsOfShape J LightProfinite.toTopCat.{u} :=
    inferInstanceAs (PreservesLimitsOfShape J (lightToProfinite ⋙ Profinite.toTopCat))
  let i : lightProfiniteToLightCondSet.{u} ≅
      LightProfinite.toTopCat.{u} ⋙ topCatToLightCondSet.{u} := by
    refine NatIso.ofComponents ?_ ?_
    · intro X
      refine (sheafToPresheaf _ _).preimageIso (NatIso.ofComponents ?_ ?_)
      intro S
      · exact {
          hom f := ⟨f.1, by continuity⟩
          inv f := TopCat.ofHom ⟨f.1, by continuity⟩
          hom_inv_id := rfl
          inv_hom_id := rfl }
      · cat_disch
    · intro X Y f
      apply (sheafToPresheaf _ _).map_injective
      ext S
      simp [-sheafToPresheaf_map, lightProfiniteToLightCondSet, topCatToLightCondSet]
      rfl
  exact preservesLimitsOfShape_of_natIso i.symm

instance : PreservesFiniteLimits lightProfiniteToLightCondSet.{u} where
  preservesFiniteLimits _ := inferInstance

noncomputable instance : lightProfiniteToLightCondSet.Monoidal := by
  have : Nonempty lightProfiniteToLightCondSet.Monoidal := by
    rw [Functor.Monoidal.nonempty_monoidal_iff_preservesFiniteProducts]
    infer_instance
  exact this.some

end LightProfinite
