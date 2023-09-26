/-
Copyright © 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Geometry.Manifold.Sheaf.Smooth
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

/-! # Smooth manifolds as locally ringed spaces -/

noncomputable section
universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  (M : Type u) [TopologicalSpace M] [ChartedSpace HM M]

open AlgebraicGeometry Manifold Opposite TopologicalSpace

theorem smoothSheafCommRing.isUnit_stalk_iff {x : M}
    (f : (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.stalk x) :
    IsUnit f ↔ f ∉ RingHom.ker (smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x) := by
  let E := smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x
  constructor
  · rintro ⟨⟨f, g, hf, hg⟩, rfl⟩ (h' : E f = 0)
    simpa [h'] using congr_arg E hf
  · rintro (hf : _ ≠ 0)
    obtain ⟨U, hxU, f, rfl⟩ := (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.germ_exist x f
    let V : OpenNhds x := ⟨U, hxU⟩
    sorry
    -- have := congr_arg (fun e ↦ e f) (smoothSheafCommRing.ι_evalHom IM 𝓘(𝕜) M 𝕜 x (op V))
    -- simp at this
    -- change smoothSheafCommRing.evalAt IM 𝓘(𝕜) M 𝕜 x V f ≠ 0 at hf
    -- let s : SmoothMap IM 𝓘(𝕜) M 𝕜 := sorry

theorem smoothSheafCommRing.nonunits_stalk {x : M} :
    nonunits ((smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.stalk x)
    = RingHom.ker (smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x) := by
  ext1 f
  rw [mem_nonunits_iff, not_iff_comm, Iff.comm]
  apply smoothSheafCommRing.isUnit_stalk_iff

/-- A smooth manifold-with-corners can be considered as a locally ringed space. -/
def SmoothManifoldWithCorners.locallyRingedSpace : LocallyRingedSpace where
  carrier := TopCat.of M
  presheaf := smoothPresheafCommRing IM 𝓘(𝕜) M 𝕜
  IsSheaf := (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).cond
  localRing := by
    intro (x : M)
    show LocalRing ((smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.stalk x)
    apply LocalRing.of_nonunits_add
    rw [smoothSheafCommRing.nonunits_stalk]
    intro f g
    exact Ideal.add_mem _
