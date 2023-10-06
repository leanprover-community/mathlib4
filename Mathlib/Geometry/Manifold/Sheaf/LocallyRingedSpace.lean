/-
Copyright © 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Geometry.Manifold.Sheaf.Smooth
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

/-! # Smooth manifolds as locally ringed spaces

This file equips a smooth manifold-with-corners with the structure of a locally ringed space.

## Main results

* `smoothSheafCommRing.isUnit_stalk_iff`: The units of the stalk at `x` of the sheaf of smooth
  functions from a smooth manifold `M` to its scalar field `𝕜`, considered as a sheaf of commutative
  rings, are the functions whose values at `x` are nonzero.

## Main definitions

* `SmoothManifoldWithCorners.locallyRingedSpace`: A smooth manifold-with-corners can be considered
  as a locally ringed space.

## TODO

Characterize morphisms-of-locally-ringed-spaces (`AlgebraicGeometry.LocallyRingedSpace.Hom`) between
smooth manifolds.

-/

noncomputable section
universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  (M : Type u) [TopologicalSpace M] [ChartedSpace HM M]

open AlgebraicGeometry Manifold TopologicalSpace Topology Opposite

/-- The units of the stalk at `x` of the sheaf of smooth functions from `M` to `𝕜`, considered as a
sheaf of commutative rings, are the functions whose values at `x` are nonzero. -/
theorem smoothSheafCommRing.isUnit_stalk_iff {x : M}
    (f : (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.stalk x) :
    IsUnit f ↔ f ∉ RingHom.ker (smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x) := by
  constructor
  · rintro ⟨⟨f, g, hf, hg⟩, rfl⟩ (h' : smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x f = 0)
    simpa [h'] using congr_arg (smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x) hf
  · let S := (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf
    -- Suppose that `f`, in the stalk at `x`, is nonzero at `x`
    rintro (hf : _ ≠ 0)
    -- Represent `f` as the germ of some function (also called `f`) on an open neighbourhood `U` of
    -- `x`, which is nonzero at `x`
    obtain ⟨U : Opens M, hxU, f : C^∞⟮IM, U; 𝓘(𝕜), 𝕜⟯, rfl⟩ := S.germ_exist x f
    have hf' : f ⟨x, hxU⟩ ≠ 0 := by
      convert hf
      exact (smoothSheafCommRing.eval_germ U ⟨x, hxU⟩ f).symm
    -- In fact, by continuity, `f` is nonzero on a neighbourhood `V` of `x`
    have H :  ∀ᶠ (z : U) in 𝓝 ⟨x, hxU⟩, f z ≠ 0 := f.2.continuous.continuousAt.eventually_ne hf'
    rw [eventually_nhds_iff] at H
    obtain ⟨V₀, hV₀f, hV₀, hxV₀⟩ := H
    let V : Opens M := ⟨Subtype.val '' V₀, U.2.isOpenMap_subtype_val V₀ hV₀⟩
    have hUV : V ≤ U := Subtype.coe_image_subset (U : Set M) V₀
    have hV : V₀ = Set.range (Set.inclusion hUV) := by
      convert (Set.range_inclusion hUV).symm
      ext y
      show _ ↔ y ∈ Subtype.val ⁻¹' (Subtype.val '' V₀)
      rw [Set.preimage_image_eq _ Subtype.coe_injective]
    clear_value V
    subst hV
    have hxV : x ∈ (V : Set M) := by
      obtain ⟨x₀, hxx₀⟩ := hxV₀
      convert x₀.2
      exact congr_arg Subtype.val hxx₀.symm
    have hVf : ∀ y : V, f (Set.inclusion hUV y) ≠ 0 :=
      fun y ↦ hV₀f (Set.inclusion hUV y) (Set.mem_range_self y)
    -- Let `g` be the pointwise inverse of `f` on `V`, which is smooth since `f` is nonzero there
    let g : C^∞⟮IM, V; 𝓘(𝕜), 𝕜⟯ := ⟨(f ∘ Set.inclusion hUV)⁻¹, ?_⟩
    -- The germ of `g` is inverse to the germ of `f`, so `f` is a unit
    · refine ⟨⟨S.germ ⟨x, hxV⟩ (SmoothMap.restrictRingHom IM 𝓘(𝕜) 𝕜 hUV f), S.germ ⟨x, hxV⟩ g,
        ?_, ?_⟩, S.germ_res_apply hUV.hom ⟨x, hxV⟩ f⟩
      · rw [← map_mul]
        convert map_one _
        apply Subtype.ext
        ext y
        apply mul_inv_cancel
        exact hVf y
      · rw [← map_mul]
        convert map_one _
        apply Subtype.ext
        ext y
        apply inv_mul_cancel
        exact hVf y
    · intro y
      exact ((contDiffAt_inv _ (hVf y)).contMDiffAt).comp y
        (f.smooth.comp (smooth_inclusion hUV)).smoothAt

/-- The non-units of the stalk at `x` of the sheaf of smooth functions from `M` to `𝕜`, considered
as a sheaf of commutative rings, are the functions whose values at `x` are zero. -/
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

variable {IM M} in
/-- Let `W` be an open set in a complex manifold `M`, and let `F` and `G` be holomorphic functions
on `W` with `F * G ≡ 0` on `W`. Let `x` be a point in `W`.  Then the germ of either `F` or `G` at
`x` must be zero. -/
theorem germ_zero_or_germ_zero_of_mul_eq_zero {W : Opens M}
    {F G : (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.obj (op W)}
    (H : F * G = 0) (x : W) :
    (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.germ x F = 0
    ∨ (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.germ x G = 0 :=
  sorry

/-- The stalk at `x` of the sheaf of holomorphic functions from `M` to `ℂ`, considered as a sheaf of
commutative rings, has no zero divisors.  This is the main step in showing that it is an integral
domain. -/
instance (x : M) : NoZeroDivisors ((smoothPresheafCommRing IM 𝓘(𝕜, 𝕜) M 𝕜).stalk (x:M)) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    let S := (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf
    intro f g hfg
    obtain ⟨U : Opens M, hxU, f : C^∞⟮IM, U; 𝓘(𝕜), 𝕜⟯, rfl⟩ := S.germ_exist x f
    obtain ⟨V : Opens M, hxV, g : C^∞⟮IM, V; 𝓘(𝕜), 𝕜⟯, rfl⟩ := S.germ_exist x g
    let X : ↑(U ⊓ V) := ⟨x, ⟨hxU, hxV⟩⟩
    have hU' : U ⊓ V ≤ U := inf_le_left
    let F : C^∞⟮IM, ↑(U ⊓ V); 𝓘(𝕜), 𝕜⟯ := S.map hU'.hom.op f
    have hF : S.germ X F = _ := S.germ_res_apply hU'.hom X f
    have hV' : U ⊓ V ≤ V := inf_le_right
    let G : C^∞⟮IM, ↑(U ⊓ V); 𝓘(𝕜), 𝕜⟯ := S.map hV'.hom.op g
    have hG : S.germ X G = _ := S.germ_res_apply hV'.hom X g
    rw [← hF, ← hG] at hfg ⊢
    have hFG : S.germ X (F * G) = S.germ X 0 := by rwa [map_mul, map_zero]
    obtain ⟨W, hxW, i, _, hFGW⟩ := S.germ_eq _ _ _ _ _ hFG
    have hFGW' : S.map i.op F * S.map i.op G = 0 := by rwa [map_mul, map_zero] at hFGW
    have hFGW'' := germ_zero_or_germ_zero_of_mul_eq_zero hFGW' ⟨x, hxW⟩
    rwa [S.germ_res_apply i, S.germ_res_apply i] at hFGW''

instance (x : M) : Nontrivial ((smoothPresheafCommRing IM 𝓘(𝕜, 𝕜) M 𝕜).stalk (x:M)) :=
  smoothSheafCommRing.stalk_nontrivial ..

/-- The stalk at `x` of the sheaf of holomorphic functions from `M` to `ℂ`, considered as a sheaf of
commutative rings, is an integral domain. -/
instance (x : M) : IsDomain ((smoothPresheafCommRing IM 𝓘(𝕜, 𝕜) M 𝕜).stalk (x:M)) :=
  NoZeroDivisors.to_isDomain ..
