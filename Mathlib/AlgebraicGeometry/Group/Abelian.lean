/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_

/-!
# Abelian varieties

## Main results
- `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`:
  A proper geometrically integral group scheme over a field is commutative.

-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}

open MonoidalCategory CartesianMonoidalCategory MonObj

instance (G : Over (Spec (.of K))) [GrpObj G] : IsClosedImmersion η[G].left :=
  isClosedImmersion_of_comp_eq_id (Y := Spec (.of K)) G.hom η[G].left (by simp)

set_option backward.isDefEq.respectTransparency false in
theorem isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed [IsAlgClosed K]
    (G : Over (Spec (.of K))) [IsProper G.hom] [IsIntegral (G ⊗ G).left] [GrpObj G] :
    IsCommMonObj G := by
  let S := Spec (.of K)
  let point : S := IsLocalRing.closedPoint K
  have hpoint : IsClosed {point} := isClosed_discrete _
  have : Nonempty G.left := ⟨η[G].left point⟩
  have : IsProper (G ⊗ G).hom := by dsimp; infer_instance
  have : JacobsonSpace (G ⊗ G).left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) (G ⊗ G).hom
  have : Surjective G.hom := ⟨Function.surjective_to_subsingleton (α := G.left) (β := Spec _) _⟩
  have : IsProper (fst G G).left := by dsimp; infer_instance
  have : Surjective (fst G G).left := by dsimp; infer_instance
  have : IsProper ((GrpObj.commutator G).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : IsClosedImmersion ((lift η[G] η[G]).left ≫ (fst G G).left) := by
    simpa using inferInstanceAs% (IsClosedImmersion η[G].left)
  have : IsClosedImmersion (lift η[G] η[G]).left := .of_comp _ (g := (fst G G).left)
  let γ : G ⊗ G ⟶ G ⊗ G := lift (fst _ _) (GrpObj.commutator _)
  have : IsProper (γ.left ≫ (fst G G).left) := by simpa [γ]
  have : IsProper γ.left := .of_comp _ (fst G G).left
  -- It suffices to check that `γ : (x, y) ↦ x * y * x⁻¹ * y⁻¹` is constantly `1`.
  rw [isCommMonObj_iff_commutator_eq_toUnit_η]
  ext1
  have H : γ.left '' ((fst G G).left ⁻¹' {η[G].left point}) ⊆ {(lift η[G] η[G]).left point} := by
    rw [Set.image_subset_iff, ← Set.diff_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro H
    obtain ⟨c₀, ⟨hc₁, hc₂⟩, hc₃⟩ := nonempty_inter_closedPoints H <| by
      rw [Set.diff_eq_compl_inter, ← Set.image_singleton, ← Set.image_singleton];
      refine (IsOpen.isLocallyClosed ?_).inter (IsClosed.isLocallyClosed ?_)
      · exact (((lift η[G] η[G]).left.isClosedMap _ hpoint).preimage γ.left.continuous).isOpen_compl
      · exact (η[G].left.isClosedMap _ hpoint).preimage (fst G G).left.continuous
    obtain ⟨⟨c, hc⟩, e⟩ := (pointEquivClosedPoint (G ⊗ G).hom).surjective ⟨c₀, hc₃⟩
    obtain rfl : c point = c₀ := congr(($e).1)
    let fc : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ G := lift (𝟙 _) (Over.homMk c hc ≫ snd G G)
    have : c ≫ pullback.fst G.hom G.hom = η[G].left :=
      ext_of_apply_closedPoint_eq G.hom (by simpa) (by simp) (by simpa)
    have H₁ : c = fc.left ≫ (η[G] ▷ G).left := by dsimp; ext <;> simp [fc, S, this]
    have H₂ : fc ≫ η ▷ G ≫ γ = lift η η := by ext1 <;> simp [fc, γ, S]
    exact hc₂ <| by simp [H₁, H₂, ← Scheme.Hom.comp_apply, Category.assoc, ← Over.comp_left]
  -- Since the image of `y ↦ γ(e, y)` is finite, by Zariski Main, there exists an open
  -- `1 ∈ U ⊆ G` such that `γ ∣_ U` factors through a finite scheme over `U`.
  obtain ⟨U, hηU, H⟩ := exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
    γ.left (fst G G).left (η[G].left point) (by
      dsimp [-Scheme.Hom.comp_base, γ]
      simp only [pullback.lift_fst]
      exact (Set.finite_singleton _).subset H)
  have H (x : U) : ((pullback.fst G.hom G.hom) ⁻¹' {x.1} ∩ Set.range ⇑γ.left).Finite := by
    refine ((((γ.left.imageι ≫ (fst G G).left) ∣_ U).finite_preimage_singleton x).image
      (Scheme.Opens.ι _ ≫ γ.left.imageι)).subset ?_
    have : U.ι ⁻¹' {x.1} = {x} := by ext; simp
    rw [← this, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      morphismRestrict_ι, ← Category.assoc, Scheme.Hom.comp_base (_ ≫ _) (fst G G).left,
      TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    dsimp
    rw [Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι,
      Scheme.Hom.support_ker, ← Set.inter_assoc, ← Set.preimage_inter,
      Set.singleton_inter_of_mem x.2, IsClosed.closure_eq
      (by exact γ.left.isClosedMap.isClosed_range)]
  -- It suffices to check set-theoretic equality on closed points of `U ×[k] G`.
  refine ext_of_apply_eq G.hom _
    ((fst G G).left ⁻¹ᵁ U).isOpen.isLocallyClosed
    (((fst G G).left ⁻¹ᵁ U).isOpen.dense ?_) ?_ ?_
  · exact .preimage ⟨_, hηU⟩ (fst G G).left.surjective
  · intro y hyU hy
    have hx : IsClosed {(fst G G).left y} := by simpa using (fst G G).left.isClosedMap _ hy
    let x : 𝟙_ _ ⟶ G := Over.homMk (pointOfClosedPoint G.hom _ hx) (by simp)
    let xe : (G ⊗ G).left := (fst G G ≫ (ρ_ _).inv ≫ G ◁ η[G]).left y
    have : γ.left y = xe := by
      -- By the choice of `U`, the set `γ({y} ×[k] G)` is finite and hence, by irreducibility,
      -- a singleton.
      refine subsingleton_image_closure_of_finite_of_isPreirreducible
        (hx.preimage (fst G G).left.continuous).isLocallyClosed ?_ γ.left.continuous
        γ.left.isClosedMap ((H ⟨_, hyU⟩).subset (Set.image_subset_iff.mpr fun _ ↦ by
          simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base, γ])) ?_ ?_
      · let α : G ⊗ G ⟶ G ⊗ G := toUnit _ ≫ x ⊗ₘ 𝟙 _
        convert ((IrreducibleSpace.isIrreducible_univ _).image α.left
          α.left.continuous.continuousOn).isPreirreducible
        rw [Over.tensorHom_left]
        simp [Set.range_comp, Scheme.Pullback.range_map, x]
      · exact ⟨y, subset_closure (by simp), rfl⟩
      · refine ⟨xe, subset_closure ?_, ?_⟩
        · simp [xe, ← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base]
        · simp only [xe, γ, ← Scheme.Hom.comp_apply, ← Over.comp_left]
          congr 6; ext <;> simp
    convert congr((snd G G).left $this) using 1
    · simp [γ, ← Scheme.Hom.comp_apply]
    · simp [xe, ← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base]
  · simp

set_option backward.isDefEq.respectTransparency false in
/-- A proper geometrically integral group scheme over a field is commutative. -/
@[stacks 0BFD]
theorem isCommMonObj_of_isProper_of_geometricallyIntegral
    (G : Over (Spec (.of K))) [IsProper G.hom] [GeometricallyIntegral G.hom] [GrpObj G] :
    IsCommMonObj G := by
  let f := Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K))
  let G' := (Over.pullback f).obj G
  have : IsProper G'.hom := by dsimp [G']; infer_instance
  have : IsIntegral (G' ⊗ G').left := by dsimp [G']; infer_instance
  let : GrpObj G' := Functor.grpObjObj
  have := isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed G'
  rw [isCommMonObj_iff_commutator_eq_toUnit_η] at this ⊢
  apply (Over.pullback f).map_injective
  rw [← cancel_epi (Functor.Monoidal.μIso (Over.pullback f) G G).hom]
  dsimp [GrpObj.commutator] at this ⊢
  simpa only [Functor.map_mul, one_eq_one, comp_one, Functor.map_one, Functor.map_inv',
    comp_mul, GrpObj.comp_inv, Functor.Monoidal.μ_fst, Functor.Monoidal.μ_snd]

end AlgebraicGeometry
