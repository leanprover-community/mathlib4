/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Locally directed covers

A locally directed `P`-cover of a scheme `X` is a cover `𝒰` with an ordering
on the indices and compatible transition maps `𝒰ᵢ ⟶ 𝒰ⱼ` for `i ≤ j` such that
every `x : 𝒰ᵢ ×[X] 𝒰ⱼ` comes from some `𝒰ₖ` for a `k ≤ i` and `k ≤ j`.

Gluing along directed covers is easier, because the intersections `𝒰ᵢ ×[X] 𝒰ⱼ` can
be covered by a subcover of `𝒰`.

Many natural covers are naturally directed, most importantly the cover of all affine
opens of a scheme.
-/

universe u

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {P : MorphismProperty Scheme.{u}} {X : Scheme.{u}}

/-- A directed `P`-cover of a scheme `X` is a cover `𝒰` with an ordering
on the indices and compatible transition maps `𝒰ᵢ ⟶ 𝒰ⱼ` for `i ≤ j` such that
every `x : 𝒰ᵢ ×[X] 𝒰ⱼ` comes from some `𝒰ₖ` for a `k ≤ i` and `k ≤ j`. -/
class Cover.LocallyDirected (𝒰 : X.Cover P) extends LE 𝒰.J where
  /-- The transition map `𝒰ᵢ ⟶ 𝒰ⱼ` for `i ≤ j`. -/
  trans {i j : 𝒰.J} (hij : i ≤ j) : 𝒰.obj i ⟶ 𝒰.obj j
  w {i j : 𝒰.J} (hij : i ≤ j) : trans hij ≫ 𝒰.map j = 𝒰.map i := by aesop_cat
  directed {i j : 𝒰.J} (x : (pullback (𝒰.map i) (𝒰.map j)).carrier) :
    ∃ (k : 𝒰.J) (hki : k ≤ i) (hkj : k ≤ j) (y : 𝒰.obj k),
      (pullback.lift (trans hki) (trans hkj) (by simp [w])).base y = x
  property_trans {i j : 𝒰.J} (hij : i ≤ j) : P (trans hij) := by infer_instance

variable (𝒰 : X.Cover P) [𝒰.LocallyDirected]

/-- The transition maps of a directed cover. -/
def Cover.trans {i j : 𝒰.J} (hij : i ≤ j) : 𝒰.obj i ⟶ 𝒰.obj j := LocallyDirected.trans hij

@[simp]
lemma Cover.trans_map {i j : 𝒰.J} (hij : i ≤ j) : 𝒰.trans hij ≫ 𝒰.map j = 𝒰.map i :=
  LocallyDirected.w hij

lemma Cover.exists_lift_trans_eq {i j : 𝒰.J} (x : (pullback (𝒰.map i) (𝒰.map j)).carrier) :
    ∃ (k : 𝒰.J) (hki : k ≤ i) (hkj : k ≤ j) (y : 𝒰.obj k),
      (pullback.lift (𝒰.trans hki) (𝒰.trans hkj) (by simp)).base y = x :=
  LocallyDirected.directed x

lemma Cover.property_trans {i j : 𝒰.J} (hij : i ≤ j) : P (𝒰.trans hij) :=
  LocallyDirected.property_trans hij

/-- If `𝒰` is a directed cover of `X`, this is the cover of `𝒰ᵢ ×[X] 𝒰ⱼ` by `{𝒰ₖ}` where
`k ≤ i` and `k ≤ j`. -/
@[simps map]
def Cover.intersectionOfLocallyDirected [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    (i j : 𝒰.J) : (pullback (𝒰.map i) (𝒰.map j)).Cover P where
  J := { k : 𝒰.J | k ≤ i ∧ k ≤ j }
  obj k := 𝒰.obj k
  map k := pullback.lift (𝒰.trans k.2.1) (𝒰.trans k.2.2) (by simp)
  f x := ⟨(𝒰.exists_lift_trans_eq x).choose, (𝒰.exists_lift_trans_eq x).choose_spec.choose,
    (𝒰.exists_lift_trans_eq x).choose_spec.choose_spec.choose⟩
  covers x := (𝒰.exists_lift_trans_eq x).choose_spec.choose_spec.choose_spec
  map_prop k := by
    apply P.of_postcomp (W' := P) _ (pullback.fst _ _) (P.pullback_fst _ _ (𝒰.map_prop _))
    rw [pullback.lift_fst]
    exact 𝒰.property_trans _

/-- If `𝒰` is a directed open cover of `X`, to glue morphisms `{gᵢ : 𝒰ᵢ ⟶ Y}` it suffices
to check compatibility with the transition maps. -/
def OpenCover.glueMorphismsOfLocallyDirected (𝒰 : X.OpenCover) [𝒰.LocallyDirected] {Y : Scheme.{u}}
    (g : ∀ i, 𝒰.obj i ⟶ Y) (h : ∀ {i j : 𝒰.J} (hij : i ≤ j), 𝒰.trans hij ≫ g j = g i) :
    X ⟶ Y :=
  𝒰.glueMorphisms g <| fun i j ↦ by
    apply (𝒰.intersectionOfLocallyDirected i j).hom_ext
    intro k
    simp [h]

@[reassoc (attr := simp)]
lemma OpenCover.map_glueMorphismsOfLocallyDirected (𝒰 : X.OpenCover) [𝒰.LocallyDirected]
    {Y : Scheme.{u}} (g : ∀ i, 𝒰.obj i ⟶ Y)
    (h : ∀ {i j : 𝒰.J} (hij : i ≤ j), 𝒰.trans hij ≫ g j = g i) (i : 𝒰.J) :
    𝒰.map i ≫ 𝒰.glueMorphismsOfLocallyDirected g h = g i := by
  simp [glueMorphismsOfLocallyDirected]

/-- If `𝒰` is a directed open cover of `X`, to glue morphisms `{gᵢ : 𝒰ᵢ ⟶ Y}` over `S` it suffices
to check compatibility with the transition maps. -/
def OpenCover.glueMorphismsOverOfLocallyDirected {S : Scheme.{u}} {X : Over S}
    (𝒰 : X.left.OpenCover) [𝒰.LocallyDirected] {Y : Over S} (g : ∀ i, 𝒰.obj i ⟶ Y.left)
    (h : ∀ {i j : 𝒰.J} (hij : i ≤ j), 𝒰.trans hij ≫ g j = g i)
    (w : ∀ i, g i ≫ Y.hom = 𝒰.map i ≫ X.hom) :
    X ⟶ Y :=
  Over.homMk (𝒰.glueMorphismsOfLocallyDirected g h) <| by
    apply 𝒰.hom_ext
    intro i
    simp [w]

@[reassoc (attr := simp)]
lemma OpenCover.map_glueMorphismsOverOfLocallyDirected_left {S : Scheme.{u}} {X : Over S}
    (𝒰 : X.left.OpenCover) [𝒰.LocallyDirected] {Y : Over S} (g : ∀ i, 𝒰.obj i ⟶ Y.left)
    (h : ∀ {i j : 𝒰.J} (hij : i ≤ j), 𝒰.trans hij ≫ g j = g i)
    (w : ∀ i, g i ≫ Y.hom = 𝒰.map i ≫ X.hom) (i : 𝒰.J) :
    𝒰.map i ≫ (𝒰.glueMorphismsOverOfLocallyDirected g h w).left = g i := by
  simp [glueMorphismsOverOfLocallyDirected]

instance Cover.locallyDirectedPullbackCover [P.IsStableUnderBaseChange] (𝒰 : X.Cover P)
    [𝒰.LocallyDirected] {Y : Scheme.{u}} (f : Y ⟶ X) :
    (𝒰.pullbackCover f).LocallyDirected where
  le (x : 𝒰.J) (y : 𝒰.J) := x ≤ y
  trans {i j} hij := pullback.map f (𝒰.map i) f (𝒰.map j) (𝟙 _) (𝒰.trans hij) (𝟙 _)
    (by simp) (by simp)
  directed {i j} x := by
    dsimp at i j x ⊢
    let iso : pullback (pullback.fst f (𝒰.map i)) (pullback.fst f (𝒰.map j)) ≅
        pullback f (pullback.fst (𝒰.map i) (𝒰.map j) ≫ 𝒰.map i) :=
      pullbackRightPullbackFstIso _ _ _ ≪≫ pullback.congrHom pullback.condition rfl ≪≫
        pullbackAssoc ..
    have (k : 𝒰.J) (hki : k ≤ i) (hkj : k ≤ j) :
        (pullback.lift
          (pullback.map f (𝒰.map k) f (𝒰.map i) (𝟙 Y) (𝒰.trans hki) (𝟙 X) (by simp) (by simp))
          (pullback.map f (𝒰.map k) f (𝒰.map j) (𝟙 Y) (𝒰.trans hkj) (𝟙 X) (by simp) (by simp))
            (by simp)) =
          pullback.map _ _ _ _ (𝟙 Y) (pullback.lift (𝒰.trans hki) (𝒰.trans hkj) (by simp)) (𝟙 X)
            (by simp) (by simp) ≫ iso.inv := by
      apply pullback.hom_ext <;> apply pullback.hom_ext <;> simp [iso]
    obtain ⟨k, hki, hkj, yk, hyk⟩ := 𝒰.exists_lift_trans_eq ((iso.hom ≫ pullback.snd _ _).base x)
    refine ⟨k, hki, hkj, show x ∈ Set.range _ from ?_⟩
    rw [this, Scheme.comp_base, TopCat.coe_comp, Set.range_comp, Pullback.range_map]
    use iso.hom.base x
    simp only [id.base, TopCat.hom_id, ContinuousMap.coe_id, Set.range_id, Set.preimage_univ,
      Set.univ_inter, Set.mem_preimage, Set.mem_range, iso_hom_base_inv_base_apply, and_true]
    exact ⟨yk, hyk⟩
  property_trans {i j} hij := by
    let iso : pullback f (𝒰.map i) ≅ pullback (pullback.snd f (𝒰.map j)) (𝒰.trans hij) :=
      pullback.congrHom rfl (by simp) ≪≫ (pullbackLeftPullbackSndIso _ _ _).symm
    rw [← P.cancel_left_of_respectsIso iso.inv]
    simp only [pullbackCover_obj, Iso.trans_inv, Iso.symm_inv, pullback.congrHom_inv,
      Category.assoc, iso]
    convert P.pullback_fst _ _ (𝒰.property_trans hij)
    apply pullback.hom_ext <;> simp [pullback.condition]

/-- If `𝒰` is an open cover such that the images of the components form a basis of the topology
of `X`, `𝒰` is directed by the ordering of subset inclusion of the images. -/
def Cover.LocallyDirected.ofIsBasisOpensRange {𝒰 : X.OpenCover} [LE 𝒰.J]
    (hle : ∀ {i j : 𝒰.J}, i ≤ j ↔ (𝒰.map i).opensRange ≤ (𝒰.map j).opensRange)
    (H : TopologicalSpace.Opens.IsBasis (Set.range <| fun i ↦ (𝒰.map i).opensRange)) :
    𝒰.LocallyDirected where
  trans {i j} hij := IsOpenImmersion.lift (𝒰.map j) (𝒰.map i) (hle.mp hij)
  directed {i j} x := by
    have : (pullback.fst (𝒰.map i) (𝒰.map j) ≫ 𝒰.map i).base x ∈
      (pullback.fst (𝒰.map i) (𝒰.map j) ≫ 𝒰.map i).opensRange := ⟨x, rfl⟩
    obtain ⟨k, ⟨k, rfl⟩, ⟨y, hy⟩, h⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp H this
    refine ⟨k, hle.mpr <| le_trans h ?_, hle.mpr <| le_trans h ?_, y, ?_⟩
    · rw [Scheme.Hom.opensRange_comp]
      exact Set.image_subset_range _ _
    · simp_rw [pullback.condition, Scheme.Hom.opensRange_comp]
      exact Set.image_subset_range _ _
    · apply (pullback.fst (𝒰.map i) (𝒰.map j) ≫ 𝒰.map i).isOpenEmbedding.injective
      rw [← Scheme.comp_base_apply, pullback.lift_fst_assoc, IsOpenImmersion.lift_fac, hy]

section

variable {𝒰 : X.OpenCover} [LE 𝒰.J]
  (hle : ∀ {i j : 𝒰.J}, i ≤ j ↔ (𝒰.map i).opensRange ≤ (𝒰.map j).opensRange)
  (H : TopologicalSpace.Opens.IsBasis (Set.range <| fun i ↦ (𝒰.map i).opensRange))

include hle in
lemma Cover.LocallyDirected.ofIsBasisOpensRange_le_iff (i j : 𝒰.J) :
    letI := Cover.LocallyDirected.ofIsBasisOpensRange hle H
    i ≤ j ↔ (𝒰.map i).opensRange ≤ (𝒰.map j).opensRange := hle

lemma Cover.LocallyDirected.ofIsBasisOpensRange_trans {i j : 𝒰.J} :
    letI := Cover.LocallyDirected.ofIsBasisOpensRange hle H
    (hij : i ≤ j) → 𝒰.trans hij = IsOpenImmersion.lift (𝒰.map j) (𝒰.map i) (hle.mp hij) :=
  fun _ ↦ rfl

end

variable (X) in
open TopologicalSpace.Opens in
/-- The directed affine open cover of `X` given by all affine opens. -/
@[simps J obj map]
def directedAffineCover : X.OpenCover where
  J := X.affineOpens
  obj U := U
  map U := U.1.ι
  f x := ⟨(isBasis_iff_nbhd.mp (isBasis_affine_open X) (mem_top x)).choose,
    (isBasis_iff_nbhd.mp (isBasis_affine_open X) (mem_top x)).choose_spec.1⟩
  covers x := by
    simpa using (isBasis_iff_nbhd.mp (isBasis_affine_open X) (mem_top x)).choose_spec.2.1

instance : LE X.directedAffineCover.J := inferInstanceAs <| LE X.affineOpens

instance : Scheme.Cover.LocallyDirected X.directedAffineCover :=
  .ofIsBasisOpensRange (by simp) <| by
    convert isBasis_affine_open X
    simp

@[simp]
lemma directedAffineCover_trans {U V : X.affineOpens} (hUV : U ≤ V) :
    Cover.trans X.directedAffineCover hUV = X.homOfLE hUV := rfl

end AlgebraicGeometry.Scheme
