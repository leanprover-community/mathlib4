/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.LocallyDirected
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Locally directed covers

A locally directed `P`-cover of a scheme `X` is a cover `𝒰` with an ordering
on the indices and compatible transition maps `𝒰ᵢ ⟶ 𝒰ⱼ` for `i ≤ j` such that
every `x : 𝒰ᵢ ×[X] 𝒰ⱼ` comes from some `𝒰ₖ` for a `k ≤ i` and `k ≤ j`.

Gluing along directed covers is easier, because the intersections `𝒰ᵢ ×[X] 𝒰ⱼ` can
be covered by a subcover of `𝒰`. In particular, if `𝒰` is a Zariski cover,
`X` naturally is the colimit of the `𝒰ᵢ`.

Many natural covers are naturally directed, most importantly the cover of all affine
opens of a scheme.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {P : MorphismProperty Scheme.{u}} {X : Scheme.{u}}

namespace Cover

/-- A directed `P`-cover of a scheme `X` is a cover `𝒰` with an ordering
on the indices and compatible transition maps `𝒰ᵢ ⟶ 𝒰ⱼ` for `i ≤ j` such that
every `x : 𝒰ᵢ ×[X] 𝒰ⱼ` comes from some `𝒰ₖ` for a `k ≤ i` and `k ≤ j`. -/
class LocallyDirected (𝒰 : X.Cover (precoverage P)) [Category* 𝒰.I₀] where
  /-- The transition map `𝒰ᵢ ⟶ 𝒰ⱼ` for `i ≤ j`. -/
  trans {i j : 𝒰.I₀} (hij : i ⟶ j) : 𝒰.X i ⟶ 𝒰.X j
  trans_id (i : 𝒰.I₀) : trans (𝟙 i) = 𝟙 (𝒰.X i) := by cat_disch
  trans_comp {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k) :
    trans (hij ≫ hjk) = trans hij ≫ trans hjk := by cat_disch
  w {i j : 𝒰.I₀} (hij : i ⟶ j) : trans hij ≫ 𝒰.f j = 𝒰.f i := by cat_disch
  directed {i j : 𝒰.I₀} (x : (pullback (𝒰.f i) (𝒰.f j)).carrier) :
    ∃ (k : 𝒰.I₀) (hki : k ⟶ i) (hkj : k ⟶ j) (y : 𝒰.X k),
      pullback.lift (trans hki) (trans hkj) (by simp [w]) y = x
  property_trans {i j : 𝒰.I₀} (hij : i ⟶ j) : P (trans hij) := by infer_instance

variable (𝒰 : X.Cover (precoverage P)) [Category* 𝒰.I₀] [𝒰.LocallyDirected]

/-- The transition maps of a directed cover. -/
def trans {i j : 𝒰.I₀} (hij : i ⟶ j) : 𝒰.X i ⟶ 𝒰.X j := LocallyDirected.trans hij

@[simp]
lemma trans_map {i j : 𝒰.I₀} (hij : i ⟶ j) : 𝒰.trans hij ≫ 𝒰.f j = 𝒰.f i :=
  LocallyDirected.w hij

@[simp]
lemma trans_id (i : 𝒰.I₀) : 𝒰.trans (𝟙 i) = 𝟙 (𝒰.X i) := LocallyDirected.trans_id i

@[simp]
lemma trans_comp {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k) :
    𝒰.trans (hij ≫ hjk) = 𝒰.trans hij ≫ 𝒰.trans hjk := LocallyDirected.trans_comp hij hjk

lemma exists_lift_trans_eq {i j : 𝒰.I₀} (x : (pullback (𝒰.f i) (𝒰.f j)).carrier) :
    ∃ (k : 𝒰.I₀) (hki : k ⟶ i) (hkj : k ⟶ j) (y : 𝒰.X k),
      pullback.lift (𝒰.trans hki) (𝒰.trans hkj) (by simp) y = x :=
  LocallyDirected.directed x

set_option backward.isDefEq.respectTransparency false in
lemma exists_of_f_eq_f {i j : 𝒰.I₀} (xi : 𝒰.X i) (xj : 𝒰.X j) (h : 𝒰.f i xi = 𝒰.f j xj) :
    ∃ (k : 𝒰.I₀) (fi : k ⟶ i) (fj : k ⟶ j) (xk : 𝒰.X k),
      𝒰.trans fi xk = xi ∧ 𝒰.trans fj xk = xj := by
  obtain ⟨z, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback xi xj h
  obtain ⟨k, fi, fj, xk, rfl⟩ := 𝒰.exists_lift_trans_eq z
  use k, fi, fj, xk
  simp [← Scheme.Hom.comp_apply]

lemma exists_of_trans_eq_trans {i j k : 𝒰.I₀} (fi : i ⟶ k) (fj : j ⟶ k) (xi : 𝒰.X i)
    (xj : 𝒰.X j) (h : 𝒰.trans fi xi = 𝒰.trans fj xj) :
    ∃ (l : 𝒰.I₀) (fli : l ⟶ i) (flj : l ⟶ j) (x : 𝒰.X l),
      𝒰.trans fli x = xi ∧ 𝒰.trans flj x = xj := exists_of_f_eq_f _ _ _ <| by
  rw [← 𝒰.trans_map fi, ← 𝒰.trans_map fj, Hom.comp_base, Hom.comp_base,
    ConcreteCategory.comp_apply, h, ConcreteCategory.comp_apply]

lemma property_trans {i j : 𝒰.I₀} (hij : i ⟶ j) : P (𝒰.trans hij) :=
  LocallyDirected.property_trans hij

/-- If `𝒰` is a directed cover of `X`, this is the cover of `𝒰ᵢ ×[X] 𝒰ⱼ` by `{𝒰ₖ}` where
`k ≤ i` and `k ≤ j`. -/
@[simps f]
def intersectionOfLocallyDirected [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    (i j : 𝒰.I₀) : (pullback (𝒰.f i) (𝒰.f j)).Cover (precoverage P) where
  I₀ := Σ (k : 𝒰.I₀), (k ⟶ i) × (k ⟶ j)
  X k := 𝒰.X k.1
  f k := pullback.lift (𝒰.trans k.2.1) (𝒰.trans k.2.2) (by simp)
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun k ↦ ?_⟩
    · use ⟨(𝒰.exists_lift_trans_eq x).choose, (𝒰.exists_lift_trans_eq x).choose_spec.choose,
        (𝒰.exists_lift_trans_eq x).choose_spec.choose_spec.choose⟩
      exact (𝒰.exists_lift_trans_eq x).choose_spec.choose_spec.choose_spec
    · apply P.of_postcomp (W' := P) _ (pullback.fst _ _) (P.pullback_fst _ _ (𝒰.map_prop _))
      rw [pullback.lift_fst]
      exact 𝒰.property_trans _

/-- The canonical diagram induced by a locally directed cover. -/
@[simps]
def functorOfLocallyDirected : 𝒰.I₀ ⥤ Scheme.{u} where
  obj := 𝒰.X
  map := 𝒰.trans

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance : (𝒰.functorOfLocallyDirected ⋙ Scheme.forget).IsLocallyDirected where
  cond {i j k} fi fj xi xj hxij := by
    simp only [Functor.comp_obj, functorOfLocallyDirected_obj, forget_obj, Functor.comp_map,
      functorOfLocallyDirected_map, forget_map, ConcreteCategory.hom_ofHom,
      TypeCat.Fun.coe_mk] at hxij
    have : 𝒰.f i xi = 𝒰.f j xj := by
      rw [← 𝒰.trans_map fi, ← 𝒰.trans_map fj, Hom.comp_base, Hom.comp_base,
        ConcreteCategory.comp_apply, hxij, ConcreteCategory.comp_apply]
    obtain ⟨z, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback xi xj this
    obtain ⟨l, gi, gj, y, rfl⟩ := 𝒰.exists_lift_trans_eq z
    refine ⟨l, gi, gj, y, ?_, ?_⟩ <;> simp [← Scheme.Hom.comp_apply]

set_option backward.defeqAttrib.useBackward true in
/-- The structure maps to `S` as a natural transformation. -/
@[simps]
def functorOfLocallyDirectedHomBase :
    𝒰.functorOfLocallyDirected ⟶ (Functor.const _).obj X where
  app i := 𝒰.f i

/--
The canonical cocone with point `X` on the functor induced by the locally directed cover `𝒰`.
If `𝒰` is an open cover, this is colimiting (see `OpenCover.isColimitCoconeOfLocallyDirected`).
-/
@[simps]
def coconeOfLocallyDirected : Cocone 𝒰.functorOfLocallyDirected where
  pt := X
  ι := 𝒰.functorOfLocallyDirectedHomBase

section BaseChange

variable [P.IsStableUnderBaseChange] (𝒰 : X.Cover (precoverage P))
    [Category* 𝒰.I₀] [𝒰.LocallyDirected] {Y : Scheme.{u}} (f : Y ⟶ X)

instance : Category (𝒰.pullback₁ f).I₀ := inferInstanceAs <| Category 𝒰.I₀

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance locallyDirectedPullbackCover : Cover.LocallyDirected (𝒰.pullback₁ f) where
  trans {i j} hij := pullback.map f (𝒰.f i) f (𝒰.f j) (𝟙 _) (𝒰.trans hij) (𝟙 _)
    (by simp) (by simp)
  trans_id i := by simp
  trans_comp hij hjk := by simp [pullback.map_comp]
  directed {i j} x := by
    dsimp at i j x ⊢
    let iso : pullback (pullback.fst f (𝒰.f i)) (pullback.fst f (𝒰.f j)) ≅
        pullback f (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) :=
      pullbackRightPullbackFstIso _ _ _ ≪≫ pullback.congrHom pullback.condition rfl ≪≫
        pullbackAssoc ..
    have (k : 𝒰.I₀) (hki : k ⟶ i) (hkj : k ⟶ j) :
        (pullback.lift
          (pullback.map f (𝒰.f k) f (𝒰.f i) (𝟙 Y) (𝒰.trans hki) (𝟙 X) (by simp) (by simp))
          (pullback.map f (𝒰.f k) f (𝒰.f j) (𝟙 Y) (𝒰.trans hkj) (𝟙 X) (by simp) (by simp))
            (by simp)) =
          pullback.map _ _ _ _ (𝟙 Y) (pullback.lift (𝒰.trans hki) (𝒰.trans hkj) (by simp)) (𝟙 X)
            (by simp) (by simp) ≫ iso.inv := by
      apply pullback.hom_ext <;> apply pullback.hom_ext <;> simp [iso]
    obtain ⟨k, hki, hkj, yk, hyk⟩ := 𝒰.exists_lift_trans_eq ((iso.hom ≫ pullback.snd _ _) x)
    refine ⟨k, hki, hkj, show x ∈ Set.range _ from ?_⟩
    rw [this, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Pullback.range_map]
    use iso.hom x
    simp only [Hom.id_base, TopCat.hom_id, ContinuousMap.coe_id, Set.range_id, Set.preimage_univ,
      Set.univ_inter, Set.mem_preimage, Set.mem_range, hom_inv_apply, and_true]
    exact ⟨yk, hyk⟩
  property_trans {i j} hij := by
    let iso : pullback f (𝒰.f i) ≅ pullback (pullback.snd f (𝒰.f j)) (𝒰.trans hij) :=
      pullback.congrHom rfl (by simp) ≪≫ (pullbackLeftPullbackSndIso _ _ _).symm
    rw [← P.cancel_left_of_respectsIso iso.inv]
    simp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
      PreZeroHypercover.pullback₁_X, Iso.trans_inv, Iso.symm_inv, pullback.congrHom_inv,
      Category.assoc, iso]
    convert P.pullback_fst (pullback.snd f (𝒰.f j)) _ (𝒰.property_trans hij)
    apply pullback.hom_ext <;> simp [pullback.condition]

end BaseChange

end Cover

namespace OpenCover

variable (𝒰 : X.OpenCover) [Category* 𝒰.I₀] [𝒰.LocallyDirected]

instance {i j : 𝒰.I₀} (f : i ⟶ j) : IsOpenImmersion (𝒰.trans f) :=
  𝒰.property_trans f

instance {i j : 𝒰.I₀} (f : i ⟶ j) : IsOpenImmersion (𝒰.functorOfLocallyDirected.map f) :=
  𝒰.property_trans f

set_option backward.isDefEq.respectTransparency false in
/--
If `𝒰` is a directed open cover of `X`, to glue morphisms `{gᵢ : 𝒰ᵢ ⟶ Y}` it suffices
to check compatibility with the transition maps.
See `OpenCover.isColimitCoconeOfLocallyDirected` for this result stated in the language of
colimits.
-/
def glueMorphismsOfLocallyDirected (𝒰 : X.OpenCover) [Category* 𝒰.I₀] [𝒰.LocallyDirected]
    {Y : Scheme.{u}}
    (g : ∀ i, 𝒰.X i ⟶ Y) (h : ∀ {i j : 𝒰.I₀} (hij : i ⟶ j), 𝒰.trans hij ≫ g j = g i) :
    X ⟶ Y :=
  𝒰.glueMorphisms g <| fun i j ↦ by
    apply (𝒰.intersectionOfLocallyDirected i j).hom_ext
    intro k
    simp [h]

@[reassoc (attr := simp)]
lemma map_glueMorphismsOfLocallyDirected {Y : Scheme.{u}} (g : ∀ i, 𝒰.X i ⟶ Y)
    (h : ∀ {i j : 𝒰.I₀} (hij : i ⟶ j), 𝒰.trans hij ≫ g j = g i) (i : 𝒰.I₀) :
    𝒰.f i ≫ 𝒰.glueMorphismsOfLocallyDirected g h = g i := by
  simp [glueMorphismsOfLocallyDirected]

set_option backward.defeqAttrib.useBackward true in
/-- If `𝒰` is an open cover of `X` that is locally directed, `X` is
the colimit of the components of `𝒰`. -/
def isColimitCoconeOfLocallyDirected : IsColimit 𝒰.coconeOfLocallyDirected where
  desc s := 𝒰.glueMorphismsOfLocallyDirected s.ι.app fun _ ↦ s.ι.naturality _
  uniq s m hm := 𝒰.hom_ext _ _ fun j ↦ by simpa using hm j

/-- If `𝒰` is a directed open cover of `X`, to glue morphisms `{gᵢ : 𝒰ᵢ ⟶ Y}` over `S` it suffices
to check compatibility with the transition maps. -/
def glueMorphismsOverOfLocallyDirected {S : Scheme.{u}} {X : Over S}
    (𝒰 : X.left.OpenCover) [Category* 𝒰.I₀] [𝒰.LocallyDirected] {Y : Over S}
    (g : ∀ i, 𝒰.X i ⟶ Y.left)
    (h : ∀ {i j : 𝒰.I₀} (hij : i ⟶ j), 𝒰.trans hij ≫ g j = g i)
    (w : ∀ i, g i ≫ Y.hom = 𝒰.f i ≫ X.hom) :
    X ⟶ Y :=
  Over.homMk (𝒰.glueMorphismsOfLocallyDirected g h) <| by
    apply 𝒰.hom_ext
    intro i
    simp [w]

@[reassoc (attr := simp)]
lemma map_glueMorphismsOverOfLocallyDirected_left {S : Scheme.{u}} {X : Over S}
    (𝒰 : X.left.OpenCover) [Category* 𝒰.I₀] [𝒰.LocallyDirected] {Y : Over S}
    (g : ∀ i, 𝒰.X i ⟶ Y.left) (h : ∀ {i j : 𝒰.I₀} (hij : i ⟶ j), 𝒰.trans hij ≫ g j = g i)
    (w : ∀ i, g i ≫ Y.hom = 𝒰.f i ≫ X.hom) (i : 𝒰.I₀) :
    𝒰.f i ≫ (𝒰.glueMorphismsOverOfLocallyDirected g h w).left = g i := by
  simp [glueMorphismsOverOfLocallyDirected]

end OpenCover

/-- If `𝒰` is an open cover such that the images of the components form a basis of the topology
of `X`, `𝒰` is directed by the ordering of subset inclusion of the images. -/
@[implicit_reducible]
def Cover.LocallyDirected.ofIsBasisOpensRange {𝒰 : X.OpenCover} [Preorder 𝒰.I₀]
    (hle : ∀ {i j : 𝒰.I₀}, i ≤ j ↔ (𝒰.f i).opensRange ≤ (𝒰.f j).opensRange)
    (H : TopologicalSpace.Opens.IsBasis (Set.range <| fun i ↦ (𝒰.f i).opensRange)) :
    𝒰.LocallyDirected where
  trans {i j} hij := IsOpenImmersion.lift (𝒰.f j) (𝒰.f i) (hle.mp (leOfHom hij))
  trans_id i := by rw [← cancel_mono (𝒰.f i)]; simp
  trans_comp hij hjk := by rw [← cancel_mono (𝒰.f _)]; simp
  directed {i j} x := by
    have : (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) x ∈
      (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i).opensRange := ⟨x, rfl⟩
    obtain ⟨k, ⟨k, rfl⟩, ⟨y, hy⟩, h⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp H this
    refine ⟨k, homOfLE <| hle.mpr <| le_trans h ?_, homOfLE <| hle.mpr <| le_trans h ?_, y, ?_⟩
    · rw [Scheme.Hom.opensRange_comp]
      exact Set.image_subset_range _ _
    · simp_rw [pullback.condition, Scheme.Hom.opensRange_comp]
      exact Set.image_subset_range _ _
    · apply (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst_assoc, IsOpenImmersion.lift_fac, hy]

section Constructions

section

variable {𝒰 : X.OpenCover} [Preorder 𝒰.I₀]
  (hle : ∀ {i j : 𝒰.I₀}, i ≤ j ↔ (𝒰.f i).opensRange ≤ (𝒰.f j).opensRange)
  (H : TopologicalSpace.Opens.IsBasis (Set.range <| fun i ↦ (𝒰.f i).opensRange))

include hle in
lemma Cover.LocallyDirected.ofIsBasisOpensRange_le_iff (i j : 𝒰.I₀) :
    letI := Cover.LocallyDirected.ofIsBasisOpensRange hle H
    i ≤ j ↔ (𝒰.f i).opensRange ≤ (𝒰.f j).opensRange := hle

lemma Cover.LocallyDirected.ofIsBasisOpensRange_trans {i j : 𝒰.I₀} :
    letI := Cover.LocallyDirected.ofIsBasisOpensRange hle H
    (hij : i ≤ j) → 𝒰.trans (homOfLE hij) = IsOpenImmersion.lift (𝒰.f j) (𝒰.f i) (hle.mp hij) :=
  fun _ ↦ rfl

end

variable (X) in
open TopologicalSpace.Opens in
/-- The directed affine open cover of `X` given by all affine opens. -/
@[simps I₀ X f]
def directedAffineCover : X.OpenCover where
  I₀ := X.affineOpens
  X U := U
  f U := U.1.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    use ⟨(isBasis_iff_nbhd.mp X.isBasis_affineOpens (mem_top x)).choose,
      (isBasis_iff_nbhd.mp X.isBasis_affineOpens (mem_top x)).choose_spec.1⟩
    simpa using (isBasis_iff_nbhd.mp X.isBasis_affineOpens (mem_top x)).choose_spec.2.1

instance : Preorder X.directedAffineCover.I₀ := inferInstanceAs <| Preorder X.affineOpens

set_option backward.defeqAttrib.useBackward true in
instance : Scheme.Cover.LocallyDirected X.directedAffineCover :=
  .ofIsBasisOpensRange (by intros; simp; rfl) <| by
    convert X.isBasis_affineOpens
    simp

@[simp]
lemma directedAffineCover_trans {U V : X.affineOpens} (hUV : U ≤ V) :
    Cover.trans X.directedAffineCover (homOfLE hUV) = X.homOfLE hUV := rfl

end Constructions

end AlgebraicGeometry.Scheme
