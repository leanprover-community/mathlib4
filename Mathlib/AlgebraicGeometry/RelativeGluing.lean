/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-!
# Relative gluing

In this file we show a relative gluing lemma (see https://stacks.math.columbia.edu/tag/01LH):
If `{Uᵢ}` is a locally directed open cover of `S` and we have a compatible family of `Xᵢ` over `Uᵢ`,
the `Xᵢ` glue to a morphism `f : X ⟶ S` such that `Xᵢ ≅ f⁻¹ Uᵢ`.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
lemma Scheme.isLocallyDirected_of_equifibered_of_injective {J : Type*} [Category J]
    {F G : J ⥤ Scheme.{u}} (s : F ⟶ G) [Quiver.IsThin J] (hs : s.Equifibered)
    (H : ∀ {i j} (hij : i ⟶ j), Function.Injective (F.map hij))
    [(G ⋙ Scheme.forget).IsLocallyDirected] :
    (F ⋙ Scheme.forget).IsLocallyDirected where
  cond {i j k} fi fj xi xj heq := by
    simp only [Functor.comp_obj, Scheme.forget_obj, Functor.comp_map, Scheme.forget_map] at heq
    obtain ⟨l, fli, flj, x, hi, hj⟩ := (G ⋙ Scheme.forget).exists_map_eq_of_isLocallyDirected fi fj
        (s.app i xi) (s.app j xj) <| by
      simp only [Functor.comp_obj, forget_obj, Functor.comp_map, forget_map,
        ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
      dsimp at heq
      rw [← Scheme.Hom.comp_apply, ← s.naturality, Scheme.Hom.comp_apply, heq,
        ← Scheme.Hom.comp_apply, s.naturality]
      simp
    use l, fli, flj
    let e := (hs fli).isoPullback
    obtain ⟨z, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback xi x hi.symm
    refine ⟨e.inv z, ?_, ?_⟩
    · simp [← h1, ← Scheme.Hom.comp_apply, e]
    · apply H fj
      simp only [Functor.comp_obj, forget_obj, Functor.comp_map, forget_map,
        ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, ← Scheme.Hom.comp_apply,
        Category.assoc, ← Functor.map_comp, show flj ≫ fj = fli ≫ fi by subsingleton]
      dsimp at heq
      simp [e, Functor.map_comp, ← heq, h1]

namespace Scheme.Cover

variable {S : Scheme.{u}} (𝒰 : S.OpenCover) [Category 𝒰.I₀] [𝒰.LocallyDirected]

/--
A relative gluing datum over a locally directed cover `𝒰` of `S` is a scheme `Xᵢ` for every
`i : 𝒰.I₀` and natural maps `Xᵢ ⟶ Uᵢ` such that for every `i ⟶ j`, the diagram
```
Xᵢ --> Uᵢ
|      |
v      v
Xⱼ --> Uⱼ
```
is a pullback square. We bundle this in the form of a functor and an equifibered natural
transformation.
The `Xᵢ` then glue to a scheme over `S`
(see `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.glued`).
-/
@[stacks 01LH]
structure RelativeGluingData where
  /-- The schemes `Xᵢ`. -/
  functor : 𝒰.I₀ ⥤ Scheme.{u}
  /-- The natural maps `Xᵢ ⟶ Uᵢ`. -/
  natTrans : functor ⟶ 𝒰.functorOfLocallyDirected
  equifibered : natTrans.Equifibered

variable {𝒰} (d : RelativeGluingData 𝒰)

namespace RelativeGluingData

instance {i j : 𝒰.I₀} (hij : i ⟶ j) : IsOpenImmersion (d.functor.map hij) := by
  apply MorphismProperty.of_isPullback (d.equifibered hij).flip
  infer_instance

instance [Quiver.IsThin 𝒰.I₀] : (d.functor ⋙ Scheme.forget).IsLocallyDirected := by
  apply isLocallyDirected_of_equifibered_of_injective d.natTrans d.equifibered
  intro i j hij
  exact (d.functor.map hij).injective

variable [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]

/--
The glued scheme of a relative gluing datum is the colimit over the `Xᵢ`. For the
structure map, see `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.toBase` and the isomorphisms
with the preimages `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.isPullback_natTrans_ι_toBase`.
-/
@[stacks 01LH]
noncomputable abbrev glued : Scheme.{u} :=
  colimit d.functor

/-- The cover of the glued `Xᵢ` given by the `Xᵢ`. -/
@[simps!]
noncomputable def cover : OpenCover d.glued :=
  Scheme.IsLocallyDirected.openCover _

instance : Category d.cover.I₀ :=
  inferInstanceAs <| Category 𝒰.I₀

/-- The structure map from the colimit of the `Xᵢ` to `S`. -/
noncomputable def toBase : d.glued ⟶ S :=
  colimit.desc _
    { pt := S
      ι := d.natTrans ≫ 𝒰.functorOfLocallyDirectedHomBase }

@[reassoc (attr := simp)]
lemma ι_toBase (i : 𝒰.I₀) :
    colimit.ι d.functor i ≫ d.toBase = d.natTrans.app i ≫ 𝒰.f i := by
  simp [toBase]

set_option backward.isDefEq.respectTransparency false in
instance : d.cover.LocallyDirected where
  trans {i j} hij := d.functor.map hij
  directed {i j} x := by
    let xi := pullback.fst (d.cover.f i) _ x
    let xj := pullback.snd (d.cover.f i) _ x
    obtain ⟨k, fi, fj, uk, h1, h2⟩ :=
        𝒰.exists_of_f_eq_f (d.natTrans.app i xi) (d.natTrans.app j xj) <| by
      dsimp [functorOfLocallyDirected_obj, xi, xj]
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← ι_toBase, pullback.condition_assoc]
      simp
    use k, fi, fj
    obtain ⟨xk, h1, h2⟩ := exists_preimage_of_isPullback (d.equifibered fj) xj uk <| by
      apply (𝒰.f j).injective
      dsimp only [functorOfLocallyDirected_obj, functorOfLocallyDirected_map]
      rw [← Scheme.Hom.comp_apply]
      simp [xj, h2]
    use xk
    apply (pullback.snd (d.cover.f i) _).injective
    rw [← Scheme.Hom.comp_apply]
    simp [h1, xj]

set_option backward.isDefEq.respectTransparency false in
lemma preimage_toBase_eq_range_ι (i : 𝒰.I₀) :
    d.toBase ⁻¹' (Set.range <| 𝒰.f i) = Set.range (colimit.ι d.functor i) := by
  ext x
  refine ⟨fun ⟨ui, h⟩ ↦ ?_, ?_⟩
  · obtain ⟨j, xj, rfl⟩ := IsLocallyDirected.ι_jointly_surjective _ x
    obtain ⟨k, fi, fj, uk, rfl, h⟩ := 𝒰.exists_of_f_eq_f ui (d.natTrans.app j xj) <| by
      simp only [h, functorOfLocallyDirected_obj, ← Scheme.Hom.comp_apply, ι_toBase]
    obtain ⟨xk, rfl, h2⟩ := exists_preimage_of_isPullback (d.equifibered fj) xj uk <| by
      apply (𝒰.f j).injective
      simp only [functorOfLocallyDirected_obj, functorOfLocallyDirected_map]
      rw [← Scheme.Hom.comp_apply, ← ι_toBase, Scheme.Hom.comp_apply, ← h]
      simp [← Scheme.Hom.comp_apply]
    use d.functor.map fi xk
    simp [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
  · rintro ⟨y, rfl⟩
    use d.natTrans.app i y
    rw [← Scheme.Hom.comp_apply, ι_toBase]
    simp

lemma toBase_preimage_eq_opensRange_ι (i : 𝒰.I₀) :
    d.toBase ⁻¹ᵁ (𝒰.f i).opensRange = (colimit.ι d.functor i).opensRange :=
  TopologicalSpace.Opens.coe_inj.mp (preimage_toBase_eq_range_ι d i)

set_option backward.isDefEq.respectTransparency false in
lemma isPullback_natTrans_ι_toBase (i : 𝒰.I₀) :
    IsPullback (d.natTrans.app i) (colimit.ι d.functor i) (𝒰.f i) d.toBase := by
  refine ⟨by simp, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro s
    apply IsOpenImmersion.lift (colimit.ι d.functor i) s.snd
    rw [← preimage_toBase_eq_range_ι]
    rintro x ⟨x, rfl⟩
    use s.fst x
    rw [← Scheme.Hom.comp_apply, ← s.condition]
    simp
  · intro s
    rw [← cancel_mono (𝒰.f i), Category.assoc, ← ι_toBase, IsOpenImmersion.lift_fac_assoc,
      s.condition]
  · simp
  · intro s m h1 h2
    simpa [← cancel_mono (colimit.ι d.functor i)]

end Scheme.Cover.RelativeGluingData

end AlgebraicGeometry
