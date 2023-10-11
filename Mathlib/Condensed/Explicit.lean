import Mathlib.CategoryTheory.Functor.InvIsos
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.Condensed.Basic
import Mathlib.Condensed.RegularExtensive
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.Topology.Category.Stonean.EffectiveEpi

universe v v₁ u u₁ w

/-
- The section `ExtensiveRegular` has been moved to a new file, `Condensed/RegularExtensive`. All
  that material is PRs #6877, and #6919 (awaiting review). Once these are merged,
  the sections `CompHausExplicitSheaves`,  `ProfiniteExplicitSheaves`, and `StoneanExplicitSheaves`
  can be PR-ed.
- TODO: Do we want to state an equivalent `EqualizerCondition` with the explicit pullbacks?
-/

section CompHausExplicitSheaves

open CategoryTheory Limits CompHaus Opposite Functor Presieve

namespace CompHaus

lemma extensivity_injective {α : Type} [Fintype α] {X : CompHaus.{u}}
    {Z : α → CompHaus.{u}} {π : (a : α) → Z a ⟶ X} {Y : CompHaus.{u}} (f : Y ⟶ X)
    [IsIso (finiteCoproduct.desc _ π)] :
    Function.Injective (finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))) := by
  let ζ := finiteCoproduct.desc _ (fun a => pullback.snd f (π a) ≫ finiteCoproduct.ι Z a )
  let σ := finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))
  let β := CategoryTheory.inv (finiteCoproduct.desc _ π)
  have h : ζ = σ ≫ f ≫ β  := by
    simp only [← Category.assoc, ← asIso_inv, Iso.eq_comp_inv]
    refine finiteCoproduct.hom_ext _ _ _ (fun a => ?_)
    simp only [asIso_hom, finiteCoproduct.ι_desc_assoc, Category.assoc, finiteCoproduct.ι_desc,
      pullback.condition]
  intro R₁ R₂ hR
  obtain ⟨a₁, r₁, h₁⟩ := finiteCoproduct.ι_jointly_surjective _ R₁
  obtain ⟨a₂, r₂, h₂⟩ := finiteCoproduct.ι_jointly_surjective _ R₂
  have ha := calc a₁ = R₁.1 := by rw [h₁]; rfl
    _ = (ζ R₁).1 := rfl
    _ = (β ((σ ≫ f) R₁)).1 := by rw [h]; simp only [comp_apply]
    _ = (β ((σ ≫ f) R₂)).1 := by simp only [comp_apply]; rw [hR]
    _ = (ζ R₂).1 := by rw [h]; simp only [comp_apply]
    _ = R₂.1 := rfl
    _ = a₂ := by rw [h₂]; rfl
  obtain ⟨r', h'⟩ : R₁ ∈ Set.range (finiteCoproduct.ι _ a₂) := by
    rw [← ha, h₁]
    simp only [Set.mem_range, exists_apply_eq_apply]
  rw [← h', h₂] at hR
  have hπ : ∀ (a : α), Function.Injective (π a) := fun a x y h ↦ (by
    rw [← finiteCoproduct.ι_desc_apply, ← finiteCoproduct.ι_desc_apply] at h
    exact (finiteCoproduct.ι_injective _ a)
      ((ConcreteCategory.bijective_of_isIso (finiteCoproduct.desc Z π)).injective h))
  have hf : ∀ (a : α), Function.Injective
      ((finiteCoproduct.ι _ a) ≫ (finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))))
  · simp only [finiteCoproduct.ι_desc]
    intro a x y h
    have h' : (pullback.fst f (π a) ≫ f) x = (pullback.fst f (π a) ≫ f) y := by
      simp only [comp_apply]; rw [h]
    rw [pullback.condition] at h'
    exact Subtype.ext (Prod.ext h (hπ a h'))
  rw [← h', h₂, hf a₂ hR]

lemma extensivity_explicit {α : Type} [Fintype α] {X : CompHaus.{u}}
    {Z : α → CompHaus.{u}} (π : (a : α) → Z a ⟶ X) {Y : CompHaus.{u}} (f : Y ⟶ X)
    [IsIso (finiteCoproduct.desc _ π)] :
    IsIso (finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))) := by
  let β := finiteCoproduct.desc _ π
  refine isIso_of_bijective _
    ⟨extensivity_injective f, fun y => ⟨⟨(inv β (f y)).1, ⟨⟨y, (inv β (f y)).2⟩,
    (ConcreteCategory.bijective_of_isIso (inv β)).injective ?_⟩⟩, rfl⟩⟩
  suffices ∀ a, π a ≫ inv β = finiteCoproduct.ι _ a by change _ = (_ ≫ inv β) _; rw [this]; rfl
  intro a
  simp only [IsIso.comp_inv_eq, finiteCoproduct.ι_desc]

instance : Extensive CompHaus where
  sigma_desc_iso := @fun α _ X Z i Y f H => by
    let θ := Sigma.mapIso (fun a => pullbackIsoPullback f (i a))
    suffices IsIso (θ.hom ≫ Sigma.desc fun x => Limits.pullback.fst) by
      · apply IsIso.of_isIso_comp_left θ.hom
    let δ := coproductIsoCoproduct (fun a => CompHaus.pullback f (i a))
    suffices IsIso <| δ.hom ≫ (θ.hom ≫ Sigma.desc fun x => Limits.pullback.fst) by
      · apply IsIso.of_isIso_comp_left δ.hom
    convert extensivity_explicit i f
    · refine' finiteCoproduct.hom_ext _ _ _ (fun a => _)
      rw [finiteCoproduct.ι_desc, ← Category.assoc, ← Sigma.ι_comp_toFiniteCoproduct]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, pullbackIsoPullback, mapIso_hom,
        colim_map, colimit.map_desc, colimit.ι_desc, Cocones.precompose_obj_pt, Cofan.mk_pt,
        Cocones.precompose_obj_ι, NatTrans.comp_app, Discrete.functor_obj, const_obj_obj,
        Discrete.natIso_hom_app, Cofan.mk_ι_app, limit.conePointUniqueUpToIso_hom_comp,
        pullback.cone_pt, pullback.cone_π]
    · suffices IsIso <| (coproductIsoCoproduct Z).inv ≫ (finiteCoproduct.desc _ i) by
        · apply IsIso.of_isIso_comp_left (coproductIsoCoproduct Z).inv
      convert H
      refine' Sigma.hom_ext _ _ (fun a => _)
      simp only [coproductIsoCoproduct, colimit.comp_coconePointUniqueUpToIso_inv_assoc,
        Discrete.functor_obj, finiteCoproduct.cocone_pt, finiteCoproduct.cocone_ι,
        Discrete.natTrans_app, finiteCoproduct.ι_desc, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]

instance : Preregular CompHaus where
  exists_fac := by
    intro X Y Z f π hπ
    refine ⟨pullback f π, pullback.fst f π, ?_, pullback.snd f π, (pullback.condition _ _).symm⟩
    rw [CompHaus.effectiveEpi_iff_surjective] at hπ ⊢
    intro y
    obtain ⟨z,hz⟩ := hπ (f y)
    exact ⟨⟨(y, z), hz.symm⟩, rfl⟩

lemma isSheafFor_of_preservesFiniteProducts_and_equalizerCondition {B : CompHaus} {S : Presieve B}
    (hS : S ∈ ((extensiveCoverage CompHaus) ⊔ (regularCoverage CompHaus)).covering B)
    {F : CompHaus.{u}ᵒᵖ ⥤ Type (u+1)} [PreservesFiniteProducts F]
    (hFecs : EqualizerCondition F) :
    S.IsSheafFor F := by
  cases' hS with hSIso hSSingle
  · simp only [extensiveCoverage, Set.mem_setOf_eq] at hSIso
    haveI : S.extensive := ⟨hSIso⟩
    exact isSheafFor_extensive_of_preservesFiniteProducts S F
  · haveI : S.regular := ⟨hSSingle⟩
    exact isSheafFor_regular_of_hasPullbacks hFecs

instance {A B : Type*} [Category A] [Category B] (F : B ⥤ A) (E : A)  [PreservesFiniteProducts F] :
    PreservesFiniteProducts (F ⋙ coyoneda.obj (op E)) :=
  ⟨fun J _ ↦ @compPreservesLimitsOfShape _ _ _ _ _ _ _ _ F (coyoneda.obj (op E))
    (PreservesFiniteProducts.preserves J) ((preservesLimitsOfSizeShrink _).preservesLimitsOfShape)⟩

theorem final (A : Type (u+2)) [Category.{u+1} A] {F : CompHaus.{u}ᵒᵖ ⥤ A}
    [PreservesFiniteProducts F]
    (hF' : ∀ (E : A), EqualizerCondition (F ⋙ coyoneda.obj (op E))) :
    Presheaf.IsSheaf (coherentTopology CompHaus) F := by
  rw [← extensive_regular_generate_coherent]
  refine' fun E => (Presieve.isSheaf_coverage _ _).2 _
  intro B S hS
  exact isSheafFor_of_preservesFiniteProducts_and_equalizerCondition hS (hF' E)

theorem final' (A : Type (u+2)) [Category.{u+1} A] {G : A ⥤ Type (u+1)}
    [HasLimits A] [PreservesLimits G] [ReflectsIsomorphisms G] {F : CompHaus.{u}ᵒᵖ ⥤ A}
    [PreservesFiniteProducts (F ⋙ G)] (hF' : EqualizerCondition (F ⋙ G)) :
    Presheaf.IsSheaf (coherentTopology CompHaus) F := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (coherentTopology CompHaus) F G,
    isSheaf_iff_isSheaf_of_type, ← extensive_regular_generate_coherent,
    Presieve.isSheaf_coverage]
  intro B S' hS
  exact isSheafFor_of_preservesFiniteProducts_and_equalizerCondition hS hF'

end CompHaus

end CompHausExplicitSheaves

section ProfiniteExplicitSheaves

open CategoryTheory Profinite Opposite CategoryTheory.Limits Functor Presieve

namespace Profinite

lemma extensivity_injective {α : Type} [Fintype α] {X : Profinite.{u}}
    {Z : α → Profinite.{u}} (π : (a : α) → Z a ⟶ X) {Y : Profinite.{u}} (f : Y ⟶ X)
    [IsIso (finiteCoproduct.desc _ π)] :
    Function.Injective (finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))) := by
  let ζ := finiteCoproduct.desc _ (fun a => pullback.snd f (π a) ≫ finiteCoproduct.ι Z a )
  let σ := finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))
  let β := CategoryTheory.inv (finiteCoproduct.desc _ π)
  have h : ζ = σ ≫ f ≫ β  := by
    simp only [← Category.assoc, ← asIso_inv, Iso.eq_comp_inv]
    refine finiteCoproduct.hom_ext _ _ _ (fun a => ?_)
    simp only [asIso_hom, finiteCoproduct.ι_desc_assoc, Category.assoc, finiteCoproduct.ι_desc,
      pullback.condition]
  intro R₁ R₂ hR
  obtain ⟨a₁, r₁, h₁⟩ := finiteCoproduct.ι_jointly_surjective _ R₁
  obtain ⟨a₂, r₂, h₂⟩ := finiteCoproduct.ι_jointly_surjective _ R₂
  have ha := calc a₁ = R₁.1 := by rw [h₁]; rfl
    _ = (ζ R₁).1 := rfl
    _ = (β ((σ ≫ f) R₁)).1 := by rw [h]; simp only [comp_apply]
    _ = (β ((σ ≫ f) R₂)).1 := by simp only [comp_apply]; rw [hR]
    _ = (ζ R₂).1 := by rw [h]; simp only [comp_apply]
    _ = R₂.1 := rfl
    _ = a₂ := by rw [h₂]; rfl
  obtain ⟨r', h'⟩ : R₁ ∈ Set.range (finiteCoproduct.ι _ a₂) := by
    rw [← ha, h₁]
    simp only [Set.mem_range, exists_apply_eq_apply]
  rw [← h', h₂] at hR
  have hπ : ∀ (a : α), Function.Injective (π a) := fun a x y h ↦ (by
    rw [← finiteCoproduct.ι_desc_apply, ← finiteCoproduct.ι_desc_apply] at h
    exact (finiteCoproduct.ι_injective _ a)
      ((ConcreteCategory.bijective_of_isIso (finiteCoproduct.desc Z π)).injective h))
  have hf : ∀ (a : α), Function.Injective
      ((finiteCoproduct.ι _ a) ≫ (finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))))
  · simp only [finiteCoproduct.ι_desc]
    intro a x y h
    have h' : (pullback.fst f (π a) ≫ f) x = (pullback.fst f (π a) ≫ f) y := by
      simp only [comp_apply]; rw [h]
    rw [pullback.condition] at h'
    exact Subtype.ext (Prod.ext h (hπ a h'))
  rw [← h', h₂, hf a₂ hR]

lemma extensivity_explicit {α : Type} [Fintype α] {X : Profinite.{u}}
    {Z : α → Profinite.{u}} (π : (a : α) → Z a ⟶ X) {Y : Profinite.{u}} (f : Y ⟶ X)
    [IsIso (finiteCoproduct.desc _ π)] :
     IsIso (finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))) := by
  let β := finiteCoproduct.desc _ π
  refine isIso_of_bijective _
    ⟨extensivity_injective π f, fun y => ⟨⟨(inv β (f y)).1, ⟨⟨y, (inv β (f y)).2⟩,
    (ConcreteCategory.bijective_of_isIso (inv β)).injective ?_⟩⟩, rfl⟩⟩
  suffices ∀ a, π a ≫ inv β = finiteCoproduct.ι _ a by change _ = (_ ≫ inv β) _; rw [this]; rfl
  intro a
  simp only [IsIso.comp_inv_eq, finiteCoproduct.ι_desc]

instance : Extensive Profinite where
  sigma_desc_iso := @fun α _ X Z i Y f H => by
    let θ := Sigma.mapIso (fun a => pullbackIsoPullback f (i a))
    suffices IsIso (θ.hom ≫ Sigma.desc fun x => Limits.pullback.fst) by
      · apply IsIso.of_isIso_comp_left θ.hom
    let δ := coproductIsoCoproduct (fun a => Profinite.pullback f (i a))
    suffices IsIso <| δ.hom ≫ (θ.hom ≫ Sigma.desc fun x => Limits.pullback.fst) by
      · apply IsIso.of_isIso_comp_left δ.hom
    convert extensivity_explicit i f
    · refine' finiteCoproduct.hom_ext _ _ _ (fun a => _)
      rw [finiteCoproduct.ι_desc, ← Category.assoc, ← Sigma.ι_comp_toFiniteCoproduct]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, pullbackIsoPullback, mapIso_hom,
        colim_map, colimit.map_desc, colimit.ι_desc, Cocones.precompose_obj_pt, Cofan.mk_pt,
        Cocones.precompose_obj_ι, NatTrans.comp_app, Discrete.functor_obj, const_obj_obj,
        Discrete.natIso_hom_app, Cofan.mk_ι_app, limit.conePointUniqueUpToIso_hom_comp,
        pullback.cone_pt, pullback.cone_π]
    · suffices IsIso <| (coproductIsoCoproduct Z).inv ≫ (finiteCoproduct.desc _ i) by
        · apply IsIso.of_isIso_comp_left (coproductIsoCoproduct Z).inv
      convert H
      refine' Sigma.hom_ext _ _ (fun a => _)
      simp only [coproductIsoCoproduct, colimit.comp_coconePointUniqueUpToIso_inv_assoc,
        Discrete.functor_obj, finiteCoproduct.cocone_pt, finiteCoproduct.cocone_ι,
        Discrete.natTrans_app, finiteCoproduct.ι_desc, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]

instance : Preregular Profinite where
  exists_fac := by
    intro X Y Z f π hπ
    refine ⟨pullback f π, pullback.fst f π, ?_, pullback.snd f π, (pullback.condition _ _).symm⟩
    rw [Profinite.effectiveEpi_iff_surjective] at hπ ⊢
    intro y
    obtain ⟨z,hz⟩ := hπ (f y)
    exact ⟨⟨(y, z), hz.symm⟩, rfl⟩

lemma isSheafFor_of_preservesFiniteProducts_and_equalizerCondition {B : Profinite} {S : Presieve B}
    (hS : S ∈ ((extensiveCoverage Profinite) ⊔ (regularCoverage Profinite)).covering B)
    {F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)} [PreservesFiniteProducts F]
    (hFecs : EqualizerCondition F) :
    S.IsSheafFor F := by
  cases' hS with hSIso hSSingle
  · simp only [extensiveCoverage, Set.mem_setOf_eq] at hSIso
    haveI : S.extensive := ⟨hSIso⟩
    exact isSheafFor_extensive_of_preservesFiniteProducts S F
  · haveI : S.regular := ⟨hSSingle⟩
    exact isSheafFor_regular_of_hasPullbacks hFecs

theorem final (A : Type (u+2)) [Category.{u+1} A] {F : Profinite.{u}ᵒᵖ ⥤ A}
    [PreservesFiniteProducts F]
    (hF' : ∀ (E : A), EqualizerCondition (F ⋙ coyoneda.obj (op E))) :
  Presheaf.IsSheaf (coherentTopology Profinite) F := by
  rw [← extensive_regular_generate_coherent]
  refine' fun E => (Presieve.isSheaf_coverage _ _).2 _
  intro B S hS
  exact isSheafFor_of_preservesFiniteProducts_and_equalizerCondition hS (hF' E)

theorem final' (A : Type (u+2)) [Category.{u+1} A] {G : A ⥤ Type (u+1)}
    [HasLimits A] [PreservesLimits G] [ReflectsIsomorphisms G]
    {F : Profinite.{u}ᵒᵖ ⥤ A}
    [PreservesFiniteProducts (F ⋙ G)] (hF' : EqualizerCondition (F ⋙ G)) :
    Presheaf.IsSheaf (coherentTopology Profinite) F := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (coherentTopology Profinite) F G,
    isSheaf_iff_isSheaf_of_type, ← extensive_regular_generate_coherent,
    Presieve.isSheaf_coverage]
  intro B S' hS
  exact isSheafFor_of_preservesFiniteProducts_and_equalizerCondition hS hF'

end Profinite

end ProfiniteExplicitSheaves

section StoneanExplicitSheaves

open CategoryTheory Stonean Opposite CategoryTheory.Limits Functor Presieve

namespace Stonean

lemma openEmbedding_of_sigma_desc_iso {α : Type} [Fintype α] {X : Stonean.{u}}
    {Z : α → Stonean.{u}} {i : (a : α) → Z a ⟶ X} (HIso : IsIso (Sigma.desc i)) :
    ∀ a, OpenEmbedding (i a) := by
  intro a
  have h₁ : OpenEmbedding (Sigma.desc i) :=
    (Stonean.homeoOfIso (asIso (Sigma.desc i))).openEmbedding
  have h₂ : OpenEmbedding (Sigma.ι Z a) := Sigma.openEmbedding_ι _ _
  have := OpenEmbedding.comp h₁ h₂
  erw [← CategoryTheory.coe_comp (Sigma.ι Z a) (Sigma.desc i)] at this
  simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app] at this
  assumption

instance : HasPullbacksOfInclusions Stonean := by
  constructor
  intro X Z α f Y i _ _ _ a
  apply HasPullbackOpenEmbedding
  apply openEmbedding_of_sigma_desc_iso inferInstance

lemma isIso_of_bijective {X Y : Stonean.{u}} (f : X ⟶ Y) (hf : Function.Bijective f) : IsIso f := by
  suffices IsIso <| toCompHaus.map f by
    · apply isIso_of_fully_faithful toCompHaus
  exact CompHaus.isIso_of_bijective _ hf

lemma extensivity_injective {α : Type} [Fintype α] {X : Stonean.{u}}
    {Z : α → Stonean.{u}} (π : (a : α) → Z a ⟶ X) {Y : Stonean.{u}} (f : Y ⟶ X)
    [IsIso (finiteCoproduct.desc _ π)] (hOpen : ∀ a, OpenEmbedding (π a)) :
    Function.Injective (finiteCoproduct.desc _ ((fun a => pullback.fst f (hOpen a)))) := by
  let ζ := finiteCoproduct.desc _ (fun a => pullback.snd f (hOpen a) ≫ finiteCoproduct.ι Z a )
  let α := finiteCoproduct.desc _ ((fun a => pullback.fst f (hOpen a)))
  let β := CategoryTheory.inv (finiteCoproduct.desc _ π)
  have h : ζ = α ≫ f ≫ β  := by
    simp only [← Category.assoc, ← asIso_inv, Iso.eq_comp_inv]
    refine finiteCoproduct.hom_ext _ _ _ (fun a => ?_)
    simp only [asIso_hom, finiteCoproduct.ι_desc_assoc, Category.assoc, finiteCoproduct.ι_desc,
      pullback.condition]
  intro R₁ R₂ hR
  have Hfst := calc R₁.1 = (ζ R₁).1 := rfl
    _ = (β ((α ≫ f) R₁)).1 := by rw [h]; rfl
    _ = (β ((α ≫ f) R₂)).1 := by change (β (f (α _))).1 = (β (f (α _))).1; rw [hR]
    _ = (ζ R₂).1 := by rw [h]; rfl
    _ = R₂.1 := rfl
  exact Sigma.subtype_ext Hfst hR

lemma extensivity_explicit {α : Type} [Fintype α] {X : Stonean.{u}}
    {Z : α → Stonean.{u}} (π : (a : α) → Z a ⟶ X) {Y : Stonean.{u}} (f : Y ⟶ X)
    [IsIso (finiteCoproduct.desc _ π)] (hOpen : ∀ a, OpenEmbedding (π a)) :
     IsIso (finiteCoproduct.desc _ ((fun a => pullback.fst f (hOpen a)))) := by
  let β := finiteCoproduct.desc _ π
  refine isIso_of_bijective _
    ⟨extensivity_injective π f hOpen, fun y => ⟨⟨(inv β (f y)).1, ⟨y, (inv β (f y)).2,
    (ConcreteCategory.bijective_of_isIso (inv β)).injective ?_⟩⟩, rfl⟩⟩
  suffices ∀ a, π a ≫ inv β = finiteCoproduct.ι _ a by change (_ ≫ inv β) _ = _; rw [this]; rfl
  intro a
  simp only [IsIso.comp_inv_eq, finiteCoproduct.ι_desc]

theorem Sigma.ι_comp_toFiniteCoproduct {α : Type} [Fintype α] {Z : α → Stonean.{u}} (a : α) :
    (Limits.Sigma.ι Z a) ≫ (coproductIsoCoproduct Z).inv = finiteCoproduct.ι Z a := by
  simp only [coproductIsoCoproduct, colimit.comp_coconePointUniqueUpToIso_inv,
    finiteCoproduct.explicitCocone_pt, finiteCoproduct.explicitCocone_ι, Discrete.natTrans_app]

instance : Extensive Stonean where
  sigma_desc_iso := @fun α _ X Z i Y f H => by
    have hOpen := openEmbedding_of_sigma_desc_iso H
    let θ := Sigma.mapIso (fun a => pullbackIsoPullback f (hOpen a))
    suffices IsIso (θ.hom ≫ Sigma.desc fun x => Limits.pullback.fst) by
      · apply IsIso.of_isIso_comp_left θ.hom
    let δ := coproductIsoCoproduct (fun a => (pullback.cone f (hOpen a)).pt)
    suffices IsIso <| δ.hom ≫ (θ.hom ≫ Sigma.desc fun x => Limits.pullback.fst) by
      · apply IsIso.of_isIso_comp_left δ.hom
    convert extensivity_explicit i f hOpen
    · refine' Stonean.finiteCoproduct.hom_ext _ _ _ (fun a => _)
      erw [finiteCoproduct.ι_desc, ← Category.assoc, ← Sigma.ι_comp_toFiniteCoproduct]
      simp only [pullback.cone_pt, Category.assoc, Iso.inv_hom_id, Category.comp_id, mapIso_hom,
        colim_map, colimit.map_desc, colimit.ι_desc, Cocones.precompose_obj_pt, Cofan.mk_pt,
        Cocones.precompose_obj_ι, NatTrans.comp_app, Discrete.functor_obj, const_obj_obj,
        Discrete.natIso_hom_app, pullbackIsoPullback_hom, Cofan.mk_ι_app, limit.lift_π,
        PullbackCone.mk_pt, PullbackCone.mk_π_app]
    · suffices IsIso <| (coproductIsoCoproduct Z).inv ≫ (finiteCoproduct.desc _ i) by
        · apply IsIso.of_isIso_comp_left (coproductIsoCoproduct Z).inv
      convert H
      refine' Sigma.hom_ext _ _ (fun a => _)
      simp only [coproductIsoCoproduct, colimit.comp_coconePointUniqueUpToIso_inv_assoc, Discrete.functor_obj,
        finiteCoproduct.explicitCocone_pt, finiteCoproduct.explicitCocone_ι, Discrete.natTrans_app,
        finiteCoproduct.ι_desc, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]

instance everything_proj (X : Stonean) : Projective X where
  factors := by
    intro B C φ f _
    haveI : ExtremallyDisconnected X.compHaus.toTop := X.extrDisc
    have hf : Function.Surjective f := by rwa [← Stonean.epi_iff_surjective]
    obtain ⟨f', h⟩ := CompactT2.ExtremallyDisconnected.projective φ.continuous f.continuous hf
    use ⟨f', h.left⟩
    ext
    exact congr_fun h.right _

def EffectiveEpiStructId {C : Type u} [Category.{v} C] {X : C} : EffectiveEpiStruct (𝟙 X) where
  desc e _ := e
  fac _ _ := by simp only [Category.id_comp]
  uniq _ _ _ h := by simp only [Category.id_comp] at h; exact h

instance {C : Type u} [Category.{v} C] {X : C} : EffectiveEpi (𝟙 X) := ⟨⟨EffectiveEpiStructId⟩⟩

instance : Preregular Stonean where
  exists_fac := by
    intro X Y Z f π hπ
    exact ⟨X, 𝟙 X, inferInstance, Projective.factors f π⟩

lemma isSheafForRegularSieve {X : Stonean} (S : Presieve X) [S.regular]
    (F : Stonean.{u}ᵒᵖ ⥤ Type (u+1)) : IsSheafFor F S := isSheafFor_regular_of_projective S F

lemma isSheafFor_of_extensiveRegular {X : Stonean} {S : Presieve X}
  (hS : S ∈ ((extensiveCoverage Stonean) ⊔ (regularCoverage Stonean)).covering X)
  {F : Stonean.{u}ᵒᵖ ⥤ Type (u+1)} [PreservesFiniteProducts F] : S.IsSheafFor F := by
  cases' hS with hSIso hSSingle
  · simp only [extensiveCoverage, Set.mem_setOf_eq] at hSIso
    haveI : S.extensive := ⟨hSIso⟩
    exact isSheafFor_extensive_of_preservesFiniteProducts S F
  · simp only [regularCoverage, Set.mem_setOf_eq] at hSSingle
    haveI : S.regular := ⟨hSSingle⟩
    exact isSheafForRegularSieve S F

theorem final (A : Type (u+2)) [Category.{u+1} A] {F : Stonean.{u}ᵒᵖ ⥤ A}
    [PreservesFiniteProducts F] : Presheaf.IsSheaf (coherentTopology Stonean) F := by
  rw [← extensive_regular_generate_coherent]
  exact fun E => (Presieve.isSheaf_coverage _ _).2 <| fun S hS => isSheafFor_of_extensiveRegular hS

end Stonean

end StoneanExplicitSheaves
