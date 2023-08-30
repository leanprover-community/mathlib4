import Mathlib.CategoryTheory.Functor.InvIsos
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.Condensed.Basic
import Mathlib.Condensed.RegularExtensive
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.Topology.Category.Stonean.EffectiveEpi

universe v v₁ u u₁ w

/-
- The sections `isSheafForPullBackSieve` and `ProdCoprod` are independent and can be PR-ed
  separately (DONE, see #6750 (merged) and #6758 (merged)).
- The section `ExtensiveRegular` depends on section `isSheafForPullBackSieve` but does not
  mention `Stonean`, `Profinite` or `CompHaus` explicitly. (PR #6847, awaiting review)
- The code in section `OpenEmbedding` should be added to `Mathlib.Topology.Category.Stonean.Limits`
  in a separate PR and does not depend on any of the previous stuff in this file
  (DONE, see #6771 (merged) and #6774 (merged)).
- The section `StoneanPullback` can be PR-ed (DONE, see #6779 (awaiting review)).
- The section `StoneanProjective` can be removed once #5808 is merged. (DONE)
- The section `StoneanPrecoherent` can be removed once #6725 is merged. (DONE)
- The sections `CompHausExplicitSheaves` and `ProfiniteExplicitSheaves` are identical except for
  the words `CompHaus` and `Profinite`. The section `StoneanExplicitSheaves` is very similar. In
  particular, the proofs of the three versions of `extensiveRegular_generates_coherent` are nearly
  identical. The common properties of these three categories used in that proof are
  `epi_iff_surjective` and `effectiveEpiFamily_tfae` (basically that effective epi families are
  finite jointly surjective). TODO: unify this into one theorem for categories satisfying this.
-/

section EffectiveEpis

open CategoryTheory

lemma CompHaus.effectiveEpi_iff_surjective {X Y : CompHaus} (f : X ⟶ Y) :
    EffectiveEpi f ↔ Function.Surjective f := sorry

lemma Profinite.effectiveEpi_iff_surjective {X Y : Profinite} (f : X ⟶ Y) :
    EffectiveEpi f ↔ Function.Surjective f := sorry

lemma Stonean.effectiveEpi_iff_surjective {X Y : Stonean} (f : X ⟶ Y) :
    EffectiveEpi f ↔ Function.Surjective f := sorry


end EffectiveEpis

section StoneanPullback -- This section is PR #6779

open CategoryTheory Limits

def OpenEmbeddingConePt {X Y Z : Stonean} (f : X ⟶ Z) {i : Y ⟶ Z} (hi : OpenEmbedding i) :
    Stonean where
  compHaus := {
    toTop := TopCat.of (f ⁻¹' (Set.range i))
    is_compact := by
      dsimp [TopCat.of]
      rw [← isCompact_iff_compactSpace]
      apply IsClosed.isCompact
      refine' IsClosed.preimage f.continuous _
      apply IsCompact.isClosed
      simp only [← Set.image_univ]
      exact IsCompact.image isCompact_univ i.continuous
    is_hausdorff := by
      dsimp [TopCat.of]
      exact inferInstance
  }
  extrDisc := by
    constructor
    have h : IsClopen (f ⁻¹' (Set.range i))
    · constructor
      · exact IsOpen.preimage f.continuous hi.open_range
      · refine' IsClosed.preimage f.continuous _
        apply IsCompact.isClosed
        simp only [← Set.image_univ]
        exact IsCompact.image isCompact_univ i.continuous
    intro U hU
    dsimp at U
    have hU' : IsOpen (Subtype.val '' U) := h.1.openEmbedding_subtype_val.isOpenMap U hU
    have := ExtremallyDisconnected.open_closure _ hU'
    rw [h.2.closedEmbedding_subtype_val.closure_image_eq U] at this
    suffices hhU : closure U = Subtype.val ⁻¹' (Subtype.val '' (closure U))
    · rw [hhU]
      exact isOpen_induced this
    exact ((closure U).preimage_image_eq Subtype.coe_injective).symm

noncomputable
def OpenEmbedding.InvRange {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] {i : X → Y}
    (hi : OpenEmbedding i) : C(Set.range i, X) where
  toFun := (Homeomorph.ofEmbedding i hi.toEmbedding).invFun
  continuous_toFun := (Homeomorph.ofEmbedding i hi.toEmbedding).symm.continuous

noncomputable
def OpenEmbedding.ToRange {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] {i : X → Y}
    (hi : OpenEmbedding i) : C(X, Set.range i) where
  toFun := (Homeomorph.ofEmbedding i hi.toEmbedding).toFun
  continuous_toFun := (Homeomorph.ofEmbedding i hi.toEmbedding).continuous

lemma aux_forall_mem {X Y Z : Stonean} (f : X ⟶ Z) {i : Y ⟶ Z} (_ : OpenEmbedding i) :
    ∀ x : f ⁻¹' (Set.range i), f x.val ∈ Set.range i := by
  rintro ⟨x, hx⟩
  simpa only [Set.mem_preimage]

lemma aux_continuous_restrict {X Y Z : Stonean} (f : X ⟶ Z) {i : Y ⟶ Z} (_ : OpenEmbedding i) :
    Continuous ((f ⁻¹' (Set.range i)).restrict f) := by
  apply ContinuousOn.restrict
  apply Continuous.continuousOn
  exact f.continuous

noncomputable
def OpenEmbeddingConeRightMap {X Y Z : Stonean} (f : X ⟶ Z) {i : Y ⟶ Z} (hi : OpenEmbedding i) :
    C(f ⁻¹' (Set.range i), Y) :=
  ContinuousMap.comp (OpenEmbedding.InvRange hi)
  ⟨(Set.range i).codRestrict ((f ⁻¹' (Set.range i)).restrict f)
  (aux_forall_mem f hi), Continuous.codRestrict
  (aux_continuous_restrict f hi) (aux_forall_mem f hi)⟩

noncomputable
def OpenEmbeddingCone {X Y Z : Stonean} (f : X ⟶ Z) {i : Y ⟶ Z} (hi : OpenEmbedding i) :
    Cone (cospan f i) where
  pt := OpenEmbeddingConePt f hi
  π := {
    app := by
      intro W
      dsimp
      match W with
      | none =>
        exact ⟨Set.restrict _ f, ContinuousOn.restrict (Continuous.continuousOn f.continuous)⟩
      | some W' =>
        · induction W' with
        | left =>
          · exact ⟨Subtype.val, continuous_subtype_val⟩
        | right =>
          · exact OpenEmbeddingConeRightMap f hi
    naturality := by
      intro W V q
      simp only [CategoryTheory.Functor.const_obj_obj,
        CategoryTheory.Functor.const_obj_map, cospan_one,
        cospan_left, id_eq, Category.id_comp]
      induction q with
      | id =>
        · simp only [cospan_one, cospan_left, WidePullbackShape.hom_id,
            CategoryTheory.Functor.map_id, Category.comp_id]
      | term j =>
        · induction j with
          | left =>
            · simp only [cospan_one, cospan_left, cospan_map_inl]
              congr
          | right =>
            · simp only [cospan_one, cospan_right, cospan_map_inr]
              dsimp [OpenEmbeddingConeRightMap, ContinuousMap.comp, Set.restrict, Set.codRestrict,
                OpenEmbedding.InvRange]
              congr
              ext x
              simp only [Function.comp_apply]
              obtain ⟨y, hy⟩ := x.prop
              rw [← hy]
              congr
              suffices : y = (Homeomorph.ofEmbedding i hi.toEmbedding).symm
                (⟨f x.val, by rw [← hy] ; simp⟩)
              · rw [this]
                rfl
              apply_fun (Homeomorph.ofEmbedding i hi.toEmbedding)
              simp only [Homeomorph.apply_symm_apply]
              dsimp [Homeomorph.ofEmbedding]
              simp_rw [hy]
  }

namespace Stonean

def pullback.fst {X Y Z : Stonean.{u}} (f : X ⟶ Z) {i : Y ⟶ Z}
    (hi : OpenEmbedding i) : (OpenEmbeddingCone f hi).pt ⟶ X :=
  ⟨Subtype.val, continuous_subtype_val⟩

noncomputable
def pullback.snd {X Y Z : Stonean.{u}} (f : X ⟶ Z) {i : Y ⟶ Z}
    (hi : OpenEmbedding i) : (OpenEmbeddingCone f hi).pt ⟶ Y :=
  (OpenEmbeddingCone f hi).π.app WalkingCospan.right

def pullback.lift {X Y Z W : Stonean} (f : X ⟶ Z) {i : Y ⟶ Z} (hi : OpenEmbedding i)
    (a : W ⟶ X) (b : W ⟶ Y) (w : a ≫ f = b ≫ i) :
    W ⟶ (OpenEmbeddingCone f hi).pt where
  toFun := fun z => ⟨a z, by
    simp only [Set.mem_preimage]
    use (b z)
    exact congr_fun (FunLike.ext'_iff.mp w.symm) z⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact a.continuous

lemma pullback.condition {X Y Z : Stonean.{u}} (f : X ⟶ Z) {i : Y ⟶ Z}
    (hi : OpenEmbedding i) : pullback.fst f hi ≫ f = pullback.snd f hi ≫ i :=
  PullbackCone.condition (OpenEmbeddingCone f hi)

@[reassoc (attr := simp)]
lemma pullback.lift_fst {X Y Z W : Stonean} (f : X ⟶ Z) {i : Y ⟶ Z} (hi : OpenEmbedding i)
    (a : W ⟶ X) (b : W ⟶ Y) (w : a ≫ f = b ≫ i) :
  pullback.lift f hi a b w ≫ pullback.fst f hi = a := rfl

lemma pullback.lift_snd {X Y Z W : Stonean} (f : X ⟶ Z) {i : Y ⟶ Z} (hi : OpenEmbedding i)
    (a : W ⟶ X) (b : W ⟶ Y) (w : a ≫ f = b ≫ i) :
    pullback.lift f hi a b w ≫ Stonean.pullback.snd f hi = b := by
  dsimp [lift, snd, OpenEmbeddingCone, OpenEmbeddingConeRightMap, ContinuousMap.comp, Set.restrict,
    Set.codRestrict, OpenEmbedding.InvRange]
  congr
  ext z
  simp only [Function.comp_apply]
  have := congr_fun (FunLike.ext'_iff.mp w.symm) z
  have h : i (b z) = f (a z) := this
  suffices : b z = (Homeomorph.ofEmbedding i hi.toEmbedding).symm
    (⟨f (a z), by rw [← h] ; simp⟩)
  · exact this.symm
  apply_fun (Homeomorph.ofEmbedding i hi.toEmbedding)
  simp only [Homeomorph.apply_symm_apply]
  dsimp [Homeomorph.ofEmbedding]
  simp_rw [h]

lemma pullback.hom_ext {X Y Z W : Stonean} (f : X ⟶ Z) {i : Y ⟶ Z} (hi : OpenEmbedding i)
    (a : W ⟶ (OpenEmbeddingCone f hi).pt) (b : W ⟶ (OpenEmbeddingCone f hi).pt)
    (hfst : a ≫ pullback.fst f hi = b ≫ pullback.fst f hi) : a = b := by
  ext z
  apply_fun (fun q => q z) at hfst--  hsnd
  apply Subtype.ext
  exact hfst

def OpenEmbeddingLimitCone {X Y Z : Stonean.{u}} (f : X ⟶ Z) {i : Y ⟶ Z}
    (hi : OpenEmbedding i) : IsLimit (OpenEmbeddingCone f hi) :=
  Limits.PullbackCone.isLimitAux _
    (fun s => pullback.lift f hi s.fst s.snd s.condition)
    (fun _ => pullback.lift_fst _ _ _ _ _)
    (fun _ => pullback.lift_snd _ _ _ _ _)
    (fun _ _ hm => pullback.hom_ext _ _ _ _ (hm WalkingCospan.left))

lemma HasPullbackOpenEmbedding {X Y Z : Stonean.{u}} (f : X ⟶ Z) {i : Y ⟶ Z}
    (hi : OpenEmbedding i) : HasPullback f i := by
  constructor
  use OpenEmbeddingCone f hi
  exact Stonean.OpenEmbeddingLimitCone f hi

section Isos

variable {X Y Z : Stonean.{u}} (f : X ⟶ Z) {i : Y ⟶ Z}  (hi : OpenEmbedding i) [HasPullback f i]

noncomputable
def toExplicit : pullback f i ⟶ (OpenEmbeddingCone f hi).pt :=
  pullback.lift f hi Limits.pullback.fst Limits.pullback.snd Limits.pullback.condition

noncomputable
def fromExplicit : (OpenEmbeddingCone f hi).pt ⟶ pullback f i :=
  Limits.pullback.lift (pullback.fst _ hi) (pullback.snd _ hi) (pullback.condition f hi)

@[simp]
theorem toExplicitCompFromExcplict :
    (toExplicit f hi ≫ fromExplicit f hi) = 𝟙 _ := by
  refine' Limits.pullback.hom_ext (k := (toExplicit f hi ≫ fromExplicit f hi)) _ _
  · simp [toExplicit, fromExplicit]
  · rw [Category.id_comp, Category.assoc, fromExplicit, Limits.pullback.lift_snd,
      toExplicit, pullback.lift_snd]

@[simp]
theorem fromExcplictComptoExplicit :
    (fromExplicit f hi ≫ toExplicit f hi) = 𝟙 _ :=
  pullback.hom_ext f hi _ _ (by simp [toExplicit, fromExplicit])

@[simps]
noncomputable
def fromExplicitIso : (OpenEmbeddingCone f hi).pt ≅ pullback f i where
  hom := fromExplicit f hi
  inv := toExplicit f hi
  hom_inv_id := fromExcplictComptoExplicit f hi
  inv_hom_id := toExplicitCompFromExcplict f hi

end Isos

end Stonean

end StoneanPullback

section CompHausExplicitSheaves

open CategoryTheory CompHaus Opposite CategoryTheory.Limits Functor Presieve

namespace CompHaus

lemma extensivity_injective {α : Type} [Fintype α] {X : CompHaus.{u}}
    {Z : α → CompHaus.{u}} {π : (a : α) → Z a ⟶ X} {Y : CompHaus.{u}} (f : Y ⟶ X)
    (HIso : IsIso (finiteCoproduct.desc _ π)) :
    Function.Injective (finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))) := by
  let ζ := finiteCoproduct.desc _ (fun a => pullback.snd f (π a) ≫ finiteCoproduct.ι Z a )
  let σ := finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))
  let β := finiteCoproduct.desc _ π
  have comm : ζ ≫ β = σ ≫ f := by
     refine' finiteCoproduct.hom_ext _ _ _ (fun a => _)
     simp [← Category.assoc, finiteCoproduct.ι_desc, pullback.condition]
  intro R₁ R₂ hR
  have himage : (ζ ≫ β) R₁ = (ζ ≫ β) R₂ := by
    rw [comm]; change f (σ R₁) = f (σ R₂); rw [hR]
  replace himage := congr_arg (inv β) himage
  change ((ζ ≫ β ≫ inv β) R₁) = ((ζ ≫ β ≫ inv β) R₂) at himage
  rw [IsIso.hom_inv_id, Category.comp_id] at himage
  have Hfst : R₁.fst = R₂.fst := by
    suffices (ζ R₁).1 = R₁.1 ∧ (ζ R₂).1 = R₂.1 by
      · rw [← this.1, ← this.2, himage]
    constructor <;> rfl
  obtain ⟨a₁, r₁, h₁⟩ := finiteCoproduct.ι_jointly_surjective _ R₁
  obtain ⟨a₂, r₂, h₂⟩ := finiteCoproduct.ι_jointly_surjective _ R₂
  have ha₁ : a₁ = R₁.fst := (congrArg Sigma.fst h₁).symm
  have ha₂ : a₂ = R₂.fst := (congrArg Sigma.fst h₂).symm
  have ha : a₁ = a₂ := by rwa [ha₁, ha₂]
  have : R₁ ∈ Set.range (finiteCoproduct.ι _ a₂)
  · rw [← ha, h₁]
    simp only [Set.mem_range, exists_apply_eq_apply]
  obtain ⟨xr', hr'⟩ := this
  rw [← hr', h₂] at hR
  have hf : ∀ (a : α), Function.Injective
      ((finiteCoproduct.ι _ a) ≫ (finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))))
  · intro a
    simp only [finiteCoproduct.ι_desc]
    intro x y h
    have h₁ := h
    apply_fun f at h
    change (pullback.fst f (π a) ≫ f) x = _ at h
    have h' := h.symm
    change (pullback.fst f (π a) ≫ f) y = _ at h'
    rw [pullback.condition] at h'
    have : Function.Injective (π a)
    · intro r s hrs
      rw [← finiteCoproduct.ι_desc_apply] at hrs
      have hrs' := hrs.symm
      rw [← finiteCoproduct.ι_desc_apply] at hrs'
      have : Function.Injective (finiteCoproduct.desc (fun a ↦ Z a) π)
      · apply Function.Bijective.injective
        exact ConcreteCategory.bijective_of_isIso _
      exact (finiteCoproduct.ι_injective _ a (this hrs')).symm
    have h₂ := this h'
    suffices : x.val = y.val
    · exact Subtype.ext this
    exact Prod.ext h₁ h₂.symm
  have := hf a₂ hR
  rw [← hr', h₂, this]

lemma extensivity_explicit {α : Type} [Fintype α] {X : CompHaus.{u}}
    {Z : α → CompHaus.{u}} {π : (a : α) → Z a ⟶ X} {Y : CompHaus.{u}} (f : Y ⟶ X)
    (HIso : IsIso (finiteCoproduct.desc _ π)) :
     IsIso (finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))) := by
  let β := finiteCoproduct.desc _ π
  apply isIso_of_bijective _
  refine' ⟨extensivity_injective f HIso, fun y => _⟩
  refine' ⟨⟨(inv β (f y)).1, ⟨⟨y, (inv β (f y)).2⟩, _⟩⟩, rfl⟩
  have inj : Function.Injective (inv β) := by --this should be obvious
    intros r s hrs
    convert congr_arg β hrs <;> change _ = (inv β ≫ β) _<;> simp only [IsIso.inv_hom_id]<;> rfl
  apply inj
  suffices ∀ a, π a ≫ inv β = finiteCoproduct.ι _ a by
    · apply Eq.symm
      change (_ ≫ inv β) _ = _
      rw [this]
      rfl
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
    have HIso : IsIso (finiteCoproduct.desc _ i) := by
      suffices IsIso <| (coproductIsoCoproduct Z).inv ≫ (finiteCoproduct.desc _ i) by
        · apply IsIso.of_isIso_comp_left (coproductIsoCoproduct Z).inv
      convert H
      refine' Sigma.hom_ext _ _ (fun a => _)
      simp only [coproductIsoCoproduct, colimit.comp_coconePointUniqueUpToIso_inv_assoc,
        Discrete.functor_obj, finiteCoproduct.cocone_pt, finiteCoproduct.cocone_ι,
        Discrete.natTrans_app, finiteCoproduct.ι_desc, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
    convert extensivity_explicit f HIso
    refine' finiteCoproduct.hom_ext _ _ _ (fun a => _)
    rw [finiteCoproduct.ι_desc, ← Category.assoc, ← Sigma.ι_comp_toFiniteCoproduct]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, pullbackIsoPullback, mapIso_hom,
      colim_map, colimit.map_desc, colimit.ι_desc, Cocones.precompose_obj_pt, Cofan.mk_pt,
      Cocones.precompose_obj_ι, NatTrans.comp_app, Discrete.functor_obj, const_obj_obj,
      Discrete.natIso_hom_app, Cofan.mk_ι_app, limit.conePointUniqueUpToIso_hom_comp,
      pullback.cone_pt, pullback.cone_π]

instance : Regular CompHaus where
  exists_fac := by
    intro X Y Z f π hπ
    refine ⟨pullback f π, pullback.fst f π, ?_, pullback.snd f π, (pullback.condition _ _).symm⟩
    rw [CompHaus.effectiveEpi_iff_surjective] at hπ ⊢
    intro y
    obtain ⟨z,hz⟩ := hπ (f y)
    exact ⟨⟨(y, z), hz.symm⟩, rfl⟩

def MapToEqualizer (P : CompHaus.{u}ᵒᵖ ⥤ Type (u+1)) {W X B : CompHaus} (f : X ⟶ B)
    (g₁ g₂ : W ⟶ X) (w : g₁ ≫ f = g₂ ≫ f) :
    P.obj (op B) → { x : P.obj (op X) | P.map g₁.op x = P.map g₂.op x } :=
  fun t ↦ ⟨P.map f.op t, by
    change (P.map _ ≫ P.map _) _ = (P.map _ ≫ P.map _) _ ;
    simp_rw [← P.map_comp, ← op_comp, w] ⟩

def EqualizerCondition (P : CompHaus.{u}ᵒᵖ ⥤ Type (u+1)) : Prop := ∀
  (X B : CompHaus) (π : X ⟶ B) (_ : Function.Surjective π),
  Function.Bijective (MapToEqualizer P π (CompHaus.pullback.fst π π) (CompHaus.pullback.snd π π)
      (CompHaus.pullback.condition _ _))

noncomputable
def EqualizerFirstObjIso (F : CompHaus.{u}ᵒᵖ ⥤ Type (u+1)) {B X : CompHaus} (π : X ⟶ B)
     : Equalizer.FirstObj F (Presieve.singleton π) ≅ F.obj (op X) :=
  CategoryTheory.Equalizer.firstObjEqFamily F (Presieve.singleton π) ≪≫
  { hom := fun e ↦ e π (Presieve.singleton_self π)
    inv := fun e _ _ h ↦ by
      induction h with
      | mk => exact e
    hom_inv_id := by
      funext _ _ _ h
      induction h with
      | mk => rfl
    inv_hom_id := by aesop }

noncomputable
def EqualizerSecondObjIso_aux (F : CompHaus.{u}ᵒᵖ ⥤ Type (u+1)) {B X : CompHaus} (π : X ⟶ B) :
    Equalizer.Presieve.SecondObj F (Presieve.singleton π) ≅ F.obj (op (Limits.pullback π π)) :=
  Types.productIso.{u+1, u+1} _ ≪≫
  { hom := fun e ↦ e (⟨X, ⟨π, Presieve.singleton_self π⟩⟩, ⟨X, ⟨π, Presieve.singleton_self π⟩⟩)
    inv := fun x ⟨⟨_, ⟨_, h₁⟩⟩ , ⟨_, ⟨_, h₂⟩⟩⟩ ↦ by
      induction h₁
      induction h₂
      exact x
    hom_inv_id := by
      funext _ ⟨⟨_, ⟨_, h₁⟩⟩ , ⟨_, ⟨_, h₂⟩⟩⟩
      induction h₁
      induction h₂
      rfl
    inv_hom_id := by aesop }

noncomputable
def EqualizerSecondObjIso (F : CompHaus.{u}ᵒᵖ ⥤ Type (u+1)) {B X : CompHaus} (π : X ⟶ B) :
    Equalizer.Presieve.SecondObj F (Presieve.singleton π) ≅ F.obj (op (CompHaus.pullback π π)) :=
  EqualizerSecondObjIso_aux F π ≪≫ (F.mapIso ((pullbackIsoPullback π π).op :
    op (Limits.pullback π π) ≅ op (CompHaus.pullback π π)))

lemma isSheafFor_of_Dagur {B : CompHaus} {S : Presieve B}
    (hS : S ∈ ((extensiveCoverage CompHaus).union (regularCoverage CompHaus)).covering B)
    {F : CompHaus.{u}ᵒᵖ ⥤ Type (u+1)} [PreservesFiniteProducts F]
    (hFecs : EqualizerCondition F) :
    S.IsSheafFor F := by
  cases' hS with hSIso hSSingle
  · simp only [extensiveCoverage, Set.mem_setOf_eq] at hSIso
    haveI : S.extensive := ⟨hSIso⟩
    exact isSheafFor_extensive_of_preservesFiniteProducts S F
  · rw [Equalizer.Presieve.sheaf_condition, Limits.Types.type_equalizer_iff_unique]
    intro y h
    simp only [regularCoverage, Set.mem_setOf_eq] at hSSingle
    obtain ⟨X, π, ⟨hS, πsurj⟩⟩ := hSSingle
    rw [Presieve.ofArrows_pUnit] at hS
    subst hS
    rw [CompHaus.effectiveEpi_iff_surjective] at πsurj
    specialize hFecs X B π πsurj
    have fork_comp : Equalizer.forkMap F (Presieve.singleton π) ≫ (EqualizerFirstObjIso F π).hom =
        F.map π.op
    · dsimp [EqualizerFirstObjIso, Equalizer.forkMap]
      ext b
      simp only [types_comp_apply, Equalizer.firstObjEqFamily_hom, Types.pi_lift_π_apply]
    have fmap_comp : (EqualizerFirstObjIso F π).hom ≫ F.map (pullback.fst π π).op =
        Equalizer.Presieve.firstMap F (Presieve.singleton π) ≫ (EqualizerSecondObjIso F π).hom
    · dsimp [EqualizerSecondObjIso]
      have : CompHaus.pullback.fst π π = (pullbackIsoPullback π π).hom ≫ Limits.pullback.fst
      · simp only [pullbackIsoPullback, limit.conePointUniqueUpToIso_hom_comp, pullback.cone_pt,
          pullback.cone_π]
      rw [this, op_comp, Functor.map_comp]
      suffices : (EqualizerFirstObjIso F π).hom ≫ F.map Limits.pullback.fst.op =
          Equalizer.Presieve.firstMap F (Presieve.singleton π) ≫
          (EqualizerSecondObjIso_aux F π).hom
      · simp only [← Category.assoc]
        rw [this]
      dsimp [EqualizerFirstObjIso, Equalizer.Presieve.firstMap, EqualizerSecondObjIso_aux]
      ext b
      simp only [types_comp_apply, Equalizer.firstObjEqFamily_hom, Types.pi_lift_π_apply]
    have smap_comp : (EqualizerFirstObjIso F π).hom ≫ F.map (pullback.snd π π).op =
        Equalizer.Presieve.secondMap F (Presieve.singleton π) ≫ (EqualizerSecondObjIso F π).hom
    · dsimp [EqualizerSecondObjIso]
      have : CompHaus.pullback.snd π π = (pullbackIsoPullback π π).hom ≫ Limits.pullback.snd
      · simp only [pullbackIsoPullback, limit.conePointUniqueUpToIso_hom_comp, pullback.cone_pt,
          pullback.cone_π]
      rw [this, op_comp, Functor.map_comp]
      suffices : (EqualizerFirstObjIso F π).hom ≫ F.map Limits.pullback.snd.op =
          Equalizer.Presieve.secondMap F (Presieve.singleton π) ≫
          (EqualizerSecondObjIso_aux F π).hom
      · simp only [← Category.assoc]
        rw [this]
      dsimp [EqualizerFirstObjIso, Equalizer.Presieve.secondMap, EqualizerSecondObjIso_aux]
      ext b
      simp only [types_comp_apply, Equalizer.firstObjEqFamily_hom, Types.pi_lift_π_apply]
    have iy_mem : F.map (pullback.fst π π).op ((EqualizerFirstObjIso F π).hom y) =
        F.map (pullback.snd π π).op ((EqualizerFirstObjIso F π).hom y)
    · change ((EqualizerFirstObjIso F π).hom ≫ _) y = _
      apply Eq.symm -- how do I avoid this ugly hack?
      change ((EqualizerFirstObjIso F π).hom ≫ _) y = _
      rw [fmap_comp, smap_comp]
      dsimp
      rw [h]
    have uniq_F : ∃! x, F.map π.op x = (EqualizerFirstObjIso F π).hom y
    · rw [Function.bijective_iff_existsUnique] at hFecs
      specialize hFecs ⟨(EqualizerFirstObjIso F π).hom y, iy_mem⟩
      obtain ⟨x, hx⟩ := hFecs
      refine' ⟨x, _⟩
      dsimp [MapToEqualizer] at *
      refine' ⟨Subtype.ext_iff.mp hx.1,_⟩
      intro z hz
      apply hx.2
      rwa [Subtype.ext_iff]
    obtain ⟨x,hx⟩ := uniq_F
    dsimp at hx
    rw [← fork_comp] at hx
    use x
    dsimp
    constructor
    · apply_fun (EqualizerFirstObjIso F π).hom
      · exact hx.1
      · apply Function.Bijective.injective
        rw [← isIso_iff_bijective]
        exact inferInstance
    · intro z hz
      apply_fun (EqualizerFirstObjIso F π).hom at hz
      exact hx.2 z hz

instance {A B : Type*} [Category A] [Category B] (F : B ⥤ A) (E : A)  [PreservesFiniteProducts F] :
    PreservesFiniteProducts (F ⋙ coyoneda.obj (op E)) :=
  ⟨fun J _ ↦ @compPreservesLimitsOfShape _ _ _ _ _ _ _ _ F (coyoneda.obj (op E))
    (PreservesFiniteProducts.preserves J) ((preservesLimitsOfSizeShrink _).preservesLimitsOfShape)⟩

theorem final (A : Type (u+2)) [Category.{u+1} A] {F : CompHaus.{u}ᵒᵖ ⥤ A}
    [PreservesFiniteProducts F]
    (hF' : ∀ (E : A), EqualizerCondition (F ⋙ coyoneda.obj (op E))) :
  Presheaf.IsSheaf (coherentTopology CompHaus) F := by
  rw [← extensive_union_regular_generates_coherent]
  refine' fun E => (Presieve.isSheaf_coverage _ _).2 _
  intro B S hS
  exact isSheafFor_of_Dagur hS (hF' E)

theorem final' (A : Type (u+2)) [Category.{u+1} A] {G : A ⥤ Type (u+1)}
    [HasLimits A] [PreservesLimits G] [ReflectsIsomorphisms G] {F : CompHaus.{u}ᵒᵖ ⥤ A}
    [PreservesFiniteProducts (F ⋙ G)] (hF' : EqualizerCondition (F ⋙ G)) :
    Presheaf.IsSheaf (coherentTopology CompHaus) F := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (coherentTopology CompHaus) F G,
    isSheaf_iff_isSheaf_of_type, ← extensive_union_regular_generates_coherent,
    Presieve.isSheaf_coverage]
  intro B S' hS
  exact isSheafFor_of_Dagur hS hF'

end CompHaus

end CompHausExplicitSheaves

section ProfiniteExplicitSheaves

open CategoryTheory Profinite Opposite CategoryTheory.Limits Functor Presieve

namespace Profinite

lemma extensivity_injective {α : Type} [Fintype α] {X : Profinite.{u}}
    {Z : α → Profinite.{u}} {π : (a : α) → Z a ⟶ X} {Y : Profinite.{u}} (f : Y ⟶ X)
    (HIso : IsIso (finiteCoproduct.desc _ π)) :
    Function.Injective (finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))) := by
  let ζ := finiteCoproduct.desc _ (fun a => pullback.snd f (π a) ≫ finiteCoproduct.ι Z a )
  let σ := finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))
  let β := finiteCoproduct.desc _ π
  have comm : ζ ≫ β = σ ≫ f := by
     refine' finiteCoproduct.hom_ext _ _ _ (fun a => _)
     simp [← Category.assoc, finiteCoproduct.ι_desc, pullback.condition]
  intro R₁ R₂ hR
  have himage : (ζ ≫ β) R₁ = (ζ ≫ β) R₂ := by
    rw [comm]; change f (σ R₁) = f (σ R₂); rw [hR]
  replace himage := congr_arg (inv β) himage
  change ((ζ ≫ β ≫ inv β) R₁) = ((ζ ≫ β ≫ inv β) R₂) at himage
  rw [IsIso.hom_inv_id, Category.comp_id] at himage
  have Hfst : R₁.fst = R₂.fst := by
    suffices (ζ R₁).1 = R₁.1 ∧ (ζ R₂).1 = R₂.1 by
      · rw [← this.1, ← this.2, himage]
    constructor <;> rfl
  obtain ⟨a₁, r₁, h₁⟩ := finiteCoproduct.ι_jointly_surjective _ R₁
  obtain ⟨a₂, r₂, h₂⟩ := finiteCoproduct.ι_jointly_surjective _ R₂
  have ha₁ : a₁ = R₁.fst := (congrArg Sigma.fst h₁).symm
  have ha₂ : a₂ = R₂.fst := (congrArg Sigma.fst h₂).symm
  have ha : a₁ = a₂ := by rwa [ha₁, ha₂]
  have : R₁ ∈ Set.range (finiteCoproduct.ι _ a₂)
  · rw [← ha, h₁]
    simp only [Set.mem_range, exists_apply_eq_apply]
  obtain ⟨xr', hr'⟩ := this
  rw [← hr', h₂] at hR
  have hf : ∀ (a : α), Function.Injective
      ((finiteCoproduct.ι _ a) ≫ (finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))))
  · intro a
    simp only [finiteCoproduct.ι_desc]
    intro x y h
    have h₁ := h
    apply_fun f at h
    change (pullback.fst f (π a) ≫ f) x = _ at h
    have h' := h.symm
    change (pullback.fst f (π a) ≫ f) y = _ at h'
    rw [pullback.condition] at h'
    have : Function.Injective (π a)
    · intro r s hrs
      rw [← finiteCoproduct.ι_desc_apply] at hrs
      have hrs' := hrs.symm
      rw [← finiteCoproduct.ι_desc_apply] at hrs'
      have : Function.Injective (finiteCoproduct.desc (fun a ↦ Z a) π)
      · apply Function.Bijective.injective
        exact ConcreteCategory.bijective_of_isIso _
      exact (finiteCoproduct.ι_injective _ a (this hrs')).symm
    have h₂ := this h'
    suffices : x.val = y.val
    · exact Subtype.ext this
    exact Prod.ext h₁ h₂.symm
  have := hf a₂ hR
  rw [← hr', h₂, this]

lemma extensivity_explicit {α : Type} [Fintype α] {X : Profinite.{u}}
    {Z : α → Profinite.{u}} {π : (a : α) → Z a ⟶ X} {Y : Profinite.{u}} (f : Y ⟶ X)
    (HIso : IsIso (finiteCoproduct.desc _ π)) :
     IsIso (finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))) := by
  let β := finiteCoproduct.desc _ π
  apply isIso_of_bijective _
  refine' ⟨extensivity_injective f HIso, fun y => _⟩
  refine' ⟨⟨(inv β (f y)).1, ⟨⟨y, (inv β (f y)).2⟩, _⟩⟩, rfl⟩
  have inj : Function.Injective (inv β) := by --this should be obvious
    intros r s hrs
    convert congr_arg β hrs <;> change _ = (inv β ≫ β) _<;> simp only [IsIso.inv_hom_id]<;> rfl
  apply inj
  suffices ∀ a, π a ≫ inv β = finiteCoproduct.ι _ a by
    · apply Eq.symm
      change (_ ≫ inv β) _ = _
      rw [this]
      rfl
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
    have HIso : IsIso (finiteCoproduct.desc _ i) := by
      suffices IsIso <| (coproductIsoCoproduct Z).inv ≫ (finiteCoproduct.desc _ i) by
        · apply IsIso.of_isIso_comp_left (coproductIsoCoproduct Z).inv
      convert H
      refine' Sigma.hom_ext _ _ (fun a => _)
      simp only [coproductIsoCoproduct, colimit.comp_coconePointUniqueUpToIso_inv_assoc,
        Discrete.functor_obj, finiteCoproduct.cocone_pt, finiteCoproduct.cocone_ι,
        Discrete.natTrans_app, finiteCoproduct.ι_desc, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
    convert extensivity_explicit f HIso
    refine' finiteCoproduct.hom_ext _ _ _ (fun a => _)
    rw [finiteCoproduct.ι_desc, ← Category.assoc, ← Sigma.ι_comp_toFiniteCoproduct]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, pullbackIsoPullback, mapIso_hom,
      colim_map, colimit.map_desc, colimit.ι_desc, Cocones.precompose_obj_pt, Cofan.mk_pt,
      Cocones.precompose_obj_ι, NatTrans.comp_app, Discrete.functor_obj, const_obj_obj,
      Discrete.natIso_hom_app, Cofan.mk_ι_app, limit.conePointUniqueUpToIso_hom_comp,
      pullback.cone_pt, pullback.cone_π]

instance : Regular Profinite where
  exists_fac := by
    intro X Y Z f π hπ
    refine ⟨pullback f π, pullback.fst f π, ?_, pullback.snd f π, (pullback.condition _ _).symm⟩
    rw [Profinite.effectiveEpi_iff_surjective] at hπ ⊢
    intro y
    obtain ⟨z,hz⟩ := hπ (f y)
    exact ⟨⟨(y, z), hz.symm⟩, rfl⟩

def MapToEqualizer (P : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) {W X B : Profinite} (f : X ⟶ B)
    (g₁ g₂ : W ⟶ X) (w : g₁ ≫ f = g₂ ≫ f) :
    P.obj (op B) → { x : P.obj (op X) | P.map g₁.op x = P.map g₂.op x } :=
  fun t ↦ ⟨P.map f.op t, by
    change (P.map _ ≫ P.map _) _ = (P.map _ ≫ P.map _) _ ;
    simp_rw [← P.map_comp, ← op_comp, w] ⟩

def EqualizerCondition (P : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) : Prop := ∀
  (X B : Profinite) (π : X ⟶ B) (_ : Function.Surjective π),
  Function.Bijective (MapToEqualizer P π (Profinite.pullback.fst π π) (Profinite.pullback.snd π π)
      (Profinite.pullback.condition _ _))

noncomputable
def EqualizerFirstObjIso (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) {B X : Profinite} (π : X ⟶ B)
     : Equalizer.FirstObj F (Presieve.singleton π) ≅ F.obj (op X) :=
  CategoryTheory.Equalizer.firstObjEqFamily F (Presieve.singleton π) ≪≫
  { hom := fun e ↦ e π (Presieve.singleton_self π)
    inv := fun e _ _ h ↦ by
      induction h with
      | mk => exact e
    hom_inv_id := by
      funext _ _ _ h
      induction h with
      | mk => rfl
    inv_hom_id := by aesop }

noncomputable
def EqualizerSecondObjIso_aux (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) {B X : Profinite} (π : X ⟶ B) :
    Equalizer.Presieve.SecondObj F (Presieve.singleton π) ≅ F.obj (op (Limits.pullback π π)) :=
  Types.productIso.{u+1, u+1} _ ≪≫
  { hom := fun e ↦ e (⟨X, ⟨π, Presieve.singleton_self π⟩⟩, ⟨X, ⟨π, Presieve.singleton_self π⟩⟩)
    inv := fun x ⟨⟨_, ⟨_, h₁⟩⟩ , ⟨_, ⟨_, h₂⟩⟩⟩ ↦ by
      induction h₁
      induction h₂
      exact x
    hom_inv_id := by
      funext _ ⟨⟨_, ⟨_, h₁⟩⟩ , ⟨_, ⟨_, h₂⟩⟩⟩
      induction h₁
      induction h₂
      rfl
    inv_hom_id := by aesop }

noncomputable
def EqualizerSecondObjIso (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) {B X : Profinite} (π : X ⟶ B) :
    Equalizer.Presieve.SecondObj F (Presieve.singleton π) ≅ F.obj (op (Profinite.pullback π π)) :=
  EqualizerSecondObjIso_aux F π ≪≫ (F.mapIso ((pullbackIsoPullback π π).op :
    op (Limits.pullback π π) ≅ op (Profinite.pullback π π)))

lemma isSheafFor_of_Dagur {B : Profinite} {S : Presieve B}
    (hS : S ∈ ((extensiveCoverage Profinite).union (regularCoverage Profinite)).covering B)
    {F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)} [PreservesFiniteProducts F]
    (hFecs : EqualizerCondition F) :
    S.IsSheafFor F := by
  cases' hS with hSIso hSSingle
  · simp only [extensiveCoverage, Set.mem_setOf_eq] at hSIso
    haveI : S.extensive := ⟨hSIso⟩
    exact isSheafFor_extensive_of_preservesFiniteProducts S F
  · rw [Equalizer.Presieve.sheaf_condition, Limits.Types.type_equalizer_iff_unique]
    intro y h
    simp only [regularCoverage, Set.mem_setOf_eq] at hSSingle
    obtain ⟨X, π, ⟨hS, πsurj⟩⟩ := hSSingle
    rw [Presieve.ofArrows_pUnit] at hS
    subst hS
    rw [Profinite.effectiveEpi_iff_surjective] at πsurj
    specialize hFecs X B π πsurj
    have fork_comp : Equalizer.forkMap F (Presieve.singleton π) ≫ (EqualizerFirstObjIso F π).hom =
        F.map π.op
    · dsimp [EqualizerFirstObjIso, Equalizer.forkMap]
      ext b
      simp only [types_comp_apply, Equalizer.firstObjEqFamily_hom, Types.pi_lift_π_apply]
    have fmap_comp : (EqualizerFirstObjIso F π).hom ≫ F.map (pullback.fst π π).op =
        Equalizer.Presieve.firstMap F (Presieve.singleton π) ≫ (EqualizerSecondObjIso F π).hom
    · dsimp [EqualizerSecondObjIso]
      have : Profinite.pullback.fst π π = (pullbackIsoPullback π π).hom ≫ Limits.pullback.fst
      · simp only [pullbackIsoPullback, limit.conePointUniqueUpToIso_hom_comp, pullback.cone_pt,
          pullback.cone_π]
      rw [this, op_comp, Functor.map_comp]
      suffices : (EqualizerFirstObjIso F π).hom ≫ F.map Limits.pullback.fst.op =
          Equalizer.Presieve.firstMap F (Presieve.singleton π) ≫
          (EqualizerSecondObjIso_aux F π).hom
      · simp only [← Category.assoc]
        rw [this]
      dsimp [EqualizerFirstObjIso, Equalizer.Presieve.firstMap, EqualizerSecondObjIso_aux]
      ext b
      simp only [types_comp_apply, Equalizer.firstObjEqFamily_hom, Types.pi_lift_π_apply]
    have smap_comp : (EqualizerFirstObjIso F π).hom ≫ F.map (pullback.snd π π).op =
        Equalizer.Presieve.secondMap F (Presieve.singleton π) ≫ (EqualizerSecondObjIso F π).hom
    · dsimp [EqualizerSecondObjIso]
      have : Profinite.pullback.snd π π = (pullbackIsoPullback π π).hom ≫ Limits.pullback.snd
      · simp only [pullbackIsoPullback, limit.conePointUniqueUpToIso_hom_comp, pullback.cone_pt,
          pullback.cone_π]
      rw [this, op_comp, Functor.map_comp]
      suffices : (EqualizerFirstObjIso F π).hom ≫ F.map Limits.pullback.snd.op =
          Equalizer.Presieve.secondMap F (Presieve.singleton π) ≫
          (EqualizerSecondObjIso_aux F π).hom
      · simp only [← Category.assoc]
        rw [this]
      dsimp [EqualizerFirstObjIso, Equalizer.Presieve.secondMap, EqualizerSecondObjIso_aux]
      ext b
      simp only [types_comp_apply, Equalizer.firstObjEqFamily_hom, Types.pi_lift_π_apply]
    have iy_mem : F.map (pullback.fst π π).op ((EqualizerFirstObjIso F π).hom y) =
        F.map (pullback.snd π π).op ((EqualizerFirstObjIso F π).hom y)
    · change ((EqualizerFirstObjIso F π).hom ≫ _) y = _
      apply Eq.symm -- how do I avoid this ugly hack?
      change ((EqualizerFirstObjIso F π).hom ≫ _) y = _
      rw [fmap_comp, smap_comp]
      dsimp
      rw [h]
    have uniq_F : ∃! x, F.map π.op x = (EqualizerFirstObjIso F π).hom y
    · rw [Function.bijective_iff_existsUnique] at hFecs
      specialize hFecs ⟨(EqualizerFirstObjIso F π).hom y, iy_mem⟩
      obtain ⟨x, hx⟩ := hFecs
      refine' ⟨x, _⟩
      dsimp [MapToEqualizer] at *
      refine' ⟨Subtype.ext_iff.mp hx.1,_⟩
      intro z hz
      apply hx.2
      rwa [Subtype.ext_iff]
    obtain ⟨x,hx⟩ := uniq_F
    dsimp at hx
    rw [← fork_comp] at hx
    use x
    dsimp
    constructor
    · apply_fun (EqualizerFirstObjIso F π).hom
      · exact hx.1
      · apply Function.Bijective.injective
        rw [← isIso_iff_bijective]
        exact inferInstance
    · intro z hz
      apply_fun (EqualizerFirstObjIso F π).hom at hz
      exact hx.2 z hz

theorem final (A : Type (u+2)) [Category.{u+1} A] {F : Profinite.{u}ᵒᵖ ⥤ A}
    [PreservesFiniteProducts F]
    (hF' : ∀ (E : A), EqualizerCondition (F ⋙ coyoneda.obj (op E))) :
  Presheaf.IsSheaf (coherentTopology Profinite) F := by
  rw [← extensive_union_regular_generates_coherent]
  refine' fun E => (Presieve.isSheaf_coverage _ _).2 _
  intro B S hS
  exact isSheafFor_of_Dagur hS (hF' E)

theorem final' (A : Type (u+2)) [Category.{u+1} A] {G : A ⥤ Type (u+1)}
    [HasLimits A] [PreservesLimits G] [ReflectsIsomorphisms G]
    {F : Profinite.{u}ᵒᵖ ⥤ A}
    [PreservesFiniteProducts (F ⋙ G)] (hF' : EqualizerCondition (F ⋙ G)) :
    Presheaf.IsSheaf (coherentTopology Profinite) F := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (coherentTopology Profinite) F G,
    isSheaf_iff_isSheaf_of_type, ← extensive_union_regular_generates_coherent,
    Presieve.isSheaf_coverage]
  intro B S' hS
  exact isSheafFor_of_Dagur hS hF'

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

lemma isIso_of_bijective {X Y : Stonean.{u}} {f : X ⟶ Y} (hf : Function.Bijective f) : IsIso f := by
  suffices IsIso <| toCompHaus.map f by
    · apply isIso_of_fully_faithful toCompHaus
  exact CompHaus.isIso_of_bijective _ hf

lemma extensivity_injective {α : Type} [Fintype α] {X : Stonean.{u}}
    {Z : α → Stonean.{u}} {π : (a : α) → Z a ⟶ X} {Y : Stonean.{u}} (f : Y ⟶ X)
    (HIso : IsIso (finiteCoproduct.desc _ π)) (hOpen : ∀ a, OpenEmbedding (π a)) :
    Function.Injective (finiteCoproduct.desc _ ((fun a => pullback.fst f (hOpen a)))) := by
  let ζ := finiteCoproduct.desc _ (fun a => pullback.snd f (hOpen a) ≫ finiteCoproduct.ι Z a )
  let α := finiteCoproduct.desc _ ((fun a => pullback.fst f (hOpen a)))
  let β := finiteCoproduct.desc _ π
  have comm : ζ ≫ β = α ≫ f := by
     refine' finiteCoproduct.hom_ext _ _ _ (fun a => _)
     simp [← Category.assoc, finiteCoproduct.ι_desc, Stonean.pullback.condition]
  intro R₁ R₂ hR
  have himage : (ζ ≫ β) R₁ = (ζ ≫ β) R₂ := by
    rw [comm]; change f (α R₁) = f (α R₂); rw [hR]
  replace himage := congr_arg (inv β) himage
  change ((ζ ≫ β ≫ inv β) R₁) = ((ζ ≫ β ≫ inv β) R₂) at himage
  rw [IsIso.hom_inv_id, Category.comp_id] at himage
  have Hfst : R₁.fst = R₂.fst := by
    suffices (ζ R₁).1 = R₁.1 ∧ (ζ R₂).1 = R₂.1 by
      · rw [← this.1, ← this.2, himage]
    constructor <;> rfl
  exact Sigma.subtype_ext Hfst hR

lemma extensivity_explicit {α : Type} [Fintype α] {X : Stonean.{u}}
    {Z : α → Stonean.{u}} {π : (a : α) → Z a ⟶ X} {Y : Stonean.{u}} (f : Y ⟶ X)
    (HIso : IsIso (finiteCoproduct.desc _ π)) (hOpen : ∀ a, OpenEmbedding (π a)) :
     IsIso (finiteCoproduct.desc _ ((fun a => pullback.fst f (hOpen a)))) := by
  let β := finiteCoproduct.desc _ π
  refine' isIso_of_bijective ⟨extensivity_injective f HIso hOpen, fun y => _⟩
  refine' ⟨⟨(inv β (f y)).1, ⟨y, (inv β (f y)).2, _⟩⟩, rfl⟩
  have inj : Function.Injective (inv β) := by --this should be obvious
    intros r s hrs
    convert congr_arg β hrs <;> change _ = (inv β ≫ β) _<;> simp only [IsIso.inv_hom_id]<;> rfl
  apply inj
  suffices ∀ a, π a ≫ inv β = finiteCoproduct.ι _ a by
    · change (_ ≫ inv β) _ = _
      rw [this]
      rfl
  intro a
  simp only [IsIso.comp_inv_eq, finiteCoproduct.ι_desc]

theorem Sigma.ι_comp_toFiniteCoproduct {α : Type} [Fintype α] {Z : α → Stonean.{u}} (a : α) :
    (Limits.Sigma.ι Z a) ≫ (coproductIsoCoproduct Z).inv = finiteCoproduct.ι Z a := by
  simp only [coproductIsoCoproduct, colimit.comp_coconePointUniqueUpToIso_inv,
    finiteCoproduct.explicitCocone_pt, finiteCoproduct.explicitCocone_ι, Discrete.natTrans_app]

instance : Extensive Stonean where
  sigma_desc_iso := @fun α _ X Z i Y f H => by
    have hOpen := openEmbedding_of_sigma_desc_iso H
    let θ := Sigma.mapIso (fun a => fromExplicitIso f (hOpen a))
    suffices IsIso (θ.hom ≫ Sigma.desc fun x => Limits.pullback.fst) by
      · apply IsIso.of_isIso_comp_left θ.hom
    let δ := coproductIsoCoproduct (fun a => (OpenEmbeddingCone f (hOpen a)).pt)
    suffices IsIso <| δ.hom ≫ (θ.hom ≫ Sigma.desc fun x => Limits.pullback.fst) by
      · apply IsIso.of_isIso_comp_left δ.hom
    have HIso : IsIso (finiteCoproduct.desc _ i) := by
      suffices IsIso <| (coproductIsoCoproduct Z).inv ≫ (finiteCoproduct.desc _ i) by
        · apply IsIso.of_isIso_comp_left (coproductIsoCoproduct Z).inv
      convert H
      refine' Sigma.hom_ext _ _ (fun a => _)
      simp only [coproductIsoCoproduct, colimit.comp_coconePointUniqueUpToIso_inv_assoc, Discrete.functor_obj,
        finiteCoproduct.explicitCocone_pt, finiteCoproduct.explicitCocone_ι, Discrete.natTrans_app,
        finiteCoproduct.ι_desc, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
    convert extensivity_explicit f HIso hOpen
    refine' Stonean.finiteCoproduct.hom_ext _ _ _ (fun a => _)
    rw [finiteCoproduct.ι_desc, ← Category.assoc, ← Sigma.ι_comp_toFiniteCoproduct]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, fromExplicitIso, fromExplicit._eq_1,
      mapIso_hom, colim_map, colimit.map_desc, Eq.ndrec, id_eq, colimit.ι_desc,
      Cocones.precompose_obj_pt, Cofan.mk_pt, Cocones.precompose_obj_ι, NatTrans.comp_app,
      Discrete.functor_obj, const_obj_obj, Discrete.natIso_hom_app, Cofan.mk_ι_app,
      limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]

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

instance : Regular Stonean where
  exists_fac := by
    intro X Y Z f π hπ
    exact ⟨X, 𝟙 X, inferInstance, Projective.factors f π⟩

lemma isSheafForRegularSieve {X : Stonean} (S : Presieve X) [S.regular]
    (F : Stonean.{u}ᵒᵖ ⥤ Type (u+1)) : IsSheafFor F S := by
  obtain ⟨Y, f, rfl, hf⟩ := Presieve.regular.single_epi (R := S)
  have proj : Projective (toCompHaus.obj X) := inferInstanceAs (Projective X.compHaus)
  have : Epi (toCompHaus.map f) := by
    rw [CompHaus.epi_iff_surjective]
    change Function.Surjective f
    rwa [← Stonean.effectiveEpi_iff_surjective]
  set g := toCompHaus.preimage <| Projective.factorThru (𝟙 _) (toCompHaus.map f) with hg
  have hfg : g ≫ f = 𝟙 _ := by
    refine' toCompHaus.map_injective _
    rw [map_comp, hg, image_preimage, Projective.factorThru_comp, CategoryTheory.Functor.map_id]
  intro y hy
  refine' ⟨F.map g.op <| y f <| ofArrows.mk (), fun Z h hZ => _, fun z hz => _⟩
  · cases' hZ with u
    have := hy (f₁ := f) (f₂ := f) (𝟙 Y) (f ≫ g) (ofArrows.mk ()) (ofArrows.mk ()) ?_
    · rw [op_id, F.map_id, types_id_apply] at this
      rw [← types_comp_apply (F.map g.op) (F.map f.op), ← F.map_comp, ← op_comp]
      exact this.symm
    · rw [Category.id_comp, Category.assoc, hfg, Category.comp_id]
  · have := congr_arg (F.map g.op) <| hz f (ofArrows.mk ())
    rwa [← types_comp_apply (F.map f.op) (F.map g.op), ← F.map_comp, ← op_comp, hfg, op_id,
      F.map_id, types_id_apply] at this

lemma isSheafFor_of_extensiveRegular {X : Stonean} {S : Presieve X}
  (hS : S ∈ ((extensiveCoverage Stonean).union (regularCoverage Stonean)).covering X)
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
  rw [← extensive_union_regular_generates_coherent]
  exact fun E => (Presieve.isSheaf_coverage _ _).2 <| fun S hS => isSheafFor_of_extensiveRegular hS

end Stonean

end StoneanExplicitSheaves
