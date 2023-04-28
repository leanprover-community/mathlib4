/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro, Andrew Yang

! This file was ported from Lean 3 source module topology.category.Top.limits.products
! leanprover-community/mathlib commit 178a32653e369dce2da68dc6b2694e385d484ef1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Category.Top.EpiMono
import Mathbin.Topology.Category.Top.Limits.Basic

/-!
# Products and coproducts in the category of topological spaces

-/


open TopologicalSpace

open CategoryTheory

open CategoryTheory.Limits

universe u v w

noncomputable section

namespace TopCat

variable {J : Type v} [SmallCategory J]

/-- The projection from the product as a bundled continous map. -/
abbrev piπ {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) : TopCat.of (∀ i, α i) ⟶ α i :=
  ⟨fun f => f i, continuous_apply i⟩
#align Top.pi_π TopCat.piπ

/-- The explicit fan of a family of topological spaces given by the pi type. -/
@[simps pt π_app]
def piFan {ι : Type v} (α : ι → TopCat.{max v u}) : Fan α :=
  Fan.mk (TopCat.of (∀ i, α i)) (piπ α)
#align Top.pi_fan TopCat.piFan

/-- The constructed fan is indeed a limit -/
def piFanIsLimit {ι : Type v} (α : ι → TopCat.{max v u}) : IsLimit (piFan α)
    where
  lift S := { toFun := fun s i => S.π.app ⟨i⟩ s }
  uniq := by
    intro S m h
    ext (x i)
    simp [← h ⟨i⟩]
  fac s j := by
    cases j
    tidy
#align Top.pi_fan_is_limit TopCat.piFanIsLimit

/-- The product is homeomorphic to the product of the underlying spaces,
equipped with the product topology.
-/
def piIsoPi {ι : Type v} (α : ι → TopCat.{max v u}) : ∏ α ≅ TopCat.of (∀ i, α i) :=
  (limit.isLimit _).conePointUniqueUpToIso (piFanIsLimit α)
#align Top.pi_iso_pi TopCat.piIsoPi

@[simp, reassoc.1]
theorem piIsoPi_inv_π {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) :
    (piIsoPi α).inv ≫ Pi.π α i = piπ α i := by simp [pi_iso_pi]
#align Top.pi_iso_pi_inv_π TopCat.piIsoPi_inv_π

@[simp]
theorem piIsoPi_inv_π_apply {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) (x : ∀ i, α i) :
    (Pi.π α i : _) ((piIsoPi α).inv x) = x i :=
  ConcreteCategory.congr_hom (piIsoPi_inv_π α i) x
#align Top.pi_iso_pi_inv_π_apply TopCat.piIsoPi_inv_π_apply

@[simp]
theorem piIsoPi_hom_apply {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) (x : ∏ α) :
    (piIsoPi α).Hom x i = (Pi.π α i : _) x :=
  by
  have := pi_iso_pi_inv_π α i
  rw [iso.inv_comp_eq] at this
  exact concrete_category.congr_hom this x
#align Top.pi_iso_pi_hom_apply TopCat.piIsoPi_hom_apply

/-- The inclusion to the coproduct as a bundled continous map. -/
abbrev sigmaι {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) : α i ⟶ TopCat.of (Σi, α i) :=
  ⟨Sigma.mk i⟩
#align Top.sigma_ι TopCat.sigmaι

/-- The explicit cofan of a family of topological spaces given by the sigma type. -/
@[simps pt ι_app]
def sigmaCofan {ι : Type v} (α : ι → TopCat.{max v u}) : Cofan α :=
  Cofan.mk (TopCat.of (Σi, α i)) (sigmaι α)
#align Top.sigma_cofan TopCat.sigmaCofan

/-- The constructed cofan is indeed a colimit -/
def sigmaCofanIsColimit {ι : Type v} (α : ι → TopCat.{max v u}) : IsColimit (sigmaCofan α)
    where
  desc S :=
    { toFun := fun s => S.ι.app ⟨s.1⟩ s.2
      continuous_toFun := continuous_sigma fun i => map_continuous (S.ι.app ⟨i⟩) }
  uniq := by
    intro S m h
    ext ⟨i, x⟩
    simp [← h ⟨i⟩]
  fac s j := by
    cases j
    tidy
#align Top.sigma_cofan_is_colimit TopCat.sigmaCofanIsColimit

/-- The coproduct is homeomorphic to the disjoint union of the topological spaces.
-/
def sigmaIsoSigma {ι : Type v} (α : ι → TopCat.{max v u}) : ∐ α ≅ TopCat.of (Σi, α i) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (sigmaCofanIsColimit α)
#align Top.sigma_iso_sigma TopCat.sigmaIsoSigma

@[simp, reassoc.1]
theorem sigmaIsoSigma_hom_ι {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) :
    Sigma.ι α i ≫ (sigmaIsoSigma α).Hom = sigmaι α i := by simp [sigma_iso_sigma]
#align Top.sigma_iso_sigma_hom_ι TopCat.sigmaIsoSigma_hom_ι

@[simp]
theorem sigmaIsoSigma_hom_ι_apply {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) (x : α i) :
    (sigmaIsoSigma α).Hom ((Sigma.ι α i : _) x) = Sigma.mk i x :=
  ConcreteCategory.congr_hom (sigmaIsoSigma_hom_ι α i) x
#align Top.sigma_iso_sigma_hom_ι_apply TopCat.sigmaIsoSigma_hom_ι_apply

@[simp]
theorem sigmaIsoSigma_inv_apply {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) (x : α i) :
    (sigmaIsoSigma α).inv ⟨i, x⟩ = (Sigma.ι α i : _) x :=
  by
  rw [← sigma_iso_sigma_hom_ι_apply, ← comp_app]
  simp
#align Top.sigma_iso_sigma_inv_apply TopCat.sigmaIsoSigma_inv_apply

theorem induced_of_isLimit {F : J ⥤ TopCat.{max v u}} (C : Cone F) (hC : IsLimit C) :
    C.pt.TopologicalSpace = ⨅ j, (F.obj j).TopologicalSpace.induced (C.π.app j) :=
  by
  let homeo := homeo_of_iso (hC.cone_point_unique_up_to_iso (limit_cone_infi_is_limit F))
  refine' homeo.inducing.induced.trans _
  change induced homeo (⨅ j : J, _) = _
  simpa [induced_infᵢ, induced_compose]
#align Top.induced_of_is_limit TopCat.induced_of_isLimit

theorem limit_topology (F : J ⥤ TopCat.{max v u}) :
    (limit F).TopologicalSpace = ⨅ j, (F.obj j).TopologicalSpace.induced (limit.π F j) :=
  induced_of_isLimit _ (limit.isLimit F)
#align Top.limit_topology TopCat.limit_topology

section Prod

/-- The first projection from the product. -/
abbrev prodFst {X Y : TopCat.{u}} : TopCat.of (X × Y) ⟶ X :=
  ⟨Prod.fst⟩
#align Top.prod_fst TopCat.prodFst

/-- The second projection from the product. -/
abbrev prodSnd {X Y : TopCat.{u}} : TopCat.of (X × Y) ⟶ Y :=
  ⟨Prod.snd⟩
#align Top.prod_snd TopCat.prodSnd

/-- The explicit binary cofan of `X, Y` given by `X × Y`. -/
def prodBinaryFan (X Y : TopCat.{u}) : BinaryFan X Y :=
  BinaryFan.mk prodFst prodSnd
#align Top.prod_binary_fan TopCat.prodBinaryFan

/-- The constructed binary fan is indeed a limit -/
def prodBinaryFanIsLimit (X Y : TopCat.{u}) : IsLimit (prodBinaryFan X Y)
    where
  lift := fun S : BinaryFan X Y => { toFun := fun s => (S.fst s, S.snd s) }
  fac := by
    rintro S (_ | _)
    tidy
  uniq := by
    intro S m h
    ext x
    · specialize h ⟨walking_pair.left⟩
      apply_fun fun e => e x  at h
      exact h
    · specialize h ⟨walking_pair.right⟩
      apply_fun fun e => e x  at h
      exact h
#align Top.prod_binary_fan_is_limit TopCat.prodBinaryFanIsLimit

/-- The homeomorphism between `X ⨯ Y` and the set-theoretic product of `X` and `Y`,
equipped with the product topology.
-/
def prodIsoProd (X Y : TopCat.{u}) : X ⨯ Y ≅ TopCat.of (X × Y) :=
  (limit.isLimit _).conePointUniqueUpToIso (prodBinaryFanIsLimit X Y)
#align Top.prod_iso_prod TopCat.prodIsoProd

@[simp, reassoc.1]
theorem prodIsoProd_hom_fst (X Y : TopCat.{u}) :
    (prodIsoProd X Y).Hom ≫ prodFst = Limits.prod.fst := by simpa [← iso.eq_inv_comp, prod_iso_prod]
#align Top.prod_iso_prod_hom_fst TopCat.prodIsoProd_hom_fst

@[simp, reassoc.1]
theorem prodIsoProd_hom_snd (X Y : TopCat.{u}) :
    (prodIsoProd X Y).Hom ≫ prodSnd = Limits.prod.snd := by simpa [← iso.eq_inv_comp, prod_iso_prod]
#align Top.prod_iso_prod_hom_snd TopCat.prodIsoProd_hom_snd

@[simp]
theorem prodIsoProd_hom_apply {X Y : TopCat.{u}} (x : X ⨯ Y) :
    (prodIsoProd X Y).Hom x = ((Limits.prod.fst : X ⨯ Y ⟶ _) x, (Limits.prod.snd : X ⨯ Y ⟶ _) x) :=
  by
  ext
  · exact concrete_category.congr_hom (prod_iso_prod_hom_fst X Y) x
  · exact concrete_category.congr_hom (prod_iso_prod_hom_snd X Y) x
#align Top.prod_iso_prod_hom_apply TopCat.prodIsoProd_hom_apply

@[simp, reassoc.1, elementwise]
theorem prodIsoProd_inv_fst (X Y : TopCat.{u}) :
    (prodIsoProd X Y).inv ≫ Limits.prod.fst = prodFst := by simp [iso.inv_comp_eq]
#align Top.prod_iso_prod_inv_fst TopCat.prodIsoProd_inv_fst

@[simp, reassoc.1, elementwise]
theorem prodIsoProd_inv_snd (X Y : TopCat.{u}) :
    (prodIsoProd X Y).inv ≫ Limits.prod.snd = prodSnd := by simp [iso.inv_comp_eq]
#align Top.prod_iso_prod_inv_snd TopCat.prodIsoProd_inv_snd

theorem prod_topology {X Y : TopCat} :
    (X ⨯ Y).TopologicalSpace =
      induced (Limits.prod.fst : X ⨯ Y ⟶ _) X.TopologicalSpace ⊓
        induced (Limits.prod.snd : X ⨯ Y ⟶ _) Y.TopologicalSpace :=
  by
  let homeo := homeo_of_iso (prod_iso_prod X Y)
  refine' homeo.inducing.induced.trans _
  change induced homeo (_ ⊓ _) = _
  simpa [induced_compose]
#align Top.prod_topology TopCat.prod_topology

theorem range_prod_map {W X Y Z : TopCat.{u}} (f : W ⟶ Y) (g : X ⟶ Z) :
    Set.range (Limits.prod.map f g) =
      (Limits.prod.fst : Y ⨯ Z ⟶ _) ⁻¹' Set.range f ∩
        (Limits.prod.snd : Y ⨯ Z ⟶ _) ⁻¹' Set.range g :=
  by
  ext
  constructor
  · rintro ⟨y, rfl⟩
    simp only [Set.mem_preimage, Set.mem_range, Set.mem_inter_iff, ← comp_apply]
    simp only [limits.prod.map_fst, limits.prod.map_snd, exists_apply_eq_apply, comp_apply,
      and_self_iff]
  · rintro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
    use (prod_iso_prod W X).inv (x₁, x₂)
    apply concrete.limit_ext
    rintro ⟨⟨⟩⟩
    · simp only [← comp_apply, category.assoc]
      erw [limits.prod.map_fst]
      simp [hx₁]
    · simp only [← comp_apply, category.assoc]
      erw [limits.prod.map_snd]
      simp [hx₂]
#align Top.range_prod_map TopCat.range_prod_map

theorem inducing_prod_map {W X Y Z : TopCat} {f : W ⟶ X} {g : Y ⟶ Z} (hf : Inducing f)
    (hg : Inducing g) : Inducing (Limits.prod.map f g) :=
  by
  constructor
  simp only [prod_topology, induced_compose, ← coe_comp, limits.prod.map_fst, limits.prod.map_snd,
    induced_inf]
  simp only [coe_comp]
  rw [← @induced_compose _ _ _ _ _ f, ← @induced_compose _ _ _ _ _ g, ← hf.induced, ← hg.induced]
#align Top.inducing_prod_map TopCat.inducing_prod_map

theorem embedding_prod_map {W X Y Z : TopCat} {f : W ⟶ X} {g : Y ⟶ Z} (hf : Embedding f)
    (hg : Embedding g) : Embedding (Limits.prod.map f g) :=
  ⟨inducing_prod_map hf.to_inducing hg.to_inducing,
    by
    haveI := (TopCat.mono_iff_injective _).mpr hf.inj
    haveI := (TopCat.mono_iff_injective _).mpr hg.inj
    exact (TopCat.mono_iff_injective _).mp inferInstance⟩
#align Top.embedding_prod_map TopCat.embedding_prod_map

end Prod

/-- The binary coproduct cofan in `Top`. -/
protected def binaryCofan (X Y : TopCat.{u}) : BinaryCofan X Y :=
  BinaryCofan.mk (⟨Sum.inl⟩ : X ⟶ TopCat.of (Sum X Y)) ⟨Sum.inr⟩
#align Top.binary_cofan TopCat.binaryCofan

/-- The constructed binary coproduct cofan in `Top` is the coproduct. -/
def binaryCofanIsColimit (X Y : TopCat.{u}) : IsColimit (TopCat.binaryCofan X Y) :=
  by
  refine' limits.binary_cofan.is_colimit_mk (fun s => ⟨Sum.elim s.inl s.inr⟩) _ _ _
  · intro s
    ext
    rfl
  · intro s
    ext
    rfl
  · intro s m h₁ h₂
    ext (x | x)
    exacts[(concrete_category.congr_hom h₁ x : _), (concrete_category.congr_hom h₂ x : _)]
#align Top.binary_cofan_is_colimit TopCat.binaryCofanIsColimit

theorem binaryCofan_isColimit_iff {X Y : TopCat} (c : BinaryCofan X Y) :
    Nonempty (IsColimit c) ↔
      OpenEmbedding c.inl ∧ OpenEmbedding c.inr ∧ IsCompl (Set.range c.inl) (Set.range c.inr) :=
  by
  classical
    constructor
    · rintro ⟨h⟩
      rw [←
        show _ = c.inl from
          h.comp_cocone_point_unique_up_to_iso_inv (binary_cofan_is_colimit X Y)
            ⟨walking_pair.left⟩,
        ←
        show _ = c.inr from
          h.comp_cocone_point_unique_up_to_iso_inv (binary_cofan_is_colimit X Y)
            ⟨walking_pair.right⟩]
      dsimp
      refine'
        ⟨(homeo_of_iso <|
                    h.cocone_point_unique_up_to_iso
                      (binary_cofan_is_colimit X Y)).symm.OpenEmbedding.comp
            openEmbedding_inl,
          (homeo_of_iso <|
                    h.cocone_point_unique_up_to_iso
                      (binary_cofan_is_colimit X Y)).symm.OpenEmbedding.comp
            openEmbedding_inr,
          _⟩
      erw [Set.range_comp, ← eq_compl_iff_isCompl, Set.range_comp _ Sum.inr, ←
        Set.image_compl_eq
          (homeo_of_iso <|
                h.cocone_point_unique_up_to_iso (binary_cofan_is_colimit X Y)).symm.Bijective]
      congr 1
      exact set.compl_range_inr.symm
    · rintro ⟨h₁, h₂, h₃⟩
      have : ∀ x, x ∈ Set.range c.inl ∨ x ∈ Set.range c.inr :=
        by
        rw [eq_compl_iff_is_compl.mpr h₃.symm]
        exact fun _ => or_not
      refine' ⟨binary_cofan.is_colimit.mk _ _ _ _ _⟩
      · intro T f g
        refine' ContinuousMap.mk _ _
        ·
          exact fun x =>
            if h : x ∈ Set.range c.inl then f ((Equiv.ofInjective _ h₁.inj).symm ⟨x, h⟩)
            else g ((Equiv.ofInjective _ h₂.inj).symm ⟨x, (this x).resolve_left h⟩)
        rw [continuous_iff_continuousAt]
        intro x
        by_cases x ∈ Set.range c.inl
        · revert h x
          apply (IsOpen.continuousOn_iff _).mp
          · rw [continuousOn_iff_continuous_restrict]
            convert_to Continuous (f ∘ (Homeomorph.ofEmbedding _ h₁.to_embedding).symm)
            · ext ⟨x, hx⟩
              exact dif_pos hx
            continuity
          · exact h₁.open_range
        · revert h x
          apply (IsOpen.continuousOn_iff _).mp
          · rw [continuousOn_iff_continuous_restrict]
            have : ∀ a, a ∉ Set.range c.inl → a ∈ Set.range c.inr :=
              by
              rintro a (h : a ∈ Set.range c.inlᶜ)
              rwa [eq_compl_iff_is_compl.mpr h₃.symm]
            convert_to Continuous
                (g ∘ (Homeomorph.ofEmbedding _ h₂.to_embedding).symm ∘ Subtype.map _ this)
            · ext ⟨x, hx⟩
              exact dif_neg hx
            continuity
            rw [embedding_subtype_coe.to_inducing.continuous_iff]
            exact continuous_subtype_val
          · change IsOpen (Set.range c.inlᶜ)
            rw [← eq_compl_iff_is_compl.mpr h₃.symm]
            exact h₂.open_range
      · intro T f g
        ext x
        refine' (dif_pos _).trans _
        · exact ⟨x, rfl⟩
        · rw [Equiv.ofInjective_symm_apply]
      · intro T f g
        ext x
        refine' (dif_neg _).trans _
        · rintro ⟨y, e⟩
          have : c.inr x ∈ Set.range c.inl ⊓ Set.range c.inr := ⟨⟨_, e⟩, ⟨_, rfl⟩⟩
          rwa [disjoint_iff.mp h₃.1] at this
        · exact congr_arg g (Equiv.ofInjective_symm_apply _ _)
      · rintro T _ _ m rfl rfl
        ext x
        change m x = dite _ _ _
        split_ifs <;> exact congr_arg _ (Equiv.apply_ofInjective_symm _ ⟨_, _⟩).symm
#align Top.binary_cofan_is_colimit_iff TopCat.binaryCofan_isColimit_iff

--TODO: Add analogous constructions for `pushout`.
end TopCat

