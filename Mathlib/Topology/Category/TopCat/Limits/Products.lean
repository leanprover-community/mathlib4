/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro, Andrew Yang
-/
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.ConcreteCategory
import Mathlib.Data.Set.Subsingleton
import Mathlib.Tactic.CategoryTheory.Elementwise

#align_import topology.category.Top.limits.products from "leanprover-community/mathlib"@"178a32653e369dce2da68dc6b2694e385d484ef1"

/-!
# Products and coproducts in the category of topological spaces
-/

-- Porting note: every ML3 decl has an uppercase letter
set_option linter.uppercaseLean3 false

open TopologicalSpace

open CategoryTheory

open CategoryTheory.Limits

universe v u w

noncomputable section

namespace TopCat

variable {J : Type v} [SmallCategory J]

/-- The projection from the product as a bundled continuous map. -/
abbrev piπ {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) : TopCat.of (∀ i, α i) ⟶ α i :=
  ⟨fun f => f i, continuous_apply i⟩
#align Top.pi_π TopCat.piπ

/-- The explicit fan of a family of topological spaces given by the pi type. -/
@[simps! pt π_app]
def piFan {ι : Type v} (α : ι → TopCat.{max v u}) : Fan α :=
  Fan.mk (TopCat.of (∀ i, α i)) (piπ.{v,u} α)
#align Top.pi_fan TopCat.piFan

/-- The constructed fan is indeed a limit -/
def piFanIsLimit {ι : Type v} (α : ι → TopCat.{max v u}) : IsLimit (piFan α) where
  lift S :=
    { toFun := fun s i => S.π.app ⟨i⟩ s
      continuous_toFun := continuous_pi (fun i => (S.π.app ⟨i⟩).2) }
  uniq := by
    intro S m h
    apply ContinuousMap.ext; intro x
    funext i
    set_option tactic.skipAssignedInstances false in
    dsimp
    rw [ContinuousMap.coe_mk, ← h ⟨i⟩]
    rfl
  fac s j := rfl
#align Top.pi_fan_is_limit TopCat.piFanIsLimit

/-- The product is homeomorphic to the product of the underlying spaces,
equipped with the product topology.
-/
def piIsoPi {ι : Type v} (α : ι → TopCat.{max v u}) : ∏ᶜ α ≅ TopCat.of (∀ i, α i) :=
  (limit.isLimit _).conePointUniqueUpToIso (piFanIsLimit.{v, u} α)
  -- Specifying the universes in `piFanIsLimit` wasn't necessary when we had `TopCatMax` 
#align Top.pi_iso_pi TopCat.piIsoPi

@[reassoc (attr := simp)]
theorem piIsoPi_inv_π {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) :
    (piIsoPi α).inv ≫ Pi.π α i = piπ α i := by simp [piIsoPi]
#align Top.pi_iso_pi_inv_π TopCat.piIsoPi_inv_π

theorem piIsoPi_inv_π_apply {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) (x : ∀ i, α i) :
    (Pi.π α i : _) ((piIsoPi α).inv x) = x i :=
  ConcreteCategory.congr_hom (piIsoPi_inv_π α i) x
#align Top.pi_iso_pi_inv_π_apply TopCat.piIsoPi_inv_π_apply

-- Porting note: needing the type ascription on `∏ᶜ α : TopCat.{max v u}` is unfortunate.
theorem piIsoPi_hom_apply {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι)
    (x : (∏ᶜ α : TopCat.{max v u})) : (piIsoPi α).hom x i = (Pi.π α i : _) x := by
  have := piIsoPi_inv_π α i
  rw [Iso.inv_comp_eq] at this
  exact ConcreteCategory.congr_hom this x
#align Top.pi_iso_pi_hom_apply TopCat.piIsoPi_hom_apply

-- Porting note: Lean doesn't automatically reduce TopCat.of X|>.α to X now
/-- The inclusion to the coproduct as a bundled continuous map. -/
abbrev sigmaι {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) : α i ⟶ TopCat.of (Σi, α i) := by
  refine ContinuousMap.mk ?_ ?_
  · dsimp
    apply Sigma.mk i
  · dsimp; continuity
#align Top.sigma_ι TopCat.sigmaι

/-- The explicit cofan of a family of topological spaces given by the sigma type. -/
@[simps! pt ι_app]
def sigmaCofan {ι : Type v} (α : ι → TopCat.{max v u}) : Cofan α :=
  Cofan.mk (TopCat.of (Σi, α i)) (sigmaι α)
#align Top.sigma_cofan TopCat.sigmaCofan

/-- The constructed cofan is indeed a colimit -/
def sigmaCofanIsColimit {ι : Type v} (β : ι → TopCat.{max v u}) : IsColimit (sigmaCofan β) where
  desc S :=
    { toFun := fun (s : of (Σ i, β i)) => S.ι.app ⟨s.1⟩ s.2
      continuous_toFun := continuous_sigma fun i => (S.ι.app ⟨i⟩).continuous_toFun }
  uniq := by
    intro S m h
    ext ⟨i, x⟩
    simp only [hom_apply, ← h]
    congr
  fac s j := by
    cases j
    aesop_cat
#align Top.sigma_cofan_is_colimit TopCat.sigmaCofanIsColimit

/-- The coproduct is homeomorphic to the disjoint union of the topological spaces.
-/
def sigmaIsoSigma {ι : Type v} (α : ι → TopCat.{max v u}) : ∐ α ≅ TopCat.of (Σi, α i) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (sigmaCofanIsColimit.{v, u} α)
  -- Specifying the universes in `sigmaCofanIsColimit` wasn't necessary when we had `TopCatMax` 
#align Top.sigma_iso_sigma TopCat.sigmaIsoSigma

@[reassoc (attr := simp)]
theorem sigmaIsoSigma_hom_ι {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) :
    Sigma.ι α i ≫ (sigmaIsoSigma α).hom = sigmaι α i := by simp [sigmaIsoSigma]
#align Top.sigma_iso_sigma_hom_ι TopCat.sigmaIsoSigma_hom_ι

theorem sigmaIsoSigma_hom_ι_apply {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) (x : α i) :
    (sigmaIsoSigma α).hom ((Sigma.ι α i : _) x) = Sigma.mk i x :=
  ConcreteCategory.congr_hom (sigmaIsoSigma_hom_ι α i) x
#align Top.sigma_iso_sigma_hom_ι_apply TopCat.sigmaIsoSigma_hom_ι_apply

theorem sigmaIsoSigma_inv_apply {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) (x : α i) :
    (sigmaIsoSigma α).inv ⟨i, x⟩ = (Sigma.ι α i : _) x := by
  rw [← sigmaIsoSigma_hom_ι_apply, ← comp_app, ← comp_app, Iso.hom_inv_id,
    Category.comp_id]
#align Top.sigma_iso_sigma_inv_apply TopCat.sigmaIsoSigma_inv_apply

-- Porting note: cannot use .topologicalSpace in place .str
theorem induced_of_isLimit {F : J ⥤ TopCat.{max v u}} (C : Cone F) (hC : IsLimit C) :
    C.pt.str = ⨅ j, (F.obj j).str.induced (C.π.app j) := by
  let homeo := homeoOfIso (hC.conePointUniqueUpToIso (limitConeInfiIsLimit F))
  refine homeo.inducing.induced.trans ?_
  change induced homeo (⨅ j : J, _) = _
  simp [induced_iInf, induced_compose]
  rfl
#align Top.induced_of_is_limit TopCat.induced_of_isLimit

theorem limit_topology (F : J ⥤ TopCat.{max v u}) :
    (limit F).str = ⨅ j, (F.obj j).str.induced (limit.π F j) :=
  induced_of_isLimit _ (limit.isLimit F)
#align Top.limit_topology TopCat.limit_topology

section Prod

-- Porting note: why is autoParam not firing?
/-- The first projection from the product. -/
abbrev prodFst {X Y : TopCat.{u}} : TopCat.of (X × Y) ⟶ X :=
  ⟨Prod.fst, by continuity⟩
#align Top.prod_fst TopCat.prodFst

/-- The second projection from the product. -/
abbrev prodSnd {X Y : TopCat.{u}} : TopCat.of (X × Y) ⟶ Y :=
  ⟨Prod.snd, by continuity⟩
#align Top.prod_snd TopCat.prodSnd

/-- The explicit binary cofan of `X, Y` given by `X × Y`. -/
def prodBinaryFan (X Y : TopCat.{u}) : BinaryFan X Y :=
  BinaryFan.mk prodFst prodSnd
#align Top.prod_binary_fan TopCat.prodBinaryFan

/-- The constructed binary fan is indeed a limit -/
def prodBinaryFanIsLimit (X Y : TopCat.{u}) : IsLimit (prodBinaryFan X Y) where
  lift := fun S : BinaryFan X Y => {
    toFun := fun s => (S.fst s, S.snd s)
    -- Porting note: continuity failed again here. Lean cannot infer
    -- ContinuousMapClass (X ⟶ Y) X Y for X Y : TopCat which may be one of the problems
    continuous_toFun := Continuous.prod_mk
      (BinaryFan.fst S).continuous_toFun (BinaryFan.snd S).continuous_toFun }
  fac := by
    rintro S (_ | _) <;> {dsimp; ext; rfl}
  uniq := by
    intro S m h
    -- Porting note: used to be `ext x`
    refine ContinuousMap.ext (fun (x : ↥(S.pt)) => Prod.ext ?_ ?_)
    · specialize h ⟨WalkingPair.left⟩
      apply_fun fun e => e x at h
      exact h
    · specialize h ⟨WalkingPair.right⟩
      apply_fun fun e => e x at h
      exact h
#align Top.prod_binary_fan_is_limit TopCat.prodBinaryFanIsLimit

/-- The homeomorphism between `X ⨯ Y` and the set-theoretic product of `X` and `Y`,
equipped with the product topology.
-/
def prodIsoProd (X Y : TopCat.{u}) : X ⨯ Y ≅ TopCat.of (X × Y) :=
  (limit.isLimit _).conePointUniqueUpToIso (prodBinaryFanIsLimit X Y)
#align Top.prod_iso_prod TopCat.prodIsoProd

@[reassoc (attr := simp)]
theorem prodIsoProd_hom_fst (X Y : TopCat.{u}) :
    (prodIsoProd X Y).hom ≫ prodFst = Limits.prod.fst := by
  simp [← Iso.eq_inv_comp, prodIsoProd]
  rfl
#align Top.prod_iso_prod_hom_fst TopCat.prodIsoProd_hom_fst

@[reassoc (attr := simp)]
theorem prodIsoProd_hom_snd (X Y : TopCat.{u}) :
    (prodIsoProd X Y).hom ≫ prodSnd = Limits.prod.snd := by
  simp [← Iso.eq_inv_comp, prodIsoProd]
  rfl
#align Top.prod_iso_prod_hom_snd TopCat.prodIsoProd_hom_snd

-- Porting note: need to force Lean to coerce X × Y to a type
theorem prodIsoProd_hom_apply {X Y : TopCat.{u}} (x : ↑ (X ⨯ Y)) :
    (prodIsoProd X Y).hom x = ((Limits.prod.fst : X ⨯ Y ⟶ _) x,
    (Limits.prod.snd : X ⨯ Y ⟶ _) x) := by
  -- Porting note: ext didn't pick this up
  apply Prod.ext
  · exact ConcreteCategory.congr_hom (prodIsoProd_hom_fst X Y) x
  · exact ConcreteCategory.congr_hom (prodIsoProd_hom_snd X Y) x
#align Top.prod_iso_prod_hom_apply TopCat.prodIsoProd_hom_apply

@[reassoc (attr := simp), elementwise]
theorem prodIsoProd_inv_fst (X Y : TopCat.{u}) :
    (prodIsoProd X Y).inv ≫ Limits.prod.fst = prodFst := by simp [Iso.inv_comp_eq]
#align Top.prod_iso_prod_inv_fst TopCat.prodIsoProd_inv_fst

@[reassoc (attr := simp), elementwise]
theorem prodIsoProd_inv_snd (X Y : TopCat.{u}) :
    (prodIsoProd X Y).inv ≫ Limits.prod.snd = prodSnd := by simp [Iso.inv_comp_eq]
#align Top.prod_iso_prod_inv_snd TopCat.prodIsoProd_inv_snd

theorem prod_topology {X Y : TopCat.{u}} :
    (X ⨯ Y).str =
      induced (Limits.prod.fst : X ⨯ Y ⟶ _) X.str ⊓
        induced (Limits.prod.snd : X ⨯ Y ⟶ _) Y.str := by
  let homeo := homeoOfIso (prodIsoProd X Y)
  refine homeo.inducing.induced.trans ?_
  change induced homeo (_ ⊓ _) = _
  simp [induced_compose]
  rfl
#align Top.prod_topology TopCat.prod_topology

theorem range_prod_map {W X Y Z : TopCat.{u}} (f : W ⟶ Y) (g : X ⟶ Z) :
    Set.range (Limits.prod.map f g) =
      (Limits.prod.fst : Y ⨯ Z ⟶ _) ⁻¹' Set.range f ∩
        (Limits.prod.snd : Y ⨯ Z ⟶ _) ⁻¹' Set.range g := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp_rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_range]
    -- sizable changes in this proof after #13170
    erw  [← comp_apply, ← comp_apply]
    simp_rw [Limits.prod.map_fst,
      Limits.prod.map_snd, comp_apply]
    exact ⟨exists_apply_eq_apply _ _, exists_apply_eq_apply _ _⟩
  · rintro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
    use (prodIsoProd W X).inv (x₁, x₂)
    change (forget TopCat).map _ _ = _
    apply Concrete.limit_ext
    rintro ⟨⟨⟩⟩
    · change limit.π (pair Y Z) _ ((prod.map f g) _) = _
      erw [← comp_apply, Limits.prod.map_fst]
      change (_ ≫ _ ≫ f) _ = _
      erw [TopCat.prodIsoProd_inv_fst_assoc,TopCat.comp_app]
      exact hx₁
    · change limit.π (pair Y Z) _ ((prod.map f g) _) = _
      erw [← comp_apply, Limits.prod.map_snd]
      change (_ ≫ _ ≫ g) _ = _
      erw [TopCat.prodIsoProd_inv_snd_assoc,TopCat.comp_app]
      exact hx₂
#align Top.range_prod_map TopCat.range_prod_map

theorem inducing_prod_map {W X Y Z : TopCat.{u}} {f : W ⟶ X} {g : Y ⟶ Z} (hf : Inducing f)
    (hg : Inducing g) : Inducing (Limits.prod.map f g) := by
  constructor
  simp_rw [topologicalSpace_coe, prod_topology, induced_inf, induced_compose, ← coe_comp,
    prod.map_fst, prod.map_snd, coe_comp, ← induced_compose (g := f), ← induced_compose (g := g)]
  erw [← hf.induced, ← hg.induced] -- now `erw` after #13170
  rfl -- `rfl` was not needed before #13170
#align Top.inducing_prod_map TopCat.inducing_prod_map

theorem embedding_prod_map {W X Y Z : TopCat.{u}} {f : W ⟶ X} {g : Y ⟶ Z} (hf : Embedding f)
    (hg : Embedding g) : Embedding (Limits.prod.map f g) :=
  ⟨inducing_prod_map hf.toInducing hg.toInducing, by
    haveI := (TopCat.mono_iff_injective _).mpr hf.inj
    haveI := (TopCat.mono_iff_injective _).mpr hg.inj
    exact (TopCat.mono_iff_injective _).mp inferInstance⟩
#align Top.embedding_prod_map TopCat.embedding_prod_map

end Prod

/-- The binary coproduct cofan in `TopCat`. -/
protected def binaryCofan (X Y : TopCat.{u}) : BinaryCofan X Y :=
  BinaryCofan.mk (⟨Sum.inl, by continuity⟩ : X ⟶ TopCat.of (Sum X Y)) ⟨Sum.inr, by continuity⟩
#align Top.binary_cofan TopCat.binaryCofan

/-- The constructed binary coproduct cofan in `TopCat` is the coproduct. -/
def binaryCofanIsColimit (X Y : TopCat.{u}) : IsColimit (TopCat.binaryCofan X Y) := by
  refine Limits.BinaryCofan.isColimitMk (fun s =>
    {toFun := Sum.elim s.inl s.inr, continuous_toFun := ?_ }) ?_ ?_ ?_
  · apply
      Continuous.sum_elim (BinaryCofan.inl s).continuous_toFun (BinaryCofan.inr s).continuous_toFun
  · intro s
    ext
    rfl
  · intro s
    ext
    rfl
  · intro s m h₁ h₂
    ext (x | x)
    exacts [(ConcreteCategory.congr_hom h₁ x : _), (ConcreteCategory.congr_hom h₂ x : _)]
#align Top.binary_cofan_is_colimit TopCat.binaryCofanIsColimit

theorem binaryCofan_isColimit_iff {X Y : TopCat} (c : BinaryCofan X Y) :
    Nonempty (IsColimit c) ↔
      OpenEmbedding c.inl ∧ OpenEmbedding c.inr ∧ IsCompl (Set.range c.inl) (Set.range c.inr) := by
  classical
    constructor
    · rintro ⟨h⟩
      rw [← show _ = c.inl from
          h.comp_coconePointUniqueUpToIso_inv (binaryCofanIsColimit X Y) ⟨WalkingPair.left⟩,
        ← show _ = c.inr from
          h.comp_coconePointUniqueUpToIso_inv (binaryCofanIsColimit X Y) ⟨WalkingPair.right⟩]
      dsimp
      refine ⟨(homeoOfIso <| h.coconePointUniqueUpToIso
        (binaryCofanIsColimit X Y)).symm.openEmbedding.comp openEmbedding_inl,
          (homeoOfIso <| h.coconePointUniqueUpToIso
            (binaryCofanIsColimit X Y)).symm.openEmbedding.comp openEmbedding_inr, ?_⟩
      erw [Set.range_comp, ← eq_compl_iff_isCompl, Set.range_comp _ Sum.inr,
        ← Set.image_compl_eq (homeoOfIso <| h.coconePointUniqueUpToIso
            (binaryCofanIsColimit X Y)).symm.bijective, Set.compl_range_inr, Set.image_comp]
    · rintro ⟨h₁, h₂, h₃⟩
      have : ∀ x, x ∈ Set.range c.inl ∨ x ∈ Set.range c.inr := by
        rw [eq_compl_iff_isCompl.mpr h₃.symm]
        exact fun _ => or_not
      refine ⟨BinaryCofan.IsColimit.mk _ ?_ ?_ ?_ ?_⟩
      · intro T f g
        refine ContinuousMap.mk ?_ ?_
        · exact fun x =>
            if h : x ∈ Set.range c.inl then f ((Equiv.ofInjective _ h₁.inj).symm ⟨x, h⟩)
            else g ((Equiv.ofInjective _ h₂.inj).symm ⟨x, (this x).resolve_left h⟩)
        rw [continuous_iff_continuousAt]
        intro x
        by_cases h : x ∈ Set.range c.inl
        · revert h x
          apply (IsOpen.continuousOn_iff _).mp
          · rw [continuousOn_iff_continuous_restrict]
            convert_to Continuous (f ∘ (Homeomorph.ofEmbedding _ h₁.toEmbedding).symm)
            · ext ⟨x, hx⟩
              exact dif_pos hx
            apply Continuous.comp
            · exact f.continuous_toFun
            · continuity
          · exact h₁.isOpen_range
        · revert h x
          apply (IsOpen.continuousOn_iff _).mp
          · rw [continuousOn_iff_continuous_restrict]
            have : ∀ a, a ∉ Set.range c.inl → a ∈ Set.range c.inr := by
              rintro a (h : a ∈ (Set.range c.inl)ᶜ)
              rwa [eq_compl_iff_isCompl.mpr h₃.symm]
            convert_to Continuous
                (g ∘ (Homeomorph.ofEmbedding _ h₂.toEmbedding).symm ∘ Subtype.map _ this)
            · ext ⟨x, hx⟩
              exact dif_neg hx
            apply Continuous.comp
            · exact g.continuous_toFun
            · apply Continuous.comp
              · continuity
              · rw [embedding_subtype_val.toInducing.continuous_iff]
                exact continuous_subtype_val
          · change IsOpen (Set.range c.inl)ᶜ
            rw [← eq_compl_iff_isCompl.mpr h₃.symm]
            exact h₂.isOpen_range
      · intro T f g
        ext x
        refine (dif_pos ?_).trans ?_
        · exact ⟨x, rfl⟩
        · dsimp
          conv_lhs => erw [Equiv.ofInjective_symm_apply]
          rfl -- `rfl` was not needed here before #13170
      · intro T f g
        ext x
        refine (dif_neg ?_).trans ?_
        · rintro ⟨y, e⟩
          have : c.inr x ∈ Set.range c.inl ⊓ Set.range c.inr := ⟨⟨_, e⟩, ⟨_, rfl⟩⟩
          rwa [disjoint_iff.mp h₃.1] at this
        · exact congr_arg g (Equiv.ofInjective_symm_apply _ _)
      · rintro T _ _ m rfl rfl
        ext x
        change m x = dite _ _ _
        split_ifs <;> exact congr_arg _ (Equiv.apply_ofInjective_symm _ ⟨_, _⟩).symm
#align Top.binary_cofan_is_colimit_iff TopCat.binaryCofan_isColimit_iff
