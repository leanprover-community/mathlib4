/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro, Andrew Yang

! This file was ported from Lean 3 source module topology.category.Top.limits
! leanprover-community/mathlib commit 8195826f5c428fc283510bc67303dd4472d78498
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Topology.Category.Top.EpiMono
import Mathlib.Topology.Category.Top.Limits.Basic

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

/-- The projection from the product as a bundled continous map. -/
abbrev piπ {ι : Type v} (α : ι → TopCatMax.{v, u}) (i : ι) : TopCat.of (∀ i, α i) ⟶ α i :=
  ⟨fun f => f i, continuous_apply i⟩
#align Top.pi_π TopCat.piπ

/-- The explicit fan of a family of topological spaces given by the pi type. -/
@[simps! pt π_app]
def piFan {ι : Type v} (α : ι → TopCatMax.{v, u}) : Fan α :=
  Fan.mk (TopCat.of (∀ i, α i)) (piπ.{v,u} α)
#align Top.pi_fan TopCat.piFan

/-- The constructed fan is indeed a limit -/
def piFanIsLimit {ι : Type v} (α : ι → TopCatMax.{v, u}) : IsLimit (piFan α) where
  lift S :=
    { toFun := fun s i => S.π.app ⟨i⟩ s
      continuous_toFun := continuous_pi (fun i => (S.π.app ⟨i⟩).2) }
  uniq := by
    intro S m h
    apply ContinuousMap.ext; intro x
    funext i
    dsimp
    rw [ContinuousMap.coe_mk, ← h ⟨i⟩]
    rfl
  fac s j := rfl
#align Top.pi_fan_is_limit TopCat.piFanIsLimit

/-- The product is homeomorphic to the product of the underlying spaces,
equipped with the product topology.
-/
def piIsoPi {ι : Type v} (α : ι → TopCatMax.{v, u}) :
  ∏ α ≅ TopCat.of (∀ i, α i) :=
  (limit.isLimit _).conePointUniqueUpToIso (piFanIsLimit α)
#align Top.pi_iso_pi TopCat.piIsoPi

@[reassoc (attr := simp)]
theorem piIsoPi_inv_π {ι : Type v} (α : ι → TopCatMax.{v, u}) (i : ι) :
    (piIsoPi α).inv ≫ Pi.π α i = piπ α i := by simp [piIsoPi]
#align Top.pi_iso_pi_inv_π TopCat.piIsoPi_inv_π

@[simp]
theorem piIsoPi_inv_π_apply {ι : Type v} (α : ι → TopCatMax.{v, u}) (i : ι) (x : ∀ i, α i) :
    (Pi.π α i : _) ((piIsoPi α).inv x) = x i :=
  ConcreteCategory.congr_hom (piIsoPi_inv_π α i) x
#align Top.pi_iso_pi_inv_π_apply TopCat.piIsoPi_inv_π_apply

-- Porting note: needing the type ascription on `∏ α : TopCatMax.{v, u}` is unfortunate.
@[simp]
theorem piIsoPi_hom_apply {ι : Type v} (α : ι → TopCatMax.{v, u}) (i : ι)
    (x : (∏ α : TopCatMax.{v, u})) : (piIsoPi α).hom x i = (Pi.π α i : _) x := by
  have := piIsoPi_inv_π α i
  rw [Iso.inv_comp_eq] at this
  exact ConcreteCategory.congr_hom this x
#align Top.pi_iso_pi_hom_apply TopCat.piIsoPi_hom_apply

-- Porting note: Lean doesn't automatically reduce TopCat.of X|>.α to X now
/-- The inclusion to the coproduct as a bundled continous map. -/
abbrev sigmaι {ι : Type v} (α : ι → TopCatMax.{v,u}) (i : ι) : α i ⟶ TopCat.of (Σi, α i) := by
  refine ContinuousMap.mk ?_ ?_
  · dsimp
    apply Sigma.mk i
  · dsimp; continuity
#align Top.sigma_ι TopCat.sigmaι

/-- The explicit cofan of a family of topological spaces given by the sigma type. -/
@[simps! pt ι_app]
def sigmaCofan {ι : Type v} (α : ι → TopCatMax.{v, u}) : Cofan α :=
  Cofan.mk (TopCat.of (Σi, α i)) (sigmaι α)
#align Top.sigma_cofan TopCat.sigmaCofan

/-- The constructed cofan is indeed a colimit -/
def sigmaCofanIsColimit {ι : Type v} (β : ι → TopCatMax.{v, u}) : IsColimit (sigmaCofan β) where
  desc S :=
    { toFun := fun (s : of (Σ i, β i)) => S.ι.app ⟨s.1⟩ s.2
      continuous_toFun := continuous_sigma fun i => (S.ι.app ⟨i⟩).continuous_toFun }
  uniq := by
    intro S m h
    ext ⟨i, x⟩
    simp only [comp_app,hom_apply,← h ⟨i⟩]
    congr
  fac s j := by
    cases j
    aesop_cat
#align Top.sigma_cofan_is_colimit TopCat.sigmaCofanIsColimit

/-- The coproduct is homeomorphic to the disjoint union of the topological spaces.
-/
def sigmaIsoSigma {ι : Type v} (α : ι → TopCatMax.{v, u}) : ∐ α ≅ TopCat.of (Σi, α i) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (sigmaCofanIsColimit α)
#align Top.sigma_iso_sigma TopCat.sigmaIsoSigma

@[reassoc (attr := simp)]
theorem sigmaIsoSigma_hom_ι {ι : Type v} (α : ι → TopCatMax.{v, u}) (i : ι) :
    Sigma.ι α i ≫ (sigmaIsoSigma α).hom = sigmaι α i := by simp [sigmaIsoSigma]
#align Top.sigma_iso_sigma_hom_ι TopCat.sigmaIsoSigma_hom_ι

@[simp]
theorem sigmaIsoSigma_hom_ι_apply {ι : Type v} (α : ι → TopCatMax.{v, u}) (i : ι) (x : α i) :
    (sigmaIsoSigma α).hom ((Sigma.ι α i : _) x) = Sigma.mk i x :=
  ConcreteCategory.congr_hom (sigmaIsoSigma_hom_ι α i) x
#align Top.sigma_iso_sigma_hom_ι_apply TopCat.sigmaIsoSigma_hom_ι_apply

@[simp]
theorem sigmaIsoSigma_inv_apply {ι : Type v} (α : ι → TopCatMax.{v, u}) (i : ι) (x : α i) :
    (sigmaIsoSigma α).inv ⟨i, x⟩ = (Sigma.ι α i : _) x := by
  rw [← sigmaIsoSigma_hom_ι_apply, ← comp_app]
  simp
#align Top.sigma_iso_sigma_inv_apply TopCat.sigmaIsoSigma_inv_apply

-- Porting note: cannot use .topologicalSpace in place .str
theorem induced_of_isLimit {F : J ⥤ TopCatMax.{v, u}} (C : Cone F) (hC : IsLimit C) :
    C.pt.str = ⨅ j, (F.obj j).str.induced (C.π.app j) := by
  let homeo := homeoOfIso (hC.conePointUniqueUpToIso (limitConeInfiIsLimit F))
  refine' homeo.inducing.induced.trans _
  change induced homeo (⨅ j : J, _) = _
  simp [induced_infᵢ, induced_compose]
  rfl
#align Top.induced_of_is_limit TopCat.induced_of_isLimit

theorem limit_topology (F : J ⥤ TopCatMax.{v, u}) :
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
    -- ContinuousMapClass (X ⟶  Y) X Y for X Y : TopCat which may be one of the problems
    continuous_toFun := (Continuous.prod_mk)
      (BinaryFan.fst S).continuous_toFun (BinaryFan.snd S).continuous_toFun }
  fac := by
    rintro S (_ | _) <;> {dsimp; ext; rfl}
  uniq := by
    intro S m h
    -- porting note: used to be `ext x`
    refine' ContinuousMap.ext (fun (x : ↥(S.pt)) => Prod.ext _ _)
    · specialize h ⟨WalkingPair.left⟩
      apply_fun fun e => e x  at h
      exact h
    · specialize h ⟨WalkingPair.right⟩
      apply_fun fun e => e x  at h
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
@[simp]
theorem prodIsoProd_hom_apply {X Y : TopCat.{u}} (x : ↑ (X ⨯ Y)) :
    (prodIsoProd X Y).hom x = ((Limits.prod.fst : X ⨯ Y ⟶ _) x, (Limits.prod.snd : X ⨯ Y ⟶ _) x) :=
  by
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

theorem prod_topology {X Y : TopCat} :
    (X ⨯ Y).str =
      induced (Limits.prod.fst : X ⨯ Y ⟶ _) X.str ⊓
        induced (Limits.prod.snd : X ⨯ Y ⟶ _) Y.str := by
  let homeo := homeoOfIso (prodIsoProd X Y)
  refine' homeo.inducing.induced.trans _
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
    simp only [Set.mem_preimage, Set.mem_range, Set.mem_inter_iff, ← comp_apply]
    simp only [Limits.prod.map_fst, Limits.prod.map_snd, exists_apply_eq_apply, comp_apply,
      and_self_iff]
  · rintro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
    use (prodIsoProd W X).inv (x₁, x₂)
    apply Concrete.limit_ext
    rintro ⟨⟨⟩⟩
    · simp only [← comp_apply, Category.assoc]
      erw [Limits.prod.map_fst]
      rw [TopCat.prodIsoProd_inv_fst_assoc,TopCat.comp_app]
      have : (forget TopCat).map prodFst (x₁, x₂) = x₁ := rfl
      rw [this, hx₁]
    · simp only [← comp_apply, Category.assoc]
      erw [Limits.prod.map_snd]
      rw [TopCat.prodIsoProd_inv_snd_assoc,TopCat.comp_app]
      have : (forget TopCat).map prodSnd (x₁, x₂) = x₂ := rfl
      rw [this, hx₂]
#align Top.range_prod_map TopCat.range_prod_map

-- Porting note: this is unpleasant because of topologicalSpace_forget had to be supplied
-- in Topology.Category.Top.Basic to get Lean to see through forget but now Lean cannot see
-- through topologicalSpace_forget
theorem inducing_prod_map {W X Y Z : TopCat} {f : W ⟶ X} {g : Y ⟶ Z} (hf : Inducing f)
    (hg : Inducing g) : Inducing (Limits.prod.map f g) := by
  constructor
  dsimp [topologicalSpace_forget, topologicalSpace_coe]
  simp only [prod_topology, induced_compose, ← coe_comp, Limits.prod.map_fst, Limits.prod.map_snd,
    induced_inf]
  simp only [coe_comp]
  have : (Z : TopCat) → topologicalSpace_forget Z = Z.str := fun _ => rfl
  rw [← this X, ← @induced_compose _ _ _ _ _ f, ←this Z, ← @induced_compose _ _ _ _ _ g, ← hf.induced, ← hg.induced]
  simp only [this]
#align Top.inducing_prod_map TopCat.inducing_prod_map

theorem embedding_prod_map {W X Y Z : TopCat} {f : W ⟶ X} {g : Y ⟶ Z} (hf : Embedding f)
    (hg : Embedding g) : Embedding (Limits.prod.map f g) :=
  ⟨inducing_prod_map hf.toInducing hg.toInducing, by
    haveI := (TopCat.mono_iff_injective _).mpr hf.inj
    haveI := (TopCat.mono_iff_injective _).mpr hg.inj
    exact (TopCat.mono_iff_injective _).mp inferInstance⟩
#align Top.embedding_prod_map TopCat.embedding_prod_map

end Prod
