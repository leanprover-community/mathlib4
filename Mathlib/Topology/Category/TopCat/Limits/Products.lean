/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro, Andrew Yang
-/
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.Topology.Category.TopCat.Limits.Basic

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
    -- ⊢ m = (fun S => ContinuousMap.mk fun s i => ↑(NatTrans.app S.π { as := i }) s) S
    apply ContinuousMap.ext; intro x
    -- ⊢ ∀ (a : ↑S.pt), ↑m a = ↑((fun S => ContinuousMap.mk fun s i => ↑(NatTrans.app …
                             -- ⊢ ↑m x = ↑((fun S => ContinuousMap.mk fun s i => ↑(NatTrans.app S.π { as := i  …
    funext i
    -- ⊢ ↑m x i = ↑((fun S => ContinuousMap.mk fun s i => ↑(NatTrans.app S.π { as :=  …
    dsimp
    -- ⊢ ↑m x i = ↑(ContinuousMap.mk fun s i => ↑(NatTrans.app S.π { as := i }) s) x i
    rw [ContinuousMap.coe_mk, ← h ⟨i⟩]
    -- ⊢ ↑m x i = ↑(m ≫ NatTrans.app (piFan α).π { as := i }) x
    rfl
    -- 🎉 no goals
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
                                               -- 🎉 no goals
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
  -- ⊢ ↑(piIsoPi α).hom x i = ↑(Pi.π α i) x
  rw [Iso.inv_comp_eq] at this
  -- ⊢ ↑(piIsoPi α).hom x i = ↑(Pi.π α i) x
  exact ConcreteCategory.congr_hom this x
  -- 🎉 no goals
#align Top.pi_iso_pi_hom_apply TopCat.piIsoPi_hom_apply

-- Porting note: Lean doesn't automatically reduce TopCat.of X|>.α to X now
/-- The inclusion to the coproduct as a bundled continuous map. -/
abbrev sigmaι {ι : Type v} (α : ι → TopCatMax.{v,u}) (i : ι) : α i ⟶ TopCat.of (Σi, α i) := by
  refine ContinuousMap.mk ?_ ?_
  -- ⊢ ↑(α i) → ↑(of ((i : ι) × ↑(α i)))
  · dsimp
    -- ⊢ ↑(α i) → (i : ι) × ↑(α i)
    apply Sigma.mk i
    -- 🎉 no goals
  · dsimp; continuity
    -- ⊢ Continuous (Sigma.mk i)
           -- 🎉 no goals
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
    -- ⊢ m = (fun S => ContinuousMap.mk fun s => ↑(NatTrans.app S.ι { as := s.fst })  …
    ext ⟨i, x⟩
    -- ⊢ ↑m { fst := i, snd := x } = ↑((fun S => ContinuousMap.mk fun s => ↑(NatTrans …
    simp only [comp_app,hom_apply,← h ⟨i⟩]
    -- ⊢ ContinuousMap.toFun m { fst := i, snd := x } = ContinuousMap.toFun (NatTrans …
    -- ⊢ NatTrans.app (sigmaCofan β).ι { as := as✝ } ≫ (fun S => ContinuousMap.mk fun …
    congr
    -- 🎉 no goals
    -- 🎉 no goals
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
                                                           -- 🎉 no goals
#align Top.sigma_iso_sigma_hom_ι TopCat.sigmaIsoSigma_hom_ι

@[simp]
theorem sigmaIsoSigma_hom_ι_apply {ι : Type v} (α : ι → TopCatMax.{v, u}) (i : ι) (x : α i) :
    (sigmaIsoSigma α).hom ((Sigma.ι α i : _) x) = Sigma.mk i x :=
  ConcreteCategory.congr_hom (sigmaIsoSigma_hom_ι α i) x
#align Top.sigma_iso_sigma_hom_ι_apply TopCat.sigmaIsoSigma_hom_ι_apply

@[simp]
theorem sigmaIsoSigma_inv_apply {ι : Type v} (α : ι → TopCatMax.{v, u}) (i : ι) (x : α i) :
    (sigmaIsoSigma α).inv ⟨i, x⟩ = (Sigma.ι α i : _) x := by
  rw [← sigmaIsoSigma_hom_ι_apply, ← comp_app, ←comp_app, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]
#align Top.sigma_iso_sigma_inv_apply TopCat.sigmaIsoSigma_inv_apply

-- Porting note: cannot use .topologicalSpace in place .str
theorem induced_of_isLimit {F : J ⥤ TopCatMax.{v, u}} (C : Cone F) (hC : IsLimit C) :
    C.pt.str = ⨅ j, (F.obj j).str.induced (C.π.app j) := by
  let homeo := homeoOfIso (hC.conePointUniqueUpToIso (limitConeInfiIsLimit F))
  -- ⊢ C.pt.str = ⨅ (j : J), induced (↑(NatTrans.app C.π j)) (F.obj j).str
  refine' homeo.inducing.induced.trans _
  -- ⊢ induced (↑homeo) (topologicalSpace_coe (limitConeInfi F).pt) = ⨅ (j : J), in …
  change induced homeo (⨅ j : J, _) = _
  -- ⊢ induced (↑homeo) (⨅ (j : J), induced (NatTrans.app (Types.limitCone (F ⋙ for …
  simp [induced_iInf, induced_compose]
  -- ⊢ ⨅ (i : J), induced (NatTrans.app (Types.limitCone (F ⋙ forget TopCat)).π i ∘ …
  rfl
  -- 🎉 no goals
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
                -- 🎉 no goals
#align Top.prod_fst TopCat.prodFst

/-- The second projection from the product. -/
abbrev prodSnd {X Y : TopCat.{u}} : TopCat.of (X × Y) ⟶ Y :=
  ⟨Prod.snd, by continuity⟩
                -- 🎉 no goals
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
    continuous_toFun := (Continuous.prod_mk)
      (BinaryFan.fst S).continuous_toFun (BinaryFan.snd S).continuous_toFun }
  fac := by
    rintro S (_ | _) <;> {dsimp; ext; rfl}
    -- ⊢ (fun S => ContinuousMap.mk fun s => (↑(BinaryFan.fst S) s, ↑(BinaryFan.snd S …
                         -- 🎉 no goals
                         -- 🎉 no goals
  uniq := by
    intro S m h
    -- ⊢ m = (fun S => ContinuousMap.mk fun s => (↑(BinaryFan.fst S) s, ↑(BinaryFan.s …
    -- porting note: used to be `ext x`
    refine' ContinuousMap.ext (fun (x : ↥(S.pt)) => Prod.ext _ _)
    -- ⊢ (↑m x).fst = (↑((fun S => ContinuousMap.mk fun s => (↑(BinaryFan.fst S) s, ↑ …
    · specialize h ⟨WalkingPair.left⟩
      -- ⊢ (↑m x).fst = (↑((fun S => ContinuousMap.mk fun s => (↑(BinaryFan.fst S) s, ↑ …
      apply_fun fun e => e x at h
      -- ⊢ (↑m x).fst = (↑((fun S => ContinuousMap.mk fun s => (↑(BinaryFan.fst S) s, ↑ …
      exact h
      -- 🎉 no goals
    · specialize h ⟨WalkingPair.right⟩
      -- ⊢ (↑m x).snd = (↑((fun S => ContinuousMap.mk fun s => (↑(BinaryFan.fst S) s, ↑ …
      apply_fun fun e => e x at h
      -- ⊢ (↑m x).snd = (↑((fun S => ContinuousMap.mk fun s => (↑(BinaryFan.fst S) s, ↑ …
      exact h
      -- 🎉 no goals
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
  -- ⊢ prodFst = BinaryFan.fst (prodBinaryFan X Y)
  rfl
  -- 🎉 no goals
#align Top.prod_iso_prod_hom_fst TopCat.prodIsoProd_hom_fst

@[reassoc (attr := simp)]
theorem prodIsoProd_hom_snd (X Y : TopCat.{u}) :
    (prodIsoProd X Y).hom ≫ prodSnd = Limits.prod.snd := by
  simp [← Iso.eq_inv_comp, prodIsoProd]
  -- ⊢ prodSnd = BinaryFan.snd (prodBinaryFan X Y)
  rfl
  -- 🎉 no goals
#align Top.prod_iso_prod_hom_snd TopCat.prodIsoProd_hom_snd

-- Porting note: need to force Lean to coerce X × Y to a type
@[simp]
theorem prodIsoProd_hom_apply {X Y : TopCat.{u}} (x : ↑ (X ⨯ Y)) :
    (prodIsoProd X Y).hom x = ((Limits.prod.fst : X ⨯ Y ⟶ _) x,
    (Limits.prod.snd : X ⨯ Y ⟶ _) x) := by
  -- Porting note: ext didn't pick this up
  apply Prod.ext
  -- ⊢ (↑(prodIsoProd X Y).hom x).fst = (↑prod.fst x, ↑prod.snd x).fst
  · exact ConcreteCategory.congr_hom (prodIsoProd_hom_fst X Y) x
    -- 🎉 no goals
  · exact ConcreteCategory.congr_hom (prodIsoProd_hom_snd X Y) x
    -- 🎉 no goals
#align Top.prod_iso_prod_hom_apply TopCat.prodIsoProd_hom_apply

@[reassoc (attr := simp), elementwise]
theorem prodIsoProd_inv_fst (X Y : TopCat.{u}) :
    (prodIsoProd X Y).inv ≫ Limits.prod.fst = prodFst := by simp [Iso.inv_comp_eq]
                                                            -- 🎉 no goals
#align Top.prod_iso_prod_inv_fst TopCat.prodIsoProd_inv_fst

@[reassoc (attr := simp), elementwise]
theorem prodIsoProd_inv_snd (X Y : TopCat.{u}) :
    (prodIsoProd X Y).inv ≫ Limits.prod.snd = prodSnd := by simp [Iso.inv_comp_eq]
                                                            -- 🎉 no goals
#align Top.prod_iso_prod_inv_snd TopCat.prodIsoProd_inv_snd

theorem prod_topology {X Y : TopCat.{u}} :
    (X ⨯ Y).str =
      induced (Limits.prod.fst : X ⨯ Y ⟶ _) X.str ⊓
        induced (Limits.prod.snd : X ⨯ Y ⟶ _) Y.str := by
  let homeo := homeoOfIso (prodIsoProd X Y)
  -- ⊢ (X ⨯ Y).str = induced (↑prod.fst) X.str ⊓ induced (↑prod.snd) Y.str
  refine' homeo.inducing.induced.trans _
  -- ⊢ induced (↑homeo) (topologicalSpace_coe (of (↑X × ↑Y))) = induced (↑prod.fst) …
  change induced homeo (_ ⊓ _) = _
  -- ⊢ induced (↑homeo) (induced Prod.fst (topologicalSpace_coe X) ⊓ induced Prod.s …
  simp [induced_compose]
  -- ⊢ induced (Prod.fst ∘ ↑(homeoOfIso (prodIsoProd X Y))) (topologicalSpace_coe X …
  rfl
  -- 🎉 no goals
#align Top.prod_topology TopCat.prod_topology

theorem range_prod_map {W X Y Z : TopCat.{u}} (f : W ⟶ Y) (g : X ⟶ Z) :
    Set.range (Limits.prod.map f g) =
      (Limits.prod.fst : Y ⨯ Z ⟶ _) ⁻¹' Set.range f ∩
        (Limits.prod.snd : Y ⨯ Z ⟶ _) ⁻¹' Set.range g := by
  ext x
  -- ⊢ x ∈ Set.range ↑(prod.map f g) ↔ x ∈ ↑prod.fst ⁻¹' Set.range ↑f ∩ ↑prod.snd ⁻ …
  constructor
  -- ⊢ x ∈ Set.range ↑(prod.map f g) → x ∈ ↑prod.fst ⁻¹' Set.range ↑f ∩ ↑prod.snd ⁻ …
  · rintro ⟨y, rfl⟩
    -- ⊢ ↑(prod.map f g) y ∈ ↑prod.fst ⁻¹' Set.range ↑f ∩ ↑prod.snd ⁻¹' Set.range ↑g
    simp only [Set.mem_preimage, Set.mem_range, Set.mem_inter_iff, ← comp_apply]
    -- ⊢ (∃ y_1, ↑f y_1 = ↑(prod.map f g ≫ prod.fst) y) ∧ ∃ y_1, ↑g y_1 = ↑(prod.map  …
    simp only [Limits.prod.map_fst, Limits.prod.map_snd, exists_apply_eq_apply, comp_apply,
      and_self_iff]
  · rintro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
    -- ⊢ x ∈ Set.range ↑(prod.map f g)
    use (prodIsoProd W X).inv (x₁, x₂)
    -- ⊢ ↑(prod.map f g) (↑(prodIsoProd W X).inv (x₁, x₂)) = x
    apply Concrete.limit_ext
    -- ⊢ ∀ (j : Discrete WalkingPair), ↑(limit.π (pair Y Z) j) (↑(prod.map f g) (↑(pr …
    rintro ⟨⟨⟩⟩
    -- ⊢ ↑(limit.π (pair Y Z) { as := WalkingPair.left }) (↑(prod.map f g) (↑(prodIso …
    · simp only [← comp_apply, Category.assoc]
      -- ⊢ ↑((prodIsoProd W X).inv ≫ prod.map f g ≫ limit.π (pair Y Z) { as := WalkingP …
      erw [Limits.prod.map_fst]
      -- ⊢ ↑((prodIsoProd W X).inv ≫ prod.fst ≫ f) (x₁, x₂) = ↑(limit.π (pair Y Z) { as …
      rw [TopCat.prodIsoProd_inv_fst_assoc,TopCat.comp_app]
      -- ⊢ ↑f (↑prodFst (x₁, x₂)) = ↑(limit.π (pair Y Z) { as := WalkingPair.left }) x
      exact hx₁
      -- 🎉 no goals
    · simp only [← comp_apply, Category.assoc]
      -- ⊢ ↑((prodIsoProd W X).inv ≫ prod.map f g ≫ limit.π (pair Y Z) { as := WalkingP …
      erw [Limits.prod.map_snd]
      -- ⊢ ↑((prodIsoProd W X).inv ≫ prod.snd ≫ g) (x₁, x₂) = ↑(limit.π (pair Y Z) { as …
      rw [TopCat.prodIsoProd_inv_snd_assoc,TopCat.comp_app]
      -- ⊢ ↑g (↑prodSnd (x₁, x₂)) = ↑(limit.π (pair Y Z) { as := WalkingPair.right }) x
      exact hx₂
      -- 🎉 no goals
#align Top.range_prod_map TopCat.range_prod_map

theorem inducing_prod_map {W X Y Z : TopCat.{u}} {f : W ⟶ X} {g : Y ⟶ Z} (hf : Inducing f)
    (hg : Inducing g) : Inducing (Limits.prod.map f g) := by
  constructor
  -- ⊢ topologicalSpace_forget (W ⨯ Y) = induced (↑(prod.map f g)) (topologicalSpac …
  simp only [prod_topology, induced_compose, ← coe_comp, Limits.prod.map_fst, Limits.prod.map_snd,
    induced_inf]
  simp only [coe_comp]
  -- ⊢ induced (↑prod.fst) W.str ⊓ induced (↑prod.snd) Y.str = induced (↑f ∘ ↑prod. …
  rw [← @induced_compose _ _ _ _ _ f, ← @induced_compose _ _ _ _ _ g, ← hf.induced, ← hg.induced]
  -- 🎉 no goals
#align Top.inducing_prod_map TopCat.inducing_prod_map

theorem embedding_prod_map {W X Y Z : TopCat.{u}} {f : W ⟶ X} {g : Y ⟶ Z} (hf : Embedding f)
    (hg : Embedding g) : Embedding (Limits.prod.map f g) :=
  ⟨inducing_prod_map hf.toInducing hg.toInducing, by
    haveI := (TopCat.mono_iff_injective _).mpr hf.inj
    -- ⊢ Function.Injective ↑(prod.map f g)
    haveI := (TopCat.mono_iff_injective _).mpr hg.inj
    -- ⊢ Function.Injective ↑(prod.map f g)
    exact (TopCat.mono_iff_injective _).mp inferInstance⟩
    -- 🎉 no goals
#align Top.embedding_prod_map TopCat.embedding_prod_map

end Prod

/-- The binary coproduct cofan in `TopCat`. -/
protected def binaryCofan (X Y : TopCat.{u}) : BinaryCofan X Y :=
  BinaryCofan.mk (⟨Sum.inl, by continuity⟩ : X ⟶ TopCat.of (Sum X Y)) ⟨Sum.inr, by continuity⟩
                               -- 🎉 no goals
                                                                                   -- 🎉 no goals
#align Top.binary_cofan TopCat.binaryCofan

/-- The constructed binary coproduct cofan in `TopCat` is the coproduct. -/
def binaryCofanIsColimit (X Y : TopCat.{u}) : IsColimit (TopCat.binaryCofan X Y) := by
  refine' Limits.BinaryCofan.isColimitMk (fun s =>
    {toFun := Sum.elim s.inl s.inr, continuous_toFun := _ }) _ _ _
  · apply
      Continuous.sum_elim (BinaryCofan.inl s).continuous_toFun (BinaryCofan.inr s).continuous_toFun
  · intro s
    -- ⊢ ContinuousMap.mk Sum.inl ≫ (fun s => ContinuousMap.mk (Sum.elim ↑(BinaryCofa …
    ext
    -- ⊢ ↑(ContinuousMap.mk Sum.inl ≫ (fun s => ContinuousMap.mk (Sum.elim ↑(BinaryCo …
    rfl
    -- 🎉 no goals
  · intro s
    -- ⊢ ContinuousMap.mk Sum.inr ≫ (fun s => ContinuousMap.mk (Sum.elim ↑(BinaryCofa …
    ext
    -- ⊢ ↑(ContinuousMap.mk Sum.inr ≫ (fun s => ContinuousMap.mk (Sum.elim ↑(BinaryCo …
    rfl
    -- 🎉 no goals
  · intro s m h₁ h₂
    -- ⊢ m = (fun s => ContinuousMap.mk (Sum.elim ↑(BinaryCofan.inl s) ↑(BinaryCofan. …
    ext (x | x)
    -- ⊢ ↑m (Sum.inl x) = ↑((fun s => ContinuousMap.mk (Sum.elim ↑(BinaryCofan.inl s) …
    exacts [(ConcreteCategory.congr_hom h₁ x : _), (ConcreteCategory.congr_hom h₂ x : _)]
    -- 🎉 no goals
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
      refine' ⟨(homeoOfIso <| h.coconePointUniqueUpToIso
        (binaryCofanIsColimit X Y)).symm.openEmbedding.comp openEmbedding_inl,
          (homeoOfIso <| h.coconePointUniqueUpToIso
            (binaryCofanIsColimit X Y)).symm.openEmbedding.comp openEmbedding_inr, _⟩
      erw [Set.range_comp, ← eq_compl_iff_isCompl, coe_comp, coe_comp, Set.range_comp _ Sum.inr,
        ← Set.image_compl_eq (homeoOfIso <| h.coconePointUniqueUpToIso
            (binaryCofanIsColimit X Y)).symm.bijective, Set.compl_range_inr, Set.image_comp]
      aesop
    · rintro ⟨h₁, h₂, h₃⟩
      have : ∀ x, x ∈ Set.range c.inl ∨ x ∈ Set.range c.inr := by
        rw [eq_compl_iff_isCompl.mpr h₃.symm]
        exact fun _ => or_not
      refine' ⟨BinaryCofan.IsColimit.mk _ _ _ _ _⟩
      · intro T f g
        refine' ContinuousMap.mk _ _
        · exact fun x =>
            if h : x ∈ Set.range c.inl then f ((Equiv.ofInjective _ h₁.inj).symm ⟨x, h⟩)
            else g ((Equiv.ofInjective _ h₂.inj).symm ⟨x, (this x).resolve_left h⟩)
        rw [continuous_iff_continuousAt]
        intro x
        by_cases x ∈ Set.range c.inl
        · revert h x
          apply (IsOpen.continuousOn_iff _).mp
          · rw [continuousOn_iff_continuous_restrict]
            convert_to Continuous (f ∘ (Homeomorph.ofEmbedding _ h₁.toEmbedding).symm)
            · ext ⟨x, hx⟩
              exact dif_pos hx
            apply Continuous.comp
            · exact f.continuous_toFun
            · continuity
          · exact h₁.open_range
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
            exact h₂.open_range
      · intro T f g
        ext x
        refine' (dif_pos _).trans _
        · exact ⟨x, rfl⟩
        · dsimp; conv_lhs => erw [Equiv.ofInjective_symm_apply]
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
