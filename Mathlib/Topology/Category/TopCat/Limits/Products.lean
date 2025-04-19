/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kim Morrison, Mario Carneiro, Andrew Yang
-/
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Data.Set.Subsingleton
import Mathlib.Tactic.CategoryTheory.Elementwise
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Products and coproducts in the category of topological spaces
-/

open CategoryTheory Limits Set TopologicalSpace Topology

universe v u w

noncomputable section

namespace TopCat

variable {J : Type v} [Category.{w} J]

/-- The projection from the product as a bundled continuous map. -/
abbrev piπ {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) : TopCat.of (∀ i, α i) ⟶ α i :=
  ofHom ⟨fun f => f i, continuous_apply i⟩

/-- The explicit fan of a family of topological spaces given by the pi type. -/
@[simps! pt π_app]
def piFan {ι : Type v} (α : ι → TopCat.{max v u}) : Fan α :=
  Fan.mk (TopCat.of (∀ i, α i)) (piπ.{v,u} α)

/-- The constructed fan is indeed a limit -/
def piFanIsLimit {ι : Type v} (α : ι → TopCat.{max v u}) : IsLimit (piFan α) where
  lift S := ofHom
    { toFun := fun s i => S.π.app ⟨i⟩ s
      continuous_toFun := continuous_pi (fun i => (S.π.app ⟨i⟩).hom.2) }
  uniq := by
    intro S m h
    ext x
    funext i
    simp [ContinuousMap.coe_mk, ← h ⟨i⟩]
  fac _ _ := rfl

/-- The product is homeomorphic to the product of the underlying spaces,
equipped with the product topology.
-/
def piIsoPi {ι : Type v} (α : ι → TopCat.{max v u}) : ∏ᶜ α ≅ TopCat.of (∀ i, α i) :=
  (limit.isLimit _).conePointUniqueUpToIso (piFanIsLimit.{v, u} α)

@[reassoc (attr := simp)]
theorem piIsoPi_inv_π {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) :
    (piIsoPi α).inv ≫ Pi.π α i = piπ α i := by simp [piIsoPi]

theorem piIsoPi_inv_π_apply {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) (x : ∀ i, α i) :
    (Pi.π α i :) ((piIsoPi α).inv x) = x i :=
  ConcreteCategory.congr_hom (piIsoPi_inv_π α i) x

theorem piIsoPi_hom_apply {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι)
    (x : (∏ᶜ α : TopCat.{max v u})) : (piIsoPi α).hom x i = (Pi.π α i :) x := by
  have := piIsoPi_inv_π α i
  rw [Iso.inv_comp_eq] at this
  exact ConcreteCategory.congr_hom this x

/-- The inclusion to the coproduct as a bundled continuous map. -/
abbrev sigmaι {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) : α i ⟶ TopCat.of (Σi, α i) := by
  refine ofHom (ContinuousMap.mk ?_ ?_)
  · dsimp
    apply Sigma.mk i
  · dsimp; continuity

/-- The explicit cofan of a family of topological spaces given by the sigma type. -/
@[simps! pt ι_app]
def sigmaCofan {ι : Type v} (α : ι → TopCat.{max v u}) : Cofan α :=
  Cofan.mk (TopCat.of (Σi, α i)) (sigmaι α)

/-- The constructed cofan is indeed a colimit -/
def sigmaCofanIsColimit {ι : Type v} (β : ι → TopCat.{max v u}) : IsColimit (sigmaCofan β) where
  desc S := ofHom
    { toFun := fun (s : of (Σ i, β i)) => S.ι.app ⟨s.1⟩ s.2
      continuous_toFun := by continuity }
  uniq := by
    intro S m h
    ext ⟨i, x⟩
    simp only [← h]
    congr
  fac s j := by
    cases j
    aesop_cat

/-- The coproduct is homeomorphic to the disjoint union of the topological spaces.
-/
def sigmaIsoSigma {ι : Type v} (α : ι → TopCat.{max v u}) : ∐ α ≅ TopCat.of (Σi, α i) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (sigmaCofanIsColimit.{v, u} α)

@[reassoc (attr := simp)]
theorem sigmaIsoSigma_hom_ι {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) :
    Sigma.ι α i ≫ (sigmaIsoSigma α).hom = sigmaι α i := by simp [sigmaIsoSigma]

theorem sigmaIsoSigma_hom_ι_apply {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) (x : α i) :
    (sigmaIsoSigma α).hom ((Sigma.ι α i :) x) = Sigma.mk i x :=
  ConcreteCategory.congr_hom (sigmaIsoSigma_hom_ι α i) x

theorem sigmaIsoSigma_inv_apply {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) (x : α i) :
    (sigmaIsoSigma α).inv ⟨i, x⟩ = (Sigma.ι α i :) x := by
  rw [← sigmaIsoSigma_hom_ι_apply, ← comp_app, ← comp_app, Iso.hom_inv_id,
    Category.comp_id]

section Prod

/-- The first projection from the product. -/
abbrev prodFst {X Y : TopCat.{u}} : TopCat.of (X × Y) ⟶ X :=
  ofHom { toFun := Prod.fst }

/-- The second projection from the product. -/
abbrev prodSnd {X Y : TopCat.{u}} : TopCat.of (X × Y) ⟶ Y :=
  ofHom { toFun := Prod.snd }

/-- The explicit binary cofan of `X, Y` given by `X × Y`. -/
def prodBinaryFan (X Y : TopCat.{u}) : BinaryFan X Y :=
  BinaryFan.mk prodFst prodSnd

/-- The constructed binary fan is indeed a limit -/
def prodBinaryFanIsLimit (X Y : TopCat.{u}) : IsLimit (prodBinaryFan X Y) where
  lift := fun S : BinaryFan X Y => ofHom {
    toFun := fun s => (S.fst s, S.snd s)
    continuous_toFun := by continuity }
  fac := by
    rintro S (_ | _) <;> {dsimp; ext; rfl}
  uniq := by
    intro S m h
    ext x
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): used to be part of `ext x`
    refine Prod.ext ?_ ?_
    · specialize h ⟨WalkingPair.left⟩
      apply_fun fun e => e x at h
      exact h
    · specialize h ⟨WalkingPair.right⟩
      apply_fun fun e => e x at h
      exact h

/-- The homeomorphism between `X ⨯ Y` and the set-theoretic product of `X` and `Y`,
equipped with the product topology.
-/
def prodIsoProd (X Y : TopCat.{u}) : X ⨯ Y ≅ TopCat.of (X × Y) :=
  (limit.isLimit _).conePointUniqueUpToIso (prodBinaryFanIsLimit X Y)

@[reassoc (attr := simp)]
theorem prodIsoProd_hom_fst (X Y : TopCat.{u}) :
    (prodIsoProd X Y).hom ≫ prodFst = Limits.prod.fst := by
  simp [← Iso.eq_inv_comp, prodIsoProd]
  rfl

@[reassoc (attr := simp)]
theorem prodIsoProd_hom_snd (X Y : TopCat.{u}) :
    (prodIsoProd X Y).hom ≫ prodSnd = Limits.prod.snd := by
  simp [← Iso.eq_inv_comp, prodIsoProd]
  rfl

-- Note that `(x : X ⨯ Y)` would mean `(x : ↑X × ↑Y)` below:
theorem prodIsoProd_hom_apply {X Y : TopCat.{u}} (x : ↑(X ⨯ Y)) :
    (prodIsoProd X Y).hom x = ((Limits.prod.fst : X ⨯ Y ⟶ _) x,
    (Limits.prod.snd : X ⨯ Y ⟶ _) x) := by
  ext
  · exact ConcreteCategory.congr_hom (prodIsoProd_hom_fst X Y) x
  · exact ConcreteCategory.congr_hom (prodIsoProd_hom_snd X Y) x

@[reassoc (attr := simp), elementwise]
theorem prodIsoProd_inv_fst (X Y : TopCat.{u}) :
    (prodIsoProd X Y).inv ≫ Limits.prod.fst = prodFst := by simp [Iso.inv_comp_eq]

@[reassoc (attr := simp), elementwise]
theorem prodIsoProd_inv_snd (X Y : TopCat.{u}) :
    (prodIsoProd X Y).inv ≫ Limits.prod.snd = prodSnd := by simp [Iso.inv_comp_eq]

theorem prod_topology {X Y : TopCat.{u}} :
    (X ⨯ Y).str =
      induced (Limits.prod.fst : X ⨯ Y ⟶ _) X.str ⊓
        induced (Limits.prod.snd : X ⨯ Y ⟶ _) Y.str := by
  let homeo := homeoOfIso (prodIsoProd X Y)
  refine homeo.isInducing.eq_induced.trans ?_
  change induced homeo (_ ⊓ _) = _
  simp [induced_compose]
  rfl

theorem range_prod_map {W X Y Z : TopCat.{u}} (f : W ⟶ Y) (g : X ⟶ Z) :
    Set.range (Limits.prod.map f g) =
      (Limits.prod.fst : Y ⨯ Z ⟶ _) ⁻¹' Set.range f ∩
        (Limits.prod.snd : Y ⨯ Z ⟶ _) ⁻¹' Set.range g := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp_rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_range, ← ConcreteCategory.comp_apply,
      Limits.prod.map_fst, Limits.prod.map_snd, ConcreteCategory.comp_apply, exists_apply_eq_apply,
      and_self_iff]
  · rintro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
    use (prodIsoProd W X).inv (x₁, x₂)
    apply Concrete.limit_ext
    rintro ⟨⟨⟩⟩
    · rw [← ConcreteCategory.comp_apply]
      erw [Limits.prod.map_fst]
      rw [ConcreteCategory.comp_apply, TopCat.prodIsoProd_inv_fst_apply]
      exact hx₁
    · rw [← ConcreteCategory.comp_apply]
      erw [Limits.prod.map_snd]
      rw [ConcreteCategory.comp_apply, TopCat.prodIsoProd_inv_snd_apply]
      exact hx₂

theorem isInducing_prodMap {W X Y Z : TopCat.{u}} {f : W ⟶ X} {g : Y ⟶ Z} (hf : IsInducing f)
    (hg : IsInducing g) : IsInducing (Limits.prod.map f g) := by
  constructor
  simp_rw [prod_topology, induced_inf, induced_compose, ← coe_comp,
    prod.map_fst, prod.map_snd, coe_comp, ← induced_compose (g := f), ← induced_compose (g := g)]
  rw [← hf.eq_induced, ← hg.eq_induced]

@[deprecated (since := "2024-10-28")] alias inducing_prod_map := isInducing_prodMap

theorem isEmbedding_prodMap {W X Y Z : TopCat.{u}} {f : W ⟶ X} {g : Y ⟶ Z} (hf : IsEmbedding f)
    (hg : IsEmbedding g) : IsEmbedding (Limits.prod.map f g) :=
  ⟨isInducing_prodMap hf.isInducing hg.isInducing, by
    haveI := (TopCat.mono_iff_injective _).mpr hf.injective
    haveI := (TopCat.mono_iff_injective _).mpr hg.injective
    exact (TopCat.mono_iff_injective _).mp inferInstance⟩

@[deprecated (since := "2024-10-26")]
alias embedding_prod_map := isEmbedding_prodMap

end Prod

/-- The binary coproduct cofan in `TopCat`. -/
protected def binaryCofan (X Y : TopCat.{u}) : BinaryCofan X Y :=
  BinaryCofan.mk (ofHom ⟨Sum.inl, by continuity⟩) (ofHom ⟨Sum.inr, by continuity⟩)

/-- The constructed binary coproduct cofan in `TopCat` is the coproduct. -/
def binaryCofanIsColimit (X Y : TopCat.{u}) : IsColimit (TopCat.binaryCofan X Y) := by
  refine Limits.BinaryCofan.isColimitMk (fun s => ofHom
    { toFun := Sum.elim s.inl s.inr, continuous_toFun := ?_ }) ?_ ?_ ?_
  · continuity
  · intro s
    ext
    rfl
  · intro s
    ext
    rfl
  · intro s m h₁ h₂
    ext (x | x)
    exacts [ConcreteCategory.congr_hom h₁ x, ConcreteCategory.congr_hom h₂ x]

theorem binaryCofan_isColimit_iff {X Y : TopCat} (c : BinaryCofan X Y) :
    Nonempty (IsColimit c) ↔
      IsOpenEmbedding c.inl ∧ IsOpenEmbedding c.inr ∧ IsCompl (range c.inl) (range c.inr) := by
  classical
    constructor
    · rintro ⟨h⟩
      rw [← show _ = c.inl from
          h.comp_coconePointUniqueUpToIso_inv (binaryCofanIsColimit X Y) ⟨WalkingPair.left⟩,
        ← show _ = c.inr from
          h.comp_coconePointUniqueUpToIso_inv (binaryCofanIsColimit X Y) ⟨WalkingPair.right⟩]
      dsimp
      refine ⟨(homeoOfIso <| h.coconePointUniqueUpToIso
        (binaryCofanIsColimit X Y)).symm.isOpenEmbedding.comp .inl,
          (homeoOfIso <| h.coconePointUniqueUpToIso
            (binaryCofanIsColimit X Y)).symm.isOpenEmbedding.comp .inr, ?_⟩
      rw [Set.range_comp, ← eq_compl_iff_isCompl]
      conv_rhs => rw [Set.range_comp]
      erw [← Set.image_compl_eq (homeoOfIso <| h.coconePointUniqueUpToIso
            (binaryCofanIsColimit X Y)).symm.bijective, Set.compl_range_inr, Set.image_comp]
    · rintro ⟨h₁, h₂, h₃⟩
      have : ∀ x, x ∈ Set.range c.inl ∨ x ∈ Set.range c.inr := by
        rw [eq_compl_iff_isCompl.mpr h₃.symm]
        exact fun _ => or_not
      refine ⟨BinaryCofan.IsColimit.mk _ ?_ ?_ ?_ ?_⟩
      · intro T f g
        refine ofHom (ContinuousMap.mk ?_ ?_)
        · exact fun x =>
            if h : x ∈ Set.range c.inl then f ((Equiv.ofInjective _ h₁.injective).symm ⟨x, h⟩)
            else g ((Equiv.ofInjective _ h₂.injective).symm ⟨x, (this x).resolve_left h⟩)
        rw [continuous_iff_continuousAt]
        intro x
        by_cases h : x ∈ Set.range c.inl
        · revert h x
          apply (IsOpen.continuousOn_iff _).mp
          · rw [continuousOn_iff_continuous_restrict]
            convert_to Continuous (f ∘ h₁.isEmbedding.toHomeomorph.symm)
            · ext ⟨x, hx⟩
              exact dif_pos hx
            continuity
          · exact h₁.isOpen_range
        · revert h x
          apply (IsOpen.continuousOn_iff _).mp
          · rw [continuousOn_iff_continuous_restrict]
            have : ∀ a, a ∉ Set.range c.inl → a ∈ Set.range c.inr := by
              rintro a (h : a ∈ (Set.range c.inl)ᶜ)
              rwa [eq_compl_iff_isCompl.mpr h₃.symm]
            convert_to Continuous
                (g ∘ h₂.isEmbedding.toHomeomorph.symm ∘ Subtype.map _ this)
            · ext ⟨x, hx⟩
              exact dif_neg hx
            apply Continuous.comp
            · exact g.hom.continuous_toFun
            · apply Continuous.comp
              · continuity
              · rw [IsEmbedding.subtypeVal.isInducing.continuous_iff]
                exact continuous_subtype_val
          · change IsOpen (Set.range c.inl)ᶜ
            rw [← eq_compl_iff_isCompl.mpr h₃.symm]
            exact h₂.isOpen_range
      · intro T f g
        ext x
        dsimp
        rw [dif_pos]
        conv_lhs => rw [Equiv.ofInjective_symm_apply]
      · intro T f g
        ext x
        dsimp
        rw [dif_neg]
        · exact congr_arg g (Equiv.ofInjective_symm_apply _ _)
        · rintro ⟨y, e⟩
          have : c.inr x ∈ Set.range c.inl ⊓ Set.range c.inr := ⟨⟨_, e⟩, ⟨_, rfl⟩⟩
          rwa [disjoint_iff.mp h₃.1] at this
      · rintro T _ _ m rfl rfl
        ext x
        change m x = dite _ _ _
        split_ifs <;> exact congr_arg _ (Equiv.apply_ofInjective_symm _ ⟨_, _⟩).symm

end TopCat
