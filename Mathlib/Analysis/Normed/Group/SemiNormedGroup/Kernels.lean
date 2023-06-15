/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Johan Commelin, Scott Morrison

! This file was ported from Lean 3 source module analysis.normed.group.SemiNormedGroup.kernels
! leanprover-community/mathlib commit 17ef379e997badd73e5eabb4d38f11919ab3c4b3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Group.SemiNormedGroup
import Mathbin.Analysis.Normed.Group.Quotient
import Mathbin.CategoryTheory.Limits.Shapes.Kernels

/-!
# Kernels and cokernels in SemiNormedGroup₁ and SemiNormedGroup

We show that `SemiNormedGroup₁` has cokernels
(for which of course the `cokernel.π f` maps are norm non-increasing),
as well as the easier result that `SemiNormedGroup` has cokernels. We also show that
`SemiNormedGroup` has kernels.

So far, I don't see a way to state nicely what we really want:
`SemiNormedGroup` has cokernels, and `cokernel.π f` is norm non-increasing.
The problem is that the limits API doesn't promise you any particular model of the cokernel,
and in `SemiNormedGroup` one can always take a cokernel and rescale its norm
(and hence making `cokernel.π f` arbitrarily large in norm), obtaining another categorical cokernel.

-/


open CategoryTheory CategoryTheory.Limits

universe u

namespace SemiNormedGroup₁

noncomputable section

/-- Auxiliary definition for `has_cokernels SemiNormedGroup₁`. -/
def cokernelCocone {X Y : SemiNormedGroup₁.{u}} (f : X ⟶ Y) : Cofork f 0 :=
  Cofork.ofπ
    (@SemiNormedGroup₁.mkHom _ (SemiNormedGroup.of (Y ⧸ NormedAddGroupHom.range f.1))
      f.1.range.normedMk (NormedAddGroupHom.isQuotientQuotient _).norm_le)
    (by
      ext
      simp only [comp_apply, limits.zero_comp, NormedAddGroupHom.zero_apply,
        SemiNormedGroup₁.mkHom_apply, SemiNormedGroup₁.zero_apply, ← NormedAddGroupHom.mem_ker,
        f.1.range.ker_normedMk, f.1.mem_range]
      use x
      rfl)
#align SemiNormedGroup₁.cokernel_cocone SemiNormedGroup₁.cokernelCocone

/-- Auxiliary definition for `has_cokernels SemiNormedGroup₁`. -/
def cokernelLift {X Y : SemiNormedGroup₁.{u}} (f : X ⟶ Y) (s : CokernelCofork f) :
    (cokernelCocone f).pt ⟶ s.pt := by
  fconstructor
  -- The lift itself:
  · apply NormedAddGroupHom.lift _ s.π.1
    rintro _ ⟨b, rfl⟩
    change (f ≫ s.π) b = 0
    simp
  -- The lift has norm at most one:
  exact NormedAddGroupHom.lift_normNoninc _ _ _ s.π.2
#align SemiNormedGroup₁.cokernel_lift SemiNormedGroup₁.cokernelLift

instance : HasCokernels SemiNormedGroup₁.{u}
    where HasColimit X Y f :=
    HasColimit.mk
      { Cocone := cokernelCocone f
        IsColimit :=
          isColimitAux _ (cokernelLift f)
            (fun s => by
              ext
              apply NormedAddGroupHom.lift_mk f.1.range
              rintro _ ⟨b, rfl⟩
              change (f ≫ s.π) b = 0
              simp)
            fun s m w =>
            Subtype.eq
              (NormedAddGroupHom.lift_unique f.1.range _ _ _ (congr_arg Subtype.val w : _)) }

-- Sanity check
example : HasCokernels SemiNormedGroup₁ := by infer_instance

end SemiNormedGroup₁

namespace SemiNormedGroup

section EqualizersAndKernels

/-- The equalizer cone for a parallel pair of morphisms of seminormed groups. -/
def fork {V W : SemiNormedGroup.{u}} (f g : V ⟶ W) : Fork f g :=
  @Fork.ofι _ _ _ _ _ _ (of (f - g).ker) (NormedAddGroupHom.incl (f - g).ker) <|
    by
    ext v
    have : v.1 ∈ (f - g).ker := v.2
    simpa only [NormedAddGroupHom.incl_apply, Pi.zero_apply, coe_comp, NormedAddGroupHom.coe_zero,
      Subtype.val_eq_coe, NormedAddGroupHom.mem_ker, NormedAddGroupHom.coe_sub, Pi.sub_apply,
      sub_eq_zero] using this
#align SemiNormedGroup.fork SemiNormedGroup.fork

instance hasLimit_parallelPair {V W : SemiNormedGroup.{u}} (f g : V ⟶ W) :
    HasLimit (parallelPair f g)
    where exists_limit :=
    Nonempty.intro
      { Cone := fork f g
        IsLimit :=
          Fork.IsLimit.mk _
            (fun c =>
              NormedAddGroupHom.ker.lift (Fork.ι c) _ <|
                show NormedAddGroupHom.compHom (f - g) c.ι = 0 by
                  rw [AddMonoidHom.map_sub, AddMonoidHom.sub_apply, sub_eq_zero]; exact c.condition)
            (fun c => NormedAddGroupHom.ker.incl_comp_lift _ _ _) fun c g h => by ext x; dsimp;
            rw [← h]; rfl }
#align SemiNormedGroup.has_limit_parallel_pair SemiNormedGroup.hasLimit_parallelPair

instance : Limits.HasEqualizers.{u, u + 1} SemiNormedGroup :=
  @hasEqualizers_of_hasLimit_parallelPair SemiNormedGroup _ fun V W f g =>
    SemiNormedGroup.hasLimit_parallelPair f g

end EqualizersAndKernels

section Cokernel

-- PROJECT: can we reuse the work to construct cokernels in `SemiNormedGroup₁` here?
-- I don't see a way to do this that is less work than just repeating the relevant parts.
/-- Auxiliary definition for `has_cokernels SemiNormedGroup`. -/
def cokernelCocone {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) : Cofork f 0 :=
  @Cofork.ofπ _ _ _ _ _ _ (SemiNormedGroup.of (Y ⧸ NormedAddGroupHom.range f)) f.range.normedMk
    (by
      ext
      simp only [comp_apply, limits.zero_comp, NormedAddGroupHom.zero_apply, ←
        NormedAddGroupHom.mem_ker, f.range.ker_normed_mk, f.mem_range, exists_apply_eq_apply])
#align SemiNormedGroup.cokernel_cocone SemiNormedGroup.cokernelCocone

/-- Auxiliary definition for `has_cokernels SemiNormedGroup`. -/
def cokernelLift {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) (s : CokernelCofork f) :
    (cokernelCocone f).pt ⟶ s.pt :=
  NormedAddGroupHom.lift _ s.π
    (by
      rintro _ ⟨b, rfl⟩
      change (f ≫ s.π) b = 0
      simp)
#align SemiNormedGroup.cokernel_lift SemiNormedGroup.cokernelLift

/-- Auxiliary definition for `has_cokernels SemiNormedGroup`. -/
def isColimitCokernelCocone {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) :
    IsColimit (cokernelCocone f) :=
  isColimitAux _ (cokernelLift f)
    (fun s => by
      ext
      apply NormedAddGroupHom.lift_mk f.range
      rintro _ ⟨b, rfl⟩
      change (f ≫ s.π) b = 0
      simp)
    fun s m w => NormedAddGroupHom.lift_unique f.range _ _ _ w
#align SemiNormedGroup.is_colimit_cokernel_cocone SemiNormedGroup.isColimitCokernelCocone

instance : HasCokernels SemiNormedGroup.{u}
    where HasColimit X Y f :=
    HasColimit.mk
      { Cocone := cokernelCocone f
        IsColimit := isColimitCokernelCocone f }

-- Sanity check
example : HasCokernels SemiNormedGroup := by infer_instance

section ExplicitCokernel

/-- An explicit choice of cokernel, which has good properties with respect to the norm. -/
def explicitCokernel {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) : SemiNormedGroup.{u} :=
  (cokernelCocone f).pt
#align SemiNormedGroup.explicit_cokernel SemiNormedGroup.explicitCokernel

/-- Descend to the explicit cokernel. -/
def explicitCokernelDesc {X Y Z : SemiNormedGroup.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (w : f ≫ g = 0) :
    explicitCokernel f ⟶ Z :=
  (isColimitCokernelCocone f).desc (Cofork.ofπ g (by simp [w]))
#align SemiNormedGroup.explicit_cokernel_desc SemiNormedGroup.explicitCokernelDesc

/-- The projection from `Y` to the explicit cokernel of `X ⟶ Y`. -/
def explicitCokernelπ {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) : Y ⟶ explicitCokernel f :=
  (cokernelCocone f).ι.app WalkingParallelPair.one
#align SemiNormedGroup.explicit_cokernel_π SemiNormedGroup.explicitCokernelπ

theorem explicitCokernelπ_surjective {X Y : SemiNormedGroup.{u}} {f : X ⟶ Y} :
    Function.Surjective (explicitCokernelπ f) :=
  surjective_quot_mk _
#align SemiNormedGroup.explicit_cokernel_π_surjective SemiNormedGroup.explicitCokernelπ_surjective

@[simp, reassoc]
theorem comp_explicitCokernelπ {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) :
    f ≫ explicitCokernelπ f = 0 :=
  by
  convert (cokernel_cocone f).w walking_parallel_pair_hom.left
  simp
#align SemiNormedGroup.comp_explicit_cokernel_π SemiNormedGroup.comp_explicitCokernelπ

@[simp]
theorem explicitCokernelπ_apply_dom_eq_zero {X Y : SemiNormedGroup.{u}} {f : X ⟶ Y} (x : X) :
    (explicitCokernelπ f) (f x) = 0 :=
  show (f ≫ explicitCokernelπ f) x = 0 by rw [comp_explicit_cokernel_π]; rfl
#align SemiNormedGroup.explicit_cokernel_π_apply_dom_eq_zero SemiNormedGroup.explicitCokernelπ_apply_dom_eq_zero

@[simp, reassoc]
theorem explicitCokernelπ_desc {X Y Z : SemiNormedGroup.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (w : f ≫ g = 0) : explicitCokernelπ f ≫ explicitCokernelDesc w = g :=
  (isColimitCokernelCocone f).fac _ _
#align SemiNormedGroup.explicit_cokernel_π_desc SemiNormedGroup.explicitCokernelπ_desc

@[simp]
theorem explicitCokernelπ_desc_apply {X Y Z : SemiNormedGroup.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {cond : f ≫ g = 0} (x : Y) : explicitCokernelDesc cond (explicitCokernelπ f x) = g x :=
  show (explicitCokernelπ f ≫ explicitCokernelDesc cond) x = g x by rw [explicit_cokernel_π_desc]
#align SemiNormedGroup.explicit_cokernel_π_desc_apply SemiNormedGroup.explicitCokernelπ_desc_apply

theorem explicitCokernelDesc_unique {X Y Z : SemiNormedGroup.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (w : f ≫ g = 0) (e : explicitCokernel f ⟶ Z) (he : explicitCokernelπ f ≫ e = g) :
    e = explicitCokernelDesc w :=
  by
  apply (is_colimit_cokernel_cocone f).uniq (cofork.of_π g (by simp [w]))
  rintro (_ | _)
  · convert w.symm
    simp
  · exact he
#align SemiNormedGroup.explicit_cokernel_desc_unique SemiNormedGroup.explicitCokernelDesc_unique

theorem explicitCokernelDesc_comp_eq_desc {X Y Z W : SemiNormedGroup.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {h : Z ⟶ W} {cond : f ≫ g = 0} :
    explicitCokernelDesc cond ≫ h =
      explicitCokernelDesc
        (show f ≫ g ≫ h = 0 by rw [← CategoryTheory.Category.assoc, cond, limits.zero_comp]) :=
  by
  refine' explicit_cokernel_desc_unique _ _ _
  rw [← CategoryTheory.Category.assoc, explicit_cokernel_π_desc]
#align SemiNormedGroup.explicit_cokernel_desc_comp_eq_desc SemiNormedGroup.explicitCokernelDesc_comp_eq_desc

@[simp]
theorem explicitCokernelDesc_zero {X Y Z : SemiNormedGroup.{u}} {f : X ⟶ Y} :
    explicitCokernelDesc (show f ≫ (0 : Y ⟶ Z) = 0 from CategoryTheory.Limits.comp_zero) = 0 :=
  Eq.symm <| explicitCokernelDesc_unique _ _ CategoryTheory.Limits.comp_zero
#align SemiNormedGroup.explicit_cokernel_desc_zero SemiNormedGroup.explicitCokernelDesc_zero

@[ext]
theorem explicitCokernel_hom_ext {X Y Z : SemiNormedGroup.{u}} {f : X ⟶ Y}
    (e₁ e₂ : explicitCokernel f ⟶ Z) (h : explicitCokernelπ f ≫ e₁ = explicitCokernelπ f ≫ e₂) :
    e₁ = e₂ := by
  let g : Y ⟶ Z := explicit_cokernel_π f ≫ e₂
  have w : f ≫ g = 0 := by simp
  have : e₂ = explicit_cokernel_desc w := by apply explicit_cokernel_desc_unique; rfl
  rw [this]
  apply explicit_cokernel_desc_unique
  exact h
#align SemiNormedGroup.explicit_cokernel_hom_ext SemiNormedGroup.explicitCokernel_hom_ext

instance explicitCokernelπ.epi {X Y : SemiNormedGroup.{u}} {f : X ⟶ Y} :
    Epi (explicitCokernelπ f) := by
  constructor
  intro Z g h H
  ext x
  obtain ⟨x, hx⟩ := explicit_cokernel_π_surjective (explicit_cokernel_π f x)
  change (explicit_cokernel_π f ≫ g) _ = _
  rw [H]
#align SemiNormedGroup.explicit_cokernel_π.epi SemiNormedGroup.explicitCokernelπ.epi

theorem isQuotient_explicitCokernelπ {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) :
    NormedAddGroupHom.IsQuotient (explicitCokernelπ f) :=
  NormedAddGroupHom.isQuotientQuotient _
#align SemiNormedGroup.is_quotient_explicit_cokernel_π SemiNormedGroup.isQuotient_explicitCokernelπ

theorem normNoninc_explicitCokernelπ {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) :
    (explicitCokernelπ f).NormNoninc :=
  (isQuotient_explicitCokernelπ f).norm_le
#align SemiNormedGroup.norm_noninc_explicit_cokernel_π SemiNormedGroup.normNoninc_explicitCokernelπ

open scoped NNReal

theorem explicitCokernelDesc_norm_le_of_norm_le {X Y Z : SemiNormedGroup.{u}} {f : X ⟶ Y}
    {g : Y ⟶ Z} (w : f ≫ g = 0) (c : ℝ≥0) (h : ‖g‖ ≤ c) : ‖explicitCokernelDesc w‖ ≤ c :=
  NormedAddGroupHom.lift_norm_le _ _ _ h
#align SemiNormedGroup.explicit_cokernel_desc_norm_le_of_norm_le SemiNormedGroup.explicitCokernelDesc_norm_le_of_norm_le

theorem explicitCokernelDesc_normNoninc {X Y Z : SemiNormedGroup.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {cond : f ≫ g = 0} (hg : g.NormNoninc) : (explicitCokernelDesc cond).NormNoninc :=
  by
  refine' NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.2 _
  rw [← NNReal.coe_one]
  exact
    explicit_cokernel_desc_norm_le_of_norm_le cond 1
      (NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1 hg)
#align SemiNormedGroup.explicit_cokernel_desc_norm_noninc SemiNormedGroup.explicitCokernelDesc_normNoninc

theorem explicitCokernelDesc_comp_eq_zero {X Y Z W : SemiNormedGroup.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {h : Z ⟶ W} (cond : f ≫ g = 0) (cond2 : g ≫ h = 0) : explicitCokernelDesc cond ≫ h = 0 :=
  by
  rw [← cancel_epi (explicit_cokernel_π f), ← category.assoc, explicit_cokernel_π_desc]
  simp [cond2]
#align SemiNormedGroup.explicit_cokernel_desc_comp_eq_zero SemiNormedGroup.explicitCokernelDesc_comp_eq_zero

theorem explicitCokernelDesc_norm_le {X Y Z : SemiNormedGroup.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (w : f ≫ g = 0) : ‖explicitCokernelDesc w‖ ≤ ‖g‖ :=
  explicitCokernelDesc_norm_le_of_norm_le w ‖g‖₊ le_rfl
#align SemiNormedGroup.explicit_cokernel_desc_norm_le SemiNormedGroup.explicitCokernelDesc_norm_le

/-- The explicit cokernel is isomorphic to the usual cokernel. -/
def explicitCokernelIso {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) : explicitCokernel f ≅ cokernel f :=
  (isColimitCokernelCocone f).coconePointUniqueUpToIso (colimit.isColimit _)
#align SemiNormedGroup.explicit_cokernel_iso SemiNormedGroup.explicitCokernelIso

@[simp]
theorem explicitCokernelIso_hom_π {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) :
    explicitCokernelπ f ≫ (explicitCokernelIso f).hom = cokernel.π _ := by
  simp [explicit_cokernel_π, explicit_cokernel_iso, is_colimit.cocone_point_unique_up_to_iso]
#align SemiNormedGroup.explicit_cokernel_iso_hom_π SemiNormedGroup.explicitCokernelIso_hom_π

@[simp]
theorem explicitCokernelIso_inv_π {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) :
    cokernel.π f ≫ (explicitCokernelIso f).inv = explicitCokernelπ f := by
  simp [explicit_cokernel_π, explicit_cokernel_iso]
#align SemiNormedGroup.explicit_cokernel_iso_inv_π SemiNormedGroup.explicitCokernelIso_inv_π

@[simp]
theorem explicitCokernelIso_hom_desc {X Y Z : SemiNormedGroup.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (w : f ≫ g = 0) : (explicitCokernelIso f).hom ≫ cokernel.desc f g w = explicitCokernelDesc w :=
  by
  ext1
  simp [explicit_cokernel_desc, explicit_cokernel_π, explicit_cokernel_iso,
    is_colimit.cocone_point_unique_up_to_iso]
#align SemiNormedGroup.explicit_cokernel_iso_hom_desc SemiNormedGroup.explicitCokernelIso_hom_desc

/-- A special case of `category_theory.limits.cokernel.map` adapted to `explicit_cokernel`. -/
noncomputable def explicitCokernel.map {A B C D : SemiNormedGroup.{u}} {fab : A ⟶ B} {fbd : B ⟶ D}
    {fac : A ⟶ C} {fcd : C ⟶ D} (h : fab ≫ fbd = fac ≫ fcd) :
    explicitCokernel fab ⟶ explicitCokernel fcd :=
  @explicitCokernelDesc _ _ _ fab (fbd ≫ explicitCokernelπ _) <| by simp [reassoc_of h]
#align SemiNormedGroup.explicit_cokernel.map SemiNormedGroup.explicitCokernel.map

/-- A special case of `category_theory.limits.cokernel.map_desc` adapted to `explicit_cokernel`. -/
theorem ExplicitCoker.map_desc {A B C D B' D' : SemiNormedGroup.{u}} {fab : A ⟶ B} {fbd : B ⟶ D}
    {fac : A ⟶ C} {fcd : C ⟶ D} {h : fab ≫ fbd = fac ≫ fcd} {fbb' : B ⟶ B'} {fdd' : D ⟶ D'}
    {condb : fab ≫ fbb' = 0} {condd : fcd ≫ fdd' = 0} {g : B' ⟶ D'} (h' : fbb' ≫ g = fbd ≫ fdd') :
    explicitCokernelDesc condb ≫ g = explicitCokernel.map h ≫ explicitCokernelDesc condd :=
  by
  delta explicit_cokernel.map
  simp [← cancel_epi (explicit_cokernel_π fab), category.assoc, explicit_cokernel_π_desc, h']
#align SemiNormedGroup.explicit_coker.map_desc SemiNormedGroup.ExplicitCoker.map_desc

end ExplicitCokernel

end Cokernel

end SemiNormedGroup

