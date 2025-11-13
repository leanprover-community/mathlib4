/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Johan Commelin, Kim Morrison
-/
import Mathlib.Analysis.Normed.Group.SemiNormedGrp
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Kernels and cokernels in SemiNormedGrp₁ and SemiNormedGrp

We show that `SemiNormedGrp₁` has cokernels
(for which of course the `cokernel.π f` maps are norm non-increasing),
as well as the easier result that `SemiNormedGrp` has cokernels. We also show that
`SemiNormedGrp` has kernels.

So far, I don't see a way to state nicely what we really want:
`SemiNormedGrp` has cokernels, and `cokernel.π f` is norm non-increasing.
The problem is that the limits API doesn't promise you any particular model of the cokernel,
and in `SemiNormedGrp` one can always take a cokernel and rescale its norm
(and hence making `cokernel.π f` arbitrarily large in norm), obtaining another categorical cokernel.

-/


open CategoryTheory CategoryTheory.Limits

universe u

namespace SemiNormedGrp₁

noncomputable section

/-- Auxiliary definition for `HasCokernels SemiNormedGrp₁`. -/
def cokernelCocone {X Y : SemiNormedGrp₁.{u}} (f : X ⟶ Y) : Cofork f 0 :=
  Cofork.ofπ
    (@SemiNormedGrp₁.mkHom _ (Y ⧸ NormedAddGroupHom.range f.1) _ _
      f.hom.1.range.normedMk (NormedAddGroupHom.isQuotientQuotient _).norm_le)
    (by
      ext x
      rw [Limits.zero_comp, comp_apply, SemiNormedGrp₁.mkHom_apply,
        SemiNormedGrp₁.zero_apply, ← NormedAddGroupHom.mem_ker, f.hom.1.range.ker_normedMk,
        f.hom.1.mem_range]
      use x)

/-- Auxiliary definition for `HasCokernels SemiNormedGrp₁`. -/
def cokernelLift {X Y : SemiNormedGrp₁.{u}} (f : X ⟶ Y) (s : CokernelCofork f) :
    (cokernelCocone f).pt ⟶ s.pt := by
  fconstructor
  -- The lift itself:
  · apply NormedAddGroupHom.lift _ s.π.1
    rintro _ ⟨b, rfl⟩
    change (f ≫ s.π) b = 0
    simp
  -- The lift has norm at most one:
  exact NormedAddGroupHom.lift_normNoninc _ _ _ s.π.2

instance : HasCokernels SemiNormedGrp₁.{u} where
  has_colimit f :=
    HasColimit.mk
      { cocone := cokernelCocone f
        isColimit :=
          isColimitAux _ (cokernelLift f)
            (fun s => by
              ext
              apply NormedAddGroupHom.lift_mk f.1.range
              rintro _ ⟨b, rfl⟩
              change (f ≫ s.π) b = 0
              simp)
            fun _ _ w =>
            SemiNormedGrp₁.hom_ext <| Subtype.eq
              (NormedAddGroupHom.lift_unique f.1.range _ _ _
                (congr_arg Subtype.val (congr_arg Hom.hom w))) }

-- Sanity check
example : HasCokernels SemiNormedGrp₁ := by infer_instance

end

end SemiNormedGrp₁

namespace SemiNormedGrp

section EqualizersAndKernels

noncomputable instance {V W : SemiNormedGrp.{u}} : Norm (V ⟶ W) where
  norm f := norm f.hom
noncomputable instance {V W : SemiNormedGrp.{u}} : NNNorm (V ⟶ W) where
  nnnorm f := nnnorm f.hom

/-- The equalizer cone for a parallel pair of morphisms of seminormed groups. -/
def fork {V W : SemiNormedGrp.{u}} (f g : V ⟶ W) : Fork f g :=
  @Fork.ofι _ _ _ _ _ _ (of (f - g).hom.ker)
    (ofHom (NormedAddGroupHom.incl (f - g).hom.ker)) <| by
    ext v
    have : v.1 ∈ (f - g).hom.ker := v.2
    simpa [-SetLike.coe_mem, NormedAddGroupHom.mem_ker, sub_eq_zero] using this

instance hasLimit_parallelPair {V W : SemiNormedGrp.{u}} (f g : V ⟶ W) :
    HasLimit (parallelPair f g) where
  exists_limit :=
    Nonempty.intro
      { cone := fork f g
        isLimit :=
          have this := fun (c : Fork f g) =>
            show NormedAddGroupHom.compHom (f - g).hom c.ι.hom = 0 by
              rw [hom_sub, AddMonoidHom.map_sub, AddMonoidHom.sub_apply, sub_eq_zero]
              exact congr_arg Hom.hom c.condition
          Fork.IsLimit.mk _
            (fun c => ofHom <|
              NormedAddGroupHom.ker.lift (Fork.ι c).hom _ <| this c)
            (fun _ => SemiNormedGrp.hom_ext <| NormedAddGroupHom.ker.incl_comp_lift _ _ (this _))
            fun c g h => by ext x; dsimp; simp_rw [← h]; rfl}

instance : Limits.HasEqualizers.{u, u + 1} SemiNormedGrp :=
  @hasEqualizers_of_hasLimit_parallelPair SemiNormedGrp _ fun {_ _ f g} =>
    SemiNormedGrp.hasLimit_parallelPair f g

end EqualizersAndKernels

section Cokernel

-- PROJECT: can we reuse the work to construct cokernels in `SemiNormedGrp₁` here?
-- I don't see a way to do this that is less work than just repeating the relevant parts.
/-- Auxiliary definition for `HasCokernels SemiNormedGrp`. -/
noncomputable
def cokernelCocone {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) : Cofork f 0 :=
  Cofork.ofπ (P := SemiNormedGrp.of (Y ⧸ NormedAddGroupHom.range f.hom))
    (ofHom f.hom.range.normedMk)
    (by aesop)

/-- Auxiliary definition for `HasCokernels SemiNormedGrp`. -/
noncomputable
def cokernelLift {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) (s : CokernelCofork f) :
    (cokernelCocone f).pt ⟶ s.pt :=
  ofHom <| NormedAddGroupHom.lift _ s.π.hom
    (by
      rintro _ ⟨b, rfl⟩
      change (f ≫ s.π) b = 0
      simp)

/-- Auxiliary definition for `HasCokernels SemiNormedGrp`. -/
noncomputable
def isColimitCokernelCocone {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) :
    IsColimit (cokernelCocone f) :=
  isColimitAux _ (cokernelLift f)
    (fun s => by
      ext
      apply NormedAddGroupHom.lift_mk f.hom.range
      rintro _ ⟨b, rfl⟩
      change (f ≫ s.π) b = 0
      simp)
    fun _ _ w => SemiNormedGrp.hom_ext <| NormedAddGroupHom.lift_unique f.hom.range _ _ _ <|
      congr_arg Hom.hom w

instance : HasCokernels SemiNormedGrp.{u} where
  has_colimit f :=
    HasColimit.mk
      { cocone := cokernelCocone f
        isColimit := isColimitCokernelCocone f }

-- Sanity check
example : HasCokernels SemiNormedGrp := by infer_instance

section ExplicitCokernel

/-- An explicit choice of cokernel, which has good properties with respect to the norm. -/
noncomputable
def explicitCokernel {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) : SemiNormedGrp.{u} :=
  (cokernelCocone f).pt

/-- Descend to the explicit cokernel. -/
noncomputable
def explicitCokernelDesc {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (w : f ≫ g = 0) :
    explicitCokernel f ⟶ Z :=
  (isColimitCokernelCocone f).desc (Cofork.ofπ g (by simp [w]))

/-- The projection from `Y` to the explicit cokernel of `X ⟶ Y`. -/
noncomputable
def explicitCokernelπ {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) : Y ⟶ explicitCokernel f :=
  (cokernelCocone f).ι.app WalkingParallelPair.one

theorem explicitCokernelπ_surjective {X Y : SemiNormedGrp.{u}} {f : X ⟶ Y} :
    Function.Surjective (explicitCokernelπ f) :=
  Quot.mk_surjective

@[reassoc (attr := simp)]
theorem comp_explicitCokernelπ {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) :
    f ≫ explicitCokernelπ f = 0 := by
  convert (cokernelCocone f).w WalkingParallelPairHom.left
  simp

@[simp]
theorem explicitCokernelπ_apply_dom_eq_zero {X Y : SemiNormedGrp.{u}} {f : X ⟶ Y} (x : X) :
    (explicitCokernelπ f) (f x) = 0 :=
  show (f ≫ explicitCokernelπ f) x = 0 by rw [comp_explicitCokernelπ]; rfl

@[simp, reassoc]
theorem explicitCokernelπ_desc {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (w : f ≫ g = 0) : explicitCokernelπ f ≫ explicitCokernelDesc w = g :=
  (isColimitCokernelCocone f).fac _ _

@[simp]
theorem explicitCokernelπ_desc_apply {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {cond : f ≫ g = 0} (x : Y) : explicitCokernelDesc cond (explicitCokernelπ f x) = g x :=
  show (explicitCokernelπ f ≫ explicitCokernelDesc cond) x = g x by rw [explicitCokernelπ_desc]

theorem explicitCokernelDesc_unique {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (w : f ≫ g = 0) (e : explicitCokernel f ⟶ Z) (he : explicitCokernelπ f ≫ e = g) :
    e = explicitCokernelDesc w := by
  apply (isColimitCokernelCocone f).uniq (Cofork.ofπ g (by simp [w]))
  rintro (_ | _)
  · convert w.symm
    simp
  · exact he

theorem explicitCokernelDesc_comp_eq_desc {X Y Z W : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {h : Z ⟶ W} {cond : f ≫ g = 0} :
    explicitCokernelDesc cond ≫ h =
      explicitCokernelDesc
        (show f ≫ g ≫ h = 0 by rw [← CategoryTheory.Category.assoc, cond, Limits.zero_comp]) := by
  refine explicitCokernelDesc_unique _ _ ?_
  rw [← CategoryTheory.Category.assoc, explicitCokernelπ_desc]

@[simp]
theorem explicitCokernelDesc_zero {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} :
    explicitCokernelDesc (show f ≫ (0 : Y ⟶ Z) = 0 from CategoryTheory.Limits.comp_zero) = 0 :=
  Eq.symm <| explicitCokernelDesc_unique _ _ CategoryTheory.Limits.comp_zero

@[ext]
theorem explicitCokernel_hom_ext {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y}
    (e₁ e₂ : explicitCokernel f ⟶ Z) (h : explicitCokernelπ f ≫ e₁ = explicitCokernelπ f ≫ e₂) :
    e₁ = e₂ := by
  let g : Y ⟶ Z := explicitCokernelπ f ≫ e₂
  have w : f ≫ g = 0 := by simp [g]
  have : e₂ = explicitCokernelDesc w := by apply explicitCokernelDesc_unique; rfl
  rw [this]
  apply explicitCokernelDesc_unique
  exact h

instance explicitCokernelπ.epi {X Y : SemiNormedGrp.{u}} {f : X ⟶ Y} :
    Epi (explicitCokernelπ f) := by
  constructor
  intro Z g h H
  ext x
  rw [H]

theorem isQuotient_explicitCokernelπ {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) :
    NormedAddGroupHom.IsQuotient (explicitCokernelπ f).hom :=
  NormedAddGroupHom.isQuotientQuotient _

theorem normNoninc_explicitCokernelπ {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) :
    (explicitCokernelπ f).hom.NormNoninc :=
  (isQuotient_explicitCokernelπ f).norm_le

open scoped NNReal

theorem explicitCokernelDesc_norm_le_of_norm_le {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y}
    {g : Y ⟶ Z} (w : f ≫ g = 0) (c : ℝ≥0) (h : ‖g‖ ≤ c) : ‖explicitCokernelDesc w‖ ≤ c :=
  NormedAddGroupHom.lift_norm_le _ _ _ h

theorem explicitCokernelDesc_normNoninc {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {cond : f ≫ g = 0} (hg : g.hom.NormNoninc) : (explicitCokernelDesc cond).hom.NormNoninc := by
  refine NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.2 ?_
  rw [← NNReal.coe_one]
  exact
    explicitCokernelDesc_norm_le_of_norm_le cond 1
      (NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1 hg)

theorem explicitCokernelDesc_comp_eq_zero {X Y Z W : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {h : Z ⟶ W} (cond : f ≫ g = 0) (cond2 : g ≫ h = 0) : explicitCokernelDesc cond ≫ h = 0 := by
  rw [← cancel_epi (explicitCokernelπ f), ← Category.assoc, explicitCokernelπ_desc]
  simp [cond2]

theorem explicitCokernelDesc_norm_le {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (w : f ≫ g = 0) : ‖explicitCokernelDesc w‖ ≤ ‖g‖ :=
  explicitCokernelDesc_norm_le_of_norm_le w ‖g‖₊ le_rfl

/-- The explicit cokernel is isomorphic to the usual cokernel. -/
noncomputable
def explicitCokernelIso {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) :
    explicitCokernel f ≅ cokernel f :=
  (isColimitCokernelCocone f).coconePointUniqueUpToIso (colimit.isColimit _)

@[simp]
theorem explicitCokernelIso_hom_π {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) :
    explicitCokernelπ f ≫ (explicitCokernelIso f).hom = cokernel.π _ := by
  simp [explicitCokernelπ, explicitCokernelIso, IsColimit.coconePointUniqueUpToIso]

@[simp]
theorem explicitCokernelIso_inv_π {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) :
    cokernel.π f ≫ (explicitCokernelIso f).inv = explicitCokernelπ f := by
  simp [explicitCokernelπ, explicitCokernelIso]

@[simp]
theorem explicitCokernelIso_hom_desc {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (w : f ≫ g = 0) :
    (explicitCokernelIso f).hom ≫ cokernel.desc f g w = explicitCokernelDesc w := by
  ext1
  simp [explicitCokernelDesc, explicitCokernelπ, explicitCokernelIso,
    IsColimit.coconePointUniqueUpToIso]

/-- A special case of `CategoryTheory.Limits.cokernel.map` adapted to `explicitCokernel`. -/
noncomputable def explicitCokernel.map {A B C D : SemiNormedGrp.{u}}
    {fab : A ⟶ B} {fbd : B ⟶ D} {fac : A ⟶ C} {fcd : C ⟶ D} (h : fab ≫ fbd = fac ≫ fcd) :
    explicitCokernel fab ⟶ explicitCokernel fcd :=
  @explicitCokernelDesc _ _ _ fab (fbd ≫ explicitCokernelπ _) <| by simp [reassoc_of% h]

/-- A special case of `CategoryTheory.Limits.cokernel.map_desc` adapted to `explicitCokernel`. -/
theorem ExplicitCoker.map_desc {A B C D B' D' : SemiNormedGrp.{u}}
    {fab : A ⟶ B} {fbd : B ⟶ D} {fac : A ⟶ C} {fcd : C ⟶ D} {h : fab ≫ fbd = fac ≫ fcd}
    {fbb' : B ⟶ B'} {fdd' : D ⟶ D'} {condb : fab ≫ fbb' = 0} {condd : fcd ≫ fdd' = 0} {g : B' ⟶ D'}
    (h' : fbb' ≫ g = fbd ≫ fdd') :
    explicitCokernelDesc condb ≫ g = explicitCokernel.map h ≫ explicitCokernelDesc condd := by
  delta explicitCokernel.map
  simp only [← Category.assoc, ← cancel_epi (explicitCokernelπ fab)]
  simp [Category.assoc, explicitCokernelπ_desc, h']

end ExplicitCokernel

end Cokernel

end SemiNormedGrp
