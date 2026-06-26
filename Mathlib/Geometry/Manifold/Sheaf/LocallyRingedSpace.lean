/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.Sheaf.Smooth
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.ResidueField
public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import Mathlib.CategoryTheory.Sites.JointlySurjective
public import Mathlib.CategoryTheory.Sites.MorphismProperty
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic

/-! # Smooth manifolds as locally ringed spaces

This file equips a smooth manifold with the structure of a locally ringed space.

## Main results

* `smoothSheafCommRing.isUnit_stalk_iff`: The units of the stalk at `x` of the sheaf of smooth
  functions from a smooth manifold `M` to its scalar field `𝕜`, considered as a sheaf of commutative
  rings, are the functions whose values at `x` are nonzero.

## Main definitions

* `ChartedSpace.locallyRingedSpace`: A smooth manifold can be considered as a locally ringed space.
* `ChartedSpace.locallyRingedSpaceMap`: A smooth map between smooth manifolds induces a morphism
  of locally ringed spaces.

## TODO

- Show that every morphism of locally ringed spaces between two smooth manifolds is induced
  by a smooth map via `ChartedSpace.locallyRingedSpaceMap`.

-/

@[expose] public section

noncomputable section
universe u

open scoped ContDiff

open CategoryTheory

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
def CategoryTheory.Limits.whiskeringColimIsoOfSubsingleton {J C : Type*} [Category* J] [Category* C]
    {α : Type*} [Preorder α]
    (D : α ⥤ J) [Nonempty α] [Subsingleton α] (a : α) :
    (Functor.whiskeringLeft α J C).obj D ⋙ colim ≅ (evaluation J C).obj (D.obj a) := by
  letI : OrderTop α := { top := a, le_top := by simp }
  refine NatIso.ofComponents
    (fun K ↦ ((colimitOfDiagramTerminal isTerminalTop _).coconePointUniqueUpToIso
      (colimit.isColimit _)).symm) ?_
  · intros
    apply colimit.hom_ext
    intro
    simp [← NatTrans.naturality]
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma CategoryTheory.Limits.ι_whiskeringColimIsoOfSubsingleton_hom {J C : Type*} [Category* J]
    [Category* C] {α : Type*} [Preorder α] (D : α ⥤ J) [Nonempty α] [Subsingleton α]
    (F : J ⥤ C) (a : α) :
    dsimp% colimit.ι (D ⋙ F) a ≫ ((whiskeringColimIsoOfSubsingleton D a).app F).hom = 𝟙 _ := by
  letI : OrderTop α := { top := a, le_top := by simp }
  simp [whiskeringColimIsoOfSubsingleton, show isTerminalTop.from a = 𝟙 _ from rfl]

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  {M : Type u} [TopologicalSpace M] [ChartedSpace HM M]
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
  {HN : Type*} [TopologicalSpace HN] (IN : ModelWithCorners 𝕜 EN HN)
  {N : Type u} [TopologicalSpace N] [ChartedSpace HN N]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] (IP : ModelWithCorners 𝕜 EP HP)
  {P : Type u} [TopologicalSpace P] [ChartedSpace HP P]

open AlgebraicGeometry Manifold TopologicalSpace Topology

/-- The units of the stalk at `x` of the sheaf of smooth functions from `M` to `𝕜`, considered as a
sheaf of commutative rings, are the functions whose values at `x` are nonzero. -/
theorem smoothSheafCommRing.isUnit_stalk_iff {x : M}
    (f : (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.stalk x) :
    IsUnit f ↔ f ∉ RingHom.ker (smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x) := by
  constructor
  · rintro ⟨⟨f, g, hf, hg⟩, rfl⟩ (h' : smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x f = 0)
    simpa [h'] using congr_arg (smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x) hf
  · let S := (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf
    -- Suppose that `f`, in the stalk at `x`, is nonzero at `x`
    rintro (hf : _ ≠ 0)
    -- Represent `f` as the germ of some function (also called `f`) on an open neighbourhood `U` of
    -- `x`, which is nonzero at `x`
    obtain ⟨U : Opens M, hxU, f : C^∞⟮IM, U; 𝓘(𝕜), 𝕜⟯, rfl⟩ := S.exists_germ_eq f
    have hf' : f ⟨x, hxU⟩ ≠ 0 := by
      convert! hf
      exact (smoothSheafCommRing.eval_germ U x hxU f).symm
    -- In fact, by continuity, `f` is nonzero on a neighbourhood `V` of `x`
    have H : ∀ᶠ (z : U) in 𝓝 ⟨x, hxU⟩, f z ≠ 0 := f.2.continuous.continuousAt.eventually_ne hf'
    rw [eventually_nhds_iff] at H
    obtain ⟨V₀, hV₀f, hV₀, hxV₀⟩ := H
    let V : Opens M := ⟨Subtype.val '' V₀, U.2.isOpenMap_subtype_val V₀ hV₀⟩
    have hUV : V ≤ U := Subtype.coe_image_subset (U : Set M) V₀
    have hV : V₀ = Set.range (Set.inclusion hUV) := by
      convert! (Set.range_inclusion hUV).symm
      ext y
      change _ ↔ y ∈ Subtype.val ⁻¹' Subtype.val '' V₀
      rw [Set.preimage_image_eq _ Subtype.coe_injective]
    clear_value V
    subst hV
    have hxV : x ∈ (V : Set M) := by
      obtain ⟨x₀, hxx₀⟩ := hxV₀
      convert! x₀.2
      exact congr_arg Subtype.val hxx₀.symm
    have hVf : ∀ y : V, f (Set.inclusion hUV y) ≠ 0 :=
      fun y ↦ hV₀f (Set.inclusion hUV y) (Set.mem_range_self y)
    -- Let `g` be the pointwise inverse of `f` on `V`, which is smooth since `f` is nonzero there
    let g : C^∞⟮IM, V; 𝓘(𝕜), 𝕜⟯ := ⟨(f ∘ Set.inclusion hUV)⁻¹, ?_⟩
    -- The germ of `g` is inverse to the germ of `f`, so `f` is a unit
    · refine ⟨⟨S.germ _ x (hxV) (ContMDiffMap.restrictRingHom IM 𝓘(𝕜) 𝕜 hUV f), S.germ _ x hxV g,
        ?_, ?_⟩, S.germ_res_apply hUV.hom x hxV f⟩
      · rw [← map_mul]
        -- Qualified the name to avoid Lean not finding a `OneHomClass` https://github.com/leanprover-community/mathlib4/pull/8386
        convert! RingHom.map_one _
        apply Subtype.ext
        ext y
        apply mul_inv_cancel₀
        exact hVf y
      · rw [← map_mul]
        -- Qualified the name to avoid Lean not finding a `OneHomClass` https://github.com/leanprover-community/mathlib4/pull/8386
        convert! RingHom.map_one _
        apply Subtype.ext
        ext y
        apply inv_mul_cancel₀
        exact hVf y
    · intro y
      exact (((contDiffAt_inv _ (hVf y)).contMDiffAt).comp y
        (f.contMDiff.comp (contMDiff_inclusion hUV)).contMDiffAt :)

/-- The non-units of the stalk at `x` of the sheaf of smooth functions from `M` to `𝕜`, considered
as a sheaf of commutative rings, are the functions whose values at `x` are zero. -/
theorem smoothSheafCommRing.nonunits_stalk (x : M) :
    nonunits ((smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.stalk x)
    = RingHom.ker (smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x) := by
  ext1 f
  rw [mem_nonunits_iff, not_iff_comm, Iff.comm]
  apply smoothSheafCommRing.isUnit_stalk_iff

/-- The stalks of the structure sheaf of a smooth manifold are local rings. -/
instance smoothSheafCommRing.instLocalRing_stalk (x : M) :
    IsLocalRing ((smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.stalk x) := by
  apply IsLocalRing.of_nonunits_add
  rw [smoothSheafCommRing.nonunits_stalk]
  intro f g
  exact Ideal.add_mem _

lemma smoothSheafCommRing.maximalIdeal_eq_ker_eval (x : M) :
    IsLocalRing.maximalIdeal ((smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.stalk x) =
      RingHom.ker (smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x) := by
  rw [SetLike.ext'_iff, ← smoothSheafCommRing.nonunits_stalk]
  ext
  simp

variable (M)

/-- A smooth manifold can be considered as a locally ringed space. -/
def ChartedSpace.locallyRingedSpace : LocallyRingedSpace where
  carrier := TopCat.of M
  presheaf := smoothPresheafCommRing IM 𝓘(𝕜) M 𝕜
  IsSheaf := (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).property
  isLocalRing x := smoothSheafCommRing.instLocalRing_stalk IM x

@[deprecated (since := "2026-04-01")]
alias IsManifold.locallyRingedSpace := ChartedSpace.locallyRingedSpace

open CategoryTheory Limits

variable {M IM IN}

/-- (Implementation): Use `ChartedSpace.locallyRingedSpaceMap`. -/
def ChartedSpace.locallyRingedSpaceMapAux (f : M → N) (hf : ContMDiff IM IN ∞ f) :
    (locallyRingedSpace IM M).toPresheafedSpace ⟶
      (locallyRingedSpace IN N).toPresheafedSpace where
  base := TopCat.ofHom ⟨f, hf.continuous⟩
  c := (hf.smoothSheafCommRingHom _ _ f).hom

/-- (Implementation): Use `ChartedSpace.stalkMap_locallyRingedSpaceMap_evalHom`. -/
lemma ChartedSpace.stalkMap_locallyRingedSpaceMapAux (f : M → N) (hf : ContMDiff IM IN ∞ f)
    (x : M) :
    (locallyRingedSpaceMapAux f hf).stalkMap x ≫
      smoothSheafCommRing.evalHom IM 𝓘(𝕜) M 𝕜 x =
      smoothSheafCommRing.evalHom IN 𝓘(𝕜) N 𝕜 (f x) := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hxU
  rw [PresheafedSpace.stalkMap_germ_assoc]
  ext a
  refine Eq.trans ?_ (smoothSheafCommRing.evalHom_germ _ _ _ _ _ _ _ a).symm
  apply smoothSheafCommRing.evalHom_germ

set_option backward.isDefEq.respectTransparency false in
/-- A smooth function of manifolds `f : M → N` induces a morphism of locally ringed spaces. -/
@[simps! base]
def ChartedSpace.locallyRingedSpaceMap (f : M → N) (hf : ContMDiff IM IN ∞ f) :
    locallyRingedSpace IM M ⟶ locallyRingedSpace IN N where
  __ := locallyRingedSpaceMapAux f hf
  prop x := by
    refine ⟨fun a ha ↦ ?_⟩
    rw [smoothSheafCommRing.isUnit_stalk_iff, RingHom.mem_ker] at ha ⊢
    convert! ha
    exact (congr($(stalkMap_locallyRingedSpaceMapAux f hf x) a)).symm

@[reassoc (attr := simp)]
lemma ChartedSpace.stalkMap_locallyRingedSpaceMap_evalHom (f : M → N) (hf : ContMDiff IM IN ∞ f)
    (x : M) :
    (locallyRingedSpaceMap f hf).stalkMap x ≫
      smoothSheafCommRing.evalHom IM 𝓘(𝕜) M 𝕜 x =
      smoothSheafCommRing.evalHom IN 𝓘(𝕜) N 𝕜 (f x) :=
  stalkMap_locallyRingedSpaceMapAux f hf x

variable (IM M) in
lemma ChartedSpace.locallyRingedSpace_id :
    locallyRingedSpaceMap (IM := IM) (IN := IM) (M := M) id contMDiff_id = 𝟙 _ :=
  rfl

lemma ChartedSpace.locallyRingedSpace_comp {f : M → N} (hf : ContMDiff IM IN ∞ f)
    {g : N → P} (hg : ContMDiff IN IP ∞ g) :
    locallyRingedSpaceMap (g ∘ f) (hg.comp hf) =
      locallyRingedSpaceMap f hf ≫ locallyRingedSpaceMap g hg :=
  rfl

-- TODO: This holds more generally if `U` is replaced by an open embedding that
-- is also a smooth immersion.
instance (U : Opens M) :
    LocallyRingedSpace.IsOpenImmersion
      (ChartedSpace.locallyRingedSpaceMap _ (contMDiff_subtype_val (I := IM) (U := U))) where
  base_open := U.isOpenEmbedding'
  c_iso V := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun a b hab ↦ Subtype.ext ?_, fun ⟨g, hg⟩ ↦ ?_⟩
    · ext ⟨x, y, hy, rfl⟩
      exact congr($(hab).1 ⟨y, ⟨y, hy, rfl⟩⟩)
    · let a : TopCat.of U ⟶ TopCat.of M := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
      have ha : IsOpenEmbedding a.hom := U.isOpenEmbedding'
      let V' : Opens U := (Opens.map a).obj (ha.isOpenMap.functor.obj V)
      let b : V' ≃ₜ ha.isOpenMap.functor.obj V :=
        U.isOpenEmbedding'.homeomorphOfSubsetRange <| Set.image_subset_range _ V.1
      refine ⟨⟨g ∘ b.symm, ContMDiff.comp hg ?_⟩, Subtype.ext <| funext fun _ ↦ ?_⟩
      · refine (ContMDiff.subtypeVal_comp_iff V' _).mp ?_
        rw [← ContMDiff.subtypeVal_comp_iff]
        convert! contMDiff_subtype_val
        ext x
        exact congr($(b.apply_symm_apply x).1)
      · change g _ = _
        congr
        apply b.symm_apply_apply

/-- Viewing a manifold as a locally ringed space commutes with restriction to open subsets. -/
@[simps]
def ChartedSpace.restrictLocallyRingedSpaceIso (U : Opens M) :
    (locallyRingedSpace IM M).restrict U.isOpenEmbedding ≅
      locallyRingedSpace IM U where
  hom := LocallyRingedSpace.IsOpenImmersion.lift
    (locallyRingedSpaceMap _ contMDiff_subtype_val)
    (LocallyRingedSpace.ofRestrict _ _) (by rfl)
  inv := LocallyRingedSpace.IsOpenImmersion.lift
    ((locallyRingedSpace IM M).ofRestrict U.isOpenEmbedding)
    (locallyRingedSpaceMap _ contMDiff_subtype_val) (by rfl)
  hom_inv_id := by
    simp [← cancel_mono ((locallyRingedSpace IM M).ofRestrict U.isOpenEmbedding)]
  inv_hom_id := by
    simp [← cancel_mono (locallyRingedSpaceMap _ contMDiff_subtype_val)]

/-- `Γ(X, U)` is notation for `X.presheaf.obj (op U)`. -/
scoped[AlgebraicGeometry.LocallyRingedSpace] notation3 "Γ(" X ", " U ")" =>
  (PresheafedSpace.presheaf (SheafedSpace.toPresheafedSpace
    (LocallyRingedSpace.toSheafedSpace X))).obj
    (Opposite.op (α := TopologicalSpace.Opens _) U)

open scoped AlgebraicGeometry.LocallyRingedSpace

def AlgebraicGeometry.LocallyRingedSpace.residue {X : LocallyRingedSpace.{u}} (x : X) :
    X.presheaf.stalk x ⟶ X.residueField x :=
  CommRingCat.ofHom (IsLocalRing.residue (X.presheaf.stalk x))

@[reassoc]
lemma AlgebraicGeometry.LocallyRingedSpace.residue_residueFieldMap
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) :
    Y.residue (f.base x) ≫ residueFieldMap f x = f.stalkMap x ≫ X.residue x :=
  rfl

@[reassoc (attr := simp)]
lemma AlgebraicGeometry.LocallyRingedSpace.Hom.germ_stalkMap {X Y : LocallyRingedSpace.{u}}
    (f : X ⟶ Y) (U : Opens Y) (x : X) (hx : f.base x ∈ U) :
    Y.presheaf.germ U (f.base x) hx ≫ f.stalkMap x = f.c.app _ ≫ X.presheaf.germ _ _ hx :=
  PresheafedSpace.stalkMap_germ _ _ _ _

-- def TopCat.Sheaf.constant

/-- Order isomorphism between `Set α` and `α → Prop`. -/
def Set.orderIsoFun (α : Type*) : Set α ≃o (α → Prop) where
  toFun s := (· ∈ s)
  invFun p := setOf p
  map_rel_iff' := .rfl

/-- `Equiv.punitArrowEquiv` as an `OrderIso`. -/
def OrderIso.pUnitArrowEquiv (α : Type*) [LE α] : (PUnit → α) ≃o α :=
  .symm <|
  { __ := (Equiv.punitArrowEquiv _).symm
    map_rel_iff' {a b} := by
      simp [Pi.le_def, Equiv.punitArrowEquiv] }

/-- Opens on a discrete topological space are all sets. -/
def TopologicalSpace.Opens.orderIsoSet (α : Type*) [TopologicalSpace α] [DiscreteTopology α] :
    Opens α ≃o Set α where
  toFun U := U.carrier
  invFun s := ⟨s, isOpen_discrete s⟩
  map_rel_iff' := .rfl

/-- `Prop` is order isomorphic to `Bool`. -/
@[simps!]
def OrderIso.propBool : Prop ≃o Bool :=
  .symm <|
  { __ := Equiv.propEquivBool.symm
    map_rel_iff' := .rfl }

@[simp]
lemma Equiv.propEquivBool_false : Equiv.propEquivBool False = false := by
  simp [Equiv.propEquivBool]

@[simp]
lemma Equiv.propEquivBool_true : Equiv.propEquivBool True = true := by
  simp [Equiv.propEquivBool]

@[simp]
lemma Equiv.propEquivBool_symm_true : Equiv.propEquivBool.symm true = True := by
  simp [Equiv.propEquivBool]

@[simp]
lemma Equiv.propEquivBool_symm_false : Equiv.propEquivBool.symm false = False := by
  simp [Equiv.propEquivBool]

/-- The opens on `PUnit` are order isomorphic to `Prop`. -/
def TopologicalSpace.Opens.pUnitOrderIso : Opens PUnit.{u + 1} ≃o Prop :=
  (TopologicalSpace.Opens.orderIsoSet _).trans <|
    (Set.orderIsoFun _).trans (OrderIso.pUnitArrowEquiv _)

/-- `Fin 2` is order isomorphic to `Bool`. -/
@[simps!]
def finTwoOrderIsoBool : OrderIso (Fin 2) Bool :=
  .symm <|
  { __ := finTwoEquiv.symm
    map_rel_iff' {a b} := by rcases a <;> rcases b <;> simp [finTwoEquiv] }

@[simp]
lemma finTwoEquiv_zero : finTwoEquiv 0 = false := rfl

@[simp]
lemma finTwoEquiv_one : finTwoEquiv 1 = true := rfl

@[simp]
lemma finTwoEquiv_symm_false : finTwoEquiv.symm false = 0 := rfl

@[simp]
lemma finTwoEquiv_symm_true : finTwoEquiv.symm true = 1 := rfl

@[simps!]
def TopologicalSpace.Opens.pUnitOrderIsoFinTwo :
    TopologicalSpace.Opens PUnit.{u + 1} ≃o Fin 2 :=
  Opens.pUnitOrderIso.trans (OrderIso.propBool.trans finTwoOrderIsoBool.symm)

@[simp]
lemma TopologicalSpace.Opens.pUnitOrderIsoFinTwo_symm_zero :
    pUnitOrderIsoFinTwo.symm 0 = ⊥ := by
  simp only [Fin.isValue, map_eq_bot_iff]
  rfl

@[simp]
lemma TopologicalSpace.Opens.pUnitOrderIsoFinTwo_bot :
    pUnitOrderIsoFinTwo ⊥ = 0 := by
  rw [map_bot]
  rfl

@[simp]
lemma TopologicalSpace.Opens.pUnitOrderIsoFinTwo_top :
    pUnitOrderIsoFinTwo ⊤ = 1 := by
  simp only [TopHomClass.map_top, Fin.isValue]
  rfl

@[simps]
def TopCat.Sheaf.star {C : Type*} [Category* C] {T : C} (hT : IsTerminal T) (A : C) :
    TopCat.Sheaf C (.of PUnit.{u + 1}) where
  obj := TopologicalSpace.Opens.pUnitOrderIsoFinTwo.toOrderEmbedding.toOrderHom.toFunctor.op ⋙
    Functor.leftOp (ComposableArrows.mk₁ (hT.from A).op)
  property := by
    rw [← TopCat.Presheaf.IsSheaf, TopCat.Presheaf.isSheaf_on_punit_iff_isTerminal]
    simpa using ⟨hT⟩

lemma CategoryTheory.Presieve.isSheafFor_of_isInitial_of_isTerminal
    {C A : Type*} [Category* C] [Category* A] [HasStrictInitialObjects C]
    (U : C) (hU : IsInitial U)
    (F : Cᵒᵖ ⥤ A) (R : Presieve U) (M : A) (hF : IsTerminal (F.obj (.op U))) :
    Presieve.IsSheafFor (F ⋙ coyoneda.obj (.op M)) R := by
  intro _ _
  rw [@existsUnique_iff_exists _ ⟨fun _ _ => _⟩]
  · refine ⟨hF.from _, fun V f hs ↦ IsTerminal.hom_ext ?_ _ _⟩
    have : IsIso f := IsInitial.isIso_to hU f
    exact .ofIso hF (F.mapIso (asIso f).op)
  · exact hF.hom_ext

lemma Presheaf.IsSheaf.iff_of_equivalence {C D A : Type*} [Category* C] [Category* D]
      [Category* A] (F : C ≌ D)
      (P : Cᵒᵖ ⥤ A) (J : GrothendieckTopology D) :
    Presheaf.IsSheaf (F.functor.inducedTopology J) P ↔ Presheaf.IsSheaf J (F.inverse.op ⋙ P) := by
  refine ⟨?_, ?_⟩
  · intro hP
    exact Functor.op_comp_isSheaf_of_isSheaf _ _ (F.functor.inducedTopology J) _ hP
  · intro hP
    let e : P ≅ F.functor.op ⋙ F.inverse.op ⋙ P :=
      (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight
          ((Functor.opId _).symm ≪≫ NatIso.op F.unitIso.symm ≪≫ Functor.opComp _ _) _ ≪≫
        Functor.associator _ _ _
    rw [Presheaf.isSheaf_of_iso_iff e]
    exact Functor.op_comp_isSheaf_of_isSheaf _ _ _ _ hP

lemma isSheaf_inducedTopology_finTwo {C : Type*} [Category* C] (F : (Fin 2)ᵒᵖ ⥤ C) :
    Presheaf.IsSheaf
      (Functor.inducedTopology
        TopologicalSpace.Opens.pUnitOrderIsoFinTwo.symm.equivalence.functor
        (Opens.grothendieckTopology PUnit)) F ↔
      Nonempty (IsTerminal (F.obj <| .op 0)) := by
  rw [Presheaf.IsSheaf.iff_of_equivalence]
  change TopCat.Presheaf.IsSheaf (X := .of PUnit) _ ↔ _
  rw [TopCat.Presheaf.isSheaf_on_punit_iff_isTerminal]
  congr! 5
  simp
  rfl

lemma Opens.bot_mem_grothendieckTopology_iff (X : TopCat.{u}) (U : Opens X) :
    ⊥ ∈ grothendieckTopology X U ↔ U = ⊥ := by
  rw [mem_grothendieckTopology]
  cat_disch

@[simp]
lemma Opens.bot_mem_grothendieckTopology_bot (X : TopCat.{u}) : ⊥ ∈ grothendieckTopology X ⊥ := by
  rw [bot_mem_grothendieckTopology_iff]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
def CategoryTheory.sheafFinTwoEquivOfIsTerminal {C : Type*} [Category* C] {T : C}
    (hT : IsTerminal T) :
    Sheaf (Opens.pUnitOrderIsoFinTwo.symm.equivalence.functor.inducedTopology
      (Opens.grothendieckTopology PUnit)) C ≌ C where
  functor := ObjectProperty.ι _ ⋙ (evaluation _ _).obj (.op ⊤)
  inverse.obj A :=
    ⟨Functor.leftOp (ComposableArrows.mk₁ (hT.from A).op), by
      rw [isSheaf_inducedTopology_finTwo]
      exact ⟨hT⟩⟩
  inverse.map f :=
    ObjectProperty.homMk <|
      NatTrans.leftOp <| ComposableArrows.homMk₁ (𝟙 _) f.op (by apply Quiver.Hom.unop_inj; simp)
  inverse.map_id X := by
    ext ⟨i⟩
    cat_disch
  inverse.map_comp {X Y Z} f g := by
    ext ⟨i⟩
    cat_disch
  unitIso := by
    refine NatIso.ofComponents ?_ ?_
    · intro F
      refine ObjectProperty.isoMk _ ?_
      refine NatIso.ofComponents ?_ ?_
      · intro ⟨i⟩
        match i with
        | 0 =>
          refine (hT.uniqueUpToIso <| F.isTerminalOfBotCover 0 ?_).symm
          rw [Functor.mem_inducedTopology_iff_of_isCoverDense, Sieve.functorPushforward_bot]
          have : Opens.pUnitOrderIsoFinTwo.{u}.symm.equivalence.functor.obj 0 = ⊥ := by
            simp
          rw [this]
          exact Opens.bot_mem_grothendieckTopology_bot (.of PUnit.{u + 1})
        | 1 => exact Iso.refl _
      · intro ⟨i⟩ ⟨j⟩ u
        match i, j, u with
        | 0, 0, _ => simp
        | 0, 1, _ => dsimp; grind
        | 1, 0, _ => simp
        | 1, 1, u =>
          obtain rfl : u = 𝟙 _ := Subsingleton.elim _ _
          simp
    · intro F G u
      ext ⟨i⟩
      cat_disch
  counitIso := .refl _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
def TopCat.Sheaf.pUnitEquivOfIsTerminal {C : Type*} [Category* C] {T : C} (hT : IsTerminal T) :
    TopCat.Sheaf C (.of PUnit.{u + 1}) ≌ C :=
  .trans (Opens.pUnitOrderIsoFinTwo.symm.equivalence.sheafCongr _ _ _).symm
    (sheafFinTwoEquivOfIsTerminal hT)

def TopCat.Sheaf.pUnitEquivOfIsTerminalInverseObjIso {C : Type*} [Category* C] {T : C}
    (hT : IsTerminal T) (A : C) :
    ((pUnitEquivOfIsTerminal.{u} hT).inverse.obj A).presheaf.obj (.op ⊤) ≅ A :=
  ((sheafFinTwoEquivOfIsTerminal.{u} hT).inverse.obj A).obj.mapIso
    (eqToIso <| show _ = .op 1 by simp; rfl)

instance (X : TopCat) [IndiscreteTopology X] (x : X) : Subsingleton (OpenNhds x) where
  allEq
    | ⟨U, hU⟩, ⟨V, hV⟩ => by
      obtain (rfl | rfl) := TopologicalSpace.Opens.eq_bot_or_top U <;>
      obtain (rfl | rfl) := TopologicalSpace.Opens.eq_bot_or_top V <;>
      simp at hU hV ⊢

def OpenNhds.orderIsoOfIndiscreteTopology (X : TopCat) [IndiscreteTopology X] (x : X) :
    OpenNhds x ≃o PUnit.{u + 1} where
  toFun _ := ⟨⟩
  invFun _ := ⟨⟨Set.univ, isOpen_univ⟩, by simp⟩
  left_inv U := Subsingleton.elim _ _
  map_rel_iff' {a b} := by
    obtain rfl := Subsingleton.elim a b
    simp

def TopCat.Presheaf.stalkFunctorIsoOfIndiscreteTopology {C : Type*} [Category* C]
    [HasColimits C] (X : TopCat) [IndiscreteTopology X] (x : X) :
    TopCat.Presheaf.stalkFunctor C x ≅ (evaluation _ _).obj (.op ⊤) :=
  Functor.isoWhiskerLeft _
    (Functor.Final.colimIso <| (orderDualEquivalence _).functor ⋙
      (OpenNhds.orderIsoOfIndiscreteTopology.{0} X x).equivalence.inverse.op).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.whiskeringLeftObjCompIso _ _).symm _ ≪≫
    CategoryTheory.Limits.whiskeringColimIsoOfSubsingleton _ ⟨⟩

/-- The stalk of a presheaf `F` on an indiscrete topological space is isomorphic to the global
sections of `F`. -/
abbrev TopCat.Presheaf.stalkIsoOfIndiscreteTopology {C : Type*} [Category* C]
    [HasColimits C] (X : TopCat) [IndiscreteTopology X] (F : TopCat.Presheaf C X) (x : X) :
    F.stalk x ≅ F.obj (.op ⊤) :=
  (TopCat.Presheaf.stalkFunctorIsoOfIndiscreteTopology _ _).app F

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma TopCat.Presheaf.germ_stalkIsoOfIndiscreteTopology_hom {C : Type*} [Category* C]
    [HasColimits C] (X : TopCat) [IndiscreteTopology X] (F : TopCat.Presheaf C X) (x : X) :
    F.germ ⊤ _ (by simp) ≫ (F.stalkIsoOfIndiscreteTopology X x).hom = 𝟙 _ := by
  let G := (orderDualEquivalence PUnit.{1}).functor ⋙
    (OpenNhds.orderIsoOfIndiscreteTopology X x).equivalence.inverse.op
  change colimit.ι ((OpenNhds.inclusion x).op ⋙ F) (G.obj PUnit.unit) ≫ _ ≫ _ = _
  have := Functor.Final.ι_colimitIso_inv G ((OpenNhds.inclusion _).op ⋙ F) ⟨⟩
  dsimp [G] at this
  simp [Functor.Final.colimIso, G, reassoc_of% this]
  rfl

/-- The stalk of the sheaf on the point induced by `A` is isomorphic to `A`. -/
abbrev TopCat.Sheaf.pUnitEquivOfIsTerminalStalkIso {C : Type*} [Category* C] [HasColimits C]
    {T : C} (hT : IsTerminal T) (A : C) (x : PUnit) :
    ((TopCat.Sheaf.pUnitEquivOfIsTerminal hT).inverse.obj A).presheaf.stalk x ≅ A :=
  TopCat.Presheaf.stalkIsoOfIndiscreteTopology _ _ _ ≪≫
    TopCat.Sheaf.pUnitEquivOfIsTerminalInverseObjIso _ _

/-- The sheafed space on the point with stalk given by `A`. -/
@[implicit_reducible]
def AlgebraicGeometry.SheafedSpace.pUnit {C : Type*} [Category* C] {T : C} (hT : IsTerminal T)
    (A : C) :
    SheafedSpace.{_, _, u} C where
  carrier := .of PUnit.{u + 1}
  presheaf := ((TopCat.Sheaf.pUnitEquivOfIsTerminal hT).inverse.obj A).presheaf
  IsSheaf := ((TopCat.Sheaf.pUnitEquivOfIsTerminal hT).inverse.obj A).property

/-- The stalk of `AlgebraicGeometry.SheafedSpace.pUnit` is `A`. -/
abbrev AlgebraicGeometry.SheafedSpace.pUnitStalkIso {C : Type*} [Category* C] [HasColimits C]
    {T : C} (hT : IsTerminal T) (A : C) (x : PUnit) :
    (AlgebraicGeometry.SheafedSpace.pUnit hT A).presheaf.stalk x ≅ A :=
  TopCat.Sheaf.pUnitEquivOfIsTerminalStalkIso _ _ _

/-- The locally ringed space on the point with stalk given by the local ring `R`. -/
@[implicit_reducible]
def AlgebraicGeometry.LocallyRingedSpace.pUnit (R : CommRingCat.{u}) [IsLocalRing R] :
    LocallyRingedSpace.{u} where
  __ := SheafedSpace.pUnit CommRingCat.punitIsTerminal (.of R)
  isLocalRing x :=
    RingEquiv.isLocalRing
      (SheafedSpace.pUnitStalkIso CommRingCat.punitIsTerminal R x).commRingCatIsoToRingEquiv.symm

/-- The stalk of `AlgebraicGeometry.LocallyRingedSpace.pUnit R` is `R`. -/
abbrev AlgebraicGeometry.LocallyRingedSpace.pUnitStalkIso (R : CommRingCat.{u}) [IsLocalRing R]
    (x : PUnit) : (pUnit R).presheaf.stalk x ≅ R :=
  AlgebraicGeometry.SheafedSpace.pUnitStalkIso _ _ _

namespace ChartedSpace

variable (IM) in
def evaluation (x : M) : (locallyRingedSpace IM M).presheaf.stalk x ⟶ .of 𝕜 :=
  smoothSheafCommRing.evalHom IM 𝓘(𝕜) M 𝕜 x

lemma ker_evaluation (x : M) :
    RingHom.ker (evaluation IM x).hom = IsLocalRing.maximalIdeal _ :=
  (smoothSheafCommRing.maximalIdeal_eq_ker_eval _ _).symm

@[simp]
lemma evaluation_germ (U : Opens M) (x : M) (hx : x ∈ U)
    (g : Γ(locallyRingedSpace IM M, U)) :
    evaluation IM x ((locallyRingedSpace IM M).presheaf.germ U x hx g) = g.val ⟨x, hx⟩ :=
  smoothSheafCommRing.eval_germ _ _ _ _

@[simp]
lemma evaluation_germ_coe (U : Opens M) (x : U)
    (g : Γ(locallyRingedSpace IM M, U)) :
    evaluation IM x.1 ((locallyRingedSpace IM M).presheaf.germ U x.1 x.2 g) = g.val x :=
  smoothSheafCommRing.eval_germ _ _ _ _

instance : ChartedSpace HM (locallyRingedSpace IM M).toPresheafedSpace :=
  inferInstanceAs <| ChartedSpace HM M

variable (IM) in
def residueIso (x : M) : (locallyRingedSpace IM M).residueField x ≅ .of 𝕜 :=
  RingEquiv.toCommRingCatIso <|
    RingEquiv.trans (Ideal.quotEquivOfEq (ker_evaluation _).symm)
    (RingHom.quotientKerEquivOfSurjective
    (smoothSheafCommRing.eval_surjective IM 𝓘(𝕜) M 𝕜 x))



@[reassoc (attr := simp)]
lemma residue_residueIso_hom (x : M) :
    (locallyRingedSpace IM M).residue x ≫ (residueIso IM x).hom = evaluation IM x :=
  rfl

instance (U : Opens M) : Algebra 𝕜 Γ(locallyRingedSpace IM M, U) :=
  --inferInstanceAs <| Algebra 𝕜 ((smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.obj _)
  sorry

instance (x : M) : Algebra 𝕜 ((locallyRingedSpace IM M).presheaf.stalk x) :=
  sorry

instance (x : M) : Algebra 𝕜 ((locallyRingedSpace IM M).residueField x) :=
  inferInstanceAs <| Algebra 𝕜 (IsLocalRing.ResidueField _)

@[reassoc (attr := simp)]
lemma algebraMap_residueField (x : M) :
    CommRingCat.ofHom (algebraMap 𝕜 <| (locallyRingedSpace IM M).residueField x) =
      (residueIso IM x).inv :=
  sorry

-- def asdfasdf : locallyRingedSpace IM PUnit ⟶ _ := sorry

@[reassoc (attr := simp)]
lemma stalkMap_evaluation (f : locallyRingedSpace IM M ⟶ locallyRingedSpace IN N) (x : M) :
    f.stalkMap x ≫ evaluation IM x = evaluation IN (f.base x) := by
  rw [← residue_residueIso_hom, ← residue_residueIso_hom]
  rw [← LocallyRingedSpace.residue_residueFieldMap_assoc]
  congr 1
  rw [← cancel_epi (residueIso _ _).inv]
  conv_lhs => rw [← algebraMap_residueField]
  erw [Iso.inv_hom_id]
  sorry

end ChartedSpace

set_option backward.isDefEq.respectTransparency false in
lemma ChartedSpace.app_apply (f : locallyRingedSpace IM M ⟶ locallyRingedSpace IN N)
    (U : Opens N) (g) (x : ((Opens.map f.base).op.obj (Opposite.op U)).unop) :
    (f.c.app (.op U) g).val x = g.val ⟨f.base x.1, x.2⟩ := by
  dsimp
  rw [← evaluation_germ]
  rw [← evaluation_germ_coe]
  simp only [← ConcreteCategory.comp_apply]
  erw [← ConcreteCategory.comp_apply]
  rw [← LocallyRingedSpace.Hom.germ_stalkMap_assoc]
  simp

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {EM : Type u} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type u} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  {M : Type u} [TopologicalSpace M] [ChartedSpace HM M]

def ModelWithCorners.locallyRingedSpace : LocallyRingedSpace.{u} :=
  ChartedSpace.locallyRingedSpace IM HM

namespace AlgebraicGeometry

namespace LocallyRingedSpace

instance : MorphismProperty.IsMultiplicative @IsOpenImmersion where
  id_mem _ := inferInstance
  comp_mem _ _ _ _ := inferInstance

instance : MorphismProperty.RespectsIso @IsOpenImmersion where
  precomp _ (_ : IsIso _) _ _ := inferInstance
  postcomp _ (_ : IsIso _) _ _ := inferInstance

instance : MorphismProperty.IsStableUnderBaseChange @IsOpenImmersion :=
  .mk' fun _ _ _ _ _ _ _ ↦ inferInstance

def zariskiPrecoverage : Precoverage LocallyRingedSpace :=
    Types.jointlySurjectivePrecoverage.comap (LocallyRingedSpace.forgetToTop ⋙ forget TopCat) ⊓
      MorphismProperty.precoverage @IsOpenImmersion
  deriving Precoverage.IsStableUnderComposition, Precoverage.HasIsos

lemma ofArrows_mem_zariskiPrecoverage_iff {ι : Type*} {X : LocallyRingedSpace.{u}}
    {Y : ι → LocallyRingedSpace.{u}} (f : ∀ i, Y i ⟶ X) :
    Presieve.ofArrows Y f ∈ zariskiPrecoverage X ↔
      (∀ x, ∃ i, x ∈ Set.range (f i).base) ∧ ∀ i, IsOpenImmersion (f i) := by
  change _ ∧ _ ↔ _
  simp only [Precoverage.mem_comap_iff, Presieve.map_ofArrows, Functor.comp_map, forgetToTop_map,
    Types.ofArrows_mem_jointlySurjectivePrecoverage_iff, Set.mem_range,
    MorphismProperty.ofArrows_mem_precoverage, and_congr_left_iff]
  intro
  rfl

lemma Hom.isOpenEmbedding {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    IsOpenEmbedding f.base :=
  PresheafedSpace.IsOpenImmersion.base_open

def Hom.opensRange {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    Opens Y :=
  ⟨Set.range f.base, f.isOpenEmbedding.isOpen_range⟩

instance {X : LocallyRingedSpace.{u}} (𝒰 : zariskiPrecoverage.ZeroHypercover X) (i : 𝒰.I₀) :
    IsOpenImmersion (𝒰.f i) :=
  𝒰.mem₀.right ⟨i⟩

@[simp]
lemma range_ofRestrict {U : TopCat.{u}} {X : LocallyRingedSpace.{u}} {f : U ⟶ X.toTopCat}
    (h : IsOpenEmbedding f) :
    Set.range (X.ofRestrict h).base = Set.range f :=
  rfl

lemma Hom.isHomeomorph {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) [IsIso f] :
    IsHomeomorph f.base := by
  rw [← TopCat.isIso_iff_isHomeomorph]
  exact Functor.map_isIso LocallyRingedSpace.forgetToTop f

@[simps]
def restrictCongr {X : LocallyRingedSpace.{u}} {U V : TopCat.{u}} {f : U ⟶ X.toTopCat}
    (hf : IsOpenEmbedding f)
    {g : V ⟶ X.toTopCat} (hg : IsOpenEmbedding g)
    (H : Set.range f = Set.range g) :
    X.restrict hf ≅ X.restrict hg where
  hom := IsOpenImmersion.lift (X.ofRestrict hg) (X.ofRestrict hf) <| by
    rw [range_ofRestrict, range_ofRestrict, H]
  inv := IsOpenImmersion.lift (X.ofRestrict hf) (X.ofRestrict hg) <| by
    rw [range_ofRestrict, range_ofRestrict, H]
  hom_inv_id := by simp [← cancel_mono (X.ofRestrict hf)]
  inv_hom_id := by simp [← cancel_mono (X.ofRestrict hg)]

end LocallyRingedSpace

/-- A locally ringed space `X` is a manifold for a given model with corners, if it is locally
isomorphic to open subsets of `HM`. -/
class LocallyRingedSpace.IsManifold (H : ModelWithCorners 𝕜 EM HM) (X : LocallyRingedSpace.{u}) :
    Prop where
  exists_isOpenImmersion (H) : ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U)
    (f : X.restrict U.isOpenEmbedding ⟶ ChartedSpace.locallyRingedSpace H HM),
    LocallyRingedSpace.IsOpenImmersion f

namespace LocallyRingedSpace.IsManifold

variable {H : ModelWithCorners 𝕜 EM HM}

set_option backward.isDefEq.respectTransparency false in
variable (H) in
lemma exists_nonempty_iso {X : LocallyRingedSpace.{u}} [X.IsManifold H] (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U) (V : Opens HM),
      Nonempty (X.restrict U.isOpenEmbedding ≅ ChartedSpace.locallyRingedSpace H V) := by
  obtain ⟨U, hxU, f, hf⟩ := exists_isOpenImmersion H x
  use U, hxU, f.opensRange
  refine ⟨IsOpenImmersion.isoRestrict f ≪≫ ?_ ≪≫ ChartedSpace.restrictLocallyRingedSpaceIso _⟩
  exact restrictCongr _ _ Subtype.range_coe_subtype.symm

variable (H) in
def euclideanOpen (X : LocallyRingedSpace.{u}) [X.IsManifold H] (x : X) :
    Opens HM :=
  (exists_nonempty_iso H x).choose_spec.choose_spec.choose

variable (H) in
def euclideanPoint (X : LocallyRingedSpace.{u}) [X.IsManifold H] (x : X) :
    euclideanOpen H X x :=
  (exists_nonempty_iso H x).choose_spec.choose_spec.choose_spec.some.hom.base
    ⟨x, (exists_nonempty_iso H x).choose_spec.choose⟩

instance (X : LocallyRingedSpace.{u}) [X.IsManifold H] (x : X) :
    Nonempty (euclideanOpen H X x) :=
  ⟨euclideanPoint H X x⟩

variable (H) in
def euclideanCover (X : LocallyRingedSpace.{u}) [X.IsManifold H] :
    zariskiPrecoverage.ZeroHypercover X where
  I₀ := X
  X x := ChartedSpace.locallyRingedSpace H (euclideanOpen H X x)
  f x :=
    (exists_nonempty_iso H x).choose_spec.choose_spec.choose_spec.some.inv ≫ (X.ofRestrict _)
  mem₀ := by
    rw [ofArrows_mem_zariskiPrecoverage_iff]
    refine ⟨fun x ↦ ⟨x, ?_⟩, ?_⟩
    · dsimp
      rw [Function.Surjective.range_comp]
      · exact ⟨⟨x, (exists_nonempty_iso H x).choose_spec.choose⟩, rfl⟩
      · exact (Hom.isHomeomorph _).surjective
    · intro i
      infer_instance

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma euclideanCover_f_euclideanPoint (X : LocallyRingedSpace.{u}) [X.IsManifold H] (x : X) :
    ((euclideanCover H X).f x).base (euclideanPoint H X x) = x := by
  simp only [euclideanCover, comp_toHom, PresheafedSpace.comp_base, TopCat.hom_comp, euclideanPoint,
    ContinuousMap.comp_apply]
  erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  simp only [← comp_base, Iso.hom_inv_id_assoc]
  rfl

variable (H) in
set_option backward.isDefEq.respectTransparency false in
def chartAt (X : LocallyRingedSpace.{u}) [X.IsManifold H] (x : X) :
    OpenPartialHomeomorph X HM :=
  haveI : Nonempty HM := Nonempty.map (Subtype.val : euclideanOpen H X x → _) inferInstance
  .lift_openEmbedding
    (Topology.IsOpenEmbedding.toOpenPartialHomeomorph (Subtype.val : euclideanOpen H X x → _)
      ((euclideanOpen H X x).isOpen.isOpenEmbedding_subtypeVal))
    ((euclideanCover H X).f x).isOpenEmbedding

variable (H) in
abbrev chartedSpace (X : LocallyRingedSpace) [X.IsManifold H] :
    ChartedSpace HM X where
  atlas := Set.range (chartAt H X)
  chartAt x := chartAt H X x
  mem_chart_source x := ⟨euclideanPoint H X x, by simp, by simp⟩
  chart_mem_atlas x := ⟨x, rfl⟩

instance (X : LocallyRingedSpace) [X.IsManifold H] :
    letI := chartedSpace H X
    _root_.IsManifold H ∞ X := by
  letI := chartedSpace H X
  apply isManifold_of_contDiffOn
  rintro - - ⟨x, rfl⟩ ⟨y, rfl⟩
  -- possibly only true under stronger hypotheses on `𝕜` and `EM`
  sorry

end LocallyRingedSpace.IsManifold

end AlgebraicGeometry
