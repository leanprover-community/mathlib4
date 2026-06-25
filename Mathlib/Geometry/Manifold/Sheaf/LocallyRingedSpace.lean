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

def Set.orderIsoFun (α : Type*) : Set α ≃o (α → Prop) where
  toFun s := (· ∈ s)
  invFun p := setOf p
  map_rel_iff' := .rfl

def OrderIso.punitArrowEquiv (α : Type*) [LE α] : (PUnit → α) ≃o α :=
  .symm <|
  { __ := (Equiv.punitArrowEquiv _).symm
    map_rel_iff' {a b} := by
      simp [Pi.le_def, Equiv.punitArrowEquiv] }

def asdfasdfasdfadsf : Set PUnit ≃o Prop :=
  (Set.orderIsoFun _).trans (OrderIso.punitArrowEquiv _)

def TopologicalSpace.Opens.orderIsoSet (α : Type*) [TopologicalSpace α] [DiscreteTopology α] :
    Opens α ≃o Set α where
  toFun U := U.carrier
  invFun s := ⟨s, isOpen_discrete s⟩
  map_rel_iff' := .rfl

def OrderIso.propBool : Prop ≃o Bool :=
  .symm <|
  { __ := Equiv.propEquivBool.symm
    map_rel_iff' := .rfl }

/-- The opens on `PUnit` are order isomorphic to `Prop`. -/
def TopologicalSpace.Opens.pUnitOrderIso : Opens PUnit.{u + 1} ≃o Prop :=
  (TopologicalSpace.Opens.orderIsoSet _).trans <|
    (Set.orderIsoFun _).trans (OrderIso.punitArrowEquiv _)

section

variable {C : Type*} [Category* C]

def CategoryTheory.Functor.fromBool {X Y : C} (f : X ⟶ Y) : Bool ⥤ C where
  obj
    | .false => X
    | .true => Y
  map {X Y} u :=
    match X, Y, u with
    | .true, .true, _ => 𝟙 _
    | .false, .true, _ => f
    | .true, .false, u => False.elim (by have := leOfHom u; contradiction)
    | .false, .false, _ => 𝟙 _
  map_comp := by grind

@[simp]
lemma CategoryTheory.Functor.fromBool_obj_true {X Y : C} (f : X ⟶ Y) :
    (fromBool f).obj .true = Y :=
  rfl

@[simp]
lemma CategoryTheory.Functor.fromBool_obj_false {X Y : C} (f : X ⟶ Y) :
    (fromBool f).obj .false = X :=
  rfl

lemma Bool.antitone_not : Antitone Bool.not :=
  fun b b' hbb' ↦ by rcases b <;> rcases b' <;> grind

def CategoryTheory.Functor.fromBoolOp {X Y : C} (f : X ⟶ Y) : Boolᵒᵖ ⥤ C where
  obj b := (Functor.fromBool f).obj b.unop.not
  map {b b'} u := (Functor.fromBool f).map (homOfLE <| Bool.antitone_not (leOfHom u.unop))
  map_comp := by simp [← Functor.map_comp]

@[simp]
lemma CategoryTheory.Functor.fromBoolOp_obj_true {X Y : C} (f : X ⟶ Y) :
    (fromBoolOp f).obj (.op .true) = X :=
  rfl

@[simp]
lemma CategoryTheory.Functor.fromBoolOp_obj_false {X Y : C} (f : X ⟶ Y) :
    (fromBoolOp f).obj (.op .false) = Y :=
  rfl

end

def TopCat.Sheaf.asdfasdf {C : Type*} [Category* C] (T : C) (hT : IsTerminal T) :
    TopCat.Sheaf C (.of PUnit.{u + 1}) ≌ C where
  functor := ObjectProperty.ι _ ⋙ (evaluation _ _).obj (.op ⊤)
  inverse.obj A :=
    ⟨Opens.pUnitOrderIso.toOrderEmbedding.toOrderHom.toFunctor.op ⋙
     OrderIso.propBool.toOrderEmbedding.toOrderHom.toFunctor.op ⋙
     Functor.fromBoolOp (hT.from A),
     sorry⟩
  inverse.map := sorry
  inverse.map_id := sorry
  inverse.map_comp := sorry
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry

def AlgebraicGeometry.SheafedSpace.pUnit {C : Type*} [Category* C] (A : C) :
    SheafedSpace.{_, _, u} C where
  carrier := .of PUnit.{u + 1}
  presheaf := sorry
  IsSheaf := sorry

-- def AlgebraicGeometry.SheafedSpace.pUnitStalkIso {C : Type*} [Category* C] (A : C) :
--     (pUnit.{u} A).presheaf.stalk ⟨⟩ ≅ A :=
--   sorry

def AlgebraicGeometry.LocallyRingedSpace.pUnit (R : Type u) [CommRing R] [IsLocalRing R] :
    LocallyRingedSpace.{u} where
  __ := SheafedSpace.pUnit (.of R)
  isLocalRing := sorry

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
