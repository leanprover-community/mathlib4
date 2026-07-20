/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Over

/-!
# Restriction of Schemes and Morphisms

## Main definition
- `AlgebraicGeometry.Scheme.restrict`: The restriction of a scheme along an open embedding.
  The map `X.restrict f ⟶ X` is `AlgebraicGeometry.Scheme.ofRestrict`.
  `U : X.Opens` has a coercion to `Scheme` and `U.ι` is a shorthand
  for `X.restrict U.open_embedding : U ⟶ X`.
- `AlgebraicGeometry.morphismRestrict`: The restriction of `X ⟶ Y` to `X ∣_ᵤ f ⁻¹ᵁ U ⟶ Y ∣_ᵤ U`.

-/

@[expose] public section

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737


noncomputable section

open TopologicalSpace CategoryTheory Opposite CategoryTheory.Limits

namespace AlgebraicGeometry

universe v v₁ v₂ u u₁

variable {C : Type u₁} [Category.{v} C]

section

variable {X : Scheme.{u}} (U : X.Opens)

namespace Scheme.Opens

/-- Open subset of a scheme as a scheme. -/
@[coe]
def toScheme {X : Scheme.{u}} (U : X.Opens) : Scheme.{u} :=
  X.restrict U.isOpenEmbedding

instance : CoeOut X.Opens Scheme := ⟨toScheme⟩

/-- The restriction of a scheme to an open subset. -/
def ι : ↑U ⟶ X := X.ofRestrict _

@[simp]
lemma ι_apply (x : U) : U.ι x = x.val := rfl

instance : IsOpenImmersion U.ι := inferInstanceAs (IsOpenImmersion (X.ofRestrict _))

@[simps! over] instance : U.toScheme.CanonicallyOver X where
  hom := U.ι

lemma ι_comp_over (S : Scheme.{u}) [X.Over S] : U.ι ≫ X ↘ S = U.toScheme ↘ S := rfl

instance (U : X.Opens) : U.ι.IsOver X where

lemma toScheme_carrier : (U : Type u) = (U : Set X) := rfl

lemma toScheme_presheaf_obj (V) : Γ(U, V) = Γ(X, U.ι ''ᵁ V) := rfl

lemma forall_toScheme {U : X.Opens} {P : U.toScheme → Prop} :
    (∀ x, P x) ↔ ∀ (x : X) (hx : x ∈ U), P ⟨x, hx⟩ := Subtype.forall

lemma exists_toScheme {U : X.Opens} {P : U.toScheme → Prop} :
    (∃ x, P x) ↔ ∃ (x : X) (hx : x ∈ U), P ⟨x, hx⟩ := Subtype.exists

@[simp]
lemma toScheme_presheaf_map {V W} (i : V ⟶ W) :
    U.toScheme.presheaf.map i = X.presheaf.map (U.ι.opensFunctor.map i.unop).op := rfl

@[simp]
lemma ι_app (V) : U.ι.app V = X.presheaf.map
    (homOfLE (x := U.ι ''ᵁ U.ι ⁻¹ᵁ V) (Set.image_preimage_subset _ _)).op :=
  rfl

@[simp]
lemma ι_appTop :
    U.ι.appTop = X.presheaf.map (homOfLE (x := U.ι ''ᵁ ⊤) le_top).op :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma ι_appLE (V W e) :
    U.ι.appLE V W e =
      X.presheaf.map (homOfLE (x := U.ι ''ᵁ W) (Set.image_subset_iff.mpr ‹_›)).op := by
  simp only [Hom.appLE, ι_app, toScheme_presheaf_map, Quiver.Hom.unop_op,
    Hom.opensFunctor_map_homOfLE, ← Functor.map_comp]
  rfl

@[simp]
lemma ι_appIso (V) : U.ι.appIso V = Iso.refl _ :=
  X.ofRestrict_appIso _ _

@[simp]
lemma opensRange_ι : U.ι.opensRange = U :=
  Opens.ext Subtype.range_val

@[simp]
lemma range_ι : Set.range U.ι = U :=
  Subtype.range_val

lemma ι_image_top : U.ι ''ᵁ ⊤ = U :=
  U.isOpenEmbedding_obj_top

lemma ι_image_le (W : U.toScheme.Opens) : U.ι ''ᵁ W ≤ U := by
  simp_rw [← U.ι_image_top]
  exact U.ι.image_mono le_top

@[simp]
lemma ι_preimage_self : U.ι ⁻¹ᵁ U = ⊤ :=
  Opens.inclusion'_map_eq_top _

@[simp]
lemma mem_ι_image_iff {x : U} {V : Opens U} : (x : X) ∈ U.ι ''ᵁ V ↔ x ∈ V :=
  U.ι.apply_mem_image_iff

set_option backward.isDefEq.respectTransparency false in
instance : IsIso (U.ι.appLE U ⊤ U.ι_preimage_self.ge) := by
  simp only [ι, ofRestrict_appLE]
  change IsIso (X.presheaf.map (eqToIso U.ι_image_top).hom.op)
  infer_instance

lemma ι_app_self : U.ι.app U = X.presheaf.map (eqToHom (X := U.ι ''ᵁ _) (by simp)).op := rfl

lemma eq_presheaf_map_eqToHom {V W : Opens U} (e : U.ι ''ᵁ V = U.ι ''ᵁ W) :
    X.presheaf.map (eqToHom e).op =
      U.toScheme.presheaf.map (eqToHom <| U.isOpenEmbedding.functor_obj_injective e).op := rfl

@[simp]
lemma nonempty_iff : Nonempty U.toScheme ↔ (U : Set X).Nonempty := by
  simp only [toScheme_carrier, SetLike.coe_sort_coe, nonempty_subtype]
  rfl

attribute [-simp] eqToHom_op in
/-- The global sections of the restriction is isomorphic to the sections on the open set. -/
@[simps!]
def topIso : Γ(U, ⊤) ≅ Γ(X, U) :=
  X.presheaf.mapIso (eqToIso U.ι_image_top.symm).op

/-- The stalks of an open subscheme are isomorphic to the stalks of the original scheme. -/
def stalkIso {X : Scheme.{u}} (U : X.Opens) (x : U) :
    U.toScheme.presheaf.stalk x ≅ X.presheaf.stalk x.1 :=
  X.restrictStalkIso (Opens.isOpenEmbedding _) _

@[reassoc (attr := simp)]
lemma germ_stalkIso_hom {X : Scheme.{u}} (U : X.Opens)
    {V : U.toScheme.Opens} (x : U) (hx : x ∈ V) :
      U.toScheme.presheaf.germ V x hx ≫ (U.stalkIso x).hom =
        X.presheaf.germ (U.ι ''ᵁ V) x.1 ⟨x, hx, rfl⟩ :=
    PresheafedSpace.restrictStalkIso_hom_eq_germ _ U.isOpenEmbedding _ _ _

@[reassoc]
lemma germ_stalkIso_inv {X : Scheme.{u}} (U : X.Opens) (V : U.toScheme.Opens) (x : U)
    (hx : x ∈ V) : X.presheaf.germ (U.ι ''ᵁ V) x ⟨x, hx, rfl⟩ ≫
      (U.stalkIso x).inv = U.toScheme.presheaf.germ V x hx :=
  PresheafedSpace.restrictStalkIso_inv_eq_germ X.toPresheafedSpace U.isOpenEmbedding V x hx

set_option backward.isDefEq.respectTransparency.types false in
lemma stalkIso_inv {X : Scheme.{u}} (U : X.Opens) (x : U) :
    (U.stalkIso x).inv = U.ι.stalkMap x := by
  rw [← Category.comp_id (U.stalkIso x).inv, Iso.inv_comp_eq]
  apply TopCat.Presheaf.stalk_hom_ext
  intro W hxW
  simp only [Category.comp_id, U.germ_stalkIso_hom_assoc]
  convert! (Scheme.Hom.germ_stalkMap U.ι (U.ι ''ᵁ W) x ⟨_, hxW, rfl⟩).symm
  refine (U.toScheme.presheaf.germ_res (homOfLE ?_) _ _).symm
  exact (Set.preimage_image_eq _ Subtype.val_injective).le

end Scheme.Opens

/-- If `U` is a family of open sets that covers `X`, then `X.restrict U` forms an `X.open_cover`. -/
@[simps! I₀ X f]
def Scheme.openCoverOfIsOpenCover {s : Type*} (X : Scheme.{u}) (U : s → X.Opens)
    (hU : IsOpenCover U) : X.OpenCover where
  I₀ := s
  X i := U i
  f i := (U i).ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    have hx : x ∈ ⨆ i, U i := hU.symm ▸ show x ∈ (⊤ : X.Opens) by trivial
    rw [Opens.mem_iSup] at hx
    obtain ⟨i, hi⟩ := hx
    use i
    simpa

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
/-- The open sets of an open subscheme corresponds to the open sets containing in the subset. -/
@[simps!]
def opensRestrict :
    Scheme.Opens U ≃ { V : X.Opens // V ≤ U } :=
  (IsOpenImmersion.opensEquiv (U.ι)).trans (Equiv.subtypeEquivProp (by simp))

instance ΓRestrictAlgebra {X : Scheme.{u}} (U : X.Opens) :
    Algebra Γ(X, ⊤) Γ(U, ⊤) :=
  U.ι.appTop.hom.toAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- A variant where `r` is first mapped into `Γ(X, U)` before taking the basic open. -/
lemma Scheme.Opens.ι_image_basicOpen' (r : Γ(U, ⊤)) :
    U.ι ''ᵁ U.toScheme.basicOpen r = X.basicOpen
      (X.presheaf.map (eqToHom U.ι_image_top.symm).op r) := by
  refine (Scheme.image_basicOpen (X.ofRestrict U.isOpenEmbedding) r).trans ?_
  rw [← Scheme.basicOpen_res_eq _ _ (eqToHom U.isOpenEmbedding_obj_top).op]
  rw [← CommRingCat.comp_apply, ← CategoryTheory.Functor.map_comp, ← op_comp, eqToHom_trans,
    eqToHom_refl, op_id]
  congr
  exact (PresheafedSpace.IsOpenImmersion.ofRestrict_invApp _ _ _).trans
    (CategoryTheory.Functor.map_id _ _).symm

set_option backward.isDefEq.respectTransparency false in
lemma Scheme.Opens.ι_image_basicOpen (r : Γ(U, ⊤)) :
    U.ι ''ᵁ U.toScheme.basicOpen r = X.basicOpen r := by
  rw [Scheme.Opens.ι_image_basicOpen', Scheme.basicOpen_res_eq]

set_option backward.isDefEq.respectTransparency false in
lemma Scheme.Opens.ι_image_basicOpen_topIso_inv (r : Γ(X, U)) :
    U.ι ''ᵁ U.toScheme.basicOpen (U.topIso.inv r) = X.basicOpen r := by
  simp only [Scheme.Opens.toScheme_presheaf_obj]
  rw [ι_image_basicOpen', basicOpen_res_eq, topIso_inv, basicOpen_res_eq X]

@[simp]
lemma Scheme.Opens.mem_basicOpen_toScheme {U : X.Opens} {V : Scheme.Opens U} {r : Γ(U, V)} {x : U} :
    x ∈ U.toScheme.basicOpen r ↔ (x : X) ∈ X.basicOpen r := by
  rw [← U.toScheme.basicOpen_res_eq _ (eqToHom (U.ι.preimage_image_eq V)).op]
  exact congr(x ∈ $(U.ι.preimage_basicOpen r)).to_iff.symm

/-- If `U ≤ V`, then `U` is also a subscheme of `V`. -/
protected noncomputable
def Scheme.homOfLE (X : Scheme.{u}) {U V : X.Opens} (e : U ≤ V) : (U : Scheme.{u}) ⟶ V :=
  IsOpenImmersion.lift V.ι U.ι (by simpa using e)

@[reassoc (attr := simp)]
lemma Scheme.homOfLE_ι (X : Scheme.{u}) {U V : X.Opens} (e : U ≤ V) :
    X.homOfLE e ≫ V.ι = U.ι :=
  IsOpenImmersion.lift_fac _ _ _

instance {U V : X.Opens} (h : U ≤ V) : (X.homOfLE h).IsOver X where

@[simp]
lemma Scheme.homOfLE_rfl (X : Scheme.{u}) (U : X.Opens) : X.homOfLE (refl U) = 𝟙 _ := by
  rw [← cancel_mono U.ι, Scheme.homOfLE_ι, Category.id_comp]

@[reassoc (attr := simp)]
lemma Scheme.homOfLE_homOfLE (X : Scheme.{u}) {U V W : X.Opens} (e₁ : U ≤ V) (e₂ : V ≤ W) :
    X.homOfLE e₁ ≫ X.homOfLE e₂ = X.homOfLE (e₁.trans e₂) := by
  rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι, Scheme.homOfLE_ι]

theorem Scheme.homOfLE_base {U V : X.Opens} (e : U ≤ V) :
    (X.homOfLE e).base = (Opens.toTopCat _).map (homOfLE e) := by
  ext a; refine Subtype.ext ?_ -- Porting note: `ext` did not pick up `Subtype.ext`
  exact congr($(X.homOfLE_ι e) a)

theorem Scheme.homOfLE_apply' {U V : X.Opens} (e : U ≤ V) (x : X) (hx : x ∈ U) :
    X.homOfLE e ⟨x, hx⟩ = ⟨x, e hx⟩ := by
  rw [homOfLE_base]
  rfl

@[simp]
theorem Scheme.homOfLE_apply {U V : X.Opens} (e : U ≤ V) (x : U) :
    (X.homOfLE e x).1 = x := by
  rw [Scheme.homOfLE_apply']

set_option backward.isDefEq.respectTransparency.types false in
theorem Scheme.ι_image_homOfLE_eq_ι_image_inf {U V : X.Opens} (e : U ≤ V) (W : Opens V) :
    U.ι ''ᵁ X.homOfLE e ⁻¹ᵁ W = V.ι ''ᵁ W ⊓ U := by
  ext x
  constructor
  · rintro ⟨⟨y, hyU⟩, hyW, rfl⟩
    exact ⟨⟨⟨y, e hyU⟩, by simpa [homOfLE_apply'] using hyW, rfl⟩, hyU⟩
  · rintro ⟨⟨y, hyW, rfl⟩, hyU⟩
    exact ⟨⟨y.1, hyU⟩, by simpa [homOfLE_apply'] using hyW, rfl⟩

theorem Scheme.ι_image_homOfLE_le_ι_image {U V : X.Opens} (e : U ≤ V) (W : Opens V) :
    U.ι ''ᵁ X.homOfLE e ⁻¹ᵁ W ≤ V.ι ''ᵁ W := by
  simp [Scheme.ι_image_homOfLE_eq_ι_image_inf]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem Scheme.homOfLE_app {U V : X.Opens} (e : U ≤ V) (W : Opens V) :
    (X.homOfLE e).app W = X.presheaf.map (homOfLE <| X.ι_image_homOfLE_le_ι_image e W).op := by
  have e₁ := Scheme.Hom.congr_app (X.homOfLE_ι e) (V.ι ''ᵁ W)
  have : V.ι ⁻¹ᵁ V.ι ''ᵁ W = W := W.map_functor_eq (U := V)
  have e₂ := (X.homOfLE e).naturality (eqToIso this).hom.op
  have e₃ := e₂.symm.trans e₁
  dsimp at e₃ ⊢
  rw [← IsIso.eq_comp_inv, ← Functor.map_inv, ← Functor.map_comp] at e₃
  rw [e₃, ← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem Scheme.homOfLE_appLE {U V : X.Opens} (e : U ≤ V) (W : Opens V) (W' : Opens U) (e') :
    (X.homOfLE e).appLE W W' e' = X.presheaf.map
      (homOfLE ((U.ι.image_mono e').trans (Scheme.ι_image_homOfLE_le_ι_image ..))).op := by
  simp [Scheme.Hom.appLE, Scheme.homOfLE_app, ← Functor.map_comp, ← op_comp]

theorem Scheme.homOfLE_appTop {U V : X.Opens} (e : U ≤ V) :
    (X.homOfLE e).appTop = X.presheaf.map (homOfLE <| X.ι_image_homOfLE_le_ι_image e ⊤).op :=
  homOfLE_app ..

instance (X : Scheme.{u}) {U V : X.Opens} (e : U ≤ V) : IsOpenImmersion (X.homOfLE e) := by
  delta Scheme.homOfLE
  infer_instance

set_option backward.isDefEq.respectTransparency false in
lemma Scheme.Hom.appIso_homOfLE_inv {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V)
    (W : (U : Scheme.{u}).Opens) :
    ((X.homOfLE h).appIso W).inv =
      X.presheaf.map (.op <| homOfLE <| by
        suffices V.ι ''ᵁ _ ≤ U.ι ''ᵁ W by simpa
        simp [← Scheme.Hom.comp_image]) := by
  rw [eq_comm, ← Iso.hom_comp_eq_id]
  dsimp
  simp only [appIso_hom, homOfLE_app, homOfLE_leOfHom, eqToHom_op, Opens.toScheme_presheaf_map,
    eqToHom_unop, ← X.presheaf.map_comp, Category.assoc, ← X.presheaf.map_id]
  rfl

@[simp]
lemma Scheme.opensRange_homOfLE {U V : X.Opens} (e : U ≤ V) :
    (X.homOfLE e).opensRange = V.ι ⁻¹ᵁ U :=
  V.ι.image_injective (by simp [← Hom.opensRange_comp, Hom.image_preimage_eq_opensRange_inf, e])

/-- The open cover of `⋃ Vᵢ` by `Vᵢ`. -/
def Scheme.Opens.iSupOpenCover {J : Type*} {X : Scheme} (U : J → X.Opens) :
    (⨆ i, U i).toScheme.OpenCover where
  I₀ := J
  X i := U i
  f j := X.homOfLE (le_iSup _ _)
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp x.2
    use i, ⟨x.1, hi⟩
    apply Subtype.ext
    simp

set_option backward.defeqAttrib.useBackward true in
variable (X) in
/-- The functor taking open subsets of `X` to open subschemes of `X`. -/
@[simps! obj_left obj_hom map_left]
def Scheme.restrictFunctor : X.Opens ⥤ Over X where
  obj U := Over.mk U.ι
  map {U V} i := Over.homMk (X.homOfLE i.le) (by simp)
  map_id U := by
    ext1
    exact Scheme.homOfLE_rfl _ _
  map_comp {U V W} i j := by
    ext1
    exact (X.homOfLE_homOfLE i.le j.le).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor that restricts to open subschemes and then takes global section is
isomorphic to the structure sheaf. -/
@[simps!]
def Scheme.restrictFunctorΓ : X.restrictFunctor.op ⋙ (Over.forget X).op ⋙ Scheme.Γ ≅ X.presheaf :=
  NatIso.ofComponents
    (fun U => X.presheaf.mapIso ((eqToIso (unop U).isOpenEmbedding_obj_top).symm.op :))
    (by
      intro U V i
      dsimp
      rw [X.homOfLE_appTop, ← Functor.map_comp, ← Functor.map_comp]
      congr 1)

/-- `X ∣_ U ∣_ V` is isomorphic to `X ∣_ V ∣_ U` -/
noncomputable
def Scheme.restrictRestrictComm (X : Scheme.{u}) (U V : X.Opens) :
    (U.ι ⁻¹ᵁ V).toScheme ≅ V.ι ⁻¹ᵁ U :=
  IsOpenImmersion.isoOfRangeEq (Opens.ι _ ≫ U.ι) (Opens.ι _ ≫ V.ι) <| by
    simp only [Hom.comp_base, TopCat.coe_comp, Set.range_comp, Opens.range_ι, Opens.map_coe,
      Set.image_preimage_eq_inter_range, Set.inter_comm (U : Set X)]

/-- If `f : X ⟶ Y` is an open immersion, then for any `U : X.Opens`,
we have the isomorphism `U ≅ f ''ᵁ U`. -/
noncomputable
def Scheme.Hom.isoImage
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Opens) :
    U.toScheme ≅ f ''ᵁ U :=
  IsOpenImmersion.isoOfRangeEq (Opens.ι _ ≫ f) (Opens.ι _) (by simp [Set.range_comp])

@[reassoc (attr := simp)]
lemma Scheme.Hom.isoImage_hom_ι
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Opens) :
    (f.isoImage U).hom ≫ (f ''ᵁ U).ι = U.ι ≫ f :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
lemma Scheme.Hom.isoImage_inv_ι
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Opens) :
    (f.isoImage U).inv ≫ U.ι ≫ f = (f ''ᵁ U).ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

@[reassoc]
lemma Scheme.Hom.isoImage_hom_homOfLE
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U V : Opens X) (e : U ≤ V) :
    (f.isoImage U).hom ≫ Y.homOfLE (f.image_mono e) = X.homOfLE e ≫ (f.isoImage V).hom := by
  simp [← cancel_mono (f ''ᵁ V).ι]

@[reassoc]
lemma Scheme.Hom.isoImage_inv_homOfLE
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U V : Opens X) (e : U ≤ V) :
    (f.isoImage U).inv ≫ X.homOfLE e = Y.homOfLE (f.image_mono e) ≫ (f.isoImage V).inv := by
  simp [← cancel_mono (f.isoImage V).hom, ← f.isoImage_hom_homOfLE]

@[reassoc (attr := simp)]
lemma Scheme.Opens.isoImage_ι_inv_ι {X : Scheme.{u}} (U : Opens X) (V : Opens U) :
    (U.ι.isoImage V).inv ≫ V.ι = X.homOfLE (U.ι_image_le V) := by
  simp [← cancel_mono U.ι]

/-- If `f : X ⟶ Y` is an open immersion, then `X` is isomorphic to its image in `Y`. -/
def Scheme.Hom.isoOpensRange {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    X ≅ f.opensRange :=
  IsOpenImmersion.isoOfRangeEq f f.opensRange.ι (by simp)

@[reassoc (attr := simp)]
lemma Scheme.Hom.isoOpensRange_hom_ι {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    f.isoOpensRange.hom ≫ f.opensRange.ι = f := by
  simp [isoOpensRange]

@[reassoc (attr := simp)]
lemma Scheme.Hom.isoOpensRange_inv_comp {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    f.isoOpensRange.inv ≫ f = f.opensRange.ι := by
  simp [isoOpensRange]

/-- `(⊤ : X.Opens)` as a scheme is isomorphic to `X`. -/
@[simps hom]
def Scheme.topIso (X : Scheme) : ↑(⊤ : X.Opens) ≅ X where
  hom := Scheme.Opens.ι _
  inv := ⟨X.restrictTopIso.inv⟩
  hom_inv_id := Hom.ext' X.restrictTopIso.hom_inv_id
  inv_hom_id := Hom.ext' X.restrictTopIso.inv_hom_id

@[reassoc (attr := simp)]
lemma Scheme.toIso_inv_ι (X : Scheme.{u}) : X.topIso.inv ≫ Opens.ι _ = 𝟙 _ :=
  X.topIso.inv_hom_id

@[reassoc (attr := simp)]
lemma Scheme.ι_toIso_inv (X : Scheme.{u}) : Opens.ι _ ≫ X.topIso.inv = 𝟙 _ :=
  X.topIso.hom_inv_id

/-- If `U = V`, then `X ∣_ U` is isomorphic to `X ∣_ V`. -/
noncomputable
def Scheme.isoOfEq (X : Scheme.{u}) {U V : X.Opens} (e : U = V) :
    (U : Scheme.{u}) ≅ V :=
  IsOpenImmersion.isoOfRangeEq U.ι V.ι (by rw [e])

@[reassoc (attr := simp)]
lemma Scheme.isoOfEq_hom_ι (X : Scheme.{u}) {U V : X.Opens} (e : U = V) :
    (X.isoOfEq e).hom ≫ V.ι = U.ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
lemma Scheme.isoOfEq_inv_ι (X : Scheme.{u}) {U V : X.Opens} (e : U = V) :
    (X.isoOfEq e).inv ≫ U.ι = V.ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

lemma Scheme.isoOfEq_hom (X : Scheme.{u}) {U V : X.Opens} (e : U = V) :
    (X.isoOfEq e).hom = X.homOfLE e.le := rfl

lemma Scheme.isoOfEq_inv (X : Scheme.{u}) {U V : X.Opens} (e : U = V) :
    (X.isoOfEq e).inv = X.homOfLE e.ge := rfl

@[simp]
lemma Scheme.isoOfEq_rfl (X : Scheme.{u}) (U : X.Opens) : X.isoOfEq (refl U) = Iso.refl _ := by
  ext1
  rw [← cancel_mono U.ι, Scheme.isoOfEq_hom_ι, Iso.refl_hom, Category.id_comp]

end

/-- The restriction of an isomorphism onto an open set. -/
noncomputable def Scheme.Hom.preimageIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso (C := Scheme) f]
    (U : Y.Opens) : (f ⁻¹ᵁ U).toScheme ≅ U := by
  apply IsOpenImmersion.isoOfRangeEq (f := (f ⁻¹ᵁ U).ι ≫ f) U.ι _
  dsimp
  rw [Set.range_comp, Opens.range_ι, Opens.range_ι]
  refine @Set.image_preimage_eq _ _ f U.1 f.homeomorph.surjective

@[reassoc (attr := simp)]
lemma Scheme.Hom.preimageIso_hom_ι {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso (C := Scheme) f]
    (U : Y.Opens) : (f.preimageIso U).hom ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
lemma Scheme.Hom.preimageIso_inv_ι {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso (C := Scheme) f]
    (U : Y.Opens) : (f.preimageIso U).inv ≫ (f ⁻¹ᵁ U).ι ≫ f = U.ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

/-- If `U ≤ V` are opens of `X`, the restriction of `U` to `V` is isomorphic to `U`. -/
noncomputable def Scheme.Opens.isoOfLE {X : Scheme.{u}} {U V : X.Opens} (hUV : U ≤ V) :
    (V.ι ⁻¹ᵁ U).toScheme ≅ U :=
  IsOpenImmersion.isoOfRangeEq ((V.ι ⁻¹ᵁ U).ι ≫ V.ι) U.ι <| by
    have : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U := by simpa [Scheme.Hom.image_preimage_eq_opensRange_inf]
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Scheme.Opens.range_ι, Set.range_comp, ← this]
    simp

@[reassoc (attr := simp)]
lemma Scheme.Opens.isoOfLE_hom_ι {X : Scheme.{u}} {U V : X.Opens} (hUV : U ≤ V) :
    (isoOfLE hUV).hom ≫ U.ι = (V.ι ⁻¹ᵁ U).ι ≫ V.ι := by
  simp [isoOfLE]

@[reassoc (attr := simp)]
lemma Scheme.Opens.isoOfLE_inv_ι {X : Scheme.{u}} {U V : X.Opens} (hUV : U ≤ V) :
    (isoOfLE hUV).inv ≫ (V.ι ⁻¹ᵁ U).ι ≫ V.ι = U.ι := by
  simp [isoOfLE]

set_option backward.isDefEq.respectTransparency.types false in
/-- For `f : R`, `D(f)` as an open subscheme of `Spec R` is isomorphic to `Spec R[1/f]`. -/
def basicOpenIsoSpecAway {R : CommRingCat.{u}} (f : R) :
    Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f) ≅
      Spec (.of <| Localization.Away f) :=
  IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι _) (Spec.map (CommRingCat.ofHom (algebraMap _ _)))
    (by
      simp only [Scheme.Opens.range_ι]
      exact (PrimeSpectrum.localization_away_comap_range _ _).symm)

@[reassoc (attr := simp)]
lemma basicOpenIsoSpecAway_hom_SpecMap {R : CommRingCat.{u}} (f : R) :
    (basicOpenIsoSpecAway f).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R _)) =
        Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) := by
  simp [basicOpenIsoSpecAway]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma basicOpenIsoSpecAway_inv_homOfLE {R : CommRingCat.{u}} (f g x : R) (hx : x = f * g) :
    haveI : IsLocalization.Away (f * g) (Localization.Away x) := by rw [hx]; infer_instance
    (basicOpenIsoSpecAway x).inv ≫ (Spec R).homOfLE (by simp [hx, PrimeSpectrum.basicOpen_mul]) =
      Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight f g)) ≫
        (basicOpenIsoSpecAway f).inv := by
  subst hx
  rw [← cancel_mono (Scheme.Opens.ι _)]
  simp only [basicOpenIsoSpecAway, Category.assoc, Scheme.homOfLE_ι,
    IsOpenImmersion.isoOfRangeEq_inv_fac]
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr
  ext x
  exact (IsLocalization.Away.awayToAwayRight_eq f g x (S := Localization.Away f)).symm

section MorphismRestrict

/-- Given a morphism `f : X ⟶ Y` and an open set `U ⊆ Y`, we have `X ×[Y] U ≅ X |_{f ⁻¹ U}` -/
def pullbackRestrictIsoRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    pullback f U.ι ≅ f ⁻¹ᵁ U := by
  refine IsOpenImmersion.isoOfRangeEq (pullback.fst f _) (Scheme.Opens.ι _) ?_
  simp [IsOpenImmersion.range_pullbackFst]

@[simp, reassoc]
theorem pullbackRestrictIsoRestrict_inv_fst {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    (pullbackRestrictIsoRestrict f U).inv ≫ pullback.fst f _ = (f ⁻¹ᵁ U).ι := by
  delta pullbackRestrictIsoRestrict; simp

@[reassoc (attr := simp)]
theorem pullbackRestrictIsoRestrict_hom_ι {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    (pullbackRestrictIsoRestrict f U).hom ≫ (f ⁻¹ᵁ U).ι = pullback.fst f _ := by
  delta pullbackRestrictIsoRestrict; simp

/-- The restriction of a morphism `X ⟶ Y` onto `X |_{f ⁻¹ U} ⟶ Y |_ U`. -/
def morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : (f ⁻¹ᵁ U).toScheme ⟶ U :=
  (pullbackRestrictIsoRestrict f U).inv ≫ pullback.snd _ _

/-- the notation for restricting a morphism of scheme to an open subset of the target scheme -/
infixl:85 " ∣_ " => morphismRestrict

@[reassoc (attr := simp)]
theorem pullbackRestrictIsoRestrict_hom_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) : (pullbackRestrictIsoRestrict f U).hom ≫ f ∣_ U = pullback.snd _ _ :=
  Iso.hom_inv_id_assoc _ _

@[reassoc (attr := simp)]
theorem morphismRestrict_ι {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f := by
  delta morphismRestrict
  rw [Category.assoc, pullback.condition.symm, pullbackRestrictIsoRestrict_inv_fst_assoc]

theorem isPullback_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    IsPullback (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι f := by
  apply IsOpenImmersion.isPullback <;>
  simp

set_option backward.isDefEq.respectTransparency.types false in
lemma isPullback_opens_inf_le {X : Scheme} {U V W : X.Opens} (hU : U ≤ W) (hV : V ≤ W) :
    IsPullback (X.homOfLE inf_le_left) (X.homOfLE inf_le_right) (X.homOfLE hU) (X.homOfLE hV) := by
  refine (isPullback_morphismRestrict (X.homOfLE hV) (W.ι ⁻¹ᵁ U)).of_iso (V.ι.isoImage _ ≪≫
    X.isoOfEq ?_) (W.ι.isoImage _ ≪≫ X.isoOfEq ?_) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← TopologicalSpace.Opens.map_comp_obj, ← Scheme.Hom.comp_base, Scheme.homOfLE_ι]
    exact V.functor_map_eq_inf U
  · exact (W.functor_map_eq_inf U).trans (by simpa)
  all_goals { simp [← cancel_mono (Scheme.Opens.ι _)] }

set_option backward.isDefEq.respectTransparency.types false in
lemma isPullback_opens_inf {X : Scheme} (U V : X.Opens) :
    IsPullback (X.homOfLE inf_le_left) (X.homOfLE inf_le_right) U.ι V.ι :=
  (isPullback_morphismRestrict V.ι U).of_iso (V.ι.isoImage _ ≪≫ X.isoOfEq
    (V.functor_map_eq_inf U)) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [← cancel_mono U.ι])
    (by simp [← cancel_mono V.ι]) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma morphismRestrict_id {X : Scheme.{u}} (U : X.Opens) : 𝟙 X ∣_ U = 𝟙 _ := by
  rw [← cancel_mono U.ι, morphismRestrict_ι, Category.comp_id, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem morphismRestrict_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Opens Z) :
    (f ≫ g) ∣_ U = f ∣_ g ⁻¹ᵁ U ≫ g ∣_ U := by
  delta morphismRestrict
  rw [← pullbackRightPullbackFstIso_inv_snd_snd]
  simp_rw [← Category.assoc]
  congr 1
  rw [← cancel_mono (pullback.fst _ _)]
  simp_rw [Category.assoc]
  rw [pullbackRestrictIsoRestrict_inv_fst, pullbackRightPullbackFstIso_inv_snd_fst, ←
    pullback.condition, pullbackRestrictIsoRestrict_inv_fst_assoc,
    pullbackRestrictIsoRestrict_inv_fst_assoc]
  rfl

@[reassoc]
theorem morphismRestrict_homOfLE {X Y : Scheme.{u}} (f : X ⟶ Y) (U V : Y.Opens) (e : U ≤ V) :
    (f ∣_ U) ≫ Y.homOfLE e = X.homOfLE (f.preimage_mono e) ≫ (f ∣_ V) := by
  simp [← cancel_mono V.ι]

@[reassoc (attr := simp)]
lemma Scheme.Hom.isoImage_preimage_hom_homOfLE {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : Y.Opens) :
    (f.isoImage (f ⁻¹ᵁ U)).hom ≫ Y.homOfLE (f.image_preimage_le U) = f ∣_ U := by
  simp [← cancel_mono U.ι]

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (U : Y.Opens) : IsIso (f ∣_ U) := by
  delta morphismRestrict; infer_instance

@[simp]
theorem morphismRestrict_base_coe {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (x) :
    ((f ∣_ U) x).1 = f x.1 :=
  congr_arg (fun f => (Scheme.Hom.toLRSHom f).base x)
    (morphismRestrict_ι f U)

theorem morphismRestrict_base {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    ⇑(f ∣_ U) = U.1.restrictPreimage f :=
  funext fun x => Subtype.ext (morphismRestrict_base_coe f U x)

theorem image_morphismRestrict_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) :
    (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V) = f ⁻¹ᵁ (U.ι ''ᵁ V) :=
  IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback (isPullback_morphismRestrict f U) V

set_option backward.isDefEq.respectTransparency false in
open Scheme in
theorem morphismRestrict_app {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.toScheme.Opens) :
    (f ∣_ U).app V = f.app (U.ι ''ᵁ V) ≫
        X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op := by
  obtain ⟨V, rfl⟩ : ∃ V', U.ι ⁻¹ᵁ U.ι ''ᵁ V' = V := ⟨_, U.ι.preimage_image_eq V⟩
  simpa [← Functor.map_comp_assoc, ← Functor.map_comp] using!
    congr(Y.presheaf.map (eqToHom (congr_arg (U.ι ''ᵁ ·) (U.ι.preimage_image_eq V).symm)).op ≫
      $(Scheme.Hom.congr_app (morphismRestrict_ι f U) (U.ι ''ᵁ V)))

theorem morphismRestrict_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    (f ∣_ U).appTop = f.app (U.ι ''ᵁ ⊤) ≫
        X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op :=
  morphismRestrict_app ..

@[simp]
theorem morphismRestrict_app' {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) :
    (f ∣_ U).app V = f.appLE _ _ (image_morphismRestrict_preimage f U V).le :=
  morphismRestrict_app f U V

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem morphismRestrict_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V W e) :
    (f ∣_ U).appLE V W e = f.appLE (U.ι ''ᵁ V) ((f ⁻¹ᵁ U).ι ''ᵁ W)
      ((Set.image_mono e).trans (image_morphismRestrict_preimage f U V).le) := by
  rw [Scheme.Hom.appLE, morphismRestrict_app', Scheme.Opens.toScheme_presheaf_map,
    Scheme.Hom.appLE_map]

@[reassoc]
theorem morphismRestrict_homOfLE_isoImage_ι_hom
    {X : Scheme.{u}} {U V : X.Opens} (e : U ≤ V) (W : Opens V) :
    X.homOfLE e ∣_ W ≫ (V.ι.isoImage W).hom =
      (U.ι.isoImage (X.homOfLE e ⁻¹ᵁ W)).hom ≫ X.homOfLE (X.ι_image_homOfLE_le_ι_image e W) := by
  simp [← cancel_mono (V.ι ''ᵁ W).ι]

@[reassoc]
theorem isoImage_ι_inv_morphismRestrict_homOfLE {X : Scheme.{u}} {U V : X.Opens}
    (e : U ≤ V) (W : Opens V) :
    (U.ι.isoImage (X.homOfLE e ⁻¹ᵁ W)).inv ≫ X.homOfLE e ∣_ W =
      X.homOfLE (X.ι_image_homOfLE_le_ι_image e W) ≫ (V.ι.isoImage W).inv := by
  simp [← cancel_mono (V.ι.isoImage W).hom, morphismRestrict_homOfLE_isoImage_ι_hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Restricting a morphism onto the image of an open immersion is isomorphic to the base change
along the immersion. -/
def morphismRestrictOpensRange {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y) [IsOpenImmersion g] :
    Arrow.mk (f ∣_ g.opensRange) ≅ Arrow.mk (pullback.snd f g) := by
  let V : Y.Opens := g.opensRange
  let e :=
    IsOpenImmersion.isoOfRangeEq g V.ι Subtype.range_coe.symm
  let t : pullback f g ⟶ pullback f V.ι :=
    pullback.map _ _ _ _ (𝟙 _) e.hom (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
      (by rw [Category.comp_id, IsOpenImmersion.isoOfRangeEq_hom_fac])
  symm
  refine Arrow.isoMk (asIso t ≪≫ pullbackRestrictIsoRestrict f V) e ?_
  rw [Iso.trans_hom, asIso_hom, ← Iso.comp_inv_eq, ← cancel_mono g]
  dsimp
  rw [Category.assoc, Category.assoc, Category.assoc, IsOpenImmersion.isoOfRangeEq_inv_fac,
    ← pullback.condition, morphismRestrict_ι,
    pullbackRestrictIsoRestrict_hom_ι_assoc, pullback.lift_fst_assoc, Category.comp_id]

/-- The restrictions onto two equal open sets are isomorphic. This currently has bad defeqs when
unfolded, but it should not matter for now. Replace this definition if better defeqs are needed. -/
def morphismRestrictEq {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : Y.Opens} (e : U = V) :
    Arrow.mk (f ∣_ U) ≅ Arrow.mk (f ∣_ V) :=
  eqToIso (by subst e; rfl)

@[reassoc]
lemma morphismRestrict_ι_image_ι_isoImage_inv
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.toScheme.Opens) :
    f ∣_ U.ι ''ᵁ V ≫ (U.ι.isoImage V).inv = (X.homOfLE (image_morphismRestrict_preimage f U V).ge ≫
      ((f ⁻¹ᵁ U).ι.isoImage ((f ∣_ U) ⁻¹ᵁ V)).inv) ≫ f ∣_ U ∣_ V := by
  simp [← cancel_mono (Scheme.Opens.ι _)]

@[reassoc]
lemma morphismRestrict_morphismRestrict_ι_isoImage_hom
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.toScheme.Opens) :
    f ∣_ U ∣_ V ≫ (U.ι.isoImage V).hom = (((f ⁻¹ᵁ U).ι.isoImage ((f ∣_ U) ⁻¹ᵁ V)).hom ≫
      X.homOfLE (image_morphismRestrict_preimage f U V).le) ≫ f ∣_ U.ι ''ᵁ V := by
  simp [← cancel_mono (Scheme.Opens.ι _)]

/-- Restricting a morphism twice is isomorphic to one restriction. -/
def morphismRestrictRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.toScheme.Opens) :
    Arrow.mk (f ∣_ U ∣_ V) ≅ Arrow.mk (f ∣_ U.ι ''ᵁ V) := by
  refine Arrow.isoMk' _ _ ((Scheme.Opens.ι _).isoImage _ ≪≫ Scheme.isoOfEq _ ?_)
    ((Scheme.Opens.ι _).isoImage _) ?_
  · exact image_morphismRestrict_preimage f U V
  · simp [← cancel_mono (Scheme.Opens.ι _)]

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a morphism twice onto a basic open set is isomorphic to one restriction. -/
def morphismRestrictRestrictBasicOpen {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (r : Γ(Y, U)) :
    Arrow.mk (f ∣_ U ∣_
          U.toScheme.basicOpen (Y.presheaf.map (eqToHom U.isOpenEmbedding_obj_top).op r)) ≅
      Arrow.mk (f ∣_ Y.basicOpen r) := by
  refine morphismRestrictRestrict _ _ _ ≪≫ morphismRestrictEq _ ?_
  simp [Scheme.Opens.ι_image_basicOpen]

set_option backward.isDefEq.respectTransparency false in
/-- The stalk map of a restriction of a morphism is isomorphic to the stalk map of the original map.
-/
def morphismRestrictStalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (x) :
    Arrow.mk ((f ∣_ U).stalkMap x) ≅ Arrow.mk (f.stalkMap x.1) := Arrow.isoMk' _ _
  (U.stalkIso ((f ∣_ U) x) ≪≫
    (TopCat.Presheaf.stalkCongr _ <| Inseparable.of_eq <| morphismRestrict_base_coe f U x))
  ((f ⁻¹ᵁ U).stalkIso x) <| TopCat.Presheaf.stalk_hom_ext _ fun V hxV ↦ by
    simp [Scheme.Hom.germ_stalkMap_assoc, Scheme.Hom.appLE]

instance {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) [IsOpenImmersion f] :
    IsOpenImmersion (f ∣_ U) := by
  delta morphismRestrict
  exact PresheafedSpace.IsOpenImmersion.comp _ _

variable {X Y : Scheme.{u}}

namespace Scheme.Hom

/-- The restriction of a morphism `f : X ⟶ Y` to open sets on the source and target. -/
def resLE (f : Hom X Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) : V.toScheme ⟶ U.toScheme :=
  X.homOfLE e ≫ f ∣_ U

variable (f : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens} (e : V ≤ f ⁻¹ᵁ U)

lemma resLE_eq_morphismRestrict : f.resLE U (f ⁻¹ᵁ U) le_rfl = f ∣_ U := by
  simp [resLE]

@[simp]
lemma resLE_id (i : V ≤ V') : resLE (𝟙 X) V' V i = X.homOfLE i := by
  simp only [resLE, morphismRestrict_id]
  rfl

@[reassoc (attr := simp)]
lemma resLE_comp_ι : f.resLE U V e ≫ U.ι = V.ι ≫ f := by
  simp [resLE]

@[reassoc]
lemma resLE_comp_resLE {Z : Scheme.{u}} (g : Y ⟶ Z) {W : Z.Opens} (e') :
    f.resLE U V e ≫ g.resLE W U e' = (f ≫ g).resLE W V
      (e.trans ((Opens.map f.base).map (homOfLE e')).le) := by
  simp [← cancel_mono W.ι]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
lemma map_resLE (i : V' ≤ V) :
    X.homOfLE i ≫ f.resLE U V e = f.resLE U V' (i.trans e) := by
  simp_rw [← resLE_id, resLE_comp_resLE, Category.id_comp]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
lemma resLE_map (i : U ≤ U') :
    f.resLE U V e ≫ Y.homOfLE i =
      f.resLE U' V (e.trans ((Opens.map f.base).map i.hom).le) := by
  simp_rw [← resLE_id, resLE_comp_resLE, Category.comp_id]

lemma resLE_congr (e₁ : U = U') (e₂ : V = V') (P : MorphismProperty Scheme.{u}) :
    P (f.resLE U V e) ↔ P (f.resLE U' V' (e₁ ▸ e₂ ▸ e)) := by
  subst e₁; subst e₂; rfl

lemma resLE_preimage (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (O : U.toScheme.Opens) :
    f.resLE U V e ⁻¹ᵁ O = V.ι ⁻¹ᵁ (f ⁻¹ᵁ U.ι ''ᵁ O) := by
  rw [← comp_preimage, ← resLE_comp_ι f e, comp_preimage, preimage_image_eq]

lemma le_resLE_preimage_iff {U : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (O : U.toScheme.Opens) (W : V.toScheme.Opens) :
    W ≤ (f.resLE U V e) ⁻¹ᵁ O ↔ V.ι ''ᵁ W ≤ f ⁻¹ᵁ U.ι ''ᵁ O := by
  simp [resLE_preimage, ← image_le_image_iff V.ι, image_preimage_eq_opensRange_inf, V.ι_image_le]

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma resLE_app_top : (f.resLE U V e).app ⊤ =
    U.topIso.hom ≫ f.appLE U V e ≫ V.topIso.inv := by simp [Scheme.Hom.resLE]

set_option backward.isDefEq.respectTransparency false in
lemma resLE_appLE {U : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (O : U.toScheme.Opens) (W : V.toScheme.Opens) (e' : W ≤ resLE f U V e ⁻¹ᵁ O) :
    (f.resLE U V e).appLE O W e' =
      f.appLE (U.ι ''ᵁ O) (V.ι ''ᵁ W) ((le_resLE_preimage_iff f e O W).mp e') := by
  dsimp [appLE, resLE]
  simp only [morphismRestrict_app', appLE, homOfLE_leOfHom, homOfLE_app, Category.assoc]
  rw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
lemma coe_resLE_apply (x : V) : (f.resLE U V e x).1 = f x := by
  simp [resLE, morphismRestrict_base]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The stalk map of `f.resLE U V` at `x : V` is the stalk map of `f` at `x`. -/
def resLEStalkMap (x : V) :
    Arrow.mk ((f.resLE U V e).stalkMap x) ≅ Arrow.mk (f.stalkMap x) :=
  Arrow.isoMk (U.stalkIso _ ≪≫
      (Y.presheaf.stalkCongr <| Inseparable.of_eq <| by simp)) (V.stalkIso x) <| by
    dsimp
    rw [Category.assoc, ← Iso.eq_inv_comp, ← Category.assoc, ← Iso.comp_inv_eq,
      Opens.stalkIso_inv, Opens.stalkIso_inv, ← stalkMap_comp,
      stalkMap_congr_hom _ _ (resLE_comp_ι f e), stalkMap_comp]
    simp

end Scheme.Hom

set_option backward.isDefEq.respectTransparency false in
/-- `f.resLE U V` induces `f.appLE U V` on global sections. -/
noncomputable def arrowResLEAppIso (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    Arrow.mk ((f.resLE U V e).appTop) ≅ Arrow.mk (f.appLE U V e) :=
  Arrow.isoMk U.topIso V.topIso <| by
  simp only [Scheme.Opens.topIso_hom, eqToHom_op, Arrow.mk_hom, Scheme.Hom.map_appLE]
  rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app, Scheme.Hom.resLE_appLE, Scheme.Hom.appLE_map]

set_option backward.isDefEq.respectTransparency.types false in
lemma Scheme.Hom.isPullback_resLE
    {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S} {iY : Y ⟶ T}
    (H : IsPullback g iY iX f)
    {US : S.Opens} {UT : T.Opens}
    {UX : X.Opens} (hUST : UT ≤ f ⁻¹ᵁ US) (hUSX : UX ≤ iX ⁻¹ᵁ US)
    {UY : Y.Opens} (hUY : UY = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) :
    IsPullback (g.resLE UX UY (by simp [*])) (iY.resLE UT UY (by simp [*]))
      (iX.resLE US UX hUSX) (f.resLE US UT hUST) := by
  refine .paste_horiz (v₁₂ := iY.resLE _ _
    ((g.preimage_mono hUSX).trans_eq congr(($H.w) ⁻¹ᵁ US) :)) ?_ ?_
  · refine (IsOpenImmersion.isPullback _ _ _ _ (by simp) ?_).flip
    simp only [Scheme.opensRange_homOfLE, ← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι]
    rw [Scheme.Hom.comp_preimage, ← (g ⁻¹ᵁ UX).ι.image_injective.eq_iff]
    simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    simp [hUY]
  · refine .of_bot ?_ ?_ (isPullback_morphismRestrict f US)
    · simpa using (isPullback_morphismRestrict g UX).paste_vert H
    · simp [← cancel_mono US.ι, H.w]

end MorphismRestrict

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The restriction of an open cover to an open subset. -/
@[simps! I₀ X f]
noncomputable
def Scheme.OpenCover.restrict {X : Scheme.{u}} (𝒰 : Scheme.OpenCover.{v} X) (U : Opens X) :
    U.toScheme.OpenCover := by
  refine Cover.copy (𝒰.pullback₁ U.ι) 𝒰.I₀ _ (𝒰.f · ∣_ U) (Equiv.refl _)
    (fun i ↦ IsOpenImmersion.isoOfRangeEq (Opens.ι _) (pullback.snd _ _) ?_) ?_
  · dsimp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
      PreZeroHypercover.pullback₁_I₀, Equiv.refl_apply, PreZeroHypercover.pullback₁_X]
    rw [IsOpenImmersion.range_pullbackSnd U.ι (𝒰.f i), Opens.opensRange_ι]
    exact Subtype.range_val
  · intro i
    rw [← cancel_mono U.ι]
    simp [morphismRestrict_ι, Equiv.refl_apply, Category.assoc, pullback.condition]

end AlgebraicGeometry
