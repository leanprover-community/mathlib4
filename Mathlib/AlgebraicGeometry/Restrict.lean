/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Over

/-!
# Restriction of Schemes and Morphisms

## Main definition
- `AlgebraicGeometry.Scheme.restrict`: The restriction of a scheme along an open embedding.
  The map `X.restrict f ⟶ X` is `AlgebraicGeometry.Scheme.ofRestrict`.
  `U : X.Opens` has a coercion to `Scheme` and `U.ι` is a shorthand
  for `X.restrict U.open_embedding : U ⟶ X`.
- `AlgebraicGeometry.morphism_restrict`: The restriction of `X ⟶ Y` to `X ∣_ᵤ f ⁻¹ᵁ U ⟶ Y ∣_ᵤ U`.

-/

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737


noncomputable section

open TopologicalSpace CategoryTheory Opposite

open CategoryTheory.Limits

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
lemma ι_base_apply (x : U) : U.ι.base x = x.val := rfl

instance : IsOpenImmersion U.ι := inferInstanceAs (IsOpenImmersion (X.ofRestrict _))

@[simps! over] instance : U.toScheme.CanonicallyOver X where
  hom := U.ι

instance (U : X.Opens) : U.ι.IsOver X where

lemma toScheme_carrier : (U : Type u) = (U : Set X) := rfl

lemma toScheme_presheaf_obj (V) : Γ(U, V) = Γ(X, U.ι ''ᵁ V) := rfl

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
lemma range_ι : Set.range U.ι.base = U :=
  Subtype.range_val

lemma ι_image_top : U.ι ''ᵁ ⊤ = U :=
  U.isOpenEmbedding_obj_top

lemma ι_image_le (W : U.toScheme.Opens) : U.ι ''ᵁ W ≤ U := by
  simp_rw [← U.ι_image_top]
  exact U.ι.image_le_image_of_le le_top

@[simp]
lemma ι_preimage_self : U.ι ⁻¹ᵁ U = ⊤ :=
  Opens.inclusion'_map_eq_top _

instance ι_appLE_isIso :
    IsIso (U.ι.appLE U ⊤ U.ι_preimage_self.ge) := by
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

lemma stalkIso_inv {X : Scheme.{u}} (U : X.Opens) (x : U) :
    (U.stalkIso x).inv = U.ι.stalkMap x := by
  rw [← Category.comp_id (U.stalkIso x).inv, Iso.inv_comp_eq]
  apply TopCat.Presheaf.stalk_hom_ext
  intro W hxW
  simp only [Category.comp_id, U.germ_stalkIso_hom_assoc]
  convert (Scheme.stalkMap_germ U.ι (U.ι ''ᵁ W) x ⟨_, hxW, rfl⟩).symm
  refine (U.toScheme.presheaf.germ_res (homOfLE ?_) _ _).symm
  exact (Set.preimage_image_eq _ Subtype.val_injective).le

end Scheme.Opens

/-- If `U` is a family of open sets that covers `X`, then `X.restrict U` forms an `X.open_cover`. -/
@[simps! I₀ X f]
def Scheme.openCoverOfISupEqTop {s : Type*} (X : Scheme.{u}) (U : s → X.Opens)
    (hU : ⨆ i, U i = ⊤) : X.OpenCover where
  I₀ := s
  X i := U i
  f i := (U i).ι
  idx x :=
    haveI : x ∈ ⨆ i, U i := hU.symm ▸ show x ∈ (⊤ : X.Opens) by trivial
    (Opens.mem_iSup.mp this).choose
  covers x := by
    erw [Subtype.range_coe]
    have : x ∈ ⨆ i, U i := hU.symm ▸ show x ∈ (⊤ : X.Opens) by trivial
    exact (Opens.mem_iSup.mp this).choose_spec

/-- The open sets of an open subscheme corresponds to the open sets containing in the subset. -/
@[simps!]
def opensRestrict :
    Scheme.Opens U ≃ { V : X.Opens // V ≤ U } :=
  (IsOpenImmersion.opensEquiv (U.ι)).trans (Equiv.subtypeEquivProp (by simp))

instance ΓRestrictAlgebra {X : Scheme.{u}} (U : X.Opens) :
    Algebra (Γ(X, ⊤)) Γ(U, ⊤) :=
  U.ι.appTop.hom.toAlgebra

lemma Scheme.map_basicOpen (r : Γ(U, ⊤)) :
    U.ι ''ᵁ U.toScheme.basicOpen r = X.basicOpen
      (X.presheaf.map (eqToHom U.isOpenEmbedding_obj_top.symm).op r) := by
  refine (Scheme.image_basicOpen (X.ofRestrict U.isOpenEmbedding) r).trans ?_
  rw [← Scheme.basicOpen_res_eq _ _ (eqToHom U.isOpenEmbedding_obj_top).op]
  rw [← CommRingCat.comp_apply, ← CategoryTheory.Functor.map_comp, ← op_comp, eqToHom_trans,
    eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  congr
  exact PresheafedSpace.IsOpenImmersion.ofRestrict_invApp _ _ _

lemma Scheme.Opens.ι_image_basicOpen (r : Γ(U, ⊤)) :
    U.ι ''ᵁ U.toScheme.basicOpen r = X.basicOpen r := by
  rw [Scheme.map_basicOpen, Scheme.basicOpen_res_eq]

lemma Scheme.map_basicOpen_map (r : Γ(X, U)) :
    U.ι ''ᵁ (U.toScheme.basicOpen <| U.topIso.inv r) = X.basicOpen r := by
  simp only [Scheme.Opens.toScheme_presheaf_obj]
  rw [Scheme.map_basicOpen, Scheme.basicOpen_res_eq, Scheme.Opens.topIso_inv,
    Scheme.basicOpen_res_eq X]

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
  exact congr($(X.homOfLE_ι e).base a)

@[simp]
theorem Scheme.homOfLE_apply {U V : X.Opens} (e : U ≤ V) (x : U) :
    ((X.homOfLE e).base x).1 = x := by
  rw [homOfLE_base]
  rfl

theorem Scheme.ι_image_homOfLE_le_ι_image {U V : X.Opens} (e : U ≤ V) (W : Opens V) :
    U.ι ''ᵁ (X.homOfLE e ⁻¹ᵁ W) ≤ V.ι ''ᵁ W := by
  simp only [← SetLike.coe_subset_coe, IsOpenMap.coe_functor_obj, Set.image_subset_iff,
    Scheme.homOfLE_base, Opens.map_coe]
  rintro _ h
  exact ⟨_, h, rfl⟩

@[simp]
theorem Scheme.homOfLE_app {U V : X.Opens} (e : U ≤ V) (W : Opens V) :
    (X.homOfLE e).app W =
      X.presheaf.map (homOfLE <| X.ι_image_homOfLE_le_ι_image e W).op := by
  have e₁ := Scheme.congr_app (X.homOfLE_ι e) (V.ι ''ᵁ W)
  have : V.ι ⁻¹ᵁ V.ι ''ᵁ W = W := W.map_functor_eq (U := V)
  have e₂ := (X.homOfLE e).naturality (eqToIso this).hom.op
  have e₃ := e₂.symm.trans e₁
  dsimp at e₃ ⊢
  rw [← IsIso.eq_comp_inv, ← Functor.map_inv, ← Functor.map_comp] at e₃
  rw [e₃, ← Functor.map_comp]
  congr 1

theorem Scheme.homOfLE_appTop {U V : X.Opens} (e : U ≤ V) :
    (X.homOfLE e).appTop =
      X.presheaf.map (homOfLE <| X.ι_image_homOfLE_le_ι_image e ⊤).op :=
  homOfLE_app ..

instance (X : Scheme.{u}) {U V : X.Opens} (e : U ≤ V) : IsOpenImmersion (X.homOfLE e) := by
  delta Scheme.homOfLE
  infer_instance

/-- The open cover of `⋃ Vᵢ` by `Vᵢ`. -/
def Scheme.Opens.iSupOpenCover {J : Type*} {X : Scheme} (U : J → X.Opens) :
    (⨆ i, U i).toScheme.OpenCover where
  I₀ := J
  X i := U i
  f j := X.homOfLE (le_iSup _ _)
  idx x := (TopologicalSpace.Opens.mem_iSup.mp x.2).choose
  covers x := ⟨⟨x.1, (TopologicalSpace.Opens.mem_iSup.mp x.2).choose_spec⟩, Subtype.ext (by simp)⟩

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
    simp only [comp_coeBase, TopCat.coe_comp, Set.range_comp, Opens.range_ι, Opens.map_coe,
      Set.image_preimage_eq_inter_range, Set.inter_comm (U : Set X)]

/-- If `f : X ⟶ Y` is an open immersion, then for any `U : X.Opens`,
we have the isomorphism `U ≅ f ''ᵁ U`. -/
noncomputable
def Scheme.Hom.isoImage
    {X Y : Scheme.{u}} (f : X.Hom Y) [IsOpenImmersion f] (U : X.Opens) :
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

/-- If `f : X ⟶ Y` is an open immersion, then `X` is isomorphic to its image in `Y`. -/
def Scheme.Hom.isoOpensRange {X Y : Scheme.{u}} (f : X.Hom Y) [IsOpenImmersion f] :
    X ≅ f.opensRange :=
  IsOpenImmersion.isoOfRangeEq f f.opensRange.ι (by simp)

@[reassoc (attr := simp)]
lemma Scheme.Hom.isoOpensRange_hom_ι {X Y : Scheme.{u}} (f : X.Hom Y) [IsOpenImmersion f] :
    f.isoOpensRange.hom ≫ f.opensRange.ι = f := by
  simp [isoOpensRange]

@[reassoc (attr := simp)]
lemma Scheme.Hom.isoOpensRange_inv_comp {X Y : Scheme.{u}} (f : X.Hom Y) [IsOpenImmersion f] :
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
noncomputable def Scheme.Hom.preimageIso {X Y : Scheme.{u}} (f : X.Hom Y) [IsIso (C := Scheme) f]
    (U : Y.Opens) : (f ⁻¹ᵁ U).toScheme ≅ U := by
  apply IsOpenImmersion.isoOfRangeEq (f := (f ⁻¹ᵁ U).ι ≫ f) U.ι _
  dsimp
  rw [Set.range_comp, Opens.range_ι, Opens.range_ι]
  refine @Set.image_preimage_eq _ _ f.base U.1 f.homeomorph.surjective

@[reassoc (attr := simp)]
lemma Scheme.Hom.preimageIso_hom_ι {X Y : Scheme.{u}} (f : X.Hom Y) [IsIso (C := Scheme) f]
    (U : Y.Opens) : (f.preimageIso U).hom ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
lemma Scheme.Hom.preimageIso_inv_ι {X Y : Scheme.{u}} (f : X.Hom Y) [IsIso (C := Scheme) f]
    (U : Y.Opens) : (f.preimageIso U).inv ≫ (f ⁻¹ᵁ U).ι ≫ f = U.ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

/-- If `U ≤ V` are opens of `X`, the restriction of `U` to `V` is isomorphic to `U`. -/
noncomputable def Scheme.Opens.isoOfLE {X : Scheme.{u}} {U V : X.Opens}
    (hUV : U ≤ V) : (V.ι ⁻¹ᵁ U).toScheme ≅ U :=
  IsOpenImmersion.isoOfRangeEq ((V.ι ⁻¹ᵁ U).ι ≫ V.ι) U.ι <| by
    have : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U := by simpa [Scheme.Hom.image_preimage_eq_opensRange_inter]
    rw [Scheme.comp_coeBase, TopCat.coe_comp, Scheme.Opens.range_ι, Set.range_comp, ← this]
    simp

@[reassoc (attr := simp)]
lemma Scheme.Opens.isoOfLE_hom_ι {X : Scheme.{u}} {U V : X.Opens}
    (hUV : U ≤ V) :
    (Scheme.Opens.isoOfLE hUV).hom ≫ U.ι = (V.ι ⁻¹ᵁ U).ι ≫ V.ι := by
  simp [isoOfLE]

@[reassoc (attr := simp)]
lemma Scheme.Opens.isoOfLE_inv_ι {X : Scheme.{u}} {U V : X.Opens}
    (hUV : U ≤ V) :
    (Scheme.Opens.isoOfLE hUV).inv ≫ (V.ι ⁻¹ᵁ U).ι ≫ V.ι = U.ι := by
  simp [isoOfLE]

/-- For `f : R`, `D(f)` as an open subscheme of `Spec R` is isomorphic to `Spec R[1/f]`. -/
def basicOpenIsoSpecAway {R : CommRingCat.{u}} (f : R) :
    Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f) ≅ Spec(Localization.Away f) :=
  IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι _) (Spec.map (CommRingCat.ofHom (algebraMap _ _)))
    (by
      simp only [Scheme.Opens.range_ι]
      exact (PrimeSpectrum.localization_away_comap_range _ _).symm)

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
  exact (IsLocalization.Away.awayToAwayRight_eq f g x).symm

section MorphismRestrict

/-- Given a morphism `f : X ⟶ Y` and an open set `U ⊆ Y`, we have `X ×[Y] U ≅ X |_{f ⁻¹ U}` -/
def pullbackRestrictIsoRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    pullback f (U.ι) ≅ f ⁻¹ᵁ U := by
  refine IsOpenImmersion.isoOfRangeEq (pullback.fst f _) (Scheme.Opens.ι _) ?_
  simp [IsOpenImmersion.range_pullback_fst_of_right]

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
    (f ∣_ U) ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f := by
  delta morphismRestrict
  rw [Category.assoc, pullback.condition.symm, pullbackRestrictIsoRestrict_inv_fst_assoc]

theorem isPullback_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    IsPullback (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι f := by
  delta morphismRestrict
  rw [← Category.id_comp f]
  refine
    (IsPullback.of_horiz_isIso ⟨?_⟩).paste_horiz
      (IsPullback.of_hasPullback f (Y.ofRestrict U.isOpenEmbedding)).flip
  erw [pullbackRestrictIsoRestrict_inv_fst]
  rw [Category.comp_id]

lemma isPullback_opens_inf_le {X : Scheme} {U V W : X.Opens} (hU : U ≤ W) (hV : V ≤ W) :
    IsPullback (X.homOfLE inf_le_left) (X.homOfLE inf_le_right) (X.homOfLE hU) (X.homOfLE hV) := by
  refine (isPullback_morphismRestrict (X.homOfLE hV) (W.ι ⁻¹ᵁ U)).of_iso (V.ι.isoImage _ ≪≫
    X.isoOfEq ?_) (W.ι.isoImage _ ≪≫ X.isoOfEq ?_) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← TopologicalSpace.Opens.map_comp_obj, ← Scheme.comp_base, Scheme.homOfLE_ι]
    exact V.functor_map_eq_inf U
  · exact (W.functor_map_eq_inf U).trans (by simpa)
  all_goals { simp [← cancel_mono (Scheme.Opens.ι _)] }

lemma isPullback_opens_inf {X : Scheme} (U V : X.Opens) :
    IsPullback (X.homOfLE inf_le_left) (X.homOfLE inf_le_right) U.ι V.ι :=
  (isPullback_morphismRestrict V.ι U).of_iso (V.ι.isoImage _ ≪≫ X.isoOfEq
    (V.functor_map_eq_inf U)) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [← cancel_mono U.ι])
    (by simp [← cancel_mono V.ι]) (by simp) (by simp)

@[simp]
lemma morphismRestrict_id {X : Scheme.{u}} (U : X.Opens) : 𝟙 X ∣_ U = 𝟙 _ := by
  rw [← cancel_mono U.ι, morphismRestrict_ι, Category.comp_id, Category.id_comp]
  rfl

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

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (U : Y.Opens) : IsIso (f ∣_ U) := by
  delta morphismRestrict; infer_instance

theorem morphismRestrict_base_coe {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (x) :
    @Coe.coe U Y (⟨fun x => x.1⟩) ((f ∣_ U).base x) = f.base x.1 :=
  congr_arg (fun f => (Scheme.Hom.toLRSHom f).base x)
    (morphismRestrict_ι f U)

theorem morphismRestrict_base {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    ⇑(f ∣_ U).base = U.1.restrictPreimage f.base :=
  funext fun x => Subtype.ext (morphismRestrict_base_coe f U x)

theorem image_morphismRestrict_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) :
    (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V) = f ⁻¹ᵁ (U.ι ''ᵁ V) := by
  ext1
  ext x
  constructor
  · rintro ⟨⟨x, hx⟩, hx' : (f ∣_ U).base _ ∈ V, rfl⟩
    refine ⟨⟨_, hx⟩, ?_, rfl⟩
    convert hx'
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext1` is not compiling
    refine Subtype.ext ?_
    exact (morphismRestrict_base_coe f U ⟨x, hx⟩).symm
  · rintro ⟨⟨x, hx⟩, hx' : _ ∈ V.1, rfl : x = _⟩
    refine ⟨⟨_, hx⟩, (?_ : (f ∣_ U).base ⟨x, hx⟩ ∈ V.1), rfl⟩
    convert hx'
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext1` is not compiling
    refine Subtype.ext ?_
    exact morphismRestrict_base_coe f U ⟨x, hx⟩

lemma eqToHom_eq_homOfLE {C} [Preorder C] {X Y : C} (e : X = Y) : eqToHom e = homOfLE e.le := rfl

open Scheme in
theorem morphismRestrict_app {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.toScheme.Opens) :
    (f ∣_ U).app V = f.app (U.ι ''ᵁ V) ≫
        X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op := by
  have := Scheme.congr_app (morphismRestrict_ι f U) (U.ι ''ᵁ V)
  simp only [Scheme.preimage_comp, Opens.toScheme_presheaf_obj, Hom.app_eq_appLE, comp_appLE,
    Opens.ι_appLE, eqToHom_op, Opens.toScheme_presheaf_map, eqToHom_unop] at this
  have e : U.ι ⁻¹ᵁ (U.ι ''ᵁ V) = V :=
    Opens.ext (Set.preimage_image_eq _ Subtype.coe_injective)
  have e' : (f ∣_ U) ⁻¹ᵁ V = (f ∣_ U) ⁻¹ᵁ U.ι ⁻¹ᵁ U.ι ''ᵁ V := by rw [e]
  simp only [Opens.toScheme_presheaf_obj, Hom.app_eq_appLE, eqToHom_op, Hom.appLE_map]
  rw [← (f ∣_ U).appLE_map' _ e', ← (f ∣_ U).map_appLE' _ e]
  simp only [Opens.toScheme_presheaf_obj, eqToHom_eq_homOfLE, Opens.toScheme_presheaf_map,
    Quiver.Hom.unop_op, Hom.opensFunctor_map_homOfLE]
  rw [this, Hom.appLE_map, Hom.appLE_map, Hom.appLE_map]

theorem morphismRestrict_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    (f ∣_ U).appTop = f.app (U.ι ''ᵁ ⊤) ≫
        X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op :=
  morphismRestrict_app ..

@[simp]
theorem morphismRestrict_app' {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) :
    (f ∣_ U).app V = f.appLE _ _ (image_morphismRestrict_preimage f U V).le :=
  morphismRestrict_app f U V

@[simp]
theorem morphismRestrict_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V W e) :
    (f ∣_ U).appLE V W e = f.appLE (U.ι ''ᵁ V) ((f ⁻¹ᵁ U).ι ''ᵁ W)
      ((Set.image_mono e).trans (image_morphismRestrict_preimage f U V).le) := by
  rw [Scheme.Hom.appLE, morphismRestrict_app', Scheme.Opens.toScheme_presheaf_map,
    Scheme.Hom.appLE_map]

theorem Γ_map_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    Scheme.Γ.map (f ∣_ U).op =
      Y.presheaf.map (eqToHom U.isOpenEmbedding_obj_top.symm).op ≫
        f.app U ≫ X.presheaf.map (eqToHom (f ⁻¹ᵁ U).isOpenEmbedding_obj_top).op := by
  rw [Scheme.Γ_map_op, morphismRestrict_appTop f U, f.naturality_assoc, ← X.presheaf.map_comp]
  rfl

/-- Restricting a morphism onto the image of an open immersion is isomorphic to the base change
along the immersion. -/
def morphismRestrictOpensRange
    {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y) [hg : IsOpenImmersion g] :
    Arrow.mk (f ∣_ g.opensRange) ≅ Arrow.mk (pullback.snd f g) := by
  let V : Y.Opens := g.opensRange
  let e :=
    IsOpenImmersion.isoOfRangeEq g V.ι Subtype.range_coe.symm
  let t : pullback f g ⟶ pullback f V.ι :=
    pullback.map _ _ _ _ (𝟙 _) e.hom (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
      (by rw [Category.comp_id, IsOpenImmersion.isoOfRangeEq_hom_fac])
  symm
  refine Arrow.isoMk (asIso t ≪≫ pullbackRestrictIsoRestrict f V) e ?_
  rw [Iso.trans_hom, asIso_hom, ← Iso.comp_inv_eq, ← cancel_mono g, Arrow.mk_hom, Arrow.mk_hom,
    Category.assoc, Category.assoc, Category.assoc, IsOpenImmersion.isoOfRangeEq_inv_fac,
    ← pullback.condition, morphismRestrict_ι,
    pullbackRestrictIsoRestrict_hom_ι_assoc, pullback.lift_fst_assoc, Category.comp_id]

/-- The restrictions onto two equal open sets are isomorphic. This currently has bad defeqs when
unfolded, but it should not matter for now. Replace this definition if better defeqs are needed. -/
def morphismRestrictEq {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : Y.Opens} (e : U = V) :
    Arrow.mk (f ∣_ U) ≅ Arrow.mk (f ∣_ V) :=
  eqToIso (by subst e; rfl)

/-- Restricting a morphism twice is isomorphic to one restriction. -/
def morphismRestrictRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.toScheme.Opens) :
    Arrow.mk (f ∣_ U ∣_ V) ≅ Arrow.mk (f ∣_ U.ι ''ᵁ V) := by
  refine Arrow.isoMk' _ _ ((Scheme.Opens.ι _).isoImage _ ≪≫ Scheme.isoOfEq _ ?_)
    ((Scheme.Opens.ι _).isoImage _) ?_
  · exact image_morphismRestrict_preimage f U V
  · rw [← cancel_mono (Scheme.Opens.ι _), Iso.trans_hom, Category.assoc, Category.assoc,
      Category.assoc, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc,
      Scheme.Hom.isoImage_hom_ι_assoc,
      Scheme.Hom.isoImage_hom_ι,
      morphismRestrict_ι_assoc, morphismRestrict_ι]

/-- Restricting a morphism twice onto a basic open set is isomorphic to one restriction. -/
def morphismRestrictRestrictBasicOpen {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (r : Γ(Y, U)) :
    Arrow.mk (f ∣_ U ∣_
          U.toScheme.basicOpen (Y.presheaf.map (eqToHom U.isOpenEmbedding_obj_top).op r)) ≅
      Arrow.mk (f ∣_ Y.basicOpen r) := by
  refine morphismRestrictRestrict _ _ _ ≪≫ morphismRestrictEq _ ?_
  have e := Scheme.preimage_basicOpen U.ι r
  rw [Scheme.Opens.ι_app] at e
  rw [← U.toScheme.basicOpen_res_eq _ (eqToHom U.inclusion'_map_eq_top).op]
  erw [← elementwise_of% Y.presheaf.map_comp]
  rw [eqToHom_op, eqToHom_op, eqToHom_map, eqToHom_trans]
  erw [← e]
  ext1
  dsimp [Opens.map_coe]
  rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left, Scheme.Opens.range_ι]
  exact Y.basicOpen_le r

/-- The stalk map of a restriction of a morphism is isomorphic to the stalk map of the original map.
-/
def morphismRestrictStalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (x) :
    Arrow.mk ((f ∣_ U).stalkMap x) ≅ Arrow.mk (f.stalkMap x.1) := Arrow.isoMk' _ _
  (U.stalkIso ((f ∣_ U).base x) ≪≫
    (TopCat.Presheaf.stalkCongr _ <| Inseparable.of_eq <| morphismRestrict_base_coe f U x))
  ((f ⁻¹ᵁ U).stalkIso x) <| by
    apply TopCat.Presheaf.stalk_hom_ext
    intro V hxV
    change ↑(f ⁻¹ᵁ U) at x
    simp [Scheme.stalkMap_germ_assoc, Scheme.Hom.appLE]

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

@[reassoc (attr := simp)]
lemma map_resLE (i : V' ≤ V) :
    X.homOfLE i ≫ f.resLE U V e = f.resLE U V' (i.trans e) := by
  simp_rw [← resLE_id, resLE_comp_resLE, Category.id_comp]

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
  rw [← preimage_comp, ← resLE_comp_ι f e, preimage_comp, preimage_image_eq]

lemma le_preimage_resLE_iff {U : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (O : U.toScheme.Opens) (W : V.toScheme.Opens) :
    W ≤ (f.resLE U V e) ⁻¹ᵁ O ↔ V.ι ''ᵁ W ≤ f ⁻¹ᵁ U.ι ''ᵁ O := by
  simp [resLE_preimage, ← image_le_image_iff V.ι, image_preimage_eq_opensRange_inter, V.ι_image_le]

lemma resLE_appLE {U : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (O : U.toScheme.Opens) (W : V.toScheme.Opens) (e' : W ≤ resLE f U V e ⁻¹ᵁ O) :
    (f.resLE U V e).appLE O W e' =
      f.appLE (U.ι ''ᵁ O) (V.ι ''ᵁ W) ((le_preimage_resLE_iff f e O W).mp e') := by
  simp only [appLE, resLE, comp_coeBase, Opens.map_comp_obj, comp_app, morphismRestrict_app',
    homOfLE_leOfHom, homOfLE_app, Category.assoc, Opens.toScheme_presheaf_map, Quiver.Hom.unop_op,
    opensFunctor_map_homOfLE]
  rw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
  rfl

@[simp]
lemma coe_resLE_base (x : V) : ((f.resLE U V e).base x).val = f.base x := by
  simp [resLE, morphismRestrict_base]

/-- The stalk map of `f.resLE U V` at `x : V` is is the stalk map of `f` at `x`. -/
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

/-- `f.resLE U V` induces `f.appLE U V` on global sections. -/
noncomputable def arrowResLEAppIso (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    Arrow.mk ((f.resLE U V e).appTop) ≅ Arrow.mk (f.appLE U V e) :=
  Arrow.isoMk U.topIso V.topIso <| by
  simp only [Arrow.mk_left, Arrow.mk_right, Functor.id_obj, Scheme.Opens.topIso_hom,
    eqToHom_op, Arrow.mk_hom, Scheme.Hom.map_appLE]
  rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app, Scheme.Hom.resLE_appLE, Scheme.Hom.appLE_map]

end MorphismRestrict

/-- The restriction of an open cover to an open subset. -/
@[simps! I₀ X f]
noncomputable
def Scheme.OpenCover.restrict {X : Scheme.{u}} (𝒰 : X.OpenCover) (U : Opens X) :
    U.toScheme.OpenCover := by
  refine Cover.copy (𝒰.pullbackCover U.ι) 𝒰.I₀ _ (𝒰.f · ∣_ U) (Equiv.refl _)
    (fun i ↦ IsOpenImmersion.isoOfRangeEq (Opens.ι _) (pullback.snd _ _) ?_) ?_
  · dsimp only [Cover.pullbackCover_X, Cover.pullbackCover_I₀, Equiv.refl_apply]
    rw [IsOpenImmersion.range_pullback_snd_of_left U.ι (𝒰.f i), Opens.opensRange_ι]
    exact Subtype.range_val
  · intro i
    rw [← cancel_mono U.ι]
    simp only [morphismRestrict_ι, Cover.pullbackCover_I₀, Equiv.refl_apply, Cover.pullbackCover_X,
      Cover.pullbackCover_f, Category.assoc, pullback.condition]
    rw [IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]

end AlgebraicGeometry
