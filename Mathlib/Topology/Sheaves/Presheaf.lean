/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Mario Carneiro, Reid Barton, Andrew Yang

! This file was ported from Lean 3 source module topology.sheaves.presheaf
! leanprover-community/mathlib commit 8a318021995877a44630c898d0b2bc376fceef3b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.KanExtension
import Mathbin.Topology.Category.Top.Opens
import Mathbin.CategoryTheory.Adjunction.Opposites

/-!
# Presheaves on a topological space

We define `presheaf C X` simply as `(opens X)ᵒᵖ ⥤ C`,
and inherit the category structure with natural transformations as morphisms.

We define
* `pushforward_obj {X Y : Top.{w}} (f : X ⟶ Y) (ℱ : X.presheaf C) : Y.presheaf C`
with notation `f _* ℱ`
and for `ℱ : X.presheaf C` provide the natural isomorphisms
* `pushforward.id : (𝟙 X) _* ℱ ≅ ℱ`
* `pushforward.comp : (f ≫ g) _* ℱ ≅ g _* (f _* ℱ)`
along with their `@[simp]` lemmas.

We also define the functors `pushforward` and `pullback` between the categories
`X.presheaf C` and `Y.presheaf C`, and provide their adjunction at
`pushforward_pullback_adjunction`.
-/


universe w v u

open CategoryTheory

open TopologicalSpace

open Opposite

variable (C : Type u) [Category.{v} C]

namespace TopCat

/-- The category of `C`-valued presheaves on a (bundled) topological space `X`. -/
@[nolint has_nonempty_instance]
def Presheaf (X : TopCat.{w}) : Type max u v w :=
  (Opens X)ᵒᵖ ⥤ C deriving Category
#align Top.presheaf TopCat.Presheaf

variable {C}

namespace Presheaf

attribute [local instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

/-- Tag lemmas to use in `Top.presheaf.restrict_tac`.  -/
@[user_attribute]
unsafe def restrict_attr : user_attribute (tactic Unit → tactic Unit) Unit
    where
  Name := `sheaf_restrict
  descr := "tag lemmas to use in `Top.presheaf.restrict_tac`"
  cache_cfg :=
    { mk_cache := fun ns =>
        pure fun t => do
          let ctx ← tactic.local_context
          ctx (tactic.focus1 ∘ (tactic.apply' >=> fun _ => tactic.done) >=> fun _ => t) <|>
              ns
                (tactic.focus1 ∘
                    (tactic.resolve_name >=> tactic.to_expr >=> tactic.apply' >=> fun _ =>
                      tactic.done) >=>
                  fun _ => t)
      dependencies := [] }
#align Top.presheaf.restrict_attr Top.presheaf.restrict_attr

/- ./././Mathport/Syntax/Translate/Expr.lean:330:4: warning: unsupported (TODO): `[tacs] -/
/-- A tactic to discharge goals of type `U ≤ V` for `Top.presheaf.restrict_open` -/
unsafe def restrict_tac : ∀ n : ℕ, tactic Unit
  | 0 => tactic.fail "`restrict_tac` failed"
  | n + 1 => Monad.join (restrict_attr.get_cache <*> pure tactic.done) <|> sorry
#align Top.presheaf.restrict_tac Top.presheaf.restrict_tac

/-- A tactic to discharge goals of type `U ≤ V` for `Top.presheaf.restrict_open`.
Defaults to three iterations. -/
unsafe def restrict_tac' :=
  restrict_tac 3
#align Top.presheaf.restrict_tac' Top.presheaf.restrict_tac'

attribute [sheaf_restrict] bot_le le_top le_refl inf_le_left inf_le_right le_sup_left le_sup_right

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic Top.presheaf.restrict_tac' -/
example {X : TopCat} {v w x y z : Opens X} (h₀ : v ≤ x) (h₁ : x ≤ z ⊓ w) (h₂ : x ≤ y ⊓ z) : v ≤ y :=
  by
  run_tac
    restrict_tac'

/-- The restriction of a section along an inclusion of open sets.
For `x : F.obj (op V)`, we provide the notation `x |_ₕ i` (`h` stands for `hom`) for `i : U ⟶ V`,
and the notation `x |_ₗ U ⟪i⟫` (`l` stands for `le`) for `i : U ≤ V`.
-/
def restrict {X : TopCat} {C : Type _} [Category C] [ConcreteCategory C] {F : X.Presheaf C}
    {V : Opens X} (x : F.obj (op V)) {U : Opens X} (h : U ⟶ V) : F.obj (op U) :=
  F.map h.op x
#align Top.presheaf.restrict TopCat.Presheaf.restrict

-- mathport name: «expr |_ₕ »
scoped[AlgebraicGeometry] infixl:80 " |_ₕ " => TopCat.Presheaf.restrict

-- mathport name: «expr |_ₗ ⟪ ⟫»
scoped[AlgebraicGeometry]
  notation:80 x " |_ₗ " U " ⟪" e "⟫ " =>
    @TopCat.Presheaf.restrict _ _ _ _ _ _ x U (@homOfLE (Opens _) _ U _ e)

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic Top.presheaf.restrict_tac' -/
/-- The restriction of a section along an inclusion of open sets.
For `x : F.obj (op V)`, we provide the notation `x |_ U`, where the proof `U ≤ V` is inferred by
the tactic `Top.presheaf.restrict_tac'` -/
abbrev restrictOpen {X : TopCat} {C : Type _} [Category C] [ConcreteCategory C] {F : X.Presheaf C}
    {V : Opens X} (x : F.obj (op V)) (U : Opens X)
    (e : U ≤ V := by
      run_tac
        Top.presheaf.restrict_tac') :
    F.obj (op U) :=
  x |_ₗ U ⟪e⟫
#align Top.presheaf.restrict_open TopCat.Presheaf.restrictOpen

-- mathport name: «expr |_ »
scoped[AlgebraicGeometry] infixl:80 " |_ " => TopCat.Presheaf.restrictOpen

@[simp]
theorem restrict_restrict {X : TopCat} {C : Type _} [Category C] [ConcreteCategory C]
    {F : X.Presheaf C} {U V W : Opens X} (e₁ : U ≤ V) (e₂ : V ≤ W) (x : F.obj (op W)) :
    x |_ V |_ U = x |_ U := by
  delta restrict_open restrict
  rw [← comp_apply, ← functor.map_comp]
  rfl
#align Top.presheaf.restrict_restrict TopCat.Presheaf.restrict_restrict

@[simp]
theorem map_restrict {X : TopCat} {C : Type _} [Category C] [ConcreteCategory C]
    {F G : X.Presheaf C} (e : F ⟶ G) {U V : Opens X} (h : U ≤ V) (x : F.obj (op V)) :
    e.app _ (x |_ U) = e.app _ x |_ U :=
  by
  delta restrict_open restrict
  rw [← comp_apply, nat_trans.naturality, comp_apply]
#align Top.presheaf.map_restrict TopCat.Presheaf.map_restrict

/-- Pushforward a presheaf on `X` along a continuous map `f : X ⟶ Y`, obtaining a presheaf
on `Y`. -/
def pushforwardObj {X Y : TopCat.{w}} (f : X ⟶ Y) (ℱ : X.Presheaf C) : Y.Presheaf C :=
  (Opens.map f).op ⋙ ℱ
#align Top.presheaf.pushforward_obj TopCat.Presheaf.pushforwardObj

-- mathport name: «expr _* »
infixl:80 " _* " => pushforwardObj

@[simp]
theorem pushforwardObj_obj {X Y : TopCat.{w}} (f : X ⟶ Y) (ℱ : X.Presheaf C) (U : (Opens Y)ᵒᵖ) :
    (f _* ℱ).obj U = ℱ.obj ((Opens.map f).op.obj U) :=
  rfl
#align Top.presheaf.pushforward_obj_obj TopCat.Presheaf.pushforwardObj_obj

@[simp]
theorem pushforwardObj_map {X Y : TopCat.{w}} (f : X ⟶ Y) (ℱ : X.Presheaf C) {U V : (Opens Y)ᵒᵖ}
    (i : U ⟶ V) : (f _* ℱ).map i = ℱ.map ((Opens.map f).op.map i) :=
  rfl
#align Top.presheaf.pushforward_obj_map TopCat.Presheaf.pushforwardObj_map

/--
An equality of continuous maps induces a natural isomorphism between the pushforwards of a presheaf
along those maps.
-/
def pushforwardEq {X Y : TopCat.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Presheaf C) :
    f _* ℱ ≅ g _* ℱ :=
  isoWhiskerRight (NatIso.op (Opens.mapIso f g h).symm) ℱ
#align Top.presheaf.pushforward_eq TopCat.Presheaf.pushforwardEq

theorem pushforward_eq' {X Y : TopCat.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Presheaf C) :
    f _* ℱ = g _* ℱ := by rw [h]
#align Top.presheaf.pushforward_eq' TopCat.Presheaf.pushforward_eq'

@[simp]
theorem pushforwardEq_hom_app {X Y : TopCat.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Presheaf C) (U) :
    (pushforwardEq h ℱ).Hom.app U =
      ℱ.map (by dsimp [functor.op]; apply Quiver.Hom.op; apply eq_to_hom; rw [h]) :=
  by simp [pushforward_eq]
#align Top.presheaf.pushforward_eq_hom_app TopCat.Presheaf.pushforwardEq_hom_app

theorem pushforward_eq'_hom_app {X Y : TopCat.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Presheaf C)
    (U) : NatTrans.app (eqToHom (pushforward_eq' h ℱ)) U = ℱ.map (eqToHom (by rw [h])) := by
  simpa [eq_to_hom_map]
#align Top.presheaf.pushforward_eq'_hom_app TopCat.Presheaf.pushforward_eq'_hom_app

@[simp]
theorem pushforwardEq_rfl {X Y : TopCat.{w}} (f : X ⟶ Y) (ℱ : X.Presheaf C) (U) :
    (pushforwardEq (rfl : f = f) ℱ).Hom.app (op U) = 𝟙 _ :=
  by
  dsimp [pushforward_eq]
  simp
#align Top.presheaf.pushforward_eq_rfl TopCat.Presheaf.pushforwardEq_rfl

theorem pushforwardEq_eq {X Y : TopCat.{w}} {f g : X ⟶ Y} (h₁ h₂ : f = g) (ℱ : X.Presheaf C) :
    ℱ.pushforwardEq h₁ = ℱ.pushforwardEq h₂ :=
  rfl
#align Top.presheaf.pushforward_eq_eq TopCat.Presheaf.pushforwardEq_eq

namespace Pushforward

variable {X : TopCat.{w}} (ℱ : X.Presheaf C)

/-- The natural isomorphism between the pushforward of a presheaf along the identity continuous map
and the original presheaf. -/
def id : 𝟙 X _* ℱ ≅ ℱ :=
  isoWhiskerRight (NatIso.op (Opens.mapId X).symm) ℱ ≪≫ Functor.leftUnitor _
#align Top.presheaf.pushforward.id TopCat.Presheaf.Pushforward.id

theorem id_eq : 𝟙 X _* ℱ = ℱ := by
  unfold pushforward_obj
  rw [opens.map_id_eq]
  erw [functor.id_comp]
#align Top.presheaf.pushforward.id_eq TopCat.Presheaf.Pushforward.id_eq

@[simp]
theorem id_hom_app' (U) (p) : (id ℱ).Hom.app (op ⟨U, p⟩) = ℱ.map (𝟙 (op ⟨U, p⟩)) :=
  by
  dsimp [id]
  simp
#align Top.presheaf.pushforward.id_hom_app' TopCat.Presheaf.Pushforward.id_hom_app'

attribute [local tidy] tactic.op_induction'

@[simp]
theorem id_hom_app (U) : (id ℱ).Hom.app U = ℱ.map (eqToHom (Opens.op_map_id_obj U)) :=
  by
  -- was `tidy`
  induction U using Opposite.rec'
  cases U
  rw [id_hom_app']
  congr
#align Top.presheaf.pushforward.id_hom_app TopCat.Presheaf.Pushforward.id_hom_app

@[simp]
theorem id_inv_app' (U) (p) : (id ℱ).inv.app (op ⟨U, p⟩) = ℱ.map (𝟙 (op ⟨U, p⟩)) :=
  by
  dsimp [id]
  simp
#align Top.presheaf.pushforward.id_inv_app' TopCat.Presheaf.Pushforward.id_inv_app'

/-- The natural isomorphism between
the pushforward of a presheaf along the composition of two continuous maps and
the corresponding pushforward of a pushforward. -/
def comp {Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g) _* ℱ ≅ g _* (f _* ℱ) :=
  isoWhiskerRight (NatIso.op (Opens.mapComp f g).symm) ℱ
#align Top.presheaf.pushforward.comp TopCat.Presheaf.Pushforward.comp

theorem comp_eq {Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g) _* ℱ = g _* (f _* ℱ) :=
  rfl
#align Top.presheaf.pushforward.comp_eq TopCat.Presheaf.Pushforward.comp_eq

@[simp]
theorem comp_hom_app {Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (comp ℱ f g).Hom.app U = 𝟙 _ := by
  dsimp [comp]
  tidy
#align Top.presheaf.pushforward.comp_hom_app TopCat.Presheaf.Pushforward.comp_hom_app

@[simp]
theorem comp_inv_app {Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (comp ℱ f g).inv.app U = 𝟙 _ := by
  dsimp [comp]
  tidy
#align Top.presheaf.pushforward.comp_inv_app TopCat.Presheaf.Pushforward.comp_inv_app

end Pushforward

/-- A morphism of presheaves gives rise to a morphisms of the pushforwards of those presheaves.
-/
@[simps]
def pushforwardMap {X Y : TopCat.{w}} (f : X ⟶ Y) {ℱ 𝒢 : X.Presheaf C} (α : ℱ ⟶ 𝒢) : f _* ℱ ⟶ f _* 𝒢
    where
  app U := α.app _
  naturality' U V i := by
    erw [α.naturality]
    rfl
#align Top.presheaf.pushforward_map TopCat.Presheaf.pushforwardMap

open CategoryTheory.Limits

section Pullback

variable [HasColimits C]

noncomputable section

/-- Pullback a presheaf on `Y` along a continuous map `f : X ⟶ Y`, obtaining a presheaf on `X`.

This is defined in terms of left Kan extensions, which is just a fancy way of saying
"take the colimits over the open sets whose preimage contains U".
-/
@[simps]
def pullbackObj {X Y : TopCat.{v}} (f : X ⟶ Y) (ℱ : Y.Presheaf C) : X.Presheaf C :=
  (lan (Opens.map f).op).obj ℱ
#align Top.presheaf.pullback_obj TopCat.Presheaf.pullbackObj

/-- Pulling back along continuous maps is functorial. -/
def pullbackMap {X Y : TopCat.{v}} (f : X ⟶ Y) {ℱ 𝒢 : Y.Presheaf C} (α : ℱ ⟶ 𝒢) :
    pullbackObj f ℱ ⟶ pullbackObj f 𝒢 :=
  (lan (Opens.map f).op).map α
#align Top.presheaf.pullback_map TopCat.Presheaf.pullbackMap

/-- If `f '' U` is open, then `f⁻¹ℱ U ≅ ℱ (f '' U)`.  -/
@[simps]
def pullbackObjObjOfImageOpen {X Y : TopCat.{v}} (f : X ⟶ Y) (ℱ : Y.Presheaf C) (U : Opens X)
    (H : IsOpen (f '' U)) : (pullbackObj f ℱ).obj (op U) ≅ ℱ.obj (op ⟨_, H⟩) :=
  by
  let x : costructured_arrow (opens.map f).op (op U) :=
    by
    refine' @costructured_arrow.mk _ _ _ _ _ (op (opens.mk (f '' U) H)) _ _
    exact (@hom_of_le _ _ _ ((opens.map f).obj ⟨_, H⟩) (set.image_preimage.le_u_l _)).op
  have hx : is_terminal x :=
    {
      lift := fun s => by
        fapply costructured_arrow.hom_mk
        change op (unop _) ⟶ op (⟨_, H⟩ : opens _)
        refine' (hom_of_le _).op
        exact
          (Set.image_subset f s.X.hom.unop.le).trans (set.image_preimage.l_u_le ↑(unop s.X.left))
        simp }
  exact
    is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _)
      (colimit_of_diagram_terminal hx _)
#align Top.presheaf.pullback_obj_obj_of_image_open TopCat.Presheaf.pullbackObjObjOfImageOpen

namespace Pullback

variable {X Y : TopCat.{v}} (ℱ : Y.Presheaf C)

/-- The pullback along the identity is isomorphic to the original presheaf. -/
def id : pullbackObj (𝟙 _) ℱ ≅ ℱ :=
  NatIso.ofComponents
    (fun U =>
      pullbackObjObjOfImageOpen (𝟙 _) ℱ (unop U) (by simpa using U.unop.2) ≪≫
        ℱ.mapIso (eqToIso (by simp)))
    fun U V i => by
    ext; simp
    erw [colimit.pre_desc_assoc]
    erw [colimit.ι_desc_assoc]
    erw [colimit.ι_desc_assoc]
    dsimp; simp only [← ℱ.map_comp]; congr
#align Top.presheaf.pullback.id TopCat.Presheaf.Pullback.id

theorem id_inv_app (U : Opens Y) :
    (id ℱ).inv.app (op U) =
      colimit.ι (Lan.diagram (Opens.map (𝟙 Y)).op ℱ (op U))
        (@CostructuredArrow.mk _ _ _ _ _ (op U) _ (eqToHom (by simp))) :=
  by
  rw [← category.id_comp ((id ℱ).inv.app (op U)), ← nat_iso.app_inv, iso.comp_inv_eq]
  dsimp [id]
  rw [colimit.ι_desc_assoc]
  dsimp
  rw [← ℱ.map_comp, ← ℱ.map_id]; rfl
#align Top.presheaf.pullback.id_inv_app TopCat.Presheaf.Pullback.id_inv_app

end Pullback

end Pullback

variable (C)

/-- The pushforward functor.
-/
def pushforward {X Y : TopCat.{w}} (f : X ⟶ Y) : X.Presheaf C ⥤ Y.Presheaf C
    where
  obj := pushforwardObj f
  map := @pushforwardMap _ _ X Y f
#align Top.presheaf.pushforward TopCat.Presheaf.pushforward

@[simp]
theorem pushforward_map_app' {X Y : TopCat.{w}} (f : X ⟶ Y) {ℱ 𝒢 : X.Presheaf C} (α : ℱ ⟶ 𝒢)
    {U : (Opens Y)ᵒᵖ} : ((pushforward C f).map α).app U = α.app (op <| (Opens.map f).obj U.unop) :=
  rfl
#align Top.presheaf.pushforward_map_app' TopCat.Presheaf.pushforward_map_app'

theorem id_pushforward {X : TopCat.{w}} : pushforward C (𝟙 X) = 𝟭 (X.Presheaf C) :=
  by
  apply CategoryTheory.Functor.ext
  · intros
    ext U
    have h := f.congr
    erw [h (opens.op_map_id_obj U)]
    simpa [eq_to_hom_map]
  · intros
    apply pushforward.id_eq
#align Top.presheaf.id_pushforward TopCat.Presheaf.id_pushforward

section Iso

/-- A homeomorphism of spaces gives an equivalence of categories of presheaves. -/
@[simps]
def presheafEquivOfIso {X Y : TopCat} (H : X ≅ Y) : X.Presheaf C ≌ Y.Presheaf C :=
  Equivalence.congrLeft (Opens.mapMapIso H).symm.op
#align Top.presheaf.presheaf_equiv_of_iso TopCat.Presheaf.presheafEquivOfIso

variable {C}

/-- If `H : X ≅ Y` is a homeomorphism,
then given an `H _* ℱ ⟶ 𝒢`, we may obtain an `ℱ ⟶ H ⁻¹ _* 𝒢`.
-/
def toPushforwardOfIso {X Y : TopCat} (H : X ≅ Y) {ℱ : X.Presheaf C} {𝒢 : Y.Presheaf C}
    (α : H.Hom _* ℱ ⟶ 𝒢) : ℱ ⟶ H.inv _* 𝒢 :=
  (presheafEquivOfIso _ H).toAdjunction.homEquiv ℱ 𝒢 α
#align Top.presheaf.to_pushforward_of_iso TopCat.Presheaf.toPushforwardOfIso

@[simp]
theorem toPushforwardOfIso_app {X Y : TopCat} (H₁ : X ≅ Y) {ℱ : X.Presheaf C} {𝒢 : Y.Presheaf C}
    (H₂ : H₁.Hom _* ℱ ⟶ 𝒢) (U : (Opens X)ᵒᵖ) :
    (toPushforwardOfIso H₁ H₂).app U =
      ℱ.map (eqToHom (by simp [opens.map, Set.preimage_preimage])) ≫
        H₂.app (op ((Opens.map H₁.inv).obj (unop U))) :=
  by
  delta to_pushforward_of_iso
  simp only [Equiv.toFun_as_coe, nat_trans.comp_app, equivalence.equivalence_mk'_unit,
    eq_to_hom_map, eq_to_hom_op, eq_to_hom_trans, presheaf_equiv_of_iso_unit_iso_hom_app_app,
    equivalence.to_adjunction, equivalence.equivalence_mk'_counit,
    presheaf_equiv_of_iso_inverse_map_app, adjunction.mk_of_unit_counit_hom_equiv_apply]
  congr
#align Top.presheaf.to_pushforward_of_iso_app TopCat.Presheaf.toPushforwardOfIso_app

/-- If `H : X ≅ Y` is a homeomorphism,
then given an `H _* ℱ ⟶ 𝒢`, we may obtain an `ℱ ⟶ H ⁻¹ _* 𝒢`.
-/
def pushforwardToOfIso {X Y : TopCat} (H₁ : X ≅ Y) {ℱ : Y.Presheaf C} {𝒢 : X.Presheaf C}
    (H₂ : ℱ ⟶ H₁.Hom _* 𝒢) : H₁.inv _* ℱ ⟶ 𝒢 :=
  ((presheafEquivOfIso _ H₁.symm).toAdjunction.homEquiv ℱ 𝒢).symm H₂
#align Top.presheaf.pushforward_to_of_iso TopCat.Presheaf.pushforwardToOfIso

@[simp]
theorem pushforwardToOfIso_app {X Y : TopCat} (H₁ : X ≅ Y) {ℱ : Y.Presheaf C} {𝒢 : X.Presheaf C}
    (H₂ : ℱ ⟶ H₁.Hom _* 𝒢) (U : (Opens X)ᵒᵖ) :
    (pushforwardToOfIso H₁ H₂).app U =
      H₂.app (op ((Opens.map H₁.inv).obj (unop U))) ≫
        𝒢.map (eqToHom (by simp [opens.map, Set.preimage_preimage])) :=
  by simpa [pushforward_to_of_iso, equivalence.to_adjunction]
#align Top.presheaf.pushforward_to_of_iso_app TopCat.Presheaf.pushforwardToOfIso_app

end Iso

variable (C) [HasColimits C]

/-- Pullback a presheaf on `Y` along a continuous map `f : X ⟶ Y`, obtaining a presheaf
on `X`. -/
@[simps map_app]
def pullback {X Y : TopCat.{v}} (f : X ⟶ Y) : Y.Presheaf C ⥤ X.Presheaf C :=
  lan (Opens.map f).op
#align Top.presheaf.pullback TopCat.Presheaf.pullback

@[simp]
theorem pullbackObj_eq_pullbackObj {C} [Category C] [HasColimits C] {X Y : TopCat.{w}} (f : X ⟶ Y)
    (ℱ : Y.Presheaf C) : (pullback C f).obj ℱ = pullbackObj f ℱ :=
  rfl
#align Top.presheaf.pullback_obj_eq_pullback_obj TopCat.Presheaf.pullbackObj_eq_pullbackObj

/-- The pullback and pushforward along a continuous map are adjoint to each other. -/
@[simps unit_app_app counit_app_app]
def pushforwardPullbackAdjunction {X Y : TopCat.{v}} (f : X ⟶ Y) : pullback C f ⊣ pushforward C f :=
  Lan.adjunction _ _
#align Top.presheaf.pushforward_pullback_adjunction TopCat.Presheaf.pushforwardPullbackAdjunction

/-- Pulling back along a homeomorphism is the same as pushing forward along its inverse. -/
def pullbackHomIsoPushforwardInv {X Y : TopCat.{v}} (H : X ≅ Y) :
    pullback C H.Hom ≅ pushforward C H.inv :=
  Adjunction.leftAdjointUniq (pushforwardPullbackAdjunction C H.Hom)
    (presheafEquivOfIso C H.symm).toAdjunction
#align Top.presheaf.pullback_hom_iso_pushforward_inv TopCat.Presheaf.pullbackHomIsoPushforwardInv

/-- Pulling back along the inverse of a homeomorphism is the same as pushing forward along it. -/
def pullbackInvIsoPushforwardHom {X Y : TopCat.{v}} (H : X ≅ Y) :
    pullback C H.inv ≅ pushforward C H.Hom :=
  Adjunction.leftAdjointUniq (pushforwardPullbackAdjunction C H.inv)
    (presheafEquivOfIso C H).toAdjunction
#align Top.presheaf.pullback_inv_iso_pushforward_hom TopCat.Presheaf.pullbackInvIsoPushforwardHom

end Presheaf

end TopCat

