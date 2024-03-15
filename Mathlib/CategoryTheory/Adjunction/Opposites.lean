/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Read, Andrew Yang
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Opposites

#align_import category_theory.adjunction.opposites from "leanprover-community/mathlib"@"0148d455199ed64bf8eb2f493a1e7eb9211ce170"

/-!
# Opposite adjunctions

This file contains constructions to relate adjunctions of functors to adjunctions of their
opposites.
These constructions are used to show uniqueness of adjoints (up to natural isomorphism).

## Tags
adjunction, opposite, uniqueness
-/


open CategoryTheory

universe v₁ v₂ u₁ u₂

-- morphism levels before object levels. See note [CategoryTheory universes].
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory.Adjunction

/-- If `G.op` is adjoint to `F.op` then `F` is adjoint to `G`. -/
-- Porting note: in mathlib3 we generated all the default `simps` lemmas.
-- However the `simpNF` linter correctly flags some of these as unsuitable simp lemmas.
-- `unit_app` and `counit_app` appear to suffice (tested in mathlib3).
-- See also the porting note on opAdjointOpOfAdjoint
@[simps! unit_app counit_app]
def adjointOfOpAdjointOp (F : C ⥤ D) (G : D ⥤ C) (h : G.op ⊣ F.op) : F ⊣ G :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun {X Y} =>
      ((h.homEquiv (Opposite.op Y) (Opposite.op X)).trans (opEquiv _ _)).symm.trans
        (opEquiv _ _)
    homEquiv_naturality_left_symm := by
      -- Porting note: This proof was handled by `obviously` in mathlib3.
      intros X' X Y f g
      dsimp [opEquiv]
      -- Porting note: Why is `erw` needed here?
      -- https://github.com/leanprover-community/mathlib4/issues/5164
      erw [homEquiv_unit, homEquiv_unit]
      simp
    homEquiv_naturality_right := by
      -- Porting note: This proof was handled by `obviously` in mathlib3.
      intros X Y Y' f g
      dsimp [opEquiv]
      -- Porting note: Why is `erw` needed here?
      -- https://github.com/leanprover-community/mathlib4/issues/5164
      erw [homEquiv_counit, homEquiv_counit]
      simp }
#align category_theory.adjunction.adjoint_of_op_adjoint_op CategoryTheory.Adjunction.adjointOfOpAdjointOp

/-- If `G` is adjoint to `F.op` then `F` is adjoint to `G.unop`. -/
def adjointUnopOfAdjointOp (F : C ⥤ D) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G ⊣ F.op) : F ⊣ G.unop :=
  adjointOfOpAdjointOp F G.unop (h.ofNatIsoLeft G.opUnopIso.symm)
#align category_theory.adjunction.adjoint_unop_of_adjoint_op CategoryTheory.Adjunction.adjointUnopOfAdjointOp

/-- If `G.op` is adjoint to `F` then `F.unop` is adjoint to `G`. -/
def unopAdjointOfOpAdjoint (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : D ⥤ C) (h : G.op ⊣ F) : F.unop ⊣ G :=
  adjointOfOpAdjointOp _ _ (h.ofNatIsoRight F.opUnopIso.symm)
#align category_theory.adjunction.unop_adjoint_of_op_adjoint CategoryTheory.Adjunction.unopAdjointOfOpAdjoint

/-- If `G` is adjoint to `F` then `F.unop` is adjoint to `G.unop`. -/
def unopAdjointUnopOfAdjoint (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G ⊣ F) : F.unop ⊣ G.unop :=
  adjointUnopOfAdjointOp F.unop G (h.ofNatIsoRight F.opUnopIso.symm)
#align category_theory.adjunction.unop_adjoint_unop_of_adjoint CategoryTheory.Adjunction.unopAdjointUnopOfAdjoint

/-- If `G` is adjoint to `F` then `F.op` is adjoint to `G.op`. -/
@[simps! unit_app counit_app]
-- Porting note: in mathlib3 we generated all the default `simps` lemmas.
-- However the `simpNF` linter correctly flags some of these as unsuitable simp lemmas.
-- `unit_app` and `counit_app` appear to suffice (tested in mathlib3).
-- See also the porting note on adjointOfOpAdjointOp
def opAdjointOpOfAdjoint (F : C ⥤ D) (G : D ⥤ C) (h : G ⊣ F) : F.op ⊣ G.op :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X Y =>
      (opEquiv _ Y).trans ((h.homEquiv _ _).symm.trans (opEquiv X (Opposite.op _)).symm)
    homEquiv_naturality_left_symm := by
      -- Porting note: This proof was handled by `obviously` in mathlib3.
      intros X' X Y f g
      dsimp [opEquiv]
      -- Porting note: Why is `erw` needed here?
      -- https://github.com/leanprover-community/mathlib4/issues/5164
      erw [homEquiv_unit, homEquiv_unit]
      simp
    homEquiv_naturality_right := by
      -- Porting note: This proof was handled by `obviously` in mathlib3.
      intros X' X Y f g
      dsimp [opEquiv]
      -- Porting note: Why is `erw` needed here?
      -- https://github.com/leanprover-community/mathlib4/issues/5164
      erw [homEquiv_counit, homEquiv_counit]
      simp }
#align category_theory.adjunction.op_adjoint_op_of_adjoint CategoryTheory.Adjunction.opAdjointOpOfAdjoint

/-- If `G` is adjoint to `F.unop` then `F` is adjoint to `G.op`. -/
def adjointOpOfAdjointUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : D ⥤ C) (h : G ⊣ F.unop) : F ⊣ G.op :=
  (opAdjointOpOfAdjoint F.unop _ h).ofNatIsoLeft F.opUnopIso
#align category_theory.adjunction.adjoint_op_of_adjoint_unop CategoryTheory.Adjunction.adjointOpOfAdjointUnop

/-- If `G.unop` is adjoint to `F` then `F.op` is adjoint to `G`. -/
def opAdjointOfUnopAdjoint (F : C ⥤ D) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G.unop ⊣ F) : F.op ⊣ G :=
  (opAdjointOpOfAdjoint _ G.unop h).ofNatIsoRight G.opUnopIso
#align category_theory.adjunction.op_adjoint_of_unop_adjoint CategoryTheory.Adjunction.opAdjointOfUnopAdjoint

/-- If `G.unop` is adjoint to `F.unop` then `F` is adjoint to `G`. -/
def adjointOfUnopAdjointUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G.unop ⊣ F.unop) : F ⊣ G :=
  (adjointOpOfAdjointUnop _ _ h).ofNatIsoRight G.opUnopIso
#align category_theory.adjunction.adjoint_of_unop_adjoint_unop CategoryTheory.Adjunction.adjointOfUnopAdjointUnop

/-- If `F` and `F'` are both adjoint to `G`, there is a natural isomorphism
`F.op ⋙ coyoneda ≅ F'.op ⋙ coyoneda`.
We use this in combination with `fullyFaithfulCancelRight` to show left adjoints are unique.
-/
def leftAdjointsCoyonedaEquiv {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) :
    F.op ⋙ coyoneda ≅ F'.op ⋙ coyoneda :=
  NatIso.ofComponents fun X =>
    NatIso.ofComponents fun Y =>
      ((adj1.homEquiv X.unop Y).trans (adj2.homEquiv X.unop Y).symm).toIso
#align category_theory.adjunction.left_adjoints_coyoneda_equiv CategoryTheory.Adjunction.leftAdjointsCoyonedaEquiv

/-- If `F` and `F'` are both left adjoint to `G`, then they are naturally isomorphic. -/
def leftAdjointUniq {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) : F ≅ F' :=
  NatIso.removeOp (fullyFaithfulCancelRight _ (leftAdjointsCoyonedaEquiv adj2 adj1))
#align category_theory.adjunction.left_adjoint_uniq CategoryTheory.Adjunction.leftAdjointUniq

-- Porting note (#10618): removed simp as simp can prove this
theorem homEquiv_leftAdjointUniq_hom_app {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    (x : C) : adj1.homEquiv _ _ ((leftAdjointUniq adj1 adj2).hom.app x) = adj2.unit.app x := by
  apply (adj1.homEquiv _ _).symm.injective
  apply Quiver.Hom.op_inj
  apply coyoneda.map_injective
  --swap; infer_instance
  ext
  simp [leftAdjointUniq, leftAdjointsCoyonedaEquiv]
#align category_theory.adjunction.hom_equiv_left_adjoint_uniq_hom_app CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app

@[reassoc (attr := simp)]
theorem unit_leftAdjointUniq_hom {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) :
    adj1.unit ≫ whiskerRight (leftAdjointUniq adj1 adj2).hom G = adj2.unit := by
  ext x
  rw [NatTrans.comp_app, ← homEquiv_leftAdjointUniq_hom_app adj1 adj2]
  simp [← G.map_comp]
#align category_theory.adjunction.unit_left_adjoint_uniq_hom CategoryTheory.Adjunction.unit_leftAdjointUniq_hom

@[reassoc (attr := simp)]
theorem unit_leftAdjointUniq_hom_app {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    (x : C) : adj1.unit.app x ≫ G.map ((leftAdjointUniq adj1 adj2).hom.app x) = adj2.unit.app x :=
  by rw [← unit_leftAdjointUniq_hom adj1 adj2]; rfl
#align category_theory.adjunction.unit_left_adjoint_uniq_hom_app CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app

@[reassoc (attr := simp)]
theorem leftAdjointUniq_hom_counit {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) :
    whiskerLeft G (leftAdjointUniq adj1 adj2).hom ≫ adj2.counit = adj1.counit := by
  ext x
  apply Quiver.Hom.op_inj
  apply coyoneda.map_injective
  ext
  simp [leftAdjointUniq, leftAdjointsCoyonedaEquiv]
#align category_theory.adjunction.left_adjoint_uniq_hom_counit CategoryTheory.Adjunction.leftAdjointUniq_hom_counit

@[reassoc (attr := simp)]
theorem leftAdjointUniq_hom_app_counit {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    (x : D) :
    (leftAdjointUniq adj1 adj2).hom.app (G.obj x) ≫ adj2.counit.app x = adj1.counit.app x := by
  rw [← leftAdjointUniq_hom_counit adj1 adj2]
  rfl
#align category_theory.adjunction.left_adjoint_uniq_hom_app_counit CategoryTheory.Adjunction.leftAdjointUniq_hom_app_counit

@[simp]
theorem leftAdjointUniq_inv_app {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (x : C) :
    (leftAdjointUniq adj1 adj2).inv.app x = (leftAdjointUniq adj2 adj1).hom.app x :=
  rfl
#align category_theory.adjunction.left_adjoint_uniq_inv_app CategoryTheory.Adjunction.leftAdjointUniq_inv_app

@[reassoc (attr := simp)]
theorem leftAdjointUniq_trans {F F' F'' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    (adj3 : F'' ⊣ G) :
    (leftAdjointUniq adj1 adj2).hom ≫ (leftAdjointUniq adj2 adj3).hom =
      (leftAdjointUniq adj1 adj3).hom := by
  ext
  apply Quiver.Hom.op_inj
  apply coyoneda.map_injective
  ext
  simp [leftAdjointsCoyonedaEquiv, leftAdjointUniq]
#align category_theory.adjunction.left_adjoint_uniq_trans CategoryTheory.Adjunction.leftAdjointUniq_trans

@[reassoc (attr := simp)]
theorem leftAdjointUniq_trans_app {F F' F'' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    (adj3 : F'' ⊣ G) (x : C) :
    (leftAdjointUniq adj1 adj2).hom.app x ≫ (leftAdjointUniq adj2 adj3).hom.app x =
      (leftAdjointUniq adj1 adj3).hom.app x := by
  rw [← leftAdjointUniq_trans adj1 adj2 adj3]
  rfl
#align category_theory.adjunction.left_adjoint_uniq_trans_app CategoryTheory.Adjunction.leftAdjointUniq_trans_app

@[simp]
theorem leftAdjointUniq_refl {F : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) :
    (leftAdjointUniq adj1 adj1).hom = 𝟙 _ := by
  ext
  apply Quiver.Hom.op_inj
  apply coyoneda.map_injective
  ext
  simp [leftAdjointsCoyonedaEquiv, leftAdjointUniq]
#align category_theory.adjunction.left_adjoint_uniq_refl CategoryTheory.Adjunction.leftAdjointUniq_refl

/-- If `G` and `G'` are both right adjoint to `F`, then they are naturally isomorphic. -/
def rightAdjointUniq {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') : G ≅ G' :=
  NatIso.removeOp (leftAdjointUniq (opAdjointOpOfAdjoint _ F adj2) (opAdjointOpOfAdjoint _ _ adj1))
#align category_theory.adjunction.right_adjoint_uniq CategoryTheory.Adjunction.rightAdjointUniq

-- Porting note (#10618): simp can prove this
theorem homEquiv_symm_rightAdjointUniq_hom_app {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G)
    (adj2 : F ⊣ G') (x : D) :
    (adj2.homEquiv _ _).symm ((rightAdjointUniq adj1 adj2).hom.app x) = adj1.counit.app x := by
  apply Quiver.Hom.op_inj
  convert homEquiv_leftAdjointUniq_hom_app (opAdjointOpOfAdjoint _ F adj2)
    (opAdjointOpOfAdjoint _ _ adj1) (Opposite.op x)
  -- Porting note: was `simpa`
  simp only [opAdjointOpOfAdjoint, Functor.op_obj, Opposite.unop_op, mkOfHomEquiv_unit_app,
    Equiv.trans_apply, homEquiv_counit, Functor.id_obj]
  -- Porting note: Yet another `erw`...
  -- https://github.com/leanprover-community/mathlib4/issues/5164
  erw [F.map_id]
  rw [Category.id_comp]
  rfl
#align category_theory.adjunction.hom_equiv_symm_right_adjoint_uniq_hom_app CategoryTheory.Adjunction.homEquiv_symm_rightAdjointUniq_hom_app

@[reassoc (attr := simp)]
theorem unit_rightAdjointUniq_hom_app {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
    (x : C) : adj1.unit.app x ≫ (rightAdjointUniq adj1 adj2).hom.app (F.obj x) =
      adj2.unit.app x := by
  apply Quiver.Hom.op_inj
  convert
    leftAdjointUniq_hom_app_counit (opAdjointOpOfAdjoint _ _ adj2)
      (opAdjointOpOfAdjoint _ _ adj1) (Opposite.op x) using 1
  --all_goals simp
  all_goals {
    -- Porting note: Again, something seems wrong here... Some `simp` lemmas are not firing!
    simp only [Functor.id_obj, Functor.comp_obj, op_comp, Functor.op_obj, Opposite.unop_op,
      opAdjointOpOfAdjoint, mkOfHomEquiv_counit_app, Equiv.invFun_as_coe, Equiv.symm_trans_apply,
      Equiv.symm_symm, homEquiv_unit]
    erw [Functor.map_id]
    rw [Category.comp_id]
    rfl }
#align category_theory.adjunction.unit_right_adjoint_uniq_hom_app CategoryTheory.Adjunction.unit_rightAdjointUniq_hom_app

@[reassoc (attr := simp)]
theorem unit_rightAdjointUniq_hom {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') :
    adj1.unit ≫ whiskerLeft F (rightAdjointUniq adj1 adj2).hom = adj2.unit := by
  ext x
  simp
#align category_theory.adjunction.unit_right_adjoint_uniq_hom CategoryTheory.Adjunction.unit_rightAdjointUniq_hom

@[reassoc (attr := simp)]
theorem rightAdjointUniq_hom_app_counit {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
    (x : D) :
    F.map ((rightAdjointUniq adj1 adj2).hom.app x) ≫ adj2.counit.app x = adj1.counit.app x := by
  apply Quiver.Hom.op_inj
  convert
    unit_leftAdjointUniq_hom_app (opAdjointOpOfAdjoint _ _ adj2)
      (opAdjointOpOfAdjoint _ _ adj1) (Opposite.op x) using 1
  · simp only [Functor.id_obj, op_comp, Functor.comp_obj, Functor.op_obj, Opposite.unop_op,
      opAdjointOpOfAdjoint_unit_app, Functor.op_map]
    dsimp [opEquiv]
    simp only [← op_comp]
    congr 2
    simp
  · simp only [Functor.id_obj, opAdjointOpOfAdjoint_unit_app, Opposite.unop_op]
    erw [Functor.map_id, Category.id_comp]
    rfl
#align category_theory.adjunction.right_adjoint_uniq_hom_app_counit CategoryTheory.Adjunction.rightAdjointUniq_hom_app_counit

@[reassoc (attr := simp)]
theorem rightAdjointUniq_hom_counit {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') :
    whiskerRight (rightAdjointUniq adj1 adj2).hom F ≫ adj2.counit = adj1.counit := by
  ext
  simp
#align category_theory.adjunction.right_adjoint_uniq_hom_counit CategoryTheory.Adjunction.rightAdjointUniq_hom_counit

@[simp]
theorem rightAdjointUniq_inv_app {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
    (x : D) : (rightAdjointUniq adj1 adj2).inv.app x = (rightAdjointUniq adj2 adj1).hom.app x :=
  rfl
#align category_theory.adjunction.right_adjoint_uniq_inv_app CategoryTheory.Adjunction.rightAdjointUniq_inv_app

@[reassoc (attr := simp)]
theorem rightAdjointUniq_trans_app {F : C ⥤ D} {G G' G'' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
    (adj3 : F ⊣ G'') (x : D) :
    (rightAdjointUniq adj1 adj2).hom.app x ≫ (rightAdjointUniq adj2 adj3).hom.app x =
      (rightAdjointUniq adj1 adj3).hom.app x := by
  apply Quiver.Hom.op_inj
  dsimp [rightAdjointUniq]
  simp
#align category_theory.adjunction.right_adjoint_uniq_trans_app CategoryTheory.Adjunction.rightAdjointUniq_trans_app

@[reassoc (attr := simp)]
theorem rightAdjointUniq_trans {F : C ⥤ D} {G G' G'' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
    (adj3 : F ⊣ G'') :
    (rightAdjointUniq adj1 adj2).hom ≫ (rightAdjointUniq adj2 adj3).hom =
      (rightAdjointUniq adj1 adj3).hom := by
  ext
  simp
#align category_theory.adjunction.right_adjoint_uniq_trans CategoryTheory.Adjunction.rightAdjointUniq_trans

@[simp]
theorem rightAdjointUniq_refl {F : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) :
    (rightAdjointUniq adj1 adj1).hom = 𝟙 _ := by
  delta rightAdjointUniq
  simp
#align category_theory.adjunction.right_adjoint_uniq_refl CategoryTheory.Adjunction.rightAdjointUniq_refl

/-- Given two adjunctions, if the left adjoints are naturally isomorphic, then so are the right
adjoints.
-/
def natIsoOfLeftAdjointNatIso {F F' : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G')
    (l : F ≅ F') : G ≅ G' :=
  rightAdjointUniq adj1 (adj2.ofNatIsoLeft l.symm)
#align category_theory.adjunction.nat_iso_of_left_adjoint_nat_iso CategoryTheory.Adjunction.natIsoOfLeftAdjointNatIso

/-- Given two adjunctions, if the right adjoints are naturally isomorphic, then so are the left
adjoints.
-/
def natIsoOfRightAdjointNatIso {F F' : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G')
    (r : G ≅ G') : F ≅ F' :=
  leftAdjointUniq adj1 (adj2.ofNatIsoRight r.symm)
#align category_theory.adjunction.nat_iso_of_right_adjoint_nat_iso CategoryTheory.Adjunction.natIsoOfRightAdjointNatIso

end CategoryTheory.Adjunction
