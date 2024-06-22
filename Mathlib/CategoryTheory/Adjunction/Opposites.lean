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

/-- Given two adjunctions, if the right adjoints are naturally isomorphic, then so are the left
adjoints.

Note: it is generally better to use `Adjunction.natIsoEquiv`, see the file `Adjunction.Unique`.
The reason this definition still exists is that apparently `CategoryTheory.extendAlongYonedaYoneda`
uses its definitional properties (TODO: figure out a way to avoid this).
-/
def natIsoOfRightAdjointNatIso {F F' : C ⥤ D} {G G' : D ⥤ C}
    (adj1 : F ⊣ G) (adj2 : F' ⊣ G') (r : G ≅ G') : F ≅ F' :=
  NatIso.removeOp ((Coyoneda.fullyFaithful.whiskeringRight _).isoEquiv.symm
    (leftAdjointsCoyonedaEquiv adj2 (adj1.ofNatIsoRight r)))
#align category_theory.adjunction.nat_iso_of_right_adjoint_nat_iso CategoryTheory.Adjunction.natIsoOfRightAdjointNatIso

/-- Given two adjunctions, if the left adjoints are naturally isomorphic, then so are the right
adjoints.

Note: it is generally better to use `Adjunction.natIsoEquiv`, see the file `Adjunction.Unique`.
-/
def natIsoOfLeftAdjointNatIso {F F' : C ⥤ D} {G G' : D ⥤ C}
    (adj1 : F ⊣ G) (adj2 : F' ⊣ G') (l : F ≅ F') : G ≅ G' :=
  NatIso.removeOp (natIsoOfRightAdjointNatIso (opAdjointOpOfAdjoint _ F' adj2)
    (opAdjointOpOfAdjoint _ _ adj1) (NatIso.op l))
#align category_theory.adjunction.nat_iso_of_left_adjoint_nat_iso CategoryTheory.Adjunction.natIsoOfLeftAdjointNatIso

end CategoryTheory.Adjunction
