/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Read, Andrew Yang
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Adjunction.Mates
/-!
# Opposite adjunctions

This file contains constructions to relate adjunctions of functors to adjunctions of their
opposites.

## Tags
adjunction, opposite, uniqueness
-/


open CategoryTheory

universe v₁ v₂ u₁ u₂ u₃ v₃

-- morphism levels before object levels. See note [CategoryTheory universes].
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory.Adjunction

attribute [local simp] homEquiv_unit homEquiv_counit

/-- If `G.op` is adjoint to `F.op` then `F` is adjoint to `G`. -/
@[simps! unit_app counit_app]
def adjointOfOpAdjointOp (F : C ⥤ D) (G : D ⥤ C) (h : G.op ⊣ F.op) : F ⊣ G :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun {X Y} =>
      ((h.homEquiv (Opposite.op Y) (Opposite.op X)).trans (opEquiv _ _)).symm.trans
        (opEquiv _ _)
    homEquiv_naturality_left_symm := by
      -- Porting note: This proof was handled by `obviously` in mathlib3. The only obstruction to
      -- automation fully kicking in here is that the `@[simps]` lemmas of `opEquiv` and
      -- `homEquiv` aren't firing.
      intros
      simp [opEquiv, homEquiv]
    homEquiv_naturality_right := by
      -- Porting note: This proof was handled by `obviously` in mathlib3. The only obstruction to
      -- automation fully kicking in here is that the `@[simps]` lemmas of `opEquiv` and
      -- `homEquiv` aren't firing.
      intros
      simp [opEquiv, homEquiv] }

/-- If `G` is adjoint to `F.op` then `F` is adjoint to `G.unop`. -/
def adjointUnopOfAdjointOp (F : C ⥤ D) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G ⊣ F.op) : F ⊣ G.unop :=
  adjointOfOpAdjointOp F G.unop (h.ofNatIsoLeft G.opUnopIso.symm)

/-- If `G.op` is adjoint to `F` then `F.unop` is adjoint to `G`. -/
def unopAdjointOfOpAdjoint (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : D ⥤ C) (h : G.op ⊣ F) : F.unop ⊣ G :=
  adjointOfOpAdjointOp _ _ (h.ofNatIsoRight F.opUnopIso.symm)

/-- If `G` is adjoint to `F` then `F.unop` is adjoint to `G.unop`. -/
def unopAdjointUnopOfAdjoint (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G ⊣ F) : F.unop ⊣ G.unop :=
  adjointUnopOfAdjointOp F.unop G (h.ofNatIsoRight F.opUnopIso.symm)

/-- If `G` is adjoint to `F` then `F.op` is adjoint to `G.op`. -/
@[simps! unit_app counit_app]
def opAdjointOpOfAdjoint (F : C ⥤ D) (G : D ⥤ C) (h : G ⊣ F) : F.op ⊣ G.op :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X Y =>
      (opEquiv _ Y).trans ((h.homEquiv _ _).symm.trans (opEquiv X (Opposite.op _)).symm)
    homEquiv_naturality_left_symm := by
      -- Porting note: This proof was handled by `obviously` in mathlib3. The only obstruction to
      -- automation fully kicking in here is that the `@[simps]` lemmas of `opEquiv` aren't firing.
      intros
      simp [opEquiv]
    homEquiv_naturality_right := by
      -- Porting note: This proof was handled by `obviously` in mathlib3. The only obstruction to
      -- automation fully kicking in here is that the `@[simps]` lemmas of `opEquiv` aren't firing.
      intros
      simp [opEquiv] }

lemma opAdjointOpOfAdjoint_homEquiv (F : C ⥤ D) (G : D ⥤ C) (h : G ⊣ F) (X : Cᵒᵖ) (Y : Dᵒᵖ) :
    (h.opAdjointOpOfAdjoint F G).homEquiv X Y = (opEquiv _ Y).trans ((h.homEquiv _ _).symm.trans
    (opEquiv X (Opposite.op _)).symm) := by simp [opAdjointOpOfAdjoint]

/-- If `G` is adjoint to `F.unop` then `F` is adjoint to `G.op`. -/
def adjointOpOfAdjointUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : D ⥤ C) (h : G ⊣ F.unop) : F ⊣ G.op :=
  (opAdjointOpOfAdjoint F.unop _ h).ofNatIsoLeft F.opUnopIso

/-- If `G.unop` is adjoint to `F` then `F.op` is adjoint to `G`. -/
def opAdjointOfUnopAdjoint (F : C ⥤ D) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G.unop ⊣ F) : F.op ⊣ G :=
  (opAdjointOpOfAdjoint _ G.unop h).ofNatIsoRight G.opUnopIso

/-- If `G.unop` is adjoint to `F.unop` then `F` is adjoint to `G`. -/
def adjointOfUnopAdjointUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G.unop ⊣ F.unop) : F ⊣ G :=
  (adjointOpOfAdjointUnop _ _ h).ofNatIsoRight G.opUnopIso

variable {E : Type u₃} [Category.{v₃,u₃} E] {F : C ⥤ D} {G : D ⥤ C} {F' : D ⥤ E} {G' : E ⥤ D}
(adj : F ⊣ G) (adj' : F' ⊣ G')
/-- Composition of adjunctions is compatible with taking opposite adjunctions.
-/
lemma comp_op : (Adjunction.comp adj adj').opAdjointOpOfAdjoint =
    Adjunction.comp adj'.opAdjointOpOfAdjoint adj.opAdjointOpOfAdjoint := by
  ext _
  · simp only [Functor.id_obj, Functor.comp_obj, Functor.op_obj, opAdjointOpOfAdjoint_unit_app,
    Functor.comp_map, comp_counit_app, comp_unit_app, Functor.op_map]
    rw [opEquiv_symm_apply, opEquiv_apply, opEquiv_symm_apply, opEquiv_symm_apply, opEquiv_apply]
    simp
  · simp only [Functor.comp_obj, Functor.op_obj, Functor.id_obj, opAdjointOpOfAdjoint_counit_app,
    comp_unit_app, Functor.comp_map, Category.assoc, comp_counit_app, Functor.op_map]
    rw [opEquiv_apply, opEquiv_apply, opEquiv_symm_apply, opEquiv_symm_apply, opEquiv_symm_apply]
    simp

end Adjunction

/-- If `e : C ≌ D` is an equivalence of categories, then the adjunction induced by
`e.op : Cᵒᵖ ≌ Dᵒᵖ` is the opposite of `e.symm.toAdjunction`.-/
lemma Equivalence.op_toAdjunction (e : C ≌ D) :
    e.op.toAdjunction = e.symm.toAdjunction.opAdjointOpOfAdjoint := by
  ext
  · simp only [Functor.id_obj, op_functor, op_inverse, Functor.comp_obj, Functor.op_obj,
    toAdjunction_unit, symm_inverse, symm_functor, Adjunction.opAdjointOpOfAdjoint_unit_app,
    toAdjunction_counit]
    rw [opEquiv_apply, opEquiv_symm_apply]
    simp only [unop_id, Functor.map_id, Category.id_comp]
    rfl
  · simp only [op_inverse, op_functor, Functor.comp_obj, Functor.op_obj, Functor.id_obj,
    toAdjunction_counit, symm_inverse, symm_functor, Adjunction.opAdjointOpOfAdjoint_counit_app,
    toAdjunction_unit]
    rw [opEquiv_apply, opEquiv_symm_apply]
    simp only [unop_id, Functor.map_id, Category.comp_id]
    rfl

namespace Adjunction

attribute [local simp] homEquiv_unit homEquiv_counit

/-- If `F` and `F'` are both adjoint to `G`, there is a natural isomorphism
`F.op ⋙ coyoneda ≅ F'.op ⋙ coyoneda`.
We use this in combination with `fullyFaithfulCancelRight` to show left adjoints are unique.
-/
def leftAdjointsCoyonedaEquiv {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) :
    F.op ⋙ coyoneda ≅ F'.op ⋙ coyoneda :=
  NatIso.ofComponents fun X =>
    NatIso.ofComponents fun Y =>
      ((adj1.homEquiv X.unop Y).trans (adj2.homEquiv X.unop Y).symm).toIso

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

/-- Given two adjunctions, if the left adjoints are naturally isomorphic, then so are the right
adjoints.

Note: it is generally better to use `Adjunction.natIsoEquiv`, see the file `Adjunction.Unique`.
-/
def natIsoOfLeftAdjointNatIso {F F' : C ⥤ D} {G G' : D ⥤ C}
    (adj1 : F ⊣ G) (adj2 : F' ⊣ G') (l : F ≅ F') : G ≅ G' :=
  NatIso.removeOp (natIsoOfRightAdjointNatIso (opAdjointOpOfAdjoint _ F' adj2)
    (opAdjointOpOfAdjoint _ _ adj1) (NatIso.op l))

/-- If we have adjunctions `F ⊣ G` and `F' ⊣ G'` from `C` to `D`, then `conjugateIsoEquiv`
gives an equivalence between `F' ≅ F` and `G ≅ G'`. This lemmas expresses the compatibility
of this equivalence with taking opposites of functors, adjunctions and natural isomorphisms.
-/
lemma conjugateIsoEquiv_op (F F' : C ⥤ D) (G G' : D ⥤ C) (adj : F ⊣ G) (adj' : F' ⊣ G') :
    (natIsoOpEquiv G G').trans
    ((conjugateIsoEquiv adj.opAdjointOpOfAdjoint adj'.opAdjointOpOfAdjoint).trans
    (natIsoOpEquiv F' F).symm) = (conjugateIsoEquiv adj adj').symm := by
  ext _
  simp only [natIsoOpEquiv, Equiv.trans_apply, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
    NatIso.removeOp_hom, conjugateIsoEquiv_apply_hom, NatIso.op_hom, NatTrans.removeOp_app,
    Functor.op_obj, conjugateEquiv_apply_app, opAdjointOpOfAdjoint_unit_app, NatTrans.op_app,
    Functor.op_map, Quiver.Hom.unop_op, opAdjointOpOfAdjoint_counit_app, unop_comp, Category.assoc,
    conjugateIsoEquiv_symm_apply_hom, conjugateEquiv_symm_apply_app]
  rw [opEquiv_apply, opEquiv_apply, opEquiv_symm_apply, opEquiv_symm_apply]
  simp

end CategoryTheory.Adjunction
