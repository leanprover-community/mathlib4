/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/

import Mathlib.CategoryTheory.Shift.Opposite
import Mathlib.CategoryTheory.Shift.Pullback

/-!
# Commutation with shifts and adjunction

-/

namespace CategoryTheory

open Category Functor CategoryTheory Opposite Adjunction CommShift

universe u₁ u₂ v₁ v₂ u

variable {C : Type u₁} {D : Type u₂} [Category.{v₁,u₁} C] [Category.{v₂,u₂} D]
  {F : C ⥤ D} {G : D ⥤ C} {A : Type u} [AddGroup A]
  [HasShift C A] [HasShift D A]

section Compatibility

namespace Adjunction

namespace CommShift

/-- Suppose that we have an adjunction between functors `adj : F ⊣ G` with `F : C ⥤ D`,
that `C` and `D` have shifts by an additive group `A`, that `a, b` are elements of `A`
such that `a + b = 0`, and that we are given isomorphisms
`e₁ : (shiftFunctor C a) ⋙ F ≅ F ⋙ (shiftFunctor D a)` and
`e₂ : (shiftFunctor D b) ⋙ G ≅ G ⋙ (shiftFunctor C b)`.

Given a morphism `u : F.obj (X⟦a⟧) ⟶ Y`, there are two natural ways to construct a
morphism `X ⟶ G.obj (Y⟦b⟧)` from `u`:
(1) Apply `Adjunction.homEquiv` for the composition of the adjunction deduced from
the equivalence `shiftEquiv' C a b` and of `adj` to obtain a morphism `X ⟶ (G.obj Y)⟦b⟧` then
compose on the right with the inverse of `e₂`;
(2) Compose on the left with the inverse of `e₁` to obtain a morphism `(F.obj X)⟦a⟧ ⟶ Y`
then apply `Adjunction.homEquiv` for the composition of `adj` and of the adjunction deduced from
the equivalence `shiftEquiv' D a b`).

We say that the adjunction `adj` is compatible with the isomorphisms `e₁` and `e₂` if,
for every morphism `u : F.obj(X⟦a⟧) ⟶ Y`, these two constructions give the same result.
-/
abbrev compat_left_right (adj : F ⊣ G) (a b : A) (h : a + b = 0)
    (e₁ : (shiftFunctor C a) ⋙ F ≅ F ⋙ (shiftFunctor D a))
    (e₂ : (shiftFunctor D b) ⋙ G ≅ G ⋙ (shiftFunctor C b)) :=
  ∀ (X : C) (Y : D) (u : F.obj (X⟦a⟧) ⟶ Y),
  ((shiftEquiv' C a b h).toAdjunction.comp adj).homEquiv X Y u ≫ e₂.inv.app Y =
  (adj.comp (shiftEquiv' D a b h).toAdjunction).homEquiv X Y (e₁.inv.app X ≫ u)

/--
Suppose that we have an adjunction between functors `adj : F ⊣ G` with `F : C ⥤ D`,
that `C` and `D` have shifts by an additive group `A`, that `a, b` are elements of `A`
such that `a + b = 0`, and that we are given isomorphisms
`e₁ : (shiftFunctor C a) ⋙ F ≅ F ⋙ (shiftFunctor D a)` and
`e₂ : (shiftFunctor D b) ⋙ G ≅ G ⋙ (shiftFunctor C b)`.

If `adj` is compatible with `e₁` and `e₂` in the sense of `compat_left_right`, this is the
compatibility condition in the other direction: for every morphism `v : X ⟶ G.obj (Y⟦a⟧)`,
the two natural ways to construct a morphism `F.obj (X⟦-a⟧) ⟶ Y` from `v` give the same result.
-/
lemma compat_right_left (adj : F ⊣ G) (a b : A) (h : a + b = 0)
    (e₁ : (shiftFunctor C a) ⋙ F ≅ F ⋙ (shiftFunctor D a))
    (e₂ : (shiftFunctor D b) ⋙ G ≅ G ⋙ (shiftFunctor C b))
    (hc : compat_left_right adj a b h e₁ e₂)
    (X : C) (Y : D) (v : X ⟶ G.obj (Y⟦b⟧)) :
    e₁.hom.app X ≫
    ((adj.comp (shiftEquiv' D a b h).toAdjunction).homEquiv _ _).symm v =
    (((shiftEquiv' C a b h).toAdjunction.comp adj).homEquiv _ _).symm
    (v ≫ e₂.hom.app Y) := by
  have := hc _ _ (e₁.hom.app X ≫
    ((adj.comp (shiftEquiv' D a b h).toAdjunction).homEquiv _ _).symm v)
  conv_rhs at this => rw [← assoc, Iso.inv_hom_id_app]; erw [id_comp]; rw [Equiv.apply_symm_apply]
  conv_rhs => rw [← this, assoc, Iso.inv_hom_id_app]; erw [comp_id]; rw [Equiv.symm_apply_apply]

/--
Suppose that we have an adjunction between functors `adj : F ⊣ G` with `F : C ⥤ D`,
that `C` and `D` have shifts by an additive group `A`, that `a, b` are elements of `A`
such that `a + b = 0`, and that we are given isomorphisms
`e₁ : (shiftFunctor C a) ⋙ F ≅ F ⋙ (shiftFunctor D a)`,
`e₂ : (shiftFunctor D b) ⋙ G ≅ G ⋙ (shiftFunctor C b)` and
`e₂' : (shiftFunctor D b) ⋙ G ≅ G ⋙ (shiftFunctor C b)`.

If `adj` is compatible with `e₁` and `e₂` in the sense of `compat_left_right`, and
also with `e₁` and `e₂'`, then we have `e₂ = e₂'`.
-/
lemma compat_left_right_unique_right (adj : F ⊣ G) (a b : A) (h : a + b = 0)
    (e₁ : (shiftFunctor C a) ⋙ F ≅ F ⋙ (shiftFunctor D a))
    (e₂ : (shiftFunctor D b) ⋙ G ≅ G ⋙ (shiftFunctor C b))
    (e₂' : (shiftFunctor D b) ⋙ G ≅ G ⋙ (shiftFunctor C b))
    (hc : compat_left_right adj a b h e₁ e₂) (hc' : compat_left_right adj a b h e₁ e₂') :
    e₂ = e₂' := by
  ext Y
  have heq := compat_right_left adj a b h e₁ e₂ hc _ Y (𝟙 _)
  apply_fun (((shiftEquiv' C a b h).toAdjunction.comp adj).homEquiv
    (G.obj ((shiftFunctor D b).obj Y)) Y) at heq
  rw [Equiv.apply_symm_apply, id_comp] at heq
  have heq' := compat_right_left adj a b h e₁ e₂' hc' _ Y (𝟙 _)
  apply_fun (((shiftEquiv' C a b h).toAdjunction.comp adj).homEquiv
    (G.obj ((shiftFunctor D b).obj Y)) Y) at heq'
  rw [Equiv.apply_symm_apply, id_comp] at heq'
  rw [← heq, ← heq']

/--
Suppose that we have an adjunction between functors `adj : F ⊣ G` with `F : C ⥤ D`,
that `C` and `D` have shifts by an additive group `A`, that `a, b` are elements of `A`
such that `a + b = 0`, and that we are given isomorphisms
`e₁ : (shiftFunctor C a) ⋙ F ≅ F ⋙ (shiftFunctor D a)`,
`(e₁ : (shiftFunctor C a) ⋙ F ≅ F ⋙ (shiftFunctor D a))` and
`e₂ : (shiftFunctor D b) ⋙ G ≅ G ⋙ (shiftFunctor C b)`.

If `adj` is compatible with `e₁` and `e₂` in the sense of `compat_left_right`, and
also with `e₁'` and `e₂'`, then we have `e₁ = e₁'`.
-/
lemma compat_left_right_unique_left (adj : F ⊣ G) (a b : A) (h : a + b = 0)
    (e₁ : (shiftFunctor C a) ⋙ F ≅ F ⋙ (shiftFunctor D a))
    (e₁' : (shiftFunctor C a) ⋙ F ≅ F ⋙ (shiftFunctor D a))
    (e₂ : (shiftFunctor D b) ⋙ G ≅ G ⋙ (shiftFunctor C b))
    (hc : compat_left_right adj a b h e₁ e₂) (hc' : compat_left_right adj a b h e₁' e₂) :
    e₁ = e₁' := by
  rw [← Iso.symm_eq_iff]
  ext X
  have heq := hc X _ (𝟙 _)
  apply_fun ((adj.comp (shiftEquiv' D a b h).toAdjunction).homEquiv X
    (F.obj ((shiftFunctor C a).obj X))).symm at heq
  rw [Equiv.symm_apply_apply] at heq; erw [comp_id] at heq
  have heq' := hc' X _ (𝟙 _)
  apply_fun ((adj.comp (shiftEquiv' D a b h).toAdjunction).homEquiv X
    (F.obj ((shiftFunctor C a).obj X))).symm at heq'
  rw [Equiv.symm_apply_apply] at heq'; erw [comp_id] at heq'
  rw [Iso.symm_hom, Iso.symm_hom, ← heq, ← heq']

/--
The isomorphisms `CommShift.isoZero F A` and `CommShift.isoZero F G` are compatible with any
adjunction between `F` and `G`.
-/
lemma compat_left_right_isoZero (adj : F ⊣ G) :
    CommShift.compat_left_right adj 0 0 (by simp) (CommShift.isoZero F A) (CommShift.isoZero G A) :=
    by
  intro X Y u
  simp only [comp_obj, shiftEquiv'_inverse, shiftEquiv'_functor, comp_homEquiv, Equiv.trans_apply,
    isoZero_inv_app, assoc]
  conv_lhs => erw [shiftEquiv'_zero_homEquiv C 0 0 rfl rfl X (G.obj Y)]
  conv_rhs => erw [shiftEquiv'_zero_homEquiv D 0 0 rfl rfl (F.obj X) Y]
  simp only [id_obj, shiftFunctorZero'_eq_shiftFunctorZero, assoc, Iso.inv_hom_id_app_assoc]
  conv_lhs => rw [← adj.homEquiv_naturality_right, ← adj.homEquiv_naturality_left]

/--
Suppose that we have an adjunction between functors `adj : F ⊣ G` with `F : C ⥤ D`,
that `C` and `D` have shifts by an additive group `A`, that `a, a', b, b'` are elements of `A`
such that `a + b = a' + b' = 0`, and that we are given isomorphisms
`e₁ : (shiftFunctor C a) ⋙ F ≅ F ⋙ (shiftFunctor D a)`,
`e₁' : (shiftFunctor C a') ⋙ F ≅ F ⋙ (shiftFunctor D a')`,
`e₂ : (shiftFunctor D b) ⋙ G ≅ G ⋙ (shiftFunctor C b)` and
`e₂' : (shiftFunctor D b') ⋙ G ≅ G ⋙ (shiftFunctor C b')`.

If `adj` is compatible with `e₁` and `e₂` in the sense of `compat_left_right`, and also
with `e₁'` and `e₂'` in the same sense, then it is compatible with `CommShift.isoAdd e₁ e₁'`
and `CommShift.isoAdd e₂' e₂`.
-/
lemma compat_left_right_isoAdd (adj : F ⊣ G) (a a' b b' : A) (h : a + b = 0) (h' : a' + b' = 0)
    (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₁' : shiftFunctor C a' ⋙ F ≅ F ⋙ shiftFunctor D a')
    (e₂ : shiftFunctor D b ⋙ G ≅ G ⋙ shiftFunctor C b)
    (e₂' : shiftFunctor D b' ⋙ G ≅ G ⋙ shiftFunctor C b')
    (hc : CommShift.compat_left_right adj a b h e₁ e₂)
    (hc' : CommShift.compat_left_right adj a' b' h' e₁' e₂') :
    CommShift.compat_left_right adj (a + a') (b' + b)
    (by rw [add_assoc a, ← add_assoc a', h', zero_add, h])
    (CommShift.isoAdd e₁ e₁') (CommShift.isoAdd e₂' e₂) := by
  intro X Y u
  simp [comp_homEquiv]
  conv_lhs => erw [shiftEquiv'_add_homEquiv C a a' b b' h h']
  conv_rhs => erw [shiftEquiv'_add_homEquiv D a a' b b' h h']
  simp [comp_homEquiv]
  have : u = F.map ((shiftFunctorAdd C a a').hom.app X) ≫
      (F.map ((shiftFunctorAdd C a a').inv.app X) ≫ u) := by
    rw [← assoc, ← map_comp, Iso.hom_inv_id_app, map_id, id_comp]
  conv_lhs => rw [this, adj.homEquiv_naturality_left, ← assoc, ← assoc, ← assoc, Iso.inv_hom_id_app]
              erw [id_comp]
              rw [← homEquiv_naturality_right]
  have := hc' _ _ (F.map ((shiftFunctorAdd C a a').inv.app X) ≫ u)
  simp [comp_homEquiv] at this
  conv_lhs => erw [this]
  have := hc _ _ (((shiftEquiv' D a' b' h').toAdjunction.homEquiv
    (F.obj ((shiftFunctor C a).obj X)) Y) (e₁'.inv.app ((shiftFunctor C a).obj X) ≫
    F.map ((shiftFunctorAdd C a a').inv.app X) ≫ u))
  simp [comp_homEquiv] at this
  conv_lhs => rw [this, ← adj.homEquiv_naturality_right]
  conv_rhs => rw [homEquiv_naturality_left]

end CommShift

variable (A)

/-- Suppose that we have an adjunction between functors `adj : F ⊣ G` that both commute with shifts
by `A`. Given a morphism `u : F.obj (X⟦a⟧) ⟶ Y`, there are two natural ways to construct a
morphism `X ⟶ G.obj (Y⟦-a⟧)` from `u`:
(1) Apply `Adjunction.homEquiv` for the composition of the adjunction deduced from
the equivalence `shiftEquiv' C a (-a)` and of `adj` to obtain a morphism `(F.obj X)⟦a⟧ ⟶ Y` then
compose on the right with `F.commShiftIso a`;
(2) Compose on the left with `G.commShiftIso (-a)` to obtain a morphism `X ⟶ (G.obj Y)⟦-a⟧`
then apply `Adjunction.homEquiv` for the composition of `adj` and of the adjunction deduced from
the equivalence `shiftEquiv' D a (-a)`).

We say that the adjunction `adj` is compatible with the `CommShift` structures on `F` and `G` if,
for every morphism `u : F.obj(X⟦a⟧) ⟶ Y`, these two constructions give the same result.
-/
class compatCommShift (adj : F ⊣ G) [CommShift F A] [CommShift G A] where
  left_right : ∀ (a b : A) (h : a + b = 0), CommShift.compat_left_right adj a b h
               (F.commShiftIso a) (G.commShiftIso b)

variable {A}

/--
If we have an adjunction between functors `adj : F ⊣ G` that both commute with shifts by `A`,
and if it is compatible with the `CommShift` structures, then this is the compatibility
condition in the other direction: for every morphism `v : X ⟶ G.obj (Y⟦a⟧)`, the two natural ways
to construct a morphism `F.obj (X⟦-a⟧) ⟶ Y` from `v` give the same result.
-/
lemma compatCommShift.right_left (adj : F ⊣ G) [CommShift F A] [CommShift G A]
    [adj.compatCommShift A]
    (a b : A) (h : a + b = 0) (X : C) (Y : D) (v : X ⟶ G.obj (Y⟦b⟧)) :
    (F.commShiftIso a).hom.app X ≫
    ((adj.comp (shiftEquiv' D a b h).toAdjunction).homEquiv _ _).symm v =
    (((shiftEquiv' C a b h).toAdjunction.comp adj).homEquiv _ _).symm
    (v ≫ (G.commShiftIso b).hom.app Y) :=
  CommShift.compat_right_left adj a b h (F.commShiftIso a) (G.commShiftIso b)
  (compatCommShift.left_right a b h) _ _ _

open scoped Opposite in
/--
If an adjunction `F ⊣ G` is compatible with `CommShift` structures on `F`
and `G`, then the opposite adjunction `G.op ⊣ F.op` is compatible with the opposite
`CommShift` structures with the naïve shifts on the opposite categories (given by
`CategoryTheory.Functor.CommShift.op`).
-/
def compatCommShift_op (adj : F ⊣ G) [CommShift F A] [CommShift G A] [adj.compatCommShift A] :
    compatCommShift (C := OppositeShift D A) (D := OppositeShift C A) A adj.opAdjointOpOfAdjoint :=
    by
  refine compatCommShift.mk ?_
  intro a b h Y X u
  have h' : b + a = 0 := by simp [eq_neg_of_add_eq_zero_left h]
  rw [← shiftEquiv'_toAdjunction_op C A b a h', ← shiftEquiv'_toAdjunction_op D A b a h',
  ← Adjunction.comp_op, ← Adjunction.comp_op, opAdjointOpOfAdjoint_homEquiv,
  opAdjointOpOfAdjoint_homEquiv]
  simp only [comp_obj, op_obj, shiftEquiv'_inverse, shiftEquiv'_functor]
  erw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply]
  rw [opEquiv_symm_apply, opEquiv_symm_apply]
  erw [opEquiv_apply, opEquiv_apply, opEquiv_apply, opEquiv_apply]
  simp only [Equiv.invFun_as_coe, comp_obj, Quiver.Hom.unop_op', commShiftOpIso, Iso.symm_inv,
    NatIso.op_hom, NatTrans.op_app]
  rw [← op_comp]
  conv_rhs => rw [← Quiver.Hom.op_unop u, ← op_comp, Quiver.Hom.unop_op]
  erw [compatCommShift.right_left adj b a h' X.unop Y.unop u.unop]
  rfl

/--
If an adjunction `F ⊣ G` is compatible with `CommShift` structures on `F`
and `G`, then we a have a shift-twisted adjunction right triangle.
-/
lemma compatCommShift_right_triangle (adj : F ⊣ G) [CommShift F A] [CommShift G A]
    [adj.compatCommShift A] (a : A) (Y : D) :
    adj.unit.app ((G.obj Y)⟦a⟧) ≫ G.map ((CommShift.iso a).hom.app (G.obj Y)) ≫
    (CommShift.iso a).hom.app (F.obj (G.obj Y)) ≫ (G.map (adj.counit.app Y))⟦a⟧' = 𝟙 _ := by
  apply Faithful.map_injective (F := shiftFunctor C (-a))
  simp only [id_obj, comp_obj, map_comp, map_id]
  have := compatCommShift.left_right a (-a) (by simp) (G.obj Y) _ (𝟙 _) (adj := adj)
  rw [homEquiv_apply, homEquiv_apply] at this
  simp only [comp_obj, shiftEquiv'_inverse, shiftEquiv'_functor, comp_unit_app, id_obj,
    Equivalence.toAdjunction_unit, shiftEquiv'_unit, Functor.comp_map, map_id, comp_id, assoc,
    map_shiftFunctorCompIsoId_inv_app] at this
  rw [← cancel_epi ((shiftFunctorCompIsoId C a (-a) (by simp)).hom.app (G.obj Y))] at this
  rw [← cancel_mono ((G.commShiftIso (-a)).hom.app _)] at this
  conv_lhs at this => slice 1 2; rw [Iso.hom_inv_id_app]
  conv_lhs at this => rw [id_comp]; slice 2 3; rw [Iso.inv_hom_id_app]
  erw [comp_id] at this
  rw [this]
  simp only [comp_obj, id_obj, assoc, commShiftIso_hom_naturality, Iso.inv_hom_id_app_assoc]
  slice_lhs 5 6 => rw [← map_comp, ← map_comp]; erw [Iso.inv_hom_id_app, map_id, map_id]
  rw [id_comp]
  slice_lhs 4 5 => rw [← map_comp]; erw [Iso.inv_hom_id_app, map_id]
  rw [id_comp]; erw [← (shiftFunctorCompIsoId C a (-a) (by simp)).inv.naturality]
  simp

open scoped Opposite in
/--
If an adjunction `F ⊣ G` is compatible with `CommShift` structures on `F`
and `G`, then we a have a shift-twisted adjunction left triangle.
-/
lemma compatCommShift_left_triangle (adj : F ⊣ G) [CommShift F A] [CommShift G A]
    [adj.compatCommShift A] (a : A) (X : C) :
    (F.map (adj.unit.app X))⟦a⟧' ≫ (CommShift.iso a).inv.app (G.obj (F.obj X)) ≫
    F.map ((CommShift.iso a).inv.app (F.obj X)) ≫ adj.counit.app ((F.obj X)⟦a⟧) = 𝟙 _ := by
  have := adj.compatCommShift_op (A := A)
  have := compatCommShift_right_triangle (C := OppositeShift D A) (D := OppositeShift C A)
      (opAdjointOpOfAdjoint G F adj) a (Opposite.op X)
  apply_fun Quiver.Hom.unop at this
  simp [opEquiv] at this
  rw [unop_comp, unop_comp, unop_comp, Quiver.Hom.unop_op, Quiver.Hom.unop_op] at this
  simp only [assoc] at this
  exact this

section Pullback

open Adjunction CommShift

variable {B : Type*} [AddGroup B] (φ : B →+ A)

open scoped Pullback in
/--
If an adjunction `F ⊣ G` is compatible with `CommShift` structures on `F`
and `G`, then it is also compatible with their pullbacks by a morphism of additive
groups (given by `CategoryTheory.Functor.pullbackCommShift`).
-/
def compat_pullbackCommShift (adj : F ⊣ G) [CommShift F A] [CommShift G A]
    [adj.compatCommShift A] :
    adj.compatCommShift (C := PullbackShift C φ) (D := PullbackShift D φ) B := by
  refine compatCommShift.mk ?_
  intro b b' h X Y u
  have h' : b' + b = 0 := by simp [eq_neg_of_add_eq_zero_left h]
  simp only [comp_obj, shiftEquiv'_inverse, shiftEquiv'_functor, comp_homEquiv, Equiv.trans_apply]
  conv_lhs => congr; erw [pullbackShiftEquiv'_homEquiv]
  conv_rhs => erw [pullbackShiftEquiv'_homEquiv]
  simp only [id_eq, eq_mpr_eq_cast, shiftEquiv'_inverse, shiftEquiv'_functor, assoc]
  have heq : u = F.map ((pullbackShiftIso C φ b (φ b) rfl).hom.app X) ≫
      (F.map ((pullbackShiftIso C φ b (φ b) rfl).inv.app X) ≫ u) := by
    rw [← assoc, ← map_comp, Iso.hom_inv_id_app, map_id, id_comp]
  conv_lhs => rw [heq, adj.homEquiv_naturality_left, ← assoc, ← assoc, Iso.inv_hom_id_app]
              erw [id_comp]
              change _ ≫ (Functor.commShiftIso (F := (G.pullbackShift φ)) b').inv.app Y
              rw [pullbackCommShift_iso_inv_app]
  slice_lhs 2 3 => rw [Iso.inv_hom_id_app]
  rw [← cancel_mono (G.map ((pullbackShiftIso D φ b' (φ b') rfl).hom.app Y))]
  slice_lhs 4 5 => rw [← map_comp, Iso.inv_hom_id_app]
  simp only [comp_obj, map_id, comp_id, id_comp]
  have := compatCommShift.left_right (adj := adj) (φ b) (φ b') (by rw [← φ.map_add, h, φ.map_zero])
    X Y (F.map ((pullbackShiftIso C φ b (φ b) rfl).inv.app X) ≫ u)
  simp [comp_homEquiv] at this
  rw [this]
  conv_rhs => rw [pullbackCommShift_iso_inv_app, ← assoc, ← assoc, Iso.inv_hom_id_app]
  simp only [comp_obj, id_comp, assoc]
  rw [adj.homEquiv_naturality_right]
  slice_rhs 2 3 => rw [← map_comp, Iso.inv_hom_id_app]
  simp

end Pullback

end Adjunction

end Compatibility

namespace CommShift

/-- Given an adjunction `F ⊣ G` and a `CommShift` structure on `F`, this defines commutation
isomorphisms `shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`.
-/
noncomputable def left_to_right_iso (adj : F ⊣ G) (commF : CommShift F A) (a : A) :=
  (conjugateIsoEquiv (Adjunction.comp adj (shiftEquiv D a).symm.toAdjunction)
  (Adjunction.comp (shiftEquiv C a).symm.toAdjunction adj)).toFun (commF.iso (-a))

/-- In the definition of `CommShift.left_to_right_iso`, we used `F.commShiftIso (-a)`
to define the commutation isomorphism `shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`.
This result shows that we can use instead any `F.commShiftIso a'` for `a'` such that
`a + a' = 0`.
-/
lemma left_to_right_iso_eq (adj : F ⊣ G) (commF : CommShift F A) (a a' : A) (h : a + a' = 0) :
    left_to_right_iso adj commF a =
    (conjugateIsoEquiv (Adjunction.comp adj (shiftEquiv' D a a' h).symm.toAdjunction)
    (Adjunction.comp (shiftEquiv' C a a' h).symm.toAdjunction adj)).toFun (commF.iso a') := by
  have h' : a' = -a := eq_neg_of_add_eq_zero_right h
  ext Y
  simp [left_to_right_iso]
  conv_lhs => rw [shiftEquiv'_symm_counit, shiftFunctorCompIsoId]
  conv_rhs => rw [shiftEquiv'_symm_counit, shiftFunctorCompIsoId]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, comp_obj, id_obj, map_comp]
  have := shiftFunctorAdd'_symm_eqToIso (C := D) a a' 0 a (-a) 0 h (by simp) rfl h'
  apply_fun (fun e ↦ e.hom.app) at this
  simp only [comp_obj, Iso.symm_hom, eqToIso_refl, Iso.trans_refl, Iso.trans_hom, eqToIso.hom]
    at this
  rw [this]
  simp only [NatTrans.comp_app, comp_obj, eqToHom_app, map_comp, assoc]
  rw [eqToHom_map, eqToHom_map]
  slice_rhs 4 5 => rw [eqToHom_naturality (z := fun i ↦ (shiftFunctor C a).map
    (G.map ((shiftFunctor D i).map (adj.counit.app ((shiftFunctor D a).obj Y))))) (w := h')]
  slice_rhs 3 4 => rw [eqToHom_naturality (z := fun i ↦ (shiftFunctor C a).map
    (G.map ((commF.iso i).hom.app (G.obj ((shiftFunctor D a).obj Y))))) (w := h')]
  slice_rhs 2 3 => rw [eqToHom_naturality (z := fun i ↦ (shiftFunctor C a).map (adj.unit.app
    ((shiftFunctor C i).obj (G.obj ((shiftFunctor D a).obj Y))))) (w := h')]
  conv_lhs => rw [shiftEquiv'_symm_unit, shiftFunctorCompIsoId]
  conv_rhs => rw [shiftEquiv'_symm_unit, shiftFunctorCompIsoId]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, id_obj, comp_obj, assoc,
    NatIso.cancel_natIso_inv_left]
  have := shiftFunctorAdd'_eqToIso (C := C) a' a 0 (-a) a 0 (by simp only [h', neg_add_cancel])
    (by simp) h' rfl
  apply_fun (fun e ↦ e.hom.app) at this
  simp only [comp_obj, eqToIso_refl, Iso.refl_trans, Iso.trans_hom, eqToIso.hom] at this
  rw [this]
  simp only [NatTrans.comp_app, comp_obj, eqToHom_app, assoc, eqToHom_trans_assoc, eqToHom_refl,
    id_comp]

lemma comp_left_to_right_iso_hom_app (adj : F ⊣ G) (commF : CommShift F A) (a a' : A)
    (h : a + a' = 0) (X : C) (Y : D) (u : X ⟶ G.obj (Y⟦a⟧)) :
    u ≫ (left_to_right_iso adj commF a).hom.app Y =
    ((shiftEquiv' C a a' h).symm.toAdjunction.homEquiv X (G.obj Y)) ((adj.homEquiv
    ((shiftFunctor C a').obj X) Y) ((CommShift.iso a').hom.app X ≫
    ((shiftEquiv' D a a' h).symm.toAdjunction.homEquiv (F.obj X) Y).symm
    ((adj.homEquiv X ((shiftFunctor D a).obj Y)).symm u))) := by
  rw [left_to_right_iso_eq adj commF a a' h]
  simp only [Equivalence.symm_inverse, shiftEquiv'_functor, comp_obj, Equivalence.symm_functor,
    shiftEquiv'_inverse, Equiv.toFun_as_coe, conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app,
    comp_unit_app, id_obj, Equivalence.toAdjunction_unit, Functor.comp_map, comp_counit_app,
    Equivalence.toAdjunction_counit, map_comp, assoc, homEquiv_symm_apply, homEquiv_apply]
  slice_lhs 1 2 => erw [(shiftEquiv' C a a' h).symm.unit.naturality u]
  simp only [id_obj, Equivalence.symm_functor, shiftEquiv'_inverse, Equivalence.symm_inverse,
    shiftEquiv'_functor, comp_obj, Functor.comp_map, assoc]
  slice_lhs 2 3 => rw [← Functor.map_comp]; erw [adj.unit.naturality]
  slice_rhs 3 4 => rw [← Functor.map_comp, ← Functor.map_comp]
                   erw [← (CommShift.iso a').hom.naturality u]
  simp only [assoc, Functor.map_comp]
  rfl

lemma left_to_right_iso_hom_app (adj : F ⊣ G) (commF : CommShift F A) (a a' : A)
    (h : a + a' = 0) (Y : D) :
    (left_to_right_iso adj commF a).hom.app Y =
    ((shiftEquiv' C a a' h).symm.toAdjunction.homEquiv _ (G.obj Y)) ((adj.homEquiv
    ((shiftFunctor C a').obj _) Y) ((CommShift.iso a').hom.app _ ≫
    ((shiftEquiv' D a a' h).symm.toAdjunction.homEquiv (F.obj _) Y).symm
    ((adj.homEquiv _ ((shiftFunctor D a).obj Y)).symm (𝟙 (G.obj (Y⟦a⟧)))))) := by
  conv_lhs => rw [← id_comp ((left_to_right_iso adj commF a).hom.app Y)]
  rw [comp_left_to_right_iso_hom_app _ _ a a' h]
  simp

/-- If we have an adjunction `adj : F ⊣ G` and a `CommShift F A` structure on `commF`, then,
for all `a, b` in `A` such that `a + b = 0`, the adjunction `adj` is compatible with the
isomorphisms `F.commShiftIso a` and `left_to_right_iso adj commF b`.
-/
lemma left_to_right_compat (adj : F ⊣ G) (commF : CommShift F A) (a b : A) (h : a + b = 0) :
    CommShift.compat_left_right adj a b h (F.commShiftIso a) (left_to_right_iso adj commF b) := by
  intro X Y u
  rw [← cancel_mono ((left_to_right_iso adj commF b).hom.app Y)]
  slice_lhs 2 3 => rw [Iso.inv_hom_id_app]
  conv_rhs => erw [comp_left_to_right_iso_hom_app adj commF b a
              (by simp [eq_neg_of_add_eq_zero_left h])]
  rw [comp_homEquiv, comp_homEquiv]
  simp only [comp_obj, shiftEquiv'_inverse, shiftEquiv'_functor, Equiv.trans_apply, comp_id,
  Equivalence.symm_functor, Equivalence.symm_inverse, Equiv.symm_apply_apply]
  rw [shiftEquiv'_symm_homEquiv, shiftEquiv'_symm_homEquiv, Equiv.symm_apply_apply, ← assoc]
  erw [Iso.hom_inv_id_app]
  simp

lemma left_to_right_iso_zero (adj : F ⊣ G) (commF : CommShift F A) :
    left_to_right_iso adj commF 0 = CommShift.isoZero G A := by
  apply CommShift.compat_left_right_unique_right adj 0 0 (by simp) (CommShift.isoZero F A)
  · rw [← F.commShiftIso_zero]; exact left_to_right_compat adj commF 0 0 (by simp)
  · exact CommShift.compat_left_right_isoZero adj

lemma left_to_right_iso_add (adj : F ⊣ G) (commF : CommShift F A) (a b : A) :
    left_to_right_iso adj commF (a + b) = CommShift.isoAdd (left_to_right_iso adj commF a)
    (left_to_right_iso adj commF b) := by
  have h : (-b + (-a)) + (a + b) = 0 := by rw [add_assoc, ← add_assoc (-a)]; simp
  apply CommShift.compat_left_right_unique_right adj (-b + (-a)) (a + b) h
    (F.commShiftIso (-b + (-a)))
  · exact left_to_right_compat adj commF (-b + (-a)) (a + b) h
  · rw [F.commShiftIso_add]
    exact CommShift.compat_left_right_isoAdd adj (-b) (-a) b a (by simp) (by simp) _ _ _ _
      (left_to_right_compat adj commF (-b) b (by simp))
      (left_to_right_compat adj commF (-a) a (by simp))

noncomputable def left_to_right (adj : F ⊣ G) (commF : CommShift F A) :
    CommShift G A where
  iso := left_to_right_iso adj commF
  zero := left_to_right_iso_zero adj commF
  add a b := left_to_right_iso_add adj commF a b

/-- If we have an adjunction `adj : F ⊣ G` and a `CommShift` structure on `F`, and if we put
the `CommShift` structure on `G` given by `CommShift.left_to_right`, then the adjunction
`adj` is compatible with these two `CommShift` structures.
-/
lemma left_to_right_compatCommShift (adj : F ⊣ G) (commF : CommShift F A) :
    @compatCommShift C D _ _ F G A _ _ _ adj commF (left_to_right adj commF) := by
  apply @compatCommShift.mk C D _ _ F G A _ _ _ adj commF (left_to_right adj commF)
  intro a b h X Y u
  rw [← cancel_mono (((left_to_right adj commF).iso b).hom.app Y)]
  slice_lhs 2 3 => change ((left_to_right adj commF).iso b).inv.app Y ≫ _
                   rw [Iso.inv_hom_id_app]
  conv_rhs => erw [comp_left_to_right_iso_hom_app adj commF b a
              (by simp [eq_neg_of_add_eq_zero_left h])]
  rw [comp_homEquiv, comp_homEquiv]
  simp only [comp_obj, shiftEquiv'_inverse, shiftEquiv'_functor, Equiv.trans_apply, comp_id,
  Equivalence.symm_functor, Equivalence.symm_inverse, Equiv.symm_apply_apply]
  rw [shiftEquiv'_symm_homEquiv, shiftEquiv'_symm_homEquiv, Equiv.symm_apply_apply, ← assoc]
  erw [Iso.hom_inv_id_app]
  simp

/-- Given an adjunction `F ⊣ G` and a `CommShift` structure on `G`, this defines commutation
isomorphisms `shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a`.
-/
noncomputable def right_to_left_iso (adj : F ⊣ G) (commG : CommShift G A) (a : A) :=
  (conjugateIsoEquiv (Adjunction.comp adj (shiftEquiv' D (-a) a
  (neg_add_cancel _)).symm.toAdjunction) (Adjunction.comp (shiftEquiv' C (-a) a
  (neg_add_cancel _)).symm.toAdjunction adj)).invFun (commG.iso (-a))

noncomputable def left_to_right_iso_op (adj : F ⊣ G) (commG : CommShift G A) (a : A) :
    (F ⋙ (shiftEquiv' D (-a) a (neg_add_cancel a)).symm.functor).op ≅
      ((shiftEquiv' C (-a) a (neg_add_cancel a)).symm.functor ⋙ F).op :=
    (left_to_right_iso (C := OppositeShift D A) (D := OppositeShift C A)
    adj.opAdjointOpOfAdjoint (@Opposite.commShiftOp D _ _ _ _ C _ _ G commG) a).symm

lemma right_to_left_eq_left_to_right_op (adj : F ⊣ G) (commG : CommShift G A) (a : A) :
    right_to_left_iso adj commG a = NatIso.removeOp (left_to_right_iso_op adj commG a) := by
  set G' : OppositeShift D A ⥤ OppositeShift C A := G.op
  set F' : OppositeShift C A ⥤ OppositeShift D A := F.op
  set commG' : CommShift G' A := @Opposite.commShiftOp D _ _ _ _ C _ _ G commG
  set adj' : G' ⊣ F' := adj.opAdjointOpOfAdjoint
  have := commG'
  dsimp [left_to_right_iso_op, left_to_right_iso, right_to_left_iso]
  rw [← conjugateIsoEquiv_op _ _ _ _ (adj.comp (shiftEquiv' D (-a) a (by simp)).symm.toAdjunction)
    ((shiftEquiv' C (-a) a (by simp)).symm.toAdjunction.comp adj)]
  simp only [Equivalence.symm_inverse, shiftEquiv'_functor, Equivalence.symm_functor,
    shiftEquiv'_inverse, natIsoOpEquiv, Equiv.trans_apply, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  congr 1
  rw [Adjunction.comp_op, Adjunction.comp_op]
  change _ = conjugateIsoEquiv _ _ _
  dsimp [shiftEquiv]
  rw [← shiftEquiv'_symm_toAdjunction_op, ← shiftEquiv'_symm_toAdjunction_op]
  rfl

lemma right_to_left_iso_eq (adj : F ⊣ G) (commG : CommShift G A) (a a' : A) (h : a + a' = 0) :
    right_to_left_iso adj commG a = (conjugateIsoEquiv (Adjunction.comp adj
    (shiftEquiv' D a' a (by simp [eq_neg_of_add_eq_zero_left h])).symm.toAdjunction)
    (Adjunction.comp (shiftEquiv' C a' a
    (by simp [eq_neg_of_add_eq_zero_left h])).symm.toAdjunction adj)).invFun (commG.iso a') := by
  rw [right_to_left_eq_left_to_right_op, left_to_right_iso_op, left_to_right_iso_eq _ _ a a' h]
  ext X
  simp only [Equivalence.symm_functor, shiftEquiv'_inverse, comp_obj, Equivalence.symm_inverse,
    shiftEquiv'_functor, Equiv.toFun_as_coe, NatIso.removeOp_hom, Iso.symm_hom,
    conjugateIsoEquiv_apply_inv, NatTrans.removeOp_app, op_obj, conjugateEquiv_apply_app,
    comp_unit_app, id_obj, opAdjointOpOfAdjoint_unit_app, Equivalence.toAdjunction_unit, op_map,
    Functor.comp_map, comp_counit_app, Equivalence.toAdjunction_counit,
    opAdjointOpOfAdjoint_counit_app, map_comp, assoc, Equiv.invFun_as_coe,
    conjugateIsoEquiv_symm_apply_hom, conjugateEquiv_symm_apply_app]
  rw [opEquiv_apply, opEquiv_apply, opEquiv_symm_apply, opEquiv_symm_apply,
    unop_comp, unop_comp, unop_comp, unop_comp]
  simp only [unop_id, map_id, comp_id, map_comp, op_comp, unop_comp, Quiver.Hom.unop_op, assoc,
    id_comp]
  rw [shiftEquiv'_symm_counit, shiftEquiv'_symm_unit]
  simp only [shiftFunctorCompIsoId, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, comp_obj,
    id_obj, Iso.trans_inv, Iso.symm_inv]
  rw [oppositeShiftFunctorAdd'_inv_app, oppositeShiftFunctorZero_hom_app]
  simp only [comp_obj, id_obj]
  rw [shiftEquiv'_symm_unit]
  simp only [shiftFunctorCompIsoId, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, id_obj,
    comp_obj, map_comp, assoc]
  rw [oppositeShiftFunctorAdd'_hom_app, oppositeShiftFunctorZero_inv_app]
  simp only [id_obj, comp_obj]
  have : F.map ((shiftFunctor (OppositeShift C A) a).map (adj.unit.app X).op).unop =
    F.map ((shiftFunctor C a).map (adj.unit.app X)) := rfl
  rw [this]
  congr 1
  have : F.map ((shiftFunctor (OppositeShift C A) a).map (G.map
              (((shiftFunctorAdd' D a a' 0 h).hom.app (F.obj X)).op ≫
                  ((shiftFunctorZero D A).inv.app (F.obj X)).op).unop).op).unop =
    F.map ((shiftFunctor C a).map (G.map ((shiftFunctorZero D A).inv.app (F.obj X)))) ≫
    F.map ((shiftFunctor C a).map (G.map ((shiftFunctorAdd' D a a' 0 h).hom.app (F.obj X)))) := by
    conv_lhs => rw [← op_comp, Quiver.Hom.unop_op]
                rw [map_comp, op_comp, map_comp, unop_comp]
                erw [Quiver.Hom.unop_op, Quiver.Hom.unop_op]
    simp only [id_obj, comp_obj, map_comp]
    rfl
  rw [this]
  simp only [id_obj, comp_obj, assoc]
  rfl

lemma comp_right_to_left_iso_hom_app (adj : F ⊣ G) (commG : CommShift G A) (a a' : A)
    (h : a + a' = 0) (X : C) (Y : D) (v : (F.obj X)⟦a⟧ ⟶ Y) :
    (right_to_left_iso adj commG a).hom.app X ≫ v = (adj.homEquiv _ _).symm
    (((shiftEquiv' C a' a (by simp [eq_neg_of_add_eq_zero_left h])).symm.toAdjunction.homEquiv
    _ _).symm (((adj.homEquiv X _) (((shiftEquiv' D a' a
    (by simp [eq_neg_of_add_eq_zero_left h])).symm.toAdjunction.homEquiv _ _) v)) ≫
    (commG.iso a').hom.app _)) := by
  rw [right_to_left_iso_eq _ _ a a' h]
  simp only [Equivalence.symm_functor, shiftEquiv'_inverse, comp_obj, Equivalence.symm_inverse,
    shiftEquiv'_functor, Equiv.invFun_as_coe, conjugateIsoEquiv_symm_apply_hom,
    conjugateEquiv_symm_apply_app, comp_unit_app, id_obj, Equivalence.toAdjunction_unit,
    Functor.comp_map, map_comp, comp_counit_app, Equivalence.toAdjunction_counit, assoc,
    homEquiv_apply, homEquiv_symm_apply]
  slice_lhs 5 6 => erw [← adj.counit.naturality]
  slice_lhs 4 5 => erw [← Functor.map_comp]
                   erw [← (shiftEquiv' C a' a
                     (by simp [eq_neg_of_add_eq_zero_left h])).symm.counit.naturality]
                   rw [Functor.map_comp]
  slice_lhs 3 4 => rw [← Functor.map_comp]; erw [← Functor.map_comp]
                   erw [← (commG.iso a').hom.naturality]
                   rw [Functor.map_comp, Functor.map_comp]
  simp only [assoc]
  rfl

noncomputable def right_to_left (adj : F ⊣ G) (commG : CommShift G A) :
    CommShift F A where
  iso := right_to_left_iso adj commG
  zero := by
    rw [right_to_left_eq_left_to_right_op, left_to_right_iso_op, left_to_right_iso_zero]
    ext Y
    simp only [Equivalence.symm_functor, shiftEquiv'_inverse, comp_obj, Equivalence.symm_inverse,
      shiftEquiv'_functor, NatIso.removeOp_hom, Iso.symm_hom, NatTrans.removeOp_app, op_obj,
      CommShift.isoZero_inv_app, op_map, unop_comp, Quiver.Hom.unop_op, CommShift.isoZero_hom_app]
    erw [oppositeShiftFunctorZero_inv_app, oppositeShiftFunctorZero_hom_app]
    simp
  add a b := by
    rw [right_to_left_eq_left_to_right_op, right_to_left_eq_left_to_right_op,
      right_to_left_eq_left_to_right_op, left_to_right_iso_op, left_to_right_iso_op,
      left_to_right_iso_op, left_to_right_iso_add]
    ext Y
    simp only [Equivalence.symm_functor, shiftEquiv'_inverse, comp_obj, Equivalence.symm_inverse,
      shiftEquiv'_functor, NatIso.removeOp_hom, Iso.symm_hom, NatTrans.removeOp_app, op_obj,
      CommShift.isoAdd_inv_app, op_map, unop_comp, Quiver.Hom.unop_op, assoc,
      CommShift.isoAdd_hom_app]
    have : ((left_to_right_iso (C := OppositeShift D A) (D := OppositeShift C A)
        (opAdjointOpOfAdjoint G F adj) (Functor.CommShift.op G) b).inv.app
        ((shiftFunctor (OppositeShift C A) a).obj (op Y))) = ((left_to_right_iso
        (C := OppositeShift D A) (D := OppositeShift C A) (opAdjointOpOfAdjoint G F adj)
        (Functor.CommShift.op G) b).inv.app (op (Y⟦a⟧))) := rfl
    erw [oppositeShiftFunctorAdd_inv_app, oppositeShiftFunctorAdd_hom_app]
    erw [this]
    simp only [comp_obj, Quiver.Hom.unop_op, Equivalence.symm_inverse, shiftEquiv'_functor]
    rfl

lemma right_to_left_compatCommShift (adj : F ⊣ G) (commG : CommShift G A) (a a' : A) (h : a + a' = 0)
    (X : C) (Y : D) (u : (F.obj X)⟦a'⟧ ⟶ Y) : commShift_left_right_compat adj
    (right_to_left adj commG) commG a a' h X Y u := by
  dsimp [commShift_left_right_compat, right_to_left]
  rw [comp_right_to_left_iso_hom_app adj commG a' a (by simp [eq_neg_of_add_eq_zero_left h]),
    comp_homEquiv, comp_homEquiv]
  simp only [Equivalence.symm_functor, shiftEquiv'_inverse, Equivalence.symm_inverse,
    shiftEquiv'_functor, comp_obj, map_comp, assoc, Equiv.trans_apply, unit_naturality_assoc,
    right_triangle_components, comp_id]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

noncomputable def left_right_equiv (adj : F ⊣ G) : CommShift F A ≃ CommShift G A where
  toFun := left_to_right adj
  invFun := right_to_left adj
  left_inv commF := by
    ext a X
    have := left_to_right_compat adj commF (-a) a (by simp) X ((F.obj X)⟦a⟧) (𝟙 _)
    dsimp [commShift_left_right_compat] at this; erw [comp_id] at this
    rw [← Equiv.eq_symm_apply] at this
    rw [this]
    have := right_to_left_compat adj (left_to_right adj commF) (-a) a (by simp) X
      ((F.obj X)⟦a⟧) (𝟙 _)
    dsimp [commShift_left_right_compat] at this; erw [comp_id] at this
    rw [← Equiv.eq_symm_apply] at this
    exact this
  right_inv commG := by
    ext a Y
    set u := ((adj.comp (shiftEquiv' D a (-a) (by simp)).symm.toAdjunction).homEquiv _ _).symm
      (𝟙 (G.obj (Y⟦a⟧)))
    have := right_to_left_compat adj commG a (-a) (by simp) (G.obj (Y⟦a⟧)) Y u
    dsimp [commShift_left_right_compat, u] at this; erw [Equiv.apply_symm_apply] at this
    rw [id_comp] at this
    rw [← this]
    have := left_to_right_compat adj (right_to_left adj commG) a (-a) (by simp) (G.obj (Y⟦a⟧)) Y u
    dsimp [commShift_left_right_compat, u] at this; erw [Equiv.apply_symm_apply] at this
    rw [id_comp] at this
    exact this.symm

-- compatibility of this equiv
noncomputable def left_right_equiv_compat_forward (adj : F ⊣ G) [CommShift F A] :
    @compatCommShift C D _ _ F G A _ _ _ adj inferInstance
    ((left_right_equiv adj).toFun inferInstance) := by
  apply @compatCommShift.mk C D _ _ F G A _ _ _ adj _ ((left_right_equiv adj).toFun inferInstance)
  intro a a' h X Y u
  exact left_to_right_compat adj inferInstance a a' h X Y u

def left_right_equiv_compat_backward (adj : F ⊣ G) [CommShift G A] :
    @compatCommShift C D _ _ F G A _ _ _ adj ((left_right_equiv adj).invFun inferInstance)
    inferInstance := by
  apply @compatCommShift.mk C D _ _ F G A _ _ _ adj
    ((left_right_equiv adj).invFun inferInstance) _
  intro a a' h X Y u
  exact right_to_left_compat adj inferInstance a a' h X Y u

end Adjunction

end CategoryTheory

#min_imports
