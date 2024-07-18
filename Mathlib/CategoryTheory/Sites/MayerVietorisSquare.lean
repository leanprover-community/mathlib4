/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!
# Mayer-Vietoris squares

The purpose of this file is to allow the formalization of long exact
Mayer-Vietoris sequences in sheaf cohomology. If `X` is an open subset
of a topological space that is covered by two open subsets `U` and `V`,
it is known that this is a long exact sequence
`... ⟶ H^q(X) ⟶ H^q(U) ⊞ H^q(V) ⟶ H^q(W) ⟶ H^{q+1}(X) ⟶ ...`
when `W` is the intersection of `U` and `V`, and `H^q` are the
cohomology groups with values in an abelian sheaf.

In this file, we introduce a structure
`GrothendieckTopology.MayerVietorisSquare` which contains the data
of a commutative square in a category `C` equipped with a Grothendieck
topology `J`, which share some properties with the square formed by
the open subsets `W`, `U`, `V`, `X` in the example above.
In particular, we require that the square become a pushout square
when it is understood as a square in the category of sheaves of sets.
We also require that `U ⟶ X` is a monomorphism. The morphism `V ⟶ X`
does not have to be a monomorphism, which shall allow the example
of Nisnevich distinguished squares in the case of the Nisnevich
topology on schemes (in which case `i : U ⟶ X` shall be an open
immersion and `j : V ⟶ X` an étale map that is an
isomorphism over the closed (reduced) subscheme `X - U`,
and `W` is the fibre product of `i` and `j`.).

## References
* https://stacks.math.columbia.edu/tag/08GL

-/
universe v u

namespace CategoryTheory

open Limits Opposite

section

variable {C : Type u} [Category.{v} C]

lemma IsPushout.of_iso {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : C}
    {f : X₁ ⟶ X₂} {g : X₁ ⟶ X₃} {h : X₂ ⟶ X₄} {i : X₃ ⟶ X₄} (H : IsPushout f g h i)
    {f' : Y₁ ⟶ Y₂} {g' : Y₁ ⟶ Y₃} {h' : Y₂ ⟶ Y₄} {i' : Y₃ ⟶ Y₄}
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (e₃ : X₃ ≅ Y₃) (e₄ : X₄ ≅ Y₄)
    (commf : f ≫ e₂.hom = e₁.hom ≫ f') (commg : g ≫ e₃.hom = e₁.hom ≫ g')
    (commh : h ≫ e₄.hom = e₂.hom ≫ h') (commi : i ≫ e₄.hom = e₃.hom ≫ i') :
   IsPushout f' g' h' i' := sorry

end

namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C]
  (J : GrothendieckTopology C)
  [HasWeakSheafify J (Type v)] [HasWeakSheafify J AddCommGrp.{v}]

/-- A Mayer-Vietoris square in a category `C` equipped with a Grothendieck
topology consists of a commutative square `p ≫ i = q ≫ j` in `C`
such that `i` is a monomorphism and that the square becomes a
pushout square in the category of sheaves of sets. -/
structure MayerVietorisSquare where
  /-- the object that is covered -/
  X : C
  /-- the first object of the covering -/
  U : C
  /-- the second object of the covering -/
  V : C
  /-- the top-left corner of the square -/
  W : C
  /-- the inclusion of `U` in `X` -/
  i : U ⟶ X
  /-- the morphism from `V` to `X` -/
  j : V ⟶ X
  /-- the morphism from `W` to `U` -/
  p : W ⟶ U
  /-- the inclusion from `W` to `V` -/
  q : W ⟶ V
  fac : p ≫ i = q ≫ j
  hi : Mono i := by infer_instance
  /-- the square becomes a pushout square in the category of sheaves of types -/
  isColimit :
    letI F := yoneda ⋙ presheafToSheaf J _
    IsColimit (PushoutCocone.mk
      (f := F.map p) (g := F.map q) (F.map i) (F.map j) (by
        simp only [← Functor.map_comp, fac]))

variable {J}

namespace MayerVietorisSquare

variable (S : J.MayerVietorisSquare)

lemma isPushout :
    letI F := yoneda ⋙ presheafToSheaf J _
    IsPushout (F.map S.p) (F.map S.q) (F.map S.i) (F.map S.j) where
  w := by simp only [← Functor.map_comp, S.fac]
  isColimit' := ⟨S.isColimit⟩

section

variable (F : Sheaf J (Type v))

lemma ext {x y : F.val.obj (op S.X)} (h₁ : F.val.map S.i.op x = F.val.map S.i.op y)
    (h₂ : F.val.map S.j.op x = F.val.map S.j.op y) : x = y := by
  apply yonedaEquiv.symm.injective
  apply ((sheafificationAdjunction _ _).homEquiv _ _).symm.injective
  apply PushoutCocone.IsColimit.hom_ext S.isColimit
  · erw [← Adjunction.homEquiv_naturality_left_symm,
      ← Adjunction.homEquiv_naturality_left_symm,
      ← yonedaEquiv_symm_map S.i.op, ← yonedaEquiv_symm_map S.i.op]
    dsimp
    rw [h₁]
  · erw [← Adjunction.homEquiv_naturality_left_symm,
      ← Adjunction.homEquiv_naturality_left_symm,
      ← yonedaEquiv_symm_map S.j.op, ← yonedaEquiv_symm_map S.j.op]
    dsimp
    rw [h₂]

variable (u : F.val.obj (op S.U)) (v : F.val.obj (op S.V))
  (h : F.val.map S.p.op u = F.val.map S.q.op v)

namespace glue

/-- Auxiliary definition for `MayerVietorisSquare.glue`. -/
noncomputable def hom : (presheafToSheaf J _).obj (yoneda.obj S.X) ⟶ F :=
  PushoutCocone.IsColimit.desc S.isColimit
      (((sheafificationAdjunction _ _).homEquiv _ _).symm (yonedaEquiv.symm u))
      (((sheafificationAdjunction _ _).homEquiv _ _).symm (yonedaEquiv.symm v)) (by
        dsimp
        erw [← Adjunction.homEquiv_naturality_left_symm,
          ← Adjunction.homEquiv_naturality_left_symm]
        congr 1
        apply yonedaEquiv.injective
        simpa [yonedaEquiv] using h)

@[reassoc (attr := simp)]
lemma map_i_op_hom :
    (presheafToSheaf J _).map (yoneda.map S.i) ≫ glue.hom S F u v h =
      ((sheafificationAdjunction J _).homEquiv _ F).symm (yonedaEquiv.symm u) :=
  PushoutCocone.IsColimit.inl_desc S.isColimit _ _ _

@[reassoc (attr := simp)]
lemma map_j_op_hom :
    (presheafToSheaf J _).map (yoneda.map S.j) ≫ glue.hom S F u v h =
      ((sheafificationAdjunction J _).homEquiv _ F).symm (yonedaEquiv.symm v) :=
  PushoutCocone.IsColimit.inr_desc S.isColimit _ _ _

end glue

/-- If `S` is a Mayer-Vietoris square, a section of a sheaf
on `S.X` can be constructed by gluing sections over `S.U` and `S.V`
which coincide on `S.W`. -/
noncomputable def glue : F.val.obj (op S.X) :=
  yonedaEquiv ((sheafificationAdjunction _ _).homEquiv _ _
    (glue.hom S F u v h))

lemma map_i_op_glue : F.val.map S.i.op (S.glue F u v h) = u := by
  apply yonedaEquiv.symm.injective
  have eq := congr_arg ((sheafificationAdjunction J _).homEquiv _ _)
    (glue.map_i_op_hom S F u v h)
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_left] at eq
  simpa only [glue, yonedaEquiv_naturality, Equiv.symm_apply_apply] using eq

lemma map_j_op_glue : F.val.map S.j.op (S.glue F u v h) = v := by
  apply yonedaEquiv.symm.injective
  have eq := congr_arg ((sheafificationAdjunction J _).homEquiv _ _)
    (glue.map_j_op_hom S F u v h)
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_left] at eq
  simpa only [glue, yonedaEquiv_naturality, Equiv.symm_apply_apply] using eq

end

lemma isPushoutAddCommGrpFreeSheaf :
    letI F := yoneda ⋙ (whiskeringRight _ _ _).obj AddCommGrp.free ⋙
      presheafToSheaf J _
    IsPushout (F.map S.p) (F.map S.q) (F.map S.i) (F.map S.j) := by
  have e := presheafToSheafCompComposeAndSheafifyIso J AddCommGrp.free
  exact (S.isPushout.map (Sheaf.composeAndSheafify J AddCommGrp.free)).of_iso
    (e.app _) (e.app _) (e.app _) (e.app _) (e.hom.naturality _)
      (e.hom.naturality _) (e.hom.naturality _) (e.hom.naturality _)

-- TODO: deduce a short exact sequence in the category of abelian sheaves

end MayerVietorisSquare

end GrothendieckTopology

end CategoryTheory
