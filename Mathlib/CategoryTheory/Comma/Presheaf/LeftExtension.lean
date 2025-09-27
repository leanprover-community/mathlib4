/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Limits.Types.Shapes

/-!

# Left Kan Extension of Presheaf on Costructured Arrow

Let `F : C ⥤ D` be a functor and `d : D`. Recall that the category `CostructuredArrow F d` is the
category of objects `c` in `C` equipped with a morphism `F.obj c ⟶ d`.

In this file we show that any functor `P : (CostructuredArrow F d)ᵒᵖ ⥤ Type u` has a left Kan
extension along the projection `CostructuredArrow F d ⥤ C` to form a functor `P' : Cᵒᵖ ⥤ Type u`.

In other words, any presheaf on `CostructuredArrow F d` can be extended to a presheaf on `C`.

Explicitly, `P'.obj (op c)` is defined to be `(u : F.obj c ⟶ d) × P.obj (op (mk u))`. In other
words, we just take all possible morphisms `u : F.obj c ⟶ d` and take the disjoint union of the
original functor `P` evaluated on those morphisms.
-/

universe u

open CategoryTheory Opposite Limits Category

namespace CategoryTheory.CostructuredArrow

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D] (F : C ⥤ D) (d : D)
  (P : (CostructuredArrow F d)ᵒᵖ ⥤ Type u)
  (d₁ d₂ d₃ : D) {c c₁ c₂ c₃ : C} (c' c₁' c₂' c₃' : Cᵒᵖ)
  (u : F.obj c ⟶ d)

variable {F d} (c)

/-- The small diagram used for defining the pointwise extension of the presheaf `P`.

For any morphism `u : F.obj c ⟶ d`, the functor `P` assigns a set (i.e. type) to `u`. This function
is the function that takes `u` to the corresponding type defined `P`. -/
abbrev fiberFun : (F.obj c ⟶ d) → Type u :=
  fun u ↦ P.obj (op (mk u))

/-- The cofan that is the disjoint union (i.e. coproduct) of the values taken by `P` on the
distinct structural morphisms `u : F.obj c ⟶ d`. -/
abbrev fiberCofan : Cofan (fiberFun P c) :=
  (Types.coproductColimitCocone (fiberFun P c)).cocone

@[simp] lemma fiberCofan_inj_fst (y : fiberFun P c u) :
    ((fiberCofan P c).inj u y).fst = u :=
  rfl

@[simp] lemma fiberCofan_inj_snd (y : fiberFun P c u) :
    ((fiberCofan P c).inj u y).snd = y :=
  rfl

/-- The disjoint union (i.e. coproduct) of the values taken by `P` on the distinct structural
morphisms `u : F.obj c ⟶ d`. -/
abbrev FiberObj : Type u :=
  (fiberCofan P c).pt

@[simp] lemma homMk_id {u : F.obj c ⟶ d} (w) :
    homMk (𝟙 c) w = 𝟙 (mk u) :=
  rfl

@[simp] lemma homMk_comp_homMk {u : F.obj c₁ ⟶ d} {v : F.obj c₂ ⟶ d} {w : F.obj c₃ ⟶ d}
    (φ : c₁ ⟶ c₂) (ψ : c₂ ⟶ c₃)
    (w₁ : F.map φ ≫ v = u) (w₂ : F.map ψ ≫ w = v) :
    (homMk φ w₁ : mk u ⟶ mk v) ≫ (homMk ψ w₂ : mk v ⟶ mk w) =
      homMk (φ ≫ ψ) (by rw [F.map_comp, assoc, mk_hom_eq_self, mk_hom_eq_self, w₂, w₁]) :=
  rfl

lemma hom_eta {R S : CostructuredArrow F d} (f : R ⟶ S) :
    homMk f.left (w f) = f :=
  rfl

lemma hom_eta' {R S : (CostructuredArrow F d)ᵒᵖ} (f : R ⟶ S) :
    (homMk f.unop.left (w f.unop)).op = f :=
  rfl

variable {P c}

/-- A better extensionality lemma than the built-in `Sigma.ext` to avoid having to talk about
heterogeneous equality. -/
@[ext (iff := false)] lemma FiberObj.ext {j j' : FiberObj P c}
    (h₁ : j.fst = j'.fst)
    (h₂ : P.map (homMk (eqToHom (show (mk j'.fst).left = (mk j.fst).left from rfl)) <| by
        rw [eqToHom_refl, F.map_id, id_comp, h₁]).op j.snd = j'.snd) :
    j = j' := by
  cases j; cases j'; generalize_proofs at h₂; subst h₁
  obtain rfl := by simpa using h₂
  rfl

variable (F d) in
/-- An intermediate category used for proving the Kan criterion.

An object of this category is given by `b : C` and two morphisms that fill in the diagram
`F.obj c ⟶ F.obj b ⟶ d`, where `c : C` and `d : D` are fixed.

Note that we need to take the opposite category so that `c ⟶ b` is in the correct direction.

This category can be partitioned into disjoint parts based on the "structural morphism"
`F.obj c ⟶ d` obtained (this is `Between.toHom`). This fact is witnessed by `Between.toHom_congr`
saying that the existence of any morphism at all between two objects forces the structural
morphisms to be equal, and also by `Between.sec` which provides an explicit representative in the
`Between` category given a structural morphism `F.obj c ⟶ d`. -/
abbrev Between : Type (u + 1) :=
  CostructuredArrow (proj F d).op c'

variable {c'} (b : Between F d c') {b₁ b₂ b₃ : Between F d c'}

/-- The projection that sends `F.obj c ⟶ F.obj b ⟶ d` to the arrow `F.obj b ⟶ d`. -/
abbrev Between.fst : CostructuredArrow F d :=
  b.left.unop

variable (F d c') in
/-- The projection `Between.fst` as a functor. This is the functor that is used in the criterion
of the existence of a Kan extension. -/
@[simps!] abbrev Between.proj : Between F d c' ⥤ (CostructuredArrow F d)ᵒᵖ :=
  CostructuredArrow.proj (CostructuredArrow.proj F d).op c'

/-- The projection that sends `F.obj c ⟶ F.obj b ⟶ d` to the arrow `c ⟶ b`. -/
abbrev Between.snd : c'.unop ⟶ b.fst.left :=
  b.hom.unop

/-- The structural morphism `F.obj c ⟶ d` determined by `b`. -/
abbrev Between.toHom : F.obj c'.unop ⟶ d :=
  F.map b.snd ≫ b.fst.hom

lemma Between.w (f : b₁ ⟶ b₂) :
    b₂.snd ≫ f.left.unop.left = b₁.snd :=
  congr($(CostructuredArrow.w f).unop)

lemma Between.w' (f : b₁ ⟶ b₂) :
    F.map f.left.unop.left ≫ b₁.fst.hom = b₂.fst.hom :=
  CostructuredArrow.w f.left.unop

/-- The witness that the `Between` category partitions into disjoint parts based on the structural
morphism `F.obj c ⟶ d` (formed by `Between.toHom`).

The existence of any morphism at all between two `Between` objects forces their `toHom` values to
be equal. -/
lemma Between.toHom_congr (f : b₁ ⟶ b₂) :
    b₁.toHom = b₂.toHom := by
  rw [toHom, ← w f, F.map_comp, assoc, w' f]

/-- A custom constructor for `Between` objects given `g : c ⟶ b` and `f : F.obj b ⟶ d`. -/
def Between.mk (f : F.obj c ⟶ d) (g : c'.unop ⟶ c) : Between F d c' :=
  CostructuredArrow.mk (Y := op (CostructuredArrow.mk f)) g.op

/-- An explicit representative of the disjoint partition given the structural morphism
`u : F.obj c ⟶ d`. -/
def Between.sec (u : F.obj c'.unop ⟶ d) : Between F d c' :=
  mk u (𝟙 c'.unop)

@[simp] lemma Between.sec_snd (u : F.obj c'.unop ⟶ d) : (sec u).snd = 𝟙 c'.unop := rfl

@[simp] lemma Between.toHom_mk (f : F.obj c ⟶ d) (g : c'.unop ⟶ c) :
    (mk f g).toHom = F.map g ≫ f := rfl

@[simp] lemma Between.toHom_sec (u : F.obj c'.unop ⟶ d) :
    (sec u).toHom = u := by
  simp [sec]

/-- The representative `sec` is terminal in its subcategory.

More rigorously, for any `b : Between`, the type of morphisms `b ⟶ sec b.toHom` is a subsingleton,
i.e. it is either empty or has a unique element. -/
def Between.homSec : b ⟶ sec b.toHom :=
  homMk (homMk b.snd).op (comp_id _)

instance (u : F.obj c'.unop ⟶ d) : Subsingleton (b ⟶ Between.sec u) where
  allEq f g := hom_ext _ _ <| unop_injective <| hom_ext _ _ <| by
    simpa using (Between.w f).trans (Between.w g).symm

variable (P c')

/-- The cocone that is used in the criterion of the existence of a left Kan extension of `P`
to a sheaf `Cᵒᵖ ⥤ Type u`. -/
@[simps!] def kanCocone : Cocone (Between.proj F d c' ⋙ P) where
  pt := FiberObj P c'.unop
  ι :=
  { app b y := (fiberCofan P c'.unop).inj b.toHom (P.map (homMk b.snd).op y)
    naturality b₁ b₂ f := funext fun y ↦ by
      refine FiberObj.ext ?_ ?_
      · simp [Between.toHom_congr f]
      · change P.map _ (P.map _ (P.map f.left _)) = P.map _ _
        rw [← hom_eta' f.left]
        simp_rw [← FunctorToTypes.map_comp_apply, ← op_comp, homMk_comp_homMk]
        congr! 3
        rw [eqToHom_refl, Between.w f]
        exact id_comp _ }

lemma kanCocone_ι_app (y : (Between.proj F d c' ⋙ P).obj b) :
    (kanCocone P c').ι.app b y = (fiberCofan P c'.unop).inj b.toHom (P.map (homMk b.snd).op y) :=
  rfl

/-- The cocone that is used in the criterion of the existence of a left Kan extension of `P`
to a sheaf `Cᵒᵖ ⥤ Type u` is a colimit. -/
def kanCoconeIsColimit : IsColimit (kanCocone P c') where
  desc c j := c.ι.app (.sec j.fst) j.snd
  fac c b := c.ι.naturality b.homSec
  uniq c f w := funext fun ⟨j₁, j₂⟩ ↦ by
    rw [← w, types_comp_apply]
    congr! 1
    exact FiberObj.ext (by simp) rfl

instance : (proj F d).op.HasPointwiseLeftKanExtension P :=
  fun c' ↦ ⟨⟨⟨_, kanCoconeIsColimit P c'⟩⟩⟩

noncomputable example := (proj F d).op.pointwiseLeftKanExtension P

end CategoryTheory.CostructuredArrow
