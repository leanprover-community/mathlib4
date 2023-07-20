/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw
-/
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.CategoryTheory.Triangulated.TriangleShift
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Homology.ShortComplex.Basic

#align_import category_theory.triangulated.pretriangulated from "leanprover-community/mathlib"@"6876fa15e3158ff3e4a4e2af1fb6e1945c6e8803"

/-!
# Pretriangulated Categories

This file contains the definition of pretriangulated categories and triangulated functors
between them.

## Implementation Notes

We work under the assumption that pretriangulated categories are preadditive categories,
but not necessarily additive categories, as is assumed in some sources.

TODO: generalise this to n-angulated categories as in https://arxiv.org/abs/1006.4592
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Preadditive

open CategoryTheory.Limits

universe v v₀ v₁ v₂ u u₀ u₁ u₂

namespace CategoryTheory

namespace Limits

-- should be moved to a better place
namespace BinaryBiproductData

variable {C : Type _} [Category C]
    {X₁ X₂ : C} [HasZeroMorphisms C] [HasBinaryBiproduct X₁ X₂] (d : BinaryBiproductData X₁ X₂)

def isoBiprod {C : Type _} [Category C]
    {X₁ X₂ : C} [HasZeroMorphisms C] [HasBinaryBiproduct X₁ X₂] (d : BinaryBiproductData X₁ X₂) :
    X₁ ⊞ X₂ ≅ d.bicone.pt :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit X₁ X₂) d.isBilimit.isLimit

@[reassoc (attr := simp)]
lemma isoBiprod_inv_fst : d.isoBiprod.inv ≫ biprod.fst = d.bicone.fst :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ d.isBilimit.isLimit ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
lemma isoBiprod_inv_snd : d.isoBiprod.inv ≫ biprod.snd = d.bicone.snd :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ d.isBilimit.isLimit ⟨WalkingPair.right⟩

@[reassoc (attr := simp)]
lemma isoBiprod_hom_fst : d.isoBiprod.hom ≫ d.bicone.fst = biprod.fst := by
  rw [← isoBiprod_inv_fst, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
lemma isoBiprod_hom_snd : d.isoBiprod.hom ≫ d.bicone.snd = biprod.snd := by
  rw [← isoBiprod_inv_snd, Iso.hom_inv_id_assoc]

end BinaryBiproductData

end Limits

lemma isIso_of_yoneda_map_bijective {C : Type _} [Category C] {X Y : C} (f : X ⟶ Y)
  (hf : ∀ (T : C), Function.Bijective (fun (x : T ⟶ X) => x ≫ f)):
    IsIso f := by
  obtain ⟨g, hg : g ≫ f = 𝟙 Y⟩ := (hf Y).2 (𝟙 Y)
  exact ⟨g, (hf _).1 (by aesop_cat), hg⟩

end CategoryTheory

namespace CategoryTheory

open Category Pretriangulated ZeroObject

/-
We work in a preadditive category `C` equipped with an additive shift.
-/
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]

/-- A preadditive category `C` with an additive shift, and a class of "distinguished triangles"
relative to that shift is called pretriangulated if the following hold:
* Any triangle that is isomorphic to a distinguished triangle is also distinguished.
* Any triangle of the form `(X,X,0,id,0,0)` is distinguished.
* For any morphism `f : X ⟶ Y` there exists a distinguished triangle of the form `(X,Y,Z,f,g,h)`.
* The triangle `(X,Y,Z,f,g,h)` is distinguished if and only if `(Y,Z,X⟦1⟧,g,h,-f⟦1⟧)` is.
* Given a diagram:
  ```
        f       g       h
    X  ───> Y  ───> Z  ───> X⟦1⟧
    │       │                │
    │a      │b               │a⟦1⟧'
    V       V                V
    X' ───> Y' ───> Z' ───> X'⟦1⟧
        f'      g'      h'
  ```
  where the left square commutes, and whose rows are distinguished triangles,
  there exists a morphism `c : Z ⟶ Z'` such that `(a,b,c)` is a triangle morphism.

See <https://stacks.math.columbia.edu/tag/0145>
-/
class Pretriangulated [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] where
  /-- a class of triangle which are called `distinguished` -/
  distinguishedTriangles : Set (Triangle C)
  /-- a triangle that is isomorphic to a distinguished triangle is distinguished -/
  isomorphic_distinguished :
    ∀ T₁ ∈ distinguishedTriangles, ∀ (T₂) (_ : T₂ ≅ T₁), T₂ ∈ distinguishedTriangles
  /-- obvious triangles `X ⟶ X ⟶ 0 ⟶ X⟦1⟧` are distinguished -/
  contractible_distinguished : ∀ X : C, contractibleTriangle X ∈ distinguishedTriangles
  /-- any morphism `X ⟶ Y` is part of a distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` -/
  distinguished_cocone_triangle :
    ∀ {X Y : C} (f : X ⟶ Y),
      ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distinguishedTriangles
  /-- a triangle is distinguished iff it is so after rotating it -/
  rotate_distinguished_triangle :
    ∀ T : Triangle C, T ∈ distinguishedTriangles ↔ T.rotate ∈ distinguishedTriangles
  /-- given two distinguished triangle, a commutative square
        can be extended as morphism of triangles -/
  complete_distinguished_triangle_morphism :
    ∀ (T₁ T₂ : Triangle C) (_ : T₁ ∈ distinguishedTriangles) (_ : T₂ ∈ distinguishedTriangles)
      (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (_ : T₁.mor₁ ≫ b = a ≫ T₂.mor₁),
      ∃ c : T₁.obj₃ ⟶ T₂.obj₃, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃
#align category_theory.pretriangulated CategoryTheory.Pretriangulated


namespace Pretriangulated

variable [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [hC : Pretriangulated C]

-- porting note: increased the priority so that we can write `T ∈ distTriang C`, and
-- not just `T ∈ (distTriang C)`
/-- distinguished triangles in a pretriangulated category -/
notation:60 "distTriang " C => @distinguishedTriangles C _ _ _ _ _ _

variable {C}

lemma distinguished_iff_of_iso {T₁ T₂ : Triangle C} (e : T₁ ≅ T₂) :
    (T₁ ∈ distTriang C) ↔ T₂ ∈ distTriang C :=
  ⟨fun hT₁ => isomorphic_distinguished _ hT₁ _ e.symm,
    fun hT₂ => isomorphic_distinguished _ hT₂ _ e⟩

/-- Given any distinguished triangle `T`, then we know `T.rotate` is also distinguished.
-/
theorem rot_of_dist_triangle (T : Triangle C) (H : T ∈ distTriang C) : T.rotate ∈ distTriang C :=
  (rotate_distinguished_triangle T).mp H
#align category_theory.pretriangulated.rot_of_dist_triangle CategoryTheory.Pretriangulated.rot_of_dist_triangle

/-- Given any distinguished triangle `T`, then we know `T.inv_rotate` is also distinguished.
-/
theorem inv_rot_of_dist_triangle (T : Triangle C) (H : T ∈ distTriang C) :
    T.invRotate ∈ distTriang C :=
  (rotate_distinguished_triangle T.invRotate).mpr
    (isomorphic_distinguished T H T.invRotate.rotate (invRotCompRot.app T))
#align category_theory.pretriangulated.inv_rot_of_dist_triangle CategoryTheory.Pretriangulated.inv_rot_of_dist_triangle

/-- Given any distinguished triangle
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
the composition `f ≫ g = 0`.
See <https://stacks.math.columbia.edu/tag/0146>
-/
@[reassoc]
theorem comp_dist_triangle_mor_zero₁₂ (T) (H : T ∈ (distTriang C)) : T.mor₁ ≫ T.mor₂ = 0 := by
  obtain ⟨c, hc⟩ :=
    complete_distinguished_triangle_morphism _ _ (contractible_distinguished T.obj₁) H (𝟙 T.obj₁)
      T.mor₁ rfl
  simpa only [contractibleTriangle_mor₂, zero_comp] using hc.left.symm
#align category_theory.pretriangulated.comp_dist_triangle_mor_zero₁₂ CategoryTheory.Pretriangulated.comp_dist_triangle_mor_zero₁₂

@[simps]
def shortComplexOfDistTriangle (T : Triangle C) (hT : T ∈ distTriang C) : ShortComplex C :=
  ShortComplex.mk T.mor₁ T.mor₂ (comp_dist_triangle_mor_zero₁₂ _ hT)

@[simps!]
def shortComplexOfDistTriangleIsoOfIso {T T' : Triangle C} (e : T ≅ T') (hT : T ∈ distTriang C) :
  shortComplexOfDistTriangle T hT ≅ shortComplexOfDistTriangle T'
    (isomorphic_distinguished _ hT _ e.symm) :=
  ShortComplex.isoMk (Triangle.π₁.mapIso e) (Triangle.π₂.mapIso e) (Triangle.π₃.mapIso e)
    (by aesop_cat) (by aesop_cat)

/-- Given any distinguished triangle
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
the composition `g ≫ h = 0`.
See <https://stacks.math.columbia.edu/tag/0146>
-/
@[reassoc]
theorem comp_dist_triangle_mor_zero₂₃ (T : Triangle C) (H : T ∈ distTriang C) :
  T.mor₂ ≫ T.mor₃ = 0 :=
  comp_dist_triangle_mor_zero₁₂ T.rotate (rot_of_dist_triangle T H)
#align category_theory.pretriangulated.comp_dist_triangle_mor_zero₂₃ CategoryTheory.Pretriangulated.comp_dist_triangle_mor_zero₂₃

/-- Given any distinguished triangle
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
the composition `h ≫ f⟦1⟧ = 0`.
See <https://stacks.math.columbia.edu/tag/0146>
-/
@[reassoc]
theorem comp_dist_triangle_mor_zero₃₁ (T : Triangle C) (H : T ∈ distTriang C) :
    T.mor₃ ≫ T.mor₁⟦1⟧' = 0 := by
  have H₂ := rot_of_dist_triangle T.rotate (rot_of_dist_triangle T H)
  simpa using comp_dist_triangle_mor_zero₁₂ T.rotate.rotate H₂
#align category_theory.pretriangulated.comp_dist_triangle_mor_zero₃₁ CategoryTheory.Pretriangulated.comp_dist_triangle_mor_zero₃₁

lemma distinguished_cocone_triangle₁ {Y Z : C} (g : Y ⟶ Z) :
  ∃ (X : C) (f : X ⟶ Y) (h : Z ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang C := by
  obtain ⟨X', f', g', mem⟩ := distinguished_cocone_triangle g
  exact ⟨_, _, _, inv_rot_of_dist_triangle _ mem⟩

lemma distinguished_cocone_triangle₂ {Z X : C} (h : Z ⟶ X⟦(1 : ℤ)⟧) :
    ∃ (Y : C) (f : X ⟶ Y) (g : Y ⟶ Z), Triangle.mk f g h ∈ distTriang C := by
  obtain ⟨Y', f', g', mem⟩ := distinguished_cocone_triangle h
  let T' := (Triangle.mk h f' g').invRotate.invRotate
  let T'' := Triangle.mk (((shiftEquiv C (1 : ℤ)).unitIso.app X).hom ≫ T'.mor₁) T'.mor₂
    (T'.mor₃ ≫ ((shiftEquiv C (1 : ℤ)).counitIso.app (X⟦(1 : ℤ)⟧)).hom)
  refine' ⟨T''.obj₂, T''.mor₁, T''.mor₂, isomorphic_distinguished _
    (inv_rot_of_dist_triangle _ (inv_rot_of_dist_triangle _ mem)) _ _⟩
  exact Triangle.isoMk _ _ ((shiftEquiv C (1 : ℤ)).unitIso.app X) (Iso.refl _) (Iso.refl _)
    (by aesop_cat) (by aesop_cat)
    (by dsimp ; simp only [shift_shiftFunctorCompIsoId_inv_app, id_comp])

lemma complete_distinguished_triangle_morphism₁ (T₁ T₂ : Triangle C)
    (hT₁ : T₁ ∈ distTriang C) (hT₂ : T₂ ∈ distTriang C) (b : T₁.obj₂ ⟶ T₂.obj₂)
    (c : T₁.obj₃ ⟶ T₂.obj₃) (comm : T₁.mor₂ ≫ c = b ≫ T₂.mor₂) :
    ∃ (a : T₁.obj₁ ⟶ T₂.obj₁), T₁.mor₁ ≫ b = a ≫ T₂.mor₁ ∧
      T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨a, ⟨ha₁, ha₂⟩⟩ := complete_distinguished_triangle_morphism _ _
    (rot_of_dist_triangle _ hT₁) (rot_of_dist_triangle _ hT₂) b c comm
  refine' ⟨(shiftFunctor C (1 : ℤ)).preimage a, ⟨_, _⟩⟩
  . apply (shiftFunctor C (1 : ℤ)).map_injective
    dsimp at ha₂
    rw [neg_comp, comp_neg, neg_inj] at ha₂
    simpa only [Functor.map_comp, Functor.image_preimage] using ha₂
  . simpa only [Functor.image_preimage] using ha₁

lemma complete_distinguished_triangle_morphism₂ (T₁ T₂ : Triangle C)
    (hT₁ : T₁ ∈ distTriang C) (hT₂ : T₂ ∈ distTriang C) (a : T₁.obj₁ ⟶ T₂.obj₁)
    (c : T₁.obj₃ ⟶ T₂.obj₃) (comm : T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃) :
    ∃ (b : T₁.obj₂ ⟶ T₂.obj₂), T₁.mor₁ ≫ b = a ≫ T₂.mor₁ ∧ T₁.mor₂ ≫ c = b ≫ T₂.mor₂ := by
  obtain ⟨a, ⟨ha₁, ha₂⟩⟩ := complete_distinguished_triangle_morphism _ _
    (inv_rot_of_dist_triangle _ hT₁) (inv_rot_of_dist_triangle _ hT₂) (c⟦(-1 : ℤ)⟧') a (by
    dsimp
    simp only [neg_comp, assoc, comp_neg, neg_inj, ← Functor.map_comp_assoc, ← comm,
      Functor.map_comp, shift_shift_neg', Functor.id_obj, assoc, Iso.inv_hom_id_app, comp_id])
  refine' ⟨a, ⟨ha₁, _⟩⟩
  dsimp only [Triangle.invRotate, Triangle.mk] at ha₂
  rw [← cancel_mono ((shiftEquiv C (1 : ℤ)).counitIso.inv.app T₂.obj₃), assoc, assoc, ← ha₂]
  simp only [shiftEquiv'_inverse, shiftEquiv'_functor, Functor.comp_obj, Functor.id_obj,
    shiftEquiv'_counitIso, shift_neg_shift', assoc, Iso.inv_hom_id_app_assoc]

lemma contractible_distinguished₁ (X : C) : Triangle.mk (0 : 0 ⟶ X) (𝟙 X) 0 ∈ distTriang C := by
  refine' isomorphic_distinguished _ (inv_rot_of_dist_triangle _ (contractible_distinguished X)) _ _
  exact Triangle.isoMk _ _ (Functor.mapZeroObject _).symm (Iso.refl _) (Iso.refl _)
    (by aesop_cat) (by aesop_cat) (by aesop_cat)

lemma contractible_distinguished₂ (X : C) :
    Triangle.mk (0 : X ⟶ 0) 0 (𝟙 (X⟦1⟧)) ∈ distTriang C := by
  refine' isomorphic_distinguished _ (inv_rot_of_dist_triangle _
    (contractible_distinguished₁ (X⟦(1 : ℤ)⟧))) _ _
  refine' Triangle.isoMk _ _ ((shiftEquiv C (1 : ℤ)).unitIso.app X) (Iso.refl _) (Iso.refl _)
    (by aesop_cat) (by aesop_cat)
    (by dsimp ; simp only [shift_shiftFunctorCompIsoId_inv_app, id_comp])

lemma contravariant_yoneda_exact₂ (T : Triangle C) (hT : T ∈ distTriang C) {X : C}
    (f : T.obj₂ ⟶ X) (hf : T.mor₁ ≫ f = 0) : ∃ (g : T.obj₃ ⟶ X), f = T.mor₂ ≫ g := by
  obtain ⟨g, ⟨hg₁, _⟩⟩ := complete_distinguished_triangle_morphism T _ hT
    (contractible_distinguished₁ X) 0 f (by aesop_cat)
  exact ⟨g, by simpa using hg₁.symm⟩

lemma contravariant_yoneda_exact₃ (T : Triangle C) (hT : T ∈ distTriang C) {X : C}
    (f : T.obj₃ ⟶ X) (hf : T.mor₂ ≫ f = 0) : ∃ (g : T.obj₁⟦(1 : ℤ)⟧ ⟶ X), f = T.mor₃ ≫ g :=
  contravariant_yoneda_exact₂ _ (rot_of_dist_triangle _ hT) f hf

lemma covariant_yoneda_exact₂ (T : Triangle C) (hT : T ∈ distTriang C) {X : C} (f : X ⟶ T.obj₂)
    (hf : f ≫ T.mor₂ = 0) : ∃ (g : X ⟶ T.obj₁), f = g ≫ T.mor₁ := by
  obtain ⟨a, ⟨ha₁, _⟩⟩ := complete_distinguished_triangle_morphism₁ _ T
    (contractible_distinguished X) hT f 0 (by aesop_cat)
  exact ⟨a, by simpa using ha₁⟩

lemma covariant_yoneda_exact₁ (T : Triangle C) (hT : T ∈ distTriang C) {X : C}
    (f : X ⟶ T.obj₁⟦(1 : ℤ)⟧) (hf : f ≫ T.mor₁⟦1⟧' = 0) : ∃ (g : X ⟶ T.obj₃), f = g ≫ T.mor₃ :=
  covariant_yoneda_exact₂ _ (rot_of_dist_triangle _
  (rot_of_dist_triangle _ hT)) f (by aesop_cat)

lemma covariant_yoneda_exact₃ (T : Triangle C) (hT : T ∈ distTriang C) {X : C} (f : X ⟶ T.obj₃)
    (hf : f ≫ T.mor₃ = 0) : ∃ (g : X ⟶ T.obj₂), f = g ≫ T.mor₂ :=
  covariant_yoneda_exact₂ _ (rot_of_dist_triangle _ hT) f hf

lemma shift_distinguished
  (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) :
    (Triangle.shiftFunctor C n).obj T ∈ distTriang C := by
  revert T hT
  let H : ℤ → Prop := fun n => ∀ (T : Triangle C) (_ : T ∈ distTriang C),
    (Triangle.shiftFunctor C n).obj T ∈ distTriang C
  change H n
  have H_zero : H 0 := fun T hT =>
    isomorphic_distinguished _ hT _ ((Triangle.shiftFunctorZero C).app T)
  have H_one : H 1 := fun T hT =>
    isomorphic_distinguished _ (rot_of_dist_triangle _
      (rot_of_dist_triangle _ (rot_of_dist_triangle _ hT))) _
        ((rotateRotateRotateIso C).symm.app T)
  have H_neg_one : H (-1):= fun T hT =>
    isomorphic_distinguished _ (inv_rot_of_dist_triangle _
      (inv_rot_of_dist_triangle _ (inv_rot_of_dist_triangle _ hT))) _
        ((invRotateInvRotateInvRotateIso C).symm.app T)
  have H_add : ∀ {a b c : ℤ} (_ : H a) (_ : H b) (_ : a + b = c), H c :=
    fun {a b c} ha hb hc T hT =>
      isomorphic_distinguished _ (hb _ (ha _ hT)) _ ((Triangle.shiftFunctorAdd' C _ _ _ hc).app T)
  obtain (n|n) := n
  . induction' n with n hn
    . exact H_zero
    . exact H_add hn H_one rfl
  . induction' n with n hn
    . exact H_neg_one
    . exact H_add hn H_neg_one rfl

lemma triangle_mor₃_eq_zero_of_epi_mor₂ (T : Triangle C) (hT : T ∈ distTriang C) (h : Epi T.mor₂) :
    T.mor₃ = 0 := by
  rw [← cancel_epi T.mor₂, comp_dist_triangle_mor_zero₂₃ _ hT, comp_zero]

lemma triangle_mor₂_eq_zero_of_epi_mor₁ (T : Triangle C) (hT : T ∈ distTriang C) (h : Epi T.mor₁) :
    T.mor₂ = 0 := by
  simpa using triangle_mor₃_eq_zero_of_epi_mor₂ _ (inv_rot_of_dist_triangle _ hT)
    (by dsimp ; infer_instance)

lemma triangle_mor₁_eq_zero_of_epi_mor₃ (T : Triangle C) (hT : T ∈ distTriang C) (h : Epi T.mor₃) :
    T.mor₁ = 0 := by
  have eq := triangle_mor₃_eq_zero_of_epi_mor₂ _ (rot_of_dist_triangle _ hT)
    (by dsimp ; infer_instance)
  dsimp at eq
  simp only [neg_eq_zero] at eq
  apply (shiftFunctor C (1 : ℤ)).map_injective
  rw [eq, Functor.map_zero]

lemma triangle_mor₃_eq_zero_of_mono_mor₁ (T : Triangle C) (hT : T ∈ distTriang C)
    (h : Mono T.mor₁) : T.mor₃ = 0 := by
  rw [← cancel_mono (T.mor₁⟦(1 : ℤ)⟧'), comp_dist_triangle_mor_zero₃₁ _ hT, zero_comp]

lemma triangle_mor₁_eq_zero_of_mono_mor₂ (T : Triangle C) (hT : T ∈ distTriang C)
    (h : Mono T.mor₂) : T.mor₁ = 0 := by
  have eq := triangle_mor₃_eq_zero_of_mono_mor₁ _ (rot_of_dist_triangle _ hT) (by dsimp ; infer_instance)
  dsimp at eq
  simp only [neg_eq_zero] at eq
  apply (shiftFunctor C (1 : ℤ)).map_injective
  rw [eq, Functor.map_zero]

lemma triangle_mor₂_eq_zero_of_mono_mor₃ (T : Triangle C) (hT : T ∈ distTriang C)
    (h : Mono T.mor₃) : T.mor₂ = 0 :=
  triangle_mor₁_eq_zero_of_mono_mor₂ _ (rot_of_dist_triangle _ hT) (by dsimp ; infer_instance)

lemma triangle_mono_mor₁ (T : Triangle C) (hT : T ∈ distTriang C) (h : T.mor₃ = 0) :
    Mono T.mor₁ := by
  refine' (shiftFunctor C (1 : ℤ)).mono_of_mono_map _
  rw [mono_iff_cancel_zero]
  intro P f hf
  obtain ⟨g, hg⟩ := covariant_yoneda_exact₁ _ hT f hf
  rw [hg, h, comp_zero]

lemma triangle_mono_mor₂ (T : Triangle C) (hT : T ∈ distTriang C) (h : T.mor₁ = 0) :
    Mono T.mor₂ :=
  triangle_mono_mor₁ _ (rot_of_dist_triangle _ hT) (by dsimp ; rw [h, Functor.map_zero, neg_zero])

lemma triangle_mono_mor₃ (T : Triangle C) (hT : T ∈ distTriang C) (h : T.mor₂ = 0) :
    Mono T.mor₃ :=
  triangle_mono_mor₂ _ (rot_of_dist_triangle _ hT) h

section

@[simps]
def binaryBiproductData (T : Triangle C) (hT : T ∈ distTriang C) (hT₀ : T.mor₃ = 0)
    (inr : T.obj₃ ⟶ T.obj₂) (inr_snd : inr ≫ T.mor₂ = 𝟙 _) (fst : T.obj₂ ⟶ T.obj₁)
    (total : fst ≫ T.mor₁ + T.mor₂ ≫ inr = 𝟙 T.obj₂) :
    BinaryBiproductData T.obj₁ T.obj₃ where
  bicone :=
    { pt := T.obj₂
      fst := fst
      snd := T.mor₂
      inl := T.mor₁
      inr := inr
      inl_fst := by
        have : Mono T.mor₁ := triangle_mono_mor₁ T hT hT₀
        have eq : fst ≫ T.mor₁ = 𝟙 T.obj₂ - T.mor₂ ≫ inr := by rw [← total, add_sub_cancel]
        simp only [← cancel_mono T.mor₁, assoc, id_comp, eq, comp_sub, comp_id,
          comp_dist_triangle_mor_zero₁₂_assoc _ hT, zero_comp, sub_zero]
      inl_snd := comp_dist_triangle_mor_zero₁₂ _ hT
      inr_fst := by
        have : Mono T.mor₁ := triangle_mono_mor₁ T hT hT₀
        have eq : fst ≫ T.mor₁ = 𝟙 T.obj₂ - T.mor₂ ≫ inr := by rw [← total, add_sub_cancel]
        simp only [← cancel_mono T.mor₁, assoc, eq, comp_sub, reassoc_of% inr_snd, comp_id,
          sub_self, zero_comp]
      inr_snd := inr_snd }
  isBilimit := isBinaryBilimitOfTotal _ total

end

instance : HasBinaryBiproducts C := ⟨fun X₁ X₃ => by
  obtain ⟨X₂, inl, snd, mem⟩ := distinguished_cocone_triangle₂ (0 : X₃ ⟶ X₁⟦(1 : ℤ)⟧)
  obtain ⟨inr : X₃ ⟶ X₂, inr_snd : 𝟙 _ = inr ≫ snd⟩ := covariant_yoneda_exact₃ _ mem (𝟙 X₃) (by simp)
  obtain ⟨fst : X₂ ⟶ X₁, hfst : 𝟙 X₂ - snd ≫ inr = fst ≫ inl⟩ :=
    covariant_yoneda_exact₂ _ mem (𝟙 X₂ - snd ≫ inr) (by
      dsimp
      simp only [sub_comp, assoc, id_comp, ← inr_snd, comp_id, sub_self])
  refine' ⟨⟨binaryBiproductData _ mem rfl inr inr_snd.symm fst _⟩⟩
  dsimp
  simp only [← hfst, sub_add_cancel]⟩

instance : HasFiniteProducts C := hasFiniteProducts_of_has_binary_and_terminal
instance : HasFiniteCoproducts C := hasFiniteCoproducts_of_has_binary_and_initial
instance : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts

lemma exists_iso_binaryBiproduct_of_dist_triang (T : Triangle C) (hT : T ∈ distTriang C)
  (zero : T.mor₃ = 0) :
    ∃ (e : T.obj₂ ≅ T.obj₁ ⊞ T.obj₃), T.mor₁ ≫ e.hom = biprod.inl ∧
      T.mor₂ = e.hom ≫ biprod.snd := by
  obtain ⟨inr, inr_snd⟩ := covariant_yoneda_exact₃ _ hT (𝟙 _) (by aesop_cat)
  obtain ⟨fst, hfst⟩ := covariant_yoneda_exact₂ _ hT (𝟙 T.obj₂ - T.mor₂ ≫ inr) (by
    simp only [sub_comp, assoc, ← inr_snd, comp_id, id_comp, sub_self])
  let d := binaryBiproductData _ hT zero inr inr_snd.symm fst
    (by dsimp ; simp only [← hfst, sub_add_cancel])
  refine' ⟨d.isoBiprod.symm, ⟨_, by simp⟩⟩
  ext
  . simpa using d.bicone.inl_fst
  . simpa using d.bicone.inl_snd

lemma binaryBiproductTriangle_distinguished (X₁ X₂ : C) :
    binaryBiproductTriangle X₁ X₂ ∈ distTriang C := by
  obtain ⟨Y, g, h, mem⟩ := distinguished_cocone_triangle₂ (0 : X₂ ⟶ X₁⟦(1 : ℤ)⟧)
  obtain ⟨e, ⟨he₁, he₂⟩⟩ := exists_iso_binaryBiproduct_of_dist_triang _ mem rfl
  dsimp at he₁ he₂
  refine' isomorphic_distinguished _ mem _ (Iso.symm _)
  refine' Triangle.isoMk _ _ (Iso.refl _) e (Iso.refl _)
    (by aesop_cat) (by aesop_cat) (by aesop_cat)

lemma binaryProductTriangle_distinguished (X₁ X₂ : C) :
    binaryProductTriangle X₁ X₂ ∈ distTriang C :=
  isomorphic_distinguished _ (binaryBiproductTriangle_distinguished X₁ X₂) _
    (binaryProductTriangleIsoBinaryBiproductTriangle X₁ X₂)

@[simps!]
def productTriangle {J : Type _} (T : J → Triangle C)
    [HasProduct (fun j => (T j).obj₁)] [HasProduct (fun j => (T j).obj₂)]
    [HasProduct (fun j => (T j).obj₃)]
    [HasProduct (fun j => (T j).obj₁⟦(1 : ℤ)⟧)] : Triangle C :=
  Triangle.mk (Pi.map (fun j => (T j).mor₁))
    (Pi.map (fun j => (T j).mor₂))
    (Pi.map (fun j => (T j).mor₃) ≫ inv (piComparison _ _))

@[simps]
def productTriangle.π {J : Type _} (T : J → Triangle C)
    [HasProduct (fun j => (T j).obj₁)] [HasProduct (fun j => (T j).obj₂)]
    [HasProduct (fun j => (T j).obj₃)]
    [HasProduct (fun j => (T j).obj₁⟦(1 : ℤ)⟧)] (j : J) :
    productTriangle T ⟶ T j where
  hom₁ := Pi.π _ j
  hom₂ := Pi.π _ j
  hom₃ := Pi.π _ j
  comm₁ := by simp
  comm₂ := by simp
  comm₃ := by
    dsimp
    rw [← piComparison_comp_π, assoc, IsIso.inv_hom_id_assoc]
    simp only [limMap_π, Discrete.natTrans_app]

lemma productTriangle.π_zero₃₁ (T : J → Triangle C)
    [HasProduct (fun j => (T j).obj₁)] [HasProduct (fun j => (T j).obj₂)]
    [HasProduct (fun j => (T j).obj₃)]
    [HasProduct (fun j => (T j).obj₁⟦(1 : ℤ)⟧)]
    [HasProduct (fun j => (T j).obj₂⟦(1 : ℤ)⟧)]
    (h : ∀ j, (T j).mor₃ ≫ (T j).mor₁⟦(1 : ℤ)⟧' = 0) :
    (productTriangle T).mor₃ ≫ (productTriangle T).mor₁⟦1⟧' = 0 := by
  dsimp
  have eq : (Pi.map fun j => (T j).mor₁) = Pi.lift (fun j => Pi.π _ j ≫ (T j).mor₁) := by
    aesop_cat
  rw [eq, assoc, ← cancel_mono (piComparison _ _), zero_comp, assoc, assoc]
  refine' Limits.Pi.hom_ext _ _ (fun j => _)
  simp only [map_lift_piComparison, assoc, limit.lift_π, Fan.mk_pt, Fan.mk_π_app, zero_comp,
    Functor.map_comp, ← piComparison_comp_π_assoc, IsIso.inv_hom_id_assoc,
    limMap_π_assoc, Discrete.natTrans_app, h j, comp_zero]

@[simps]
def productTriangle.lift {J : Type _} {T' : Triangle C} (T : J → Triangle C)
  (φ : ∀ j, T' ⟶ T j)
    [HasProduct (fun j => (T j).obj₁)] [HasProduct (fun j => (T j).obj₂)]
    [HasProduct (fun j => (T j).obj₃)]
    [HasProduct (fun j => (T j).obj₁⟦(1 : ℤ)⟧)] : T' ⟶ productTriangle T where
  hom₁ := Pi.lift (fun j => (φ j).hom₁)
  hom₂ := Pi.lift (fun j => (φ j).hom₂)
  hom₃ := Pi.lift (fun j => (φ j).hom₃)
  comm₁ := Limits.Pi.hom_ext _ _ (fun j => by simp)
  comm₂ := Limits.Pi.hom_ext _ _ (fun j => by simp)
  comm₃ := by
    dsimp
    rw [← cancel_mono (piComparison _ _), assoc, assoc, assoc, IsIso.inv_hom_id]
    refine' Limits.Pi.hom_ext _ _ (fun j => by simp)

lemma productTriangle_distinguished {J : Type _} (T : J → Triangle C)
    (hT : ∀ j, T j ∈ distTriang C)
    [HasProduct (fun j => (T j).obj₁)] [HasProduct (fun j => (T j).obj₂)]
    [HasProduct (fun j => (T j).obj₃)]
    [HasProduct (fun j => (T j).obj₁⟦(1 : ℤ)⟧)]
    [HasProduct (fun j => (T j).obj₂⟦(1 : ℤ)⟧)] :
    productTriangle T ∈ distTriang C := by
  let f₁ := Pi.map (fun j => (T j).mor₁)
  obtain ⟨Z, f₂, f₃, hT'⟩  := distinguished_cocone_triangle f₁
  let T' := Triangle.mk f₁ f₂ f₃
  change T' ∈ distTriang C at hT'
  have h := fun j => complete_distinguished_triangle_morphism _ _ hT' (hT j)
    (Pi.π _ j) (Pi.π _ j) (by simp)
  let φ : ∀ j, T' ⟶ T j := fun j =>
    { hom₁ := Pi.π _ j
      hom₂ := Pi.π _ j
      hom₃ := (h j).choose
      comm₁ := by simp
      comm₂ := (h j).choose_spec.1
      comm₃ := (h j).choose_spec.2 }
  obtain ⟨φ', hφ'⟩ : ∃ (φ' : T' ⟶ productTriangle T), φ' = productTriangle.lift _ φ := ⟨_, rfl⟩
  suffices IsIso φ' by
    apply isomorphic_distinguished _ hT' _ (asIso φ').symm
  have h₁ : φ'.hom₁ = 𝟙 _ := Limits.Pi.hom_ext _ _ (by simp [hφ'])
  have h₂ : φ'.hom₂ = 𝟙 _ := Limits.Pi.hom_ext _ _ (by simp [hφ'])
  have : IsIso φ'.hom₁ := by rw [h₁] ; infer_instance
  have : IsIso φ'.hom₂ := by rw [h₂] ; infer_instance
  suffices IsIso φ'.hom₃ from inferInstance
  have : Mono φ'.hom₃ := by
    rw [mono_iff_cancel_zero]
    intro A f hf
    have hf' : f ≫ T'.mor₃ = 0 := by
      rw [← cancel_mono (φ'.hom₁⟦1⟧'), zero_comp, assoc, φ'.comm₃, reassoc_of% hf, zero_comp]
    obtain ⟨g, hg⟩ := covariant_yoneda_exact₃ _ hT' f hf'
    have hg' : ∀ j, (g ≫ Pi.π _ j) ≫ (T j).mor₂ = 0 := fun j => by
      have : g ≫ T'.mor₂ ≫ φ'.hom₃ ≫ Pi.π _ j = 0 := by rw [← reassoc_of% hg,
        reassoc_of% hf, zero_comp]
      rw [φ'.comm₂_assoc, h₂, id_comp] at this
      simpa using this
    have hg'' := fun j => covariant_yoneda_exact₂ _ (hT j) _ (hg' j)
    let α := fun j => (hg'' j).choose
    have hα : ∀ j, _ = α j ≫ _ := fun j => (hg'' j).choose_spec
    have hg''' : g = Pi.lift α ≫ T'.mor₁ := Limits.Pi.hom_ext _ _
        (fun j => by rw [hα] ; simp)
    rw [hg, hg''', assoc, comp_dist_triangle_mor_zero₁₂ _ hT', comp_zero]
  refine' isIso_of_yoneda_map_bijective _ (fun A => ⟨_, _⟩)
  . intro a₁ a₂ ha
    simpa only [← cancel_mono φ'.hom₃] using ha
  . intro a
    obtain ⟨a', ha'⟩ : ∃ (a' : A ⟶ Z), a' ≫ T'.mor₃ = a ≫ (productTriangle T).mor₃ := by
      have zero : ((productTriangle T).mor₃) ≫ (shiftFunctor C 1).map T'.mor₁ = 0 := by
        rw [← cancel_mono (φ'.hom₂⟦1⟧'), zero_comp, assoc, ← Functor.map_comp, φ'.comm₁, h₁,
          id_comp]
        rw [productTriangle.π_zero₃₁]
        intro j
        exact comp_dist_triangle_mor_zero₃₁ _ (hT j)
      have ⟨g, hg⟩ := covariant_yoneda_exact₁ _ hT' (a ≫ (productTriangle T).mor₃) (by
        rw [assoc, zero, comp_zero])
      exact ⟨g, hg.symm⟩
    have ha'' := fun (j : J) => covariant_yoneda_exact₃ _ (hT j)
      ((a - a' ≫ φ'.hom₃) ≫ Pi.π _ j) (by
        simp only [sub_comp, assoc]
        erw [← (productTriangle.π T j).comm₃]
        erw [← φ'.comm₃_assoc]
        rw [reassoc_of% ha']
        simp [h₁])
    let b := fun j => (ha'' j).choose
    have hb : ∀ j, _  = b j ≫ _ := fun j => (ha'' j).choose_spec
    have hb' : a - a' ≫ φ'.hom₃ = Pi.lift b ≫ (productTriangle T).mor₂ :=
      Limits.Pi.hom_ext _ _ (fun j => by rw [hb] ; simp)
    have : (a' + (by exact Pi.lift b) ≫ T'.mor₂) ≫ φ'.hom₃ = a := by
      rw [add_comp, assoc, φ'.comm₂, h₂, id_comp, ← hb', add_sub_cancel'_right]
    exact ⟨_, this⟩

lemma isZero_of_isIso_mor₁ (T : Triangle C) (hT : T ∈ distTriang C) (h : IsIso T.mor₁) :
    IsZero T.obj₃ := by
  have eq : T.mor₃ = 0 := triangle_mor₃_eq_zero_of_mono_mor₁ _ hT inferInstance
  rw [IsZero.iff_id_eq_zero]
  obtain ⟨f, hf⟩ := covariant_yoneda_exact₃ _ hT (𝟙 _) (by rw [eq, comp_zero])
  obtain ⟨g, hg⟩ : ∃ g, f = g ≫ T.mor₁ := by
    refine' ⟨f ≫ inv T.mor₁, by simp only [assoc, IsIso.inv_hom_id, comp_id]⟩
  rw [hf, hg, assoc, comp_dist_triangle_mor_zero₁₂ _ hT, comp_zero]

lemma isIso₂_of_isIso₁₃ {T T' : Triangle C} (φ : T ⟶ T') (hT : T ∈ distTriang C)
    (hT' : T' ∈ distTriang C) (h₁ : IsIso φ.hom₁) (h₃ : IsIso φ.hom₃) : IsIso φ.hom₂ := by
  have : Mono φ.hom₂ := by
    rw [mono_iff_cancel_zero]
    intro A f hf
    obtain ⟨g, rfl⟩ := covariant_yoneda_exact₂ _ hT f (by
      rw [← cancel_mono φ.hom₃, assoc, φ.comm₂, reassoc_of% hf, zero_comp, zero_comp])
    rw [assoc] at hf
    obtain ⟨h, hh⟩ := covariant_yoneda_exact₂ T'.invRotate (inv_rot_of_dist_triangle _ hT')
      (g ≫ φ.hom₁) (by dsimp ; rw [assoc, ← φ.comm₁, hf])
    obtain ⟨k, rfl⟩ : ∃ (k : A ⟶ T.invRotate.obj₁), k ≫ T.invRotate.mor₁ = g := by
      refine' ⟨h ≫ inv (φ.hom₃⟦(-1 : ℤ)⟧'), _⟩
      have eq := ((invRotate C).map φ).comm₁
      dsimp only [invRotate] at eq
      rw [← cancel_mono φ.hom₁, assoc, assoc, eq, IsIso.inv_hom_id_assoc, hh]
    erw [assoc, comp_dist_triangle_mor_zero₁₂ _ (inv_rot_of_dist_triangle _ hT), comp_zero]
  refine' isIso_of_yoneda_map_bijective _ (fun A => ⟨_, _⟩)
  . intro f₁ f₂ h
    simpa only [← cancel_mono φ.hom₂] using h
  . intro y₂
    obtain ⟨x₃, hx₃⟩ : ∃ (x₃ : A ⟶ T.obj₃), x₃ ≫ φ.hom₃ = y₂ ≫ T'.mor₂ :=
      ⟨y₂ ≫ T'.mor₂ ≫ inv φ.hom₃, by simp⟩
    obtain ⟨x₂, hx₂⟩ := covariant_yoneda_exact₃ _ hT x₃ (by
      rw [← cancel_mono (φ.hom₁⟦(1 : ℤ)⟧'), assoc, zero_comp, φ.comm₃, reassoc_of% hx₃,
        comp_dist_triangle_mor_zero₂₃ _ hT', comp_zero])
    obtain ⟨y₁, hy₁⟩ := covariant_yoneda_exact₂ _ hT' (y₂ - x₂ ≫ φ.hom₂) (by
      rw [sub_comp, assoc, ← φ.comm₂, ← reassoc_of% hx₂, hx₃, sub_self])
    obtain ⟨x₁, hx₁⟩ : ∃ (x₁ : A ⟶ T.obj₁), x₁ ≫ φ.hom₁ = y₁ := ⟨y₁ ≫ inv φ.hom₁, by simp⟩
    refine' ⟨x₂ + x₁ ≫ T.mor₁, _⟩
    dsimp
    rw [add_comp, assoc, φ.comm₁, reassoc_of% hx₁, ← hy₁, add_sub_cancel'_right]

lemma isIso₃_of_isIso₁₂ {T T' : Triangle C} (φ : T ⟶ T') (hT : T ∈ distTriang C)
    (hT' : T' ∈ distTriang C) (h₁ : IsIso φ.hom₁) (h₂ : IsIso φ.hom₂) : IsIso φ.hom₃ :=
    isIso₂_of_isIso₁₃ ((rotate C).map φ) (rot_of_dist_triangle _ hT)
      (rot_of_dist_triangle _ hT') h₂ (by dsimp ; infer_instance)

lemma complete_distinguished_triangle_morphism' (T₁ T₂ : Triangle C)
    (hT₁ : T₁ ∈ distTriang C) (hT₂ : T₂ ∈ distTriang C)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (comm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
      ∃ (φ : T₁ ⟶ T₂), φ.hom₁ = a ∧ φ.hom₂ = b := by
  obtain ⟨c, ⟨hc₁, hc₂⟩⟩ := complete_distinguished_triangle_morphism _ _ hT₁ hT₂ a b comm
  exact ⟨{  hom₁ := a
            hom₂ := b
            hom₃ := c
            comm₁ := comm
            comm₂ := hc₁
            comm₃ := hc₂ }, rfl, rfl⟩

lemma exists_iso_of_arrow_iso (T₁ T₂ : Triangle C) (hT₁ : T₁ ∈ distTriang C)
    (hT₂ : T₂ ∈ distTriang C) (e : Arrow.mk T₁.mor₁ ≅ Arrow.mk T₂.mor₁) :
    ∃ (e' : T₁ ≅ T₂), e'.hom.hom₁ = e.hom.left ∧ e'.hom.hom₂ = e.hom.right := by
  obtain ⟨φ, ⟨hφ₁, hφ₂⟩⟩ :=
    complete_distinguished_triangle_morphism' T₁ T₂ hT₁ hT₂ e.hom.left e.hom.right e.hom.w.symm
  have : IsIso φ.hom₁ := by rw [hφ₁] ; infer_instance
  have : IsIso φ.hom₂ := by rw [hφ₂] ; infer_instance
  have : IsIso φ.hom₃ := isIso₃_of_isIso₁₂ φ hT₁ hT₂ inferInstance inferInstance
  exact ⟨asIso φ, hφ₁, hφ₂⟩

@[simps! hom_hom₁ hom_hom₂ inv_hom₁ inv_hom₂]
def isoTriangleOfIso₁₂ (T₁ T₂ : Triangle C) (hT₁ : T₁ ∈ distTriang C)
    (hT₂ : T₂ ∈ distTriang C) (e₁ : T₁.obj₁ ≅ T₂.obj₁) (e₂ : T₁.obj₂ ≅ T₂.obj₂)
    (comm : T₁.mor₁ ≫ e₂.hom = e₁.hom ≫ T₂.mor₁) : T₁ ≅ T₂ := by
    have h := exists_iso_of_arrow_iso T₁ T₂ hT₁ hT₂ (Arrow.isoMk e₁ e₂ comm.symm)
    let e := h.choose
    refine' Triangle.isoMk _ _ e₁ e₂ (Triangle.π₃.mapIso e) comm (by
      convert e.hom.comm₂
      exact h.choose_spec.2.symm) (by
      convert e.hom.comm₃
      exact h.choose_spec.1.symm)

lemma isIso₂_iff (T : Triangle C) (hT : T ∈ distTriang C) :
    IsIso T.mor₂ ↔ (T.mor₁ = 0 ∧ T.mor₃ = 0) := by
  constructor
  . intro
    constructor
    . exact triangle_mor₁_eq_zero_of_mono_mor₂ T hT inferInstance
    . exact triangle_mor₃_eq_zero_of_epi_mor₂ T hT inferInstance
  . rintro ⟨h₁, h₃⟩
    obtain ⟨φ, hφ⟩ := covariant_yoneda_exact₃ T hT (𝟙 T.obj₃) (by rw [h₃, comp_zero])
    have := triangle_mono_mor₂ T hT h₁
    exact ⟨⟨φ, by rw [← cancel_mono T.mor₂, assoc, id_comp, ← hφ, comp_id], hφ.symm⟩⟩

lemma isIso₁_iff (T : Triangle C) (hT : T ∈ distTriang C) :
    IsIso T.mor₁ ↔ (T.mor₂ = 0 ∧ T.mor₃ = 0) := by
  refine' (isIso₂_iff _ (inv_rot_of_dist_triangle T hT)).trans _
  have : (shiftFunctor C (-1 : ℤ)).map T.mor₃ = 0 ↔ T.mor₃ = 0 := by
    constructor
    . intro h
      apply (shiftFunctor C (-1 : ℤ)).map_injective
      rw [h, Functor.map_zero]
    . intro h
      simp only [h, Functor.map_zero]
  dsimp
  simp only [neg_eq_zero, IsIso.comp_right_eq_zero, this]
  tauto

lemma isIso₃_iff (T : Triangle C) (hT : T ∈ distTriang C) :
    IsIso T.mor₃ ↔ (T.mor₁ = 0 ∧ T.mor₂ = 0) := by
  refine' (isIso₂_iff _ (rot_of_dist_triangle T hT)).trans _
  have : (shiftFunctor C (1 : ℤ)).map T.mor₁ = 0 ↔ T.mor₁ = 0 := by
    constructor
    . intro h
      apply (shiftFunctor C (1 : ℤ)).map_injective
      rw [h, Functor.map_zero]
    . intro h
      simp only [h, Functor.map_zero]
  dsimp
  simp only [neg_eq_zero, this]
  tauto

lemma isIso₁_iff_isZero₃ (T : Triangle C) (hT : T ∈ distTriang C) :
    IsIso T.mor₁ ↔ IsZero T.obj₃ := by
  rw [isIso₁_iff _ hT]
  constructor
  . rintro ⟨h₂, h₃⟩
    have := triangle_mono_mor₃ _ hT h₂
    rw [IsZero.iff_id_eq_zero, ← cancel_mono T.mor₃, id_comp, zero_comp, h₃]
  . intro h
    exact ⟨h.eq_of_tgt _ _, h.eq_of_src _ _⟩

lemma isIso₂_iff_isZero₁ (T : Triangle C) (hT : T ∈ distTriang C) :
    IsIso T.mor₂ ↔ IsZero T.obj₁ := by
  refine' (isIso₁_iff_isZero₃ _ (rot_of_dist_triangle _ hT)).trans _
  dsimp
  simp only [IsZero.iff_id_eq_zero]
  constructor
  . intro h
    apply (shiftFunctor C (1 : ℤ)).map_injective
    rw [Functor.map_id, Functor.map_zero, h]
  . intro h
    rw [← Functor.map_id, h, Functor.map_zero]

lemma isIso₃_iff_isZero₂ (T : Triangle C) (hT : T ∈ distTriang C) :
    IsIso T.mor₃ ↔ IsZero T.obj₂ :=
  isIso₂_iff_isZero₁ _ (rot_of_dist_triangle _ hT)

lemma isZero₂_of_isZero₂₃ (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : IsZero T.obj₁) (h₃ : IsZero T.obj₃) : IsZero T.obj₂ := by
  rw [← isIso₃_iff_isZero₂ _ hT]
  refine' ⟨⟨0, h₃.eq_of_src _ _, IsZero.eq_of_tgt _ _ _⟩⟩
  rw [IsZero.iff_id_eq_zero, ← Functor.map_id,
    (IsZero.iff_id_eq_zero _).1 h₁, Functor.map_zero]

/-
TODO: If `C` is pretriangulated with respect to a shift,
then `Cᵒᵖ` is pretriangulated with respect to the inverse shift.
-/

end Pretriangulated

end CategoryTheory
