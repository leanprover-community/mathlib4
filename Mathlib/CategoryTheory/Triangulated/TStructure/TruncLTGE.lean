/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Basic

/-!
# Truncations for a t-structure

Let `t` be a t-structure on a (pre)triangulated category `C`.
In this file, for any `n : ℤ`, we construct truncation functors `t.truncLT n : C ⥤ C`,
`t.truncGE n : C ⥤ C` and natural transformations `t.truncLTι n : t.truncLT n ⟶ 𝟭 C`,
`t.truncGEπ n : 𝟭 C ⟶ t.truncGE n` and
`t.truncGEδLT n : t.truncGE n ⟶ t.truncLT n ⋙ shiftFunctor C (1 : ℤ)` which are
part of a distinguished triangle
`(t.truncLT n).obj X ⟶ X ⟶ (t.truncGE n).obj X ⟶ ((t.truncLT n).obj X)⟦1⟧` for any `X : C`,
with `(t.truncLT n).obj X < n` and `(t.truncGE n).obj X ≥ n`.

-/

universe v u

namespace CategoryTheory

open Limits Pretriangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

namespace TStructure

variable (t : TStructure C)

/-- Two morphisms `T ⟶ T'` between distinguished triangles must coincide when
they coincide on the middle object, and there are integers `a ≤ b` such that
for a t-structure, we have `T.obj₁ ≤ a` and `T'.obj₃ ≥ b`. -/
public lemma triangle_map_ext {T T' : Triangle C} {f₁ f₂ : T ⟶ T'}
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C) (a b : ℤ)
    (h₀ : t.IsLE T.obj₁ a) (h₁ : t.IsGE T'.obj₃ b)
    (H : f₁.hom₂ = f₂.hom₂ := by cat_disch)
    (hab : a ≤ b := by cutsat) : f₁ = f₂ := by
  suffices ∀ (f : T ⟶ T'), f.hom₂ = 0 → f = 0 by rw [← sub_eq_zero]; cat_disch
  intro f hf
  ext
  · obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ hT')
      f.hom₁ (by simp [← f.comm₁, hf])
    simp [hg, t.zero_of_isLE_of_isGE g a (b + 1) (by cutsat)
      h₀ (t.isGE_shift _ b (-1) (b + 1))]
  · simp [hf]
  · obtain ⟨g, hg⟩ := T.yoneda_exact₃ hT f.hom₃ (by cat_disch)
    simp [hg, t.zero_of_isLE_of_isGE g (a - 1) b (by cutsat)
      (t.isLE_shift _ a 1 (a - 1)) inferInstance]

/-- If `a < b`, then a morphism `T.obj₂ ⟶ T'.obj₂` extends to a morphism `T ⟶ T'`
of distinguished triangles when for a t-structure `T.obj₁ ≤ a` and `T'.obj₃ ≥ b`. -/
public lemma triangle_map_exists {T T' : Triangle C}
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (φ : T.obj₂ ⟶ T'.obj₂) (a b : ℤ)
    (h₀ : t.IsLE T.obj₁ a) (h₁' : t.IsGE T'.obj₃ b) (h : a < b := by cutsat) :
    ∃ (f : T ⟶ T'), f.hom₂ = φ := by
  obtain ⟨a, comm₁⟩ := T'.coyoneda_exact₂ hT' (T.mor₁ ≫ φ) (t.zero _ a b)
  obtain ⟨c, comm₂, comm₃⟩ := complete_distinguished_triangle_morphism _ _ hT hT' a φ comm₁
  exact ⟨{ hom₁ := a, hom₂ := φ, hom₃ := c }, rfl⟩

/-- If `a < b`, then an isomorphism `T.obj₂ ≅ T'.obj₂` extends to an isomorphism `T ≅ T'`
of distinguished triangles when for a t-structure, both `T.obj₁` and `T'.obj₁` are `≤ a` and
both `T.obj₃` and `T'.obj₃` are `≥ b`. -/
public lemma triangle_iso_exists {T T' : Triangle C}
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C) (e : T.obj₂ ≅ T'.obj₂)
    (a b : ℤ) (h₀ : t.IsLE T.obj₁ a) (h₁ : t.IsGE T.obj₃ b)
    (h₀' : t.IsLE T'.obj₁ a) (h₁' : t.IsGE T'.obj₃ b) (h : a < b := by cutsat) :
    ∃ (e' : T ≅ T'), e'.hom.hom₂ = e.hom := by
  obtain ⟨hom, hhom⟩ := triangle_map_exists t hT hT' e.hom _ _ h₀ h₁'
  obtain ⟨inv, _⟩ := triangle_map_exists t hT' hT e.inv _ _ h₀' h₁
  exact
    ⟨{hom := hom
      inv := inv
      hom_inv_id := triangle_map_ext t hT hT a b h₀ h₁
      inv_hom_id := triangle_map_ext t hT' hT' a b h₀' h₁' }, hhom⟩

namespace TruncAux
/-! The private definitions in the namespace `TStructure.TruncAux` are part of the
implementation of the truncation functors `truncLT`, `truncGE` and the
distinguished triangles they fit in. -/

variable (n : ℤ) (X : C)

/-- Given a t-structure `t` on `C`, `X : C` and `n : ℤ`, this is a distinguished
triangle `obj₁ ⟶ X ⟶ obj₃ ⟶ obj₁⟦1⟧` where `obj₁` is `< n` and `obj₃` is `≥ n`.
(This should not be used directly: use `truncLT` and `truncGE` instead.) -/
@[simps! obj₂]
noncomputable def triangle : Triangle C :=
  Triangle.mk
    (t.exists_triangle X (n - 1) n
      (by cutsat)).choose_spec.choose_spec.choose_spec.choose_spec.choose
    (t.exists_triangle X (n - 1) n
      (by cutsat)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
    (t.exists_triangle X (n - 1) n
      (by cutsat)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

lemma triangle_distinguished :
    triangle t n X ∈ distTriang C :=
  (t.exists_triangle X (n - 1) n
    (by cutsat)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

instance triangle_obj₁_isLE (n : ℤ) :
    t.IsLE (triangle t n X).obj₁ (n-1) :=
  ⟨(t.exists_triangle X (n - 1) n (by cutsat)).choose_spec.choose_spec.choose⟩

instance triangle_obj₃_isGE :
    t.IsGE (triangle t n X).obj₃ n :=
  ⟨(t.exists_triangle X (n - 1) n (by cutsat)).choose_spec.choose_spec.choose_spec.choose⟩

variable {X} {Y : C} (φ : X ⟶ Y)

/-- Version of `TStructure.triangle_map_ext` that is specialized for the auxiliary
definition `TruncAux.triangle`. -/
@[ext]
lemma triangle_map_ext' (f₁ f₂ : triangle t n X ⟶ triangle t n Y)
    (H : f₁.hom₂ = f₂.hom₂ := by cat_disch) : f₁ = f₂ :=
  triangle_map_ext t (triangle_distinguished t n X) (triangle_distinguished t n Y) (n - 1) n
    inferInstance inferInstance H (by cutsat)

/-- Auxiliary definition for `triangleFunctor`. -/
@[simps hom₂]
noncomputable def triangleMap : triangle t n X ⟶ triangle t n Y :=
  have H := triangle_map_exists t (triangle_distinguished t n X)
    (triangle_distinguished t n Y) φ (n - 1) n inferInstance inferInstance (by cutsat)
  { hom₁ := H.choose.hom₁
    hom₂ := φ
    hom₃ := H.choose.hom₃
    comm₁ := by rw [← H.choose.comm₁, H.choose_spec]
    comm₂ := by rw [H.choose.comm₂, H.choose_spec]
    comm₃ := H.choose.comm₃ }

/-- Given a t-structure `t` on `C` and `n : ℤ`, this is the
functorial (distinguished) triangle `obj₁ ⟶ X ⟶ obj₃ ⟶ obj₁⟦1⟧` for any `X : C`,
where `obj₁` is `< n` and `obj₃` is `≥ n`.
(This should not be used directly: use `triangleLTGE` instead.) -/
@[simps]
noncomputable def triangleFunctor : C ⥤ Triangle C where
  obj := triangle t n
  map φ := triangleMap t n φ

variable (A)

lemma triangleFunctor_obj_distinguished :
    (triangleFunctor t n).obj A ∈ distTriang C :=
  triangle_distinguished t n A

instance isLE_triangleFunctor_obj_obj₁ :
    t.IsLE ((triangleFunctor t n).obj A).obj₁ (n-1) := by
  dsimp [triangleFunctor]
  infer_instance

instance isGE_triangleFunctor_obj_obj₃ :
    t.IsGE ((triangleFunctor t n).obj A).obj₃ n := by
  dsimp [triangleFunctor]
  infer_instance

instance : (triangleFunctor t n).Additive where

end TruncAux

public section

/-- Given a t-structure `t` on a pretriangulated category `C` and `n : ℤ`, this
is the `< n`-truncation functor. See also the natural transformation `truncLTι`. -/
noncomputable def truncLT (n : ℤ) : C ⥤ C :=
  TruncAux.triangleFunctor t n ⋙ Triangle.π₁

instance (n : ℤ) : (t.truncLT n).Additive where
  map_add {_ _ _ _} := by
    dsimp only [truncLT, Functor.comp_map]
    rw [Functor.map_add]
    dsimp

/-- The natural transformation `t.truncLT n ⟶ 𝟭 C` when `t` is a t-structure
on a category `C` and `n : ℤ`. -/
noncomputable def truncLTι (n : ℤ) : t.truncLT n ⟶ 𝟭 _ :=
  Functor.whiskerLeft (TruncAux.triangleFunctor t n) Triangle.π₁Toπ₂

/-- Given a t-structure `t` on a pretriangulated category `C` and `n : ℤ`, this
is the `≥ n`-truncation functor. See also the natural transformation `truncGEπ`. -/
noncomputable def truncGE (n : ℤ) : C ⥤ C :=
  TruncAux.triangleFunctor t n ⋙ Triangle.π₃

instance (n : ℤ) : (t.truncGE n).Additive where
  map_add {_ _ _ _} := by
    dsimp only [truncGE, Functor.comp_map]
    rw [Functor.map_add]
    dsimp

/-- The natural transformation `𝟭 C ⟶ t.truncGE n` when `t` is a t-structure
on a category `C` and `n : ℤ`. -/
noncomputable def truncGEπ (n : ℤ) : 𝟭 _ ⟶ t.truncGE n :=
  Functor.whiskerLeft (TruncAux.triangleFunctor t n) Triangle.π₂Toπ₃

instance (X : C) (n : ℤ) : t.IsLE ((t.truncLT n).obj X) (n - 1) := by
  dsimp [truncLT]
  infer_instance

instance (X : C) (n : ℤ) : t.IsGE ((t.truncGE n).obj X) n := by
  dsimp [truncGE]
  infer_instance

/-- The connecting morphism `t.truncGE n ⟶ t.truncLT n ⋙ shiftFunctor C (1 : ℤ)`
when `t` is a t-structure on a pretriangulated category and `n : ℤ`. -/
noncomputable def truncGEδLT (n : ℤ) :
    t.truncGE n ⟶ t.truncLT n ⋙ shiftFunctor C (1 : ℤ) :=
  Functor.whiskerLeft (TruncAux.triangleFunctor t n) Triangle.π₃Toπ₁

/-- The distinguished triangle `(t.truncLT n).obj A ⟶ A ⟶ (t.truncGE n).obj A ⟶ ...`
as a functor `C ⥤ Triangle C` when `t` is a `t`-structure on a pretriangulated
category `C` and `n : ℤ`. -/
@[expose, simps!]
noncomputable def triangleLTGE (n : ℤ) : C ⥤ Triangle C :=
  Triangle.functorMk (t.truncLTι n) (t.truncGEπ n) (t.truncGEδLT n)

lemma triangleLTGE_distinguished (n : ℤ) (X : C) :
    (t.triangleLTGE n).obj X ∈ distTriang C :=
  TruncAux.triangleFunctor_obj_distinguished t n X

instance (X : C) (n : ℤ) : t.IsLE ((t.triangleLTGE n).obj X).obj₁ (n - 1) := by
  dsimp
  infer_instance

instance (X : C) (n : ℤ) : t.IsGE ((t.triangleLTGE n).obj X).obj₃ n := by
  dsimp
  infer_instance

end

end TStructure

end Triangulated

end CategoryTheory
