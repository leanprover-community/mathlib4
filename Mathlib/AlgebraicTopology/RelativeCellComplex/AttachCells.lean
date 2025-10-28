/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Attaching cells

Given a family of morphisms `g a : A a ⟶ B a` and a morphism `f : X₁ ⟶ X₂`,
we introduce a structure `AttachCells g f` which expresses that `X₂`
is obtained from `X₁` by attaching cells of the form `g a`. It means that
there is a pushout diagram of the form
```
⨿ i, A (π i) -----> X₁
  |                 |f
  v                 v
⨿ i, B (π i) -----> X₂
```
In other words, the morphism `f` is a pushout of coproducts of morphisms
of the form `g a : A a ⟶ B a`, see `nonempty_attachCells_iff`.

See the file `Mathlib/AlgebraicTopology/RelativeCellComplex/Basic.lean` for transfinite compositions
of morphisms `f` with `AttachCells g f` structures.

-/

universe w' w t t' v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]
  {α : Type t} {A B : α → C} (g : ∀ a, A a ⟶ B a)
  {X₁ X₂ : C} (f : X₁ ⟶ X₂)

/-- Given a family of morphisms `g a : A a ⟶ B a` and a morphism `f : X₁ ⟶ X₂`,
this structure contains the data and properties which expresses that `X₂`
is obtained from `X₁` by attaching cells of the form `g a`. -/
structure AttachCells where
  /-- the index type of the cells -/
  ι : Type w
  /-- for each `i : ι`, we shall attach a cell given by the morphism `g (π i)`. -/
  π : ι → α
  /-- a colimit cofan which gives the coproduct of the object `A (π i)` -/
  cofan₁ : Cofan (fun i ↦ A (π i))
  /-- a colimit cofan which gives the coproduct of the object `B (π i)` -/
  cofan₂ : Cofan (fun i ↦ B (π i))
  /-- `cofan₁` is colimit -/
  isColimit₁ : IsColimit cofan₁
  /-- `cofan₂` is colimit -/
  isColimit₂ : IsColimit cofan₂
  /-- the coproduct of the maps `g (π i) : A (π i) ⟶ B (π i)` for all `i : ι`. -/
  m : cofan₁.pt ⟶ cofan₂.pt
  hm (i : ι) : cofan₁.inj i ≫ m = g (π i) ≫ cofan₂.inj i := by cat_disch
  /-- the top morphism of the pushout square -/
  g₁ : cofan₁.pt ⟶ X₁
  /-- the bottom morphism of the pushout square -/
  g₂ : cofan₂.pt ⟶ X₂
  isPushout : IsPushout g₁ m f g₂

namespace AttachCells

open MorphismProperty

attribute [reassoc (attr := simp)] hm

variable {g f} (c : AttachCells.{w} g f)

include c

lemma pushouts_coproducts : (coproducts.{w} (ofHoms g)).pushouts f := by
  refine ⟨_, _, _, _, _, ?_, c.isPushout⟩
  have : c.m = c.isColimit₁.desc
      (Cocone.mk _ (Discrete.natTrans (fun ⟨i⟩ ↦ by exact g (c.π i)) ≫ c.cofan₂.ι)) :=
    c.isColimit₁.hom_ext (fun ⟨i⟩ ↦ by rw [IsColimit.fac]; exact c.hm i)
  rw [this, coproducts_iff]
  exact ⟨c.ι, ⟨_, _, _, _, c.isColimit₁, c.isColimit₂, _, fun i ↦ ⟨_⟩⟩⟩

/-- The inclusion of a cell. -/
def cell (i : c.ι) : B (c.π i) ⟶ X₂ := c.cofan₂.inj i ≫ c.g₂

@[reassoc]
lemma cell_def (i : c.ι) : c.cell i = c.cofan₂.inj i ≫ c.g₂ := rfl

lemma hom_ext {Z : C} {φ φ' : X₂ ⟶ Z}
    (h₀ : f ≫ φ = f ≫ φ') (h : ∀ i, c.cell i ≫ φ = c.cell i ≫ φ') :
    φ = φ' := by
  apply c.isPushout.hom_ext h₀
  apply Cofan.IsColimit.hom_ext c.isColimit₂
  simpa [cell_def] using h

/-- If `f` and `f'` are isomorphic morphisms and the target of `f`
is obtained by attaching cells to the source of `f`,
then the same holds for `f'`. -/
@[simps]
def ofArrowIso {Y₁ Y₂ : C} {f' : Y₁ ⟶ Y₂} (e : Arrow.mk f ≅ Arrow.mk f') :
    AttachCells.{w} g f' where
  ι := c.ι
  π := c.π
  cofan₁ := c.cofan₁
  cofan₂ := c.cofan₂
  isColimit₁ := c.isColimit₁
  isColimit₂ := c.isColimit₂
  m := c.m
  g₁ := c.g₁ ≫ Arrow.leftFunc.map e.hom
  g₂ := c.g₂ ≫ Arrow.rightFunc.map e.hom
  isPushout :=
    c.isPushout.of_iso (Iso.refl _) (Arrow.leftFunc.mapIso e) (Iso.refl _)
      (Arrow.rightFunc.mapIso e) (by simp) (by simp) (by simp) (by simp)

/-- This definition allows the replacement of the `ι` field of
a `AttachCells g f` structure by an equivalent type. -/
@[simps]
def reindex {ι' : Type w'} (e : ι' ≃ c.ι) :
    AttachCells.{w'} g f where
  ι := ι'
  π i' := c.π (e i')
  cofan₁ := Cofan.mk c.cofan₁.pt (fun i' ↦ c.cofan₁.inj (e i'))
  cofan₂ := Cofan.mk c.cofan₂.pt (fun i' ↦ c.cofan₂.inj (e i'))
  isColimit₁ := IsColimit.whiskerEquivalence (c.isColimit₁) (Discrete.equivalence e)
  isColimit₂ := IsColimit.whiskerEquivalence (c.isColimit₂) (Discrete.equivalence e)
  m := c.m
  g₁ := c.g₁
  g₂ := c.g₂
  hm i' := c.hm (e i')
  isPushout := c.isPushout

section

variable {α' : Type t'} {A' B' : α' → C} (g' : ∀ i', A' i' ⟶ B' i')
  (a : α → α') (ha : ∀ (i : α), Arrow.mk (g i) ≅ Arrow.mk (g' (a i)))

/-- If a family of maps `g` is contained in another family `g'` (up to isomorphisms),
if `f : X₁ ⟶ X₂` is a morphism, and `X₂` is obtained from `X₁` by attaching cells
of the form `g`, then it is also obtained by attaching cells of the form `g'`. -/
def reindexCellTypes : AttachCells g' f where
  ι := c.ι
  π := a ∘ c.π
  cofan₁ := Cofan.mk c.cofan₁.pt
    (fun i ↦ Arrow.leftFunc.map (ha (c.π i)).inv ≫ c.cofan₁.inj i)
  cofan₂ := Cofan.mk c.cofan₂.pt
    (fun i ↦ Arrow.rightFunc.map (ha (c.π i)).inv ≫ c.cofan₂.inj i)
  isColimit₁ := by
    let e : Discrete.functor (fun i ↦ A (c.π i)) ≅
        Discrete.functor (fun i ↦ A' (a (c.π i))) :=
      Discrete.natIso (fun ⟨i⟩ ↦ Arrow.leftFunc.mapIso (ha (c.π i)))
    refine (IsColimit.precomposeHomEquiv e _).1
      (IsColimit.ofIsoColimit c.isColimit₁ (Cofan.ext (Iso.refl _) (fun i ↦ ?_)))
    simp [Cocones.precompose, e, Cofan.inj]
  isColimit₂ := by
    let e : Discrete.functor (fun i ↦ B (c.π i)) ≅
        Discrete.functor (fun i ↦ B' (a (c.π i))) :=
      Discrete.natIso (fun ⟨i⟩ ↦ Arrow.rightFunc.mapIso (ha (c.π i)))
    refine (IsColimit.precomposeHomEquiv e _).1
      (IsColimit.ofIsoColimit c.isColimit₂ (Cofan.ext (Iso.refl _) (fun i ↦ ?_)))
    simp [Cocones.precompose, e, Cofan.inj]
  m := c.m
  g₁ := c.g₁
  g₂ := c.g₂
  isPushout := c.isPushout

end

end AttachCells

open MorphismProperty in
lemma nonempty_attachCells_iff :
    Nonempty (AttachCells.{w} g f) ↔ (coproducts.{w} (ofHoms g)).pushouts f := by
  constructor
  · rintro ⟨c⟩
    exact c.pushouts_coproducts
  · rintro ⟨Y₁, Y₂, m, g₁, g₂, h, sq⟩
    rw [coproducts_iff] at h
    obtain ⟨ι, ⟨F₁, F₂, c₁, c₂, h₁, h₂, φ, hφ⟩⟩ := h
    let π (i : ι) : α := ((ofHoms_iff _ _).1 (hφ ⟨i⟩)).choose
    let e (i : ι) : Arrow.mk (φ.app ⟨i⟩) ≅ Arrow.mk (g (π i)) :=
      eqToIso (((ofHoms_iff _ _).1 (hφ ⟨i⟩)).choose_spec)
    let e₁ (i : ι) : F₁.obj ⟨i⟩ ≅ A (π i) := Arrow.leftFunc.mapIso (e i)
    let e₂ (i : ι) : F₂.obj ⟨i⟩ ≅ B (π i) := Arrow.rightFunc.mapIso (e i)
    exact ⟨{
      ι := ι
      π := π
      cofan₁ := Cofan.mk c₁.pt (fun i ↦ (e₁ i).inv ≫ c₁.ι.app ⟨i⟩)
      cofan₂ := Cofan.mk c₂.pt (fun i ↦ (e₂ i).inv ≫ c₂.ι.app ⟨i⟩)
      isColimit₁ :=
        (IsColimit.precomposeHomEquiv (Discrete.natIso (fun ⟨i⟩ ↦ e₁ i)) _).1
          (IsColimit.ofIsoColimit h₁ (Cocones.ext (Iso.refl _) (by simp)))
      isColimit₂ :=
        (IsColimit.precomposeHomEquiv (Discrete.natIso (fun ⟨i⟩ ↦ e₂ i)) _).1
          (IsColimit.ofIsoColimit h₂ (Cocones.ext (Iso.refl _) (by simp)))
      hm i := by simp [e₁, e₂]
      isPushout := sq, .. }⟩

end HomotopicalAlgebra
