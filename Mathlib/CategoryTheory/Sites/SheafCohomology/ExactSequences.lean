/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Long exact sequence for sheaf cohomology

We obtain the long exact sequence on sheaf cohomology coming from a short exact sequence
of sheaves. We also show it is functorial. In practice, it is often best to work with
cohomology as a Type (the long sequence necessarily takes values in the category `AddCommGrpCat`,
so the objects in it are really `AddCommGrpCat.of (H F n)`). To do this, you can use the lemmas
`CategoryTheory.Sheaf.H.longSequence_exact₁`, `CategoryTheory.Sheaf.H.longSequence_exact₂` and
`CategoryTheory.Sheaf.H.longSequence_exact₃`.

## Main definitions

* `CategoryTheory.Sheaf.H.δ`: Given a short exact sequence of sheaves `S`,
  this is the connecting homomorphism `Hⁿ(S.X₃) ⟶ Hⁿ⁺¹(S.X₁)`.
* `CategoryTheory.Sheaf.H.longSequence`: Given a short exact sequence of sheaves `S`, this
  is the long exact sequence:
  `Hⁿ(S.X₁) ⟶ Hⁿ(S.X₂) ⟶ Hⁿ(S.X₃) ⟶ Hⁿ⁺¹(S.X₁) ⟶ Hⁿ⁺¹(S.X₂) ⟶ Hⁿ⁺¹(S.X₃)`

* `CategoryTheory.Sheaf.H.longSequenceHom`: Given a morphism of short exact sequences of sheaves
  `f : S₁ ⟶ S₂`, this is the induced morphism between their long exact sequences. On each object,
  it is just `CategoryTheory.Sheaf.H.map` applied to the corresponding morphism in `f`. E.g. the
  first morphism is `H.map` applied to `f.τ₁`.
* `CategoryTheory.Sheaf.H.longSequenceFunctor`: This is the functor that sends a short exact
  sequence to its long exact sequence on cohomology and sends morphisms to `longSequenceHom`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe w' w v u

namespace CategoryTheory

open Abelian AddCommGrpCat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace Sheaf

variable [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

variable {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact) (n₀ n₁ : ℕ)
  (h : n₀ + 1 = n₁)

namespace H

/-- Given a short exact sequence of sheaves `S`, this is the connecting homomorphism
`Hⁿ(S.X₃) ⟶ Hⁿ⁺¹(S.X₁)`. -/
noncomputable def δ : H S.X₃ n₀ →+ H S.X₁ n₁ :=
  hS.extClass.postcomp _ h

variable {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂)

set_option backward.isDefEq.respectTransparency false in
theorem δ_naturality (x : H S₁.X₃ n₀) :
    δ h₂ n₀ n₁ h (map f.τ₃ n₀ x) = map f.τ₁ n₁ (δ h₁ n₀ n₁ h x) := by
  delta δ H map
  simp [ShortComplex.ShortExact.extClass_naturality h₁ h₂ f]

/-- This is the long exact sequence:
`Hⁿ(S.X₁) ⟶ Hⁿ(S.X₂) ⟶ Hⁿ(S.X₃) ⟶ Hⁿ⁺¹(S.X₁) ⟶ Hⁿ⁺¹(S.X₂) ⟶ Hⁿ⁺¹(S.X₃)`. -/
noncomputable def longSequence (h : n₀ + 1 = n₁ := by lia) :
    ComposableArrows AddCommGrpCat.{w'} 5 := ComposableArrows.mk₅
  (ofHom (map S.f n₀)) (ofHom (map S.g n₀)) (ofHom (δ hS n₀ n₁ h))
  (ofHom (map S.f n₁)) (ofHom (map S.g n₁))

open ComposableArrows

@[simp]
lemma longSequence_obj₀ : (longSequence hS n₀ n₁ h).obj 0 = of (S.X₁.H n₀) := rfl

@[simp]
lemma longSequence_obj₁ : (longSequence hS n₀ n₁ h).obj 1 = of (S.X₂.H n₀) := rfl

@[simp]
lemma longSequence_obj₂ : (longSequence hS n₀ n₁ h).obj 2 = of (S.X₃.H n₀) := rfl

@[simp]
lemma longSequence_obj₃ : (longSequence hS n₀ n₁ h).obj 3 = of (S.X₁.H n₁) := rfl

@[simp]
lemma longSequence_obj₄ : (longSequence hS n₀ n₁ h).obj 4 = of (S.X₂.H n₁) := rfl

@[simp]
lemma longSequence_obj₅ : (longSequence hS n₀ n₁ h).obj 5 = of (S.X₃.H n₁) := rfl

@[simp]
lemma longSequence_map₀₁ (i : (0 : Fin 6) ⟶ 1) :
    (longSequence hS n₀ n₁ h).map i = ofHom (map S.f n₀) := rfl

@[simp]
lemma longSequence_map₁₂ (i : (1 : Fin 6) ⟶ 2) :
    (longSequence hS n₀ n₁ h).map i = ofHom (map S.g n₀) := rfl

@[simp]
lemma longSequence_map₂₃ (i : (2 : Fin 6) ⟶ 3) :
    (longSequence hS n₀ n₁ h).map i = ofHom (δ hS n₀ n₁ h) := rfl

@[simp]
lemma longSequence_map₃₄ (i : (3 : Fin 6) ⟶ 4) :
    (longSequence hS n₀ n₁ h).map i = ofHom (map S.f n₁) := rfl

@[simp]
lemma longSequence_map₄₅ (i : (4 : Fin 6) ⟶ 5) :
    (longSequence hS n₀ n₁ h).map i = ofHom (map S.g n₁) := rfl

theorem longSequence_exact : (longSequence hS n₀ n₁ h).Exact :=
  Ext.covariantSequence_exact _ hS n₀ n₁ h

/-- The induced homomorphism of long exact equences obtained by applying `H.map` everywhere. -/
noncomputable abbrev longSequenceHom (h : n₀ + 1 = n₁ := by lia) :
    longSequence h₁ n₀ n₁ h ⟶ longSequence h₂ n₀ n₁ h := by
  refine ComposableArrows.homMk₅
    (ofHom (map f.τ₁ n₀))
    (ofHom (map f.τ₂ n₀))
    (ofHom (map f.τ₃ n₀))
    (ofHom (map f.τ₁ n₁))
    (ofHom (map f.τ₂ n₁))
    (ofHom (map f.τ₃ n₁)) ?_ ?_ ?_ ?_ ?_
  any_goals
    dsimp
    ext
    simp [← H.map_comp_apply, f.4, f.5, ← δ_naturality n₀ n₁ h h₁ h₂ f]

@[simp]
lemma longSequenceHom_app₀ :
    (longSequenceHom n₀ n₁ h₁ h₂ f h).app 0 = ofHom (map f.τ₁ n₀) := rfl

@[simp]
lemma longSequenceHom_app₁ :
    (longSequenceHom n₀ n₁ h₁ h₂ f h).app 1 = ofHom (map f.τ₂ n₀) := rfl

@[simp]
lemma longSequenceHom_app₂ :
    (longSequenceHom n₀ n₁ h₁ h₂ f h).app 2 = ofHom (map f.τ₃ n₀) := rfl

@[simp]
lemma longSequenceHom_app₃ :
    (longSequenceHom n₀ n₁ h₁ h₂ f h).app 3 = ofHom (map f.τ₁ n₁) := rfl

@[simp]
lemma longSequenceHom_app₄ :
    (longSequenceHom n₀ n₁ h₁ h₂ f h).app 4 = ofHom (map f.τ₂ n₁) := rfl

@[simp]
lemma longSequenceHom_app₅ :
    (longSequenceHom n₀ n₁ h₁ h₂ f h).app 5 = ofHom (map f.τ₃ n₁) := rfl

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] H.map_comp_apply in
/-- The long exact sequence of cohomology is functorial -/
@[simps]
noncomputable def longSequenceFunctor :
    ObjectProperty.FullSubcategory (ShortComplex.ShortExact (C := (Sheaf J AddCommGrpCat.{w}))) ⥤
      ComposableArrows AddCommGrpCat.{w'} 5 where
  obj S := longSequence S.property n₀ n₁ h
  map {S₁ S₂} f := longSequenceHom n₀ n₁ S₁.property S₂.property f.hom h

lemma longSequence_exact₁' (h : n₀ + 1 = n₁ := by lia) :
    (ShortComplex.mk (ofHom (δ hS n₀ n₁ h)) (ofHom (map S.f n₁))
      ((longSequence_exact hS n₀ n₁ h).zero 2)).Exact :=
  (longSequence_exact hS n₀ n₁ h).exact 2

lemma longSequence_exact₃' (h : n₀ + 1 = n₁ := by lia) :
    (ShortComplex.mk (ofHom (map S.g n₀)) (ofHom (δ hS n₀ n₁ h))
      ((longSequence_exact hS n₀ n₁ h).zero 1)).Exact :=
  (longSequence_exact hS n₀ n₁ h).exact 1

lemma longSequence_exact₂' (n : ℕ) :
    (ShortComplex.mk (ofHom (map S.f n)) (ofHom (map S.g n))
      (((longSequence_exact hS n _ rfl).sc 0).zero)).Exact :=
  (longSequence_exact hS n _ rfl).exact 0

include hS in
lemma longSequence_exact₂ (n : ℕ) (x₂ : H S.X₂ n) (hx₂ : map S.g n x₂ = 0) :
    ∃ x₁ : H S.X₁ n, map S.f n x₁ = x₂ :=
  Ext.covariant_sequence_exact₂ _ hS _ hx₂

lemma longSequence_exact₃ (x₃ : H S.X₃ n₀)
    (hx₃ : δ hS n₀ n₁ h x₃ = 0) :
    ∃ x₂ : H S.X₂ n₀, map S.g n₀ x₂ = x₃ :=
  Ext.covariant_sequence_exact₃ _ _ _ h hx₃

lemma longSequence_exact₁ (x₁ : H S.X₁ n₁)
    (hx₁ : map S.f n₁ x₁ = 0) :
    ∃ x₃ : H S.X₃ n₀, δ hS n₀ n₁ h x₃ = x₁ :=
  Ext.covariant_sequence_exact₁ _ _ _ hx₁ h

variable {T : C} (hT : Limits.IsTerminal T)

open Opposite

lemma longSequence_equiv₀_exact₃ (x₃ : S.X₃.obj.obj (op T))
    (hx₃ : (δ hS 0 1 rfl) ((equiv₀ S.X₃ hT).symm x₃) = 0) :
    ∃ x₂ : S.X₂.obj.obj (op T), S.g.hom.app (op T) x₂ = x₃ := by
  obtain ⟨x₂', hx₂'⟩ := longSequence_exact₃ hS 0 _ _ ((equiv₀ S.X₃ hT).symm x₃) hx₃
  use equiv₀ S.X₂ hT x₂'
  simp [equiv₀_naturality, hx₂']

end H

end Sheaf

end CategoryTheory
