/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# `κ`-filtered categories and `κ`-directed poset

-/

universe w

lemma hasCardinalLT_of_finite
    (X : Type*) [Finite X] (κ : Cardinal) (hκ : Cardinal.aleph0 ≤ κ) :
    HasCardinalLT X κ := by
  exact HasCardinalLT.of_le (by rwa [hasCardinalLT_aleph0_iff]) hκ

lemma hasCardinalLT_punit (κ : Cardinal) (hκ : Cardinal.aleph0 ≤ κ) :
    HasCardinalLT PUnit κ :=
  hasCardinalLT_of_finite _ _ hκ

namespace CategoryTheory

namespace IsCardinalFiltered

variable (J : Type w) [SmallCategory J] (κ : Cardinal.{w})

namespace ExistsDirected

@[ext]
structure PreDiagram where
  W : MorphismProperty J
  P : ObjectProperty J
  src {i j : J} {f : i ⟶ j} : W f → P i
  tgt {i j : J} {f : i ⟶ j} : W f → P j
  hW : HasCardinalLT W.toSet κ
  hP : HasCardinalLT (Subtype P) κ

namespace PreDiagram

variable {J κ}

structure Terminal (D : PreDiagram J κ) (e : J) where
  prop_id : D.W (𝟙 e)
  lift {j : J} (hj : D.P j) : j ⟶ e
  hlift {j : J} (hj : D.P j) : D.W (lift hj)
  uniq {j : J} (hj : D.P j) {φ : j ⟶ e} (hφ : D.W φ) : lift hj = φ
  comm {i j : J} (f : i ⟶ j) (hf : D.W f) : f ≫ lift (D.tgt hf) = lift (D.src hf)

namespace Terminal

attribute [reassoc] Terminal.comm

variable {D : PreDiagram J κ} {e : J}

lemma prop (h : D.Terminal e) : D.P e := D.src (h.prop_id)

@[simp]
lemma lift_self (h : D.Terminal e) : h.lift h.prop = 𝟙 e := h.uniq _ h.prop_id

instance : Subsingleton (D.Terminal e) where
  allEq h₁ h₂ := by
    have : @h₁.lift = @h₂.lift := by
      ext j hj
      exact h₁.uniq hj (h₂.hlift hj)
    cases h₁
    cases h₂
    aesop

end Terminal

end PreDiagram

structure Diagram extends PreDiagram J κ where
  e : J
  terminal : toPreDiagram.Terminal e
  uniq_terminal (j : J) (hj : toPreDiagram.Terminal j) : j = e

@[ext]
lemma Diagram.ext {D₁ D₂ : Diagram J κ} (hW : D₁.W = D₂.W) (hP : D₁.P = D₂.P) : D₁ = D₂ := by
  obtain ⟨D₁, e, h₁, h₁'⟩ := D₁
  obtain ⟨D₂, e', h₂, h₂'⟩ := D₂
  obtain rfl : D₁ = D₂ := by aesop
  obtain rfl : e = e' := h₂' _ h₁
  obtain rfl : h₁ = h₂ := by subsingleton
  rfl

instance : PartialOrder (Diagram J κ) where
  le D₁ D₂ := D₁.W ≤ D₂.W ∧ D₁.P ≤ D₂.P
  le_refl _ := ⟨by rfl, by rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ := by
    ext : 1
    · exact le_antisymm h₁.1 h₂.1
    · exact le_antisymm h₁.2 h₂.2

section

variable {J κ}

def functorMap {D₁ D₂ : Diagram J κ} (h : D₁ ≤ D₂) : D₁.e ⟶ D₂.e :=
  D₂.terminal.lift (h.2 _ D₁.terminal.prop)

@[simp]
lemma functorMap_id (D : Diagram J κ) : functorMap (le_refl D) = 𝟙 D.e := by
  simp [functorMap]

@[reassoc (attr := simp)]
lemma functorMap_comp {D₁ D₂ D₃ : Diagram J κ} (h₁₂ : D₁ ≤ D₂) (h₂₃ : D₂ ≤ D₃) :
    functorMap h₁₂ ≫ functorMap h₂₃ = functorMap (h₁₂.trans h₂₃) :=
  D₃.terminal.comm _ (h₂₃.1 _ (D₂.terminal.hlift _))

end

@[simps]
def functor : Diagram J κ ⥤ J where
  obj D := D.e
  map h := functorMap (leOfHom h)

variable [Fact κ.IsRegular]

def PreDiagram.single (j : J) : PreDiagram J κ where
  W := .ofHoms (fun (_ : Unit) ↦ 𝟙 j)
  P := .ofObj (fun (_ : Unit) ↦ j)
  src := by rintro _ _ _ ⟨⟩; exact ⟨⟨⟩⟩
  tgt := by rintro _ _ _ ⟨⟩; exact ⟨⟨⟩⟩
  hW :=
    (hasCardinalLT_punit κ (Cardinal.IsRegular.aleph0_le Fact.out)).of_surjective
        (f := fun (_ : Unit) ↦ ⟨Arrow.mk (𝟙 j), ⟨⟨⟩⟩⟩) (by
      rintro ⟨f, hf⟩
      refine ⟨⟨⟩, ?_⟩
      ext
      exact ((MorphismProperty.ofHoms_iff _ _).1
        ((MorphismProperty.arrow_mk_mem_toSet_iff _ _).1 hf)).choose_spec.symm)
  hP :=
    (hasCardinalLT_punit κ (Cardinal.IsRegular.aleph0_le Fact.out)).of_surjective
      (f := fun (_ : Unit) ↦ ⟨j, by simp⟩) (fun ⟨k, hk⟩ ↦ ⟨⟨⟩, by aesop⟩)

variable (hJ : ∀ (e : J), (∀ (j : J), Nonempty (j ⟶ e)) → False)

end ExistsDirected

end IsCardinalFiltered

end CategoryTheory
