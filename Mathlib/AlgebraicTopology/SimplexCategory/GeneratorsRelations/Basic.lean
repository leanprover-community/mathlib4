/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.AlgebraicTopology.SimplexCategory
import Mathlib.CategoryTheory.PathCategory.Basic
/-! # Presentation of the simplex category by generator and relations.

We introduce `SimplexCategoryGenRel` as the category presented by generating
morphisms `δ i : [n] ⟶ [n + 1]` and `σ i : [n + 1] ⟶ [n]` and subject to the
simplicial identities, and we provide induction principles for reasoning about
objects and morphisms in this category.

This category admits a canonical functor `toSimplexCategory` to the usual simplex category.
The fact that this functor is an equivalence will be recorded in a separate file.
-/
open CategoryTheory

/-- The objects of the free simplex quiver are the natural numbers. -/
def FreeSimplexQuiver := ℕ

/-- Making an object of `FreeSimplexQuiver` out of a natural number. -/
def FreeSimplexQuiver.mk (n : ℕ) : FreeSimplexQuiver := n

/-- Getting back the natural number from the objects. -/
def FreeSimplexQuiver.len (x : FreeSimplexQuiver) : ℕ := x

namespace FreeSimplexQuiver

/-- A morphism in `FreeSimplexQuiver` is either a face map (`δ`) or a degeneracy map (`σ`). -/
inductive Hom : FreeSimplexQuiver → FreeSimplexQuiver → Type
  | δ {n : ℕ} (i : Fin (n + 2)) : Hom (.mk n) (.mk (n + 1))
  | σ {n : ℕ} (i : Fin (n + 1)) : Hom (.mk (n + 1)) (.mk n)

instance quiv : Quiver FreeSimplexQuiver where
  Hom := FreeSimplexQuiver.Hom

/-- `FreeSimplexQuiver.δ i` represents the `i`-th face map `.mk n ⟶ .mk (n + 1)`. -/
abbrev δ {n : ℕ} (i : Fin (n + 2)) : FreeSimplexQuiver.mk n ⟶ .mk (n + 1) :=
  FreeSimplexQuiver.Hom.δ i

/-- `FreeSimplexQuiver.σ i` represents `i`-th degeneracy map `.mk (n + 1) ⟶ .mk n`. -/
abbrev σ {n : ℕ} (i : Fin (n + 1)) : FreeSimplexQuiver.mk (n + 1) ⟶ .mk n :=
  FreeSimplexQuiver.Hom.σ i

/-- `FreeSimplexQuiver.homRel` is the relation on morphisms freely generated on the
five simplicial identities. -/
inductive homRel : HomRel (Paths FreeSimplexQuiver)
  | δ_comp_δ {n : ℕ} {i j : Fin (n + 2)} (H : i ≤ j) : homRel
    (Paths.of.map (δ i) ≫ Paths.of.map (δ j.succ))
    (Paths.of.map (δ j) ≫ Paths.of.map (δ i.castSucc))
  | δ_comp_σ_of_le {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ j.castSucc) : homRel
    (Paths.of.map (δ i.castSucc) ≫ Paths.of.map (σ j.succ))
    (Paths.of.map (σ j) ≫ Paths.of.map (δ i))
  | δ_comp_σ_self {n : ℕ} {i : Fin (n + 1)} : homRel
    (Paths.of.map (δ i.castSucc) ≫ Paths.of.map (σ i)) (𝟙 _)
  | δ_comp_σ_succ {n : ℕ} {i : Fin (n + 1)} : homRel
    (Paths.of.map (δ i.succ) ≫ Paths.of.map (σ i)) (𝟙 _)
  | δ_comp_σ_of_gt {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.castSucc < i) : homRel
    (Paths.of.map (δ i.succ) ≫ Paths.of.map (σ j.castSucc))
    (Paths.of.map (σ j) ≫ Paths.of.map (δ i))
  | σ_comp_σ {n : ℕ} {i j : Fin (n + 1)} (H : i ≤ j) : homRel
    (Paths.of.map (σ i.castSucc) ≫ Paths.of.map (σ j))
    (Paths.of.map (σ j.succ) ≫ Paths.of.map (σ i))

end FreeSimplexQuiver

/-- SimplexCategory is the category presented by generators and relation by the simplicial
identities.-/
def SimplexCategoryGenRel := Quotient FreeSimplexQuiver.homRel
  deriving Category

/-- `SimplexCategoryGenRel.mk` is the main constructor for objects of `SimplexCategoryGenRel`. -/
def SimplexCategoryGenRel.mk (n : ℕ) : SimplexCategoryGenRel where
  as := Paths.of.obj n

namespace SimplexCategoryGenRel

/-- `SimplexCategoryGenRel.δ i` is the `i`-th face map `.mk n ⟶ .mk (n + 1)`. -/
abbrev δ {n : ℕ} (i : Fin (n + 2)) : mk n ⟶ mk (n + 1) :=
  (Quotient.functor FreeSimplexQuiver.homRel).map <| Paths.of.map (.δ i)

/-- `SimplexCategoryGenRel.σ i` is the `i`-th degeneracy map `.mk (n + 1) ⟶ .mk n`. -/
abbrev σ {n : ℕ} (i : Fin (n + 1)) : mk (n + 1) ⟶ mk n :=
  (Quotient.functor FreeSimplexQuiver.homRel).map <| Paths.of.map (.σ i)

/-- The length of an object of `SimplexCategoryGenRel`. -/
def len (x : SimplexCategoryGenRel) : ℕ := by rcases x with ⟨n⟩; exact n

@[simp]
lemma mk_len (n : ℕ) : len (mk n) = n := rfl

section InductionPrinciples

/-- An induction principle for reasonning about morphisms properties in SimplexCategoryGenRel. -/
lemma hom_induction (P : MorphismProperty SimplexCategoryGenRel)
    (hi : ∀ {n : ℕ}, P (𝟙 (mk n)))
    (hc₁ : ∀ {n m : ℕ} (u : mk n ⟶ mk m) (i : Fin (m + 2)), P u → P (u ≫ δ i))
    (hc₂ : ∀ {n m : ℕ} (u : mk n ⟶ mk (m + 1)) (i : Fin (m + 1)), P u → P (u ≫ σ i))
    {a b : SimplexCategoryGenRel} (f : a ⟶ b) :
    P f := by
  apply CategoryTheory.Quotient.induction (P := (fun f ↦ P f))
  apply Paths.induction
  · exact hi
  · rintro _ _ _ _ ⟨⟩
    · exact hc₁ _ _
    · exact hc₂ _ _

/-- An induction principle for reasonning about morphisms in SimplexCategoryGenRel, where we compose
with generators on the right. -/
lemma hom_induction' (P : MorphismProperty SimplexCategoryGenRel)
    (hi : ∀ {n : ℕ}, P (𝟙 (mk n)))
    (hc₁ : ∀ {n m : ℕ} (u : mk (m + 1) ⟶ mk n)
      (i : Fin (m + 2)), P u → P (δ i ≫ u))
    (hc₂ : ∀ {n m : ℕ} (u : mk m ⟶ mk n)
      (i : Fin (m + 1)), P u → P (σ i ≫ u )) {a b : SimplexCategoryGenRel} (f : a ⟶ b) :
    P f := by
  apply CategoryTheory.Quotient.induction (P := (fun f ↦ P f))
  apply Paths.induction'
  · exact hi
  · rintro _ _ _ ⟨⟩ _
    · exact hc₁ _ _
    · exact hc₂ _ _

/-- An induction principle for reasonning about morphisms properties in SimplexCategoryGenRel. -/
lemma morphismProperty_eq_top (P : MorphismProperty SimplexCategoryGenRel)
    (hi : ∀ {n : ℕ}, P (𝟙 (.mk n)))
    (hc₁ : ∀ {n m : ℕ} (u : .mk n ⟶ .mk m) (i : Fin (m + 2)),
      P u → P (u ≫ δ i))
    (hc₂ : ∀ {n m : ℕ} (u : .mk n ⟶ .mk (m + 1))
      (i : Fin (m + 1)), P u → P (u ≫ σ i)) :
    P = ⊤ := by
  ext; constructor
  · simp
  · intro _
    apply hom_induction <;> assumption

/-- An induction principle for reasonning about morphisms properties in SimplexCategoryGenRel,
where we compose with generators on the right. -/
lemma morphismProperty_eq_top' (P : MorphismProperty SimplexCategoryGenRel)
    (hi : ∀ {n : ℕ}, P (𝟙 (.mk n)))
    (hc₁ : ∀ {n m : ℕ} (u : .mk (m + 1) ⟶ .mk n) (i : Fin (m + 2)), P u → (P (δ i ≫ u)))
    (hc₂ : ∀ {n m : ℕ} (u : .mk m ⟶ .mk n) (i : Fin (m + 1)), P u → (P (σ i ≫ u ))) :
    P = ⊤ := by
  ext; constructor
  · simp
  · intro _
    apply hom_induction' <;> assumption

/-- An induction principle for reasonning about objects in SimplexCategoryGenRel. This should be
used instead of identifying an object with `mk` of its len.-/
@[elab_as_elim, cases_eliminator]
protected def rec {P : SimplexCategoryGenRel → Sort*}
    (H : ∀ n : ℕ, P (.mk n)) :
    ∀ x : SimplexCategoryGenRel, P x := by
  intro x
  exact H x.len

/-- A basic ext lemma for objects of SimplexCategoryGenRel --/
@[ext]
lemma ext {x y : SimplexCategoryGenRel} (h : x.len = y.len) : x = y := by
  cases x
  cases y
  simp only [mk_len] at h
  congr

end InductionPrinciples

section SimplicialIdentities

@[reassoc]
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    δ i ≫ δ j.succ = δ j ≫ δ i.castSucc := by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_δ H

@[reassoc]
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ j.castSucc) :
    δ i.castSucc ≫ σ j.succ = σ j ≫ δ i := by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_σ_of_le H

@[reassoc]
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} :
    δ i.castSucc ≫ σ i = 𝟙 (mk n) := by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_σ_self

@[reassoc]
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : δ i.succ ≫ σ i = 𝟙 (mk n) := by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_σ_succ

@[reassoc]
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.castSucc < i) :
    δ i.succ ≫ σ j.castSucc = σ j ≫ δ i := by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_σ_of_gt H

@[reassoc]
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    σ i.castSucc ≫ σ j = σ j.succ ≫ σ i := by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.σ_comp_σ H

/-- A version of δ_comp_δ with indices in ℕ satisfying relevant inequalities. -/
lemma δ_comp_δ_nat {n} (i j : ℕ) (hi : i < n + 2) (hj : j < n + 2) (H : i ≤ j) :
    δ ⟨i, hi⟩ ≫ δ ⟨j + 1, by omega⟩ = δ ⟨j, hj⟩ ≫ δ ⟨i, by omega⟩ :=
  δ_comp_δ (n := n) (i := ⟨i, by omega⟩) (j := ⟨j, by omega⟩) (by simpa)

/-- A version of σ_comp_σ with indices in ℕ satisfying relevant inequalities. -/
lemma σ_comp_σ_nat {n} (i j : ℕ) (hi : i < n + 1) (hj : j < n + 1) (H : i ≤ j) :
    σ ⟨i, by omega⟩ ≫ σ ⟨j, hj⟩ = σ ⟨j + 1, by omega⟩ ≫ σ ⟨i, hi⟩ :=
  σ_comp_σ (n := n) (i := ⟨i, by omega⟩) (j := ⟨j, by omega⟩) (by simpa)

end SimplicialIdentities

/-- The canonical functor from `SimplexCategoryGenRel` to SimplexCategory, which exists as the
simplicial identities hold in `SimplexCategory`. -/
def toSimplexCategory : SimplexCategoryGenRel ⥤ SimplexCategory :=
  CategoryTheory.Quotient.lift _
    (Paths.lift
      { obj := .mk
        map f := match f with
          | FreeSimplexQuiver.Hom.δ i => SimplexCategory.δ i
          | FreeSimplexQuiver.Hom.σ i => SimplexCategory.σ i })
    (fun _ _ _ _ h ↦ match h with
      | .δ_comp_δ H => SimplexCategory.δ_comp_δ H
      | .δ_comp_σ_of_le H => SimplexCategory.δ_comp_σ_of_le H
      | .δ_comp_σ_self => SimplexCategory.δ_comp_σ_self
      | .δ_comp_σ_succ => SimplexCategory.δ_comp_σ_succ
      | .δ_comp_σ_of_gt H => SimplexCategory.δ_comp_σ_of_gt H
      | .σ_comp_σ H => SimplexCategory.σ_comp_σ H)

@[simp]
lemma toSimplexCategory_obj_mk (n : ℕ) : toSimplexCategory.obj (mk n) = .mk n := rfl

@[simp]
lemma toSimplexCategory_map_δ {n : ℕ} (i : Fin (n + 2)) :
    toSimplexCategory.map (δ i) = SimplexCategory.δ i := rfl

@[simp]
lemma toSimplexCategory_map_σ {n : ℕ} (i : Fin (n + 1)) :
    toSimplexCategory.map (σ i) = SimplexCategory.σ i := rfl

@[simp]
lemma toSimplexCategory_len {x : SimplexCategoryGenRel} : (toSimplexCategory.obj x).len = x.len :=
  rfl

end SimplexCategoryGenRel
