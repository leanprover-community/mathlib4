/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.PathCategory.Basic
/-! # Presentation of the simplex category by generators and relations.

We introduce `SimplexCategoryGenRel` as the category presented by generating
morphisms `δ i : [n] ⟶ [n + 1]` and `σ i : [n + 1] ⟶ [n]` and subject to the
simplicial identities, and we provide induction principles for reasoning about
objects and morphisms in this category.

This category admits a canonical functor `toSimplexCategory` to the usual simplex category.
The fact that this functor is an equivalence will be recorded in a separate file.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section
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
    ((Paths.of FreeSimplexQuiver).map (δ i) ≫ (Paths.of FreeSimplexQuiver).map (δ j.succ))
    ((Paths.of FreeSimplexQuiver).map (δ j) ≫ (Paths.of FreeSimplexQuiver).map (δ i.castSucc))
  | δ_comp_σ_of_le {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ j.castSucc) : homRel
    ((Paths.of FreeSimplexQuiver).map (δ i.castSucc) ≫ (Paths.of FreeSimplexQuiver).map (σ j.succ))
    ((Paths.of FreeSimplexQuiver).map (σ j) ≫ (Paths.of FreeSimplexQuiver).map (δ i))
  | δ_comp_σ_self {n : ℕ} {i : Fin (n + 1)} : homRel
    ((Paths.of FreeSimplexQuiver).map (δ i.castSucc) ≫ (Paths.of FreeSimplexQuiver).map (σ i)) (𝟙 _)
  | δ_comp_σ_succ {n : ℕ} {i : Fin (n + 1)} : homRel
    ((Paths.of FreeSimplexQuiver).map (δ i.succ) ≫ (Paths.of FreeSimplexQuiver).map (σ i)) (𝟙 _)
  | δ_comp_σ_of_gt {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.castSucc < i) : homRel
    ((Paths.of FreeSimplexQuiver).map (δ i.succ) ≫ (Paths.of FreeSimplexQuiver).map (σ j.castSucc))
    ((Paths.of FreeSimplexQuiver).map (σ j) ≫ (Paths.of FreeSimplexQuiver).map (δ i))
  | σ_comp_σ {n : ℕ} {i j : Fin (n + 1)} (H : i ≤ j) : homRel
    ((Paths.of FreeSimplexQuiver).map (σ i.castSucc) ≫ (Paths.of FreeSimplexQuiver).map (σ j))
    ((Paths.of FreeSimplexQuiver).map (σ j.succ) ≫ (Paths.of FreeSimplexQuiver).map (σ i))

end FreeSimplexQuiver

/-- SimplexCategory is the category presented by generators and relation by the simplicial
identities. -/
def SimplexCategoryGenRel := Quotient FreeSimplexQuiver.homRel
  deriving Category

/-- `SimplexCategoryGenRel.mk` is the main constructor for objects of `SimplexCategoryGenRel`. -/
def SimplexCategoryGenRel.mk (n : ℕ) : SimplexCategoryGenRel where
  as := (Paths.of FreeSimplexQuiver).obj n

namespace SimplexCategoryGenRel

/-- `SimplexCategoryGenRel.δ i` is the `i`-th face map `.mk n ⟶ .mk (n + 1)`. -/
abbrev δ {n : ℕ} (i : Fin (n + 2)) : mk n ⟶ mk (n + 1) :=
  (Quotient.functor FreeSimplexQuiver.homRel).map <| (Paths.of FreeSimplexQuiver).map (.δ i)

/-- `SimplexCategoryGenRel.σ i` is the `i`-th degeneracy map `.mk (n + 1) ⟶ .mk n`. -/
abbrev σ {n : ℕ} (i : Fin (n + 1)) : mk (n + 1) ⟶ mk n :=
  (Quotient.functor FreeSimplexQuiver.homRel).map <| (Paths.of FreeSimplexQuiver).map (.σ i)

/-- The length of an object of `SimplexCategoryGenRel`. -/
def len (x : SimplexCategoryGenRel) : ℕ := by rcases x with ⟨n⟩; exact n

@[simp]
lemma mk_len (n : ℕ) : len (mk n) = n := rfl

section InductionPrinciples

/-- A morphism is called a face if it is a `δ i` for some `i : Fin (n + 2)`. -/
inductive faces : MorphismProperty SimplexCategoryGenRel
  | δ {n : ℕ} (i : Fin (n + 2)) : faces (δ i)

/-- A morphism is called a degeneracy if it is a `σ i` for some `i : Fin (n + 1)`. -/
inductive degeneracies : MorphismProperty SimplexCategoryGenRel
  | σ {n : ℕ} (i : Fin (n + 1)) : degeneracies (σ i)

/-- A morphism is a generator if it is either a face or a degeneracy. -/
abbrev generators := faces ⊔ degeneracies

namespace generators

lemma δ {n : ℕ} (i : Fin (n + 2)) : generators (δ i) := le_sup_left (a := faces) _ (.δ i)

lemma σ {n : ℕ} (i : Fin (n + 1)) : generators (σ i) := le_sup_right (a := faces) _ (.σ i)

end generators

/-- A property is true for every morphism iff it holds for generators and is multiplicative. -/
lemma multiplicativeClosure_isGenerator_eq_top : generators.multiplicativeClosure = ⊤ := by
  apply le_antisymm (by simp)
  rintro x y f -
  induction f using CategoryTheory.Quotient.induction with | _ f
  induction f using Paths.induction with
  | id => exact generators.multiplicativeClosure.id_mem _
  | comp _ k h =>
    cases k
    · exact generators.multiplicativeClosure.comp_mem _ _ h <| .of _ <| .δ _
    · exact generators.multiplicativeClosure.comp_mem _ _ h <| .of _ <| .σ _

/-- An unrolled version of the induction principle obtained in the previous lemma. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
lemma hom_induction (P : MorphismProperty SimplexCategoryGenRel)
    (id : ∀ {n : ℕ}, P (𝟙 (mk n)))
    (comp_δ : ∀ {n m : ℕ} (u : mk n ⟶ mk m) (i : Fin (m + 2)), P u → P (u ≫ δ i))
    (comp_σ : ∀ {n m : ℕ} (u : mk n ⟶ mk (m + 1)) (i : Fin (m + 1)), P u → P (u ≫ σ i))
    {a b : SimplexCategoryGenRel} (f : a ⟶ b) :
    P f :=
  by
  suffices generators.multiplicativeClosure ≤ P by
    rw [multiplicativeClosure_isGenerator_eq_top, top_le_iff] at this
    rw [this]
    apply MorphismProperty.top_apply
  intro _ _ f hf
  induction hf with
  | of f h =>
    rcases h with ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩
    · simpa using (comp_δ (𝟙 _) i id)
    · simpa using (comp_σ (𝟙 _) i id)
  | id n => exact id
  | comp_of f g hf hg hrec =>
    rcases hg with ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩
    · simpa using (comp_δ f i hrec)
    · simpa using (comp_σ f i hrec)

/-- An induction principle for reasoning about morphisms in SimplexCategoryGenRel, where we compose
with generators on the right. -/
lemma hom_induction' (P : MorphismProperty SimplexCategoryGenRel)
    (id : ∀ {n : ℕ}, P (𝟙 (mk n)))
    (δ_comp : ∀ {n m : ℕ} (u : mk (m + 1) ⟶ mk n)
      (i : Fin (m + 2)), P u → P (δ i ≫ u))
    (σ_comp : ∀ {n m : ℕ} (u : mk m ⟶ mk n)
      (i : Fin (m + 1)), P u → P (σ i ≫ u)) {a b : SimplexCategoryGenRel} (f : a ⟶ b) :
    P f := by
  suffices generators.multiplicativeClosure' ≤ P by
    rw [← MorphismProperty.multiplicativeClosure_eq_multiplicativeClosure',
      multiplicativeClosure_isGenerator_eq_top, top_le_iff] at this
    rw [this]
    apply MorphismProperty.top_apply
  intro _ _ f hf
  induction hf with
  | of f h =>
    rcases h with ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩
    · simpa using (δ_comp (𝟙 _) i id)
    · simpa using (σ_comp (𝟙 _) i id)
  | id n => exact id
  | of_comp f g hf hg hrec =>
    rcases hf with ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩
    · simpa using (δ_comp g i hrec)
    · simpa using (σ_comp g i hrec)

/-- An induction principle for reasoning about objects in `SimplexCategoryGenRel`. This should be
used instead of identifying an object with `mk` of its `len`. -/
@[elab_as_elim, cases_eliminator]
protected def rec {P : SimplexCategoryGenRel → Sort*}
    (H : ∀ n : ℕ, P (.mk n)) :
    ∀ x : SimplexCategoryGenRel, P x := by
  intro x
  exact H x.len

/-- A basic `ext` lemma for objects of `SimplexCategoryGenRel`. -/
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
    δ ⟨i, hi⟩ ≫ δ ⟨j + 1, by lia⟩ = δ ⟨j, hj⟩ ≫ δ ⟨i, by lia⟩ :=
  δ_comp_δ (n := n) (i := ⟨i, by lia⟩) (j := ⟨j, by lia⟩) (by simpa)

/-- A version of σ_comp_σ with indices in ℕ satisfying relevant inequalities. -/
lemma σ_comp_σ_nat {n} (i j : ℕ) (hi : i < n + 1) (hj : j < n + 1) (H : i ≤ j) :
    σ ⟨i, by lia⟩ ≫ σ ⟨j, hj⟩ = σ ⟨j + 1, by lia⟩ ≫ σ ⟨i, hi⟩ :=
  σ_comp_σ (n := n) (i := ⟨i, by lia⟩) (j := ⟨j, by lia⟩) (by simpa)

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
