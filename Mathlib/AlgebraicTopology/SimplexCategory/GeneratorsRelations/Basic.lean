/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.PathCategory.MorphismProperty
import Mathlib.AlgebraicTopology.SimplexCategory
/-! # Presentation of the simplex category by generator and relations.

We introduce `SimplexCategoryGenRel` as a the category presented by generating
morphisms `δ i : [n] ⟶ [n + 1]` and `σ i : [n + 1] ⟶ [n]` and subject to the
simplicial identities, and we provide induction principles for reasoning about
objects and morphisms in this category.

This category admits a canonical functor `toSimplexCategory` to the usual simplex category.
The fact that this functor is an equivalence will be recorded in a separate file.
-/
namespace AlgebraicTopology.SimplexCategory

open CategoryTheory

/-- The objects of the free simplex quiver are the natural numbers. -/
def FreeSimplexQuiver := ℕ

/-- Making an object of `FreeSimplexQuiver` out of a natural number. -/
def FreeSimplexQuiver.mk (n : ℕ) : FreeSimplexQuiver := n

/-- Getting back the natural number from the objects. -/
def FreeSimplexQuiver.len (x : FreeSimplexQuiver) : ℕ := x

namespace FreeSimplexQuiver

/-- A morphisms in `FreeSimplexQuiver` is either a face map (`δ`) or a degeneracy map (`σ`). -/
inductive Hom : FreeSimplexQuiver → FreeSimplexQuiver → Type
  | δ {n : ℕ} (i : Fin (n + 2)) : Hom (.mk n) (.mk (n + 1))
  | σ {n : ℕ} (i : Fin (n + 1)) : Hom (.mk (n + 1)) (.mk n)

instance Quiv : Quiver FreeSimplexQuiver where
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
  | simplicial1 {n : ℕ} {i j : Fin (n + 2)} (H : i ≤ j) : homRel
    (Paths.of.map (δ i) ≫ Paths.of.map (δ j.succ))
    (Paths.of.map (δ j) ≫ Paths.of.map (δ i.castSucc))
  | simplicial2 {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ j.castSucc) : homRel
    (Paths.of.map (δ i.castSucc) ≫ Paths.of.map (σ j.succ))
    (Paths.of.map (σ j) ≫ Paths.of.map (δ i))
  | simplicial3₁ {n : ℕ} {i : Fin (n + 1)} : homRel
    (Paths.of.map (δ i.castSucc) ≫ Paths.of.map (σ i)) (𝟙 _)
  | simplicial3₂ {n : ℕ} {i : Fin (n + 1)} : homRel
    (Paths.of.map (δ i.succ) ≫ Paths.of.map (σ i)) (𝟙 _)
  | simplicial4 {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.castSucc < i) : homRel
    (Paths.of.map (δ i.succ) ≫ Paths.of.map (σ j.castSucc))
    (Paths.of.map (σ j) ≫ Paths.of.map (δ i))
  | simplicial5 {n : ℕ} {i j : Fin (n + 1)} (H : i ≤ j) : homRel
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
abbrev δ {n : ℕ} (i : Fin (n + 2)) : (SimplexCategoryGenRel.mk n) ⟶ .mk (n + 1) :=
  (Quotient.functor FreeSimplexQuiver.homRel).map <| Paths.of.map (.δ i)

/-- `SimplexCategoryGenRel.σ i` is the `i`-th degeneracy map `.mk (n + 1) ⟶ .mk n`. -/
abbrev σ {n : ℕ} (i : Fin (n + 1)) :
    (SimplexCategoryGenRel.mk (n + 1)) ⟶ (SimplexCategoryGenRel.mk n) :=
  (Quotient.functor FreeSimplexQuiver.homRel).map <| Paths.of.map (.σ i)

/-- The length of an object of `SimplexCategoryGenRel`. -/
def len (x : SimplexCategoryGenRel) : ℕ := by rcases x with ⟨n⟩; exact n

@[simp]
lemma mk_len (n : ℕ) : (len (mk n)) = n := rfl

section InductionPrinciples

/-- An induction principle for reasonning about morphisms properties in SimplexCategoryGenRel. -/
lemma hom_induction (P : MorphismProperty SimplexCategoryGenRel)
    (hi : ∀ {n : ℕ}, P (𝟙 (.mk n)))
    (hc₁ : ∀ {n m : ℕ} (u : .mk n ⟶ .mk m) (i : Fin (m + 2)), P u → P (u ≫ δ i))
    (hc₂ : ∀ {n m : ℕ} (u : .mk n ⟶ .mk (m + 1)) (i : Fin (m + 1)), P u → P (u ≫ σ i))
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
    (hi : ∀ {n : ℕ}, P (𝟙 (SimplexCategoryGenRel.mk n)))
    (hc₁ : ∀ {n m : ℕ} (u : SimplexCategoryGenRel.mk (m + 1) ⟶ SimplexCategoryGenRel.mk n)
      (i : Fin (m + 2)), P u → P (δ i ≫ u))
    (hc₂ : ∀ {n m : ℕ} (u : SimplexCategoryGenRel.mk m ⟶ SimplexCategoryGenRel.mk n)
      (i : Fin (m + 1)), P u → P (σ i ≫ u )) {a b : SimplexCategoryGenRel} (f : a ⟶ b) :
    P f := by
  apply CategoryTheory.Quotient.induction (P := (fun f ↦ P f))
  apply Paths.induction'
  · exact hi
  · rintro _ _ _ ⟨⟩ _
    · exact hc₁ _ _
    · exact hc₂ _ _

/-- An induction principle for reasonning about morphisms properties in SimplexCategoryGenRel. -/
lemma hom_induction_eq_top (P : MorphismProperty SimplexCategoryGenRel)
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
lemma hom_induction_eq_top' (P : MorphismProperty SimplexCategoryGenRel)
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
@[elab_as_elim]
def obj_induction {P : SimplexCategoryGenRel → Sort*}
    (H : ∀ n : ℕ, P (.mk n)) :
    ∀ x : SimplexCategoryGenRel, P x := by
  intro x
  exact H x.len

/-- A basic ext lemma for objects of SimplexCategoryGenRel --/
@[ext]
lemma obj_ext {x y : SimplexCategoryGenRel} (h : x.len = y.len) : x = y := by
  cases x using obj_induction
  cases y using obj_induction
  simp only [mk_len] at h
  congr

end InductionPrinciples

section SimplicialIdentities

@[reassoc]
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    δ i ≫ δ j.succ = δ j ≫ δ i.castSucc := by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.simplicial1 H

@[reassoc]
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ j.castSucc) :
    δ i.castSucc ≫ σ j.succ = σ j ≫ δ i := by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.simplicial2 H

@[reassoc]
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} :
    δ i.castSucc ≫ σ i = 𝟙 (mk n) := by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.simplicial3₁

@[reassoc]
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : δ i.succ ≫ σ i = 𝟙 (mk n) := by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.simplicial3₂

@[reassoc]
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.castSucc < i) :
    δ i.succ ≫ σ j.castSucc = σ j ≫ δ i := by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.simplicial4 H

@[reassoc]
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    σ i.castSucc ≫ σ j = σ j.succ ≫ σ i := by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.simplicial5 H

/-- A version of δ_comp_δ with indices in ℕ satisfying relevant inequalities. -/
lemma δ_comp_δ_nat {n} (i j : ℕ) (hi : i < n + 2) (hj : j < n + 2) (H : i ≤ j) :
    δ (i : Fin (n + 2)) ≫ δ ↑(j + 1) = δ ↑j ≫ δ ↑i := by
  let i₁ : Fin (n + 2) := ⟨i, hi⟩
  let j₁ : Fin (n + 2) := ⟨j, hj⟩
  conv_lhs =>
    congr
    · right
      equals i₁ =>
        congr
        ext
        simp only [Fin.val_natCast, Nat.mod_eq_of_lt hi]
        rfl
    · right
      equals j₁.succ =>
        congr
        ext
        simp only [Fin.val_natCast]
        rw [Nat.mod_eq_of_lt]
        · rfl
        · omega
  rw [δ_comp_δ (by simpa)]
  congr
  · ext
    simp only [Fin.val_succ, Fin.val_natCast, Nat.mod_eq_of_lt hj,
      Nat.mod_eq_of_lt (Nat.succ_lt_succ hi), Nat.succ_eq_add_one, add_left_inj ]
    rfl
  · ext
    simp only [Fin.val_succ, Fin.val_natCast, Nat.succ_eq_add_one, add_left_inj ]
    rw [Nat.mod_eq_of_lt]
    · rfl
    · omega

/-- A version of σ_comp_σ with indices in ℕ satisfying relevant inequalities. -/
lemma σ_comp_σ_nat {n} (i j : ℕ) (hi : i < n + 1) (hj : j < n + 1) (H : i ≤ j) :
    σ (i : Fin (n + 1 + 1)) ≫ σ (j : Fin (n + 1)) = σ ↑(j + 1) ≫ σ ↑i := by
  let i₁ : Fin (n + 1) := ⟨i, hi⟩
  let j₁ : Fin (n + 1) := ⟨j, hj⟩
  conv_lhs =>
    congr
    · right
      equals i₁.castSucc =>
        congr
        ext
        simp only [Fin.val_natCast, Nat.mod_eq_of_lt (Nat.lt_succ_of_lt hi), Fin.coe_castSucc]
        rfl
    · right
      equals j₁ =>
        congr
        ext
        simp only [Fin.val_natCast, Nat.mod_eq_of_lt hj]
        rfl
  rw [σ_comp_σ (by simpa)]
  congr <;> {
    ext
    simp only [Fin.val_succ, Fin.val_natCast, Nat.mod_eq_of_lt hi,
      Nat.mod_eq_of_lt (Nat.succ_lt_succ hj), Nat.succ_eq_add_one, add_left_inj ]
    rfl }

end SimplicialIdentities

/-- The canonical functor from `SimplexCategoryGenRel` to SimplexCategory, which exists as the
simplicial identities hold in `SimplexCategory`. -/
def toSimplexCategory : SimplexCategoryGenRel ⥤ SimplexCategory := by
  fapply CategoryTheory.Quotient.lift
  · fapply Paths.lift
    exact { obj i := .mk i,
            map f := match f with
              | FreeSimplexQuiver.Hom.δ i => SimplexCategory.δ i
              | FreeSimplexQuiver.Hom.σ i => SimplexCategory.σ i }
  · intro x y f₁ f₂ h
    cases h with
    | simplicial1 H => exact SimplexCategory.δ_comp_δ H
    | simplicial2 H => exact SimplexCategory.δ_comp_σ_of_le H
    | simplicial3₁ => exact SimplexCategory.δ_comp_σ_self
    | simplicial3₂ => exact SimplexCategory.δ_comp_σ_succ
    | simplicial4 H => exact SimplexCategory.δ_comp_σ_of_gt H
    | simplicial5 H => exact SimplexCategory.σ_comp_σ H

@[simp]
lemma toSimplexCategory_obj_mk (n : ℕ) : toSimplexCategory.obj (mk n) = .mk n := rfl

@[simp]
lemma toSimplexCategory_map_δ {n : ℕ} (i : Fin (n + 2)) : toSimplexCategory.map (δ i) =
    SimplexCategory.δ i := rfl

@[simp]
lemma toSimplexCategory_map_σ {n : ℕ} (i : Fin (n + 1)) : toSimplexCategory.map (σ i) =
    SimplexCategory.σ i := rfl

@[simp]
lemma toSimplexCategory_len {x : SimplexCategoryGenRel} : (toSimplexCategory.obj x).len = x.len :=
  rfl

end SimplexCategoryGenRel

end AlgebraicTopology.SimplexCategory
