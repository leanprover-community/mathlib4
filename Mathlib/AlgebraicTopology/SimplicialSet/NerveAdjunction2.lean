/-
Copyright (c) 2024 Mario Carneiro and Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
import Mathlib.CategoryTheory.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Limits.Presheaf

/-!

-/

universe u

open CategoryTheory Nerve Simplicial SimplicialObject.Truncated
  SimplexCategory.Truncated Opposite

namespace SSet

namespace Truncated

namespace Path
variable {n : ℕ} {X : Truncated.{u} (n + 1)} (p q : X.Path 1)
  (h : p.vertex 1 = q.vertex 0)

@[simps!]
def mk₂ : X.Path 2 where
  vertex := ![p.vertex 0, p.vertex 1, q.vertex 1]
  arrow := ![p.arrow 0, q.arrow 0]
  arrow_src i := by
    fin_cases i
    · exact p.arrow_src 0
    · exact (q.arrow_src 0).trans h.symm
  arrow_tgt i := by
    fin_cases i
    · exact p.arrow_tgt 0
    · exact q.arrow_tgt 0

end Path

section

variable {n : ℕ} {X Y : Truncated.{u} 2} (f₀ : X _⦋0⦌₂ → Y _⦋0⦌₂) (f₁ : X _⦋1⦌₂ → Y _⦋1⦌₂)
  (hδ₁ : ∀ (x : X _⦋1⦌₂), f₀ (X.map (δ₂ 1).op x) = Y.map (δ₂ 1).op (f₁ x))
  (hδ₀ : ∀ (x : X _⦋1⦌₂), f₀ (X.map (δ₂ 0).op x) = Y.map (δ₂ 0).op (f₁ x))
  (hσ : ∀ (x : X _⦋0⦌₂), f₁ (X.map (σ₂ 0).op x) = Y.map (σ₂ 0).op (f₀ x))
  (hY : Y.StrictSegal)

namespace liftOfIsStrictSegal

def f₂ (x : X _⦋2⦌₂) : Y _⦋2⦌₂ :=
  (hY.spineEquiv 2).symm
    (.mk₂ (Y.spine 1 (by simp) (f₁ (X.map (δ₂ 2).op x)))
      (Y.spine 1 (by simp) (f₁ (X.map (δ₂ 0).op x))) (by
        simp only [spine_vertex]
        rw [← δ₂_one_eq_const, ← δ₂_zero_eq_const, ← hδ₁, ← hδ₀]
        simp only [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_zero_comp_δ₂_two]))

@[simp]
lemma spineEquiv_f₂_arrow_zero (x : X _⦋2⦌₂) :
    ((hY.spineEquiv 2) (f₂ f₀ f₁ hδ₁ hδ₀ hY x)).arrow 0 = f₁ (X.map (δ₂ 2).op x) := by
  simp [f₂]

@[simp]
lemma spineEquiv_f₂_arrow_one (x : X _⦋2⦌₂) :
    ((hY.spineEquiv 2) (f₂ f₀ f₁ hδ₁ hδ₀ hY x)).arrow 1 = f₁ (X.map (δ₂ 0).op x) := by
  simp [f₂]

lemma hδ'₀ (x : X _⦋2⦌₂) :
    f₁ (X.map (δ₂ 0).op x) = Y.map (δ₂ 0).op (f₂ f₀ f₁ hδ₁ hδ₀ hY x) := by
  simp [← spineEquiv_f₂_arrow_one f₀ f₁ hδ₁ hδ₀ hY, StrictSegal.spineEquiv,
    SimplexCategory.mkOfSucc_one_eq_δ]

variable (hδ'₁ : ∀ (x : X _⦋2⦌₂), f₁ (X.map (δ₂ 1).op x) = Y.map (δ₂ 1).op (f₂ f₀ f₁ hδ₁ hδ₀ hY x))

lemma hδ'₂ (x : X _⦋2⦌₂) :
    f₁ (X.map (δ₂ 2).op x) = Y.map (δ₂ 2).op (f₂ f₀ f₁ hδ₁ hδ₀ hY x) := by
  simp [← spineEquiv_f₂_arrow_zero f₀ f₁ hδ₁ hδ₀ hY, StrictSegal.spineEquiv,
    SimplexCategory.mkOfSucc_zero_eq_δ]

include hσ in
lemma hσ'₀ (x : X _⦋1⦌₂) :
    f₂ f₀ f₁ hδ₁ hδ₀ hY (X.map (σ₂ 0).op x) = Y.map (σ₂ 0).op (f₁ x) := by
  apply (hY.spineEquiv 2).injective
  ext i
  fin_cases i
  · dsimp
    rw [spineEquiv_f₂_arrow_zero]
    dsimp [StrictSegal.spineEquiv]
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_two_comp_σ₂_zero, op_comp,
      FunctorToTypes.map_comp_apply, hσ, SimplexCategory.mkOfSucc_zero_eq_δ,
      ← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_two_comp_σ₂_zero,
      op_comp, FunctorToTypes.map_comp_apply, hδ₁]
  · dsimp
    rw [spineEquiv_f₂_arrow_one]
    simp [StrictSegal.spineEquiv, SimplexCategory.mkOfSucc_one_eq_δ,
      ← FunctorToTypes.map_comp_apply, ← op_comp]

include hσ in
lemma hσ'₁ (x : X _⦋1⦌₂) :
    f₂ f₀ f₁ hδ₁ hδ₀ hY (X.map (σ₂ 1).op x) = Y.map (σ₂ 1).op (f₁ x) := by
  have := hσ
  apply (hY.spineEquiv 2).injective
  ext i
  fin_cases i
  · dsimp
    rw [spineEquiv_f₂_arrow_zero]
    simp [StrictSegal.spineEquiv, SimplexCategory.mkOfSucc_zero_eq_δ,
      ← FunctorToTypes.map_comp_apply, ← op_comp]
  · dsimp
    rw [spineEquiv_f₂_arrow_one]
    dsimp [StrictSegal.spineEquiv]
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_zero_comp_σ₂_one, op_comp,
      FunctorToTypes.map_comp_apply, hσ, SimplexCategory.mkOfSucc_one_eq_δ,
      ← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_zero_comp_σ₂_one,
      op_comp, FunctorToTypes.map_comp_apply, hδ₀]

def app (n : (SimplexCategory.Truncated 2)ᵒᵖ) : X.obj n ⟶ Y.obj n := by
  obtain ⟨n, hn⟩ := n
  induction n using SimplexCategory.rec with | _ n
  match n with
  | 0 => exact f₀
  | 1 => exact f₁
  | 2 => exact f₂ f₀ f₁ hδ₁ hδ₀ hY

abbrev naturalityProperty : MorphismProperty (SimplexCategory.Truncated 2) :=
  (MorphismProperty.naturalityProperty (app f₀ f₁ hδ₁ hδ₀ hY)).unop

include hδ'₁ hσ in
lemma naturalityProperty_eq_top :
    naturalityProperty f₀ f₁ hδ₁ hδ₀ hY = ⊤ := by
  refine SimplexCategory.Truncated.morphismProperty_eq_top _
    (fun n hn i ↦ ?_) (fun n hn i ↦ ?_)
  · obtain _ | _ | n := n
    · fin_cases i
      · ext; apply hδ₀
      · ext; apply hδ₁
    · fin_cases i
      · ext; apply hδ'₀ f₀ f₁ hδ₁ hδ₀ hY
      · ext; apply hδ'₁
      · ext; apply hδ'₂ f₀ f₁ hδ₁ hδ₀ hY
    · omega
  · obtain _ | _ | n := n
    · fin_cases i
      ext; apply hσ
    · fin_cases i
      · ext; apply hσ'₀ f₀ f₁ hδ₁ hδ₀ hσ hY
      · ext; apply hσ'₁ f₀ f₁ hδ₁ hδ₀ hσ hY
    · omega

end liftOfIsStrictSegal

open liftOfIsStrictSegal in
def liftOfIsStrictSegal
    (hδ'₁ : ∀ (x : X _⦋2⦌₂), f₁ (X.map (δ₂ 1).op x) =
      Y.map (δ₂ 1).op (f₂ f₀ f₁ hδ₁ hδ₀ hY x)) : X ⟶ Y where
  app := liftOfIsStrictSegal.app f₀ f₁ hδ₁ hδ₀ hY
  naturality _ _ φ :=
    (liftOfIsStrictSegal.naturalityProperty_eq_top f₀ f₁ hδ₁ hδ₀ hσ hY hδ'₁).symm.le
      φ.unop (by simp)

end

namespace HomotopyCategory

variable {X : Truncated.{u} 2} {C : Type u} [SmallCategory C]

def descOfTruncation (φ : X ⟶ (truncation 2).obj (nerve C)) :
    X.HomotopyCategory ⥤ C :=
  lift (fun x ↦ nerveEquiv (φ.app _ x)) (fun e ↦ nerveHomEquiv (e.map φ))
    (fun x ↦ by simpa using nerveHomEquiv_id (φ.app _ x))
      (fun h ↦ nerveHomEquiv_comp (h.map φ))

def functorEquiv :
    (X.HomotopyCategory ⥤ C) ≃ (X ⟶ (truncation 2).obj (nerve C)) where
  toFun F :=
    liftOfIsStrictSegal (fun x ↦ nerveEquiv.symm (F.obj (mk x))) (by
      sorry) sorry sorry sorry sorry sorry
  invFun φ := descOfTruncation φ
  left_inv := sorry
  right_inv := sorry

end HomotopyCategory

/-- The adjunction between the 2-truncated homotopy category functor
and the 2-truncated nerve functor and the . -/
def nerve₂Adj : hoFunctor₂.{u} ⊣ nerveFunctor₂ :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := HomotopyCategory.functorEquiv
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

end Truncated

end SSet
