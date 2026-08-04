/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex.MulStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncatedQuasicategory


/-!
# The fundamental groupoid of a Kan complex


-/

@[expose] public section

universe u

open HomotopicalAlgebra CategoryTheory Simplicial

namespace SSet

namespace KanComplex

/-- The fundamental groupoid of a Kan complex. -/
@[nolint unusedArguments]
def FundamentalGroupoid (X : SSet.{u}) [KanComplex X] :=
  Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj X)

variable {X : SSet.{u}} [KanComplex X]

noncomputable instance : Category (FundamentalGroupoid X) :=
  inferInstanceAs (Category (Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj X)))

namespace FundamentalGroupoid

/-- The objects of the fundamental groupoid of a Kan complex identify to `0`-simplices. -/
@[implicit_reducible, simps]
def objEquiv : FundamentalGroupoid X ≃ X _⦋0⦌ where
  toFun x := x.pt
  invFun x := { pt := x }

/-- Constructor for objects of the fundamental groupoid of a Kan complex. -/
abbrev objMk (x : X _⦋0⦌) : FundamentalGroupoid X := objEquiv.symm x

/-- Induction principle for objects of `FundamentalGroupoid X`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
def rec {motive : FundamentalGroupoid X → Sort*}
    (objMk : ∀ (x : X _⦋0⦌), motive (objMk x)) (x : FundamentalGroupoid X) :
    motive x :=
  objMk x.pt

/-- Constructor for morphisms of the fundamental groupoid of a Kan complex. -/
@[no_expose]
def homMk {x y : X _⦋0⦌} (e : Edge x y) : objMk x ⟶ objMk y :=
  Truncated.HomotopyCategory₂.homMk e

@[simp]
lemma homMk_id (x : X _⦋0⦌) : homMk (.id x) = 𝟙 _ := by
  rfl

lemma homMk_surjective {x y : X _⦋0⦌} :
    Function.Surjective (fun (e : Edge x y) ↦ homMk e) :=
  Truncated.HomotopyCategory₂.homMk_surjective

@[elab_as_elim, cases_eliminator, induction_eliminator]
lemma hom_rec {x y : X _⦋0⦌} (motive : (objMk x ⟶ objMk y) → Prop)
    (homMk : ∀ (e : Edge x y), motive (homMk e)) (f : objMk x ⟶ objMk y) :
    motive f := by
  obtain ⟨e, rfl⟩ := homMk_surjective f
  exact homMk e

@[reassoc]
lemma homMk_fac_of_compStruct {x y z : X _⦋0⦌} {e₁ : Edge x y} {e₂ : Edge y z} {e₃ : Edge x z}
    (h : Edge.CompStruct e₁ e₂ e₃) :
    homMk e₁ ≫ homMk e₂ = homMk e₃ :=
  Truncated.Edge.CompStruct.nonempty_iff.1 ⟨h⟩

private lemma isGroupoid_aux {x₀ x₁ : X _⦋0⦌} (e : Edge x₀ x₁) :
    ∃ (e' : Edge x₁ x₀), Nonempty (Edge.CompStruct e e' (.id x₀)) := by
  let φ (j : Fin 3) (hk : j ≠ 0) : Δ[1] ⟶ X :=
    if j = 1 then const x₀ else yonedaEquiv.symm e.edge
  have hφ : horn.IsCompatible φ := by
    rw [horn.isCompatible_iff]
    intro j k
    fin_cases j <;> fin_cases k <;> simp [φ, yonedaEquiv_symm_zero]
  refine ⟨Edge.mk (yonedaEquiv (stdSimplex.δ 0 ≫ hφ.liftOfKanComplex))
    (yonedaEquiv.symm.injective ?_) (yonedaEquiv.symm.injective ?_),
    ⟨Edge.CompStruct.mk (yonedaEquiv hφ.liftOfKanComplex) ?_ ?_ ?_⟩⟩
  · simp [← stdSimplex.δ_comp_yonedaEquiv_symm,
      ← dsimp% stdSimplex.δ_comp_δ_assoc (n := 0) (i := 0) (j := 1) (by simp),
      hφ.δ_liftOfKanComplex 2 (by simp), φ]
  · simp [← stdSimplex.δ_comp_yonedaEquiv_symm,
      dsimp% stdSimplex.δ_comp_δ_self_assoc (n := 0) (i := 0),
      hφ.δ_liftOfKanComplex 1 (by simp), φ, yonedaEquiv_symm_zero]
  · simp [← stdSimplex.yonedaEquiv_δ_comp, hφ.δ_liftOfKanComplex 2 (by simp), φ]
  · simp [stdSimplex.yonedaEquiv_δ_comp]
  · simp [← stdSimplex.yonedaEquiv_δ_comp, hφ.δ_liftOfKanComplex 1 (by simp), φ,
      σ_zero_eq_yonedaEquiv_const]

private lemma isGroupoid_aux' {x₀ x₁ : X _⦋0⦌} (e : Edge x₀ x₁) :
    ∃ (e' : Edge x₁ x₀), Nonempty (Edge.CompStruct e' e (.id x₁)) := by
  obtain ⟨e', ⟨h⟩⟩ := isGroupoid_aux e.op
  exact ⟨e'.unop, ⟨h.unop.ofEq rfl rfl (by simp)⟩⟩

instance : IsGroupoid (FundamentalGroupoid X) := by
  refine ⟨fun {x₀ x₁} f ↦ ?_⟩
  induction x₀ with | objMk x₀
  induction x₁ with | objMk x₁
  induction f with | homMk e
  obtain ⟨e', ⟨h⟩⟩ := isGroupoid_aux e
  obtain ⟨e'', ⟨h'⟩⟩ := isGroupoid_aux' e
  replace h : homMk e ≫ homMk e' = 𝟙 _ := by simpa using homMk_fac_of_compStruct h
  replace h' : homMk e'' ≫ homMk e = 𝟙 _ := by simpa using homMk_fac_of_compStruct h'
  have h'' : homMk e' = homMk e'' := by
    trans homMk e'' ≫ homMk e ≫ homMk e'
    · simp [reassoc_of% h']
    · simp [h]
  exact ⟨homMk e', h, by rw [h'', h']⟩

end FundamentalGroupoid

end KanComplex

namespace Edge

variable {X : SSet.{u}} [KanComplex X] {x y z : X _⦋0⦌}

open KanComplex.FundamentalGroupoid

lemma CompStruct.nonempty_iff {e₁ : Edge x y} {e₂ : Edge y z} {e₃ : Edge x z} :
    Nonempty (CompStruct e₁ e₂ e₃) ↔ homMk e₁ ≫ homMk e₂ = homMk e₃ :=
  Truncated.Edge.CompStruct.nonempty_iff

/-- A choice of inverse of an edge in a Kan complex. -/
@[no_expose]
protected noncomputable def inv (e : Edge x y) : Edge y x :=
  (homMk_surjective (CategoryTheory.inv (homMk e))).choose

@[simp]
lemma homMk_inv (e : Edge x y) : homMk e.inv = inv (homMk e) :=
  (homMk_surjective (CategoryTheory.inv (homMk e))).choose_spec

/-- `Edge.inv` is a right inverse. -/
@[no_expose]
noncomputable def CompStruct.homInvId (e : Edge x y) : CompStruct e e.inv (id x) :=
  Nonempty.some (by simp [nonempty_iff])

/-- `Edge.inv` is a left inverse. -/
@[no_expose]
noncomputable def CompStruct.invHomId (e : Edge x y) : CompStruct e.inv e (id y) :=
  Nonempty.some (by simp [nonempty_iff])

end Edge

end SSet
