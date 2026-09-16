/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
# ...

## References
* [P. Gabriel, M. Zisman, *Calculus of fractions and homotopy theory*, IV.2][gabriel-zisman-1967]

-/

@[expose] public section

universe u

universe v w in
lemma ULift.down_mono {α : Type w} [Preorder α] : Monotone (ULift.down.{v} (α := α)) :=
  fun _ _ h ↦ h

universe v w in
lemma ULift.up_mono {α : Type w} [Preorder α] : Monotone (ULift.up.{v} (α := α)) :=
  fun _ _ h ↦ h

open CategoryTheory HomotopicalAlgebra MonoidalCategory

open scoped Simplicial

namespace SSet

namespace horn

def ρOrderHom {n : ℕ} (x₀ : Fin (n + 1)) : (Fin (n + 1) × Fin 2) →o Fin (n + 1) where
  toFun xy := match xy with
    | ⟨x, 0⟩ => if x ≤ x₀ then x else x₀
    | ⟨x, 1⟩ => x
  monotone' := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    obtain ⟨hx, hy⟩ := Prod.le_def.1 h
    dsimp at hx hy
    fin_cases y <;> fin_cases y' <;> grind

@[simp]
lemma ρOrderHom_one {n : ℕ} (x₀ : Fin (n + 1)) (i : Fin (n + 1)) :
    ρOrderHom x₀ ⟨i, 1⟩ = i := rfl

def ρ {n : ℕ} (x₀ : Fin (n + 1)) : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ Δ[n] :=
  (prodStdSimplex.isoNerve.{u} n 1).hom ≫
    nerveMap (ULift.up_mono.{u}.comp ((ρOrderHom x₀).monotone.comp ULift.down_mono.{u})).functor ≫
      (stdSimplex.isoNerve n).inv

@[reassoc (attr := simp)]
lemma ι₁_ρ {n : ℕ} (x₀ : Fin (n + 1)) :
    ι₁ ≫ ρ.{u} x₀ = 𝟙 _ :=
  yonedaEquiv.injective (by ext i : 1; exact ρOrderHom_one x₀ i)

set_option backward.isDefEq.respectTransparency.types false in
noncomputable def retractArrowCastSuccι {n : ℕ} (i : Fin (n + 1)) :
    RetractArrow Λ[n + 1, i.castSucc].ι (Subcomplex.unionProd.{u} ∂Δ[n + 1] Λ[1, 0]).ι where
  i := Arrow.homMk (Subcomplex.lift (Λ[n + 1, i.castSucc].ι ≫ ι₁) sorry) ι₁ rfl
  r := Arrow.homMk (Subcomplex.lift (Subcomplex.ι _ ≫ (ρ i.castSucc)) sorry) (ρ i.castSucc) rfl
  retract := by
    ext : 1
    · rw [← cancel_mono (Subcomplex.ι _)]
      simp
    · simp

def retractArrowSuccι {n : ℕ} (i : Fin (n + 1)) :
    RetractArrow Λ[n + 1, i.succ].ι (Subcomplex.unionProd.{u} ∂Δ[n + 1] Λ[1, 1]).ι := by
  sorry

end horn

namespace modelCategoryQuillen

lemma fibration_iff_hasLiftingProperty_unionProd_boundary_horn_one {E B : SSet.{u}} (p : E ⟶ B) :
    Fibration p ↔
      ∀ (n : ℕ) (i : Fin 2), HasLiftingProperty (Subcomplex.unionProd.{u} ∂Δ[n] Λ[1, i]).ι p := by
  refine ⟨fun _ n i ↦ anodyneExtensions_unionProd_ι _ _ (.horn_ι i) _ (mem_fibrations p),
    fun _ ↦ ?_⟩
  rw [fibration_iff]
  rintro _ _ _ h
  simp only [J, MorphismProperty.iSup_iff] at h
  obtain ⟨n, ⟨i⟩⟩ := h
  obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
  · exact (horn.retractArrowCastSuccι i).leftLiftingProperty _
  · exact (horn.retractArrowSuccι (Fin.last n)).leftLiftingProperty _

lemma fibration_iff_hasLiftingProperty_unionProd_horn_one_boundary {E B : SSet.{u}} (p : E ⟶ B) :
    Fibration p ↔
      ∀ (n : ℕ) (i : Fin 2), HasLiftingProperty (Subcomplex.unionProd.{u} Λ[1, i] ∂Δ[n]).ι p := by
  rw [fibration_iff_hasLiftingProperty_unionProd_boundary_horn_one]
  refine forall_congr' (fun n ↦ forall_congr' (fun i ↦ ?_))
  exact HasLiftingProperty.iff_of_arrow_iso_left
    (Arrow.isoMk (Subcomplex.unionProd.symmIso _ _) (β_ _ _)) _

end modelCategoryQuillen

end SSet
