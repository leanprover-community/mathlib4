/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Sites.Coherent.Basic
import Mathlib.CategoryTheory.Sites.Preserves
/-!

# Sheaves for the extensive topology

This file characterises sheaves for the extensive topology.

## Main result

* `isSheaf_iff_preservesFiniteProducts`: In a finitary extensive category, the sheaves for the
  extensive topology are precisely those preserving finite products.
-/

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

variable [FinitaryPreExtensive C]

/-- A presieve is *extensive* if it is finite and its arrows induce an isomorphism from the
coproduct to the target. -/
class Presieve.Extensive {X : C} (R : Presieve X) : Prop where
  /-- `R` consists of a finite collection of arrows that together induce an isomorphism from the
  coproduct of their sources. -/
  arrows_nonempty_isColimit : ∃ (α : Type) (_ : Finite α) (Z : α → C) (π : (a : α) → (Z a ⟶ X)),
    R = Presieve.ofArrows Z π ∧ Nonempty (IsColimit (Cofan.mk X π))

instance {X : C} (S : Presieve X) [S.Extensive] : S.hasPullbacks where
  has_pullbacks := by
    obtain ⟨_, _, _, _, rfl, ⟨hc⟩⟩ := Presieve.Extensive.arrows_nonempty_isColimit (R := S)
    intro _ _ _ _ _ hg
    cases hg
    apply FinitaryPreExtensive.hasPullbacks_of_is_coproduct hc

open Presieve Opposite

/--
A finite product preserving presheaf is a sheaf for the extensive topology on a category which is
`FinitaryPreExtensive`.
-/
theorem isSheafFor_extensive_of_preservesFiniteProducts {X : C} (S : Presieve X) [S.Extensive]
    (F : Cᵒᵖ ⥤ Type max u v) [PreservesFiniteProducts F] : S.IsSheafFor F  := by
  obtain ⟨α, _, Z, π, rfl, ⟨hc⟩⟩ := Extensive.arrows_nonempty_isColimit (R := S)
  have : (ofArrows Z (Cofan.mk X π).inj).hasPullbacks :=
    (inferInstance : (ofArrows Z π).hasPullbacks)
  cases nonempty_fintype α
  exact isSheafFor_of_preservesProduct _ _ hc

instance {α : Type} [Finite α] (Z : α → C) : (ofArrows Z (fun i ↦ Sigma.ι Z i)).Extensive :=
  ⟨⟨α, inferInstance, Z, (fun i ↦ Sigma.ι Z i), rfl, ⟨coproductIsCoproduct _⟩⟩⟩

/--
A presheaf on a category which is `FinitaryExtensive` is a sheaf iff it preserves finite products.
-/
theorem isSheaf_iff_preservesFiniteProducts [FinitaryExtensive C] (F : Cᵒᵖ ⥤ Type max u v) :
    Presieve.IsSheaf (extensiveCoverage C).toGrothendieck F ↔
    Nonempty (PreservesFiniteProducts F) := by
  refine ⟨fun hF ↦ ⟨⟨fun α _ ↦ ⟨fun {K} ↦ ?_⟩⟩⟩, fun hF ↦ ?_⟩
  · rw [Presieve.isSheaf_coverage] at hF
    let Z : α → C := fun i ↦ unop (K.obj ⟨i⟩)
    have : (Presieve.ofArrows Z (Cofan.mk (∐ Z) (Sigma.ι Z)).inj).hasPullbacks :=
      (inferInstance : (Presieve.ofArrows Z (Sigma.ι Z)).hasPullbacks)
    have : ∀ (i : α), Mono (Cofan.inj (Cofan.mk (∐ Z) (Sigma.ι Z)) i) :=
      (inferInstance : ∀ (i : α), Mono (Sigma.ι Z i))
    let i : K ≅ Discrete.functor (fun i ↦ op (Z i)) := Discrete.natIsoFunctor
    let _ : PreservesLimit (Discrete.functor (fun i ↦ op (Z i))) F :=
        Presieve.preservesProductOfIsSheafFor F ?_ initialIsInitial _ (coproductIsCoproduct Z)
        (FinitaryExtensive.isPullback_initial_to_sigma_ι Z)
        (hF (Presieve.ofArrows Z (fun i ↦ Sigma.ι Z i)) ?_)
    · exact preservesLimitOfIsoDiagram F i.symm
    · apply hF
      exact ⟨Empty, inferInstance, Empty.elim, IsEmpty.elim inferInstance, rfl,
        ⟨Cofan.isColimitOfIsIsoSigmaDesc _⟩⟩
    · exact ⟨α, inferInstance, Z, (fun i ↦ Sigma.ι Z i), rfl, ⟨coproductIsCoproduct _⟩⟩
  · let _ := hF.some
    rw [Presieve.isSheaf_coverage]
    intro X R ⟨Y, α, Z, π, hR, hi⟩
    have : R.Extensive := ⟨Y, α, Z, π, hR, hi⟩
    exact isSheafFor_extensive_of_preservesFiniteProducts R F

end CategoryTheory
