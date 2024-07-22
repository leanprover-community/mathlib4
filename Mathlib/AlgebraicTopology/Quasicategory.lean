/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import Mathlib.AlgebraicTopology.KanComplex
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Closed.FunctorToTypes
import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# Quasicategories

In this file we define quasicategories,
a common model of infinity categories.
We show that every Kan complex is a quasicategory.

In `Mathlib/AlgebraicTopology/Nerve.lean`
we show (TODO) that the nerve of a category is a quasicategory.

## TODO

- Generalize the definition to higher universes.
  See the corresponding TODO in `Mathlib/AlgebraicTopology/KanComplex.lean`.

-/

namespace SSet

open CategoryTheory Simplicial

/-- A simplicial set `S` is a *quasicategory* if it satisfies the following horn-filling condition:
for every `n : ℕ` and `0 < i < n`,
every map of simplicial sets `σ₀ : Λ[n, i] → S` can be extended to a map `σ : Δ[n] → S`.

[Kerodon, 003A] -/
class Quasicategory (S : SSet) : Prop where
  hornFilling' : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (σ₀ : Λ[n+2, i] ⟶ S)
    (_h0 : 0 < i) (_hn : i < Fin.last (n+2)),
      ∃ σ : Δ[n+2] ⟶ S, σ₀ = hornInclusion (n+2) i ≫ σ

lemma Quasicategory.hornFilling {S : SSet} [Quasicategory S] ⦃n : ℕ⦄ ⦃i : Fin (n+1)⦄
    (h0 : 0 < i) (hn : i < Fin.last n)
    (σ₀ : Λ[n, i] ⟶ S) : ∃ σ : Δ[n] ⟶ S, σ₀ = hornInclusion n i ≫ σ := by
  cases n using Nat.casesAuxOn with
  | zero => simp [Fin.lt_iff_val_lt_val] at hn
  | succ n =>
  cases n using Nat.casesAuxOn with
  | zero =>
    simp only [Fin.lt_iff_val_lt_val, Fin.val_zero, Fin.val_last, zero_add, Nat.lt_one_iff] at h0 hn
    simp [hn] at h0
  | succ n => exact Quasicategory.hornFilling' σ₀ h0 hn

/-- Every Kan complex is a quasicategory.

[Kerodon, 003C] -/
instance (S : SSet) [KanComplex S] : Quasicategory S where
  hornFilling' _ _ σ₀ _ _ := KanComplex.hornFilling σ₀

lemma quasicategory_of_filler (S : SSet)
    (filler : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (σ₀ : Λ[n+2, i] ⟶ S)
      (_h0 : 0 < i) (_hn : i < Fin.last (n+2)),
      ∃ σ : S _[n+2], ∀ (j) (h : j ≠ i), S.δ j σ = σ₀.app _ (horn.face i j h)) :
    Quasicategory S where
  hornFilling' n i σ₀ h₀ hₙ := by
    obtain ⟨σ, h⟩ := filler σ₀ h₀ hₙ
    refine ⟨(S.yonedaEquiv _).symm σ, ?_⟩
    apply horn.hom_ext
    intro j hj
    rw [← h j hj, NatTrans.comp_app]
    rfl

section

instance : MonoidalClosed SSet := FunctorToTypes.monoidalClosed

/- p : X ⟶ Y is a trivial Kan fibration if it has the right lifting property wrt
  every boundary inclusion  ∂Δ[n] ⟶ Δ[n] -/
class trivialKanFibration {X Y : SSet} (p : X ⟶ Y) where
  has_rlp (n : ℕ) : HasLiftingProperty (boundaryInclusion n) p

/- equivalent definition of trivial Kan fibration by 006Y -/
class rlp_mono {X Y : SSet} (p : X ⟶ Y) where
  has_rlp (A B : SSet) (i : A ⟶ B) [Mono i] : HasLiftingProperty i p

/- RLP wrt all monomorphisms implies trivial Kan fib -/
instance tkf_of_rlp_mono {X Y : SSet} (p : X ⟶ Y) [rlp_mono p] :
    trivialKanFibration p := sorry

/- trivial Kan fib implies RLP wrt all monomorphisms -/
instance rlp_mono_of_tkf {X Y : SSet} (p : X ⟶ Y) [trivialKanFibration p] :
    rlp_mono p := sorry

noncomputable
abbrev Fun : SSetᵒᵖ ⥤ SSet ⥤ SSet := MonoidalClosed.internalHom

def ihom_equiv (X Y Z : SSet) : (ihom X).obj ((ihom Y).obj Z) ≅ (ihom Y).obj ((ihom X).obj Z) where
  hom := { app := fun n x ↦ { app := fun m f ym ↦ {
    app := fun k g xk ↦ (x.app k (f ≫ g) xk).app k (𝟙 _) (Y.map g ym)
    naturality := by
      dsimp at f ⊢
      intro k l g h
      ext xk
      dsimp
      have := congr_fun ((x.app k (f ≫ h) xk).naturality g (𝟙 k)) (Y.map h ym)
      dsimp at this
      rw [← this]
      simp

      sorry
      }
    }
  }
  inv := { app := fun n x ↦ { app := fun m f xm ↦ {
    app := fun k g yk ↦ (x.app k (f ≫ g) yk).app k (𝟙 _) (X.map g xm)
    naturality := sorry
      }
    }
  }

-- `0079`
/- if B is a quasicat, then Fun(Δ[2], B) ⟶ Fun(Λ[2, 1], B) is a trivial Kan fib -/
instance horn_tkf_of_quasicat (B : SSet) [Quasicategory B] :
    trivialKanFibration ((Fun.map (hornInclusion 2 1).op).app B) := sorry

-- `0079`
/- if Fun(Δ[2], B) ⟶ Fun(Λ[2, 1], B) is a trivial Kan fib, then B is a quasicat -/
instance quasicat_of_horn_tkf (B : SSet)
    [trivialKanFibration ((Fun.map (hornInclusion 2 1).op).app B)] :
    Quasicategory B := sorry

open MonoidalCategory
instance (B : SSet) (n : ℕ) : Mono ((boundaryInclusion n) ▷ B) where
  right_cancellation := sorry

-- changing the square to apply the lifting property of p
lemma induced_tkf_aux (B X Y : SSet) (p : X ⟶ Y)
    [trivialKanFibration p] (n : ℕ) [h : HasLiftingProperty (boundaryInclusion n ▷ B) p] :
    HasLiftingProperty (boundaryInclusion n) ((Fun.obj (Opposite.op B)).map p) where
  sq_hasLift := by
    intro f g sq
    dsimp at f g sq
    have w := sq.w
    have := (yonedaEquiv _ _ g)
    dsimp [ihom, Closed.rightAdj, FunctorToTypes.rightAdj, Functor.ihom,
      Functor.hom₂Functor] at this
    --have := h.sq_hasLift
    sorry

-- `0071` (special case of `0070`)
/- if p : X ⟶ Y is a trivial Kan fib, then Fun(B,X) ⟶ Fun(B, Y) is -/
noncomputable
instance induced_tkf (B X Y : SSet) (p : X ⟶ Y) [trivialKanFibration p] :
    trivialKanFibration ((Fun.obj (.op B)).map p) where
  has_rlp n := by
    have := (rlp_mono_of_tkf p).has_rlp _ _ ((boundaryInclusion n) ▷ B)
    apply induced_tkf_aux

-- uses `0071` and `0079`
/- the map Fun(Δ[2], Fun(S, D)) ⟶ Fun(Λ[2,1], Fun(S, D)) is a trivial Kan fib -/
-- apply `to_be_shown` and `0079`. need lemma about tranferring lifting properties through isom
open MonoidalClosed in
noncomputable
instance fun_quasicat_aux (S D : SSet) [Quasicategory D] :
    trivialKanFibration ((Fun.map (hornInclusion 2 1).op).app ((Fun.obj (.op S)).obj D)) where
  has_rlp n := by
    have := (induced_tkf S _ _ ((Fun.map (hornInclusion 2 1).op).app D)).has_rlp n
    dsimp at this
    have H : Arrow.mk ((ihom S).map ((pre (hornInclusion 2 1)).app D)) ≅
        Arrow.mk ((pre (hornInclusion 2 1)).app ((ihom S).obj D)) := {
      hom := {
        left := (ihom_equiv _ _ _).hom
        right := (ihom_equiv _ _ _).inv }
      inv := {
        left := (ihom_equiv _ _ _).inv
        right := (ihom_equiv _ _ _).hom
        w := by
          dsimp
          ext n x
          change ((ihom S).map ((MonoidalClosed.pre (hornInclusion 2 1)).app D)).app n
            ((S.ihom_equiv Δ[2] D).inv.app n x) = ((Λ[2, 1].ihom_equiv S D).hom).app n
              (((MonoidalClosed.pre (hornInclusion 2 1)).app ((ihom S).obj D)).app n x)
          sorry
      }
    }
    exact HasLiftingProperty.of_arrow_iso_right _ H

-- `0066`
/- if D is a quasicat, then Fun(S, D) is -/
instance fun_quasicat (S D : SSet) [Quasicategory D] : Quasicategory ((Fun.obj (.op S)).obj D) :=
  quasicat_of_horn_tkf ((Fun.obj (.op S)).obj D) -- instance inferred by `fun_quasicat_aux`

end

end SSet
