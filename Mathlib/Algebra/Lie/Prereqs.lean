/-
Copyright (c) 2024 Lucas Whitfield. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucas Whitfield
-/
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Batteries.Tactic.ShowUnused

-- move this
section

variable (R L M : Type*)
variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M]

instance instCanLiftSubmoduleLieSubmodule : CanLift (Submodule R M) (LieSubmodule R L M) (·)
    (fun N ↦ ∀ {x : L} {m : M}, m ∈ N → ⁅x, m⁆ ∈ N) where
  prf N hN := ⟨⟨N, hN⟩, rfl⟩

end

-- move this
section

open LieAlgebra

class LieTower (L₁ L₂ M : Type*) [Add M] [Bracket L₁ L₂] [Bracket L₁ M] [Bracket L₂ M] where
    leibniz_lie : ∀ (x : L₁) (y : L₂) (m : M), ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆

lemma leibniz_lie' {L₁ L₂ M : Type*}
    [Add M] [Bracket L₁ L₂] [Bracket L₁ M] [Bracket L₂ M] [LieTower L₁ L₂ M]
    (x : L₁) (y : L₂) (m : M) :
    ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆ := LieTower.leibniz_lie x y m

lemma lie_swap_lie {L₁ L₂ M : Type*} [AddCommGroup M]
    [Bracket L₁ L₂] [Bracket L₂ L₁] [Bracket L₁ M] [Bracket L₂ M]
    [LieTower L₁ L₂ M] [LieTower L₂ L₁ M]
    (x : L₁) (y : L₂) (m : M) :
    ⁅⁅x, y⁆, m⁆ = -⁅⁅y, x⁆, m⁆ := by
  have h1 := leibniz_lie' x y m
  have h2 := leibniz_lie' y x m
  convert congr($h1.symm - $h2) using 1 <;> abel

instance {L : Type*} (M : Type*) [LieRing L] [AddCommGroup M] [LieRingModule L M] :
    LieTower L L M where
  leibniz_lie x y m := leibniz_lie x y m

instance {R L : Type*} (M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [LieRingModule L M] (A : LieSubalgebra R L) :
    LieTower A L M where
  leibniz_lie x y m := leibniz_lie x.val y m

instance {R L : Type*} (M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [LieRingModule L M] (A : LieIdeal R L) :
    LieTower A L M where
  leibniz_lie x y m := leibniz_lie x.val y m

instance {R L : Type*} (M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [LieRingModule L M] (A : LieIdeal R L) :
    LieTower L A M where
  leibniz_lie x y m := leibniz_lie x y.val m

end

