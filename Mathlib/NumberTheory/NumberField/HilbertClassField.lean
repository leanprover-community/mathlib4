/-
Copyright (c) 2026 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/
module

public import Mathlib

@[expose] public section

namespace NumberField

noncomputable section KroneckerWeber

variable (K : Type*) [Field K] [CharZero K] [IsAbelianGalois ℚ K]

theorem_wanted IsAbelianGalois.le_isCyclotomic
  (K : Type*) [Field K] [NumberField K] [IsAbelianGalois ℚ K] : ∃ S : Set ℕ,
  (IsAlgClosed.lift (S := K)).range ≤
    Algebra.adjoin ℚ {b : AlgebraicClosure ℚ | ∃ n ∈ S, n ≠ 0 ∧ b ^ n = 1}

theorem_wanted IsAbelianGalois.le_cyclotomicField
  (K : Type*) [Field K] [NumberField K] [IsAbelianGalois ℚ K] :
    ∃ d : ℕ, Nonempty (K →ₐ[ℚ] CyclotomicField d ℚ)

open Classical in
def_wanted IsAbelianGalois.conductor' [NumberField K] : ℕ :=
    Nat.find <| ❰IsAbelianGalois.le_cyclotomicField❱ K

end KroneckerWeber

section HilberClassField

def HilbertClassField (K : Type*) [Field K] [NumberField K] : Type := by sorry

variable (K : Type*) [Field K] [NumberField K]

instance : Field (HilbertClassField K) := sorry

instance : Algebra K (HilbertClassField K) := sorry

instance : Module.Finite K (HilbertClassField K) := sorry

instance : NumberField (HilbertClassField K) := of_module_finite K (HilbertClassField K)

instance : IsAbelianGalois K (HilbertClassField K) := sorry

def HilbertClassField.galoisEquiv :
  Gal((HilbertClassField K)/K) ≃* ClassGroup (𝓞 K) := sorry

open Algebra

instance : Unramified (𝓞 K) (𝓞 (HilbertClassField K)) := sorry

instance : IsUnramifiedAtInfinitePlaces K (HilbertClassField K) := sorry

proof_wanted HilbertClassField_eq_top (H : Type*) [Field H] [Algebra K H] [NumberField H]
      [IsAbelianGalois K H] [Unramified (𝓞 K) (𝓞 (HilbertClassField K))]
      [IsUnramifiedAtInfinitePlaces K (HilbertClassField K)] :
    Nonempty (H ≃ₐ[K] HilbertClassField K)

proof_wanted HilbertClassField.principal (P : Ideal (𝓞 K)) :
  Submodule.IsPrincipal <| P.map (algebraMap (𝓞 K) (𝓞 (HilbertClassField K)))

-- theorem HilberClassField.extended : ClassGroup.extendedHom (𝓞 K) (𝓞 (HilbertClassField K)) = 1 := sorry

end HilberClassField

end NumberField
end
