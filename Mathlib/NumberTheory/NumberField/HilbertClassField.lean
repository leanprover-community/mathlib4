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

namespace HilbertClassField

def_wanted HilbertClassField (K : Type*) [Field K] [NumberField K] : Type

variable (K : Type*) [Field K] [NumberField K]

instance_wanted : Field (❰HilbertClassField❱ K)

instance_wanted : Algebra K (❰HilbertClassField❱ K)

instance_wanted : Module.Finite K (❰HilbertClassField❱ K)

instance_wanted instNumberField : NumberField (❰HilbertClassField❱ K) :=
  of_module_finite K (❰HilbertClassField❱ K)

instance_wanted : IsAbelianGalois K (❰HilbertClassField❱ K)

def_wanted HilbertClassField.galoisEquiv :
  Gal((❰HilbertClassField❱ K)/K) ≃* ClassGroup (𝓞 K)

open Algebra

instance_wanted : Unramified (𝓞 K) (𝓞 (❰HilbertClassField❱ K))

instance_wanted : IsUnramifiedAtInfinitePlaces K (❰HilbertClassField❱ K)

theorem_wanted eq_top (H : Type*) [Field H] [Algebra K H] [NumberField H]
      [IsAbelianGalois K H] [Unramified (𝓞 K) (𝓞 H)] [IsUnramifiedAtInfinitePlaces K (H)] :
    Nonempty (H ≃ₐ[K] ❰HilbertClassField❱ K)

variable {K} in
theorem_wanted principal (P : Ideal (𝓞 K)) :
  Submodule.IsPrincipal <| P.map (algebraMap (𝓞 K) (𝓞 (❰HilbertClassField❱ K)))

#synth IsDedekindDomain (𝓞 K)
theorem_wanted classGroupExtendedHom_eq_one :
    ClassGroup.extendedHom (𝓞 K) (𝓞 (❰HilbertClassField❱ K)) = 1 := by
  have := @ClassGroup.extendedHom_eq_one_of_forall_isPrincipal (𝓞 K) (𝓞 (❰HilbertClassField❱ K)) _ _
    _ _ _ ?_
  apply this
  · intro I
    have hpr := @principal K _ _ I ?_ _ _
    sorry
  -- apply isDedekindDom
  have _ : NumberField (❰HilbertClassField❱ K) := instNumberField K
  have := RingOfIntegers.instIsDedekindDomain (❰HilbertClassField❱ K)


end HilbertClassField

end NumberField
end
