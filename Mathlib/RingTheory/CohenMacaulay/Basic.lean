/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.RingTheory.Regular.Depth
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.Algebra.Module.LocalizedModule.AtPrime

/-!
# Definition of Cohen-Macaulay Ring

-/

universe v' v u' u

variable {R : Type u} [CommRing R]

open RingTheory.Sequence IsLocalRing ModuleCat

class ModuleCat.IsCohenMacaulay [IsLocalRing R] [Small.{v} R]
    [Small.{v} (R ⧸ (maximalIdeal R))] (M : ModuleCat.{v} R) : Prop where
  depth_eq_dim : Subsingleton M ∨ Module.supportDim R M = IsLocalRing.depth M

--isCohenMacaulay under iso

--isCohenMacaulay universe invariant

section IsLocalization

variable [IsLocalRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
  [Small.{v} R] [Small.{v} (R ⧸ (maximalIdeal R))]

variable {Rₚ : Type u'} [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
  [IsLocalRing Rₚ]
  -- This can be deduced from `IsLocalization.AtPrime Rₚ p`, but cannot be an
  -- `instance`, so we need to manually add this condition.
  [Small.{v'} Rₚ] [Small.{v'} (Rₚ ⧸ (maximalIdeal Rₚ))]

variable (M : ModuleCat.{v} R) (Mₚ : ModuleCat.{v'} Rₚ)
  [Module R Mₚ] (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f]

include p f

lemma isLocalize_at_prime_isCohenMacaulay_of_isCohenMacaulay [M.IsCohenMacaulay] :
    Mₚ.IsCohenMacaulay := by
  sorry

lemma isLocalize_at_prime_depth_eq_of_isCohenMacaulay [Small.{v} (R ⧸ p)] [M.IsCohenMacaulay] :
    p.depth M = IsLocalRing.depth Mₚ := sorry

end IsLocalization

--have some universe problem may have better statement using `IsLocalizedModule`
lemma localize_at_prime_isCohenMacaulay_of_isCohenMacaulay [IsLocalRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] [Small.{v} R] [Small.{v} (R ⧸ (maximalIdeal R))]
    (M : ModuleCat.{v} R) [M.IsCohenMacaulay] :
    (ModuleCat.of (Localization.AtPrime p) (LocalizedModule.AtPrime p M)).IsCohenMacaulay :=
  isLocalize_at_prime_isCohenMacaulay_of_isCohenMacaulay p M _
    (LocalizedModule.mkLinearMap p.primeCompl M)

--have some universe problem may have better statement using `IsLocalizedModule`
lemma localize_at_prime_depth_eq_of_isCohenMacaulay [IsLocalRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] [Small.{v} R] [Small.{v} (R ⧸ (maximalIdeal R))] [Small.{v} (R ⧸ p)]
    (M : ModuleCat.{v} R) [M.IsCohenMacaulay] : p.depth M =
    IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (LocalizedModule.AtPrime p M)) :=
  isLocalize_at_prime_depth_eq_of_isCohenMacaulay p M _
    (LocalizedModule.mkLinearMap p.primeCompl M)

lemma quotient_regular_isCohenMacaulay_iff_isCohenMacaulay [IsLocalRing R] [IsNoetherianRing R]
    [Small.{v} R] [Small.{v} (R ⧸ maximalIdeal R)]
    (rs : List R) (M : ModuleCat.{v} R) (reg : IsRegular M rs)
    (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    M.IsCohenMacaulay ↔
    (ModuleCat.of R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M))).IsCohenMacaulay := by
  sorry

variable (R)

class IsLocalRing.IsCohenMacaulay [IsLocalRing R] : Prop where
  depth_eq_dim : ringKrullDim R = IsLocalRing.depth (ModuleCat.of R R)

class RingTheory.IsCohenMacaulay : Prop where
  CM_localize : ∀ p : Ideal R, ∀ (_ : p.IsPrime),
    IsLocalRing.IsCohenMacaulay (Localization.AtPrime p)

lemma RingTheory.IsCohenMacaulay_iff : RingTheory.IsCohenMacaulay R ↔
    ∀ m : Ideal R, ∀ (_ : m.IsMaximal), IsLocalRing.IsCohenMacaulay (Localization.AtPrime m) := by
  sorry

--unmixedness theorem

--polynomial ring over CM ring is CM
