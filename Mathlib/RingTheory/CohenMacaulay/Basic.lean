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

universe u v

variable {R : Type u} [CommRing R]

open RingTheory.Sequence IsLocalRing ModuleCat

class ModuleCat.isCohenMacaulay [IsLocalRing R] [Small.{v} R]
    [Small.{v} (R ⧸ (maximalIdeal R))] (M : ModuleCat.{v} R) : Prop where
  depth_eq_dim : Subsingleton M ∨ Module.supportDim R M = IsLocalRing.depth M

--isCohenMacaulay under iso

--isCohenMacaulay universe invariant

--have some universe problem may have better statement using `IsLocalizedModule`
lemma localize_at_prime_isCohenMacaulay_of_isCohenMacaulay [IsLocalRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime]
    [Small.{v} R] [Small.{v} (R ⧸ (maximalIdeal R))] [Small.{v} (R ⧸ p)]
    (M : ModuleCat.{v} R) [M.isCohenMacaulay] :
    (ModuleCat.of (Localization.AtPrime p) (LocalizedModule.AtPrime p M)).isCohenMacaulay := by
  sorry

--have some universe problem may have better statement using `IsLocalizedModule`
lemma localize_at_prime_depth_eq_of_isCohenMacaulay [IsLocalRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime]
    [Small.{v} R] [Small.{v} (R ⧸ (maximalIdeal R))] [Small.{v} (R ⧸ p)]
    (M : ModuleCat.{v} R) [M.isCohenMacaulay] : p.depth M =
    IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (LocalizedModule.AtPrime p M)) := by
  sorry

lemma quotient_regular_isCohenMacaulay_iff_isCohenMacaulay [IsLocalRing R] [IsNoetherianRing R]
    [Small.{v} R] [Small.{v} (R ⧸ maximalIdeal R)]
    (rs : List R) (M : ModuleCat.{v} R) (reg : IsRegular M rs)
    (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    M.isCohenMacaulay ↔
    (ModuleCat.of R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M))).isCohenMacaulay := by
  sorry

variable (R)

class IsLocalRing.isCohenMacaulay [IsLocalRing R] : Prop where
  depth_eq_dim : ringKrullDim R = IsLocalRing.depth (ModuleCat.of R R)

class RingTheory.isCohenMacaulay : Prop where
  CM_localize : ∀ p : Ideal R, ∀ (_ : p.IsPrime),
    IsLocalRing.isCohenMacaulay (Localization.AtPrime p)

lemma RingTheory.isCohenMacaulay_iff : RingTheory.isCohenMacaulay R ↔
    ∀ m : Ideal R, ∀ (_ : m.IsMaximal), IsLocalRing.isCohenMacaulay (Localization.AtPrime m) := by
  sorry

--unmixedness theorem

--polynomial ring over CM ring is CM
