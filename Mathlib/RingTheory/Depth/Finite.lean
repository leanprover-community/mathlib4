/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.KrullDimension.Regular

/-!

# Depth over Noetherian Local ring is finite.

In this file, we bound depth by Krull dimension, obtaining it is finite.

## Main Result

* `Ideal.depth_le_supportDim`: For a finitely generated non-zero module `M` over
  Noetherian ring `R` and `I` an ideal of `R` with `IM < M`, then `I.depth M ≤ dim(M)`.

-/

public section

open IsLocalRing LinearMap Module

universe u v

variable {R : Type u} [CommRing R] [Small.{v} R]

lemma Ideal.depth_le_supportDim [IsNoetherianRing R] (I : Ideal R)
    (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M]
    (smul_lt : I • (⊤ : Submodule R M) < ⊤) : I.depth M ≤ supportDim R M := by
  rw [Ideal.depth_eq_sSup_length_isRegular I M smul_lt,
    ← WithBot.le_unbot_iff (supportDim_ne_bot_of_nontrivial R M), sSup_le_iff]
  intro l ⟨rs, reg, mem, len⟩
  rw [← len, WithBot.le_unbot_iff, ENat.WithBot.coe_eq_natCast, ← zero_add (rs.length : WithBot ℕ∞)]
  apply le_trans (add_le_add_left _ _) (supportDim_quotient_add_length_le_of_isRegular rs reg)
  have : Nontrivial (M ⧸ ofList rs • (⊤ : Submodule R M)) := reg.quot_ofList_smul_nontrivial ⊤
  exact supportDim_nonneg_of_nontrivial R _

theorem IsLocalRing.depth_le_supportDim [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M] :
    IsLocalRing.depth M ≤ Module.supportDim R M :=
  Ideal.depth_le_supportDim _ M ((Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    (maximalIdeal_le_jacobson (Module.annihilator R M))).lt_top')

theorem IsLocalRing.depth_le_ringKrullDim [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M] :
    IsLocalRing.depth M ≤ ringKrullDim R :=
  (depth_le_supportDim M).trans (Module.supportDim_le_ringKrullDim R M)

theorem IsLocalRing.depth_ne_top [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M] :
    IsLocalRing.depth M ≠ ⊤ := by
  have := lt_of_le_of_lt (depth_le_ringKrullDim M) ringKrullDim_lt_top
  simp only [← WithBot.coe_top, WithBot.coe_lt_coe] at this
  exact this.ne_top
