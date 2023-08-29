/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Solvable
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.Normalizer
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.RingTheory.Nilpotent
import Mathlib.Tactic.Monotonicity

#align_import algebra.lie.nilpotent from "leanprover-community/mathlib"@"6b0169218d01f2837d79ea2784882009a0da1aa1"

/-!
# Nilpotent Lie algebras

Like groups, Lie algebras admit a natural concept of nilpotency. More generally, any Lie module
carries a natural concept of nilpotency. We define these here via the lower central series.

## Main definitions

  * `LieModule.lowerCentralSeries`
  * `LieModule.IsNilpotent`

## Tags

lie algebra, lower central series, nilpotent
-/


universe u v w w₁ w₂

section NilpotentModules

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

variable (k : ℕ) (N : LieSubmodule R L M)

namespace LieSubmodule

/-- A generalisation of the lower central series. The zeroth term is a specified Lie submodule of
a Lie module. In the case when we specify the top ideal `⊤` of the Lie algebra, regarded as a Lie
module over itself, we get the usual lower central series of a Lie algebra.

It can be more convenient to work with this generalisation when considering the lower central series
of a Lie submodule, regarded as a Lie module in its own right, since it provides a type-theoretic
expression of the fact that the terms of the Lie submodule's lower central series are also Lie
submodules of the enclosing Lie module.

See also `LieSubmodule.lowerCentralSeries_eq_lcs_comap` and
`LieSubmodule.lowerCentralSeries_map_eq_lcs` below, as well as `LieSubmodule.ucs`. -/
def lcs : LieSubmodule R L M → LieSubmodule R L M :=
  (fun N => ⁅(⊤ : LieIdeal R L), N⁆)^[k]
#align lie_submodule.lcs LieSubmodule.lcs

@[simp]
theorem lcs_zero (N : LieSubmodule R L M) : N.lcs 0 = N :=
  rfl
#align lie_submodule.lcs_zero LieSubmodule.lcs_zero

@[simp]
theorem lcs_succ : N.lcs (k + 1) = ⁅(⊤ : LieIdeal R L), N.lcs k⁆ :=
  Function.iterate_succ_apply' (fun N' => ⁅⊤, N'⁆) k N
#align lie_submodule.lcs_succ LieSubmodule.lcs_succ

end LieSubmodule

namespace LieModule

variable (R L M)

/-- The lower central series of Lie submodules of a Lie module. -/
def lowerCentralSeries : LieSubmodule R L M :=
  (⊤ : LieSubmodule R L M).lcs k
#align lie_module.lower_central_series LieModule.lowerCentralSeries

@[simp]
theorem lowerCentralSeries_zero : lowerCentralSeries R L M 0 = ⊤ :=
  rfl
#align lie_module.lower_central_series_zero LieModule.lowerCentralSeries_zero

@[simp]
theorem lowerCentralSeries_succ :
    lowerCentralSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆ :=
  (⊤ : LieSubmodule R L M).lcs_succ k
#align lie_module.lower_central_series_succ LieModule.lowerCentralSeries_succ

end LieModule

namespace LieSubmodule

open LieModule

theorem lcs_le_self : N.lcs k ≤ N := by
  induction' k with k ih
  -- ⊢ lcs Nat.zero N ≤ N
  · simp
    -- 🎉 no goals
  · simp only [lcs_succ]
    -- ⊢ ⁅⊤, lcs k N⁆ ≤ N
    exact (LieSubmodule.mono_lie_right _ _ ⊤ ih).trans (N.lie_le_right ⊤)
    -- 🎉 no goals
#align lie_submodule.lcs_le_self LieSubmodule.lcs_le_self

theorem lowerCentralSeries_eq_lcs_comap : lowerCentralSeries R L N k = (N.lcs k).comap N.incl := by
  induction' k with k ih
  -- ⊢ lowerCentralSeries R L { x // x ∈ ↑N } Nat.zero = comap (incl N) (lcs Nat.ze …
  · simp
    -- 🎉 no goals
  · simp only [lcs_succ, lowerCentralSeries_succ] at ih ⊢
    -- ⊢ ⁅⊤, lowerCentralSeries R L { x // x ∈ ↑N } k⁆ = comap (incl N) ⁅⊤, lcs k N⁆
    have : N.lcs k ≤ N.incl.range := by
      rw [N.range_incl]
      apply lcs_le_self
    rw [ih, LieSubmodule.comap_bracket_eq _ _ N.incl N.ker_incl this]
    -- 🎉 no goals
#align lie_submodule.lower_central_series_eq_lcs_comap LieSubmodule.lowerCentralSeries_eq_lcs_comap

theorem lowerCentralSeries_map_eq_lcs : (lowerCentralSeries R L N k).map N.incl = N.lcs k := by
  rw [lowerCentralSeries_eq_lcs_comap, LieSubmodule.map_comap_incl, inf_eq_right]
  -- ⊢ lcs k N ≤ N
  apply lcs_le_self
  -- 🎉 no goals
#align lie_submodule.lower_central_series_map_eq_lcs LieSubmodule.lowerCentralSeries_map_eq_lcs

end LieSubmodule

namespace LieModule

variable (R L M)

theorem antitone_lowerCentralSeries : Antitone <| lowerCentralSeries R L M := by
  intro l k
  -- ⊢ l ≤ k → lowerCentralSeries R L M k ≤ lowerCentralSeries R L M l
  induction' k with k ih generalizing l <;> intro h
  -- ⊢ l ≤ Nat.zero → lowerCentralSeries R L M Nat.zero ≤ lowerCentralSeries R L M l
                                            -- ⊢ lowerCentralSeries R L M Nat.zero ≤ lowerCentralSeries R L M l
                                            -- ⊢ lowerCentralSeries R L M (Nat.succ k) ≤ lowerCentralSeries R L M l
  · exact (le_zero_iff.mp h).symm ▸ le_rfl
    -- 🎉 no goals
  · rcases Nat.of_le_succ h with (hk | hk)
    -- ⊢ lowerCentralSeries R L M (Nat.succ k) ≤ lowerCentralSeries R L M l
    · rw [lowerCentralSeries_succ]
      -- ⊢ ⁅⊤, lowerCentralSeries R L M k⁆ ≤ lowerCentralSeries R L M l
      exact (LieSubmodule.mono_lie_right _ _ ⊤ (ih hk)).trans (LieSubmodule.lie_le_right _ _)
      -- 🎉 no goals
    · exact hk.symm ▸ le_rfl
      -- 🎉 no goals
#align lie_module.antitone_lower_central_series LieModule.antitone_lowerCentralSeries

theorem trivial_iff_lower_central_eq_bot : IsTrivial L M ↔ lowerCentralSeries R L M 1 = ⊥ := by
  constructor <;> intro h
  -- ⊢ IsTrivial L M → lowerCentralSeries R L M 1 = ⊥
                  -- ⊢ lowerCentralSeries R L M 1 = ⊥
                  -- ⊢ IsTrivial L M
  · erw [eq_bot_iff, LieSubmodule.lieSpan_le]; rintro m ⟨x, n, hn⟩; rw [← hn, h.trivial]; simp
    -- ⊢ {m | ∃ x n, ⁅↑x, ↑n⁆ = m} ⊆ ↑⊥
                                               -- ⊢ m ∈ ↑⊥
                                                                    -- ⊢ 0 ∈ ↑⊥
                                                                                          -- 🎉 no goals
  · rw [LieSubmodule.eq_bot_iff] at h; apply IsTrivial.mk; intro x m; apply h
    -- ⊢ IsTrivial L M
                                       -- ⊢ ∀ (x : L) (m : M), ⁅x, m⁆ = 0
                                                           -- ⊢ ⁅x, m⁆ = 0
                                                                      -- ⊢ ⁅x, m⁆ ∈ lowerCentralSeries R L M 1
    apply LieSubmodule.subset_lieSpan
    -- ⊢ ⁅x, m⁆ ∈ {m | ∃ x n, ⁅↑x, ↑n⁆ = m}
    -- Porting note: was `use x, m; rfl`
    simp only [LieSubmodule.top_coe, Subtype.exists, LieSubmodule.mem_top, exists_prop, true_and,
      Set.mem_setOf]
    exact ⟨x, m, rfl⟩
    -- 🎉 no goals
#align lie_module.trivial_iff_lower_central_eq_bot LieModule.trivial_iff_lower_central_eq_bot

theorem iterate_toEndomorphism_mem_lowerCentralSeries (x : L) (m : M) (k : ℕ) :
    (toEndomorphism R L M x)^[k] m ∈ lowerCentralSeries R L M k := by
  induction' k with k ih
  -- ⊢ (↑(↑(toEndomorphism R L M) x))^[Nat.zero] m ∈ lowerCentralSeries R L M Nat.z …
  · simp only [Nat.zero_eq, Function.iterate_zero, lowerCentralSeries_zero, LieSubmodule.mem_top]
    -- 🎉 no goals
  · simp only [lowerCentralSeries_succ, Function.comp_apply, Function.iterate_succ',
      toEndomorphism_apply_apply]
    exact LieSubmodule.lie_mem_lie _ _ (LieSubmodule.mem_top x) ih
    -- 🎉 no goals
#align lie_module.iterate_to_endomorphism_mem_lower_central_series LieModule.iterate_toEndomorphism_mem_lowerCentralSeries

theorem iterate_toEndomorphism_mem_lowerCentralSeries₂ (x y : L) (m : M) (k : ℕ) :
    (toEndomorphism R L M x ∘ₗ toEndomorphism R L M y)^[k] m ∈
      lowerCentralSeries R L M (2 * k) := by
  induction' k with k ih; simp
  -- ⊢ (↑(LinearMap.comp (↑(toEndomorphism R L M) x) (↑(toEndomorphism R L M) y)))^ …
                          -- ⊢ (↑(LinearMap.comp (↑(toEndomorphism R L M) x) (↑(toEndomorphism R L M) y)))^ …
  have hk : 2 * k.succ = (2 * k + 1) + 1 := rfl
  -- ⊢ (↑(LinearMap.comp (↑(toEndomorphism R L M) x) (↑(toEndomorphism R L M) y)))^ …
  simp only [lowerCentralSeries_succ, Function.comp_apply, Function.iterate_succ', hk,
      toEndomorphism_apply_apply, LinearMap.coe_comp, toEndomorphism_apply_apply]
  refine' LieSubmodule.lie_mem_lie _ _ (LieSubmodule.mem_top x) _
  -- ⊢ ⁅y, (↑(↑(toEndomorphism R L M) x) ∘ ↑(↑(toEndomorphism R L M) y))^[k] m⁆ ∈ ⁅ …
  exact LieSubmodule.lie_mem_lie _ _ (LieSubmodule.mem_top y) ih
  -- 🎉 no goals

variable {R L M}

theorem map_lowerCentralSeries_le {M₂ : Type w₁} [AddCommGroup M₂] [Module R M₂]
    [LieRingModule L M₂] [LieModule R L M₂] (k : ℕ) (f : M →ₗ⁅R,L⁆ M₂) :
    LieSubmodule.map f (lowerCentralSeries R L M k) ≤ lowerCentralSeries R L M₂ k := by
  induction' k with k ih
  -- ⊢ LieSubmodule.map f (lowerCentralSeries R L M Nat.zero) ≤ lowerCentralSeries  …
  · simp only [Nat.zero_eq, lowerCentralSeries_zero, le_top]
    -- 🎉 no goals
  · simp only [LieModule.lowerCentralSeries_succ, LieSubmodule.map_bracket_eq]
    -- ⊢ ⁅⊤, LieSubmodule.map f (lowerCentralSeries R L M k)⁆ ≤ ⁅⊤, lowerCentralSerie …
    exact LieSubmodule.mono_lie_right _ _ ⊤ ih
    -- 🎉 no goals
#align lie_module.map_lower_central_series_le LieModule.map_lowerCentralSeries_le

variable (R L M)

open LieAlgebra

theorem derivedSeries_le_lowerCentralSeries (k : ℕ) :
    derivedSeries R L k ≤ lowerCentralSeries R L L k := by
  induction' k with k h
  -- ⊢ derivedSeries R L Nat.zero ≤ lowerCentralSeries R L L Nat.zero
  · rw [derivedSeries_def, derivedSeriesOfIdeal_zero, lowerCentralSeries_zero]
    -- 🎉 no goals
  · have h' : derivedSeries R L k ≤ ⊤ := by simp only [le_top]
    -- ⊢ derivedSeries R L (Nat.succ k) ≤ lowerCentralSeries R L L (Nat.succ k)
    rw [derivedSeries_def, derivedSeriesOfIdeal_succ, lowerCentralSeries_succ]
    -- ⊢ ⁅derivedSeriesOfIdeal R L k ⊤, derivedSeriesOfIdeal R L k ⊤⁆ ≤ ⁅⊤, lowerCent …
    exact LieSubmodule.mono_lie _ _ _ _ h' h
    -- 🎉 no goals
#align lie_module.derived_series_le_lower_central_series LieModule.derivedSeries_le_lowerCentralSeries

/-- A Lie module is nilpotent if its lower central series reaches 0 (in a finite number of
steps). -/
class IsNilpotent : Prop where
  nilpotent : ∃ k, lowerCentralSeries R L M k = ⊥
#align lie_module.is_nilpotent LieModule.IsNilpotent

theorem exists_lowerCentralSeries_eq_bot_of_isNilpotent [IsNilpotent R L M] :
    ∃ k, lowerCentralSeries R L M k = ⊥ :=
  IsNilpotent.nilpotent

/-- See also `LieModule.isNilpotent_iff_exists_ucs_eq_top`. -/
theorem isNilpotent_iff : IsNilpotent R L M ↔ ∃ k, lowerCentralSeries R L M k = ⊥ :=
  ⟨fun h => h.nilpotent, fun h => ⟨h⟩⟩
#align lie_module.is_nilpotent_iff LieModule.isNilpotent_iff

variable {R L M}

theorem _root_.LieSubmodule.isNilpotent_iff_exists_lcs_eq_bot (N : LieSubmodule R L M) :
    LieModule.IsNilpotent R L N ↔ ∃ k, N.lcs k = ⊥ := by
  rw [isNilpotent_iff]
  -- ⊢ (∃ k, lowerCentralSeries R L { x // x ∈ ↑N } k = ⊥) ↔ ∃ k, LieSubmodule.lcs  …
  refine' exists_congr fun k => _
  -- ⊢ lowerCentralSeries R L { x // x ∈ ↑N } k = ⊥ ↔ LieSubmodule.lcs k N = ⊥
  rw [N.lowerCentralSeries_eq_lcs_comap k, LieSubmodule.comap_incl_eq_bot,
    inf_eq_right.mpr (N.lcs_le_self k)]
#align lie_submodule.is_nilpotent_iff_exists_lcs_eq_bot LieSubmodule.isNilpotent_iff_exists_lcs_eq_bot

variable (R L M)

instance (priority := 100) trivialIsNilpotent [IsTrivial L M] : IsNilpotent R L M :=
  ⟨by use 1; change ⁅⊤, ⊤⁆ = ⊥; simp⟩
      -- ⊢ lowerCentralSeries R L M 1 = ⊥
             -- ⊢ ⁅⊤, ⊤⁆ = ⊥
                                -- 🎉 no goals
#align lie_module.trivial_is_nilpotent LieModule.trivialIsNilpotent

theorem exists_forall_pow_toEndomorphism_eq_zero [hM : IsNilpotent R L M] :
    ∃ k : ℕ, ∀ x : L, toEndomorphism R L M x ^ k = 0 := by
  obtain ⟨k, hM⟩ := hM
  -- ⊢ ∃ k, ∀ (x : L), ↑(toEndomorphism R L M) x ^ k = 0
  use k
  -- ⊢ ∀ (x : L), ↑(toEndomorphism R L M) x ^ k = 0
  intro x; ext m
  -- ⊢ ↑(toEndomorphism R L M) x ^ k = 0
           -- ⊢ ↑(↑(toEndomorphism R L M) x ^ k) m = ↑0 m
  rw [LinearMap.pow_apply, LinearMap.zero_apply, ← @LieSubmodule.mem_bot R L M, ← hM]
  -- ⊢ (↑(↑(toEndomorphism R L M) x))^[k] m ∈ lowerCentralSeries R L M k
  exact iterate_toEndomorphism_mem_lowerCentralSeries R L M x m k
  -- 🎉 no goals
#align lie_module.nilpotent_endo_of_nilpotent_module LieModule.exists_forall_pow_toEndomorphism_eq_zero

theorem isNilpotent_toEndomorphism_of_isNilpotent [IsNilpotent R L M] (x : L) :
    _root_.IsNilpotent (toEndomorphism R L M x) := by
  change ∃ k, toEndomorphism R L M x ^ k = 0
  -- ⊢ ∃ k, ↑(toEndomorphism R L M) x ^ k = 0
  have := exists_forall_pow_toEndomorphism_eq_zero R L M
  -- ⊢ ∃ k, ↑(toEndomorphism R L M) x ^ k = 0
  tauto
  -- 🎉 no goals

theorem isNilpotent_toEndomorphism_of_isNilpotent₂ [IsNilpotent R L M] (x y : L) :
    _root_.IsNilpotent (toEndomorphism R L M x ∘ₗ toEndomorphism R L M y) := by
  obtain ⟨k, hM⟩ := exists_lowerCentralSeries_eq_bot_of_isNilpotent R L M
  -- ⊢ _root_.IsNilpotent (LinearMap.comp (↑(toEndomorphism R L M) x) (↑(toEndomorp …
  replace hM : lowerCentralSeries R L M (2 * k) = ⊥ := by
    rw [eq_bot_iff, ← hM]; exact antitone_lowerCentralSeries R L M (by linarith)
  use k
  -- ⊢ LinearMap.comp (↑(toEndomorphism R L M) x) (↑(toEndomorphism R L M) y) ^ k = 0
  ext m
  -- ⊢ ↑(LinearMap.comp (↑(toEndomorphism R L M) x) (↑(toEndomorphism R L M) y) ^ k …
  rw [LinearMap.pow_apply, LinearMap.zero_apply, ← LieSubmodule.mem_bot (R := R) (L := L), ← hM]
  -- ⊢ (↑(LinearMap.comp (↑(toEndomorphism R L M) x) (↑(toEndomorphism R L M) y)))^ …
  exact iterate_toEndomorphism_mem_lowerCentralSeries₂ R L M x y m k
  -- 🎉 no goals

/-- For a nilpotent Lie module, the weight space of the 0 weight is the whole module.

This result will be used downstream to show that weight spaces are Lie submodules, at which time
it will be possible to state it in the language of weight spaces. -/
theorem iInf_max_gen_zero_eigenspace_eq_top_of_nilpotent [IsNilpotent R L M] :
    ⨅ x : L, (toEndomorphism R L M x).maximalGeneralizedEigenspace 0 = ⊤ := by
  ext m
  -- ⊢ m ∈ ⨅ (x : L), Module.End.maximalGeneralizedEigenspace (↑(toEndomorphism R L …
  simp only [Module.End.mem_maximalGeneralizedEigenspace, Submodule.mem_top, sub_zero, iff_true_iff,
    zero_smul, Submodule.mem_iInf]
  intro x
  -- ⊢ ∃ k, ↑(↑(toEndomorphism R L M) x ^ k) m = 0
  obtain ⟨k, hk⟩ := exists_forall_pow_toEndomorphism_eq_zero R L M
  -- ⊢ ∃ k, ↑(↑(toEndomorphism R L M) x ^ k) m = 0
  use k; rw [hk]
  -- ⊢ ↑(↑(toEndomorphism R L M) x ^ k) m = 0
         -- ⊢ ↑0 m = 0
  exact LinearMap.zero_apply m
  -- 🎉 no goals
#align lie_module.infi_max_gen_zero_eigenspace_eq_top_of_nilpotent LieModule.iInf_max_gen_zero_eigenspace_eq_top_of_nilpotent

/-- If the quotient of a Lie module `M` by a Lie submodule on which the Lie algebra acts trivially
is nilpotent then `M` is nilpotent.

This is essentially the Lie module equivalent of the fact that a central
extension of nilpotent Lie algebras is nilpotent. See `LieAlgebra.nilpotent_of_nilpotent_quotient`
below for the corresponding result for Lie algebras. -/
theorem nilpotentOfNilpotentQuotient {N : LieSubmodule R L M} (h₁ : N ≤ maxTrivSubmodule R L M)
    (h₂ : IsNilpotent R L (M ⧸ N)) : IsNilpotent R L M := by
  obtain ⟨k, hk⟩ := h₂
  -- ⊢ IsNilpotent R L M
  use k + 1
  -- ⊢ lowerCentralSeries R L M (k + 1) = ⊥
  simp only [lowerCentralSeries_succ]
  -- ⊢ ⁅⊤, lowerCentralSeries R L M k⁆ = ⊥
  suffices lowerCentralSeries R L M k ≤ N by
    replace this := LieSubmodule.mono_lie_right _ _ ⊤ (le_trans this h₁)
    rwa [ideal_oper_maxTrivSubmodule_eq_bot, le_bot_iff] at this
  rw [← LieSubmodule.Quotient.map_mk'_eq_bot_le, ← le_bot_iff, ← hk]
  -- ⊢ LieSubmodule.map (LieSubmodule.Quotient.mk' N) (lowerCentralSeries R L M k)  …
  exact map_lowerCentralSeries_le k (LieSubmodule.Quotient.mk' N)
  -- 🎉 no goals
#align lie_module.nilpotent_of_nilpotent_quotient LieModule.nilpotentOfNilpotentQuotient

/-- Given a nilpotent Lie module `M` with lower central series `M = C₀ ≥ C₁ ≥ ⋯ ≥ Cₖ = ⊥`, this is
the natural number `k` (the number of inclusions).

For a non-nilpotent module, we use the junk value 0. -/
noncomputable def nilpotencyLength : ℕ :=
  sInf {k | lowerCentralSeries R L M k = ⊥}
#align lie_module.nilpotency_length LieModule.nilpotencyLength

theorem nilpotencyLength_eq_zero_iff [IsNilpotent R L M] :
    nilpotencyLength R L M = 0 ↔ Subsingleton M := by
  let s := {k | lowerCentralSeries R L M k = ⊥}
  -- ⊢ nilpotencyLength R L M = 0 ↔ Subsingleton M
  have hs : s.Nonempty := by
    obtain ⟨k, hk⟩ := (by infer_instance : IsNilpotent R L M)
    exact ⟨k, hk⟩
  change sInf s = 0 ↔ _
  -- ⊢ sInf s = 0 ↔ Subsingleton M
  rw [← LieSubmodule.subsingleton_iff R L M, ← subsingleton_iff_bot_eq_top, ←
    lowerCentralSeries_zero, @eq_comm (LieSubmodule R L M)]
  refine' ⟨fun h => h ▸ Nat.sInf_mem hs, fun h => _⟩
  -- ⊢ sInf s = 0
  rw [Nat.sInf_eq_zero]
  -- ⊢ 0 ∈ s ∨ s = ∅
  exact Or.inl h
  -- 🎉 no goals
#align lie_module.nilpotency_length_eq_zero_iff LieModule.nilpotencyLength_eq_zero_iff

theorem nilpotencyLength_eq_succ_iff (k : ℕ) :
    nilpotencyLength R L M = k + 1 ↔
      lowerCentralSeries R L M (k + 1) = ⊥ ∧ lowerCentralSeries R L M k ≠ ⊥ := by
  let s := {k | lowerCentralSeries R L M k = ⊥}
  -- ⊢ nilpotencyLength R L M = k + 1 ↔ lowerCentralSeries R L M (k + 1) = ⊥ ∧ lowe …
  change sInf s = k + 1 ↔ k + 1 ∈ s ∧ k ∉ s
  -- ⊢ sInf s = k + 1 ↔ k + 1 ∈ s ∧ ¬k ∈ s
  have hs : ∀ k₁ k₂, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s := by
    rintro k₁ k₂ h₁₂ (h₁ : lowerCentralSeries R L M k₁ = ⊥)
    exact eq_bot_iff.mpr (h₁ ▸ antitone_lowerCentralSeries R L M h₁₂)
  exact Nat.sInf_upward_closed_eq_succ_iff hs k
  -- 🎉 no goals
#align lie_module.nilpotency_length_eq_succ_iff LieModule.nilpotencyLength_eq_succ_iff

/-- Given a non-trivial nilpotent Lie module `M` with lower central series
`M = C₀ ≥ C₁ ≥ ⋯ ≥ Cₖ = ⊥`, this is the `k-1`th term in the lower central series (the last
non-trivial term).

For a trivial or non-nilpotent module, this is the bottom submodule, `⊥`. -/
noncomputable def lowerCentralSeriesLast : LieSubmodule R L M :=
  match nilpotencyLength R L M with
  | 0 => ⊥
  | k + 1 => lowerCentralSeries R L M k
#align lie_module.lower_central_series_last LieModule.lowerCentralSeriesLast

theorem lowerCentralSeriesLast_le_max_triv :
    lowerCentralSeriesLast R L M ≤ maxTrivSubmodule R L M := by
  rw [lowerCentralSeriesLast]
  -- ⊢ (match nilpotencyLength R L M with
  cases' h : nilpotencyLength R L M with k
  · exact bot_le
    -- 🎉 no goals
  · rw [le_max_triv_iff_bracket_eq_bot]
    -- ⊢ ⁅⊤,
    rw [nilpotencyLength_eq_succ_iff, lowerCentralSeries_succ] at h
    -- ⊢ ⁅⊤,
    exact h.1
    -- 🎉 no goals
#align lie_module.lower_central_series_last_le_max_triv LieModule.lowerCentralSeriesLast_le_max_triv

theorem nontrivial_lowerCentralSeriesLast [Nontrivial M] [IsNilpotent R L M] :
    Nontrivial (lowerCentralSeriesLast R L M) := by
  rw [LieSubmodule.nontrivial_iff_ne_bot, lowerCentralSeriesLast]
  -- ⊢ (match nilpotencyLength R L M with
  cases h : nilpotencyLength R L M
  · rw [nilpotencyLength_eq_zero_iff, ← not_nontrivial_iff_subsingleton] at h
    -- ⊢ (match Nat.zero with
    contradiction
    -- 🎉 no goals
  · rw [nilpotencyLength_eq_succ_iff] at h
    -- ⊢ (match Nat.succ n✝ with
    exact h.2
    -- 🎉 no goals
#align lie_module.nontrivial_lower_central_series_last LieModule.nontrivial_lowerCentralSeriesLast

theorem nontrivial_max_triv_of_isNilpotent [Nontrivial M] [IsNilpotent R L M] :
    Nontrivial (maxTrivSubmodule R L M) :=
  Set.nontrivial_mono (lowerCentralSeriesLast_le_max_triv R L M)
    (nontrivial_lowerCentralSeriesLast R L M)
#align lie_module.nontrivial_max_triv_of_is_nilpotent LieModule.nontrivial_max_triv_of_isNilpotent

@[simp]
theorem coe_lcs_range_toEndomorphism_eq (k : ℕ) :
    (lowerCentralSeries R (toEndomorphism R L M).range M k : Submodule R M) =
      lowerCentralSeries R L M k := by
  induction' k with k ih
  -- ⊢ ↑(lowerCentralSeries R { x // x ∈ LieHom.range (toEndomorphism R L M) } M Na …
  · simp
    -- 🎉 no goals
  · simp only [lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span', ←
      (lowerCentralSeries R (toEndomorphism R L M).range M k).mem_coeSubmodule, ih]
    congr
    -- ⊢ {m | ∃ x, x ∈ ⊤ ∧ ∃ n, n ∈ ↑(lowerCentralSeries R L M k) ∧ ⁅x, n⁆ = m} = {m  …
    ext m
    -- ⊢ m ∈ {m | ∃ x, x ∈ ⊤ ∧ ∃ n, n ∈ ↑(lowerCentralSeries R L M k) ∧ ⁅x, n⁆ = m} ↔ …
    constructor
    -- ⊢ m ∈ {m | ∃ x, x ∈ ⊤ ∧ ∃ n, n ∈ ↑(lowerCentralSeries R L M k) ∧ ⁅x, n⁆ = m} → …
    · rintro ⟨⟨-, ⟨y, rfl⟩⟩, -, n, hn, rfl⟩
      -- ⊢ ⁅{ val := ↑↑(toEndomorphism R L M) y, property := (_ : ∃ y_1, ↑↑(toEndomorph …
      exact ⟨y, LieSubmodule.mem_top _, n, hn, rfl⟩
      -- 🎉 no goals
    · rintro ⟨x, -, n, hn, rfl⟩
      -- ⊢ ⁅x, n⁆ ∈ {m | ∃ x, x ∈ ⊤ ∧ ∃ n, n ∈ ↑(lowerCentralSeries R L M k) ∧ ⁅x, n⁆ = …
      exact
        ⟨⟨toEndomorphism R L M x, LieHom.mem_range_self _ x⟩, LieSubmodule.mem_top _, n, hn, rfl⟩
#align lie_module.coe_lcs_range_to_endomorphism_eq LieModule.coe_lcs_range_toEndomorphism_eq

@[simp]
theorem isNilpotent_range_toEndomorphism_iff :
    IsNilpotent R (toEndomorphism R L M).range M ↔ IsNilpotent R L M := by
  constructor <;> rintro ⟨k, hk⟩ <;> use k <;>
  -- ⊢ IsNilpotent R { x // x ∈ LieHom.range (toEndomorphism R L M) } M → IsNilpote …
                  -- ⊢ IsNilpotent R L M
                  -- ⊢ IsNilpotent R { x // x ∈ LieHom.range (toEndomorphism R L M) } M
                                     -- ⊢ lowerCentralSeries R L M k = ⊥
                                     -- ⊢ lowerCentralSeries R { x // x ∈ LieHom.range (toEndomorphism R L M) } M k = ⊥
      rw [← LieSubmodule.coe_toSubmodule_eq_iff] at hk ⊢ <;>
      -- ⊢ ↑(lowerCentralSeries R L M k) = ↑⊥
      -- ⊢ ↑(lowerCentralSeries R { x // x ∈ LieHom.range (toEndomorphism R L M) } M k) …
    simpa using hk
    -- 🎉 no goals
    -- 🎉 no goals
#align lie_module.is_nilpotent_range_to_endomorphism_iff LieModule.isNilpotent_range_toEndomorphism_iff

end LieModule

namespace LieSubmodule

variable {N₁ N₂ : LieSubmodule R L M}

/-- The upper (aka ascending) central series.

See also `LieSubmodule.lcs`. -/
def ucs (k : ℕ) : LieSubmodule R L M → LieSubmodule R L M :=
  normalizer^[k]
#align lie_submodule.ucs LieSubmodule.ucs

@[simp]
theorem ucs_zero : N.ucs 0 = N :=
  rfl
#align lie_submodule.ucs_zero LieSubmodule.ucs_zero

@[simp]
theorem ucs_succ (k : ℕ) : N.ucs (k + 1) = (N.ucs k).normalizer :=
  Function.iterate_succ_apply' normalizer k N
#align lie_submodule.ucs_succ LieSubmodule.ucs_succ

theorem ucs_add (k l : ℕ) : N.ucs (k + l) = (N.ucs l).ucs k :=
  Function.iterate_add_apply normalizer k l N
#align lie_submodule.ucs_add LieSubmodule.ucs_add

@[mono]
theorem ucs_mono (k : ℕ) (h : N₁ ≤ N₂) : N₁.ucs k ≤ N₂.ucs k := by
  induction' k with k ih
  -- ⊢ ucs Nat.zero N₁ ≤ ucs Nat.zero N₂
  · simpa
    -- 🎉 no goals
  simp only [ucs_succ]
  -- ⊢ normalizer (ucs k N₁) ≤ normalizer (ucs k N₂)
  -- Porting note: `mono` makes no progress
  apply monotone_normalizer ih
  -- 🎉 no goals
#align lie_submodule.ucs_mono LieSubmodule.ucs_mono

theorem ucs_eq_self_of_normalizer_eq_self (h : N₁.normalizer = N₁) (k : ℕ) : N₁.ucs k = N₁ := by
  induction' k with k ih
  -- ⊢ ucs Nat.zero N₁ = N₁
  · simp
    -- 🎉 no goals
  · rwa [ucs_succ, ih]
    -- 🎉 no goals
#align lie_submodule.ucs_eq_self_of_normalizer_eq_self LieSubmodule.ucs_eq_self_of_normalizer_eq_self

/-- If a Lie module `M` contains a self-normalizing Lie submodule `N`, then all terms of the upper
central series of `M` are contained in `N`.

An important instance of this situation arises from a Cartan subalgebra `H ⊆ L` with the roles of
`L`, `M`, `N` played by `H`, `L`, `H`, respectively. -/
theorem ucs_le_of_normalizer_eq_self (h : N₁.normalizer = N₁) (k : ℕ) :
    (⊥ : LieSubmodule R L M).ucs k ≤ N₁ := by
  rw [← ucs_eq_self_of_normalizer_eq_self h k]
  -- ⊢ ucs k ⊥ ≤ ucs k N₁
  mono
  -- ⊢ ⊥ ≤ N₁
  simp
  -- 🎉 no goals
#align lie_submodule.ucs_le_of_normalizer_eq_self LieSubmodule.ucs_le_of_normalizer_eq_self

theorem lcs_add_le_iff (l k : ℕ) : N₁.lcs (l + k) ≤ N₂ ↔ N₁.lcs l ≤ N₂.ucs k := by
  induction' k with k ih generalizing l
  -- ⊢ lcs (l + Nat.zero) N₁ ≤ N₂ ↔ lcs l N₁ ≤ ucs Nat.zero N₂
  · simp
    -- 🎉 no goals
  rw [(by abel : l + (k + 1) = l + 1 + k), ih, ucs_succ, lcs_succ, top_lie_le_iff_le_normalizer]
  -- 🎉 no goals
#align lie_submodule.lcs_add_le_iff LieSubmodule.lcs_add_le_iff

theorem lcs_le_iff (k : ℕ) : N₁.lcs k ≤ N₂ ↔ N₁ ≤ N₂.ucs k := by
  -- Porting note: `convert` needed type annotations
  convert lcs_add_le_iff (R := R) (L := L) (M := M) 0 k
  -- ⊢ k = 0 + k
  rw [zero_add]
  -- 🎉 no goals
#align lie_submodule.lcs_le_iff LieSubmodule.lcs_le_iff

theorem gc_lcs_ucs (k : ℕ) :
    GaloisConnection (fun N : LieSubmodule R L M => N.lcs k) fun N : LieSubmodule R L M =>
      N.ucs k :=
  fun _ _ => lcs_le_iff k
#align lie_submodule.gc_lcs_ucs LieSubmodule.gc_lcs_ucs

theorem ucs_eq_top_iff (k : ℕ) : N.ucs k = ⊤ ↔ LieModule.lowerCentralSeries R L M k ≤ N := by
  rw [eq_top_iff, ← lcs_le_iff]; rfl
  -- ⊢ lcs k ⊤ ≤ N ↔ LieModule.lowerCentralSeries R L M k ≤ N
                                 -- 🎉 no goals
#align lie_submodule.ucs_eq_top_iff LieSubmodule.ucs_eq_top_iff

theorem _root_.LieModule.isNilpotent_iff_exists_ucs_eq_top :
    LieModule.IsNilpotent R L M ↔ ∃ k, (⊥ : LieSubmodule R L M).ucs k = ⊤ := by
  rw [LieModule.isNilpotent_iff]; exact exists_congr fun k => by simp [ucs_eq_top_iff]
  -- ⊢ (∃ k, LieModule.lowerCentralSeries R L M k = ⊥) ↔ ∃ k, ucs k ⊥ = ⊤
                                  -- 🎉 no goals
#align lie_module.is_nilpotent_iff_exists_ucs_eq_top LieModule.isNilpotent_iff_exists_ucs_eq_top

theorem ucs_comap_incl (k : ℕ) :
    ((⊥ : LieSubmodule R L M).ucs k).comap N.incl = (⊥ : LieSubmodule R L N).ucs k := by
  induction' k with k ih
  -- ⊢ comap (incl N) (ucs Nat.zero ⊥) = ucs Nat.zero ⊥
  · exact N.ker_incl
    -- 🎉 no goals
  · simp [← ih]
    -- 🎉 no goals
#align lie_submodule.ucs_comap_incl LieSubmodule.ucs_comap_incl

theorem isNilpotent_iff_exists_self_le_ucs :
    LieModule.IsNilpotent R L N ↔ ∃ k, N ≤ (⊥ : LieSubmodule R L M).ucs k := by
  simp_rw [LieModule.isNilpotent_iff_exists_ucs_eq_top, ← ucs_comap_incl, comap_incl_eq_top]
  -- 🎉 no goals
#align lie_submodule.is_nilpotent_iff_exists_self_le_ucs LieSubmodule.isNilpotent_iff_exists_self_le_ucs

end LieSubmodule

section Morphisms

open LieModule Function

variable {L₂ M₂ : Type*} [LieRing L₂] [LieAlgebra R L₂]

variable [AddCommGroup M₂] [Module R M₂] [LieRingModule L₂ M₂] [LieModule R L₂ M₂]

variable {f : L →ₗ⁅R⁆ L₂} {g : M →ₗ[R] M₂}

variable (hf : Surjective f) (hg : Surjective g) (hfg : ∀ x m, ⁅f x, g m⁆ = g ⁅x, m⁆)

theorem Function.Surjective.lieModule_lcs_map_eq (k : ℕ) :
    (lowerCentralSeries R L M k : Submodule R M).map g = lowerCentralSeries R L₂ M₂ k := by
  induction' k with k ih
  -- ⊢ Submodule.map g ↑(lowerCentralSeries R L M Nat.zero) = ↑(lowerCentralSeries  …
  · simpa [LinearMap.range_eq_top]
    -- 🎉 no goals
  · suffices
      g '' {m | ∃ (x : L) (n : _), n ∈ lowerCentralSeries R L M k ∧ ⁅x, n⁆ = m} =
        {m | ∃ (x : L₂) (n : _), n ∈ lowerCentralSeries R L M k ∧ ⁅x, g n⁆ = m} by
      simp only [← LieSubmodule.mem_coeSubmodule] at this
      -- Porting note: was
      -- simp [← LieSubmodule.mem_coeSubmodule, ← ih, LieSubmodule.lieIdeal_oper_eq_linear_span',
      --   Submodule.map_span, -Submodule.span_image, this,
      --   -LieSubmodule.mem_coeSubmodule]
      simp_rw [lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span',
        Submodule.map_span, LieSubmodule.mem_top, true_and, ← LieSubmodule.mem_coeSubmodule, this,
        ← ih, Submodule.mem_map, exists_exists_and_eq_and]
    ext m₂
    -- ⊢ m₂ ∈ ↑g '' {m | ∃ x n, n ∈ lowerCentralSeries R L M k ∧ ⁅x, n⁆ = m} ↔ m₂ ∈ { …
    constructor
    -- ⊢ m₂ ∈ ↑g '' {m | ∃ x n, n ∈ lowerCentralSeries R L M k ∧ ⁅x, n⁆ = m} → m₂ ∈ { …
    · rintro ⟨m, ⟨x, n, hn, rfl⟩, rfl⟩
      -- ⊢ ↑g ⁅x, n⁆ ∈ {m | ∃ x n, n ∈ lowerCentralSeries R L M k ∧ ⁅x, ↑g n⁆ = m}
      exact ⟨f x, n, hn, hfg x n⟩
      -- 🎉 no goals
    · rintro ⟨x, n, hn, rfl⟩
      -- ⊢ ⁅x, ↑g n⁆ ∈ ↑g '' {m | ∃ x n, n ∈ lowerCentralSeries R L M k ∧ ⁅x, n⁆ = m}
      obtain ⟨y, rfl⟩ := hf x
      -- ⊢ ⁅↑f y, ↑g n⁆ ∈ ↑g '' {m | ∃ x n, n ∈ lowerCentralSeries R L M k ∧ ⁅x, n⁆ = m}
      exact ⟨⁅y, n⁆, ⟨y, n, hn, rfl⟩, (hfg y n).symm⟩
      -- 🎉 no goals
#align function.surjective.lie_module_lcs_map_eq Function.Surjective.lieModule_lcs_map_eq

theorem Function.Surjective.lieModuleIsNilpotent [IsNilpotent R L M] : IsNilpotent R L₂ M₂ := by
  obtain ⟨k, hk⟩ := id (by infer_instance : IsNilpotent R L M)
  -- ⊢ LieModule.IsNilpotent R L₂ M₂
  use k
  -- ⊢ lowerCentralSeries R L₂ M₂ k = ⊥
  rw [← LieSubmodule.coe_toSubmodule_eq_iff] at hk ⊢
  -- ⊢ ↑(lowerCentralSeries R L₂ M₂ k) = ↑⊥
  simp [← hf.lieModule_lcs_map_eq hg hfg k, hk]
  -- 🎉 no goals
#align function.surjective.lie_module_is_nilpotent Function.Surjective.lieModuleIsNilpotent

theorem Equiv.lieModule_isNilpotent_iff (f : L ≃ₗ⁅R⁆ L₂) (g : M ≃ₗ[R] M₂)
    (hfg : ∀ x m, ⁅f x, g m⁆ = g ⁅x, m⁆) : IsNilpotent R L M ↔ IsNilpotent R L₂ M₂ := by
  constructor <;> intro h
  -- ⊢ LieModule.IsNilpotent R L M → LieModule.IsNilpotent R L₂ M₂
                  -- ⊢ LieModule.IsNilpotent R L₂ M₂
                  -- ⊢ LieModule.IsNilpotent R L M
  · have hg : Surjective (g : M →ₗ[R] M₂) := g.surjective
    -- ⊢ LieModule.IsNilpotent R L₂ M₂
    exact f.surjective.lieModuleIsNilpotent hg hfg
    -- 🎉 no goals
  · have hg : Surjective (g.symm : M₂ →ₗ[R] M) := g.symm.surjective
    -- ⊢ LieModule.IsNilpotent R L M
    refine' f.symm.surjective.lieModuleIsNilpotent hg fun x m => _
    -- ⊢ ⁅↑(LieEquiv.symm f).toLieHom x, ↑↑(LinearEquiv.symm g) m⁆ = ↑↑(LinearEquiv.s …
    rw [LinearEquiv.coe_coe, LieEquiv.coe_to_lieHom, ← g.symm_apply_apply ⁅f.symm x, g.symm m⁆, ←
      hfg, f.apply_symm_apply, g.apply_symm_apply]
#align equiv.lie_module_is_nilpotent_iff Equiv.lieModule_isNilpotent_iff

@[simp]
theorem LieModule.isNilpotent_of_top_iff :
    IsNilpotent R (⊤ : LieSubalgebra R L) M ↔ IsNilpotent R L M :=
  Equiv.lieModule_isNilpotent_iff LieSubalgebra.topEquiv (1 : M ≃ₗ[R] M) fun _ _ => rfl
#align lie_module.is_nilpotent_of_top_iff LieModule.isNilpotent_of_top_iff

end Morphisms

end NilpotentModules

instance (priority := 100) LieAlgebra.isSolvable_of_isNilpotent (R : Type u) (L : Type v)
    [CommRing R] [LieRing L] [LieAlgebra R L] [hL : LieModule.IsNilpotent R L L] :
    LieAlgebra.IsSolvable R L := by
  obtain ⟨k, h⟩ : ∃ k, LieModule.lowerCentralSeries R L L k = ⊥ := hL.nilpotent
  -- ⊢ IsSolvable R L
  use k; rw [← le_bot_iff] at h ⊢
  -- ⊢ derivedSeries R L k = ⊥
         -- ⊢ derivedSeries R L k ≤ ⊥
  exact le_trans (LieModule.derivedSeries_le_lowerCentralSeries R L k) h
  -- 🎉 no goals
#align lie_algebra.is_solvable_of_is_nilpotent LieAlgebra.isSolvable_of_isNilpotent

section NilpotentAlgebras

variable (R : Type u) (L : Type v) (L' : Type w)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

/-- We say a Lie algebra is nilpotent when it is nilpotent as a Lie module over itself via the
adjoint representation. -/
abbrev LieAlgebra.IsNilpotent (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L] :
    Prop :=
  LieModule.IsNilpotent R L L
#align lie_algebra.is_nilpotent LieAlgebra.IsNilpotent

open LieAlgebra

theorem LieAlgebra.nilpotent_ad_of_nilpotent_algebra [IsNilpotent R L] :
    ∃ k : ℕ, ∀ x : L, ad R L x ^ k = 0 :=
  LieModule.exists_forall_pow_toEndomorphism_eq_zero R L L
#align lie_algebra.nilpotent_ad_of_nilpotent_algebra LieAlgebra.nilpotent_ad_of_nilpotent_algebra

/-- See also `LieAlgebra.zero_rootSpace_eq_top_of_nilpotent`. -/
theorem LieAlgebra.iInf_max_gen_zero_eigenspace_eq_top_of_nilpotent [IsNilpotent R L] :
    ⨅ x : L, (ad R L x).maximalGeneralizedEigenspace 0 = ⊤ :=
  LieModule.iInf_max_gen_zero_eigenspace_eq_top_of_nilpotent R L L
#align lie_algebra.infi_max_gen_zero_eigenspace_eq_top_of_nilpotent LieAlgebra.iInf_max_gen_zero_eigenspace_eq_top_of_nilpotent

-- TODO Generalise the below to Lie modules if / when we define morphisms, equivs of Lie modules
-- covering a Lie algebra morphism of (possibly different) Lie algebras.
variable {R L L'}

open LieModule (lowerCentralSeries)

/-- Given an ideal `I` of a Lie algebra `L`, the lower central series of `L ⧸ I` is the same
whether we regard `L ⧸ I` as an `L` module or an `L ⧸ I` module.

TODO: This result obviously generalises but the generalisation requires the missing definition of
morphisms between Lie modules over different Lie algebras. -/
-- Porting note: added `LieSubmodule.toSubmodule` in the statement
theorem coe_lowerCentralSeries_ideal_quot_eq {I : LieIdeal R L} (k : ℕ) :
    LieSubmodule.toSubmodule (lowerCentralSeries R L (L ⧸ I) k) =
      LieSubmodule.toSubmodule (lowerCentralSeries R (L ⧸ I) (L ⧸ I) k) := by
  induction' k with k ih
  -- ⊢ ↑(lowerCentralSeries R L (L ⧸ I) Nat.zero) = ↑(lowerCentralSeries R (L ⧸ I)  …
  · simp only [Nat.zero_eq, LieModule.lowerCentralSeries_zero, LieSubmodule.top_coeSubmodule,
      LieIdeal.top_coe_lieSubalgebra, LieSubalgebra.top_coe_submodule]
  · simp only [LieModule.lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span]
    -- ⊢ Submodule.span R {m | ∃ x n, ⁅↑x, ↑n⁆ = m} = Submodule.span R {m | ∃ x n, ⁅↑ …
    congr
    -- ⊢ {m | ∃ x n, ⁅↑x, ↑n⁆ = m} = {m | ∃ x n, ⁅↑x, ↑n⁆ = m}
    ext x
    -- ⊢ x ∈ {m | ∃ x n, ⁅↑x, ↑n⁆ = m} ↔ x ∈ {m | ∃ x n, ⁅↑x, ↑n⁆ = m}
    constructor
    -- ⊢ x ∈ {m | ∃ x n, ⁅↑x, ↑n⁆ = m} → x ∈ {m | ∃ x n, ⁅↑x, ↑n⁆ = m}
    · rintro ⟨⟨y, -⟩, ⟨z, hz⟩, rfl : ⁅y, z⁆ = x⟩
      -- ⊢ ⁅y, z⁆ ∈ {m | ∃ x n, ⁅↑x, ↑n⁆ = m}
      erw [← LieSubmodule.mem_coeSubmodule, ih, LieSubmodule.mem_coeSubmodule] at hz
      -- ⊢ ⁅y, z⁆ ∈ {m | ∃ x n, ⁅↑x, ↑n⁆ = m}
      exact ⟨⟨LieSubmodule.Quotient.mk y, LieSubmodule.mem_top _⟩, ⟨z, hz⟩, rfl⟩
      -- 🎉 no goals
    · rintro ⟨⟨⟨y⟩, -⟩, ⟨z, hz⟩, rfl : ⁅y, z⁆ = x⟩
      -- ⊢ ⁅y, z⁆ ∈ {m | ∃ x n, ⁅↑x, ↑n⁆ = m}
      erw [← LieSubmodule.mem_coeSubmodule, ← ih, LieSubmodule.mem_coeSubmodule] at hz
      -- ⊢ ⁅y, z⁆ ∈ {m | ∃ x n, ⁅↑x, ↑n⁆ = m}
      exact ⟨⟨y, LieSubmodule.mem_top _⟩, ⟨z, hz⟩, rfl⟩
      -- 🎉 no goals
#align coe_lower_central_series_ideal_quot_eq coe_lowerCentralSeries_ideal_quot_eq

/-- Note that the below inequality can be strict. For example the ideal of strictly-upper-triangular
2x2 matrices inside the Lie algebra of upper-triangular 2x2 matrices with `k = 1`. -/
-- Porting note: added `LieSubmodule.toSubmodule` in the statement
theorem LieModule.coe_lowerCentralSeries_ideal_le {I : LieIdeal R L} (k : ℕ) :
    LieSubmodule.toSubmodule (lowerCentralSeries R I I k) ≤ lowerCentralSeries R L I k := by
  induction' k with k ih
  -- ⊢ ↑(lowerCentralSeries R { x // x ∈ ↑I } { x // x ∈ ↑I } Nat.zero) ≤ ↑(lowerCe …
  · simp
    -- 🎉 no goals
  · simp only [LieModule.lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span]
    -- ⊢ Submodule.span R {m | ∃ x n, ⁅↑x, ↑n⁆ = m} ≤ Submodule.span R {m | ∃ x n, ⁅↑ …
    apply Submodule.span_mono
    -- ⊢ {m | ∃ x n, ⁅↑x, ↑n⁆ = m} ⊆ {m | ∃ x n, ⁅↑x, ↑n⁆ = m}
    rintro x ⟨⟨y, -⟩, ⟨z, hz⟩, rfl : ⁅y, z⁆ = x⟩
    -- ⊢ ⁅y, z⁆ ∈ {m | ∃ x n, ⁅↑x, ↑n⁆ = m}
    exact ⟨⟨y.val, LieSubmodule.mem_top _⟩, ⟨z, ih hz⟩, rfl⟩
    -- 🎉 no goals
#align lie_module.coe_lower_central_series_ideal_le LieModule.coe_lowerCentralSeries_ideal_le

/-- A central extension of nilpotent Lie algebras is nilpotent. -/
theorem LieAlgebra.nilpotent_of_nilpotent_quotient {I : LieIdeal R L} (h₁ : I ≤ center R L)
    (h₂ : IsNilpotent R (L ⧸ I)) : IsNilpotent R L := by
  suffices LieModule.IsNilpotent R L (L ⧸ I) by
    exact LieModule.nilpotentOfNilpotentQuotient R L L h₁ this
  obtain ⟨k, hk⟩ := h₂
  -- ⊢ LieModule.IsNilpotent R L (L ⧸ I)
  use k
  -- ⊢ lowerCentralSeries R L (L ⧸ I) k = ⊥
  simp [← LieSubmodule.coe_toSubmodule_eq_iff, coe_lowerCentralSeries_ideal_quot_eq, hk]
  -- 🎉 no goals
#align lie_algebra.nilpotent_of_nilpotent_quotient LieAlgebra.nilpotent_of_nilpotent_quotient

theorem LieAlgebra.non_trivial_center_of_isNilpotent [Nontrivial L] [IsNilpotent R L] :
    Nontrivial <| center R L :=
  LieModule.nontrivial_max_triv_of_isNilpotent R L L
#align lie_algebra.non_trivial_center_of_is_nilpotent LieAlgebra.non_trivial_center_of_isNilpotent

theorem LieIdeal.map_lowerCentralSeries_le (k : ℕ) {f : L →ₗ⁅R⁆ L'} :
    LieIdeal.map f (lowerCentralSeries R L L k) ≤ lowerCentralSeries R L' L' k := by
  induction' k with k ih
  -- ⊢ map f (lowerCentralSeries R L L Nat.zero) ≤ lowerCentralSeries R L' L' Nat.z …
  · simp only [Nat.zero_eq, LieModule.lowerCentralSeries_zero, le_top]
    -- 🎉 no goals
  · simp only [LieModule.lowerCentralSeries_succ]
    -- ⊢ map f ⁅⊤, lowerCentralSeries R L L k⁆ ≤ ⁅⊤, lowerCentralSeries R L' L' k⁆
    exact le_trans (LieIdeal.map_bracket_le f) (LieSubmodule.mono_lie _ _ _ _ le_top ih)
    -- 🎉 no goals
#align lie_ideal.map_lower_central_series_le LieIdeal.map_lowerCentralSeries_le

theorem LieIdeal.lowerCentralSeries_map_eq (k : ℕ) {f : L →ₗ⁅R⁆ L'} (h : Function.Surjective f) :
    LieIdeal.map f (lowerCentralSeries R L L k) = lowerCentralSeries R L' L' k := by
  have h' : (⊤ : LieIdeal R L).map f = ⊤ := by
    rw [← f.idealRange_eq_map]
    exact f.idealRange_eq_top_of_surjective h
  induction' k with k ih
  -- ⊢ map f (lowerCentralSeries R L L Nat.zero) = lowerCentralSeries R L' L' Nat.z …
  · simp only [LieModule.lowerCentralSeries_zero]; exact h'
    -- ⊢ map f ⊤ = ⊤
                                                   -- 🎉 no goals
  · simp only [LieModule.lowerCentralSeries_succ, LieIdeal.map_bracket_eq f h, ih, h']
    -- 🎉 no goals
#align lie_ideal.lower_central_series_map_eq LieIdeal.lowerCentralSeries_map_eq

theorem Function.Injective.lieAlgebra_isNilpotent [h₁ : IsNilpotent R L'] {f : L →ₗ⁅R⁆ L'}
    (h₂ : Function.Injective f) : IsNilpotent R L :=
  { nilpotent := by
      obtain ⟨k, hk⟩ := id h₁
      -- ⊢ ∃ k, lowerCentralSeries R L L k = ⊥
      use k
      -- ⊢ lowerCentralSeries R L L k = ⊥
      apply LieIdeal.bot_of_map_eq_bot h₂; rw [eq_bot_iff, ← hk]
      -- ⊢ LieIdeal.map f (lowerCentralSeries R L L k) = ⊥
                                           -- ⊢ LieIdeal.map f (lowerCentralSeries R L L k) ≤ lowerCentralSeries R L' L' k
      apply LieIdeal.map_lowerCentralSeries_le }
      -- 🎉 no goals
#align function.injective.lie_algebra_is_nilpotent Function.Injective.lieAlgebra_isNilpotent

theorem Function.Surjective.lieAlgebra_isNilpotent [h₁ : IsNilpotent R L] {f : L →ₗ⁅R⁆ L'}
    (h₂ : Function.Surjective f) : IsNilpotent R L' :=
  { nilpotent := by
      obtain ⟨k, hk⟩ := id h₁
      -- ⊢ ∃ k, lowerCentralSeries R L' L' k = ⊥
      use k
      -- ⊢ lowerCentralSeries R L' L' k = ⊥
      rw [← LieIdeal.lowerCentralSeries_map_eq k h₂, hk]
      -- ⊢ LieIdeal.map f ⊥ = ⊥
      simp only [LieIdeal.map_eq_bot_iff, bot_le] }
      -- 🎉 no goals
#align function.surjective.lie_algebra_is_nilpotent Function.Surjective.lieAlgebra_isNilpotent

theorem LieEquiv.nilpotent_iff_equiv_nilpotent (e : L ≃ₗ⁅R⁆ L') :
    IsNilpotent R L ↔ IsNilpotent R L' := by
  constructor <;> intro h
  -- ⊢ LieAlgebra.IsNilpotent R L → LieAlgebra.IsNilpotent R L'
                  -- ⊢ LieAlgebra.IsNilpotent R L'
                  -- ⊢ LieAlgebra.IsNilpotent R L
  · exact e.symm.injective.lieAlgebra_isNilpotent
    -- 🎉 no goals
  · exact e.injective.lieAlgebra_isNilpotent
    -- 🎉 no goals
#align lie_equiv.nilpotent_iff_equiv_nilpotent LieEquiv.nilpotent_iff_equiv_nilpotent

theorem LieHom.isNilpotent_range [IsNilpotent R L] (f : L →ₗ⁅R⁆ L') : IsNilpotent R f.range :=
  f.surjective_rangeRestrict.lieAlgebra_isNilpotent
#align lie_hom.is_nilpotent_range LieHom.isNilpotent_range

/-- Note that this result is not quite a special case of
`LieModule.isNilpotent_range_toEndomorphism_iff` which concerns nilpotency of the
`(ad R L).range`-module `L`, whereas this result concerns nilpotency of the `(ad R L).range`-module
`(ad R L).range`. -/
@[simp]
theorem LieAlgebra.isNilpotent_range_ad_iff : IsNilpotent R (ad R L).range ↔ IsNilpotent R L := by
  refine' ⟨fun h => _, _⟩
  -- ⊢ IsNilpotent R L
  · have : (ad R L).ker = center R L := by simp
    -- ⊢ IsNilpotent R L
    exact
      LieAlgebra.nilpotent_of_nilpotent_quotient (le_of_eq this)
        ((ad R L).quotKerEquivRange.nilpotent_iff_equiv_nilpotent.mpr h)
  · intro h
    -- ⊢ IsNilpotent R { x // x ∈ LieHom.range (ad R L) }
    exact (ad R L).isNilpotent_range
    -- 🎉 no goals
#align lie_algebra.is_nilpotent_range_ad_iff LieAlgebra.isNilpotent_range_ad_iff

instance [h : LieAlgebra.IsNilpotent R L] : LieAlgebra.IsNilpotent R (⊤ : LieSubalgebra R L) :=
  LieSubalgebra.topEquiv.nilpotent_iff_equiv_nilpotent.mpr h

end NilpotentAlgebras

namespace LieIdeal

open LieModule

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (I : LieIdeal R L)

variable (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable (k : ℕ)

/-- Given a Lie module `M` over a Lie algebra `L` together with an ideal `I` of `L`, this is the
lower central series of `M` as an `I`-module. The advantage of using this definition instead of
`LieModule.lowerCentralSeries R I M` is that its terms are Lie submodules of `M` as an
`L`-module, rather than just as an `I`-module.

See also `LieIdeal.coe_lcs_eq`. -/
def lcs : LieSubmodule R L M :=
  (fun N => ⁅I, N⁆)^[k] ⊤
#align lie_ideal.lcs LieIdeal.lcs

@[simp]
theorem lcs_zero : I.lcs M 0 = ⊤ :=
  rfl
#align lie_ideal.lcs_zero LieIdeal.lcs_zero

@[simp]
theorem lcs_succ : I.lcs M (k + 1) = ⁅I, I.lcs M k⁆ :=
  Function.iterate_succ_apply' (fun N => ⁅I, N⁆) k ⊤
#align lie_ideal.lcs_succ LieIdeal.lcs_succ

theorem lcs_top : (⊤ : LieIdeal R L).lcs M k = lowerCentralSeries R L M k :=
  rfl
#align lie_ideal.lcs_top LieIdeal.lcs_top

-- Porting note: added `LieSubmodule.toSubmodule` in the statement
theorem coe_lcs_eq : LieSubmodule.toSubmodule (I.lcs M k) = lowerCentralSeries R I M k := by
  induction' k with k ih
  -- ⊢ ↑(lcs I M Nat.zero) = ↑(lowerCentralSeries R { x // x ∈ ↑I } M Nat.zero)
  · simp
    -- 🎉 no goals
  · simp_rw [lowerCentralSeries_succ, lcs_succ, LieSubmodule.lieIdeal_oper_eq_linear_span', ←
      (I.lcs M k).mem_coeSubmodule, ih, LieSubmodule.mem_coeSubmodule, LieSubmodule.mem_top,
      true_and, (I : LieSubalgebra R L).coe_bracket_of_module]
    congr
    -- ⊢ {m | ∃ x, x ∈ I ∧ ∃ n, n ∈ lowerCentralSeries R { x // x ∈ ↑I } M k ∧ ⁅x, n⁆ …
    ext m
    -- ⊢ m ∈ {m | ∃ x, x ∈ I ∧ ∃ n, n ∈ lowerCentralSeries R { x // x ∈ ↑I } M k ∧ ⁅x …
    constructor
    -- ⊢ m ∈ {m | ∃ x, x ∈ I ∧ ∃ n, n ∈ lowerCentralSeries R { x // x ∈ ↑I } M k ∧ ⁅x …
    · rintro ⟨x, hx, m, hm, rfl⟩
      -- ⊢ ⁅x, m⁆ ∈ {m | ∃ x n, n ∈ lowerCentralSeries R { x // x ∈ ↑I } M k ∧ ⁅↑x, n⁆  …
      exact ⟨⟨x, hx⟩, m, hm, rfl⟩
      -- 🎉 no goals
    · rintro ⟨⟨x, hx⟩, m, hm, rfl⟩
      -- ⊢ ⁅↑{ val := x, property := hx }, m⁆ ∈ {m | ∃ x, x ∈ I ∧ ∃ n, n ∈ lowerCentral …
      exact ⟨x, hx, m, hm, rfl⟩
      -- 🎉 no goals
#align lie_ideal.coe_lcs_eq LieIdeal.coe_lcs_eq

end LieIdeal

section OfAssociative

variable (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A]

theorem _root_.LieAlgebra.ad_nilpotent_of_nilpotent {a : A} (h : IsNilpotent a) :
    IsNilpotent (LieAlgebra.ad R A a) := by
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  -- ⊢ IsNilpotent ((LinearMap.mulLeft R - LinearMap.mulRight R) a)
  have hl : IsNilpotent (LinearMap.mulLeft R a) := by rwa [LinearMap.isNilpotent_mulLeft_iff]
  -- ⊢ IsNilpotent ((LinearMap.mulLeft R - LinearMap.mulRight R) a)
  have hr : IsNilpotent (LinearMap.mulRight R a) := by rwa [LinearMap.isNilpotent_mulRight_iff]
  -- ⊢ IsNilpotent ((LinearMap.mulLeft R - LinearMap.mulRight R) a)
  have := @LinearMap.commute_mulLeft_right R A _ _ _ _ _ a a
  -- ⊢ IsNilpotent ((LinearMap.mulLeft R - LinearMap.mulRight R) a)
  exact this.isNilpotent_sub hl hr
  -- 🎉 no goals
#align lie_algebra.ad_nilpotent_of_nilpotent LieAlgebra.ad_nilpotent_of_nilpotent

variable {R}

theorem _root_.LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad {L : Type v} [LieRing L]
    [LieAlgebra R L] (K : LieSubalgebra R L) {x : K} (h : IsNilpotent (LieAlgebra.ad R L ↑x)) :
    IsNilpotent (LieAlgebra.ad R K x) := by
  obtain ⟨n, hn⟩ := h
  -- ⊢ IsNilpotent (↑(LieAlgebra.ad R { x // x ∈ K }) x)
  use n
  -- ⊢ ↑(LieAlgebra.ad R { x // x ∈ K }) x ^ n = 0
  exact LinearMap.submodule_pow_eq_zero_of_pow_eq_zero (K.ad_comp_incl_eq x) hn
  -- 🎉 no goals
#align lie_subalgebra.is_nilpotent_ad_of_is_nilpotent_ad LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad

theorem _root_.LieAlgebra.isNilpotent_ad_of_isNilpotent {L : LieSubalgebra R A} {x : L}
    (h : IsNilpotent (x : A)) : IsNilpotent (LieAlgebra.ad R L x) :=
  L.isNilpotent_ad_of_isNilpotent_ad <| LieAlgebra.ad_nilpotent_of_nilpotent R h
#align lie_algebra.is_nilpotent_ad_of_is_nilpotent LieAlgebra.isNilpotent_ad_of_isNilpotent

end OfAssociative
