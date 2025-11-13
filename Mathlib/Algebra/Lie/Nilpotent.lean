/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Solvable
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.Normalizer
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Nilpotent Lie algebras

Like groups, Lie algebras admit a natural concept of nilpotency. More generally, any Lie module
carries a natural concept of nilpotency. We define these here via the lower central series.

## Main definitions

  * `LieModule.lowerCentralSeries`
  * `LieModule.IsNilpotent`
  * `LieModule.maxNilpotentSubmodule`
  * `LieAlgebra.maxNilpotentIdeal`

## Tags

lie algebra, lower central series, nilpotent, max nilpotent ideal
-/

universe u v w w₁ w₂

section NilpotentModules

variable {R : Type u} {L : Type v} {M : Type w}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M]
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

@[simp]
theorem lcs_zero (N : LieSubmodule R L M) : N.lcs 0 = N :=
  rfl

@[simp]
theorem lcs_succ : N.lcs (k + 1) = ⁅(⊤ : LieIdeal R L), N.lcs k⁆ :=
  Function.iterate_succ_apply' (fun N' => ⁅⊤, N'⁆) k N

@[simp]
lemma lcs_sup {N₁ N₂ : LieSubmodule R L M} {k : ℕ} :
    (N₁ ⊔ N₂).lcs k = N₁.lcs k ⊔ N₂.lcs k := by
  induction k with
  | zero => simp
  | succ k ih => simp only [LieSubmodule.lcs_succ, ih, LieSubmodule.lie_sup]

end LieSubmodule

namespace LieModule

variable (R L M)

/-- The lower central series of Lie submodules of a Lie module. -/
def lowerCentralSeries : LieSubmodule R L M :=
  (⊤ : LieSubmodule R L M).lcs k

@[simp]
theorem lowerCentralSeries_zero : lowerCentralSeries R L M 0 = ⊤ :=
  rfl

@[simp]
theorem lowerCentralSeries_succ :
    lowerCentralSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆ :=
  (⊤ : LieSubmodule R L M).lcs_succ k

private theorem coe_lowerCentralSeries_eq_int_aux (R₁ R₂ L M : Type*)
    [CommRing R₁] [CommRing R₂] [AddCommGroup M]
    [LieRing L] [LieAlgebra R₁ L] [LieAlgebra R₂ L] [Module R₁ M] [Module R₂ M] [LieRingModule L M]
    [LieModule R₁ L M] (k : ℕ) :
    let I := lowerCentralSeries R₂ L M k; let S : Set M := {⁅a, b⁆ | (a : L) (b ∈ I)}
    (Submodule.span R₁ S : Set M) ≤ (Submodule.span R₂ S : Set M) := by
  intro I S x hx
  simp only [SetLike.mem_coe] at hx ⊢
  induction hx using Submodule.closure_induction with
  | zero => exact Submodule.zero_mem _
  | add y z hy₁ hz₁ hy₂ hz₂ => exact Submodule.add_mem _ hy₂ hz₂
  | smul_mem c y hy =>
      obtain ⟨a, b, hb, rfl⟩ := hy
      rw [← smul_lie]
      exact Submodule.subset_span ⟨c • a, b, hb, rfl⟩

theorem coe_lowerCentralSeries_eq_int [LieModule R L M] (k : ℕ) :
    (lowerCentralSeries R L M k : Set M) = (lowerCentralSeries ℤ L M k : Set M) := by
  rw [← LieSubmodule.coe_toSubmodule, ← LieSubmodule.coe_toSubmodule]
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [lowerCentralSeries_succ, lowerCentralSeries_succ]
    rw [LieSubmodule.lieIdeal_oper_eq_linear_span', LieSubmodule.lieIdeal_oper_eq_linear_span']
    rw [Set.ext_iff] at ih
    simp only [SetLike.mem_coe, LieSubmodule.mem_toSubmodule] at ih
    simp only [LieSubmodule.mem_top, ih, true_and]
    apply le_antisymm
    · exact coe_lowerCentralSeries_eq_int_aux _ _ L M k
    · simp only [← ih]
      exact coe_lowerCentralSeries_eq_int_aux _ _ L M k

end LieModule

namespace LieSubmodule

open LieModule

theorem lcs_le_self : N.lcs k ≤ N := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [lcs_succ]
    exact (LieSubmodule.mono_lie_right ⊤ ih).trans (N.lie_le_right ⊤)

variable [LieModule R L M]

theorem lowerCentralSeries_eq_lcs_comap : lowerCentralSeries R L N k = (N.lcs k).comap N.incl := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [lcs_succ, lowerCentralSeries_succ] at ih ⊢
    have : N.lcs k ≤ N.incl.range := by
      rw [N.range_incl]
      apply lcs_le_self
    rw [ih, LieSubmodule.comap_bracket_eq _ N.incl _ N.ker_incl this]

theorem lowerCentralSeries_map_eq_lcs : (lowerCentralSeries R L N k).map N.incl = N.lcs k := by
  rw [lowerCentralSeries_eq_lcs_comap, LieSubmodule.map_comap_incl, inf_eq_right]
  apply lcs_le_self

theorem lowerCentralSeries_eq_bot_iff_lcs_eq_bot :
    lowerCentralSeries R L N k = ⊥ ↔ lcs k N = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← N.lowerCentralSeries_map_eq_lcs, ← LieModuleHom.le_ker_iff_map]
    simpa
  · rw [N.lowerCentralSeries_eq_lcs_comap, comap_incl_eq_bot]
    simp [h]

end LieSubmodule

namespace LieModule

variable {M₂ : Type w₁} [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂] [LieModule R L M₂]
variable (R L M)

theorem antitone_lowerCentralSeries : Antitone <| lowerCentralSeries R L M := by
  intro l k
  induction k generalizing l with
  | zero => exact fun h ↦ (Nat.le_zero.mp h).symm ▸ le_rfl
  | succ k ih =>
    intro h
    rcases Nat.of_le_succ h with (hk | hk)
    · rw [lowerCentralSeries_succ]
      exact (LieSubmodule.mono_lie_right ⊤ (ih hk)).trans (LieSubmodule.lie_le_right _ _)
    · exact hk.symm ▸ le_rfl

theorem eventually_iInf_lowerCentralSeries_eq [IsArtinian R M] :
    ∀ᶠ l in Filter.atTop, ⨅ k, lowerCentralSeries R L M k = lowerCentralSeries R L M l := by
  have h_wf : WellFoundedGT (LieSubmodule R L M)ᵒᵈ :=
    LieSubmodule.wellFoundedLT_of_isArtinian R L M
  obtain ⟨n, hn : ∀ m, n ≤ m → lowerCentralSeries R L M n = lowerCentralSeries R L M m⟩ :=
    h_wf.monotone_chain_condition ⟨_, antitone_lowerCentralSeries R L M⟩
  refine Filter.eventually_atTop.mpr ⟨n, fun l hl ↦ le_antisymm (iInf_le _ _) (le_iInf fun m ↦ ?_)⟩
  rcases le_or_gt l m with h | h
  · rw [← hn _ hl, ← hn _ (hl.trans h)]
  · exact antitone_lowerCentralSeries R L M (le_of_lt h)

theorem trivial_iff_lower_central_eq_bot : IsTrivial L M ↔ lowerCentralSeries R L M 1 = ⊥ := by
  constructor <;> intro h
  · simp
  · rw [LieSubmodule.eq_bot_iff] at h; apply IsTrivial.mk; intro x m; apply h
    apply LieSubmodule.subset_lieSpan
    simp only [Subtype.exists, LieSubmodule.mem_top, exists_prop, true_and, Set.mem_setOf]
    exact ⟨x, m, rfl⟩

section
variable [LieModule R L M]

theorem iterate_toEnd_mem_lowerCentralSeries (x : L) (m : M) (k : ℕ) :
    (toEnd R L M x)^[k] m ∈ lowerCentralSeries R L M k := by
  induction k with
  | zero => simp only [Function.iterate_zero, lowerCentralSeries_zero, LieSubmodule.mem_top]
  | succ k ih =>
    simp only [lowerCentralSeries_succ, Function.comp_apply, Function.iterate_succ',
      toEnd_apply_apply]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) ih

theorem iterate_toEnd_mem_lowerCentralSeries₂ (x y : L) (m : M) (k : ℕ) :
    (toEnd R L M x ∘ₗ toEnd R L M y)^[k] m ∈
      lowerCentralSeries R L M (2 * k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : 2 * k.succ = (2 * k + 1) + 1 := rfl
    simp only [lowerCentralSeries_succ, Function.comp_apply, Function.iterate_succ', hk,
      toEnd_apply_apply, LinearMap.coe_comp, toEnd_apply_apply]
    refine LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) ?_
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top y) ih

variable {R L M}

theorem map_lowerCentralSeries_le (f : M →ₗ⁅R,L⁆ M₂) :
    (lowerCentralSeries R L M k).map f ≤ lowerCentralSeries R L M₂ k := by
  induction k with
  | zero => simp only [lowerCentralSeries_zero, le_top]
  | succ k ih =>
    simp only [LieModule.lowerCentralSeries_succ, LieSubmodule.map_bracket_eq]
    exact LieSubmodule.mono_lie_right ⊤ ih

lemma map_lowerCentralSeries_eq {f : M →ₗ⁅R,L⁆ M₂} (hf : Function.Surjective f) :
    (lowerCentralSeries R L M k).map f = lowerCentralSeries R L M₂ k := by
  apply le_antisymm (map_lowerCentralSeries_le k f)
  induction k with
  | zero =>
    rwa [lowerCentralSeries_zero, lowerCentralSeries_zero, top_le_iff, f.map_top,
      f.range_eq_top]
  | succ =>
    simp only [lowerCentralSeries_succ, LieSubmodule.map_bracket_eq]
    apply LieSubmodule.mono_lie_right
    assumption

end

open LieAlgebra

theorem derivedSeries_le_lowerCentralSeries (k : ℕ) :
    derivedSeries R L k ≤ lowerCentralSeries R L L k := by
  induction k with
  | zero => rw [derivedSeries_def, derivedSeriesOfIdeal_zero, lowerCentralSeries_zero]
  | succ k h =>
    have h' : derivedSeries R L k ≤ ⊤ := by simp only [le_top]
    rw [derivedSeries_def, derivedSeriesOfIdeal_succ, lowerCentralSeries_succ]
    exact LieSubmodule.mono_lie h' h

/-- A Lie module is nilpotent if its lower central series reaches 0 (in a finite number of
steps). -/
@[mk_iff isNilpotent_iff_int]
class IsNilpotent : Prop where
  mk_int ::
  nilpotent_int : ∃ k, lowerCentralSeries ℤ L M k = ⊥

section

variable [LieModule R L M]

/-- See also `LieModule.isNilpotent_iff_exists_ucs_eq_top`. -/
lemma isNilpotent_iff :
    IsNilpotent L M ↔ ∃ k, lowerCentralSeries R L M k = ⊥ := by
  simp [isNilpotent_iff_int, SetLike.ext'_iff, coe_lowerCentralSeries_eq_int R L M]

lemma IsNilpotent.nilpotent [IsNilpotent L M] : ∃ k, lowerCentralSeries R L M k = ⊥ :=
  (isNilpotent_iff R L M).mp ‹_›

variable {R L} in
lemma IsNilpotent.mk {k : ℕ} (h : lowerCentralSeries R L M k = ⊥) : IsNilpotent L M :=
  (isNilpotent_iff R L M).mpr ⟨k, h⟩

@[simp] lemma iInf_lowerCentralSeries_eq_bot_of_isNilpotent [IsNilpotent L M] :
    ⨅ k, lowerCentralSeries R L M k = ⊥ := by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L M
  rw [eq_bot_iff, ← hk]
  exact iInf_le _ _

end

section
variable {R L M}
variable [LieModule R L M]

theorem _root_.LieSubmodule.isNilpotent_iff_exists_lcs_eq_bot (N : LieSubmodule R L M) :
    LieModule.IsNilpotent L N ↔ ∃ k, N.lcs k = ⊥ := by
  rw [isNilpotent_iff R L N]
  refine exists_congr fun k => ?_
  rw [N.lowerCentralSeries_eq_lcs_comap k, LieSubmodule.comap_incl_eq_bot,
    inf_eq_right.mpr (N.lcs_le_self k)]

variable (R L M)

instance (priority := 100) trivialIsNilpotent [IsTrivial L M] : IsNilpotent L M :=
  ⟨by use 1; simp⟩

instance instIsNilpotentSup (M₁ M₂ : LieSubmodule R L M) [IsNilpotent L M₁] [IsNilpotent L M₂] :
    IsNilpotent L (M₁ ⊔ M₂ : LieSubmodule R L M) := by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L M₁
  obtain ⟨l, hl⟩ := IsNilpotent.nilpotent R L M₂
  let lcs_eq_bot {m n} (N : LieSubmodule R L M) (le : m ≤ n) (hn : lowerCentralSeries R L N m = ⊥) :
    lowerCentralSeries R L N n = ⊥ := by
    simpa [hn] using antitone_lowerCentralSeries R L N le
  have h₁ : lowerCentralSeries R L M₁ (k ⊔ l) = ⊥ := lcs_eq_bot M₁ (Nat.le_max_left k l) hk
  have h₂ : lowerCentralSeries R L M₂ (k ⊔ l) = ⊥ := lcs_eq_bot M₂ (Nat.le_max_right k l) hl
  refine (isNilpotent_iff R L (M₁ + M₂)).mpr ⟨k ⊔ l, ?_⟩
  simp [LieSubmodule.add_eq_sup, (M₁ ⊔ M₂).lowerCentralSeries_eq_lcs_comap, LieSubmodule.lcs_sup,
    (M₁.lowerCentralSeries_eq_bot_iff_lcs_eq_bot (k ⊔ l)).1 h₁,
    (M₂.lowerCentralSeries_eq_bot_iff_lcs_eq_bot (k ⊔ l)).1 h₂, LieSubmodule.comap_incl_eq_bot]

theorem exists_forall_pow_toEnd_eq_zero [IsNilpotent L M] :
    ∃ k : ℕ, ∀ x : L, toEnd R L M x ^ k = 0 := by
  obtain ⟨k, hM⟩ := IsNilpotent.nilpotent R L M
  use k
  intro x; ext m
  rw [Module.End.pow_apply, LinearMap.zero_apply, ← @LieSubmodule.mem_bot R L M, ← hM]
  exact iterate_toEnd_mem_lowerCentralSeries R L M x m k

theorem isNilpotent_toEnd_of_isNilpotent [IsNilpotent L M] (x : L) :
    _root_.IsNilpotent (toEnd R L M x) := by
  change ∃ k, toEnd R L M x ^ k = 0
  have := exists_forall_pow_toEnd_eq_zero R L M
  tauto

theorem isNilpotent_toEnd_of_isNilpotent₂ [IsNilpotent L M] (x y : L) :
    _root_.IsNilpotent (toEnd R L M x ∘ₗ toEnd R L M y) := by
  obtain ⟨k, hM⟩ := IsNilpotent.nilpotent R L M
  replace hM : lowerCentralSeries R L M (2 * k) = ⊥ := by
    rw [eq_bot_iff, ← hM]; exact antitone_lowerCentralSeries R L M (by cutsat)
  use k
  ext m
  rw [Module.End.pow_apply, LinearMap.zero_apply, ← LieSubmodule.mem_bot (R := R) (L := L), ← hM]
  exact iterate_toEnd_mem_lowerCentralSeries₂ R L M x y m k

@[simp] lemma maxGenEigenSpace_toEnd_eq_top [IsNilpotent L M] (x : L) :
    ((toEnd R L M x).maxGenEigenspace 0) = ⊤ := by
  ext m
  simp only [Module.End.mem_maxGenEigenspace, zero_smul, sub_zero, Submodule.mem_top,
    iff_true]
  obtain ⟨k, hk⟩ := exists_forall_pow_toEnd_eq_zero R L M
  exact ⟨k, by simp [hk x]⟩

/-- If the quotient of a Lie module `M` by a Lie submodule on which the Lie algebra acts trivially
is nilpotent then `M` is nilpotent.

This is essentially the Lie module equivalent of the fact that a central
extension of nilpotent Lie algebras is nilpotent. See `LieAlgebra.nilpotent_of_nilpotent_quotient`
below for the corresponding result for Lie algebras. -/
theorem nilpotentOfNilpotentQuotient {N : LieSubmodule R L M} (h₁ : N ≤ maxTrivSubmodule R L M)
    (h₂ : IsNilpotent L (M ⧸ N)) : IsNilpotent L M := by
  rw [isNilpotent_iff R L] at h₂ ⊢
  obtain ⟨k, hk⟩ := h₂
  use k + 1
  simp only [lowerCentralSeries_succ]
  suffices lowerCentralSeries R L M k ≤ N by
    replace this := LieSubmodule.mono_lie_right ⊤ (le_trans this h₁)
    rwa [ideal_oper_maxTrivSubmodule_eq_bot, le_bot_iff] at this
  rw [← LieSubmodule.Quotient.map_mk'_eq_bot_le, ← le_bot_iff, ← hk]
  exact map_lowerCentralSeries_le k (LieSubmodule.Quotient.mk' N)

theorem isNilpotent_quotient_iff :
    IsNilpotent L (M ⧸ N) ↔ ∃ k, lowerCentralSeries R L M k ≤ N := by
  rw [isNilpotent_iff R L]
  refine exists_congr fun k ↦ ?_
  rw [← LieSubmodule.Quotient.map_mk'_eq_bot_le, map_lowerCentralSeries_eq k
    (LieSubmodule.Quotient.surjective_mk' N)]

theorem iInf_lcs_le_of_isNilpotent_quot (h : IsNilpotent L (M ⧸ N)) :
    ⨅ k, lowerCentralSeries R L M k ≤ N := by
  obtain ⟨k, hk⟩ := (isNilpotent_quotient_iff R L M N).mp h
  exact iInf_le_of_le k hk

end

/-- Given a nilpotent Lie module `M` with lower central series `M = C₀ ≥ C₁ ≥ ⋯ ≥ Cₖ = ⊥`, this is
the natural number `k` (the number of inclusions).

For a non-nilpotent module, we use the junk value 0. -/
noncomputable def nilpotencyLength : ℕ :=
  sInf {k | lowerCentralSeries ℤ L M k = ⊥}

@[simp]
theorem nilpotencyLength_eq_zero_iff [IsNilpotent L M] :
    nilpotencyLength L M = 0 ↔ Subsingleton M := by
  let s := {k | lowerCentralSeries ℤ L M k = ⊥}
  have hs : s.Nonempty := by
    obtain ⟨k, hk⟩ := IsNilpotent.nilpotent ℤ L M
    exact ⟨k, hk⟩
  change sInf s = 0 ↔ _
  rw [← LieSubmodule.subsingleton_iff ℤ L M, ← subsingleton_iff_bot_eq_top, ←
    lowerCentralSeries_zero, @eq_comm (LieSubmodule ℤ L M)]
  refine ⟨fun h => h ▸ Nat.sInf_mem hs, fun h => ?_⟩
  rw [Nat.sInf_eq_zero]
  exact Or.inl h

section

variable [LieModule R L M]

theorem nilpotencyLength_eq_succ_iff (k : ℕ) :
    nilpotencyLength L M = k + 1 ↔
      lowerCentralSeries R L M (k + 1) = ⊥ ∧ lowerCentralSeries R L M k ≠ ⊥ := by
  have aux (k : ℕ) : lowerCentralSeries R L M k = ⊥ ↔ lowerCentralSeries ℤ L M k = ⊥ := by
    simp [SetLike.ext'_iff, coe_lowerCentralSeries_eq_int R L M]
  let s := {k | lowerCentralSeries ℤ L M k = ⊥}
  rw [aux, ne_eq, aux]
  change sInf s = k + 1 ↔ k + 1 ∈ s ∧ k ∉ s
  have hs : ∀ k₁ k₂, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s := by
    rintro k₁ k₂ h₁₂ (h₁ : lowerCentralSeries ℤ L M k₁ = ⊥)
    exact eq_bot_iff.mpr (h₁ ▸ antitone_lowerCentralSeries ℤ L M h₁₂)
  exact Nat.sInf_upward_closed_eq_succ_iff hs k

@[simp]
theorem nilpotencyLength_eq_one_iff [Nontrivial M] :
    nilpotencyLength L M = 1 ↔ IsTrivial L M := by
  rw [nilpotencyLength_eq_succ_iff ℤ, ← trivial_iff_lower_central_eq_bot]
  simp

theorem isTrivial_of_nilpotencyLength_le_one [IsNilpotent L M] (h : nilpotencyLength L M ≤ 1) :
    IsTrivial L M := by
  nontriviality M
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h | h
  · rw [nilpotencyLength_eq_zero_iff] at h; infer_instance
  · rwa [nilpotencyLength_eq_one_iff] at h

end

/-- Given a non-trivial nilpotent Lie module `M` with lower central series
`M = C₀ ≥ C₁ ≥ ⋯ ≥ Cₖ = ⊥`, this is the `k-1`th term in the lower central series (the last
non-trivial term).

For a trivial or non-nilpotent module, this is the bottom submodule, `⊥`. -/
noncomputable def lowerCentralSeriesLast : LieSubmodule R L M :=
  match nilpotencyLength L M with
  | 0 => ⊥
  | k + 1 => lowerCentralSeries R L M k

theorem lowerCentralSeriesLast_le_max_triv [LieModule R L M] :
    lowerCentralSeriesLast R L M ≤ maxTrivSubmodule R L M := by
  rw [lowerCentralSeriesLast]
  rcases h : nilpotencyLength L M with - | k
  · exact bot_le
  · rw [le_max_triv_iff_bracket_eq_bot]
    rw [nilpotencyLength_eq_succ_iff R, lowerCentralSeries_succ] at h
    exact h.1

theorem nontrivial_lowerCentralSeriesLast [LieModule R L M] [Nontrivial M] [IsNilpotent L M] :
    Nontrivial (lowerCentralSeriesLast R L M) := by
  rw [LieSubmodule.nontrivial_iff_ne_bot, lowerCentralSeriesLast]
  cases h : nilpotencyLength L M
  · rw [nilpotencyLength_eq_zero_iff, ← not_nontrivial_iff_subsingleton] at h
    contradiction
  · rw [nilpotencyLength_eq_succ_iff R] at h
    exact h.2

theorem lowerCentralSeriesLast_le_of_not_isTrivial [IsNilpotent L M] (h : ¬ IsTrivial L M) :
    lowerCentralSeriesLast R L M ≤ lowerCentralSeries R L M 1 := by
  rw [lowerCentralSeriesLast]
  replace h : 1 < nilpotencyLength L M := by
    by_contra contra
    have := isTrivial_of_nilpotencyLength_le_one L M (not_lt.mp contra)
    contradiction
  rcases hk : nilpotencyLength L M with - | k <;> rw [hk] at h
  · contradiction
  · exact antitone_lowerCentralSeries _ _ _ (Nat.lt_succ.mp h)

variable [LieModule R L M]

/-- For a nilpotent Lie module `M` of a Lie algebra `L`, the first term in the lower central series
of `M` contains a non-zero element on which `L` acts trivially unless the entire action is trivial.

Taking `M = L`, this provides a useful characterisation of Abelian-ness for nilpotent Lie
algebras. -/
lemma disjoint_lowerCentralSeries_maxTrivSubmodule_iff [IsNilpotent L M] :
    Disjoint (lowerCentralSeries R L M 1) (maxTrivSubmodule R L M) ↔ IsTrivial L M := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp⟩
  nontriviality M
  by_contra contra
  have : lowerCentralSeriesLast R L M ≤ lowerCentralSeries R L M 1 ⊓ maxTrivSubmodule R L M :=
    le_inf_iff.mpr ⟨lowerCentralSeriesLast_le_of_not_isTrivial R L M contra,
      lowerCentralSeriesLast_le_max_triv R L M⟩
  suffices ¬ Nontrivial (lowerCentralSeriesLast R L M) by
    exact this (nontrivial_lowerCentralSeriesLast R L M)
  rw [h.eq_bot, le_bot_iff] at this
  exact this ▸ not_nontrivial _

theorem nontrivial_max_triv_of_isNilpotent [Nontrivial M] [IsNilpotent L M] :
    Nontrivial (maxTrivSubmodule R L M) :=
  Set.nontrivial_mono (lowerCentralSeriesLast_le_max_triv R L M)
    (nontrivial_lowerCentralSeriesLast R L M)

@[simp]
theorem coe_lcs_range_toEnd_eq (k : ℕ) :
    (lowerCentralSeries R (toEnd R L M).range M k : Submodule R M) =
      lowerCentralSeries R L M k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span', ←
      (lowerCentralSeries R (toEnd R L M).range M k).mem_toSubmodule, ih]
    simp

@[simp]
theorem isNilpotent_range_toEnd_iff :
    IsNilpotent (toEnd R L M).range M ↔ IsNilpotent L M := by
  simp only [isNilpotent_iff R _ M]
  constructor <;> rintro ⟨k, hk⟩ <;> use k <;>
      rw [← LieSubmodule.toSubmodule_inj] at hk ⊢ <;>
    simpa using hk

end LieModule

namespace LieSubmodule

variable {N₁ N₂ : LieSubmodule R L M}
variable [LieModule R L M]

/-- The upper (aka ascending) central series.

See also `LieSubmodule.lcs`. -/
def ucs (k : ℕ) : LieSubmodule R L M → LieSubmodule R L M :=
  normalizer^[k]

@[simp]
theorem ucs_zero : N.ucs 0 = N :=
  rfl

@[simp]
theorem ucs_succ (k : ℕ) : N.ucs (k + 1) = (N.ucs k).normalizer :=
  Function.iterate_succ_apply' normalizer k N

theorem ucs_add (k l : ℕ) : N.ucs (k + l) = (N.ucs l).ucs k :=
  Function.iterate_add_apply normalizer k l N

@[gcongr, mono]
theorem ucs_mono (k : ℕ) (h : N₁ ≤ N₂) : N₁.ucs k ≤ N₂.ucs k := by
  induction k with
  | zero => simpa
  | succ k ih =>
    simp only [ucs_succ]
    gcongr

theorem ucs_eq_self_of_normalizer_eq_self (h : N₁.normalizer = N₁) (k : ℕ) : N₁.ucs k = N₁ := by
  induction k with
  | zero => simp
  | succ k ih => rwa [ucs_succ, ih]

/-- If a Lie module `M` contains a self-normalizing Lie submodule `N`, then all terms of the upper
central series of `M` are contained in `N`.

An important instance of this situation arises from a Cartan subalgebra `H ⊆ L` with the roles of
`L`, `M`, `N` played by `H`, `L`, `H`, respectively. -/
theorem ucs_le_of_normalizer_eq_self (h : N₁.normalizer = N₁) (k : ℕ) :
    (⊥ : LieSubmodule R L M).ucs k ≤ N₁ := by
  rw [← ucs_eq_self_of_normalizer_eq_self h k]
  gcongr
  simp

theorem lcs_add_le_iff (l k : ℕ) : N₁.lcs (l + k) ≤ N₂ ↔ N₁.lcs l ≤ N₂.ucs k := by
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
    rw [(by abel : l + (k + 1) = l + 1 + k), ih, ucs_succ, lcs_succ, top_lie_le_iff_le_normalizer]

theorem lcs_le_iff (k : ℕ) : N₁.lcs k ≤ N₂ ↔ N₁ ≤ N₂.ucs k := by
  convert lcs_add_le_iff (R := R) (L := L) (M := M) 0 k
  rw [zero_add]

theorem gc_lcs_ucs (k : ℕ) :
    GaloisConnection (fun N : LieSubmodule R L M => N.lcs k) fun N : LieSubmodule R L M =>
      N.ucs k :=
  fun _ _ => lcs_le_iff k

theorem ucs_eq_top_iff (k : ℕ) : N.ucs k = ⊤ ↔ LieModule.lowerCentralSeries R L M k ≤ N := by
  rw [eq_top_iff, ← lcs_le_iff]; rfl

variable (R) in
theorem _root_.LieModule.isNilpotent_iff_exists_ucs_eq_top :
    LieModule.IsNilpotent L M ↔ ∃ k, (⊥ : LieSubmodule R L M).ucs k = ⊤ := by
  rw [LieModule.isNilpotent_iff R]; exact exists_congr fun k => by simp [ucs_eq_top_iff]

theorem ucs_comap_incl (k : ℕ) :
    ((⊥ : LieSubmodule R L M).ucs k).comap N.incl = (⊥ : LieSubmodule R L N).ucs k := by
  induction k with
  | zero => exact N.ker_incl
  | succ k ih => simp [← ih]

theorem isNilpotent_iff_exists_self_le_ucs :
    LieModule.IsNilpotent L N ↔ ∃ k, N ≤ (⊥ : LieSubmodule R L M).ucs k := by
  simp_rw [LieModule.isNilpotent_iff_exists_ucs_eq_top R, ← ucs_comap_incl, comap_incl_eq_top]

theorem ucs_bot_one : (⊥ : LieSubmodule R L M).ucs 1 = LieModule.maxTrivSubmodule R L M := by
  simp [LieSubmodule.normalizer_bot_eq_maxTrivSubmodule]

end LieSubmodule

section Morphisms

open LieModule Function

variable [LieModule R L M]
variable {L₂ M₂ : Type*} [LieRing L₂] [LieAlgebra R L₂]
variable [AddCommGroup M₂] [Module R M₂] [LieRingModule L₂ M₂]
variable {f : L →ₗ⁅R⁆ L₂} {g : M →ₗ[R] M₂}
variable (hfg : ∀ x m, ⁅f x, g m⁆ = g ⁅x, m⁆)

include hfg in
theorem lieModule_lcs_map_le (k : ℕ) :
    (lowerCentralSeries R L M k : Submodule R M).map g ≤ lowerCentralSeries R L₂ M₂ k := by
  induction k with
  | zero =>
    simp [Submodule.map_top]
  | succ k ih =>
    rw [lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span', Submodule.map_span,
      Submodule.span_le]
    rintro m₂ ⟨m, ⟨x, n, m_n, ⟨h₁, h₂⟩⟩, rfl⟩
    simp only [lowerCentralSeries_succ, SetLike.mem_coe, LieSubmodule.mem_toSubmodule]
    have : ∃ y : L₂, ∃ n : lowerCentralSeries R L₂ M₂ k, ⁅y, n⁆ = g m := by
      use f x, ⟨g m_n, ih (Submodule.mem_map_of_mem h₁)⟩
      simp [hfg x m_n, h₂]
    obtain ⟨y, n, hn⟩ := this
    rw [← hn]
    apply LieSubmodule.lie_mem_lie
    · simp
    · exact SetLike.coe_mem n

variable [LieModule R L₂ M₂] (hg_inj : Injective g)

include hg_inj hfg in
theorem Function.Injective.lieModuleIsNilpotent [IsNilpotent L₂ M₂] : IsNilpotent L M := by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L₂ M₂
  rw [isNilpotent_iff R]
  use k
  rw [← LieSubmodule.toSubmodule_inj] at hk ⊢
  apply Submodule.map_injective_of_injective hg_inj
  simpa [hk] using lieModule_lcs_map_le hfg k

variable (hf_surj : Surjective f) (hg_surj : Surjective g)

include hf_surj hg_surj hfg in
theorem Function.Surjective.lieModule_lcs_map_eq (k : ℕ) :
    (lowerCentralSeries R L M k : Submodule R M).map g = lowerCentralSeries R L₂ M₂ k := by
  refine le_antisymm (lieModule_lcs_map_le hfg k) ?_
  induction k with
  | zero => simpa [LinearMap.range_eq_top]
  | succ k ih =>
    suffices
      {m | ∃ (x : L₂) (n : _), n ∈ lowerCentralSeries R L M k ∧ ⁅x, g n⁆ = m} ⊆
        g '' {m | ∃ (x : L) (n : _), n ∈ lowerCentralSeries R L M k ∧ ⁅x, n⁆ = m} by
      simp only [← LieSubmodule.mem_toSubmodule] at this
      simp_rw [lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span',
        Submodule.map_span, LieSubmodule.mem_top, true_and, ← LieSubmodule.mem_toSubmodule]
      refine Submodule.span_mono (Set.Subset.trans ?_ this)
      rintro m₁ ⟨x, n, hn, rfl⟩
      obtain ⟨n', hn', rfl⟩ := ih hn
      exact ⟨x, n', hn', rfl⟩
    rintro m₂ ⟨x, n, hn, rfl⟩
    obtain ⟨y, rfl⟩ := hf_surj x
    exact ⟨⁅y, n⁆, ⟨y, n, hn, rfl⟩, (hfg y n).symm⟩

include hf_surj hg_surj hfg in
theorem Function.Surjective.lieModuleIsNilpotent [IsNilpotent L M] : IsNilpotent L₂ M₂ := by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L M
  rw [isNilpotent_iff R]
  use k
  rw [← LieSubmodule.toSubmodule_inj] at hk ⊢
  simp [← hf_surj.lieModule_lcs_map_eq hfg hg_surj k, hk]

theorem Equiv.lieModule_isNilpotent_iff (f : L ≃ₗ⁅R⁆ L₂) (g : M ≃ₗ[R] M₂)
    (hfg : ∀ x m, ⁅f x, g m⁆ = g ⁅x, m⁆) : IsNilpotent L M ↔ IsNilpotent L₂ M₂ := by
  constructor <;> intro h
  · have hg : Surjective (g : M →ₗ[R] M₂) := g.surjective
    exact f.surjective.lieModuleIsNilpotent hfg hg
  · have hg : Surjective (g.symm : M₂ →ₗ[R] M) := g.symm.surjective
    refine f.symm.surjective.lieModuleIsNilpotent (fun x m => ?_) hg
    rw [LinearEquiv.coe_coe, LieEquiv.coe_toLieHom, ← g.symm_apply_apply ⁅f.symm x, g.symm m⁆, ←
      hfg, f.apply_symm_apply, g.apply_symm_apply]

@[simp]
theorem LieModule.isNilpotent_of_top_iff :
    IsNilpotent (⊤ : LieSubalgebra R L) M ↔ IsNilpotent L M :=
  Equiv.lieModule_isNilpotent_iff LieSubalgebra.topEquiv (1 : M ≃ₗ[R] M) fun _ _ => rfl

@[simp] lemma LieModule.isNilpotent_of_top_iff' :
    IsNilpotent L {x // x ∈ (⊤ : LieSubmodule R L M)} ↔ IsNilpotent L M :=
  Equiv.lieModule_isNilpotent_iff 1 (LinearEquiv.ofTop ⊤ rfl) fun _ _ ↦ rfl

end Morphisms

namespace LieModule

variable (R L M)
variable [LieModule R L M]

theorem isNilpotent_of_le (M₁ M₂ : LieSubmodule R L M) (h₁ : M₁ ≤ M₂) [IsNilpotent L M₂] :
    IsNilpotent L M₁ := by
  let f : L →ₗ⁅R⁆ L := LieHom.id
  let g : M₁ →ₗ[R] M₂ := Submodule.inclusion h₁
  have hfg : ∀ x m, ⁅f x, g m⁆ = g ⁅x, m⁆ := by aesop
  exact (Submodule.inclusion_injective h₁).lieModuleIsNilpotent hfg

/-- The max nilpotent submodule is the `sSup` of all nilpotent submodules. -/
def maxNilpotentSubmodule :=
  sSup { N : LieSubmodule R L M | IsNilpotent L N }

instance instMaxNilpotentSubmoduleIsNilpotent [IsNoetherian R M] :
    IsNilpotent L (maxNilpotentSubmodule R L M) := by
  have hwf := CompleteLattice.WellFoundedGT.isSupClosedCompact (LieSubmodule R L M) inferInstance
  refine hwf { N : LieSubmodule R L M | IsNilpotent L N } ⟨⊥, ?_⟩ fun N₁ h₁ N₂ h₂ => ?_ <;>
  simp_all <;> infer_instance

theorem isNilpotent_iff_le_maxNilpotentSubmodule [IsNoetherian R M] (N : LieSubmodule R L M) :
    IsNilpotent L N ↔ N ≤ maxNilpotentSubmodule R L M :=
  ⟨fun h ↦ le_sSup h, fun h ↦ isNilpotent_of_le R L M N (maxNilpotentSubmodule R L M) h⟩

@[simp] lemma maxNilpotentSubmodule_eq_top_of_isNilpotent [LieModule.IsNilpotent L M] :
    maxNilpotentSubmodule R L M = ⊤ := by
  rw [eq_top_iff]
  apply le_sSup
  simpa

end LieModule

end NilpotentModules

instance (priority := 100) LieAlgebra.isSolvable_of_isNilpotent (L : Type v)
    [LieRing L] [hL : LieModule.IsNilpotent L L] :
    LieAlgebra.IsSolvable L := by
  obtain ⟨k, h⟩ : ∃ k, LieModule.lowerCentralSeries ℤ L L k = ⊥ := hL.nilpotent_int
  use k; rw [← le_bot_iff] at h ⊢
  exact le_trans (LieModule.derivedSeries_le_lowerCentralSeries ℤ L k) h

section NilpotentAlgebras

variable (R : Type u) (L : Type v) (L' : Type w)
variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

/-- We say a Lie ring is nilpotent when it is nilpotent as a Lie module over itself via the
adjoint representation. -/
abbrev LieRing.IsNilpotent (L : Type v) [LieRing L] : Prop :=
  LieModule.IsNilpotent L L

open LieRing

theorem LieAlgebra.nilpotent_ad_of_nilpotent_algebra [IsNilpotent L] :
    ∃ k : ℕ, ∀ x : L, ad R L x ^ k = 0 :=
  LieModule.exists_forall_pow_toEnd_eq_zero R L L

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
  induction k with
  | zero =>
    simp only [LieModule.lowerCentralSeries_zero, LieSubmodule.top_toSubmodule]
  | succ k ih =>
    simp only [LieModule.lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span]
    congr
    ext x
    constructor
    · rintro ⟨⟨y, -⟩, ⟨z, hz⟩, rfl : ⁅y, z⁆ = x⟩
      rw [← LieSubmodule.mem_toSubmodule, ih, LieSubmodule.mem_toSubmodule] at hz
      exact ⟨⟨LieSubmodule.Quotient.mk y, LieSubmodule.mem_top _⟩, ⟨z, hz⟩, rfl⟩
    · rintro ⟨⟨⟨y⟩, -⟩, ⟨z, hz⟩, rfl : ⁅y, z⁆ = x⟩
      rw [← LieSubmodule.mem_toSubmodule, ← ih, LieSubmodule.mem_toSubmodule] at hz
      exact ⟨⟨y, LieSubmodule.mem_top _⟩, ⟨z, hz⟩, rfl⟩

/-- Note that the below inequality can be strict. For example the ideal of strictly-upper-triangular
2x2 matrices inside the Lie algebra of upper-triangular 2x2 matrices with `k = 1`. -/
-- Porting note: added `LieSubmodule.toSubmodule` in the statement
theorem LieModule.coe_lowerCentralSeries_ideal_le {I : LieIdeal R L} (k : ℕ) :
    LieSubmodule.toSubmodule (lowerCentralSeries R I I k) ≤ lowerCentralSeries R L I k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [LieModule.lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span]
    apply Submodule.span_mono
    rintro x ⟨⟨y, -⟩, ⟨z, hz⟩, rfl : ⁅y, z⁆ = x⟩
    exact ⟨⟨y.val, LieSubmodule.mem_top _⟩, ⟨z, ih hz⟩, rfl⟩

/-- A central extension of nilpotent Lie algebras is nilpotent. -/
theorem LieAlgebra.nilpotent_of_nilpotent_quotient {I : LieIdeal R L} (h₁ : I ≤ center R L)
    (h₂ : IsNilpotent (L ⧸ I)) : IsNilpotent L := by
  suffices LieModule.IsNilpotent L (L ⧸ I) by
    exact LieModule.nilpotentOfNilpotentQuotient R L L h₁ this
  simp only [LieRing.IsNilpotent, LieModule.isNilpotent_iff R] at h₂ ⊢
  peel h₂ with k hk
  simp [← LieSubmodule.toSubmodule_inj, coe_lowerCentralSeries_ideal_quot_eq, hk]

theorem LieAlgebra.non_trivial_center_of_isNilpotent [Nontrivial L] [IsNilpotent L] :
    Nontrivial <| center R L :=
  LieModule.nontrivial_max_triv_of_isNilpotent R L L

theorem LieIdeal.map_lowerCentralSeries_le (k : ℕ) {f : L →ₗ⁅R⁆ L'} :
    LieIdeal.map f (lowerCentralSeries R L L k) ≤ lowerCentralSeries R L' L' k := by
  induction k with
  | zero => simp only [LieModule.lowerCentralSeries_zero, le_top]
  | succ k ih =>
    simp only [LieModule.lowerCentralSeries_succ]
    exact le_trans (LieIdeal.map_bracket_le f) (LieSubmodule.mono_lie le_top ih)

theorem LieIdeal.lowerCentralSeries_map_eq (k : ℕ) {f : L →ₗ⁅R⁆ L'} (h : Function.Surjective f) :
    LieIdeal.map f (lowerCentralSeries R L L k) = lowerCentralSeries R L' L' k := by
  have h' : (⊤ : LieIdeal R L).map f = ⊤ := by
    rw [← f.idealRange_eq_map]
    exact f.idealRange_eq_top_of_surjective h
  induction k with
  | zero => simp only [LieModule.lowerCentralSeries_zero]; exact h'
  | succ k ih => simp only [LieModule.lowerCentralSeries_succ, LieIdeal.map_bracket_eq f h, ih, h']

theorem Function.Injective.lieAlgebra_isNilpotent [h₁ : IsNilpotent L'] {f : L →ₗ⁅R⁆ L'}
    (h₂ : Function.Injective f) : IsNilpotent L := by
  rw [LieRing.IsNilpotent, LieModule.isNilpotent_iff R] at h₁ ⊢
  peel h₁ with k hk
  apply LieIdeal.bot_of_map_eq_bot h₂; rw [eq_bot_iff, ← hk]
  apply LieIdeal.map_lowerCentralSeries_le

theorem Function.Surjective.lieAlgebra_isNilpotent [h₁ : IsNilpotent L] {f : L →ₗ⁅R⁆ L'}
    (h₂ : Function.Surjective f) : IsNilpotent L' := by
  rw [LieRing.IsNilpotent, LieModule.isNilpotent_iff R] at h₁ ⊢
  peel h₁ with k hk
  rw [← LieIdeal.lowerCentralSeries_map_eq k h₂, hk]
  simp only [LieIdeal.map_eq_bot_iff, bot_le]

theorem LieEquiv.nilpotent_iff_equiv_nilpotent (e : L ≃ₗ⁅R⁆ L') :
    IsNilpotent L ↔ IsNilpotent L' := by
  constructor <;> intro h
  · exact e.symm.injective.lieAlgebra_isNilpotent
  · exact e.injective.lieAlgebra_isNilpotent

theorem LieHom.isNilpotent_range [IsNilpotent L] (f : L →ₗ⁅R⁆ L') : IsNilpotent f.range :=
  f.surjective_rangeRestrict.lieAlgebra_isNilpotent

/-- Note that this result is not quite a special case of
`LieModule.isNilpotent_range_toEnd_iff` which concerns nilpotency of the
`(ad R L).range`-module `L`, whereas this result concerns nilpotency of the `(ad R L).range`-module
`(ad R L).range`. -/
@[simp]
theorem LieAlgebra.isNilpotent_range_ad_iff : IsNilpotent (ad R L).range ↔ IsNilpotent L := by
  refine ⟨fun h => ?_, ?_⟩
  · have : (ad R L).ker = center R L := by simp
    exact
      LieAlgebra.nilpotent_of_nilpotent_quotient (le_of_eq this)
        ((ad R L).quotKerEquivRange.nilpotent_iff_equiv_nilpotent.mpr h)
  · intro h
    exact (ad R L).isNilpotent_range

instance [h : LieRing.IsNilpotent L] : LieRing.IsNilpotent (⊤ : LieSubalgebra R L) :=
  LieSubalgebra.topEquiv.nilpotent_iff_equiv_nilpotent.mpr h

end NilpotentAlgebras

namespace LieIdeal

open LieModule

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (I : LieIdeal R L)
variable (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M]
variable (k : ℕ)

/-- Given a Lie module `M` over a Lie algebra `L` together with an ideal `I` of `L`, this is the
lower central series of `M` as an `I`-module. The advantage of using this definition instead of
`LieModule.lowerCentralSeries R I M` is that its terms are Lie submodules of `M` as an
`L`-module, rather than just as an `I`-module.

See also `LieIdeal.coe_lcs_eq`. -/
def lcs : LieSubmodule R L M :=
  (fun N => ⁅I, N⁆)^[k] ⊤

@[simp]
theorem lcs_zero : I.lcs M 0 = ⊤ :=
  rfl

@[simp]
theorem lcs_succ : I.lcs M (k + 1) = ⁅I, I.lcs M k⁆ :=
  Function.iterate_succ_apply' (fun N => ⁅I, N⁆) k ⊤

theorem lcs_top : (⊤ : LieIdeal R L).lcs M k = lowerCentralSeries R L M k :=
  rfl

-- Porting note: added `LieSubmodule.toSubmodule` in the statement
theorem coe_lcs_eq [LieModule R L M] :
    LieSubmodule.toSubmodule (I.lcs M k) = lowerCentralSeries R I M k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp_rw [lowerCentralSeries_succ, lcs_succ, LieSubmodule.lieIdeal_oper_eq_linear_span', ←
      (I.lcs M k).mem_toSubmodule, ih, LieSubmodule.mem_toSubmodule, LieSubmodule.mem_top,
      true_and, (I : LieSubalgebra R L).coe_bracket_of_module]
    simp

instance [IsNilpotent L I] : LieRing.IsNilpotent I := by
  let f : I →ₗ⁅R⁆ L := I.incl
  let g : I →ₗ⁅R⁆ I := LieHom.id
  have hfg : ∀ x m, ⁅f x, g m⁆ = g ⁅x, m⁆ := by aesop
  exact Function.injective_id.lieModuleIsNilpotent hfg

end LieIdeal

section OfAssociative

variable (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A]

theorem _root_.LieAlgebra.ad_nilpotent_of_nilpotent {a : A} (h : IsNilpotent a) :
    IsNilpotent (LieAlgebra.ad R A a) := by
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  have hl : IsNilpotent (LinearMap.mulLeft R a) := by rwa [LinearMap.isNilpotent_mulLeft_iff]
  have hr : IsNilpotent (LinearMap.mulRight R a) := by rwa [LinearMap.isNilpotent_mulRight_iff]
  have := @LinearMap.commute_mulLeft_right R A _ _ _ _ _ a a
  exact this.isNilpotent_sub hl hr

variable {R}

theorem _root_.LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad {L : Type v} [LieRing L]
    [LieAlgebra R L] (K : LieSubalgebra R L) {x : K} (h : IsNilpotent (LieAlgebra.ad R L ↑x)) :
    IsNilpotent (LieAlgebra.ad R K x) := by
  obtain ⟨n, hn⟩ := h
  use n
  exact Module.End.submodule_pow_eq_zero_of_pow_eq_zero (K.ad_comp_incl_eq x) hn

theorem _root_.LieAlgebra.isNilpotent_ad_of_isNilpotent {L : LieSubalgebra R A} {x : L}
    (h : IsNilpotent (x : A)) : IsNilpotent (LieAlgebra.ad R L x) :=
  L.isNilpotent_ad_of_isNilpotent_ad <| LieAlgebra.ad_nilpotent_of_nilpotent R h

end OfAssociative

section ExtendScalars

open LieModule TensorProduct

variable (R A L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [CommRing A] [Algebra R A]

@[simp]
lemma LieSubmodule.lowerCentralSeries_tensor_eq_baseChange (k : ℕ) :
    lowerCentralSeries A (A ⊗[R] L) (A ⊗[R] M) k =
    (lowerCentralSeries R L M k).baseChange A := by
  induction k with
  | zero => simp
  | succ k ih => simp only [lowerCentralSeries_succ, ih, ← baseChange_top, lie_baseChange]

instance LieModule.instIsNilpotentTensor [IsNilpotent L M] :
    IsNilpotent (A ⊗[R] L) (A ⊗[R] M) := by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L M
  rw [isNilpotent_iff A]
  exact ⟨k, by simp [hk]⟩

end ExtendScalars

namespace LieAlgebra

open LieModule

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The max nilpotent ideal of a Lie algebra. It is defined as the max nilpotent Lie submodule of
`L` under the adjoint action. -/
def maxNilpotentIdeal := maxNilpotentSubmodule R L L

instance maxNilpotentIdealIsNilpotent [IsNoetherian R L] :
    IsNilpotent L (maxNilpotentIdeal R L) :=
  instMaxNilpotentSubmoduleIsNilpotent R L L

theorem LieIdeal.isNilpotent_iff_le_maxNilpotentIdeal [IsNoetherian R L] (I : LieIdeal R L) :
    IsNilpotent L I ↔ I ≤ maxNilpotentIdeal R L :=
  isNilpotent_iff_le_maxNilpotentSubmodule R L L I

theorem center_le_maxNilpotentIdeal : center R L ≤ maxNilpotentIdeal R L :=
  le_sSup (trivialIsNilpotent L (center R L))

theorem maxNilpotentIdeal_le_radical : maxNilpotentIdeal R L ≤ radical R L :=
  sSup_le_sSup fun I (_ : IsNilpotent L I) ↦ isSolvable_of_isNilpotent I

@[simp] lemma maxNilpotentIdeal_eq_top_of_isNilpotent [LieRing.IsNilpotent L] :
    maxNilpotentIdeal R L = ⊤ :=
  maxNilpotentSubmodule_eq_top_of_isNilpotent R L L

end LieAlgebra
