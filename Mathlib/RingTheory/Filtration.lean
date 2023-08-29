/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Ideal.LocalRing
import Mathlib.RingTheory.Noetherian
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.Finiteness
import Mathlib.Data.Polynomial.Module
import Mathlib.Order.Hom.Lattice

#align_import ring_theory.filtration from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!

# `I`-filtrations of modules

This file contains the definitions and basic results around (stable) `I`-filtrations of modules.

## Main results

- `Ideal.Filtration`: An `I`-filtration on the module `M` is a sequence of decreasing submodules
  `N i` such that `I • N ≤ I (i + 1)`. Note that we do not require the filtration to start from `⊤`.
- `Ideal.Filtration.Stable`: An `I`-filtration is stable if `I • (N i) = N (i + 1)` for large
  enough `i`.
- `Ideal.Filtration.submodule`: The associated module `⨁ Nᵢ` of a filtration, implemented as a
  submodule of `M[X]`.
- `Ideal.Filtration.submodule_fg_iff_stable`: If `F.N i` are all finitely generated, then
  `F.Stable` iff `F.submodule.FG`.
- `Ideal.Filtration.Stable.of_le`: In a finite module over a noetherian ring,
  if `F' ≤ F`, then `F.Stable → F'.Stable`.
- `Ideal.exists_pow_inf_eq_pow_smul`: **Artin-Rees lemma**.
  given `N ≤ M`, there exists a `k` such that `IⁿM ⊓ N = Iⁿ⁻ᵏ(IᵏM ⊓ N)` for all `n ≥ k`.
- `Ideal.iInf_pow_eq_bot_of_localRing`:
  **Krull's intersection theorem** (`⨅ i, I ^ i = ⊥`) for noetherian local rings.
- `Ideal.iInf_pow_eq_bot_of_isDomain`:
  **Krull's intersection theorem** (`⨅ i, I ^ i = ⊥`) for noetherian domains.

-/


universe u v

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

open Polynomial

open scoped Polynomial BigOperators

/-- An `I`-filtration on the module `M` is a sequence of decreasing submodules `N i` such that
`I • (N i) ≤ N (i + 1)`. Note that we do not require the filtration to start from `⊤`. -/
@[ext]
structure Ideal.Filtration (M : Type u) [AddCommGroup M] [Module R M] where
  N : ℕ → Submodule R M
  mono : ∀ i, N (i + 1) ≤ N i
  smul_le : ∀ i, I • N i ≤ N (i + 1)
#align ideal.filtration Ideal.Filtration

variable (F F' : I.Filtration M) {I}

namespace Ideal.Filtration

theorem pow_smul_le (i j : ℕ) : I ^ i • F.N j ≤ F.N (i + j) := by
  induction' i with _ ih
  -- ⊢ I ^ Nat.zero • N F j ≤ N F (Nat.zero + j)
  · simp
    -- 🎉 no goals
  · rw [pow_succ, mul_smul, Nat.succ_eq_add_one, add_assoc, add_comm 1, ← add_assoc]
    -- ⊢ I • I ^ n✝ • N F j ≤ N F (n✝ + j + 1)
    exact (Submodule.smul_mono_right ih).trans (F.smul_le _)
    -- 🎉 no goals
#align ideal.filtration.pow_smul_le Ideal.Filtration.pow_smul_le

theorem pow_smul_le_pow_smul (i j k : ℕ) : I ^ (i + k) • F.N j ≤ I ^ k • F.N (i + j) := by
  rw [add_comm, pow_add, mul_smul]
  -- ⊢ I ^ k • I ^ i • N F j ≤ I ^ k • N F (i + j)
  exact Submodule.smul_mono_right (F.pow_smul_le i j)
  -- 🎉 no goals
#align ideal.filtration.pow_smul_le_pow_smul Ideal.Filtration.pow_smul_le_pow_smul

protected theorem antitone : Antitone F.N :=
  antitone_nat_of_succ_le F.mono
#align ideal.filtration.antitone Ideal.Filtration.antitone

/-- The trivial `I`-filtration of `N`. -/
@[simps]
def _root_.Ideal.trivialFiltration (I : Ideal R) (N : Submodule R M) : I.Filtration M where
  N _ := N
  mono _ := le_of_eq rfl
  smul_le _ := Submodule.smul_le_right
#align ideal.trivial_filtration Ideal.trivialFiltration

/-- The `sup` of two `I.Filtration`s is an `I.Filtration`. -/
instance : Sup (I.Filtration M) :=
  ⟨fun F F' =>
    ⟨F.N ⊔ F'.N, fun i => sup_le_sup (F.mono i) (F'.mono i), fun i =>
      (le_of_eq (Submodule.smul_sup _ _ _)).trans <| sup_le_sup (F.smul_le i) (F'.smul_le i)⟩⟩

/-- The `sSup` of a family of `I.Filtration`s is an `I.Filtration`. -/
instance : SupSet (I.Filtration M) :=
  ⟨fun S =>
    { N := sSup (Ideal.Filtration.N '' S)
      mono := fun i => by
        apply sSup_le_sSup_of_forall_exists_le _
        -- ⊢ ∀ (x : Submodule R M), (x ∈ Set.range fun f => ↑f (i + 1)) → ∃ y, (y ∈ Set.r …
        rintro _ ⟨⟨_, F, hF, rfl⟩, rfl⟩
        -- ⊢ ∃ y, (y ∈ Set.range fun f => ↑f i) ∧ (fun f => ↑f (i + 1)) { val := F.N, pro …
        exact ⟨_, ⟨⟨_, F, hF, rfl⟩, rfl⟩, F.mono i⟩
        -- 🎉 no goals
      smul_le := fun i => by
        rw [sSup_eq_iSup', iSup_apply, Submodule.smul_iSup, iSup_apply]
        -- ⊢ ⨆ (i_1 : ↑(N '' S)), I • ↑i_1 i ≤ ⨆ (i_1 : ↑(N '' S)), ↑i_1 (i + 1)
        apply iSup_mono _
        -- ⊢ ∀ (i_1 : ↑(N '' S)), I • ↑i_1 i ≤ ↑i_1 (i + 1)
        rintro ⟨_, F, hF, rfl⟩
        -- ⊢ I • ↑{ val := F.N, property := (_ : ∃ a, a ∈ S ∧ a.N = F.N) } i ≤ ↑{ val :=  …
        exact F.smul_le i }⟩
        -- 🎉 no goals

/-- The `inf` of two `I.Filtration`s is an `I.Filtration`. -/
instance : Inf (I.Filtration M) :=
  ⟨fun F F' =>
    ⟨F.N ⊓ F'.N, fun i => inf_le_inf (F.mono i) (F'.mono i), fun i =>
      (Submodule.smul_inf_le _ _ _).trans <| inf_le_inf (F.smul_le i) (F'.smul_le i)⟩⟩

/-- The `sInf` of a family of `I.Filtration`s is an `I.Filtration`. -/
instance : InfSet (I.Filtration M) :=
  ⟨fun S =>
    { N := sInf (Ideal.Filtration.N '' S)
      mono := fun i => by
        apply sInf_le_sInf_of_forall_exists_le _
        -- ⊢ ∀ (x : Submodule R M), (x ∈ Set.range fun f => ↑f i) → ∃ y, (y ∈ Set.range f …
        rintro _ ⟨⟨_, F, hF, rfl⟩, rfl⟩
        -- ⊢ ∃ y, (y ∈ Set.range fun f => ↑f (i + 1)) ∧ y ≤ (fun f => ↑f i) { val := F.N, …
        exact ⟨_, ⟨⟨_, F, hF, rfl⟩, rfl⟩, F.mono i⟩
        -- 🎉 no goals
      smul_le := fun i => by
        rw [sInf_eq_iInf', iInf_apply, iInf_apply]
        -- ⊢ I • ⨅ (i_1 : ↑(N '' S)), ↑i_1 i ≤ ⨅ (i_1 : ↑(N '' S)), ↑i_1 (i + 1)
        refine' Submodule.smul_iInf_le.trans _
        -- ⊢ ⨅ (i_1 : ↑(N '' S)), I • ↑i_1 i ≤ ⨅ (i_1 : ↑(N '' S)), ↑i_1 (i + 1)
        apply iInf_mono _
        -- ⊢ ∀ (i_1 : ↑(N '' S)), I • ↑i_1 i ≤ ↑i_1 (i + 1)
        rintro ⟨_, F, hF, rfl⟩
        -- ⊢ I • ↑{ val := F.N, property := (_ : ∃ a, a ∈ S ∧ a.N = F.N) } i ≤ ↑{ val :=  …
        exact F.smul_le i }⟩
        -- 🎉 no goals

instance : Top (I.Filtration M) :=
  ⟨I.trivialFiltration ⊤⟩

instance : Bot (I.Filtration M) :=
  ⟨I.trivialFiltration ⊥⟩

@[simp]
theorem sup_N : (F ⊔ F').N = F.N ⊔ F'.N :=
  rfl
set_option linter.uppercaseLean3 false in
#align ideal.filtration.sup_N Ideal.Filtration.sup_N

@[simp]
theorem sSup_N (S : Set (I.Filtration M)) : (sSup S).N = sSup (Ideal.Filtration.N '' S) :=
  rfl
set_option linter.uppercaseLean3 false in
#align ideal.filtration.Sup_N Ideal.Filtration.sSup_N

@[simp]
theorem inf_N : (F ⊓ F').N = F.N ⊓ F'.N :=
  rfl
set_option linter.uppercaseLean3 false in
#align ideal.filtration.inf_N Ideal.Filtration.inf_N

@[simp]
theorem sInf_N (S : Set (I.Filtration M)) : (sInf S).N = sInf (Ideal.Filtration.N '' S) :=
  rfl
set_option linter.uppercaseLean3 false in
#align ideal.filtration.Inf_N Ideal.Filtration.sInf_N

@[simp]
theorem top_N : (⊤ : I.Filtration M).N = ⊤ :=
  rfl
set_option linter.uppercaseLean3 false in
#align ideal.filtration.top_N Ideal.Filtration.top_N

@[simp]
theorem bot_N : (⊥ : I.Filtration M).N = ⊥ :=
  rfl
set_option linter.uppercaseLean3 false in
#align ideal.filtration.bot_N Ideal.Filtration.bot_N

@[simp]
theorem iSup_N {ι : Sort*} (f : ι → I.Filtration M) : (iSup f).N = ⨆ i, (f i).N :=
  congr_arg sSup (Set.range_comp _ _).symm
set_option linter.uppercaseLean3 false in
#align ideal.filtration.supr_N Ideal.Filtration.iSup_N

@[simp]
theorem iInf_N {ι : Sort*} (f : ι → I.Filtration M) : (iInf f).N = ⨅ i, (f i).N :=
  congr_arg sInf (Set.range_comp _ _).symm
set_option linter.uppercaseLean3 false in
#align ideal.filtration.infi_N Ideal.Filtration.iInf_N

instance : CompleteLattice (I.Filtration M) :=
  Function.Injective.completeLattice Ideal.Filtration.N Ideal.Filtration.ext sup_N inf_N
    (fun _ => sSup_image) (fun _ => sInf_image) top_N bot_N

instance : Inhabited (I.Filtration M) :=
  ⟨⊥⟩

/-- An `I` filtration is stable if `I • F.N n = F.N (n+1)` for large enough `n`. -/
def Stable : Prop :=
  ∃ n₀, ∀ n ≥ n₀, I • F.N n = F.N (n + 1)
#align ideal.filtration.stable Ideal.Filtration.Stable

/-- The trivial stable `I`-filtration of `N`. -/
@[simps]
def _root_.Ideal.stableFiltration (I : Ideal R) (N : Submodule R M) : I.Filtration M where
  N i := I ^ i • N
  mono i := by dsimp only; rw [add_comm, pow_add, mul_smul]; exact Submodule.smul_le_right
               -- ⊢ I ^ (i + 1) • N ≤ I ^ i • N
                           -- ⊢ I ^ 1 • I ^ i • N ≤ I ^ i • N
                                                             -- 🎉 no goals
  smul_le i := by dsimp only; rw [add_comm, pow_add, mul_smul, pow_one]
                  -- ⊢ I • I ^ i • N ≤ I ^ (i + 1) • N
                              -- 🎉 no goals
#align ideal.stable_filtration Ideal.stableFiltration

theorem _root_.Ideal.stableFiltration_stable (I : Ideal R) (N : Submodule R M) :
    (I.stableFiltration N).Stable := by
  use 0
  -- ⊢ ∀ (n : ℕ), n ≥ 0 → I • Ideal.Filtration.N (stableFiltration I N) n = Ideal.F …
  intro n _
  -- ⊢ I • Ideal.Filtration.N (stableFiltration I N) n = Ideal.Filtration.N (stable …
  dsimp
  -- ⊢ I • I ^ n • N = I ^ (n + 1) • N
  rw [add_comm, pow_add, mul_smul, pow_one]
  -- 🎉 no goals
#align ideal.stable_filtration_stable Ideal.stableFiltration_stable

variable {F F'} (h : F.Stable)

theorem Stable.exists_pow_smul_eq : ∃ n₀, ∀ k, F.N (n₀ + k) = I ^ k • F.N n₀ := by
  obtain ⟨n₀, hn⟩ := h
  -- ⊢ ∃ n₀, ∀ (k : ℕ), N F (n₀ + k) = I ^ k • N F n₀
  use n₀
  -- ⊢ ∀ (k : ℕ), N F (n₀ + k) = I ^ k • N F n₀
  intro k
  -- ⊢ N F (n₀ + k) = I ^ k • N F n₀
  induction' k with _ ih
  -- ⊢ N F (n₀ + Nat.zero) = I ^ Nat.zero • N F n₀
  · simp
    -- 🎉 no goals
  · rw [Nat.succ_eq_add_one, ← add_assoc, ← hn, ih, add_comm, pow_add, mul_smul, pow_one]
    -- ⊢ n₀ + n✝ ≥ n₀
    linarith
    -- 🎉 no goals
#align ideal.filtration.stable.exists_pow_smul_eq Ideal.Filtration.Stable.exists_pow_smul_eq

theorem Stable.exists_pow_smul_eq_of_ge : ∃ n₀, ∀ n ≥ n₀, F.N n = I ^ (n - n₀) • F.N n₀ := by
  obtain ⟨n₀, hn₀⟩ := h.exists_pow_smul_eq
  -- ⊢ ∃ n₀, ∀ (n : ℕ), n ≥ n₀ → N F n = I ^ (n - n₀) • N F n₀
  use n₀
  -- ⊢ ∀ (n : ℕ), n ≥ n₀ → N F n = I ^ (n - n₀) • N F n₀
  intro n hn
  -- ⊢ N F n = I ^ (n - n₀) • N F n₀
  convert hn₀ (n - n₀)
  -- ⊢ n = n₀ + (n - n₀)
  rw [add_comm, tsub_add_cancel_of_le hn]
  -- 🎉 no goals
#align ideal.filtration.stable.exists_pow_smul_eq_of_ge Ideal.Filtration.Stable.exists_pow_smul_eq_of_ge

theorem stable_iff_exists_pow_smul_eq_of_ge :
    F.Stable ↔ ∃ n₀, ∀ n ≥ n₀, F.N n = I ^ (n - n₀) • F.N n₀ := by
  refine' ⟨Stable.exists_pow_smul_eq_of_ge, fun h => ⟨h.choose, fun n hn => _⟩⟩
  -- ⊢ I • N F n = N F (n + 1)
  rw [h.choose_spec n hn, h.choose_spec (n + 1) (by linarith), smul_smul, ← pow_succ,
    tsub_add_eq_add_tsub hn]
#align ideal.filtration.stable_iff_exists_pow_smul_eq_of_ge Ideal.Filtration.stable_iff_exists_pow_smul_eq_of_ge

theorem Stable.exists_forall_le (h : F.Stable) (e : F.N 0 ≤ F'.N 0) :
    ∃ n₀, ∀ n, F.N (n + n₀) ≤ F'.N n := by
  obtain ⟨n₀, hF⟩ := h
  -- ⊢ ∃ n₀, ∀ (n : ℕ), N F (n + n₀) ≤ N F' n
  use n₀
  -- ⊢ ∀ (n : ℕ), N F (n + n₀) ≤ N F' n
  intro n
  -- ⊢ N F (n + n₀) ≤ N F' n
  induction' n with n hn
  -- ⊢ N F (Nat.zero + n₀) ≤ N F' Nat.zero
  · refine' (F.antitone _).trans e; simp
    -- ⊢ 0 ≤ Nat.zero + n₀
                                    -- 🎉 no goals
  · rw [Nat.succ_eq_one_add, add_assoc, add_comm, add_comm 1 n, ← hF]
    -- ⊢ I • N F (n + n₀) ≤ N F' (n + 1)
    exact (Submodule.smul_mono_right hn).trans (F'.smul_le _)
    -- ⊢ n + n₀ ≥ n₀
    simp
    -- 🎉 no goals
#align ideal.filtration.stable.exists_forall_le Ideal.Filtration.Stable.exists_forall_le

theorem Stable.bounded_difference (h : F.Stable) (h' : F'.Stable) (e : F.N 0 = F'.N 0) :
    ∃ n₀, ∀ n, F.N (n + n₀) ≤ F'.N n ∧ F'.N (n + n₀) ≤ F.N n := by
  obtain ⟨n₁, h₁⟩ := h.exists_forall_le (le_of_eq e)
  -- ⊢ ∃ n₀, ∀ (n : ℕ), N F (n + n₀) ≤ N F' n ∧ N F' (n + n₀) ≤ N F n
  obtain ⟨n₂, h₂⟩ := h'.exists_forall_le (le_of_eq e.symm)
  -- ⊢ ∃ n₀, ∀ (n : ℕ), N F (n + n₀) ≤ N F' n ∧ N F' (n + n₀) ≤ N F n
  use max n₁ n₂
  -- ⊢ ∀ (n : ℕ), N F (n + max n₁ n₂) ≤ N F' n ∧ N F' (n + max n₁ n₂) ≤ N F n
  intro n
  -- ⊢ N F (n + max n₁ n₂) ≤ N F' n ∧ N F' (n + max n₁ n₂) ≤ N F n
  refine' ⟨(F.antitone _).trans (h₁ n), (F'.antitone _).trans (h₂ n)⟩ <;> simp
  -- ⊢ n + n₁ ≤ n + max n₁ n₂
                                                                          -- 🎉 no goals
                                                                          -- 🎉 no goals
#align ideal.filtration.stable.bounded_difference Ideal.Filtration.Stable.bounded_difference

open PolynomialModule

variable (F F')

/-- The `R[IX]`-submodule of `M[X]` associated with an `I`-filtration. -/
protected def submodule : Submodule (reesAlgebra I) (PolynomialModule R M) where
  carrier := { f | ∀ i, f i ∈ F.N i }
  add_mem' hf hg i := Submodule.add_mem _ (hf i) (hg i)
  zero_mem' i := Submodule.zero_mem _
  smul_mem' r f hf i := by
    rw [Subalgebra.smul_def, PolynomialModule.smul_apply]
    -- ⊢ ∑ x in Finset.Nat.antidiagonal i, coeff (↑r) x.fst • ↑f x.snd ∈ N F i
    apply Submodule.sum_mem
    -- ⊢ ∀ (c : ℕ × ℕ), c ∈ Finset.Nat.antidiagonal i → coeff (↑r) c.fst • ↑f c.snd ∈ …
    rintro ⟨j, k⟩ e
    -- ⊢ coeff ↑r (j, k).fst • ↑f (j, k).snd ∈ N F i
    rw [Finset.Nat.mem_antidiagonal] at e
    -- ⊢ coeff ↑r (j, k).fst • ↑f (j, k).snd ∈ N F i
    subst e
    -- ⊢ coeff ↑r (j, k).fst • ↑f (j, k).snd ∈ N F ((j, k).fst + (j, k).snd)
    exact F.pow_smul_le j k (Submodule.smul_mem_smul (r.2 j) (hf k))
    -- 🎉 no goals
#align ideal.filtration.submodule Ideal.Filtration.submodule

@[simp]
theorem mem_submodule (f : PolynomialModule R M) : f ∈ F.submodule ↔ ∀ i, f i ∈ F.N i :=
  Iff.rfl
#align ideal.filtration.mem_submodule Ideal.Filtration.mem_submodule

theorem inf_submodule : (F ⊓ F').submodule = F.submodule ⊓ F'.submodule := by
  ext
  -- ⊢ x✝ ∈ Filtration.submodule (F ⊓ F') ↔ x✝ ∈ Filtration.submodule F ⊓ Filtratio …
  exact forall_and
  -- 🎉 no goals
#align ideal.filtration.inf_submodule Ideal.Filtration.inf_submodule

variable (I M)

/-- `Ideal.Filtration.submodule` as an `InfHom`. -/
def submoduleInfHom :
    InfHom (I.Filtration M) (Submodule (reesAlgebra I) (PolynomialModule R M)) where
  toFun := Ideal.Filtration.submodule
  map_inf' := inf_submodule
#align ideal.filtration.submodule_inf_hom Ideal.Filtration.submoduleInfHom

variable {I M}

theorem submodule_closure_single :
    AddSubmonoid.closure (⋃ i, single R i '' (F.N i : Set M)) = F.submodule.toAddSubmonoid := by
  apply le_antisymm
  -- ⊢ AddSubmonoid.closure (⋃ (i : ℕ), ↑(single R i) '' ↑(N F i)) ≤ (Filtration.su …
  · rw [AddSubmonoid.closure_le, Set.iUnion_subset_iff]
    -- ⊢ ∀ (i : ℕ), ↑(single R i) '' ↑(N F i) ⊆ ↑(Filtration.submodule F).toAddSubmon …
    rintro i _ ⟨m, hm, rfl⟩ j
    -- ⊢ ↑(↑(single R i) m) j ∈ N F j
    rw [single_apply]
    -- ⊢ (if i = j then m else 0) ∈ N F j
    split_ifs with h
    -- ⊢ m ∈ N F j
    · rwa [← h]
      -- 🎉 no goals
    · exact (F.N j).zero_mem
      -- 🎉 no goals
  · intro f hf
    -- ⊢ f ∈ AddSubmonoid.closure (⋃ (i : ℕ), ↑(single R i) '' ↑(N F i))
    rw [← f.sum_single]
    -- ⊢ Finsupp.sum f Finsupp.single ∈ AddSubmonoid.closure (⋃ (i : ℕ), ↑(single R i …
    apply AddSubmonoid.sum_mem _ _
    -- ⊢ ∀ (c : ℕ), c ∈ f.support → Finsupp.single c (↑f c) ∈ AddSubmonoid.closure (⋃ …
    rintro c -
    -- ⊢ Finsupp.single c (↑f c) ∈ AddSubmonoid.closure (⋃ (i : ℕ), ↑(single R i) ''  …
    exact AddSubmonoid.subset_closure (Set.subset_iUnion _ c <| Set.mem_image_of_mem _ (hf c))
    -- 🎉 no goals
#align ideal.filtration.submodule_closure_single Ideal.Filtration.submodule_closure_single

theorem submodule_span_single :
    Submodule.span (reesAlgebra I) (⋃ i, single R i '' (F.N i : Set M)) = F.submodule := by
  rw [← Submodule.span_closure, submodule_closure_single, Submodule.coe_toAddSubmonoid]
  -- ⊢ Submodule.span { x // x ∈ reesAlgebra I } ↑(Filtration.submodule F) = Filtra …
  exact Submodule.span_eq (Filtration.submodule F)
  -- 🎉 no goals
#align ideal.filtration.submodule_span_single Ideal.Filtration.submodule_span_single

theorem submodule_eq_span_le_iff_stable_ge (n₀ : ℕ) :
    F.submodule = Submodule.span _ (⋃ i ≤ n₀, single R i '' (F.N i : Set M)) ↔
      ∀ n ≥ n₀, I • F.N n = F.N (n + 1) := by
  rw [← submodule_span_single, ← LE.le.le_iff_eq, Submodule.span_le, Set.iUnion_subset_iff]
  -- ⊢ (∀ (i : ℕ), ↑(single R i) '' ↑(N F i) ⊆ ↑(Submodule.span { x // x ∈ reesAlge …
  swap; · exact Submodule.span_mono (Set.iUnion₂_subset_iUnion _ _)
  -- ⊢ Submodule.span { x // x ∈ reesAlgebra I } (⋃ (i : ℕ) (_ : i ≤ n₀), ↑(single  …
          -- 🎉 no goals
  constructor
  -- ⊢ (∀ (i : ℕ), ↑(single R i) '' ↑(N F i) ⊆ ↑(Submodule.span { x // x ∈ reesAlge …
  · intro H n hn
    -- ⊢ I • N F n = N F (n + 1)
    refine' (F.smul_le n).antisymm _
    -- ⊢ N F (n + 1) ≤ I • N F n
    intro x hx
    -- ⊢ x ∈ I • N F n
    obtain ⟨l, hl⟩ := (Finsupp.mem_span_iff_total _ _ _).mp (H _ ⟨x, hx, rfl⟩)
    -- ⊢ x ∈ I • N F n
    replace hl := congr_arg (fun f : ℕ →₀ M => f (n + 1)) hl
    -- ⊢ x ∈ I • N F n
    dsimp only at hl
    -- ⊢ x ∈ I • N F n
    erw [Finsupp.single_eq_same] at hl
    -- ⊢ x ∈ I • N F n
    rw [← hl, Finsupp.total_apply, Finsupp.sum_apply]
    -- ⊢ (Finsupp.sum l fun a₁ b => ↑(b • ↑a₁) (n + 1)) ∈ I • N F n
    apply Submodule.sum_mem _ _
    -- ⊢ ∀ (c : ↑(⋃ (i : ℕ) (_ : i ≤ n₀), ↑(single R i) '' ↑(N F i))), c ∈ l.support  …
    rintro ⟨_, _, ⟨n', rfl⟩, _, ⟨hn', rfl⟩, m, hm, rfl⟩ -
    -- ⊢ (fun a₁ b => ↑(b • ↑a₁) (n + 1)) { val := ↑(single R n') m, property := (_ : …
    dsimp only [Subtype.coe_mk]
    -- ⊢ ↑(↑l { val := ↑(single R n') m, property := (_ : ∃ t, (t ∈ Set.range fun i = …
    rw [Subalgebra.smul_def, smul_single_apply, if_pos (show n' ≤ n + 1 by linarith)]
    -- ⊢ coeff (↑(↑l { val := ↑(single R n') m, property := (_ : ∃ t, (t ∈ Set.range  …
    have e : n' ≤ n := by linarith
    -- ⊢ coeff (↑(↑l { val := ↑(single R n') m, property := (_ : ∃ t, (t ∈ Set.range  …
    have := F.pow_smul_le_pow_smul (n - n') n' 1
    -- ⊢ coeff (↑(↑l { val := ↑(single R n') m, property := (_ : ∃ t, (t ∈ Set.range  …
    rw [tsub_add_cancel_of_le e, pow_one, add_comm _ 1, ← add_tsub_assoc_of_le e, add_comm] at this
    -- ⊢ coeff (↑(↑l { val := ↑(single R n') m, property := (_ : ∃ t, (t ∈ Set.range  …
    exact this (Submodule.smul_mem_smul ((l _).2 <| n + 1 - n') hm)
    -- 🎉 no goals
  · let F' := Submodule.span (reesAlgebra I) (⋃ i ≤ n₀, single R i '' (F.N i : Set M))
    -- ⊢ (∀ (n : ℕ), n ≥ n₀ → I • N F n = N F (n + 1)) → ∀ (i : ℕ), ↑(single R i) ''  …
    intro hF i
    -- ⊢ ↑(single R i) '' ↑(N F i) ⊆ ↑(Submodule.span { x // x ∈ reesAlgebra I } (⋃ ( …
    have : ∀ i ≤ n₀, single R i '' (F.N i : Set M) ⊆ F' := by
      -- Porting note: Original proof was
      -- `fun i hi => Set.Subset.trans (Set.subset_iUnion₂ i hi) Submodule.subset_span`
      intro i hi
      refine Set.Subset.trans ?_ Submodule.subset_span
      refine @Set.subset_iUnion₂ _ _ _ (fun i => fun _ => ↑((single R i) '' ((N F i) : Set M))) i ?_
      exact hi
    induction' i with j hj
    -- ⊢ ↑(single R Nat.zero) '' ↑(N F Nat.zero) ⊆ ↑(Submodule.span { x // x ∈ reesAl …
    · exact this _ (zero_le _)
      -- 🎉 no goals
    by_cases hj' : j.succ ≤ n₀
    -- ⊢ ↑(single R (Nat.succ j)) '' ↑(N F (Nat.succ j)) ⊆ ↑(Submodule.span { x // x  …
    · exact this _ hj'
      -- 🎉 no goals
    simp only [not_le, Nat.lt_succ_iff] at hj'
    -- ⊢ ↑(single R (Nat.succ j)) '' ↑(N F (Nat.succ j)) ⊆ ↑(Submodule.span { x // x  …
    rw [Nat.succ_eq_add_one, ← hF _ hj']
    -- ⊢ ↑(single R (j + 1)) '' ↑(I • N F j) ⊆ ↑(Submodule.span { x // x ∈ reesAlgebr …
    rintro _ ⟨m, hm, rfl⟩
    -- ⊢ ↑(single R (j + 1)) m ∈ ↑(Submodule.span { x // x ∈ reesAlgebra I } (⋃ (i :  …
    refine' Submodule.smul_induction_on hm (fun r hr m' hm' => _) (fun x y hx hy => _)
    -- ⊢ ↑(single R (j + 1)) (r • m') ∈ ↑(Submodule.span { x // x ∈ reesAlgebra I } ( …
    · rw [add_comm, ← monomial_smul_single]
      -- ⊢ ↑(monomial 1) r • ↑(single R j) m' ∈ ↑(Submodule.span { x // x ∈ reesAlgebra …
      exact F'.smul_mem
        ⟨_, reesAlgebra.monomial_mem.mpr (by rwa [pow_one])⟩ (hj <| Set.mem_image_of_mem _ hm')
    · rw [map_add]
      -- ⊢ ↑(single R (j + 1)) x + ↑(single R (j + 1)) y ∈ ↑(Submodule.span { x // x ∈  …
      exact F'.add_mem hx hy
      -- 🎉 no goals
#align ideal.filtration.submodule_eq_span_le_iff_stable_ge Ideal.Filtration.submodule_eq_span_le_iff_stable_ge

/-- If the components of a filtration are finitely generated, then the filtration is stable iff
its associated submodule of is finitely generated. -/
theorem submodule_fg_iff_stable (hF' : ∀ i, (F.N i).FG) : F.submodule.FG ↔ F.Stable := by
  classical
  delta Ideal.Filtration.Stable
  simp_rw [← F.submodule_eq_span_le_iff_stable_ge]
  constructor
  · rintro H
    refine H.stablizes_of_iSup_eq
        ⟨fun n₀ => Submodule.span _ (⋃ (i : ℕ) (_ : i ≤ n₀), single R i '' ↑(F.N i)), ?_⟩ ?_
    · intro n m e
      rw [Submodule.span_le, Set.iUnion₂_subset_iff]
      intro i hi
      refine Set.Subset.trans ?_ Submodule.subset_span
      refine @Set.subset_iUnion₂ _ _ _ (fun i => fun _ => ↑((single R i) '' ((N F i) : Set M))) i ?_
      exact hi.trans e
    · dsimp
      rw [← Submodule.span_iUnion, ← submodule_span_single]
      congr 1
      ext
      simp only [Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, exists_prop]
      constructor
      · rintro ⟨-, i, -, e⟩; exact ⟨i, e⟩
      · rintro ⟨i, e⟩; exact ⟨i, i, le_refl i, e⟩
  · rintro ⟨n, hn⟩
    rw [hn]
    simp_rw [Submodule.span_iUnion₂, ← Finset.mem_range_succ_iff, iSup_subtype']
    apply Submodule.fg_iSup
    rintro ⟨i, hi⟩
    obtain ⟨s, hs⟩ := hF' i
    have : Submodule.span (reesAlgebra I) (s.image (lsingle R i) : Set (PolynomialModule R M)) =
        Submodule.span _ (single R i '' (F.N i : Set M)) := by
      rw [Finset.coe_image, ← Submodule.span_span_of_tower R, ← Submodule.map_span, hs]; rfl
    rw [Subtype.coe_mk, ← this]
    exact ⟨_, rfl⟩
#align ideal.filtration.submodule_fg_iff_stable Ideal.Filtration.submodule_fg_iff_stable

variable {F}

theorem Stable.of_le [IsNoetherianRing R] [Module.Finite R M] (hF : F.Stable)
    {F' : I.Filtration M} (hf : F' ≤ F) : F'.Stable := by
  have := isNoetherian_of_isNoetherianRing_of_finite R M
  -- ⊢ Stable F'
  rw [← submodule_fg_iff_stable] at hF ⊢
  any_goals intro i; exact IsNoetherian.noetherian _
  -- ⊢ Submodule.FG (Filtration.submodule F')
  have := isNoetherian_of_fg_of_noetherian _ hF
  -- ⊢ Submodule.FG (Filtration.submodule F')
  rw [isNoetherian_submodule] at this
  -- ⊢ Submodule.FG (Filtration.submodule F')
  exact this _ (OrderHomClass.mono (submoduleInfHom M I) hf)
  -- 🎉 no goals
#align ideal.filtration.stable.of_le Ideal.Filtration.Stable.of_le

theorem Stable.inter_right [IsNoetherianRing R] [Module.Finite R M] (hF : F.Stable) :
    (F ⊓ F').Stable :=
  hF.of_le inf_le_left
#align ideal.filtration.stable.inter_right Ideal.Filtration.Stable.inter_right

theorem Stable.inter_left [IsNoetherianRing R] [Module.Finite R M] (hF : F.Stable) :
    (F' ⊓ F).Stable :=
  hF.of_le inf_le_right
#align ideal.filtration.stable.inter_left Ideal.Filtration.Stable.inter_left

end Ideal.Filtration

variable (I)

/-- **Artin-Rees lemma** -/
theorem Ideal.exists_pow_inf_eq_pow_smul [IsNoetherianRing R] [Module.Finite R M]
    (N : Submodule R M) : ∃ k : ℕ, ∀ n ≥ k, I ^ n • ⊤ ⊓ N = I ^ (n - k) • (I ^ k • ⊤ ⊓ N) :=
  ((I.stableFiltration_stable ⊤).inter_right (I.trivialFiltration N)).exists_pow_smul_eq_of_ge
#align ideal.exists_pow_inf_eq_pow_smul Ideal.exists_pow_inf_eq_pow_smul

theorem Ideal.mem_iInf_smul_pow_eq_bot_iff [IsNoetherianRing R] [Module.Finite R M] (x : M) :
    x ∈ (⨅ i : ℕ, I ^ i • ⊤ : Submodule R M) ↔ ∃ r : I, (r : R) • x = x := by
  let N := (⨅ i : ℕ, I ^ i • ⊤ : Submodule R M)
  -- ⊢ x ∈ ⨅ (i : ℕ), I ^ i • ⊤ ↔ ∃ r, ↑r • x = x
  have hN : ∀ k, (I.stableFiltration ⊤ ⊓ I.trivialFiltration N).N k = N :=
    fun k => inf_eq_right.mpr ((iInf_le _ k).trans <| le_of_eq <| by simp)
  constructor
  -- ⊢ x ∈ ⨅ (i : ℕ), I ^ i • ⊤ → ∃ r, ↑r • x = x
  · have := isNoetherian_of_isNoetherianRing_of_finite R M
    -- ⊢ x ∈ ⨅ (i : ℕ), I ^ i • ⊤ → ∃ r, ↑r • x = x
    obtain ⟨r, hr₁, hr₂⟩ :=
      Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I N (IsNoetherian.noetherian N) (by
        obtain ⟨k, hk⟩ := (I.stableFiltration_stable ⊤).inter_right (I.trivialFiltration N)
        have := hk k (le_refl _)
        rw [hN, hN] at this
        exact le_of_eq this.symm)
    intro H
    -- ⊢ ∃ r, ↑r • x = x
    exact ⟨⟨r, hr₁⟩, hr₂ _ H⟩
    -- 🎉 no goals
  · rintro ⟨r, eq⟩
    -- ⊢ x ∈ ⨅ (i : ℕ), I ^ i • ⊤
    rw [Submodule.mem_iInf]
    -- ⊢ ∀ (i : ℕ), x ∈ I ^ i • ⊤
    intro i
    -- ⊢ x ∈ I ^ i • ⊤
    induction' i with i hi
    -- ⊢ x ∈ I ^ Nat.zero • ⊤
    · simp
      -- 🎉 no goals
    · rw [Nat.succ_eq_one_add, pow_add, ← smul_smul, pow_one, ← eq]
      -- ⊢ ↑r • x ∈ I • I ^ i • ⊤
      exact Submodule.smul_mem_smul r.prop hi
      -- 🎉 no goals
#align ideal.mem_infi_smul_pow_eq_bot_iff Ideal.mem_iInf_smul_pow_eq_bot_iff

theorem Ideal.iInf_pow_smul_eq_bot_of_localRing [IsNoetherianRing R] [LocalRing R]
    [Module.Finite R M] (h : I ≠ ⊤) : (⨅ i : ℕ, I ^ i • ⊤ : Submodule R M) = ⊥ := by
  rw [eq_bot_iff]
  -- ⊢ ⨅ (i : ℕ), I ^ i • ⊤ ≤ ⊥
  intro x hx
  -- ⊢ x ∈ ⊥
  obtain ⟨r, hr⟩ := (I.mem_iInf_smul_pow_eq_bot_iff x).mp hx
  -- ⊢ x ∈ ⊥
  have := LocalRing.isUnit_one_sub_self_of_mem_nonunits _ (LocalRing.le_maximalIdeal h r.prop)
  -- ⊢ x ∈ ⊥
  apply this.smul_left_cancel.mp
  -- ⊢ (1 - ↑r) • x = (1 - ↑r) • 0
  simp [sub_smul, hr]
  -- 🎉 no goals
#align ideal.infi_pow_smul_eq_bot_of_local_ring Ideal.iInf_pow_smul_eq_bot_of_localRing

/-- **Krull's intersection theorem** for noetherian local rings. -/
theorem Ideal.iInf_pow_eq_bot_of_localRing [IsNoetherianRing R] [LocalRing R] (h : I ≠ ⊤) :
    ⨅ i : ℕ, I ^ i = ⊥ := by
  convert I.iInf_pow_smul_eq_bot_of_localRing (M := R) h
  -- ⊢ I ^ x✝ = I ^ x✝ • ⊤
  ext i
  -- ⊢ i ∈ I ^ x✝ ↔ i ∈ I ^ x✝ • ⊤
  rw [smul_eq_mul, ← Ideal.one_eq_top, mul_one]
  -- 🎉 no goals
#align ideal.infi_pow_eq_bot_of_local_ring Ideal.iInf_pow_eq_bot_of_localRing

/-- **Krull's intersection theorem** for noetherian domains. -/
theorem Ideal.iInf_pow_eq_bot_of_isDomain [IsNoetherianRing R] [IsDomain R] (h : I ≠ ⊤) :
    ⨅ i : ℕ, I ^ i = ⊥ := by
  rw [eq_bot_iff]
  -- ⊢ ⨅ (i : ℕ), I ^ i ≤ ⊥
  intro x hx
  -- ⊢ x ∈ ⊥
  by_contra hx'
  -- ⊢ False
  have := Ideal.mem_iInf_smul_pow_eq_bot_iff I x
  -- ⊢ False
  simp_rw [smul_eq_mul, ← Ideal.one_eq_top, mul_one] at this
  -- ⊢ False
  obtain ⟨r, hr⟩ := this.mp hx
  -- ⊢ False
  have := mul_right_cancel₀ hx' (hr.trans (one_mul x).symm)
  -- ⊢ False
  exact I.eq_top_iff_one.not.mp h (this ▸ r.prop)
  -- 🎉 no goals
#align ideal.infi_pow_eq_bot_of_is_domain Ideal.iInf_pow_eq_bot_of_isDomain
