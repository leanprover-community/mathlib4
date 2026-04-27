/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yi Song
-/
module

public import Mathlib.RingTheory.Depth.Rees
public import Mathlib.Tactic.ENatToNat

/-!

# The Definition of Depth

In this section, we give the definition of depth of a module over a local ring. We also extablished
some basic facts about it using the Rees theorem proven above.
In this section, we set `R` be a noetherian commutative ring, all modules refer to `R`-module.

# Main definition and results

* `moduleDepth` : The depth between two `R`-modules defined as the minimal nontrivial `Ext`
  between them, equal to `⊤ : ℕ∞` if no such index.

* `Ideal.depth` : The depth of a `R`-module `M` with respect to an ideal `I`,
  defined as `moduleDepth (R⧸ I, M)`.

* `IsLocalRing.depth` : For a local ring `R`, the depth of a `R`-module with respect to
  the maximal ideal.

* `moduleDepth_eq_depth_of_supp_eq` : For `I : Ideal R`, if support of a finitely generated module
  `N` is equal to `PrimeSpectrum.zeroLocus I`, then for any finitely generated nontrivial module
  `M` with `IM < M`, `moduleDepth N M = I.depth M`

* `moduleDepth_eq_sSup_length_regular` : For `I : Ideal R`, nontrivial finitely generated module
  `M` and N`, if support of `N` is equal to `PrimeSpectrum.zeroLocus I` and `IM < M`,
  `moduleDepth N M` is equal to the supremum of length of `M`-regular sequence in `I`

* `IsLocalRing.depth_quotSMulTop_succ_eq_moduleDepth` : For `R` local, a `R`-module `M` and a
  `M`-regular element `x` in `maximalIdeal R`,
  `IsLocalRing.depth (QuotSMulTop x M) + 1 = IsLocalRing.depth M`

* `moduleDepth_quotient_regular_sequence_add_length_eq_moduleDepth` : For `R` local, a `R`-module
  `M` and a `M`-regular sequence `rs` in `maximalIdeal R`,
  `moduleDepth N (M ⧸ (Ideal.ofList rs) • (⊤ : Submodule R M)) + rs.length = moduleDepth N M`

-/

@[expose] public section

open IsLocalRing LinearMap Module

universe v u

open RingTheory.Sequence Ideal CategoryTheory Abelian Limits Pointwise ModuleCat IsSMulRegular

variable {R : Type u} [CommRing R] [Small.{v} R]

section depth

/-- The depth between two `R`-modules defined as the minimal nontrivial `Ext` between them. -/
noncomputable def moduleDepth (N M : ModuleCat.{v} R) : ℕ∞ :=
  sSup {n : ℕ∞ | ∀ i : ℕ, i < n → Subsingleton (Ext N M i)}

/-- The depth of a `R`-module `M` with respect to an ideal `I`,
defined as `moduleDepth (R⧸ I, M)`. -/
noncomputable def Ideal.depth (I : Ideal R) (M : ModuleCat.{v} R) : ℕ∞ :=
  moduleDepth (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M

/-- For a local ring `R`, the depth of a `R`-module with respect to the maximal ideal. -/
noncomputable def IsLocalRing.depth [IsLocalRing R] (M : ModuleCat.{v} R) : ℕ∞ :=
  (IsLocalRing.maximalIdeal R).depth M

set_option backward.isDefEq.respectTransparency false in
open Classical in
lemma moduleDepth_eq_find (N M : ModuleCat.{v} R) (h : ∃ n, Nontrivial (Ext N M n)) :
    moduleDepth N M = Nat.find h := by
  apply le_antisymm
  · simp only [moduleDepth, sSup_le_iff, Set.mem_setOf_eq]
    intro n hn
    by_contra gt
    absurd Nat.find_spec h
    exact not_nontrivial_iff_subsingleton.mpr (hn (Nat.find h) (not_le.mp gt))
  · simp only [moduleDepth]
    apply le_sSup
    simp only [Set.mem_setOf_eq, Nat.cast_lt, Nat.lt_find_iff]
    intro i hi
    exact not_nontrivial_iff_subsingleton.mp (hi i (le_refl i))

lemma moduleDepth_eq_top_iff (N M : ModuleCat.{v} R) :
    moduleDepth N M = ⊤ ↔ ∀ i, Subsingleton (Ext N M i) := by
  refine ⟨fun h ↦ ?_, fun h ↦ csSup_eq_top_of_top_mem (fun i _ ↦ h i)⟩
  by_contra! exist
  rw [moduleDepth_eq_find N M exist] at h
  simp at h

lemma moduleDepth_lt_top_iff (N M : ModuleCat.{v} R) :
    moduleDepth N M < ⊤ ↔ ∃ n, Nontrivial (Ext N M n) := by
  convert (moduleDepth_eq_top_iff N M).not
  · exact lt_top_iff_ne_top
  · simp [not_subsingleton_iff_nontrivial]

set_option backward.isDefEq.respectTransparency false in
lemma moduleDepth_eq_iff (N M : ModuleCat.{v} R) (n : ℕ) : moduleDepth N M = n ↔
    Nontrivial (Ext N M n) ∧ ∀ i < n, Subsingleton (Ext N M i) := by
  classical
  refine ⟨fun h ↦ ?_, fun ⟨ntr, h⟩ ↦ ?_⟩
  · have exist := (moduleDepth_lt_top_iff N M).mp (by simp [h])
    simp only [moduleDepth_eq_find _ _ exist, Nat.cast_inj] at h
    refine ⟨h ▸ Nat.find_spec exist, fun i hi ↦ ?_⟩
    exact not_nontrivial_iff_subsingleton.mp (Nat.find_min exist (lt_of_lt_of_eq hi h.symm))
  · have exist : ∃ n, Nontrivial (Ext N M n) := by use n
    simp only [moduleDepth_eq_find _ _ exist, Nat.cast_inj, Nat.find_eq_iff, ntr, true_and]
    intro i hi
    exact not_nontrivial_iff_subsingleton.mpr (h i hi)

lemma ext_subsingleton_of_lt_moduleDepth {N M : ModuleCat.{v} R} {i : ℕ}
    (lt : i < moduleDepth N M) : Subsingleton (Ext N M i) := by
  by_cases lttop : moduleDepth N M < ⊤
  · let _ : Nonempty {n : ℕ∞ | ∀ (i : ℕ), i < n → Subsingleton (Ext N M i)} :=
      Nonempty.intro ⟨(0 : ℕ∞), by simp⟩
    exact ENat.sSup_mem_of_nonempty_of_lt_top lttop i lt
  · simp only [not_lt, top_le_iff, moduleDepth_eq_top_iff] at lttop
    exact lttop i

lemma moduleDepth_eq_sup_nat (N M : ModuleCat.{v} R) : moduleDepth N M =
    sSup {n : ℕ∞ | n < ⊤ ∧ ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} := by
  simp only [moduleDepth]
  by_cases h : ⊤ ∈ {n : ℕ∞ | ∀ (i : ℕ), i < n → Subsingleton (Ext N M i)}
  · rw [csSup_eq_top_of_top_mem h, eq_comm, ENat.eq_top_iff_forall_ge]
    intro m
    apply le_sSup
    simp only [Set.mem_setOf_eq, ENat.coe_lt_top, forall_const] at h
    simpa using fun i _ ↦ h i
  · congr
    ext n
    exact ⟨fun mem ↦ ⟨top_notMem_iff.mp h n mem, mem⟩, fun mem ↦ mem.2⟩

lemma moduleDepth_eq_depth_of_supp_eq [IsNoetherianRing R] (I : Ideal R)
    (N M : ModuleCat.{v} R) [Module.Finite R M] [Nfin : Module.Finite R N]
    [Nntr : Nontrivial N] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I) :
    moduleDepth N M = I.depth M := by
  have (n : ℕ) : (∀ i < n, Subsingleton (Ext N M i)) ↔
    (∀ i < n, Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M i)) := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · apply ((exists_isRegular_tfae I n M smul_lt).out 1 2).mpr
      use N
    · have rees := ((exists_isRegular_tfae I n M smul_lt).out 0 1).mpr h
      exact rees N Nntr Nfin (le_of_eq hsupp)
  simp only [moduleDepth_eq_sup_nat, Ideal.depth]
  congr
  ext n
  simp only [and_congr_right_iff]
  intro lt_top
  convert this n.toNat
  <;> nth_rw 1 [← ENat.coe_toNat (LT.lt.ne_top lt_top), ENat.coe_lt_coe]

open Opposite in
lemma moduleDepth_eq_of_iso_fst (M : ModuleCat.{v} R) {N N' : ModuleCat.{v} R} (e : N ≅ N') :
    moduleDepth N M = moduleDepth N' M := by
  simp only [moduleDepth]
  congr
  ext n
  exact forall₂_congr fun i _ ↦
    (((extFunctor.{v} i).mapIso e.symm.op).app M).addCommGroupIsoToAddEquiv.subsingleton_congr

lemma moduleDepth_eq_of_iso_snd (N : ModuleCat.{v} R) {M M' : ModuleCat.{v} R} (e : M ≅ M') :
    moduleDepth N M = moduleDepth N M' := by
  simp only [moduleDepth]
  congr
  ext n
  exact forall₂_congr fun i _ ↦
    ((extFunctorObj N i).mapIso e).addCommGroupIsoToAddEquiv.subsingleton_congr

lemma Ideal.depth_eq_of_iso (I : Ideal R) {M M' : ModuleCat.{v} R} (e : M ≅ M') :
    I.depth M = I.depth M' :=
  moduleDepth_eq_of_iso_snd (ModuleCat.of R (Shrink.{v, u} (R ⧸ I))) e

lemma IsLocalRing.depth_eq_of_iso [IsLocalRing R] {M M' : ModuleCat.{v} R} (e : M ≅ M') :
    IsLocalRing.depth M = IsLocalRing.depth M' :=
  (maximalIdeal R).depth_eq_of_iso e

set_option backward.isDefEq.respectTransparency false in
lemma moduleDepth_eq_zero_of_hom_nontrivial (N M : ModuleCat.{v} R) :
    moduleDepth N M = 0 ↔ Nontrivial (N →ₗ[R] M) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [moduleDepth] at h
    have : 1 ∉ {n : ℕ∞ | ∀ (i : ℕ), i < n → Subsingleton (Ext N M i)} := by
      by_contra mem
      absurd le_sSup mem
      simp [h]
    simp only [Set.mem_setOf_eq, Nat.cast_lt_one, forall_eq,
      not_subsingleton_iff_nontrivial, Ext.addEquiv₀.nontrivial_congr] at this
    exact (ModuleCat.homLinearEquiv (S := R)).nontrivial_congr.mp this
  · apply nonpos_iff_eq_zero.mp (sSup_le (fun n mem ↦ ?_))
    by_contra pos
    absurd mem 0 (lt_of_not_ge pos)
    simpa [not_subsingleton_iff_nontrivial, Ext.addEquiv₀.nontrivial_congr]
      using (ModuleCat.homLinearEquiv (S := R)).nontrivial_congr.mpr h

lemma moduleDepth_ge_min_of_shortExact_snd_fst
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    (N : ModuleCat.{v} R) : moduleDepth S.X₂ N ≥ moduleDepth S.X₁ N ⊓ moduleDepth S.X₃ N := by
  apply le_sSup
  simp only [Set.mem_setOf_eq, lt_inf_iff, and_imp]
  intro i hi1 hi3
  have zero1 : IsZero (AddCommGrpCat.of (Ext S.X₁ N i)) :=
      @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi1)
  have zero3 : IsZero (AddCommGrpCat.of (Ext S.X₃ N i)) :=
      @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi3)
  exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    (Ext.contravariant_sequence_exact₂' hS N i)
    (zero3.eq_zero_of_src _) (zero1.eq_zero_of_tgt _)

lemma moduleDepth_ge_min_of_shortExact_fst_fst
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    (N : ModuleCat.{v} R) : moduleDepth S.X₁ N ≥ moduleDepth S.X₂ N ⊓ (moduleDepth S.X₃ N - 1) := by
  apply le_sSup
  simp only [Set.mem_setOf_eq, lt_inf_iff, and_imp]
  intro i hi2 hi3
  have zero2 : IsZero (AddCommGrpCat.of (Ext S.X₂ N i)) :=
      @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi2)
  have hi3' : (i + 1 : ℕ) < moduleDepth S.X₃ N := by
    simpa using lt_tsub_iff_right.mp hi3
  have zero3 : IsZero (AddCommGrpCat.of (Ext S.X₃ N (i + 1))) :=
      @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi3')
  exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    (Ext.contravariant_sequence_exact₁' hS N i (i + 1) (add_comm _ _))
    (zero2.eq_zero_of_src _) (zero3.eq_zero_of_tgt _)

lemma moduleDepth_ge_min_of_shortExact_trd_fst
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    (N : ModuleCat.{v} R) : moduleDepth S.X₃ N ≥ moduleDepth S.X₂ N ⊓ (moduleDepth S.X₁ N + 1) := by
  apply le_sSup
  simp only [Set.mem_setOf_eq, lt_inf_iff, and_imp]
  intro i hi2 hi1
  have zero2 : IsZero (AddCommGrpCat.of (Ext S.X₂ N i)) :=
    @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi2)
  by_cases eq0 : i = 0
  · simp only [eq0, AddCommGrpCat.isZero_iff_subsingleton] at zero2 ⊢
    exact (Ext.precomp_mk₀_injective_of_epi N S.g (hg := hS.epi_g)).subsingleton
  · have hi1' : (i - 1 : ℕ) < moduleDepth S.X₁ N := by
      have : i - 1 + 1 = i := Nat.succ_pred_eq_of_ne_zero eq0
      rw [← this, Nat.cast_add, Nat.cast_one] at hi1
      exact lt_of_add_lt_add_right hi1
    have zero1 : IsZero (AddCommGrpCat.of (Ext S.X₁ N (i - 1))) :=
      @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi1')
    exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
      (Ext.contravariant_sequence_exact₃' hS N (i - 1) i (by omega))
      (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)

lemma moduleDepth_ge_min_of_shortExact_snd_snd
    (N : ModuleCat.{v} R) (S : ShortComplex (ModuleCat.{v} R))
    (hS : S.ShortExact) : moduleDepth N S.X₂ ≥ moduleDepth N S.X₁ ⊓ moduleDepth N S.X₃ := by
  apply le_sSup
  simp only [Set.mem_setOf_eq, lt_inf_iff, and_imp]
  intro i hi1 hi3
  have zero1 : IsZero (AddCommGrpCat.of (Ext N S.X₁ i)) :=
      @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi1)
  have zero3 : IsZero (AddCommGrpCat.of (Ext N S.X₃ i)) :=
      @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi3)
  exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    (Ext.covariant_sequence_exact₂' N hS i)
    (zero1.eq_zero_of_src _) (zero3.eq_zero_of_tgt _)

lemma moduleDepth_ge_min_of_shortExact_fst_snd
    (N : ModuleCat.{v} R) (S : ShortComplex (ModuleCat.{v} R))
    (hS : S.ShortExact) : moduleDepth N S.X₁ ≥ moduleDepth N S.X₂ ⊓ (moduleDepth N S.X₃ + 1) := by
  apply le_sSup
  simp only [Set.mem_setOf_eq, lt_inf_iff, and_imp]
  intro i hi2 hi3
  have zero2 : IsZero (AddCommGrpCat.of (Ext N S.X₂ i)) :=
    @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi2)
  by_cases eq0 : i = 0
  · simp only [eq0, AddCommGrpCat.isZero_iff_subsingleton] at zero2 ⊢
    exact (Ext.postcomp_mk₀_injective_of_mono N S.f (hf := hS.mono_f)).subsingleton
  · have hi3' : (i - 1 : ℕ) < moduleDepth N S.X₃ := by
      have : i - 1 + 1 = i := Nat.succ_pred_eq_of_ne_zero eq0
      rw [← this, Nat.cast_add, Nat.cast_one] at hi3
      exact lt_of_add_lt_add_right hi3
    have zero3 : IsZero (AddCommGrpCat.of (Ext N S.X₃ (i - 1))) :=
      @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi3')
    exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
      (Ext.covariant_sequence_exact₁' N hS (i - 1) i (by omega))
      (zero3.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)

lemma moduleDepth_ge_min_of_shortExact_trd_snd
    (N : ModuleCat.{v} R) (S : ShortComplex (ModuleCat.{v} R))
    (hS : S.ShortExact) : moduleDepth N S.X₃ ≥ moduleDepth N S.X₂ ⊓ (moduleDepth N S.X₁ - 1) := by
  apply le_sSup
  simp only [Set.mem_setOf_eq, lt_inf_iff, and_imp]
  intro i hi2 hi1
  have zero2 : IsZero (AddCommGrpCat.of (Ext N S.X₂ i)) :=
    @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi2)
  have hi1' : (i + 1 : ℕ) < moduleDepth N S.X₁ := by
    simpa using lt_tsub_iff_right.mp hi1
  have zero1 : IsZero (AddCommGrpCat.of (Ext N S.X₁ (i + 1))) :=
    @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi1')
  exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    (Ext.covariant_sequence_exact₃' N hS i (i + 1) rfl)
    (zero2.eq_zero_of_src _) (zero1.eq_zero_of_tgt _)

set_option backward.isDefEq.respectTransparency false in
lemma moduleDepth_eq_sSup_length_regular [IsNoetherianRing R] (I : Ideal R)
    (N M : ModuleCat.{v} R) [Module.Finite R M] [Nfin : Module.Finite R N]
    [Nntr : Nontrivial N] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I) :
    moduleDepth N M = sSup {(List.length rs : ℕ∞) | (rs : List R)
    (_ : RingTheory.Sequence.IsRegular M rs) (_ : ∀ r ∈ rs, r ∈ I) } := by
  rw [moduleDepth_eq_sup_nat]
  congr
  ext m
  simp only [exists_prop]
  refine ⟨fun ⟨lt_top, h⟩ ↦ ?_, fun ⟨rs, reg, mem, len⟩ ↦ ?_⟩
  · rcases ENat.ne_top_iff_exists.mp (ne_top_of_lt lt_top) with ⟨n, hn⟩
    simp only [← hn, Nat.cast_lt, Nat.cast_inj] at h ⊢
    have : ∃ N : ModuleCat.{v} R, Nontrivial N ∧ Module.Finite R N ∧
      Module.support R N = PrimeSpectrum.zeroLocus I ∧ ∀ i < n, Subsingleton (Ext N M i) := by
      use N
    rcases ((exists_isRegular_tfae I n M smul_lt).out 2 3).mp this with ⟨rs, len, mem, reg⟩
    use rs
  · simp only [← len, ENat.coe_lt_top, Nat.cast_lt, true_and]
    have rees := ((exists_isRegular_tfae I rs.length M smul_lt).out 3 0).mp (by use rs)
    exact rees N Nntr Nfin (le_of_eq hsupp)

lemma IsLocalRing.ideal_depth_eq_sSup_length_regular [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) (netop : I ≠ ⊤) (M : ModuleCat.{v} R) [Module.Finite R M]
    [Nontrivial M] : I.depth M = sSup {(List.length rs : ℕ∞) | (rs : List R)
    (_ : RingTheory.Sequence.IsRegular M rs) (_ : ∀ r ∈ rs, r ∈ I) } := by
  let _ := Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ I)).symm
  let _ : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr netop
  have smul_lt : I • (⊤ : Submodule R M) < ⊤ := lt_of_le_of_lt
      (Submodule.smul_mono (le_maximalIdeal netop) (le_refl _))
      (Ne.lt_top' (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (IsLocalRing.maximalIdeal_le_jacobson _)))
  apply moduleDepth_eq_sSup_length_regular I (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M smul_lt
  rw [(Shrink.linearEquiv R (R ⧸ I)).support_eq, Module.support_eq_zeroLocus,
    Ideal.annihilator_quotient]

lemma IsLocalRing.depth_eq_sSup_length_regular [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M] :
    IsLocalRing.depth M = sSup {(List.length rs : ℕ∞) | (rs : List R)
    (_ : RingTheory.Sequence.IsRegular M rs) (_ : ∀ r ∈ rs, r ∈ maximalIdeal R) } :=
  IsLocalRing.ideal_depth_eq_sSup_length_regular (maximalIdeal R) IsPrime.ne_top' M

lemma IsLocalRing.ideal_depth_le_depth [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) (netop : I ≠ ⊤) (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M] :
    I.depth M ≤ IsLocalRing.depth M := by
  rw [ideal_depth_eq_sSup_length_regular I netop, depth_eq_sSup_length_regular]
  apply sSup_le (fun n hn ↦ le_sSup ?_)
  rcases hn with ⟨rs, reg, mem, len⟩
  have : ∀ r ∈ rs, r ∈ maximalIdeal R := fun r a ↦ (le_maximalIdeal netop) (mem r a)
  use rs

omit [Small.{v, u} R] in
lemma Submodule.comap_lt_top_of_lt_range {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (p : Submodule R N)
    (lt : p < LinearMap.range f) : Submodule.comap f p < ⊤ := by
  obtain ⟨x, ⟨y, hy⟩, nmem⟩ : ∃ x ∈ LinearMap.range f, x ∉ p := Set.exists_of_ssubset lt
  have : y ∉ Submodule.comap f p := by simpa [hy] using nmem
  exact lt_of_le_not_ge (fun _ a ↦ trivial) fun a ↦ this (a trivial)

section

universe w

/-- Universe invariant of `moduleDepth`, would be repalced by a more general version when universe
invariant of `Ext` is provided. -/
lemma moduleDepth_eq_moduleDepth_shrink [IsNoetherianRing R] (I : Ideal R) [Small.{w, u} R]
    (N M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Nfin : Module.Finite R N] [Nntr : Nontrivial N]
    (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I) [Small.{w} M] [Small.{w} N] :
    moduleDepth (ModuleCat.of R N) (ModuleCat.of R M) =
    moduleDepth (ModuleCat.of R (Shrink.{w} N)) (ModuleCat.of R (Shrink.{w} M)) := by
  rw [moduleDepth_eq_sSup_length_regular I (ModuleCat.of R N) (ModuleCat.of R M) smul_lt hsupp]
  let _ : Module.Finite R (Shrink.{w} M) :=
    Module.Finite.equiv (Shrink.linearEquiv.{w} R M).symm
  let _ : Module.Finite R (Shrink.{w} N) :=
    Module.Finite.equiv (Shrink.linearEquiv.{w} R N).symm
  have smul_lt' : I • (⊤ : Submodule R (Shrink.{w} M)) < ⊤ := by
    apply lt_of_le_of_lt (Submodule.smul_top_le_comap_smul_top I
      (Shrink.linearEquiv.{w} R M).toLinearMap) (Submodule.comap_lt_top_of_lt_range _ _ _)
    simpa using smul_lt
  have hsupp' : Module.support R (Shrink.{w} N) = PrimeSpectrum.zeroLocus I := by
    rw [LinearEquiv.support_eq (Shrink.linearEquiv.{w} R N), hsupp]
  rw [moduleDepth_eq_sSup_length_regular I
    (ModuleCat.of R (Shrink.{w} N)) (ModuleCat.of R (Shrink.{w} M)) smul_lt' hsupp']
  have : RingTheory.Sequence.IsRegular M =
    RingTheory.Sequence.IsRegular (R := R) (Shrink.{w, v} M) := by
    ext rs
    exact LinearEquiv.isRegular_congr (Shrink.linearEquiv.{w} R M).symm rs
  congr!

lemma ring_depth_invariant [IsNoetherianRing R] (I : Ideal R) (lt_top : I < ⊤) :
    I.depth (ModuleCat.of R (Shrink.{v} R)) = I.depth (ModuleCat.of R R) := by
  simp only [Ideal.depth]
  let _ : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr lt_top.ne
  let _ : Nontrivial R := (Submodule.nontrivial_iff R).mp (nontrivial_of_lt I ⊤ lt_top)
  let e : (of R (Shrink.{u, u} (R ⧸ I))) ≅ (of R (R ⧸ I)) :=
    (Shrink.linearEquiv.{u, u} R (R ⧸ I)).toModuleIso
  rw [moduleDepth_eq_of_iso_fst _ e, eq_comm]
  have smul_lt : I • (⊤ : Submodule R R) < ⊤ := by simpa using lt_top
  apply moduleDepth_eq_moduleDepth_shrink I (R ⧸ I) R smul_lt
  simp [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]

omit [Small.{v, u} R] in
lemma ring_depth_uLift [IsNoetherianRing R] (I : Ideal R) (lt_top : I < ⊤) :
    I.depth (ModuleCat.of R (ULift.{w} R)) = I.depth (ModuleCat.of R R) := by
  let e : (of R (Shrink.{max u w} R)) ≅ (of R (ULift.{w} R)) :=
    ((Shrink.linearEquiv.{max u w} R R).trans ULift.moduleEquiv.symm).toModuleIso
  rw [← I.depth_eq_of_iso e]
  exact ring_depth_invariant.{max u w} I lt_top

end

lemma moduleDepth_quotSMulTop_succ_eq_moduleDepth (N M : ModuleCat.{v} R) (x : R)
    (reg : IsSMulRegular M x) (mem : x ∈ Module.annihilator R N) :
    moduleDepth N (ModuleCat.of R (QuotSMulTop x M)) + 1 = moduleDepth N M := by
  simp only [moduleDepth, add_comm]
  have iff (i : ℕ) : Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop x M)) i) ↔
    (Subsingleton (Ext N M i) ∧ Subsingleton (Ext N M (i + 1))) := by
    refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h1, h3⟩ ↦ ?_⟩
    · exact @Function.Injective.subsingleton _ _ _ ((AddCommGrpCat.mono_iff_injective _).mp <|
        (Ext.covariant_sequence_exact₂' N reg.smulShortComplex_shortExact i).mono_g
        (Ext.smul_id_postcomp_eq_zero_of_mem_annihilator mem i)) h
    · exact @Function.Surjective.subsingleton _ _ _ h ((AddCommGrpCat.epi_iff_surjective _).mp <|
        (Ext.covariant_sequence_exact₁' N reg.smulShortComplex_shortExact i (i + 1) rfl).epi_f
        (Ext.smul_id_postcomp_eq_zero_of_mem_annihilator mem (i + 1)))
    · exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
        (Ext.covariant_sequence_exact₃' N reg.smulShortComplex_shortExact i (i + 1) rfl)
        ((@AddCommGrpCat.isZero_of_subsingleton _ h1).eq_zero_of_src _)
        ((@AddCommGrpCat.isZero_of_subsingleton _ h3).eq_zero_of_tgt _)
  apply le_antisymm
  · rw [ENat.add_sSup ⟨0, by simp⟩]
    apply iSup_le (fun n ↦ iSup_le (fun hn ↦ ?_))
    apply le_sSup
    intro i hi
    by_cases eq0 : i = 0
    · rw [eq0, Ext.addEquiv₀.subsingleton_congr, ModuleCat.homAddEquiv.subsingleton_congr]
      exact linearMap_subsingleton_of_mem_annihilator reg mem
    · have eq : i - 1 + 1 = i := Nat.sub_one_add_one eq0
      have : i - 1 < n := by
        enat_to_nat
        omega
      have := ((iff (i - 1)).mp (hn (i - 1) this)).2
      simpa only [eq] using this
  · apply sSup_le (fun n hn ↦ ?_)
    by_cases eq0 : n = 0
    · simp [eq0]
    · have : n - 1 + 1 = n := by
        enat_to_nat
        omega
      rw [add_comm, ← this]
      apply add_le_add_left
      apply le_sSup
      intro i hi
      have lt2 : i + 1 < n := by
        enat_to_nat
        omega
      have lt1 : i < n := lt_of_le_of_lt (self_le_add_right _ _) lt2
      exact (iff i).mpr ⟨hn i lt1, hn (i + 1) lt2⟩

lemma Ideal.depth_quotSMulTop_succ_eq_moduleDepth (I : Ideal R) (M : ModuleCat.{v} R) (x : R)
    (reg : IsSMulRegular M x) (mem : x ∈ I) :
    I.depth (ModuleCat.of R (QuotSMulTop x M)) + 1 = I.depth M := by
  apply moduleDepth_quotSMulTop_succ_eq_moduleDepth _ M x reg
  simpa [LinearEquiv.annihilator_eq (Shrink.linearEquiv R (R ⧸ I)), Ideal.annihilator_quotient]

lemma IsLocalRing.depth_quotSMulTop_succ_eq_moduleDepth [IsLocalRing R] (M : ModuleCat.{v} R)
    (x : R) (reg : IsSMulRegular M x) (mem : x ∈ maximalIdeal R) :
    IsLocalRing.depth (ModuleCat.of R (QuotSMulTop x M)) + 1 = IsLocalRing.depth M :=
  (maximalIdeal R).depth_quotSMulTop_succ_eq_moduleDepth M x reg mem

lemma moduleDepth_quotient_regular_sequence_add_length_eq_moduleDepth (N M : ModuleCat.{v} R)
    (rs : List R) (reg : IsWeaklyRegular M rs) (h : ∀ r ∈ rs, r ∈ Module.annihilator R N) :
    moduleDepth N (ModuleCat.of R (M ⧸ (Ideal.ofList rs) • (⊤ : Submodule R M))) + rs.length =
    moduleDepth N M := by
  generalize len : rs.length = n
  induction n generalizing M rs
  · rw [List.length_eq_zero_iff.mp len, Ideal.ofList_nil, Submodule.bot_smul]
    simpa using moduleDepth_eq_of_iso_snd N (Submodule.quotEquivOfEqBot ⊥ rfl).toModuleIso
  · rename_i n hn
    match rs with
    | [] => simp at len
    | x :: rs' =>
      simp only [Nat.cast_add, Nat.cast_one]
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      have : IsSMulRegular M x := ((isWeaklyRegular_cons_iff M _ _).mp reg).1
      rw [moduleDepth_eq_of_iso_snd N
        (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs').toModuleIso,
        ← moduleDepth_quotSMulTop_succ_eq_moduleDepth N M x this (h x List.mem_cons_self),
        ← hn (ModuleCat.of R (QuotSMulTop x M)) rs' ((isWeaklyRegular_cons_iff M _ _).mp reg).2
        (fun r hr ↦ h r (List.mem_cons_of_mem x hr)) len, add_assoc]

lemma ideal_depth_quotient_regular_sequence_add_length_eq_ideal_depth (I : Ideal R)
    (M : ModuleCat.{v} R) (rs : List R) (reg : IsWeaklyRegular M rs)
    (h : ∀ r ∈ rs, r ∈ I) :
    I.depth (ModuleCat.of R (M ⧸ (Ideal.ofList rs) • (⊤ : Submodule R M))) + rs.length =
    I.depth M := by
  apply moduleDepth_quotient_regular_sequence_add_length_eq_moduleDepth _ M rs reg
  simpa [(Shrink.linearEquiv R (R ⧸ I)).annihilator_eq , Ideal.annihilator_quotient] using h

lemma depth_quotient_regular_sequence_add_length_eq_depth [IsLocalRing R]
    (M : ModuleCat.{v} R) (rs : List R)
    (reg : IsRegular M rs) :
    IsLocalRing.depth (ModuleCat.of R (M ⧸ (Ideal.ofList rs) • (⊤ : Submodule R M))) + rs.length =
    IsLocalRing.depth M := by
  apply ideal_depth_quotient_regular_sequence_add_length_eq_ideal_depth _ M rs reg.toIsWeaklyRegular
  intro r hr
  simp only [mem_maximalIdeal, mem_nonunits_iff]
  by_contra isu
  absurd reg.2
  simp [eq_top_of_isUnit_mem (ofList rs) (Ideal.subset_span hr) isu]

section ring

local instance (R : Type*) [CommRing R] (I : Ideal R) [IsNoetherianRing R] :
    IsNoetherianRing (R ⧸ I) :=
  isNoetherianRing_of_surjective R _ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

lemma IsLocalRing.depth_eq_of_ringEquiv {R R' : Type*} [CommRing R] [CommRing R']
    [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing R'] [IsNoetherianRing R'] (e : R ≃+* R') :
    IsLocalRing.depth (ModuleCat.of R R) = IsLocalRing.depth (ModuleCat.of R' R') := by
  let _ : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  let _ : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
  let e' : R ≃ₛₗ[e.toRingHom] R' := {
    __ := e
    map_smul' a b := by simp }
  simp only [depth_eq_sSup_length_regular]
  congr!
  rename_i n
  refine ⟨fun ⟨rs, reg, mem, len⟩ ↦ ?_, fun ⟨rs, reg, mem, len⟩ ↦ ?_⟩
  · use rs.map e.toRingHom, (e'.isRegular_congr' rs).mp reg
    simpa [len]
  · use rs.map e.symm.toRingHom, (e'.symm.isRegular_congr' rs).mp reg
    simpa [len]

lemma IsLocalRing.depth_eq_of_algebraMap_surjective [IsLocalRing R] [IsNoetherianRing R]
    {S : Type u} [CommRing S] [IsLocalRing S] [Algebra R S] [Small.{v} S] [IsNoetherianRing S]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module S M]
    [IsScalarTower R S M] [Nontrivial M] (surj : Function.Surjective (algebraMap R S)) :
    IsLocalRing.depth (ModuleCat.of R M) = IsLocalRing.depth (ModuleCat.of S M) := by
  have : Module.Finite S M := Module.Finite.of_restrictScalars_finite R S M
  have loc_hom : IsLocalHom (algebraMap R S) := surj.isLocalHom _
  simp only [depth_eq_sSup_length_regular]
  congr!
  rename_i n
  refine ⟨fun ⟨rs, reg, mem, len⟩ ↦ ?_, fun ⟨rs, reg, mem, len⟩ ↦ ?_⟩
  · have mem' : ∀ r ∈ rs.map (algebraMap R S), r ∈ maximalIdeal S := by
      intro r hr
      simp only [List.mem_map] at hr
      rcases hr with ⟨r', hr', eq⟩
      simpa [← eq] using mem r' hr'
    have reg' : IsRegular M (rs.map (algebraMap R S)) := by
      refine ⟨(isWeaklyRegular_map_algebraMap_iff S M rs).mpr reg.1, ?_⟩
      apply (ne_top_of_le_ne_top (Ne.symm _) (Submodule.smul_mono_left (span_le.mpr mem'))).symm
      apply Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      exact IsLocalRing.maximalIdeal_le_jacobson _
    use rs.map (algebraMap R S), reg', mem'
    simpa
  · rcases List.map_surjective_iff.mpr surj rs with ⟨rs', hrs'⟩
    have mem' : ∀ r ∈ rs', r ∈ maximalIdeal R := by
      intro r hr
      have : algebraMap R S r ∈ maximalIdeal S := by
        apply mem
        simp only [← hrs', List.mem_map]
        use r
      simpa using this
    have reg' : IsRegular M rs' := by
      refine ⟨(isWeaklyRegular_map_algebraMap_iff S M rs').mp (by simpa [hrs'] using reg.1), ?_⟩
      apply (ne_top_of_le_ne_top (Ne.symm _) (Submodule.smul_mono_left (span_le.mpr mem'))).symm
      apply Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      exact IsLocalRing.maximalIdeal_le_jacobson _
    use rs', reg', mem'
    simpa [← hrs'] using len

omit [Small.{v, u} R] in
lemma IsLocalRing.depth_quotient_regular_succ_eq_depth [IsLocalRing R] [IsNoetherianRing R] (x : R)
    (reg : IsSMulRegular R x) (mem : x ∈ maximalIdeal R) :
    letI : IsLocalRing (R ⧸ x • (⊤ : Ideal R)) :=
      have : Nontrivial (R ⧸ x • (⊤ : Ideal R)) :=
        Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
      have : IsLocalHom (Ideal.Quotient.mk (x • (⊤ : Ideal R))) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      IsLocalRing.of_surjective (Ideal.Quotient.mk (x • (⊤ : Ideal R))) Ideal.Quotient.mk_surjective
    IsLocalRing.depth (ModuleCat.of (R ⧸ x • (⊤ : Ideal R)) (R ⧸ x • (⊤ : Ideal R))) + 1 =
    IsLocalRing.depth (ModuleCat.of R R) := by
  have : Nontrivial (R ⧸ x • (⊤ : Ideal R)) :=
        Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
  have loc_hom : IsLocalHom (Ideal.Quotient.mk (x • (⊤ : Ideal R))) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have : IsLocalRing (R ⧸ x • (⊤ : Ideal R)) :=
    IsLocalRing.of_surjective (Ideal.Quotient.mk (x • (⊤ : Ideal R))) Ideal.Quotient.mk_surjective
  rw [← IsLocalRing.depth_quotSMulTop_succ_eq_moduleDepth (ModuleCat.of R R) x reg mem, eq_comm]
  congr 1
  apply depth_eq_of_algebraMap_surjective _
  simpa only [Quotient.algebraMap_eq] using Ideal.Quotient.mk_surjective

set_option backward.isDefEq.respectTransparency false in
omit [Small.{v, u} R] in
lemma IsLocalRing.depth_quotient_span_regular_succ_eq_depth [IsLocalRing R] [IsNoetherianRing R]
    (x : R) (reg : IsSMulRegular R x) (mem : x ∈ maximalIdeal R) :
    letI : IsLocalRing (R ⧸ Ideal.span {x}) :=
      have : Nontrivial (R ⧸ Ideal.span {x}) :=
        Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
      have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x})) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      IsLocalRing.of_surjective (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
    IsLocalRing.depth (ModuleCat.of (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x})) + 1 =
    IsLocalRing.depth (ModuleCat.of R R) := by
  let _ : IsLocalRing (R ⧸ Ideal.span {x}) :=
    have : Nontrivial (R ⧸ Ideal.span {x}) :=
      Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
    have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    IsLocalRing.of_surjective (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  letI : IsLocalRing (R ⧸ x • (⊤ : Ideal R)) :=
    have : Nontrivial (R ⧸ x • (⊤ : Ideal R)) :=
      Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
    have : IsLocalHom (Ideal.Quotient.mk (x • (⊤ : Ideal R))) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    IsLocalRing.of_surjective (Ideal.Quotient.mk (x • (⊤ : Ideal R))) Ideal.Quotient.mk_surjective
  have := Submodule.ideal_span_singleton_smul x (⊤ :Ideal R)
  simp only [smul_eq_mul, mul_top] at this
  rw [IsLocalRing.depth_eq_of_ringEquiv (Ideal.quotientEquivAlgOfEq R this).toRingEquiv,
    IsLocalRing.depth_quotient_regular_succ_eq_depth x reg mem]

set_option backward.isDefEq.respectTransparency false in
omit [Small.{v, u} R] in
lemma IsLocalRing.depth_quotient_regular_sequence_add_length_eq_depth [IsLocalRing R]
    [IsNoetherianRing R] (rs : List R) (reg : RingTheory.Sequence.IsWeaklyRegular R rs)
    (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    letI : IsLocalRing (R ⧸ Ideal.ofList rs) :=
      have : Nontrivial (R ⧸ Ideal.ofList rs) := Submodule.Quotient.nontrivial_iff.mpr
        (ne_top_of_le_ne_top IsPrime.ne_top' (span_le.mpr mem))
      have : IsLocalHom (Ideal.Quotient.mk (Ideal.ofList rs)) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      IsLocalRing.of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    IsLocalRing.depth (ModuleCat.of (R ⧸ Ideal.ofList rs)
      (R ⧸ Ideal.ofList rs)) + rs.length =
    IsLocalRing.depth (ModuleCat.of R R) := by
  generalize len : rs.length = n
  induction n generalizing R rs
  · let e : R ⧸ ofList rs ≃+* R :=
      (RingEquiv.ofBijective _ ((Ideal.Quotient.mk_bijective_iff_eq_bot (Ideal.ofList rs)).mpr
        (by simp [List.length_eq_zero_iff.mp len]))).symm
    have : IsLocalRing (R ⧸ ofList rs) := RingEquiv.isLocalRing e.symm
    have : IsNoetherianRing (R ⧸ ofList rs) := isNoetherianRing_of_ringEquiv R e.symm
    simpa using IsLocalRing.depth_eq_of_ringEquiv e
  · rename_i n hn _ _ _
    match rs with
    | [] => simp at len
    | x :: rs' =>
      let _ : IsLocalRing (R ⧸ Ideal.ofList (x :: rs')) :=
        have : Nontrivial (R ⧸ Ideal.ofList (x :: rs')) :=
          Submodule.Quotient.nontrivial_iff.mpr
          (ne_top_of_le_ne_top IsPrime.ne_top' (span_le.mpr mem))
        have : IsLocalHom (Ideal.Quotient.mk (Ideal.ofList (x :: rs'))) :=
          IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
        IsLocalRing.of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      simp only [List.mem_cons, forall_eq_or_imp] at mem
      simp only [Nat.cast_add, Nat.cast_one, ← add_assoc,
       ← depth_quotient_regular_succ_eq_depth x ((isWeaklyRegular_cons_iff _ x rs').mp reg).1 mem.1]
      have : Nontrivial (R ⧸ x • (⊤ : Ideal R)) :=
        Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul] using mem.1)
      have loc_hom : IsLocalHom (Ideal.Quotient.mk (x • (⊤ : Ideal R))) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      have : IsLocalRing (R ⧸ x • (⊤ : Ideal R)) :=
        IsLocalRing.of_surjective (Ideal.Quotient.mk (x • (⊤ : Ideal R)))
          Ideal.Quotient.mk_surjective
      have mem' : ∀ r ∈ List.map (Ideal.Quotient.mk (x • (⊤ : Ideal R))) rs',
        r ∈ maximalIdeal (R ⧸ x • (⊤ : Ideal R)) := by
        intro r hr
        rcases List.mem_map.mp hr with ⟨r', hr', eq⟩
        simpa [← eq] using mem.2 r' hr'
      simp only [← hn (rs'.map (Ideal.Quotient.mk (x • (⊤ : Ideal R))))
        ((isWeaklyRegular_map_algebraMap_iff (R ⧸ x • (⊤ : Ideal R)) _ rs').mpr
        ((isWeaklyRegular_cons_iff _ x rs').mp reg).2) mem' (by simpa using len)]
      congr 2
      have eq1 : x • (⊤ : Ideal R) = span {x} := by simp [← Submodule.ideal_span_singleton_smul]
      have eq2 : ofList (rs'.map (Ideal.Quotient.mk (span {x}))) =
        (ofList rs').map (Ideal.Quotient.mk (span {x})) := by simp
      let e : R ⧸ ofList (x :: rs') ≃+* ((R ⧸ x • (⊤ : Ideal R)) ⧸
        ofList (rs'.map (Ideal.Quotient.mk (x • (⊤ : Ideal R))))) := by
        rw [Ideal.ofList_cons, eq1, eq2]
        exact (DoubleQuot.quotQuotEquivQuotSup _ _).symm
      let _ := RingEquiv.isLocalRing e
      exact IsLocalRing.depth_eq_of_ringEquiv e

end ring

end depth
