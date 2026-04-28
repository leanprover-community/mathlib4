/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yi Song
-/
module

public import Mathlib.RingTheory.Depth.Rees

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
  · have : Nonempty {n : ℕ∞ | ∀ (i : ℕ), i < n → Subsingleton (Ext N M i)} := ⟨⟨(0 : ℕ∞), by simp⟩⟩
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
  induction n with
  | top => simp
  | coe n => simpa using this n

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
    AddCommGrpCat.isZero_iff_subsingleton'.mpr (ext_subsingleton_of_lt_moduleDepth hi1)
  have zero3 : IsZero (AddCommGrpCat.of (Ext S.X₃ N i)) :=
    AddCommGrpCat.isZero_iff_subsingleton'.mpr (ext_subsingleton_of_lt_moduleDepth hi3)
  exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    (Ext.contravariant_sequence_exact₂' hS N i)
    (zero3.eq_zero_of_src _) (zero1.eq_zero_of_tgt _)

lemma moduleDepth_ge_min_of_shortExact_fst_fst
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    (N : ModuleCat.{v} R) : moduleDepth S.X₁ N ≥ moduleDepth S.X₂ N ⊓ (moduleDepth S.X₃ N - 1) := by
  apply le_sSup
  simp only [Set.mem_setOf_eq, lt_inf_iff, and_imp]
  intro i hi2 hi3
  have hi3' : (i + 1 : ℕ) < moduleDepth S.X₃ N := by simpa using lt_tsub_iff_right.mp hi3
  have zero2 : IsZero (AddCommGrpCat.of (Ext S.X₂ N i)) :=
    AddCommGrpCat.isZero_iff_subsingleton'.mpr (ext_subsingleton_of_lt_moduleDepth hi2)
  have zero3 : IsZero (AddCommGrpCat.of (Ext S.X₃ N (i + 1))) :=
    AddCommGrpCat.isZero_iff_subsingleton'.mpr (ext_subsingleton_of_lt_moduleDepth hi3')
  exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    (Ext.contravariant_sequence_exact₁' hS N i (i + 1) (add_comm _ _))
    (zero2.eq_zero_of_src _) (zero3.eq_zero_of_tgt _)

lemma moduleDepth_ge_min_of_shortExact_trd_fst
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    (N : ModuleCat.{v} R) : moduleDepth S.X₃ N ≥ moduleDepth S.X₂ N ⊓ (moduleDepth S.X₁ N + 1) := by
  apply le_sSup
  simp only [Set.mem_setOf_eq, lt_inf_iff, and_imp]
  intro i hi2 hi1
  have zero2 := AddCommGrpCat.isZero_iff_subsingleton'.mpr (ext_subsingleton_of_lt_moduleDepth hi2)
  match i with
  | 0 =>
    simp only [AddCommGrpCat.isZero_iff_subsingleton] at zero2 ⊢
    exact (Ext.precomp_mk₀_injective_of_epi N S.g (hg := hS.epi_g)).subsingleton
  | i + 1 =>
    have hi1' : i < moduleDepth S.X₁ N := by simpa using hi1
    have zero1 : IsZero (AddCommGrpCat.of (Ext S.X₁ N i)) :=
      AddCommGrpCat.isZero_iff_subsingleton'.mpr (ext_subsingleton_of_lt_moduleDepth hi1')
    exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
      (Ext.contravariant_sequence_exact₃' hS N i (i + 1) (by omega))
      (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)

lemma moduleDepth_ge_min_of_shortExact_snd_snd
    (N : ModuleCat.{v} R) (S : ShortComplex (ModuleCat.{v} R))
    (hS : S.ShortExact) : moduleDepth N S.X₂ ≥ moduleDepth N S.X₁ ⊓ moduleDepth N S.X₃ := by
  apply le_sSup
  simp only [Set.mem_setOf_eq, lt_inf_iff, and_imp]
  intro i hi1 hi3
  have zero1 : IsZero (AddCommGrpCat.of (Ext N S.X₁ i)) :=
    AddCommGrpCat.isZero_iff_subsingleton'.mpr (ext_subsingleton_of_lt_moduleDepth hi1)
  have zero3 : IsZero (AddCommGrpCat.of (Ext N S.X₃ i)) :=
    AddCommGrpCat.isZero_iff_subsingleton'.mpr (ext_subsingleton_of_lt_moduleDepth hi3)
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
    AddCommGrpCat.isZero_iff_subsingleton'.mpr (ext_subsingleton_of_lt_moduleDepth hi2)
  match i with
  | 0 =>
    simp only [AddCommGrpCat.isZero_iff_subsingleton] at zero2 ⊢
    exact (Ext.postcomp_mk₀_injective_of_mono N S.f (hf := hS.mono_f)).subsingleton
  | i + 1 =>
    have hi3' : i < moduleDepth N S.X₃ := by simpa using hi3
    have zero3 : IsZero (AddCommGrpCat.of (Ext N S.X₃ i)) :=
      AddCommGrpCat.isZero_iff_subsingleton'.mpr (ext_subsingleton_of_lt_moduleDepth hi3')
    exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
      (Ext.covariant_sequence_exact₁' N hS i (i + 1) (by omega))
      (zero3.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)

lemma moduleDepth_ge_min_of_shortExact_trd_snd
    (N : ModuleCat.{v} R) (S : ShortComplex (ModuleCat.{v} R))
    (hS : S.ShortExact) : moduleDepth N S.X₃ ≥ moduleDepth N S.X₂ ⊓ (moduleDepth N S.X₁ - 1) := by
  apply le_sSup
  simp only [Set.mem_setOf_eq, lt_inf_iff, and_imp]
  intro i hi2 hi1
  have hi1' : (i + 1 : ℕ) < moduleDepth N S.X₁ := by simpa using lt_tsub_iff_right.mp hi1
  have zero2 : IsZero (AddCommGrpCat.of (Ext N S.X₂ i)) :=
    AddCommGrpCat.isZero_iff_subsingleton'.mpr (ext_subsingleton_of_lt_moduleDepth hi2)
  have zero1 : IsZero (AddCommGrpCat.of (Ext N S.X₁ (i + 1))) :=
    AddCommGrpCat.isZero_iff_subsingleton'.mpr (ext_subsingleton_of_lt_moduleDepth hi1')
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
  · rcases ENat.ne_top_iff_exists.mp lt_top.ne with ⟨n, hn⟩
    simp only [← hn, Nat.cast_lt, Nat.cast_inj] at h ⊢
    rcases ((exists_isRegular_tfae I n M smul_lt).out 2 3).mp (by use N) with ⟨rs, len, mem, reg⟩
    use rs
  · simp only [← len, ENat.coe_lt_top, Nat.cast_lt, true_and]
    have rees := ((exists_isRegular_tfae I rs.length M smul_lt).out 3 0).mp (by use rs)
    exact rees N Nntr Nfin (le_of_eq hsupp)

lemma IsLocalRing.ideal_depth_eq_sSup_length_regular [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) (netop : I ≠ ⊤) (M : ModuleCat.{v} R) [Module.Finite R M]
    [Nontrivial M] : I.depth M = sSup {(List.length rs : ℕ∞) | (rs : List R)
      (_ : RingTheory.Sequence.IsRegular M rs) (_ : ∀ r ∈ rs, r ∈ I) } := by
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr netop
  have smul_lt : I • (⊤ : Submodule R M) < ⊤ := lt_of_le_of_lt
    (Submodule.smul_mono (le_maximalIdeal netop) (le_refl _))
      (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (IsLocalRing.maximalIdeal_le_jacobson _)).lt_top'
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

variable [IsNoetherianRing R] [Small.{w, u} R] {N M : Type v} {N' M' : Type w}
  [AddCommGroup M] [Module R M] [Module.Finite R M]
  [AddCommGroup N] [Module R N] [Module.Finite R N]
  [AddCommGroup M'] [Module R M'] [Module.Finite R M']
  [AddCommGroup N'] [Module R N'] [Module.Finite R N']

lemma moduleDepth_eq_of_linearEquiv [Nontrivial N] (eM : M ≃ₗ[R] M') (eN : N ≃ₗ[R] N')
    (I : Ideal R) (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I) :
    moduleDepth (ModuleCat.of R N) (ModuleCat.of R M) =
    moduleDepth (ModuleCat.of R N') (ModuleCat.of R M') := by
  have : Nontrivial N' := eN.injective.nontrivial
  rw [moduleDepth_eq_sSup_length_regular I (ModuleCat.of R N) (ModuleCat.of R M) smul_lt hsupp]
  have smul_lt' : I • (⊤ : Submodule R M') < ⊤ := by
    apply lt_of_le_of_lt (Submodule.smul_top_le_comap_smul_top I eM.symm.toLinearMap)
      (Submodule.comap_lt_top_of_lt_range _ _ _)
    simpa using smul_lt
  have hsupp' : Module.support R N' = PrimeSpectrum.zeroLocus I := by rw [← eN.support_eq, hsupp]
  rw [moduleDepth_eq_sSup_length_regular I (ModuleCat.of R N') (ModuleCat.of R M') smul_lt' hsupp']
  congr!
  ext rs
  exact eM.isRegular_congr rs

lemma Ideal.depth_eq_of_linearEquiv (eM : M ≃ₗ[R] M')
    (I : Ideal R) (smul_lt : I • (⊤ : Submodule R M) < ⊤) :
    I.depth (ModuleCat.of R M) = I.depth (ModuleCat.of R M') := by
  simp only [Ideal.depth]
  have : Nontrivial (R ⧸ I) := by
    apply Submodule.Quotient.nontrivial_iff.mpr
    by_contra eq
    simp [eq] at smul_lt
  let e : (Shrink.{v} (R ⧸ I)) ≃ₗ[R] (Shrink.{w} (R ⧸ I)) :=
    ((Shrink.linearEquiv R _).trans (Shrink.linearEquiv R _).symm)
  apply moduleDepth_eq_of_linearEquiv eM e I smul_lt
  rw [(Shrink.linearEquiv R _).support_eq, Module.support_eq_zeroLocus, annihilator_quotient]

lemma IsLocalRing.depth_eq_of_linearEquiv [IsLocalRing R] [Nontrivial M] (eM : M ≃ₗ[R] M') :
    IsLocalRing.depth (ModuleCat.of R M) = IsLocalRing.depth (ModuleCat.of R M') :=
  Ideal.depth_eq_of_linearEquiv eM _ (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    (IsLocalRing.maximalIdeal_le_jacobson _)).lt_top'

omit [Small.{w, u} R] in
lemma ring_depth_shrink_eq (I : Ideal R) (lt_top : I < ⊤) :
    I.depth (ModuleCat.of R (Shrink.{v} R)) = I.depth (ModuleCat.of R R) := by
  apply (Ideal.depth_eq_of_linearEquiv (Shrink.linearEquiv.{v} R R).symm I _).symm
  simpa using lt_top

end

end depth
