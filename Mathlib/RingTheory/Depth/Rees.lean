/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yi Song
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Regular.Category
public import Mathlib.RingTheory.Regular.LinearMap
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!

# The Rees theorem

In this file we prove the Rees theorem for depth, which relates the vanishing of
certain `Ext` groups and the length of a maximal regular sequence in a certain ideal.

## Main results

* `exists_isRegular_tfae` (Rees theorem) : For any `n : ℕ`, noetherian ring `R`, `I : Ideal R`, and
  finitely generated and nontrivial `R`-module `M` satisfying `IM < M`,
  the following are equivalent:
  · for any `N : ModuleCat R` finitely generated and nontrivial with support contained in the
    zero locus of `I`, `∀ i < n, Ext N M i = 0`
  · `∀ i < n, Ext (A⧸I) M i = 0`
  · there exists a `N : ModuleCat R` finitely generated and nontrivial with support equal to the
    zero locus of `I`, `∀ i < n, Ext N M i = 0`
  · there exists a `M`-regular sequence of length `n` with every element in `I`

-/

@[expose] public section

open IsLocalRing LinearMap Module

universe v u

open RingTheory.Sequence Ideal CategoryTheory Abelian Limits

variable {R : Type u} [CommRing R] [Small.{v} R]

namespace CategoryTheory.Abelian

set_option backward.isDefEq.respectTransparency false in
lemma Ext.smul_id_postcomp_eq_zero_of_mem_ann {M N : ModuleCat.{v} R}
    {r : R} (mem_ann : r ∈ Module.annihilator R N) (n : ℕ) :
    AddCommGrpCat.ofHom ((Ext.mk₀ (r • (𝟙 M))).postcomp N (add_zero n)) = 0 := by
  ext h
  have : r • (𝟙 N) = 0 := ModuleCat.hom_ext (LinearMap.ext (Module.mem_annihilator.mp mem_ann ·))
  have smul_eq : r • h = (Ext.mk₀ (r • (𝟙 N))).comp h (zero_add n) := by simp [Ext.mk₀_smul]
  simp [Ext.mk₀_smul, this, smul_eq]

end CategoryTheory.Abelian

open Pointwise ModuleCat IsSMulRegular

lemma ModuleCat.exists_isRegular_of_exists_subsingleton_ext [IsNoetherianRing R] (I : Ideal R)
    (n : ℕ) (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (exists_N : ∃ N : ModuleCat.{v} R, Nontrivial N ∧ Module.Finite R N ∧
      Module.support R N = PrimeSpectrum.zeroLocus I ∧ ∀ i < n, Subsingleton (Ext N M i)) :
    ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ IsRegular M rs := by
  induction n generalizing M with
  | zero =>
    let : Nontrivial M := (Submodule.nontrivial_iff R).mp (nontrivial_of_lt _ _ smul_lt)
    use []
    simp [isRegular_iff]
  | succ n ih =>
    rcases exists_N with ⟨N, ntr, fin, h_supp, h_ext⟩
    have h_supp' := h_supp
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_eq_iff] at h_supp'
    -- use `Ext N M 0` vanish to obtain an `M`-regular element `x` in `Ann(N)`
    have : Subsingleton (N ⟶ M) := Ext.addEquiv₀.subsingleton_congr.mp (h_ext 0 n.zero_lt_succ)
    have : Subsingleton (N →ₗ[R] M) := ModuleCat.homAddEquiv.symm.subsingleton
    rcases subsingleton_linearMap_iff.mp this with ⟨x, mem_ann, hx⟩
    -- take a power of it to make `xᵏ` fall into `I`
    rcases le_of_le_of_eq Ideal.le_radical h_supp' mem_ann with ⟨k, hk⟩
    -- prepare to apply induction hypotesis to `M ⧸ xᵏM`
    have ne : I • (⊤ : Submodule R (QuotSMulTop (x ^ k) M)) ≠ ⊤ := by
      by_contra eq
      absurd congrArg (Submodule.comap (Submodule.mkQ _)) eq
      simpa [Submodule.comap_smul_top_of_surjective I _ (Submodule.mkQ_surjective _),
        Submodule.smul_mono_left ((span_singleton_le_iff_mem I).mpr hk),
        ← Submodule.ideal_span_singleton_smul] using smul_lt.ne
    -- verify that `N` indeed make `M ⧸ xᵏM` satisfy the induction hypothesis
    have exists_N' : (∃ N : ModuleCat R, Nontrivial N ∧ Module.Finite R N ∧
        Module.support R N = PrimeSpectrum.zeroLocus I ∧
          ∀ i < n, Subsingleton (Abelian.Ext N (ModuleCat.of R (QuotSMulTop (x ^ k) M)) i)) := by
      use N
      simp only [ntr, fin, h_supp, true_and]
      intro i hi
      -- the vanishing of `Ext` is obtained from the (covariant) long exact sequence given by
      -- `M.smulShortComplex (x ^ k)`
      have zero1 : IsZero (AddCommGrpCat.of (Ext N M i)) :=
        @AddCommGrpCat.isZero_of_subsingleton _ (h_ext i (Nat.lt_add_right 1 hi))
      have zero2 : IsZero (AddCommGrpCat.of (Ext N M (i + 1))) :=
        @AddCommGrpCat.isZero_of_subsingleton _ (h_ext (i + 1) (Nat.add_lt_add_right hi 1))
      exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
        ((Ext.covariant_sequence_exact₃' N (hx.pow k).smulShortComplex_shortExact) i (i + 1) rfl)
        (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)
    rcases ih (ModuleCat.of R (QuotSMulTop (x ^ k) M)) ne.lt_top exists_N' with ⟨rs, len, mem, reg⟩
    use x ^ k :: rs
    simpa [len, hk] using ⟨mem, hx.pow k, reg⟩

set_option backward.isDefEq.respectTransparency false in
lemma CategoryTheory.Abelian.Ext.pow_mono_of_mono (a : R) (k : ℕ) (i : ℕ) {M N : ModuleCat.{v} R}
    (f_mono : Mono (AddCommGrpCat.ofHom ((Ext.mk₀ (smulShortComplex M a).f).postcomp
    N (add_zero i)))) : Mono (AddCommGrpCat.ofHom ((Ext.mk₀ (smulShortComplex M (a ^ k)).f).postcomp
    N (add_zero i))) := by
  have (x : R) : Mono (AddCommGrpCat.ofHom ((Ext.mk₀ (smulShortComplex M x).f).postcomp
    N (add_zero i))) ↔ IsSMulRegular (Ext N M i) x := by
    simp only [IsSMulRegular, AddCommGrpCat.mono_iff_injective]
    congr!
    ext
    rw [smulShortComplex_f_eq_smul_id]
    simp [smulShortComplex, Ext.mk₀_smul]
  rw [this] at f_mono ⊢
  exact f_mono.pow k

lemma ModuleCat.subsingleton_ext_of_exists_isRegular [IsNoetherianRing R] (I : Ideal R) (n : ℕ)
    (N : ModuleCat.{v} R) [Nfin : Module.Finite R N]
    (Nsupp : Module.support R N ⊆ PrimeSpectrum.zeroLocus I)
    (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (rs : List R) (len : rs.length = n) (mem : ∀ r ∈ rs, r ∈ I) (reg : IsRegular M rs) :
    ∀ i < n, Subsingleton (Ext N M i) := by
  induction n generalizing M rs with
  | zero => simp
  | succ n ih =>
    rintro i hi
    have le_rad := Nsupp
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at le_rad
    match rs with
    | [] => simp at len
    | a :: rs' =>
      -- find a positive power of `a` lying in `Ann(N)`
      rcases le_rad (mem a List.mem_cons_self) with ⟨k, hk⟩
      simp only [isRegular_cons_iff] at reg
      simp only [List.mem_cons, forall_eq_or_imp] at mem
      simp only [List.length_cons, Nat.add_left_inj] at len
      -- prepare to apply induction hypothesis to `M/aM`
      have ne : I • (⊤ : Submodule R (QuotSMulTop a M)) ≠ ⊤ := by
        by_contra eq
        absurd congrArg (Submodule.comap (Submodule.mkQ _)) eq
        simpa [Submodule.comap_smul_top_of_surjective I _ (Submodule.mkQ_surjective _),
          Submodule.smul_mono_left ((span_singleton_le_iff_mem I).mpr mem.1),
          ← Submodule.ideal_span_singleton_smul] using smul_lt.ne
      match i with
      | 0 => -- vanishing of `Ext N M 0` follows from `aᵏ ∈ Ann(N)`
        have : Subsingleton (N →ₗ[R] M) := subsingleton_linearMap_iff.mpr ⟨a ^ k, hk, reg.1.pow k⟩
        exact (Ext.addEquiv₀.trans ModuleCat.homAddEquiv).subsingleton
      | i + 1 =>
        let g := (AddCommGrpCat.ofHom ((Ext.mk₀ (smulShortComplex M a).f).postcomp N
          (add_zero (i + 1))))
        -- from the (covariant) long exact sequence given by `M.smulShortComplex a`
        -- we obtain scalar multiple by `a` on `Ext N M i` is injective
        have mono_g : Mono g := by
          apply (Ext.covariant_sequence_exact₁' N reg.1.smulShortComplex_shortExact i (i + 1)
            rfl).mono_g ((@AddCommGrpCat.isZero_of_subsingleton _ ?_).eq_zero_of_src _)
          exact ih (ModuleCat.of R (QuotSMulTop a M)) ne.lt_top rs' len mem.2 reg.2 i (by omega)
        let gk := AddCommGrpCat.ofHom ((Ext.mk₀ (M.smulShortComplex (a ^ k)).f).postcomp N
          (add_zero (i + 1)))
        have mono_gk := Ext.pow_mono_of_mono a k (i + 1) mono_g
        -- scalar multiple by `aᵏ` on `Ext N M i` is zero since `aᵏ ∈ Ann(N)`, so `Ext N M i` vanish
        have zero_gk : gk = 0 := Ext.smul_id_postcomp_eq_zero_of_mem_ann hk (i + 1)
        exact AddCommGrpCat.subsingleton_of_isZero (IsZero.of_mono_eq_zero _ zero_gk)

/--
**The Rees theorem**
For any `n : ℕ`, Noetherian ring `R`, `I : Ideal R`, and finitely generated and nontrivial
`R`-module `M` satisfying `IM < M`, the following are equivalent:
· for any `N : ModuleCat R` finitely generated and nontrivial with support contained in the
  zero locus of `I`, `∀ i < n, Ext N M i = 0`
· `∀ i < n, Ext (A⧸I) M i = 0`
· there exists a `N : ModuleCat R` finitely generated and nontrivial with support equal to the
  zero locus of `I`, `∀ i < n, Ext N M i = 0`
· there exists a `M`-regular sequence of length `n` with every element in `I`
-/
lemma ModuleCat.exists_isRegular_tfae [IsNoetherianRing R] (I : Ideal R) (n : ℕ)
    (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤) :
    [∀ N : ModuleCat.{v} R, Nontrivial N → Module.Finite R N →
      Module.support R N ⊆ PrimeSpectrum.zeroLocus I → ∀ i < n, Subsingleton (Ext N M i),
      ∀ i < n, Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M i),
      ∃ N : ModuleCat R, Nontrivial N ∧ Module.Finite R N ∧
      Module.support R N = PrimeSpectrum.zeroLocus I ∧ ∀ i < n, Subsingleton (Ext N M i),
      ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs
      ].TFAE := by
  -- two main implications `3 → 4` and `4 → 1` are separated out, the rest are trivial
  have ntrQ : Nontrivial (R ⧸ I) := by
    apply Submodule.Quotient.nontrivial_iff.mpr
    by_contra eq
    simp [eq] at smul_lt
  have suppQ : Module.support R (Shrink.{v} (R ⧸ I)) = PrimeSpectrum.zeroLocus I := by
    rw [(Shrink.linearEquiv R _).support_eq, Module.support_eq_zeroLocus, annihilator_quotient]
  tfae_have 1 → 2 := fun h1 i hi ↦ h1 (ModuleCat.of R (Shrink.{v} (R ⧸ I)))
    inferInstance inferInstance suppQ.subset i hi
  tfae_have 2 → 3 := fun h2 ↦ ⟨(ModuleCat.of R (Shrink.{v} (R ⧸ I))),
    inferInstance, Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ I)).symm, suppQ, h2⟩
  tfae_have 3 → 4 := exists_isRegular_of_exists_subsingleton_ext I n M smul_lt
  tfae_have 4 → 1 := fun ⟨rs, len, mem, reg⟩ N Nntr Nfin Nsupp i hi ↦
    subsingleton_ext_of_exists_isRegular I n N Nsupp M smul_lt rs len mem reg i hi
  tfae_finish

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

end depth
