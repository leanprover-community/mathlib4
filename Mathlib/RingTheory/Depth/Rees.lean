/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yi Song
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.RingTheory.Regular.Category
public import Mathlib.RingTheory.Regular.LinearMap
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!

# The Rees theorem

In this file we prove the Rees theorem for depth, which relates the vanishing of
certain `Ext` groups and the length of a maximal regular sequence in a certain ideal.

## Main results

* `ModuleCat.exists_isRegular_tfae` (Rees theorem) : For any `n : ℕ`, noetherian ring `R`,
  `I : Ideal R`, and finitely generated and nontrivial `R`-module `M` satisfying `IM < M`,
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

open Pointwise ModuleCat IsSMulRegular

lemma ModuleCat.exists_isRegular_of_exists_subsingleton_ext [IsNoetherianRing R] (I : Ideal R)
    (n : ℕ) (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (N : ModuleCat.{v} R) [Nontrivial N] [Module.Finite R N]
    (h_supp : Module.support R N = PrimeSpectrum.zeroLocus I)
    (h_ext : ∀ i < n, Subsingleton (Ext N M i)) :
    ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ IsRegular M rs := by
  induction n generalizing M with
  | zero =>
    have : Nontrivial M := (Submodule.nontrivial_iff R).mp (nontrivial_of_lt _ _ smul_lt)
    use []
    simp [isRegular_iff]
  | succ n ih =>
    have h_supp' := h_supp
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_eq_iff] at h_supp'
    -- use `Ext N M 0` vanish to obtain an `M`-regular element `x` in `Ann(N)`
    have : Subsingleton (N ⟶ M) := Ext.addEquiv₀.subsingleton_congr.mp (h_ext 0 n.zero_lt_succ)
    have : Subsingleton (N →ₗ[R] M) := ModuleCat.homAddEquiv.symm.subsingleton
    rcases subsingleton_linearMap_iff.mp this with ⟨x, mem_ann, hx⟩
    -- take a power of it to make `xᵏ` fall into `I`
    rcases le_of_le_of_eq Ideal.le_radical h_supp' mem_ann with ⟨k, hk⟩
    -- prepare to apply induction hypothesis to `M ⧸ xᵏM`
    have ne : I • (⊤ : Submodule R (QuotSMulTop (x ^ k) M)) ≠ ⊤ := by
      by_contra eq
      absurd congrArg (Submodule.comap (Submodule.mkQ _)) eq
      simpa [Submodule.comap_smul_top_of_surjective I _ (Submodule.mkQ_surjective _),
        Submodule.smul_mono_left ((span_singleton_le_iff_mem I).mpr hk),
        ← Submodule.ideal_span_singleton_smul] using smul_lt.ne
    -- verify that `N` indeed make `M ⧸ xᵏM` satisfy the induction hypothesis
    have h_ext' : ∀ i < n, Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop (x ^ k) M)) i) := by
      intro i hi
      -- the vanishing of `Ext` is obtained from the (covariant) long exact sequence given by
      -- `M.smulShortComplex (x ^ k)`
      have := h_ext i (Nat.lt_add_right 1 hi)
      have zero1 : IsZero (AddCommGrpCat.of (Ext N M i)) :=
        AddCommGrpCat.isZero_of_subsingleton _
      have := (h_ext (i + 1) (Nat.add_lt_add_right hi 1))
      --add iszero for `AddCommGrpCat.of`
      have zero2 : IsZero (AddCommGrpCat.of (Ext N M (i + 1))) :=
        AddCommGrpCat.isZero_of_subsingleton _
      exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
        ((Ext.covariant_sequence_exact₃' N (hx.pow k).smulShortComplex_shortExact) i (i + 1) rfl)
        (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)
    rcases ih (ModuleCat.of R (QuotSMulTop (x ^ k) M)) ne.lt_top h_ext' with ⟨rs, len, mem, reg⟩
    use x ^ k :: rs
    simpa [len, hk] using ⟨mem, hx.pow k, reg⟩

lemma ModuleCat.subsingleton_ext_of_exists_isRegular [IsNoetherianRing R] (I : Ideal R)
    (N : ModuleCat.{v} R) [Nfin : Module.Finite R N]
    (Nsupp : Module.support R N ⊆ PrimeSpectrum.zeroLocus I)
    (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (rs : List R) (mem : ∀ r ∈ rs, r ∈ I) (reg : IsRegular M rs) :
    ∀ i < rs.length, Subsingleton (Ext N M i) := by
  generalize len : rs.length = n
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
          exact ih (ModuleCat.of R (QuotSMulTop a M)) ne.lt_top rs' mem.2 reg.2 len i (by omega)
        let gk := AddCommGrpCat.ofHom ((Ext.mk₀ (M.smulShortComplex (a ^ k)).f).postcomp N
          (add_zero (i + 1)))
        have mono_gk : Mono gk := by
          simp only [smulShortComplex_f_eq_smul_id, g, gk] at mono_g ⊢
          exact (Ext.smul_id_postcomp_mono_iff (a ^ k) (i + 1)).mpr <|
            ((Ext.smul_id_postcomp_mono_iff a (i + 1)).mp mono_g).pow k
        -- scalar multiple by `aᵏ` on `Ext N M i` is zero since `aᵏ ∈ Ann(N)`, so `Ext N M i` vanish
        have zero_gk : gk = 0 := Ext.smul_id_postcomp_eq_zero_of_mem_annihilator hk (i + 1)
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
  tfae_have 3 → 4 := fun ⟨N, _, _, h_supp, h_ext⟩ ↦
    exists_isRegular_of_exists_subsingleton_ext I n M smul_lt N h_supp h_ext
  tfae_have 4 → 1 := fun ⟨rs, len, mem, reg⟩ N Nntr Nfin Nsupp i hi ↦
    subsingleton_ext_of_exists_isRegular I N Nsupp M smul_lt rs mem reg i (hi.trans_eq len.symm)
  tfae_finish
