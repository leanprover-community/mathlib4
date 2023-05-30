/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module ring_theory.filtration
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Ideal.LocalRing
import Mathbin.RingTheory.Noetherian
import Mathbin.RingTheory.ReesAlgebra
import Mathbin.RingTheory.Finiteness
import Mathbin.Data.Polynomial.Module
import Mathbin.Order.Hom.Lattice

/-!

# `I`-filtrations of modules

This file contains the definitions and basic results around (stable) `I`-filtrations of modules.

## Main results

- `ideal.filtration`: An `I`-filtration on the module `M` is a sequence of decreasing submodules
  `N i` such that `I • N ≤ I (i + 1)`. Note that we do not require the filtration to start from `⊤`.
- `ideal.filtration.stable`: An `I`-filtration is stable if `I • (N i) = N (i + 1)` for large
  enough `i`.
- `ideal.filtration.submodule`: The associated module `⨁ Nᵢ` of a filtration, implemented as a
  submodule of `M[X]`.
- `ideal.filtration.submodule_fg_iff_stable`: If `F.N i` are all finitely generated, then
  `F.stable` iff `F.submodule.fg`.
- `ideal.filtration.stable.of_le`: In a finite module over a noetherian ring,
  if `F' ≤ F`, then `F.stable → F'.stable`.
- `ideal.exists_pow_inf_eq_pow_smul`: **Artin-Rees lemma**.
  given `N ≤ M`, there exists a `k` such that `IⁿM ⊓ N = Iⁿ⁻ᵏ(IᵏM ⊓ N)` for all `n ≥ k`.
- `ideal.infi_pow_eq_bot_of_local_ring`:
  **Krull's intersection theorem** (`⨅ i, I ^ i = ⊥`) for noetherian local rings.
- `ideal.infi_pow_eq_bot_of_is_domain`:
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
  n : ℕ → Submodule R M
  mono : ∀ i, N (i + 1) ≤ N i
  smul_le : ∀ i, I • N i ≤ N (i + 1)
#align ideal.filtration Ideal.Filtration

variable (F F' : I.Filtration M) {I}

namespace Ideal.Filtration

theorem pow_smul_le (i j : ℕ) : I ^ i • F.n j ≤ F.n (i + j) :=
  by
  induction i
  · simp
  · rw [pow_succ, mul_smul, Nat.succ_eq_add_one, add_assoc, add_comm 1, ← add_assoc]
    exact (Submodule.smul_mono_right i_ih).trans (F.smul_le _)
#align ideal.filtration.pow_smul_le Ideal.Filtration.pow_smul_le

theorem pow_smul_le_pow_smul (i j k : ℕ) : I ^ (i + k) • F.n j ≤ I ^ k • F.n (i + j) := by
  rw [add_comm, pow_add, mul_smul]; exact Submodule.smul_mono_right (F.pow_smul_le i j)
#align ideal.filtration.pow_smul_le_pow_smul Ideal.Filtration.pow_smul_le_pow_smul

protected theorem antitone : Antitone F.n :=
  antitone_nat_of_succ_le F.mono
#align ideal.filtration.antitone Ideal.Filtration.antitone

/-- The trivial `I`-filtration of `N`. -/
@[simps]
def Ideal.trivialFiltration (I : Ideal R) (N : Submodule R M) : I.Filtration M
    where
  n i := N
  mono i := le_of_eq rfl
  smul_le i := Submodule.smul_le_right
#align ideal.trivial_filtration Ideal.trivialFiltration

/-- The `sup` of two `I.filtration`s is an `I.filtration`. -/
instance : Sup (I.Filtration M) :=
  ⟨fun F F' =>
    ⟨F.n ⊔ F'.n, fun i => sup_le_sup (F.mono i) (F'.mono i), fun i =>
      (le_of_eq (Submodule.smul_sup _ _ _)).trans <| sup_le_sup (F.smul_le i) (F'.smul_le i)⟩⟩

/-- The `Sup` of a family of `I.filtration`s is an `I.filtration`. -/
instance : SupSet (I.Filtration M) :=
  ⟨fun S =>
    { n := sSup (Ideal.Filtration.n '' S)
      mono := fun i => by
        apply sSup_le_sSup_of_forall_exists_le _
        rintro _ ⟨⟨_, F, hF, rfl⟩, rfl⟩
        exact ⟨_, ⟨⟨_, F, hF, rfl⟩, rfl⟩, F.mono i⟩
      smul_le := fun i =>
        by
        rw [sSup_eq_iSup', iSup_apply, Submodule.smul_iSup, iSup_apply]
        apply iSup_mono _
        rintro ⟨_, F, hF, rfl⟩
        exact F.smul_le i }⟩

/-- The `inf` of two `I.filtration`s is an `I.filtration`. -/
instance : Inf (I.Filtration M) :=
  ⟨fun F F' =>
    ⟨F.n ⊓ F'.n, fun i => inf_le_inf (F.mono i) (F'.mono i), fun i =>
      (Submodule.smul_inf_le _ _ _).trans <| inf_le_inf (F.smul_le i) (F'.smul_le i)⟩⟩

/-- The `Inf` of a family of `I.filtration`s is an `I.filtration`. -/
instance : InfSet (I.Filtration M) :=
  ⟨fun S =>
    { n := sInf (Ideal.Filtration.n '' S)
      mono := fun i => by
        apply sInf_le_sInf_of_forall_exists_le _
        rintro _ ⟨⟨_, F, hF, rfl⟩, rfl⟩
        exact ⟨_, ⟨⟨_, F, hF, rfl⟩, rfl⟩, F.mono i⟩
      smul_le := fun i => by
        rw [sInf_eq_iInf', iInf_apply, iInf_apply]
        refine' submodule.smul_infi_le.trans _
        apply iInf_mono _
        rintro ⟨_, F, hF, rfl⟩
        exact F.smul_le i }⟩

instance : Top (I.Filtration M) :=
  ⟨I.trivialFiltration ⊤⟩

instance : Bot (I.Filtration M) :=
  ⟨I.trivialFiltration ⊥⟩

@[simp]
theorem sup_n : (F ⊔ F').n = F.n ⊔ F'.n :=
  rfl
#align ideal.filtration.sup_N Ideal.Filtration.sup_n

@[simp]
theorem sSup_n (S : Set (I.Filtration M)) : (sSup S).n = sSup (Ideal.Filtration.n '' S) :=
  rfl
#align ideal.filtration.Sup_N Ideal.Filtration.sSup_n

@[simp]
theorem inf_n : (F ⊓ F').n = F.n ⊓ F'.n :=
  rfl
#align ideal.filtration.inf_N Ideal.Filtration.inf_n

@[simp]
theorem sInf_n (S : Set (I.Filtration M)) : (sInf S).n = sInf (Ideal.Filtration.n '' S) :=
  rfl
#align ideal.filtration.Inf_N Ideal.Filtration.sInf_n

@[simp]
theorem top_n : (⊤ : I.Filtration M).n = ⊤ :=
  rfl
#align ideal.filtration.top_N Ideal.Filtration.top_n

@[simp]
theorem bot_n : (⊥ : I.Filtration M).n = ⊥ :=
  rfl
#align ideal.filtration.bot_N Ideal.Filtration.bot_n

@[simp]
theorem iSup_n {ι : Sort _} (f : ι → I.Filtration M) : (iSup f).n = ⨆ i, (f i).n :=
  congr_arg sSup (Set.range_comp _ _).symm
#align ideal.filtration.supr_N Ideal.Filtration.iSup_n

@[simp]
theorem iInf_n {ι : Sort _} (f : ι → I.Filtration M) : (iInf f).n = ⨅ i, (f i).n :=
  congr_arg sInf (Set.range_comp _ _).symm
#align ideal.filtration.infi_N Ideal.Filtration.iInf_n

instance : CompleteLattice (I.Filtration M) :=
  Function.Injective.completeLattice Ideal.Filtration.n Ideal.Filtration.ext sup_n inf_n
    (fun _ => sSup_image) (fun _ => sInf_image) top_n bot_n

instance : Inhabited (I.Filtration M) :=
  ⟨⊥⟩

/-- An `I` filtration is stable if `I • F.N n = F.N (n+1)` for large enough `n`. -/
def Stable : Prop :=
  ∃ n₀, ∀ n ≥ n₀, I • F.n n = F.n (n + 1)
#align ideal.filtration.stable Ideal.Filtration.Stable

/-- The trivial stable `I`-filtration of `N`. -/
@[simps]
def Ideal.stableFiltration (I : Ideal R) (N : Submodule R M) : I.Filtration M
    where
  n i := I ^ i • N
  mono i := by rw [add_comm, pow_add, mul_smul]; exact Submodule.smul_le_right
  smul_le i := by rw [add_comm, pow_add, mul_smul, pow_one]; exact le_refl _
#align ideal.stable_filtration Ideal.stableFiltration

theorem Ideal.stableFiltration_stable (I : Ideal R) (N : Submodule R M) :
    (I.stableFiltration N).Stable := by use 0; intro n _; dsimp;
  rw [add_comm, pow_add, mul_smul, pow_one]
#align ideal.stable_filtration_stable Ideal.stableFiltration_stable

variable {F F'} (h : F.Stable)

include h

theorem Stable.exists_pow_smul_eq : ∃ n₀, ∀ k, F.n (n₀ + k) = I ^ k • F.n n₀ :=
  by
  obtain ⟨n₀, hn⟩ := h
  use n₀
  intro k
  induction k
  · simp
  · rw [Nat.succ_eq_add_one, ← add_assoc, ← hn, k_ih, add_comm, pow_add, mul_smul, pow_one]
    linarith
#align ideal.filtration.stable.exists_pow_smul_eq Ideal.Filtration.Stable.exists_pow_smul_eq

theorem Stable.exists_pow_smul_eq_of_ge : ∃ n₀, ∀ n ≥ n₀, F.n n = I ^ (n - n₀) • F.n n₀ :=
  by
  obtain ⟨n₀, hn₀⟩ := h.exists_pow_smul_eq
  use n₀
  intro n hn
  convert hn₀ (n - n₀)
  rw [add_comm, tsub_add_cancel_of_le hn]
#align ideal.filtration.stable.exists_pow_smul_eq_of_ge Ideal.Filtration.Stable.exists_pow_smul_eq_of_ge

omit h

theorem stable_iff_exists_pow_smul_eq_of_ge :
    F.Stable ↔ ∃ n₀, ∀ n ≥ n₀, F.n n = I ^ (n - n₀) • F.n n₀ :=
  by
  refine' ⟨stable.exists_pow_smul_eq_of_ge, fun h => ⟨h.some, fun n hn => _⟩⟩
  rw [h.some_spec n hn, h.some_spec (n + 1) (by linarith), smul_smul, ← pow_succ,
    tsub_add_eq_add_tsub hn]
#align ideal.filtration.stable_iff_exists_pow_smul_eq_of_ge Ideal.Filtration.stable_iff_exists_pow_smul_eq_of_ge

theorem Stable.exists_forall_le (h : F.Stable) (e : F.n 0 ≤ F'.n 0) :
    ∃ n₀, ∀ n, F.n (n + n₀) ≤ F'.n n :=
  by
  obtain ⟨n₀, hF⟩ := h
  use n₀
  intro n
  induction' n with n hn
  · refine' (F.antitone _).trans e; simp
  · rw [Nat.succ_eq_one_add, add_assoc, add_comm, add_comm 1 n, ← hF]
    exact (Submodule.smul_mono_right hn).trans (F'.smul_le _)
    simp
#align ideal.filtration.stable.exists_forall_le Ideal.Filtration.Stable.exists_forall_le

theorem Stable.bounded_difference (h : F.Stable) (h' : F'.Stable) (e : F.n 0 = F'.n 0) :
    ∃ n₀, ∀ n, F.n (n + n₀) ≤ F'.n n ∧ F'.n (n + n₀) ≤ F.n n :=
  by
  obtain ⟨n₁, h₁⟩ := h.exists_forall_le (le_of_eq e)
  obtain ⟨n₂, h₂⟩ := h'.exists_forall_le (le_of_eq e.symm)
  use max n₁ n₂
  intro n
  refine' ⟨(F.antitone _).trans (h₁ n), (F'.antitone _).trans (h₂ n)⟩ <;> simp
#align ideal.filtration.stable.bounded_difference Ideal.Filtration.Stable.bounded_difference

open PolynomialModule

variable (F F')

/-- The `R[IX]`-submodule of `M[X]` associated with an `I`-filtration. -/
protected def submodule : Submodule (reesAlgebra I) (PolynomialModule R M)
    where
  carrier := { f | ∀ i, f i ∈ F.n i }
  add_mem' f g hf hg i := Submodule.add_mem _ (hf i) (hg i)
  zero_mem' i := Submodule.zero_mem _
  smul_mem' r f hf i := by
    rw [Subalgebra.smul_def, PolynomialModule.smul_apply]
    apply Submodule.sum_mem
    rintro ⟨j, k⟩ e
    rw [Finset.Nat.mem_antidiagonal] at e
    subst e
    exact F.pow_smul_le j k (Submodule.smul_mem_smul (r.2 j) (hf k))
#align ideal.filtration.submodule Ideal.Filtration.submodule

@[simp]
theorem mem_submodule (f : PolynomialModule R M) : f ∈ F.Submodule ↔ ∀ i, f i ∈ F.n i :=
  Iff.rfl
#align ideal.filtration.mem_submodule Ideal.Filtration.mem_submodule

theorem inf_submodule : (F ⊓ F').Submodule = F.Submodule ⊓ F'.Submodule := by ext; exact forall_and
#align ideal.filtration.inf_submodule Ideal.Filtration.inf_submodule

variable (I M)

/-- `ideal.filtration.submodule` as an `inf_hom` -/
def submoduleInfHom : InfHom (I.Filtration M) (Submodule (reesAlgebra I) (PolynomialModule R M))
    where
  toFun := Ideal.Filtration.submodule
  map_inf' := inf_submodule
#align ideal.filtration.submodule_inf_hom Ideal.Filtration.submoduleInfHom

variable {I M}

theorem submodule_closure_single :
    AddSubmonoid.closure (⋃ i, single R i '' (F.n i : Set M)) = F.Submodule.toAddSubmonoid :=
  by
  apply le_antisymm
  · rw [AddSubmonoid.closure_le, Set.iUnion_subset_iff]
    rintro i _ ⟨m, hm, rfl⟩ j
    rw [single_apply]
    split_ifs
    · rwa [← h]
    · exact (F.N j).zero_mem
  · intro f hf
    rw [← f.sum_single]
    apply AddSubmonoid.sum_mem _ _
    rintro c -
    exact AddSubmonoid.subset_closure (Set.subset_iUnion _ c <| Set.mem_image_of_mem _ (hf c))
#align ideal.filtration.submodule_closure_single Ideal.Filtration.submodule_closure_single

theorem submodule_span_single :
    Submodule.span (reesAlgebra I) (⋃ i, single R i '' (F.n i : Set M)) = F.Submodule :=
  by
  rw [← Submodule.span_closure, submodule_closure_single]
  simp
#align ideal.filtration.submodule_span_single Ideal.Filtration.submodule_span_single

theorem submodule_eq_span_le_iff_stable_ge (n₀ : ℕ) :
    F.Submodule = Submodule.span _ (⋃ i ≤ n₀, single R i '' (F.n i : Set M)) ↔
      ∀ n ≥ n₀, I • F.n n = F.n (n + 1) :=
  by
  rw [← submodule_span_single, ← LE.le.le_iff_eq, Submodule.span_le, Set.iUnion_subset_iff]
  swap; · exact Submodule.span_mono (Set.iUnion₂_subset_iUnion _ _)
  constructor
  · intro H n hn
    refine' (F.smul_le n).antisymm _
    intro x hx
    obtain ⟨l, hl⟩ := (Finsupp.mem_span_iff_total _ _ _).mp (H _ ⟨x, hx, rfl⟩)
    replace hl := congr_arg (fun f : ℕ →₀ M => f (n + 1)) hl
    dsimp only at hl
    erw [Finsupp.single_eq_same] at hl
    rw [← hl, Finsupp.total_apply, Finsupp.sum_apply]
    apply Submodule.sum_mem _ _
    rintro ⟨_, _, ⟨n', rfl⟩, _, ⟨hn', rfl⟩, m, hm, rfl⟩ -
    dsimp only [Subtype.coe_mk]
    rw [Subalgebra.smul_def, smul_single_apply, if_pos (show n' ≤ n + 1 by linarith)]
    have e : n' ≤ n := by linarith
    have := F.pow_smul_le_pow_smul (n - n') n' 1
    rw [tsub_add_cancel_of_le e, pow_one, add_comm _ 1, ← add_tsub_assoc_of_le e, add_comm] at this
    exact this (Submodule.smul_mem_smul ((l _).2 <| n + 1 - n') hm)
  · let F' := Submodule.span (reesAlgebra I) (⋃ i ≤ n₀, single R i '' (F.N i : Set M))
    intro hF i
    have : ∀ i ≤ n₀, single R i '' (F.N i : Set M) ⊆ F' := fun i hi =>
      Set.Subset.trans (Set.subset_iUnion₂ i hi) Submodule.subset_span
    induction' i with j hj
    · exact this _ (zero_le _)
    by_cases hj' : j.succ ≤ n₀
    · exact this _ hj'
    simp only [not_le, Nat.lt_succ_iff] at hj'
    rw [Nat.succ_eq_add_one, ← hF _ hj']
    rintro _ ⟨m, hm, rfl⟩
    apply Submodule.smul_induction_on hm
    · intro r hr m' hm'
      rw [add_comm, ← monomial_smul_single]
      exact
        F'.smul_mem ⟨_, rees_algebra.monomial_mem.mpr (by rwa [pow_one])⟩
          (hj <| Set.mem_image_of_mem _ hm')
    · intro x y hx hy; rw [map_add]; exact F'.add_mem hx hy
#align ideal.filtration.submodule_eq_span_le_iff_stable_ge Ideal.Filtration.submodule_eq_span_le_iff_stable_ge

/-- If the components of a filtration are finitely generated, then the filtration is stable iff
its associated submodule of is finitely generated.  -/
theorem submodule_fG_iff_stable (hF' : ∀ i, (F.n i).FG) : F.Submodule.FG ↔ F.Stable := by
  classical
    delta Ideal.Filtration.Stable
    simp_rw [← F.submodule_eq_span_le_iff_stable_ge]
    constructor
    · rintro H
      apply
        H.stablizes_of_supr_eq
          ⟨fun n₀ => Submodule.span _ (⋃ (i : ℕ) (H : i ≤ n₀), single R i '' ↑(F.N i)), _⟩
      · dsimp
        rw [← Submodule.span_iUnion, ← submodule_span_single]
        congr 1
        ext
        simp only [Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, exists_prop]
        constructor
        · rintro ⟨-, i, -, e⟩; exact ⟨i, e⟩
        · rintro ⟨i, e⟩; exact ⟨i, i, le_refl i, e⟩
      · intro n m e
        rw [Submodule.span_le, Set.iUnion₂_subset_iff]
        intro i hi
        refine'
          (Set.Subset.trans _ (Set.subset_iUnion₂ i (hi.trans e : _))).trans Submodule.subset_span
        rfl
    · rintro ⟨n, hn⟩
      rw [hn]
      simp_rw [Submodule.span_iUnion₂, ← Finset.mem_range_succ_iff, iSup_subtype']
      apply Submodule.fg_iSup
      rintro ⟨i, hi⟩
      obtain ⟨s, hs⟩ := hF' i
      have :
        Submodule.span (reesAlgebra I) (s.image (lsingle R i) : Set (PolynomialModule R M)) =
          Submodule.span _ (single R i '' (F.N i : Set M)) :=
        by rw [Finset.coe_image, ← Submodule.span_span_of_tower R, ← Submodule.map_span, hs]; rfl
      rw [Subtype.coe_mk, ← this]
      exact ⟨_, rfl⟩
#align ideal.filtration.submodule_fg_iff_stable Ideal.Filtration.submodule_fG_iff_stable

variable {F}

theorem Stable.of_le [IsNoetherianRing R] [h : Module.Finite R M] (hF : F.Stable)
    {F' : I.Filtration M} (hf : F' ≤ F) : F'.Stable :=
  by
  haveI := isNoetherian_of_fg_of_noetherian' h.1
  rw [← submodule_fg_iff_stable] at hF⊢
  any_goals intro i; exact IsNoetherian.noetherian _
  have := isNoetherian_of_fg_of_noetherian _ hF
  rw [isNoetherian_submodule] at this
  exact this _ (OrderHomClass.mono (submodule_inf_hom M I) hf)
#align ideal.filtration.stable.of_le Ideal.Filtration.Stable.of_le

theorem Stable.inter_right [IsNoetherianRing R] [h : Module.Finite R M] (hF : F.Stable) :
    (F ⊓ F').Stable :=
  hF.of_le inf_le_left
#align ideal.filtration.stable.inter_right Ideal.Filtration.Stable.inter_right

theorem Stable.inter_left [IsNoetherianRing R] [h : Module.Finite R M] (hF : F.Stable) :
    (F' ⊓ F).Stable :=
  hF.of_le inf_le_right
#align ideal.filtration.stable.inter_left Ideal.Filtration.Stable.inter_left

end Ideal.Filtration

variable (I)

/-- **Artin-Rees lemma** -/
theorem Ideal.exists_pow_inf_eq_pow_smul [IsNoetherianRing R] [h : Module.Finite R M]
    (N : Submodule R M) : ∃ k : ℕ, ∀ n ≥ k, I ^ n • ⊤ ⊓ N = I ^ (n - k) • (I ^ k • ⊤ ⊓ N) :=
  ((I.stableFiltration_stable ⊤).inter_right (I.trivialFiltration N)).exists_pow_smul_eq_of_ge
#align ideal.exists_pow_inf_eq_pow_smul Ideal.exists_pow_inf_eq_pow_smul

theorem Ideal.mem_iInf_smul_pow_eq_bot_iff [IsNoetherianRing R] [hM : Module.Finite R M] (x : M) :
    x ∈ (⨅ i : ℕ, I ^ i • ⊤ : Submodule R M) ↔ ∃ r : I, (r : R) • x = x :=
  by
  let N := (⨅ i : ℕ, I ^ i • ⊤ : Submodule R M)
  have hN : ∀ k, (I.stable_filtration ⊤ ⊓ I.trivial_filtration N).n k = N := by intro k;
    exact inf_eq_right.mpr ((iInf_le _ k).trans <| le_of_eq <| by simp)
  constructor
  · haveI := isNoetherian_of_fg_of_noetherian' hM.out
    obtain ⟨r, hr₁, hr₂⟩ :=
      Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I N (IsNoetherian.noetherian N) _
    · intro H; exact ⟨⟨r, hr₁⟩, hr₂ _ H⟩
    obtain ⟨k, hk⟩ := (I.stable_filtration_stable ⊤).inter_right (I.trivial_filtration N)
    have := hk k (le_refl _)
    rw [hN, hN] at this
    exact le_of_eq this.symm
  · rintro ⟨r, eq⟩
    rw [Submodule.mem_iInf]
    intro i
    induction' i with i hi
    · simp
    · rw [Nat.succ_eq_one_add, pow_add, ← smul_smul, pow_one, ← Eq]
      exact Submodule.smul_mem_smul r.prop hi
#align ideal.mem_infi_smul_pow_eq_bot_iff Ideal.mem_iInf_smul_pow_eq_bot_iff

theorem Ideal.iInf_pow_smul_eq_bot_of_localRing [IsNoetherianRing R] [LocalRing R]
    [Module.Finite R M] (h : I ≠ ⊤) : (⨅ i : ℕ, I ^ i • ⊤ : Submodule R M) = ⊥ :=
  by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨r, hr⟩ := (I.mem_infi_smul_pow_eq_bot_iff x).mp hx
  have := LocalRing.isUnit_one_sub_self_of_mem_nonunits _ (LocalRing.le_maximalIdeal h r.prop)
  apply this.smul_left_cancel.mp
  swap; · infer_instance
  simp [sub_smul, hr]
#align ideal.infi_pow_smul_eq_bot_of_local_ring Ideal.iInf_pow_smul_eq_bot_of_localRing

/-- **Krull's intersection theorem** for noetherian local rings. -/
theorem Ideal.iInf_pow_eq_bot_of_localRing [IsNoetherianRing R] [LocalRing R] (h : I ≠ ⊤) :
    (⨅ i : ℕ, I ^ i) = ⊥ :=
  by
  convert I.infi_pow_smul_eq_bot_of_local_ring h
  ext i
  rw [smul_eq_mul, ← Ideal.one_eq_top, mul_one]
  infer_instance
#align ideal.infi_pow_eq_bot_of_local_ring Ideal.iInf_pow_eq_bot_of_localRing

/-- **Krull's intersection theorem** for noetherian domains. -/
theorem Ideal.iInf_pow_eq_bot_of_isDomain [IsNoetherianRing R] [IsDomain R] (h : I ≠ ⊤) :
    (⨅ i : ℕ, I ^ i) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  by_contra hx'
  have := Ideal.mem_iInf_smul_pow_eq_bot_iff I x
  simp_rw [smul_eq_mul, ← Ideal.one_eq_top, mul_one] at this
  obtain ⟨r, hr⟩ := this.mp hx
  have := mul_right_cancel₀ hx' (hr.trans (one_mul x).symm)
  exact I.eq_top_iff_one.not.mp h (this ▸ r.prop)
#align ideal.infi_pow_eq_bot_of_is_domain Ideal.iInf_pow_eq_bot_of_isDomain

