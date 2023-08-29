/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.RingTheory.Ideal.Operations

#align_import ring_theory.finiteness from "leanprover-community/mathlib"@"c813ed7de0f5115f956239124e9b30f3a621966f"

/-!
# Finiteness conditions in commutative algebra

In this file we define a notion of finiteness that is common in commutative algebra.

## Main declarations

- `Submodule.FG`, `Ideal.FG`
  These express that some object is finitely generated as *submodule* over some base ring.

- `Module.Finite`, `RingHom.Finite`, `AlgHom.Finite`
  all of these express that some object is finitely generated *as module* over some base ring.

## Main results

* `exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul` is Nakayama's lemma, in the following form:
  if N is a finitely generated submodule of an ambient R-module M and I is an ideal of R
  such that N ⊆ IN, then there exists r ∈ 1 + I such that rN = 0.

-/


open Function (Surjective)

open BigOperators

namespace Submodule

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

open Set

/-- A submodule of `M` is finitely generated if it is the span of a finite subset of `M`. -/
def FG (N : Submodule R M) : Prop :=
  ∃ S : Finset M, Submodule.span R ↑S = N
#align submodule.fg Submodule.FG

theorem fg_def {N : Submodule R M} : N.FG ↔ ∃ S : Set M, S.Finite ∧ span R S = N :=
  ⟨fun ⟨t, h⟩ => ⟨_, Finset.finite_toSet t, h⟩, by
    rintro ⟨t', h, rfl⟩
    -- ⊢ FG (span R t')
    rcases Finite.exists_finset_coe h with ⟨t, rfl⟩
    -- ⊢ FG (span R ↑t)
    exact ⟨t, rfl⟩⟩
    -- 🎉 no goals
#align submodule.fg_def Submodule.fg_def

theorem fg_iff_addSubmonoid_fg (P : Submodule ℕ M) : P.FG ↔ P.toAddSubmonoid.FG :=
  ⟨fun ⟨S, hS⟩ => ⟨S, by simpa [← span_nat_eq_addSubmonoid_closure] using hS⟩, fun ⟨S, hS⟩ =>
                         -- 🎉 no goals
    ⟨S, by simpa [← span_nat_eq_addSubmonoid_closure] using hS⟩⟩
           -- 🎉 no goals
#align submodule.fg_iff_add_submonoid_fg Submodule.fg_iff_addSubmonoid_fg

theorem fg_iff_add_subgroup_fg {G : Type*} [AddCommGroup G] (P : Submodule ℤ G) :
    P.FG ↔ P.toAddSubgroup.FG :=
  ⟨fun ⟨S, hS⟩ => ⟨S, by simpa [← span_int_eq_addSubgroup_closure] using hS⟩, fun ⟨S, hS⟩ =>
                         -- 🎉 no goals
    ⟨S, by simpa [← span_int_eq_addSubgroup_closure] using hS⟩⟩
           -- 🎉 no goals
#align submodule.fg_iff_add_subgroup_fg Submodule.fg_iff_add_subgroup_fg

theorem fg_iff_exists_fin_generating_family {N : Submodule R M} :
    N.FG ↔ ∃ (n : ℕ) (s : Fin n → M), span R (range s) = N := by
  rw [fg_def]
  -- ⊢ (∃ S, Set.Finite S ∧ span R S = N) ↔ ∃ n s, span R (range s) = N
  constructor
  -- ⊢ (∃ S, Set.Finite S ∧ span R S = N) → ∃ n s, span R (range s) = N
  · rintro ⟨S, Sfin, hS⟩
    -- ⊢ ∃ n s, span R (range s) = N
    obtain ⟨n, f, rfl⟩ := Sfin.fin_embedding
    -- ⊢ ∃ n s, span R (range s) = N
    exact ⟨n, f, hS⟩
    -- 🎉 no goals
  · rintro ⟨n, s, hs⟩
    -- ⊢ ∃ S, Set.Finite S ∧ span R S = N
    refine' ⟨range s, finite_range s, hs⟩
    -- 🎉 no goals
#align submodule.fg_iff_exists_fin_generating_family Submodule.fg_iff_exists_fin_generating_family

/-- **Nakayama's Lemma**. Atiyah-Macdonald 2.5, Eisenbud 4.7, Matsumura 2.2,
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV) -/
theorem exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (I : Ideal R) (N : Submodule R M) (hn : N.FG) (hin : N ≤ I • N) :
    ∃ r : R, r - 1 ∈ I ∧ ∀ n ∈ N, r • n = (0 : M) := by
  rw [fg_def] at hn
  -- ⊢ ∃ r, r - 1 ∈ I ∧ ∀ (n : M), n ∈ N → r • n = 0
  rcases hn with ⟨s, hfs, hs⟩
  -- ⊢ ∃ r, r - 1 ∈ I ∧ ∀ (n : M), n ∈ N → r • n = 0
  have : ∃ r : R, r - 1 ∈ I ∧ N ≤ (I • span R s).comap (LinearMap.lsmul R M r) ∧ s ⊆ N := by
    refine' ⟨1, _, _, _⟩
    · rw [sub_self]
      exact I.zero_mem
    · rw [hs]
      intro n hn
      rw [mem_comap]
      change (1 : R) • n ∈ I • N
      rw [one_smul]
      exact hin hn
    · rw [← span_le, hs]
  clear hin hs
  -- ⊢ ∃ r, r - 1 ∈ I ∧ ∀ (n : M), n ∈ N → r • n = 0
  revert this
  -- ⊢ (∃ r, r - 1 ∈ I ∧ N ≤ comap (↑(LinearMap.lsmul R M) r) (I • span R s) ∧ s ⊆  …
  refine' Set.Finite.dinduction_on _ hfs (fun H => _) @fun i s _ _ ih H => _
  -- ⊢ ∃ r, r - 1 ∈ I ∧ ∀ (n : M), n ∈ N → r • n = 0
  · rcases H with ⟨r, hr1, hrn, _⟩
    -- ⊢ ∃ r, r - 1 ∈ I ∧ ∀ (n : M), n ∈ N → r • n = 0
    refine' ⟨r, hr1, fun n hn => _⟩
    -- ⊢ r • n = 0
    specialize hrn hn
    -- ⊢ r • n = 0
    rwa [mem_comap, span_empty, smul_bot, mem_bot] at hrn
    -- 🎉 no goals
  apply ih
  -- ⊢ ∃ r, r - 1 ∈ I ∧ N ≤ comap (↑(LinearMap.lsmul R M) r) (I • span R s) ∧ s ⊆ ↑N
  rcases H with ⟨r, hr1, hrn, hs⟩
  -- ⊢ ∃ r, r - 1 ∈ I ∧ N ≤ comap (↑(LinearMap.lsmul R M) r) (I • span R s) ∧ s ⊆ ↑N
  rw [← Set.singleton_union, span_union, smul_sup] at hrn
  -- ⊢ ∃ r, r - 1 ∈ I ∧ N ≤ comap (↑(LinearMap.lsmul R M) r) (I • span R s) ∧ s ⊆ ↑N
  rw [Set.insert_subset_iff] at hs
  -- ⊢ ∃ r, r - 1 ∈ I ∧ N ≤ comap (↑(LinearMap.lsmul R M) r) (I • span R s) ∧ s ⊆ ↑N
  have : ∃ c : R, c - 1 ∈ I ∧ c • i ∈ I • span R s := by
    specialize hrn hs.1
    rw [mem_comap, mem_sup] at hrn
    rcases hrn with ⟨y, hy, z, hz, hyz⟩
    dsimp at hyz
    rw [mem_smul_span_singleton] at hy
    rcases hy with ⟨c, hci, rfl⟩
    use r - c
    constructor
    · rw [sub_right_comm]
      exact I.sub_mem hr1 hci
    · rw [sub_smul, ← hyz, add_sub_cancel']
      exact hz
  rcases this with ⟨c, hc1, hci⟩
  -- ⊢ ∃ r, r - 1 ∈ I ∧ N ≤ comap (↑(LinearMap.lsmul R M) r) (I • span R s) ∧ s ⊆ ↑N
  refine' ⟨c * r, _, _, hs.2⟩
  -- ⊢ c * r - 1 ∈ I
  · simpa only [mul_sub, mul_one, sub_add_sub_cancel] using I.add_mem (I.mul_mem_left c hr1) hc1
    -- 🎉 no goals
  · intro n hn
    -- ⊢ n ∈ comap (↑(LinearMap.lsmul R M) (c * r)) (I • span R s)
    specialize hrn hn
    -- ⊢ n ∈ comap (↑(LinearMap.lsmul R M) (c * r)) (I • span R s)
    rw [mem_comap, mem_sup] at hrn
    -- ⊢ n ∈ comap (↑(LinearMap.lsmul R M) (c * r)) (I • span R s)
    rcases hrn with ⟨y, hy, z, hz, hyz⟩
    -- ⊢ n ∈ comap (↑(LinearMap.lsmul R M) (c * r)) (I • span R s)
    dsimp at hyz
    -- ⊢ n ∈ comap (↑(LinearMap.lsmul R M) (c * r)) (I • span R s)
    rw [mem_smul_span_singleton] at hy
    -- ⊢ n ∈ comap (↑(LinearMap.lsmul R M) (c * r)) (I • span R s)
    rcases hy with ⟨d, _, rfl⟩
    -- ⊢ n ∈ comap (↑(LinearMap.lsmul R M) (c * r)) (I • span R s)
    simp only [mem_comap, LinearMap.lsmul_apply]
    -- ⊢ (c * r) • n ∈ I • span R s
    rw [mul_smul, ← hyz, smul_add, smul_smul, mul_comm, mul_smul]
    -- ⊢ d • c • i + c • z ∈ I • span R s
    exact add_mem (smul_mem _ _ hci) (smul_mem _ _ hz)
    -- 🎉 no goals
#align submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul

theorem exists_mem_and_smul_eq_self_of_fg_of_le_smul {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (I : Ideal R) (N : Submodule R M) (hn : N.FG) (hin : N ≤ I • N) :
    ∃ r ∈ I, ∀ n ∈ N, r • n = n := by
  obtain ⟨r, hr, hr'⟩ := exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I N hn hin
  -- ⊢ ∃ r, r ∈ I ∧ ∀ (n : M), n ∈ N → r • n = n
  exact ⟨-(r - 1), I.neg_mem hr, fun n hn => by simpa [sub_smul] using hr' n hn⟩
  -- 🎉 no goals
#align submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul

theorem fg_bot : (⊥ : Submodule R M).FG :=
  ⟨∅, by rw [Finset.coe_empty, span_empty]⟩
         -- 🎉 no goals
#align submodule.fg_bot Submodule.fg_bot

theorem _root_.Subalgebra.fg_bot_toSubmodule {R A : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] : (⊥ : Subalgebra R A).toSubmodule.FG :=
  ⟨{1}, by simp [Algebra.toSubmodule_bot]⟩
           -- 🎉 no goals
#align subalgebra.fg_bot_to_submodule Subalgebra.fg_bot_toSubmodule

theorem fg_unit {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (I : (Submodule R A)ˣ) :
    (I : Submodule R A).FG := by
  have : (1 : A) ∈ (I * ↑I⁻¹ : Submodule R A) := by
    rw [I.mul_inv]
    exact one_le.mp le_rfl
  obtain ⟨T, T', hT, hT', one_mem⟩ := mem_span_mul_finite_of_mem_mul this
  -- ⊢ FG ↑I
  refine' ⟨T, span_eq_of_le _ hT _⟩
  -- ⊢ ↑I ≤ span R ↑T
  rw [← one_mul I, ← mul_one (span R (T : Set A))]
  -- ⊢ ↑(1 * I) ≤ span R ↑T * 1
  conv_rhs => rw [← I.inv_mul, ← mul_assoc]
  -- ⊢ ↑(1 * I) ≤ span R ↑T * ↑I⁻¹ * ↑I
  refine' mul_le_mul_left (le_trans _ <| mul_le_mul_right <| span_le.mpr hT')
  -- ⊢ ↑1 ≤ span R ↑T * span R ↑T'
  simp only [Units.val_one, span_mul_span]
  -- ⊢ 1 ≤ span R (↑T * ↑T')
  rwa [one_le]
  -- 🎉 no goals
#align submodule.fg_unit Submodule.fg_unit

theorem fg_of_isUnit {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {I : Submodule R A}
    (hI : IsUnit I) : I.FG :=
  fg_unit hI.unit
#align submodule.fg_of_is_unit Submodule.fg_of_isUnit

theorem fg_span {s : Set M} (hs : s.Finite) : FG (span R s) :=
  ⟨hs.toFinset, by rw [hs.coe_toFinset]⟩
                   -- 🎉 no goals
#align submodule.fg_span Submodule.fg_span

theorem fg_span_singleton (x : M) : FG (R ∙ x) :=
  fg_span (finite_singleton x)
#align submodule.fg_span_singleton Submodule.fg_span_singleton

theorem FG.sup {N₁ N₂ : Submodule R M} (hN₁ : N₁.FG) (hN₂ : N₂.FG) : (N₁ ⊔ N₂).FG :=
  let ⟨t₁, ht₁⟩ := fg_def.1 hN₁
  let ⟨t₂, ht₂⟩ := fg_def.1 hN₂
  fg_def.2 ⟨t₁ ∪ t₂, ht₁.1.union ht₂.1, by rw [span_union, ht₁.2, ht₂.2]⟩
                                           -- 🎉 no goals
#align submodule.fg.sup Submodule.FG.sup

theorem fg_finset_sup {ι : Type*} (s : Finset ι) (N : ι → Submodule R M) (h : ∀ i ∈ s, (N i).FG) :
    (s.sup N).FG :=
  Finset.sup_induction fg_bot (fun _ ha _ hb => ha.sup hb) h
#align submodule.fg_finset_sup Submodule.fg_finset_sup

theorem fg_biSup {ι : Type*} (s : Finset ι) (N : ι → Submodule R M) (h : ∀ i ∈ s, (N i).FG) :
    (⨆ i ∈ s, N i).FG := by simpa only [Finset.sup_eq_iSup] using fg_finset_sup s N h
                            -- 🎉 no goals
#align submodule.fg_bsupr Submodule.fg_biSup

theorem fg_iSup {ι : Type*} [Finite ι] (N : ι → Submodule R M) (h : ∀ i, (N i).FG) :
    (iSup N).FG := by
  cases nonempty_fintype ι
  -- ⊢ FG (iSup N)
  simpa using fg_biSup Finset.univ N fun i _ => h i
  -- 🎉 no goals
#align submodule.fg_supr Submodule.fg_iSup

variable {P : Type*} [AddCommMonoid P] [Module R P]

variable (f : M →ₗ[R] P)

theorem FG.map {N : Submodule R M} (hs : N.FG) : (N.map f).FG :=
  let ⟨t, ht⟩ := fg_def.1 hs
  fg_def.2 ⟨f '' t, ht.1.image _, by rw [span_image, ht.2]⟩
                                     -- 🎉 no goals
#align submodule.fg.map Submodule.FG.map

variable {f}

theorem fg_of_fg_map_injective (f : M →ₗ[R] P) (hf : Function.Injective f) {N : Submodule R M}
    (hfn : (N.map f).FG) : N.FG :=
  let ⟨t, ht⟩ := hfn
  ⟨t.preimage f fun x _ y _ h => hf h,
    Submodule.map_injective_of_injective hf <| by
      rw [map_span, Finset.coe_preimage, Set.image_preimage_eq_inter_range,
        Set.inter_eq_self_of_subset_left, ht]
      rw [← LinearMap.range_coe, ← span_le, ht, ← map_top]
      -- ⊢ map f N ≤ map f ⊤
      exact map_mono le_top⟩
      -- 🎉 no goals
#align submodule.fg_of_fg_map_injective Submodule.fg_of_fg_map_injective

theorem fg_of_fg_map {R M P : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup P]
    [Module R P] (f : M →ₗ[R] P)
    (hf : LinearMap.ker f = ⊥) {N : Submodule R M}
    (hfn : (N.map f).FG) : N.FG :=
  fg_of_fg_map_injective f (LinearMap.ker_eq_bot.1 hf) hfn
#align submodule.fg_of_fg_map Submodule.fg_of_fg_map

theorem fg_top (N : Submodule R M) : (⊤ : Submodule R N).FG ↔ N.FG :=
  ⟨fun h => N.range_subtype ▸ map_top N.subtype ▸ h.map _, fun h =>
    fg_of_fg_map_injective N.subtype Subtype.val_injective <| by rwa [map_top, range_subtype]⟩
                                                                 -- 🎉 no goals
#align submodule.fg_top Submodule.fg_top

theorem fg_of_linearEquiv (e : M ≃ₗ[R] P) (h : (⊤ : Submodule R P).FG) : (⊤ : Submodule R M).FG :=
  e.symm.range ▸ map_top (e.symm : P →ₗ[R] M) ▸ h.map _
#align submodule.fg_of_linear_equiv Submodule.fg_of_linearEquiv

theorem FG.prod {sb : Submodule R M} {sc : Submodule R P} (hsb : sb.FG) (hsc : sc.FG) :
    (sb.prod sc).FG :=
  let ⟨tb, htb⟩ := fg_def.1 hsb
  let ⟨tc, htc⟩ := fg_def.1 hsc
  fg_def.2
    ⟨LinearMap.inl R M P '' tb ∪ LinearMap.inr R M P '' tc, (htb.1.image _).union (htc.1.image _),
      by rw [LinearMap.span_inl_union_inr, htb.2, htc.2]⟩
         -- 🎉 no goals
#align submodule.fg.prod Submodule.FG.prod

theorem fg_pi {ι : Type*} {M : ι → Type*} [Finite ι] [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] {p : ∀ i, Submodule R (M i)} (hsb : ∀ i, (p i).FG) :
    (Submodule.pi Set.univ p).FG := by
  classical
    simp_rw [fg_def] at hsb ⊢
    choose t htf hts using hsb
    -- Porting note: `refine'` doesn't work here
    refine
      ⟨⋃ i, (LinearMap.single i : _ →ₗ[R] _) '' t i, Set.finite_iUnion fun i => (htf i).image _, ?_⟩
    simp_rw [span_iUnion, span_image, hts, Submodule.iSup_map_single]
#align submodule.fg_pi Submodule.fg_pi

/-- If 0 → M' → M → M'' → 0 is exact and M' and M'' are
finitely generated then so is M. -/
theorem fg_of_fg_map_of_fg_inf_ker {R M P : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] P) {s : Submodule R M}
    (hs1 : (s.map f).FG)
    (hs2 : (s ⊓ LinearMap.ker f).FG) : s.FG := by
  haveI := Classical.decEq R
  -- ⊢ FG s
  haveI := Classical.decEq M
  -- ⊢ FG s
  haveI := Classical.decEq P
  -- ⊢ FG s
  cases' hs1 with t1 ht1
  -- ⊢ FG s
  cases' hs2 with t2 ht2
  -- ⊢ FG s
  have : ∀ y ∈ t1, ∃ x ∈ s, f x = y := by
    intro y hy
    have : y ∈ s.map f := by
      rw [← ht1]
      exact subset_span hy
    rcases mem_map.1 this with ⟨x, hx1, hx2⟩
    exact ⟨x, hx1, hx2⟩
  have : ∃ g : P → M, ∀ y ∈ t1, g y ∈ s ∧ f (g y) = y := by
    choose g hg1 hg2 using this
    exists fun y => if H : y ∈ t1 then g y H else 0
    intro y H
    constructor
    · simp only [dif_pos H]
      apply hg1
    · simp only [dif_pos H]
      apply hg2
  cases' this with g hg
  -- ⊢ FG s
  clear this
  -- ⊢ FG s
  exists t1.image g ∪ t2
  -- ⊢ span R ↑(Finset.image g t1 ∪ t2) = s
  rw [Finset.coe_union, span_union, Finset.coe_image]
  -- ⊢ span R (g '' ↑t1) ⊔ span R ↑t2 = s
  apply le_antisymm
  -- ⊢ span R (g '' ↑t1) ⊔ span R ↑t2 ≤ s
  · refine' sup_le (span_le.2 <| image_subset_iff.2 _) (span_le.2 _)
    -- ⊢ ↑t1 ⊆ g ⁻¹' ↑s
    · intro y hy
      -- ⊢ y ∈ g ⁻¹' ↑s
      exact (hg y hy).1
      -- 🎉 no goals
    · intro x hx
      -- ⊢ x ∈ ↑s
      have : x ∈ span R t2 := subset_span hx
      -- ⊢ x ∈ ↑s
      rw [ht2] at this
      -- ⊢ x ∈ ↑s
      exact this.1
      -- 🎉 no goals
  intro x hx
  -- ⊢ x ∈ span R (g '' ↑t1) ⊔ span R ↑t2
  have : f x ∈ s.map f := by
    rw [mem_map]
    exact ⟨x, hx, rfl⟩
  rw [← ht1, ← Set.image_id (t1 : Set P), Finsupp.mem_span_image_iff_total] at this
  -- ⊢ x ∈ span R (g '' ↑t1) ⊔ span R ↑t2
  rcases this with ⟨l, hl1, hl2⟩
  -- ⊢ x ∈ span R (g '' ↑t1) ⊔ span R ↑t2
  refine'
    mem_sup.2
      ⟨(Finsupp.total M M R id).toFun ((Finsupp.lmapDomain R R g : (P →₀ R) → M →₀ R) l), _,
        x - Finsupp.total M M R id ((Finsupp.lmapDomain R R g : (P →₀ R) → M →₀ R) l), _,
        add_sub_cancel'_right _ _⟩
  · rw [← Set.image_id (g '' ↑t1), Finsupp.mem_span_image_iff_total]
    -- ⊢ ∃ l_1, l_1 ∈ Finsupp.supported R R (g '' ↑t1) ∧ ↑(Finsupp.total M M R id) l_ …
    refine' ⟨_, _, rfl⟩
    -- ⊢ ↑(Finsupp.lmapDomain R R g) l ∈ Finsupp.supported R R (g '' ↑t1)
    haveI : Inhabited P := ⟨0⟩
    -- ⊢ ↑(Finsupp.lmapDomain R R g) l ∈ Finsupp.supported R R (g '' ↑t1)
    rw [← Finsupp.lmapDomain_supported _ _ g, mem_map]
    -- ⊢ ∃ y, y ∈ Finsupp.supported R R ↑t1 ∧ ↑(Finsupp.lmapDomain R R g) y = ↑(Finsu …
    refine' ⟨l, hl1, _⟩
    -- ⊢ ↑(Finsupp.lmapDomain R R g) l = ↑(Finsupp.lmapDomain R R g) l
    rfl
    -- 🎉 no goals
  rw [ht2, mem_inf]
  -- ⊢ x - ↑(Finsupp.total M M R id) (↑(Finsupp.lmapDomain R R g) l) ∈ s ∧ x - ↑(Fi …
  constructor
  -- ⊢ x - ↑(Finsupp.total M M R id) (↑(Finsupp.lmapDomain R R g) l) ∈ s
  · apply s.sub_mem hx
    -- ⊢ ↑(Finsupp.total M M R id) (↑(Finsupp.lmapDomain R R g) l) ∈ s
    rw [Finsupp.total_apply, Finsupp.lmapDomain_apply, Finsupp.sum_mapDomain_index]
    refine' s.sum_mem _
    · intro y hy
      -- ⊢ (fun a m => m • id (g a)) y (↑l y) ∈ s
      exact s.smul_mem _ (hg y (hl1 hy)).1
      -- 🎉 no goals
    · exact zero_smul _
      -- 🎉 no goals
    · exact fun _ _ _ => add_smul _ _ _
      -- 🎉 no goals
  · rw [LinearMap.mem_ker, f.map_sub, ← hl2]
    -- ⊢ ↑(Finsupp.total P ((fun x => P) x) R id) l - ↑f (↑(Finsupp.total M M R id) ( …
    rw [Finsupp.total_apply, Finsupp.total_apply, Finsupp.lmapDomain_apply]
    -- ⊢ (Finsupp.sum l fun i a => a • id i) - ↑f (Finsupp.sum (Finsupp.mapDomain g l …
    rw [Finsupp.sum_mapDomain_index, Finsupp.sum, Finsupp.sum, f.map_sum]
    rw [sub_eq_zero]
    refine' Finset.sum_congr rfl fun y hy => _
    unfold id
    rw [f.map_smul, (hg y (hl1 hy)).2]
    -- ⊢ ∀ (b : M), 0 • id b = 0
    · exact zero_smul _
      -- 🎉 no goals
    · exact fun _ _ _ => add_smul _ _ _
      -- 🎉 no goals
#align submodule.fg_of_fg_map_of_fg_inf_ker Submodule.fg_of_fg_map_of_fg_inf_ker

theorem fg_induction (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
    (P : Submodule R M → Prop) (h₁ : ∀ x, P (Submodule.span R {x}))
    (h₂ : ∀ M₁ M₂, P M₁ → P M₂ → P (M₁ ⊔ M₂)) (N : Submodule R M) (hN : N.FG) : P N := by
  classical
    obtain ⟨s, rfl⟩ := hN
    induction s using Finset.induction
    · rw [Finset.coe_empty, Submodule.span_empty, ← Submodule.span_zero_singleton]
      apply h₁
    · rw [Finset.coe_insert, Submodule.span_insert]
      apply h₂ <;> apply_assumption
#align submodule.fg_induction Submodule.fg_induction

/-- The kernel of the composition of two linear maps is finitely generated if both kernels are and
the first morphism is surjective. -/
theorem fg_ker_comp {R M N P : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf1 : (LinearMap.ker f).FG) (hf2 : (LinearMap.ker g).FG)
    (hsur : Function.Surjective f) : (g.comp f).ker.FG := by
  rw [LinearMap.ker_comp]
  -- ⊢ FG (comap f (LinearMap.ker g))
  apply fg_of_fg_map_of_fg_inf_ker f
  -- ⊢ FG (map f (comap f (LinearMap.ker g)))
  · rwa [Submodule.map_comap_eq, LinearMap.range_eq_top.2 hsur, top_inf_eq]
    -- 🎉 no goals
  · rwa [inf_of_le_right (show (LinearMap.ker f) ≤
      (LinearMap.ker g).comap f from comap_mono bot_le)]
#align submodule.fg_ker_comp Submodule.fg_ker_comp

theorem fg_restrictScalars {R S M : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] (N : Submodule S M)
    (hfin : N.FG) (h : Function.Surjective (algebraMap R S)) :
    (Submodule.restrictScalars R N).FG := by
  obtain ⟨X, rfl⟩ := hfin
  -- ⊢ FG (restrictScalars R (span S ↑X))
  use X
  -- ⊢ span R ↑X = restrictScalars R (span S ↑X)
  exact (Submodule.restrictScalars_span R S h (X : Set M)).symm
  -- 🎉 no goals
#align submodule.fg_restrict_scalars Submodule.fg_restrictScalars

theorem FG.stablizes_of_iSup_eq {M' : Submodule R M} (hM' : M'.FG) (N : ℕ →o Submodule R M)
    (H : iSup N = M') : ∃ n, M' = N n := by
  obtain ⟨S, hS⟩ := hM'
  -- ⊢ ∃ n, M' = ↑N n
  have : ∀ s : S, ∃ n, (s : M) ∈ N n := fun s =>
    (Submodule.mem_iSup_of_chain N s).mp
      (by
        rw [H, ← hS]
        exact Submodule.subset_span s.2)
  choose f hf using this
  -- ⊢ ∃ n, M' = ↑N n
  use S.attach.sup f
  -- ⊢ M' = ↑N (Finset.sup (Finset.attach S) f)
  apply le_antisymm
  -- ⊢ M' ≤ ↑N (Finset.sup (Finset.attach S) f)
  · conv_lhs => rw [← hS]
    -- ⊢ span R ↑S ≤ ↑N (Finset.sup (Finset.attach S) f)
    rw [Submodule.span_le]
    -- ⊢ ↑S ⊆ ↑(↑N (Finset.sup (Finset.attach S) f))
    intro s hs
    -- ⊢ s ∈ ↑(↑N (Finset.sup (Finset.attach S) f))
    exact N.2 (Finset.le_sup <| S.mem_attach ⟨s, hs⟩) (hf _)
    -- 🎉 no goals
  · rw [← H]
    -- ⊢ ↑N (Finset.sup (Finset.attach S) f) ≤ iSup ↑N
    exact le_iSup _ _
    -- 🎉 no goals
#align submodule.fg.stablizes_of_supr_eq Submodule.FG.stablizes_of_iSup_eq

/-- Finitely generated submodules are precisely compact elements in the submodule lattice. -/
theorem fg_iff_compact (s : Submodule R M) : s.FG ↔ CompleteLattice.IsCompactElement s := by
  classical
    -- Introduce shorthand for span of an element
    let sp : M → Submodule R M := fun a => span R {a}
    -- Trivial rewrite lemma; a small hack since simp (only) & rw can't accomplish this smoothly.
    have supr_rw : ∀ t : Finset M, ⨆ x ∈ t, sp x = ⨆ x ∈ (↑t : Set M), sp x := fun t => by rfl
    constructor
    · rintro ⟨t, rfl⟩
      rw [span_eq_iSup_of_singleton_spans, ← supr_rw, ← Finset.sup_eq_iSup t sp]
      apply CompleteLattice.finset_sup_compact_of_compact
      exact fun n _ => singleton_span_isCompactElement n
    · intro h
      -- s is the Sup of the spans of its elements.
      have sSup' : s = sSup (sp '' ↑s) := by
        rw [sSup_eq_iSup, iSup_image, ← span_eq_iSup_of_singleton_spans, eq_comm, span_eq]
      -- by h, s is then below (and equal to) the sup of the spans of finitely many elements.
      obtain ⟨u, ⟨huspan, husup⟩⟩ := h (sp '' ↑s) (le_of_eq sSup')
      have ssup : s = u.sup id := by
        suffices : u.sup id ≤ s
        exact le_antisymm husup this
        rw [sSup', Finset.sup_id_eq_sSup]
        exact sSup_le_sSup huspan
      -- Porting note: had to split this out of the `obtain`
      have := Finset.subset_image_iff.mp huspan
      obtain ⟨t, ⟨-, rfl⟩⟩ := this
      rw [Finset.sup_image, Function.comp.left_id, Finset.sup_eq_iSup, supr_rw, ←
        span_eq_iSup_of_singleton_spans, eq_comm] at ssup
      exact ⟨t, ssup⟩
#align submodule.fg_iff_compact Submodule.fg_iff_compact

end Submodule

namespace Submodule

section Map₂

variable {R M N P : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]

variable [Module R M] [Module R N] [Module R P]

theorem FG.map₂ (f : M →ₗ[R] N →ₗ[R] P) {p : Submodule R M} {q : Submodule R N} (hp : p.FG)
    (hq : q.FG) : (map₂ f p q).FG :=
  let ⟨sm, hfm, hm⟩ := fg_def.1 hp
  let ⟨sn, hfn, hn⟩ := fg_def.1 hq
  fg_def.2
    ⟨Set.image2 (fun m n => f m n) sm sn, hfm.image2 _ hfn,
      map₂_span_span R f sm sn ▸ hm ▸ hn ▸ rfl⟩
#align submodule.fg.map₂ Submodule.FG.map₂

end Map₂

section Mul

variable {R : Type*} {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

variable {M N : Submodule R A}

theorem FG.mul (hm : M.FG) (hn : N.FG) : (M * N).FG :=
  hm.map₂ _ hn
#align submodule.fg.mul Submodule.FG.mul

theorem FG.pow (h : M.FG) (n : ℕ) : (M ^ n).FG :=
  Nat.recOn n ⟨{1}, by simp [one_eq_span]⟩ fun n ih => by simpa [pow_succ] using h.mul ih
                       -- 🎉 no goals
                                                          -- 🎉 no goals
#align submodule.fg.pow Submodule.FG.pow

end Mul

end Submodule

namespace Ideal

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- An ideal of `R` is finitely generated if it is the span of a finite subset of `R`.

This is defeq to `Submodule.FG`, but unfolds more nicely. -/
def FG (I : Ideal R) : Prop :=
  ∃ S : Finset R, Ideal.span ↑S = I
#align ideal.fg Ideal.FG

/-- The image of a finitely generated ideal is finitely generated.

This is the `Ideal` version of `Submodule.FG.map`. -/
theorem FG.map {R S : Type*} [Semiring R] [Semiring S] {I : Ideal R} (h : I.FG) (f : R →+* S) :
    (I.map f).FG := by
  classical
    obtain ⟨s, hs⟩ := h
    refine' ⟨s.image f, _⟩
    rw [Finset.coe_image, ← Ideal.map_span, hs]
#align ideal.fg.map Ideal.FG.map

theorem fg_ker_comp {R S A : Type*} [CommRing R] [CommRing S] [CommRing A] (f : R →+* S)
    (g : S →+* A) (hf : f.ker.FG) (hg : g.ker.FG) (hsur : Function.Surjective f) :
    (g.comp f).ker.FG := by
  letI : Algebra R S := RingHom.toAlgebra f
  -- ⊢ FG (RingHom.ker (RingHom.comp g f))
  letI : Algebra R A := RingHom.toAlgebra (g.comp f)
  -- ⊢ FG (RingHom.ker (RingHom.comp g f))
  letI : Algebra S A := RingHom.toAlgebra g
  -- ⊢ FG (RingHom.ker (RingHom.comp g f))
  letI : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- ⊢ FG (RingHom.ker (RingHom.comp g f))
  let f₁ := Algebra.linearMap R S
  -- ⊢ FG (RingHom.ker (RingHom.comp g f))
  let g₁ := (IsScalarTower.toAlgHom R S A).toLinearMap
  -- ⊢ FG (RingHom.ker (RingHom.comp g f))
  exact Submodule.fg_ker_comp f₁ g₁ hf (Submodule.fg_restrictScalars (RingHom.ker g) hg hsur) hsur
  -- 🎉 no goals
#align ideal.fg_ker_comp Ideal.fg_ker_comp

theorem exists_radical_pow_le_of_fg {R : Type*} [CommSemiring R] (I : Ideal R) (h : I.radical.FG) :
    ∃ n : ℕ, I.radical ^ n ≤ I := by
  have := le_refl I.radical; revert this
  -- ⊢ ∃ n, radical I ^ n ≤ I
                             -- ⊢ radical I ≤ radical I → ∃ n, radical I ^ n ≤ I
  refine' Submodule.fg_induction _ _ (fun J => J ≤ I.radical → ∃ n : ℕ, J ^ n ≤ I) _ _ _ h
  -- ⊢ ∀ (x : R), (fun J => J ≤ radical I → ∃ n, J ^ n ≤ I) (Submodule.span R {x})
  · intro x hx
    -- ⊢ ∃ n, Submodule.span R {x} ^ n ≤ I
    obtain ⟨n, hn⟩ := hx (subset_span (Set.mem_singleton x))
    -- ⊢ ∃ n, Submodule.span R {x} ^ n ≤ I
    exact ⟨n, by rwa [← Ideal.span, span_singleton_pow, span_le, Set.singleton_subset_iff]⟩
    -- 🎉 no goals
  · intro J K hJ hK hJK
    -- ⊢ ∃ n, (J ⊔ K) ^ n ≤ I
    obtain ⟨n, hn⟩ := hJ fun x hx => hJK <| Ideal.mem_sup_left hx
    -- ⊢ ∃ n, (J ⊔ K) ^ n ≤ I
    obtain ⟨m, hm⟩ := hK fun x hx => hJK <| Ideal.mem_sup_right hx
    -- ⊢ ∃ n, (J ⊔ K) ^ n ≤ I
    use n + m
    -- ⊢ (J ⊔ K) ^ (n + m) ≤ I
    rw [← Ideal.add_eq_sup, add_pow, Ideal.sum_eq_sup, Finset.sup_le_iff]
    -- ⊢ ∀ (b : ℕ), b ∈ Finset.range (n + m + 1) → J ^ b * K ^ (n + m - b) * ↑(Nat.ch …
    refine' fun i _ => Ideal.mul_le_right.trans _
    -- ⊢ J ^ i * K ^ (n + m - i) ≤ I
    obtain h | h := le_or_lt n i
    -- ⊢ J ^ i * K ^ (n + m - i) ≤ I
    · apply Ideal.mul_le_right.trans ((Ideal.pow_le_pow h).trans hn)
      -- 🎉 no goals
    · apply Ideal.mul_le_left.trans
      -- ⊢ K ^ (n + m - i) ≤ I
      refine' (Ideal.pow_le_pow _).trans hm
      -- ⊢ m ≤ n + m - i
      rw [add_comm, Nat.add_sub_assoc h.le]
      -- ⊢ m ≤ m + (n - i)
      apply Nat.le_add_right
      -- 🎉 no goals
#align ideal.exists_radical_pow_le_of_fg Ideal.exists_radical_pow_le_of_fg

end Ideal

section ModuleAndAlgebra

variable (R A B M N : Type*)

/-- A module over a semiring is `Finite` if it is finitely generated as a module. -/
class Module.Finite [Semiring R] [AddCommMonoid M] [Module R M] : Prop where
  out : (⊤ : Submodule R M).FG
#align module.finite Module.Finite

attribute [inherit_doc Module.Finite] Module.Finite.out

namespace Module

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

theorem finite_def {R M} [Semiring R] [AddCommMonoid M] [Module R M] :
    Finite R M ↔ (⊤ : Submodule R M).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align module.finite_def Module.finite_def

namespace Finite

open Submodule Set

theorem iff_addMonoid_fg {M : Type*} [AddCommMonoid M] : Module.Finite ℕ M ↔ AddMonoid.FG M :=
  ⟨fun h => AddMonoid.fg_def.2 <| (Submodule.fg_iff_addSubmonoid_fg ⊤).1 (finite_def.1 h), fun h =>
    finite_def.2 <| (Submodule.fg_iff_addSubmonoid_fg ⊤).2 (AddMonoid.fg_def.1 h)⟩
#align module.finite.iff_add_monoid_fg Module.Finite.iff_addMonoid_fg

theorem iff_addGroup_fg {G : Type*} [AddCommGroup G] : Module.Finite ℤ G ↔ AddGroup.FG G :=
  ⟨fun h => AddGroup.fg_def.2 <| (Submodule.fg_iff_add_subgroup_fg ⊤).1 (finite_def.1 h), fun h =>
    finite_def.2 <| (Submodule.fg_iff_add_subgroup_fg ⊤).2 (AddGroup.fg_def.1 h)⟩
#align module.finite.iff_add_group_fg Module.Finite.iff_addGroup_fg

variable {R M N}

theorem exists_fin [Finite R M] : ∃ (n : ℕ) (s : Fin n → M), Submodule.span R (range s) = ⊤ :=
  Submodule.fg_iff_exists_fin_generating_family.mp out
#align module.finite.exists_fin Module.Finite.exists_fin

theorem of_surjective [hM : Finite R M] (f : M →ₗ[R] N) (hf : Surjective f) : Finite R N :=
  ⟨by
    rw [← LinearMap.range_eq_top.2 hf, ← Submodule.map_top]
    -- ⊢ FG (map f ⊤)
    exact hM.1.map f⟩
    -- 🎉 no goals
#align module.finite.of_surjective Module.Finite.of_surjective

/-- The range of a linear map from a finite module is finite. -/
instance range [Finite R M] (f : M →ₗ[R] N) : Finite R (LinearMap.range f) :=
  of_surjective f.rangeRestrict fun ⟨_, y, hy⟩ => ⟨y, Subtype.ext hy⟩
#align module.finite.range Module.Finite.range

/-- Pushforwards of finite submodules are finite. -/
instance map (p : Submodule R M) [Finite R p] (f : M →ₗ[R] N) : Finite R (p.map f) :=
  of_surjective (f.restrict fun _ => Submodule.mem_map_of_mem) fun ⟨_, _, hy, hy'⟩ =>
    ⟨⟨_, hy⟩, Subtype.ext hy'⟩
#align module.finite.map Module.Finite.map

variable (R)

instance self : Finite R R :=
  ⟨⟨{1}, by simpa only [Finset.coe_singleton] using Ideal.span_singleton_one⟩⟩
            -- 🎉 no goals
#align module.finite.self Module.Finite.self

variable (M)

theorem of_restrictScalars_finite (R A M : Type*) [CommSemiring R] [Semiring A] [AddCommMonoid M]
    [Module R M] [Module A M] [Algebra R A] [IsScalarTower R A M] [hM : Finite R M] :
    Finite A M := by
  rw [finite_def, Submodule.fg_def] at hM ⊢
  -- ⊢ ∃ S, Set.Finite S ∧ span A S = ⊤
  obtain ⟨S, hSfin, hSgen⟩ := hM
  -- ⊢ ∃ S, Set.Finite S ∧ span A S = ⊤
  refine' ⟨S, hSfin, eq_top_iff.2 _⟩
  -- ⊢ ⊤ ≤ span A S
  have := Submodule.span_le_restrictScalars R A S
  -- ⊢ ⊤ ≤ span A S
  rw [hSgen] at this
  -- ⊢ ⊤ ≤ span A S
  exact this
  -- 🎉 no goals
#align module.finite.of_restrict_scalars_finite Module.Finite.of_restrictScalars_finite

variable {R M}

instance prod [hM : Finite R M] [hN : Finite R N] : Finite R (M × N) :=
  ⟨by
    rw [← Submodule.prod_top]
    -- ⊢ FG (Submodule.prod ⊤ ⊤)
    exact hM.1.prod hN.1⟩
    -- 🎉 no goals
#align module.finite.prod Module.Finite.prod

instance pi {ι : Type*} {M : ι → Type*} [_root_.Finite ι] [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] [h : ∀ i, Finite R (M i)] : Finite R (∀ i, M i) :=
  ⟨by
    rw [← Submodule.pi_top]
    -- ⊢ FG (Submodule.pi ?m.416535 fun i => ⊤)
    exact Submodule.fg_pi fun i => (h i).1⟩
    -- 🎉 no goals
#align module.finite.pi Module.Finite.pi

theorem equiv [Finite R M] (e : M ≃ₗ[R] N) : Finite R N :=
  of_surjective (e : M →ₗ[R] N) e.surjective
#align module.finite.equiv Module.Finite.equiv

section Algebra

theorem trans {R : Type*} (A M : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M] :
    ∀ [Finite R A] [Finite A M], Finite R M
  | ⟨⟨s, hs⟩⟩, ⟨⟨t, ht⟩⟩ =>
    ⟨Submodule.fg_def.2
        ⟨Set.image2 (· • ·) (↑s : Set A) (↑t : Set M),
          Set.Finite.image2 _ s.finite_toSet t.finite_toSet, by
          erw [Set.image2_smul, Submodule.span_smul_of_span_eq_top hs (↑t : Set M), ht,
            Submodule.restrictScalars_top]⟩⟩
#align module.finite.trans Module.Finite.trans

end Algebra

end Finite

end Module

/-- Porting note: reminding Lean about this instance for Module.Finite.base_change -/
local instance [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M] [Module R M] :
  Module A (TensorProduct R A M) :=
  haveI : SMulCommClass R A A := IsScalarTower.to_smulCommClass
  TensorProduct.leftModule

instance Module.Finite.base_change [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M]
    [Module R M] [h : Module.Finite R M] : Module.Finite A (TensorProduct R A M) := by
  classical
    obtain ⟨s, hs⟩ := h.out
    refine' ⟨⟨s.image (TensorProduct.mk R A M 1), eq_top_iff.mpr fun x _ => _⟩⟩
    apply @TensorProduct.induction_on _ _ _ _ _ _ _ _ _ x
    · exact zero_mem _
    · intro x y
      -- Porting note: new TC reminder
      haveI : IsScalarTower R A (TensorProduct R A M) := TensorProduct.isScalarTower_left
      rw [Finset.coe_image, ← Submodule.span_span_of_tower R, Submodule.span_image, hs,
        Submodule.map_top, LinearMap.range_coe]
      change _ ∈ Submodule.span A (Set.range <| TensorProduct.mk R A M 1)
      rw [← mul_one x, ← smul_eq_mul, ← TensorProduct.smul_tmul']
      exact Submodule.smul_mem _ x (Submodule.subset_span <| Set.mem_range_self y)
    · exact fun _ _ => Submodule.add_mem _
#align module.finite.base_change Module.Finite.base_change

instance Module.Finite.tensorProduct [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [hM : Module.Finite R M] [hN : Module.Finite R N] :
    Module.Finite R (TensorProduct R M N) where
  out := (TensorProduct.map₂_mk_top_top_eq_top R M N).subst (hM.out.map₂ _ hN.out)
#align module.finite.tensor_product Module.Finite.tensorProduct

end ModuleAndAlgebra

namespace RingHom

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- A ring morphism `A →+* B` is `Finite` if `B` is finitely generated as `A`-module. -/
def Finite (f : A →+* B) : Prop :=
  letI : Algebra A B := f.toAlgebra
  Module.Finite A B
#align ring_hom.finite RingHom.Finite

namespace Finite

variable (A)

theorem id : Finite (RingHom.id A) :=
  Module.Finite.self A
#align ring_hom.finite.id RingHom.Finite.id

variable {A}

theorem of_surjective (f : A →+* B) (hf : Surjective f) : f.Finite :=
  letI := f.toAlgebra
  Module.Finite.of_surjective (Algebra.linearMap A B) hf
#align ring_hom.finite.of_surjective RingHom.Finite.of_surjective

theorem comp {g : B →+* C} {f : A →+* B} (hg : g.Finite) (hf : f.Finite) : (g.comp f).Finite := by
  letI := f.toAlgebra
  -- ⊢ Finite (RingHom.comp g f)
  letI := g.toAlgebra
  -- ⊢ Finite (RingHom.comp g f)
  letI := (g.comp f).toAlgebra
  -- ⊢ Finite (RingHom.comp g f)
  letI : IsScalarTower A B C := RestrictScalars.isScalarTower A B C
  -- ⊢ Finite (RingHom.comp g f)
  letI : Module.Finite A B := hf
  -- ⊢ Finite (RingHom.comp g f)
  letI : Module.Finite B C := hg
  -- ⊢ Finite (RingHom.comp g f)
  exact Module.Finite.trans B C
  -- 🎉 no goals
#align ring_hom.finite.comp RingHom.Finite.comp

theorem of_comp_finite {f : A →+* B} {g : B →+* C} (h : (g.comp f).Finite) : g.Finite := by
  letI := f.toAlgebra
  -- ⊢ Finite g
  letI := g.toAlgebra
  -- ⊢ Finite g
  letI := (g.comp f).toAlgebra
  -- ⊢ Finite g
  letI : IsScalarTower A B C := RestrictScalars.isScalarTower A B C
  -- ⊢ Finite g
  letI : Module.Finite A C := h
  -- ⊢ Finite g
  exact Module.Finite.of_restrictScalars_finite A B C
  -- 🎉 no goals
#align ring_hom.finite.of_comp_finite RingHom.Finite.of_comp_finite

end Finite

end RingHom

namespace AlgHom

variable {R A B C : Type*} [CommRing R]

variable [CommRing A] [CommRing B] [CommRing C]

variable [Algebra R A] [Algebra R B] [Algebra R C]

/-- An algebra morphism `A →ₐ[R] B` is finite if it is finite as ring morphism.
In other words, if `B` is finitely generated as `A`-module. -/
def Finite (f : A →ₐ[R] B) : Prop :=
  f.toRingHom.Finite
#align alg_hom.finite AlgHom.Finite

namespace Finite

variable (R A)

theorem id : Finite (AlgHom.id R A) :=
  RingHom.Finite.id A
#align alg_hom.finite.id AlgHom.Finite.id

variable {R A}

theorem comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.Finite) (hf : f.Finite) : (g.comp f).Finite :=
  RingHom.Finite.comp hg hf
#align alg_hom.finite.comp AlgHom.Finite.comp

theorem of_surjective (f : A →ₐ[R] B) (hf : Surjective f) : f.Finite :=
  RingHom.Finite.of_surjective f.toRingHom hf
#align alg_hom.finite.of_surjective AlgHom.Finite.of_surjective

theorem of_comp_finite {f : A →ₐ[R] B} {g : B →ₐ[R] C} (h : (g.comp f).Finite) : g.Finite :=
  RingHom.Finite.of_comp_finite h
#align alg_hom.finite.of_comp_finite AlgHom.Finite.of_comp_finite

end Finite

end AlgHom
