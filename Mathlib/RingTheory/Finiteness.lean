/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.LinearAlgebra.Quotient
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.GroupTheory.Finiteness
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Nilpotent.Defs

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
    rcases Finite.exists_finset_coe h with ⟨t, rfl⟩
    exact ⟨t, rfl⟩⟩
#align submodule.fg_def Submodule.fg_def

theorem fg_iff_addSubmonoid_fg (P : Submodule ℕ M) : P.FG ↔ P.toAddSubmonoid.FG :=
  ⟨fun ⟨S, hS⟩ => ⟨S, by simpa [← span_nat_eq_addSubmonoid_closure] using hS⟩, fun ⟨S, hS⟩ =>
    ⟨S, by simpa [← span_nat_eq_addSubmonoid_closure] using hS⟩⟩
#align submodule.fg_iff_add_submonoid_fg Submodule.fg_iff_addSubmonoid_fg

theorem fg_iff_add_subgroup_fg {G : Type*} [AddCommGroup G] (P : Submodule ℤ G) :
    P.FG ↔ P.toAddSubgroup.FG :=
  ⟨fun ⟨S, hS⟩ => ⟨S, by simpa [← span_int_eq_addSubgroup_closure] using hS⟩, fun ⟨S, hS⟩ =>
    ⟨S, by simpa [← span_int_eq_addSubgroup_closure] using hS⟩⟩
#align submodule.fg_iff_add_subgroup_fg Submodule.fg_iff_add_subgroup_fg

theorem fg_iff_exists_fin_generating_family {N : Submodule R M} :
    N.FG ↔ ∃ (n : ℕ) (s : Fin n → M), span R (range s) = N := by
  rw [fg_def]
  constructor
  · rintro ⟨S, Sfin, hS⟩
    obtain ⟨n, f, rfl⟩ := Sfin.fin_embedding
    exact ⟨n, f, hS⟩
  · rintro ⟨n, s, hs⟩
    exact ⟨range s, finite_range s, hs⟩
#align submodule.fg_iff_exists_fin_generating_family Submodule.fg_iff_exists_fin_generating_family

/-- **Nakayama's Lemma**. Atiyah-Macdonald 2.5, Eisenbud 4.7, Matsumura 2.2,
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV) -/
theorem exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (I : Ideal R) (N : Submodule R M) (hn : N.FG) (hin : N ≤ I • N) :
    ∃ r : R, r - 1 ∈ I ∧ ∀ n ∈ N, r • n = (0 : M) := by
  rw [fg_def] at hn
  rcases hn with ⟨s, hfs, hs⟩
  have : ∃ r : R, r - 1 ∈ I ∧ N ≤ (I • span R s).comap (LinearMap.lsmul R M r) ∧ s ⊆ N := by
    refine ⟨1, ?_, ?_, ?_⟩
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
  revert this
  refine Set.Finite.dinduction_on _ hfs (fun H => ?_) @fun i s _ _ ih H => ?_
  · rcases H with ⟨r, hr1, hrn, _⟩
    refine ⟨r, hr1, fun n hn => ?_⟩
    specialize hrn hn
    rwa [mem_comap, span_empty, smul_bot, mem_bot] at hrn
  apply ih
  rcases H with ⟨r, hr1, hrn, hs⟩
  rw [← Set.singleton_union, span_union, smul_sup] at hrn
  rw [Set.insert_subset_iff] at hs
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
    · rw [sub_smul, ← hyz, add_sub_cancel_left]
      exact hz
  rcases this with ⟨c, hc1, hci⟩
  refine ⟨c * r, ?_, ?_, hs.2⟩
  · simpa only [mul_sub, mul_one, sub_add_sub_cancel] using I.add_mem (I.mul_mem_left c hr1) hc1
  · intro n hn
    specialize hrn hn
    rw [mem_comap, mem_sup] at hrn
    rcases hrn with ⟨y, hy, z, hz, hyz⟩
    dsimp at hyz
    rw [mem_smul_span_singleton] at hy
    rcases hy with ⟨d, _, rfl⟩
    simp only [mem_comap, LinearMap.lsmul_apply]
    rw [mul_smul, ← hyz, smul_add, smul_smul, mul_comm, mul_smul]
    exact add_mem (smul_mem _ _ hci) (smul_mem _ _ hz)
#align submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul

theorem exists_mem_and_smul_eq_self_of_fg_of_le_smul {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (I : Ideal R) (N : Submodule R M) (hn : N.FG) (hin : N ≤ I • N) :
    ∃ r ∈ I, ∀ n ∈ N, r • n = n := by
  obtain ⟨r, hr, hr'⟩ := exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I N hn hin
  exact ⟨-(r - 1), I.neg_mem hr, fun n hn => by simpa [sub_smul] using hr' n hn⟩
#align submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul

theorem fg_bot : (⊥ : Submodule R M).FG :=
  ⟨∅, by rw [Finset.coe_empty, span_empty]⟩
#align submodule.fg_bot Submodule.fg_bot

theorem _root_.Subalgebra.fg_bot_toSubmodule {R A : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] : (⊥ : Subalgebra R A).toSubmodule.FG :=
  ⟨{1}, by simp [Algebra.toSubmodule_bot, one_eq_span]⟩
#align subalgebra.fg_bot_to_submodule Subalgebra.fg_bot_toSubmodule

theorem fg_unit {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (I : (Submodule R A)ˣ) :
    (I : Submodule R A).FG := by
  have : (1 : A) ∈ (I * ↑I⁻¹ : Submodule R A) := by
    rw [I.mul_inv]
    exact one_le.mp le_rfl
  obtain ⟨T, T', hT, hT', one_mem⟩ := mem_span_mul_finite_of_mem_mul this
  refine ⟨T, span_eq_of_le _ hT ?_⟩
  rw [← one_mul I, ← mul_one (span R (T : Set A))]
  conv_rhs => rw [← I.inv_mul, ← mul_assoc]
  refine mul_le_mul_left (le_trans ?_ <| mul_le_mul_right <| span_le.mpr hT')
  simp only [Units.val_one, span_mul_span]
  rwa [one_le]
#align submodule.fg_unit Submodule.fg_unit

theorem fg_of_isUnit {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {I : Submodule R A}
    (hI : IsUnit I) : I.FG :=
  fg_unit hI.unit
#align submodule.fg_of_is_unit Submodule.fg_of_isUnit

theorem fg_span {s : Set M} (hs : s.Finite) : FG (span R s) :=
  ⟨hs.toFinset, by rw [hs.coe_toFinset]⟩
#align submodule.fg_span Submodule.fg_span

theorem fg_span_singleton (x : M) : FG (R ∙ x) :=
  fg_span (finite_singleton x)
#align submodule.fg_span_singleton Submodule.fg_span_singleton

theorem FG.sup {N₁ N₂ : Submodule R M} (hN₁ : N₁.FG) (hN₂ : N₂.FG) : (N₁ ⊔ N₂).FG :=
  let ⟨t₁, ht₁⟩ := fg_def.1 hN₁
  let ⟨t₂, ht₂⟩ := fg_def.1 hN₂
  fg_def.2 ⟨t₁ ∪ t₂, ht₁.1.union ht₂.1, by rw [span_union, ht₁.2, ht₂.2]⟩
#align submodule.fg.sup Submodule.FG.sup

theorem fg_finset_sup {ι : Type*} (s : Finset ι) (N : ι → Submodule R M) (h : ∀ i ∈ s, (N i).FG) :
    (s.sup N).FG :=
  Finset.sup_induction fg_bot (fun _ ha _ hb => ha.sup hb) h
#align submodule.fg_finset_sup Submodule.fg_finset_sup

theorem fg_biSup {ι : Type*} (s : Finset ι) (N : ι → Submodule R M) (h : ∀ i ∈ s, (N i).FG) :
    (⨆ i ∈ s, N i).FG := by simpa only [Finset.sup_eq_iSup] using fg_finset_sup s N h
#align submodule.fg_bsupr Submodule.fg_biSup

theorem fg_iSup {ι : Sort*} [Finite ι] (N : ι → Submodule R M) (h : ∀ i, (N i).FG) :
    (iSup N).FG := by
  cases nonempty_fintype (PLift ι)
  simpa [iSup_plift_down] using fg_biSup Finset.univ (N ∘ PLift.down) fun i _ => h i.down
#align submodule.fg_supr Submodule.fg_iSup

variable {P : Type*} [AddCommMonoid P] [Module R P]
variable (f : M →ₗ[R] P)

theorem FG.map {N : Submodule R M} (hs : N.FG) : (N.map f).FG :=
  let ⟨t, ht⟩ := fg_def.1 hs
  fg_def.2 ⟨f '' t, ht.1.image _, by rw [span_image, ht.2]⟩
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
      exact map_mono le_top⟩
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
#align submodule.fg.prod Submodule.FG.prod

theorem fg_pi {ι : Type*} {M : ι → Type*} [Finite ι] [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] {p : ∀ i, Submodule R (M i)} (hsb : ∀ i, (p i).FG) :
    (Submodule.pi Set.univ p).FG := by
  classical
    simp_rw [fg_def] at hsb ⊢
    choose t htf hts using hsb
    refine
      ⟨⋃ i, (LinearMap.single i : _ →ₗ[R] _) '' t i, Set.finite_iUnion fun i => (htf i).image _, ?_⟩
    -- Note: #8386 changed `span_image` into `span_image _`
    simp_rw [span_iUnion, span_image _, hts, Submodule.iSup_map_single]
#align submodule.fg_pi Submodule.fg_pi

/-- If 0 → M' → M → M'' → 0 is exact and M' and M'' are
finitely generated then so is M. -/
theorem fg_of_fg_map_of_fg_inf_ker {R M P : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] P) {s : Submodule R M}
    (hs1 : (s.map f).FG)
    (hs2 : (s ⊓ LinearMap.ker f).FG) : s.FG := by
  haveI := Classical.decEq R
  haveI := Classical.decEq M
  haveI := Classical.decEq P
  cases' hs1 with t1 ht1
  cases' hs2 with t2 ht2
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
  clear this
  exists t1.image g ∪ t2
  rw [Finset.coe_union, span_union, Finset.coe_image]
  apply le_antisymm
  · refine sup_le (span_le.2 <| image_subset_iff.2 ?_) (span_le.2 ?_)
    · intro y hy
      exact (hg y hy).1
    · intro x hx
      have : x ∈ span R t2 := subset_span hx
      rw [ht2] at this
      exact this.1
  intro x hx
  have : f x ∈ s.map f := by
    rw [mem_map]
    exact ⟨x, hx, rfl⟩
  rw [← ht1, ← Set.image_id (t1 : Set P), Finsupp.mem_span_image_iff_total] at this
  rcases this with ⟨l, hl1, hl2⟩
  refine
    mem_sup.2
      ⟨(Finsupp.total M M R id).toFun ((Finsupp.lmapDomain R R g : (P →₀ R) → M →₀ R) l), ?_,
        x - Finsupp.total M M R id ((Finsupp.lmapDomain R R g : (P →₀ R) → M →₀ R) l), ?_,
        add_sub_cancel _ _⟩
  · rw [← Set.image_id (g '' ↑t1), Finsupp.mem_span_image_iff_total]
    refine ⟨_, ?_, rfl⟩
    haveI : Inhabited P := ⟨0⟩
    rw [← Finsupp.lmapDomain_supported _ _ g, mem_map]
    refine ⟨l, hl1, ?_⟩
    rfl
  rw [ht2, mem_inf]
  constructor
  · apply s.sub_mem hx
    rw [Finsupp.total_apply, Finsupp.lmapDomain_apply, Finsupp.sum_mapDomain_index]
    · refine s.sum_mem ?_
      intro y hy
      exact s.smul_mem _ (hg y (hl1 hy)).1
    · exact zero_smul _
    · exact fun _ _ _ => add_smul _ _ _
  · rw [LinearMap.mem_ker, f.map_sub, ← hl2]
    rw [Finsupp.total_apply, Finsupp.total_apply, Finsupp.lmapDomain_apply]
    rw [Finsupp.sum_mapDomain_index, Finsupp.sum, Finsupp.sum, map_sum]
    · rw [sub_eq_zero]
      refine Finset.sum_congr rfl fun y hy => ?_
      unfold id
      rw [f.map_smul, (hg y (hl1 hy)).2]
    · exact zero_smul _
    · exact fun _ _ _ => add_smul _ _ _
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
  apply fg_of_fg_map_of_fg_inf_ker f
  · rwa [Submodule.map_comap_eq, LinearMap.range_eq_top.2 hsur, top_inf_eq]
  · rwa [inf_of_le_right (show (LinearMap.ker f) ≤
      (LinearMap.ker g).comap f from comap_mono bot_le)]
#align submodule.fg_ker_comp Submodule.fg_ker_comp

theorem fg_restrictScalars {R S M : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] (N : Submodule S M)
    (hfin : N.FG) (h : Function.Surjective (algebraMap R S)) :
    (Submodule.restrictScalars R N).FG := by
  obtain ⟨X, rfl⟩ := hfin
  use X
  exact (Submodule.restrictScalars_span R S h (X : Set M)).symm
#align submodule.fg_restrict_scalars Submodule.fg_restrictScalars

theorem FG.stabilizes_of_iSup_eq {M' : Submodule R M} (hM' : M'.FG) (N : ℕ →o Submodule R M)
    (H : iSup N = M') : ∃ n, M' = N n := by
  obtain ⟨S, hS⟩ := hM'
  have : ∀ s : S, ∃ n, (s : M) ∈ N n := fun s =>
    (Submodule.mem_iSup_of_chain N s).mp
      (by
        rw [H, ← hS]
        exact Submodule.subset_span s.2)
  choose f hf using this
  use S.attach.sup f
  apply le_antisymm
  · conv_lhs => rw [← hS]
    rw [Submodule.span_le]
    intro s hs
    exact N.2 (Finset.le_sup <| S.mem_attach ⟨s, hs⟩) (hf _)
  · rw [← H]
    exact le_iSup _ _
#align submodule.fg.stablizes_of_supr_eq Submodule.FG.stabilizes_of_iSup_eq

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
      apply CompleteLattice.isCompactElement_finsetSup
      exact fun n _ => singleton_span_isCompactElement n
    · intro h
      -- s is the Sup of the spans of its elements.
      have sSup' : s = sSup (sp '' ↑s) := by
        rw [sSup_eq_iSup, iSup_image, ← span_eq_iSup_of_singleton_spans, eq_comm, span_eq]
      -- by h, s is then below (and equal to) the sup of the spans of finitely many elements.
      obtain ⟨u, ⟨huspan, husup⟩⟩ := h (sp '' ↑s) (le_of_eq sSup')
      have ssup : s = u.sup id := by
        suffices u.sup id ≤ s from le_antisymm husup this
        rw [sSup', Finset.sup_id_eq_sSup]
        exact sSup_le_sSup huspan
      -- Porting note: had to split this out of the `obtain`
      have := Finset.subset_image_iff.mp huspan
      obtain ⟨t, ⟨-, rfl⟩⟩ := this
      rw [Finset.sup_image, Function.id_comp, Finset.sup_eq_iSup, supr_rw, ←
        span_eq_iSup_of_singleton_spans, eq_comm] at ssup
      exact ⟨t, ssup⟩
#align submodule.fg_iff_compact Submodule.fg_iff_compact

open TensorProduct LinearMap in
/-- Every `x : I ⊗ M` is the image of some `y : J ⊗ M`, where `J ≤ I` is finitely generated,
under the tensor product of `J.inclusion ‹J ≤ I› : J → I` and the identity `M → M`. -/
theorem exists_fg_le_eq_rTensor_inclusion {R M N : Type*} [CommRing R] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] {I : Submodule R N} (x : I ⊗ M) :
      ∃ (J : Submodule R N) (_ : J.FG) (hle : J ≤ I) (y : J ⊗ M),
        x = rTensor M (J.inclusion hle) y := by
  induction x with
  | zero => exact ⟨⊥, fg_bot, zero_le _, 0, rfl⟩
  | tmul i m => exact ⟨R ∙ i.val, fg_span_singleton i.val,
      (span_singleton_le_iff_mem _ _).mpr i.property,
      ⟨i.val, mem_span_singleton_self _⟩ ⊗ₜ[R] m, rfl⟩
  | add x₁ x₂ ihx₁ ihx₂ =>
    obtain ⟨J₁, hfg₁, hle₁, y₁, rfl⟩ := ihx₁
    obtain ⟨J₂, hfg₂, hle₂, y₂, rfl⟩ := ihx₂
    refine ⟨J₁ ⊔ J₂, hfg₁.sup hfg₂, sup_le hle₁ hle₂,
      rTensor M (J₁.inclusion (le_sup_left : J₁ ≤ J₁ ⊔ J₂)) y₁ +
        rTensor M (J₂.inclusion (le_sup_right : J₂ ≤ J₁ ⊔ J₂)) y₂, ?_⟩
    rewrite [map_add, ← rTensor_comp_apply, ← rTensor_comp_apply]
    rfl

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
  Nat.recOn n ⟨{1}, by simp [one_eq_span]⟩ fun n ih => by simpa [pow_succ] using ih.mul h
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
    refine ⟨s.image f, ?_⟩
    rw [Finset.coe_image, ← Ideal.map_span, hs]
#align ideal.fg.map Ideal.FG.map

theorem fg_ker_comp {R S A : Type*} [CommRing R] [CommRing S] [CommRing A] (f : R →+* S)
    (g : S →+* A) (hf : f.ker.FG) (hg : g.ker.FG) (hsur : Function.Surjective f) :
    (g.comp f).ker.FG := by
  letI : Algebra R S := RingHom.toAlgebra f
  letI : Algebra R A := RingHom.toAlgebra (g.comp f)
  letI : Algebra S A := RingHom.toAlgebra g
  letI : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f₁ := Algebra.linearMap R S
  let g₁ := (IsScalarTower.toAlgHom R S A).toLinearMap
  exact Submodule.fg_ker_comp f₁ g₁ hf (Submodule.fg_restrictScalars (RingHom.ker g) hg hsur) hsur
#align ideal.fg_ker_comp Ideal.fg_ker_comp

theorem exists_radical_pow_le_of_fg {R : Type*} [CommSemiring R] (I : Ideal R) (h : I.radical.FG) :
    ∃ n : ℕ, I.radical ^ n ≤ I := by
  have := le_refl I.radical; revert this
  refine Submodule.fg_induction _ _ (fun J => J ≤ I.radical → ∃ n : ℕ, J ^ n ≤ I) ?_ ?_ _ h
  · intro x hx
    obtain ⟨n, hn⟩ := hx (subset_span (Set.mem_singleton x))
    exact ⟨n, by rwa [← Ideal.span, span_singleton_pow, span_le, Set.singleton_subset_iff]⟩
  · intro J K hJ hK hJK
    obtain ⟨n, hn⟩ := hJ fun x hx => hJK <| Ideal.mem_sup_left hx
    obtain ⟨m, hm⟩ := hK fun x hx => hJK <| Ideal.mem_sup_right hx
    use n + m
    rw [← Ideal.add_eq_sup, add_pow, Ideal.sum_eq_sup, Finset.sup_le_iff]
    refine fun i _ => Ideal.mul_le_right.trans ?_
    obtain h | h := le_or_lt n i
    · apply Ideal.mul_le_right.trans ((Ideal.pow_le_pow_right h).trans hn)
    · apply Ideal.mul_le_left.trans
      refine (Ideal.pow_le_pow_right ?_).trans hm
      rw [add_comm, Nat.add_sub_assoc h.le]
      apply Nat.le_add_right
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

instance {M} [AddCommMonoid M] [AddMonoid.FG M] : Module.Finite ℕ M := iff_addMonoid_fg.mpr ‹_›

theorem iff_addGroup_fg {G : Type*} [AddCommGroup G] : Module.Finite ℤ G ↔ AddGroup.FG G :=
  ⟨fun h => AddGroup.fg_def.2 <| (Submodule.fg_iff_add_subgroup_fg ⊤).1 (finite_def.1 h), fun h =>
    finite_def.2 <| (Submodule.fg_iff_add_subgroup_fg ⊤).2 (AddGroup.fg_def.1 h)⟩
#align module.finite.iff_add_group_fg Module.Finite.iff_addGroup_fg

instance {M} [AddCommGroup M] [AddGroup.FG M] : Module.Finite ℤ M := iff_addGroup_fg.mpr ‹_›

variable {R M N}

/-- See also `Module.Finite.exists_fin'`. -/
theorem exists_fin [Finite R M] : ∃ (n : ℕ) (s : Fin n → M), Submodule.span R (range s) = ⊤ :=
  Submodule.fg_iff_exists_fin_generating_family.mp out
#align module.finite.exists_fin Module.Finite.exists_fin

variable (R M) in
lemma exists_fin' [Finite R M] : ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M), Surjective f := by
  have ⟨n, s, hs⟩ := exists_fin (R := R) (M := M)
  refine ⟨n, Basis.constr (Pi.basisFun R _) ℕ s, ?_⟩
  rw [← LinearMap.range_eq_top, Basis.constr_range, hs]

theorem of_surjective [hM : Finite R M] (f : M →ₗ[R] N) (hf : Surjective f) : Finite R N :=
  ⟨by
    rw [← LinearMap.range_eq_top.2 hf, ← Submodule.map_top]
    exact hM.1.map f⟩
#align module.finite.of_surjective Module.Finite.of_surjective

instance quotient (R) {A M} [Semiring R] [AddCommGroup M] [Ring A] [Module A M] [Module R M]
    [SMul R A] [IsScalarTower R A M] [Finite R M]
    (N : Submodule A M) : Finite R (M ⧸ N) :=
  Module.Finite.of_surjective (N.mkQ.restrictScalars R) N.mkQ_surjective

/-- The range of a linear map from a finite module is finite. -/
instance range {F : Type*} [FunLike F M N] [SemilinearMapClass F (RingHom.id R) M N] [Finite R M]
    (f : F) : Finite R (LinearMap.range f) :=
  of_surjective (SemilinearMapClass.semilinearMap f).rangeRestrict
    fun ⟨_, y, hy⟩ => ⟨y, Subtype.ext hy⟩
#align module.finite.range Module.Finite.range

/-- Pushforwards of finite submodules are finite. -/
instance map (p : Submodule R M) [Finite R p] (f : M →ₗ[R] N) : Finite R (p.map f) :=
  of_surjective (f.restrict fun _ => Submodule.mem_map_of_mem) fun ⟨_, _, hy, hy'⟩ =>
    ⟨⟨_, hy⟩, Subtype.ext hy'⟩
#align module.finite.map Module.Finite.map

variable (R)

instance self : Finite R R :=
  ⟨⟨{1}, by simpa only [Finset.coe_singleton] using Ideal.span_singleton_one⟩⟩
#align module.finite.self Module.Finite.self

variable (M)

theorem of_restrictScalars_finite (R A M : Type*) [CommSemiring R] [Semiring A] [AddCommMonoid M]
    [Module R M] [Module A M] [Algebra R A] [IsScalarTower R A M] [hM : Finite R M] :
    Finite A M := by
  rw [finite_def, Submodule.fg_def] at hM ⊢
  obtain ⟨S, hSfin, hSgen⟩ := hM
  refine ⟨S, hSfin, eq_top_iff.2 ?_⟩
  have := Submodule.span_le_restrictScalars R A S
  rw [hSgen] at this
  exact this
#align module.finite.of_restrict_scalars_finite Module.Finite.of_restrictScalars_finite

variable {R M}

instance prod [hM : Finite R M] [hN : Finite R N] : Finite R (M × N) :=
  ⟨by
    rw [← Submodule.prod_top]
    exact hM.1.prod hN.1⟩
#align module.finite.prod Module.Finite.prod

instance pi {ι : Type*} {M : ι → Type*} [_root_.Finite ι] [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] [h : ∀ i, Finite R (M i)] : Finite R (∀ i, M i) :=
  ⟨by
    rw [← Submodule.pi_top]
    exact Submodule.fg_pi fun i => (h i).1⟩
#align module.finite.pi Module.Finite.pi

theorem equiv [Finite R M] (e : M ≃ₗ[R] N) : Finite R N :=
  of_surjective (e : M →ₗ[R] N) e.surjective
#align module.finite.equiv Module.Finite.equiv

theorem equiv_iff (e : M ≃ₗ[R] N) : Finite R M ↔ Finite R N :=
  ⟨fun _ ↦ equiv e, fun _ ↦ equiv e.symm⟩

instance ulift [Finite R M] : Finite R (ULift M) := equiv ULift.moduleEquiv.symm

theorem iff_fg {N : Submodule R M} : Module.Finite R N ↔ N.FG := Module.finite_def.trans (fg_top _)

variable (R M)

instance bot : Module.Finite R (⊥ : Submodule R M) := iff_fg.mpr fg_bot

instance top [Finite R M] : Module.Finite R (⊤ : Submodule R M) := iff_fg.mpr out

variable {M}

/-- The submodule generated by a finite set is `R`-finite. -/
theorem span_of_finite {A : Set M} (hA : Set.Finite A) :
    Module.Finite R (Submodule.span R A) :=
  ⟨(Submodule.fg_top _).mpr ⟨hA.toFinset, hA.coe_toFinset.symm ▸ rfl⟩⟩

/-- The submodule generated by a single element is `R`-finite. -/
instance span_singleton (x : M) : Module.Finite R (R ∙ x) :=
  Module.Finite.span_of_finite R <| Set.finite_singleton _

/-- The submodule generated by a finset is `R`-finite. -/
instance span_finset (s : Finset M) : Module.Finite R (span R (s : Set M)) :=
  ⟨(Submodule.fg_top _).mpr ⟨s, rfl⟩⟩


theorem Module.End.isNilpotent_iff_of_finite {R M : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] [Module.Finite R M] {f : End R M} :
    IsNilpotent f ↔ ∀ m : M, ∃ n : ℕ, (f ^ n) m = 0 := by
  refine ⟨fun ⟨n, hn⟩ m ↦ ⟨n, by simp [hn]⟩, fun h ↦ ?_⟩
  rcases Module.Finite.out (R := R) (M := M) with ⟨S, hS⟩
  choose g hg using h
  use Finset.sup S g
  ext m
  have hm : m ∈ Submodule.span R S := by simp [hS]
  induction hm using Submodule.span_induction'
  · next x hx => exact LinearMap.pow_map_zero_of_le (Finset.le_sup hx) (hg x)
  · simp
  · simp_all
  · simp_all

variable {R}

section Algebra

theorem trans {R : Type*} (A M : Type*) [Semiring R] [Semiring A] [Module R A]
    [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M] :
    ∀ [Finite R A] [Finite A M], Finite R M
  | ⟨⟨s, hs⟩⟩, ⟨⟨t, ht⟩⟩ =>
    ⟨Submodule.fg_def.2
        ⟨Set.image2 (· • ·) (↑s : Set A) (↑t : Set M),
          Set.Finite.image2 _ s.finite_toSet t.finite_toSet, by
          erw [Set.image2_smul, Submodule.span_smul_of_span_eq_top hs (↑t : Set M), ht,
            Submodule.restrictScalars_top]⟩⟩
#align module.finite.trans Module.Finite.trans

lemma of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*} [CommRing A₁] [CommRing B₁]
    [CommRing A₂] [CommRing B₂] [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = RingHom.comp ↑e₂ (algebraMap A₁ B₁))
    [Module.Finite A₁ B₁] : Module.Finite A₂ B₂ := by
  letI := e₁.toRingHom.toAlgebra
  letI := ((algebraMap A₁ B₁).comp e₁.symm.toRingHom).toAlgebra
  haveI : IsScalarTower A₁ A₂ B₁ := IsScalarTower.of_algebraMap_eq
    (fun x ↦ by simp [RingHom.algebraMap_toAlgebra])
  let e : B₁ ≃ₐ[A₂] B₂ :=
    { e₂ with
      commutes' := fun r ↦ by
        simpa [RingHom.algebraMap_toAlgebra] using DFunLike.congr_fun he.symm (e₁.symm r) }
  haveI := Module.Finite.of_restrictScalars_finite A₁ A₂ B₁
  exact Module.Finite.equiv e.toLinearEquiv

end Algebra

end Finite

end Module

/-- Porting note: reminding Lean about this instance for Module.Finite.base_change -/
noncomputable local instance
    [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M] [Module R M] :
    Module A (TensorProduct R A M) :=
  haveI : SMulCommClass R A A := IsScalarTower.to_smulCommClass
  TensorProduct.leftModule

instance Module.Finite.base_change [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M]
    [Module R M] [h : Module.Finite R M] : Module.Finite A (TensorProduct R A M) := by
  classical
    obtain ⟨s, hs⟩ := h.out
    refine ⟨⟨s.image (TensorProduct.mk R A M 1), eq_top_iff.mpr ?_⟩⟩
    rintro x -
    induction x with
    | zero => exact zero_mem _
    | tmul x y =>
      -- Porting note: new TC reminder
      haveI : IsScalarTower R A (TensorProduct R A M) := TensorProduct.isScalarTower_left
      rw [Finset.coe_image, ← Submodule.span_span_of_tower R, Submodule.span_image, hs,
        Submodule.map_top, LinearMap.range_coe]
      change _ ∈ Submodule.span A (Set.range <| TensorProduct.mk R A M 1)
      rw [← mul_one x, ← smul_eq_mul, ← TensorProduct.smul_tmul']
      exact Submodule.smul_mem _ x (Submodule.subset_span <| Set.mem_range_self y)
    | add x y hx hy => exact Submodule.add_mem _ hx hy
#align module.finite.base_change Module.Finite.base_change

instance Module.Finite.tensorProduct [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [hM : Module.Finite R M] [hN : Module.Finite R N] :
    Module.Finite R (TensorProduct R M N) where
  out := (TensorProduct.map₂_mk_top_top_eq_top R M N).subst (hM.out.map₂ _ hN.out)
#align module.finite.tensor_product Module.Finite.tensorProduct

/-- If a free module is finite, then any arbitrary basis is finite. -/
lemma Module.Finite.finite_basis {R M} [Ring R] [Nontrivial R] [AddCommGroup M] [Module R M]
    {ι} [Module.Finite R M] (b : Basis ι R M) :
    _root_.Finite ι :=
  let ⟨s, hs⟩ := ‹Module.Finite R M›
  basis_finite_of_finite_spans (↑s) s.finite_toSet hs b

end ModuleAndAlgebra

namespace Submodule

open Module

variable {R V} [Ring R] [AddCommGroup V] [Module R V]

/-- The sup of two fg submodules is finite. Also see `Submodule.FG.sup`. -/
instance finite_sup (S₁ S₂ : Submodule R V) [h₁ : Module.Finite R S₁]
    [h₂ : Module.Finite R S₂] : Module.Finite R (S₁ ⊔ S₂ : Submodule R V) := by
  rw [finite_def] at *
  exact (fg_top _).2 (((fg_top S₁).1 h₁).sup ((fg_top S₂).1 h₂))

/-- The submodule generated by a finite supremum of finite dimensional submodules is
finite-dimensional.

Note that strictly this only needs `∀ i ∈ s, FiniteDimensional K (S i)`, but that doesn't
work well with typeclass search. -/
instance finite_finset_sup {ι : Type*} (s : Finset ι) (S : ι → Submodule R V)
    [∀ i, Module.Finite R (S i)] : Module.Finite R (s.sup S : Submodule R V) := by
  refine
    @Finset.sup_induction _ _ _ _ s S (fun i => Module.Finite R ↑i) (Module.Finite.bot R V)
      ?_ fun i _ => by infer_instance
  intro S₁ hS₁ S₂ hS₂
  exact Submodule.finite_sup S₁ S₂

/-- The submodule generated by a supremum of finite dimensional submodules, indexed by a finite
sort is finite-dimensional. -/
instance finite_iSup {ι : Sort*} [Finite ι] (S : ι → Submodule R V)
    [∀ i, Module.Finite R (S i)] : Module.Finite R ↑(⨆ i, S i) := by
  cases nonempty_fintype (PLift ι)
  rw [← iSup_plift_down, ← Finset.sup_univ_eq_iSup]
  exact Submodule.finite_finset_sup _ _

end Submodule

section

variable {R V} [Ring R] [AddCommGroup V] [Module R V]

instance Module.Finite.finsupp {ι : Type*} [_root_.Finite ι] [Module.Finite R V] :
    Module.Finite R (ι →₀ V) :=
  Module.Finite.equiv (Finsupp.linearEquivFunOnFinite R V ι).symm

end

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
  letI := g.toAlgebra
  letI := (g.comp f).toAlgebra
  letI : IsScalarTower A B C := RestrictScalars.isScalarTower A B C
  letI : Module.Finite A B := hf
  letI : Module.Finite B C := hg
  exact Module.Finite.trans B C
#align ring_hom.finite.comp RingHom.Finite.comp

theorem of_comp_finite {f : A →+* B} {g : B →+* C} (h : (g.comp f).Finite) : g.Finite := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := (g.comp f).toAlgebra
  letI : IsScalarTower A B C := RestrictScalars.isScalarTower A B C
  letI : Module.Finite A C := h
  exact Module.Finite.of_restrictScalars_finite A B C
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

instance Subalgebra.finite_bot {F E : Type*} [CommSemiring F] [Semiring E] [Algebra F E] :
    Module.Finite F (⊥ : Subalgebra F E) := Module.Finite.range (Algebra.linearMap F E)
