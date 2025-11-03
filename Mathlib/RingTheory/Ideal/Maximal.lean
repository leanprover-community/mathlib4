/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Span

/-!

# Ideals over a ring

This file contains an assortment of definitions and results for `Ideal R`,
the type of (left) ideals over a ring `R`.
Note that over commutative rings, left ideals and two-sided ideals are equivalent.

## Implementation notes

`Ideal R` is implemented using `Submodule R R`, where `•` is interpreted as `*`.

## TODO

Support right ideals, and two-sided ideals over non-commutative rings.
-/


universe u v w

variable {α : Type u} {β : Type v} {F : Type w}

open Set Function

open Pointwise

section Semiring

namespace Ideal

variable [Semiring α] (I : Ideal α) {a b : α}

/-- An ideal is maximal if it is maximal in the collection of proper ideals. -/
class IsMaximal (I : Ideal α) : Prop where
  /-- The maximal ideal is a coatom in the ordering on ideals; that is, it is not the entire ring,
  and there are no other proper ideals strictly containing it. -/
  out : IsCoatom I

theorem isMaximal_def {I : Ideal α} : I.IsMaximal ↔ IsCoatom I :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem IsMaximal.ne_top {I : Ideal α} (h : I.IsMaximal) : I ≠ ⊤ :=
  (isMaximal_def.1 h).1

theorem isMaximal_iff {I : Ideal α} :
    I.IsMaximal ↔ (1 : α) ∉ I ∧ ∀ (J : Ideal α) (x), I ≤ J → x ∉ I → x ∈ J → (1 : α) ∈ J := by
  simp_rw [isMaximal_def, SetLike.isCoatom_iff, Ideal.ne_top_iff_one, ← Ideal.eq_top_iff_one]

theorem IsMaximal.eq_of_le {I J : Ideal α} (hI : I.IsMaximal) (hJ : J ≠ ⊤) (IJ : I ≤ J) : I = J :=
  eq_iff_le_not_lt.2 ⟨IJ, fun h => hJ (hI.1.2 _ h)⟩

instance : IsCoatomic (Ideal α) := CompleteLattice.coatomic_of_top_compact isCompactElement_top

theorem IsMaximal.coprime_of_ne {M M' : Ideal α} (hM : M.IsMaximal) (hM' : M'.IsMaximal)
    (hne : M ≠ M') : M ⊔ M' = ⊤ := by
  contrapose! hne with h
  exact hM.eq_of_le hM'.ne_top (le_sup_left.trans_eq (hM'.eq_of_le h le_sup_right).symm)

/-- **Krull's theorem**: if `I` is an ideal that is not the whole ring, then it is included in some
    maximal ideal. -/
theorem exists_le_maximal (I : Ideal α) (hI : I ≠ ⊤) : ∃ M : Ideal α, M.IsMaximal ∧ I ≤ M :=
  let ⟨m, hm⟩ := (eq_top_or_exists_le_coatom I).resolve_left hI
  ⟨m, ⟨⟨hm.1⟩, hm.2⟩⟩

variable (α) in
/-- Krull's theorem: a nontrivial ring has a maximal ideal. -/
theorem exists_maximal [Nontrivial α] : ∃ M : Ideal α, M.IsMaximal :=
  let ⟨I, ⟨hI, _⟩⟩ := exists_le_maximal (⊥ : Ideal α) bot_ne_top
  ⟨I, hI⟩

theorem ne_top_iff_exists_maximal {I : Ideal α} : I ≠ ⊤ ↔ ∃ M : Ideal α, M.IsMaximal ∧ I ≤ M := by
  refine ⟨exists_le_maximal I, ?_⟩
  contrapose!
  rintro rfl _ hMmax
  rw [top_le_iff]
  exact IsMaximal.ne_top hMmax

instance [Nontrivial α] : Nontrivial (Ideal α) := by
  rcases@exists_maximal α _ _ with ⟨M, hM, _⟩
  exact nontrivial_of_ne M ⊤ hM

/-- If P is not properly contained in any maximal ideal then it is not properly contained
  in any proper ideal -/
theorem maximal_of_no_maximal {P : Ideal α}
    (hmax : ∀ m : Ideal α, P < m → ¬IsMaximal m) (J : Ideal α) (hPJ : P < J) : J = ⊤ := by
  by_contra hnonmax
  rcases exists_le_maximal J hnonmax with ⟨M, hM1, hM2⟩
  exact hmax M (lt_of_lt_of_le hPJ hM2) hM1

theorem IsMaximal.exists_inv {I : Ideal α} (hI : I.IsMaximal) {x} (hx : x ∉ I) :
    ∃ y, ∃ i ∈ I, y * x + i = 1 := by
  obtain ⟨H₁, H₂⟩ := isMaximal_iff.1 hI
  rcases mem_span_insert.1
      (H₂ (span (insert x I)) x (Set.Subset.trans (subset_insert _ _) subset_span) hx
        (subset_span (mem_insert _ _))) with
    ⟨y, z, hz, hy⟩
  refine ⟨y, z, ?_, hy.symm⟩
  rwa [← span_eq I]

theorem sInf_isPrime_of_isChain {s : Set (Ideal α)} (hs : s.Nonempty) (hs' : IsChain (· ≤ ·) s)
    (H : ∀ p ∈ s, p.IsPrime) : (sInf s).IsPrime :=
  ⟨fun e =>
    let ⟨x, hx⟩ := hs
    (H x hx).ne_top (eq_top_iff.mpr (e.symm.trans_le (sInf_le hx))),
    fun e =>
    or_iff_not_imp_left.mpr fun hx => by
      rw [Ideal.mem_sInf] at hx e ⊢
      push_neg at hx
      obtain ⟨I, hI, hI'⟩ := hx
      intro J hJ
      rcases hs'.total hI hJ with h | h
      · exact h (((H I hI).mem_or_mem (e hI)).resolve_left hI')
      · exact ((H J hJ).mem_or_mem (e hJ)).resolve_left fun x => hI' <| h x⟩

end Ideal

end Semiring

section CommSemiring

variable {a b : α}

-- A separate namespace definition is needed because the variables were historically in a different
-- order.
namespace Ideal

variable [CommSemiring α] (I : Ideal α)

theorem span_singleton_prime {p : α} (hp : p ≠ 0) : IsPrime (span ({p} : Set α)) ↔ Prime p := by
  simp [isPrime_iff, Prime, span_singleton_eq_top, hp, mem_span_singleton]

theorem IsMaximal.isPrime {I : Ideal α} (H : I.IsMaximal) : I.IsPrime :=
  ⟨H.1.1, @fun x y hxy =>
    or_iff_not_imp_left.2 fun hx => by
      let J : Ideal α := Submodule.span α (insert x ↑I)
      have IJ : I ≤ J := Set.Subset.trans (subset_insert _ _) subset_span
      have xJ : x ∈ J := Ideal.subset_span (Set.mem_insert x I)
      obtain ⟨_, oJ⟩ := isMaximal_iff.1 H
      specialize oJ J x IJ hx xJ
      rcases Submodule.mem_span_insert.mp oJ with ⟨a, b, h, oe⟩
      obtain F : y * 1 = y * (a • x + b) := congr_arg (fun g : α => y * g) oe
      rw [← mul_one y, F, mul_add, mul_comm, smul_eq_mul, mul_assoc]
      refine Submodule.add_mem I (I.mul_mem_left a hxy) (Submodule.smul_mem I y ?_)
      rwa [Submodule.span_eq] at h⟩

-- see Note [lower instance priority]
instance (priority := 100) IsMaximal.isPrime' (I : Ideal α) : ∀ [_H : I.IsMaximal], I.IsPrime :=
  @IsMaximal.isPrime _ _ _

theorem exists_disjoint_powers_of_span_eq_top (s : Set α) (hs : span s = ⊤) (I : Ideal α)
    (hI : I ≠ ⊤) : ∃ r ∈ s, Disjoint (I : Set α) (Submonoid.powers r) := by
  have ⟨M, hM, le⟩ := exists_le_maximal I hI
  have := hM.1.1
  rw [Ne, eq_top_iff, ← hs, span_le, Set.not_subset] at this
  have ⟨a, has, haM⟩ := this
  exact ⟨a, has, Set.disjoint_left.mpr fun x hx ⟨n, hn⟩ ↦
    haM (hM.isPrime.mem_of_pow_mem _ (le <| hn ▸ hx))⟩

theorem span_singleton_lt_span_singleton [IsDomain α] {x y : α} :
    span ({x} : Set α) < span ({y} : Set α) ↔ DvdNotUnit y x := by
  rw [lt_iff_le_not_ge, span_singleton_le_span_singleton, span_singleton_le_span_singleton,
    dvd_and_not_dvd_iff]

lemma isPrime_of_maximally_disjoint (I : Ideal α)
    (S : Submonoid α)
    (disjoint : Disjoint (I : Set α) S)
    (maximally_disjoint : ∀ (J : Ideal α), I < J → ¬ Disjoint (J : Set α) S) :
    I.IsPrime where
  ne_top' := by
    rintro rfl
    have : 1 ∈ (S : Set α) := S.one_mem
    simp_all
  mem_or_mem' {x y} hxy := by
    by_contra! rid
    have hx := maximally_disjoint (I ⊔ span {x}) (Submodule.lt_sup_iff_notMem.mpr rid.1)
    have hy := maximally_disjoint (I ⊔ span {y}) (Submodule.lt_sup_iff_notMem.mpr rid.2)
    simp only [Set.not_disjoint_iff, SetLike.mem_coe, Submodule.mem_sup,
      mem_span_singleton] at hx hy
    obtain ⟨s₁, ⟨i₁, hi₁, ⟨_, ⟨r₁, rfl⟩, hr₁⟩⟩, hs₁⟩ := hx
    obtain ⟨s₂, ⟨i₂, hi₂, ⟨_, ⟨r₂, rfl⟩, hr₂⟩⟩, hs₂⟩ := hy
    refine disjoint.ne_of_mem
      (I.add_mem (I.mul_mem_left (i₁ + x * r₁) hi₂) <| I.add_mem (I.mul_mem_right (y * r₂) hi₁) <|
        I.mul_mem_right (r₁ * r₂) hxy)
      (S.mul_mem hs₁ hs₂) ?_
    rw [← hr₁, ← hr₂]
    ring

theorem exists_le_prime_disjoint (S : Submonoid α) (disjoint : Disjoint (I : Set α) S) :
    ∃ p : Ideal α, p.IsPrime ∧ I ≤ p ∧ Disjoint (p : Set α) S := by
  have ⟨p, hIp, hp⟩ := zorn_le_nonempty₀ {p : Ideal α | Disjoint (p : Set α) S}
    (fun c hc hc' x hx ↦ ?_) I disjoint
  · exact ⟨p, isPrime_of_maximally_disjoint _ _ hp.1 (fun _ ↦ hp.not_prop_of_gt), hIp, hp.1⟩
  cases isEmpty_or_nonempty c
  · exact ⟨I, disjoint, fun J hJ ↦ isEmptyElim (⟨J, hJ⟩ : c)⟩
  refine ⟨sSup c, Set.disjoint_left.mpr fun x hx ↦ ?_, fun _ ↦ le_sSup⟩
  have ⟨p, hp⟩ := (Submodule.mem_iSup_of_directed _ hc'.directed).mp (sSup_eq_iSup' c ▸ hx)
  exact Set.disjoint_left.mp (hc p.2) hp

theorem exists_le_prime_notMem_of_isIdempotentElem (a : α) (ha : IsIdempotentElem a) (haI : a ∉ I) :
    ∃ p : Ideal α, p.IsPrime ∧ I ≤ p ∧ a ∉ p :=
  have : Disjoint (I : Set α) (Submonoid.powers a) := Set.disjoint_right.mpr <| by
    rw [ha.coe_powers]
    rintro _ (rfl | rfl)
    exacts [I.ne_top_iff_one.mp (ne_of_mem_of_not_mem' Submodule.mem_top haI).symm, haI]
  have ⟨p, h1, h2, h3⟩ := exists_le_prime_disjoint _ _ this
  ⟨p, h1, h2, Set.disjoint_right.mp h3 (Submonoid.mem_powers a)⟩

@[deprecated (since := "2025-05-24")]
alias exists_le_prime_nmem_of_isIdempotentElem := exists_le_prime_notMem_of_isIdempotentElem

section IsPrincipalIdealRing

variable [IsPrincipalIdealRing α]

theorem isPrime_iff_of_isPrincipalIdealRing {P : Ideal α} (hP : P ≠ ⊥) :
    P.IsPrime ↔ ∃ p, Prime p ∧ P = span {p} where
  mp h := by
    obtain ⟨p, rfl⟩ := Submodule.IsPrincipal.principal P
    exact ⟨p, (span_singleton_prime (by simp [·] at hP)).mp h, rfl⟩
  mpr := by
    rintro ⟨p, hp, rfl⟩
    rwa [span_singleton_prime (by simp [hp.ne_zero])]

theorem isPrime_iff_of_isPrincipalIdealRing_of_noZeroDivisors [NoZeroDivisors α] [Nontrivial α]
    {P : Ideal α} : P.IsPrime ↔ P = ⊥ ∨ ∃ p, Prime p ∧ P = span {p} := by
  rw [or_iff_not_imp_left, ← forall_congr' isPrime_iff_of_isPrincipalIdealRing,
    ← or_iff_not_imp_left, or_iff_right_of_imp]
  rintro rfl; exact bot_prime

end IsPrincipalIdealRing

end Ideal

end CommSemiring

section DivisionSemiring

variable {K : Type u} [DivisionSemiring K] (I : Ideal K)

namespace Ideal

theorem bot_isMaximal : IsMaximal (⊥ : Ideal K) :=
  ⟨⟨fun h => absurd ((eq_top_iff_one (⊤ : Ideal K)).mp rfl) (by rw [← h]; simp), fun I hI =>
      or_iff_not_imp_left.mp (eq_bot_or_top I) (ne_of_gt hI)⟩⟩

end Ideal

end DivisionSemiring
