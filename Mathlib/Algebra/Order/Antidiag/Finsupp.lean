/-
Copyright (c) 2023 Antoine Chambert-Loir and María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Eric Wieser, Bhavik Mehta,
  Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Order.Antidiag.Pi

/-!
# Antidiagonal of finitely supported functions as finsets

This file defines the finset of finitely functions summing to a specific value on a finset. Such
finsets should be thought of as the "antidiagonals" in the space of finitely supported functions.

Precisely, for a commutative monoid `μ` with antidiagonals (see `Finset.HasAntidiagonal`),
`Finset.finsuppAntidiagonal s n` is the finset of all finitely supported functions `f : ι →₀ μ` with
support contained in `s` and such that the sum of its values equals `n : μ`.

We define it using `Finset.piAntidiagonal s n`, the corresponding antidiagonal in `ι → μ`.

## Main declarations

* `Finset.finsuppAntidiagonal s n`: Finset of all finitely supported functions `f : ι →₀ μ`
  with support contained in `s` and such that the sum of its values equals `n : μ`.

-/

@[expose] public section

assert_not_exists Field

open Finsupp Function

variable {ι μ μ' : Type*}

namespace Finset
section AddCommMonoid
variable [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {s : Finset ι}
  {n : μ} {f : ι →₀ μ}

/-- The finset of functions `ι →₀ μ` with support contained in `s` and sum equal to `n`. -/
def finsuppAntidiagonal (s : Finset ι) (n : μ) : Finset (ι →₀ μ) :=
  (piAntidiagonal s n).attach.map ⟨fun f ↦ ⟨s.filter (f.1 · ≠ 0), f.1, by
    simpa using (mem_piAntidiagonal.1 f.2).2⟩, fun _ _ hfg ↦ Subtype.ext (congr_arg (⇑) hfg)⟩

@[deprecated (since := "2026-09-06")] alias finsuppAntidiag := finsuppAntidiagonal

@[simp] lemma mem_finsuppAntidiagonal :
    f ∈ finsuppAntidiagonal s n ↔ s.sum f = n ∧ f.support ⊆ s := by
  simp [finsuppAntidiagonal, ← DFunLike.coe_fn_eq, subset_iff]

@[deprecated (since := "2026-09-06")] alias mem_finsuppAntidiag := mem_finsuppAntidiagonal

lemma mem_finsuppAntidiagonal' :
    f ∈ finsuppAntidiagonal s n ↔ f.sum (fun _ x ↦ x) = n ∧ f.support ⊆ s := by
  simp only [mem_finsuppAntidiagonal, and_congr_left_iff]
  rintro hf
  rw [sum_of_support_subset (N := μ) f hf (fun _ x ↦ x) fun _ _ ↦ rfl]

@[deprecated (since := "2026-09-06")] alias mem_finsuppAntidiag' := mem_finsuppAntidiagonal'

@[simp] lemma finsuppAntidiagonal_empty_zero :
    finsuppAntidiagonal (∅ : Finset ι) (0 : μ) = {0} := by
  ext f; simp

@[deprecated (since := "2026-09-06")]
alias finsuppAntidiag_empty_zero := finsuppAntidiagonal_empty_zero

@[simp] lemma finsuppAntidiagonal_empty_of_ne_zero (hn : n ≠ 0) :
    finsuppAntidiagonal (∅ : Finset ι) n = ∅ :=
  eq_empty_of_forall_notMem (by simp [hn.symm])

@[deprecated (since := "2026-09-06")]
alias finsuppAntidiag_empty_of_ne_zero := finsuppAntidiagonal_empty_of_ne_zero

lemma finsuppAntidiagonal_empty (n : μ) :
    finsuppAntidiagonal (∅ : Finset ι) n = if n = 0 then {0} else ∅ := by
  split_ifs with hn <;> simp [*]

@[deprecated (since := "2026-09-06")] alias finsuppAntidiag_empty := finsuppAntidiagonal_empty

theorem mem_finsuppAntidiagonal_insert {a : ι} {s : Finset ι}
    (h : a ∉ s) (n : μ) {f : ι →₀ μ} :
    f ∈ finsuppAntidiagonal (insert a s) n ↔
      ∃ m ∈ antidiagonal n, ∃ (g : ι →₀ μ),
        f = Finsupp.update g a m.1 ∧ g ∈ finsuppAntidiagonal s m.2 := by
  simp only [mem_finsuppAntidiagonal, mem_antidiagonal, Prod.exists, sum_insert h]
  constructor
  · rintro ⟨rfl, hsupp⟩
    refine ⟨_, _, rfl, Finsupp.erase a f, ?_, ?_, ?_⟩
    · rw [update_erase_eq_update, Finsupp.update_self]
    · apply sum_congr rfl
      intro x hx
      rw [Finsupp.erase_ne (ne_of_mem_of_not_mem hx h)]
    · rwa [support_erase, ← subset_insert_iff]
  · rintro ⟨n1, n2, rfl, g, rfl, rfl, hgsupp⟩
    refine ⟨?_, (support_update_subset _ _).trans (insert_subset_insert a hgsupp)⟩
    simp only [coe_update]
    apply congr_arg₂
    · rw [Function.update_self]
    · apply sum_congr rfl
      intro x hx
      rw [update_of_ne (ne_of_mem_of_not_mem hx h) n1 ⇑g]

@[deprecated (since := "2026-09-06")]
alias mem_finsuppAntidiag_insert := mem_finsuppAntidiagonal_insert

set_option backward.isDefEq.respectTransparency false in
theorem finsuppAntidiagonal_insert {a : ι} {s : Finset ι}
    (h : a ∉ s) (n : μ) :
    finsuppAntidiagonal (insert a s) n = (antidiagonal n).biUnion
      (fun p : μ × μ =>
        (finsuppAntidiagonal s p.snd).attach.map
        ⟨fun f => Finsupp.update f.val a p.fst,
        (fun ⟨f, hf⟩ ⟨g, hg⟩ hfg => Subtype.ext <| by
          simp only [mem_finsuppAntidiagonal] at hf hg
          simp only [DFunLike.ext_iff] at hfg ⊢
          intro x
          obtain rfl | hx := eq_or_ne x a
          · replace hf := mt (hf.2 ·) h
            replace hg := mt (hg.2 ·) h
            rw [notMem_support_iff.mp hf, notMem_support_iff.mp hg]
          · simpa only [coe_update, Function.update, dite_eq_right hx] using hfg x)⟩) := by
  ext f
  rw [mem_finsuppAntidiagonal_insert h, mem_biUnion]
  simp_rw [mem_map, mem_attach, true_and, Subtype.exists, Embedding.coeFn_mk, exists_prop, and_comm,
    eq_comm]

@[deprecated (since := "2026-09-06")] alias finsuppAntidiag_insert := finsuppAntidiagonal_insert

@[gcongr]
theorem finsuppAntidiagonal_mono {s t : Finset ι} (h : s ⊆ t) (n : μ) :
    finsuppAntidiagonal s n ⊆ finsuppAntidiagonal t n := by
  intro a
  simp_rw [mem_finsuppAntidiagonal']
  rintro ⟨hsum, hmem⟩
  exact ⟨hsum, hmem.trans h⟩

@[deprecated (since := "2026-09-06")] alias finsuppAntidiag_mono := finsuppAntidiagonal_mono

variable [AddCommMonoid μ'] [HasAntidiagonal μ'] [DecidableEq μ']

set_option backward.isDefEq.respectTransparency false in
-- This should work under the assumption that e is an embedding and an AddHom
lemma mapRange_finsuppAntidiagonal_subset {e : μ ≃+ μ'} {s : Finset ι} {n : μ} :
    (finsuppAntidiagonal s n).map (mapRange.addEquiv e).toEmbedding ⊆
      finsuppAntidiagonal s (e n) := by
  intro f
  simp only [mem_map, mem_finsuppAntidiagonal']
  rintro ⟨g, ⟨hsum, hsupp⟩, rfl⟩
  simp only [AddEquiv.toEquiv_eq_coe, mapRange.addEquiv_toEquiv, Equiv.coe_toEmbedding,
    mapRange.equiv_apply, EquivLike.coe_coe]
  constructor
  · rw [sum_mapRange_index (fun _ ↦ rfl), ← hsum, _root_.map_finsuppSum]
  · exact subset_trans (support_mapRange) hsupp

@[deprecated (since := "2026-09-06")]
alias mapRange_finsuppAntidiag_subset := mapRange_finsuppAntidiagonal_subset

lemma mapRange_finsuppAntidiagonal_eq {e : μ ≃+ μ'} {s : Finset ι} {n : μ} :
    (finsuppAntidiagonal s n).map (mapRange.addEquiv e).toEmbedding =
      finsuppAntidiagonal s (e n) := by
  ext f
  constructor
  · apply mapRange_finsuppAntidiagonal_subset
  · set h := (mapRange.addEquiv e).toEquiv with hh
    intro hf
    have : n = e.symm (e n) := (AddEquiv.eq_symm_apply e).mpr rfl
    rw [mem_map_equiv, this]
    apply mapRange_finsuppAntidiagonal_subset
    rw [← mem_map_equiv]
    convert! hf
    rw [map_map, hh]
    convert! map_refl
    apply Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding

@[deprecated (since := "2026-09-06")]
alias mapRange_finsuppAntidiag_eq := mapRange_finsuppAntidiagonal_eq

end AddCommMonoid

section CanonicallyOrderedAddCommMonoid
variable [DecidableEq ι] [DecidableEq μ] [AddCommMonoid μ] [PartialOrder μ]
  [CanonicallyOrderedAdd μ] [HasAntidiagonal μ]

@[simp] lemma finsuppAntidiagonal_zero (s : Finset ι) : finsuppAntidiagonal s (0 : μ) = {0} := by
  ext f; simp [finsuppAntidiagonal, ← DFunLike.coe_fn_eq (g := f), eq_comm]

@[deprecated (since := "2026-09-06")] alias finsuppAntidiag_zero := finsuppAntidiagonal_zero

end CanonicallyOrderedAddCommMonoid
end Finset
