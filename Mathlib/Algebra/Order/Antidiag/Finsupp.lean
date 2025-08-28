/-
Copyright (c) 2023 Antoine Chambert-Loir and María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Eric Wieser, Bhavik Mehta,
  Yaël Dillies
-/
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Finsupp.Basic

/-!
# Antidiagonal of finitely supported functions as finsets

This file defines the finset of finitely functions summing to a specific value on a finset. Such
finsets should be thought of as the "antidiagonals" in the space of finitely supported functions.

Precisely, for a commutative monoid `μ` with antidiagonals (see `Finset.HasAntidiagonal`),
`Finset.finsuppAntidiag s n` is the finset of all finitely supported functions `f : ι →₀ μ` with
support contained in `s` and such that the sum of its values equals `n : μ`.

We define it using `Finset.piAntidiag s n`, the corresponding antidiagonal in `ι → μ`.

## Main declarations

* `Finset.finsuppAntidiag s n`: Finset of all finitely supported functions `f : ι →₀ μ` with support
  contained in `s` and such that the sum of its values equals `n : μ`.

-/

open Finsupp Function

variable {ι μ μ' : Type*}

namespace Finset
section AddCommMonoid
variable [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {s : Finset ι}
  {n : μ} {f : ι →₀ μ}

/-- The finset of functions `ι →₀ μ` with support contained in `s` and sum equal to `n`. -/
def finsuppAntidiag (s : Finset ι) (n : μ) : Finset (ι →₀ μ) :=
  (piAntidiag s n).attach.map ⟨fun f ↦ ⟨s.filter (f.1 · ≠ 0), f.1, by
    simpa using (mem_piAntidiag.1 f.2).2⟩, fun _ _ hfg ↦ Subtype.ext (congr_arg (⇑) hfg)⟩

@[simp] lemma mem_finsuppAntidiag : f ∈ finsuppAntidiag s n ↔ s.sum f = n ∧ f.support ⊆ s := by
  simp [finsuppAntidiag, ← DFunLike.coe_fn_eq, subset_iff]

lemma mem_finsuppAntidiag' :
    f ∈ finsuppAntidiag s n ↔ f.sum (fun _ x ↦ x) = n ∧ f.support ⊆ s := by
  simp only [mem_finsuppAntidiag, and_congr_left_iff]
  rintro hf
  rw [sum_of_support_subset (N := μ) f hf (fun _ x ↦ x) fun _ _ ↦ rfl]

@[simp] lemma finsuppAntidiag_empty_zero : finsuppAntidiag (∅ : Finset ι) (0 : μ) = {0} := by
  ext f; simp [finsuppAntidiag, ← DFunLike.coe_fn_eq (g := f), eq_comm]

@[simp] lemma finsuppAntidiag_empty_of_ne_zero (hn : n ≠ 0) :
    finsuppAntidiag (∅ : Finset ι) n = ∅ :=
  eq_empty_of_forall_notMem (by simp [hn.symm])

lemma finsuppAntidiag_empty (n : μ) :
    finsuppAntidiag (∅ : Finset ι) n = if n = 0 then {0} else ∅ := by split_ifs with hn <;> simp [*]

theorem mem_finsuppAntidiag_insert {a : ι} {s : Finset ι}
    (h : a ∉ s) (n : μ) {f : ι →₀ μ} :
    f ∈ finsuppAntidiag (insert a s) n ↔
      ∃ m ∈ antidiagonal n, ∃ (g : ι →₀ μ),
        f = Finsupp.update g a m.1 ∧ g ∈ finsuppAntidiag s m.2 := by
  simp only [mem_finsuppAntidiag, mem_antidiagonal, Prod.exists, sum_insert h]
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

theorem finsuppAntidiag_insert {a : ι} {s : Finset ι}
    (h : a ∉ s) (n : μ) :
    finsuppAntidiag (insert a s) n = (antidiagonal n).biUnion
      (fun p : μ × μ =>
        (finsuppAntidiag s p.snd).attach.map
        ⟨fun f => Finsupp.update f.val a p.fst,
        (fun ⟨f, hf⟩ ⟨g, hg⟩ hfg => Subtype.ext <| by
          simp only [mem_finsuppAntidiag] at hf hg
          simp only [DFunLike.ext_iff] at hfg ⊢
          intro x
          obtain rfl | hx := eq_or_ne x a
          · replace hf := mt (hf.2 ·) h
            replace hg := mt (hg.2 ·) h
            rw [notMem_support_iff.mp hf, notMem_support_iff.mp hg]
          · simpa only [coe_update, Function.update, dif_neg hx] using hfg x)⟩) := by
  ext f
  rw [mem_finsuppAntidiag_insert h, mem_biUnion]
  simp_rw [mem_map, mem_attach, true_and, Subtype.exists, Embedding.coeFn_mk, exists_prop, and_comm,
    eq_comm]

variable [AddCommMonoid μ'] [HasAntidiagonal μ'] [DecidableEq μ']

-- This should work under the assumption that e is an embedding and an AddHom
lemma mapRange_finsuppAntidiag_subset {e : μ ≃+ μ'} {s : Finset ι} {n : μ} :
    (finsuppAntidiag s n).map (mapRange.addEquiv e).toEmbedding ⊆ finsuppAntidiag s (e n) := by
  intro f
  simp only [mem_map, mem_finsuppAntidiag']
  rintro ⟨g, ⟨hsum, hsupp⟩, rfl⟩
  simp only [AddEquiv.toEquiv_eq_coe, mapRange.addEquiv_toEquiv, Equiv.coe_toEmbedding,
    mapRange.equiv_apply, EquivLike.coe_coe]
  constructor
  · rw [sum_mapRange_index (fun _ ↦ rfl), ← hsum, _root_.map_finsuppSum]
  · exact subset_trans (support_mapRange) hsupp

lemma mapRange_finsuppAntidiag_eq {e : μ ≃+ μ'} {s : Finset ι} {n : μ} :
    (finsuppAntidiag s n).map (mapRange.addEquiv e).toEmbedding = finsuppAntidiag s (e n) := by
  ext f
  constructor
  · apply mapRange_finsuppAntidiag_subset
  · set h := (mapRange.addEquiv e).toEquiv with hh
    intro hf
    have : n = e.symm (e n) := (AddEquiv.eq_symm_apply e).mpr rfl
    rw [mem_map_equiv, this]
    apply mapRange_finsuppAntidiag_subset
    rw [← mem_map_equiv]
    convert hf
    rw [map_map, hh]
    convert map_refl
    apply Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding

end AddCommMonoid

section CanonicallyOrderedAddCommMonoid
variable [DecidableEq ι] [DecidableEq μ] [AddCommMonoid μ] [PartialOrder μ]
  [CanonicallyOrderedAdd μ] [HasAntidiagonal μ]

@[simp] lemma finsuppAntidiag_zero (s : Finset ι) : finsuppAntidiag s (0 : μ) = {0} := by
  ext f; simp [finsuppAntidiag, ← DFunLike.coe_fn_eq (g := f), -mem_piAntidiag, eq_comm]

end CanonicallyOrderedAddCommMonoid
end Finset
