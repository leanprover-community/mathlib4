/-
Copyright (c) 2023 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pi

/-!
# Fin-indexed tuples of finsets
-/

open Fin Fintype

namespace Fin
variable {n : ℕ} {α : Fin (n + 1) → Type*} {f : ∀ i, α i} {s : ∀ i, Finset (α i)} {p : Fin (n + 1)}

lemma mem_piFinset_iff_zero_tail :
    f ∈ Fintype.piFinset s ↔ f 0 ∈ s 0 ∧ tail f ∈ piFinset (tail s) := by
  simp only [Fintype.mem_piFinset, forall_fin_succ, tail]

lemma mem_piFinset_iff_last_init :
    f ∈ piFinset s ↔ f (last n) ∈ s (last n) ∧ init f ∈ piFinset (init s) := by
  simp only [Fintype.mem_piFinset, forall_fin_succ', init, and_comm]

lemma mem_piFinset_iff_pivot_removeNth (p : Fin (n + 1)) :
    f ∈ piFinset s ↔ f p ∈ s p ∧ removeNth p f ∈ piFinset (removeNth p s) := by
  simp only [Fintype.mem_piFinset, forall_iff_succAbove p, removeNth]

lemma cons_mem_piFinset_cons {x_zero : α 0} {x_tail : (i : Fin n) → α i.succ}
    {s_zero : Finset (α 0)} {s_tail : (i : Fin n) → Finset (α i.succ)} :
    cons x_zero x_tail ∈ piFinset (cons s_zero s_tail) ↔
      x_zero ∈ s_zero ∧ x_tail ∈ piFinset s_tail := by
  simp_rw [mem_piFinset_iff_zero_tail, cons_zero, tail_cons]

lemma snoc_mem_piFinset_snoc {x_last : α (last n)} {x_init : (i : Fin n) → α i.castSucc}
    {s_last : Finset (α (last n))} {s_init : (i : Fin n) → Finset (α i.castSucc)} :
    snoc x_init x_last ∈ piFinset (snoc s_init s_last) ↔
      x_last ∈ s_last ∧ x_init ∈ piFinset s_init := by
  simp_rw [mem_piFinset_iff_last_init, init_snoc, snoc_last]

lemma insertNth_mem_piFinset_insertNth {x_pivot : α p} {x_remove : ∀ i, α (succAbove p i)}
    {s_pivot : Finset (α p)} {s_remove : ∀ i, Finset (α (succAbove p i))} :
    insertNth p x_pivot x_remove ∈ piFinset (insertNth p s_pivot s_remove) ↔
      x_pivot ∈ s_pivot ∧ x_remove ∈ piFinset s_remove := by
  simp [mem_piFinset_iff_pivot_removeNth p]

end Fin

namespace Finset
variable {n : ℕ} {α : Fin (n + 1) → Type*} {p : Fin (n + 1)} (S : ∀ i, Finset (α i))

lemma map_consEquiv_filter_piFinset (P : (∀ i, α (succ i)) → Prop) [DecidablePred P] :
    {r ∈ piFinset S | P (tail r)}.map (consEquiv α).symm.toEmbedding =
      S 0 ×ˢ {r ∈ piFinset (tail S) | P r} := by
  unfold tail; ext; simp [Fin.forall_iff_succ, and_assoc]

lemma map_snocEquiv_filter_piFinset (P : (∀ i, α (castSucc i)) → Prop) [DecidablePred P] :
    {r ∈ piFinset S | P (init r)}.map (snocEquiv α).symm.toEmbedding =
      S (last _) ×ˢ {r ∈ piFinset (init S) | P r} := by
  unfold init; ext; simp [Fin.forall_iff_castSucc, and_assoc]

lemma map_insertNthEquiv_filter_piFinset (P : (∀ i, α (p.succAbove i)) → Prop) [DecidablePred P] :
    {r ∈ piFinset S | P (p.removeNth r)}.map (p.insertNthEquiv α).symm.toEmbedding =
      S p ×ˢ {r ∈ piFinset (p.removeNth  S) | P r} := by
  unfold removeNth; ext; simp [Fin.forall_iff_succAbove p, and_assoc]

lemma filter_piFinset_eq_map_consEquiv (P : (∀ i, α (succ i)) → Prop) [DecidablePred P] :
    {r ∈ piFinset S | P (tail r)} =
      (S 0 ×ˢ {r ∈ piFinset (tail S) | P r}).map (consEquiv α).toEmbedding := by
  simp [← map_consEquiv_filter_piFinset, map_map]

lemma filter_piFinset_eq_map_snocEquiv (P : (∀ i, α (castSucc i)) → Prop) [DecidablePred P] :
    {r ∈ piFinset S | P (init r)} =
      (S (last _) ×ˢ {r ∈ piFinset (init S) | P r}).map (snocEquiv α).toEmbedding := by
  simp [← map_snocEquiv_filter_piFinset, map_map]

lemma filter_piFinset_eq_map_insertNthEquiv (P : (∀ i, α (p.succAbove i)) → Prop)
    [DecidablePred P] :
    {r ∈ piFinset S | P (p.removeNth r)} =
      (S p ×ˢ {r ∈ piFinset (p.removeNth  S) | P r}).map (p.insertNthEquiv α).toEmbedding := by
  simp [← map_insertNthEquiv_filter_piFinset, map_map]

lemma card_consEquiv_filter_piFinset (P : (∀ i, α (succ i)) → Prop) [DecidablePred P] :
    {r ∈ piFinset S | P (tail r)}.card = (S 0).card * {r ∈ piFinset (tail S) | P r}.card := by
  rw [← card_product, ← map_consEquiv_filter_piFinset, card_map]

lemma card_snocEquiv_filter_piFinset (P : (∀ i, α (castSucc i)) → Prop) [DecidablePred P] :
    {r ∈ piFinset S | P (init r)}.card =
      (S (last _)).card * {r ∈ piFinset (init S) | P r}.card := by
  rw [← card_product, ← map_snocEquiv_filter_piFinset, card_map]

lemma card_insertNthEquiv_filter_piFinset (P : (∀ i, α (p.succAbove i)) → Prop) [DecidablePred P] :
    {r ∈ piFinset S | P (p.removeNth r)}.card =
      (S p).card * {r ∈ piFinset (p.removeNth  S) | P r}.card := by
  rw [← card_product, ← map_insertNthEquiv_filter_piFinset, card_map]

end Finset
