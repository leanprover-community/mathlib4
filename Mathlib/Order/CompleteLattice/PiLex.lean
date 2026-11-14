/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.PiLex

/-!
# Complete linear order instance on lexicographically ordered pi types

We show that for `α` a family of complete linear orders, the lexicographically ordered type of
dependent functions `Πₗ i, α i` is itself a complete linear order.
-/

public section

variable {ι : Type*} {α : ι → Type*} [LinearOrder ι] [∀ i, CompleteLinearOrder (α i)]

namespace Pi

/-! ### Lexicographic ordering -/

namespace Lex

private def inf [WellFoundedLT ι] (s : Set (Πₗ i, α i)) (i : ι) : α i :=
  ⨅ e : {e ∈ s | ∀ j < i, e.ofLex j = inf s j}, e.1.ofLex i
termination_by wellFounded_lt.wrap i

variable [WellFoundedLT ι]

@[no_expose]
instance : InfSet (Πₗ i, α i) where
  sInf s := Lex.toLex (inf s)

theorem sInf_apply (s : Set (Πₗ i, α i)) (i : ι) :
    (sInf s).ofLex i = ⨅ e : {e ∈ s | ∀ j < i, e.ofLex j = (sInf s).ofLex j}, e.1.ofLex i := by
  -- This still works without excluding `iInf_of_isEmpty`, but very slowly
  simp [sInf, inf, -iInf_of_isEmpty]

theorem sInf_apply_le {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
    (he : e ∈ s) (h : ∀ j < i, e.ofLex j = (sInf s).ofLex j) : (sInf s).ofLex i ≤ e.ofLex i := by
  rw [sInf_apply]
  exact sInf_le ⟨⟨e, he, h⟩, rfl⟩

theorem le_sInf_apply {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
    (h : ∀ f ∈ s, (∀ j < i, f.ofLex j = (sInf s).ofLex j) → e.ofLex i ≤ f.ofLex i) :
    e.ofLex i ≤ (sInf s).ofLex i := by
  rw [sInf_apply]
  apply le_sInf
  grind

private theorem isGLB_sInf {s : Set (Πₗ i, α i)} : IsGLB s (sInf s) := by
  refine ⟨fun e he ↦ ?_, fun e h ↦ ?_⟩
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
    exact ha.2.not_ge (sInf_apply_le he ha.1)
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
    refine ha.2.not_ge <| le_sInf_apply fun f hf hf' ↦ apply_le_of_toLex (h hf) ?_
    simp_all

-- TODO: figure out how to use `to_dual` here

@[no_expose]
instance : SupSet (Πₗ i, α i) where
  sSup s := sInf (α := Πₗ i, (α i)ᵒᵈ) s

theorem sSup_apply (s : Set (Πₗ i, α i)) (i : ι) :
    (sSup s).ofLex i = ⨆ e : {e ∈ s | ∀ j < i, e.ofLex j = (sSup s).ofLex j}, e.1.ofLex i :=
  sInf_apply (α := fun i ↦ (α i)ᵒᵈ) ..

theorem le_sSup_apply {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
    (he : e ∈ s) (h : ∀ j < i, e.ofLex j = (sSup s).ofLex j) : e.ofLex i ≤ (sSup s).ofLex i :=
  sInf_apply_le (α := fun i ↦ (α i)ᵒᵈ) he h

theorem sSup_apply_le {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
    (h : ∀ f ∈ s, (∀ j < i, f.ofLex j = (sSup s).ofLex j) → f.ofLex i ≤ e.ofLex i) :
    (sSup s).ofLex i ≤ e.ofLex i :=
  le_sInf_apply (α := fun i ↦ (α i)ᵒᵈ) h

private theorem isLUB_sSup {s : Set (Πₗ i, α i)} : IsLUB s (sSup s) := by
  refine ⟨fun e he ↦ ?_, fun e h ↦ ?_⟩
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
    exact ha.2.not_ge (le_sSup_apply he fun j hj ↦ (ha.1 j hj).symm)
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
    refine ha.2.not_ge <| sSup_apply_le fun f hf hf' ↦ apply_le_of_toLex (h hf) ?_
    simp_all

noncomputable instance completeLattice : CompleteLattice (Πₗ i, α i) where
  isLUB_sSup _ := by exact isLUB_sSup
  isGLB_sInf _ := by exact isGLB_sInf

noncomputable instance : CompleteLinearOrder (Πₗ i, α i) where
  __ := linearOrder
  __ := completeLattice
  __ := LinearOrder.toBiheytingAlgebra _

end Lex

/-! ### Colexicographic ordering -/

namespace Colex

private def inf [WellFoundedGT ι] (s : Set (Colex ((i : ι) → α i))) (i : ι) : α i :=
  ⨅ e : {e ∈ s | ∀ j > i, e.ofColex j = inf s j}, e.1.ofColex i
termination_by wellFounded_gt.wrap i

variable [WellFoundedGT ι]

@[no_expose]
instance : InfSet (Colex ((i : ι) → α i)) where
  sInf s := Colex.toColex (inf s)

theorem sInf_apply (s : Set (Colex ((i : ι) → α i))) (i : ι) :
    (sInf s).ofColex i =
    ⨅ e : {e ∈ s | ∀ j > i, e.ofColex j = (sInf s).ofColex j}, e.1.ofColex i := by
  simp [sInf, inf, -iInf_of_isEmpty]

theorem sInf_apply_le {s : Set (Colex ((i : ι) → α i))} {i : ι} {e : Colex ((i : ι) → α i)}
    (he : e ∈ s) (h : ∀ j > i, e.ofColex j = (sInf s).ofColex j) :
    (sInf s).ofColex i ≤ e.ofColex i := by
  rw [sInf_apply]
  exact sInf_le ⟨⟨e, he, h⟩, rfl⟩

theorem le_sInf_apply {s : Set (Colex ((i : ι) → α i))} {i : ι} {e : Colex ((i : ι) → α i)}
    (h : ∀ f ∈ s, (∀ j > i, f.ofColex j = (sInf s).ofColex j) → e.ofColex i ≤ f.ofColex i) :
    e.ofColex i ≤ (sInf s).ofColex i := by
  rw [sInf_apply]
  apply le_sInf
  grind

private theorem isGLB_sInf {s : Set (Colex ((i : ι) → α i))} : IsGLB s (sInf s) := by
  refine ⟨fun e he ↦ ?_, fun e h ↦ ?_⟩
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
    exact ha.2.not_ge (sInf_apply_le he ha.1)
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
    refine ha.2.not_ge <| le_sInf_apply fun f hf hf' ↦ apply_le_of_toColex (h hf) ?_
    simp_all

-- TODO: figure out how to use `to_dual` here

@[no_expose]
instance : SupSet (Colex ((i : ι) → α i)) where
  sSup s := sInf (α := Colex ((i : ι) → (α i)ᵒᵈ)) s

theorem sSup_apply (s : Set (Colex ((i : ι) → α i))) (i : ι) :
    (sSup s).ofColex i = ⨆ e : {e ∈ s | ∀ j > i, e.ofColex j = (sSup s).ofColex j}, e.1.ofColex i :=
  sInf_apply (α := fun i ↦ (α i)ᵒᵈ) ..

theorem le_sSup_apply {s : Set (Colex ((i : ι) → α i))} {i : ι} {e : Colex ((i : ι) → α i)}
    (he : e ∈ s) (h : ∀ j > i, e.ofColex j = (sSup s).ofColex j) :
    e.ofColex i ≤ (sSup s).ofColex i :=
  sInf_apply_le (α := fun i ↦ (α i)ᵒᵈ) he h

theorem sSup_apply_le {s : Set (Colex ((i : ι) → α i))} {i : ι} {e : Colex ((i : ι) → α i)}
    (h : ∀ f ∈ s, (∀ j > i, f.ofColex j = (sSup s).ofColex j) → f.ofColex i ≤ e.ofColex i) :
    (sSup s).ofColex i ≤ e.ofColex i :=
  le_sInf_apply (α := fun i ↦ (α i)ᵒᵈ) h

private theorem isLUB_sSup {s : Set (Colex ((i : ι) → α i))} : IsLUB s (sSup s) := by
  refine ⟨fun e he ↦ ?_, fun e h ↦ ?_⟩
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
    exact ha.2.not_ge (le_sSup_apply he fun j hj ↦ (ha.1 j hj).symm)
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
    refine ha.2.not_ge <| sSup_apply_le fun f hf hf' ↦ apply_le_of_toColex (h hf) ?_
    simp_all

noncomputable instance completeLattice : CompleteLattice (Colex ((i : ι) → α i)) where
  isLUB_sSup _ := by exact isLUB_sSup
  isGLB_sInf _ := by exact isGLB_sInf

noncomputable instance : CompleteLinearOrder (Colex ((i : ι) → α i)) where
  __ := linearOrder
  __ := completeLattice
  __ := LinearOrder.toBiheytingAlgebra _

end Colex
end Pi
