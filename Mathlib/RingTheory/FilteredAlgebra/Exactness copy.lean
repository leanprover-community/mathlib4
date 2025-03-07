/-
Copyright (c) 2025 Huanyu Zheng, Weichen Jiao, Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huanyu Zheng, Weichen Jiao, Yi Yuan
-/
import Mathlib.RingTheory.FilteredAlgebra.Exactness
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.RingTheory.Ideal.Maps

variable {R S T σR σS σT : Type*}

variable [Ring R] [SetLike σR R] [AddSubgroupClass σR R]

variable [Ring S] [SetLike σS S] [AddSubgroupClass σS S]

variable [Ring T] [SetLike σT T] [AddSubgroupClass σT T]

variable {FR : ℤ → σR} {FS : ℤ → σS} {FT : ℤ → σT}

variable [IsRingFiltration FS (fun n ↦ FS (n - 1))] [IsRingFiltration FT (fun n ↦ FT (n - 1))]

variable (f : FilteredRingHom FR (fun n ↦ FR (n - 1)) FS (fun n ↦ FS (n - 1)))
variable (g : FilteredRingHom FS (fun n ↦ FS (n - 1)) FT (fun n ↦ FT (n - 1)))
variable [hasGMul FR fun n ↦ FR (n - 1)] [hasGMul FT fun n ↦ FT (n - 1)]
  [hasGMul FS fun n ↦ FS (n - 1)]

open RingHom DirectSum DFinsupp FilteredRingHom GradedPiece


theorem exists_nonneg_x_in_filtration (x : S) (p : ℤ)
(Exhaustive : IsExhaustiveFiltration FS (fun n ↦ FS (n - 1)))
 : ∃ s, s ≥ 0 ∧ (x : S) ∈ FS (p + s) := by
  obtain ⟨s₀, xin⟩ : ∃ s, (x : S) ∈ FS s := by
    apply Set.mem_iUnion.mp
    rw[IsExhaustiveFiltration.exhaustive (fun n ↦ FS (n - 1)) (F := FS) (A := S)]
    trivial
  rcases lt_or_le p s₀ with ch | ch
  · exact ⟨s₀ - p, by simp only [ge_iff_le, sub_nonneg, add_sub_cancel, xin, and_true, le_of_lt ch]⟩
  · exact ⟨0, by simp only [ge_iff_le, le_refl, add_zero, (IsFiltration.mono ch) xin, and_self]⟩




#check Int.le_induction_down
#check Nat.decreasingInduction'
--**It needs refactor**
lemma Int.decreasingInduction' (m n : ℤ) {P : ℤ → Prop}
    (h : (k : ℤ) → k ≤ n → m < k → P k → P (k - 1)) (mn : m ≤ n) (hP : P n) : P m := by
  have (s : ℕ) (hs : s < n - m) : P (n - s) → P (n - s - 1) :=
    h (n - s) (by linarith) (by linarith[hs])
  obtain⟨r, hr⟩ : ∃ r : ℕ, r = n - m := CanLift.prf (n - m) (by linarith)
  have : m = n - r := by simp only [hr, sub_sub_cancel]
  rw[this]
  have (t : ℕ) (hs : t ≤ n - m) : P (n - t) := by
    induction' t with t ih
    · simp[hP]
    · have : n - (t : ℤ) - 1 = n - ((t + 1 : ℕ) : ℤ) := Int.sub_sub n (↑t) 1
      rw[← this]
      apply h (n - t) (by linarith) (by linarith[hs])
      apply ih (by linarith[hs])
  apply this
  simp only [hr, le_refl]



lemma induction_lemma (p s : ℤ) (x : S)
    (fg_exact : Function.Exact f.toRingHom g.toRingHom) (GfGg_exact : Function.Exact Gr[f] Gr[g]) :
    ∀ k ≤ p + s, p < k → g.toRingHom x ∈ g.toRingHom '' (FS k) →
    g.toRingHom x ∈ g.toRingHom '' (FS (k - 1)) := by
  sorry



theorem strictness_under_exact_and_exhaustive'
    (fg_exact : Function.Exact f.toRingHom g.toRingHom) (GfGg_exact : Function.Exact Gr[f] Gr[g])
    (Exhaustive : IsExhaustiveFiltration FS (fun n ↦ FS (n - 1))) (p : ℤ) (y : T) :
 y ∈ FT p → y ∈ Set.range g.toRingHom → y ∈ g.toRingHom '' (FS p : Set S) := by
  intro yinFT ⟨x, hx⟩
  rw[← hx]
  obtain⟨s, sge0, xin⟩ : ∃s, s ≥ 0 ∧ x ∈ FS (p + s) := exists_nonneg_x_in_filtration x p Exhaustive
  rcases Or.symm (LE.le.gt_or_eq sge0) with ch | ch
  · rw[ch, add_zero] at xin
    exact Set.mem_image_of_mem (⇑g.toRingHom) xin
  · apply Int.decreasingInduction' (P := fun n ↦ g.toRingHom x ∈ g.toRingHom '' (FS n)) (n := p + s)
    · exact induction_lemma f g p s x fg_exact GfGg_exact
    · linarith
    · exact Set.mem_image_of_mem (⇑g.toRingHom) xin



theorem strictness_under_exact_and_exhaustive
    (fg_exact : Function.Exact f.toRingHom g.toRingHom) (GfGg_exact : Function.Exact Gr[f] Gr[g])
    (Exhaustive : IsExhaustiveFiltration FS (fun n ↦ FS (n - 1))) : g.IsStrict := by
  constructor
  · intro p y
    exact strictness_under_exact_and_exhaustive' f g fg_exact GfGg_exact Exhaustive p y
  · intro p y
    exact strictness_under_exact_and_exhaustive' f g fg_exact GfGg_exact Exhaustive (p - 1) y
