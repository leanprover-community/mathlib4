import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

import Init.Data.Fin.Lemmas

open Real
open Real Set

-- need to complete the proof of equivalrnce of convergence
-- equivalence of infinite sums.



noncomputable section

def φ (x : ℝ) : ℝ :=
x * Real.log x

end section

#check Ici (0:ℝ)

theorem φ_stcon : StrictConvexOn ℝ (Ici (0:ℝ)) φ := by
  exact Real.strictConvexOn_mul_log


def convex_on' (s : Set ℝ ) (f : ℝ → ℝ) : Prop :=
∀ (n : ℕ)(hn: 2 ≤ (n:ℝ ))(x : Fin n → ℝ ) (t : Fin n → ℝ),
  (∀ i , x i ∈ s) →
  (∀ i, 0 ≤ t i) →
  (∑ i, t i = 1) →
  f (∑ i, t i * x i) ≤ ∑ i, t i * f (x i)

#check Finset.sum_lt_sum
#check Finset.sum_const
#check nsmul_eq_mul
#check Finset.card_fin
#check Finset.sum_eq_add
#check if_neg
#check Fin.sum_univ_succ
#check Fin.sum_univ_zero

theorem  con_eq  (s : Set ℝ ) (f : ℝ → ℝ) : ConvexOn ℝ s f ↔ convex_on' s f := by
  constructor
  · intro h n
    induction' n with n ih
    · field_simp
    · intro  hn x t hx ht htt
      have h: ∃ i: Fin (n+1), t i < 1 := by
        by_contra hc
        push_neg at hc
        have : ∑ i: Fin (n+1), 1 ≤ ∑ i, t i := by
          apply Finset.sum_le_sum
          intro i hi; exact hc i
        rw [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,mul_one] at this
        have : 2 ≤ ∑ i, t i := by
          apply le_trans
          · apply hn
          · apply this
        linarith
      rcases h with ⟨i, hi⟩
      let a := t i
      let b := ∑ j, if j = i then 0 else t j
      have hab : a + b = 1 := by
        dsimp [a,b]
        rw[Finset.sum_eq_add]
        sorry
      sorry
  · intro h
    constructor
    · sorry
    · intro x hx y hy a b ha hb hab
      let t : Fin 2 → ℝ := λ i ↦ if i=0 then a else b
      let x': Fin 2 → ℝ := λ i ↦ if i=0 then x else y
      have h1 : ∀ i, x' i ∈ s := by
        intro i
        by_cases h: i = 0
        · simp [x',h]; exact hx
        · simp [x',if_neg h] ; exact hy
      have h2 : ∀ i, 0 ≤ t i := by
        intro i
        by_cases h: i = 0
        · simp [t,h]; exact ha
        · simp [t,if_neg h] ; exact hb
      have h3: ∑ i, t i = 1 := by
        rw [Fin.sum_univ_succ,Fin.sum_univ_one];simp [t]; exact hab
      specialize h 2 (by exact le_refl 2) x' t h1 h2 h3
      simp[t,x'] at h
      exact h























        --have : 1 < (∑ i, t i) := by





  · sorry
