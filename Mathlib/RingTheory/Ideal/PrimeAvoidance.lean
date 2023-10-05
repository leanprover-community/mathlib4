import Mathlib.RingTheory.Ideal.Basic

variable {R : Type _} [CommRing R]

open Set
open BigOperators

-- This is the version in wikipedia:
-- https://en.wikipedia.org/wiki/Prime_avoidance_lemma
example
    (E : AddSubgroup R)
    (multiplicative_closed : ∀ a b : R, a ∈ E → b ∈ E → a * b ∈ E)
    (n : ℕ)
    (p : Fin n → Ideal R) (isPrime : ∀ i, (p i).IsPrime)
    (not_contained : ∀ i, ¬ (E : Set R) ⊆ p i) :
    ¬ (E : Set R) ⊆ ⋃ i, p i := by

  cases' n with n
  · simp only [Nat.zero_eq, iUnion_of_empty]
    rw [subset_empty_iff, eq_empty_iff_forall_not_mem]
    exact fun r => r 0 E.zero_mem

  induction' n with n ih
  · specialize not_contained 0
    convert not_contained
    ext1 x
    rw [mem_iUnion, SetLike.mem_coe]
    refine ⟨?_, fun h => ⟨0, h⟩⟩
    rintro ⟨(i : Fin 1), hi⟩
    convert SetLike.mem_coe.mp hi

  · let p_hat (i : Fin n.succ.succ) : Fin n.succ → Ideal R := fun j =>
      if j.1 < i.1
      then p j.castSucc
      else p j.succ

    have set_eq1 (i : Fin n.succ.succ) : (⋃ j, p j : Set R) = (⋃ j, p_hat i j) ∪ p i
    · ext1 x
      rw [mem_iUnion, mem_union, mem_iUnion]
      fconstructor
      · rintro ⟨j, hj⟩
        obtain ineqj|rfl|ineqj := lt_trichotomy i j
        · left
          refine ⟨⟨j.1 - 1, ?_⟩, ?_⟩
          · by_cases ineqj' : j.1 = 0
            · rw [ineqj']
              norm_num
            exact lt_of_lt_of_le (Nat.pred_lt ineqj') (Nat.lt_succ.mp j.2)
          · simp only [Fin.coe_pred, ge_iff_le, Fin.succ_pred, SetLike.mem_coe]
            rw [if_neg (not_lt.mpr <| Nat.le_pred_of_lt ineqj)]
            convert SetLike.mem_coe.mp hj using 2
            exact Fin.ext <| Nat.succ_pred_eq_of_pos <| lt_of_le_of_lt (by norm_num) <|
              Fin.val_fin_lt.mpr ineqj

        · right; assumption
        · left
          refine ⟨⟨j.1, lt_of_lt_of_le (Fin.val_fin_lt.mpr ineqj) <| Nat.lt_succ.mp i.2⟩, ?_⟩
          simp only [Fin.val_fin_lt, Fin.castSucc_mk, Fin.eta, Fin.succ_mk, SetLike.mem_coe]
          rw [if_pos (Fin.val_fin_lt.mp ineqj)]
          exact hj

      · rintro (⟨j, hj⟩|hj)
        · simp only [SetLike.mem_coe] at hj
          split_ifs at hj with H
          · exact ⟨_, hj⟩
          · exact ⟨_, hj⟩
        · exact ⟨_, hj⟩

    have not_subset' (i : Fin n.succ.succ) : ¬ (E : Set R) ⊆ ⋃ j, p_hat i j
    · refine ih (p_hat i) (fun j => by dsimp only; split_ifs <;> exact isPrime _)
        (fun j => by dsimp only; split_ifs <;> exact not_contained _)


    simp_rw [not_subset] at not_subset'
    choose z z_mem_E z_not_mem_union using not_subset'

    -- three auxiliary lemmas
    have stronger_multiplicative_closed (m : ℕ) (x : Fin m.succ → R) (mem : ∀ j, x j ∈ E) :
        ∏ j, x j ∈ E
    · induction' m with m ih
      · simpa only [Nat.zero_eq, Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton]
          using mem _
      · rw [Fin.prod_univ_succ]
        exact multiplicative_closed _ _ (mem _) <| ih (x ∘ Fin.succ) fun _ => mem _
    have stronger_mem_or_mem (i : Fin n.succ.succ) (m : ℕ)
        (x : Fin m.succ → R) (mem : ∏ j, x j ∈ p i) :
        ∃ j, x j ∈ p i
    · induction' m with m ih
      · simp only [Nat.zero_eq, Finset.univ_unique, Fin.default_eq_zero,
          Finset.prod_singleton] at mem
        exact ⟨0, mem⟩
      · rw [Fin.prod_univ_succ] at mem
        exact ((isPrime i).mem_or_mem mem).elim (fun h => ⟨_, h⟩) fun h => ⟨_, (ih _ h).choose_spec⟩
    have stronger_mul_mem (i : Fin n.succ.succ) (m : ℕ)
        (x : Fin m.succ → R) (mem : ∃ j, x j ∈ p i) :
        ∏ j, x j ∈ p i
    · obtain ⟨j, hj⟩ := mem
      rw [Fin.prod_univ_succAbove]
      exact (p i).mul_mem_right _ hj

    by_cases avoidance : ∀ i, z i ∈ p i
    · let ζ := (∏ i : Fin n.succ, z i.castSucc) + z (Fin.last _)
      have ζ_mem_E : ζ ∈ E := E.add_mem (stronger_multiplicative_closed _ _ fun _ => z_mem_E _) <|
        z_mem_E _
      have ζ_not_mem_union : ¬ ζ ∈ ⋃ i, p i
      · intro r
        rw [mem_iUnion] at r
        obtain ⟨j, hj⟩ := r
        by_cases ineqj : j = Fin.last _
        · subst ineqj
          have mem' : ∏ i : Fin n.succ, z i.castSucc ∈ p (Fin.last _)
          · convert (p _).sub_mem hj (avoidance _)
            simp only [add_sub_cancel]
          obtain ⟨j, hj⟩ := stronger_mem_or_mem (Fin.last _) _ _ mem'
          refine z_not_mem_union j.castSucc <| mem_iUnion.mpr ⟨Fin.last _, ?_⟩
          rw [SetLike.mem_coe, if_neg]
          pick_goal 2
          · exact not_lt.mpr <| Nat.lt_succ.mp j.2
          exact hj
        · have ineqj' : j.1 < n + 1
          · have ineq1 : j.1 < n + 2 := j.2
            rw [Nat.lt_succ, le_iff_lt_or_eq] at ineq1
            exact ineq1.resolve_right (Fin.ext_iff.not.mp ineqj)
          have mem' : z (Fin.last _) ∈ p j
          · have mem' : (∏ i : Fin n.succ, z i.castSucc) ∈ p j
            · exact stronger_mul_mem _ _ _ ⟨⟨j.1, ineqj'⟩, avoidance j⟩
            convert (p j).sub_mem hj <| mem'
            simp only [add_sub_cancel']

          refine z_not_mem_union (Fin.last _) <| mem_iUnion.mpr ⟨⟨j.1, ineqj'⟩, ?_⟩
          · simp only [Fin.val_last, Fin.castSucc_mk, Fin.eta, Fin.succ_mk, SetLike.mem_coe]
            rw [if_pos ineqj']
            exact mem'
      exact not_subset.mpr ⟨ζ, ζ_mem_E, ζ_not_mem_union⟩

    · push_neg at avoidance
      rcases avoidance with ⟨i, H⟩
      exact not_subset.mpr ⟨z i, z_mem_E _, set_eq1 i ▸ fun r => r.elim (z_not_mem_union _) H⟩
