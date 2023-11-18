import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Tactic.IntervalCases

variable {R : Type _} [CommRing R]

open Set
open BigOperators

-- This is the version in wikipedia:
-- https://en.wikipedia.org/wiki/Prime_avoidance_lemma
lemma not_subset_union_prime_ideals_of_not_subset_prime_ideal
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
            erw [if_neg (not_lt.mpr <| Nat.le_pred_of_lt ineqj)]
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

variable [DecidablePred fun I : Ideal R => I.IsPrime]

-- Prime avoidance lemma in stack project
theorem Ideal.subset_of_subset_union_with_at_most_two_non_primes
    (J : Ideal R)
    (ℐ : Finset (Ideal R))
    (number_of_non_prime : (ℐ.filter fun I => ¬ I.IsPrime).card ≤ 2)
    (subset_union : (J : Set R) ⊆ ⋃ (I : ℐ), I) :
    ∃ I, I ∈ ℐ ∧ (J : Set R) ⊆ I  := by
  classical
  induction' ℐ using Finset.strongInductionOn with ℐ ih
  by_cases card : ℐ.card ≤ 2
  · replace card : ℐ.card = 0 ∨ ℐ.card = 1 ∨ ℐ.card = 2
    · interval_cases ℐ.card <;> tauto
    obtain card|card|card := card
    · simp only [Finset.card_eq_zero] at card
      subst card
      simp only [iUnion_of_empty, subset_empty_iff, eq_empty_iff_forall_not_mem] at subset_union
      exact (subset_union 0 J.zero_mem).elim
    · rw [Finset.card_eq_one] at card
      obtain ⟨i, rfl⟩ := card
      simp only [Finset.mem_singleton, SetLike.coe_subset_coe, exists_eq_left]
      intro x hx
      specialize subset_union hx
      simp only [Set.mem_iUnion, SetLike.mem_coe, Subtype.exists, Finset.mem_singleton, exists_prop,
        exists_eq_left] at subset_union
      exact subset_union
    · rw [Finset.card_eq_two] at card
      obtain ⟨a, b, -, rfl⟩ := card
      simp only [Finset.mem_singleton, Finset.mem_insert, SetLike.coe_subset_coe, exists_eq_or_imp,
        exists_eq_left]
      simp only [iUnion_subtype, Finset.mem_singleton, Finset.mem_insert, iUnion_iUnion_eq_or_left,
        iUnion_iUnion_eq_left] at subset_union
      by_contra rid -- subset_union
      push_neg at rid
      rcases rid with ⟨h1, h2⟩
      change ¬ (J : Set R) ⊆ _ at h1 h2
      rw [not_subset_iff_exists_mem_not_mem] at h1 h2
      rcases h1 with ⟨x, hx1, hx2⟩
      rcases h2 with ⟨y, hy1, hy2⟩
      have subset_union' := subset_union
      specialize subset_union <| J.add_mem hx1 hy1
      rcases subset_union with h|h
      · refine (subset_union' hy1).elim (fun h' => hx2 ?_) (fun h' => hy2 h')
        convert a.sub_mem h h'
        simp only [SetLike.mem_coe, add_sub_cancel]
      · refine (subset_union' hx1).elim (fun h' => hx2 h') (fun h' => hy2 ?_)
        convert b.sub_mem h h'
        simp only [SetLike.mem_coe, add_sub_cancel']
  · by_cases subset' : ∀ ℐ', ℐ' ⊂ ℐ → ¬ (J : Set R) ⊆ ⋃ (I : ℐ'), I
    · have nonempty : ℐ.filter (fun I ↦ I.IsPrime) ≠ ∅
      · intro rid
        have rid' : ℐ.filter (fun I ↦ ¬ I.IsPrime) = ℐ
        · rw [Finset.filter_not, rid, Finset.sdiff_empty]
        rw [rid'] at number_of_non_prime
        exact card number_of_non_prime
      rw [← Finset.nonempty_iff_ne_empty] at nonempty
      obtain ⟨I, hI⟩ := nonempty
      rw [Finset.mem_filter] at hI
      obtain ⟨hI1, hI2⟩ := hI
      let ℐ_hat : Ideal R → Finset (Ideal R) := ℐ.erase
      have subset_hat : ∀ I : ℐ, ¬ (J : Set R) ⊆ ⋃ (i : ℐ_hat I), i
      · rintro ⟨I, hI⟩ rid
        specialize subset' (ℐ_hat I) (Finset.erase_ssubset hI)
        exact subset' rid
      simp_rw [not_subset] at subset_hat
      choose x hx1 hx2 using subset_hat
      have hx3 : ∀ i, x i ∈ i.1
      · rintro i
        specialize hx2 i
        specialize hx1 i
        contrapose! hx2
        specialize subset_union hx1
        rw [Set.mem_iUnion] at subset_union ⊢
        rcases subset_union with ⟨j, hj⟩
        exact ⟨⟨j.1, Finset.mem_erase.mpr ⟨fun r => hx2 <| r ▸ hj, j.2⟩⟩, hj⟩


      let X := ∏ i in (ℐ.erase I).attach, x ⟨i.1, Finset.erase_subset _ _ i.2⟩ + x ⟨I, hI1⟩
      have hX1 : X ∈ J
      · refine J.add_mem ?_ (hx1 _)
        apply Ideal.prod_mem_of_mem
        have H : (ℐ.erase I).Nonempty
        · rw [← Finset.card_pos, Finset.card_erase_eq_ite, if_pos hI1]
          simp only [ge_iff_le, tsub_pos_iff_lt]
          linarith
        simp_rw [Finset.mem_attach, true_and_iff]
        rcases H with ⟨c, hc⟩
        exact ⟨⟨c, hc⟩, hx1 _⟩
      specialize subset_union hX1
      rw [mem_iUnion] at subset_union
      obtain ⟨⟨I', hI'₁⟩, hI'₂⟩ := subset_union
      by_cases H : I = I'
      · subst H
        have : ∃ i : ℐ.erase I, x ⟨i.1, Finset.erase_subset _ _ i.2⟩ ∈ I
        · have := I.sub_mem hI'₂ (hx3 ⟨I, hI1⟩)
          simp only [add_sub_cancel] at this
          simp_rw [Ideal.IsPrime.prod_mem_iff_exists_mem, Finset.mem_attach, true_and_iff] at this
          exact this
        obtain ⟨⟨i, hi1⟩, hi2⟩ := this
        rw [Finset.mem_erase] at hi1
        simp only at hi2
        specialize hx1 ⟨i, hi1.2⟩
        specialize hx2 ⟨i, hi1.2⟩
        simp only [SetLike.mem_coe, Finset.coe_erase, Finset.mem_coe, mem_sUnion, not_exists,
          not_and] at hx1 hx2
        refine (hx2 <| mem_iUnion.mpr ⟨⟨I, Finset.mem_erase.mpr ⟨hi1.1.symm, hI'₁⟩⟩, hi2⟩).elim
      · have mem1 : ∏ i in (ℐ.erase I).attach, x ⟨i.1, Finset.erase_subset _ _ i.2⟩ ∈ I'
        · apply Ideal.prod_mem_of_mem
          simp_rw [Finset.mem_attach, true_and_iff]
          exact ⟨⟨I', Finset.mem_erase.mpr ⟨Ne.symm H, hI'₁⟩⟩, hx3 _⟩
        have mem2 : x ⟨I, hI1⟩ ∈ I'
        · have := I'.sub_mem hI'₂ mem1
          simpa only [add_sub_cancel'] using this
        specialize hx1 ⟨I, hI1⟩
        specialize hx2 ⟨I, hI1⟩
        rw [mem_iUnion] at hx2
        push_neg at hx2
        refine (hx2 ⟨I', Finset.mem_erase.mpr ⟨Ne.symm H, hI'₁⟩⟩ mem2).elim
    · -- Use induction hypothesis here
      push_neg at subset'
      obtain ⟨ℐ', lt, le⟩ := subset'
      obtain ⟨I, hI1, hI2⟩ := ih _ lt
        (le_trans (Finset.card_le_of_subset <| Finset.filter_subset_filter _ lt.1)
          number_of_non_prime) le
      exact ⟨I, lt.1 hI1, hI2⟩
