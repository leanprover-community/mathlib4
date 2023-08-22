import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Order.LocallyFinite
import Mathlib.Data.Fin.Interval
import Mathlib.Data.List.Intervals
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fin

lemma wierd0 (m : Type)[Fintype m](p: m → Prop)[DecidablePred p] :
    Fintype.card m = Fintype.card {i // p i} + Fintype.card {i // ¬ p i} := by
  rw [Fintype.card_subtype_compl, ← Nat.add_sub_assoc, Nat.add_sub_cancel_left]
  exact Fintype.card_subtype_le _

-- lemma wierd01 (m : Type)[Fintype m] (p q : m → Prop) [DecidablePred p] [DecidablePred q] :
--   Fintype.card {i // p i} = Fintype.card {j : {i // p i} // q j} +
--     Fintype.card {j : {i // p i} // ¬ q j} := by
--   exact wierd0 { i // p i } fun i ↦ q ↑i

-- set_option pp.explicit true
/-- A sorted nonnegative list with m elements and exactly r ≤ m non-zero elemnts has the first
(m - r) elemnts as zero -/
lemma wierd2 (m r : ℕ) [NeZero m] (f : Fin m → ℝ)
    (h_nonneg : ∀ (i : Fin m), 0 ≤  f i)
    (h_nz_cnt : Fintype.card { i // f i =  0} = r)
    (h_sorted : Monotone f)
    (j : Fin m):
    ( (j:ℕ) < r) → f j = 0 := by
  intro hjm
  apply Or.by_cases' (eq_or_lt_of_le ( h_nonneg j))
  · intro h; exact h.symm
  · intro hj
    exfalso
    unfold Monotone at h_sorted
    have : ∃ q : Fin m, (r) ≤ q ∧ f q = 0 := by
      by_contra h
      push_neg at h
      have h1 : m - r < Fintype.card {i // f i ≠ 0} := by
        have h2 : Fintype.card {i // f i ≠ 0} = Fintype.card {j : {i // f i ≠ 0} // j < r} +
          Fintype.card {j : {i // f i ≠ 0} // ¬ (j < r)} := wierd0 _ _
        rw [h2]
        have h3 : 1 ≤ Fintype.card {j : {i // f i ≠ 0} // j < r} := by
          apply Fintype.card_pos_iff.2
          refine' Nonempty.intro ?_
          refine' ⟨ ⟨ j, ne_of_gt hj⟩, hjm ⟩
        have h4 : (m - r) = Fintype.card {j : {i // f i ≠ 0} // ¬ (j < r)} := by
          simp only [ne_eq, not_lt]
          rw [← Fintype.card_fin (m - r)]
          rw [Fintype.card_eq]
          apply Nonempty.intro
          refine' ⟨fun z => ?_, fun y => ?_ , ?_, ?_ ⟩
          · let q : Fin m := ⟨r + z, ?_ ⟩
            have hrq : r ≤ q := by simp only [le_add_iff_nonneg_right, zero_le]
            refine ⟨ ⟨q, ?_⟩, ?_ ⟩
            apply h q hrq
            simp only [le_add_iff_nonneg_right, zero_le]
            have : z < m - r := by apply Fin.is_lt
            rw [add_comm]
            apply Nat.add_lt_of_lt_sub this
          · refine' ⟨y - r, ?_⟩
            apply Nat.lt_sub_of_add_lt
            rw [Nat.sub_add_cancel]
            apply Fin.is_lt
            apply y.prop
          · intro x
            dsimp
            simp only [ge_iff_le, add_le_iff_nonpos_right, nonpos_iff_eq_zero, add_tsub_cancel_left, Fin.eta]
          · intro x
            dsimp
            conv_lhs =>
              congr
              congr
              congr
              rw [Nat.add_sub_cancel']
              rfl
              exact x.prop
            done
        have h5 : m - r < m - r + 1 := by exact Nat.lt.base (m - r)
        apply lt_of_lt_of_le h5 _
        rw [Nat.add_comm]
        exact (Nat.add_le_add h3 (le_of_eq h4))
      simp only [Fintype.card_subtype_compl, Fintype.card_fin] at h1
      rw [h_nz_cnt] at h1
      apply (lt_irrefl _) h1
    obtain ⟨q , hq⟩ := this
    have hjq : j < q := by exact_mod_cast lt_of_lt_of_le hjm hq.left
    have h1 : (f q < f j) := by
      rw [hq.2]
      exact hj
    have h2 := h_sorted (le_of_lt hjq)
    apply (not_lt.2 h2) h1

#print axioms LE.le.lt_or_eq

lemma subtype_subtype_eq_and
    (m : Type)[Fintype m] (p q : m → Prop) [DecidablePred p] [DecidablePred q] :
    {j : {i // p i} // q j } ≃ {i // p i ∧ q i} := by
  exact Equiv.subtypeSubtypeEquivSubtypeInter (fun i ↦ p i) q

lemma wierd_ℵ0 (m r : ℕ) (h : r ≤ m) : Fintype.card {i : Fin m // r ≤ i} = m - r := by
  rw [eq_comm, Nat.sub_eq_iff_eq_add]
  have : Fintype.card { i : Fin m // ¬ (r ≤ i)} = r := by
    simp_rw [not_le]
  -- Fintype.exists_ne_map_eq_of_card_lt

lemma Subtype_and_comm (m : Type)[Fintype m] (p q : m → Prop) [DecidablePred p] [DecidablePred q] :
  {i // p i ∧ q i} ≃ {i // q i ∧ p i} := by sorry

lemma Fintype_subtype_and_comm (m : Type)[Fintype m] (p q : m → Prop) [DecidablePred p] [DecidablePred q] :
  Fintype.card {i // p i ∧ q i} = Fintype.card {i // q i ∧ p i} := by sorry



lemma wierd3 (m r : ℕ)(hrm: r < m) [NeZero m] {α : Type} [LinearOrder α] (a : α) (f : Fin m → α)
    (h_nonneg : ∀ (i : Fin m), a ≤  f i)
    (h_nz_cnt : Fintype.card { i // f i =  a} = r)
    (h_sorted : Monotone f)
    (j : Fin m) :
    ( (j:ℕ) < r) → f j = a := by
  /- The argument:
  - We argue by contradiction that suppose f j > a.
  - Then set of elements with indices less than r is exactly r. We have one of them that is already
    not equal to a (that is elemnt j from previous step)
  - Hence the number of elements satisfying two properties :  index < r and (f index = a)
      must be less than r.
  - We then argue that since the number of elements with f i = a is exactly r there must be at least
    one outside index < r. This gives a contradiciton with monotonicity. -/
  /- Perhaps it is easier to contrapose the argumnet since the beginning?! -/
  contrapose!
  intro hja
  by_contra' hrj

  let pp := fun i => f i = a
  let qp := fun i : Fin m => (i:ℕ) < r
  let pn := fun i => f i ≠ a
  let qn := fun i : Fin m => ¬ ((i:ℕ) < r)

  have z1 := Fintype.card_eq.2 (Nonempty.intro (subtype_subtype_eq_and _ pp qp))
  have z1' := Fintype.card_eq.2 (Nonempty.intro (subtype_subtype_eq_and _ qp pp))
  have z2 := Fintype.card_eq.2 (Nonempty.intro (subtype_subtype_eq_and _ pn qp))
  have z3 := Fintype.card_eq.2 (Nonempty.intro (subtype_subtype_eq_and _ pp qn))
  have z4 := Fintype.card_eq.2 (Nonempty.intro (subtype_subtype_eq_and _ pn qn))

  dsimp at z1 z2 z3 z4

  have h1 : m =
    Fintype.card {i // f i ≠ a ∧ (i:ℕ) < r} + Fintype.card {i // f i ≠ a ∧ ¬((i:ℕ) < r)} +
    Fintype.card {i // f i = a ∧ (i:ℕ) < r} + Fintype.card {i // f i = a ∧ ¬((i:ℕ) < r)} := by
    rw [←z1, ← z2, ← z3, ← z4 ]
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, Fintype.card_subtype_compl,
      Nat.add_sub_cancel', add_assoc, Nat.add_sub_cancel', Nat.sub_add_cancel, Fintype.card_fin _]
    apply Fintype.card_subtype_le
    apply Fintype.card_subtype_le
    rw [← Fintype.card_subtype_compl]
    apply Fintype.card_subtype_le

  have h2 : Fintype.card {i // f i ≠ a} = m - r := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, h_nz_cnt]

  rw [← z2, ← z4, Fintype.card_subtype_compl, Nat.add_sub_cancel' (Fintype.card_subtype_le _),
    h2, add_comm, ← Nat.sub_eq_iff_eq_add, eq_comm, Nat.sub_add_eq, Nat.sub_sub_self] at h1

  have : Fintype.card {i // f i = a ∧ (i:ℕ) < r} < r := by
    have : Fintype.card {i : Fin m // (i:ℕ) < r} = r := by
      conv_rhs => rw [← Fintype.card_fin r]
      apply Fintype.card_eq.2 (Nonempty.intro _)


      refine ⟨fun i => ⟨i, i.prop⟩, fun j => ?_, ?_, ?_ ⟩
      refine' ⟨j, ?_⟩
      rw [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt]
      exact j.prop
      apply lt_trans j.prop hrm
      intro j
      dsimp
      congr
      rw [Fin.ext_iff, Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt]
      simp only [Fin.is_lt]
      intro i
      dsimp
      congr
      rw [Nat.mod_eq_of_lt]
      apply lt_trans i.prop hrm




    rw [ Fintype.card_eq.2 (Nonempty.intro (Subtype_and_comm (Fin m) pp qp))]
    rw [←  Fintype.card_eq.2 (Nonempty.intro (Equiv.subtypeSubtypeEquivSubtypeInter qp pp))]
    conv_rhs => rw [← this]
    dsimp
    refine' Fintype.card_subtype_lt ?_
    refine' ⟨j, hrj⟩
    exact hja

  have : 0 < Fintype.card {i // f i = a ∧ ¬((i:ℕ) < r)} := by sorry
  have := (Fintype.card_pos_iff.1 this)
  simp only [not_lt, nonempty_subtype] at this
  obtain ⟨b, hb⟩ := this
  unfold Monotone at h_sorted
  have hjb : j < b := by apply lt_of_lt_of_le hrj hb.2
  have z := h_sorted (le_of_lt hjb)
  have : f b < f j := by
    rw [hb.1]
    exact lt_of_le_of_ne (h_nonneg _) hja.symm
  apply (not_lt.2 z) this
  exact le_of_lt hrm



/-- A sorted nonnegative list with m elements and exactly r ≤ m non-zero elemnts has the first
(m - r) elemnts as zero -/
lemma wierd4 (m r : ℕ) [NeZero m] (f : Fin m → ℝ)
    (h_nonneg : ∀ (i : Fin m), 0 ≤  f i)
    (h_nz_cnt : Fintype.card { i // f i =  0} = r)
    (h_sorted : Monotone f)
    (j : Fin m) : ((j:ℕ) < r) → f j = 0 := by
  intro h
  contrapose! h_nz_cnt
  apply ne_of_lt
  replace h_nz_cnt := h_nz_cnt.lt_of_le' (h_nonneg _)
  have key : ∀ {i}, j ≤ i → f i ≠ 0
  · intro i hi
    exact (h_nz_cnt.trans_le (h_sorted hi)).ne'
  refine lt_of_le_of_lt ?_ h
  have := Fintype.card_subtype_compl (¬f · = 0)
  simp_rw [not_not] at this
  rw [this, Fintype.card_fin, tsub_le_iff_left, ←tsub_le_iff_right, Fintype.card_subtype]
  refine le_trans (by simp) (Finset.card_mono $ show Finset.Ici j ≤ _ from fun k hk ↦ ?_)
  simp only [Finset.mem_Ici] at hk
  simp only [Finset.mem_univ, forall_true_left, Finset.mem_filter, true_and]
  exact key hk

lemma wierd5 (m r : ℕ) [NeZero m] (f : Fin m → ℝ)
    (h_nonneg : ∀ (i : Fin m), 0 ≤  f i)
    (h_nz_cnt : Fintype.card { i // f i =  0} = r)
    (h_sorted : Monotone f)
    (j : Fin m) : ((j:ℕ) < r) → f j = 0 := by
  intro h
  contrapose! h_nz_cnt
  apply ne_of_lt
  sorry

lemma wierd2' {α} [LinearOrder α] (m : ℕ) (f : Fin m → α) (a : α)
    (h_sorted : Monotone f)
    (j : Fin m) (h : j < Fintype.card {i // f i ≤ a}) :
    f j ≤ a := by
  contrapose! h
  have := Fintype.card_subtype_compl (¬f · ≤ a)
  simp_rw [not_not, not_le] at this
  rw [this, Fintype.card_fin, tsub_le_iff_tsub_le, Fintype.card_subtype]
  refine le_trans (by simp) (Finset.card_mono $ show Finset.Ici j ≤ _ from fun k hk ↦ ?_)
  simp only [Finset.mem_Ici] at hk
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.trans_le (h_sorted hk)⟩

lemma wierd6 {α} [LinearOrder α] (m : ℕ) (f : Fin m → α) (a : α)
    (h_sorted : Monotone f)
    (j : Fin m) :
    (j < Fintype.card {i // f i ≤ a}) ↔ f j ≤ a := by sorry
