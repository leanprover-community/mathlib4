import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Order.Bounded
import Mathlib.SetTheory.Ordinal.Topology
import Mathlib.Data.Nat.Parity


universe u
variable {α : Type u}


class CountablyCompleteLinearOrder (α : Type*) extends LinearOrder α where
  /-- The supremum of a countable set -/
  supω : (s : Set α) → Set.Nonempty s → Set.Countable s → ∃ x, IsLUB s x
namespace Order
variable [TopologicalSpace α] [Preorder α] [OrderTopology α]

structure IsClub (s : Set α) : Prop :=
  unbounded : Set.Unbounded (· ≤ ·) s
  closed : IsClosed s

structure IsStationary (s : Set α) : Prop :=
  interClub {c : Set α} (h : IsClub c) : Set.Nonempty (s ∩ c)


section
variable [NoTopOrder α]
@[simp] def isClub_univ: IsClub (Set.univ : Set α) where
  unbounded := by
    intro x
    obtain ⟨b, hb⟩ := exists_not_le x
    use b
    simp[hb]
  closed := by simp
end
end Order
namespace Order
section

variable [CountablyCompleteLinearOrder α] [NoTopOrder α] [TopologicalSpace α] [OrderTopology α]

def IsClub.inter {s t : Set α} (hs : IsClub s) (ht : IsClub t) : IsClub (s ∩ t) where
  closed := IsClosed.inter hs.closed ht.closed
  unbounded := by
    intro a
    let f := Nat.rec (motive := λ _ ↦ α × α)
              (Classical.choose (ht.unbounded a), Classical.choose (hs.unbounded a))
              (λ n p ↦ (Classical.choose (ht.unbounded p.snd), Classical.choose (hs.unbounded p.fst)))
    have h₁ (n) : f n ∈ t.prod s := by
      induction n with
      | zero =>
        dsimp only
        apply Set.mk_mem_prod
        · have := Classical.choose_spec (ht.unbounded a)
          tauto
        · have := Classical.choose_spec (hs.unbounded a)
          tauto
      | succ n _ =>
        dsimp only
        apply Set.mk_mem_prod
        · have := Classical.choose_spec (ht.unbounded (Nat.rec (motive := λ _ ↦ α × α)
              (Classical.choose (unbounded ht a), Classical.choose (unbounded hs a))
            (fun n p ↦ (Classical.choose (unbounded ht p.snd),
                         Classical.choose (unbounded hs p.fst))) n).snd)
          tauto
        · have := Classical.choose_spec (hs.unbounded (Nat.rec (motive := λ _ ↦ α × α)
              (Classical.choose (unbounded ht a), Classical.choose (unbounded hs a))
            (fun n p ↦ (Classical.choose (unbounded ht p.snd),
                         Classical.choose (unbounded hs p.fst))) n).fst )
          tauto
    have h₂ (n) : (f n).fst < (f (n+1)).snd := by
      match n with
      | 0 =>
        dsimp only
        have := (Classical.choose_spec (hs.unbounded (Classical.choose (ht.unbounded a)))).right
        dsimp at this
        rw[← GE.ge] at this
        have := lt_of_not_ge (α := α) this
        tauto
      | n =>
        simp only [Nat.rec_add_one]
        have := (Classical.choose_spec
                (hs.unbounded  (Nat.rec (motive := λ _ ↦ α × α)
                (Classical.choose (unbounded ht a), Classical.choose (unbounded hs a))
                (fun n p ↦ (Classical.choose (unbounded ht p.snd),
                             Classical.choose (unbounded hs p.fst))) n).fst)).right
        dsimp at this
        rw[← GE.ge] at this
        have := lt_of_not_ge (α := α) this
        tauto
    have h₃ (n) : (f n).snd < (f (n+1)).fst := by
      match n with
      | 0 =>
        dsimp only
        have := (Classical.choose_spec (ht.unbounded (Classical.choose (hs.unbounded a)))).right
        dsimp at this
        rw[← GE.ge] at this
        have := lt_of_not_ge (α := α) this
        tauto
      | n =>
        simp only [Nat.rec_add_one]
        have := (Classical.choose_spec
                (ht.unbounded  (Nat.rec (motive := λ _ ↦ α × α)
                (Classical.choose (unbounded ht a), Classical.choose (unbounded hs a))
                (fun n p ↦ (Classical.choose (unbounded ht p.snd),
                             Classical.choose (unbounded hs p.fst))) n).snd)).right
        dsimp at this
        rw[← GE.ge] at this
        have := lt_of_not_ge (α := α) this
        tauto
    have ha : a < (f 0).fst := by
      dsimp
      have := Classical.choose_spec (ht.unbounded a)
      dsimp at this
      rw[← GE.ge] at this
      exact lt_of_not_ge (α := α) this.right
    have fst_ne : Set.Nonempty {(f n).fst | n} := by
      use (f 0).fst
      exact ⟨0, rfl⟩
    have snd_ne : Set.Nonempty {(f n).snd | n} := by
      use (f 0).snd
      exact ⟨0, rfl⟩
    clear_value f
    obtain ⟨sup, prf_sp⟩ := CountablyCompleteLinearOrder.supω {(f n).fst | n} fst_ne (Set.countable_range _)

    have sup_in_closure : sup ∈ closure {(f n).fst | n} := by
      apply prf_sp.mem_closure
      assumption
    obtain ⟨sup', prf_sp'⟩ := CountablyCompleteLinearOrder.supω {(f n).snd | n} snd_ne (Set.countable_range _)

    have sup_is_other_sup : sup = sup' := by
      apply le_antisymm
      · rw[isLUB_le_iff prf_sp]
        simp[upperBounds]
        intro n
        apply le_of_lt
        apply lt_of_lt_of_le (h₂ n)
        replace prf_sp' := And.left prf_sp'
        simp [upperBounds] at prf_sp'
        tauto
      · rw[isLUB_le_iff prf_sp']
        simp[upperBounds]
        intro n
        apply le_of_lt
        apply lt_of_lt_of_le (h₃ n)
        replace prf_sp := And.left prf_sp
        simp [upperBounds] at prf_sp
        tauto

    have sup_in_other_closure : sup ∈ closure {x | ∃ n, (f n).snd = x}
      := by
      rw[sup_is_other_sup]
      apply prf_sp'.mem_closure
      assumption

    use sup
    simp
    constructor
    · constructor
      · have h4 := (IsClosed.closure_subset_iff (s := {x | ∃ n, (f n).snd = x}) hs.closed).mpr
        apply h4
        · rintro x ⟨n, prf_n⟩
          rw[← prf_n]
          specialize h₁ n
          rw[Set.prod] at h₁
          exact h₁.right
        · assumption
      · have h4 := (IsClosed.closure_subset_iff (s := {x | ∃ n, (f n).fst = x}) ht.closed).mpr
        apply h4
        · rintro x ⟨n, prf_n⟩
          rw[← prf_n]
          specialize h₁ n
          rw[Set.prod] at h₁
          exact h₁.left
        · assumption
    · replace prf_sp := And.left prf_sp ⟨0, rfl⟩
      exact lt_of_lt_of_le ha prf_sp

noncomputable def isClub_FilterBasis : FilterBasis α where
  sets := IsClub
  nonempty := ⟨Set.univ, isClub_univ⟩
  inter_sets := by
    intro x y hx hy
    use x ∩ y
    simp only [Set.subset_inter_iff, Set.inter_subset_left, Set.inter_subset_right, and_self, and_true]
    exact IsClub.inter hx hy


def Filter.club : Filter α := isClub_FilterBasis.filter
end
end Order


namespace Cardinal
section
variable {c : Cardinal.{u}} (cofinality : ℵ₀ < Ordinal.cof (Cardinal.ord c))
noncomputable instance inst_uncountable_cofinal_countably_complete : CountablyCompleteLinearOrder (Set.Iio c.ord) := by
  constructor
  intro s s_ne s_cnt
  obtain ⟨f, hf⟩ := Set.Countable.exists_eq_range s_cnt s_ne
  let h := Ordinal.sup (Subtype.val ∘ f)
  use ⟨h,?le⟩
  swap
  · simp only [Set.mem_Iio]
    apply Ordinal.sup_lt_ord_lift
    · simpa
    · intro n
      simp only [Function.comp_apply]
      rcases fn_eq : f n with ⟨fn, ineq⟩
      simp only [Set.mem_Iio] at ineq
      simpa
  · constructor
    · rintro ⟨x, ineq⟩ x_in_s
      simp only [Set.mem_Iio] at ineq
      simp only [hf, Set.mem_range] at x_in_s
      rcases x_in_s with ⟨n, prf⟩
      have h2 := Ordinal.le_sup (Subtype.val ∘ f) n
      simp only [Function.comp_apply, prf] at h2
      simp[h2]
    · rintro ⟨x, ineq⟩ x_in_s
      simp only [upperBounds, Set.mem_setOf_eq] at x_in_s
      simp only [ge_iff_le, Subtype.mk_le_mk, Ordinal.sup_le_iff, Function.comp_apply]
      intro n
      specialize x_in_s (a := f n) (by simp[hf])
      congr
end
section
variable {c : Cardinal.{u}} (uncnt : ℵ₀ < c) (reg : IsRegular c)
noncomputable instance inst_uncountable_regular_countably_complete : CountablyCompleteLinearOrder (Set.Iio c.ord) :=
  inst_uncountable_cofinal_countably_complete (lt_of_lt_of_le uncnt reg.right)
end

def IsStronglyMahlo (c : Cardinal) := Order.IsStationary {x ∈ Set.Iio c.ord | IsInaccessible x.card}

end Cardinal



theorem isUnbounded_univ_iff_limit {a : Ordinal} : (IsLimit a ∨ a = 0) ↔
  Set.Unbounded (· ≤ ·) (Set.univ : Set (Set.Iio a)) := by
  constructor
  · rintro (⟨h⟩|⟨h⟩)
    · suffices h : NoTopOrder ↑(Set.Iio a) by apply Set.unbounded_le_univ
      rw[noTopOrder_iff_noMaxOrder]
      simp[no_max_order_of_limit,h]
    · rw[h]
      intro x
      rcases x with ⟨x,hx⟩
      simp[Ordinal.not_lt_zero] at hx
  · intro unb
    suffices ∀ x, a ≠ Order.succ x by
      have h := zero_or_succ_or_limit a
      rcases h with (⟨h⟩|⟨h⟩|⟨h⟩)
      · simp only [*, or_true]
      · tauto
      · simp only [h, true_or]
    intro x eq
    obtain ⟨⟨b, b_lt⟩, _, hb2⟩ := unb ⟨x, by simp[*,Order.lt_succ]⟩
    simp only [Subtype.mk_lt_mk, not_lt, Set.mem_Iio] at hb2 b_lt
    have: b > x := by simp_all only [isClosed_univ, Set.mem_univ, Subtype.mk_le_mk, not_le,
                                     Order.lt_succ_iff, gt_iff_lt]
    rw[eq] at b_lt
    simp_all only [Order.lt_succ_iff, gt_iff_lt, isClosed_univ, Set.mem_univ, Subtype.mk_le_mk, not_true]


theorem isClub_univ_iff_limit {a : Ordinal} : (IsLimit a ∨ a = 0) ↔ IsClub a (Set.Iio a) := by
  have: {x : Set.Iio a | ↑x ∈ Set.Iio a} = {x : Set.Iio a | ↑x ∈ (Set.univ : Set Ordinal)} := by
          ext x
          rcases x with ⟨x,h⟩
          rw[Set.mem_Iio] at h
          simp[h]
  constructor
  · rintro (⟨h⟩|⟨h⟩)
    · constructor
      · rw[this]
        exact isUnbounded_univ_iff_limit.mp (Or.inl h)
      · rw[this]
        simp
    · constructor
      · rw[this]
        exact isUnbounded_univ_iff_limit.mp (Or.inr h)
      · rw[this]
        simp
  · simp only [isUnbounded_univ_iff_limit]
    intro h
    have h2 := IsClub.unbounded h
    rw[this] at h2
    simp only [Set.mem_univ, Set.setOf_true] at h2
    exact h2

theorem closed_iff_of_unbounded {a : Ordinal} (ha : IsLimit a) (s : Set Ordinal)
  (hs : Set.Unbounded (· ≤ ·) s): IsClosed {x : Set.Iio a | ↑x ∈ s} ↔
    (∀ b < a, (f : ∀ c < b, Ordinal) → (∀ x p, f x p ∈ s) →
    bsup _ f ∈ s) := by
  constructor
  · intro h b b_lt_a f prf
    simp at h








end Ordinal
