import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Order.Bounded
import Mathlib.SetTheory.Ordinal.Topology
import Mathlib.Data.Nat.Parity

namespace Order
variable [TopologicalSpace α] [Preorder α] [OrderTopology α]

structure IsClub (s : Set α) : Prop :=
  unbounded : Set.Unbounded (· ≤ ·) s
  closed : IsClosed s


section
variable [NoTopOrder α]
@[simp] def isClub_univ: IsClub (Set.univ : Set α) where
  unbounded := by
    intro x
    obtain ⟨b, hb⟩ := exists_not_le x
    use b
    simp[hb]
  closed := by simp

@[simp] theorem Nat.even_succ_succ {n : ℕ} : Even (n.succ.succ) ↔ Even n := by
  simp[Even]
  constructor
  · rintro ⟨r,x⟩
    match r with
    | 0 => linarith
    | h + 1 =>
      use h
      linarith
  · rintro ⟨r,x⟩
    use r+1
    linarith

def Nat.even_odd_rec {p q : ℕ → Sort u} (p0 : p 0)
  (even_odd: (n : ℕ) → p (2 * n) → q (2 * n + 1))
  (odd_even : (n : ℕ) → q (2 * n + 1) → p (2 * n + 2))
  (n : ℕ) :
  if Even n then p n else q n := by
  induction n with
  | zero => exact p0
  | succ m ind =>
    split_ifs with h₁
    · simp only at h₁
      rw[Nat.even_add_one] at h₁
      simp only [h₁, ite_false] at ind
      rw[← Nat.odd_iff_not_even] at h₁
      have h₁ := Nat.two_mul_div_two_add_one_of_odd h₁
      rw[← h₁] at ind
      rw[← h₁]
      apply odd_even _ ind
    · simp only [Nat.even_add_one, not_not] at h₁
      simp only [h₁, ite_true] at ind
      have h₁ := Nat.two_mul_div_two_of_even h₁
      rw[← h₁] at ind
      rw[← h₁]
      apply even_odd _ ind

def Nat.even_odd_rec' {α : Type} (p0 : α)
  (even_odd: (n : ℕ) → α → α)
  (odd_even : (n : ℕ) → α → α)
  (n : ℕ) :
  α := by
  rw[← ite_self (c := Even n) (a := α)]
  apply Nat.even_odd_rec (p := λ _ ↦ α) (q := λ _ ↦ α) p0 even_odd odd_even n
end
end Order
namespace Order
section

variable [LinearOrder α] [NoTopOrder α] [TopologicalSpace α]

def IsClub.inter {s t : Set α} (hs : IsClub s) (ht : IsClub t) : IsClub (s ∩ t) where
  closed := IsClosed.inter hs.closed ht.closed
  unbounded := by
    intro a
    let f := Nat.rec (motive := λ n ↦ α × α)
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
      | succ n ih =>
        dsimp only
        apply Set.mk_mem_prod
        · have := Classical.choose_spec (ht.unbounded (Nat.rec (motive := λ n ↦ α × α)
              (Classical.choose (unbounded ht a), Classical.choose (unbounded hs a))
            (fun n p ↦ (Classical.choose (unbounded ht p.snd),
                         Classical.choose (unbounded hs p.fst))) n).snd)
          tauto
        · have := Classical.choose_spec (hs.unbounded (Nat.rec (motive := λ n ↦ α × α)
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
                (hs.unbounded  (Nat.rec (motive := λ n ↦ α × α)
                (Classical.choose (unbounded ht a), Classical.choose (unbounded hs a))
                (fun n p ↦ (Classical.choose (unbounded ht p.snd),
                             Classical.choose (unbounded hs p.fst))) n).fst)).right
        dsimp at this
        rw[← GE.ge] at this
        have := lt_of_not_ge (α := α) this
        tauto






noncomputable def isClub_FilterBasis : FilterBasis α where
  sets := IsClub
  nonempty := ⟨Set.univ, isClub_univ⟩
  inter_sets := by
    intro x y hx hy
    use x ∩ y
    simp only [Set.subset_inter_iff, Set.inter_subset_left, Set.inter_subset_right, and_self, and_true]
    exact IsClub.inter hx hy


def Filter.club : Filter α where
  sets := {x | ∃ y, IsClub y ∧ y ⊆ x}
  univ_sets := by
    use Set.univ
    simp
  sets_of_superset
end
end


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
