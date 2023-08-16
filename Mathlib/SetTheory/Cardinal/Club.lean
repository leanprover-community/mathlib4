import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Order.Bounded
import Mathlib.SetTheory.Ordinal.Topology
import Mathlib.Data.Nat.Parity


universe u v
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
variable [ConditionallyCompleteLinearOrderBot α] [NoTopOrder α] [TopologicalSpace α] [OrderTopology α]
section
variable {s : Set α} (h_lt : Cardinal.mk (↑ s) < Order.cof (· ≤ · : α → _))
theorem bddAbove_of_card_lt_cof : BddAbove s := by
  contrapose! h_lt
  rw[not_bddAbove_iff'] at h_lt
  apply Order.cof_le
  intro a
  specialize h_lt a
  obtain ⟨y, y_in_s, y_lt⟩ := h_lt
  use y
  exact ⟨y_in_s, le_of_not_le y_lt⟩

theorem isLUB_csSup_of_card_lt_cof : IsLUB s (sSup s) := isLUB_csSup' (bddAbove_of_card_lt_cof h_lt)
end

section
variable (lt_cof : Cardinal.aleph0 < Order.cof (· ≤ · : α → _))

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
    let sup := sSup {x | ∃ n, (f n).fst = x}
    have prf_sp : IsLUB {x | ∃ n, (f n).fst = x} sup := by
      apply isLUB_csSup_of_card_lt_cof (s := {(f n).fst | n})
      suffices h : Cardinal.mk ↑{x | ∃ n, (f n).fst = x} ≤ Cardinal.aleph0 from
        lt_of_le_of_lt h lt_cof
      simp only [Set.coe_setOf, Cardinal.le_aleph0_iff_subtype_countable]
      apply Set.countable_range
    clear_value sup

    have sup_in_closure : sup ∈ closure {(f n).fst | n} := by
      apply prf_sp.mem_closure
      assumption

    let sup' := sSup {x | ∃ n, (f n).snd = x}
    have prf_sp' : IsLUB {x | ∃ n, (f n).snd = x} sup' := by
      apply isLUB_csSup_of_card_lt_cof (s := {(f n).snd | n})
      suffices h : Cardinal.mk ↑{x | ∃ n, (f n).snd = x} ≤ Cardinal.aleph0 from
        lt_of_le_of_lt h lt_cof
      simp only [Set.coe_setOf, Cardinal.le_aleph0_iff_subtype_countable]
      apply Set.countable_range
    clear_value sup'

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

theorem unbounded_choose_spec1 {s : Set α} (h : Set.Unbounded (· ≤ ·) s) (a : α) :
  a < (h a).choose := by
  have h2 := (h a).choose_spec.right
  dsimp at h2
  apply lt_of_not_ge h2

theorem unbounded_choose_spec2 {s : Set α} (h : Set.Unbounded (· ≤ ·) s) (a : α) :
  (h a).choose ∈ s := (h a).choose_spec.left


protected def IsClub.iInter_ordinal {o : Ordinal} {f : Set.Iio o → Set α} (h_club : ∀ x, IsClub (f x))
  (h_lt : o.card < Order.cof (· ≤ · : α → _)) : IsClub (⋂ (x : Set.Iio o), f x) := by
  induction o using Ordinal.limitRecOn with
  | H₁ => simp[Ordinal.not_lt_zero]
  | H₂ S ih =>
    let g x := if x.val = S then Set.univ else f x
    suffices h : (⋂ (x : ↑(Set.Iio (succ S))), f x) = (⋂ (x : ↑(Set.Iio (succ S))), g x)
      ∩ f ⟨S, (by simp)⟩ by
      rw[h]
      apply IsClub.inter lt_cof
      suffices h_eq : (⋂ (x : ↑(Set.Iio (succ S))), g x) =
        (⋂ (x : ↑(Set.Iio S)), f ⟨x.val, by {have x2 := x.2; rw[Set.mem_Iio] at x2; simp only [Iio_succ,
                                              Set.mem_Iic, ge_iff_le]; exact le_of_lt x2;}⟩) by
        rw[h_eq]
        apply ih
        · intro x
          apply h_club
        · simp only [ge_iff_le, Ordinal.card_succ] at h_lt
          exact lt_of_le_of_lt (le_self_add (c := 1)) h_lt

      · ext x
        simp only [Set.iInter_coe_set, Iio_succ, Set.mem_Iic, Set.mem_iInter, Set.mem_Iio]
        apply forall_congr'
        intro a
        split_ifs with h2
        · simp only [h2, le_refl, Set.mem_univ, forall_true_left, true_iff]
          intro i
          simp[h2] at i
        · constructor
          · intro all_i i
            specialize all_i (le_of_lt i)
            simp[all_i]
          · intro all_i i
            specialize all_i (lt_of_le_of_ne i h2)
            simp[all_i]
      · apply h_club
    ext x
    simp only [Set.iInter_coe_set, Iio_succ, Set.mem_Iic, Set.mem_iInter, Set.mem_inter_iff, Set.mem_ite_univ_left]
    constructor
    · intro hi
      constructor
      · intro i i_le i_ne
        apply hi i i_le
      · exact hi S le_rfl
    · intro ⟨hi, x_in⟩ i i_le
      by_cases i = S
      · simp[h, x_in]
      · apply hi i i_le h
  | H₃ S L ih =>
    convert_to IsClub (⋂ (x : ↑(Set.Iio S)), ⋂ (y : ↑(Set.Iio x)), f y)
    · sorry
    · constructor
      · have inters_club (x : ↑(Set.Iio S)) : IsClub (⋂ (y : ↑(Set.Iio x.val)),
        f ⟨y.val,
        by {rcases y with ⟨y,hy⟩; rcases x with ⟨x,hx⟩; simp only[Set.mem_Iio] at hy hx;
            simp only [Set.mem_Iio]; exact lt_trans hy hx}⟩) := by
          apply ih
          · rcases x with ⟨x, hx⟩
            rw[Set.mem_Iio] at hx
            exact hx
          · intro y
            apply h_club
          · apply lt_of_le_of_lt _ h_lt
            rcases x with ⟨x, hx⟩
            rw[Set.mem_Iio] at hx
            exact Ordinal.card_le_card (le_of_lt hx)

        intro a
        let g' (o : ↑(Set.Iio S)) : o.val ∈ Set.Iio S → α :=
          o.val.limitRecOn
            (λ _ ↦ a)
            (λ p a h ↦ let h2 : p ∈ Set.Iio S :=
                by {simp only[Set.mem_Iio] at *; exact lt_trans (lt_succ _) h}
              ((inters_club ⟨p, h2⟩).unbounded (a h2)).choose)
            (λ o l h is_in ↦ iSup (λ p : Set.Iio o ↦ h p.val p.prop (lt_trans (Set.mem_Iio.mp p.prop) is_in)))
        let g (o : ↑(Set.Iio S)) : α := g' o o.prop

        have hg1 (o : _): g o ∈ (⋂ (y : ↑(Set.Iio ↑o)), f { val := ↑y, property := (_ : ↑y ∈ Set.Iio S) }) := by
          rcases o with ⟨o, lt_prf⟩
          induction o using Ordinal.limitRecOn with
            | H₁ => simp[Ordinal.not_lt_zero]
            | H₂ S' ih' =>
              rw[Set.mem_iInter]
              intro i
              dsimp
              rw[Ordinal.limitRecOn_succ]


            | H₃ S' L' ih' => sorry
      · apply isClosed_iInter
        intro i
        apply isClosed_iInter
        intro j
        exact (h_club _).closed


noncomputable def isClub_FilterBasis : FilterBasis α where
  sets := IsClub
  nonempty := ⟨Set.univ, isClub_univ⟩
  inter_sets := by
    intro x y hx hy
    use x ∩ y
    simp only [Set.subset_inter_iff, Set.inter_subset_left, Set.inter_subset_right, and_self, and_true]
    exact IsClub.inter lt_cof hx hy



def Filter.club : Filter α := (isClub_FilterBasis lt_cof).filter
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

structure IsStronglyMahlo (c : Cardinal) where
  club_stationary : Order.IsStationary {x ∈ Set.Iio c.ord | IsInaccessible x.card ∧ x = x.card.ord}
  inaccessible : IsInaccessible c

end Cardinal
