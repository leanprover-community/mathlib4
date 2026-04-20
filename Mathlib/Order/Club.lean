/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.Order.DirSupClosed

import Mathlib.Data.Set.Monotone
import Mathlib.Order.CompleteLatticeIntervals

/-!
# Club sets and stationary sets

A subset of a well-ordered type `α` is called a **club set** when it is closed in the order topology
and cofinal. If `α` has no maximum, then an equivalent condition is that `α` is closed and
unbounded; hence the name.

A set is called **stationary** when it intersects all club sets.

## Implementation notes

To avoid importing topology in the ordinals, we spell out the closure property using `DirSupClosed`.
For any type equipped with the Scott-Hausdorff topology (which includes well-orders with the order
topology), `DirSupClosed s` and `IsClosed s` are equivalent predicates.
-/

@[expose] public section

universe u v

open Cardinal Ordinal

/-! ### Club sets -/

/-- A club set is closed under suprema and cofinal. -/
structure IsClub {α : Type*} [LinearOrder α] (s : Set α) where
  /-- Club sets are closed under suprema. If `α` is a well-order with the order topology, this
  condition is equivalent to `IsClosed s`. -/
  dirSupClosed : DirSupClosed s
  /-- Club sets are cofinal. If `α` has no maximum, this condition is equivalent to `¬ BddAbove s`.
  See `not_bddAbove_iff_isCofinal`. -/
  isCofinal : IsCofinal s

variable {α : Type v} {s t : Set α} {x : α} [LinearOrder α]

@[simp]
theorem IsClub.of_isEmpty [IsEmpty α] (s : Set α) : IsClub s :=
  ⟨.of_isEmpty s, .of_isEmpty s⟩

@[simp]
theorem IsClub.univ : IsClub (.univ (α := α)) :=
  ⟨.univ, .univ⟩

theorem isClub_empty_iff : IsClub (α := α) ∅ ↔ IsEmpty α :=
  ⟨fun h ↦ isCofinal_empty_iff.1 h.isCofinal, fun _ ↦ IsClub.of_isEmpty _⟩

theorem IsClub.nonempty [Nonempty α] (hs : IsClub s) : s.Nonempty := by
  by_contra!
  simp [isClub_empty_iff, this] at hs

-- Depends on #37304.
proof_wanted IsClub.union (hs : IsClub s) (ht : IsClub t) : IsClub (s ∪ t)

theorem IsClub.isLUB_mem (hs : IsClub s) (ht : t ⊆ s) (ht₀ : t.Nonempty) (hx : IsLUB t x) : x ∈ s :=
  hs.dirSupClosed ht ht₀ (Std.Total.directedOn _) hx

theorem IsClub.csSup_mem {α} [ConditionallyCompleteLinearOrder α] {s t : Set α}
    (hs : IsClub s) (ht : t ⊆ s) (ht₀ : t.Nonempty) (ht₁ : BddAbove t) : sSup t ∈ s :=
  hs.isLUB_mem ht ht₀ (isLUB_csSup ht₀ ht₁)

theorem IsClub.ciSup_mem {α} [ConditionallyCompleteLinearOrder α] {ι} {f : ι → α} [Nonempty ι]
    {s : Set α} (hs : IsClub s) (ht : .range f ⊆ s) (ht' : BddAbove (.range f)) : ⨆ i, f i ∈ s :=
  hs.csSup_mem ht (Set.range_nonempty _) ht'

theorem isClub_Ioi [NoMaxOrder α] (x : α) : IsClub (Set.Ioi x) where
  dirSupClosed := dirSupClosed_Ioi x
  isCofinal := .of_not_bddAbove (not_bddAbove_Ioi x)

section WellFoundedLT

variable [WellFoundedLT α]

attribute [local instance]
  WellFoundedLT.toOrderBot WellFoundedLT.conditionallyCompleteLinearOrderBot

theorem IsClub.sInter {s : Set (Set α)} (hα : ℵ₀ < Order.cof α) (hsα : #s < Order.cof α)
    (hs : ∀ x ∈ s, IsClub x) : IsClub (⋂₀ s) := by
  cases isEmpty_or_nonempty α; · simp
  refine ⟨.sInter fun x hx ↦ (hs x hx).dirSupClosed, fun a ↦ ?_⟩
  choose f hf using fun x : s ↦ (hs _ x.2).isCofinal
  let g : ℕ → α := Nat.rec a fun _ IH ↦ sSup (.range (f · IH))
  have hg : BddAbove (.range g) := by
    refine .of_not_isCofinal fun hg ↦ (Order.cof_le hg).not_gt (hα.trans_le' ?_)
    simpa using mk_range_le_lift (f := g)
  refine ⟨_, fun t ht ↦ ?_, le_csSup hg ⟨0, rfl⟩⟩
  apply (hs t ht).isLUB_mem (t := .range fun n ↦ f ⟨t, ht⟩ (g n)) _ (Set.range_nonempty _)
  · refine ⟨?_, fun b hb ↦ csSup_le' ?_⟩ <;> rintro _ ⟨n, rfl⟩
    · apply (le_csSup (.of_not_isCofinal _) _).trans (le_csSup hg ⟨n + 1, rfl⟩)
      · exact fun hg' ↦ (Order.cof_le hg').not_gt (mk_range_le.trans_lt hsα)
      · use ⟨t, ht⟩
    · exact (hf ⟨t, ht⟩ _).2.trans <| hb ⟨_, rfl⟩
  · grind

theorem IsClub.iInter {ι : Type u} {f : ι → Set α} (hα : ℵ₀ < Order.cof α)
    (hι : Cardinal.lift.{v} #ι < Cardinal.lift.{u} (Order.cof α)) (hf : ∀ i, IsClub (f i)) :
    IsClub (⋂ i, f i) := by
  rw [← Set.sInter_range]
  refine IsClub.sInter hα ?_ (by simpa)
  rw [← Cardinal.lift_lt]
  exact mk_range_le_lift.trans_lt hι

theorem IsClub.biInter {ι : Type u} {s : Set ι} {f : ι → Set α} (hα : ℵ₀ < Order.cof α)
    (hs : Cardinal.lift.{v} #s < Cardinal.lift.{u} (Order.cof α)) (hf : ∀ i ∈ s, IsClub (f i)) :
    IsClub (⋂ i ∈ s, f i) := by
  rw [Set.biInter_eq_iInter]
  exact iInter hα hs (by simpa)

theorem IsClub.inter {s t : Set α} (hα : ℵ₀ < Order.cof α) (hs : IsClub s) (ht : IsClub t) :
    IsClub (s ∩ t) := by
  rw [← Set.sInter_pair]
  exact IsClub.sInter hα (hα.trans_le' <| by simp) (by simp [hs, ht])

attribute [-simp] Function.iterate_succ in
/-- Club sets are closed under diagonal intersections. -/
theorem IsClub.diag {f : α → Set α} (hα' : ℵ₀ < Order.cof α) (hα : typeLT α ≤ (Order.cof α).ord)
    (hf : ∀ a, IsClub (f a)) : IsClub {a | ∀ b < a, a ∈ f b} where
  dirSupClosed t ht ht₀ _ a ha b hb := by
    obtain ⟨c, hc, hbc, -⟩ := ha.exists_between hb
    apply (hf b).isLUB_mem _ ⟨c, _⟩ (ha.inter_Ici_of_mem hc) <;> grind
  isCofinal a := by
    have : Nonempty α := ⟨a⟩
    have := (noTopOrder_iff_noMaxOrder α).1 <| Order.one_lt_cof_iff.1 (one_lt_aleph0.trans hα')
    replace hα : (Order.cof α).ord = typeLT α := by
      apply hα.antisymm'
      rw [ord_le]
      exact Order.cof_le_cardinalMk α
    have hα'' : Order.cof α = #α := by simpa using congrArg card hα
    have (b : α) : ∃ c ∈ ⋂₀ (f '' Set.Iio b), b < c := by
      obtain ⟨b', hb'⟩ := exists_gt b
      have ⟨c, hc, hbc⟩ :=
        (IsClub.sInter (s := f '' Set.Iio b) hα' (mk_image_le.trans_lt ?_) ?_).isCofinal b'
      · exact ⟨c, hc, hb'.trans_le hbc⟩
      · rw [hα'']
        apply mk_Iio_lt
        rw [← hα, hα'']
      · simp [hf]
    choose g hg using this
    have hgm : StrictMono fun n ↦ g^[n] a := by
      apply strictMono_of_lt_add_one fun n _ ↦ ?_
      rw [← n.succ_eq_add_one, g.iterate_succ_apply']
      exact (hg _).2
    have hg' : IsLUB (.range fun n ↦ g^[n] a) (⨆ n, g^[n] a) := by
      refine isLUB_ciSup (.of_not_isCofinal fun h ↦ ?_)
      apply (Order.cof_le h).not_gt (hα'.trans_le' _)
      simpa using mk_range_le_lift (f := fun n ↦ g^[n] a)
    refine ⟨⨆ n, g^[n] a, fun b hb ↦ ?_, hg'.1 ⟨0, rfl⟩⟩
    obtain ⟨_, ⟨n, rfl⟩, hb, hn⟩ := hg'.exists_between hb
    apply (hf b).isLUB_mem _ _ (hg'.inter_Ici_of_mem ⟨n + 1, rfl⟩)
    · rintro _ ⟨⟨m, rfl⟩, hm⟩
      rw [Set.mem_Ici, hgm.le_iff_le, Nat.add_one_le_iff] at hm
      cases m with
      | zero => contradiction
      | succ m =>
        dsimp
        rw [g.iterate_succ_apply']
        rw [Nat.lt_add_one_iff] at hm
        simp_rw [Set.sInter_image, Set.mem_iInter] at hg
        exact (hg _).1 _ (hb.trans_le <| hgm.monotone hm)
    · use g^[n + 1] a; simp

theorem Order.IsNormal.isClub_fixedPoints {f : α → α} (hα : ℵ₀ < cof α) (hf : IsNormal f) :
    IsClub f.fixedPoints := by
  cases isEmpty_or_nonempty α; · simp
  refine ⟨fun s hs hs₀ _ a ha ↦ (hf.map_isLUB ha hs₀).unique ?_, fun a ↦ ?_⟩
  · rwa [Set.image_congr hs, Set.image_id']
  · suffices BddAbove (.range fun n ↦ f^[n] a) from
      ⟨_, hf.iSup_iterate_mem_fixedPoints a this, le_csSup this ⟨0, rfl⟩⟩
    refine .of_not_isCofinal fun h ↦ (Order.cof_le h).not_gt (hα.trans_le' ?_)
    simpa using mk_range_le_lift (f := fun n : ℕ ↦ f^[n] a)

lemma isClub_almost_fixed_points [NoMaxOrder α] {f : α → α} (hα' : ℵ₀ < Order.cof α)
    (hα : typeLT α ≤ (Order.cof α).ord) : IsClub {x : α | ∀ y < x, f y < x} :=
  IsClub.diag hα' hα fun x => isClub_Ioi (f x)

end WellFoundedLT

/-! ### Stationary sets -/

/-- A set is called stationary when it intersects all club sets. -/
def IsStationary (s : Set α) : Prop :=
  ∀ ⦃t⦄, IsClub t → (s ∩ t).Nonempty

@[gcongr]
theorem IsStationary.mono (hs : IsStationary s) (h : s ⊆ t) : IsStationary t :=
  fun _u hu ↦ (hs hu).mono (Set.inter_subset_inter_left _ h)

theorem IsStationary.nonempty (hs : IsStationary s) : s.Nonempty := by
  simpa using hs .univ

theorem isStationary_univ_iff : IsStationary (.univ (α := α)) ↔ Nonempty α := by
  simp_rw [IsStationary, Set.univ_inter, ← not_imp_not (b := IsClub _),
    Set.not_nonempty_iff_eq_empty, forall_eq, isClub_empty_iff, not_isEmpty_iff]

@[simp]
theorem IsStationary.univ [Nonempty α] : IsStationary (.univ (α := α)) :=
  isStationary_univ_iff.2 ‹_›

theorem IsStationary.not_bddAbove [NoMaxOrder α] (hs : IsStationary s) : ¬ BddAbove s := by
  by_contra ⟨a, ha⟩
  apply (hs (isClub_Ioi a)).ne_empty
  simpa [Set.eq_empty_iff_forall_notMem, mem_upperBounds] using ha

theorem IsStationary.of_not_isCofinal_compl (hs : ¬ IsCofinal (sᶜ)) : IsStationary s := by
  rw [not_isCofinal_iff] at hs
  intro t ht
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb, hb'⟩ := ht.isCofinal a
  refine ⟨b, ?_, hb⟩
  contrapose! ha
  exact ⟨b, ha, hb'⟩

proof_wanted isStationary_iff_not_isCofinal_compl (hα : Order.cof α ≤ ℵ₀) :
    IsStationary s ↔ ¬ IsCofinal (sᶜ)

theorem IsStationary.inter_isClub [WellFoundedLT α] (hα : ℵ₀ < Order.cof α) (hs : IsStationary s)
    (ht : IsClub t) : IsStationary (s ∩ t) := by
  intro t' ht'
  rw [Set.inter_assoc]
  exact hs (ht.inter hα ht')

/-- **Fodor's lemma,** or the **pressing down lemma:** if `α` has the order type of a regular
cardinal, `s` is a stationary set, and `f : s → α` is a regressive function, there exists some
stationary subset of `s` which is constant on `f`. -/
theorem exists_isStationary_preimage_singleton [WellFoundedLT α] {f : s → α}
    (hα' : ℵ₀ < Order.cof α) (hα : typeLT α ≤ (Order.cof α).ord)
    (hs : IsStationary s) (hf : ∀ x : s, f x < x) :
    ∃ a, IsStationary (Subtype.val '' (f ⁻¹' {a})) := by
  unfold IsStationary
  by_contra!
  choose g hg using this
  simp_rw [Set.eq_empty_iff_forall_notMem] at hg
  obtain ⟨a, hs, ha⟩ := hs <| .diag hα' hα fun a ↦ (hg a).1
  apply (hg (f ⟨a, hs⟩)).2 a
  simpa using ⟨hs, ha _ (hf ⟨a, hs⟩)⟩

lemma exists_isStationary_preimage_singleton_of_cardinalMk_range_lt_cof [WellFoundedLT α]
    {f : s → Set α} (hα : ℵ₀ < Order.cof α) (hs : IsStationary s)
    (hf : #(Set.range f) < Order.cof α) : ∃ a, IsStationary (Subtype.val '' (f ⁻¹' {a})) := by
  unfold IsStationary
  by_contra!
  choose g hg using this
  apply (hs (.biInter hα (by simpa) fun i _ => (hg i).1)).ne_empty
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  rw [Set.mem_inter_iff, Set.mem_iInter₂] at hx
  apply Set.not_nonempty_iff_eq_empty.2 (hg (f ⟨x, hx.1⟩)).2
  exists x
  grind [Subtype.exists]

/-- For regular cardinals `α < κ`, the set `{o < κ | cof o = α}` is stationary in `κ`. -/
lemma Cardinal.IsRegular.isStationary_setOf_cof_eq {α κ : Cardinal.{u}} (hκ : κ.IsRegular)
    (hα : α.IsRegular) (h : α < κ) : IsStationary {o : Set.Iio κ.ord | cof o = α} := by
  intro C hC
  haveI : NoMaxOrder (Set.Iio κ.ord) := noMaxOrder_Iio_ord hκ.aleph0_le
  haveI : Fact (¬ IsMin κ.ord) := ⟨by simp [pos_iff_ne_zero.1 hκ.pos]⟩
  rcases hC.nonempty with ⟨a, ha⟩
  have := not_bddAbove_iff_isCofinal.2 hC.isCofinal
  simp only [bddAbove_def, not_exists, not_forall, exists_prop, not_le] at this
  choose! f hf₁ hf₂ using this
  let g : Ordinal.{u} → Set.Iio κ.ord := fun x =>
    Ordinal.limitRecOn x a (fun _ => f) fun x _ ih => ⨆ y : Set.Iio x, ih y.1 y.2
  have hg0 : g 0 = a := by simp [g]
  have hg_succ : ∀ x, g (Order.succ x) = f (g x) := by simp [g, -Order.succ_eq_add_one]
  have hg_limit : ∀ x, Order.IsSuccLimit x → g x = ⨆ y : Set.Iio x, g y := by
    simp +contextual [g, Ordinal.limitRecOn_limit]
  have hg₁ : ∀ x < κ.ord, g x ∈ C := by
    intro x hx
    induction x using Ordinal.limitRecOn with
    | zero => simpa [hg0]
    | succ x ih =>
      grind [Order.lt_succ]
    | limit x hx' ih =>
      simp only [hx', hg_limit]
      haveI : Nonempty (Set.Iio x) := ⟨0, by simpa using hx'.bot_lt⟩
      apply hC.ciSup_mem
      · grind
      · apply bddAbove_range_Iio_of_lt_cof
        rwa [hκ.cof_ord, mk_Iio_ordinal, lift_lift, lift_lt, ← lt_ord]
  have hg₂ : StrictMonoOn g (Set.Iio κ.ord) := by
    intro x hx y hy h
    simp only [Set.mem_Iio] at hx hy
    induction y using Ordinal.limitRecOn generalizing x with
    | zero => simp at h
    | succ y ih =>
      simp only [hg_succ]
      apply (hf₂ _).trans_le'
      rw [Order.lt_succ_iff, le_iff_lt_or_eq] at h
      grind [Order.lt_succ]
    | limit y hy' ih =>
      simp only [hy', hg_limit]
      apply (hf₂ _).trans_le
      rw [← hg_succ]
      refine le_ciSup_of_le ?_ (⟨Order.succ x, ?_⟩ : Set.Iio y) le_rfl
      · apply bddAbove_range_Iio_of_lt_cof
        rwa [hκ.cof_ord, mk_Iio_ordinal, lift_lift, lift_lt, ← lt_ord]
      · simpa [-Order.succ_eq_add_one] using hy'.succ_lt h
  simp only [Set.nonempty_def, Set.mem_inter_iff, Set.mem_setOf_eq]
  refine ⟨g α.ord, ?_, ?_⟩
  · rw [hg_limit _ (Cardinal.isSuccLimit_ord hα.aleph0_le),
      Set.Iio.coe_iSup (bddAbove_range_Iio_of_lt_cof (by simpa [hκ.cof_ord])),
      Ordinal.cof_iSup_Iio, hα.cof_ord]
    · exact (hg₂.mono (Set.Iio_subset_Iio (Cardinal.ord_le_ord.2 h.le))).strictMono
    · exact (Cardinal.isSuccLimit_ord hα.aleph0_le).isSuccPrelimit
  · grind [Cardinal.ord_lt_ord]

lemma Cardinal.IsRegular.card_eq_of_isStationary {c : Cardinal.{u}} (hc : c.IsRegular)
    {s : Set (Set.Iio c.ord)} (hs : IsStationary s) : #s = Cardinal.lift.{u + 1} c := by
  apply le_antisymm
  · grw [mk_set_le]
    simp
  conv_lhs => rw [← hc.cof_ord, lift_cof, ← cof_Iio]
  by_contra! h
  haveI : NoMaxOrder (Set.Iio c.ord) := noMaxOrder_Iio_ord hc.aleph0_le
  apply hs.not_bddAbove
  contrapose! h
  rw [not_bddAbove_iff_isCofinal] at h
  exact Order.cof_le h
