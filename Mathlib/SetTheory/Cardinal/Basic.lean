/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Data.Countable.Small
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Small.Set
import Mathlib.Logic.UnivLE
import Mathlib.SetTheory.Cardinal.Order

/-!
# Basic results on cardinal numbers

We provide a collection of basic results on cardinal numbers, in particular focussing on
finite/countable/small types and sets.

## Main definitions

* `Cardinal.powerlt a b` or `a ^< b` is defined as the supremum of `a ^ c` for `c < b`.

## References

* <https://en.wikipedia.org/wiki/Cardinal_number>

## Tags

cardinal number, cardinal arithmetic, cardinal exponentiation, aleph,
Cantor's theorem, König's theorem, Konig's theorem
-/

assert_not_exists Field

open List (Vector)
open Function Order Set

noncomputable section

universe u v w v' w'

variable {α β : Type u}

namespace Cardinal

/-! ### Lifting cardinals to a higher universe -/

@[simp]
lemma mk_preimage_down {s : Set α} : #(ULift.down.{v} ⁻¹' s) = lift.{v} (#s) := by
  rw [← mk_uLift, Cardinal.eq]
  constructor
  let f : ULift.down ⁻¹' s → ULift s := fun x ↦ ULift.up (restrictPreimage s ULift.down x)
  have : Function.Bijective f :=
    ULift.up_bijective.comp (restrictPreimage_bijective _ (ULift.down_bijective))
  exact Equiv.ofBijective f this

-- `simp` can't figure out universe levels: normal form is `lift_mk_shrink'`.
theorem lift_mk_shrink (α : Type u) [Small.{v} α] :
    Cardinal.lift.{max u w} #(Shrink.{v} α) = Cardinal.lift.{max v w} #α :=
  lift_mk_eq.2 ⟨(equivShrink α).symm⟩

@[simp]
theorem lift_mk_shrink' (α : Type u) [Small.{v} α] :
    Cardinal.lift.{u} #(Shrink.{v} α) = Cardinal.lift.{v} #α :=
  lift_mk_shrink.{u, v, 0} α

@[simp]
theorem lift_mk_shrink'' (α : Type max u v) [Small.{v} α] :
    Cardinal.lift.{u} #(Shrink.{v} α) = #α := by
  rw [← lift_umax, lift_mk_shrink.{max u v, v, 0} α, ← lift_umax, lift_id]

theorem prod_eq_of_fintype {α : Type u} [h : Fintype α] (f : α → Cardinal.{v}) :
    prod f = Cardinal.lift.{u} (∏ i, f i) := by
  revert f
  refine Fintype.induction_empty_option ?_ ?_ ?_ α (h_fintype := h)
  · intro α β hβ e h f
    letI := Fintype.ofEquiv β e.symm
    rw [← e.prod_comp f, ← h]
    exact mk_congr (e.piCongrLeft _).symm
  · intro f
    rw [Fintype.univ_pempty, Finset.prod_empty, lift_one, Cardinal.prod, mk_eq_one]
  · intro α hα h f
    rw [Cardinal.prod, mk_congr Equiv.piOptionEquivProd, mk_prod, lift_umax.{v, u}, mk_out, ←
        Cardinal.prod, lift_prod, Fintype.prod_option, lift_mul, ← h fun a => f (some a)]
    simp only [lift_id]

/-! ### Basic cardinals -/

theorem le_one_iff_subsingleton {α : Type u} : #α ≤ 1 ↔ Subsingleton α :=
  ⟨fun ⟨f⟩ => ⟨fun _ _ => f.injective (Subsingleton.elim _ _)⟩, fun ⟨h⟩ =>
    ⟨fun _ => ULift.up 0, fun _ _ _ => h _ _⟩⟩

@[simp]
theorem mk_le_one_iff_set_subsingleton {s : Set α} : #s ≤ 1 ↔ s.Subsingleton :=
  le_one_iff_subsingleton.trans s.subsingleton_coe

alias ⟨_, _root_.Set.Subsingleton.cardinalMk_le_one⟩ := mk_le_one_iff_set_subsingleton

@[deprecated (since := "2024-11-10")]
alias _root_.Set.Subsingleton.cardinal_mk_le_one := Set.Subsingleton.cardinalMk_le_one

private theorem cast_succ (n : ℕ) : ((n + 1 : ℕ) : Cardinal.{u}) = n + 1 := by
  change #(ULift.{u} _) = #(ULift.{u} _) + 1
  rw [← mk_option]
  simp

/-! ### Order properties -/

theorem one_lt_iff_nontrivial {α : Type u} : 1 < #α ↔ Nontrivial α := by
  rw [← not_le, le_one_iff_subsingleton, ← not_nontrivial_iff_subsingleton, Classical.not_not]

lemma sInf_eq_zero_iff {s : Set Cardinal} : sInf s = 0 ↔ s = ∅ ∨ ∃ a ∈ s, a = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases s.eq_empty_or_nonempty with rfl | hne
    · exact Or.inl rfl
    · exact Or.inr ⟨sInf s, csInf_mem hne, h⟩
  · rcases h with rfl | ⟨a, ha, rfl⟩
    · exact Cardinal.sInf_empty
    · exact eq_bot_iff.2 (csInf_le' ha)

lemma iInf_eq_zero_iff {ι : Sort*} {f : ι → Cardinal} :
    (⨅ i, f i) = 0 ↔ IsEmpty ι ∨ ∃ i, f i = 0 := by
  simp [iInf, sInf_eq_zero_iff]

/-- A variant of `ciSup_of_empty` but with `0` on the RHS for convenience -/
protected theorem iSup_of_empty {ι} (f : ι → Cardinal) [IsEmpty ι] : iSup f = 0 :=
  ciSup_of_empty f

@[simp]
theorem lift_sInf (s : Set Cardinal) : lift.{u, v} (sInf s) = sInf (lift.{u, v} '' s) := by
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · simp
  · exact lift_monotone.map_csInf hs

@[simp]
theorem lift_iInf {ι} (f : ι → Cardinal) : lift.{u, v} (iInf f) = ⨅ i, lift.{u, v} (f i) := by
  unfold iInf
  convert lift_sInf (range f)
  simp_rw [← comp_apply (f := lift), range_comp]

end Cardinal

/-! ### Small sets of cardinals -/

namespace Cardinal

instance small_Iic (a : Cardinal.{u}) : Small.{u} (Iic a) := by
  rw [← mk_out a]
  apply @small_of_surjective (Set a.out) (Iic #a.out) _ fun x => ⟨#x, mk_set_le x⟩
  rintro ⟨x, hx⟩
  simpa using le_mk_iff_exists_set.1 hx

instance small_Iio (a : Cardinal.{u}) : Small.{u} (Iio a) := small_subset Iio_subset_Iic_self
instance small_Icc (a b : Cardinal.{u}) : Small.{u} (Icc a b) := small_subset Icc_subset_Iic_self
instance small_Ico (a b : Cardinal.{u}) : Small.{u} (Ico a b) := small_subset Ico_subset_Iio_self
instance small_Ioc (a b : Cardinal.{u}) : Small.{u} (Ioc a b) := small_subset Ioc_subset_Iic_self
instance small_Ioo (a b : Cardinal.{u}) : Small.{u} (Ioo a b) := small_subset Ioo_subset_Iio_self

/-- A set of cardinals is bounded above iff it's small, i.e. it corresponds to a usual ZFC set. -/
theorem bddAbove_iff_small {s : Set Cardinal.{u}} : BddAbove s ↔ Small.{u} s :=
  ⟨fun ⟨a, ha⟩ => @small_subset _ (Iic a) s (fun _ h => ha h) _, by
    rintro ⟨ι, ⟨e⟩⟩
    use sum.{u, u} fun x ↦ e.symm x
    intro a ha
    simpa using le_sum (fun x ↦ e.symm x) (e ⟨a, ha⟩)⟩

theorem bddAbove_of_small (s : Set Cardinal.{u}) [h : Small.{u} s] : BddAbove s :=
  bddAbove_iff_small.2 h

theorem bddAbove_range {ι : Type*} [Small.{u} ι] (f : ι → Cardinal.{u}) : BddAbove (Set.range f) :=
  bddAbove_of_small _

theorem bddAbove_image (f : Cardinal.{u} → Cardinal.{max u v}) {s : Set Cardinal.{u}}
    (hs : BddAbove s) : BddAbove (f '' s) := by
  rw [bddAbove_iff_small] at hs ⊢
  exact small_lift _

theorem bddAbove_range_comp {ι : Type u} {f : ι → Cardinal.{v}} (hf : BddAbove (range f))
    (g : Cardinal.{v} → Cardinal.{max v w}) : BddAbove (range (g ∘ f)) := by
  rw [range_comp]
  exact bddAbove_image g hf

/-- The type of cardinals in universe `u` is not `Small.{u}`. This is a version of the Burali-Forti
paradox. -/
theorem _root_.not_small_cardinal : ¬ Small.{u} Cardinal.{max u v} := by
  intro h
  have := small_lift.{_, v} Cardinal.{max u v}
  rw [← small_univ_iff, ← bddAbove_iff_small] at this
  exact not_bddAbove_univ this

instance uncountable : Uncountable Cardinal.{u} :=
  Uncountable.of_not_small not_small_cardinal.{u}

/-! ### Bounds on suprema -/

theorem sum_le_iSup_lift {ι : Type u}
    (f : ι → Cardinal.{max u v}) : sum f ≤ Cardinal.lift #ι * iSup f := by
  rw [← (iSup f).lift_id, ← lift_umax, lift_umax.{max u v, u}, ← sum_const]
  exact sum_le_sum _ _ (le_ciSup <| bddAbove_of_small _)

theorem sum_le_iSup {ι : Type u} (f : ι → Cardinal.{u}) : sum f ≤ #ι * iSup f := by
  rw [← lift_id #ι]
  exact sum_le_iSup_lift f

/-- The lift of a supremum is the supremum of the lifts. -/
theorem lift_sSup {s : Set Cardinal} (hs : BddAbove s) :
    lift.{u} (sSup s) = sSup (lift.{u} '' s) := by
  apply ((le_csSup_iff' (bddAbove_image.{_,u} _ hs)).2 fun c hc => _).antisymm (csSup_le' _)
  · intro c hc
    by_contra h
    obtain ⟨d, rfl⟩ := Cardinal.mem_range_lift_of_le (not_le.1 h).le
    simp_rw [lift_le] at h hc
    rw [csSup_le_iff' hs] at h
    exact h fun a ha => lift_le.1 <| hc (mem_image_of_mem _ ha)
  · rintro i ⟨j, hj, rfl⟩
    exact lift_le.2 (le_csSup hs hj)

/-- The lift of a supremum is the supremum of the lifts. -/
theorem lift_iSup {ι : Type v} {f : ι → Cardinal.{w}} (hf : BddAbove (range f)) :
    lift.{u} (iSup f) = ⨆ i, lift.{u} (f i) := by
  rw [iSup, iSup, lift_sSup hf, ← range_comp]
  simp [Function.comp_def]

/-- To prove that the lift of a supremum is bounded by some cardinal `t`,
it suffices to show that the lift of each cardinal is bounded by `t`. -/
theorem lift_iSup_le {ι : Type v} {f : ι → Cardinal.{w}} {t : Cardinal} (hf : BddAbove (range f))
    (w : ∀ i, lift.{u} (f i) ≤ t) : lift.{u} (iSup f) ≤ t := by
  rw [lift_iSup hf]
  exact ciSup_le' w

@[simp]
theorem lift_iSup_le_iff {ι : Type v} {f : ι → Cardinal.{w}} (hf : BddAbove (range f))
    {t : Cardinal} : lift.{u} (iSup f) ≤ t ↔ ∀ i, lift.{u} (f i) ≤ t := by
  rw [lift_iSup hf]
  exact ciSup_le_iff' (bddAbove_range_comp.{_,_,u} hf _)

/-- To prove an inequality between the lifts to a common universe of two different supremums,
it suffices to show that the lift of each cardinal from the smaller supremum
if bounded by the lift of some cardinal from the larger supremum.
-/
theorem lift_iSup_le_lift_iSup {ι : Type v} {ι' : Type v'} {f : ι → Cardinal.{w}}
    {f' : ι' → Cardinal.{w'}} (hf : BddAbove (range f)) (hf' : BddAbove (range f')) {g : ι → ι'}
    (h : ∀ i, lift.{w'} (f i) ≤ lift.{w} (f' (g i))) : lift.{w'} (iSup f) ≤ lift.{w} (iSup f') := by
  rw [lift_iSup hf, lift_iSup hf']
  exact ciSup_mono' (bddAbove_range_comp.{_,_,w} hf' _) fun i => ⟨_, h i⟩

/-- A variant of `lift_iSup_le_lift_iSup` with universes specialized via `w = v` and `w' = v'`.
This is sometimes necessary to avoid universe unification issues. -/
theorem lift_iSup_le_lift_iSup' {ι : Type v} {ι' : Type v'} {f : ι → Cardinal.{v}}
    {f' : ι' → Cardinal.{v'}} (hf : BddAbove (range f)) (hf' : BddAbove (range f')) (g : ι → ι')
    (h : ∀ i, lift.{v'} (f i) ≤ lift.{v} (f' (g i))) : lift.{v'} (iSup f) ≤ lift.{v} (iSup f') :=
  lift_iSup_le_lift_iSup hf hf' h

/-! ### Properties about the cast from `ℕ` -/

theorem mk_finset_of_fintype [Fintype α] : #(Finset α) = 2 ^ Fintype.card α := by
  simp [Pow.pow]

@[norm_cast]
theorem nat_succ (n : ℕ) : (n.succ : Cardinal) = succ ↑n := by
  rw [Nat.cast_succ]
  refine (add_one_le_succ _).antisymm (succ_le_of_lt ?_)
  rw [← Nat.cast_succ]
  exact Nat.cast_lt.2 (Nat.lt_succ_self _)

lemma succ_natCast (n : ℕ) : Order.succ (n : Cardinal) = n + 1 := by
  rw [← Cardinal.nat_succ]
  norm_cast

lemma natCast_add_one_le_iff {n : ℕ} {c : Cardinal} : n + 1 ≤ c ↔ n < c := by
  rw [← Order.succ_le_iff, Cardinal.succ_natCast]

lemma two_le_iff_one_lt {c : Cardinal} : 2 ≤ c ↔ 1 < c := by
  convert natCast_add_one_le_iff
  norm_cast

@[simp]
theorem succ_zero : succ (0 : Cardinal) = 1 := by norm_cast

-- This works generally to prove inequalities between numeric cardinals.
theorem one_lt_two : (1 : Cardinal) < 2 := by norm_cast

theorem exists_finset_le_card (α : Type*) (n : ℕ) (h : n ≤ #α) :
    ∃ s : Finset α, n ≤ s.card := by
  obtain hα|hα := finite_or_infinite α
  · let hα := Fintype.ofFinite α
    use Finset.univ
    simpa only [mk_fintype, Nat.cast_le] using h
  · obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq α n
    exact ⟨s, hs.ge⟩

theorem card_le_of {α : Type u} {n : ℕ} (H : ∀ s : Finset α, s.card ≤ n) : #α ≤ n := by
  contrapose! H
  apply exists_finset_le_card α (n+1)
  simpa only [nat_succ, succ_le_iff] using H

theorem cantor' (a) {b : Cardinal} (hb : 1 < b) : a < b ^ a := by
  rw [← succ_le_iff, (by norm_cast : succ (1 : Cardinal) = 2)] at hb
  exact (cantor a).trans_le (power_le_power_right hb)

theorem one_le_iff_pos {c : Cardinal} : 1 ≤ c ↔ 0 < c := by
  rw [← succ_zero, succ_le_iff]

theorem one_le_iff_ne_zero {c : Cardinal} : 1 ≤ c ↔ c ≠ 0 := by
  rw [one_le_iff_pos, pos_iff_ne_zero]

@[simp]
theorem lt_one_iff_zero {c : Cardinal} : c < 1 ↔ c = 0 := by
  simpa using lt_succ_bot_iff (a := c)

/-! ### Properties about `aleph0` -/

theorem nat_lt_aleph0 (n : ℕ) : (n : Cardinal.{u}) < ℵ₀ :=
  succ_le_iff.1
    (by
      rw [← nat_succ, ← lift_mk_fin, aleph0, lift_mk_le.{u}]
      exact ⟨⟨(↑), fun a b => Fin.ext⟩⟩)

@[simp]
theorem one_lt_aleph0 : 1 < ℵ₀ := by simpa using nat_lt_aleph0 1

@[simp]
theorem one_le_aleph0 : 1 ≤ ℵ₀ :=
  one_lt_aleph0.le

theorem lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ ∃ n : ℕ, c = n :=
  ⟨fun h => by
    rcases lt_lift_iff.1 h with ⟨c, h', rfl⟩
    rcases le_mk_iff_exists_set.1 h'.1 with ⟨S, rfl⟩
    suffices S.Finite by
      lift S to Finset ℕ using this
      simp
    contrapose! h'
    haveI := Infinite.to_subtype h'
    exact ⟨Infinite.natEmbedding S⟩, fun ⟨_, e⟩ => e.symm ▸ nat_lt_aleph0 _⟩

lemma succ_eq_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) : Order.succ c = c + 1 := by
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp h
  rw [hn, succ_natCast]

theorem aleph0_le {c : Cardinal} : ℵ₀ ≤ c ↔ ∀ n : ℕ, ↑n ≤ c :=
  ⟨fun h _ => (nat_lt_aleph0 _).le.trans h, fun h =>
    le_of_not_gt fun hn => by
      rcases lt_aleph0.1 hn with ⟨n, rfl⟩
      exact (Nat.lt_succ_self _).not_ge (Nat.cast_le.1 (h (n + 1)))⟩

theorem isSuccPrelimit_aleph0 : IsSuccPrelimit ℵ₀ :=
  isSuccPrelimit_of_succ_lt fun a ha => by
    rcases lt_aleph0.1 ha with ⟨n, rfl⟩
    rw [← nat_succ]
    apply nat_lt_aleph0

theorem isSuccLimit_aleph0 : IsSuccLimit ℵ₀ := by
  rw [Cardinal.isSuccLimit_iff]
  exact ⟨aleph0_ne_zero, isSuccPrelimit_aleph0⟩

lemma not_isSuccLimit_natCast : (n : ℕ) → ¬ IsSuccLimit (n : Cardinal.{u})
  | 0, e => e.1 isMin_bot
  | Nat.succ n, e => Order.not_isSuccPrelimit_succ _ (nat_succ n ▸ e.2)

theorem not_isSuccLimit_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) : ¬ IsSuccLimit c := by
  obtain ⟨n, rfl⟩ := lt_aleph0.1 h
  exact not_isSuccLimit_natCast n

theorem aleph0_le_of_isSuccLimit {c : Cardinal} (h : IsSuccLimit c) : ℵ₀ ≤ c := by
  contrapose! h
  exact not_isSuccLimit_of_lt_aleph0 h

theorem isStrongLimit_aleph0 : IsStrongLimit ℵ₀ := by
  refine ⟨aleph0_ne_zero, fun x hx ↦ ?_⟩
  obtain ⟨n, rfl⟩ := lt_aleph0.1 hx
  exact_mod_cast nat_lt_aleph0 _

theorem IsStrongLimit.aleph0_le {c} (H : IsStrongLimit c) : ℵ₀ ≤ c :=
  aleph0_le_of_isSuccLimit H.isSuccLimit

lemma exists_eq_natCast_of_iSup_eq {ι : Type u} [Nonempty ι] (f : ι → Cardinal.{v})
    (hf : BddAbove (range f)) (n : ℕ) (h : ⨆ i, f i = n) : ∃ i, f i = n :=
  exists_eq_of_iSup_eq_of_not_isSuccLimit.{u, v} f hf (not_isSuccLimit_natCast n) h

@[simp]
theorem range_natCast : range ((↑) : ℕ → Cardinal) = Iio ℵ₀ :=
  ext fun x => by simp only [mem_Iio, mem_range, eq_comm, lt_aleph0]

theorem mk_eq_nat_iff {α : Type u} {n : ℕ} : #α = n ↔ Nonempty (α ≃ Fin n) := by
  rw [← lift_mk_fin, ← lift_uzero #α, lift_mk_eq']

theorem lt_aleph0_iff_finite {α : Type u} : #α < ℵ₀ ↔ Finite α := by
  simp only [lt_aleph0, mk_eq_nat_iff, finite_iff_exists_equiv_fin]

theorem lt_aleph0_iff_fintype {α : Type u} : #α < ℵ₀ ↔ Nonempty (Fintype α) :=
  lt_aleph0_iff_finite.trans (finite_iff_nonempty_fintype _)

theorem lt_aleph0_of_finite (α : Type u) [Finite α] : #α < ℵ₀ :=
  lt_aleph0_iff_finite.2 ‹_›

theorem lt_aleph0_iff_set_finite {S : Set α} : #S < ℵ₀ ↔ S.Finite :=
  lt_aleph0_iff_finite.trans finite_coe_iff

alias ⟨_, _root_.Set.Finite.lt_aleph0⟩ := lt_aleph0_iff_set_finite

@[simp]
theorem lt_aleph0_iff_subtype_finite {p : α → Prop} : #{ x // p x } < ℵ₀ ↔ { x | p x }.Finite :=
  lt_aleph0_iff_set_finite

theorem mk_le_aleph0_iff : #α ≤ ℵ₀ ↔ Countable α := by
  rw [countable_iff_nonempty_embedding, aleph0, ← lift_uzero #α, lift_mk_le']

@[simp]
theorem mk_le_aleph0 [Countable α] : #α ≤ ℵ₀ :=
  mk_le_aleph0_iff.mpr ‹_›

theorem le_aleph0_iff_set_countable {s : Set α} : #s ≤ ℵ₀ ↔ s.Countable := mk_le_aleph0_iff

alias ⟨_, _root_.Set.Countable.le_aleph0⟩ := le_aleph0_iff_set_countable

@[simp]
theorem le_aleph0_iff_subtype_countable {p : α → Prop} :
    #{ x // p x } ≤ ℵ₀ ↔ { x | p x }.Countable :=
  le_aleph0_iff_set_countable

theorem aleph0_lt_mk_iff : ℵ₀ < #α ↔ Uncountable α := by
  rw [← not_le, ← not_countable_iff, not_iff_not, mk_le_aleph0_iff]

@[simp]
theorem aleph0_lt_mk [Uncountable α] : ℵ₀ < #α :=
  aleph0_lt_mk_iff.mpr ‹_›

instance canLiftCardinalNat : CanLift Cardinal ℕ (↑) fun x => x < ℵ₀ :=
  ⟨fun _ hx =>
    let ⟨n, hn⟩ := lt_aleph0.mp hx
    ⟨n, hn.symm⟩⟩

theorem add_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a + b < ℵ₀ :=
  match a, b, lt_aleph0.1 ha, lt_aleph0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by rw [← Nat.cast_add]; apply nat_lt_aleph0

theorem add_lt_aleph0_iff {a b : Cardinal} : a + b < ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀ :=
  ⟨fun h => ⟨(self_le_add_right _ _).trans_lt h, (self_le_add_left _ _).trans_lt h⟩,
   fun ⟨h1, h2⟩ => add_lt_aleph0 h1 h2⟩

theorem aleph0_le_add_iff {a b : Cardinal} : ℵ₀ ≤ a + b ↔ ℵ₀ ≤ a ∨ ℵ₀ ≤ b := by
  simp only [← not_lt, add_lt_aleph0_iff, not_and_or]

/-- See also `Cardinal.nsmul_lt_aleph0_iff_of_ne_zero` if you already have `n ≠ 0`. -/
theorem nsmul_lt_aleph0_iff {n : ℕ} {a : Cardinal} : n • a < ℵ₀ ↔ n = 0 ∨ a < ℵ₀ := by
  cases n with
  | zero => simpa using nat_lt_aleph0 0
  | succ n =>
      simp only [Nat.succ_ne_zero, false_or]
      induction n with
      | zero => simp
      | succ n ih => rw [succ_nsmul, add_lt_aleph0_iff, ih, and_self_iff]

/-- See also `Cardinal.nsmul_lt_aleph0_iff` for a hypothesis-free version. -/
theorem nsmul_lt_aleph0_iff_of_ne_zero {n : ℕ} {a : Cardinal} (h : n ≠ 0) : n • a < ℵ₀ ↔ a < ℵ₀ :=
  nsmul_lt_aleph0_iff.trans <| or_iff_right h

theorem mul_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a * b < ℵ₀ :=
  match a, b, lt_aleph0.1 ha, lt_aleph0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by rw [← Nat.cast_mul]; apply nat_lt_aleph0

theorem mul_lt_aleph0_iff {a b : Cardinal} : a * b < ℵ₀ ↔ a = 0 ∨ b = 0 ∨ a < ℵ₀ ∧ b < ℵ₀ := by
  refine ⟨fun h => ?_, ?_⟩
  · by_cases ha : a = 0
    · exact Or.inl ha
    right
    by_cases hb : b = 0
    · exact Or.inl hb
    right
    rw [← Ne, ← one_le_iff_ne_zero] at ha hb
    constructor
    · rw [← mul_one a]
      exact (mul_le_mul' le_rfl hb).trans_lt h
    · rw [← one_mul b]
      exact (mul_le_mul' ha le_rfl).trans_lt h
  rintro (rfl | rfl | ⟨ha, hb⟩) <;> simp only [*, mul_lt_aleph0, aleph0_pos, zero_mul, mul_zero]

/-- See also `Cardinal.aleph0_le_mul_iff`. -/
theorem aleph0_le_mul_iff {a b : Cardinal} : ℵ₀ ≤ a * b ↔ a ≠ 0 ∧ b ≠ 0 ∧ (ℵ₀ ≤ a ∨ ℵ₀ ≤ b) := by
  let h := (@mul_lt_aleph0_iff a b).not
  rwa [not_lt, not_or, not_or, not_and_or, not_lt, not_lt] at h

/-- See also `Cardinal.aleph0_le_mul_iff'`. -/
theorem aleph0_le_mul_iff' {a b : Cardinal.{u}} : ℵ₀ ≤ a * b ↔ a ≠ 0 ∧ ℵ₀ ≤ b ∨ ℵ₀ ≤ a ∧ b ≠ 0 := by
  have : ∀ {a : Cardinal.{u}}, ℵ₀ ≤ a → a ≠ 0 := fun a => ne_bot_of_le_ne_bot aleph0_ne_zero a
  simp only [aleph0_le_mul_iff, and_or_left, and_iff_right_of_imp this, @and_left_comm (a ≠ 0)]
  simp only [and_comm, or_comm]

theorem mul_lt_aleph0_iff_of_ne_zero {a b : Cardinal} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b < ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀ := by simp [mul_lt_aleph0_iff, ha, hb]

theorem power_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a ^ b < ℵ₀ :=
  match a, b, lt_aleph0.1 ha, lt_aleph0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by rw [power_natCast, ← Nat.cast_pow]; apply nat_lt_aleph0

theorem eq_one_iff_unique {α : Type*} : #α = 1 ↔ Subsingleton α ∧ Nonempty α :=
  calc
    #α = 1 ↔ #α ≤ 1 ∧ 1 ≤ #α := le_antisymm_iff
    _ ↔ Subsingleton α ∧ Nonempty α :=
      le_one_iff_subsingleton.and (one_le_iff_ne_zero.trans mk_ne_zero_iff)

theorem infinite_iff {α : Type u} : Infinite α ↔ ℵ₀ ≤ #α := by
  rw [← not_lt, lt_aleph0_iff_finite, not_finite_iff_infinite]

lemma aleph0_le_mk_iff : ℵ₀ ≤ #α ↔ Infinite α := infinite_iff.symm
lemma mk_lt_aleph0_iff : #α < ℵ₀ ↔ Finite α := by simp [← not_le, aleph0_le_mk_iff]

@[simp] lemma mk_lt_aleph0 [Finite α] : #α < ℵ₀ := mk_lt_aleph0_iff.2 ‹_›

@[simp]
theorem aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ ≤ #α :=
  infinite_iff.1 ‹_›

@[simp]
theorem mk_eq_aleph0 (α : Type*) [Countable α] [Infinite α] : #α = ℵ₀ :=
  mk_le_aleph0.antisymm <| aleph0_le_mk _

theorem denumerable_iff {α : Type u} : Nonempty (Denumerable α) ↔ #α = ℵ₀ :=
  ⟨fun ⟨h⟩ => mk_congr ((@Denumerable.eqv α h).trans Equiv.ulift.symm), fun h => by
    obtain ⟨f⟩ := Quotient.exact h
    exact ⟨Denumerable.mk' <| f.trans Equiv.ulift⟩⟩

theorem mk_denumerable (α : Type u) [Denumerable α] : #α = ℵ₀ :=
  denumerable_iff.1 ⟨‹_›⟩

theorem _root_.Set.countable_infinite_iff_nonempty_denumerable {α : Type*} {s : Set α} :
    s.Countable ∧ s.Infinite ↔ Nonempty (Denumerable s) := by
  rw [nonempty_denumerable_iff, ← Set.infinite_coe_iff, countable_coe_iff]

@[simp]
theorem aleph0_add_aleph0 : ℵ₀ + ℵ₀ = ℵ₀ :=
  mk_denumerable _

theorem aleph0_mul_aleph0 : ℵ₀ * ℵ₀ = ℵ₀ :=
  mk_denumerable _

@[simp]
theorem nat_mul_aleph0 {n : ℕ} (hn : n ≠ 0) : ↑n * ℵ₀ = ℵ₀ :=
  le_antisymm (lift_mk_fin n ▸ mk_le_aleph0) <|
    le_mul_of_one_le_left (zero_le _) <| by
      rwa [← Nat.cast_one, Nat.cast_le, Nat.one_le_iff_ne_zero]

@[simp]
theorem aleph0_mul_nat {n : ℕ} (hn : n ≠ 0) : ℵ₀ * n = ℵ₀ := by rw [mul_comm, nat_mul_aleph0 hn]

@[simp]
theorem ofNat_mul_aleph0 {n : ℕ} [Nat.AtLeastTwo n] : ofNat(n) * ℵ₀ = ℵ₀ :=
  nat_mul_aleph0 (NeZero.ne n)

@[simp]
theorem aleph0_mul_ofNat {n : ℕ} [Nat.AtLeastTwo n] : ℵ₀ * ofNat(n) = ℵ₀ :=
  aleph0_mul_nat (NeZero.ne n)

@[simp]
theorem add_le_aleph0 {c₁ c₂ : Cardinal} : c₁ + c₂ ≤ ℵ₀ ↔ c₁ ≤ ℵ₀ ∧ c₂ ≤ ℵ₀ :=
  ⟨fun h => ⟨le_self_add.trans h, le_add_self.trans h⟩, fun h =>
    aleph0_add_aleph0 ▸ add_le_add h.1 h.2⟩

@[simp]
theorem aleph0_add_nat (n : ℕ) : ℵ₀ + n = ℵ₀ :=
  (add_le_aleph0.2 ⟨le_rfl, (nat_lt_aleph0 n).le⟩).antisymm le_self_add

@[simp]
theorem nat_add_aleph0 (n : ℕ) : ↑n + ℵ₀ = ℵ₀ := by rw [add_comm, aleph0_add_nat]

@[simp]
theorem ofNat_add_aleph0 {n : ℕ} [Nat.AtLeastTwo n] : ofNat(n) + ℵ₀ = ℵ₀ :=
  nat_add_aleph0 n

@[simp]
theorem aleph0_add_ofNat {n : ℕ} [Nat.AtLeastTwo n] : ℵ₀ + ofNat(n) = ℵ₀ :=
  aleph0_add_nat n

theorem exists_nat_eq_of_le_nat {c : Cardinal} {n : ℕ} (h : c ≤ n) : ∃ m, m ≤ n ∧ c = m := by
  lift c to ℕ using h.trans_lt (nat_lt_aleph0 _)
  exact ⟨c, mod_cast h, rfl⟩

theorem mk_int : #ℤ = ℵ₀ :=
  mk_denumerable ℤ

theorem mk_pnat : #ℕ+ = ℵ₀ :=
  mk_denumerable ℕ+

@[deprecated (since := "2025-04-27")]
alias mk_pNat := mk_pnat

/-! ### Cardinalities of basic sets and types -/

@[simp] theorem mk_additive : #(Additive α) = #α := rfl

@[simp] theorem mk_multiplicative : #(Multiplicative α) = #α := rfl

@[to_additive (attr := simp)] theorem mk_mulOpposite : #(MulOpposite α) = #α :=
  mk_congr MulOpposite.opEquiv.symm

theorem mk_singleton {α : Type u} (x : α) : #({x} : Set α) = 1 :=
  mk_eq_one _

@[simp]
theorem mk_vector (α : Type u) (n : ℕ) : #(List.Vector α n) = #α ^ n :=
  (mk_congr (Equiv.vectorEquivFin α n)).trans <| by simp

theorem mk_list_eq_sum_pow (α : Type u) : #(List α) = sum fun n : ℕ => #α ^ n :=
  calc
    #(List α) = #(Σn, List.Vector α n) := mk_congr (Equiv.sigmaFiberEquiv List.length).symm
    _ = sum fun n : ℕ => #α ^ n := by simp

theorem mk_quot_le {α : Type u} {r : α → α → Prop} : #(Quot r) ≤ #α :=
  mk_le_of_surjective Quot.exists_rep

theorem mk_quotient_le {α : Type u} {s : Setoid α} : #(Quotient s) ≤ #α :=
  mk_quot_le

theorem mk_subtype_le_of_subset {α : Type u} {p q : α → Prop} (h : ∀ ⦃x⦄, p x → q x) :
    #(Subtype p) ≤ #(Subtype q) :=
  ⟨Embedding.subtypeMap (Embedding.refl α) h⟩

theorem mk_emptyCollection (α : Type u) : #(∅ : Set α) = 0 :=
  mk_eq_zero _

theorem mk_emptyCollection_iff {α : Type u} {s : Set α} : #s = 0 ↔ s = ∅ := by
  rw [mk_eq_zero_iff, isEmpty_coe_sort]

lemma mk_set_ne_zero_iff {α : Type u} (s : Set α) : #s ≠ 0 ↔ s.Nonempty := by
  rw [mk_ne_zero_iff, nonempty_coe_sort]

@[simp]
theorem mk_univ {α : Type u} : #(@univ α) = #α :=
  mk_congr (Equiv.Set.univ α)

@[simp] lemma mk_setProd {α β : Type u} (s : Set α) (t : Set β) : #(s ×ˢ t) = #s * #t := by
  rw [mul_def, mk_congr (Equiv.Set.prod ..)]

theorem mk_image_le {α β : Type u} {f : α → β} {s : Set α} : #(f '' s) ≤ #s :=
  mk_le_of_surjective surjective_onto_image

lemma mk_image2_le {α β γ : Type u} {f : α → β → γ} {s : Set α} {t : Set β} :
    #(image2 f s t) ≤ #s * #t := by
  rw [← image_uncurry_prod, ← mk_setProd]
  exact mk_image_le

theorem mk_image_le_lift {α : Type u} {β : Type v} {f : α → β} {s : Set α} :
    lift.{u} #(f '' s) ≤ lift.{v} #s :=
  lift_mk_le.{0}.mpr ⟨Embedding.ofSurjective _ surjective_onto_image⟩

theorem mk_range_le {α β : Type u} {f : α → β} : #(range f) ≤ #α :=
  mk_le_of_surjective surjective_onto_range

theorem mk_range_le_lift {α : Type u} {β : Type v} {f : α → β} :
    lift.{u} #(range f) ≤ lift.{v} #α :=
  lift_mk_le.{0}.mpr ⟨Embedding.ofSurjective _ surjective_onto_range⟩

theorem mk_range_eq (f : α → β) (h : Injective f) : #(range f) = #α :=
  mk_congr (Equiv.ofInjective f h).symm

theorem mk_range_eq_lift {α : Type u} {β : Type v} {f : α → β} (hf : Injective f) :
    lift.{max u w} #(range f) = lift.{max v w} #α :=
  lift_mk_eq.{v,u,w}.mpr ⟨(Equiv.ofInjective f hf).symm⟩

theorem mk_range_eq_of_injective {α : Type u} {β : Type v} {f : α → β} (hf : Injective f) :
    lift.{u} #(range f) = lift.{v} #α :=
  lift_mk_eq'.mpr ⟨(Equiv.ofInjective f hf).symm⟩

lemma lift_mk_le_lift_mk_of_injective {α : Type u} {β : Type v} {f : α → β} (hf : Injective f) :
    Cardinal.lift.{v} (#α) ≤ Cardinal.lift.{u} (#β) := by
  rw [← Cardinal.mk_range_eq_of_injective hf]
  exact Cardinal.lift_le.2 (Cardinal.mk_set_le _)

lemma lift_mk_le_lift_mk_of_surjective {α : Type u} {β : Type v} {f : α → β} (hf : Surjective f) :
    Cardinal.lift.{u} (#β) ≤ Cardinal.lift.{v} (#α) :=
  lift_mk_le_lift_mk_of_injective (injective_surjInv hf)

theorem mk_image_eq_of_injOn {α β : Type u} (f : α → β) (s : Set α) (h : InjOn f s) :
    #(f '' s) = #s :=
  mk_congr (Equiv.Set.imageOfInjOn f s h).symm

theorem mk_image_eq_of_injOn_lift {α : Type u} {β : Type v} (f : α → β) (s : Set α)
    (h : InjOn f s) : lift.{u} #(f '' s) = lift.{v} #s :=
  lift_mk_eq.{v, u, 0}.mpr ⟨(Equiv.Set.imageOfInjOn f s h).symm⟩

theorem mk_image_eq {α β : Type u} {f : α → β} {s : Set α} (hf : Injective f) : #(f '' s) = #s :=
  mk_image_eq_of_injOn _ _ hf.injOn

theorem mk_image_eq_lift {α : Type u} {β : Type v} (f : α → β) (s : Set α) (h : Injective f) :
    lift.{u} #(f '' s) = lift.{v} #s :=
  mk_image_eq_of_injOn_lift _ _ h.injOn

@[simp]
theorem mk_image_embedding_lift {β : Type v} (f : α ↪ β) (s : Set α) :
    lift.{u} #(f '' s) = lift.{v} #s :=
  mk_image_eq_lift _ _ f.injective

@[simp]
theorem mk_image_embedding (f : α ↪ β) (s : Set α) : #(f '' s) = #s := by
  simpa using mk_image_embedding_lift f s

theorem mk_iUnion_le_sum_mk {α ι : Type u} {f : ι → Set α} : #(⋃ i, f i) ≤ sum fun i => #(f i) :=
  calc
    #(⋃ i, f i) ≤ #(Σi, f i) := mk_le_of_surjective (Set.sigmaToiUnion_surjective f)
    _ = sum fun i => #(f i) := mk_sigma _

theorem mk_iUnion_le_sum_mk_lift {α : Type u} {ι : Type v} {f : ι → Set α} :
    lift.{v} #(⋃ i, f i) ≤ sum fun i => #(f i) :=
  calc
    lift.{v} #(⋃ i, f i) ≤ #(Σi, f i) :=
      mk_le_of_surjective <| ULift.up_surjective.comp (Set.sigmaToiUnion_surjective f)
    _ = sum fun i => #(f i) := mk_sigma _

theorem mk_iUnion_eq_sum_mk {α ι : Type u} {f : ι → Set α}
    (h : Pairwise (Disjoint on f)) : #(⋃ i, f i) = sum fun i => #(f i) :=
  calc
    #(⋃ i, f i) = #(Σi, f i) := mk_congr (Set.unionEqSigmaOfDisjoint h)
    _ = sum fun i => #(f i) := mk_sigma _

theorem mk_iUnion_eq_sum_mk_lift {α : Type u} {ι : Type v} {f : ι → Set α}
    (h : Pairwise (Disjoint on f)) :
    lift.{v} #(⋃ i, f i) = sum fun i => #(f i) :=
  calc
    lift.{v} #(⋃ i, f i) = #(Σi, f i) :=
      mk_congr <| .trans Equiv.ulift (Set.unionEqSigmaOfDisjoint h)
    _ = sum fun i => #(f i) := mk_sigma _

theorem mk_iUnion_le {α ι : Type u} (f : ι → Set α) : #(⋃ i, f i) ≤ #ι * ⨆ i, #(f i) :=
  mk_iUnion_le_sum_mk.trans (sum_le_iSup _)

theorem mk_iUnion_le_lift {α : Type u} {ι : Type v} (f : ι → Set α) :
    lift.{v} #(⋃ i, f i) ≤ lift.{u} #ι * ⨆ i, lift.{v} #(f i) := by
  refine mk_iUnion_le_sum_mk_lift.trans <| Eq.trans_le ?_ (sum_le_iSup_lift _)
  rw [← lift_sum, lift_id'.{_,u}]

theorem mk_sUnion_le {α : Type u} (A : Set (Set α)) : #(⋃₀ A) ≤ #A * ⨆ s : A, #s := by
  rw [sUnion_eq_iUnion]
  apply mk_iUnion_le

theorem mk_biUnion_le {ι α : Type u} (A : ι → Set α) (s : Set ι) :
    #(⋃ x ∈ s, A x) ≤ #s * ⨆ x : s, #(A x.1) := by
  rw [biUnion_eq_iUnion]
  apply mk_iUnion_le

theorem mk_biUnion_le_lift {α : Type u} {ι : Type v} (A : ι → Set α) (s : Set ι) :
    lift.{v} #(⋃ x ∈ s, A x) ≤ lift.{u} #s * ⨆ x : s, lift.{v} #(A x.1) := by
  rw [biUnion_eq_iUnion]
  apply mk_iUnion_le_lift

theorem finset_card_lt_aleph0 (s : Finset α) : #(↑s : Set α) < ℵ₀ :=
  lt_aleph0_of_finite _

theorem mk_set_eq_nat_iff_finset {α} {s : Set α} {n : ℕ} :
    #s = n ↔ ∃ t : Finset α, (t : Set α) = s ∧ t.card = n := by
  constructor
  · intro h
    lift s to Finset α using lt_aleph0_iff_set_finite.1 (h.symm ▸ nat_lt_aleph0 n)
    simpa using h
  · rintro ⟨t, rfl, rfl⟩
    exact mk_coe_finset

theorem mk_eq_nat_iff_finset {n : ℕ} :
    #α = n ↔ ∃ t : Finset α, (t : Set α) = univ ∧ t.card = n := by
  rw [← mk_univ, mk_set_eq_nat_iff_finset]

theorem mk_eq_nat_iff_fintype {n : ℕ} : #α = n ↔ ∃ h : Fintype α, @Fintype.card α h = n := by
  rw [mk_eq_nat_iff_finset]
  constructor
  · rintro ⟨t, ht, hn⟩
    exact ⟨⟨t, eq_univ_iff_forall.1 ht⟩, hn⟩
  · rintro ⟨⟨t, ht⟩, hn⟩
    exact ⟨t, eq_univ_iff_forall.2 ht, hn⟩

theorem mk_union_add_mk_inter {α : Type u} {S T : Set α} :
    #(S ∪ T : Set α) + #(S ∩ T : Set α) = #S + #T := by
  classical
  exact Quot.sound ⟨Equiv.Set.unionSumInter S T⟩

/-- The cardinality of a union is at most the sum of the cardinalities
of the two sets. -/
theorem mk_union_le {α : Type u} (S T : Set α) : #(S ∪ T : Set α) ≤ #S + #T :=
  @mk_union_add_mk_inter α S T ▸ self_le_add_right #(S ∪ T : Set α) #(S ∩ T : Set α)

theorem mk_union_of_disjoint {α : Type u} {S T : Set α} (H : Disjoint S T) :
    #(S ∪ T : Set α) = #S + #T := by
  classical
  exact Quot.sound ⟨Equiv.Set.union H⟩

theorem mk_insert {α : Type u} {s : Set α} {a : α} (h : a ∉ s) :
    #(insert a s : Set α) = #s + 1 := by
  rw [← union_singleton, mk_union_of_disjoint, mk_singleton]
  simpa

theorem mk_insert_le {α : Type u} {s : Set α} {a : α} : #(insert a s : Set α) ≤ #s + 1 := by
  by_cases h : a ∈ s
  · simp only [insert_eq_of_mem h, self_le_add_right]
  · rw [mk_insert h]

theorem mk_sum_compl {α} (s : Set α) : #s + #(sᶜ : Set α) = #α := by
  classical
  exact mk_congr (Equiv.Set.sumCompl s)

theorem mk_le_mk_of_subset {α} {s t : Set α} (h : s ⊆ t) : #s ≤ #t :=
  ⟨Set.embeddingOfSubset s t h⟩

theorem mk_le_iff_forall_finset_subset_card_le {α : Type u} {n : ℕ} {t : Set α} :
    #t ≤ n ↔ ∀ s : Finset α, (s : Set α) ⊆ t → s.card ≤ n := by
  refine ⟨fun H s hs ↦ by simpa using (mk_le_mk_of_subset hs).trans H, fun H ↦ ?_⟩
  apply card_le_of (fun s ↦ ?_)
  classical
  let u : Finset α := s.image Subtype.val
  have : u.card = s.card := Finset.card_image_of_injOn Subtype.coe_injective.injOn
  rw [← this]
  apply H
  simp only [u, Finset.coe_image, image_subset_iff, Subtype.coe_preimage_self, subset_univ]

theorem mk_subtype_mono {p q : α → Prop} (h : ∀ x, p x → q x) :
    #{ x // p x } ≤ #{ x // q x } :=
  ⟨embeddingOfSubset _ _ h⟩

theorem le_mk_diff_add_mk (S T : Set α) : #S ≤ #(S \ T : Set α) + #T :=
  (mk_le_mk_of_subset <| subset_diff_union _ _).trans <| mk_union_le _ _

theorem mk_diff_add_mk {S T : Set α} (h : T ⊆ S) : #(S \ T : Set α) + #T = #S := by
  refine (mk_union_of_disjoint <| ?_).symm.trans <| by rw [diff_union_of_subset h]
  exact disjoint_sdiff_self_left

lemma diff_nonempty_of_mk_lt_mk {S T : Set α} (h : #S < #T) : (T \ S).Nonempty := by
  rw [← mk_set_ne_zero_iff]
  intro h'
  exact h.not_ge ((le_mk_diff_add_mk T S).trans (by simp [h']))

lemma compl_nonempty_of_mk_lt_mk {S : Set α} (h : #S < #α) : Sᶜ.Nonempty := by
  rw [← mk_univ (α := α)] at h
  simpa [Set.compl_eq_univ_diff] using diff_nonempty_of_mk_lt_mk h

theorem mk_union_le_aleph0 {α} {P Q : Set α} :
    #(P ∪ Q : Set α) ≤ ℵ₀ ↔ #P ≤ ℵ₀ ∧ #Q ≤ ℵ₀ := by
  simp only [le_aleph0_iff_subtype_countable, mem_union, setOf_mem_eq, Set.union_def,
    ← countable_union]

theorem mk_sep (s : Set α) (t : α → Prop) : #({ x ∈ s | t x } : Set α) = #{ x : s | t x.1 } :=
  mk_congr (Equiv.Set.sep s t)

theorem mk_preimage_of_injective_lift {α : Type u} {β : Type v} (f : α → β) (s : Set β)
    (h : Injective f) : lift.{v} #(f ⁻¹' s) ≤ lift.{u} #s := by
  rw [lift_mk_le.{0}]
  -- Porting note: Needed to insert `mem_preimage.mp` below
  use Subtype.coind (fun x => f x.1) fun x => mem_preimage.mp x.2
  apply Subtype.coind_injective; exact h.comp Subtype.val_injective

theorem mk_preimage_of_subset_range_lift {α : Type u} {β : Type v} (f : α → β) (s : Set β)
    (h : s ⊆ range f) : lift.{u} #s ≤ lift.{v} #(f ⁻¹' s) := by
  rw [← image_preimage_eq_iff] at h
  nth_rewrite 1 [← h]
  apply mk_image_le_lift

theorem mk_preimage_of_injective_of_subset_range_lift {β : Type v} (f : α → β) (s : Set β)
    (h : Injective f) (h2 : s ⊆ range f) : lift.{v} #(f ⁻¹' s) = lift.{u} #s :=
  le_antisymm (mk_preimage_of_injective_lift f s h) (mk_preimage_of_subset_range_lift f s h2)

theorem mk_preimage_of_injective_of_subset_range (f : α → β) (s : Set β) (h : Injective f)
    (h2 : s ⊆ range f) : #(f ⁻¹' s) = #s := by
  convert mk_preimage_of_injective_of_subset_range_lift.{u, u} f s h h2 using 1 <;> rw [lift_id]

@[simp]
theorem mk_preimage_equiv_lift {β : Type v} (f : α ≃ β) (s : Set β) :
    lift.{v} #(f ⁻¹' s) = lift.{u} #s := by
  apply mk_preimage_of_injective_of_subset_range_lift _ _ f.injective
  rw [f.range_eq_univ]
  exact fun _ _ ↦ ⟨⟩

@[simp]
theorem mk_preimage_equiv (f : α ≃ β) (s : Set β) : #(f ⁻¹' s) = #s := by
  simpa using mk_preimage_equiv_lift f s

theorem mk_preimage_of_injective (f : α → β) (s : Set β) (h : Injective f) :
    #(f ⁻¹' s) ≤ #s := by
  rw [← lift_id #(↑(f ⁻¹' s)), ← lift_id #(↑s)]
  exact mk_preimage_of_injective_lift f s h

theorem mk_preimage_of_subset_range (f : α → β) (s : Set β) (h : s ⊆ range f) :
    #s ≤ #(f ⁻¹' s) := by
  rw [← lift_id #(↑(f ⁻¹' s)), ← lift_id #(↑s)]
  exact mk_preimage_of_subset_range_lift f s h

theorem mk_subset_ge_of_subset_image_lift {α : Type u} {β : Type v} (f : α → β) {s : Set α}
    {t : Set β} (h : t ⊆ f '' s) : lift.{u} #t ≤ lift.{v} #({ x ∈ s | f x ∈ t } : Set α) := by
  rw [image_eq_range] at h
  convert mk_preimage_of_subset_range_lift _ _ h using 1
  rw [mk_sep]
  rfl

theorem mk_subset_ge_of_subset_image (f : α → β) {s : Set α} {t : Set β} (h : t ⊆ f '' s) :
    #t ≤ #({ x ∈ s | f x ∈ t } : Set α) := by
  rw [image_eq_range] at h
  convert mk_preimage_of_subset_range _ _ h using 1
  rw [mk_sep]
  rfl

theorem le_mk_iff_exists_subset {c : Cardinal} {α : Type u} {s : Set α} :
    c ≤ #s ↔ ∃ p : Set α, p ⊆ s ∧ #p = c := by
  rw [le_mk_iff_exists_set, ← Subtype.exists_set_subtype]
  apply exists_congr; intro t; rw [mk_image_eq]; apply Subtype.val_injective

@[simp]
theorem mk_range_inl {α : Type u} {β : Type v} : #(range (@Sum.inl α β)) = lift.{v} #α := by
  rw [← lift_id'.{u, v} #_, (Equiv.Set.rangeInl α β).lift_cardinal_eq, lift_umax.{u, v}]

@[simp]
theorem mk_range_inr {α : Type u} {β : Type v} : #(range (@Sum.inr α β)) = lift.{u} #β := by
  rw [← lift_id'.{v, u} #_, (Equiv.Set.rangeInr α β).lift_cardinal_eq, lift_umax.{v, u}]

theorem two_le_iff : (2 : Cardinal) ≤ #α ↔ ∃ x y : α, x ≠ y := by
  rw [← Nat.cast_two, nat_succ, succ_le_iff, Nat.cast_one, one_lt_iff_nontrivial, nontrivial_iff]

theorem two_le_iff' (x : α) : (2 : Cardinal) ≤ #α ↔ ∃ y : α, y ≠ x := by
  rw [two_le_iff, ← nontrivial_iff, nontrivial_iff_exists_ne x]

theorem mk_eq_two_iff : #α = 2 ↔ ∃ x y : α, x ≠ y ∧ ({x, y} : Set α) = univ := by
  classical
  simp only [← @Nat.cast_two Cardinal, mk_eq_nat_iff_finset, Finset.card_eq_two]
  constructor
  · rintro ⟨t, ht, x, y, hne, rfl⟩
    exact ⟨x, y, hne, by simpa using ht⟩
  · rintro ⟨x, y, hne, h⟩
    exact ⟨{x, y}, by simpa using h, x, y, hne, rfl⟩

theorem mk_eq_two_iff' (x : α) : #α = 2 ↔ ∃! y, y ≠ x := by
  rw [mk_eq_two_iff]; constructor
  · rintro ⟨a, b, hne, h⟩
    simp only [eq_univ_iff_forall, mem_insert_iff, mem_singleton_iff] at h
    rcases h x with (rfl | rfl)
    exacts [⟨b, hne.symm, fun z => (h z).resolve_left⟩, ⟨a, hne, fun z => (h z).resolve_right⟩]
  · rintro ⟨y, hne, hy⟩
    exact ⟨x, y, hne.symm, eq_univ_of_forall fun z => or_iff_not_imp_left.2 (hy z)⟩

theorem exists_notMem_of_length_lt {α : Type*} (l : List α) (h : ↑l.length < #α) :
    ∃ z : α, z ∉ l := by
  classical
  contrapose! h
  calc
    #α = #(Set.univ : Set α) := mk_univ.symm
    _ ≤ #l.toFinset := mk_le_mk_of_subset fun x _ => List.mem_toFinset.mpr (h x)
    _ = l.toFinset.card := Cardinal.mk_coe_finset
    _ ≤ l.length := Nat.cast_le.mpr (List.toFinset_card_le l)

@[deprecated (since := "2025-05-23")]
alias exists_not_mem_of_length_lt := exists_notMem_of_length_lt

theorem three_le {α : Type*} (h : 3 ≤ #α) (x : α) (y : α) : ∃ z : α, z ≠ x ∧ z ≠ y := by
  have : ↑(3 : ℕ) ≤ #α := by simpa using h
  have : ↑(2 : ℕ) < #α := by rwa [← succ_le_iff, ← Cardinal.nat_succ]
  have := exists_notMem_of_length_lt [x, y] this
  simpa [not_or] using this

/-! ### `powerlt` operation -/

/-- The function `a ^< b`, defined as the supremum of `a ^ c` for `c < b`. -/
def powerlt (a b : Cardinal.{u}) : Cardinal.{u} :=
  ⨆ c : Iio b, a ^ (c : Cardinal)

@[inherit_doc]
infixl:80 " ^< " => powerlt

theorem le_powerlt {b c : Cardinal.{u}} (a) (h : c < b) : (a^c) ≤ a ^< b := by
  refine le_ciSup (f := fun y : Iio b => a ^ (y : Cardinal)) ?_ ⟨c, h⟩
  rw [← image_eq_range]
  exact bddAbove_image.{u, u} _ bddAbove_Iio

theorem powerlt_le {a b c : Cardinal.{u}} : a ^< b ≤ c ↔ ∀ x < b, a ^ x ≤ c := by
  rw [powerlt, ciSup_le_iff']
  · simp
  · rw [← image_eq_range]
    exact bddAbove_image.{u, u} _ bddAbove_Iio

theorem powerlt_le_powerlt_left {a b c : Cardinal} (h : b ≤ c) : a ^< b ≤ a ^< c :=
  powerlt_le.2 fun _ hx => le_powerlt a <| hx.trans_le h

theorem powerlt_mono_left (a) : Monotone fun c => a ^< c := fun _ _ => powerlt_le_powerlt_left

theorem powerlt_succ {a b : Cardinal} (h : a ≠ 0) : a ^< succ b = a ^ b :=
  (powerlt_le.2 fun _ h' => power_le_power_left h <| le_of_lt_succ h').antisymm <|
    le_powerlt a (lt_succ b)

theorem powerlt_min {a b c : Cardinal} : a ^< min b c = min (a ^< b) (a ^< c) :=
  (powerlt_mono_left a).map_min

theorem powerlt_max {a b c : Cardinal} : a ^< max b c = max (a ^< b) (a ^< c) :=
  (powerlt_mono_left a).map_max

theorem zero_powerlt {a : Cardinal} (h : a ≠ 0) : 0 ^< a = 1 := by
  apply (powerlt_le.2 fun c _ => zero_power_le _).antisymm
  rw [← power_zero]
  exact le_powerlt 0 (pos_iff_ne_zero.2 h)

@[simp]
theorem powerlt_zero {a : Cardinal} : a ^< 0 = 0 := by
  convert Cardinal.iSup_of_empty _
  exact Subtype.isEmpty_of_false fun x => mem_Iio.not.mpr (Cardinal.zero_le x).not_gt

end Cardinal
