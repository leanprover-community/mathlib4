/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Arithmetic on families of ordinals

This file proves basic results about the suprema of families of ordinals.

Various other basic arithmetic results are given in `Principal.lean` instead.
-/

@[expose] public noncomputable section

assert_not_exists Field Module

open Function Cardinal Set Order

universe u v w

namespace Ordinal

variable {α β : Type*}

/-! ### Supremum of a family of ordinals -/

theorem bddAbove_of_small {s : Set Ordinal.{u}} [Small.{u} s] : BddAbove s := by
  obtain ⟨a, ha⟩ := Cardinal.bddAbove_of_small (s := (succ ∘ card) '' s)
  refine ⟨a.ord, fun b hb ↦ le_of_lt ?_⟩
  simpa [lt_ord] using ha (mem_image_of_mem _ hb)

@[deprecated bddAbove_of_small +typeChanged (since := "2026-04-04")]
theorem bddAbove_range {ι : Type u} (f : ι → Ordinal.{max u v}) : BddAbove (Set.range f) :=
  bddAbove_of_small

theorem bddAbove_iff_small {s : Set Ordinal.{u}} : BddAbove s ↔ Small.{u} s :=
  ⟨fun ⟨a, h⟩ ↦ small_subset (s := Iic a) fun _ hx ↦ h hx, fun _ ↦ bddAbove_of_small⟩

theorem bddAbove_image {s : Set Ordinal.{u}} (hf : BddAbove s)
    (f : Ordinal.{u} → Ordinal.{max u v}) : BddAbove (f '' s) := by
  rw [bddAbove_iff_small] at hf ⊢
  exact small_lift _

theorem bddAbove_range_comp {ι : Type u} {f : ι → Ordinal.{v}} (hf : BddAbove (range f))
    (g : Ordinal.{v} → Ordinal.{max v w}) : BddAbove (range (g ∘ f)) := by
  rw [range_comp]
  exact bddAbove_image hf g

/-- `le_ciSup` whenever the input type is small in the output universe. This lemma sometimes
fails to infer `f` in simple cases and needs it to be given explicitly. -/
protected theorem le_iSup {ι} (f : ι → Ordinal.{u}) [Small.{u} ι] : ∀ i, f i ≤ ⨆ i, f i :=
  le_ciSup bddAbove_of_small

/-- `ciSup_le_iff'` whenever the input type is small in the output universe. -/
@[simp]
protected theorem iSup_le_iff {ι} {f : ι → Ordinal.{u}} {a : Ordinal.{u}} [Small.{u} ι] :
    ⨆ i, f i ≤ a ↔ ∀ i, f i ≤ a :=
  ciSup_le_iff' bddAbove_of_small

/-- An alias of `ciSup_le'` for discoverability. -/
protected theorem iSup_le {ι} {f : ι → Ordinal} {a} : (∀ i, f i ≤ a) → ⨆ i, f i ≤ a :=
  ciSup_le'

/-- `lt_ciSup_iff'` whenever the input type is small in the output universe. -/
@[simp]
protected theorem lt_iSup_iff {ι} {f : ι → Ordinal.{u}} {a : Ordinal.{u}} [Small.{u} ι] :
    a < ⨆ i, f i ↔ ∃ i, a < f i :=
  lt_ciSup_iff' bddAbove_of_small

theorem lt_iSup_add_one {ι} (f : ι → Ordinal.{u}) [Small.{u} ι] (i) : f i < ⨆ i, f i + 1 := by
  rw [← add_one_le_iff]
  apply Ordinal.le_iSup

theorem iSup_add_one_le_iff {ι} {f : ι → Ordinal.{u}} {a : Ordinal.{u}} [Small.{u} ι] :
    ⨆ i, f i + 1 ≤ a ↔ ∀ i, f i < a := by
  simp

theorem iSup_add_one_le {ι} {f : ι → Ordinal.{u}} {a} (h : ∀ i, f i < a) : ⨆ i, f i + 1 ≤ a :=
  ciSup_le' (by simpa)

theorem lt_iSup_add_one_iff {ι} {f : ι → Ordinal.{u}} {a} [Small.{u} ι] :
    a < ⨆ i, f i + 1 ↔ ∃ i, a ≤ f i := by
  simp

-- TODO: state in terms of `IsSuccLimit`.
theorem succ_lt_iSup_of_ne_iSup {ι} {f : ι → Ordinal.{u}} [Small.{u} ι]
    (hf : ∀ i, f i ≠ iSup f) {a} (hao : a < iSup f) : succ a < iSup f := by
  by_contra! hoa
  exact hao.not_ge (Ordinal.iSup_le fun i ↦ le_of_lt_succ <|
    ((Ordinal.le_iSup _ _).lt_of_ne (hf i)).trans_le hoa)

-- TODO: generalize to conditionally complete lattices.
theorem iSup_eq_zero_iff {ι} {f : ι → Ordinal.{u}} [Small.{u} ι] :
    iSup f = 0 ↔ ∀ i, f i = 0 := by
  refine
    ⟨fun h i => ?_, fun h =>
      le_antisymm (Ordinal.iSup_le fun i => nonpos_iff_eq_zero.2 (h i)) zero_le⟩
  rw [← nonpos_iff_eq_zero, ← h]
  exact Ordinal.le_iSup f i

@[deprecated congrArg +typeChanged (since := "2026-03-27")]
theorem iSup_eq_of_range_eq {ι ι'} {f : ι → Ordinal} {g : ι' → Ordinal}
    (h : Set.range f = Set.range g) : iSup f = iSup g :=
  congr_arg _ h

-- TODO: generalize to conditionally complete lattices
theorem iSup_sum {α β} (f : α ⊕ β → Ordinal.{u}) [Small.{u} α] [Small.{u} β] :
    iSup f = max (⨆ a, f (Sum.inl a)) (⨆ b, f (Sum.inr b)) := by
  apply (Ordinal.iSup_le _).antisymm (max_le _ _)
  · rintro (i | i)
    · exact le_max_of_le_left (Ordinal.le_iSup (fun x ↦ f (Sum.inl x)) i)
    · exact le_max_of_le_right (Ordinal.le_iSup (fun x ↦ f (Sum.inr x)) i)
  all_goals
    apply csSup_le_csSup' bddAbove_of_small
    rintro i ⟨a, rfl⟩
    apply mem_range_self

@[deprecated "deprecated without replacement" (since := "2026-09-20")]
theorem unbounded_range_of_le_iSup {α β : Type u} [LinearOrder α] [WellFoundedLT α] (f : β → α)
    (h : typeLT α ≤ ⨆ i, typein (f i)) : Unbounded (· < ·) (range f) :=
  (not_bounded_iff _).1 fun ⟨x, hx⟩ =>
    h.not_gt <| lt_of_le_of_lt
      (Ordinal.iSup_le fun y => (typein.lt_iff_lt.2 <| hx _ <| mem_range_self y).le)
      (typein_lt_type x)

theorem sSup_ord (s : Set Cardinal) : (sSup s).ord = sSup (ord '' s) := by
  obtain rfl | hn := s.eq_empty_or_nonempty
  · simp
  · by_cases hs : BddAbove s
    · exact isNormal_ord.map_sSup hn hs
    · rw [csSup_of_not_bddAbove hs, csSup_of_not_bddAbove (bddAbove_ord_image_iff.not.2 hs)]
      simp

theorem iSup_ord {ι} (f : ι → Cardinal) : (⨆ i, f i).ord = ⨆ i, (f i).ord := by
  rw [iSup, iSup, sSup_ord, range_comp']

theorem lift_card_sInf_compl_le (s : Set Ordinal.{u}) :
    Cardinal.lift.{u + 1} (sInf sᶜ).card ≤ #s := by
  rw [← Cardinal.mk_Iio_ordinal]
  refine mk_le_mk_of_subset fun x (hx : x < _) ↦ ?_
  rw [← not_notMem]
  exact notMem_of_lt_csInf' hx

theorem card_sInf_range_compl_le_lift {ι : Type u} (f : ι → Ordinal.{max u v}) :
    (sInf (range f)ᶜ).card ≤ Cardinal.lift.{v} #ι := by
  rw [← Cardinal.lift_le.{max u v + 1}, Cardinal.lift_lift]
  apply (lift_card_sInf_compl_le _).trans
  rw [← Cardinal.lift_id'.{u, max u v + 1} #(range _)]
  exact mk_range_le_lift

theorem card_sInf_range_compl_le {ι : Type u} (f : ι → Ordinal.{u}) :
    (sInf (range f)ᶜ).card ≤ #ι :=
  Cardinal.lift_id #ι ▸ card_sInf_range_compl_le_lift f

theorem sInf_compl_lt_lift_ord_succ {ι : Type u} (f : ι → Ordinal.{max u v}) :
    sInf (range f)ᶜ < lift.{v} (succ #ι).ord := by
  rw [lift_ord, Cardinal.lift_succ, ← card_le_iff]
  exact card_sInf_range_compl_le_lift f

theorem sInf_compl_lt_ord_succ {ι : Type u} (f : ι → Ordinal.{u}) :
    sInf (range f)ᶜ < (succ #ι).ord :=
  lift_id (succ #ι).ord ▸ sInf_compl_lt_lift_ord_succ f

theorem bddAbove_add_one_image_iff {s : Set Ordinal} :
    BddAbove ((· + 1) '' s) ↔ BddAbove s := by
  constructor <;> rintro ⟨a, ha⟩
  · exact ⟨a, fun b hb ↦ (lt_add_one _).le.trans (ha (mem_image_of_mem _ hb))⟩
  · use a + 1
    simpa [upperBounds]

theorem bddAbove_range_add_one_iff {f : β → Ordinal.{u}} :
    BddAbove (range fun i ↦ f i + 1) ↔ BddAbove (range f) := by
  rw [range_comp' (· + 1), bddAbove_add_one_image_iff]

theorem sSup_le_sSup_add_one (s : Set Ordinal) : sSup s ≤ sSup ((· + 1) '' s) := by
  by_cases hs : BddAbove s
  · have hs' := bddAbove_add_one_image_iff.2 hs
    rw [csSup_le_iff' hs]
    exact fun x hx ↦ (lt_add_one _).le.trans (le_csSup hs' (mem_image_of_mem _ hx))
  · rw [csSup_of_not_bddAbove hs, csSup_of_not_bddAbove (s := _ '' _)]
    rwa [bddAbove_add_one_image_iff]

theorem iSup_le_iSup_add_one (f : β → Ordinal) : ⨆ i, f i ≤ ⨆ i, f i + 1 := by
  rw [iSup, iSup, range_comp' (· + 1)]
  exact sSup_le_sSup_add_one _

theorem iSup_add_one {β : Type*} [LinearOrder β] [NoMaxOrder β]
    {f : β → Ordinal.{u}} (hf : StrictMono f) : ⨆ i, f i + 1 = ⨆ i, f i := by
  apply (iSup_le_iSup_add_one f).antisymm'
  by_cases hf' : BddAbove (range f)
  · rw [ciSup_le_iff' (bddAbove_range_add_one_iff.2 hf')]
    intro i
    obtain ⟨j, hj⟩ := exists_gt i
    apply (le_ciSup hf' j).trans'
    rw [add_one_le_iff]
    exact hf hj
  · rw [ciSup_of_not_bddAbove hf', ciSup_of_not_bddAbove]
    rwa [← bddAbove_range_add_one_iff] at hf'

theorem iSup_Iio_add_one {a : Ordinal.{u}} {f : Iio a → Ordinal.{u}}
    (hf : StrictMono f) (ha : IsSuccPrelimit a) : ⨆ i : Iio a, f i + 1 = ⨆ i : Iio a, f i := by
  have := ha.noMaxOrder_Iio
  exact iSup_add_one hf

end Ordinal

/-! ### Results about injectivity and surjectivity -/

theorem not_surjective_of_ordinal {α : Type*} [Small.{u} α] (f : α → Ordinal.{u}) :
    ¬ Surjective f := by
  intro h
  obtain ⟨a, ha⟩ := h (⨆ i, succ (f i))
  apply ha.not_lt
  rw [Ordinal.lt_iSup_iff]
  exact ⟨a, Order.lt_succ _⟩

theorem not_injective_of_ordinal {α : Type*} [Small.{u} α] (f : Ordinal.{u} → α) :
    ¬ Injective f := fun h ↦ not_surjective_of_ordinal _ (invFun_surjective h)

/-- The type of ordinals in universe `u` is not `Small.{u}`. This is the type-theoretic analog of
the Burali-Forti paradox. -/
theorem not_small_ordinal : ¬Small.{u} Ordinal.{max u v} := fun h =>
  @not_injective_of_ordinal _ h _ fun _a _b => Ordinal.lift_inj.{v, u}.1

instance Ordinal.uncountable : Uncountable Ordinal.{u} :=
  Uncountable.of_not_small not_small_ordinal.{u}

theorem Ordinal.not_bddAbove_compl_of_small (s : Set Ordinal.{u}) [hs : Small.{u} s] :
    ¬BddAbove sᶜ := by
  rw [bddAbove_iff_small]
  intro h
  have := small_union s sᶜ
  rw [union_compl_self, small_univ_iff] at this
  exact not_small_ordinal this

namespace Ordinal

/-! ### Casting naturals into ordinals, compatibility with operations -/

@[simp]
theorem iSup_natCast : iSup Nat.cast = ω :=
  (Ordinal.iSup_le fun n => (natCast_lt_omega0 n).le).antisymm <| omega0_le.2 <| Ordinal.le_iSup _

theorem apply_omega0_of_isNormal {f : Ordinal.{u} → Ordinal.{v}} (hf : IsNormal f) :
    ⨆ n : ℕ, f n = f ω := by
  rw [← iSup_natCast, hf.map_iSup bddAbove_of_small]

@[simp]
theorem add_iSup (o : Ordinal.{u}) {ι} [Small.{u} ι] [Nonempty ι] (f : ι → Ordinal) :
    o + ⨆ i, f i = ⨆ i, o + f i :=
  (isNormal_add_right o).map_iSup bddAbove_of_small

@[simp]
theorem add_sSup (o : Ordinal.{u}) {s : Set Ordinal} [Small.{u} s] (hs : s.Nonempty) :
    o + sSup s = sSup ((o + ·) '' s) :=
  (isNormal_add_right o).map_sSup hs bddAbove_of_small

@[simp]
lemma mul_sSup (o : Ordinal) (s : Set Ordinal) : o * sSup s = sSup ((o * ·) '' s) := by
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · simp
  rcases eq_zero_or_pos o with (rfl | ho)
  · simp [hs.image_const]
  by_cases bdd : BddAbove s
  · exact (isNormal_mul_right ho).map_sSup hs bdd
  · rw [csSup_of_not_bddAbove bdd, csSup_empty, csSup_of_not_bddAbove]
    · simp
    exact fun ⟨u, hu⟩ ↦ bdd ⟨u, fun x hx ↦ (x.le_mul_right ho).trans (hu ⟨x, hx, rfl⟩)⟩

@[simp]
lemma mul_iSup (o : Ordinal) {ι} (f : ι → Ordinal) : o * ⨆ i, f i = ⨆ i, o * f i := by
  rw [← sSup_range, mul_sSup, ← Set.range_comp', sSup_range]

@[simp]
theorem iSup_add_natCast (o : Ordinal) : ⨆ n : ℕ, o + n = o + ω := by
  rw [← iSup_natCast, Ordinal.add_iSup]

@[simp]
theorem iSup_mul_natCast (o : Ordinal) : ⨆ n : ℕ, o * n = o * ω := by
  rw [← iSup_natCast, Ordinal.mul_iSup]

end Ordinal
