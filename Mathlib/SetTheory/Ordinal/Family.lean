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

/-- Converts a family indexed by a `Type u` to one indexed by an `Ordinal.{u}` using a specified
well-ordering. -/
@[deprecated enum +typeChanged (since := "2026-04-06")]
def bfamilyOfFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α) :
    ∀ a < type r, α := fun a ha => f (enum r ⟨a, ha⟩)

/-- Converts a family indexed by a `Type u` to one indexed by an `Ordinal.{u}` using a well-ordering
given by the axiom of choice. -/
@[deprecated enum +typeChanged (since := "2026-04-06")]
def bfamilyOfFamily {ι : Type u} : (ι → α) → ∀ a < type (@WellOrderingRel ι), α :=
  bfamilyOfFamily' WellOrderingRel

/-- Converts a family indexed by an `Ordinal.{u}` to one indexed by a `Type u` using a specified
well-ordering. -/
@[deprecated typein +typeChanged (since := "2026-04-06")]
def familyOfBFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o} (ho : type r = o)
    (f : ∀ a < o, α) : ι → α := fun i =>
  f (typein r i)
    (by
      rw [← ho]
      exact typein_lt_type r i)

/-- Converts a family indexed by an `Ordinal.{u}` to one indexed by a `Type u` using a well-ordering
given by the axiom of choice. -/
@[deprecated typein +typeChanged (since := "2026-04-06")]
def familyOfBFamily (o : Ordinal) (f : ∀ a < o, α) : o.ToType → α :=
  familyOfBFamily' (· < ·) (type_toType o) f

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
theorem bfamilyOfFamily'_typein {ι} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α) (i) :
    bfamilyOfFamily' r f (typein r i) (typein_lt_type r i) = f i := by
  simp only [bfamilyOfFamily', enum_typein]

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
theorem bfamilyOfFamily_typein {ι} (f : ι → α) (i) :
    bfamilyOfFamily f (typein _ i) (typein_lt_type _ i) = f i :=
  bfamilyOfFamily'_typein _ f i

set_option backward.isDefEq.respectTransparency false in
@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
theorem familyOfBFamily'_enum {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o}
    (ho : type r = o) (f : ∀ a < o, α) (i hi) :
    familyOfBFamily' r ho f (enum r ⟨i, by rwa [ho]⟩) = f i hi := by
  simp only [familyOfBFamily', typein_enum]

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
theorem familyOfBFamily_enum (o : Ordinal) (f : ∀ a < o, α) (i hi) :
    familyOfBFamily o f (enum (α := o.ToType) (· < ·) ⟨i, hi.trans_eq (type_toType _).symm⟩)
    = f i hi :=
  familyOfBFamily'_enum _ (type_toType o) f _ _

/-- The range of a family indexed by ordinals. -/
@[deprecated range +typeChanged (since := "2026-04-06")]
def brange (o : Ordinal) (f : ∀ a < o, α) : Set α :=
  { a | ∃ i hi, f i hi = a }

@[deprecated mem_range +typeChanged (since := "2026-04-06")]
theorem mem_brange {o : Ordinal} {f : ∀ a < o, α} {a} : a ∈ brange o f ↔ ∃ i hi, f i hi = a :=
  Iff.rfl

@[deprecated mem_range_self +typeChanged (since := "2026-04-06")]
theorem mem_brange_self {o} (f : ∀ a < o, α) (i hi) : f i hi ∈ brange o f :=
  ⟨i, hi, rfl⟩

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
theorem range_familyOfBFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o}
    (ho : type r = o) (f : ∀ a < o, α) : range (familyOfBFamily' r ho f) = brange o f := by
  refine Set.ext fun a => ⟨?_, ?_⟩
  · rintro ⟨b, rfl⟩
    apply mem_brange_self
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, familyOfBFamily'_enum _ _ _ _ _⟩

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
theorem range_familyOfBFamily {o} (f : ∀ a < o, α) : range (familyOfBFamily o f) = brange o f :=
  range_familyOfBFamily' _ _ f

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
theorem brange_bfamilyOfFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α) :
    brange _ (bfamilyOfFamily' r f) = range f := by
  refine Set.ext fun a => ⟨?_, ?_⟩
  · rintro ⟨i, hi, rfl⟩
    apply mem_range_self
  · rintro ⟨b, rfl⟩
    exact ⟨_, _, bfamilyOfFamily'_typein _ _ _⟩

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
theorem brange_bfamilyOfFamily {ι : Type u} (f : ι → α) : brange _ (bfamilyOfFamily f) = range f :=
  brange_bfamilyOfFamily' _ _

@[deprecated "brange is deprecated" (since := "2026-04-06")]
theorem brange_const {o : Ordinal} (ho : o ≠ 0) {c : α} : (brange o fun _ _ => c) = {c} := by
  rw [← range_familyOfBFamily]
  exact @Set.range_const _ o.ToType (nonempty_toType_iff.2 ho) c

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
theorem comp_bfamilyOfFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α)
    (g : α → β) : (fun i hi => g (bfamilyOfFamily' r f i hi)) = bfamilyOfFamily' r (g ∘ f) :=
  rfl

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
theorem comp_bfamilyOfFamily {ι : Type u} (f : ι → α) (g : α → β) :
    (fun i hi => g (bfamilyOfFamily f i hi)) = bfamilyOfFamily (g ∘ f) :=
  rfl

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
theorem comp_familyOfBFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o}
    (ho : type r = o) (f : ∀ a < o, α) (g : α → β) :
    g ∘ familyOfBFamily' r ho f = familyOfBFamily' r ho fun i hi => g (f i hi) :=
  rfl

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
theorem comp_familyOfBFamily {o} (f : ∀ a < o, α) (g : α → β) :
    g ∘ familyOfBFamily o f = familyOfBFamily o fun i hi => g (f i hi) :=
  rfl

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

theorem unbounded_range_of_le_iSup {α β : Type u} (r : α → α → Prop) [IsWellOrder α r] (f : β → α)
    (h : type r ≤ ⨆ i, typein r (f i)) : Unbounded r (range f) :=
  (not_bounded_iff _).1 fun ⟨x, hx⟩ =>
    h.not_gt <| lt_of_le_of_lt
      (Ordinal.iSup_le fun y => ((typein_lt_typein r).2 <| hx _ <| mem_range_self y).le)
      (typein_lt_type r x)

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

section bsup

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
theorem iSup_eq_iSup {ι ι' : Type u} (r : ι → ι → Prop) (r' : ι' → ι' → Prop) [IsWellOrder ι r]
    [IsWellOrder ι' r'] {o : Ordinal} (ho : type r = o) (ho' : type r' = o) (f : ∀ a < o, Ordinal) :
    iSup (familyOfBFamily' r ho f) = iSup (familyOfBFamily' r' ho' f) :=
  congrArg sSup (by simp_rw [range_familyOfBFamily'])

/-- The supremum of a family of ordinals indexed by the set of ordinals less than some
`o : Ordinal.{u}`. This is a special case of `iSup` over the family provided by
`familyOfBFamily`. -/
@[deprecated "write `⨆ i : Iio a, f i` instead." (since := "2026-04-05")]
def bsup (o : Ordinal.{u}) (f : ∀ a < o, Ordinal.{max u v}) : Ordinal.{max u v} :=
  iSup (familyOfBFamily o f)

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem iSup_eq_bsup {o : Ordinal} (f : ∀ a < o, Ordinal) :
    iSup (familyOfBFamily o f) = bsup o f :=
  rfl

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem iSup'_eq_bsup {o : Ordinal} {ι} (r : ι → ι → Prop) [IsWellOrder ι r] (ho : type r = o)
    (f : ∀ a < o, Ordinal) : iSup (familyOfBFamily' r ho f) = bsup o f :=
  iSup_eq_iSup r _ ho _ f

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem sSup_eq_bsup {o : Ordinal} (f : ∀ a < o, Ordinal) : sSup (brange o f) = bsup o f := by
  congr
  rw [range_familyOfBFamily]

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup'_eq_iSup {ι} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → Ordinal) :
    bsup _ (bfamilyOfFamily' r f) = iSup f := by
  simp +unfoldPartialApp only [← iSup'_eq_bsup r, enum_typein, familyOfBFamily', bfamilyOfFamily']

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_eq_iSup {ι} (f : ι → Ordinal) : bsup _ (bfamilyOfFamily f) = iSup f :=
  bsup'_eq_iSup _ f

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_eq_bsup {ι : Type u} (r r' : ι → ι → Prop) [IsWellOrder ι r] [IsWellOrder ι r']
    (f : ι → Ordinal.{max u v}) :
    bsup.{_, v} _ (bfamilyOfFamily' r f) = bsup.{_, v} _ (bfamilyOfFamily' r' f) := by
  rw [bsup'_eq_iSup, bsup'_eq_iSup]

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_congr {o₁ o₂ : Ordinal.{u}} (f : ∀ a < o₁, Ordinal.{max u v}) (ho : o₁ = o₂) :
    bsup.{_, v} o₁ f = bsup.{_, v} o₂ fun a h => f a (h.trans_eq ho.symm) := by
  subst ho
  rfl

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_le_iff {o f a} : bsup.{u, v} o f ≤ a ↔ ∀ i h, f i h ≤ a :=
  Ordinal.iSup_le_iff.trans
    ⟨fun h i hi => by
      rw [← familyOfBFamily_enum o f]
      exact h _, fun h _ => h _ _⟩

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_le {o : Ordinal} {f : ∀ b < o, Ordinal} {a} :
    (∀ i h, f i h ≤ a) → bsup.{u, v} o f ≤ a :=
  bsup_le_iff.2

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem le_bsup {o} (f : ∀ a < o, Ordinal) (i h) : f i h ≤ bsup o f :=
  bsup_le_iff.1 le_rfl _ _

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem lt_bsup {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) {a} :
    a < bsup.{_, v} o f ↔ ∃ i hi, a < f i hi := by
  simpa only [not_forall, not_le] using not_congr (@bsup_le_iff.{_, v} _ f a)

@[deprecated IsNormal.map_iSup +typeChanged (since := "2026-04-05")]
theorem IsNormal.bsup {f : Ordinal → Ordinal} (H : IsNormal f) {o : Ordinal} :
    ∀ (g : ∀ a < o, Ordinal), o ≠ 0 → f (bsup o g) = bsup o fun a h => f (g a h) :=
  inductionOn o fun α r _ g h => by
    have := type_ne_zero_iff_nonempty.1 h
    rw [← iSup'_eq_bsup r, Order.IsNormal.map_iSup H bddAbove_of_small, ← iSup'_eq_bsup r] <;>
      rfl

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem lt_bsup_of_ne_bsup {o : Ordinal.{u}} {f : ∀ a < o, Ordinal.{max u v}} :
    (∀ i h, f i h ≠ bsup.{_, v} o f) ↔ ∀ i h, f i h < bsup.{_, v} o f :=
  ⟨fun hf _ _ => lt_of_le_of_ne (le_bsup _ _ _) (hf _ _), fun hf _ _ => ne_of_lt (hf _ _)⟩

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_not_succ_of_ne_bsup {o : Ordinal.{u}} {f : ∀ a < o, Ordinal.{max u v}}
    (hf : ∀ {i : Ordinal} (h : i < o), f i h ≠ bsup.{_, v} o f) (a) :
    a < bsup.{_, v} o f → succ a < bsup.{_, v} o f := by
  rw [← iSup_eq_bsup] at *
  exact succ_lt_iSup_of_ne_iSup fun i => hf _

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_eq_zero_iff {o} {f : ∀ a < o, Ordinal} : bsup o f = 0 ↔ ∀ i hi, f i hi = 0 := by
  refine
    ⟨fun h i hi => ?_, fun h =>
      le_antisymm (bsup_le fun i hi => nonpos_iff_eq_zero.2 (h i hi)) zero_le⟩
  rw [← nonpos_iff_eq_zero, ← h]
  exact le_bsup f i hi

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem lt_bsup_of_limit {o : Ordinal} {f : ∀ a < o, Ordinal}
    (hf : ∀ {a a'} (ha : a < o) (ha' : a' < o), a < a' → f a ha < f a' ha')
    (ho : ∀ a < o, succ a < o) (i h) : f i h < bsup o f :=
  (hf _ _ <| lt_succ i).trans_le (le_bsup f (succ i) <| ho _ h)

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_succ_of_mono {o : Ordinal} {f : ∀ a < succ o, Ordinal}
    (hf : ∀ {i j} (hi hj), i ≤ j → f i hi ≤ f j hj) : bsup _ f = f o (lt_succ o) :=
  le_antisymm (bsup_le fun _i hi => hf _ _ <| le_of_lt_succ hi) (le_bsup _ _ _)

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_zero (f : ∀ a < (0 : Ordinal), Ordinal) : bsup 0 f = 0 :=
  bsup_eq_zero_iff.2 fun _i hi => (not_lt_zero hi).elim

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_const {o : Ordinal.{u}} (ho : o ≠ 0) (a : Ordinal.{max u v}) :
    (bsup.{_, v} o fun _ _ => a) = a :=
  le_antisymm (bsup_le fun _ _ => le_rfl) (le_bsup _ 0 (pos_iff_ne_zero.2 ho))

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_one (f : ∀ a < (1 : Ordinal), Ordinal) : bsup 1 f = f 0 zero_lt_one := by
  simp_rw [← iSup_eq_bsup, ciSup_unique, familyOfBFamily, familyOfBFamily', typein_one_toType]

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_le_of_brange_subset {o o'} {f : ∀ a < o, Ordinal} {g : ∀ a < o', Ordinal}
    (h : brange o f ⊆ brange o' g) : bsup.{u, max v w} o f ≤ bsup.{v, max u w} o' g :=
  bsup_le fun i hi => by
    obtain ⟨j, hj, hj'⟩ := h ⟨i, hi, rfl⟩
    rw [← hj']
    apply le_bsup

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_eq_of_brange_eq {o o'} {f : ∀ a < o, Ordinal} {g : ∀ a < o', Ordinal}
    (h : brange o f = brange o' g) : bsup.{u, max v w} o f = bsup.{v, max u w} o' g :=
  (bsup_le_of_brange_subset.{u, v, w} h.le).antisymm (bsup_le_of_brange_subset.{v, u, w} h.ge)

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem iSup_Iio_eq_bsup {o} {f : ∀ a < o, Ordinal} : ⨆ a : Iio o, f a.1 a.2 = bsup o f := by
  simp_rw [Iio, bsup, iSup, range_familyOfBFamily, brange, range, Subtype.exists, mem_ofPred]

end bsup

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
