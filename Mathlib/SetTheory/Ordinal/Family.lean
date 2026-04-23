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
@[deprecated enum (since := "2026-04-06")]
def bfamilyOfFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α) :
    ∀ a < type r, α := fun a ha => f (enum r ⟨a, ha⟩)

set_option linter.deprecated false in
/-- Converts a family indexed by a `Type u` to one indexed by an `Ordinal.{u}` using a well-ordering
given by the axiom of choice. -/
@[deprecated enum (since := "2026-04-06")]
def bfamilyOfFamily {ι : Type u} : (ι → α) → ∀ a < type (@WellOrderingRel ι), α :=
  bfamilyOfFamily' WellOrderingRel

/-- Converts a family indexed by an `Ordinal.{u}` to one indexed by a `Type u` using a specified
well-ordering. -/
@[deprecated typein (since := "2026-04-06")]
def familyOfBFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o} (ho : type r = o)
    (f : ∀ a < o, α) : ι → α := fun i =>
  f (typein r i)
    (by
      rw [← ho]
      exact typein_lt_type r i)

set_option linter.deprecated false in
/-- Converts a family indexed by an `Ordinal.{u}` to one indexed by a `Type u` using a well-ordering
given by the axiom of choice. -/
@[deprecated typein (since := "2026-04-06")]
def familyOfBFamily (o : Ordinal) (f : ∀ a < o, α) : o.ToType → α :=
  familyOfBFamily' (· < ·) (type_toType o) f

set_option linter.deprecated false in
@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
theorem bfamilyOfFamily'_typein {ι} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α) (i) :
    bfamilyOfFamily' r f (typein r i) (typein_lt_type r i) = f i := by
  simp only [bfamilyOfFamily', enum_typein]

set_option linter.deprecated false in
@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
theorem bfamilyOfFamily_typein {ι} (f : ι → α) (i) :
    bfamilyOfFamily f (typein _ i) (typein_lt_type _ i) = f i :=
  bfamilyOfFamily'_typein _ f i

set_option linter.deprecated false in
@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
theorem familyOfBFamily'_enum {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o}
    (ho : type r = o) (f : ∀ a < o, α) (i hi) :
    familyOfBFamily' r ho f (enum r ⟨i, by rwa [ho]⟩) = f i hi := by
  simp only [familyOfBFamily', typein_enum]

set_option linter.deprecated false in
@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
theorem familyOfBFamily_enum (o : Ordinal) (f : ∀ a < o, α) (i hi) :
    familyOfBFamily o f (enum (α := o.ToType) (· < ·) ⟨i, hi.trans_eq (type_toType _).symm⟩)
    = f i hi :=
  familyOfBFamily'_enum _ (type_toType o) f _ _

/-- The range of a family indexed by ordinals. -/
@[deprecated range (since := "2026-04-06")]
def brange (o : Ordinal) (f : ∀ a < o, α) : Set α :=
  { a | ∃ i hi, f i hi = a }

set_option linter.deprecated false in
@[deprecated mem_range (since := "2026-04-06")]
theorem mem_brange {o : Ordinal} {f : ∀ a < o, α} {a} : a ∈ brange o f ↔ ∃ i hi, f i hi = a :=
  Iff.rfl

set_option linter.deprecated false in
@[deprecated mem_range_self (since := "2026-04-06")]
theorem mem_brange_self {o} (f : ∀ a < o, α) (i hi) : f i hi ∈ brange o f :=
  ⟨i, hi, rfl⟩

set_option linter.deprecated false in
@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
theorem range_familyOfBFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o}
    (ho : type r = o) (f : ∀ a < o, α) : range (familyOfBFamily' r ho f) = brange o f := by
  refine Set.ext fun a => ⟨?_, ?_⟩
  · rintro ⟨b, rfl⟩
    apply mem_brange_self
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, familyOfBFamily'_enum _ _ _ _ _⟩

set_option linter.deprecated false in
@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
theorem range_familyOfBFamily {o} (f : ∀ a < o, α) : range (familyOfBFamily o f) = brange o f :=
  range_familyOfBFamily' _ _ f

set_option linter.deprecated false in
@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
theorem brange_bfamilyOfFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α) :
    brange _ (bfamilyOfFamily' r f) = range f := by
  refine Set.ext fun a => ⟨?_, ?_⟩
  · rintro ⟨i, hi, rfl⟩
    apply mem_range_self
  · rintro ⟨b, rfl⟩
    exact ⟨_, _, bfamilyOfFamily'_typein _ _ _⟩

set_option linter.deprecated false in
@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
theorem brange_bfamilyOfFamily {ι : Type u} (f : ι → α) : brange _ (bfamilyOfFamily f) = range f :=
  brange_bfamilyOfFamily' _ _

set_option linter.deprecated false in
@[deprecated "brange is deprecated" (since := "2026-04-06")]
theorem brange_const {o : Ordinal} (ho : o ≠ 0) {c : α} : (brange o fun _ _ => c) = {c} := by
  rw [← range_familyOfBFamily]
  exact @Set.range_const _ o.ToType (nonempty_toType_iff.2 ho) c

set_option linter.deprecated false in
@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
theorem comp_bfamilyOfFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α)
    (g : α → β) : (fun i hi => g (bfamilyOfFamily' r f i hi)) = bfamilyOfFamily' r (g ∘ f) :=
  rfl

set_option linter.deprecated false in
@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
theorem comp_bfamilyOfFamily {ι : Type u} (f : ι → α) (g : α → β) :
    (fun i hi => g (bfamilyOfFamily f i hi)) = bfamilyOfFamily (g ∘ f) :=
  rfl

set_option linter.deprecated false in
@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
theorem comp_familyOfBFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o}
    (ho : type r = o) (f : ∀ a < o, α) (g : α → β) :
    g ∘ familyOfBFamily' r ho f = familyOfBFamily' r ho fun i hi => g (f i hi) :=
  rfl

set_option linter.deprecated false in
@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
theorem comp_familyOfBFamily {o} (f : ∀ a < o, α) (g : α → β) :
    g ∘ familyOfBFamily o f = familyOfBFamily o fun i hi => g (f i hi) :=
  rfl

/-! ### Supremum of a family of ordinals -/

theorem bddAbove_of_small {s : Set Ordinal.{u}} [Small.{u} s] : BddAbove s := by
  obtain ⟨a, ha⟩ := Cardinal.bddAbove_of_small (s := (succ ∘ card) '' s)
  refine ⟨a.ord, fun b hb ↦ le_of_lt ?_⟩
  simpa [lt_ord] using ha (mem_image_of_mem _ hb)

@[deprecated bddAbove_of_small (since := "2026-04-04")]
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
      le_antisymm (Ordinal.iSup_le fun i => nonpos_iff_eq_zero.2 (h i)) (zero_le _)⟩
  rw [← nonpos_iff_eq_zero, ← h]
  exact Ordinal.le_iSup f i

@[deprecated congrArg (since := "2026-03-27")]
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

theorem unbounded_range_of_le_iSup {α β : Type u} (r : α → α → Prop) [IsWellOrder α r] (f : β → α)
    (h : type r ≤ ⨆ i, typein r (f i)) : Unbounded r (range f) :=
  (not_bounded_iff _).1 fun ⟨x, hx⟩ =>
    h.not_gt <| lt_of_le_of_lt
      (Ordinal.iSup_le fun y => ((typein_lt_typein r).2 <| hx _ <| mem_range_self y).le)
      (typein_lt_type r x)

set_option linter.deprecated false in
@[deprecated Order.IsNormal.map_iSup (since := "2025-12-25")]
theorem IsNormal.map_iSup_of_bddAbove {f : Ordinal.{u} → Ordinal.{v}} (H : Ordinal.IsNormal f)
    {ι : Type*} (g : ι → Ordinal.{u}) (hg : BddAbove (range g))
    [Nonempty ι] : f (⨆ i, g i) = ⨆ i, f (g i) :=
  Order.IsNormal.map_iSup H hg

set_option linter.deprecated false in
@[deprecated Order.IsNormal.map_iSup (since := "2025-12-25")]
theorem IsNormal.map_iSup {f : Ordinal.{u} → Ordinal.{v}} (H : Ordinal.IsNormal f)
    {ι : Type w} (g : ι → Ordinal.{u}) [Small.{u} ι] [Nonempty ι] :
    f (⨆ i, g i) = ⨆ i, f (g i) :=
  Order.IsNormal.map_iSup H bddAbove_of_small

set_option linter.deprecated false in
@[deprecated Order.IsNormal.map_sSup (since := "2025-12-25")]
theorem IsNormal.map_sSup_of_bddAbove {f : Ordinal.{u} → Ordinal.{v}} (H : Ordinal.IsNormal f)
    {s : Set Ordinal.{u}} (hs : BddAbove s) (hn : s.Nonempty) : f (sSup s) = sSup (f '' s) :=
  Order.IsNormal.map_sSup H hn hs

set_option linter.deprecated false in
@[deprecated Order.IsNormal.map_sSup (since := "2025-12-25")]
theorem IsNormal.map_sSup {f : Ordinal.{u} → Ordinal.{v}} (H : IsNormal f)
    {s : Set Ordinal.{u}} (hn : s.Nonempty) [Small.{u} s] : f (sSup s) = sSup (f '' s) :=
  Order.IsNormal.map_sSup H hn bddAbove_of_small

set_option linter.deprecated false in
@[deprecated Order.IsNormal.apply_of_isSuccLimit (since := "2025-12-25")]
theorem IsNormal.apply_of_isSuccLimit {f : Ordinal.{u} → Ordinal.{v}} (H : Ordinal.IsNormal f)
    {o : Ordinal} (ho : IsSuccLimit o) : f o = ⨆ a : Iio o, f a :=
  Order.IsNormal.apply_of_isSuccLimit H ho

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

set_option linter.deprecated false in
@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
theorem iSup_eq_iSup {ι ι' : Type u} (r : ι → ι → Prop) (r' : ι' → ι' → Prop) [IsWellOrder ι r]
    [IsWellOrder ι' r'] {o : Ordinal} (ho : type r = o) (ho' : type r' = o) (f : ∀ a < o, Ordinal) :
    iSup (familyOfBFamily' r ho f) = iSup (familyOfBFamily' r' ho' f) :=
  congrArg sSup (by simp_rw [range_familyOfBFamily'])

set_option linter.deprecated false in
/-- The supremum of a family of ordinals indexed by the set of ordinals less than some
`o : Ordinal.{u}`. This is a special case of `iSup` over the family provided by
`familyOfBFamily`. -/
@[deprecated "write `⨆ i : Iio a, f i` instead." (since := "2026-04-05")]
def bsup (o : Ordinal.{u}) (f : ∀ a < o, Ordinal.{max u v}) : Ordinal.{max u v} :=
  iSup (familyOfBFamily o f)

set_option linter.deprecated false in
@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem iSup_eq_bsup {o : Ordinal} (f : ∀ a < o, Ordinal) :
    iSup (familyOfBFamily o f) = bsup o f :=
  rfl

set_option linter.deprecated false in
@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem iSup'_eq_bsup {o : Ordinal} {ι} (r : ι → ι → Prop) [IsWellOrder ι r] (ho : type r = o)
    (f : ∀ a < o, Ordinal) : iSup (familyOfBFamily' r ho f) = bsup o f :=
  iSup_eq_iSup r _ ho _ f

set_option linter.deprecated false in
@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem sSup_eq_bsup {o : Ordinal} (f : ∀ a < o, Ordinal) : sSup (brange o f) = bsup o f := by
  congr
  rw [range_familyOfBFamily]

set_option linter.deprecated false in
@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup'_eq_iSup {ι} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → Ordinal) :
    bsup _ (bfamilyOfFamily' r f) = iSup f := by
  simp +unfoldPartialApp only [← iSup'_eq_bsup r, enum_typein, familyOfBFamily', bfamilyOfFamily']

set_option linter.deprecated false in
@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_eq_iSup {ι} (f : ι → Ordinal) : bsup _ (bfamilyOfFamily f) = iSup f :=
  bsup'_eq_iSup _ f

set_option linter.deprecated false in
@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_eq_bsup {ι : Type u} (r r' : ι → ι → Prop) [IsWellOrder ι r] [IsWellOrder ι r']
    (f : ι → Ordinal.{max u v}) :
    bsup.{_, v} _ (bfamilyOfFamily' r f) = bsup.{_, v} _ (bfamilyOfFamily' r' f) := by
  rw [bsup'_eq_iSup, bsup'_eq_iSup]

set_option linter.deprecated false in
@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_congr {o₁ o₂ : Ordinal.{u}} (f : ∀ a < o₁, Ordinal.{max u v}) (ho : o₁ = o₂) :
    bsup.{_, v} o₁ f = bsup.{_, v} o₂ fun a h => f a (h.trans_eq ho.symm) := by
  subst ho
  rfl

set_option linter.deprecated false in
@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_le_iff {o f a} : bsup.{u, v} o f ≤ a ↔ ∀ i h, f i h ≤ a :=
  Ordinal.iSup_le_iff.trans
    ⟨fun h i hi => by
      rw [← familyOfBFamily_enum o f]
      exact h _, fun h _ => h _ _⟩

set_option linter.deprecated false in
@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_le {o : Ordinal} {f : ∀ b < o, Ordinal} {a} :
    (∀ i h, f i h ≤ a) → bsup.{u, v} o f ≤ a :=
  bsup_le_iff.2

set_option linter.deprecated false in
@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem le_bsup {o} (f : ∀ a < o, Ordinal) (i h) : f i h ≤ bsup o f :=
  bsup_le_iff.1 le_rfl _ _

set_option linter.deprecated false in
@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem lt_bsup {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) {a} :
    a < bsup.{_, v} o f ↔ ∃ i hi, a < f i hi := by
  simpa only [not_forall, not_le] using not_congr (@bsup_le_iff.{_, v} _ f a)

set_option linter.deprecated false in
@[deprecated IsNormal.map_iSup (since := "2026-04-05")]
theorem IsNormal.bsup {f : Ordinal → Ordinal} (H : IsNormal f) {o : Ordinal} :
    ∀ (g : ∀ a < o, Ordinal), o ≠ 0 → f (bsup o g) = bsup o fun a h => f (g a h) :=
  inductionOn o fun α r _ g h => by
    haveI := type_ne_zero_iff_nonempty.1 h
    rw [← iSup'_eq_bsup r, Order.IsNormal.map_iSup H bddAbove_of_small, ← iSup'_eq_bsup r] <;>
      rfl

set_option linter.deprecated false in
@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem lt_bsup_of_ne_bsup {o : Ordinal.{u}} {f : ∀ a < o, Ordinal.{max u v}} :
    (∀ i h, f i h ≠ bsup.{_, v} o f) ↔ ∀ i h, f i h < bsup.{_, v} o f :=
  ⟨fun hf _ _ => lt_of_le_of_ne (le_bsup _ _ _) (hf _ _), fun hf _ _ => ne_of_lt (hf _ _)⟩

set_option linter.deprecated false in
@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_not_succ_of_ne_bsup {o : Ordinal.{u}} {f : ∀ a < o, Ordinal.{max u v}}
    (hf : ∀ {i : Ordinal} (h : i < o), f i h ≠ bsup.{_, v} o f) (a) :
    a < bsup.{_, v} o f → succ a < bsup.{_, v} o f := by
  rw [← iSup_eq_bsup] at *
  exact succ_lt_iSup_of_ne_iSup fun i => hf _

set_option linter.deprecated false in
@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_eq_zero_iff {o} {f : ∀ a < o, Ordinal} : bsup o f = 0 ↔ ∀ i hi, f i hi = 0 := by
  refine
    ⟨fun h i hi => ?_, fun h =>
      le_antisymm (bsup_le fun i hi => nonpos_iff_eq_zero.2 (h i hi)) (zero_le _)⟩
  rw [← nonpos_iff_eq_zero, ← h]
  exact le_bsup f i hi

set_option linter.deprecated false in
@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem lt_bsup_of_limit {o : Ordinal} {f : ∀ a < o, Ordinal}
    (hf : ∀ {a a'} (ha : a < o) (ha' : a' < o), a < a' → f a ha < f a' ha')
    (ho : ∀ a < o, succ a < o) (i h) : f i h < bsup o f :=
  (hf _ _ <| lt_succ i).trans_le (le_bsup f (succ i) <| ho _ h)

set_option linter.deprecated false in
@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_succ_of_mono {o : Ordinal} {f : ∀ a < succ o, Ordinal}
    (hf : ∀ {i j} (hi hj), i ≤ j → f i hi ≤ f j hj) : bsup _ f = f o (lt_succ o) :=
  le_antisymm (bsup_le fun _i hi => hf _ _ <| le_of_lt_succ hi) (le_bsup _ _ _)

set_option linter.deprecated false in
@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_zero (f : ∀ a < (0 : Ordinal), Ordinal) : bsup 0 f = 0 :=
  bsup_eq_zero_iff.2 fun _i hi => (not_lt_zero hi).elim

set_option linter.deprecated false in
@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_const {o : Ordinal.{u}} (ho : o ≠ 0) (a : Ordinal.{max u v}) :
    (bsup.{_, v} o fun _ _ => a) = a :=
  le_antisymm (bsup_le fun _ _ => le_rfl) (le_bsup _ 0 (pos_iff_ne_zero.2 ho))

set_option linter.deprecated false in
@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_one (f : ∀ a < (1 : Ordinal), Ordinal) : bsup 1 f = f 0 zero_lt_one := by
  simp_rw [← iSup_eq_bsup, ciSup_unique, familyOfBFamily, familyOfBFamily', typein_one_toType]

set_option linter.deprecated false in
@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_le_of_brange_subset {o o'} {f : ∀ a < o, Ordinal} {g : ∀ a < o', Ordinal}
    (h : brange o f ⊆ brange o' g) : bsup.{u, max v w} o f ≤ bsup.{v, max u w} o' g :=
  bsup_le fun i hi => by
    obtain ⟨j, hj, hj'⟩ := h ⟨i, hi, rfl⟩
    rw [← hj']
    apply le_bsup

set_option linter.deprecated false in
@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem bsup_eq_of_brange_eq {o o'} {f : ∀ a < o, Ordinal} {g : ∀ a < o', Ordinal}
    (h : brange o f = brange o' g) : bsup.{u, max v w} o f = bsup.{v, max u w} o' g :=
  (bsup_le_of_brange_subset.{u, v, w} h.le).antisymm (bsup_le_of_brange_subset.{v, u, w} h.ge)

set_option linter.deprecated false in
@[deprecated "bsup is deprecated" (since := "2026-04-05")]
theorem iSup_Iio_eq_bsup {o} {f : ∀ a < o, Ordinal} : ⨆ a : Iio o, f a.1 a.2 = bsup o f := by
  simp_rw [Iio, bsup, iSup, range_familyOfBFamily, brange, range, Subtype.exists, mem_setOf]

end bsup

section lsub

/-- The least strict upper bound of a family of ordinals. -/
@[deprecated "write `⨆ i, f i + 1` instead." (since := "2026-03-27")]
def lsub {ι : Type u} (f : ι → Ordinal.{max u v}) : Ordinal :=
  iSup (succ ∘ f)

set_option linter.deprecated false in
@[deprecated "lsub is deprecated" (since := "2026-03-27")]
theorem iSup_eq_lsub {ι} (f : ι → Ordinal) : iSup (succ ∘ f) = lsub f :=
  rfl

set_option linter.deprecated false in
@[deprecated "lsub is deprecated" (since := "2026-03-27")]
theorem lsub_le_iff {ι} {f : ι → Ordinal} {a} : lsub f ≤ a ↔ ∀ i, f i < a :=
  Ordinal.iSup_add_one_le_iff

set_option linter.deprecated false in
@[deprecated "lsub is deprecated" (since := "2026-03-27")]
theorem lsub_le {ι} {f : ι → Ordinal} {a} : (∀ i, f i < a) → lsub f ≤ a :=
  lsub_le_iff.2

set_option linter.deprecated false in
@[deprecated "lsub is deprecated" (since := "2026-03-27")]
theorem lt_lsub {ι} (f : ι → Ordinal) (i) : f i < lsub f :=
  Ordinal.lt_iSup_add_one f i

set_option linter.deprecated false in
@[deprecated "lsub is deprecated" (since := "2026-03-27")]
theorem lt_lsub_iff {ι} {f : ι → Ordinal} {a} : a < lsub f ↔ ∃ i, a ≤ f i := by
  simpa only [not_forall, not_lt, not_le] using not_congr lsub_le_iff

set_option linter.deprecated false in
@[deprecated "lsub is deprecated" (since := "2026-03-27")]
theorem iSup_le_lsub {ι} (f : ι → Ordinal) : iSup f ≤ lsub f :=
  Ordinal.iSup_le fun i => (lt_lsub f i).le

set_option linter.deprecated false in
@[deprecated "lsub is deprecated" (since := "2026-03-27")]
theorem lsub_le_succ_iSup {ι} (f : ι → Ordinal) : lsub f ≤ succ (iSup f) :=
  lsub_le fun i => lt_succ_iff.2 (Ordinal.le_iSup f i)

set_option linter.deprecated false in
@[deprecated "lsub is deprecated" (since := "2026-03-27")]
theorem iSup_eq_lsub_or_succ_iSup_eq_lsub {ι} (f : ι → Ordinal) :
    iSup f = lsub f ∨ succ (iSup f) = lsub f := by
  rcases eq_or_lt_of_le (iSup_le_lsub f) with h | h
  · exact Or.inl h
  · exact Or.inr ((succ_le_of_lt h).antisymm (lsub_le_succ_iSup f))

set_option linter.deprecated false in
@[deprecated "lsub is deprecated" (since := "2026-03-27")]
theorem succ_iSup_le_lsub_iff {ι} (f : ι → Ordinal) :
    succ (iSup f) ≤ lsub f ↔ ∃ i, f i = iSup f := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra! hf
    have := forall_congr' fun i ↦ (Ordinal.le_iSup f i).lt_iff_ne.symm
    exact (succ_le_iff.1 h).ne ((iSup_le_lsub f).antisymm (lsub_le (this.1 hf)))
  rintro ⟨_, hf⟩
  rw [succ_le_iff, ← hf]
  exact lt_lsub _ _

set_option linter.deprecated false in
@[deprecated "lsub is deprecated" (since := "2026-03-27")]
theorem succ_iSup_eq_lsub_iff {ι} (f : ι → Ordinal) :
    succ (iSup f) = lsub f ↔ ∃ i, f i = iSup f :=
  (lsub_le_succ_iSup f).ge_iff_eq'.symm.trans (succ_iSup_le_lsub_iff f)

set_option linter.deprecated false in
@[deprecated "lsub is deprecated" (since := "2026-03-27")]
theorem iSup_eq_lsub_iff {ι} (f : ι → Ordinal) :
    iSup f = lsub f ↔ ∀ a < lsub f, succ a < lsub f := by
  refine ⟨fun h => ?_, fun hf => le_antisymm (iSup_le_lsub f) (lsub_le fun i => ?_)⟩
  · rw [← h]
    exact fun a => succ_lt_iSup_of_ne_iSup fun i => (lsub_le_iff.1 (le_of_eq h.symm) i).ne
  by_contra! hle
  have heq := (succ_iSup_eq_lsub_iff f).2 ⟨i, le_antisymm (Ordinal.le_iSup _ _) hle⟩
  have :=
    hf _
      (by
        rw [← heq]
        exact lt_succ (iSup f))
  rw [heq] at this
  exact this.false

set_option linter.deprecated false in
@[deprecated "lsub is deprecated" (since := "2026-03-27")]
theorem iSup_eq_lsub_iff_lt_iSup {ι} (f : ι → Ordinal) :
    iSup f = lsub f ↔ ∀ i, f i < iSup f :=
  ⟨fun h i => by
    rw [h]
    apply lt_lsub, fun h => le_antisymm (iSup_le_lsub f) (lsub_le h)⟩

set_option linter.deprecated false in
@[deprecated "lsub is deprecated" (since := "2026-03-27")]
theorem lsub_empty {ι} [h : IsEmpty ι] (f : ι → Ordinal) : lsub f = 0 := by
  rw [← nonpos_iff_eq_zero, lsub_le_iff]
  exact h.elim

set_option linter.deprecated false in
@[deprecated "lsub is deprecated" (since := "2026-03-27")]
theorem lsub_pos {ι} [h : Nonempty ι] (f : ι → Ordinal) : 0 < lsub f :=
  h.elim fun i => (zero_le _).trans_lt (lt_lsub f i)

set_option linter.deprecated false in
@[deprecated "lsub is deprecated" (since := "2026-03-27")]
theorem lsub_eq_zero_iff {ι} (f : ι → Ordinal) :
    lsub.{_, v} f = 0 ↔ IsEmpty ι := by
  refine ⟨fun h => ⟨fun i => ?_⟩, fun h => @lsub_empty _ h _⟩
  have := @lsub_pos.{_, v} _ ⟨i⟩ f
  rw [h] at this
  exact this.false

set_option linter.deprecated false in
@[deprecated "lsub is deprecated" (since := "2026-03-27")]
theorem lsub_const {ι} [Nonempty ι] (o : Ordinal) : (lsub fun _ : ι => o) = succ o :=
  ciSup_const

set_option linter.deprecated false in
@[deprecated "lsub is deprecated" (since := "2026-03-27")]
theorem lsub_unique {ι} [Unique ι] (f : ι → Ordinal) : lsub f = succ (f default) :=
  ciSup_unique

set_option linter.deprecated false in
@[deprecated "lsub is deprecated" (since := "2026-03-27")]
theorem lsub_le_of_range_subset {ι ι'} {f : ι → Ordinal} {g : ι' → Ordinal}
    (h : Set.range f ⊆ Set.range g) : lsub.{u, max v w} f ≤ lsub.{v, max u w} g :=
  csSup_le_csSup' bddAbove_of_small (by convert Set.image_mono h <;> apply Set.range_comp)

set_option linter.deprecated false in
@[deprecated "lsub is deprecated" (since := "2026-03-27")]
theorem lsub_eq_of_range_eq {ι ι'} {f : ι → Ordinal} {g : ι' → Ordinal}
    (h : Set.range f = Set.range g) : lsub.{u, max v w} f = lsub.{v, max u w} g :=
  (lsub_le_of_range_subset.{u, v, w} h.le).antisymm (lsub_le_of_range_subset.{v, u, w} h.ge)

set_option linter.deprecated false in
@[deprecated "lsub is deprecated" (since := "2026-03-27")]
theorem lsub_sum {α : Type u} {β : Type v} (f : α ⊕ β → Ordinal) :
    lsub.{max u v, w} f =
      max (lsub.{u, max v w} fun a => f (Sum.inl a)) (lsub.{v, max u w} fun b => f (Sum.inr b)) :=
  iSup_sum _

set_option linter.deprecated false in
@[deprecated "lsub is deprecated" (since := "2026-03-27")]
theorem lsub_notMem_range {ι} (f : ι → Ordinal) :
    lsub f ∉ Set.range f := fun ⟨i, h⟩ =>
  h.not_lt (lt_lsub f i)

set_option linter.deprecated false in
@[deprecated "lsub is deprecated" (since := "2026-03-27")]
theorem nonempty_compl_range {ι : Type u} (f : ι → Ordinal.{max u v}) : (Set.range f)ᶜ.Nonempty :=
  ⟨_, lsub_notMem_range f⟩

set_option linter.deprecated false in
@[deprecated "lsub is deprecated" (since := "2026-03-27")]
theorem lsub_typein (o : Ordinal) : lsub.{u, u} (typein (α := o.ToType) (· < ·)) = o :=
  (lsub_le.{u, u} typein_lt_self).antisymm
    (by
      by_contra! h
      have h := h.trans_eq (type_toType o).symm
      simpa [typein_enum] using lt_lsub.{u, u} (typein (· < ·)) (enum (· < ·) ⟨_, h⟩))

set_option linter.deprecated false in
@[deprecated IsSuccPrelimit.sSup_Iio (since := "2026-03-27")]
theorem iSup_typein_limit {o : Ordinal.{u}} (ho : ∀ a, a < o → succ a < o) :
    iSup (typein ((· < ·) : o.ToType → o.ToType → Prop)) = o := by
  replace ho : IsSuccPrelimit o := by rwa [isSuccPrelimit_iff_succ_lt]
  rw [iSup, PrincipalSeg.range_eq]
  simpa [Iio_def] using ho.sSup_Iio

@[deprecated csSup_Iic (since := "2026-03-27")]
theorem iSup_typein_succ {o : Ordinal} :
    iSup (typein ((· < ·) : (succ o).ToType → (succ o).ToType → Prop)) = o := by
  rw [← csSup_Iic (a := o), iSup, PrincipalSeg.range_eq]
  congr
  simp

end lsub

section blsub

set_option linter.deprecated false in
/-- The least strict upper bound of a family of ordinals indexed by the set of ordinals less than
some `o : Ordinal.{u}`. -/
@[deprecated "write `⨆ i : Iio o, f i + 1` instead." (since := "2026-03-23")]
def blsub (o : Ordinal.{u}) (f : ∀ a < o, Ordinal.{max u v}) : Ordinal.{max u v} :=
  bsup.{_, v} o fun a ha => succ (f a ha)

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem bsup_eq_blsub (o : Ordinal.{u}) (f : ∀ a < o, Ordinal.{max u v}) :
    (bsup.{_, v} o fun a ha => succ (f a ha)) = blsub.{_, v} o f :=
  rfl

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem lsub_eq_blsub' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o} (ho : type r = o)
    (f : ∀ a < o, Ordinal) : lsub (familyOfBFamily' r ho f) = blsub o f :=
  iSup'_eq_bsup r ho fun a ha => succ (f a ha)

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem lsub_eq_lsub {ι ι' : Type u} (r : ι → ι → Prop) (r' : ι' → ι' → Prop) [IsWellOrder ι r]
    [IsWellOrder ι' r'] {o} (ho : type r = o) (ho' : type r' = o)
    (f : ∀ a < o, Ordinal.{max u v}) :
    lsub.{_, v} (familyOfBFamily' r ho f) = lsub.{_, v} (familyOfBFamily' r' ho' f) := by
  rw [lsub_eq_blsub', lsub_eq_blsub']

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem lsub_eq_blsub {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    lsub.{_, v} (familyOfBFamily o f) = blsub.{_, v} o f :=
  lsub_eq_blsub' _ _ _

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem blsub_eq_lsub' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r]
    (f : ι → Ordinal.{max u v}) : blsub.{_, v} _ (bfamilyOfFamily' r f) = lsub.{_, v} f :=
  bsup'_eq_iSup r (succ ∘ f)

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem blsub_eq_blsub {ι : Type u} (r r' : ι → ι → Prop) [IsWellOrder ι r] [IsWellOrder ι r']
    (f : ι → Ordinal.{max u v}) :
    blsub.{_, v} _ (bfamilyOfFamily' r f) = blsub.{_, v} _ (bfamilyOfFamily' r' f) := by
  rw [blsub_eq_lsub', blsub_eq_lsub']

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem blsub_eq_lsub {ι : Type u} (f : ι → Ordinal.{max u v}) :
    blsub.{_, v} _ (bfamilyOfFamily f) = lsub.{_, v} f :=
  blsub_eq_lsub' _ _

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem blsub_congr {o₁ o₂ : Ordinal.{u}} (f : ∀ a < o₁, Ordinal.{max u v}) (ho : o₁ = o₂) :
    blsub.{_, v} o₁ f = blsub.{_, v} o₂ fun a h => f a (h.trans_eq ho.symm) := by
  subst ho
  rfl

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem blsub_le_iff {o : Ordinal.{u}} {f : ∀ a < o, Ordinal.{max u v}} {a} :
    blsub.{_, v} o f ≤ a ↔ ∀ i h, f i h < a := by
  convert bsup_le_iff.{_, v} (f := fun a ha => succ (f a ha)) (a := a) using 2
  simp_rw [succ_le_iff]

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem blsub_le {o : Ordinal} {f : ∀ b < o, Ordinal} {a} : (∀ i h, f i h < a) → blsub o f ≤ a :=
  blsub_le_iff.2

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem lt_blsub {o} (f : ∀ a < o, Ordinal) (i h) : f i h < blsub o f :=
  blsub_le_iff.1 le_rfl _ _

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem lt_blsub_iff {o : Ordinal.{u}} {f : ∀ b < o, Ordinal.{max u v}} {a} :
    a < blsub.{_, v} o f ↔ ∃ i hi, a ≤ f i hi := by
  simpa only [not_forall, not_lt, not_le] using not_congr (@blsub_le_iff.{_, v} _ f a)

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem bsup_le_blsub {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    bsup.{_, v} o f ≤ blsub.{_, v} o f :=
  bsup_le fun i h => (lt_blsub f i h).le

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem blsub_le_bsup_succ {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    blsub.{_, v} o f ≤ succ (bsup.{_, v} o f) :=
  blsub_le fun i h => lt_succ_iff.2 (le_bsup f i h)

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem bsup_eq_blsub_or_succ_bsup_eq_blsub {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    bsup.{_, v} o f = blsub.{_, v} o f ∨ succ (bsup.{_, v} o f) = blsub.{_, v} o f := by
  rw [← iSup_eq_bsup, ← lsub_eq_blsub]
  exact iSup_eq_lsub_or_succ_iSup_eq_lsub _

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem bsup_succ_le_blsub {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    succ (bsup.{_, v} o f) ≤ blsub.{_, v} o f ↔ ∃ i hi, f i hi = bsup.{_, v} o f := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra! hf
    exact
      ne_of_lt (succ_le_iff.1 h)
        (le_antisymm (bsup_le_blsub f) (blsub_le (lt_bsup_of_ne_bsup.1 hf)))
  rintro ⟨_, _, hf⟩
  rw [succ_le_iff, ← hf]
  exact lt_blsub _ _ _

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem bsup_succ_eq_blsub {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    succ (bsup.{_, v} o f) = blsub.{_, v} o f ↔ ∃ i hi, f i hi = bsup.{_, v} o f :=
  (blsub_le_bsup_succ f).ge_iff_eq'.symm.trans (bsup_succ_le_blsub f)

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem bsup_eq_blsub_iff_succ {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    bsup.{_, v} o f = blsub.{_, v} o f ↔ ∀ a < blsub.{_, v} o f, succ a < blsub.{_, v} o f := by
  rw [← iSup_eq_bsup, ← lsub_eq_blsub]
  apply iSup_eq_lsub_iff

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem bsup_eq_blsub_iff_lt_bsup {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    bsup.{_, v} o f = blsub.{_, v} o f ↔ ∀ i hi, f i hi < bsup.{_, v} o f :=
  ⟨fun h i => by
    rw [h]
    apply lt_blsub, fun h => le_antisymm (bsup_le_blsub f) (blsub_le h)⟩

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem bsup_eq_blsub_of_lt_succ_limit {o : Ordinal.{u}} (ho : IsSuccLimit o)
    {f : ∀ a < o, Ordinal.{max u v}} (hf : ∀ a ha, f a ha < f (succ a) (ho.succ_lt ha)) :
    bsup.{_, v} o f = blsub.{_, v} o f := by
  rw [bsup_eq_blsub_iff_lt_bsup]
  exact fun i hi => (hf i hi).trans_le (le_bsup f _ _)

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem blsub_succ_of_mono {o : Ordinal.{u}} {f : ∀ a < succ o, Ordinal.{max u v}}
    (hf : ∀ {i j} (hi hj), i ≤ j → f i hi ≤ f j hj) : blsub.{_, v} _ f = succ (f o (lt_succ o)) :=
  bsup_succ_of_mono fun {_ _} hi hj h => succ_le_succ (hf hi hj h)

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem blsub_eq_zero_iff {o} {f : ∀ a < o, Ordinal} : blsub o f = 0 ↔ o = 0 := by
  rw [← lsub_eq_blsub, lsub_eq_zero_iff]
  exact isEmpty_toType_iff

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem blsub_zero (f : ∀ a < (0 : Ordinal), Ordinal) : blsub 0 f = 0 := by rw [blsub_eq_zero_iff]

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem blsub_pos {o : Ordinal} (ho : 0 < o) (f : ∀ a < o, Ordinal) : 0 < blsub o f :=
  (zero_le _).trans_lt (lt_blsub f 0 ho)

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem blsub_type {α : Type u} (r : α → α → Prop) [IsWellOrder α r]
    (f : ∀ a < type r, Ordinal.{max u v}) :
    blsub.{_, v} (type r) f = lsub.{_, v} fun a => f (typein r a) (typein_lt_type _ _) :=
  eq_of_forall_ge_iff fun o => by
    rw [blsub_le_iff, lsub_le_iff]
    exact ⟨fun H b => H _ _, fun H i h => by simpa only [typein_enum] using H (enum r ⟨i, h⟩)⟩

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem blsub_const {o : Ordinal} (ho : o ≠ 0) (a : Ordinal) :
    (blsub.{u, v} o fun _ _ => a) = succ a :=
  bsup_const.{u, v} ho (succ a)

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem blsub_one (f : ∀ a < (1 : Ordinal), Ordinal) : blsub 1 f = succ (f 0 zero_lt_one) :=
  bsup_one _

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem blsub_id : ∀ o, (blsub.{u, u} o fun x _ => x) = o :=
  lsub_typein

set_option linter.deprecated false in
@[deprecated IsSuccPrelimit.sSup_Iio (since := "2026-03-23")]
theorem bsup_id_limit {o : Ordinal} : (∀ a < o, succ a < o) → (bsup.{u, u} o fun x _ => x) = o :=
  iSup_typein_limit

set_option linter.deprecated false in
@[deprecated csSup_Iic (since := "2026-03-23")]
theorem bsup_id_add_one (o) : (bsup.{u, u} (o + 1) fun x _ => x) = o :=
  iSup_typein_succ

set_option linter.deprecated false in
@[deprecated csSup_Iic (since := "2026-03-23")]
theorem bsup_id_succ (o) : (bsup.{u, u} (succ o) fun x _ => x) = o :=
  iSup_typein_succ

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem blsub_le_of_brange_subset {o o'} {f : ∀ a < o, Ordinal} {g : ∀ a < o', Ordinal}
    (h : brange o f ⊆ brange o' g) : blsub.{u, max v w} o f ≤ blsub.{v, max u w} o' g :=
  bsup_le_of_brange_subset.{u, v, w} fun a ⟨b, hb, hb'⟩ => by
    obtain ⟨c, hc, hc'⟩ := h ⟨b, hb, rfl⟩
    simp_rw [← hc'] at hb'
    exact ⟨c, hc, hb'⟩

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem blsub_eq_of_brange_eq {o o'} {f : ∀ a < o, Ordinal} {g : ∀ a < o', Ordinal}
    (h : { o | ∃ i hi, f i hi = o } = { o | ∃ i hi, g i hi = o }) :
    blsub.{u, max v w} o f = blsub.{v, max u w} o' g :=
  (blsub_le_of_brange_subset.{u, v, w} h.le).antisymm (blsub_le_of_brange_subset.{v, u, w} h.ge)

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem bsup_comp {o o' : Ordinal.{max u v}} {f : ∀ a < o, Ordinal.{max u v w}}
    (hf : ∀ {i j} (hi) (hj), i ≤ j → f i hi ≤ f j hj) {g : ∀ a < o', Ordinal.{max u v}}
    (hg : blsub.{_, u} o' g = o) :
    (bsup.{_, w} o' fun a ha => f (g a ha) (by rw [← hg]; apply lt_blsub)) = bsup.{_, w} o f := by
  apply le_antisymm <;> refine bsup_le fun i hi => ?_
  · apply le_bsup
  · rw [← hg, lt_blsub_iff] at hi
    rcases hi with ⟨j, hj, hj'⟩
    exact (hf _ _ hj').trans (le_bsup _ _ _)

set_option linter.deprecated false in
@[deprecated "blsub is deprecated" (since := "2026-03-23")]
theorem blsub_comp {o o' : Ordinal.{max u v}} {f : ∀ a < o, Ordinal.{max u v w}}
    (hf : ∀ {i j} (hi) (hj), i ≤ j → f i hi ≤ f j hj) {g : ∀ a < o', Ordinal.{max u v}}
    (hg : blsub.{_, u} o' g = o) :
    (blsub.{_, w} o' fun a ha => f (g a ha) (by rw [← hg]; apply lt_blsub)) = blsub.{_, w} o f :=
  @bsup_comp.{u, v, w} o _ (fun a ha => succ (f a ha))
    (fun {_ _} _ _ h => succ_le_succ_iff.2 (hf _ _ h)) g hg

set_option linter.deprecated false in
@[deprecated IsNormal.apply_of_isSuccLimit (since := "2026-03-23")]
theorem IsNormal.bsup_eq {f : Ordinal.{u} → Ordinal.{max u v}} (H : IsNormal f) {o : Ordinal.{u}}
    (h : IsSuccLimit o) : (Ordinal.bsup.{_, v} o fun x _ => f x) = f o := by
  rw [← IsNormal.bsup.{u, u, v} H (fun x _ => x) h.ne_bot, bsup_id_limit fun _ ↦ h.succ_lt]

set_option linter.deprecated false in
@[deprecated IsNormal.apply_of_isSuccLimit (since := "2026-03-23")]
theorem IsNormal.blsub_eq {f : Ordinal.{u} → Ordinal.{max u v}} (H : IsNormal f) {o : Ordinal.{u}}
    (h : IsSuccLimit o) : (blsub.{_, v} o fun x _ => f x) = f o := by
  rw [← IsNormal.bsup_eq.{u, v} H h, bsup_eq_blsub_of_lt_succ_limit h]
  exact fun a _ => H.strictMono (lt_succ a)

set_option linter.deprecated false in
@[deprecated isNormal_iff (since := "2026-03-23")]
theorem isNormal_iff_lt_succ_and_bsup_eq {f : Ordinal.{u} → Ordinal.{max u v}} :
    IsNormal f ↔ (∀ a, f a < f (succ a)) ∧
      ∀ o, IsSuccLimit o → (bsup.{_, v} o fun x _ => f x) = f o :=
  ⟨fun h => ⟨fun a ↦ h.strictMono (lt_succ a), @IsNormal.bsup_eq f h⟩, fun ⟨h₁, h₂⟩ =>
    .of_succ_lt h₁ fun ho ↦ by
      rw [← h₂ _ ho]
      simpa [IsLUB, upperBounds, lowerBounds, IsLeast, bsup_le_iff] using le_bsup _⟩

set_option linter.deprecated false in
@[deprecated isNormal_iff (since := "2026-03-23")]
theorem isNormal_iff_lt_succ_and_blsub_eq {f : Ordinal.{u} → Ordinal.{max u v}} :
    IsNormal f ↔ (∀ a, f a < f (succ a)) ∧
      ∀ o, IsSuccLimit o → (blsub.{_, v} o fun x _ => f x) = f o := by
  rw [isNormal_iff_lt_succ_and_bsup_eq.{u, v}, and_congr_right_iff]
  intro h
  constructor <;> intro H o ho <;> have := H o ho <;>
    rwa [← bsup_eq_blsub_of_lt_succ_limit ho fun a _ => h a] at *

@[deprecated IsNormal.ext_iff (since := "2025-12-25")]
theorem IsNormal.eq_iff_zero_and_succ {f g : Ordinal.{u} → Ordinal.{u}} (hf : IsNormal f)
    (hg : IsNormal g) : f = g ↔ f 0 = g 0 ∧ ∀ a, f a = g a → f (succ a) = g (succ a) :=
  Order.IsNormal.ext_iff hf hg

end blsub

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

@[deprecated (since := "2025-12-25")]
alias IsNormal.apply_omega0 := apply_omega0_of_isNormal

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
  · rw [csSup_of_not_bddAbove bdd, sSup_empty, csSup_of_not_bddAbove]
    · simp
    exact fun ⟨u, hu⟩ ↦ bdd ⟨u, fun x hx ↦ (x.le_mul_right ho).trans (hu ⟨x, hx, rfl⟩)⟩

@[simp]
lemma mul_iSup (o : Ordinal) {ι} (f : ι → Ordinal) : o * ⨆ i, f i = ⨆ i, o * f i := by
  rw [← sSup_range, mul_sSup, ← Set.range_comp', sSup_range]

@[simp]
theorem iSup_add_natCast (o : Ordinal) : ⨆ n : ℕ, o + n = o + ω := by
  rw [← iSup_natCast, Ordinal.add_iSup]

@[deprecated (since := "2025-12-25")]
alias iSup_add_nat := iSup_add_natCast

@[simp]
theorem iSup_mul_natCast (o : Ordinal) : ⨆ n : ℕ, o * n = o * ω := by
  rw [← iSup_natCast, Ordinal.mul_iSup]

@[deprecated (since := "2025-12-25")]
alias iSup_mul_nat := iSup_mul_natCast

end Ordinal
