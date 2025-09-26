/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Data.Set.Function
import Mathlib.Logic.Pairwise
import Mathlib.Logic.Relation

/-!
# Relations holding pairwise

This file develops pairwise relations and defines pairwise disjoint indexed sets.

We also prove many basic facts about `Pairwise`. It is possible that an intermediate file,
with more imports than `Logic.Pairwise` but not importing `Data.Set.Function` would be appropriate
to hold many of these basic facts.

## Main declarations

* `Set.PairwiseDisjoint`: `s.PairwiseDisjoint f` states that images under `f` of distinct elements
  of `s` are either equal or `Disjoint`.

## Notes

The spelling `s.PairwiseDisjoint id` is preferred over `s.Pairwise Disjoint` to permit dot notation
on `Set.PairwiseDisjoint`, even though the latter unfolds to something nicer.
-/


open Function Order Set

variable {α β γ ι ι' : Type*} {r p : α → α → Prop}

section Pairwise

variable {f g : ι → α} {s t : Set α} {a b : α}

theorem pairwise_on_bool (hr : Symmetric r) {a b : α} :
    Pairwise (r on fun c => cond c a b) ↔ r a b := by simpa [Pairwise, Function.onFun] using @hr a b

theorem pairwise_disjoint_on_bool [PartialOrder α] [OrderBot α] {a b : α} :
    Pairwise (Disjoint on fun c => cond c a b) ↔ Disjoint a b :=
  pairwise_on_bool Disjoint.symm

theorem Symmetric.pairwise_on [LinearOrder ι] (hr : Symmetric r) (f : ι → α) :
    Pairwise (r on f) ↔ ∀ ⦃m n⦄, m < n → r (f m) (f n) :=
  ⟨fun h _m _n hmn => h hmn.ne, fun h _m _n hmn => hmn.lt_or_gt.elim (@h _ _) fun h' => hr (h h')⟩

theorem pairwise_disjoint_on [PartialOrder α] [OrderBot α] [LinearOrder ι] (f : ι → α) :
    Pairwise (Disjoint on f) ↔ ∀ ⦃m n⦄, m < n → Disjoint (f m) (f n) :=
  Symmetric.pairwise_on Disjoint.symm f

theorem pairwise_disjoint_mono [PartialOrder α] [OrderBot α] (hs : Pairwise (Disjoint on f))
    (h : g ≤ f) : Pairwise (Disjoint on g) :=
  hs.mono fun i j hij => Disjoint.mono (h i) (h j) hij

theorem Pairwise.disjoint_extend_bot [PartialOrder γ] [OrderBot γ]
    {e : α → β} {f : α → γ} (hf : Pairwise (Disjoint on f)) (he : FactorsThrough f e) :
    Pairwise (Disjoint on extend e f ⊥) := by
  intro b₁ b₂ hne
  rcases em (∃ a₁, e a₁ = b₁) with ⟨a₁, rfl⟩ | hb₁
  · rcases em (∃ a₂, e a₂ = b₂) with ⟨a₂, rfl⟩ | hb₂
    · simpa only [onFun, he.extend_apply] using hf (ne_of_apply_ne e hne)
    · simpa only [onFun, extend_apply' _ _ _ hb₂] using disjoint_bot_right
  · simpa only [onFun, extend_apply' _ _ _ hb₁] using disjoint_bot_left

namespace Set

theorem Pairwise.mono (h : t ⊆ s) (hs : s.Pairwise r) : t.Pairwise r :=
  fun _x xt _y yt => hs (h xt) (h yt)

theorem Pairwise.mono' (H : r ≤ p) (hr : s.Pairwise r) : s.Pairwise p :=
  hr.imp H

theorem pairwise_top (s : Set α) : s.Pairwise ⊤ :=
  pairwise_of_forall s _ fun _ _ => trivial

protected theorem Subsingleton.pairwise (h : s.Subsingleton) (r : α → α → Prop) : s.Pairwise r :=
  fun _x hx _y hy hne => (hne (h hx hy)).elim

@[simp]
theorem pairwise_empty (r : α → α → Prop) : (∅ : Set α).Pairwise r :=
  subsingleton_empty.pairwise r

@[simp]
theorem pairwise_singleton (a : α) (r : α → α → Prop) : Set.Pairwise {a} r :=
  subsingleton_singleton.pairwise r

theorem pairwise_iff_of_refl [IsRefl α r] : s.Pairwise r ↔ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → r a b :=
  forall₄_congr fun _ _ _ _ => or_iff_not_imp_left.symm.trans <| or_iff_right_of_imp of_eq

alias ⟨Pairwise.of_refl, _⟩ := pairwise_iff_of_refl

theorem Nonempty.pairwise_iff_exists_forall [IsEquiv α r] {s : Set ι} (hs : s.Nonempty) :
    s.Pairwise (r on f) ↔ ∃ z, ∀ x ∈ s, r (f x) z := by
  constructor
  · rcases hs with ⟨y, hy⟩
    refine fun H => ⟨f y, fun x hx => ?_⟩
    rcases eq_or_ne x y with (rfl | hne)
    · apply IsRefl.refl
    · exact H hx hy hne
  · rintro ⟨z, hz⟩ x hx y hy _
    exact @IsTrans.trans α r _ (f x) z (f y) (hz _ hx) (IsSymm.symm _ _ <| hz _ hy)

/-- For a nonempty set `s`, a function `f` takes pairwise equal values on `s` if and only if
for some `z` in the codomain, `f` takes value `z` on all `x ∈ s`. See also
`Set.pairwise_eq_iff_exists_eq` for a version that assumes `[Nonempty ι]` instead of
`Set.Nonempty s`. -/
theorem Nonempty.pairwise_eq_iff_exists_eq {s : Set α} (hs : s.Nonempty) {f : α → ι} :
    (s.Pairwise fun x y => f x = f y) ↔ ∃ z, ∀ x ∈ s, f x = z :=
  hs.pairwise_iff_exists_forall

theorem pairwise_iff_exists_forall [Nonempty ι] (s : Set α) (f : α → ι) {r : ι → ι → Prop}
    [IsEquiv ι r] : s.Pairwise (r on f) ↔ ∃ z, ∀ x ∈ s, r (f x) z := by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · simp
  · exact hne.pairwise_iff_exists_forall

/-- A function `f : α → ι` with nonempty codomain takes pairwise equal values on a set `s` if and
only if for some `z` in the codomain, `f` takes value `z` on all `x ∈ s`. See also
`Set.Nonempty.pairwise_eq_iff_exists_eq` for a version that assumes `Set.Nonempty s` instead of
`[Nonempty ι]`. -/
theorem pairwise_eq_iff_exists_eq [Nonempty ι] (s : Set α) (f : α → ι) :
    (s.Pairwise fun x y => f x = f y) ↔ ∃ z, ∀ x ∈ s, f x = z :=
  pairwise_iff_exists_forall s f

theorem pairwise_union :
    (s ∪ t).Pairwise r ↔
    s.Pairwise r ∧ t.Pairwise r ∧ ∀ a ∈ s, ∀ b ∈ t, a ≠ b → r a b ∧ r b a := by
  simp only [Set.Pairwise, mem_union, or_imp, forall_and]
  aesop

theorem pairwise_union_of_symmetric (hr : Symmetric r) :
    (s ∪ t).Pairwise r ↔ s.Pairwise r ∧ t.Pairwise r ∧ ∀ a ∈ s, ∀ b ∈ t, a ≠ b → r a b :=
  pairwise_union.trans <| by simp only [hr.iff, and_self_iff]

theorem pairwise_insert :
    (insert a s).Pairwise r ↔ s.Pairwise r ∧ ∀ b ∈ s, a ≠ b → r a b ∧ r b a := by
  simp only [insert_eq, pairwise_union, pairwise_singleton, true_and, mem_singleton_iff, forall_eq]

theorem pairwise_insert_of_notMem (ha : a ∉ s) :
    (insert a s).Pairwise r ↔ s.Pairwise r ∧ ∀ b ∈ s, r a b ∧ r b a :=
  pairwise_insert.trans <|
    and_congr_right' <| forall₂_congr fun b hb => by simp [(ne_of_mem_of_not_mem hb ha).symm]

@[deprecated (since := "2025-05-23")] alias pairwise_insert_of_not_mem := pairwise_insert_of_notMem

protected theorem Pairwise.insert (hs : s.Pairwise r) (h : ∀ b ∈ s, a ≠ b → r a b ∧ r b a) :
    (insert a s).Pairwise r :=
  pairwise_insert.2 ⟨hs, h⟩

theorem Pairwise.insert_of_notMem (ha : a ∉ s) (hs : s.Pairwise r) (h : ∀ b ∈ s, r a b ∧ r b a) :
    (insert a s).Pairwise r :=
  (pairwise_insert_of_notMem ha).2 ⟨hs, h⟩

@[deprecated (since := "2025-05-23")] alias Pairwise.insert_of_not_mem := Pairwise.insert_of_notMem

theorem pairwise_insert_of_symmetric (hr : Symmetric r) :
    (insert a s).Pairwise r ↔ s.Pairwise r ∧ ∀ b ∈ s, a ≠ b → r a b := by
  simp only [pairwise_insert, hr.iff a, and_self_iff]

theorem pairwise_insert_of_symmetric_of_notMem (hr : Symmetric r) (ha : a ∉ s) :
    (insert a s).Pairwise r ↔ s.Pairwise r ∧ ∀ b ∈ s, r a b := by
  simp only [pairwise_insert_of_notMem ha, hr.iff a, and_self_iff]

@[deprecated (since := "2025-05-23")]
alias pairwise_insert_of_symmetric_of_not_mem := pairwise_insert_of_symmetric_of_notMem

theorem Pairwise.insert_of_symmetric (hs : s.Pairwise r) (hr : Symmetric r)
    (h : ∀ b ∈ s, a ≠ b → r a b) : (insert a s).Pairwise r :=
  (pairwise_insert_of_symmetric hr).2 ⟨hs, h⟩

@[deprecated Pairwise.insert_of_symmetric (since := "2025-03-19")]
theorem Pairwise.insert_of_symmetric_of_notMem (hs : s.Pairwise r) (hr : Symmetric r) (ha : a ∉ s)
    (h : ∀ b ∈ s, r a b) : (insert a s).Pairwise r :=
  (pairwise_insert_of_symmetric_of_notMem hr ha).2 ⟨hs, h⟩

@[deprecated (since := "2025-05-23")]
alias Pairwise.insert_of_symmetric_of_not_mem := Pairwise.insert_of_symmetric_of_notMem

theorem pairwise_pair : Set.Pairwise {a, b} r ↔ a ≠ b → r a b ∧ r b a := by simp [pairwise_insert]

theorem pairwise_pair_of_symmetric (hr : Symmetric r) : Set.Pairwise {a, b} r ↔ a ≠ b → r a b := by
  simp [pairwise_insert_of_symmetric hr]

theorem pairwise_univ : (univ : Set α).Pairwise r ↔ Pairwise r := by
  simp only [Set.Pairwise, Pairwise, mem_univ, forall_const]

@[simp]
theorem pairwise_bot_iff : s.Pairwise (⊥ : α → α → Prop) ↔ (s : Set α).Subsingleton :=
  ⟨fun h _a ha _b hb => h.eq ha hb id, fun h => h.pairwise _⟩

alias ⟨Pairwise.subsingleton, _⟩ := pairwise_bot_iff

/-- See also `Function.injective_iff_pairwise_ne` -/
lemma injOn_iff_pairwise_ne {s : Set ι} : InjOn f s ↔ s.Pairwise (f · ≠ f ·) := by
  simp only [InjOn, Set.Pairwise, not_imp_not]

alias ⟨InjOn.pairwise_ne, _⟩ := injOn_iff_pairwise_ne

protected theorem Pairwise.image {s : Set ι} (h : s.Pairwise (r on f)) : (f '' s).Pairwise r :=
  forall_mem_image.2 fun _x hx ↦ forall_mem_image.2 fun _y hy hne ↦ h hx hy <| ne_of_apply_ne _ hne

/-- See also `Set.Pairwise.image`. -/
theorem InjOn.pairwise_image {s : Set ι} (h : s.InjOn f) :
    (f '' s).Pairwise r ↔ s.Pairwise (r on f) := by
  simp +contextual [h.eq_iff, Set.Pairwise]

lemma _root_.Pairwise.range_pairwise (hr : Pairwise (r on f)) : (Set.range f).Pairwise r :=
  image_univ ▸ (pairwise_univ.mpr hr).image

end Set

end Pairwise

theorem pairwise_subtype_iff_pairwise_set (s : Set α) (r : α → α → Prop) :
    (Pairwise fun (x : s) (y : s) => r x y) ↔ s.Pairwise r := by
  simp only [Pairwise, Set.Pairwise, SetCoe.forall, Ne, Subtype.ext_iff]

alias ⟨Pairwise.set_of_subtype, Set.Pairwise.subtype⟩ := pairwise_subtype_iff_pairwise_set

namespace Set

section PartialOrderBot

variable [PartialOrder α] [OrderBot α] {s t : Set ι} {f g : ι → α}

/-- A set is `PairwiseDisjoint` under `f`, if the images of any distinct two elements under `f`
are disjoint.

`s.Pairwise Disjoint` is (definitionally) the same as `s.PairwiseDisjoint id`. We prefer the latter
in order to allow dot notation on `Set.PairwiseDisjoint`, even though the former unfolds more
nicely. -/
def PairwiseDisjoint (s : Set ι) (f : ι → α) : Prop :=
  s.Pairwise (Disjoint on f)

theorem PairwiseDisjoint.subset (ht : t.PairwiseDisjoint f) (h : s ⊆ t) : s.PairwiseDisjoint f :=
  Pairwise.mono h ht

theorem PairwiseDisjoint.mono_on (hs : s.PairwiseDisjoint f) (h : ∀ ⦃i⦄, i ∈ s → g i ≤ f i) :
    s.PairwiseDisjoint g := fun _a ha _b hb hab => (hs ha hb hab).mono (h ha) (h hb)

theorem PairwiseDisjoint.mono (hs : s.PairwiseDisjoint f) (h : g ≤ f) : s.PairwiseDisjoint g :=
  hs.mono_on fun i _ => h i

@[simp]
theorem pairwiseDisjoint_empty : (∅ : Set ι).PairwiseDisjoint f :=
  pairwise_empty _

@[simp]
theorem pairwiseDisjoint_singleton (i : ι) (f : ι → α) : PairwiseDisjoint {i} f :=
  pairwise_singleton i _

theorem pairwiseDisjoint_insert {i : ι} :
    (insert i s).PairwiseDisjoint f ↔
      s.PairwiseDisjoint f ∧ ∀ j ∈ s, i ≠ j → Disjoint (f i) (f j) :=
  pairwise_insert_of_symmetric <| symmetric_disjoint.comap f

theorem pairwiseDisjoint_insert_of_notMem {i : ι} (hi : i ∉ s) :
    (insert i s).PairwiseDisjoint f ↔ s.PairwiseDisjoint f ∧ ∀ j ∈ s, Disjoint (f i) (f j) :=
  pairwise_insert_of_symmetric_of_notMem (symmetric_disjoint.comap f) hi

@[deprecated (since := "2025-05-23")]
alias pairwiseDisjoint_insert_of_not_mem := pairwiseDisjoint_insert_of_notMem

protected theorem PairwiseDisjoint.insert (hs : s.PairwiseDisjoint f) {i : ι}
    (h : ∀ j ∈ s, i ≠ j → Disjoint (f i) (f j)) : (insert i s).PairwiseDisjoint f :=
  pairwiseDisjoint_insert.2 ⟨hs, h⟩

theorem PairwiseDisjoint.insert_of_notMem (hs : s.PairwiseDisjoint f) {i : ι} (hi : i ∉ s)
    (h : ∀ j ∈ s, Disjoint (f i) (f j)) : (insert i s).PairwiseDisjoint f :=
  (pairwiseDisjoint_insert_of_notMem hi).2 ⟨hs, h⟩

@[deprecated (since := "2025-05-23")]
alias PairwiseDisjoint.insert_of_not_mem := PairwiseDisjoint.insert_of_notMem

theorem PairwiseDisjoint.image_of_le (hs : s.PairwiseDisjoint f) {g : ι → ι} (hg : f ∘ g ≤ f) :
    (g '' s).PairwiseDisjoint f := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h
  exact (hs ha hb <| ne_of_apply_ne _ h).mono (hg a) (hg b)

theorem InjOn.pairwiseDisjoint_image {g : ι' → ι} {s : Set ι'} (h : s.InjOn g) :
    (g '' s).PairwiseDisjoint f ↔ s.PairwiseDisjoint (f ∘ g) :=
  h.pairwise_image

theorem PairwiseDisjoint.range (g : s → ι) (hg : ∀ i : s, f (g i) ≤ f i)
    (ht : s.PairwiseDisjoint f) : (range g).PairwiseDisjoint f := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
  exact ((ht x.2 y.2) fun h => hxy <| congr_arg g <| Subtype.ext h).mono (hg x) (hg y)

theorem pairwiseDisjoint_union :
    (s ∪ t).PairwiseDisjoint f ↔
      s.PairwiseDisjoint f ∧
        t.PairwiseDisjoint f ∧ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ t → i ≠ j → Disjoint (f i) (f j) :=
  pairwise_union_of_symmetric <| symmetric_disjoint.comap f

theorem PairwiseDisjoint.union (hs : s.PairwiseDisjoint f) (ht : t.PairwiseDisjoint f)
    (h : ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ t → i ≠ j → Disjoint (f i) (f j)) : (s ∪ t).PairwiseDisjoint f :=
  pairwiseDisjoint_union.2 ⟨hs, ht, h⟩

-- classical
theorem PairwiseDisjoint.elim (hs : s.PairwiseDisjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (h : ¬Disjoint (f i) (f j)) : i = j :=
  hs.eq hi hj h

lemma PairwiseDisjoint.eq_or_disjoint
    (h : s.PairwiseDisjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    i = j ∨ Disjoint (f i) (f j) := by
  rw [or_iff_not_imp_right]
  exact h.elim hi hj

lemma pairwiseDisjoint_range_iff {α β : Type*} {f : α → (Set β)} :
    (range f).PairwiseDisjoint id ↔ ∀ x y, f x ≠ f y → Disjoint (f x) (f y) := by
  aesop (add simp [PairwiseDisjoint, Set.Pairwise])

/-- If the range of `f` is pairwise disjoint, then the image of any set `s` under `f` is as well. -/
lemma _root_.Pairwise.pairwiseDisjoint (h : Pairwise (Disjoint on f)) (s : Set ι) :
    s.PairwiseDisjoint f := h.set_pairwise s

end PartialOrderBot

section SemilatticeInfBot

variable [SemilatticeInf α] [OrderBot α] {s : Set ι} {f : ι → α}

-- classical
theorem PairwiseDisjoint.elim' (hs : s.PairwiseDisjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (h : f i ⊓ f j ≠ ⊥) : i = j :=
  (hs.elim hi hj) fun hij => h hij.eq_bot

theorem PairwiseDisjoint.eq_of_le (hs : s.PairwiseDisjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (hf : f i ≠ ⊥) (hij : f i ≤ f j) : i = j :=
  (hs.elim' hi hj) fun h => hf <| (inf_of_le_left hij).symm.trans h

end SemilatticeInfBot

/-! ### Pairwise disjoint set of sets -/

variable {s : Set ι} {t : Set ι'}

theorem pairwiseDisjoint_range_singleton :
    (range (singleton : ι → Set ι)).PairwiseDisjoint id :=
  Pairwise.range_pairwise fun _ _ => disjoint_singleton.2

theorem pairwiseDisjoint_fiber (f : ι → α) (s : Set α) : s.PairwiseDisjoint fun a => f ⁻¹' {a} :=
  fun _a _ _b _ h => disjoint_iff_inf_le.mpr fun _i ⟨hia, hib⟩ => h <| (Eq.symm hia).trans hib

-- classical
theorem PairwiseDisjoint.elim_set {s : Set ι} {f : ι → Set α} (hs : s.PairwiseDisjoint f) {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) (a : α) (hai : a ∈ f i) (haj : a ∈ f j) : i = j :=
  hs.elim hi hj <| not_disjoint_iff.2 ⟨a, hai, haj⟩

theorem PairwiseDisjoint.prod {f : ι → Set α} {g : ι' → Set β} (hs : s.PairwiseDisjoint f)
    (ht : t.PairwiseDisjoint g) :
    (s ×ˢ t : Set (ι × ι')).PairwiseDisjoint fun i => f i.1 ×ˢ g i.2 :=
  fun ⟨_, _⟩ ⟨hi, hi'⟩ ⟨_, _⟩ ⟨hj, hj'⟩ hij =>
  disjoint_left.2 fun ⟨_, _⟩ ⟨hai, hbi⟩ ⟨haj, hbj⟩ =>
    hij <| Prod.ext (hs.elim_set hi hj _ hai haj) <| ht.elim_set hi' hj' _ hbi hbj

theorem pairwiseDisjoint_pi {ι' α : ι → Type*} {s : ∀ i, Set (ι' i)} {f : ∀ i, ι' i → Set (α i)}
    (hs : ∀ i, (s i).PairwiseDisjoint (f i)) :
    ((univ : Set ι).pi s).PairwiseDisjoint fun I => (univ : Set ι).pi fun i => f _ (I i) :=
  fun _ hI _ hJ hIJ =>
  disjoint_left.2 fun a haI haJ =>
    hIJ <|
      funext fun i =>
        (hs i).elim_set (hI i trivial) (hJ i trivial) (a i) (haI i trivial) (haJ i trivial)

/-- The partial images of a binary function `f` whose partial evaluations are injective are pairwise
disjoint iff `f` is injective . -/
theorem pairwiseDisjoint_image_right_iff {f : α → β → γ} {s : Set α} {t : Set β}
    (hf : ∀ a ∈ s, Injective (f a)) :
    (s.PairwiseDisjoint fun a => f a '' t) ↔ (s ×ˢ t).InjOn fun p => f p.1 p.2 := by
  refine ⟨fun hs x hx y hy (h : f _ _ = _) => ?_, fun hs x hx y hy h => ?_⟩
  · suffices x.1 = y.1 by exact Prod.ext this (hf _ hx.1 <| h.trans <| by rw [this])
    refine hs.elim hx.1 hy.1 (not_disjoint_iff.2 ⟨_, mem_image_of_mem _ hx.2, ?_⟩)
    rw [h]
    exact mem_image_of_mem _ hy.2
  · refine disjoint_iff_inf_le.mpr ?_
    rintro _ ⟨⟨a, ha, hab⟩, b, hb, rfl⟩
    exact h (congr_arg Prod.fst <| hs (mk_mem_prod hx ha) (mk_mem_prod hy hb) hab)

/-- The partial images of a binary function `f` whose partial evaluations are injective are pairwise
disjoint iff `f` is injective . -/
theorem pairwiseDisjoint_image_left_iff {f : α → β → γ} {s : Set α} {t : Set β}
    (hf : ∀ b ∈ t, Injective fun a => f a b) :
    (t.PairwiseDisjoint fun b => (fun a => f a b) '' s) ↔ (s ×ˢ t).InjOn fun p => f p.1 p.2 := by
  refine ⟨fun ht x hx y hy (h : f _ _ = _) => ?_, fun ht x hx y hy h => ?_⟩
  · suffices x.2 = y.2 by exact Prod.ext (hf _ hx.2 <| h.trans <| by rw [this]) this
    refine ht.elim hx.2 hy.2 (not_disjoint_iff.2 ⟨_, mem_image_of_mem _ hx.1, ?_⟩)
    rw [h]
    exact mem_image_of_mem _ hy.1
  · refine disjoint_iff_inf_le.mpr ?_
    rintro _ ⟨⟨a, ha, hab⟩, b, hb, rfl⟩
    exact h (congr_arg Prod.snd <| ht (mk_mem_prod ha hx) (mk_mem_prod hb hy) hab)

lemma exists_ne_mem_inter_of_not_pairwiseDisjoint
    {f : ι → Set α} (h : ¬ s.PairwiseDisjoint f) :
    ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ ∃ x : α, x ∈ f i ∩ f j := by
  change ¬ ∀ i, i ∈ s → ∀ j, j ∈ s → i ≠ j → ∀ t, t ≤ f i → t ≤ f j → t ≤ ⊥ at h
  simp only [not_forall] at h
  obtain ⟨i, hi, j, hj, h_ne, t, hfi, hfj, ht⟩ := h
  replace ht : t.Nonempty := by
    rwa [le_bot_iff, bot_eq_empty, ← Ne, ← nonempty_iff_ne_empty] at ht
  obtain ⟨x, hx⟩ := ht
  exact ⟨i, hi, j, hj, h_ne, x, hfi hx, hfj hx⟩

lemma exists_lt_mem_inter_of_not_pairwiseDisjoint [LinearOrder ι]
    {f : ι → Set α} (h : ¬ s.PairwiseDisjoint f) :
    ∃ i ∈ s, ∃ j ∈ s, i < j ∧ ∃ x, x ∈ f i ∩ f j := by
  obtain ⟨i, hi, j, hj, hne, x, hx₁, hx₂⟩ := exists_ne_mem_inter_of_not_pairwiseDisjoint h
  rcases lt_or_lt_iff_ne.mpr hne with h_lt | h_lt
  · exact ⟨i, hi, j, hj, h_lt, x, hx₁, hx₂⟩
  · exact ⟨j, hj, i, hi, h_lt, x, hx₂, hx₁⟩

end Set

lemma exists_ne_mem_inter_of_not_pairwise_disjoint
    {f : ι → Set α} (h : ¬ Pairwise (Disjoint on f)) :
    ∃ i j : ι, i ≠ j ∧ ∃ x, x ∈ f i ∩ f j := by
  rw [← pairwise_univ] at h
  obtain ⟨i, _hi, j, _hj, h⟩ := exists_ne_mem_inter_of_not_pairwiseDisjoint h
  exact ⟨i, j, h⟩

lemma exists_lt_mem_inter_of_not_pairwise_disjoint [LinearOrder ι]
    {f : ι → Set α} (h : ¬ Pairwise (Disjoint on f)) :
    ∃ i j : ι, i < j ∧ ∃ x, x ∈ f i ∩ f j := by
  rw [← pairwise_univ] at h
  obtain ⟨i, _hi, j, _hj, h⟩ := exists_lt_mem_inter_of_not_pairwiseDisjoint h
  exact ⟨i, j, h⟩

theorem pairwise_disjoint_fiber (f : ι → α) : Pairwise (Disjoint on fun a : α => f ⁻¹' {a}) :=
  pairwise_univ.1 <| Set.pairwiseDisjoint_fiber f univ

lemma subsingleton_setOf_mem_iff_pairwise_disjoint {f : ι → Set α} :
    (∀ a, {i | a ∈ f i}.Subsingleton) ↔ Pairwise (Disjoint on f) :=
  ⟨fun h _ _ hij ↦ disjoint_left.2 fun a hi hj ↦ hij (h a hi hj),
   fun h _ _ hx _ hy ↦ by_contra fun hne ↦ disjoint_left.1 (h hne) hx hy⟩
