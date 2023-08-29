/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Data.Set.Function
import Mathlib.Logic.Relation
import Mathlib.Logic.Pairwise

#align_import data.set.pairwise.basic from "leanprover-community/mathlib"@"c4c2ed622f43768eff32608d4a0f8a6cec1c047d"

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

variable {α β γ ι ι' : Type*} {r p q : α → α → Prop}

section Pairwise

variable {f g : ι → α} {s t u : Set α} {a b : α}

theorem pairwise_on_bool (hr : Symmetric r) {a b : α} :
    Pairwise (r on fun c => cond c a b) ↔ r a b := by simpa [Pairwise, Function.onFun] using @hr a b
                                                      -- 🎉 no goals
#align pairwise_on_bool pairwise_on_bool

theorem pairwise_disjoint_on_bool [SemilatticeInf α] [OrderBot α] {a b : α} :
    Pairwise (Disjoint on fun c => cond c a b) ↔ Disjoint a b :=
  pairwise_on_bool Disjoint.symm
#align pairwise_disjoint_on_bool pairwise_disjoint_on_bool

theorem Symmetric.pairwise_on [LinearOrder ι] (hr : Symmetric r) (f : ι → α) :
    Pairwise (r on f) ↔ ∀ ⦃m n⦄, m < n → r (f m) (f n) :=
  ⟨fun h _m _n hmn => h hmn.ne, fun h _m _n hmn => hmn.lt_or_lt.elim (@h _ _) fun h' => hr (h h')⟩
#align symmetric.pairwise_on Symmetric.pairwise_on

theorem pairwise_disjoint_on [SemilatticeInf α] [OrderBot α] [LinearOrder ι] (f : ι → α) :
    Pairwise (Disjoint on f) ↔ ∀ ⦃m n⦄, m < n → Disjoint (f m) (f n) :=
  Symmetric.pairwise_on Disjoint.symm f
#align pairwise_disjoint_on pairwise_disjoint_on

theorem pairwise_disjoint_mono [SemilatticeInf α] [OrderBot α] (hs : Pairwise (Disjoint on f))
    (h : g ≤ f) : Pairwise (Disjoint on g) :=
  hs.mono fun i j hij => Disjoint.mono (h i) (h j) hij
#align pairwise_disjoint.mono pairwise_disjoint_mono

namespace Set

theorem Pairwise.mono (h : t ⊆ s) (hs : s.Pairwise r) : t.Pairwise r :=
  fun _x xt _y yt => hs (h xt) (h yt)
#align set.pairwise.mono Set.Pairwise.mono

theorem Pairwise.mono' (H : r ≤ p) (hr : s.Pairwise r) : s.Pairwise p :=
  hr.imp H
#align set.pairwise.mono' Set.Pairwise.mono'

theorem pairwise_top (s : Set α) : s.Pairwise ⊤ :=
  pairwise_of_forall s _ fun _ _ => trivial
#align set.pairwise_top Set.pairwise_top

protected theorem Subsingleton.pairwise (h : s.Subsingleton) (r : α → α → Prop) : s.Pairwise r :=
  fun _x hx _y hy hne => (hne (h hx hy)).elim
#align set.subsingleton.pairwise Set.Subsingleton.pairwise

@[simp]
theorem pairwise_empty (r : α → α → Prop) : (∅ : Set α).Pairwise r :=
  subsingleton_empty.pairwise r
#align set.pairwise_empty Set.pairwise_empty

@[simp]
theorem pairwise_singleton (a : α) (r : α → α → Prop) : Set.Pairwise {a} r :=
  subsingleton_singleton.pairwise r
#align set.pairwise_singleton Set.pairwise_singleton

theorem pairwise_iff_of_refl [IsRefl α r] : s.Pairwise r ↔ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → r a b :=
  forall₄_congr fun _ _ _ _ => or_iff_not_imp_left.symm.trans <| or_iff_right_of_imp of_eq
#align set.pairwise_iff_of_refl Set.pairwise_iff_of_refl

alias ⟨Pairwise.of_refl, _⟩ := pairwise_iff_of_refl
#align set.pairwise.of_refl Set.Pairwise.of_refl

theorem Nonempty.pairwise_iff_exists_forall [IsEquiv α r] {s : Set ι} (hs : s.Nonempty) :
    s.Pairwise (r on f) ↔ ∃ z, ∀ x ∈ s, r (f x) z := by
  constructor
  -- ⊢ Set.Pairwise s (r on f) → ∃ z, ∀ (x : ι), x ∈ s → r (f x) z
  · rcases hs with ⟨y, hy⟩
    -- ⊢ Set.Pairwise s (r on f) → ∃ z, ∀ (x : ι), x ∈ s → r (f x) z
    refine' fun H => ⟨f y, fun x hx => _⟩
    -- ⊢ r (f x) (f y)
    rcases eq_or_ne x y with (rfl | hne)
    -- ⊢ r (f x) (f x)
    · apply IsRefl.refl
      -- 🎉 no goals
    · exact H hx hy hne
      -- 🎉 no goals
  · rintro ⟨z, hz⟩ x hx y hy _
    -- ⊢ (r on f) x y
    exact @IsTrans.trans α r _ (f x) z (f y) (hz _ hx) (IsSymm.symm _ _ <| hz _ hy)
    -- 🎉 no goals
#align set.nonempty.pairwise_iff_exists_forall Set.Nonempty.pairwise_iff_exists_forall

/-- For a nonempty set `s`, a function `f` takes pairwise equal values on `s` if and only if
for some `z` in the codomain, `f` takes value `z` on all `x ∈ s`. See also
`Set.pairwise_eq_iff_exists_eq` for a version that assumes `[Nonempty ι]` instead of
`Set.Nonempty s`. -/
theorem Nonempty.pairwise_eq_iff_exists_eq {s : Set α} (hs : s.Nonempty) {f : α → ι} :
    (s.Pairwise fun x y => f x = f y) ↔ ∃ z, ∀ x ∈ s, f x = z :=
  hs.pairwise_iff_exists_forall
#align set.nonempty.pairwise_eq_iff_exists_eq Set.Nonempty.pairwise_eq_iff_exists_eq

theorem pairwise_iff_exists_forall [Nonempty ι] (s : Set α) (f : α → ι) {r : ι → ι → Prop}
    [IsEquiv ι r] : s.Pairwise (r on f) ↔ ∃ z, ∀ x ∈ s, r (f x) z := by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  -- ⊢ Set.Pairwise ∅ (r on f) ↔ ∃ z, ∀ (x : α), x ∈ ∅ → r (f x) z
  · simp
    -- 🎉 no goals
  · exact hne.pairwise_iff_exists_forall
    -- 🎉 no goals
#align set.pairwise_iff_exists_forall Set.pairwise_iff_exists_forall

/-- A function `f : α → ι` with nonempty codomain takes pairwise equal values on a set `s` if and
only if for some `z` in the codomain, `f` takes value `z` on all `x ∈ s`. See also
`Set.Nonempty.pairwise_eq_iff_exists_eq` for a version that assumes `Set.Nonempty s` instead of
`[Nonempty ι]`. -/
theorem pairwise_eq_iff_exists_eq [Nonempty ι] (s : Set α) (f : α → ι) :
    (s.Pairwise fun x y => f x = f y) ↔ ∃ z, ∀ x ∈ s, f x = z :=
  pairwise_iff_exists_forall s f
#align set.pairwise_eq_iff_exists_eq Set.pairwise_eq_iff_exists_eq

theorem pairwise_union :
  (s ∪ t).Pairwise r ↔
    s.Pairwise r ∧ t.Pairwise r ∧ ∀ a ∈ s, ∀ b ∈ t, a ≠ b → r a b ∧ r b a := by
  simp only [Set.Pairwise, mem_union, or_imp, forall_and]
  -- ⊢ (((∀ (x : α), x ∈ s → ∀ (x_1 : α), x_1 ∈ s → x ≠ x_1 → r x x_1) ∧ ∀ (x : α), …
  exact
    ⟨fun H => ⟨H.1.1, H.2.2, H.2.1, fun x hx y hy hne => H.1.2 y hy x hx hne.symm⟩, fun H =>
      ⟨⟨H.1, fun x hx y hy hne => H.2.2.2 y hy x hx hne.symm⟩, H.2.2.1, H.2.1⟩⟩
#align set.pairwise_union Set.pairwise_union

theorem pairwise_union_of_symmetric (hr : Symmetric r) :
    (s ∪ t).Pairwise r ↔ s.Pairwise r ∧ t.Pairwise r ∧ ∀ a ∈ s, ∀ b ∈ t, a ≠ b → r a b :=
  pairwise_union.trans <| by simp only [hr.iff, and_self_iff]
                             -- 🎉 no goals
#align set.pairwise_union_of_symmetric Set.pairwise_union_of_symmetric

theorem pairwise_insert :
    (insert a s).Pairwise r ↔ s.Pairwise r ∧ ∀ b ∈ s, a ≠ b → r a b ∧ r b a := by
  simp only [insert_eq, pairwise_union, pairwise_singleton, true_and_iff, mem_singleton_iff,
    forall_eq]
#align set.pairwise_insert Set.pairwise_insert

theorem pairwise_insert_of_not_mem (ha : a ∉ s) :
    (insert a s).Pairwise r ↔ s.Pairwise r ∧ ∀ b ∈ s, r a b ∧ r b a :=
  pairwise_insert.trans <|
    and_congr_right' <| forall₂_congr fun b hb => by simp [(ne_of_mem_of_not_mem hb ha).symm]
                                                     -- 🎉 no goals
#align set.pairwise_insert_of_not_mem Set.pairwise_insert_of_not_mem

protected theorem Pairwise.insert (hs : s.Pairwise r) (h : ∀ b ∈ s, a ≠ b → r a b ∧ r b a) :
    (insert a s).Pairwise r :=
  pairwise_insert.2 ⟨hs, h⟩
#align set.pairwise.insert Set.Pairwise.insert

theorem Pairwise.insert_of_not_mem (ha : a ∉ s) (hs : s.Pairwise r) (h : ∀ b ∈ s, r a b ∧ r b a) :
    (insert a s).Pairwise r :=
  (pairwise_insert_of_not_mem ha).2 ⟨hs, h⟩
#align set.pairwise.insert_of_not_mem Set.Pairwise.insert_of_not_mem

theorem pairwise_insert_of_symmetric (hr : Symmetric r) :
    (insert a s).Pairwise r ↔ s.Pairwise r ∧ ∀ b ∈ s, a ≠ b → r a b := by
  simp only [pairwise_insert, hr.iff a, and_self_iff]
  -- 🎉 no goals
#align set.pairwise_insert_of_symmetric Set.pairwise_insert_of_symmetric

theorem pairwise_insert_of_symmetric_of_not_mem (hr : Symmetric r) (ha : a ∉ s) :
    (insert a s).Pairwise r ↔ s.Pairwise r ∧ ∀ b ∈ s, r a b := by
  simp only [pairwise_insert_of_not_mem ha, hr.iff a, and_self_iff]
  -- 🎉 no goals
#align set.pairwise_insert_of_symmetric_of_not_mem Set.pairwise_insert_of_symmetric_of_not_mem

theorem Pairwise.insert_of_symmetric (hs : s.Pairwise r) (hr : Symmetric r)
    (h : ∀ b ∈ s, a ≠ b → r a b) : (insert a s).Pairwise r :=
  (pairwise_insert_of_symmetric hr).2 ⟨hs, h⟩
#align set.pairwise.insert_of_symmetric Set.Pairwise.insert_of_symmetric

theorem Pairwise.insert_of_symmetric_of_not_mem (hs : s.Pairwise r) (hr : Symmetric r) (ha : a ∉ s)
    (h : ∀ b ∈ s, r a b) : (insert a s).Pairwise r :=
  (pairwise_insert_of_symmetric_of_not_mem hr ha).2 ⟨hs, h⟩
#align set.pairwise.insert_of_symmetric_of_not_mem Set.Pairwise.insert_of_symmetric_of_not_mem

theorem pairwise_pair : Set.Pairwise {a, b} r ↔ a ≠ b → r a b ∧ r b a := by simp [pairwise_insert]
                                                                            -- 🎉 no goals
#align set.pairwise_pair Set.pairwise_pair

theorem pairwise_pair_of_symmetric (hr : Symmetric r) : Set.Pairwise {a, b} r ↔ a ≠ b → r a b := by
  simp [pairwise_insert_of_symmetric hr]
  -- 🎉 no goals
#align set.pairwise_pair_of_symmetric Set.pairwise_pair_of_symmetric

theorem pairwise_univ : (univ : Set α).Pairwise r ↔ Pairwise r := by
  simp only [Set.Pairwise, Pairwise, mem_univ, forall_const]
  -- 🎉 no goals
#align set.pairwise_univ Set.pairwise_univ

@[simp]
theorem pairwise_bot_iff : s.Pairwise (⊥ : α → α → Prop) ↔ (s : Set α).Subsingleton :=
  ⟨fun h _a ha _b hb => h.eq ha hb id, fun h => h.pairwise _⟩
#align set.pairwise_bot_iff Set.pairwise_bot_iff

alias ⟨Pairwise.subsingleton, _⟩ := pairwise_bot_iff
#align set.pairwise.subsingleton Set.Pairwise.subsingleton

theorem InjOn.pairwise_image {s : Set ι} (h : s.InjOn f) :
    (f '' s).Pairwise r ↔ s.Pairwise (r on f) := by
  simp (config := { contextual := true }) [h.eq_iff, Set.Pairwise]
  -- 🎉 no goals
#align set.inj_on.pairwise_image Set.InjOn.pairwise_image

end Set

end Pairwise

theorem pairwise_subtype_iff_pairwise_set (s : Set α) (r : α → α → Prop) :
    (Pairwise fun (x : s) (y : s) => r x y) ↔ s.Pairwise r := by
  simp only [Pairwise, Set.Pairwise, SetCoe.forall, Ne.def, Subtype.ext_iff, Subtype.coe_mk]
  -- 🎉 no goals
#align pairwise_subtype_iff_pairwise_set pairwise_subtype_iff_pairwise_set

alias ⟨Pairwise.set_of_subtype, Set.Pairwise.subtype⟩ := pairwise_subtype_iff_pairwise_set
#align pairwise.set_of_subtype Pairwise.set_of_subtype
#align set.pairwise.subtype Set.Pairwise.subtype

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
#align set.pairwise_disjoint Set.PairwiseDisjoint

theorem PairwiseDisjoint.subset (ht : t.PairwiseDisjoint f) (h : s ⊆ t) : s.PairwiseDisjoint f :=
  Pairwise.mono h ht
#align set.pairwise_disjoint.subset Set.PairwiseDisjoint.subset

theorem PairwiseDisjoint.mono_on (hs : s.PairwiseDisjoint f) (h : ∀ ⦃i⦄, i ∈ s → g i ≤ f i) :
    s.PairwiseDisjoint g := fun _a ha _b hb hab => (hs ha hb hab).mono (h ha) (h hb)
#align set.pairwise_disjoint.mono_on Set.PairwiseDisjoint.mono_on

theorem PairwiseDisjoint.mono (hs : s.PairwiseDisjoint f) (h : g ≤ f) : s.PairwiseDisjoint g :=
  hs.mono_on fun i _ => h i
#align set.pairwise_disjoint.mono Set.PairwiseDisjoint.mono

@[simp]
theorem pairwiseDisjoint_empty : (∅ : Set ι).PairwiseDisjoint f :=
  pairwise_empty _
#align set.pairwise_disjoint_empty Set.pairwiseDisjoint_empty

@[simp]
theorem pairwiseDisjoint_singleton (i : ι) (f : ι → α) : PairwiseDisjoint {i} f :=
  pairwise_singleton i _
#align set.pairwise_disjoint_singleton Set.pairwiseDisjoint_singleton

theorem pairwiseDisjoint_insert {i : ι} :
    (insert i s).PairwiseDisjoint f ↔
      s.PairwiseDisjoint f ∧ ∀ j ∈ s, i ≠ j → Disjoint (f i) (f j) :=
  pairwise_insert_of_symmetric <| symmetric_disjoint.comap f
#align set.pairwise_disjoint_insert Set.pairwiseDisjoint_insert

theorem pairwiseDisjoint_insert_of_not_mem {i : ι} (hi : i ∉ s) :
    (insert i s).PairwiseDisjoint f ↔ s.PairwiseDisjoint f ∧ ∀ j ∈ s, Disjoint (f i) (f j) :=
  pairwise_insert_of_symmetric_of_not_mem (symmetric_disjoint.comap f) hi
#align set.pairwise_disjoint_insert_of_not_mem Set.pairwiseDisjoint_insert_of_not_mem

protected theorem PairwiseDisjoint.insert (hs : s.PairwiseDisjoint f) {i : ι}
    (h : ∀ j ∈ s, i ≠ j → Disjoint (f i) (f j)) : (insert i s).PairwiseDisjoint f :=
  pairwiseDisjoint_insert.2 ⟨hs, h⟩
#align set.pairwise_disjoint.insert Set.PairwiseDisjoint.insert

theorem PairwiseDisjoint.insert_of_not_mem (hs : s.PairwiseDisjoint f) {i : ι} (hi : i ∉ s)
    (h : ∀ j ∈ s, Disjoint (f i) (f j)) : (insert i s).PairwiseDisjoint f :=
  (pairwiseDisjoint_insert_of_not_mem hi).2 ⟨hs, h⟩
#align set.pairwise_disjoint.insert_of_not_mem Set.PairwiseDisjoint.insert_of_not_mem

theorem PairwiseDisjoint.image_of_le (hs : s.PairwiseDisjoint f) {g : ι → ι} (hg : f ∘ g ≤ f) :
    (g '' s).PairwiseDisjoint f := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h
  -- ⊢ (Disjoint on f) (g a) (g b)
  exact (hs ha hb <| ne_of_apply_ne _ h).mono (hg a) (hg b)
  -- 🎉 no goals
#align set.pairwise_disjoint.image_of_le Set.PairwiseDisjoint.image_of_le

theorem InjOn.pairwiseDisjoint_image {g : ι' → ι} {s : Set ι'} (h : s.InjOn g) :
    (g '' s).PairwiseDisjoint f ↔ s.PairwiseDisjoint (f ∘ g) :=
  h.pairwise_image
#align set.inj_on.pairwise_disjoint_image Set.InjOn.pairwiseDisjoint_image

theorem PairwiseDisjoint.range (g : s → ι) (hg : ∀ i : s, f (g i) ≤ f i)
    (ht : s.PairwiseDisjoint f) : (range g).PairwiseDisjoint f := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
  -- ⊢ (Disjoint on f) (g x) (g y)
  exact ((ht x.2 y.2) fun h => hxy <| congr_arg g <| Subtype.ext h).mono (hg x) (hg y)
  -- 🎉 no goals
#align set.pairwise_disjoint.range Set.PairwiseDisjoint.range

theorem pairwiseDisjoint_union :
    (s ∪ t).PairwiseDisjoint f ↔
      s.PairwiseDisjoint f ∧
        t.PairwiseDisjoint f ∧ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ t → i ≠ j → Disjoint (f i) (f j) :=
  pairwise_union_of_symmetric <| symmetric_disjoint.comap f
#align set.pairwise_disjoint_union Set.pairwiseDisjoint_union

theorem PairwiseDisjoint.union (hs : s.PairwiseDisjoint f) (ht : t.PairwiseDisjoint f)
    (h : ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ t → i ≠ j → Disjoint (f i) (f j)) : (s ∪ t).PairwiseDisjoint f :=
  pairwiseDisjoint_union.2 ⟨hs, ht, h⟩
#align set.pairwise_disjoint.union Set.PairwiseDisjoint.union

-- classical
theorem PairwiseDisjoint.elim (hs : s.PairwiseDisjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (h : ¬Disjoint (f i) (f j)) : i = j :=
  hs.eq hi hj h
#align set.pairwise_disjoint.elim Set.PairwiseDisjoint.elim

end PartialOrderBot

section SemilatticeInfBot

variable [SemilatticeInf α] [OrderBot α] {s t : Set ι} {f g : ι → α}

-- classical
theorem PairwiseDisjoint.elim' (hs : s.PairwiseDisjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (h : f i ⊓ f j ≠ ⊥) : i = j :=
  (hs.elim hi hj) fun hij => h hij.eq_bot
#align set.pairwise_disjoint.elim' Set.PairwiseDisjoint.elim'

theorem PairwiseDisjoint.eq_of_le (hs : s.PairwiseDisjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (hf : f i ≠ ⊥) (hij : f i ≤ f j) : i = j :=
  (hs.elim' hi hj) fun h => hf <| (inf_of_le_left hij).symm.trans h
#align set.pairwise_disjoint.eq_of_le Set.PairwiseDisjoint.eq_of_le

end SemilatticeInfBot

/-! ### Pairwise disjoint set of sets -/

variable {s : Set ι} {t : Set ι'}

theorem pairwiseDisjoint_range_singleton :
    (range (singleton : ι → Set ι)).PairwiseDisjoint id := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h
  -- ⊢ (Disjoint on id) {a} {b}
  exact disjoint_singleton.2 (ne_of_apply_ne _ h)
  -- 🎉 no goals
#align set.pairwise_disjoint_range_singleton Set.pairwiseDisjoint_range_singleton

theorem pairwiseDisjoint_fiber (f : ι → α) (s : Set α) : s.PairwiseDisjoint fun a => f ⁻¹' {a} :=
  fun _a _ _b _ h => disjoint_iff_inf_le.mpr fun _i ⟨hia, hib⟩ => h <| (Eq.symm hia).trans hib
#align set.pairwise_disjoint_fiber Set.pairwiseDisjoint_fiber

-- classical
theorem PairwiseDisjoint.elim_set {s : Set ι} {f : ι → Set α} (hs : s.PairwiseDisjoint f) {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) (a : α) (hai : a ∈ f i) (haj : a ∈ f j) : i = j :=
  hs.elim hi hj <| not_disjoint_iff.2 ⟨a, hai, haj⟩
#align set.pairwise_disjoint.elim_set Set.PairwiseDisjoint.elim_set

theorem PairwiseDisjoint.prod {f : ι → Set α} {g : ι' → Set β} (hs : s.PairwiseDisjoint f)
    (ht : t.PairwiseDisjoint g) :
    (s ×ˢ t : Set (ι × ι')).PairwiseDisjoint fun i => f i.1 ×ˢ g i.2 :=
  fun ⟨_, _⟩ ⟨hi, hi'⟩ ⟨_, _⟩ ⟨hj, hj'⟩ hij =>
  disjoint_left.2 fun ⟨_, _⟩ ⟨hai, hbi⟩ ⟨haj, hbj⟩ =>
    hij <| Prod.ext (hs.elim_set hi hj _ hai haj) <| ht.elim_set hi' hj' _ hbi hbj
#align set.pairwise_disjoint.prod Set.PairwiseDisjoint.prod

theorem pairwiseDisjoint_pi {ι' α : ι → Type*} {s : ∀ i, Set (ι' i)} {f : ∀ i, ι' i → Set (α i)}
    (hs : ∀ i, (s i).PairwiseDisjoint (f i)) :
    ((univ : Set ι).pi s).PairwiseDisjoint fun I => (univ : Set ι).pi fun i => f _ (I i) :=
  fun _ hI _ hJ hIJ =>
  disjoint_left.2 fun a haI haJ =>
    hIJ <|
      funext fun i =>
        (hs i).elim_set (hI i trivial) (hJ i trivial) (a i) (haI i trivial) (haJ i trivial)
#align set.pairwise_disjoint_pi Set.pairwiseDisjoint_pi

/-- The partial images of a binary function `f` whose partial evaluations are injective are pairwise
disjoint iff `f` is injective . -/
theorem pairwiseDisjoint_image_right_iff {f : α → β → γ} {s : Set α} {t : Set β}
    (hf : ∀ a ∈ s, Injective (f a)) :
    (s.PairwiseDisjoint fun a => f a '' t) ↔ (s ×ˢ t).InjOn fun p => f p.1 p.2 := by
  refine' ⟨fun hs x hx y hy (h : f _ _ = _) => _, fun hs x hx y hy h => _⟩
  -- ⊢ x = y
  · suffices x.1 = y.1 by exact Prod.ext this (hf _ hx.1 <| h.trans <| by rw [this])
    -- ⊢ x.fst = y.fst
    refine' hs.elim hx.1 hy.1 (not_disjoint_iff.2 ⟨_, mem_image_of_mem _ hx.2, _⟩)
    -- ⊢ f x.fst x.snd ∈ f y.fst '' t
    rw [h]
    -- ⊢ (fun p => f p.fst p.snd) y ∈ f y.fst '' t
    exact mem_image_of_mem _ hy.2
    -- 🎉 no goals
  · refine' disjoint_iff_inf_le.mpr _
    -- ⊢ (fun a => f a '' t) x ⊓ (fun a => f a '' t) y ≤ ⊥
    rintro _ ⟨⟨a, ha, hab⟩, b, hb, rfl⟩
    -- ⊢ f y b ∈ ⊥
    exact h (congr_arg Prod.fst <| hs (mk_mem_prod hx ha) (mk_mem_prod hy hb) hab)
    -- 🎉 no goals
#align set.pairwise_disjoint_image_right_iff Set.pairwiseDisjoint_image_right_iff

/-- The partial images of a binary function `f` whose partial evaluations are injective are pairwise
disjoint iff `f` is injective . -/
theorem pairwiseDisjoint_image_left_iff {f : α → β → γ} {s : Set α} {t : Set β}
    (hf : ∀ b ∈ t, Injective fun a => f a b) :
    (t.PairwiseDisjoint fun b => (fun a => f a b) '' s) ↔ (s ×ˢ t).InjOn fun p => f p.1 p.2 := by
  refine' ⟨fun ht x hx y hy (h : f _ _ = _) => _, fun ht x hx y hy h => _⟩
  -- ⊢ x = y
  · suffices x.2 = y.2 by exact Prod.ext (hf _ hx.2 <| h.trans <| by rw [this]) this
    -- ⊢ x.snd = y.snd
    refine' ht.elim hx.2 hy.2 (not_disjoint_iff.2 ⟨_, mem_image_of_mem _ hx.1, _⟩)
    -- ⊢ f x.fst x.snd ∈ (fun a => f a y.snd) '' s
    rw [h]
    -- ⊢ (fun p => f p.fst p.snd) y ∈ (fun a => f a y.snd) '' s
    exact mem_image_of_mem _ hy.1
    -- 🎉 no goals
  · refine' disjoint_iff_inf_le.mpr _
    -- ⊢ (fun b => (fun a => f a b) '' s) x ⊓ (fun b => (fun a => f a b) '' s) y ≤ ⊥
    rintro _ ⟨⟨a, ha, hab⟩, b, hb, rfl⟩
    -- ⊢ (fun a => f a y) b ∈ ⊥
    exact h (congr_arg Prod.snd <| ht (mk_mem_prod ha hx) (mk_mem_prod hb hy) hab)
    -- 🎉 no goals
#align set.pairwise_disjoint_image_left_iff Set.pairwiseDisjoint_image_left_iff

lemma exists_ne_mem_inter_of_not_pairwiseDisjoint
    {f : ι → Set α} (h : ¬ s.PairwiseDisjoint f) :
    ∃ i ∈ s, ∃ j ∈ s, ∃ (_hij : i ≠ j) (x : α), x ∈ f i ∩ f j := by
  change ¬ ∀ i, i ∈ s → ∀ j, j ∈ s → i ≠ j → ∀ t, t ≤ f i → t ≤ f j → t ≤ ⊥ at h
  -- ⊢ ∃ i, i ∈ s ∧ ∃ j, j ∈ s ∧ ∃ _hij x, x ∈ f i ∩ f j
  simp only [not_forall] at h
  -- ⊢ ∃ i, i ∈ s ∧ ∃ j, j ∈ s ∧ ∃ _hij x, x ∈ f i ∩ f j
  obtain ⟨i, hi, j, hj, h_ne, t, hfi, hfj, ht⟩ := h
  -- ⊢ ∃ i, i ∈ s ∧ ∃ j, j ∈ s ∧ ∃ _hij x, x ∈ f i ∩ f j
  replace ht : t.Nonempty := by
    rwa [le_bot_iff, bot_eq_empty, ← Ne.def, ← nonempty_iff_ne_empty] at ht
  obtain ⟨x, hx⟩ := ht
  -- ⊢ ∃ i, i ∈ s ∧ ∃ j, j ∈ s ∧ ∃ _hij x, x ∈ f i ∩ f j
  exact ⟨i, hi, j, hj, h_ne, x, hfi hx, hfj hx⟩
  -- 🎉 no goals

lemma exists_lt_mem_inter_of_not_pairwiseDisjoint [LinearOrder ι]
    {f : ι → Set α} (h : ¬ s.PairwiseDisjoint f) :
    ∃ i ∈ s, ∃ j ∈ s, ∃ (_hij : i < j) (x : α), x ∈ f i ∩ f j := by
  obtain ⟨i, hi, j, hj, hne, x, hx₁, hx₂⟩ := exists_ne_mem_inter_of_not_pairwiseDisjoint h
  -- ⊢ ∃ i, i ∈ s ∧ ∃ j, j ∈ s ∧ ∃ _hij x, x ∈ f i ∩ f j
  cases' lt_or_lt_iff_ne.mpr hne with h_lt h_lt
  -- ⊢ ∃ i, i ∈ s ∧ ∃ j, j ∈ s ∧ ∃ _hij x, x ∈ f i ∩ f j
  · exact ⟨i, hi, j, hj, h_lt, x, hx₁, hx₂⟩
    -- 🎉 no goals
  · exact ⟨j, hj, i, hi, h_lt, x, hx₂, hx₁⟩
    -- 🎉 no goals

end Set

lemma exists_ne_mem_inter_of_not_pairwise_disjoint
    {f : ι → Set α} (h : ¬ Pairwise (Disjoint on f)) :
    ∃ (i j : ι) (_hij : i ≠ j) (x : α), x ∈ f i ∩ f j := by
  rw [← pairwise_univ] at h
  -- ⊢ ∃ i j _hij x, x ∈ f i ∩ f j
  obtain ⟨i, _hi, j, _hj, h⟩ := exists_ne_mem_inter_of_not_pairwiseDisjoint h
  -- ⊢ ∃ i j _hij x, x ∈ f i ∩ f j
  exact ⟨i, j, h⟩
  -- 🎉 no goals

lemma exists_lt_mem_inter_of_not_pairwise_disjoint [LinearOrder ι]
    {f : ι → Set α} (h : ¬ Pairwise (Disjoint on f)) :
    ∃ (i j : ι) (_ : i < j) (x : α), x ∈ f i ∩ f j := by
  rw [← pairwise_univ] at h
  -- ⊢ ∃ i j x x, x ∈ f i ∩ f j
  obtain ⟨i, _hi, j, _hj, h⟩ := exists_lt_mem_inter_of_not_pairwiseDisjoint h
  -- ⊢ ∃ i j x x, x ∈ f i ∩ f j
  exact ⟨i, j, h⟩
  -- 🎉 no goals

theorem pairwise_disjoint_fiber (f : ι → α) : Pairwise (Disjoint on fun a : α => f ⁻¹' {a}) :=
  pairwise_univ.1 <| Set.pairwiseDisjoint_fiber f univ
#align pairwise_disjoint_fiber pairwise_disjoint_fiber
