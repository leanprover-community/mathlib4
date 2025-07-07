/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Multiset.Replicate
import Mathlib.Data.Set.List

/-!
# Mapping and folding multisets

## Main definitions

* `Multiset.map`: `map f s` applies `f` to each element of `s`.
* `Multiset.foldl`: `foldl f b s` picks elements out of `s` and applies `f (f ... b x₁) x₂`.
* `Multiset.foldr`: `foldr f b s` picks elements out of `s` and applies `f x₁ (f ... x₂ b)`.

## TODO

Many lemmas about `Multiset.map` are proven in `Mathlib/Data/Multiset/Filter.lean`:
should we switch the import direction?

-/

-- No algebra should be required
assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

/-! ### `Multiset.map` -/


/-- `map f s` is the lift of the list `map` operation. The multiplicity
  of `b` in `map f s` is the number of `a ∈ s` (counting multiplicity)
  such that `f a = b`. -/
def map (f : α → β) (s : Multiset α) : Multiset β :=
  Quot.liftOn s (fun l : List α => (l.map f : Multiset β)) fun _l₁ _l₂ p => Quot.sound (p.map f)

@[congr]
theorem map_congr {f g : α → β} {s t : Multiset α} :
    s = t → (∀ x ∈ t, f x = g x) → map f s = map g t := by
  rintro rfl h
  induction s using Quot.inductionOn
  exact congr_arg _ (List.map_congr_left h)

theorem map_hcongr {β' : Type v} {m : Multiset α} {f : α → β} {f' : α → β'} (h : β = β')
    (hf : ∀ a ∈ m, f a ≍ f' a) : map f m ≍ map f' m := by
  subst h; simp at hf
  simp [map_congr rfl hf]

theorem forall_mem_map_iff {f : α → β} {p : β → Prop} {s : Multiset α} :
    (∀ y ∈ s.map f, p y) ↔ ∀ x ∈ s, p (f x) :=
  Quotient.inductionOn' s fun _L => List.forall_mem_map

@[simp, norm_cast] lemma map_coe (f : α → β) (l : List α) : map f l = l.map f := rfl

@[simp]
theorem map_zero (f : α → β) : map f 0 = 0 :=
  rfl

@[simp]
theorem map_cons (f : α → β) (a s) : map f (a ::ₘ s) = f a ::ₘ map f s :=
  Quot.inductionOn s fun _l => rfl

theorem map_comp_cons (f : α → β) (t) : map f ∘ cons t = cons (f t) ∘ map f := by
  ext
  simp

@[simp]
theorem map_singleton (f : α → β) (a : α) : ({a} : Multiset α).map f = {f a} :=
  rfl

@[simp]
theorem map_replicate (f : α → β) (k : ℕ) (a : α) : (replicate k a).map f = replicate k (f a) := by
  simp only [← coe_replicate, map_coe, List.map_replicate]

@[simp]
theorem map_add (f : α → β) (s t) : map f (s + t) = map f s + map f t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => congr_arg _ map_append

/-- If each element of `s : Multiset α` can be lifted to `β`, then `s` can be lifted to
`Multiset β`. -/
instance canLift (c) (p) [CanLift α β c p] :
    CanLift (Multiset α) (Multiset β) (map c) fun s => ∀ x ∈ s, p x where
  prf := by
    rintro ⟨l⟩ hl
    lift l to List β using hl
    exact ⟨l, map_coe _ _⟩

@[simp]
theorem mem_map {f : α → β} {b : β} {s : Multiset α} : b ∈ map f s ↔ ∃ a, a ∈ s ∧ f a = b :=
  Quot.inductionOn s fun _l => List.mem_map

@[simp]
theorem card_map (f : α → β) (s) : card (map f s) = card s :=
  Quot.inductionOn s fun _ => length_map _

@[simp]
theorem map_eq_zero {s : Multiset α} {f : α → β} : s.map f = 0 ↔ s = 0 := by
  rw [← Multiset.card_eq_zero, Multiset.card_map, Multiset.card_eq_zero]

theorem mem_map_of_mem (f : α → β) {a : α} {s : Multiset α} (h : a ∈ s) : f a ∈ map f s :=
  mem_map.2 ⟨_, h, rfl⟩

theorem map_eq_singleton {f : α → β} {s : Multiset α} {b : β} :
    map f s = {b} ↔ ∃ a : α, s = {a} ∧ f a = b := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ : ∃ a, s = {a} := by rw [← card_eq_one, ← card_map, h, card_singleton]
    refine ⟨a, ha, ?_⟩
    rw [← mem_singleton, ← h, ha, map_singleton, mem_singleton]
  · rintro ⟨a, rfl, rfl⟩
    simp

theorem map_eq_cons [DecidableEq α] (f : α → β) (s : Multiset α) (t : Multiset β) (b : β) :
    (∃ a ∈ s, f a = b ∧ (s.erase a).map f = t) ↔ s.map f = b ::ₘ t := by
  constructor
  · rintro ⟨a, ha, rfl, rfl⟩
    rw [← map_cons, Multiset.cons_erase ha]
  · intro h
    have : b ∈ s.map f := by
      rw [h]
      exact mem_cons_self _ _
    obtain ⟨a, h1, rfl⟩ := mem_map.mp this
    obtain ⟨u, rfl⟩ := exists_cons_of_mem h1
    rw [map_cons, cons_inj_right] at h
    refine ⟨a, mem_cons_self _ _, rfl, ?_⟩
    rw [Multiset.erase_cons_head, h]

-- The simpNF linter says that the LHS can be simplified via `Multiset.mem_map`.
-- However this is a higher priority lemma.
-- It seems the side condition `H` is not applied by `simpNF`.
-- https://github.com/leanprover/std4/issues/207
@[simp 1100, nolint simpNF]
theorem mem_map_of_injective {f : α → β} (H : Function.Injective f) {a : α} {s : Multiset α} :
    f a ∈ map f s ↔ a ∈ s :=
  Quot.inductionOn s fun _l => List.mem_map_of_injective H

@[simp]
theorem map_map (g : β → γ) (f : α → β) (s : Multiset α) : map g (map f s) = map (g ∘ f) s :=
  Quot.inductionOn s fun _l => congr_arg _ List.map_map

theorem map_id (s : Multiset α) : map id s = s :=
  Quot.inductionOn s fun _l => congr_arg _ <| List.map_id _

@[simp]
theorem map_id' (s : Multiset α) : map (fun x => x) s = s :=
  map_id s

-- `simp`-normal form lemma is `map_const'`
theorem map_const (s : Multiset α) (b : β) : map (const α b) s = replicate (card s) b :=
  Quot.inductionOn s fun _ => congr_arg _ List.map_const'

@[simp] theorem map_const' (s : Multiset α) (b : β) : map (fun _ ↦ b) s = replicate (card s) b :=
  map_const _ _

theorem eq_of_mem_map_const {b₁ b₂ : β} {l : List α} (h : b₁ ∈ map (Function.const α b₂) l) :
    b₁ = b₂ :=
  eq_of_mem_replicate (n := card (l : Multiset α)) <| by rwa [map_const] at h

@[simp, gcongr]
theorem map_le_map {f : α → β} {s t : Multiset α} (h : s ≤ t) : map f s ≤ map f t :=
  leInductionOn h fun h => (h.map f).subperm

@[simp, gcongr]
theorem map_lt_map {f : α → β} {s t : Multiset α} (h : s < t) : s.map f < t.map f := by
  refine (map_le_map h.le).lt_of_not_ge fun H => h.ne <| eq_of_le_of_card_le h.le ?_
  rw [← s.card_map f, ← t.card_map f]
  exact card_le_card H

theorem map_mono (f : α → β) : Monotone (map f) := fun _ _ => map_le_map

theorem map_strictMono (f : α → β) : StrictMono (map f) := fun _ _ => map_lt_map

@[simp, gcongr]
theorem map_subset_map {f : α → β} {s t : Multiset α} (H : s ⊆ t) : map f s ⊆ map f t := fun _b m =>
  let ⟨a, h, e⟩ := mem_map.1 m
  mem_map.2 ⟨a, H h, e⟩

theorem map_erase [DecidableEq α] [DecidableEq β] (f : α → β) (hf : Function.Injective f) (x : α)
    (s : Multiset α) : (s.erase x).map f = (s.map f).erase (f x) := by
  induction s using Multiset.induction_on with | empty => simp | cons y s ih => ?_
  by_cases hxy : y = x
  · cases hxy
    simp
  · rw [s.erase_cons_tail hxy, map_cons, map_cons, (s.map f).erase_cons_tail (hf.ne hxy), ih]

theorem map_erase_of_mem [DecidableEq α] [DecidableEq β] (f : α → β)
    (s : Multiset α) {x : α} (h : x ∈ s) : (s.erase x).map f = (s.map f).erase (f x) := by
  induction s using Multiset.induction_on with | empty => simp | cons y s ih => ?_
  rcases eq_or_ne y x with rfl | hxy
  · simp
  replace h : x ∈ s := by simpa [hxy.symm] using h
  rw [s.erase_cons_tail hxy, map_cons, map_cons, ih h, erase_cons_tail_of_mem (mem_map_of_mem f h)]

theorem map_surjective_of_surjective {f : α → β} (hf : Function.Surjective f) :
    Function.Surjective (map f) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, map_zero _⟩
  | cons x s ih =>
    obtain ⟨y, rfl⟩ := hf x
    obtain ⟨t, rfl⟩ := ih
    exact ⟨y ::ₘ t, map_cons _ _ _⟩

/-! ### `Multiset.fold` -/


section foldl

/-- `foldl f H b s` is the lift of the list operation `foldl f b l`,
  which folds `f` over the multiset. It is well defined when `f` is right-commutative,
  that is, `f (f b a₁) a₂ = f (f b a₂) a₁`. -/
def foldl (f : β → α → β) [RightCommutative f] (b : β) (s : Multiset α) : β :=
  Quot.liftOn s (fun l => List.foldl f b l) fun _l₁ _l₂ p => p.foldl_eq b

variable (f : β → α → β) [RightCommutative f]

@[simp]
theorem foldl_zero (b) : foldl f b 0 = b :=
  rfl

@[simp]
theorem foldl_cons (b a s) : foldl f b (a ::ₘ s) = foldl f (f b a) s :=
  Quot.inductionOn s fun _l => rfl

@[simp]
theorem foldl_add (b s t) : foldl f b (s + t) = foldl f (foldl f b s) t :=
  Quotient.inductionOn₂ s t fun _ _ => foldl_append

end foldl

section foldr

/-- `foldr f H b s` is the lift of the list operation `foldr f b l`,
  which folds `f` over the multiset. It is well defined when `f` is left-commutative,
  that is, `f a₁ (f a₂ b) = f a₂ (f a₁ b)`. -/
def foldr (f : α → β → β) [LeftCommutative f] (b : β) (s : Multiset α) : β :=
  Quot.liftOn s (fun l => List.foldr f b l) fun _l₁ _l₂ p => p.foldr_eq b

variable (f : α → β → β) [LeftCommutative f]

@[simp]
theorem foldr_zero (b) : foldr f b 0 = b :=
  rfl

@[simp]
theorem foldr_cons (b a s) : foldr f b (a ::ₘ s) = f a (foldr f b s) :=
  Quot.inductionOn s fun _l => rfl

@[simp]
theorem foldr_singleton (b a) : foldr f b ({a} : Multiset α) = f a b :=
  rfl

@[simp]
theorem foldr_add (b s t) : foldr f b (s + t) = foldr f (foldr f b t) s :=
  Quotient.inductionOn₂ s t fun _ _ => foldr_append

end foldr

@[simp]
theorem coe_foldr (f : α → β → β) [LeftCommutative f] (b : β) (l : List α) :
    foldr f b l = l.foldr f b :=
  rfl

@[simp]
theorem coe_foldl (f : β → α → β) [RightCommutative f] (b : β) (l : List α) :
    foldl f b l = l.foldl f b :=
  rfl

theorem coe_foldr_swap (f : α → β → β) [LeftCommutative f] (b : β) (l : List α) :
    foldr f b l = l.foldl (fun x y => f y x) b :=
  (congr_arg (foldr f b) (coe_reverse l)).symm.trans foldr_reverse

theorem foldr_swap (f : α → β → β) [LeftCommutative f] (b : β) (s : Multiset α) :
    foldr f b s = foldl (fun x y => f y x) b s :=
  Quot.inductionOn s fun _l => coe_foldr_swap _ _ _

theorem foldl_swap (f : β → α → β) [RightCommutative f] (b : β) (s : Multiset α) :
    foldl f b s = foldr (fun x y => f y x) b s :=
  (foldr_swap _ _ _).symm

theorem foldr_induction' (f : α → β → β) [LeftCommutative f] (x : β) (q : α → Prop)
    (p : β → Prop) (s : Multiset α) (hpqf : ∀ a b, q a → p b → p (f a b)) (px : p x)
    (q_s : ∀ a ∈ s, q a) : p (foldr f x s) := by
  induction s using Multiset.induction with
  | empty => simpa
  | cons a s ihs =>
    simp only [forall_mem_cons, foldr_cons] at q_s ⊢
    exact hpqf _ _ q_s.1 (ihs q_s.2)

theorem foldr_induction (f : α → α → α) [LeftCommutative f] (x : α) (p : α → Prop)
    (s : Multiset α) (p_f : ∀ a b, p a → p b → p (f a b)) (px : p x) (p_s : ∀ a ∈ s, p a) :
    p (foldr f x s) :=
  foldr_induction' f x p p s p_f px p_s

theorem foldl_induction' (f : β → α → β) [RightCommutative f] (x : β) (q : α → Prop)
    (p : β → Prop) (s : Multiset α) (hpqf : ∀ a b, q a → p b → p (f b a)) (px : p x)
    (q_s : ∀ a ∈ s, q a) : p (foldl f x s) := by
  rw [foldl_swap]
  exact foldr_induction' (fun x y => f y x) x q p s hpqf px q_s

theorem foldl_induction (f : α → α → α) [RightCommutative f] (x : α) (p : α → Prop)
    (s : Multiset α) (p_f : ∀ a b, p a → p b → p (f b a)) (px : p x) (p_s : ∀ a ∈ s, p a) :
    p (foldl f x s) :=
  foldl_induction' f x p p s p_f px p_s

/-! ### Map for partial functions -/

theorem pmap_eq_map (p : α → Prop) (f : α → β) (s : Multiset α) :
    ∀ H, @pmap _ _ p (fun a _ => f a) s H = map f s :=
  Quot.inductionOn s fun _ H => congr_arg _ <| List.pmap_eq_map H

theorem map_pmap {p : α → Prop} (g : β → γ) (f : ∀ a, p a → β) (s) :
    ∀ H, map g (pmap f s H) = pmap (fun a h => g (f a h)) s H :=
  Quot.inductionOn s fun _ H => congr_arg _ <| List.map_pmap H

theorem pmap_eq_map_attach {p : α → Prop} (f : ∀ a, p a → β) (s) :
    ∀ H, pmap f s H = s.attach.map fun x => f x.1 (H _ x.2) :=
  Quot.inductionOn s fun _ H => congr_arg _ <| List.pmap_eq_map_attach H

@[simp]
theorem attach_map_val' (s : Multiset α) (f : α → β) : (s.attach.map fun i => f i.val) = s.map f :=
  Quot.inductionOn s fun _ => congr_arg _ List.attach_map_val

@[simp]
theorem attach_map_val (s : Multiset α) : s.attach.map Subtype.val = s :=
  (attach_map_val' _ _).trans s.map_id

theorem attach_cons (a : α) (m : Multiset α) :
    (a ::ₘ m).attach =
      ⟨a, mem_cons_self a m⟩ ::ₘ m.attach.map fun p => ⟨p.1, mem_cons_of_mem p.2⟩ :=
  Quotient.inductionOn m fun l =>
    congr_arg _ <|
      congr_arg (List.cons _) <| by
        rw [List.map_pmap]; exact List.pmap_congr_left _ fun _ _ _ _ => Subtype.eq rfl

section

variable [DecidableEq α] {s t u : Multiset α}

lemma erase_attach_map_val (s : Multiset α) (x : {x // x ∈ s}) :
    (s.attach.erase x).map (↑) = s.erase x := by
  rw [Multiset.map_erase _ val_injective, attach_map_val]

lemma erase_attach_map (s : Multiset α) (f : α → β) (x : {x // x ∈ s}) :
    (s.attach.erase x).map (fun j : {x // x ∈ s} ↦ f j) = (s.erase x).map f := by
  simp only [← Function.comp_apply (f := f)]
  rw [← map_map, erase_attach_map_val]

end

/-! ### Subtraction -/

section sub
variable [DecidableEq α] {s t u : Multiset α} {a : α}

lemma sub_eq_fold_erase (s t : Multiset α) : s - t = foldl erase s t :=
  Quotient.inductionOn₂ s t fun l₁ l₂ => by
    change ofList (l₁.diff l₂) = foldl erase l₁ l₂
    rw [diff_eq_foldl l₁ l₂]
    symm
    exact foldl_hom _ fun x y => rfl

end sub

/-! ### Lift a relation to `Multiset`s -/


section Rel

variable {δ : Type*} {r : α → β → Prop} {p : γ → δ → Prop}

theorem rel_map_left {s : Multiset γ} {f : γ → α} :
    ∀ {t}, Rel r (s.map f) t ↔ Rel (fun a b => r (f a) b) s t :=
  @(Multiset.induction_on s (by simp) (by simp +contextual [rel_cons_left]))

theorem rel_map_right {s : Multiset α} {t : Multiset γ} {f : γ → β} :
    Rel r s (t.map f) ↔ Rel (fun a b => r a (f b)) s t := by
  rw [← rel_flip, rel_map_left, ← rel_flip]; rfl

theorem rel_map {s : Multiset α} {t : Multiset β} {f : α → γ} {g : β → δ} :
    Rel p (s.map f) (t.map g) ↔ Rel (fun a b => p (f a) (g b)) s t :=
  rel_map_left.trans rel_map_right

end Rel

section Map

theorem map_eq_map {f : α → β} (hf : Function.Injective f) {s t : Multiset α} :
    s.map f = t.map f ↔ s = t := by
  rw [← rel_eq, ← rel_eq, rel_map]
  simp only [hf.eq_iff]

theorem map_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective (Multiset.map f) := fun _x _y => (map_eq_map hf).1

end Map

section Quot

theorem map_mk_eq_map_mk_of_rel {r : α → α → Prop} {s t : Multiset α} (hst : s.Rel r t) :
    s.map (Quot.mk r) = t.map (Quot.mk r) :=
  Rel.recOn hst rfl fun hab _hst ih => by simp [ih, Quot.sound hab]

theorem exists_multiset_eq_map_quot_mk {r : α → α → Prop} (s : Multiset (Quot r)) :
    ∃ t : Multiset α, s = t.map (Quot.mk r) :=
  Multiset.induction_on s ⟨0, rfl⟩ fun a _s ⟨t, ht⟩ =>
    Quot.inductionOn a fun a => ht.symm ▸ ⟨a ::ₘ t, (map_cons _ _ _).symm⟩

theorem induction_on_multiset_quot {r : α → α → Prop} {p : Multiset (Quot r) → Prop}
    (s : Multiset (Quot r)) : (∀ s : Multiset α, p (s.map (Quot.mk r))) → p s :=
  match s, exists_multiset_eq_map_quot_mk s with
  | _, ⟨_t, rfl⟩ => fun h => h _

end Quot

section Nodup

variable {s : Multiset α}

theorem Nodup.of_map (f : α → β) : Nodup (map f s) → Nodup s :=
  Quot.induction_on s fun _ => List.Nodup.of_map f

theorem Nodup.map_on {f : α → β} :
    (∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) → Nodup s → Nodup (map f s) :=
  Quot.induction_on s fun _ => List.Nodup.map_on

theorem Nodup.map {f : α → β} {s : Multiset α} (hf : Injective f) : Nodup s → Nodup (map f s) :=
  Nodup.map_on fun _ _ _ _ h => hf h

theorem nodup_map_iff_of_inj_on {f : α → β} (d : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) :
    Nodup (map f s) ↔ Nodup s :=
  ⟨Nodup.of_map _, fun h => h.map_on d⟩

theorem nodup_map_iff_of_injective {f : α → β} (d : Function.Injective f) :
    Nodup (map f s) ↔ Nodup s :=
  ⟨Nodup.of_map _, fun h => h.map d⟩

theorem inj_on_of_nodup_map {f : α → β} {s : Multiset α} :
    Nodup (map f s) → ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y :=
  Quot.induction_on s fun _ => List.inj_on_of_nodup_map

theorem nodup_map_iff_inj_on {f : α → β} {s : Multiset α} (d : Nodup s) :
    Nodup (map f s) ↔ ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y :=
  ⟨inj_on_of_nodup_map, fun h => d.map_on h⟩

theorem Nodup.pmap {p : α → Prop} {f : ∀ a, p a → β} {s : Multiset α} {H}
    (hf : ∀ a ha b hb, f a ha = f b hb → a = b) : Nodup s → Nodup (pmap f s H) :=
  Quot.induction_on s (fun _ _ => List.Nodup.pmap hf) H

@[simp]
theorem nodup_attach {s : Multiset α} : Nodup (attach s) ↔ Nodup s :=
  Quot.induction_on s fun _ => List.nodup_attach

protected alias ⟨_, Nodup.attach⟩ := nodup_attach

theorem map_eq_map_of_bij_of_nodup (f : α → γ) (g : β → γ) {s : Multiset α} {t : Multiset β}
    (hs : s.Nodup) (ht : t.Nodup) (i : ∀ a ∈ s, β) (hi : ∀ a ha, i a ha ∈ t)
    (i_inj : ∀ a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ha, i a ha = b) (h : ∀ a ha, f a = g (i a ha)) : s.map f = t.map g := by
  have : t = s.attach.map fun x => i x.1 x.2 := by
    rw [ht.ext]
    · aesop
    · exact hs.attach.map fun x y hxy ↦ Subtype.ext <| i_inj _ x.2 _ y.2 hxy
  calc
    s.map f = s.pmap (fun x _ => f x) fun _ => id := by rw [pmap_eq_map]
    _ = s.attach.map fun x => f x.1 := by rw [pmap_eq_map_attach]
    _ = t.map g := by rw [this, Multiset.map_map]; exact map_congr rfl fun x _ => h _ _

end Nodup

end Multiset
