/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Data.Set.Image
public import Mathlib.Util.Delaborators

/-!
# Predirected indexed families and sets

This file defines predirected indexed families and predirected sets. An indexed family/set is
predirected iff each pair of elements has a shared upper bound.

This is the notion of a *directed* family/set with the nonemptiness requirement dropped: a directed
family/set is usually additionally required to be nonempty, so that it has an upper bound for
*every* finite subset rather than merely for every pair. In particular the empty set is
`r`-predirected but not `r`-directed.

## Main declarations

* `Predirected r f`: Predicate stating that the indexed family `f` is `r`-predirected.
* `PredirectedOn r s`: Predicate stating that the set `s` is `r`-predirected.
* `IsPredirected α r`: Prop-valued mixin stating that `α` is `r`-predirected. Follows the style of
  the unbundled relation classes such as `Std.Total`.

## TODO

Define connected orders (the transitive symmetric closure of `≤` is everything) and show that
(co)predirected orders are connected.

## References
* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]
-/

@[expose] public section


open Function

variable {α β : Type*} {ι κ : Sort*} (r r' s : α → α → Prop)

/-- Local notation for a relation -/
local infixl:50 " ≼ " => r

/-- A family of elements of `α` is predirected (with respect to a relation `≼` on `α`)
  if there is a member of the family `≼`-above any pair in the family.

  Unlike a directed family, a predirected family is not required to be nonempty. -/
def Predirected (f : ι → α) :=
  ∀ x y, ∃ z, f x ≼ f z ∧ f y ≼ f z

/-- A subset of `α` is predirected if there is an element of the set `≼`-above any
  pair of elements in the set.

  Unlike a directed set, a predirected set is not required to be nonempty: the empty set is
  `≼`-predirected. -/
def PredirectedOn (s : Set α) :=
  ∀ x ∈ s, ∀ y ∈ s, ∃ z ∈ s, x ≼ z ∧ y ≼ z

variable {r r'}

theorem predirectedOn_iff_predirected {s} :
    @PredirectedOn α r s ↔ Predirected r (Subtype.val : s → α) := by
  simp only [PredirectedOn, Predirected, Subtype.exists, exists_and_left, exists_prop,
    Subtype.forall]
  exact forall₂_congr fun x _ => by simp [And.comm, and_assoc]

alias ⟨PredirectedOn.predirected_val, _⟩ := predirectedOn_iff_predirected

theorem predirectedOn_range {f : ι → α} : PredirectedOn r (.range f) ↔ Predirected r f := by
  simp_rw [Predirected, PredirectedOn, Set.forall_mem_range, Set.exists_range_iff]

protected alias ⟨_, Predirected.predirectedOn_range⟩ := predirectedOn_range

theorem predirectedOn_image {s : Set β} {f : β → α} :
    PredirectedOn r (f '' s) ↔ PredirectedOn (f ⁻¹'o r) s := by
  simp only [PredirectedOn, Set.mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Order.Preimage]

theorem PredirectedOn.mono' {s : Set α} (hs : PredirectedOn r s)
    (h : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → r a b → r' a b) : PredirectedOn r' s := fun _ hx _ hy =>
  let ⟨z, hz, hxz, hyz⟩ := hs _ hx _ hy
  ⟨z, hz, h hx hz hxz, h hy hz hyz⟩

theorem PredirectedOn.mono {s : Set α} (h : PredirectedOn r s) (H : ∀ ⦃a b⦄, r a b → r' a b) :
    PredirectedOn r' s :=
  h.mono' fun _ _ _ _ h ↦ H h

theorem predirected_comp {ι} {f : ι → β} {g : β → α} :
    Predirected r (g ∘ f) ↔ Predirected (g ⁻¹'o r) f :=
  Iff.rfl

lemma predirected_comp_iff_of_surjective {f : ι → κ} (hf : f.Surjective) {g : κ → α} :
    Predirected r (g ∘ f) ↔ Predirected r g := by simp [Predirected, hf.forall, hf.exists]

alias ⟨_, Predirected.comp_of_surjective⟩ := predirected_comp_iff_of_surjective

theorem Predirected.mono {s : α → α → Prop} {ι} {f : ι → α} (H : ∀ a b, r a b → s a b)
    (h : Predirected r f) : Predirected s f := fun a b =>
  let ⟨c, h₁, h₂⟩ := h a b
  ⟨c, H _ _ h₁, H _ _ h₂⟩

theorem Predirected.mono_comp (r : α → α → Prop) {ι} {rb : β → β → Prop} {g : α → β} {f : ι → α}
    (hg : ∀ ⦃x y⦄, r x y → rb (g x) (g y)) (hf : Predirected r f) : Predirected rb (g ∘ f) :=
  predirected_comp.2 <| hf.mono hg

theorem PredirectedOn.mono_comp {r : α → α → Prop} {rb : β → β → Prop} {g : α → β} {s : Set α}
    (hg : ∀ ⦃x y⦄, r x y → rb (g x) (g y)) (hf : PredirectedOn r s) : PredirectedOn rb (g '' s) :=
  predirectedOn_image.mpr (hf.mono hg)

lemma predirectedOn_onFun_iff {r : α → α → Prop} {f : β → α} {s : Set β} :
    PredirectedOn (r on f) s ↔ PredirectedOn r (f '' s) := by
  refine ⟨PredirectedOn.mono_comp (by simp), fun h x hx y hy ↦ ?_⟩
  obtain ⟨_, ⟨z, hz, rfl⟩, hz'⟩ := h (f x) (Set.mem_image_of_mem f hx) (f y)
    (Set.mem_image_of_mem f hy)
  grind

/-- A set stable by supremum is `≤`-predirected. -/
theorem predirectedOn_of_sup_mem [SemilatticeSup α] {S : Set α}
    (H : ∀ ⦃i j⦄, i ∈ S → j ∈ S → i ⊔ j ∈ S) : PredirectedOn (· ≤ ·) S := fun a ha b hb =>
  ⟨a ⊔ b, H ha hb, le_sup_left, le_sup_right⟩

theorem Predirected.extend_bot [Preorder α] [OrderBot α] {e : ι → β} {f : ι → α}
    (hf : Predirected (· ≤ ·) f) (he : Function.Injective e) :
    Predirected (· ≤ ·) (Function.extend e f ⊥) := by
  intro a b
  rcases (em (∃ i, e i = a)).symm with (ha | ⟨i, rfl⟩)
  · use b
    simp [Function.extend_apply' _ _ _ ha]
  rcases (em (∃ i, e i = b)).symm with (hb | ⟨j, rfl⟩)
  · use e i
    simp [Function.extend_apply' _ _ _ hb]
  rcases hf i j with ⟨k, hi, hj⟩
  use e k
  simp only [he.extend_apply, *, true_and]

/-- A set stable by infimum is `≥`-predirected. -/
theorem predirectedOn_of_inf_mem [SemilatticeInf α] {S : Set α}
    (H : ∀ ⦃i j⦄, i ∈ S → j ∈ S → i ⊓ j ∈ S) : PredirectedOn (· ≥ ·) S :=
  predirectedOn_of_sup_mem (α := αᵒᵈ) H

theorem Std.Total.predirected [Std.Total r] (f : ι → α) : Predirected r f := fun i j =>
  Or.casesOn (total_of r (f i) (f j)) (fun h => ⟨j, h, refl _⟩) fun h => ⟨i, refl _, h⟩

theorem Std.Total.predirectedOn [Std.Total r] (s : Set α) : PredirectedOn r s := fun a ha b hb =>
  Or.casesOn (total_of r a b) (fun h => ⟨b, hb, h, refl _⟩) fun h => ⟨a, ha, refl _, h⟩

@[simp]
theorem PredirectedOn.of_linearOrder [LinearOrder α] (s : Set α) : PredirectedOn (· ≤ ·) s :=
  Std.Total.predirectedOn s

/-- `IsPredirected α r` states that for any elements `a`, `b` there exists an element `c` such that
`r a c` and `r b c`. -/
class IsPredirected (α : Sort*) (r : α → α → Prop) : Prop where
  /-- For every pair of elements `a` and `b` there is a `c` such that `r a c` and `r b c` -/
  predirected (a b : α) : ∃ c, r a c ∧ r b c

/-- A class for an `IsPredirected` relation `≤`. -/
@[to_dual /-- A class for an `IsPredirected` relation `≥`. -/]
abbrev IsPredirectedOrder (α : Type*) [LE α] : Prop := IsPredirected α (· ≤ ·)

theorem predirected_of (r : α → α → Prop) [IsPredirected α r] (a b : α) : ∃ c, r a c ∧ r b c :=
  IsPredirected.predirected _ _

theorem predirected_of₃ (r : α → α → Prop) [IsPredirected α r] [IsTrans α r] (a b c : α) :
    ∃ d, r a d ∧ r b d ∧ r c d :=
  have ⟨e, hae, hbe⟩ := predirected_of r a b
  have ⟨f, hef, hcf⟩ := predirected_of r e c
  ⟨f, Trans.trans hae hef, Trans.trans hbe hef, hcf⟩

theorem isPredirected_onFun {f : ι → α} : IsPredirected ι (r on f) ↔ Predirected r f :=
  ⟨(·.predirected), (⟨·⟩)⟩

theorem predirected_id [IsPredirected α r] : Predirected r id := predirected_of r

theorem predirected_id_iff : Predirected r id ↔ IsPredirected α r :=
  isPredirected_onFun.symm

theorem predirectedOn_univ [IsPredirected α r] : PredirectedOn r Set.univ := fun a _ b _ =>
  let ⟨c, hc⟩ := predirected_of r a b
  ⟨c, trivial, hc⟩

theorem predirectedOn_univ_iff : PredirectedOn r Set.univ ↔ IsPredirected α r :=
  ⟨fun h =>
    ⟨fun a b =>
      let ⟨c, _, hc⟩ := h a trivial b trivial
      ⟨c, hc⟩⟩,
    @predirectedOn_univ _ _⟩

-- see Note [lower instance priority]
instance (priority := 100) Std.Total.to_isPredirected [Std.Total r] : IsPredirected α r :=
  predirected_id_iff.1 <| Std.Total.predirected _

theorem isPredirected_mono [IsPredirected α r] (h : ∀ ⦃a b⦄, r a b → s a b) : IsPredirected α s :=
  ⟨fun a b =>
    let ⟨c, ha, hb⟩ := IsPredirected.predirected a b
    ⟨c, h ha, h hb⟩⟩

@[to_dual exists_le_le]
theorem exists_ge_ge [LE α] [IsPredirectedOrder α] (a b : α) : ∃ c, a ≤ c ∧ b ≤ c :=
  predirected_of (· ≤ ·) a b

@[to_dual isPredirected_le]
instance OrderDual.isPredirected_ge [LE α] [IsPredirectedOrder α] : IsPrecodirectedOrder αᵒᵈ := by
  assumption

/-- A monotone function on an upwards-predirected type is predirected. -/
@[to_dual (reorder := H (i j)) predirected_of_isPredirected_ge
/-- An antitone function on a downwards-predirected type is predirected. -/]
theorem predirected_of_isPredirected_le [LE α] [IsPredirectedOrder α] {f : α → β} {r : β → β → Prop}
    (H : ∀ ⦃i j⦄, i ≤ j → r (f i) (f j)) : Predirected r f :=
  predirected_id.mono_comp _ H

@[to_dual predirected_ge]
theorem Monotone.predirected_le [Preorder α] [IsPredirectedOrder α] [Preorder β] {f : α → β} :
    Monotone f → Predirected (· ≤ ·) f :=
  predirected_of_isPredirected_le

@[to_dual predirected_ge]
theorem Antitone.predirected_le [Preorder α] [IsPrecodirectedOrder α] [Preorder β] {f : α → β}
    (hf : Antitone f) : Predirected (· ≤ ·) f :=
  predirected_of_isPredirected_ge hf

@[to_dual]
lemma predirectedOn_iff_isPredirectedOrder [LE α] {s : Set α} :
    PredirectedOn (· ≤ ·) s ↔ IsPredirectedOrder s := by
  rw [predirectedOn_iff_predirected, IsPredirectedOrder]
  exact ⟨fun h ↦ ⟨h⟩, fun ⟨h⟩ ↦ h⟩

@[to_dual]
alias ⟨PredirectedOn.isPredirectedOrder, PredirectedOn.of_isPredirectedOrder⟩ :=
  predirectedOn_iff_isPredirectedOrder

section Reflexive

protected theorem PredirectedOn.insert [Std.Refl r] (a : α) {s : Set α} (hd : PredirectedOn r s)
    (ha : ∀ b ∈ s, ∃ c ∈ s, a ≼ c ∧ b ≼ c) : PredirectedOn r (insert a s) := by
  rintro x (rfl | hx) y (rfl | hy)
  · exact ⟨y, Set.mem_insert _ _, refl _, refl _⟩
  · obtain ⟨w, hws, hwr⟩ := ha y hy
    exact ⟨w, Set.mem_insert_of_mem _ hws, hwr⟩
  · obtain ⟨w, hws, hwr⟩ := ha x hx
    exact ⟨w, Set.mem_insert_of_mem _ hws, hwr.symm⟩
  · obtain ⟨w, hws, hwr⟩ := hd x hx y hy
    exact ⟨w, Set.mem_insert_of_mem _ hws, hwr⟩

theorem predirectedOn_singleton [Std.Refl r] (a : α) : PredirectedOn r ({a} : Set α) :=
  fun x hx _ hy => ⟨x, hx, refl _, hx.symm ▸ hy.symm ▸ refl _⟩

theorem predirectedOn_pair [Std.Refl r] {a b : α} (hab : a ≼ b) :
    PredirectedOn r ({a, b} : Set α) :=
  (predirectedOn_singleton _).insert _ fun c hc => ⟨c, hc, hc.symm ▸ hab, refl _⟩

theorem predirectedOn_pair' [Std.Refl r] {a b : α} (hab : a ≼ b) :
    PredirectedOn r ({b, a} : Set α) := by
  rw [Set.pair_comm]
  apply predirectedOn_pair hab

end Reflexive

section Preorder

variable [Preorder α] {a : α}

@[to_dual]
protected theorem IsMax.isTop [IsPredirectedOrder α] (h : IsMax a) : IsTop a := fun b ↦
  let ⟨_, hca, hcb⟩ := exists_ge_ge a b
  hcb.trans (h hca)

@[to_dual]
lemma PredirectedOn.is_top_of_is_max {s : Set α} (hd : PredirectedOn (· ≤ ·) s)
    {m} (hm : m ∈ s) (hmax : ∀ a ∈ s, m ≤ a → a ≤ m) : ∀ a ∈ s, a ≤ m := fun a as ↦
  let ⟨x, xs, xm, xa⟩ := hd m hm a as
  xa.trans (hmax x xs xm)

@[to_dual isBot_or_exists_lt]
theorem isTop_or_exists_gt [IsPredirectedOrder α] (a : α) : IsTop a ∨ ∃ b, a < b :=
  (em (IsMax a)).imp IsMax.isTop not_isMax_iff.mp

@[to_dual]
theorem isTop_iff_isMax [IsPredirectedOrder α] : IsTop a ↔ IsMax a :=
  ⟨IsTop.isMax, IsMax.isTop⟩

/-- If `f` is monotone, `g` is antitone, and `f ≤ g`, then for all `a`, `b` we have `f a ≤ g b`. -/
theorem Monotone.forall_le_of_antitone [IsPredirectedOrder α] [Preorder β] {f g : α → β}
    (hf : Monotone f) (hg : Antitone g) (h : f ≤ g) (m n : α) : f m ≤ g n := by
  obtain ⟨k, hkm, hkn⟩ := exists_ge_ge m n
  calc
    f m ≤ f k := hf hkm
    _ ≤ g k := h _
    _ ≤ g n := hg hkn

end Preorder

section PartialOrder

variable [PartialOrder β]

section Nontrivial

variable [Nontrivial β]

variable (β) in
@[to_dual exists_lt_of_predirected_le]
theorem exists_lt_of_predirected_ge [IsPrecodirectedOrder β] :
    ∃ a b : β, a < b := by
  rcases exists_pair_ne β with ⟨a, b, hne⟩
  rcases isBot_or_exists_lt a with (ha | ⟨c, hc⟩)
  exacts [⟨a, b, (ha b).lt_of_ne hne⟩, ⟨_, _, hc⟩]

@[to_dual]
protected theorem IsMax.not_isMin [IsPredirectedOrder β] {b : β} (hb : IsMax b) : ¬ IsMin b := by
  intro hb'
  obtain ⟨a, c, hac⟩ := exists_lt_of_predirected_le β
  have := hb.isTop a
  obtain rfl := (hb' <| this).antisymm this
  exact hb'.not_lt hac

@[to_dual]
protected theorem IsMin.not_isMax' [IsPredirectedOrder β] {b : β} (hb : IsMin b) : ¬ IsMax b :=
  fun hb' ↦ hb'.toDual.not_isMax hb.toDual

end Nontrivial

variable [Preorder α] {f : α → β} {s : Set α}

-- TODO: Generalise the following two lemmas to connected orders

/-- If `f` is monotone and antitone on a predirected order, then `f` is constant. -/
lemma constant_of_monotone_antitone [IsPredirectedOrder α] (hf : Monotone f) (hf' : Antitone f)
    (a b : α) : f a = f b := by
  have := hf.forall_le_of_antitone hf' le_rfl
  exact le_antisymm (this a b) (this b a)

/-- If `f` is monotone and antitone on a predirected set `s`, then `f` is constant on `s`. -/
lemma constant_of_monotoneOn_antitoneOn (hf : MonotoneOn f s) (hf' : AntitoneOn f s)
    (hs : PredirectedOn (· ≤ ·) s) : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → f a = f b := by
  rintro a ha b hb
  obtain ⟨c, hc, hac, hbc⟩ := hs _ ha _ hb
  exact le_antisymm ((hf ha hc hac).trans <| hf' hb hc hbc) ((hf hb hc hbc).trans <| hf' ha hc hac)

end PartialOrder

-- see Note [lower instance priority]
@[to_dual]
instance (priority := 100) SemilatticeSup.instIsPredirectedOrder [SemilatticeSup α] :
    IsPredirectedOrder α :=
  ⟨fun a b => ⟨a ⊔ b, le_sup_left, le_sup_right⟩⟩

-- see Note [lower instance priority]
@[to_dual]
instance (priority := 100) OrderTop.instIsPredirectedOrder [LE α] [OrderTop α] :
    IsPredirectedOrder α :=
  ⟨fun _ _ => ⟨⊤, le_top _, le_top _⟩⟩

namespace PredirectedOn

section Pi

variable {ι : Type*} {α : ι → Type*} {r : (i : ι) → α i → α i → Prop}

lemma proj {d : Set (Π i, α i)} (hd : PredirectedOn (fun x y => ∀ i, r i (x i) (y i)) d) (i : ι) :
    PredirectedOn (r i) ((fun a => a i) '' d) :=
  PredirectedOn.mono_comp (fun _ _ h => h) (mono hd fun ⦃_ _⦄ h ↦ h i)

lemma pi {d : (i : ι) → Set (α i)} (hd : ∀ (i : ι), PredirectedOn (r i) (d i)) :
    PredirectedOn (fun x y => ∀ i, r i (x i) (y i)) (Set.pi Set.univ d) := by
  intro a ha b hb
  choose f hfd haf hbf using fun i => hd i (a i) (ha i trivial) (b i) (hb i trivial)
  exact ⟨f, fun i _ => hfd i, haf, hbf⟩

end Pi

section Prod

variable {r₂ : β → β → Prop}

/-- Local notation for a relation -/
local infixl:50 " ≼₁ " => r
/-- Local notation for a relation -/
local infixl:50 " ≼₂ " => r₂

lemma fst {d : Set (α × β)} (hd : PredirectedOn (fun p q ↦ p.1 ≼₁ q.1 ∧ p.2 ≼₂ q.2) d) :
    PredirectedOn (· ≼₁ ·) (Prod.fst '' d) :=
  PredirectedOn.mono_comp (fun ⦃_ _⦄ h ↦ h) (mono hd fun ⦃_ _⦄ h ↦ h.1)

lemma snd {d : Set (α × β)} (hd : PredirectedOn (fun p q ↦ p.1 ≼₁ q.1 ∧ p.2 ≼₂ q.2) d) :
    PredirectedOn (· ≼₂ ·) (Prod.snd '' d) :=
  PredirectedOn.mono_comp (fun ⦃_ _⦄ h ↦ h) (mono hd fun ⦃_ _⦄ h ↦ h.2)

lemma prod {d₁ : Set α} {d₂ : Set β} (h₁ : PredirectedOn (· ≼₁ ·) d₁)
    (h₂ : PredirectedOn (· ≼₂ ·) d₂) :
    PredirectedOn (fun p q ↦ p.1 ≼₁ q.1 ∧ p.2 ≼₂ q.2) (d₁ ×ˢ d₂) := fun _ hpd _ hqd => by
  obtain ⟨r₁, hdr₁, hpr₁, hqr₁⟩ := h₁ _ hpd.1 _ hqd.1
  obtain ⟨r₂, hdr₂, hpr₂, hqr₂⟩ := h₂ _ hpd.2 _ hqd.2
  exact ⟨⟨r₁, r₂⟩, ⟨hdr₁, hdr₂⟩, ⟨hpr₁, hpr₂⟩, ⟨hqr₁, hqr₂⟩⟩

end Prod

end PredirectedOn
