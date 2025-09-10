/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.AdaptationNote
import Mathlib.Tactic.Simps.Basic

/-!
# Subtypes

This file provides basic API for subtypes, which are defined in core.

A subtype is a type made from restricting another type, say `α`, to its elements that satisfy some
predicate, say `p : α → Prop`. Specifically, it is the type of pairs `⟨val, property⟩` where
`val : α` and `property : p val`. It is denoted `Subtype p` and notation `{val : α // p val}` is
available.

A subtype has a natural coercion to the parent type, by coercing `⟨val, property⟩` to `val`. As
such, subtypes can be thought of as bundled sets, the difference being that elements of a set are
still of type `α` while elements of a subtype aren't.
-/


open Function

namespace Subtype

variable {α β γ : Sort*} {p q : α → Prop}

attribute [coe] Subtype.val

initialize_simps_projections Subtype (val → coe)

/-- A version of `x.property` or `x.2` where `p` is syntactically applied to the coercion of `x`
  instead of `x.1`. A similar result is `Subtype.mem` in `Mathlib/Data/Set/Basic.lean`. -/
-- This is a leftover from Lean 3: it is identical to `Subtype.property`, and should be deprecated.
theorem prop (x : Subtype p) : p x :=
  x.2

/-- An alternative version of `Subtype.forall`. This one is useful if Lean cannot figure out `q`
  when using `Subtype.forall` from right to left. -/
protected theorem forall' {q : ∀ x, p x → Prop} : (∀ x h, q x h) ↔ ∀ x : { a // p a }, q x x.2 :=
  (@Subtype.forall _ _ fun x ↦ q x.1 x.2).symm

/-- An alternative version of `Subtype.exists`. This one is useful if Lean cannot figure out `q`
  when using `Subtype.exists` from right to left. -/
protected theorem exists' {q : ∀ x, p x → Prop} : (∃ x h, q x h) ↔ ∃ x : { a // p a }, q x x.2 :=
  (@Subtype.exists _ _ fun x ↦ q x.1 x.2).symm

theorem heq_iff_coe_eq (h : ∀ x, p x ↔ q x) {a1 : { x // p x }} {a2 : { x // q x }} :
    a1 ≍ a2 ↔ (a1 : α) = (a2 : α) :=
  Eq.rec
    (motive := fun (pp : (α → Prop)) _ ↦ ∀ a2' : {x // pp x}, a1 ≍ a2' ↔ (a1 : α) = (a2' : α))
    (fun _ ↦ heq_iff_eq.trans Subtype.ext_iff) (funext <| fun x ↦ propext (h x)) a2

lemma heq_iff_coe_heq {α β : Sort _} {p : α → Prop} {q : β → Prop} {a : {x // p x}}
    {b : {y // q y}} (h : α = β) (h' : p ≍ q) : a ≍ b ↔ (a : α) ≍ (b : β) := by
  subst h
  subst h'
  rw [heq_iff_eq, heq_iff_eq, Subtype.ext_iff]

@[deprecated Subtype.ext (since := "2025-09-10")]
theorem ext_val {a1 a2 : { x // p x }} : a1.1 = a2.1 → a1 = a2 :=
  Subtype.ext

@[deprecated Subtype.ext_iff (since := "2025-09-10")]
theorem ext_iff_val {a1 a2 : { x // p x }} : a1 = a2 ↔ a1.1 = a2.1 :=
  Subtype.ext_iff

@[simp]
theorem coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a :=
  Subtype.ext rfl

theorem coe_mk (a h) : (@mk α p a h : α) = a :=
  rfl

/-- Restatement of `Subtype.mk.injEq` as an iff. -/
theorem mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a = a' := by simp

theorem coe_eq_of_eq_mk {a : { a // p a }} {b : α} (h : ↑a = b) : a = ⟨b, h ▸ a.2⟩ :=
  Subtype.ext h

theorem coe_eq_iff {a : { a // p a }} {b : α} : ↑a = b ↔ ∃ h, a = ⟨b, h⟩ :=
  ⟨fun h ↦ h ▸ ⟨a.2, (coe_eta _ _).symm⟩, fun ⟨_, ha⟩ ↦ ha.symm ▸ rfl⟩

theorem coe_injective : Injective (fun (a : Subtype p) ↦ (a : α)) := fun _ _ ↦ Subtype.ext

@[simp] theorem val_injective : Injective (@val _ p) :=
  coe_injective

theorem coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b :=
  coe_injective.eq_iff

theorem val_inj {a b : Subtype p} : a.val = b.val ↔ a = b :=
  coe_inj

lemma coe_ne_coe {a b : Subtype p} : (a : α) ≠ b ↔ a ≠ b := coe_injective.ne_iff

@[simp]
theorem _root_.exists_eq_subtype_mk_iff {a : Subtype p} {b : α} :
    (∃ h : p b, a = Subtype.mk b h) ↔ ↑a = b :=
  coe_eq_iff.symm

@[simp]
theorem _root_.exists_subtype_mk_eq_iff {a : Subtype p} {b : α} :
    (∃ h : p b, Subtype.mk b h = a) ↔ b = a := by
  simp only [@eq_comm _ b, exists_eq_subtype_mk_iff, @eq_comm _ _ a]

theorem _root_.Function.extend_val_apply {p : β → Prop} {g : {x // p x} → γ} {j : β → γ}
    {b : β} (hb : p b) : val.extend g j b = g ⟨b, hb⟩ :=
  val_injective.extend_apply g j ⟨b, hb⟩

theorem _root_.Function.extend_val_apply' {p : β → Prop} {g : {x // p x} → γ} {j : β → γ}
    {b : β} (hb : ¬p b) : val.extend g j b = j b := by
  refine Function.extend_apply' g j b ?_
  rintro ⟨a, rfl⟩
  exact hb a.2

/-- Restrict a (dependent) function to a subtype -/
def restrict {α} {β : α → Type*} (p : α → Prop) (f : ∀ x, β x) (x : Subtype p) : β x.1 :=
  f x

theorem restrict_apply {α} {β : α → Type*} (f : ∀ x, β x) (p : α → Prop) (x : Subtype p) :
    restrict p f x = f x.1 := by
  rfl

theorem restrict_def {α β} (f : α → β) (p : α → Prop) :
    restrict p f = f ∘ (fun (a : Subtype p) ↦ a) := rfl

theorem restrict_injective {α β} {f : α → β} (p : α → Prop) (h : Injective f) :
    Injective (restrict p f) :=
  h.comp coe_injective

theorem surjective_restrict {α} {β : α → Type*} [ne : ∀ a, Nonempty (β a)] (p : α → Prop) :
    Surjective fun f : ∀ x, β x ↦ restrict p f := by
  letI := Classical.decPred p
  refine fun f ↦ ⟨fun x ↦ if h : p x then f ⟨x, h⟩ else Nonempty.some (ne x), funext <| ?_⟩
  rintro ⟨x, hx⟩
  exact dif_pos hx

/-- Defining a map into a subtype, this can be seen as a "coinduction principle" of `Subtype` -/
@[simps]
def coind {α β} (f : α → β) {p : β → Prop} (h : ∀ a, p (f a)) : α → Subtype p := fun a ↦ ⟨f a, h a⟩

theorem coind_injective {α β} {f : α → β} {p : β → Prop} (h : ∀ a, p (f a)) (hf : Injective f) :
    Injective (coind f h) := fun x y hxy ↦ hf <| by apply congr_arg Subtype.val hxy

theorem coind_surjective {α β} {f : α → β} {p : β → Prop} (h : ∀ a, p (f a)) (hf : Surjective f) :
    Surjective (coind f h) := fun x ↦
  let ⟨a, ha⟩ := hf x
  ⟨a, coe_injective ha⟩

theorem coind_bijective {α β} {f : α → β} {p : β → Prop} (h : ∀ a, p (f a)) (hf : Bijective f) :
    Bijective (coind f h) :=
  ⟨coind_injective h hf.1, coind_surjective h hf.2⟩

/-- Restriction of a function to a function on subtypes. -/
@[simps]
def map {p : α → Prop} {q : β → Prop} (f : α → β) (h : ∀ a, p a → q (f a)) :
    Subtype p → Subtype q :=
  fun x ↦ ⟨f x, h x x.prop⟩

theorem map_def {p : α → Prop} {q : β → Prop} (f : α → β) (h : ∀ a, p a → q (f a)) :
    map f h = fun x ↦ ⟨f x, h x x.prop⟩ :=
  rfl

theorem map_comp {p : α → Prop} {q : β → Prop} {r : γ → Prop} {x : Subtype p}
    (f : α → β) (h : ∀ a, p a → q (f a)) (g : β → γ) (l : ∀ a, q a → r (g a)) :
    map g l (map f h x) = map (g ∘ f) (fun a ha ↦ l (f a) <| h a ha) x :=
  rfl

theorem map_id {p : α → Prop} {h : ∀ a, p a → p (id a)} : map (@id α) h = id :=
  funext fun _ ↦ rfl

theorem map_injective {p : α → Prop} {q : β → Prop} {f : α → β} (h : ∀ a, p a → q (f a))
    (hf : Injective f) : Injective (map f h) :=
  coind_injective _ <| hf.comp coe_injective

theorem map_involutive {p : α → Prop} {f : α → α} (h : ∀ a, p a → p (f a))
    (hf : Involutive f) : Involutive (map f h) :=
  fun x ↦ Subtype.ext (hf x)

theorem map_eq {p : α → Prop} {q : β → Prop} {f g : α → β}
    (h₁ : ∀ a : α, p a → q (f a)) (h₂ : ∀ a : α, p a → q (g a))
    {x y : Subtype p} :
    map f h₁ x = map g h₂ y ↔ f x = g y :=
  Subtype.ext_iff

theorem map_ne {p : α → Prop} {q : β → Prop} {f g : α → β}
    (h₁ : ∀ a : α, p a → q (f a)) (h₂ : ∀ a : α, p a → q (g a))
    {x y : Subtype p} :
    map f h₁ x ≠ map g h₂ y ↔ f x ≠ g y :=
  map_eq h₁ h₂ |>.not

instance [HasEquiv α] (p : α → Prop) : HasEquiv (Subtype p) :=
  ⟨fun s t ↦ (s : α) ≈ (t : α)⟩

theorem equiv_iff [HasEquiv α] {p : α → Prop} {s t : Subtype p} : s ≈ t ↔ (s : α) ≈ (t : α) :=
  Iff.rfl

variable [Setoid α]

protected theorem refl (s : Subtype p) : s ≈ s :=
  Setoid.refl _

protected theorem symm {s t : Subtype p} (h : s ≈ t) : t ≈ s :=
  Setoid.symm h

protected theorem trans {s t u : Subtype p} (h₁ : s ≈ t) (h₂ : t ≈ u) : s ≈ u :=
  Setoid.trans h₁ h₂

theorem equivalence (p : α → Prop) : Equivalence (@HasEquiv.Equiv (Subtype p) _) :=
  .mk (Subtype.refl) (@Subtype.symm _ p _) (@Subtype.trans _ p _)

instance (p : α → Prop) : Setoid (Subtype p) :=
  Setoid.mk (· ≈ ·) (equivalence p)

end Subtype

namespace Subtype

/-! Some facts about sets, which require that `α` is a type. -/
variable {α : Type*}

@[simp]
theorem coe_prop {S : Set α} (a : { a // a ∈ S }) : ↑a ∈ S :=
  a.prop

theorem val_prop {S : Set α} (a : { a // a ∈ S }) : a.val ∈ S :=
  a.prop

end Subtype
