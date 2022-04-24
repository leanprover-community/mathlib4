/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/

import Mathlib.Init.Function
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Coe
import Mathlib.Tactic.Ext

open Function

namespace Subtype
variable {α : Sort _} {β : Sort _} {γ : Sort _} {p : α → Prop} {q : α → Prop}

def simps.coe (x: Subtype p) : α := x

/-- A version of `x.property` or `x.2` where `p` is syntactically applied to the coercion of `x`
  instead of `x.1`. A similar result is `Subtype.mem` in `data.set.basic`. -/
lemma prop (x : Subtype p) : p x := x.2

@[simp] protected theorem «forall» {q : {a // p a} → Prop} :
  (∀ x, q x) ↔ (∀ a b, q ⟨a, b⟩) :=
⟨λ h a b => h ⟨a, b⟩, λ h ⟨a, b⟩ => h a b⟩

/-- An alternative version of `Subtype.forall`. This one is useful if Lean cannot figure out `q`
  when using `Subtype.forall` from right to left. -/
protected theorem forall' {q : ∀x, p x → Prop} :
  (∀ x h, q x h) ↔ (∀ x : {a // p a}, q x x.2) :=
(@Subtype.forall _ _ (λ x => q x.1 x.2)).symm

@[simp] protected theorem «exists» {q : {a // p a} → Prop} :
  (∃ x, q x) ↔ (∃ a b, q ⟨a, b⟩) :=
⟨λ ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, λ ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩

protected lemma ext : ∀ {a1 a2 : {x // p x}}, (a1 : α) = (a2 : α) → a1 = a2
| ⟨x, h1⟩, ⟨y, h2⟩, hz => by simp [hz]

lemma ext_iff {a1 a2 : {x // p x}} : a1 = a2 ↔ (a1 : α) = (a2 : α) :=
⟨congrArg _, Subtype.ext⟩

lemma heq_iff_coe_eq (h : ∀ x, p x ↔ q x) {a1 : {x // p x}} {a2 : {x // q x}} :
  HEq a1 a2 ↔ (a1 : α) = (a2 : α) :=
Eq.rec (motive := λ (pp: (α → Prop)) _ => ∀ a2' : {x // pp x}, HEq a1 a2' ↔ (a1 : α) = (a2' : α))
       (λ a2' => heq_iff_eq.trans ext_iff) (funext $ λ x => propext (h x)) a2

lemma heq_iff_coe_heq {α β : Sort _} {p : α → Prop} {q : β → Prop} {a : {x // p x}}
  {b : {y // q y}} (h : α = β) (h' : HEq p q) :
  HEq a b ↔ HEq (a : α) (b : β) :=
by subst h
   have hpq : p = q := heq_iff_eq.1 h'
   subst hpq
   rw [heq_iff_eq, heq_iff_eq, ext_iff]

lemma ext_val {a1 a2 : {x // p x}} : a1.1 = a2.1 → a1 = a2 :=
Subtype.ext

lemma ext_iff_val {a1 a2 : {x // p x}} : a1 = a2 ↔ a1.1 = a2.1 :=
ext_iff

@[simp] theorem coe_eta (a : {a // p a}) (h : p (a : α)) : mk (a : α) h = a := Subtype.ext rfl

theorem coe_mk (a h) : (@mk α p a h : α) = a := rfl

theorem mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a = a' :=
ext_iff

theorem coe_eq_iff {a : {a // p a}} {b : α} : ↑a = b ↔ ∃ h, a = ⟨b, h⟩ :=
⟨λ h => h ▸ ⟨a.2, (coe_eta _ _).symm⟩, λ ⟨hb, ha⟩ => ha.symm ▸ rfl⟩

theorem coe_injective : injective ((↑·) : Subtype p → α) :=
by intros a b hab
   exact Subtype.ext hab

theorem val_injective : injective (@val _ p) :=
coe_injective

/-- Restrict a (dependent) function to a subtype -/
def restrict {α} {β : α → Type _} (f : ∀x, β x) (p : α → Prop) (x : Subtype p) : β x.1 :=
f x

lemma restrict_apply {α} {β : α → Type _} (f : ∀x, β x) (p : α → Prop) (x : Subtype p) :
  restrict f p x = f x.1 := rfl

lemma restrict_def {α β} (f : α → β) (p : α → Prop) : restrict f p = f ∘ (↑) := rfl

lemma restrict_injective {α β} {f : α → β} (p : α → Prop) (h : injective f) :
  injective (restrict f p) :=
h.comp coe_injective

/-- Defining a map into a subtype, this can be seen as an "coinduction principle" of `Subtype`-/
def coind {α β} (f : α → β) {p : β → Prop} (h : ∀a, p (f a)) : α → Subtype p :=
λ a => ⟨f a, h a⟩

theorem coind_injective {α β} {f : α → β} {p : β → Prop} (h : ∀a, p (f a))
  (hf : injective f) : injective (coind f h) :=
by intros x y hxy
   refine hf ?_
   apply congrArg Subtype.val hxy

theorem coind_surjective {α β} {f : α → β} {p : β → Prop} (h : ∀a, p (f a))
  (hf : surjective f) : surjective (coind f h) :=
λ x => let ⟨a, ha⟩ := hf x
       ⟨a, coe_injective ha⟩

theorem coind_bijective {α β} {f : α → β} {p : β → Prop} (h : ∀a, p (f a))
  (hf : bijective f) : bijective (coind f h) :=
⟨coind_injective h hf.1, coind_surjective h hf.2⟩

/-- Restriction of a function to a function on subtypes. -/
def map {p : α → Prop} {q : β → Prop} (f : α → β) (h : ∀a, p a → q (f a)) :
  Subtype p → Subtype q :=
λ x => ⟨f x, h x x.prop⟩

theorem map_comp {p : α → Prop} {q : β → Prop} {r : γ → Prop} {x : Subtype p}
  (f : α → β) (h : ∀a, p a → q (f a)) (g : β → γ) (l : ∀a, q a → r (g a)) :
  map g l (map f h x) = map (g ∘ f) (λ a ha => l (f a) $ h a ha) x :=
rfl

theorem map_id {p : α → Prop} {h : ∀a, p a → p (id a)} : map (@id α) h = id :=
funext $ λ ⟨v, h⟩ => rfl

lemma map_injective {p : α → Prop} {q : β → Prop} {f : α → β} (h : ∀a, p a → q (f a))
  (hf : injective f) : injective (map f h) :=
coind_injective _ $ hf.comp coe_injective

lemma map_involutive {p : α → Prop} {f : α → α} (h : ∀a, p a → p (f a))
  (hf : involutive f) : involutive (map f h) :=
λ x => Subtype.ext (hf x)

instance [HasEquiv α] (p : α → Prop) : HasEquiv (Subtype p) :=
⟨λ s t => (s : α) ≈ (t : α)⟩

/-
  Port note: we need explicit universes here because in Lean 3 we have

    has_equiv.equiv : Π {α : Sort u} [c : has_equiv α], α → α → Prop

  but in Lean 4 `HasEquiv.Equiv` is additionally parameteric over the universe of
  the result. I.e

    HasEquiv.Equiv.{u, v} : {α : Sort u} → [self : HasEquiv α] → α → α → Sort v
-/
theorem equiv_iff [HasEquiv.{u_1, 0} α] {p : α → Prop} {s t : Subtype p} :
  HasEquiv.Equiv.{max 1 u_1, 0} s t ↔ HasEquiv.Equiv.{u_1, 0} (s : α) (t : α) :=
Iff.rfl

variable [Setoid α]

protected theorem refl (s : Subtype p) : s ≈ s :=
Setoid.refl (s : α)

protected theorem symm {s t : Subtype p} (h : s ≈ t) : t ≈ s :=
Setoid.symm h

protected theorem trans {s t u : Subtype p} (h₁ : s ≈ t) (h₂ : t ≈ u) : s ≈ u :=
Setoid.trans h₁ h₂

theorem equivalence (p : α → Prop) : Equivalence (@HasEquiv.Equiv (Subtype p) _) :=
⟨Subtype.refl, @Subtype.symm _ p _, @Subtype.trans _ p _⟩

instance (p : α → Prop) : Setoid (Subtype p) :=
Setoid.mk (·≈·) (equivalence p)

end Subtype

namespace Subtype
/-! Some facts about sets, which require that `α` is a type. -/
variable {α : Type _} {β : Type _} {γ : Type _} {p : α → Prop}

-- ∈-notation is reducible in Lean 4, so this won't trigger as a simp-lemma
lemma val_prop {S : Set α} (a : {a // a ∈ S}) : a.val ∈ S := a.property

end Subtype
