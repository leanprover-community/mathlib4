/-
Copyright (c) 2016 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Logic.Basic
import Mathlib.Function
import Mathlib.Set

universe u v w

namespace Function

section
variable {α β γ : Sort _} {f : α → β}

/-- Evaluate a function at an argument. Useful if you want to talk about the partially applied
  `Function.eval x : (∀ x, β x) → β x`. -/
@[reducible] def eval {β : α → Sort _} (x : α) (f : ∀ x, β x) : β x := f x

@[simp] lemma eval_apply {β : α → Sort _} (x : α) (f : ∀ x, β x) : eval x f = f x := rfl

lemma comp_apply {α : Sort u} {β : Sort v} {φ : Sort w} (f : β → φ) (g : α → β) (a : α) :
  (f ∘ g) a = f (g a) := rfl

lemma const_def {y : β} : (λ x : α => y) = const α y := rfl

@[simp] lemma const_apply {y : β} {x : α} : const α y x = y := rfl

@[simp] lemma const_comp {f : α → β} {c : γ} : const β c ∘ f = const α c := rfl

@[simp] lemma comp_const {f : β → γ} {b : β} : f ∘ const α b = const α (f b) := rfl

lemma id_def : @id α = λ x => x := rfl

lemma hfunext {α α': Sort u} {β : α → Sort v} {β' : α' → Sort v} {f : ∀a, β a} {f' : ∀a, β' a}
  (hα : α = α') (h : ∀a a', HEq a a' → HEq (f a) (f' a')) : HEq f f' := by
  subst hα
  have : ∀a, HEq (f a) (f' a) := λ a => h a a (HEq.refl a)
  have : β = β' := by funext a
                      exact type_eq_of_heq (this a)
  subst this
  apply heq_of_eq
  funext a
  exact eq_of_heq (this a)

lemma funext_iff {β : α → Sort _} {f₁ f₂ : ∀ (x : α), β x} : f₁ = f₂ ↔ (∀a, f₁ a = f₂ a) :=
Iff.intro (λ h a => h ▸ rfl) funext

protected lemma bijective.injective {f : α → β} (hf : bijective f) : injective f := hf.1
protected lemma bijective.surjective {f : α → β} (hf : bijective f) : surjective f := hf.2

theorem injective.eq_iff (I : injective f) {a b : α} :
  f a = f b ↔ a = b :=
⟨@I _ _, congr_arg f⟩

theorem injective.eq_iff' (I : injective f) {a b : α} {c : β} (h : f b = c) :
  f a = c ↔ a = b :=
h ▸ I.eq_iff

lemma injective.ne (hf : injective f) {a₁ a₂ : α} : a₁ ≠ a₂ → f a₁ ≠ f a₂ :=
mt (λ h => hf h)

lemma injective.ne_iff (hf : injective f) {x y : α} : f x ≠ f y ↔ x ≠ y :=
⟨mt $ congr_arg f, hf.ne⟩

lemma injective.ne_iff' (hf : injective f) {x y : α} {z : β} (h : f y = z) :
  f x ≠ z ↔ x ≠ y :=
h ▸ hf.ne_iff

/-- If the co-domain `β` of an injective function `f : α → β` has decidable equality, then
the domain `α` also has decidable equality. -/
def injective.decidable_eq [DecidableEq β] (I : injective f) : DecidableEq α :=
λ a b => decidable_of_iff _ I.eq_iff

lemma injective.of_comp {g : γ → α} (I : injective (f ∘ g)) : injective g :=
λ {x y} h => I $ show f (g x) = f (g y) from congr_arg f h

lemma injective.of_comp_iff {f : α → β} (hf : injective f) (g : γ → α) :
  injective (f ∘ g) ↔ injective g :=
⟨injective.of_comp, hf.comp⟩

lemma injective.of_comp_iff' (f : α → β) {g : γ → α} (hg : bijective g) :
  injective (f ∘ g) ↔ injective f :=
⟨ λ h x y => let ⟨x', hx⟩ := hg.surjective x
             let ⟨y', hy⟩ := hg.surjective y
             hx ▸ hy ▸ λ hf => h hf ▸ rfl,
  λ h => h.comp hg.injective⟩

lemma injective_of_subsingleton [Subsingleton α] (f : α → β) :
  injective f :=
λ {a b} ab => Subsingleton.elim _ _

lemma injective.dite (p : α → Prop) [DecidablePred p]
  {f : {a : α // p a} → β} {f' : {a : α // ¬ p a} → β}
  (hf : injective f) (hf' : injective f')
  (im_disj : ∀ {x x' : α} {hx : p x} {hx' : ¬ p x'}, f ⟨x, hx⟩ ≠ f' ⟨x', hx'⟩) :
  Function.injective (λ x => if h : p x then f ⟨x, h⟩ else f' ⟨x, h⟩) :=
by intros x₁ x₂ h
   --TODO mathlib3 uses dsimp here
   have hrw1 : (fun (x : α) => if h : p x then f ⟨x, h⟩ else f' ⟨x, h⟩) x₁ =
                if h : p x₁ then f ⟨x₁, h⟩ else f' ⟨x₁, h⟩ := rfl
   have hrw2 : (fun (x : α) => if h : p x then f ⟨x, h⟩ else f' ⟨x, h⟩) x₂ =
               if h : p x₂ then f ⟨x₂, h⟩ else f' ⟨x₂, h⟩ := rfl
   rw [hrw1, hrw2] at h
   exact Decidable.byCases
     (λ (h₁ : p x₁) =>
       Decidable.byCases
         (λ (h₂ : p x₂) => by rw [dif_pos h₁, dif_pos h₂] at h
                              injection (hf h)
                              assumption)
         (λ (h₂ : ¬ p x₂) => by rw [dif_pos h₁, dif_neg h₂] at h
                                exact (im_disj h).elim))
     (λ (h₁ : ¬ p x₁) =>
       Decidable.byCases
         (λ (h₂ : p x₂) => by rw [dif_neg h₁, dif_pos h₂] at h
                              exact (im_disj h.symm).elim)
         (λ (h₂ : ¬ p x₂) => by rw [dif_neg h₁, dif_neg h₂] at h
                                injection (hf' h)
                                assumption))

lemma surjective.of_comp {g : γ → α} (S : surjective (f ∘ g)) : surjective f :=
λ y => let ⟨x, h⟩ := S y
       ⟨g x, h⟩

lemma surjective.of_comp_iff (f : α → β) {g : γ → α} (hg : surjective g) :
  surjective (f ∘ g) ↔ surjective f :=
⟨surjective.of_comp, λ h => h.comp hg⟩

lemma surjective.of_comp_iff' {f : α → β} (hf : bijective f) (g : γ → α) :
  surjective (f ∘ g) ↔ surjective g :=
⟨λ h x => let ⟨x', hx'⟩ := h (f x)
          ⟨x', hf.injective hx'⟩, hf.surjective.comp⟩

instance decidable_eq_pfun (p : Prop) [Decidable p] (α : p → Type _)
  [∀ hp, DecidableEq (α hp)] : DecidableEq (∀hp, α hp)
| f, g => decidable_of_iff (∀ hp, f hp = g hp) funext_iff.symm

theorem surjective.forall {f : α → β} (hf : surjective f) {p : β → Prop} :
  (∀ y, p y) ↔ ∀ x, p (f x) :=
⟨λ h x => h (f x),
 λ h y => let ⟨x, hx⟩ := hf y
          hx ▸ h x⟩

theorem surjective.forall₂ {f : α → β} (hf : surjective f) {p : β → β → Prop} :
  (∀ y₁ y₂, p y₁ y₂) ↔ ∀ x₁ x₂, p (f x₁) (f x₂) :=
hf.forall.trans $ forall_congr $ λ x => hf.forall

theorem surjective.forall₃ {f : α → β} (hf : surjective f) {p : β → β → β → Prop} :
  (∀ y₁ y₂ y₃, p y₁ y₂ y₃) ↔ ∀ x₁ x₂ x₃, p (f x₁) (f x₂) (f x₃) :=
hf.forall.trans $ forall_congr $ λ x => hf.forall₂

theorem surjective.exists {f : α → β} (hf : surjective f) {p : β → Prop} :
  (∃ y, p y) ↔ ∃ x, p (f x) :=
⟨λ ⟨y, hy⟩ => let ⟨x, hx⟩ := hf y
              ⟨x, hx.symm ▸ hy⟩,
 λ ⟨x, hx⟩ => ⟨f x, hx⟩⟩

theorem surjective.exists₂ {f : α → β} (hf : surjective f) {p : β → β → Prop} :
  (∃ y₁ y₂, p y₁ y₂) ↔ ∃ x₁ x₂, p (f x₁) (f x₂) :=
hf.exists.trans $ exists_congr $ λ x => hf.exists

theorem surjective.exists₃ {f : α → β} (hf : surjective f) {p : β → β → β → Prop} :
  (∃ y₁ y₂ y₃, p y₁ y₂ y₃) ↔ ∃ x₁ x₂ x₃, p (f x₁) (f x₂) (f x₃) :=
hf.exists.trans $ exists_congr $ λ x => hf.exists₂

lemma bijective_iff_exists_unique (f : α → β) : bijective f ↔
  ∀ b : β, ∃! (a : α), f a = b :=
⟨ λ hf b => let ⟨a, ha⟩ := hf.surjective b
            ⟨a, ha, λ a' ha' => hf.injective (ha'.trans ha.symm)⟩,
  λ he => ⟨
    λ {a a'} h => ExistsUnique.unique (he (f a')) h rfl,
    λ b => ExistsUnique.exists (he b) ⟩⟩

/-- Shorthand for using projection notation with `function.bijective_iff_exists_unique`. -/
lemma bijective.exists_unique {f : α → β} (hf : bijective f) (b : β) : ∃! (a : α), f a = b :=
(bijective_iff_exists_unique f).mp hf b

lemma bijective.of_comp_iff (f : α → β) {g : γ → α} (hg : bijective g) :
  bijective (f ∘ g) ↔ bijective f :=
and_congr (injective.of_comp_iff' _ hg) (surjective.of_comp_iff _ hg.surjective)

lemma bijective.of_comp_iff' {f : α → β} (hf : bijective f) (g : γ → α) :
  Function.bijective (f ∘ g) ↔ Function.bijective g :=
and_congr (injective.of_comp_iff hf.injective _) (surjective.of_comp_iff' hf _)

/-- Cantor's diagonal argument implies that there are no surjective functions from `α`
to `Set α`. -/
theorem cantor_surjective {α} (f : α → Set α) : ¬ Function.surjective f
| h => let ⟨D, e⟩ := h (λ a => ¬ f a a)
       by have x := @iff_not_self (f D D)
          exact (@iff_not_self (f D D)) $ iff_of_eq (congr_fun e D)

/-- Cantor's diagonal argument implies that there are no injective functions from `Set α` to `α`. -/
theorem cantor_injective {α : Type _} (f : (Set α) → α) :
  ¬ Function.injective f
| i => cantor_surjective (λ a b => ∀ U, a = f U → U b) $
       right_inverse.surjective
         (λ U => funext $ λ a => propext ⟨λ h => h U rfl, λ h' U' e => i e ▸ h'⟩)

/-- `g` is a partial inverse to `f` (an injective but not necessarily
  surjective function) if `g y = some x` implies `f x = y`, and `g y = none`
  implies that `y` is not in the range of `f`. -/
def is_partial_inv {α β} (f : α → β) (g : β → Option α) : Prop :=
∀ x y, g y = some x ↔ f x = y

theorem is_partial_inv_left {α β} {f : α → β} {g} (H : is_partial_inv f g) (x) : g (f x) = some x :=
(H _ _).2 rfl

theorem injective_of_partial_inv {α β} {f : α → β} {g} (H : is_partial_inv f g) : injective f :=
λ {a b} h => Option.some.inj $ ((H _ _).2 h).symm.trans ((H _ _).2 rfl)

-- TODO mathlib3 uses Mem here
theorem injective_of_partial_inv_right {α β} {f : α → β} {g} (H : is_partial_inv f g)
 (x y b) (h₁ : g x = some b) (h₂ : g y = some b) : x = y :=
((H _ _).1 h₁).symm.trans ((H _ _).1 h₂)

theorem left_inverse.comp_eq_id {f : α → β} {g : β → α} (h : left_inverse f g) : f ∘ g = id :=
funext h

theorem left_inverse_iff_comp {f : α → β} {g : β → α} : left_inverse f g ↔ f ∘ g = id :=
⟨left_inverse.comp_eq_id, congr_fun⟩

theorem right_inverse.comp_eq_id {f : α → β} {g : β → α} (h : right_inverse f g) : g ∘ f = id :=
funext h

theorem right_inverse_iff_comp {f : α → β} {g : β → α} : right_inverse f g ↔ g ∘ f = id :=
⟨right_inverse.comp_eq_id, congr_fun⟩

theorem left_inverse.comp {f : α → β} {g : β → α} {h : β → γ} {i : γ → β}
  (hf : left_inverse f g) (hh : left_inverse h i) : left_inverse (h ∘ f) (g ∘ i) :=
λ a => show h (f (g (i a))) = a by rw [hf (i a), hh a]

theorem right_inverse.comp {f : α → β} {g : β → α} {h : β → γ} {i : γ → β}
  (hf : right_inverse f g) (hh : right_inverse h i) : right_inverse (h ∘ f) (g ∘ i) :=
left_inverse.comp hh hf

theorem left_inverse.right_inverse {f : α → β} {g : β → α} (h : left_inverse g f) :
  right_inverse f g := h

theorem right_inverse.left_inverse {f : α → β} {g : β → α} (h : right_inverse g f) :
  left_inverse f g := h

theorem left_inverse.surjective {f : α → β} {g : β → α} (h : left_inverse f g) :
  surjective f :=
h.right_inverse.surjective

theorem right_inverse.injective {f : α → β} {g : β → α} (h : right_inverse f g) :
  injective f :=
h.left_inverse.injective

theorem left_inverse.eq_right_inverse {f : α → β} {g₁ g₂ : β → α} (h₁ : left_inverse g₁ f)
  (h₂ : Function.right_inverse g₂ f) :
  g₁ = g₂ := by
  have h₃ : g₁ = g₁ ∘ f ∘ g₂ := by rw [h₂.comp_eq_id, comp.right_id]
  have h₄ : g₁ ∘ f ∘ g₂ = g₂ := by rw [← comp.assoc, h₁.comp_eq_id, comp.left_id]
  rwa [←h₄]

attribute [local instance] Classical.propDecidable

/-- We can use choice to construct explicitly a partial inverse for
  a given injective function `f`. -/
noncomputable def partial_inv {α β} (f : α → β) (b : β) : Option α :=
if h : ∃ a, f a = b then some (Classical.choose h) else none

theorem partial_inv_of_injective {α β} {f : α → β} (I : injective f) :
  is_partial_inv f (partial_inv f)
| a, b =>
⟨λ h => have hpi: partial_inv f b = if h : ∃ a, f a = b then some (Classical.choose h) else none := rfl
        if h' : ∃ a, f a = b
        then by rw [hpi, dif_pos h'] at h
                injection h with h
                subst h
                apply Classical.chooseSpec h'
        else by rw [hpi, dif_neg h'] at h; contradiction,
 λ e => e ▸ have h : ∃ a', f a' = f a := ⟨_, rfl⟩
            (dif_pos h).trans (congr_arg _ (I $ Classical.chooseSpec h))⟩

theorem partial_inv_left {α β} {f : α → β} (I : injective f) : ∀ x, partial_inv f (f x) = some x :=
is_partial_inv_left (partial_inv_of_injective I)

end
