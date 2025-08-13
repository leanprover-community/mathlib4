/-
Copyright (c) 2016 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Basic
import Mathlib.Logic.ExistsUnique
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Nontrivial.Defs
import Batteries.Tactic.Init
import Mathlib.Order.Defs.Unbundled

/-!
# Miscellaneous function constructions and lemmas
-/

open Function

universe u v w x

namespace Function

section

variable {α β γ : Sort*} {f : α → β}

/-- Evaluate a function at an argument. Useful if you want to talk about the partially applied
  `Function.eval x : (∀ x, β x) → β x`. -/
@[reducible, simp] def eval {β : α → Sort*} (x : α) (f : ∀ x, β x) : β x := f x

theorem eval_apply {β : α → Sort*} (x : α) (f : ∀ x, β x) : eval x f = f x :=
  rfl

theorem const_def {y : β} : (fun _ : α ↦ y) = const α y :=
  rfl

theorem const_injective [Nonempty α] : Injective (const α : β → α → β) := fun _ _ h ↦
  let ⟨x⟩ := ‹Nonempty α›
  congr_fun h x

@[simp]
theorem const_inj [Nonempty α] {y₁ y₂ : β} : const α y₁ = const α y₂ ↔ y₁ = y₂ :=
  ⟨fun h ↦ const_injective h, fun h ↦ h ▸ rfl⟩

theorem onFun_apply (f : β → β → γ) (g : α → β) (a b : α) : onFun f g a b = f (g a) (g b) :=
  rfl

lemma hfunext {α α' : Sort u} {β : α → Sort v} {β' : α' → Sort v} {f : ∀ a, β a} {f' : ∀ a, β' a}
    (hα : α = α') (h : ∀ a a', a ≍ a' → f a ≍ f' a') : f ≍ f' := by
  subst hα
  have : ∀ a, f a ≍ f' a := fun a ↦ h a a (HEq.refl a)
  have : β = β' := by funext a; exact type_eq_of_heq (this a)
  subst this
  apply heq_of_eq
  funext a
  exact eq_of_heq (this a)

theorem ne_iff {β : α → Sort*} {f₁ f₂ : ∀ a, β a} : f₁ ≠ f₂ ↔ ∃ a, f₁ a ≠ f₂ a :=
  funext_iff.not.trans not_forall

lemma funext_iff_of_subsingleton [Subsingleton α] {g : α → β} (x y : α) :
    f x = g y ↔ f = g := by
  refine ⟨fun h ↦ funext fun z ↦ ?_, fun h ↦ ?_⟩
  · rwa [Subsingleton.elim x z, Subsingleton.elim y z] at h
  · rw [h, Subsingleton.elim x y]

theorem swap_lt {α} [LT α] : swap (· < · : α → α → _) = (· > ·) := rfl
theorem swap_le {α} [LE α] : swap (· ≤ · : α → α → _) = (· ≥ ·) := rfl
theorem swap_gt {α} [LT α] : swap (· > · : α → α → _) = (· < ·) := rfl
theorem swap_ge {α} [LE α] : swap (· ≥ · : α → α → _) = (· ≤ ·) := rfl

protected theorem Bijective.injective {f : α → β} (hf : Bijective f) : Injective f := hf.1
protected theorem Bijective.surjective {f : α → β} (hf : Bijective f) : Surjective f := hf.2

theorem not_injective_iff : ¬ Injective f ↔ ∃ a b, f a = f b ∧ a ≠ b := by
  simp only [Injective, not_forall, exists_prop]

/-- If the co-domain `β` of an injective function `f : α → β` has decidable equality, then
the domain `α` also has decidable equality. -/
protected def Injective.decidableEq [DecidableEq β] (I : Injective f) : DecidableEq α :=
  fun _ _ ↦ decidable_of_iff _ I.eq_iff

theorem Injective.of_comp {g : γ → α} (I : Injective (f ∘ g)) : Injective g :=
  fun _ _ h ↦ I <| congr_arg f h

@[simp]
theorem Injective.of_comp_iff (hf : Injective f) (g : γ → α) :
    Injective (f ∘ g) ↔ Injective g :=
  ⟨Injective.of_comp, hf.comp⟩

theorem Injective.of_comp_right {g : γ → α} (I : Injective (f ∘ g)) (hg : Surjective g) :
    Injective f := fun x y h ↦ by
  obtain ⟨x, rfl⟩ := hg x
  obtain ⟨y, rfl⟩ := hg y
  exact congr_arg g (I h)

theorem Surjective.bijective₂_of_injective {g : γ → α} (hf : Surjective f) (hg : Surjective g)
    (I : Injective (f ∘ g)) : Bijective f ∧ Bijective g :=
  ⟨⟨I.of_comp_right hg, hf⟩, I.of_comp, hg⟩

@[simp]
theorem Injective.of_comp_iff' (f : α → β) {g : γ → α} (hg : Bijective g) :
    Injective (f ∘ g) ↔ Injective f :=
  ⟨fun I ↦ I.of_comp_right hg.2, fun h ↦ h.comp hg.injective⟩

theorem Injective.piMap {ι : Sort*} {α β : ι → Sort*} {f : ∀ i, α i → β i}
    (hf : ∀ i, Injective (f i)) : Injective (Pi.map f) := fun _ _ h ↦
  funext fun i ↦ hf i <| congrFun h _

/-- Composition by an injective function on the left is itself injective. -/
theorem Injective.comp_left {g : β → γ} (hg : Injective g) : Injective (g ∘ · : (α → β) → α → γ) :=
  .piMap fun _ ↦ hg

theorem injective_comp_left_iff [Nonempty α] {g : β → γ} :
    Injective (g ∘ · : (α → β) → α → γ) ↔ Injective g :=
  ⟨fun h b₁ b₂ eq ↦ Nonempty.elim ‹_›
    (congr_fun <| h (a₁ := fun _ ↦ b₁) (a₂ := fun _ ↦ b₂) <| funext fun _ ↦ eq), (·.comp_left)⟩

@[nontriviality] theorem injective_of_subsingleton [Subsingleton α] (f : α → β) : Injective f :=
  fun _ _ _ ↦ Subsingleton.elim _ _

@[nontriviality] theorem bijective_of_subsingleton [Subsingleton α] (f : α → α) : Bijective f :=
  ⟨injective_of_subsingleton f, fun a ↦ ⟨a, Subsingleton.elim ..⟩⟩

lemma Injective.dite (p : α → Prop) [DecidablePred p]
    {f : {a : α // p a} → β} {f' : {a : α // ¬ p a} → β}
    (hf : Injective f) (hf' : Injective f')
    (im_disj : ∀ {x x' : α} {hx : p x} {hx' : ¬ p x'}, f ⟨x, hx⟩ ≠ f' ⟨x', hx'⟩) :
    Function.Injective (fun x ↦ if h : p x then f ⟨x, h⟩ else f' ⟨x, h⟩) := fun x₁ x₂ h => by
  dsimp only at h
  by_cases h₁ : p x₁ <;> by_cases h₂ : p x₂
  · rw [dif_pos h₁, dif_pos h₂] at h; injection (hf h)
  · rw [dif_pos h₁, dif_neg h₂] at h; exact (im_disj h).elim
  · rw [dif_neg h₁, dif_pos h₂] at h; exact (im_disj h.symm).elim
  · rw [dif_neg h₁, dif_neg h₂] at h; injection (hf' h)

theorem Surjective.of_comp {g : γ → α} (S : Surjective (f ∘ g)) : Surjective f := fun y ↦
  let ⟨x, h⟩ := S y
  ⟨g x, h⟩

@[simp]
theorem Surjective.of_comp_iff (f : α → β) {g : γ → α} (hg : Surjective g) :
    Surjective (f ∘ g) ↔ Surjective f :=
  ⟨Surjective.of_comp, fun h ↦ h.comp hg⟩

theorem Surjective.of_comp_left {g : γ → α} (S : Surjective (f ∘ g)) (hf : Injective f) :
    Surjective g := fun a ↦ let ⟨c, hc⟩ := S (f a); ⟨c, hf hc⟩

theorem Injective.bijective₂_of_surjective {g : γ → α} (hf : Injective f) (hg : Injective g)
    (S : Surjective (f ∘ g)) : Bijective f ∧ Bijective g :=
  ⟨⟨hf, S.of_comp⟩, hg, S.of_comp_left hf⟩

@[simp]
theorem Surjective.of_comp_iff' (hf : Bijective f) (g : γ → α) :
    Surjective (f ∘ g) ↔ Surjective g :=
  ⟨fun S ↦ S.of_comp_left hf.1, hf.surjective.comp⟩

instance decidableEqPFun (p : Prop) [Decidable p] (α : p → Type*) [∀ hp, DecidableEq (α hp)] :
    DecidableEq (∀ hp, α hp)
  | f, g => decidable_of_iff (∀ hp, f hp = g hp) funext_iff.symm

protected theorem Surjective.forall (hf : Surjective f) {p : β → Prop} :
    (∀ y, p y) ↔ ∀ x, p (f x) :=
  ⟨fun h x ↦ h (f x), fun h y ↦
    let ⟨x, hx⟩ := hf y
    hx ▸ h x⟩

protected theorem Surjective.forall₂ (hf : Surjective f) {p : β → β → Prop} :
    (∀ y₁ y₂, p y₁ y₂) ↔ ∀ x₁ x₂, p (f x₁) (f x₂) :=
  hf.forall.trans <| forall_congr' fun _ ↦ hf.forall

protected theorem Surjective.forall₃ (hf : Surjective f) {p : β → β → β → Prop} :
    (∀ y₁ y₂ y₃, p y₁ y₂ y₃) ↔ ∀ x₁ x₂ x₃, p (f x₁) (f x₂) (f x₃) :=
  hf.forall.trans <| forall_congr' fun _ ↦ hf.forall₂

protected theorem Surjective.exists (hf : Surjective f) {p : β → Prop} :
    (∃ y, p y) ↔ ∃ x, p (f x) :=
  ⟨fun ⟨y, hy⟩ ↦
    let ⟨x, hx⟩ := hf y
    ⟨x, hx.symm ▸ hy⟩,
    fun ⟨x, hx⟩ ↦ ⟨f x, hx⟩⟩

protected theorem Surjective.exists₂ (hf : Surjective f) {p : β → β → Prop} :
    (∃ y₁ y₂, p y₁ y₂) ↔ ∃ x₁ x₂, p (f x₁) (f x₂) :=
  hf.exists.trans <| exists_congr fun _ ↦ hf.exists

protected theorem Surjective.exists₃ (hf : Surjective f) {p : β → β → β → Prop} :
    (∃ y₁ y₂ y₃, p y₁ y₂ y₃) ↔ ∃ x₁ x₂ x₃, p (f x₁) (f x₂) (f x₃) :=
  hf.exists.trans <| exists_congr fun _ ↦ hf.exists₂

theorem Surjective.injective_comp_right (hf : Surjective f) : Injective fun g : β → γ ↦ g ∘ f :=
  fun _ _ h ↦ funext <| hf.forall.2 <| congr_fun h

theorem injective_comp_right_iff_surjective {γ : Type*} [Nontrivial γ] :
    Injective (fun g : β → γ ↦ g ∘ f) ↔ Surjective f := by
  refine ⟨not_imp_not.mp fun not_surj inj ↦ not_subsingleton γ ⟨fun c c' ↦ ?_⟩,
    (·.injective_comp_right)⟩
  have ⟨b₀, hb⟩ := not_forall.mp not_surj
  classical have := inj (a₁ := fun _ ↦ c) (a₂ := (if · = b₀ then c' else c)) ?_
  · simpa using congr_fun this b₀
  ext a; simp only [comp_apply, if_neg fun h ↦ hb ⟨a, h⟩]

protected theorem Surjective.right_cancellable (hf : Surjective f) {g₁ g₂ : β → γ} :
    g₁ ∘ f = g₂ ∘ f ↔ g₁ = g₂ :=
  hf.injective_comp_right.eq_iff

theorem surjective_of_right_cancellable_Prop (h : ∀ g₁ g₂ : β → Prop, g₁ ∘ f = g₂ ∘ f → g₁ = g₂) :
    Surjective f :=
  injective_comp_right_iff_surjective.mp h

theorem bijective_iff_existsUnique (f : α → β) : Bijective f ↔ ∀ b : β, ∃! a : α, f a = b :=
  ⟨fun hf b ↦
      let ⟨a, ha⟩ := hf.surjective b
      ⟨a, ha, fun _ ha' ↦ hf.injective (ha'.trans ha.symm)⟩,
    fun he ↦ ⟨fun {_a a'} h ↦ (he (f a')).unique h rfl, fun b ↦ (he b).exists⟩⟩

/-- Shorthand for using projection notation with `Function.bijective_iff_existsUnique`. -/
protected theorem Bijective.existsUnique {f : α → β} (hf : Bijective f) (b : β) :
    ∃! a : α, f a = b :=
  (bijective_iff_existsUnique f).mp hf b

theorem Bijective.existsUnique_iff {f : α → β} (hf : Bijective f) {p : β → Prop} :
    (∃! y, p y) ↔ ∃! x, p (f x) :=
  ⟨fun ⟨y, hpy, hy⟩ ↦
    let ⟨x, hx⟩ := hf.surjective y
    ⟨x, by simpa [hx], fun z (hz : p (f z)) ↦ hf.injective <| hx.symm ▸ hy _ hz⟩,
    fun ⟨x, hpx, hx⟩ ↦
    ⟨f x, hpx, fun y hy ↦
      let ⟨z, hz⟩ := hf.surjective y
      hz ▸ congr_arg f (hx _ (by simpa [hz]))⟩⟩

theorem Bijective.of_comp_iff (f : α → β) {g : γ → α} (hg : Bijective g) :
    Bijective (f ∘ g) ↔ Bijective f :=
  and_congr (Injective.of_comp_iff' _ hg) (Surjective.of_comp_iff _ hg.surjective)

theorem Bijective.of_comp_iff' {f : α → β} (hf : Bijective f) (g : γ → α) :
    Function.Bijective (f ∘ g) ↔ Function.Bijective g :=
  and_congr (Injective.of_comp_iff hf.injective _) (Surjective.of_comp_iff' hf _)

/-- **Cantor's diagonal argument** implies that there are no surjective functions from `α`
to `Set α`. -/
theorem cantor_surjective {α} (f : α → Set α) : ¬Surjective f
  | h => let ⟨D, e⟩ := h {a | ¬ f a a}
        @iff_not_self (D ∈ f D) <| iff_of_eq <| congr_arg (D ∈ ·) e

/-- **Cantor's diagonal argument** implies that there are no injective functions from `Set α`
to `α`. -/
theorem cantor_injective {α : Type*} (f : Set α → α) : ¬Injective f
  | i => cantor_surjective (fun a ↦ {b | ∀ U, a = f U → U b}) <|
         RightInverse.surjective (fun U ↦ Set.ext fun _ ↦ ⟨fun h ↦ h U rfl, fun h _ e ↦ i e ▸ h⟩)

/-- There is no surjection from `α : Type u` into `Type (max u v)`. This theorem
  demonstrates why `Type : Type` would be inconsistent in Lean. -/
theorem not_surjective_Type {α : Type u} (f : α → Type max u v) : ¬Surjective f := by
  intro hf
  let T : Type max u v := Sigma f
  cases hf (Set T) with | intro U hU =>
  let g : Set T → T := fun s ↦ ⟨U, cast hU.symm s⟩
  have hg : Injective g := by
    intro s t h
    suffices cast hU (g s).2 = cast hU (g t).2 by
      simp only [g, cast_cast, cast_eq] at this
      assumption
    · congr
  exact cantor_injective g hg

/-- `g` is a partial inverse to `f` (an injective but not necessarily
  surjective function) if `g y = some x` implies `f x = y`, and `g y = none`
  implies that `y` is not in the range of `f`. -/
def IsPartialInv {α β} (f : α → β) (g : β → Option α) : Prop :=
  ∀ x y, g y = some x ↔ f x = y

theorem isPartialInv_left {α β} {f : α → β} {g} (H : IsPartialInv f g) (x) : g (f x) = some x :=
  (H _ _).2 rfl

theorem injective_of_isPartialInv {α β} {f : α → β} {g} (H : IsPartialInv f g) :
    Injective f := fun _ _ h ↦
  Option.some.inj <| ((H _ _).2 h).symm.trans ((H _ _).2 rfl)

theorem injective_of_isPartialInv_right {α β} {f : α → β} {g} (H : IsPartialInv f g) (x y b)
    (h₁ : b ∈ g x) (h₂ : b ∈ g y) : x = y :=
  ((H _ _).1 h₁).symm.trans ((H _ _).1 h₂)

theorem LeftInverse.comp_eq_id {f : α → β} {g : β → α} (h : LeftInverse f g) : f ∘ g = id :=
  funext h

theorem leftInverse_iff_comp {f : α → β} {g : β → α} : LeftInverse f g ↔ f ∘ g = id :=
  ⟨LeftInverse.comp_eq_id, congr_fun⟩

theorem RightInverse.comp_eq_id {f : α → β} {g : β → α} (h : RightInverse f g) : g ∘ f = id :=
  funext h

theorem rightInverse_iff_comp {f : α → β} {g : β → α} : RightInverse f g ↔ g ∘ f = id :=
  ⟨RightInverse.comp_eq_id, congr_fun⟩

theorem LeftInverse.comp {f : α → β} {g : β → α} {h : β → γ} {i : γ → β} (hf : LeftInverse f g)
    (hh : LeftInverse h i) : LeftInverse (h ∘ f) (g ∘ i) :=
  fun a ↦ show h (f (g (i a))) = a by rw [hf (i a), hh a]

theorem RightInverse.comp {f : α → β} {g : β → α} {h : β → γ} {i : γ → β} (hf : RightInverse f g)
    (hh : RightInverse h i) : RightInverse (h ∘ f) (g ∘ i) :=
  LeftInverse.comp hh hf

theorem LeftInverse.rightInverse {f : α → β} {g : β → α} (h : LeftInverse g f) : RightInverse f g :=
  h

theorem RightInverse.leftInverse {f : α → β} {g : β → α} (h : RightInverse g f) : LeftInverse f g :=
  h

theorem LeftInverse.surjective {f : α → β} {g : β → α} (h : LeftInverse f g) : Surjective f :=
  h.rightInverse.surjective

theorem RightInverse.injective {f : α → β} {g : β → α} (h : RightInverse f g) : Injective f :=
  h.leftInverse.injective

theorem LeftInverse.rightInverse_of_injective {f : α → β} {g : β → α} (h : LeftInverse f g)
    (hf : Injective f) : RightInverse f g :=
  fun x ↦ hf <| h (f x)

theorem LeftInverse.rightInverse_of_surjective {f : α → β} {g : β → α} (h : LeftInverse f g)
    (hg : Surjective g) : RightInverse f g :=
  fun x ↦ let ⟨y, hy⟩ := hg x; hy ▸ congr_arg g (h y)

theorem RightInverse.leftInverse_of_surjective {f : α → β} {g : β → α} :
    RightInverse f g → Surjective f → LeftInverse f g :=
  LeftInverse.rightInverse_of_surjective

theorem RightInverse.leftInverse_of_injective {f : α → β} {g : β → α} :
    RightInverse f g → Injective g → LeftInverse f g :=
  LeftInverse.rightInverse_of_injective

theorem LeftInverse.eq_rightInverse {f : α → β} {g₁ g₂ : β → α} (h₁ : LeftInverse g₁ f)
    (h₂ : RightInverse g₂ f) : g₁ = g₂ :=
  calc
    g₁ = g₁ ∘ f ∘ g₂ := by rw [h₂.comp_eq_id, comp_id]
     _ = g₂ := by rw [← comp_assoc, h₁.comp_eq_id, id_comp]

/-- We can use choice to construct explicitly a partial inverse for
  a given injective function `f`. -/
noncomputable def partialInv {α β} (f : α → β) (b : β) : Option α :=
  open scoped Classical in
  if h : ∃ a, f a = b then some (Classical.choose h) else none

theorem partialInv_of_injective {α β} {f : α → β} (I : Injective f) : IsPartialInv f (partialInv f)
  | a, b =>
  ⟨fun h =>
    open scoped Classical in
    have hpi : partialInv f b = if h : ∃ a, f a = b then some (Classical.choose h) else none :=
      rfl
    if h' : ∃ a, f a = b
    then by rw [hpi, dif_pos h'] at h
            injection h with h
            subst h
            apply Classical.choose_spec h'
    else by rw [hpi, dif_neg h'] at h; contradiction,
  fun e => e ▸ have h : ∃ a', f a' = f a := ⟨_, rfl⟩
              (dif_pos h).trans (congr_arg _ (I <| Classical.choose_spec h))⟩

theorem partialInv_left {α β} {f : α → β} (I : Injective f) : ∀ x, partialInv f (f x) = some x :=
  isPartialInv_left (partialInv_of_injective I)

end

section InvFun

variable {α β : Sort*} [Nonempty α] {f : α → β} {b : β}

/-- The inverse of a function (which is a left inverse if `f` is injective
  and a right inverse if `f` is surjective). -/
-- Explicit Sort so that `α` isn't inferred to be Prop via `exists_prop_decidable`
noncomputable def invFun {α : Sort u} {β} [Nonempty α] (f : α → β) : β → α :=
  open scoped Classical in
  fun y ↦ if h : (∃ x, f x = y) then h.choose else Classical.arbitrary α

theorem invFun_eq (h : ∃ a, f a = b) : f (invFun f b) = b := by
  simp only [invFun, dif_pos h, h.choose_spec]

theorem apply_invFun_apply {α β : Type*} {f : α → β} {a : α} :
    f (@invFun _ _ ⟨a⟩ f (f a)) = f a :=
  @invFun_eq _ _ ⟨a⟩ _ _ ⟨_, rfl⟩

theorem invFun_neg (h : ¬∃ a, f a = b) : invFun f b = Classical.choice ‹_› :=
  dif_neg h

theorem invFun_eq_of_injective_of_rightInverse {g : β → α} (hf : Injective f)
    (hg : RightInverse g f) : invFun f = g :=
  funext fun b ↦
    hf
      (by
        rw [hg b]
        exact invFun_eq ⟨g b, hg b⟩)

theorem rightInverse_invFun (hf : Surjective f) : RightInverse (invFun f) f :=
  fun b ↦ invFun_eq <| hf b

theorem leftInverse_invFun (hf : Injective f) : LeftInverse (invFun f) f :=
  fun b ↦ hf <| invFun_eq ⟨b, rfl⟩

theorem invFun_surjective (hf : Injective f) : Surjective (invFun f) :=
  (leftInverse_invFun hf).surjective

theorem invFun_comp (hf : Injective f) : invFun f ∘ f = id :=
  funext <| leftInverse_invFun hf

theorem Injective.hasLeftInverse (hf : Injective f) : HasLeftInverse f :=
  ⟨invFun f, leftInverse_invFun hf⟩

theorem injective_iff_hasLeftInverse : Injective f ↔ HasLeftInverse f :=
  ⟨Injective.hasLeftInverse, HasLeftInverse.injective⟩

end InvFun

section SurjInv

variable {α : Sort u} {β : Sort v} {γ : Sort w} {f : α → β}

/-- The inverse of a surjective function. (Unlike `invFun`, this does not require
  `α` to be inhabited.) -/
noncomputable def surjInv {f : α → β} (h : Surjective f) (b : β) : α :=
  Classical.choose (h b)

theorem surjInv_eq (h : Surjective f) (b) : f (surjInv h b) = b :=
  Classical.choose_spec (h b)

theorem rightInverse_surjInv (hf : Surjective f) : RightInverse (surjInv hf) f :=
  surjInv_eq hf

theorem leftInverse_surjInv (hf : Bijective f) : LeftInverse (surjInv hf.2) f :=
  rightInverse_of_injective_of_leftInverse hf.1 (rightInverse_surjInv hf.2)

theorem Surjective.hasRightInverse (hf : Surjective f) : HasRightInverse f :=
  ⟨_, rightInverse_surjInv hf⟩

theorem surjective_iff_hasRightInverse : Surjective f ↔ HasRightInverse f :=
  ⟨Surjective.hasRightInverse, HasRightInverse.surjective⟩

theorem bijective_iff_has_inverse : Bijective f ↔ ∃ g, LeftInverse g f ∧ RightInverse g f :=
  ⟨fun hf ↦ ⟨_, leftInverse_surjInv hf, rightInverse_surjInv hf.2⟩, fun ⟨_, gl, gr⟩ ↦
    ⟨gl.injective, gr.surjective⟩⟩

theorem injective_surjInv (h : Surjective f) : Injective (surjInv h) :=
  (rightInverse_surjInv h).injective

theorem surjective_to_subsingleton [na : Nonempty α] [Subsingleton β] (f : α → β) :
    Surjective f :=
  fun _ ↦ let ⟨a⟩ := na; ⟨a, Subsingleton.elim _ _⟩

theorem Surjective.piMap {ι : Sort*} {α β : ι → Sort*} {f : ∀ i, α i → β i}
    (hf : ∀ i, Surjective (f i)) : Surjective (Pi.map f) := fun g ↦
  ⟨fun i ↦ surjInv (hf i) (g i), funext fun _ ↦ rightInverse_surjInv _ _⟩

/-- Composition by a surjective function on the left is itself surjective. -/
theorem Surjective.comp_left {g : β → γ} (hg : Surjective g) :
    Surjective (g ∘ · : (α → β) → α → γ) :=
  .piMap fun _ ↦ hg

theorem surjective_comp_left_iff [Nonempty α] {g : β → γ} :
    Surjective (g ∘ · : (α → β) → α → γ) ↔ Surjective g := by
  refine ⟨fun h c ↦ Nonempty.elim ‹_› fun a ↦ ?_, (·.comp_left)⟩
  have ⟨f, hf⟩ := h fun _ ↦ c
  exact ⟨f a, congr_fun hf _⟩

theorem Bijective.piMap {ι : Sort*} {α β : ι → Sort*} {f : ∀ i, α i → β i}
    (hf : ∀ i, Bijective (f i)) : Bijective (Pi.map f) :=
  ⟨.piMap fun i ↦ (hf i).1, .piMap fun i ↦ (hf i).2⟩

/-- Composition by a bijective function on the left is itself bijective. -/
theorem Bijective.comp_left {g : β → γ} (hg : Bijective g) :
    Bijective (g ∘ · : (α → β) → α → γ) :=
  ⟨hg.injective.comp_left, hg.surjective.comp_left⟩

end SurjInv

section Update

variable {α : Sort u} {β : α → Sort v} {α' : Sort w} [DecidableEq α]
  {f : (a : α) → β a} {a : α} {b : β a}


/-- Replacing the value of a function at a given point by a given value. -/
def update (f : ∀ a, β a) (a' : α) (v : β a') (a : α) : β a :=
  if h : a = a' then Eq.ndrec v h.symm else f a

@[simp]
theorem update_self (a : α) (v : β a) (f : ∀ a, β a) : update f a v a = v :=
  dif_pos rfl

@[simp]
theorem update_of_ne {a a' : α} (h : a ≠ a') (v : β a') (f : ∀ a, β a) : update f a' v a = f a :=
  dif_neg h

/-- On non-dependent functions, `Function.update` can be expressed as an `ite` -/
theorem update_apply {β : Sort*} (f : α → β) (a' : α) (b : β) (a : α) :
    update f a' b a = if a = a' then b else f a := by
  rcases Decidable.eq_or_ne a a' with rfl | hne <;> simp [*]

@[nontriviality]
theorem update_eq_const_of_subsingleton [Subsingleton α] (a : α) (v : α') (f : α → α') :
    update f a v = const α v :=
  funext fun a' ↦ Subsingleton.elim a a' ▸ update_self ..

theorem surjective_eval {α : Sort u} {β : α → Sort v} [h : ∀ a, Nonempty (β a)] (a : α) :
    Surjective (eval a : (∀ a, β a) → β a) := fun b ↦
  ⟨@update _ _ (Classical.decEq α) (fun a ↦ (h a).some) a b,
   @update_self _ _ (Classical.decEq α) _ _ _⟩

theorem update_injective (f : ∀ a, β a) (a' : α) : Injective (update f a') := fun v v' h ↦ by
  have := congr_fun h a'
  rwa [update_self, update_self] at this

lemma forall_update_iff (f : ∀ a, β a) {a : α} {b : β a} (p : ∀ a, β a → Prop) :
    (∀ x, p x (update f a b x)) ↔ p a b ∧ ∀ x, x ≠ a → p x (f x) := by
  rw [← and_forall_ne a, update_self]
  simp +contextual

theorem exists_update_iff (f : ∀ a, β a) {a : α} {b : β a} (p : ∀ a, β a → Prop) :
    (∃ x, p x (update f a b x)) ↔ p a b ∨ ∃ x ≠ a, p x (f x) := by
  rw [← not_forall_not, forall_update_iff f fun a b ↦ ¬p a b]
  simp [-not_and, not_and_or]

theorem update_eq_iff {a : α} {b : β a} {f g : ∀ a, β a} :
    update f a b = g ↔ b = g a ∧ ∀ x ≠ a, f x = g x :=
  funext_iff.trans <| forall_update_iff _ fun x y ↦ y = g x

theorem eq_update_iff {a : α} {b : β a} {f g : ∀ a, β a} :
    g = update f a b ↔ g a = b ∧ ∀ x ≠ a, g x = f x :=
  funext_iff.trans <| forall_update_iff _ fun x y ↦ g x = y

@[simp] lemma update_eq_self_iff : update f a b = f ↔ b = f a := by simp [update_eq_iff]

@[simp] lemma eq_update_self_iff : f = update f a b ↔ f a = b := by simp [eq_update_iff]

lemma ne_update_self_iff : f ≠ update f a b ↔ f a ≠ b := eq_update_self_iff.not

lemma update_ne_self_iff : update f a b ≠ f ↔ b ≠ f a := update_eq_self_iff.not

@[simp]
theorem update_eq_self (a : α) (f : ∀ a, β a) : update f a (f a) = f :=
  update_eq_iff.2 ⟨rfl, fun _ _ ↦ rfl⟩

theorem update_comp_eq_of_forall_ne' {α'} (g : ∀ a, β a) {f : α' → α} {i : α} (a : β i)
    (h : ∀ x, f x ≠ i) : (fun j ↦ (update g i a) (f j)) = fun j ↦ g (f j) :=
  funext fun _ ↦ update_of_ne (h _) _ _

variable [DecidableEq α']

/-- Non-dependent version of `Function.update_comp_eq_of_forall_ne'` -/
theorem update_comp_eq_of_forall_ne {α β : Sort*} (g : α' → β) {f : α → α'} {i : α'} (a : β)
    (h : ∀ x, f x ≠ i) : update g i a ∘ f = g ∘ f :=
  update_comp_eq_of_forall_ne' g a h

theorem update_comp_eq_of_injective' (g : ∀ a, β a) {f : α' → α} (hf : Function.Injective f)
    (i : α') (a : β (f i)) : (fun j ↦ update g (f i) a (f j)) = update (fun i ↦ g (f i)) i a :=
  eq_update_iff.2 ⟨update_self .., fun _ hj ↦ update_of_ne (hf.ne hj) _ _⟩

theorem update_apply_of_injective
    (g : ∀ a, β a) {f : α' → α} (hf : Function.Injective f)
    (i : α') (a : β (f i)) (j : α') :
    update g (f i) a (f j) = update (fun i ↦ g (f i)) i a j :=
  congr_fun (update_comp_eq_of_injective' g hf i a) j

/-- Non-dependent version of `Function.update_comp_eq_of_injective'` -/
theorem update_comp_eq_of_injective {β : Sort*} (g : α' → β) {f : α → α'}
    (hf : Function.Injective f) (i : α) (a : β) :
    Function.update g (f i) a ∘ f = Function.update (g ∘ f) i a :=
  update_comp_eq_of_injective' g hf i a

/-- Recursors can be pushed inside `Function.update`.

The `ctor` argument should be a one-argument constructor like `Sum.inl`,
and `recursor` should be an inductive recursor partially applied in all but that constructor,
such as `(Sum.rec · g)`.

In future, we should build some automation to generate applications like `Option.rec_update` for all
inductive types. -/
lemma rec_update {ι κ : Sort*} {α : κ → Sort*} [DecidableEq ι] [DecidableEq κ]
    {ctor : ι → κ} (hctor : Function.Injective ctor)
    (recursor : ((i : ι) → α (ctor i)) → ((i : κ) → α i))
    (h : ∀ f i, recursor f (ctor i) = f i)
    (h2 : ∀ f₁ f₂ k, (∀ i, ctor i ≠ k) → recursor f₁ k = recursor f₂ k)
    (f : (i : ι) → α (ctor i)) (i : ι) (x : α (ctor i)) :
    recursor (update f i x) = update (recursor f) (ctor i) x := by
  ext k
  by_cases h : ∃ i, ctor i = k
  · obtain ⟨i', rfl⟩ := h
    obtain rfl | hi := eq_or_ne i' i
    · simp [h]
    · have hk := hctor.ne hi
      simp [h, hi, hk, Function.update_of_ne]
  · rw [not_exists] at h
    rw [h2 _ f _ h]
    rw [Function.update_of_ne (Ne.symm <| h i)]

@[simp]
lemma _root_.Option.rec_update {α : Type*} {β : Option α → Sort*} [DecidableEq α]
    (f : β none) (g : ∀ a, β (.some a)) (a : α) (x : β (.some a)) :
    Option.rec f (update g a x) = update (Option.rec f g) (.some a) x :=
  Function.rec_update (@Option.some.inj _) (Option.rec f) (fun _ _ => rfl) (fun
    | _, _, .some _, h => (h _ rfl).elim
    | _, _, .none, _ => rfl) _ _ _

theorem apply_update {ι : Sort*} [DecidableEq ι] {α β : ι → Sort*} (f : ∀ i, α i → β i)
    (g : ∀ i, α i) (i : ι) (v : α i) (j : ι) :
    f j (update g i v j) = update (fun k ↦ f k (g k)) i (f i v) j := by
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

theorem apply_update₂ {ι : Sort*} [DecidableEq ι] {α β γ : ι → Sort*} (f : ∀ i, α i → β i → γ i)
    (g : ∀ i, α i) (h : ∀ i, β i) (i : ι) (v : α i) (w : β i) (j : ι) :
    f j (update g i v j) (update h i w j) = update (fun k ↦ f k (g k) (h k)) i (f i v w) j := by
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

theorem pred_update (P : ∀ ⦃a⦄, β a → Prop) (f : ∀ a, β a) (a' : α) (v : β a') (a : α) :
    P (update f a' v a) ↔ a = a' ∧ P v ∨ a ≠ a' ∧ P (f a) := by
  rw [apply_update P, update_apply, ite_prop_iff_or]

theorem comp_update {α' : Sort*} {β : Sort*} (f : α' → β) (g : α → α') (i : α) (v : α') :
    f ∘ update g i v = update (f ∘ g) i (f v) :=
  funext <| apply_update _ _ _ _

theorem update_comm {α} [DecidableEq α] {β : α → Sort*} {a b : α} (h : a ≠ b) (v : β a) (w : β b)
    (f : ∀ a, β a) : update (update f a v) b w = update (update f b w) a v := by
  funext c
  simp only [update]
  by_cases h₁ : c = b <;> by_cases h₂ : c = a
  · rw [dif_pos h₁, dif_pos h₂]
    cases h (h₂.symm.trans h₁)
  · rw [dif_pos h₁, dif_pos h₁, dif_neg h₂]
  · rw [dif_neg h₁, dif_neg h₁]
  · rw [dif_neg h₁, dif_neg h₁]

@[simp]
theorem update_idem {α} [DecidableEq α] {β : α → Sort*} {a : α} (v w : β a) (f : ∀ a, β a) :
    update (update f a v) a w = update f a w := by
  funext b
  by_cases h : b = a <;> simp [update, h]

@[simp]
theorem _root_.Pi.map_update {ι : Sort*} [DecidableEq ι] {α β : ι → Sort*}
    {f : ∀ i, α i → β i}
    (g : ∀ i, α i) (i : ι) (a : α i) :
    Pi.map f (Function.update g i a) = Function.update (Pi.map f g) i (f i a) := by
  ext j
  obtain rfl | hij := eq_or_ne j i <;> simp [*]

@[simp]
theorem _root_.Pi.map_injective
    {ι : Sort*} {α β : ι → Sort*} [∀ i, Nonempty (α i)] {f : ∀ i, α i → β i} :
    Injective (Pi.map f) ↔ ∀ i, Injective (f i) where
  mp h i x y hxy := by
    classical
    have : Inhabited (∀ i, α i) := ⟨fun _ => Classical.choice inferInstance⟩
    replace h := @h (Function.update default i x) (Function.update default i y) ?_
    · simpa using congrFun h i
    rw [Pi.map_update, Pi.map_update, hxy]
  mpr := .piMap

end Update

noncomputable section Extend

variable {α β γ : Sort*} {f : α → β}

/-- Extension of a function `g : α → γ` along a function `f : α → β`.

For every `a : α`, `f a` is sent to `g a`. `f` might not be surjective, so we use an auxiliary
function `j : β → γ` by sending `b : β` not in the range of `f` to `j b`. If you do not care about
the behavior outside the range, `j` can be used as a junk value by setting it to be `0` or
`Classical.arbitrary` (assuming `γ` is nonempty).

This definition is mathematically meaningful only when `f a₁ = f a₂ → g a₁ = g a₂` (spelled
`g.FactorsThrough f`). In particular this holds if `f` is injective.

A typical use case is extending a function from a subtype to the entire type. If you wish to extend
`g : {b : β // p b} → γ` to a function `β → γ`, you should use `Function.extend Subtype.val g j`. -/
def extend (f : α → β) (g : α → γ) (j : β → γ) : β → γ := fun b ↦
  open scoped Classical in
  if h : ∃ a, f a = b then g (Classical.choose h) else j b

/-- g factors through f : `f a = f b → g a = g b` -/
def FactorsThrough (g : α → γ) (f : α → β) : Prop :=
  ∀ ⦃a b⦄, f a = f b → g a = g b

theorem extend_def (f : α → β) (g : α → γ) (e' : β → γ) (b : β) [Decidable (∃ a, f a = b)] :
    extend f g e' b = if h : ∃ a, f a = b then g (Classical.choose h) else e' b := by
  unfold extend
  congr

lemma Injective.factorsThrough (hf : Injective f) (g : α → γ) : g.FactorsThrough f :=
  fun _ _ h => congr_arg g (hf h)

lemma FactorsThrough.extend_apply {g : α → γ} (hf : g.FactorsThrough f) (e' : β → γ) (a : α) :
    extend f g e' (f a) = g a := by
  classical
  simp only [extend_def, dif_pos, exists_apply_eq_apply]
  exact hf (Classical.choose_spec (exists_apply_eq_apply f a))

@[simp]
theorem Injective.extend_apply (hf : Injective f) (g : α → γ) (e' : β → γ) (a : α) :
    extend f g e' (f a) = g a :=
  (hf.factorsThrough g).extend_apply e' a

@[simp]
theorem extend_apply' (g : α → γ) (e' : β → γ) (b : β) (hb : ¬∃ a, f a = b) :
    extend f g e' b = e' b := by
  classical
  simp [Function.extend_def, hb]

@[simp]
theorem extend_id (g : α → γ) (e' : α → γ) :
    extend id g e' = g :=
  funext <| injective_id.extend_apply g _

theorem Injective.extend_comp {α₁ α₂ α₃ : Sort*} {f₁₂ : α₁ → α₂} (h₁₂ : Function.Injective f₁₂)
    {f₂₃ : α₂ → α₃} (h₂₃ : Function.Injective f₂₃) (g : α₁ → γ) (e' : α₃ → γ) :
    extend (f₂₃ ∘ f₁₂) g e' = extend f₂₃ (extend f₁₂ g (e' ∘ f₂₃)) e' := by
  ext a
  by_cases h₃ : ∃ b, f₂₃ b = a
  · obtain ⟨b, rfl⟩ := h₃
    rw [Injective.extend_apply h₂₃]
    by_cases h₂ : ∃ c, f₁₂ c = b
    · obtain ⟨c, rfl⟩ := h₂
      rw [h₁₂.extend_apply]
      exact (h₂₃.comp h₁₂).extend_apply _ _ _
    · rw [extend_apply' _ _ _ h₂, extend_apply', comp_apply]
      exact fun h ↦ h₂ (Exists.casesOn h fun c hc ↦ Exists.intro c (h₂₃ hc))
  · rw [extend_apply' _ _ _ h₃, extend_apply']
    exact fun h ↦ h₃ (Exists.casesOn h fun c hc ↦ Exists.intro (f₁₂ c) (hc))

lemma factorsThrough_iff (g : α → γ) [Nonempty γ] : g.FactorsThrough f ↔ ∃ (e : β → γ), g = e ∘ f :=
  ⟨fun hf => ⟨extend f g (const β (Classical.arbitrary γ)),
      funext (fun x => by simp only [comp_apply, hf.extend_apply])⟩,
  fun h _ _ hf => by rw [Classical.choose_spec h, comp_apply, comp_apply, hf]⟩

lemma apply_extend {δ} {g : α → γ} (F : γ → δ) (f : α → β) (e' : β → γ) (b : β) :
    F (extend f g e' b) = extend f (F ∘ g) (F ∘ e') b :=
  open scoped Classical in apply_dite F _ _ _

theorem extend_injective (hf : Injective f) (e' : β → γ) : Injective fun g ↦ extend f g e' := by
  intro g₁ g₂ hg
  refine funext fun x ↦ ?_
  have H := congr_fun hg (f x)
  simp only [hf.extend_apply] at H
  exact H

lemma FactorsThrough.extend_comp {g : α → γ} (e' : β → γ) (hf : FactorsThrough g f) :
    extend f g e' ∘ f = g :=
  funext fun a => hf.extend_apply e' a

@[simp]
lemma extend_const (f : α → β) (c : γ) : extend f (fun _ ↦ c) (fun _ ↦ c) = fun _ ↦ c :=
  funext fun _ ↦ open scoped Classical in ite_id _

@[simp]
theorem extend_comp (hf : Injective f) (g : α → γ) (e' : β → γ) : extend f g e' ∘ f = g :=
  funext fun a ↦ hf.extend_apply g e' a

theorem Injective.surjective_comp_right' (hf : Injective f) (g₀ : β → γ) :
    Surjective fun g : β → γ ↦ g ∘ f :=
  fun g ↦ ⟨extend f g g₀, Function.extend_comp hf _ _⟩

theorem Injective.surjective_comp_right [Nonempty γ] (hf : Injective f) :
    Surjective fun g : β → γ ↦ g ∘ f :=
  hf.surjective_comp_right' fun _ ↦ Classical.choice ‹_›

theorem surjective_comp_right_iff_injective {γ : Type*} [Nontrivial γ] :
    Surjective (fun g : β → γ ↦ g ∘ f) ↔ Injective f := by
  classical
  refine ⟨not_imp_not.mp fun not_inj surj ↦ not_subsingleton γ ⟨fun c c' ↦ ?_⟩,
    (·.surjective_comp_right)⟩
  simp only [Injective, not_forall] at not_inj
  have ⟨a₁, a₂, eq, ne⟩ := not_inj
  have ⟨f, hf⟩ := surj (if · = a₂ then c else c')
  have h₁ := congr_fun hf a₁
  have h₂ := congr_fun hf a₂
  simp only [comp_apply, if_neg ne, reduceIte] at h₁ h₂
  rw [← h₁, eq, h₂]

theorem Bijective.comp_right (hf : Bijective f) : Bijective fun g : β → γ ↦ g ∘ f :=
  ⟨hf.surjective.injective_comp_right, fun g ↦
    ⟨g ∘ surjInv hf.surjective,
     by simp only [comp_assoc g _ f, (leftInverse_surjInv hf).comp_eq_id, comp_id]⟩⟩

end Extend

namespace FactorsThrough

protected theorem rfl {α β : Sort*} {f : α → β} : FactorsThrough f f := fun _ _ ↦ id

theorem comp_left {α β γ δ : Sort*} {f : α → β} {g : α → γ} (h : FactorsThrough g f) (g' : γ → δ) :
    FactorsThrough (g' ∘ g) f := fun _x _y hxy ↦
  congr_arg g' (h hxy)

theorem comp_right {α β γ δ : Sort*} {f : α → β} {g : α → γ} (h : FactorsThrough g f) (g' : δ → α) :
    FactorsThrough (g ∘ g') (f ∘ g') := fun _x _y hxy ↦
  h hxy

end FactorsThrough

theorem uncurry_def {α β γ} (f : α → β → γ) : uncurry f = fun p ↦ f p.1 p.2 :=
  rfl

section Bicomp

variable {α β γ δ ε : Type*}

/-- Compose a binary function `f` with a pair of unary functions `g` and `h`.
If both arguments of `f` have the same type and `g = h`, then `bicompl f g g = f on g`. -/
def bicompl (f : γ → δ → ε) (g : α → γ) (h : β → δ) (a b) :=
  f (g a) (h b)

/-- Compose a unary function `f` with a binary function `g`. -/
def bicompr (f : γ → δ) (g : α → β → γ) (a b) :=
  f (g a b)

-- Suggested local notation:
local notation f " ∘₂ " g => bicompr f g

theorem uncurry_bicompr (f : α → β → γ) (g : γ → δ) : uncurry (g ∘₂ f) = g ∘ uncurry f :=
  rfl

theorem uncurry_bicompl (f : γ → δ → ε) (g : α → γ) (h : β → δ) :
    uncurry (bicompl f g h) = uncurry f ∘ Prod.map g h :=
  rfl

end Bicomp

section Uncurry

variable {α β γ δ : Type*}

/-- Records a way to turn an element of `α` into a function from `β` to `γ`. The most generic use
is to recursively uncurry. For instance `f : α → β → γ → δ` will be turned into
`↿f : α × β × γ → δ`. One can also add instances for bundled maps. -/
class HasUncurry (α : Type*) (β : outParam Type*) (γ : outParam Type*) where
  /-- Uncurrying operator. The most generic use is to recursively uncurry. For instance
  `f : α → β → γ → δ` will be turned into `↿f : α × β × γ → δ`. One can also add instances
  for bundled maps. -/
  uncurry : α → β → γ

@[inherit_doc] prefix:max "↿" => HasUncurry.uncurry

instance hasUncurryBase : HasUncurry (α → β) α β :=
  ⟨id⟩

instance hasUncurryInduction [HasUncurry β γ δ] : HasUncurry (α → β) (α × γ) δ :=
  ⟨fun f p ↦ ↿(f p.1) p.2⟩

end Uncurry

/-- A function is involutive, if `f ∘ f = id`. -/
def Involutive {α} (f : α → α) : Prop :=
  ∀ x, f (f x) = x

theorem _root_.Bool.involutive_not : Involutive not :=
  Bool.not_not

namespace Involutive

variable {α : Sort u} {f : α → α} (h : Involutive f)

include h

@[simp]
theorem comp_self : f ∘ f = id :=
  funext h

protected theorem leftInverse : LeftInverse f f := h

theorem leftInverse_iff {g : α → α} :
    g.LeftInverse f ↔ g = f :=
  ⟨fun hg ↦ funext fun x ↦ by rw [← h x, hg, h], fun he ↦ he ▸ h.leftInverse⟩

protected theorem rightInverse : RightInverse f f := h

protected theorem injective : Injective f := h.leftInverse.injective

protected theorem surjective : Surjective f := fun x ↦ ⟨f x, h x⟩

protected theorem bijective : Bijective f := ⟨h.injective, h.surjective⟩

/-- Involuting an `ite` of an involuted value `x : α` negates the `Prop` condition in the `ite`. -/
protected theorem ite_not (P : Prop) [Decidable P] (x : α) :
    f (ite P x (f x)) = ite (¬P) x (f x) := by rw [apply_ite f, h, ite_not]

/-- An involution commutes across an equality. Compare to `Function.Injective.eq_iff`. -/
protected theorem eq_iff {x y : α} : f x = y ↔ x = f y :=
  h.injective.eq_iff' (h y)

end Involutive

lemma not_involutive : Involutive Not := fun _ ↦ propext not_not
lemma not_injective : Injective Not := not_involutive.injective
lemma not_surjective : Surjective Not := not_involutive.surjective
lemma not_bijective : Bijective Not := not_involutive.bijective

@[simp]
lemma symmetric_apply_eq_iff {α : Sort*} {f : α → α} : Symmetric (f · = ·) ↔ Involutive f := by
  simp [Symmetric, Involutive]

/-- The property of a binary function `f : α → β → γ` being injective.
Mathematically this should be thought of as the corresponding function `α × β → γ` being injective.
-/
def Injective2 {α β γ : Sort*} (f : α → β → γ) : Prop :=
  ∀ ⦃a₁ a₂ b₁ b₂⦄, f a₁ b₁ = f a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂

namespace Injective2

variable {α β γ : Sort*} {f : α → β → γ}

/-- A binary injective function is injective when only the left argument varies. -/
protected theorem left (hf : Injective2 f) (b : β) : Function.Injective fun a ↦ f a b :=
  fun _ _ h ↦ (hf h).left

/-- A binary injective function is injective when only the right argument varies. -/
protected theorem right (hf : Injective2 f) (a : α) : Function.Injective (f a) :=
  fun _ _ h ↦ (hf h).right

protected theorem uncurry {α β γ : Type*} {f : α → β → γ} (hf : Injective2 f) :
    Function.Injective (uncurry f) :=
  fun ⟨_, _⟩ ⟨_, _⟩ h ↦ (hf h).elim (congr_arg₂ _)

/-- As a map from the left argument to a unary function, `f` is injective. -/
theorem left' (hf : Injective2 f) [Nonempty β] : Function.Injective f := fun _ _ h ↦
  let ⟨b⟩ := ‹Nonempty β›
  hf.left b <| (congr_fun h b :)

/-- As a map from the right argument to a unary function, `f` is injective. -/
theorem right' (hf : Injective2 f) [Nonempty α] : Function.Injective fun b a ↦ f a b :=
  fun _ _ h ↦
    let ⟨a⟩ := ‹Nonempty α›
    hf.right a <| (congr_fun h a :)

theorem eq_iff (hf : Injective2 f) {a₁ a₂ b₁ b₂} : f a₁ b₁ = f a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
  ⟨fun h ↦ hf h, fun ⟨h1, h2⟩ ↦ congr_arg₂ f h1 h2⟩

end Injective2

section Sometimes

/-- `sometimes f` evaluates to some value of `f`, if it exists. This function is especially
interesting in the case where `α` is a proposition, in which case `f` is necessarily a
constant function, so that `sometimes f = f a` for all `a`. -/
noncomputable def sometimes {α β} [Nonempty β] (f : α → β) : β :=
  open scoped Classical in
  if h : Nonempty α then f (Classical.choice h) else Classical.choice ‹_›

theorem sometimes_eq {p : Prop} {α} [Nonempty α] (f : p → α) (a : p) : sometimes f = f a :=
  dif_pos ⟨a⟩

theorem sometimes_spec {p : Prop} {α} [Nonempty α] (P : α → Prop) (f : p → α) (a : p)
    (h : P (f a)) : P (sometimes f) := by
  rwa [sometimes_eq]

end Sometimes

end Function

variable {α β : Sort*}

/-- A relation `r : α → β → Prop` is "function-like"
(for each `a` there exists a unique `b` such that `r a b`)
if and only if it is `(f · = ·)` for some function `f`. -/
lemma forall_existsUnique_iff {r : α → β → Prop} :
    (∀ a, ∃! b, r a b) ↔ ∃ f : α → β, ∀ {a b}, r a b ↔ f a = b := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · refine ⟨fun a ↦ (h a).choose, fun hr ↦ ?_, fun h' ↦ h' ▸ ?_⟩
    exacts [((h _).choose_spec.2 _ hr).symm, (h _).choose_spec.1]
  · rintro ⟨f, hf⟩
    simp [hf]

/-- A relation `r : α → β → Prop` is "function-like"
(for each `a` there exists a unique `b` such that `r a b`)
if and only if it is `(f · = ·)` for some function `f`. -/
lemma forall_existsUnique_iff' {r : α → β → Prop} :
    (∀ a, ∃! b, r a b) ↔ ∃ f : α → β, r = (f · = ·) := by
  simp [forall_existsUnique_iff, funext_iff]

/-- A symmetric relation `r : α → α → Prop` is "function-like"
(for each `a` there exists a unique `b` such that `r a b`)
if and only if it is `(f · = ·)` for some involutive function `f`. -/
protected lemma Symmetric.forall_existsUnique_iff' {r : α → α → Prop} (hr : Symmetric r) :
    (∀ a, ∃! b, r a b) ↔ ∃ f : α → α, Involutive f ∧ r = (f · = ·) := by
  refine ⟨fun h ↦ ?_, fun ⟨f, _, hf⟩ ↦ forall_existsUnique_iff'.2 ⟨f, hf⟩⟩
  rcases forall_existsUnique_iff'.1 h with ⟨f, rfl : r = _⟩
  exact ⟨f, symmetric_apply_eq_iff.1 hr, rfl⟩

/-- A symmetric relation `r : α → α → Prop` is "function-like"
(for each `a` there exists a unique `b` such that `r a b`)
if and only if it is `(f · = ·)` for some involutive function `f`. -/
protected lemma Symmetric.forall_existsUnique_iff {r : α → α → Prop} (hr : Symmetric r) :
    (∀ a, ∃! b, r a b) ↔ ∃ f : α → α, Involutive f ∧ ∀ {a b}, r a b ↔ f a = b := by
  simp [hr.forall_existsUnique_iff', funext_iff]

/-- `s.piecewise f g` is the function equal to `f` on the set `s`, and to `g` on its complement. -/
def Set.piecewise {α : Type u} {β : α → Sort v} (s : Set α) (f g : ∀ i, β i)
    [∀ j, Decidable (j ∈ s)] : ∀ i, β i :=
  fun i ↦ if i ∈ s then f i else g i


/-! ### Bijectivity of `Eq.rec`, `Eq.mp`, `Eq.mpr`, and `cast` -/

theorem eq_rec_on_bijective {C : α → Sort*} :
    ∀ {a a' : α} (h : a = a'), Function.Bijective (@Eq.ndrec _ _ C · _ h)
  | _, _, rfl => ⟨fun _ _ ↦ id, fun x ↦ ⟨x, rfl⟩⟩

theorem eq_mp_bijective {α β : Sort _} (h : α = β) : Function.Bijective (Eq.mp h) := by
  -- TODO: mathlib3 uses `eq_rec_on_bijective`, difference in elaboration here
  -- due to `@[macro_inline]` possibly?
  cases h
  exact ⟨fun _ _ ↦ id, fun x ↦ ⟨x, rfl⟩⟩

theorem eq_mpr_bijective {α β : Sort _} (h : α = β) : Function.Bijective (Eq.mpr h) := by
  cases h
  exact ⟨fun _ _ ↦ id, fun x ↦ ⟨x, rfl⟩⟩

theorem cast_bijective {α β : Sort _} (h : α = β) : Function.Bijective (cast h) := by
  cases h
  exact ⟨fun _ _ ↦ id, fun x ↦ ⟨x, rfl⟩⟩

/-! Note these lemmas apply to `Type*` not `Sort*`, as the latter interferes with `simp`, and
is trivial anyway. -/

@[simp]
theorem eq_rec_inj {a a' : α} (h : a = a') {C : α → Type*} (x y : C a) :
    (Eq.ndrec x h : C a') = Eq.ndrec y h ↔ x = y :=
  (eq_rec_on_bijective h).injective.eq_iff

@[simp]
theorem cast_inj {α β : Type u} (h : α = β) {x y : α} : cast h x = cast h y ↔ x = y :=
  (cast_bijective h).injective.eq_iff

theorem Function.LeftInverse.eq_rec_eq {γ : β → Sort v} {f : α → β} {g : β → α}
    (h : Function.LeftInverse g f) (C : ∀ a : α, γ (f a)) (a : α) :
    -- TODO: mathlib3 uses `(congr_arg f (h a)).rec (C (g (f a)))` for LHS
    @Eq.rec β (f (g (f a))) (fun x _ ↦ γ x) (C (g (f a))) (f a) (congr_arg f (h a)) = C a :=
  eq_of_heq <| (eqRec_heq _ _).trans <| by rw [h]

theorem Function.LeftInverse.eq_rec_on_eq {γ : β → Sort v} {f : α → β} {g : β → α}
    (h : Function.LeftInverse g f) (C : ∀ a : α, γ (f a)) (a : α) :
    -- TODO: mathlib3 uses `(congr_arg f (h a)).recOn (C (g (f a)))` for LHS
    @Eq.recOn β (f (g (f a))) (fun x _ ↦ γ x) (f a) (congr_arg f (h a)) (C (g (f a))) = C a :=
  h.eq_rec_eq _ _

theorem Function.LeftInverse.cast_eq {γ : β → Sort v} {f : α → β} {g : β → α}
    (h : Function.LeftInverse g f) (C : ∀ a : α, γ (f a)) (a : α) :
    cast (congr_arg (fun a ↦ γ (f a)) (h a)) (C (g (f a))) = C a := by
  rw [cast_eq_iff_heq, h]

/-- A set of functions "separates points"
if for each pair of distinct points there is a function taking different values on them. -/
def Set.SeparatesPoints {α β : Type*} (A : Set (α → β)) : Prop :=
  ∀ ⦃x y : α⦄, x ≠ y → ∃ f ∈ A, (f x : β) ≠ f y

theorem InvImage.equivalence {α : Sort u} {β : Sort v} (r : β → β → Prop) (f : α → β)
    (h : Equivalence r) : Equivalence (InvImage r f) :=
  ⟨fun _ ↦ h.1 _, h.symm, h.trans⟩

instance {α β : Type*} {r : α → β → Prop} {x : α × β} [Decidable (r x.1 x.2)] :
    Decidable (uncurry r x) :=
  ‹Decidable _›

instance {α β : Type*} {r : α × β → Prop} {a : α} {b : β} [Decidable (r (a, b))] :
    Decidable (curry r a b) :=
  ‹Decidable _›
