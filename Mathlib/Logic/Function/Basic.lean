/-
Copyright (c) 2016 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module logic.function.basic
! leanprover-community/mathlib commit d6aae1bcbd04b8de2022b9b83a5b5b10e10c777d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Logic.Nonempty
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Set
import Mathlib.Util.WhatsNew

/-!
# Miscellaneous function constructions and lemmas
-/


universe u v w

namespace Function

section

variable {α β γ : Sort _} {f : α → β}

/-- Evaluate a function at an argument. Useful if you want to talk about the partially applied
  `Function.eval x : (∀ x, β x) → β x`. -/
@[reducible, simp] def eval {β : α → Sort _} (x : α) (f : ∀ x, β x) : β x := f x

theorem eval_apply {β : α → Sort _} (x : α) (f : ∀ x, β x) : eval x f = f x :=
  rfl

theorem const_def {y : β} : (fun _ : α ↦ y) = const α y :=
  rfl

@[simp]
theorem const_comp {f : α → β} {c : γ} : const β c ∘ f = const α c :=
  rfl

@[simp]
theorem comp_const {f : β → γ} {b : β} : f ∘ const α b = const α (f b) :=
  rfl

theorem const_injective [Nonempty α] : Injective (const α : β → α → β) := fun y₁ y₂ h ↦
  let ⟨x⟩ := ‹Nonempty α›
  congr_fun h x

@[simp]
theorem const_inj [Nonempty α] {y₁ y₂ : β} : const α y₁ = const α y₂ ↔ y₁ = y₂ :=
  ⟨fun h ↦ const_injective h, fun h ↦ h ▸ rfl⟩

theorem id_def : @id α = fun x ↦ x :=
  rfl

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

theorem funext_iff {β : α → Sort _} {f₁ f₂ : ∀ x : α, β x} : f₁ = f₂ ↔ ∀ a, f₁ a = f₂ a :=
  Iff.intro (fun h _ ↦ h ▸ rfl) funext

theorem ne_iff {β : α → Sort _} {f₁ f₂ : ∀ a, β a} : f₁ ≠ f₂ ↔ ∃ a, f₁ a ≠ f₂ a :=
  funext_iff.not.trans not_forall

protected theorem Bijective.injective {f : α → β} (hf : Bijective f) : Injective f := hf.1
#align function.bijective.injective Function.Bijective.injective
protected theorem Bijective.surjective {f : α → β} (hf : Bijective f) : Surjective f := hf.2
#align function.bijective.surjective Function.Bijective.surjective

theorem Injective.eq_iff (I : Injective f) {a b : α} : f a = f b ↔ a = b :=
  ⟨@I _ _, congr_arg f⟩

theorem Injective.beq_eq [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (I : Injective f) {a b : α} : (f a == f b) = (a == b) := by
  by_cases h : a == b <;> simp [h] <;> simpa [I.eq_iff] using h

theorem Injective.eq_iff' (I : Injective f) {a b : α} {c : β} (h : f b = c) : f a = c ↔ a = b :=
  h ▸ I.eq_iff

theorem Injective.ne (hf : Injective f) {a₁ a₂ : α} : a₁ ≠ a₂ → f a₁ ≠ f a₂ :=
  mt fun h ↦ hf h
#align function.injective.ne Function.Injective.ne

theorem Injective.ne_iff (hf : Injective f) {x y : α} : f x ≠ f y ↔ x ≠ y :=
  ⟨mt <| congr_arg f, hf.ne⟩

theorem Injective.ne_iff' (hf : Injective f) {x y : α} {z : β} (h : f y = z) : f x ≠ z ↔ x ≠ y :=
  h ▸ hf.ne_iff

/-- If the co-domain `β` of an injective function `f : α → β` has decidable equality, then
the domain `α` also has decidable equality. -/
protected def Injective.decidableEq [DecidableEq β] (I : Injective f) : DecidableEq α :=
  fun _ _ ↦ decidable_of_iff _ I.eq_iff

theorem Injective.of_comp {g : γ → α} (I : Injective (f ∘ g)) : Injective g := fun x y h ↦
  I <| show f (g x) = f (g y) from congr_arg f h

theorem Injective.of_comp_iff {f : α → β} (hf : Injective f) (g : γ → α) :
    Injective (f ∘ g) ↔ Injective g :=
  ⟨Injective.of_comp, hf.comp⟩

theorem Injective.of_comp_iff' (f : α → β) {g : γ → α} (hg : Bijective g) :
    Injective (f ∘ g) ↔ Injective f :=
⟨ λ h x y => let ⟨_, hx⟩ := hg.surjective x
             let ⟨_, hy⟩ := hg.surjective y
             hx ▸ hy ▸ λ hf => h hf ▸ rfl,
  λ h => h.comp hg.injective⟩

/-- Composition by an injective function on the left is itself injective. -/
theorem Injective.comp_left {g : β → γ} (hg : Function.Injective g) :
    Function.Injective ((· ∘ ·) g : (α → β) → α → γ) :=
  fun _ _ hgf ↦ funext fun i ↦ hg <| (congr_fun hgf i : _)

theorem injective_of_subsingleton [Subsingleton α] (f : α → β) : Injective f :=
  fun _ _ _ ↦ Subsingleton.elim _ _

lemma Injective.dite (p : α → Prop) [DecidablePred p]
  {f : {a : α // p a} → β} {f' : {a : α // ¬ p a} → β}
  (hf : Injective f) (hf' : Injective f')
  (im_disj : ∀ {x x' : α} {hx : p x} {hx' : ¬ p x'}, f ⟨x, hx⟩ ≠ f' ⟨x', hx'⟩) :
  Function.Injective (λ x => if h : p x then f ⟨x, h⟩ else f' ⟨x, h⟩) :=
by intros x₁ x₂ h
   dsimp only at h
   by_cases h₁ : p x₁ <;> by_cases h₂ : p x₂
   · rw [dif_pos h₁, dif_pos h₂] at h; injection (hf h)
   · rw [dif_pos h₁, dif_neg h₂] at h; exact (im_disj h).elim
   · rw [dif_neg h₁, dif_pos h₂] at h; exact (im_disj h.symm).elim
   · rw [dif_neg h₁, dif_neg h₂] at h; injection (hf' h)

theorem Surjective.of_comp {g : γ → α} (S : Surjective (f ∘ g)) : Surjective f := fun y ↦
  let ⟨x, h⟩ := S y
  ⟨g x, h⟩

theorem Surjective.of_comp_iff (f : α → β) {g : γ → α} (hg : Surjective g) :
    Surjective (f ∘ g) ↔ Surjective f :=
  ⟨Surjective.of_comp, fun h ↦ h.comp hg⟩

theorem Surjective.of_comp_iff' (hf : Bijective f) (g : γ → α) :
    Surjective (f ∘ g) ↔ Surjective g :=
  ⟨fun h x ↦
    let ⟨x', hx'⟩ := h (f x)
    ⟨x', hf.injective hx'⟩,
    hf.surjective.comp⟩

instance decidableEqPfun (p : Prop) [Decidable p] (α : p → Type _) [∀ hp, DecidableEq (α hp)] :
    DecidableEq (∀ hp, α hp)
  | f, g => decidable_of_iff (∀ hp, f hp = g hp) funext_iff.symm

protected theorem Surjective.forall (hf : Surjective f) {p : β → Prop} :
    (∀ y, p y) ↔ ∀ x, p (f x) :=
  ⟨fun h x ↦ h (f x), fun h y ↦
    let ⟨x, hx⟩ := hf y
    hx ▸ h x⟩

protected theorem Surjective.forall₂ (hf : Surjective f) {p : β → β → Prop} :
    (∀ y₁ y₂, p y₁ y₂) ↔ ∀ x₁ x₂, p (f x₁) (f x₂) :=
  hf.forall.trans $ forall_congr' fun _ ↦ hf.forall

protected theorem Surjective.forall₃ (hf : Surjective f) {p : β → β → β → Prop} :
    (∀ y₁ y₂ y₃, p y₁ y₂ y₃) ↔ ∀ x₁ x₂ x₃, p (f x₁) (f x₂) (f x₃) :=
  hf.forall.trans $ forall_congr' fun _ ↦ hf.forall₂

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

protected theorem Surjective.right_cancellable (hf : Surjective f) {g₁ g₂ : β → γ} :
    g₁ ∘ f = g₂ ∘ f ↔ g₁ = g₂ :=
  hf.injective_comp_right.eq_iff

theorem surjective_of_right_cancellable_Prop (h : ∀ g₁ g₂ : β → Prop, g₁ ∘ f = g₂ ∘ f → g₁ = g₂) :
    Surjective f := by
  specialize h (fun y ↦ ∃ x, f x = y) (fun _ ↦ True) (funext fun x ↦ eq_true ⟨_, rfl⟩)
  intro y; rw [congr_fun h y]; trivial

theorem bijective_iff_existsUnique (f : α → β) : Bijective f ↔ ∀ b : β, ∃! a : α, f a = b :=
  ⟨fun hf b ↦
      let ⟨a, ha⟩ := hf.surjective b
      ⟨a, ha, fun _ ha' ↦ hf.injective (ha'.trans ha.symm)⟩,
    fun he ↦ ⟨fun {_a a'} h ↦ (he (f a')).unique h rfl, fun b ↦ (he b).exists⟩⟩
#align function.bijective_iff_exists_unique Function.bijective_iff_existsUnique

/-- Shorthand for using projection notation with `Function.bijective_iff_existsUnique`. -/
protected theorem Bijective.existsUnique {f : α → β} (hf : Bijective f) (b : β) :
    ∃! a : α, f a = b :=
  (bijective_iff_existsUnique f).mp hf b
#align function.bijective.exists_unique Function.Bijective.existsUnique

theorem Bijective.existsUnique_iff {f : α → β} (hf : Bijective f) {p : β → Prop} :
    (∃! y, p y) ↔ ∃! x, p (f x) :=
  ⟨fun ⟨y, hpy, hy⟩ ↦
    let ⟨x, hx⟩ := hf.surjective y
    ⟨x, by simpa [hx], fun z (hz : p (f z)) ↦ hf.injective <| hx.symm ▸ hy _ hz⟩,
    fun ⟨x, hpx, hx⟩ ↦
    ⟨f x, hpx, fun y hy ↦
      let ⟨z, hz⟩ := hf.surjective y
      hz ▸ congr_arg f (hx _ (by simpa [hz]))⟩⟩
#align function.bijective.exists_unique_iff Function.Bijective.existsUnique_iff

theorem Bijective.of_comp_iff (f : α → β) {g : γ → α} (hg : Bijective g) :
    Bijective (f ∘ g) ↔ Bijective f :=
  and_congr (Injective.of_comp_iff' _ hg) (Surjective.of_comp_iff _ hg.surjective)

theorem Bijective.of_comp_iff' {f : α → β} (hf : Bijective f) (g : γ → α) :
    Function.Bijective (f ∘ g) ↔ Function.Bijective g :=
  and_congr (Injective.of_comp_iff hf.injective _) (Surjective.of_comp_iff' hf _)

/-- **Cantor's diagonal argument** implies that there are no surjective functions from `α`
to `Set α`. -/
theorem cantor_surjective {α} (f : α → Set α) : ¬Surjective f
  | h => let ⟨D, e⟩ := h (λ a => ¬ f a a)
        (@iff_not_self (f D D)) $ iff_of_eq (congr_fun e D)

/-- **Cantor's diagonal argument** implies that there are no injective functions from `Set α`
to `α`. -/
theorem cantor_injective {α : Type _} (f : Set α → α) : ¬Injective f
| i => cantor_surjective (λ a b => ∀ U, a = f U → U b) $
       RightInverse.surjective
         (λ U => funext $ λ _a => propext ⟨λ h => h U rfl, λ h' _U e => i e ▸ h'⟩)

/-- There is no surjection from `α : Type u` into `Type u`. This theorem
  demonstrates why `Type : Type` would be inconsistent in Lean. -/
theorem not_surjective_Type {α : Type u} (f : α → Type max u v) : ¬Surjective f := by
  intro hf
  let T : Type max u v := Sigma f
  cases' hf (Set T) with U hU
  let g : Set T → T := fun s ↦ ⟨U, cast hU.symm s⟩
  have hg : Injective g := by
    intro s t h
    suffices cast hU (g s).2 = cast hU (g t).2 by
      simp only [cast_cast, cast_eq] at this
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
#align function.is_partial_inv_left Function.isPartialInv_left

theorem injective_of_isPartialInv {α β} {f : α → β} {g} (H : IsPartialInv f g) :
    Injective f := fun _ _ h ↦
  Option.some.inj <| ((H _ _).2 h).symm.trans ((H _ _).2 rfl)
#align function.injective_of_partial_inv Function.injective_of_isPartialInv

theorem injective_of_isPartialInv_right {α β} {f : α → β} {g} (H : IsPartialInv f g) (x y b)
    (h₁ : b ∈ g x) (h₂ : b ∈ g y) : x = y :=
  ((H _ _).1 h₁).symm.trans ((H _ _).1 h₂)
#align function.injective_of_partial_inv_right Function.injective_of_isPartialInv_right

theorem LeftInverse.comp_eq_id {f : α → β} {g : β → α} (h : LeftInverse f g) : f ∘ g = id :=
  funext h

theorem leftInverse_iff_comp {f : α → β} {g : β → α} : LeftInverse f g ↔ f ∘ g = id :=
  ⟨LeftInverse.comp_eq_id, congr_fun⟩
#align function.left_inverse_iff_comp Function.leftInverse_iff_comp

theorem RightInverse.comp_eq_id {f : α → β} {g : β → α} (h : RightInverse f g) : g ∘ f = id :=
  funext h

theorem rightInverse_iff_comp {f : α → β} {g : β → α} : RightInverse f g ↔ g ∘ f = id :=
  ⟨RightInverse.comp_eq_id, congr_fun⟩
#align function.right_inverse_iff_comp Function.rightInverse_iff_comp

theorem LeftInverse.comp {f : α → β} {g : β → α} {h : β → γ} {i : γ → β} (hf : LeftInverse f g)
    (hh : LeftInverse h i) : LeftInverse (h ∘ f) (g ∘ i) :=
  fun a ↦ show h (f (g (i a))) = a by rw [hf (i a), hh a]

theorem RightInverse.comp {f : α → β} {g : β → α} {h : β → γ} {i : γ → β} (hf : RightInverse f g)
    (hh : RightInverse h i) : RightInverse (h ∘ f) (g ∘ i) :=
  LeftInverse.comp hh hf

theorem LeftInverse.rightInverse {f : α → β} {g : β → α} (h : LeftInverse g f) : RightInverse f g :=
  h

#align function.left_inverse.right_inverse Function.LeftInverse.rightInverse

theorem RightInverse.leftInverse {f : α → β} {g : β → α} (h : RightInverse g f) : LeftInverse f g :=
  h

#align function.right_inverse.left_inverse Function.RightInverse.leftInverse

theorem LeftInverse.surjective {f : α → β} {g : β → α} (h : LeftInverse f g) : Surjective f :=
  h.rightInverse.surjective

theorem RightInverse.injective {f : α → β} {g : β → α} (h : RightInverse f g) : Injective f :=
  h.leftInverse.injective

theorem LeftInverse.rightInverse_of_injective {f : α → β} {g : β → α} (h : LeftInverse f g)
    (hf : Injective f) : RightInverse f g :=
  fun x ↦ hf <| h (f x)
#align function.left_inverse.right_inverse_of_injective Function.LeftInverse.rightInverse_of_injective

theorem LeftInverse.rightInverse_of_surjective {f : α → β} {g : β → α} (h : LeftInverse f g)
    (hg : Surjective g) : RightInverse f g :=
  fun x ↦ let ⟨y, hy⟩ := hg x; hy ▸ congr_arg g (h y)
#align function.left_inverse.right_inverse_of_surjective Function.LeftInverse.rightInverse_of_surjective

theorem RightInverse.leftInverse_of_surjective {f : α → β} {g : β → α} :
    RightInverse f g → Surjective f → LeftInverse f g :=
  LeftInverse.rightInverse_of_surjective
#align function.right_inverse.left_inverse_of_surjective Function.RightInverse.leftInverse_of_surjective

theorem RightInverse.leftInverse_of_injective {f : α → β} {g : β → α} :
    RightInverse f g → Injective g → LeftInverse f g :=
  LeftInverse.rightInverse_of_injective
#align function.right_inverse.left_inverse_of_injective Function.RightInverse.leftInverse_of_injective

theorem LeftInverse.eq_rightInverse {f : α → β} {g₁ g₂ : β → α} (h₁ : LeftInverse g₁ f)
    (h₂ : RightInverse g₂ f) : g₁ = g₂ :=
  calc
    g₁ = g₁ ∘ f ∘ g₂ := by rw [h₂.comp_eq_id, comp.right_id]
     _ = g₂ := by rw [← comp.assoc, h₁.comp_eq_id, comp.left_id]
#align function.left_inverse.eq_right_inverse Function.LeftInverse.eq_rightInverse

attribute [local instance] Classical.propDecidable

/-- We can use choice to construct explicitly a partial inverse for
  a given injective function `f`. -/
noncomputable def partialInv {α β} (f : α → β) (b : β) : Option α :=
  if h : ∃ a, f a = b then some (Classical.choose h) else none

theorem partialInv_of_injective {α β} {f : α → β} (I : Injective f) : IsPartialInv f (partialInv f)
| a, b =>
⟨λ h => have hpi : partialInv f b = if h : ∃ a, f a = b then some (Classical.choose h) else none :=
          rfl
        if h' : ∃ a, f a = b
        then by rw [hpi, dif_pos h'] at h
                injection h with h
                subst h
                apply Classical.choose_spec h'
        else by rw [hpi, dif_neg h'] at h; contradiction,
 λ e => e ▸ have h : ∃ a', f a' = f a := ⟨_, rfl⟩
            (dif_pos h).trans (congr_arg _ (I $ Classical.choose_spec h))⟩
#align function.partial_inv_of_injective Function.partialInv_of_injective

theorem partialInv_left {α β} {f : α → β} (I : Injective f) : ∀ x, partialInv f (f x) = some x :=
  isPartialInv_left (partialInv_of_injective I)
#align function.partial_inv_left Function.partialInv_left

end

section InvFun

variable {α β : Sort _} [Nonempty α] {f : α → β} {a : α} {b : β}

attribute [local instance] Classical.propDecidable

/-- The inverse of a function (which is a left inverse if `f` is injective
  and a right inverse if `f` is surjective). -/
-- Explicit Sort so that `α` isn't inferred to be Prop via `exists_prop_decidable`
noncomputable def invFun {α : Sort u} {β} [Nonempty α] (f : α → β) : β → α :=
  fun y ↦ if h : (∃ x, f x = y) then h.choose else Classical.arbitrary α

theorem invFun_eq (h : ∃ a, f a = b) : f (invFun f b) = b :=
  by simp only [invFun, dif_pos h, h.choose_spec]
#align function.inv_fun_eq Function.invFun_eq

theorem invFun_neg (h : ¬∃ a, f a = b) : invFun f b = Classical.choice ‹_› :=
  dif_neg h
#align function.inv_fun_neg Function.invFun_neg

theorem invFun_eq_of_injective_of_rightInverse {g : β → α} (hf : Injective f)
    (hg : RightInverse g f) : invFun f = g :=
  funext fun b ↦
    hf
      (by
        rw [hg b]
        exact invFun_eq ⟨g b, hg b⟩)
#align function.inv_fun_eq_of_injective_of_right_inverse Function.invFun_eq_of_injective_of_rightInverse

theorem rightInverse_invFun (hf : Surjective f) : RightInverse (invFun f) f :=
  fun b ↦ invFun_eq <| hf b
#align function.right_inverse_inv_fun Function.rightInverse_invFun

theorem leftInverse_invFun (hf : Injective f) : LeftInverse (invFun f) f :=
  fun b ↦ hf <| invFun_eq ⟨b, rfl⟩
#align function.left_inverse_inv_fun Function.leftInverse_invFun

theorem invFun_surjective (hf : Injective f) : Surjective (invFun f) :=
  (leftInverse_invFun hf).surjective
#align function.inv_fun_surjective Function.invFun_surjective

theorem invFun_comp (hf : Injective f) : invFun f ∘ f = id :=
  funext <| leftInverse_invFun hf
#align function.inv_fun_comp Function.invFun_comp

theorem Injective.hasLeftInverse (hf : Injective f) : HasLeftInverse f :=
  ⟨invFun f, leftInverse_invFun hf⟩
#align function.injective.has_left_inverse Function.Injective.hasLeftInverse

theorem injective_iff_hasLeftInverse : Injective f ↔ HasLeftInverse f :=
  ⟨Injective.hasLeftInverse, HasLeftInverse.injective⟩
#align function.injective_iff_has_left_inverse Function.injective_iff_hasLeftInverse

end InvFun

section SurjInv

variable {α : Sort u} {β : Sort v} {γ : Sort w} {f : α → β}

/-- The inverse of a surjective function. (Unlike `invFun`, this does not require
  `α` to be inhabited.) -/
noncomputable def surjInv {f : α → β} (h : Surjective f) (b : β) : α :=
  Classical.choose (h b)

theorem surjInv_eq (h : Surjective f) (b) : f (surjInv h b) = b :=
  Classical.choose_spec (h b)
#align function.surj_inv_eq Function.surjInv_eq

theorem rightInverse_surjInv (hf : Surjective f) : RightInverse (surjInv hf) f :=
  surjInv_eq hf
#align function.right_inverse_surj_inv Function.rightInverse_surjInv

theorem leftInverse_surjInv (hf : Bijective f) : LeftInverse (surjInv hf.2) f :=
  rightInverse_of_injective_of_leftInverse hf.1 (rightInverse_surjInv hf.2)
#align function.left_inverse_surj_inv Function.leftInverse_surjInv

theorem Surjective.hasRightInverse (hf : Surjective f) : HasRightInverse f :=
  ⟨_, rightInverse_surjInv hf⟩
#align function.surjective.has_right_inverse Function.Surjective.hasRightInverse

theorem surjective_iff_hasRightInverse : Surjective f ↔ HasRightInverse f :=
  ⟨Surjective.hasRightInverse, HasRightInverse.surjective⟩
#align function.surjective_iff_has_right_inverse Function.surjective_iff_hasRightInverse

theorem bijective_iff_has_inverse : Bijective f ↔ ∃ g, LeftInverse g f ∧ RightInverse g f :=
  ⟨fun hf ↦ ⟨_, leftInverse_surjInv hf, rightInverse_surjInv hf.2⟩, fun ⟨_, gl, gr⟩ ↦
    ⟨gl.injective, gr.surjective⟩⟩

theorem injective_surjInv (h : Surjective f) : Injective (surjInv h) :=
  (rightInverse_surjInv h).injective
#align function.injective_surj_inv Function.injective_surjInv

theorem surjective_to_subsingleton [na : Nonempty α] [Subsingleton β] (f : α → β) :
    Surjective f :=
  fun _ ↦ let ⟨a⟩ := na; ⟨a, Subsingleton.elim _ _⟩

/-- Composition by an surjective function on the left is itself surjective. -/
theorem Surjective.comp_left {g : β → γ} (hg : Surjective g) :
    Surjective ((· ∘ ·) g : (α → β) → α → γ) := fun f ↦
  ⟨surjInv hg ∘ f, funext fun _ ↦ rightInverse_surjInv _ _⟩

/-- Composition by an bijective function on the left is itself bijective. -/
theorem Bijective.comp_left {g : β → γ} (hg : Bijective g) :
    Bijective ((· ∘ ·) g : (α → β) → α → γ) :=
  ⟨hg.injective.comp_left, hg.surjective.comp_left⟩

end SurjInv

section Update

variable {α : Sort u} {β : α → Sort v} {α' : Sort w} [DecidableEq α] [DecidableEq α']
  {f g : (a : α) → β a} {a : α} {b : β a}


/-- Replacing the value of a function at a given point by a given value. -/
def update (f : ∀ a, β a) (a' : α) (v : β a') (a : α) : β a :=
  if h : a = a' then Eq.ndrec v h.symm else f a

/-- On non-dependent functions, `Function.update` can be expressed as an `ite` -/
theorem update_apply {β : Sort _} (f : α → β) (a' : α) (b : β) (a : α) :
    update f a' b a = if a = a' then b else f a :=
by have h2 : (h : a = a') → Eq.rec (motive := λ _ _ => β) b h.symm = b :=
     by intro h
        rw [eq_rec_constant]
   have h3 : (λ h : a = a' => Eq.rec (motive := λ _ _ => β) b h.symm) =
             (λ _ : a = a' =>  b) := funext h2
   let f := λ x => dite (a = a') x (λ (_: ¬ a = a') => (f a))
   exact congrArg f h3

@[simp]
theorem update_same (a : α) (v : β a) (f : ∀ a, β a) : update f a v a = v :=
  dif_pos rfl

theorem surjective_eval {α : Sort u} {β : α → Sort v} [h : ∀ a, Nonempty (β a)] (a : α) :
    Surjective (eval a : (∀ a, β a) → β a) := fun b ↦
  ⟨@update _ _ (Classical.decEq α) (fun a ↦ (h a).some) a b,
   @update_same _ _ (Classical.decEq α) _ _ _⟩

theorem update_injective (f : ∀ a, β a) (a' : α) : Injective (update f a') := fun v v' h ↦ by
  have := congr_fun h a'
  rwa [update_same, update_same] at this

@[simp]
theorem update_noteq {a a' : α} (h : a ≠ a') (v : β a') (f : ∀ a, β a) : update f a' v a = f a :=
  dif_neg h

lemma forall_update_iff (f : ∀a, β a) {a : α} {b : β a} (p : ∀a, β a → Prop) :
  (∀ x, p x (update f a b x)) ↔ p a b ∧ ∀ x, x ≠ a → p x (f x) := by
  rw [← and_forall_ne a, update_same]
  simp (config := { contextual := true })

theorem exists_update_iff (f : ∀ a, β a) {a : α} {b : β a} (p : ∀ a, β a → Prop) :
    (∃ x, p x (update f a b x)) ↔ p a b ∨ ∃ (x : _)(_ : x ≠ a), p x (f x) := by
  rw [← not_forall_not, forall_update_iff f fun a b ↦ ¬p a b]
  simp [-not_and, not_and_or]

theorem update_eq_iff {a : α} {b : β a} {f g : ∀ a, β a} :
    update f a b = g ↔ b = g a ∧ ∀ (x) (_ : x ≠ a), f x = g x :=
  funext_iff.trans <| forall_update_iff _ fun x y ↦ y = g x

theorem eq_update_iff {a : α} {b : β a} {f g : ∀ a, β a} :
    g = update f a b ↔ g a = b ∧ ∀ (x) (_ : x ≠ a), g x = f x :=
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
  funext fun _ ↦ update_noteq (h _) _ _

/-- Non-dependent version of `Function.update_comp_eq_of_forall_ne'` -/
theorem update_comp_eq_of_forall_ne {α β : Sort _} (g : α' → β) {f : α → α'} {i : α'} (a : β)
    (h : ∀ x, f x ≠ i) : update g i a ∘ f = g ∘ f :=
  update_comp_eq_of_forall_ne' g a h

theorem update_comp_eq_of_injective' (g : ∀ a, β a) {f : α' → α} (hf : Function.Injective f)
    (i : α') (a : β (f i)) : (fun j ↦ update g (f i) a (f j)) = update (fun i ↦ g (f i)) i a :=
  eq_update_iff.2 ⟨update_same _ _ _, fun _ hj ↦ update_noteq (hf.ne hj) _ _⟩

/-- Non-dependent version of `Function.update_comp_eq_of_injective'` -/
theorem update_comp_eq_of_injective {β : Sort _} (g : α' → β) {f : α → α'}
    (hf : Function.Injective f) (i : α) (a : β) :
    Function.update g (f i) a ∘ f = Function.update (g ∘ f) i a :=
  update_comp_eq_of_injective' g hf i a

theorem apply_update {ι : Sort _} [DecidableEq ι] {α β : ι → Sort _} (f : ∀ i, α i → β i)
    (g : ∀ i, α i) (i : ι) (v : α i) (j : ι) :
    f j (update g i v j) = update (fun k ↦ f k (g k)) i (f i v) j := by
  by_cases h:j = i
  · subst j
    simp
  · simp [h]

theorem apply_update₂ {ι : Sort _} [DecidableEq ι] {α β γ : ι → Sort _} (f : ∀ i, α i → β i → γ i)
    (g : ∀ i, α i) (h : ∀ i, β i) (i : ι) (v : α i) (w : β i) (j : ι) :
    f j (update g i v j) (update h i w j) = update (fun k ↦ f k (g k) (h k)) i (f i v w) j := by
  by_cases h:j = i
  · subst j
    simp
  · simp [h]


theorem comp_update {α' : Sort _} {β : Sort _} (f : α' → β) (g : α → α') (i : α) (v : α') :
    f ∘ update g i v = update (f ∘ g) i (f v) :=
  funext <| apply_update _ _ _ _

theorem update_comm {α} [DecidableEq α] {β : α → Sort _} {a b : α} (h : a ≠ b) (v : β a) (w : β b)
    (f : ∀ a, β a) : update (update f a v) b w = update (update f b w) a v := by
  funext c
  simp only [update]
  by_cases h₁ : c = b <;> by_cases h₂ : c = a
  · rw [dif_pos h₁, dif_pos h₂]
    cases h (h₂.symm.trans h₁)
  · rw [dif_pos h₁, dif_pos h₁, dif_neg h₂]
  · rw [dif_neg h₁, dif_neg h₁, dif_pos h₂]
  · rw [dif_neg h₁, dif_neg h₁, dif_neg h₂]

@[simp]
theorem update_idem {α} [DecidableEq α] {β : α → Sort _} {a : α} (v w : β a) (f : ∀ a, β a) :
    update (update f a v) a w = update f a w := by
  funext b
  by_cases b = a <;> simp [update, h]

end Update

noncomputable section Extend

attribute [local instance] Classical.propDecidable

variable {α β γ : Sort _} {f : α → β}

/-- `extend f g e'` extends a function `g : α → γ`
along a function `f : α → β` to a function `β → γ`,
by using the values of `g` on the range of `f`
and the values of an auxiliary function `e' : β → γ` elsewhere.

Mostly useful when `f` is injective, or more generally when `g.factors_through f` -/
-- Explicit Sort so that `α` isn't inferred to be Prop via `exists_prop_decidable`
def extend {α : Sort u} {β γ} (f : α → β) (g : α → γ) (e' : β → γ) : β → γ := fun b ↦
  if h : ∃ a, f a = b then g (Classical.choose h) else e' b

/-- g factors through f : `f a = f b → g a = g b` -/
def FactorsThrough (g : α → γ) (f : α → β) : Prop :=
  ∀ ⦃a b⦄, f a = f b → g a = g b

theorem extend_def (f : α → β) (g : α → γ) (e' : β → γ) (b : β) [Decidable (∃ a, f a = b)] :
    extend f g e' b = if h : ∃ a, f a = b then g (Classical.choose h) else e' b := by
  unfold extend
  congr

lemma Injective.FactorsThrough (hf : Injective f) (g : α → γ) : g.FactorsThrough f :=
  fun _ _ h => congr_arg g (hf h)

lemma FactorsThrough.extend_apply {g : α → γ} (hf : g.FactorsThrough f) (e' : β → γ) (a : α) :
  extend f g e' (f a) = g a := by
  simp only [extend_def, dif_pos, exists_apply_eq_apply]
  exact hf (Classical.choose_spec (exists_apply_eq_apply f a))

@[simp]
theorem Injective.extend_apply (hf : Injective f) (g : α → γ) (e' : β → γ) (a : α) :
    extend f g e' (f a) = g a :=
  (hf.FactorsThrough g).extend_apply e' a

@[simp]
theorem extend_apply' (g : α → γ) (e' : β → γ) (b : β) (hb : ¬∃ a, f a = b) :
    extend f g e' b = e' b := by
  simp [Function.extend_def, hb]

lemma factorsThrough_iff (g : α → γ) [Nonempty γ] :
  g.FactorsThrough f ↔ ∃ (e : β → γ), g = e ∘ f :=
⟨fun hf => ⟨extend f g (const β (Classical.arbitrary γ)),
      funext (fun x => by simp only [comp_apply, hf.extend_apply])⟩,
  fun h _ _ hf => by rw [Classical.choose_spec h, comp_apply, comp_apply, hf]⟩

lemma FactorsThrough.apply_extend {δ} {g : α → γ} (hf : FactorsThrough g f)
  (F : γ → δ) (e' : β → γ) (b : β) :
  F (extend f g e' b) = extend f (F ∘ g) (F ∘ e') b := by
  by_cases hb : ∃ a, f a = b
  case pos =>
    rcases hb with ⟨a, ha⟩
    subst b
    rw [hf.extend_apply, FactorsThrough.extend_apply, comp]
    case intro.hf =>
      intro a b h
      simp only [comp_apply]
      apply congr_arg
      exact hf h
  case neg =>
    rw [extend_apply' _ _ _ hb, extend_apply' _ _ _ hb, comp]

lemma Injective.apply_extend {δ} (hf : Injective f) (F : γ → δ) (g : α → γ) (e' : β → γ) (b : β) :
  F (extend f g e' b) = extend f (F ∘ g) (F ∘ e') b :=
  (hf.FactorsThrough g).apply_extend F e' b

theorem extend_injective (hf : Injective f) (e' : β → γ) : Injective fun g ↦ extend f g e' := by
  intro g₁ g₂ hg
  refine' funext fun x ↦ _
  have H := congr_fun hg (f x)
  simp only [hf.extend_apply] at H
  exact H

lemma FactorsThrough.extend_comp {g : α → γ} (e' : β → γ) (hf : FactorsThrough g f) :
  extend f g e' ∘ f = g :=
  funext $ fun a => hf.extend_apply e' a

@[simp]
theorem extend_comp (hf : Injective f) (g : α → γ) (e' : β → γ) : extend f g e' ∘ f = g :=
  funext fun a ↦ hf.extend_apply g e' a

theorem Injective.surjective_comp_right' (hf : Injective f) (g₀ : β → γ) :
    Surjective fun g : β → γ ↦ g ∘ f :=
  fun g ↦ ⟨extend f g g₀, extend_comp hf _ _⟩

theorem Injective.surjective_comp_right [Nonempty γ] (hf : Injective f) :
    Surjective fun g : β → γ ↦ g ∘ f :=
  hf.surjective_comp_right' fun _ ↦ Classical.choice ‹_›

theorem Bijective.comp_right (hf : Bijective f) : Bijective fun g : β → γ ↦ g ∘ f :=
  ⟨hf.surjective.injective_comp_right, fun g ↦
    ⟨g ∘ surjInv hf.surjective,
     by simp only [comp.assoc g _ f, (leftInverse_surjInv hf).comp_eq_id, comp.right_id]⟩⟩

end Extend

theorem uncurry_def {α β γ} (f : α → β → γ) : uncurry f = fun p ↦ f p.1 p.2 :=
  rfl

@[simp]
theorem uncurry_apply_pair {α β γ} (f : α → β → γ) (x : α) (y : β) : uncurry f (x, y) = f x y :=
  rfl

@[simp]
theorem curry_apply {α β γ} (f : α × β → γ) (x : α) (y : β) : curry f x y = f (x, y) :=
  rfl

section Bicomp

variable {α β γ δ ε : Type _}

/-- Compose a binary function `f` with a pair of unary functions `g` and `h`.
If both arguments of `f` have the same type and `g = h`, then `bicompl f g g = f on g`. -/
def bicompl (f : γ → δ → ε) (g : α → γ) (h : β → δ) (a b) :=
  f (g a) (h b)

/-- Compose an unary function `f` with a binary function `g`. -/
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

variable {α β γ δ : Type _}

/-- Records a way to turn an element of `α` into a function from `β` to `γ`. The most generic use
is to recursively uncurry. For instance `f : α → β → γ → δ` will be turned into
`↿f : α × β × γ → δ`. One can also add instances for bundled maps. -/
class HasUncurry (α : Type _) (β : outParam (Type _)) (γ : outParam (Type _)) where
  /-- Uncurrying operator. The most generic use is to recursively uncurry. For instance
  `f : α → β → γ → δ` will be turned into `↿f : α × β × γ → δ`. One can also add instances
  for bundled maps.-/
  uncurry : α → β → γ

notation:arg "↿" x:arg => HasUncurry.uncurry x

instance hasUncurryBase : HasUncurry (α → β) α β :=
  ⟨id⟩

instance hasUncurryInduction [HasUncurry β γ δ] : HasUncurry (α → β) (α × γ) δ :=
  ⟨fun f p ↦ (↿(f p.1)) p.2⟩

end Uncurry

/-- A function is involutive, if `f ∘ f = id`. -/
def Involutive {α} (f : α → α) : Prop :=
  ∀ x, f (f x) = x

theorem involutive_iff_iter_2_eq_id {α} {f : α → α} : Involutive f ↔ f^[2] = id :=
  funext_iff.symm

theorem _root_.Bool.involutive_not : Involutive not :=
  Bool.not_not

namespace Involutive

variable {α : Sort u} {f : α → α} (h : Involutive f)

@[simp]
theorem comp_self : f ∘ f = id :=
  funext h

protected theorem leftInverse : LeftInverse f f := h
#align function.involutive.left_inverse Function.Involutive.leftInverse

protected theorem rightInverse : RightInverse f f := h
#align function.involutive.right_inverse Function.Involutive.rightInverse

protected theorem injective : Injective f := h.leftInverse.injective
#align function.involutive.injective Function.Involutive.injective

protected theorem surjective : Surjective f := fun x ↦ ⟨f x, h x⟩
#align function.involutive.surjective Function.Involutive.surjective

protected theorem bijective : Bijective f := ⟨h.injective, h.surjective⟩
#align function.involutive.bijective Function.Involutive.bijective

/-- Involuting an `ite` of an involuted value `x : α` negates the `Prop` condition in the `ite`. -/
protected theorem ite_not (P : Prop) [Decidable P] (x : α) : f (ite P x (f x)) = ite (¬P) x (f x) :=
  by rw [apply_ite f, h, ite_not]

/-- An involution commutes across an equality. Compare to `Function.Injective.eq_iff`. -/
protected theorem eq_iff {x y : α} : f x = y ↔ x = f y :=
  h.injective.eq_iff' (h y)

end Involutive

/-- The property of a binary function `f : α → β → γ` being injective.
Mathematically this should be thought of as the corresponding function `α × β → γ` being injective.
-/
def Injective2 {α β γ} (f : α → β → γ) : Prop :=
  ∀ ⦃a₁ a₂ b₁ b₂⦄, f a₁ b₁ = f a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂

namespace Injective2

variable {α β γ : Sort _} {f : α → β → γ}

/-- A binary injective function is injective when only the left argument varies. -/
protected theorem left (hf : Injective2 f) (b : β) : Function.Injective fun a ↦ f a b :=
  fun _ _ h ↦ (hf h).left

/-- A binary injective function is injective when only the right argument varies. -/
protected theorem right (hf : Injective2 f) (a : α) : Function.Injective (f a) :=
  fun _ _ h ↦ (hf h).right

protected theorem uncurry {α β γ : Type _} {f : α → β → γ} (hf : Injective2 f) :
    Function.Injective (uncurry f) :=
  fun ⟨_, _⟩ ⟨_, _⟩ h ↦ (hf h).elim (congr_arg₂ _)

/-- As a map from the left argument to a unary function, `f` is injective. -/
theorem left' (hf : Injective2 f) [Nonempty β] : Function.Injective f := fun a₁ a₂ h ↦
  let ⟨b⟩ := ‹Nonempty β›
  hf.left b <| (congr_fun h b : _)

/-- As a map from the right argument to a unary function, `f` is injective. -/
theorem right' (hf : Injective2 f) [Nonempty α] : Function.Injective fun b a ↦ f a b :=
  fun b₁ b₂ h ↦
    let ⟨a⟩ := ‹Nonempty α›
    hf.right a <| (congr_fun h a : _)

theorem eq_iff (hf : Injective2 f) {a₁ a₂ b₁ b₂} : f a₁ b₁ = f a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
  ⟨fun h ↦ hf h, fun ⟨h1, h2⟩ ↦ congr_arg₂ f h1 h2⟩

end Injective2

section Sometimes

attribute [local instance] Classical.propDecidable

/-- `sometimes f` evaluates to some value of `f`, if it exists. This function is especially
interesting in the case where `α` is a proposition, in which case `f` is necessarily a
constant function, so that `sometimes f = f a` for all `a`. -/
noncomputable def sometimes {α β} [Nonempty β] (f : α → β) : β :=
  if h : Nonempty α then f (Classical.choice h) else Classical.choice ‹_›

theorem sometimes_eq {p : Prop} {α} [Nonempty α] (f : p → α) (a : p) : sometimes f = f a :=
  dif_pos ⟨a⟩

theorem sometimes_spec {p : Prop} {α} [Nonempty α] (P : α → Prop) (f : p → α) (a : p)
    (h : P (f a)) : P (sometimes f) :=
  by rwa [sometimes_eq]

end Sometimes

end Function

/-- `s.piecewise f g` is the function equal to `f` on the set `s`, and to `g` on its complement. -/
def Set.piecewise {α : Type u} {β : α → Sort v} (s : Set α) (f g : ∀ i, β i)
    [∀ j, Decidable (j ∈ s)] : ∀ i, β i :=
  fun i ↦ if i ∈ s then f i else g i

/-! ### Bijectivity of `eq.rec`, `eq.mp`, `eq.mpr`, and `cast` -/


theorem eq_rec_on_bijective {α : Sort _} {C : α → Sort _} :
    ∀ {a a' : α} (h : a = a'), Function.Bijective (@Eq.ndrec _ _ C · _ h)
  | _, _, rfl => ⟨fun _ _ ↦ id, fun x ↦ ⟨x, rfl⟩⟩

theorem eq_mp_bijective {α β : Sort _} (h : α = β) : Function.Bijective (Eq.mp h) := by
  -- TODO: mathlib3 uses `eq_rec_on_bijective`, difference in elaboration here
  -- due to `@[macro_inline] possibly?
  cases h
  refine ⟨fun _ _ ↦ id, fun x ↦ ⟨x, rfl⟩⟩

theorem eq_mpr_bijective {α β : Sort _} (h : α = β) : Function.Bijective (Eq.mpr h) := by
  cases h
  refine ⟨fun _ _ ↦ id, fun x ↦ ⟨x, rfl⟩⟩

theorem cast_bijective {α β : Sort _} (h : α = β) : Function.Bijective (cast h) := by
  cases h
  refine ⟨fun _ _ ↦ id, fun x ↦ ⟨x, rfl⟩⟩

/-! Note these lemmas apply to `Type _` not `Sort*`, as the latter interferes with `simp`, and
is trivial anyway.-/


@[simp]
theorem eq_rec_inj {α : Sort _} {a a' : α} (h : a = a') {C : α → Type _} (x y : C a) :
    (Eq.ndrec x h : C a') = Eq.ndrec y h ↔ x = y :=
  (eq_rec_on_bijective h).injective.eq_iff

@[simp]
theorem cast_inj {α β : Type _} (h : α = β) {x y : α} : cast h x = cast h y ↔ x = y :=
  (cast_bijective h).injective.eq_iff

theorem Function.LeftInverse.eq_rec_eq {α β : Sort _} {γ : β → Sort v} {f : α → β} {g : β → α}
    (h : Function.LeftInverse g f) (C : ∀ a : α, γ (f a)) (a : α) :
    -- TODO: mathlib3 uses `(congr_arg f (h a)).rec (C (g (f a)))` for LHS
    @Eq.rec β (f (g (f a))) (fun x _ ↦ γ x) (C (g (f a))) (f a) (congr_arg f (h a)) = C a :=
  eq_of_heq <| (eq_rec_heq _ _).trans <| by rw [h]

theorem Function.LeftInverse.eq_rec_on_eq {α β : Sort _} {γ : β → Sort v} {f : α → β} {g : β → α}
    (h : Function.LeftInverse g f) (C : ∀ a : α, γ (f a)) (a : α) :
    -- TODO: mathlib3 uses `(congr_arg f (h a)).recOn (C (g (f a)))` for LHS
    @Eq.recOn β (f (g (f a))) (fun x _ ↦ γ x) (f a) (congr_arg f (h a)) (C (g (f a))) = C a :=
  h.eq_rec_eq _ _

theorem Function.LeftInverse.cast_eq {α β : Sort _} {γ : β → Sort v} {f : α → β} {g : β → α}
    (h : Function.LeftInverse g f) (C : ∀ a : α, γ (f a)) (a : α) :
    cast (congr_arg (fun a ↦ γ (f a)) (h a)) (C (g (f a))) = C a := by
  rw [cast_eq_iff_heq, h]

/-- A set of functions "separates points"
if for each pair of distinct points there is a function taking different values on them. -/
def Set.SeparatesPoints {α β : Type _} (A : Set (α → β)) : Prop :=
  ∀ ⦃x y : α⦄, x ≠ y → ∃ f ∈ A, (f x : β) ≠ f y

theorem IsSymmOp.flip_eq {α β} (op) [IsSymmOp α β op] : flip op = op :=
  funext fun a ↦ funext fun b ↦ (IsSymmOp.symm_op a b).symm

theorem InvImage.equivalence {α : Sort u} {β : Sort v} (r : β → β → Prop) (f : α → β)
    (h : Equivalence r) : Equivalence (InvImage r f) :=
  ⟨fun _ ↦ h.1 _, fun w ↦ h.symm w, fun h₁ h₂ ↦ InvImage.trans r f (fun _ _ _ ↦ h.trans) h₁ h₂⟩
