/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Andrew Zipperer, Haitao Zhang, Minchao Wu, Yury Kudryashov

! This file was ported from Lean 3 source module data.set.function
! leanprover-community/mathlib commit 198161d833f2c01498c39c266b0b3dbe2c7a8c07
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Prod
import Mathbin.Logic.Function.Conjugate

/-!
# Functions over sets

## Main definitions

### Predicate

* `set.eq_on f₁ f₂ s` : functions `f₁` and `f₂` are equal at every point of `s`;
* `set.maps_to f s t` : `f` sends every point of `s` to a point of `t`;
* `set.inj_on f s` : restriction of `f` to `s` is injective;
* `set.surj_on f s t` : every point in `s` has a preimage in `s`;
* `set.bij_on f s t` : `f` is a bijection between `s` and `t`;
* `set.left_inv_on f' f s` : for every `x ∈ s` we have `f' (f x) = x`;
* `set.right_inv_on f' f t` : for every `y ∈ t` we have `f (f' y) = y`;
* `set.inv_on f' f s t` : `f'` is a two-side inverse of `f` on `s` and `t`, i.e.
  we have `set.left_inv_on f' f s` and `set.right_inv_on f' f t`.

### Functions

* `set.restrict f s` : restrict the domain of `f` to the set `s`;
* `set.cod_restrict f s h` : given `h : ∀ x, f x ∈ s`, restrict the codomain of `f` to the set `s`;
* `set.maps_to.restrict f s t h`: given `h : maps_to f s t`, restrict the domain of `f` to `s`
  and the codomain to `t`.
-/


universe u v w x y

variable {α : Type u} {β : Type v} {π : α → Type v} {γ : Type w} {ι : Sort x}

open Function

namespace Set

/-! ### Restrict -/


/-- Restrict domain of a function `f` to a set `s`. Same as `subtype.restrict` but this version
takes an argument `↥s` instead of `subtype s`. -/
def restrict (s : Set α) (f : ∀ a : α, π a) : ∀ a : s, π a := fun x => f x
#align set.restrict Set.restrict

theorem restrict_eq (f : α → β) (s : Set α) : s.restrict f = f ∘ coe :=
  rfl
#align set.restrict_eq Set.restrict_eq

@[simp]
theorem restrict_apply (f : α → β) (s : Set α) (x : s) : s.restrict f x = f x :=
  rfl
#align set.restrict_apply Set.restrict_apply

theorem restrict_eq_iff {f : ∀ a, π a} {s : Set α} {g : ∀ a : s, π a} :
    restrict s f = g ↔ ∀ (a) (ha : a ∈ s), f a = g ⟨a, ha⟩ :=
  funext_iff.trans Subtype.forall
#align set.restrict_eq_iff Set.restrict_eq_iff

theorem eq_restrict_iff {s : Set α} {f : ∀ a : s, π a} {g : ∀ a, π a} :
    f = restrict s g ↔ ∀ (a) (ha : a ∈ s), f ⟨a, ha⟩ = g a :=
  funext_iff.trans Subtype.forall
#align set.eq_restrict_iff Set.eq_restrict_iff

@[simp]
theorem range_restrict (f : α → β) (s : Set α) : Set.range (s.restrict f) = f '' s :=
  (range_comp _ _).trans <| congr_arg ((· '' ·) f) Subtype.range_coe
#align set.range_restrict Set.range_restrict

theorem image_restrict (f : α → β) (s t : Set α) : s.restrict f '' (coe ⁻¹' t) = f '' (t ∩ s) := by
  rw [restrict, image_comp, image_preimage_eq_inter_range, Subtype.range_coe]
#align set.image_restrict Set.image_restrict

/- ./././Mathport/Syntax/Translate/Basic.lean:631:2: warning: expanding binder collection (a «expr ∉ » s) -/
@[simp]
theorem restrict_dite {s : Set α} [∀ x, Decidable (x ∈ s)] (f : ∀ a ∈ s, β)
    (g : ∀ (a) (_ : a ∉ s), β) :
    (s.restrict fun a => if h : a ∈ s then f a h else g a h) = fun a => f a a.2 :=
  funext fun a => dif_pos a.2
#align set.restrict_dite Set.restrict_dite

/- ./././Mathport/Syntax/Translate/Basic.lean:631:2: warning: expanding binder collection (a «expr ∉ » s) -/
@[simp]
theorem restrict_dite_compl {s : Set α} [∀ x, Decidable (x ∈ s)] (f : ∀ a ∈ s, β)
    (g : ∀ (a) (_ : a ∉ s), β) :
    (sᶜ.restrict fun a => if h : a ∈ s then f a h else g a h) = fun a => g a a.2 :=
  funext fun a => dif_neg a.2
#align set.restrict_dite_compl Set.restrict_dite_compl

@[simp]
theorem restrict_ite (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    (s.restrict fun a => if a ∈ s then f a else g a) = s.restrict f :=
  restrict_dite _ _
#align set.restrict_ite Set.restrict_ite

@[simp]
theorem restrict_ite_compl (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    (sᶜ.restrict fun a => if a ∈ s then f a else g a) = sᶜ.restrict g :=
  restrict_dite_compl _ _
#align set.restrict_ite_compl Set.restrict_ite_compl

@[simp]
theorem restrict_piecewise (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    s.restrict (piecewise s f g) = s.restrict f :=
  restrict_ite _ _ _
#align set.restrict_piecewise Set.restrict_piecewise

@[simp]
theorem restrict_piecewise_compl (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    sᶜ.restrict (piecewise s f g) = sᶜ.restrict g :=
  restrict_ite_compl _ _ _
#align set.restrict_piecewise_compl Set.restrict_piecewise_compl

theorem restrict_extend_range (f : α → β) (g : α → γ) (g' : β → γ) :
    (range f).restrict (extend f g g') = fun x => g x.coe_prop.some := by convert restrict_dite _ _
#align set.restrict_extend_range Set.restrict_extend_range

@[simp]
theorem restrict_extend_compl_range (f : α → β) (g : α → γ) (g' : β → γ) :
    range fᶜ.restrict (extend f g g') = g' ∘ coe := by convert restrict_dite_compl _ _
#align set.restrict_extend_compl_range Set.restrict_extend_compl_range

theorem range_extend_subset (f : α → β) (g : α → γ) (g' : β → γ) :
    range (extend f g g') ⊆ range g ∪ g' '' range fᶜ := by
  classical 
    rintro _ ⟨y, rfl⟩
    rw [extend_def]
    split_ifs
    exacts[Or.inl (mem_range_self _), Or.inr (mem_image_of_mem _ h)]
#align set.range_extend_subset Set.range_extend_subset

theorem range_extend {f : α → β} (hf : Injective f) (g : α → γ) (g' : β → γ) :
    range (extend f g g') = range g ∪ g' '' range fᶜ := by
  refine' (range_extend_subset _ _ _).antisymm _
  rintro z (⟨x, rfl⟩ | ⟨y, hy, rfl⟩)
  exacts[⟨f x, hf.extend_apply _ _ _⟩, ⟨y, extend_apply' _ _ _ hy⟩]
#align set.range_extend Set.range_extend

/-- Restrict codomain of a function `f` to a set `s`. Same as `subtype.coind` but this version
has codomain `↥s` instead of `subtype s`. -/
def codRestrict (f : ι → α) (s : Set α) (h : ∀ x, f x ∈ s) : ι → s := fun x => ⟨f x, h x⟩
#align set.cod_restrict Set.codRestrict

@[simp]
theorem coe_cod_restrict_apply (f : ι → α) (s : Set α) (h : ∀ x, f x ∈ s) (x : ι) :
    (codRestrict f s h x : α) = f x :=
  rfl
#align set.coe_cod_restrict_apply Set.coe_cod_restrict_apply

@[simp]
theorem restrict_comp_cod_restrict {f : ι → α} {g : α → β} {b : Set α} (h : ∀ x, f x ∈ b) :
    b.restrict g ∘ b.codRestrict f h = g ∘ f :=
  rfl
#align set.restrict_comp_cod_restrict Set.restrict_comp_cod_restrict

@[simp]
theorem injective_cod_restrict {f : ι → α} {s : Set α} (h : ∀ x, f x ∈ s) :
    Injective (codRestrict f s h) ↔ Injective f := by
  simp only [injective, Subtype.ext_iff, coe_cod_restrict_apply]
#align set.injective_cod_restrict Set.injective_cod_restrict

alias injective_cod_restrict ↔ _ _root_.function.injective.cod_restrict

variable {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {p : Set γ} {f f₁ f₂ f₃ : α → β} {g g₁ g₂ : β → γ}
  {f' f₁' f₂' : β → α} {g' : γ → β}

/-! ### Equality on a set -/


/-- Two functions `f₁ f₂ : α → β` are equal on `s`
  if `f₁ x = f₂ x` for all `x ∈ a`. -/
def EqOn (f₁ f₂ : α → β) (s : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ s → f₁ x = f₂ x
#align set.eq_on Set.EqOn

@[simp]
theorem eq_on_empty (f₁ f₂ : α → β) : EqOn f₁ f₂ ∅ := fun x => False.elim
#align set.eq_on_empty Set.eq_on_empty

@[simp]
theorem restrict_eq_restrict_iff : restrict s f₁ = restrict s f₂ ↔ EqOn f₁ f₂ s :=
  restrict_eq_iff
#align set.restrict_eq_restrict_iff Set.restrict_eq_restrict_iff

@[symm]
theorem EqOn.symm (h : EqOn f₁ f₂ s) : EqOn f₂ f₁ s := fun x hx => (h hx).symm
#align set.eq_on.symm Set.EqOn.symm

theorem eq_on_comm : EqOn f₁ f₂ s ↔ EqOn f₂ f₁ s :=
  ⟨EqOn.symm, EqOn.symm⟩
#align set.eq_on_comm Set.eq_on_comm

@[refl]
theorem eq_on_refl (f : α → β) (s : Set α) : EqOn f f s := fun _ _ => rfl
#align set.eq_on_refl Set.eq_on_refl

@[trans]
theorem EqOn.trans (h₁ : EqOn f₁ f₂ s) (h₂ : EqOn f₂ f₃ s) : EqOn f₁ f₃ s := fun x hx =>
  (h₁ hx).trans (h₂ hx)
#align set.eq_on.trans Set.EqOn.trans

theorem EqOn.image_eq (heq : EqOn f₁ f₂ s) : f₁ '' s = f₂ '' s :=
  image_congr HEq
#align set.eq_on.image_eq Set.EqOn.image_eq

theorem EqOn.inter_preimage_eq (heq : EqOn f₁ f₂ s) (t : Set β) : s ∩ f₁ ⁻¹' t = s ∩ f₂ ⁻¹' t :=
  ext fun x => and_congr_right_iff.2 fun hx => by rw [mem_preimage, mem_preimage, HEq hx]
#align set.eq_on.inter_preimage_eq Set.EqOn.inter_preimage_eq

theorem EqOn.mono (hs : s₁ ⊆ s₂) (hf : EqOn f₁ f₂ s₂) : EqOn f₁ f₂ s₁ := fun x hx => hf (hs hx)
#align set.eq_on.mono Set.EqOn.mono

@[simp]
theorem eq_on_union : EqOn f₁ f₂ (s₁ ∪ s₂) ↔ EqOn f₁ f₂ s₁ ∧ EqOn f₁ f₂ s₂ :=
  ball_or_left
#align set.eq_on_union Set.eq_on_union

theorem EqOn.union (h₁ : EqOn f₁ f₂ s₁) (h₂ : EqOn f₁ f₂ s₂) : EqOn f₁ f₂ (s₁ ∪ s₂) :=
  eq_on_union.2 ⟨h₁, h₂⟩
#align set.eq_on.union Set.EqOn.union

theorem EqOn.comp_left (h : s.EqOn f₁ f₂) : s.EqOn (g ∘ f₁) (g ∘ f₂) := fun a ha =>
  congr_arg _ <| h ha
#align set.eq_on.comp_left Set.EqOn.comp_left

@[simp]
theorem eq_on_range {ι : Sort _} {f : ι → α} {g₁ g₂ : α → β} :
    EqOn g₁ g₂ (range f) ↔ g₁ ∘ f = g₂ ∘ f :=
  forall_range_iff.trans <| funext_iff.symm
#align set.eq_on_range Set.eq_on_range

alias eq_on_range ↔ eq_on.comp_eq _

/-! ### Congruence lemmas -/


section Order

variable [Preorder α] [Preorder β]

theorem MonotoneOn.congr (h₁ : MonotoneOn f₁ s) (h : s.EqOn f₁ f₂) : MonotoneOn f₂ s := by
  intro a ha b hb hab
  rw [← h ha, ← h hb]
  exact h₁ ha hb hab
#align monotone_on.congr MonotoneOn.congr

theorem AntitoneOn.congr (h₁ : AntitoneOn f₁ s) (h : s.EqOn f₁ f₂) : AntitoneOn f₂ s :=
  h₁.dual_right.congr h
#align antitone_on.congr AntitoneOn.congr

theorem StrictMonoOn.congr (h₁ : StrictMonoOn f₁ s) (h : s.EqOn f₁ f₂) : StrictMonoOn f₂ s := by
  intro a ha b hb hab
  rw [← h ha, ← h hb]
  exact h₁ ha hb hab
#align strict_mono_on.congr StrictMonoOn.congr

theorem StrictAntiOn.congr (h₁ : StrictAntiOn f₁ s) (h : s.EqOn f₁ f₂) : StrictAntiOn f₂ s :=
  h₁.dual_right.congr h
#align strict_anti_on.congr StrictAntiOn.congr

theorem EqOn.congr_monotone_on (h : s.EqOn f₁ f₂) : MonotoneOn f₁ s ↔ MonotoneOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩
#align set.eq_on.congr_monotone_on Set.EqOn.congr_monotone_on

theorem EqOn.congr_antitone_on (h : s.EqOn f₁ f₂) : AntitoneOn f₁ s ↔ AntitoneOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩
#align set.eq_on.congr_antitone_on Set.EqOn.congr_antitone_on

theorem EqOn.congr_strict_mono_on (h : s.EqOn f₁ f₂) : StrictMonoOn f₁ s ↔ StrictMonoOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩
#align set.eq_on.congr_strict_mono_on Set.EqOn.congr_strict_mono_on

theorem EqOn.congr_strict_anti_on (h : s.EqOn f₁ f₂) : StrictAntiOn f₁ s ↔ StrictAntiOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩
#align set.eq_on.congr_strict_anti_on Set.EqOn.congr_strict_anti_on

end Order

/-! ### Mono lemmas-/


section Mono

variable [Preorder α] [Preorder β]

theorem MonotoneOn.mono (h : MonotoneOn f s) (h' : s₂ ⊆ s) : MonotoneOn f s₂ := fun x hx y hy =>
  h (h' hx) (h' hy)
#align monotone_on.mono MonotoneOn.mono

theorem AntitoneOn.mono (h : AntitoneOn f s) (h' : s₂ ⊆ s) : AntitoneOn f s₂ := fun x hx y hy =>
  h (h' hx) (h' hy)
#align antitone_on.mono AntitoneOn.mono

theorem StrictMonoOn.mono (h : StrictMonoOn f s) (h' : s₂ ⊆ s) : StrictMonoOn f s₂ :=
  fun x hx y hy => h (h' hx) (h' hy)
#align strict_mono_on.mono StrictMonoOn.mono

theorem StrictAntiOn.mono (h : StrictAntiOn f s) (h' : s₂ ⊆ s) : StrictAntiOn f s₂ :=
  fun x hx y hy => h (h' hx) (h' hy)
#align strict_anti_on.mono StrictAntiOn.mono

protected theorem MonotoneOn.monotone (h : MonotoneOn f s) : Monotone (f ∘ coe : s → β) :=
  fun x y hle => h x.coe_prop y.coe_prop hle
#align monotone_on.monotone MonotoneOn.monotone

protected theorem AntitoneOn.monotone (h : AntitoneOn f s) : Antitone (f ∘ coe : s → β) :=
  fun x y hle => h x.coe_prop y.coe_prop hle
#align antitone_on.monotone AntitoneOn.monotone

protected theorem StrictMonoOn.strict_mono (h : StrictMonoOn f s) : StrictMono (f ∘ coe : s → β) :=
  fun x y hlt => h x.coe_prop y.coe_prop hlt
#align strict_mono_on.strict_mono StrictMonoOn.strict_mono

protected theorem StrictAntiOn.strict_anti (h : StrictAntiOn f s) : StrictAnti (f ∘ coe : s → β) :=
  fun x y hlt => h x.coe_prop y.coe_prop hlt
#align strict_anti_on.strict_anti StrictAntiOn.strict_anti

end Mono

/-! ### maps to -/


/-- `maps_to f a b` means that the image of `a` is contained in `b`. -/
def MapsTo (f : α → β) (s : Set α) (t : Set β) : Prop :=
  ∀ ⦃x⦄, x ∈ s → f x ∈ t
#align set.maps_to Set.MapsTo

/-- Given a map `f` sending `s : set α` into `t : set β`, restrict domain of `f` to `s`
and the codomain to `t`. Same as `subtype.map`. -/
def MapsTo.restrict (f : α → β) (s : Set α) (t : Set β) (h : MapsTo f s t) : s → t :=
  Subtype.map f h
#align set.maps_to.restrict Set.MapsTo.restrict

@[simp]
theorem MapsTo.coe_restrict_apply (h : MapsTo f s t) (x : s) : (h.restrict f s t x : β) = f x :=
  rfl
#align set.maps_to.coe_restrict_apply Set.MapsTo.coe_restrict_apply

/-- Restricting the domain and then the codomain is the same as `maps_to.restrict`. -/
@[simp]
theorem cod_restrict_restrict (h : ∀ x : s, f x ∈ t) :
    codRestrict (s.restrict f) t h = MapsTo.restrict f s t fun x hx => h ⟨x, hx⟩ :=
  rfl
#align set.cod_restrict_restrict Set.cod_restrict_restrict

/-- Reverse of `set.cod_restrict_restrict`. -/
theorem MapsTo.restrict_eq_cod_restrict (h : MapsTo f s t) :
    h.restrict f s t = codRestrict (s.restrict f) t fun x => h x.2 :=
  rfl
#align set.maps_to.restrict_eq_cod_restrict Set.MapsTo.restrict_eq_cod_restrict

theorem MapsTo.coe_restrict (h : Set.MapsTo f s t) : coe ∘ h.restrict f s t = s.restrict f :=
  rfl
#align set.maps_to.coe_restrict Set.MapsTo.coe_restrict

theorem MapsTo.range_restrict (f : α → β) (s : Set α) (t : Set β) (h : MapsTo f s t) :
    range (h.restrict f s t) = coe ⁻¹' (f '' s) :=
  Set.range_subtype_map f h
#align set.maps_to.range_restrict Set.MapsTo.range_restrict

theorem maps_to_iff_exists_map_subtype : MapsTo f s t ↔ ∃ g : s → t, ∀ x : s, f x = g x :=
  ⟨fun h => ⟨h.restrict f s t, fun _ => rfl⟩, fun ⟨g, hg⟩ x hx => by
    erw [hg ⟨x, hx⟩]
    apply Subtype.coe_prop⟩
#align set.maps_to_iff_exists_map_subtype Set.maps_to_iff_exists_map_subtype

theorem maps_to' : MapsTo f s t ↔ f '' s ⊆ t :=
  image_subset_iff.symm
#align set.maps_to' Set.maps_to'

theorem MapsTo.subset_preimage {f : α → β} {s : Set α} {t : Set β} (hf : MapsTo f s t) :
    s ⊆ f ⁻¹' t :=
  hf
#align set.maps_to.subset_preimage Set.MapsTo.subset_preimage

@[simp]
theorem maps_to_singleton {x : α} : MapsTo f {x} t ↔ f x ∈ t :=
  singleton_subset_iff
#align set.maps_to_singleton Set.maps_to_singleton

theorem maps_to_empty (f : α → β) (t : Set β) : MapsTo f ∅ t :=
  empty_subset _
#align set.maps_to_empty Set.maps_to_empty

theorem MapsTo.image_subset (h : MapsTo f s t) : f '' s ⊆ t :=
  maps_to'.1 h
#align set.maps_to.image_subset Set.MapsTo.image_subset

theorem MapsTo.congr (h₁ : MapsTo f₁ s t) (h : EqOn f₁ f₂ s) : MapsTo f₂ s t := fun x hx =>
  h hx ▸ h₁ hx
#align set.maps_to.congr Set.MapsTo.congr

theorem EqOn.comp_right (hg : t.EqOn g₁ g₂) (hf : s.MapsTo f t) : s.EqOn (g₁ ∘ f) (g₂ ∘ f) :=
  fun a ha => hg <| hf ha
#align set.eq_on.comp_right Set.EqOn.comp_right

theorem EqOn.maps_to_iff (H : EqOn f₁ f₂ s) : MapsTo f₁ s t ↔ MapsTo f₂ s t :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩
#align set.eq_on.maps_to_iff Set.EqOn.maps_to_iff

theorem MapsTo.comp (h₁ : MapsTo g t p) (h₂ : MapsTo f s t) : MapsTo (g ∘ f) s p := fun x h =>
  h₁ (h₂ h)
#align set.maps_to.comp Set.MapsTo.comp

theorem maps_to_id (s : Set α) : MapsTo id s s := fun x => id
#align set.maps_to_id Set.maps_to_id

theorem MapsTo.iterate {f : α → α} {s : Set α} (h : MapsTo f s s) : ∀ n, MapsTo (f^[n]) s s
  | 0 => fun _ => id
  | n + 1 => (maps_to.iterate n).comp h
#align set.maps_to.iterate Set.MapsTo.iterate

theorem MapsTo.iterate_restrict {f : α → α} {s : Set α} (h : MapsTo f s s) (n : ℕ) :
    h.restrict f s s^[n] = (h.iterate n).restrict _ _ _ := by
  funext x
  rw [Subtype.ext_iff, maps_to.coe_restrict_apply]
  induction' n with n ihn generalizing x
  · rfl
  · simp [Nat.iterate, ihn]
#align set.maps_to.iterate_restrict Set.MapsTo.iterate_restrict

theorem MapsTo.mono (hf : MapsTo f s₁ t₁) (hs : s₂ ⊆ s₁) (ht : t₁ ⊆ t₂) : MapsTo f s₂ t₂ :=
  fun x hx => ht (hf <| hs hx)
#align set.maps_to.mono Set.MapsTo.mono

theorem MapsTo.mono_left (hf : MapsTo f s₁ t) (hs : s₂ ⊆ s₁) : MapsTo f s₂ t := fun x hx =>
  hf (hs hx)
#align set.maps_to.mono_left Set.MapsTo.mono_left

theorem MapsTo.mono_right (hf : MapsTo f s t₁) (ht : t₁ ⊆ t₂) : MapsTo f s t₂ := fun x hx =>
  ht (hf hx)
#align set.maps_to.mono_right Set.MapsTo.mono_right

theorem MapsTo.union_union (h₁ : MapsTo f s₁ t₁) (h₂ : MapsTo f s₂ t₂) :
    MapsTo f (s₁ ∪ s₂) (t₁ ∪ t₂) := fun x hx =>
  hx.elim (fun hx => Or.inl <| h₁ hx) fun hx => Or.inr <| h₂ hx
#align set.maps_to.union_union Set.MapsTo.union_union

theorem MapsTo.union (h₁ : MapsTo f s₁ t) (h₂ : MapsTo f s₂ t) : MapsTo f (s₁ ∪ s₂) t :=
  union_self t ▸ h₁.union_union h₂
#align set.maps_to.union Set.MapsTo.union

@[simp]
theorem maps_to_union : MapsTo f (s₁ ∪ s₂) t ↔ MapsTo f s₁ t ∧ MapsTo f s₂ t :=
  ⟨fun h =>
    ⟨h.mono (subset_union_left s₁ s₂) (Subset.refl t),
      h.mono (subset_union_right s₁ s₂) (Subset.refl t)⟩,
    fun h => h.1.union h.2⟩
#align set.maps_to_union Set.maps_to_union

theorem MapsTo.inter (h₁ : MapsTo f s t₁) (h₂ : MapsTo f s t₂) : MapsTo f s (t₁ ∩ t₂) := fun x hx =>
  ⟨h₁ hx, h₂ hx⟩
#align set.maps_to.inter Set.MapsTo.inter

theorem MapsTo.inter_inter (h₁ : MapsTo f s₁ t₁) (h₂ : MapsTo f s₂ t₂) :
    MapsTo f (s₁ ∩ s₂) (t₁ ∩ t₂) := fun x hx => ⟨h₁ hx.1, h₂ hx.2⟩
#align set.maps_to.inter_inter Set.MapsTo.inter_inter

@[simp]
theorem maps_to_inter : MapsTo f s (t₁ ∩ t₂) ↔ MapsTo f s t₁ ∧ MapsTo f s t₂ :=
  ⟨fun h =>
    ⟨h.mono (Subset.refl s) (inter_subset_left t₁ t₂),
      h.mono (Subset.refl s) (inter_subset_right t₁ t₂)⟩,
    fun h => h.1.inter h.2⟩
#align set.maps_to_inter Set.maps_to_inter

theorem maps_to_univ (f : α → β) (s : Set α) : MapsTo f s univ := fun x h => trivial
#align set.maps_to_univ Set.maps_to_univ

theorem maps_to_image (f : α → β) (s : Set α) : MapsTo f s (f '' s) := by rw [maps_to']
#align set.maps_to_image Set.maps_to_image

theorem maps_to_preimage (f : α → β) (t : Set β) : MapsTo f (f ⁻¹' t) t :=
  Subset.refl _
#align set.maps_to_preimage Set.maps_to_preimage

theorem maps_to_range (f : α → β) (s : Set α) : MapsTo f s (range f) :=
  (maps_to_image f s).mono (Subset.refl s) (image_subset_range _ _)
#align set.maps_to_range Set.maps_to_range

@[simp]
theorem maps_image_to (f : α → β) (g : γ → α) (s : Set γ) (t : Set β) :
    MapsTo f (g '' s) t ↔ MapsTo (f ∘ g) s t :=
  ⟨fun h c hc => h ⟨c, hc, rfl⟩, fun h d ⟨c, hc⟩ => hc.2 ▸ h hc.1⟩
#align set.maps_image_to Set.maps_image_to

@[simp]
theorem maps_univ_to (f : α → β) (s : Set β) : MapsTo f univ s ↔ ∀ a, f a ∈ s :=
  ⟨fun h a => h (mem_univ _), fun h x _ => h x⟩
#align set.maps_univ_to Set.maps_univ_to

@[simp]
theorem maps_range_to (f : α → β) (g : γ → α) (s : Set β) :
    MapsTo f (range g) s ↔ MapsTo (f ∘ g) univ s := by rw [← image_univ, maps_image_to]
#align set.maps_range_to Set.maps_range_to

theorem surjective_maps_to_image_restrict (f : α → β) (s : Set α) :
    Surjective ((maps_to_image f s).restrict f s (f '' s)) := fun ⟨y, x, hs, hxy⟩ =>
  ⟨⟨x, hs⟩, Subtype.ext hxy⟩
#align set.surjective_maps_to_image_restrict Set.surjective_maps_to_image_restrict

theorem MapsTo.mem_iff (h : MapsTo f s t) (hc : MapsTo f (sᶜ) (tᶜ)) {x} : f x ∈ t ↔ x ∈ s :=
  ⟨fun ht => by_contra fun hs => hc hs ht, fun hx => h hx⟩
#align set.maps_to.mem_iff Set.MapsTo.mem_iff

/-! ### Restriction onto preimage -/


section

variable (t f)

/-- The restriction of a function onto the preimage of a set. -/
@[simps]
def restrictPreimage : f ⁻¹' t → t :=
  (Set.maps_to_preimage f t).restrict _ _ _
#align set.restrict_preimage Set.restrictPreimage

theorem range_restrict_preimage : range (t.restrictPreimage f) = coe ⁻¹' range f := by
  delta Set.restrictPreimage
  rw [maps_to.range_restrict, Set.image_preimage_eq_inter_range, Set.preimage_inter,
    Subtype.coe_preimage_self, Set.univ_inter]
#align set.range_restrict_preimage Set.range_restrict_preimage

end

/-! ### Injectivity on a set -/


/-- `f` is injective on `a` if the restriction of `f` to `a` is injective. -/
def InjOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃x₁ : α⦄, x₁ ∈ s → ∀ ⦃x₂ : α⦄, x₂ ∈ s → f x₁ = f x₂ → x₁ = x₂
#align set.inj_on Set.InjOn

theorem Subsingleton.inj_on (hs : s.Subsingleton) (f : α → β) : InjOn f s := fun x hx y hy h =>
  hs hx hy
#align set.subsingleton.inj_on Set.Subsingleton.inj_on

@[simp]
theorem inj_on_empty (f : α → β) : InjOn f ∅ :=
  subsingleton_empty.InjOn f
#align set.inj_on_empty Set.inj_on_empty

@[simp]
theorem inj_on_singleton (f : α → β) (a : α) : InjOn f {a} :=
  subsingleton_singleton.InjOn f
#align set.inj_on_singleton Set.inj_on_singleton

theorem InjOn.eq_iff {x y} (h : InjOn f s) (hx : x ∈ s) (hy : y ∈ s) : f x = f y ↔ x = y :=
  ⟨h hx hy, fun h => h ▸ rfl⟩
#align set.inj_on.eq_iff Set.InjOn.eq_iff

theorem InjOn.ne_iff {x y} (h : InjOn f s) (hx : x ∈ s) (hy : y ∈ s) : f x ≠ f y ↔ x ≠ y :=
  (h.eq_iff hx hy).Not
#align set.inj_on.ne_iff Set.InjOn.ne_iff

alias inj_on.ne_iff ↔ _ inj_on.ne

theorem InjOn.congr (h₁ : InjOn f₁ s) (h : EqOn f₁ f₂ s) : InjOn f₂ s := fun x hx y hy =>
  h hx ▸ h hy ▸ h₁ hx hy
#align set.inj_on.congr Set.InjOn.congr

theorem EqOn.inj_on_iff (H : EqOn f₁ f₂ s) : InjOn f₁ s ↔ InjOn f₂ s :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩
#align set.eq_on.inj_on_iff Set.EqOn.inj_on_iff

theorem InjOn.mono (h : s₁ ⊆ s₂) (ht : InjOn f s₂) : InjOn f s₁ := fun x hx y hy H =>
  ht (h hx) (h hy) H
#align set.inj_on.mono Set.InjOn.mono

theorem inj_on_union (h : Disjoint s₁ s₂) :
    InjOn f (s₁ ∪ s₂) ↔ InjOn f s₁ ∧ InjOn f s₂ ∧ ∀ x ∈ s₁, ∀ y ∈ s₂, f x ≠ f y := by
  refine' ⟨fun H => ⟨H.mono <| subset_union_left _ _, H.mono <| subset_union_right _ _, _⟩, _⟩
  · intro x hx y hy hxy
    obtain rfl : x = y
    exact H (Or.inl hx) (Or.inr hy) hxy
    exact h.le_bot ⟨hx, hy⟩
  · rintro ⟨h₁, h₂, h₁₂⟩
    rintro x (hx | hx) y (hy | hy) hxy
    exacts[h₁ hx hy hxy, (h₁₂ _ hx _ hy hxy).elim, (h₁₂ _ hy _ hx hxy.symm).elim, h₂ hx hy hxy]
#align set.inj_on_union Set.inj_on_union

theorem inj_on_insert {f : α → β} {s : Set α} {a : α} (has : a ∉ s) :
    Set.InjOn f (insert a s) ↔ Set.InjOn f s ∧ f a ∉ f '' s := by
  have : Disjoint s {a} := disjoint_iff_inf_le.mpr fun x ⟨hxs, (hxa : x = a)⟩ => has (hxa ▸ hxs)
  rw [← union_singleton, inj_on_union this]
  simp
#align set.inj_on_insert Set.inj_on_insert

theorem injective_iff_inj_on_univ : Injective f ↔ InjOn f univ :=
  ⟨fun h x hx y hy hxy => h hxy, fun h _ _ heq => h trivial trivial HEq⟩
#align set.injective_iff_inj_on_univ Set.injective_iff_inj_on_univ

theorem inj_on_of_injective (h : Injective f) (s : Set α) : InjOn f s := fun x hx y hy hxy => h hxy
#align set.inj_on_of_injective Set.inj_on_of_injective

alias inj_on_of_injective ← _root_.function.injective.inj_on

theorem InjOn.comp (hg : InjOn g t) (hf : InjOn f s) (h : MapsTo f s t) : InjOn (g ∘ f) s :=
  fun x hx y hy heq => hf hx hy <| hg (h hx) (h hy) HEq
#align set.inj_on.comp Set.InjOn.comp

theorem Function.Injective.inj_on_range (h : Injective (g ∘ f)) : InjOn g (range f) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ H
  exact congr_arg f (h H)
#align function.injective.inj_on_range Function.Injective.inj_on_range

theorem inj_on_iff_injective : InjOn f s ↔ Injective (s.restrict f) :=
  ⟨fun H a b h => Subtype.eq <| H a.2 b.2 h, fun H a as b bs h =>
    congr_arg Subtype.val <| @H ⟨a, as⟩ ⟨b, bs⟩ h⟩
#align set.inj_on_iff_injective Set.inj_on_iff_injective

alias inj_on_iff_injective ↔ inj_on.injective _

theorem MapsTo.restrict_inj (h : MapsTo f s t) : Injective (h.restrict f s t) ↔ InjOn f s := by
  rw [h.restrict_eq_cod_restrict, injective_cod_restrict, inj_on_iff_injective]
#align set.maps_to.restrict_inj Set.MapsTo.restrict_inj

theorem exists_inj_on_iff_injective [Nonempty β] :
    (∃ f : α → β, InjOn f s) ↔ ∃ f : s → β, Injective f :=
  ⟨fun ⟨f, hf⟩ => ⟨_, hf.Injective⟩, fun ⟨f, hf⟩ => by
    lift f to α → β using trivial
    exact ⟨f, inj_on_iff_injective.2 hf⟩⟩
#align set.exists_inj_on_iff_injective Set.exists_inj_on_iff_injective

theorem inj_on_preimage {B : Set (Set β)} (hB : B ⊆ 𝒫 range f) : InjOn (preimage f) B :=
  fun s hs t ht hst => (preimage_eq_preimage' (hB hs) (hB ht)).1 hst
#align set.inj_on_preimage Set.inj_on_preimage

theorem InjOn.mem_of_mem_image {x} (hf : InjOn f s) (hs : s₁ ⊆ s) (h : x ∈ s) (h₁ : f x ∈ f '' s₁) :
    x ∈ s₁ :=
  let ⟨x', h', Eq⟩ := h₁
  hf (hs h') h Eq ▸ h'
#align set.inj_on.mem_of_mem_image Set.InjOn.mem_of_mem_image

theorem InjOn.mem_image_iff {x} (hf : InjOn f s) (hs : s₁ ⊆ s) (hx : x ∈ s) :
    f x ∈ f '' s₁ ↔ x ∈ s₁ :=
  ⟨hf.mem_of_mem_image hs hx, mem_image_of_mem f⟩
#align set.inj_on.mem_image_iff Set.InjOn.mem_image_iff

theorem InjOn.preimage_image_inter (hf : InjOn f s) (hs : s₁ ⊆ s) : f ⁻¹' (f '' s₁) ∩ s = s₁ :=
  ext fun x => ⟨fun ⟨h₁, h₂⟩ => hf.mem_of_mem_image hs h₂ h₁, fun h => ⟨mem_image_of_mem _ h, hs h⟩⟩
#align set.inj_on.preimage_image_inter Set.InjOn.preimage_image_inter

theorem EqOn.cancel_left (h : s.EqOn (g ∘ f₁) (g ∘ f₂)) (hg : t.InjOn g) (hf₁ : s.MapsTo f₁ t)
    (hf₂ : s.MapsTo f₂ t) : s.EqOn f₁ f₂ := fun a ha => hg (hf₁ ha) (hf₂ ha) (h ha)
#align set.eq_on.cancel_left Set.EqOn.cancel_left

theorem InjOn.cancel_left (hg : t.InjOn g) (hf₁ : s.MapsTo f₁ t) (hf₂ : s.MapsTo f₂ t) :
    s.EqOn (g ∘ f₁) (g ∘ f₂) ↔ s.EqOn f₁ f₂ :=
  ⟨fun h => h.cancel_left hg hf₁ hf₂, EqOn.comp_left⟩
#align set.inj_on.cancel_left Set.InjOn.cancel_left

/-! ### Surjectivity on a set -/


/-- `f` is surjective from `a` to `b` if `b` is contained in the image of `a`. -/
def SurjOn (f : α → β) (s : Set α) (t : Set β) : Prop :=
  t ⊆ f '' s
#align set.surj_on Set.SurjOn

theorem SurjOn.subset_range (h : SurjOn f s t) : t ⊆ range f :=
  Subset.trans h <| image_subset_range f s
#align set.surj_on.subset_range Set.SurjOn.subset_range

theorem surj_on_iff_exists_map_subtype :
    SurjOn f s t ↔ ∃ (t' : Set β)(g : s → t'), t ⊆ t' ∧ Surjective g ∧ ∀ x : s, f x = g x :=
  ⟨fun h =>
    ⟨_, (maps_to_image f s).restrict f s _, h, surjective_maps_to_image_restrict _ _, fun _ => rfl⟩,
    fun ⟨t', g, htt', hg, hfg⟩ y hy =>
    let ⟨x, hx⟩ := hg ⟨y, htt' hy⟩
    ⟨x, x.2, by rw [hfg, hx, Subtype.coe_mk]⟩⟩
#align set.surj_on_iff_exists_map_subtype Set.surj_on_iff_exists_map_subtype

theorem surj_on_empty (f : α → β) (s : Set α) : SurjOn f s ∅ :=
  empty_subset _
#align set.surj_on_empty Set.surj_on_empty

theorem surj_on_image (f : α → β) (s : Set α) : SurjOn f s (f '' s) :=
  subset.rfl
#align set.surj_on_image Set.surj_on_image

theorem SurjOn.comap_nonempty (h : SurjOn f s t) (ht : t.Nonempty) : s.Nonempty :=
  (ht.mono h).of_image
#align set.surj_on.comap_nonempty Set.SurjOn.comap_nonempty

theorem SurjOn.congr (h : SurjOn f₁ s t) (H : EqOn f₁ f₂ s) : SurjOn f₂ s t := by
  rwa [surj_on, ← H.image_eq]
#align set.surj_on.congr Set.SurjOn.congr

theorem EqOn.surj_on_iff (h : EqOn f₁ f₂ s) : SurjOn f₁ s t ↔ SurjOn f₂ s t :=
  ⟨fun H => H.congr h, fun H => H.congr h.symm⟩
#align set.eq_on.surj_on_iff Set.EqOn.surj_on_iff

theorem SurjOn.mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) (hf : SurjOn f s₁ t₂) : SurjOn f s₂ t₁ :=
  Subset.trans ht <| Subset.trans hf <| image_subset _ hs
#align set.surj_on.mono Set.SurjOn.mono

theorem SurjOn.union (h₁ : SurjOn f s t₁) (h₂ : SurjOn f s t₂) : SurjOn f s (t₁ ∪ t₂) := fun x hx =>
  hx.elim (fun hx => h₁ hx) fun hx => h₂ hx
#align set.surj_on.union Set.SurjOn.union

theorem SurjOn.union_union (h₁ : SurjOn f s₁ t₁) (h₂ : SurjOn f s₂ t₂) :
    SurjOn f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
  (h₁.mono (subset_union_left _ _) (Subset.refl _)).union
    (h₂.mono (subset_union_right _ _) (Subset.refl _))
#align set.surj_on.union_union Set.SurjOn.union_union

theorem SurjOn.inter_inter (h₁ : SurjOn f s₁ t₁) (h₂ : SurjOn f s₂ t₂) (h : InjOn f (s₁ ∪ s₂)) :
    SurjOn f (s₁ ∩ s₂) (t₁ ∩ t₂) := by 
  intro y hy
  rcases h₁ hy.1 with ⟨x₁, hx₁, rfl⟩
  rcases h₂ hy.2 with ⟨x₂, hx₂, heq⟩
  obtain rfl : x₁ = x₂ := h (Or.inl hx₁) (Or.inr hx₂) HEq.symm
  exact mem_image_of_mem f ⟨hx₁, hx₂⟩
#align set.surj_on.inter_inter Set.SurjOn.inter_inter

theorem SurjOn.inter (h₁ : SurjOn f s₁ t) (h₂ : SurjOn f s₂ t) (h : InjOn f (s₁ ∪ s₂)) :
    SurjOn f (s₁ ∩ s₂) t :=
  inter_self t ▸ h₁.inter_inter h₂ h
#align set.surj_on.inter Set.SurjOn.inter

theorem SurjOn.comp (hg : SurjOn g t p) (hf : SurjOn f s t) : SurjOn (g ∘ f) s p :=
  Subset.trans hg <| Subset.trans (image_subset g hf) <| image_comp g f s ▸ Subset.refl _
#align set.surj_on.comp Set.SurjOn.comp

theorem surjective_iff_surj_on_univ : Surjective f ↔ SurjOn f univ univ := by
  simp [surjective, surj_on, subset_def]
#align set.surjective_iff_surj_on_univ Set.surjective_iff_surj_on_univ

theorem surj_on_iff_surjective : SurjOn f s univ ↔ Surjective (s.restrict f) :=
  ⟨fun H b =>
    let ⟨a, as, e⟩ := @H b trivial
    ⟨⟨a, as⟩, e⟩,
    fun H b _ =>
    let ⟨⟨a, as⟩, e⟩ := H b
    ⟨a, as, e⟩⟩
#align set.surj_on_iff_surjective Set.surj_on_iff_surjective

theorem SurjOn.image_eq_of_maps_to (h₁ : SurjOn f s t) (h₂ : MapsTo f s t) : f '' s = t :=
  eq_of_subset_of_subset h₂.image_subset h₁
#align set.surj_on.image_eq_of_maps_to Set.SurjOn.image_eq_of_maps_to

theorem image_eq_iff_surj_on_maps_to : f '' s = t ↔ s.SurjOn f t ∧ s.MapsTo f t := by
  refine' ⟨_, fun h => h.1.image_eq_of_maps_to h.2⟩
  rintro rfl
  exact ⟨s.surj_on_image f, s.maps_to_image f⟩
#align set.image_eq_iff_surj_on_maps_to Set.image_eq_iff_surj_on_maps_to

theorem SurjOn.maps_to_compl (h : SurjOn f s t) (h' : Injective f) : MapsTo f (sᶜ) (tᶜ) :=
  fun x hs ht =>
  let ⟨x', hx', HEq⟩ := h ht
  hs <| h' HEq ▸ hx'
#align set.surj_on.maps_to_compl Set.SurjOn.maps_to_compl

theorem MapsTo.surj_on_compl (h : MapsTo f s t) (h' : Surjective f) : SurjOn f (sᶜ) (tᶜ) :=
  h'.forall.2 fun x ht => (mem_image_of_mem _) fun hs => ht (h hs)
#align set.maps_to.surj_on_compl Set.MapsTo.surj_on_compl

theorem EqOn.cancel_right (hf : s.EqOn (g₁ ∘ f) (g₂ ∘ f)) (hf' : s.SurjOn f t) : t.EqOn g₁ g₂ := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := hf' hb
  exact hf ha
#align set.eq_on.cancel_right Set.EqOn.cancel_right

theorem SurjOn.cancel_right (hf : s.SurjOn f t) (hf' : s.MapsTo f t) :
    s.EqOn (g₁ ∘ f) (g₂ ∘ f) ↔ t.EqOn g₁ g₂ :=
  ⟨fun h => h.cancel_right hf, fun h => h.compRight hf'⟩
#align set.surj_on.cancel_right Set.SurjOn.cancel_right

theorem eq_on_comp_right_iff : s.EqOn (g₁ ∘ f) (g₂ ∘ f) ↔ (f '' s).EqOn g₁ g₂ :=
  (s.surj_on_image f).cancel_right <| s.maps_to_image f
#align set.eq_on_comp_right_iff Set.eq_on_comp_right_iff

/-! ### Bijectivity -/


/-- `f` is bijective from `s` to `t` if `f` is injective on `s` and `f '' s = t`. -/
def BijOn (f : α → β) (s : Set α) (t : Set β) : Prop :=
  MapsTo f s t ∧ InjOn f s ∧ SurjOn f s t
#align set.bij_on Set.BijOn

theorem BijOn.maps_to (h : BijOn f s t) : MapsTo f s t :=
  h.left
#align set.bij_on.maps_to Set.BijOn.maps_to

theorem BijOn.inj_on (h : BijOn f s t) : InjOn f s :=
  h.right.left
#align set.bij_on.inj_on Set.BijOn.inj_on

theorem BijOn.surj_on (h : BijOn f s t) : SurjOn f s t :=
  h.right.right
#align set.bij_on.surj_on Set.BijOn.surj_on

theorem BijOn.mk (h₁ : MapsTo f s t) (h₂ : InjOn f s) (h₃ : SurjOn f s t) : BijOn f s t :=
  ⟨h₁, h₂, h₃⟩
#align set.bij_on.mk Set.BijOn.mk

theorem bij_on_empty (f : α → β) : BijOn f ∅ ∅ :=
  ⟨maps_to_empty f ∅, inj_on_empty f, surj_on_empty f ∅⟩
#align set.bij_on_empty Set.bij_on_empty

theorem BijOn.inter_maps_to (h₁ : BijOn f s₁ t₁) (h₂ : MapsTo f s₂ t₂) (h₃ : s₁ ∩ f ⁻¹' t₂ ⊆ s₂) :
    BijOn f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
  ⟨h₁.MapsTo.inter_inter h₂, h₁.InjOn.mono <| inter_subset_left _ _, fun y hy =>
    let ⟨x, hx, hxy⟩ := h₁.SurjOn hy.1
    ⟨x, ⟨hx, h₃ ⟨hx, hxy.symm.recOn hy.2⟩⟩, hxy⟩⟩
#align set.bij_on.inter_maps_to Set.BijOn.inter_maps_to

theorem MapsTo.inter_bij_on (h₁ : MapsTo f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h₃ : s₂ ∩ f ⁻¹' t₁ ⊆ s₁) :
    BijOn f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
  inter_comm s₂ s₁ ▸ inter_comm t₂ t₁ ▸ h₂.inter_maps_to h₁ h₃
#align set.maps_to.inter_bij_on Set.MapsTo.inter_bij_on

theorem BijOn.inter (h₁ : BijOn f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h : InjOn f (s₁ ∪ s₂)) :
    BijOn f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
  ⟨h₁.MapsTo.inter_inter h₂.MapsTo, h₁.InjOn.mono <| inter_subset_left _ _,
    h₁.SurjOn.inter_inter h₂.SurjOn h⟩
#align set.bij_on.inter Set.BijOn.inter

theorem BijOn.union (h₁ : BijOn f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h : InjOn f (s₁ ∪ s₂)) :
    BijOn f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
  ⟨h₁.MapsTo.union_union h₂.MapsTo, h, h₁.SurjOn.union_union h₂.SurjOn⟩
#align set.bij_on.union Set.BijOn.union

theorem BijOn.subset_range (h : BijOn f s t) : t ⊆ range f :=
  h.SurjOn.subset_range
#align set.bij_on.subset_range Set.BijOn.subset_range

theorem InjOn.bij_on_image (h : InjOn f s) : BijOn f s (f '' s) :=
  BijOn.mk (maps_to_image f s) h (Subset.refl _)
#align set.inj_on.bij_on_image Set.InjOn.bij_on_image

theorem BijOn.congr (h₁ : BijOn f₁ s t) (h : EqOn f₁ f₂ s) : BijOn f₂ s t :=
  BijOn.mk (h₁.MapsTo.congr h) (h₁.InjOn.congr h) (h₁.SurjOn.congr h)
#align set.bij_on.congr Set.BijOn.congr

theorem EqOn.bij_on_iff (H : EqOn f₁ f₂ s) : BijOn f₁ s t ↔ BijOn f₂ s t :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩
#align set.eq_on.bij_on_iff Set.EqOn.bij_on_iff

theorem BijOn.image_eq (h : BijOn f s t) : f '' s = t :=
  h.SurjOn.image_eq_of_maps_to h.MapsTo
#align set.bij_on.image_eq Set.BijOn.image_eq

theorem BijOn.comp (hg : BijOn g t p) (hf : BijOn f s t) : BijOn (g ∘ f) s p :=
  BijOn.mk (hg.MapsTo.comp hf.MapsTo) (hg.InjOn.comp hf.InjOn hf.MapsTo) (hg.SurjOn.comp hf.SurjOn)
#align set.bij_on.comp Set.BijOn.comp

theorem BijOn.bijective (h : BijOn f s t) : Bijective (h.MapsTo.restrict f s t) :=
  ⟨fun x y h' => Subtype.ext <| h.InjOn x.2 y.2 <| Subtype.ext_iff.1 h', fun ⟨y, hy⟩ =>
    let ⟨x, hx, hxy⟩ := h.SurjOn hy
    ⟨⟨x, hx⟩, Subtype.eq hxy⟩⟩
#align set.bij_on.bijective Set.BijOn.bijective

theorem bijective_iff_bij_on_univ : Bijective f ↔ BijOn f univ univ :=
  Iff.intro
    (fun h =>
      let ⟨inj, surj⟩ := h
      ⟨maps_to_univ f _, inj.InjOn _, Iff.mp surjective_iff_surj_on_univ surj⟩)
    fun h =>
    let ⟨map, inj, surj⟩ := h
    ⟨Iff.mpr injective_iff_inj_on_univ inj, Iff.mpr surjective_iff_surj_on_univ surj⟩
#align set.bijective_iff_bij_on_univ Set.bijective_iff_bij_on_univ

theorem BijOn.compl (hst : BijOn f s t) (hf : Bijective f) : BijOn f (sᶜ) (tᶜ) :=
  ⟨hst.SurjOn.maps_to_compl hf.1, hf.1.InjOn _, hst.MapsTo.surj_on_compl hf.2⟩
#align set.bij_on.compl Set.BijOn.compl

/-! ### left inverse -/


/-- `g` is a left inverse to `f` on `a` means that `g (f x) = x` for all `x ∈ a`. -/
def LeftInvOn (f' : β → α) (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ s → f' (f x) = x
#align set.left_inv_on Set.LeftInvOn

theorem LeftInvOn.eq_on (h : LeftInvOn f' f s) : EqOn (f' ∘ f) id s :=
  h
#align set.left_inv_on.eq_on Set.LeftInvOn.eq_on

theorem LeftInvOn.eq (h : LeftInvOn f' f s) {x} (hx : x ∈ s) : f' (f x) = x :=
  h hx
#align set.left_inv_on.eq Set.LeftInvOn.eq

theorem LeftInvOn.congr_left (h₁ : LeftInvOn f₁' f s) {t : Set β} (h₁' : MapsTo f s t)
    (heq : EqOn f₁' f₂' t) : LeftInvOn f₂' f s := fun x hx => HEq (h₁' hx) ▸ h₁ hx
#align set.left_inv_on.congr_left Set.LeftInvOn.congr_left

theorem LeftInvOn.congr_right (h₁ : LeftInvOn f₁' f₁ s) (heq : EqOn f₁ f₂ s) : LeftInvOn f₁' f₂ s :=
  fun x hx => HEq hx ▸ h₁ hx
#align set.left_inv_on.congr_right Set.LeftInvOn.congr_right

theorem LeftInvOn.inj_on (h : LeftInvOn f₁' f s) : InjOn f s := fun x₁ h₁ x₂ h₂ heq =>
  calc
    x₁ = f₁' (f x₁) := Eq.symm <| h h₁
    _ = f₁' (f x₂) := congr_arg f₁' HEq
    _ = x₂ := h h₂
    
#align set.left_inv_on.inj_on Set.LeftInvOn.inj_on

theorem LeftInvOn.surj_on (h : LeftInvOn f' f s) (hf : MapsTo f s t) : SurjOn f' t s := fun x hx =>
  ⟨f x, hf hx, h hx⟩
#align set.left_inv_on.surj_on Set.LeftInvOn.surj_on

theorem LeftInvOn.maps_to (h : LeftInvOn f' f s) (hf : SurjOn f s t) : MapsTo f' t s := fun y hy =>
  by 
  let ⟨x, hs, hx⟩ := hf hy
  rwa [← hx, h hs]
#align set.left_inv_on.maps_to Set.LeftInvOn.maps_to

theorem LeftInvOn.comp (hf' : LeftInvOn f' f s) (hg' : LeftInvOn g' g t) (hf : MapsTo f s t) :
    LeftInvOn (f' ∘ g') (g ∘ f) s := fun x h =>
  calc
    (f' ∘ g') ((g ∘ f) x) = f' (f x) := congr_arg f' (hg' (hf h))
    _ = x := hf' h
    
#align set.left_inv_on.comp Set.LeftInvOn.comp

theorem LeftInvOn.mono (hf : LeftInvOn f' f s) (ht : s₁ ⊆ s) : LeftInvOn f' f s₁ := fun x hx =>
  hf (ht hx)
#align set.left_inv_on.mono Set.LeftInvOn.mono

theorem LeftInvOn.image_inter' (hf : LeftInvOn f' f s) : f '' (s₁ ∩ s) = f' ⁻¹' s₁ ∩ f '' s := by
  apply subset.antisymm
  · rintro _ ⟨x, ⟨h₁, h⟩, rfl⟩
    exact ⟨by rwa [mem_preimage, hf h], mem_image_of_mem _ h⟩
  · rintro _ ⟨h₁, ⟨x, h, rfl⟩⟩
    exact mem_image_of_mem _ ⟨by rwa [← hf h], h⟩
#align set.left_inv_on.image_inter' Set.LeftInvOn.image_inter'

theorem LeftInvOn.image_inter (hf : LeftInvOn f' f s) : f '' (s₁ ∩ s) = f' ⁻¹' (s₁ ∩ s) ∩ f '' s :=
  by 
  rw [hf.image_inter']
  refine' subset.antisymm _ (inter_subset_inter_left _ (preimage_mono <| inter_subset_left _ _))
  rintro _ ⟨h₁, x, hx, rfl⟩; exact ⟨⟨h₁, by rwa [hf hx]⟩, mem_image_of_mem _ hx⟩
#align set.left_inv_on.image_inter Set.LeftInvOn.image_inter

theorem LeftInvOn.image_image (hf : LeftInvOn f' f s) : f' '' (f '' s) = s := by
  rw [image_image, image_congr hf, image_id']
#align set.left_inv_on.image_image Set.LeftInvOn.image_image

theorem LeftInvOn.image_image' (hf : LeftInvOn f' f s) (hs : s₁ ⊆ s) : f' '' (f '' s₁) = s₁ :=
  (hf.mono hs).image_image
#align set.left_inv_on.image_image' Set.LeftInvOn.image_image'

/-! ### Right inverse -/


/-- `g` is a right inverse to `f` on `b` if `f (g x) = x` for all `x ∈ b`. -/
@[reducible]
def RightInvOn (f' : β → α) (f : α → β) (t : Set β) : Prop :=
  LeftInvOn f f' t
#align set.right_inv_on Set.RightInvOn

theorem RightInvOn.eq_on (h : RightInvOn f' f t) : EqOn (f ∘ f') id t :=
  h
#align set.right_inv_on.eq_on Set.RightInvOn.eq_on

theorem RightInvOn.eq (h : RightInvOn f' f t) {y} (hy : y ∈ t) : f (f' y) = y :=
  h hy
#align set.right_inv_on.eq Set.RightInvOn.eq

theorem LeftInvOn.right_inv_on_image (h : LeftInvOn f' f s) : RightInvOn f' f (f '' s) :=
  fun y ⟨x, hx, Eq⟩ => Eq ▸ congr_arg f <| h.Eq hx
#align set.left_inv_on.right_inv_on_image Set.LeftInvOn.right_inv_on_image

theorem RightInvOn.congr_left (h₁ : RightInvOn f₁' f t) (heq : EqOn f₁' f₂' t) :
    RightInvOn f₂' f t :=
  h₁.congr_right HEq
#align set.right_inv_on.congr_left Set.RightInvOn.congr_left

theorem RightInvOn.congr_right (h₁ : RightInvOn f' f₁ t) (hg : MapsTo f' t s) (heq : EqOn f₁ f₂ s) :
    RightInvOn f' f₂ t :=
  LeftInvOn.congr_left h₁ hg HEq
#align set.right_inv_on.congr_right Set.RightInvOn.congr_right

theorem RightInvOn.surj_on (hf : RightInvOn f' f t) (hf' : MapsTo f' t s) : SurjOn f s t :=
  hf.SurjOn hf'
#align set.right_inv_on.surj_on Set.RightInvOn.surj_on

theorem RightInvOn.maps_to (h : RightInvOn f' f t) (hf : SurjOn f' t s) : MapsTo f s t :=
  h.MapsTo hf
#align set.right_inv_on.maps_to Set.RightInvOn.maps_to

theorem RightInvOn.comp (hf : RightInvOn f' f t) (hg : RightInvOn g' g p) (g'pt : MapsTo g' p t) :
    RightInvOn (f' ∘ g') (g ∘ f) p :=
  hg.comp hf g'pt
#align set.right_inv_on.comp Set.RightInvOn.comp

theorem RightInvOn.mono (hf : RightInvOn f' f t) (ht : t₁ ⊆ t) : RightInvOn f' f t₁ :=
  hf.mono ht
#align set.right_inv_on.mono Set.RightInvOn.mono

theorem InjOn.right_inv_on_of_left_inv_on (hf : InjOn f s) (hf' : LeftInvOn f f' t)
    (h₁ : MapsTo f s t) (h₂ : MapsTo f' t s) : RightInvOn f f' s := fun x h =>
  hf (h₂ <| h₁ h) h (hf' (h₁ h))
#align set.inj_on.right_inv_on_of_left_inv_on Set.InjOn.right_inv_on_of_left_inv_on

theorem eq_on_of_left_inv_on_of_right_inv_on (h₁ : LeftInvOn f₁' f s) (h₂ : RightInvOn f₂' f t)
    (h : MapsTo f₂' t s) : EqOn f₁' f₂' t := fun y hy =>
  calc
    f₁' y = (f₁' ∘ f ∘ f₂') y := congr_arg f₁' (h₂ hy).symm
    _ = f₂' y := h₁ (h hy)
    
#align set.eq_on_of_left_inv_on_of_right_inv_on Set.eq_on_of_left_inv_on_of_right_inv_on

theorem SurjOn.left_inv_on_of_right_inv_on (hf : SurjOn f s t) (hf' : RightInvOn f f' s) :
    LeftInvOn f f' t := fun y hy => by 
  let ⟨x, hx, HEq⟩ := hf hy
  rw [← HEq, hf' hx]
#align set.surj_on.left_inv_on_of_right_inv_on Set.SurjOn.left_inv_on_of_right_inv_on

/-! ### Two-side inverses -/


/-- `g` is an inverse to `f` viewed as a map from `a` to `b` -/
def InvOn (g : β → α) (f : α → β) (s : Set α) (t : Set β) : Prop :=
  LeftInvOn g f s ∧ RightInvOn g f t
#align set.inv_on Set.InvOn

theorem InvOn.symm (h : InvOn f' f s t) : InvOn f f' t s :=
  ⟨h.right, h.left⟩
#align set.inv_on.symm Set.InvOn.symm

theorem InvOn.mono (h : InvOn f' f s t) (hs : s₁ ⊆ s) (ht : t₁ ⊆ t) : InvOn f' f s₁ t₁ :=
  ⟨h.1.mono hs, h.2.mono ht⟩
#align set.inv_on.mono Set.InvOn.mono

/-- If functions `f'` and `f` are inverse on `s` and `t`, `f` maps `s` into `t`, and `f'` maps `t`
into `s`, then `f` is a bijection between `s` and `t`. The `maps_to` arguments can be deduced from
`surj_on` statements using `left_inv_on.maps_to` and `right_inv_on.maps_to`. -/
theorem InvOn.bij_on (h : InvOn f' f s t) (hf : MapsTo f s t) (hf' : MapsTo f' t s) : BijOn f s t :=
  ⟨hf, h.left.InjOn, h.right.SurjOn hf'⟩
#align set.inv_on.bij_on Set.InvOn.bij_on

end Set

/-! ### `inv_fun_on` is a left/right inverse -/


namespace Function

variable [Nonempty α] {s : Set α} {f : α → β} {a : α} {b : β}

attribute [local instance] Classical.propDecidable

/-- Construct the inverse for a function `f` on domain `s`. This function is a right inverse of `f`
on `f '' s`. For a computable version, see `function.injective.inv_of_mem_range`. -/
noncomputable def invFunOn (f : α → β) (s : Set α) (b : β) : α :=
  if h : ∃ a, a ∈ s ∧ f a = b then Classical.choose h else Classical.choice ‹Nonempty α›
#align function.inv_fun_on Function.invFunOn

theorem inv_fun_on_pos (h : ∃ a ∈ s, f a = b) : invFunOn f s b ∈ s ∧ f (invFunOn f s b) = b := by
  rw [bex_def] at h <;> rw [inv_fun_on, dif_pos h] <;> exact Classical.choose_spec h
#align function.inv_fun_on_pos Function.inv_fun_on_pos

theorem inv_fun_on_mem (h : ∃ a ∈ s, f a = b) : invFunOn f s b ∈ s :=
  (inv_fun_on_pos h).left
#align function.inv_fun_on_mem Function.inv_fun_on_mem

theorem inv_fun_on_eq (h : ∃ a ∈ s, f a = b) : f (invFunOn f s b) = b :=
  (inv_fun_on_pos h).right
#align function.inv_fun_on_eq Function.inv_fun_on_eq

theorem inv_fun_on_neg (h : ¬∃ a ∈ s, f a = b) : invFunOn f s b = Classical.choice ‹Nonempty α› :=
  by rw [bex_def] at h <;> rw [inv_fun_on, dif_neg h]
#align function.inv_fun_on_neg Function.inv_fun_on_neg

@[simp]
theorem inv_fun_on_apply_mem (h : a ∈ s) : invFunOn f s (f a) ∈ s :=
  inv_fun_on_mem ⟨a, h, rfl⟩
#align function.inv_fun_on_apply_mem Function.inv_fun_on_apply_mem

theorem inv_fun_on_apply_eq (h : a ∈ s) : f (invFunOn f s (f a)) = f a :=
  inv_fun_on_eq ⟨a, h, rfl⟩
#align function.inv_fun_on_apply_eq Function.inv_fun_on_apply_eq

end Function

open Function

namespace Set

variable {s s₁ s₂ : Set α} {t : Set β} {f : α → β}

theorem InjOn.left_inv_on_inv_fun_on [Nonempty α] (h : InjOn f s) : LeftInvOn (invFunOn f s) f s :=
  fun a ha => h (inv_fun_on_apply_mem ha) ha (inv_fun_on_apply_eq ha)
#align set.inj_on.left_inv_on_inv_fun_on Set.InjOn.left_inv_on_inv_fun_on

theorem InjOn.inv_fun_on_image [Nonempty α] (h : InjOn f s₂) (ht : s₁ ⊆ s₂) :
    invFunOn f s₂ '' (f '' s₁) = s₁ :=
  h.left_inv_on_inv_fun_on.image_image' ht
#align set.inj_on.inv_fun_on_image Set.InjOn.inv_fun_on_image

theorem SurjOn.right_inv_on_inv_fun_on [Nonempty α] (h : SurjOn f s t) :
    RightInvOn (invFunOn f s) f t := fun y hy => inv_fun_on_eq <| mem_image_iff_bex.1 <| h hy
#align set.surj_on.right_inv_on_inv_fun_on Set.SurjOn.right_inv_on_inv_fun_on

theorem BijOn.inv_on_inv_fun_on [Nonempty α] (h : BijOn f s t) : InvOn (invFunOn f s) f s t :=
  ⟨h.InjOn.left_inv_on_inv_fun_on, h.SurjOn.right_inv_on_inv_fun_on⟩
#align set.bij_on.inv_on_inv_fun_on Set.BijOn.inv_on_inv_fun_on

theorem SurjOn.inv_on_inv_fun_on [Nonempty α] (h : SurjOn f s t) :
    InvOn (invFunOn f s) f (invFunOn f s '' t) t := by
  refine' ⟨_, h.right_inv_on_inv_fun_on⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [h.right_inv_on_inv_fun_on hy]
#align set.surj_on.inv_on_inv_fun_on Set.SurjOn.inv_on_inv_fun_on

theorem SurjOn.maps_to_inv_fun_on [Nonempty α] (h : SurjOn f s t) : MapsTo (invFunOn f s) t s :=
  fun y hy => mem_preimage.2 <| inv_fun_on_mem <| mem_image_iff_bex.1 <| h hy
#align set.surj_on.maps_to_inv_fun_on Set.SurjOn.maps_to_inv_fun_on

theorem SurjOn.bij_on_subset [Nonempty α] (h : SurjOn f s t) : BijOn f (invFunOn f s '' t) t := by
  refine' h.inv_on_inv_fun_on.bij_on _ (maps_to_image _ _)
  rintro _ ⟨y, hy, rfl⟩
  rwa [h.right_inv_on_inv_fun_on hy]
#align set.surj_on.bij_on_subset Set.SurjOn.bij_on_subset

/- ./././Mathport/Syntax/Translate/Basic.lean:631:2: warning: expanding binder collection (s' «expr ⊆ » s) -/
theorem surj_on_iff_exists_bij_on_subset : SurjOn f s t ↔ ∃ (s' : _)(_ : s' ⊆ s), BijOn f s' t := by
  constructor
  · rcases eq_empty_or_nonempty t with (rfl | ht)
    · exact fun _ => ⟨∅, empty_subset _, bij_on_empty f⟩
    · intro h
      haveI : Nonempty α := ⟨Classical.choose (h.comap_nonempty ht)⟩
      exact ⟨_, h.maps_to_inv_fun_on.image_subset, h.bij_on_subset⟩
  · rintro ⟨s', hs', hfs'⟩
    exact hfs'.surj_on.mono hs' (subset.refl _)
#align set.surj_on_iff_exists_bij_on_subset Set.surj_on_iff_exists_bij_on_subset

theorem preimage_inv_fun_of_mem [n : Nonempty α] {f : α → β} (hf : Injective f) {s : Set α}
    (h : Classical.choice n ∈ s) : invFun f ⁻¹' s = f '' s ∪ range fᶜ := by
  ext x
  rcases em (x ∈ range f) with (⟨a, rfl⟩ | hx)
  · simp [left_inverse_inv_fun hf _, hf.mem_set_image]
  · simp [mem_preimage, inv_fun_neg hx, h, hx]
#align set.preimage_inv_fun_of_mem Set.preimage_inv_fun_of_mem

theorem preimage_inv_fun_of_not_mem [n : Nonempty α] {f : α → β} (hf : Injective f) {s : Set α}
    (h : Classical.choice n ∉ s) : invFun f ⁻¹' s = f '' s := by
  ext x
  rcases em (x ∈ range f) with (⟨a, rfl⟩ | hx)
  · rw [mem_preimage, left_inverse_inv_fun hf, hf.mem_set_image]
  · have : x ∉ f '' s := fun h' => hx (image_subset_range _ _ h')
    simp only [mem_preimage, inv_fun_neg hx, h, this]
#align set.preimage_inv_fun_of_not_mem Set.preimage_inv_fun_of_not_mem

end Set

/-! ### Monotone -/


namespace Monotone

variable [Preorder α] [Preorder β] {f : α → β}

protected theorem restrict (h : Monotone f) (s : Set α) : Monotone (s.restrict f) := fun x y hxy =>
  h hxy
#align monotone.restrict Monotone.restrict

protected theorem cod_restrict (h : Monotone f) {s : Set β} (hs : ∀ x, f x ∈ s) :
    Monotone (s.codRestrict f hs) :=
  h
#align monotone.cod_restrict Monotone.cod_restrict

protected theorem range_factorization (h : Monotone f) : Monotone (Set.rangeFactorization f) :=
  h
#align monotone.range_factorization Monotone.range_factorization

end Monotone

/-! ### Piecewise defined function -/


namespace Set

variable {δ : α → Sort y} (s : Set α) (f g : ∀ i, δ i)

@[simp]
theorem piecewise_empty [∀ i : α, Decidable (i ∈ (∅ : Set α))] : piecewise ∅ f g = g := by
  ext i
  simp [piecewise]
#align set.piecewise_empty Set.piecewise_empty

@[simp]
theorem piecewise_univ [∀ i : α, Decidable (i ∈ (Set.univ : Set α))] : piecewise Set.univ f g = f :=
  by 
  ext i
  simp [piecewise]
#align set.piecewise_univ Set.piecewise_univ

@[simp]
theorem piecewise_insert_self {j : α} [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g j = f j := by simp [piecewise]
#align set.piecewise_insert_self Set.piecewise_insert_self

variable [∀ j, Decidable (j ∈ s)]

instance Compl.decidableMem (j : α) : Decidable (j ∈ sᶜ) :=
  Not.decidable
#align set.compl.decidable_mem Set.Compl.decidableMem

theorem piecewise_insert [DecidableEq α] (j : α) [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g = Function.update (s.piecewise f g) j (f j) := by
  simp [piecewise]
  ext i
  by_cases h : i = j
  · rw [h]
    simp
  · by_cases h' : i ∈ s <;> simp [h, h']
#align set.piecewise_insert Set.piecewise_insert

@[simp]
theorem piecewise_eq_of_mem {i : α} (hi : i ∈ s) : s.piecewise f g i = f i :=
  if_pos hi
#align set.piecewise_eq_of_mem Set.piecewise_eq_of_mem

@[simp]
theorem piecewise_eq_of_not_mem {i : α} (hi : i ∉ s) : s.piecewise f g i = g i :=
  if_neg hi
#align set.piecewise_eq_of_not_mem Set.piecewise_eq_of_not_mem

theorem piecewise_singleton (x : α) [∀ y, Decidable (y ∈ ({x} : Set α))] [DecidableEq α]
    (f g : α → β) : piecewise {x} f g = Function.update g x (f x) := by
  ext y
  by_cases hy : y = x
  · subst y
    simp
  · simp [hy]
#align set.piecewise_singleton Set.piecewise_singleton

theorem piecewise_eq_on (f g : α → β) : EqOn (s.piecewise f g) f s := fun _ =>
  piecewise_eq_of_mem _ _ _
#align set.piecewise_eq_on Set.piecewise_eq_on

theorem piecewise_eq_on_compl (f g : α → β) : EqOn (s.piecewise f g) g (sᶜ) := fun _ =>
  piecewise_eq_of_not_mem _ _ _
#align set.piecewise_eq_on_compl Set.piecewise_eq_on_compl

/- ./././Mathport/Syntax/Translate/Basic.lean:631:2: warning: expanding binder collection (i «expr ∉ » s) -/
theorem piecewise_le {δ : α → Type _} [∀ i, Preorder (δ i)] {s : Set α} [∀ j, Decidable (j ∈ s)]
    {f₁ f₂ g : ∀ i, δ i} (h₁ : ∀ i ∈ s, f₁ i ≤ g i) (h₂ : ∀ (i) (_ : i ∉ s), f₂ i ≤ g i) :
    s.piecewise f₁ f₂ ≤ g := fun i => if h : i ∈ s then by simp [*] else by simp [*]
#align set.piecewise_le Set.piecewise_le

/- ./././Mathport/Syntax/Translate/Basic.lean:631:2: warning: expanding binder collection (i «expr ∉ » s) -/
theorem le_piecewise {δ : α → Type _} [∀ i, Preorder (δ i)] {s : Set α} [∀ j, Decidable (j ∈ s)]
    {f₁ f₂ g : ∀ i, δ i} (h₁ : ∀ i ∈ s, g i ≤ f₁ i) (h₂ : ∀ (i) (_ : i ∉ s), g i ≤ f₂ i) :
    g ≤ s.piecewise f₁ f₂ :=
  @piecewise_le α (fun i => (δ i)ᵒᵈ) _ s _ _ _ _ h₁ h₂
#align set.le_piecewise Set.le_piecewise

/- ./././Mathport/Syntax/Translate/Basic.lean:631:2: warning: expanding binder collection (i «expr ∉ » s) -/
theorem piecewise_le_piecewise {δ : α → Type _} [∀ i, Preorder (δ i)] {s : Set α}
    [∀ j, Decidable (j ∈ s)] {f₁ f₂ g₁ g₂ : ∀ i, δ i} (h₁ : ∀ i ∈ s, f₁ i ≤ g₁ i)
    (h₂ : ∀ (i) (_ : i ∉ s), f₂ i ≤ g₂ i) : s.piecewise f₁ f₂ ≤ s.piecewise g₁ g₂ := by
  apply piecewise_le <;> intros <;> simp [*]
#align set.piecewise_le_piecewise Set.piecewise_le_piecewise

@[simp]
theorem piecewise_insert_of_ne {i j : α} (h : i ≠ j) [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g i = s.piecewise f g i := by simp [piecewise, h]
#align set.piecewise_insert_of_ne Set.piecewise_insert_of_ne

@[simp]
theorem piecewise_compl [∀ i, Decidable (i ∈ sᶜ)] : sᶜ.piecewise f g = s.piecewise g f :=
  funext fun x => if hx : x ∈ s then by simp [hx] else by simp [hx]
#align set.piecewise_compl Set.piecewise_compl

@[simp]
theorem piecewise_range_comp {ι : Sort _} (f : ι → α) [∀ j, Decidable (j ∈ range f)]
    (g₁ g₂ : α → β) : (range f).piecewise g₁ g₂ ∘ f = g₁ ∘ f :=
  eq_on.comp_eq <| piecewise_eq_on _ _ _
#align set.piecewise_range_comp Set.piecewise_range_comp

theorem MapsTo.piecewise_ite {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {f₁ f₂ : α → β}
    [∀ i, Decidable (i ∈ s)] (h₁ : MapsTo f₁ (s₁ ∩ s) (t₁ ∩ t))
    (h₂ : MapsTo f₂ (s₂ ∩ sᶜ) (t₂ ∩ tᶜ)) : MapsTo (s.piecewise f₁ f₂) (s.ite s₁ s₂) (t.ite t₁ t₂) :=
  by 
  refine' (h₁.congr _).union_union (h₂.congr _)
  exacts[(piecewise_eq_on s f₁ f₂).symm.mono (inter_subset_right _ _),
    (piecewise_eq_on_compl s f₁ f₂).symm.mono (inter_subset_right _ _)]
#align set.maps_to.piecewise_ite Set.MapsTo.piecewise_ite

theorem eq_on_piecewise {f f' g : α → β} {t} :
    EqOn (s.piecewise f f') g t ↔ EqOn f g (t ∩ s) ∧ EqOn f' g (t ∩ sᶜ) := by
  simp only [eq_on, ← forall_and]
  refine' forall_congr' fun a => _; by_cases a ∈ s <;> simp [*]
#align set.eq_on_piecewise Set.eq_on_piecewise

theorem EqOn.piecewise_ite' {f f' g : α → β} {t t'} (h : EqOn f g (t ∩ s))
    (h' : EqOn f' g (t' ∩ sᶜ)) : EqOn (s.piecewise f f') g (s.ite t t') := by
  simp [eq_on_piecewise, *]
#align set.eq_on.piecewise_ite' Set.EqOn.piecewise_ite'

theorem EqOn.piecewise_ite {f f' g : α → β} {t t'} (h : EqOn f g t) (h' : EqOn f' g t') :
    EqOn (s.piecewise f f') g (s.ite t t') :=
  (h.mono (inter_subset_left _ _)).piecewise_ite' s (h'.mono (inter_subset_left _ _))
#align set.eq_on.piecewise_ite Set.EqOn.piecewise_ite

theorem piecewise_preimage (f g : α → β) (t) : s.piecewise f g ⁻¹' t = s.ite (f ⁻¹' t) (g ⁻¹' t) :=
  ext fun x => by by_cases x ∈ s <;> simp [*, Set.ite]
#align set.piecewise_preimage Set.piecewise_preimage

theorem apply_piecewise {δ' : α → Sort _} (h : ∀ i, δ i → δ' i) {x : α} :
    h x (s.piecewise f g x) = s.piecewise (fun x => h x (f x)) (fun x => h x (g x)) x := by
  by_cases hx : x ∈ s <;> simp [hx]
#align set.apply_piecewise Set.apply_piecewise

theorem apply_piecewise₂ {δ' δ'' : α → Sort _} (f' g' : ∀ i, δ' i) (h : ∀ i, δ i → δ' i → δ'' i)
    {x : α} :
    h x (s.piecewise f g x) (s.piecewise f' g' x) =
      s.piecewise (fun x => h x (f x) (f' x)) (fun x => h x (g x) (g' x)) x :=
  by by_cases hx : x ∈ s <;> simp [hx]
#align set.apply_piecewise₂ Set.apply_piecewise₂

theorem piecewise_op {δ' : α → Sort _} (h : ∀ i, δ i → δ' i) :
    (s.piecewise (fun x => h x (f x)) fun x => h x (g x)) = fun x => h x (s.piecewise f g x) :=
  funext fun x => (apply_piecewise _ _ _ _).symm
#align set.piecewise_op Set.piecewise_op

theorem piecewise_op₂ {δ' δ'' : α → Sort _} (f' g' : ∀ i, δ' i) (h : ∀ i, δ i → δ' i → δ'' i) :
    (s.piecewise (fun x => h x (f x) (f' x)) fun x => h x (g x) (g' x)) = fun x =>
      h x (s.piecewise f g x) (s.piecewise f' g' x) :=
  funext fun x => (apply_piecewise₂ _ _ _ _ _ _).symm
#align set.piecewise_op₂ Set.piecewise_op₂

@[simp]
theorem piecewise_same : s.piecewise f f = f := by
  ext x
  by_cases hx : x ∈ s <;> simp [hx]
#align set.piecewise_same Set.piecewise_same

theorem range_piecewise (f g : α → β) : range (s.piecewise f g) = f '' s ∪ g '' sᶜ := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    by_cases h : x ∈ s <;> [left, right] <;> use x <;> simp [h]
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;> use x <;> simp_all
#align set.range_piecewise Set.range_piecewise

/- ./././Mathport/Syntax/Translate/Basic.lean:631:2: warning: expanding binder collection (y «expr ∉ » s) -/
theorem injective_piecewise_iff {f g : α → β} :
    Injective (s.piecewise f g) ↔
      InjOn f s ∧ InjOn g (sᶜ) ∧ ∀ x ∈ s, ∀ (y) (_ : y ∉ s), f x ≠ g y :=
  by
  rw [injective_iff_inj_on_univ, ← union_compl_self s, inj_on_union (@disjoint_compl_right _ _ s),
    (piecewise_eq_on s f g).inj_on_iff, (piecewise_eq_on_compl s f g).inj_on_iff]
  refine' and_congr Iff.rfl (and_congr Iff.rfl <| forall₄_congr fun x hx y hy => _)
  rw [piecewise_eq_of_mem s f g hx, piecewise_eq_of_not_mem s f g hy]
#align set.injective_piecewise_iff Set.injective_piecewise_iff

theorem piecewise_mem_pi {δ : α → Type _} {t : Set α} {t' : ∀ i, Set (δ i)} {f g} (hf : f ∈ pi t t')
    (hg : g ∈ pi t t') : s.piecewise f g ∈ pi t t' := by
  intro i ht
  by_cases hs : i ∈ s <;> simp [hf i ht, hg i ht, hs]
#align set.piecewise_mem_pi Set.piecewise_mem_pi

@[simp]
theorem pi_piecewise {ι : Type _} {α : ι → Type _} (s s' : Set ι) (t t' : ∀ i, Set (α i))
    [∀ x, Decidable (x ∈ s')] : pi s (s'.piecewise t t') = pi (s ∩ s') t ∩ pi (s \ s') t' := by
  ext x
  simp only [mem_pi, mem_inter_iff, ← forall_and]
  refine' forall_congr' fun i => _
  by_cases hi : i ∈ s' <;> simp [*]
#align set.pi_piecewise Set.pi_piecewise

theorem univ_pi_piecewise {ι : Type _} {α : ι → Type _} (s : Set ι) (t : ∀ i, Set (α i))
    [∀ x, Decidable (x ∈ s)] : pi univ (s.piecewise t fun _ => univ) = pi s t := by simp
#align set.univ_pi_piecewise Set.univ_pi_piecewise

end Set

theorem StrictMonoOn.inj_on [LinearOrder α] [Preorder β] {f : α → β} {s : Set α}
    (H : StrictMonoOn f s) : s.InjOn f := fun x hx y hy hxy =>
  show Ordering.eq.Compares x y from (H.Compares hx hy).1 hxy
#align strict_mono_on.inj_on StrictMonoOn.inj_on

theorem StrictAntiOn.inj_on [LinearOrder α] [Preorder β] {f : α → β} {s : Set α}
    (H : StrictAntiOn f s) : s.InjOn f :=
  @StrictMonoOn.inj_on α βᵒᵈ _ _ f s H
#align strict_anti_on.inj_on StrictAntiOn.inj_on

theorem StrictMonoOn.comp [Preorder α] [Preorder β] [Preorder γ] {g : β → γ} {f : α → β} {s : Set α}
    {t : Set β} (hg : StrictMonoOn g t) (hf : StrictMonoOn f s) (hs : Set.MapsTo f s t) :
    StrictMonoOn (g ∘ f) s := fun x hx y hy hxy => hg (hs hx) (hs hy) <| hf hx hy hxy
#align strict_mono_on.comp StrictMonoOn.comp

theorem StrictMonoOn.comp_strict_anti_on [Preorder α] [Preorder β] [Preorder γ] {g : β → γ}
    {f : α → β} {s : Set α} {t : Set β} (hg : StrictMonoOn g t) (hf : StrictAntiOn f s)
    (hs : Set.MapsTo f s t) : StrictAntiOn (g ∘ f) s := fun x hx y hy hxy =>
  hg (hs hy) (hs hx) <| hf hx hy hxy
#align strict_mono_on.comp_strict_anti_on StrictMonoOn.comp_strict_anti_on

theorem StrictAntiOn.comp [Preorder α] [Preorder β] [Preorder γ] {g : β → γ} {f : α → β} {s : Set α}
    {t : Set β} (hg : StrictAntiOn g t) (hf : StrictAntiOn f s) (hs : Set.MapsTo f s t) :
    StrictMonoOn (g ∘ f) s := fun x hx y hy hxy => hg (hs hy) (hs hx) <| hf hx hy hxy
#align strict_anti_on.comp StrictAntiOn.comp

theorem StrictAntiOn.comp_strict_mono_on [Preorder α] [Preorder β] [Preorder γ] {g : β → γ}
    {f : α → β} {s : Set α} {t : Set β} (hg : StrictAntiOn g t) (hf : StrictMonoOn f s)
    (hs : Set.MapsTo f s t) : StrictAntiOn (g ∘ f) s := fun x hx y hy hxy =>
  hg (hs hx) (hs hy) <| hf hx hy hxy
#align strict_anti_on.comp_strict_mono_on StrictAntiOn.comp_strict_mono_on

@[simp]
theorem strict_mono_restrict [Preorder α] [Preorder β] {f : α → β} {s : Set α} :
    StrictMono (s.restrict f) ↔ StrictMonoOn f s := by simp [Set.restrict, StrictMono, StrictMonoOn]
#align strict_mono_restrict strict_mono_restrict

alias strict_mono_restrict ↔ _root_.strict_mono.of_restrict _root_.strict_mono_on.restrict

theorem StrictMono.cod_restrict [Preorder α] [Preorder β] {f : α → β} (hf : StrictMono f)
    {s : Set β} (hs : ∀ x, f x ∈ s) : StrictMono (Set.codRestrict f s hs) :=
  hf
#align strict_mono.cod_restrict StrictMono.cod_restrict

namespace Function

open Set

variable {fa : α → α} {fb : β → β} {f : α → β} {g : β → γ} {s t : Set α}

theorem Injective.comp_inj_on (hg : Injective g) (hf : s.InjOn f) : s.InjOn (g ∘ f) :=
  (hg.InjOn univ).comp hf (maps_to_univ _ _)
#align function.injective.comp_inj_on Function.Injective.comp_inj_on

theorem Surjective.surj_on (hf : Surjective f) (s : Set β) : SurjOn f univ s :=
  (surjective_iff_surj_on_univ.1 hf).mono (Subset.refl _) (subset_univ _)
#align function.surjective.surj_on Function.Surjective.surj_on

theorem LeftInverse.left_inv_on {g : β → α} (h : LeftInverse f g) (s : Set β) : LeftInvOn f g s :=
  fun x hx => h x
#align function.left_inverse.left_inv_on Function.LeftInverse.left_inv_on

theorem RightInverse.right_inv_on {g : β → α} (h : RightInverse f g) (s : Set α) :
    RightInvOn f g s := fun x hx => h x
#align function.right_inverse.right_inv_on Function.RightInverse.right_inv_on

theorem LeftInverse.right_inv_on_range {g : β → α} (h : LeftInverse f g) :
    RightInvOn f g (range g) :=
  forall_range_iff.2 fun i => congr_arg g (h i)
#align function.left_inverse.right_inv_on_range Function.LeftInverse.right_inv_on_range

namespace Semiconj

theorem maps_to_image (h : Semiconj f fa fb) (ha : MapsTo fa s t) : MapsTo fb (f '' s) (f '' t) :=
  fun y ⟨x, hx, hy⟩ => hy ▸ ⟨fa x, ha hx, h x⟩
#align function.semiconj.maps_to_image Function.Semiconj.maps_to_image

theorem maps_to_range (h : Semiconj f fa fb) : MapsTo fb (range f) (range f) := fun y ⟨x, hy⟩ =>
  hy ▸ ⟨fa x, h x⟩
#align function.semiconj.maps_to_range Function.Semiconj.maps_to_range

theorem surj_on_image (h : Semiconj f fa fb) (ha : SurjOn fa s t) : SurjOn fb (f '' s) (f '' t) :=
  by 
  rintro y ⟨x, hxt, rfl⟩
  rcases ha hxt with ⟨x, hxs, rfl⟩
  rw [h x]
  exact mem_image_of_mem _ (mem_image_of_mem _ hxs)
#align function.semiconj.surj_on_image Function.Semiconj.surj_on_image

theorem surj_on_range (h : Semiconj f fa fb) (ha : Surjective fa) : SurjOn fb (range f) (range f) :=
  by 
  rw [← image_univ]
  exact h.surj_on_image (ha.surj_on univ)
#align function.semiconj.surj_on_range Function.Semiconj.surj_on_range

theorem inj_on_image (h : Semiconj f fa fb) (ha : InjOn fa s) (hf : InjOn f (fa '' s)) :
    InjOn fb (f '' s) := by 
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ H
  simp only [← h.eq] at H
  exact congr_arg f (ha hx hy <| hf (mem_image_of_mem fa hx) (mem_image_of_mem fa hy) H)
#align function.semiconj.inj_on_image Function.Semiconj.inj_on_image

theorem inj_on_range (h : Semiconj f fa fb) (ha : Injective fa) (hf : InjOn f (range fa)) :
    InjOn fb (range f) := by 
  rw [← image_univ] at *
  exact h.inj_on_image (ha.inj_on univ) hf
#align function.semiconj.inj_on_range Function.Semiconj.inj_on_range

theorem bij_on_image (h : Semiconj f fa fb) (ha : BijOn fa s t) (hf : InjOn f t) :
    BijOn fb (f '' s) (f '' t) :=
  ⟨h.maps_to_image ha.MapsTo, h.inj_on_image ha.InjOn (ha.image_eq.symm ▸ hf),
    h.surj_on_image ha.SurjOn⟩
#align function.semiconj.bij_on_image Function.Semiconj.bij_on_image

theorem bij_on_range (h : Semiconj f fa fb) (ha : Bijective fa) (hf : Injective f) :
    BijOn fb (range f) (range f) := by 
  rw [← image_univ]
  exact h.bij_on_image (bijective_iff_bij_on_univ.1 ha) (hf.inj_on univ)
#align function.semiconj.bij_on_range Function.Semiconj.bij_on_range

theorem maps_to_preimage (h : Semiconj f fa fb) {s t : Set β} (hb : MapsTo fb s t) :
    MapsTo fa (f ⁻¹' s) (f ⁻¹' t) := fun x hx => by simp only [mem_preimage, h x, hb hx]
#align function.semiconj.maps_to_preimage Function.Semiconj.maps_to_preimage

theorem inj_on_preimage (h : Semiconj f fa fb) {s : Set β} (hb : InjOn fb s)
    (hf : InjOn f (f ⁻¹' s)) : InjOn fa (f ⁻¹' s) := by
  intro x hx y hy H
  have := congr_arg f H
  rw [h.eq, h.eq] at this
  exact hf hx hy (hb hx hy this)
#align function.semiconj.inj_on_preimage Function.Semiconj.inj_on_preimage

end Semiconj

theorem update_comp_eq_of_not_mem_range' {α β : Sort _} {γ : β → Sort _} [DecidableEq β]
    (g : ∀ b, γ b) {f : α → β} {i : β} (a : γ i) (h : i ∉ Set.range f) :
    (fun j => (Function.update g i a) (f j)) = fun j => g (f j) :=
  (update_comp_eq_of_forall_ne' _ _) fun x hx => h ⟨x, hx⟩
#align function.update_comp_eq_of_not_mem_range' Function.update_comp_eq_of_not_mem_range'

/-- Non-dependent version of `function.update_comp_eq_of_not_mem_range'` -/
theorem update_comp_eq_of_not_mem_range {α β γ : Sort _} [DecidableEq β] (g : β → γ) {f : α → β}
    {i : β} (a : γ) (h : i ∉ Set.range f) : Function.update g i a ∘ f = g ∘ f :=
  update_comp_eq_of_not_mem_range' g a h
#align function.update_comp_eq_of_not_mem_range Function.update_comp_eq_of_not_mem_range

theorem insert_inj_on (s : Set α) : sᶜ.InjOn fun a => insert a s := fun a ha b _ =>
  (insert_inj ha).1
#align function.insert_inj_on Function.insert_inj_on

end Function

