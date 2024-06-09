/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Andrew Zipperer, Haitao Zhang, Minchao Wu, Yury Kudryashov
-/
import Mathlib.Data.Set.Prod
import Mathlib.Logic.Function.Conjugate

#align_import data.set.function from "leanprover-community/mathlib"@"996b0ff959da753a555053a480f36e5f264d4207"

/-!
# Functions over sets

## Main definitions

### Predicate

* `Set.EqOn f₁ f₂ s` : functions `f₁` and `f₂` are equal at every point of `s`;
* `Set.MapsTo f s t` : `f` sends every point of `s` to a point of `t`;
* `Set.InjOn f s` : restriction of `f` to `s` is injective;
* `Set.SurjOn f s t` : every point in `s` has a preimage in `s`;
* `Set.BijOn f s t` : `f` is a bijection between `s` and `t`;
* `Set.LeftInvOn f' f s` : for every `x ∈ s` we have `f' (f x) = x`;
* `Set.RightInvOn f' f t` : for every `y ∈ t` we have `f (f' y) = y`;
* `Set.InvOn f' f s t` : `f'` is a two-side inverse of `f` on `s` and `t`, i.e.
  we have `Set.LeftInvOn f' f s` and `Set.RightInvOn f' f t`.

### Functions

* `Set.restrict f s` : restrict the domain of `f` to the set `s`;
* `Set.codRestrict f s h` : given `h : ∀ x, f x ∈ s`, restrict the codomain of `f` to the set `s`;
* `Set.MapsTo.restrict f s t h`: given `h : MapsTo f s t`, restrict the domain of `f` to `s`
  and the codomain to `t`.
-/

variable {α β γ : Type*} {ι : Sort*} {π : α → Type*}

open Equiv Equiv.Perm Function

namespace Set

/-! ### Restrict -/
section restrict

/-- Restrict domain of a function `f` to a set `s`. Same as `Subtype.restrict` but this version
takes an argument `↥s` instead of `Subtype s`. -/
def restrict (s : Set α) (f : ∀ a : α, π a) : ∀ a : s, π a := fun x => f x
#align set.restrict Set.restrict

theorem restrict_eq (f : α → β) (s : Set α) : s.restrict f = f ∘ Subtype.val :=
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
  (range_comp _ _).trans <| congr_arg (f '' ·) Subtype.range_coe
#align set.range_restrict Set.range_restrict

theorem image_restrict (f : α → β) (s t : Set α) :
    s.restrict f '' (Subtype.val ⁻¹' t) = f '' (t ∩ s) := by
  rw [restrict_eq, image_comp, image_preimage_eq_inter_range, Subtype.range_coe]
#align set.image_restrict Set.image_restrict

@[simp]
theorem restrict_dite {s : Set α} [∀ x, Decidable (x ∈ s)] (f : ∀ a ∈ s, β)
    (g : ∀ a ∉ s, β) :
    (s.restrict fun a => if h : a ∈ s then f a h else g a h) = (fun a : s => f a a.2) :=
  funext fun a => dif_pos a.2
#align set.restrict_dite Set.restrict_dite

@[simp]
theorem restrict_dite_compl {s : Set α} [∀ x, Decidable (x ∈ s)] (f : ∀ a ∈ s, β)
    (g : ∀ a ∉ s, β) :
    (sᶜ.restrict fun a => if h : a ∈ s then f a h else g a h) = (fun a : (sᶜ : Set α) => g a a.2) :=
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
    (range f).restrict (extend f g g') = fun x => g x.coe_prop.choose := by
  classical
  exact restrict_dite _ _
#align set.restrict_extend_range Set.restrict_extend_range

@[simp]
theorem restrict_extend_compl_range (f : α → β) (g : α → γ) (g' : β → γ) :
    (range f)ᶜ.restrict (extend f g g') = g' ∘ Subtype.val := by
  classical
  exact restrict_dite_compl _ _
#align set.restrict_extend_compl_range Set.restrict_extend_compl_range

theorem range_extend_subset (f : α → β) (g : α → γ) (g' : β → γ) :
    range (extend f g g') ⊆ range g ∪ g' '' (range f)ᶜ := by
  classical
  rintro _ ⟨y, rfl⟩
  rw [extend_def]
  split_ifs with h
  exacts [Or.inl (mem_range_self _), Or.inr (mem_image_of_mem _ h)]
#align set.range_extend_subset Set.range_extend_subset

theorem range_extend {f : α → β} (hf : Injective f) (g : α → γ) (g' : β → γ) :
    range (extend f g g') = range g ∪ g' '' (range f)ᶜ := by
  refine (range_extend_subset _ _ _).antisymm ?_
  rintro z (⟨x, rfl⟩ | ⟨y, hy, rfl⟩)
  exacts [⟨f x, hf.extend_apply _ _ _⟩, ⟨y, extend_apply' _ _ _ hy⟩]
#align set.range_extend Set.range_extend

/-- Restrict codomain of a function `f` to a set `s`. Same as `Subtype.coind` but this version
has codomain `↥s` instead of `Subtype s`. -/
def codRestrict (f : ι → α) (s : Set α) (h : ∀ x, f x ∈ s) : ι → s := fun x => ⟨f x, h x⟩
#align set.cod_restrict Set.codRestrict

@[simp]
theorem val_codRestrict_apply (f : ι → α) (s : Set α) (h : ∀ x, f x ∈ s) (x : ι) :
    (codRestrict f s h x : α) = f x :=
  rfl
#align set.coe_cod_restrict_apply Set.val_codRestrict_apply

@[simp]
theorem restrict_comp_codRestrict {f : ι → α} {g : α → β} {b : Set α} (h : ∀ x, f x ∈ b) :
    b.restrict g ∘ b.codRestrict f h = g ∘ f :=
  rfl
#align set.restrict_comp_cod_restrict Set.restrict_comp_codRestrict

@[simp]
theorem injective_codRestrict {f : ι → α} {s : Set α} (h : ∀ x, f x ∈ s) :
    Injective (codRestrict f s h) ↔ Injective f := by
  simp only [Injective, Subtype.ext_iff, val_codRestrict_apply]
#align set.injective_cod_restrict Set.injective_codRestrict

alias ⟨_, _root_.Function.Injective.codRestrict⟩ := injective_codRestrict
#align function.injective.cod_restrict Function.Injective.codRestrict

end restrict

/-! ### Equality on a set -/
section equality

variable {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {p : Set γ} {f f₁ f₂ f₃ : α → β} {g g₁ g₂ : β → γ}
  {f' f₁' f₂' : β → α} {g' : γ → β} {a : α} {b : β}

@[simp]
theorem eqOn_empty (f₁ f₂ : α → β) : EqOn f₁ f₂ ∅ := fun _ => False.elim
#align set.eq_on_empty Set.eqOn_empty

@[simp]
theorem eqOn_singleton : Set.EqOn f₁ f₂ {a} ↔ f₁ a = f₂ a := by
  simp [Set.EqOn]
#align set.eq_on_singleton Set.eqOn_singleton

@[simp]
theorem eqOn_univ (f₁ f₂ : α → β) : EqOn f₁ f₂ univ ↔ f₁ = f₂ := by
  simp [EqOn, funext_iff]

@[simp]
theorem restrict_eq_restrict_iff : restrict s f₁ = restrict s f₂ ↔ EqOn f₁ f₂ s :=
  restrict_eq_iff
#align set.restrict_eq_restrict_iff Set.restrict_eq_restrict_iff

@[symm]
theorem EqOn.symm (h : EqOn f₁ f₂ s) : EqOn f₂ f₁ s := fun _ hx => (h hx).symm
#align set.eq_on.symm Set.EqOn.symm

theorem eqOn_comm : EqOn f₁ f₂ s ↔ EqOn f₂ f₁ s :=
  ⟨EqOn.symm, EqOn.symm⟩
#align set.eq_on_comm Set.eqOn_comm

-- This can not be tagged as `@[refl]` with the current argument order.
-- See note below at `EqOn.trans`.
theorem eqOn_refl (f : α → β) (s : Set α) : EqOn f f s := fun _ _ => rfl
#align set.eq_on_refl Set.eqOn_refl

-- Note: this was formerly tagged with `@[trans]`, and although the `trans` attribute accepted it
-- the `trans` tactic could not use it.
-- An update to the trans tactic coming in mathlib4#7014 will reject this attribute.
-- It can be restored by changing the argument order from `EqOn f₁ f₂ s` to `EqOn s f₁ f₂`.
-- This change will be made separately: [zulip](https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Reordering.20arguments.20of.20.60Set.2EEqOn.60/near/390467581).
theorem EqOn.trans (h₁ : EqOn f₁ f₂ s) (h₂ : EqOn f₂ f₃ s) : EqOn f₁ f₃ s := fun _ hx =>
  (h₁ hx).trans (h₂ hx)
#align set.eq_on.trans Set.EqOn.trans

theorem EqOn.image_eq (heq : EqOn f₁ f₂ s) : f₁ '' s = f₂ '' s :=
  image_congr heq
#align set.eq_on.image_eq Set.EqOn.image_eq

/-- Variant of `EqOn.image_eq`, for one function being the identity. -/
theorem EqOn.image_eq_self {f : α → α} (h : Set.EqOn f id s) : f '' s = s := by
  rw [h.image_eq, image_id]

theorem EqOn.inter_preimage_eq (heq : EqOn f₁ f₂ s) (t : Set β) : s ∩ f₁ ⁻¹' t = s ∩ f₂ ⁻¹' t :=
  ext fun x => and_congr_right_iff.2 fun hx => by rw [mem_preimage, mem_preimage, heq hx]
#align set.eq_on.inter_preimage_eq Set.EqOn.inter_preimage_eq

theorem EqOn.mono (hs : s₁ ⊆ s₂) (hf : EqOn f₁ f₂ s₂) : EqOn f₁ f₂ s₁ := fun _ hx => hf (hs hx)
#align set.eq_on.mono Set.EqOn.mono

@[simp]
theorem eqOn_union : EqOn f₁ f₂ (s₁ ∪ s₂) ↔ EqOn f₁ f₂ s₁ ∧ EqOn f₁ f₂ s₂ :=
  forall₂_or_left
#align set.eq_on_union Set.eqOn_union

theorem EqOn.union (h₁ : EqOn f₁ f₂ s₁) (h₂ : EqOn f₁ f₂ s₂) : EqOn f₁ f₂ (s₁ ∪ s₂) :=
  eqOn_union.2 ⟨h₁, h₂⟩
#align set.eq_on.union Set.EqOn.union

theorem EqOn.comp_left (h : s.EqOn f₁ f₂) : s.EqOn (g ∘ f₁) (g ∘ f₂) := fun _ ha =>
  congr_arg _ <| h ha
#align set.eq_on.comp_left Set.EqOn.comp_left

@[simp]
theorem eqOn_range {ι : Sort*} {f : ι → α} {g₁ g₂ : α → β} :
    EqOn g₁ g₂ (range f) ↔ g₁ ∘ f = g₂ ∘ f :=
  forall_mem_range.trans <| funext_iff.symm
#align set.eq_on_range Set.eqOn_range

alias ⟨EqOn.comp_eq, _⟩ := eqOn_range
#align set.eq_on.comp_eq Set.EqOn.comp_eq

end equality

/-! ### Congruence lemmas for monotonicity and antitonicity -/
section Order

variable {s : Set α} {f₁ f₂ : α → β} [Preorder α] [Preorder β]

theorem _root_.MonotoneOn.congr (h₁ : MonotoneOn f₁ s) (h : s.EqOn f₁ f₂) : MonotoneOn f₂ s := by
  intro a ha b hb hab
  rw [← h ha, ← h hb]
  exact h₁ ha hb hab
#align monotone_on.congr MonotoneOn.congr

theorem _root_.AntitoneOn.congr (h₁ : AntitoneOn f₁ s) (h : s.EqOn f₁ f₂) : AntitoneOn f₂ s :=
  h₁.dual_right.congr h
#align antitone_on.congr AntitoneOn.congr

theorem _root_.StrictMonoOn.congr (h₁ : StrictMonoOn f₁ s) (h : s.EqOn f₁ f₂) :
    StrictMonoOn f₂ s := by
  intro a ha b hb hab
  rw [← h ha, ← h hb]
  exact h₁ ha hb hab
#align strict_mono_on.congr StrictMonoOn.congr

theorem _root_.StrictAntiOn.congr (h₁ : StrictAntiOn f₁ s) (h : s.EqOn f₁ f₂) : StrictAntiOn f₂ s :=
  h₁.dual_right.congr h
#align strict_anti_on.congr StrictAntiOn.congr

theorem EqOn.congr_monotoneOn (h : s.EqOn f₁ f₂) : MonotoneOn f₁ s ↔ MonotoneOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩
#align set.eq_on.congr_monotone_on Set.EqOn.congr_monotoneOn

theorem EqOn.congr_antitoneOn (h : s.EqOn f₁ f₂) : AntitoneOn f₁ s ↔ AntitoneOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩
#align set.eq_on.congr_antitone_on Set.EqOn.congr_antitoneOn

theorem EqOn.congr_strictMonoOn (h : s.EqOn f₁ f₂) : StrictMonoOn f₁ s ↔ StrictMonoOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩
#align set.eq_on.congr_strict_mono_on Set.EqOn.congr_strictMonoOn

theorem EqOn.congr_strictAntiOn (h : s.EqOn f₁ f₂) : StrictAntiOn f₁ s ↔ StrictAntiOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩
#align set.eq_on.congr_strict_anti_on Set.EqOn.congr_strictAntiOn

end Order

/-! ### Monotonicity lemmas-/
section Mono

variable {s s₁ s₂ : Set α} {f f₁ f₂ : α → β} [Preorder α] [Preorder β]

theorem _root_.MonotoneOn.mono (h : MonotoneOn f s) (h' : s₂ ⊆ s) : MonotoneOn f s₂ :=
  fun _ hx _ hy => h (h' hx) (h' hy)
#align monotone_on.mono MonotoneOn.mono

theorem _root_.AntitoneOn.mono (h : AntitoneOn f s) (h' : s₂ ⊆ s) : AntitoneOn f s₂ :=
  fun _ hx _ hy => h (h' hx) (h' hy)
#align antitone_on.mono AntitoneOn.mono

theorem _root_.StrictMonoOn.mono (h : StrictMonoOn f s) (h' : s₂ ⊆ s) : StrictMonoOn f s₂ :=
  fun _ hx _ hy => h (h' hx) (h' hy)
#align strict_mono_on.mono StrictMonoOn.mono

theorem _root_.StrictAntiOn.mono (h : StrictAntiOn f s) (h' : s₂ ⊆ s) : StrictAntiOn f s₂ :=
  fun _ hx _ hy => h (h' hx) (h' hy)
#align strict_anti_on.mono StrictAntiOn.mono

protected theorem _root_.MonotoneOn.monotone (h : MonotoneOn f s) :
    Monotone (f ∘ Subtype.val : s → β) :=
  fun x y hle => h x.coe_prop y.coe_prop hle
#align monotone_on.monotone MonotoneOn.monotone

protected theorem _root_.AntitoneOn.monotone (h : AntitoneOn f s) :
    Antitone (f ∘ Subtype.val : s → β) :=
  fun x y hle => h x.coe_prop y.coe_prop hle
#align antitone_on.monotone AntitoneOn.monotone

protected theorem _root_.StrictMonoOn.strictMono (h : StrictMonoOn f s) :
    StrictMono (f ∘ Subtype.val : s → β) :=
  fun x y hlt => h x.coe_prop y.coe_prop hlt
#align strict_mono_on.strict_mono StrictMonoOn.strictMono

protected theorem _root_.StrictAntiOn.strictAnti (h : StrictAntiOn f s) :
    StrictAnti (f ∘ Subtype.val : s → β) :=
  fun x y hlt => h x.coe_prop y.coe_prop hlt
#align strict_anti_on.strict_anti StrictAntiOn.strictAnti

end Mono

variable {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {p : Set γ} {f f₁ f₂ f₃ : α → β} {g g₁ g₂ : β → γ}
  {f' f₁' f₂' : β → α} {g' : γ → β} {a : α} {b : β}

section MapsTo

theorem MapsTo.restrict_commutes (f : α → β) (s : Set α) (t : Set β) (h : MapsTo f s t) :
    Subtype.val ∘ h.restrict f s t = f ∘ Subtype.val :=
  rfl

@[simp]
theorem MapsTo.val_restrict_apply (h : MapsTo f s t) (x : s) : (h.restrict f s t x : β) = f x :=
  rfl
#align set.maps_to.coe_restrict_apply Set.MapsTo.val_restrict_apply

theorem MapsTo.coe_iterate_restrict {f : α → α} (h : MapsTo f s s) (x : s) (k : ℕ) :
    h.restrict^[k] x = f^[k] x := by
  induction' k with k ih; · simp
  simp only [iterate_succ', comp_apply, val_restrict_apply, ih]

/-- Restricting the domain and then the codomain is the same as `MapsTo.restrict`. -/
@[simp]
theorem codRestrict_restrict (h : ∀ x : s, f x ∈ t) :
    codRestrict (s.restrict f) t h = MapsTo.restrict f s t fun x hx => h ⟨x, hx⟩ :=
  rfl
#align set.cod_restrict_restrict Set.codRestrict_restrict

/-- Reverse of `Set.codRestrict_restrict`. -/
theorem MapsTo.restrict_eq_codRestrict (h : MapsTo f s t) :
    h.restrict f s t = codRestrict (s.restrict f) t fun x => h x.2 :=
  rfl
#align set.maps_to.restrict_eq_cod_restrict Set.MapsTo.restrict_eq_codRestrict

theorem MapsTo.coe_restrict (h : Set.MapsTo f s t) :
    Subtype.val ∘ h.restrict f s t = s.restrict f :=
  rfl
#align set.maps_to.coe_restrict Set.MapsTo.coe_restrict

theorem MapsTo.range_restrict (f : α → β) (s : Set α) (t : Set β) (h : MapsTo f s t) :
    range (h.restrict f s t) = Subtype.val ⁻¹' (f '' s) :=
  Set.range_subtype_map f h
#align set.maps_to.range_restrict Set.MapsTo.range_restrict

theorem mapsTo_iff_exists_map_subtype : MapsTo f s t ↔ ∃ g : s → t, ∀ x : s, f x = g x :=
  ⟨fun h => ⟨h.restrict f s t, fun _ => rfl⟩, fun ⟨g, hg⟩ x hx => by
    erw [hg ⟨x, hx⟩]
    apply Subtype.coe_prop⟩
#align set.maps_to_iff_exists_map_subtype Set.mapsTo_iff_exists_map_subtype

theorem mapsTo' : MapsTo f s t ↔ f '' s ⊆ t :=
  image_subset_iff.symm
#align set.maps_to' Set.mapsTo'

theorem mapsTo_prod_map_diagonal : MapsTo (Prod.map f f) (diagonal α) (diagonal β) :=
  diagonal_subset_iff.2 fun _ => rfl
#align set.maps_to_prod_map_diagonal Set.mapsTo_prod_map_diagonal

theorem MapsTo.subset_preimage {f : α → β} {s : Set α} {t : Set β} (hf : MapsTo f s t) :
    s ⊆ f ⁻¹' t :=
  hf
#align set.maps_to.subset_preimage Set.MapsTo.subset_preimage

@[simp]
theorem mapsTo_singleton {x : α} : MapsTo f {x} t ↔ f x ∈ t :=
  singleton_subset_iff
#align set.maps_to_singleton Set.mapsTo_singleton

theorem mapsTo_empty (f : α → β) (t : Set β) : MapsTo f ∅ t :=
  empty_subset _
#align set.maps_to_empty Set.mapsTo_empty

/-- If `f` maps `s` to `t` and `s` is non-empty, `t` is non-empty. -/
theorem MapsTo.nonempty (h : MapsTo f s t) (hs : s.Nonempty) : t.Nonempty :=
  (hs.image f).mono (mapsTo'.mp h)

theorem MapsTo.image_subset (h : MapsTo f s t) : f '' s ⊆ t :=
  mapsTo'.1 h
#align set.maps_to.image_subset Set.MapsTo.image_subset

theorem MapsTo.congr (h₁ : MapsTo f₁ s t) (h : EqOn f₁ f₂ s) : MapsTo f₂ s t := fun _ hx =>
  h hx ▸ h₁ hx
#align set.maps_to.congr Set.MapsTo.congr

theorem EqOn.comp_right (hg : t.EqOn g₁ g₂) (hf : s.MapsTo f t) : s.EqOn (g₁ ∘ f) (g₂ ∘ f) :=
  fun _ ha => hg <| hf ha
#align set.eq_on.comp_right Set.EqOn.comp_right

theorem EqOn.mapsTo_iff (H : EqOn f₁ f₂ s) : MapsTo f₁ s t ↔ MapsTo f₂ s t :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩
#align set.eq_on.maps_to_iff Set.EqOn.mapsTo_iff

theorem MapsTo.comp (h₁ : MapsTo g t p) (h₂ : MapsTo f s t) : MapsTo (g ∘ f) s p := fun _ h =>
  h₁ (h₂ h)
#align set.maps_to.comp Set.MapsTo.comp

theorem mapsTo_id (s : Set α) : MapsTo id s s := fun _ => id
#align set.maps_to_id Set.mapsTo_id

theorem MapsTo.iterate {f : α → α} {s : Set α} (h : MapsTo f s s) : ∀ n, MapsTo f^[n] s s
  | 0 => fun _ => id
  | n + 1 => (MapsTo.iterate h n).comp h
#align set.maps_to.iterate Set.MapsTo.iterate

theorem MapsTo.iterate_restrict {f : α → α} {s : Set α} (h : MapsTo f s s) (n : ℕ) :
    (h.restrict f s s)^[n] = (h.iterate n).restrict _ _ _ := by
  funext x
  rw [Subtype.ext_iff, MapsTo.val_restrict_apply]
  induction' n with n ihn generalizing x
  · rfl
  · simp [Nat.iterate, ihn]
#align set.maps_to.iterate_restrict Set.MapsTo.iterate_restrict

lemma mapsTo_of_subsingleton' [Subsingleton β] (f : α → β) (h : s.Nonempty → t.Nonempty) :
    MapsTo f s t :=
  fun a ha ↦ Subsingleton.mem_iff_nonempty.2 <| h ⟨a, ha⟩
#align set.maps_to_of_subsingleton' Set.mapsTo_of_subsingleton'

lemma mapsTo_of_subsingleton [Subsingleton α] (f : α → α) (s : Set α) : MapsTo f s s :=
  mapsTo_of_subsingleton' _ id
#align set.maps_to_of_subsingleton Set.mapsTo_of_subsingleton

theorem MapsTo.mono (hf : MapsTo f s₁ t₁) (hs : s₂ ⊆ s₁) (ht : t₁ ⊆ t₂) : MapsTo f s₂ t₂ :=
  fun _ hx => ht (hf <| hs hx)
#align set.maps_to.mono Set.MapsTo.mono

theorem MapsTo.mono_left (hf : MapsTo f s₁ t) (hs : s₂ ⊆ s₁) : MapsTo f s₂ t := fun _ hx =>
  hf (hs hx)
#align set.maps_to.mono_left Set.MapsTo.mono_left

theorem MapsTo.mono_right (hf : MapsTo f s t₁) (ht : t₁ ⊆ t₂) : MapsTo f s t₂ := fun _ hx =>
  ht (hf hx)
#align set.maps_to.mono_right Set.MapsTo.mono_right

theorem MapsTo.union_union (h₁ : MapsTo f s₁ t₁) (h₂ : MapsTo f s₂ t₂) :
    MapsTo f (s₁ ∪ s₂) (t₁ ∪ t₂) := fun _ hx =>
  hx.elim (fun hx => Or.inl <| h₁ hx) fun hx => Or.inr <| h₂ hx
#align set.maps_to.union_union Set.MapsTo.union_union

theorem MapsTo.union (h₁ : MapsTo f s₁ t) (h₂ : MapsTo f s₂ t) : MapsTo f (s₁ ∪ s₂) t :=
  union_self t ▸ h₁.union_union h₂
#align set.maps_to.union Set.MapsTo.union

@[simp]
theorem mapsTo_union : MapsTo f (s₁ ∪ s₂) t ↔ MapsTo f s₁ t ∧ MapsTo f s₂ t :=
  ⟨fun h =>
    ⟨h.mono subset_union_left (Subset.refl t),
      h.mono subset_union_right (Subset.refl t)⟩,
    fun h => h.1.union h.2⟩
#align set.maps_to_union Set.mapsTo_union

theorem MapsTo.inter (h₁ : MapsTo f s t₁) (h₂ : MapsTo f s t₂) : MapsTo f s (t₁ ∩ t₂) := fun _ hx =>
  ⟨h₁ hx, h₂ hx⟩
#align set.maps_to.inter Set.MapsTo.inter

theorem MapsTo.inter_inter (h₁ : MapsTo f s₁ t₁) (h₂ : MapsTo f s₂ t₂) :
    MapsTo f (s₁ ∩ s₂) (t₁ ∩ t₂) := fun _ hx => ⟨h₁ hx.1, h₂ hx.2⟩
#align set.maps_to.inter_inter Set.MapsTo.inter_inter

@[simp]
theorem mapsTo_inter : MapsTo f s (t₁ ∩ t₂) ↔ MapsTo f s t₁ ∧ MapsTo f s t₂ :=
  ⟨fun h =>
    ⟨h.mono (Subset.refl s) inter_subset_left,
      h.mono (Subset.refl s) inter_subset_right⟩,
    fun h => h.1.inter h.2⟩
#align set.maps_to_inter Set.mapsTo_inter

theorem mapsTo_univ (f : α → β) (s : Set α) : MapsTo f s univ := fun _ _ => trivial
#align set.maps_to_univ Set.mapsTo_univ

theorem mapsTo_range (f : α → β) (s : Set α) : MapsTo f s (range f) :=
  (mapsTo_image f s).mono (Subset.refl s) (image_subset_range _ _)
#align set.maps_to_range Set.mapsTo_range

@[simp]
theorem mapsTo_image_iff {f : α → β} {g : γ → α} {s : Set γ} {t : Set β} :
    MapsTo f (g '' s) t ↔ MapsTo (f ∘ g) s t :=
  ⟨fun h c hc => h ⟨c, hc, rfl⟩, fun h _ ⟨_, hc⟩ => hc.2 ▸ h hc.1⟩
#align set.maps_image_to Set.mapsTo_image_iff

@[deprecated (since := "2023-12-25")]
lemma maps_image_to (f : α → β) (g : γ → α) (s : Set γ) (t : Set β) :
    MapsTo f (g '' s) t ↔ MapsTo (f ∘ g) s t :=
  mapsTo_image_iff

lemma MapsTo.comp_left (g : β → γ) (hf : MapsTo f s t) : MapsTo (g ∘ f) s (g '' t) :=
  fun x hx ↦ ⟨f x, hf hx, rfl⟩
#align set.maps_to.comp_left Set.MapsTo.comp_left

lemma MapsTo.comp_right {s : Set β} {t : Set γ} (hg : MapsTo g s t) (f : α → β) :
    MapsTo (g ∘ f) (f ⁻¹' s) t := fun _ hx ↦ hg hx
#align set.maps_to.comp_right Set.MapsTo.comp_right

@[simp]
lemma mapsTo_univ_iff : MapsTo f univ t ↔ ∀ x, f x ∈ t :=
  ⟨fun h _ => h (mem_univ _), fun h x _ => h x⟩

@[deprecated (since := "2023-12-25")]
theorem maps_univ_to (f : α → β) (s : Set β) : MapsTo f univ s ↔ ∀ a, f a ∈ s :=
  mapsTo_univ_iff
#align set.maps_univ_to Set.maps_univ_to

@[simp]
lemma mapsTo_range_iff {g : ι → α} : MapsTo f (range g) t ↔ ∀ i, f (g i) ∈ t :=
  forall_mem_range

@[deprecated mapsTo_range_iff (since := "2023-12-25")]
theorem maps_range_to (f : α → β) (g : γ → α) (s : Set β) :
    MapsTo f (range g) s ↔ MapsTo (f ∘ g) univ s := by rw [← image_univ, mapsTo_image_iff]
#align set.maps_range_to Set.maps_range_to

theorem surjective_mapsTo_image_restrict (f : α → β) (s : Set α) :
    Surjective ((mapsTo_image f s).restrict f s (f '' s)) := fun ⟨_, x, hs, hxy⟩ =>
  ⟨⟨x, hs⟩, Subtype.ext hxy⟩
#align set.surjective_maps_to_image_restrict Set.surjective_mapsTo_image_restrict

theorem MapsTo.mem_iff (h : MapsTo f s t) (hc : MapsTo f sᶜ tᶜ) {x} : f x ∈ t ↔ x ∈ s :=
  ⟨fun ht => by_contra fun hs => hc hs ht, fun hx => h hx⟩
#align set.maps_to.mem_iff Set.MapsTo.mem_iff

end MapsTo

/-! ### Restriction onto preimage -/
section

variable (t)

variable (f s) in
theorem image_restrictPreimage :
    t.restrictPreimage f '' (Subtype.val ⁻¹' s) = Subtype.val ⁻¹' (f '' s) := by
  delta Set.restrictPreimage
  rw [← (Subtype.coe_injective).image_injective.eq_iff, ← image_comp, MapsTo.restrict_commutes,
    image_comp, Subtype.image_preimage_coe, Subtype.image_preimage_coe, image_preimage_inter]

variable (f) in
theorem range_restrictPreimage : range (t.restrictPreimage f) = Subtype.val ⁻¹' range f := by
  simp only [← image_univ, ← image_restrictPreimage, preimage_univ]
#align set.range_restrict_preimage Set.range_restrictPreimage

variable {U : ι → Set β}

lemma restrictPreimage_injective (hf : Injective f) : Injective (t.restrictPreimage f) :=
  fun _ _ e => Subtype.coe_injective <| hf <| Subtype.mk.inj e
#align set.restrict_preimage_injective Set.restrictPreimage_injective

lemma restrictPreimage_surjective (hf : Surjective f) : Surjective (t.restrictPreimage f) :=
  fun x => ⟨⟨_, ((hf x).choose_spec.symm ▸ x.2 : _ ∈ t)⟩, Subtype.ext (hf x).choose_spec⟩
#align set.restrict_preimage_surjective Set.restrictPreimage_surjective

lemma restrictPreimage_bijective (hf : Bijective f) : Bijective (t.restrictPreimage f) :=
  ⟨t.restrictPreimage_injective hf.1, t.restrictPreimage_surjective hf.2⟩
#align set.restrict_preimage_bijective Set.restrictPreimage_bijective

alias _root_.Function.Injective.restrictPreimage := Set.restrictPreimage_injective
alias _root_.Function.Surjective.restrictPreimage := Set.restrictPreimage_surjective
alias _root_.Function.Bijective.restrictPreimage := Set.restrictPreimage_bijective
#align function.bijective.restrict_preimage Function.Bijective.restrictPreimage
#align function.surjective.restrict_preimage Function.Surjective.restrictPreimage
#align function.injective.restrict_preimage Function.Injective.restrictPreimage

end

/-! ### Injectivity on a set -/
section injOn

theorem Subsingleton.injOn (hs : s.Subsingleton) (f : α → β) : InjOn f s := fun _ hx _ hy _ =>
  hs hx hy
#align set.subsingleton.inj_on Set.Subsingleton.injOn

@[simp]
theorem injOn_empty (f : α → β) : InjOn f ∅ :=
  subsingleton_empty.injOn f
#align set.inj_on_empty Set.injOn_empty
@[simp]
theorem injOn_singleton (f : α → β) (a : α) : InjOn f {a} :=
  subsingleton_singleton.injOn f
#align set.inj_on_singleton Set.injOn_singleton

@[simp] lemma injOn_pair {b : α} : InjOn f {a, b} ↔ f a = f b → a = b := by unfold InjOn; aesop

theorem InjOn.eq_iff {x y} (h : InjOn f s) (hx : x ∈ s) (hy : y ∈ s) : f x = f y ↔ x = y :=
  ⟨h hx hy, fun h => h ▸ rfl⟩
#align set.inj_on.eq_iff Set.InjOn.eq_iff

theorem InjOn.ne_iff {x y} (h : InjOn f s) (hx : x ∈ s) (hy : y ∈ s) : f x ≠ f y ↔ x ≠ y :=
  (h.eq_iff hx hy).not
#align set.inj_on.ne_iff Set.InjOn.ne_iff

alias ⟨_, InjOn.ne⟩ := InjOn.ne_iff
#align set.inj_on.ne Set.InjOn.ne

theorem InjOn.congr (h₁ : InjOn f₁ s) (h : EqOn f₁ f₂ s) : InjOn f₂ s := fun _ hx _ hy =>
  h hx ▸ h hy ▸ h₁ hx hy
#align set.inj_on.congr Set.InjOn.congr

theorem EqOn.injOn_iff (H : EqOn f₁ f₂ s) : InjOn f₁ s ↔ InjOn f₂ s :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩
#align set.eq_on.inj_on_iff Set.EqOn.injOn_iff

theorem InjOn.mono (h : s₁ ⊆ s₂) (ht : InjOn f s₂) : InjOn f s₁ := fun _ hx _ hy H =>
  ht (h hx) (h hy) H
#align set.inj_on.mono Set.InjOn.mono

theorem injOn_union (h : Disjoint s₁ s₂) :
    InjOn f (s₁ ∪ s₂) ↔ InjOn f s₁ ∧ InjOn f s₂ ∧ ∀ x ∈ s₁, ∀ y ∈ s₂, f x ≠ f y := by
  refine ⟨fun H => ⟨H.mono subset_union_left, H.mono subset_union_right, ?_⟩, ?_⟩
  · intro x hx y hy hxy
    obtain rfl : x = y := H (Or.inl hx) (Or.inr hy) hxy
    exact h.le_bot ⟨hx, hy⟩
  · rintro ⟨h₁, h₂, h₁₂⟩
    rintro x (hx | hx) y (hy | hy) hxy
    exacts [h₁ hx hy hxy, (h₁₂ _ hx _ hy hxy).elim, (h₁₂ _ hy _ hx hxy.symm).elim, h₂ hx hy hxy]
#align set.inj_on_union Set.injOn_union

theorem injOn_insert {f : α → β} {s : Set α} {a : α} (has : a ∉ s) :
    Set.InjOn f (insert a s) ↔ Set.InjOn f s ∧ f a ∉ f '' s := by
  rw [← union_singleton, injOn_union (disjoint_singleton_right.2 has)]
  simp
#align set.inj_on_insert Set.injOn_insert

theorem injective_iff_injOn_univ : Injective f ↔ InjOn f univ :=
  ⟨fun h _ _ _ _ hxy => h hxy, fun h _ _ heq => h trivial trivial heq⟩
#align set.injective_iff_inj_on_univ Set.injective_iff_injOn_univ

theorem injOn_of_injective (h : Injective f) {s : Set α} : InjOn f s := fun _ _ _ _ hxy => h hxy
#align set.inj_on_of_injective Set.injOn_of_injective

alias _root_.Function.Injective.injOn := injOn_of_injective
#align function.injective.inj_on Function.Injective.injOn

-- A specialization of `injOn_of_injective` for `Subtype.val`.
theorem injOn_subtype_val {s : Set { x // p x }} : Set.InjOn Subtype.val s :=
  Subtype.coe_injective.injOn

lemma injOn_id (s : Set α) : InjOn id s := injective_id.injOn
#align set.inj_on_id Set.injOn_id

theorem InjOn.comp (hg : InjOn g t) (hf : InjOn f s) (h : MapsTo f s t) : InjOn (g ∘ f) s :=
  fun _ hx _ hy heq => hf hx hy <| hg (h hx) (h hy) heq
#align set.inj_on.comp Set.InjOn.comp

lemma InjOn.image_of_comp (h : InjOn (g ∘ f) s) : InjOn g (f '' s) :=
  forall_mem_image.2 fun _x hx ↦ forall_mem_image.2 fun _y hy heq ↦ congr_arg f <| h hx hy heq

lemma InjOn.iterate {f : α → α} {s : Set α} (h : InjOn f s) (hf : MapsTo f s s) :
    ∀ n, InjOn f^[n] s
  | 0 => injOn_id _
  | (n + 1) => (h.iterate hf n).comp h hf
#align set.inj_on.iterate Set.InjOn.iterate

lemma injOn_of_subsingleton [Subsingleton α] (f : α → β) (s : Set α) : InjOn f s :=
  (injective_of_subsingleton _).injOn
#align set.inj_on_of_subsingleton Set.injOn_of_subsingleton

theorem _root_.Function.Injective.injOn_range (h : Injective (g ∘ f)) : InjOn g (range f) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ H
  exact congr_arg f (h H)
#align function.injective.inj_on_range Function.Injective.injOn_range

theorem injOn_iff_injective : InjOn f s ↔ Injective (s.restrict f) :=
  ⟨fun H a b h => Subtype.eq <| H a.2 b.2 h, fun H a as b bs h =>
    congr_arg Subtype.val <| @H ⟨a, as⟩ ⟨b, bs⟩ h⟩
#align set.inj_on_iff_injective Set.injOn_iff_injective

alias ⟨InjOn.injective, _⟩ := Set.injOn_iff_injective
#align set.inj_on.injective Set.InjOn.injective

theorem MapsTo.restrict_inj (h : MapsTo f s t) : Injective (h.restrict f s t) ↔ InjOn f s := by
  rw [h.restrict_eq_codRestrict, injective_codRestrict, injOn_iff_injective]
#align set.maps_to.restrict_inj Set.MapsTo.restrict_inj

theorem exists_injOn_iff_injective [Nonempty β] :
    (∃ f : α → β, InjOn f s) ↔ ∃ f : s → β, Injective f :=
  ⟨fun ⟨f, hf⟩ => ⟨_, hf.injective⟩,
   fun ⟨f, hf⟩ => by
    lift f to α → β using trivial
    exact ⟨f, injOn_iff_injective.2 hf⟩⟩
#align set.exists_inj_on_iff_injective Set.exists_injOn_iff_injective

theorem injOn_preimage {B : Set (Set β)} (hB : B ⊆ 𝒫 range f) : InjOn (preimage f) B :=
  fun s hs t ht hst => (preimage_eq_preimage' (@hB s hs) (@hB t ht)).1 hst
-- Porting note: is there a semi-implicit variable problem with `⊆`?
#align set.inj_on_preimage Set.injOn_preimage

theorem InjOn.mem_of_mem_image {x} (hf : InjOn f s) (hs : s₁ ⊆ s) (h : x ∈ s) (h₁ : f x ∈ f '' s₁) :
    x ∈ s₁ :=
  let ⟨_, h', Eq⟩ := h₁
  hf (hs h') h Eq ▸ h'
#align set.inj_on.mem_of_mem_image Set.InjOn.mem_of_mem_image

theorem InjOn.mem_image_iff {x} (hf : InjOn f s) (hs : s₁ ⊆ s) (hx : x ∈ s) :
    f x ∈ f '' s₁ ↔ x ∈ s₁ :=
  ⟨hf.mem_of_mem_image hs hx, mem_image_of_mem f⟩
#align set.inj_on.mem_image_iff Set.InjOn.mem_image_iff

theorem InjOn.preimage_image_inter (hf : InjOn f s) (hs : s₁ ⊆ s) : f ⁻¹' (f '' s₁) ∩ s = s₁ :=
  ext fun _ => ⟨fun ⟨h₁, h₂⟩ => hf.mem_of_mem_image hs h₂ h₁, fun h => ⟨mem_image_of_mem _ h, hs h⟩⟩
#align set.inj_on.preimage_image_inter Set.InjOn.preimage_image_inter

theorem EqOn.cancel_left (h : s.EqOn (g ∘ f₁) (g ∘ f₂)) (hg : t.InjOn g) (hf₁ : s.MapsTo f₁ t)
    (hf₂ : s.MapsTo f₂ t) : s.EqOn f₁ f₂ := fun _ ha => hg (hf₁ ha) (hf₂ ha) (h ha)
#align set.eq_on.cancel_left Set.EqOn.cancel_left

theorem InjOn.cancel_left (hg : t.InjOn g) (hf₁ : s.MapsTo f₁ t) (hf₂ : s.MapsTo f₂ t) :
    s.EqOn (g ∘ f₁) (g ∘ f₂) ↔ s.EqOn f₁ f₂ :=
  ⟨fun h => h.cancel_left hg hf₁ hf₂, EqOn.comp_left⟩
#align set.inj_on.cancel_left Set.InjOn.cancel_left

lemma InjOn.image_inter {s t u : Set α} (hf : u.InjOn f) (hs : s ⊆ u) (ht : t ⊆ u) :
    f '' (s ∩ t) = f '' s ∩ f '' t := by
  apply Subset.antisymm (image_inter_subset _ _ _)
  intro x ⟨⟨y, ys, hy⟩, ⟨z, zt, hz⟩⟩
  have : y = z := by
    apply hf (hs ys) (ht zt)
    rwa [← hz] at hy
  rw [← this] at zt
  exact ⟨y, ⟨ys, zt⟩, hy⟩
#align set.inj_on.image_inter Set.InjOn.image_inter

lemma InjOn.image (h : s.InjOn f) : s.powerset.InjOn (image f) :=
  fun s₁ hs₁ s₂ hs₂ h' ↦ by rw [← h.preimage_image_inter hs₁, h', h.preimage_image_inter hs₂]

theorem InjOn.image_eq_image_iff (h : s.InjOn f) (h₁ : s₁ ⊆ s) (h₂ : s₂ ⊆ s) :
    f '' s₁ = f '' s₂ ↔ s₁ = s₂ :=
  h.image.eq_iff h₁ h₂

lemma InjOn.image_subset_image_iff (h : s.InjOn f) (h₁ : s₁ ⊆ s) (h₂ : s₂ ⊆ s) :
    f '' s₁ ⊆ f '' s₂ ↔ s₁ ⊆ s₂ := by
  refine' ⟨fun h' ↦ _, image_subset _⟩
  rw [← h.preimage_image_inter h₁, ← h.preimage_image_inter h₂]
  exact inter_subset_inter_left _ (preimage_mono h')

lemma InjOn.image_ssubset_image_iff (h : s.InjOn f) (h₁ : s₁ ⊆ s) (h₂ : s₂ ⊆ s) :
    f '' s₁ ⊂ f '' s₂ ↔ s₁ ⊂ s₂ := by
  simp_rw [ssubset_def, h.image_subset_image_iff h₁ h₂, h.image_subset_image_iff h₂ h₁]

-- TODO: can this move to a better place?
theorem _root_.Disjoint.image {s t u : Set α} {f : α → β} (h : Disjoint s t) (hf : u.InjOn f)
    (hs : s ⊆ u) (ht : t ⊆ u) : Disjoint (f '' s) (f '' t) := by
  rw [disjoint_iff_inter_eq_empty] at h ⊢
  rw [← hf.image_inter hs ht, h, image_empty]
#align disjoint.image Disjoint.image

lemma InjOn.image_diff {t : Set α} (h : s.InjOn f) : f '' (s \ t) = f '' s \ f '' (s ∩ t) := by
  refine subset_antisymm (subset_diff.2 ⟨image_subset f diff_subset, ?_⟩)
    (diff_subset_iff.2 (by rw [← image_union, inter_union_diff]))
  exact Disjoint.image disjoint_sdiff_inter h diff_subset inter_subset_left

lemma InjOn.image_diff_subset {f : α → β} {t : Set α} (h : InjOn f s) (hst : t ⊆ s) :
    f '' (s \ t) = f '' s \ f '' t := by
  rw [h.image_diff, inter_eq_self_of_subset_right hst]

theorem InjOn.imageFactorization_injective (h : InjOn f s) :
    Injective (s.imageFactorization f) :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ h' ↦ by simpa [imageFactorization, h.eq_iff hx hy] using h'

@[simp] theorem imageFactorization_injective_iff : Injective (s.imageFactorization f) ↔ InjOn f s :=
  ⟨fun h x hx y hy _ ↦ by simpa using @h ⟨x, hx⟩ ⟨y, hy⟩ (by simpa [imageFactorization]),
    InjOn.imageFactorization_injective⟩

end injOn

section graphOn

@[simp] lemma graphOn_empty (f : α → β) : graphOn f ∅ = ∅ := image_empty _

@[simp]
lemma graphOn_union (f : α → β) (s t : Set α) : graphOn f (s ∪ t) = graphOn f s ∪ graphOn f t :=
  image_union ..

@[simp]
lemma graphOn_singleton (f : α → β) (x : α) : graphOn f {x} = {(x, f x)} :=
  image_singleton ..

@[simp]
lemma graphOn_insert (f : α → β) (x : α) (s : Set α) :
    graphOn f (insert x s) = insert (x, f x) (graphOn f s) :=
  image_insert_eq ..

@[simp]
lemma image_fst_graphOn (f : α → β) (s : Set α) : Prod.fst '' graphOn f s = s := by
  simp [graphOn, image_image]

lemma exists_eq_graphOn_image_fst [Nonempty β] {s : Set (α × β)} :
    (∃ f : α → β, s = graphOn f (Prod.fst '' s)) ↔ InjOn Prod.fst s := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨f, hf⟩
    rw [hf]
    exact InjOn.image_of_comp <| injOn_id _
  · have : ∀ x ∈ Prod.fst '' s, ∃ y, (x, y) ∈ s := forall_mem_image.2 fun (x, y) h ↦ ⟨y, h⟩
    choose! f hf using this
    rw [forall_mem_image] at hf
    use f
    rw [graphOn, image_image, EqOn.image_eq_self]
    exact fun x hx ↦ h (hf hx) hx rfl

lemma exists_eq_graphOn [Nonempty β] {s : Set (α × β)} :
    (∃ f t, s = graphOn f t) ↔ InjOn Prod.fst s :=
  .trans ⟨fun ⟨f, t, hs⟩ ↦ ⟨f, by rw [hs, image_fst_graphOn]⟩, fun ⟨f, hf⟩ ↦ ⟨f, _, hf⟩⟩
    exists_eq_graphOn_image_fst

end graphOn

/-! ### Surjectivity on a set -/
section surjOn

theorem SurjOn.subset_range (h : SurjOn f s t) : t ⊆ range f :=
  Subset.trans h <| image_subset_range f s
#align set.surj_on.subset_range Set.SurjOn.subset_range

theorem surjOn_iff_exists_map_subtype :
    SurjOn f s t ↔ ∃ (t' : Set β) (g : s → t'), t ⊆ t' ∧ Surjective g ∧ ∀ x : s, f x = g x :=
  ⟨fun h =>
    ⟨_, (mapsTo_image f s).restrict f s _, h, surjective_mapsTo_image_restrict _ _, fun _ => rfl⟩,
    fun ⟨t', g, htt', hg, hfg⟩ y hy =>
    let ⟨x, hx⟩ := hg ⟨y, htt' hy⟩
    ⟨x, x.2, by rw [hfg, hx, Subtype.coe_mk]⟩⟩
#align set.surj_on_iff_exists_map_subtype Set.surjOn_iff_exists_map_subtype

theorem surjOn_empty (f : α → β) (s : Set α) : SurjOn f s ∅ :=
  empty_subset _
#align set.surj_on_empty Set.surjOn_empty

@[simp] lemma surjOn_singleton : SurjOn f s {b} ↔ b ∈ f '' s := singleton_subset_iff
#align set.surj_on_singleton Set.surjOn_singleton

theorem surjOn_image (f : α → β) (s : Set α) : SurjOn f s (f '' s) :=
  Subset.rfl
#align set.surj_on_image Set.surjOn_image

theorem SurjOn.comap_nonempty (h : SurjOn f s t) (ht : t.Nonempty) : s.Nonempty :=
  (ht.mono h).of_image
#align set.surj_on.comap_nonempty Set.SurjOn.comap_nonempty

theorem SurjOn.congr (h : SurjOn f₁ s t) (H : EqOn f₁ f₂ s) : SurjOn f₂ s t := by
  rwa [SurjOn, ← H.image_eq]
#align set.surj_on.congr Set.SurjOn.congr

theorem EqOn.surjOn_iff (h : EqOn f₁ f₂ s) : SurjOn f₁ s t ↔ SurjOn f₂ s t :=
  ⟨fun H => H.congr h, fun H => H.congr h.symm⟩
#align set.eq_on.surj_on_iff Set.EqOn.surjOn_iff

theorem SurjOn.mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) (hf : SurjOn f s₁ t₂) : SurjOn f s₂ t₁ :=
  Subset.trans ht <| Subset.trans hf <| image_subset _ hs
#align set.surj_on.mono Set.SurjOn.mono

theorem SurjOn.union (h₁ : SurjOn f s t₁) (h₂ : SurjOn f s t₂) : SurjOn f s (t₁ ∪ t₂) := fun _ hx =>
  hx.elim (fun hx => h₁ hx) fun hx => h₂ hx
#align set.surj_on.union Set.SurjOn.union

theorem SurjOn.union_union (h₁ : SurjOn f s₁ t₁) (h₂ : SurjOn f s₂ t₂) :
    SurjOn f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
  (h₁.mono subset_union_left (Subset.refl _)).union
    (h₂.mono subset_union_right (Subset.refl _))
#align set.surj_on.union_union Set.SurjOn.union_union

theorem SurjOn.inter_inter (h₁ : SurjOn f s₁ t₁) (h₂ : SurjOn f s₂ t₂) (h : InjOn f (s₁ ∪ s₂)) :
    SurjOn f (s₁ ∩ s₂) (t₁ ∩ t₂) := by
  intro y hy
  rcases h₁ hy.1 with ⟨x₁, hx₁, rfl⟩
  rcases h₂ hy.2 with ⟨x₂, hx₂, heq⟩
  obtain rfl : x₁ = x₂ := h (Or.inl hx₁) (Or.inr hx₂) heq.symm
  exact mem_image_of_mem f ⟨hx₁, hx₂⟩
#align set.surj_on.inter_inter Set.SurjOn.inter_inter

theorem SurjOn.inter (h₁ : SurjOn f s₁ t) (h₂ : SurjOn f s₂ t) (h : InjOn f (s₁ ∪ s₂)) :
    SurjOn f (s₁ ∩ s₂) t :=
  inter_self t ▸ h₁.inter_inter h₂ h
#align set.surj_on.inter Set.SurjOn.inter

-- Porting note: Why does `simp` not call `refl` by itself?
lemma surjOn_id (s : Set α) : SurjOn id s s := by simp [SurjOn, subset_rfl]
#align set.surj_on_id Set.surjOn_id

theorem SurjOn.comp (hg : SurjOn g t p) (hf : SurjOn f s t) : SurjOn (g ∘ f) s p :=
  Subset.trans hg <| Subset.trans (image_subset g hf) <| image_comp g f s ▸ Subset.refl _
#align set.surj_on.comp Set.SurjOn.comp

lemma SurjOn.iterate {f : α → α} {s : Set α} (h : SurjOn f s s) : ∀ n, SurjOn f^[n] s s
  | 0 => surjOn_id _
  | (n + 1) => (h.iterate n).comp h
#align set.surj_on.iterate Set.SurjOn.iterate

lemma SurjOn.comp_left (hf : SurjOn f s t) (g : β → γ) : SurjOn (g ∘ f) s (g '' t) := by
  rw [SurjOn, image_comp g f]; exact image_subset _ hf
#align set.surj_on.comp_left Set.SurjOn.comp_left

lemma SurjOn.comp_right {s : Set β} {t : Set γ} (hf : Surjective f) (hg : SurjOn g s t) :
    SurjOn (g ∘ f) (f ⁻¹' s) t := by
  rwa [SurjOn, image_comp g f, image_preimage_eq _ hf]
#align set.surj_on.comp_right Set.SurjOn.comp_right

lemma surjOn_of_subsingleton' [Subsingleton β] (f : α → β) (h : t.Nonempty → s.Nonempty) :
    SurjOn f s t :=
  fun _ ha ↦ Subsingleton.mem_iff_nonempty.2 <| (h ⟨_, ha⟩).image _
#align set.surj_on_of_subsingleton' Set.surjOn_of_subsingleton'

lemma surjOn_of_subsingleton [Subsingleton α] (f : α → α) (s : Set α) : SurjOn f s s :=
  surjOn_of_subsingleton' _ id
#align set.surj_on_of_subsingleton Set.surjOn_of_subsingleton

theorem surjective_iff_surjOn_univ : Surjective f ↔ SurjOn f univ univ := by
  simp [Surjective, SurjOn, subset_def]
#align set.surjective_iff_surj_on_univ Set.surjective_iff_surjOn_univ

theorem surjOn_iff_surjective : SurjOn f s univ ↔ Surjective (s.restrict f) :=
  ⟨fun H b =>
    let ⟨a, as, e⟩ := @H b trivial
    ⟨⟨a, as⟩, e⟩,
    fun H b _ =>
    let ⟨⟨a, as⟩, e⟩ := H b
    ⟨a, as, e⟩⟩
#align set.surj_on_iff_surjective Set.surjOn_iff_surjective

@[simp]
theorem MapsTo.restrict_surjective_iff (h : MapsTo f s t) :
    Surjective (MapsTo.restrict _ _ _ h) ↔ SurjOn f s t := by
  refine ⟨fun h' b hb ↦ ?_, fun h' ⟨b, hb⟩ ↦ ?_⟩
  · obtain ⟨⟨a, ha⟩, ha'⟩ := h' ⟨b, hb⟩
    replace ha' : f a = b := by simpa [Subtype.ext_iff] using ha'
    rw [← ha']
    exact mem_image_of_mem f ha
  · obtain ⟨a, ha, rfl⟩ := h' hb
    exact ⟨⟨a, ha⟩, rfl⟩

theorem SurjOn.image_eq_of_mapsTo (h₁ : SurjOn f s t) (h₂ : MapsTo f s t) : f '' s = t :=
  eq_of_subset_of_subset h₂.image_subset h₁
#align set.surj_on.image_eq_of_maps_to Set.SurjOn.image_eq_of_mapsTo

theorem image_eq_iff_surjOn_mapsTo : f '' s = t ↔ s.SurjOn f t ∧ s.MapsTo f t := by
  refine ⟨?_, fun h => h.1.image_eq_of_mapsTo h.2⟩
  rintro rfl
  exact ⟨s.surjOn_image f, s.mapsTo_image f⟩
#align set.image_eq_iff_surj_on_maps_to Set.image_eq_iff_surjOn_mapsTo

lemma SurjOn.image_preimage (h : Set.SurjOn f s t) (ht : t₁ ⊆ t) : f '' (f ⁻¹' t₁) = t₁ :=
  image_preimage_eq_iff.2 fun _ hx ↦ mem_range_of_mem_image f s <| h <| ht hx

theorem SurjOn.mapsTo_compl (h : SurjOn f s t) (h' : Injective f) : MapsTo f sᶜ tᶜ :=
  fun _ hs ht =>
  let ⟨_, hx', HEq⟩ := h ht
  hs <| h' HEq ▸ hx'
#align set.surj_on.maps_to_compl Set.SurjOn.mapsTo_compl

theorem MapsTo.surjOn_compl (h : MapsTo f s t) (h' : Surjective f) : SurjOn f sᶜ tᶜ :=
  h'.forall.2 fun _ ht => (mem_image_of_mem _) fun hs => ht (h hs)
#align set.maps_to.surj_on_compl Set.MapsTo.surjOn_compl

theorem EqOn.cancel_right (hf : s.EqOn (g₁ ∘ f) (g₂ ∘ f)) (hf' : s.SurjOn f t) : t.EqOn g₁ g₂ := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := hf' hb
  exact hf ha
#align set.eq_on.cancel_right Set.EqOn.cancel_right

theorem SurjOn.cancel_right (hf : s.SurjOn f t) (hf' : s.MapsTo f t) :
    s.EqOn (g₁ ∘ f) (g₂ ∘ f) ↔ t.EqOn g₁ g₂ :=
  ⟨fun h => h.cancel_right hf, fun h => h.comp_right hf'⟩
#align set.surj_on.cancel_right Set.SurjOn.cancel_right

theorem eqOn_comp_right_iff : s.EqOn (g₁ ∘ f) (g₂ ∘ f) ↔ (f '' s).EqOn g₁ g₂ :=
  (s.surjOn_image f).cancel_right <| s.mapsTo_image f
#align set.eq_on_comp_right_iff Set.eqOn_comp_right_iff

theorem SurjOn.forall {p : β → Prop} (hf : s.SurjOn f t) (hf' : s.MapsTo f t) :
    (∀ y ∈ t, p y) ↔ (∀ x ∈ s, p (f x)) :=
  ⟨fun H x hx ↦ H (f x) (hf' hx), fun H _y hy ↦ let ⟨x, hx, hxy⟩ := hf hy; hxy ▸ H x hx⟩

end surjOn

/-! ### Bijectivity -/
section bijOn

theorem BijOn.mapsTo (h : BijOn f s t) : MapsTo f s t :=
  h.left
#align set.bij_on.maps_to Set.BijOn.mapsTo

theorem BijOn.injOn (h : BijOn f s t) : InjOn f s :=
  h.right.left
#align set.bij_on.inj_on Set.BijOn.injOn

theorem BijOn.surjOn (h : BijOn f s t) : SurjOn f s t :=
  h.right.right
#align set.bij_on.surj_on Set.BijOn.surjOn

theorem BijOn.mk (h₁ : MapsTo f s t) (h₂ : InjOn f s) (h₃ : SurjOn f s t) : BijOn f s t :=
  ⟨h₁, h₂, h₃⟩
#align set.bij_on.mk Set.BijOn.mk

theorem bijOn_empty (f : α → β) : BijOn f ∅ ∅ :=
  ⟨mapsTo_empty f ∅, injOn_empty f, surjOn_empty f ∅⟩
#align set.bij_on_empty Set.bijOn_empty

@[simp] lemma bijOn_singleton : BijOn f {a} {b} ↔ f a = b := by simp [BijOn, eq_comm]
#align set.bij_on_singleton Set.bijOn_singleton

theorem BijOn.inter_mapsTo (h₁ : BijOn f s₁ t₁) (h₂ : MapsTo f s₂ t₂) (h₃ : s₁ ∩ f ⁻¹' t₂ ⊆ s₂) :
    BijOn f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
  ⟨h₁.mapsTo.inter_inter h₂, h₁.injOn.mono inter_subset_left, fun _ hy =>
    let ⟨x, hx, hxy⟩ := h₁.surjOn hy.1
    ⟨x, ⟨hx, h₃ ⟨hx, hxy.symm.subst hy.2⟩⟩, hxy⟩⟩
#align set.bij_on.inter_maps_to Set.BijOn.inter_mapsTo

theorem MapsTo.inter_bijOn (h₁ : MapsTo f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h₃ : s₂ ∩ f ⁻¹' t₁ ⊆ s₁) :
    BijOn f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
  inter_comm s₂ s₁ ▸ inter_comm t₂ t₁ ▸ h₂.inter_mapsTo h₁ h₃
#align set.maps_to.inter_bij_on Set.MapsTo.inter_bijOn

theorem BijOn.inter (h₁ : BijOn f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h : InjOn f (s₁ ∪ s₂)) :
    BijOn f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
  ⟨h₁.mapsTo.inter_inter h₂.mapsTo, h₁.injOn.mono inter_subset_left,
    h₁.surjOn.inter_inter h₂.surjOn h⟩
#align set.bij_on.inter Set.BijOn.inter

theorem BijOn.union (h₁ : BijOn f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h : InjOn f (s₁ ∪ s₂)) :
    BijOn f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
  ⟨h₁.mapsTo.union_union h₂.mapsTo, h, h₁.surjOn.union_union h₂.surjOn⟩
#align set.bij_on.union Set.BijOn.union

theorem BijOn.subset_range (h : BijOn f s t) : t ⊆ range f :=
  h.surjOn.subset_range
#align set.bij_on.subset_range Set.BijOn.subset_range

theorem InjOn.bijOn_image (h : InjOn f s) : BijOn f s (f '' s) :=
  BijOn.mk (mapsTo_image f s) h (Subset.refl _)
#align set.inj_on.bij_on_image Set.InjOn.bijOn_image

theorem BijOn.congr (h₁ : BijOn f₁ s t) (h : EqOn f₁ f₂ s) : BijOn f₂ s t :=
  BijOn.mk (h₁.mapsTo.congr h) (h₁.injOn.congr h) (h₁.surjOn.congr h)
#align set.bij_on.congr Set.BijOn.congr

theorem EqOn.bijOn_iff (H : EqOn f₁ f₂ s) : BijOn f₁ s t ↔ BijOn f₂ s t :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩
#align set.eq_on.bij_on_iff Set.EqOn.bijOn_iff

theorem BijOn.image_eq (h : BijOn f s t) : f '' s = t :=
  h.surjOn.image_eq_of_mapsTo h.mapsTo
#align set.bij_on.image_eq Set.BijOn.image_eq

lemma BijOn.forall {p : β → Prop} (hf : BijOn f s t) : (∀ b ∈ t, p b) ↔ ∀ a ∈ s, p (f a) where
  mp h a ha := h _ $ hf.mapsTo ha
  mpr h b hb := by obtain ⟨a, ha, rfl⟩ := hf.surjOn hb; exact h _ ha

lemma BijOn.exists {p : β → Prop} (hf : BijOn f s t) : (∃ b ∈ t, p b) ↔ ∃ a ∈ s, p (f a) where
  mp := by rintro ⟨b, hb, h⟩; obtain ⟨a, ha, rfl⟩ := hf.surjOn hb; exact ⟨a, ha, h⟩
  mpr := by rintro ⟨a, ha, h⟩; exact ⟨f a, hf.mapsTo ha, h⟩

lemma _root_.Equiv.image_eq_iff_bijOn (e : α ≃ β) : e '' s = t ↔ BijOn e s t :=
  ⟨fun h ↦ ⟨(mapsTo_image e s).mono_right h.subset, e.injective.injOn, h ▸ surjOn_image e s⟩,
  BijOn.image_eq⟩

lemma bijOn_id (s : Set α) : BijOn id s s := ⟨s.mapsTo_id, s.injOn_id, s.surjOn_id⟩
#align set.bij_on_id Set.bijOn_id

theorem BijOn.comp (hg : BijOn g t p) (hf : BijOn f s t) : BijOn (g ∘ f) s p :=
  BijOn.mk (hg.mapsTo.comp hf.mapsTo) (hg.injOn.comp hf.injOn hf.mapsTo) (hg.surjOn.comp hf.surjOn)
#align set.bij_on.comp Set.BijOn.comp

lemma BijOn.iterate {f : α → α} {s : Set α} (h : BijOn f s s) : ∀ n, BijOn f^[n] s s
  | 0 => s.bijOn_id
  | (n + 1) => (h.iterate n).comp h
#align set.bij_on.iterate Set.BijOn.iterate

lemma bijOn_of_subsingleton' [Subsingleton α] [Subsingleton β] (f : α → β)
    (h : s.Nonempty ↔ t.Nonempty) : BijOn f s t :=
  ⟨mapsTo_of_subsingleton' _ h.1, injOn_of_subsingleton _ _, surjOn_of_subsingleton' _ h.2⟩
#align set.bij_on_of_subsingleton' Set.bijOn_of_subsingleton'

lemma bijOn_of_subsingleton [Subsingleton α] (f : α → α) (s : Set α) : BijOn f s s :=
  bijOn_of_subsingleton' _ Iff.rfl
#align set.bij_on_of_subsingleton Set.bijOn_of_subsingleton

theorem BijOn.bijective (h : BijOn f s t) : Bijective (h.mapsTo.restrict f s t) :=
  ⟨fun x y h' => Subtype.ext <| h.injOn x.2 y.2 <| Subtype.ext_iff.1 h', fun ⟨_, hy⟩ =>
    let ⟨x, hx, hxy⟩ := h.surjOn hy
    ⟨⟨x, hx⟩, Subtype.eq hxy⟩⟩
#align set.bij_on.bijective Set.BijOn.bijective

theorem bijective_iff_bijOn_univ : Bijective f ↔ BijOn f univ univ :=
  Iff.intro
    (fun h =>
      let ⟨inj, surj⟩ := h
      ⟨mapsTo_univ f _, inj.injOn, Iff.mp surjective_iff_surjOn_univ surj⟩)
    fun h =>
    let ⟨_map, inj, surj⟩ := h
    ⟨Iff.mpr injective_iff_injOn_univ inj, Iff.mpr surjective_iff_surjOn_univ surj⟩
#align set.bijective_iff_bij_on_univ Set.bijective_iff_bijOn_univ

alias ⟨_root_.Function.Bijective.bijOn_univ, _⟩ := bijective_iff_bijOn_univ
#align function.bijective.bij_on_univ Function.Bijective.bijOn_univ

theorem BijOn.compl (hst : BijOn f s t) (hf : Bijective f) : BijOn f sᶜ tᶜ :=
  ⟨hst.surjOn.mapsTo_compl hf.1, hf.1.injOn, hst.mapsTo.surjOn_compl hf.2⟩
#align set.bij_on.compl Set.BijOn.compl

theorem BijOn.subset_right {r : Set β} (hf : BijOn f s t) (hrt : r ⊆ t) :
    BijOn f (s ∩ f ⁻¹' r) r := by
  refine ⟨inter_subset_right, hf.injOn.mono inter_subset_left, fun x hx ↦ ?_⟩
  obtain ⟨y, hy, rfl⟩ := hf.surjOn (hrt hx)
  exact ⟨y, ⟨hy, hx⟩, rfl⟩

theorem BijOn.subset_left {r : Set α} (hf : BijOn f s t) (hrs : r ⊆ s) :
    BijOn f r (f '' r) :=
  (hf.injOn.mono hrs).bijOn_image

end bijOn

/-! ### left inverse -/
namespace LeftInvOn

theorem eqOn (h : LeftInvOn f' f s) : EqOn (f' ∘ f) id s :=
  h
#align set.left_inv_on.eq_on Set.LeftInvOn.eqOn

theorem eq (h : LeftInvOn f' f s) {x} (hx : x ∈ s) : f' (f x) = x :=
  h hx
#align set.left_inv_on.eq Set.LeftInvOn.eq

theorem congr_left (h₁ : LeftInvOn f₁' f s) {t : Set β} (h₁' : MapsTo f s t)
    (heq : EqOn f₁' f₂' t) : LeftInvOn f₂' f s := fun _ hx => heq (h₁' hx) ▸ h₁ hx
#align set.left_inv_on.congr_left Set.LeftInvOn.congr_left

theorem congr_right (h₁ : LeftInvOn f₁' f₁ s) (heq : EqOn f₁ f₂ s) : LeftInvOn f₁' f₂ s :=
  fun _ hx => heq hx ▸ h₁ hx
#align set.left_inv_on.congr_right Set.LeftInvOn.congr_right

theorem injOn (h : LeftInvOn f₁' f s) : InjOn f s := fun x₁ h₁ x₂ h₂ heq =>
  calc
    x₁ = f₁' (f x₁) := Eq.symm <| h h₁
    _ = f₁' (f x₂) := congr_arg f₁' heq
    _ = x₂ := h h₂
#align set.left_inv_on.inj_on Set.LeftInvOn.injOn

theorem surjOn (h : LeftInvOn f' f s) (hf : MapsTo f s t) : SurjOn f' t s := fun x hx =>
  ⟨f x, hf hx, h hx⟩
#align set.left_inv_on.surj_on Set.LeftInvOn.surjOn

theorem mapsTo (h : LeftInvOn f' f s) (hf : SurjOn f s t) :
    MapsTo f' t s := fun y hy => by
  let ⟨x, hs, hx⟩ := hf hy
  rwa [← hx, h hs]
#align set.left_inv_on.maps_to Set.LeftInvOn.mapsTo

lemma _root_.Set.leftInvOn_id (s : Set α) : LeftInvOn id id s := fun _ _ ↦ rfl
#align set.left_inv_on_id Set.leftInvOn_id

theorem comp (hf' : LeftInvOn f' f s) (hg' : LeftInvOn g' g t) (hf : MapsTo f s t) :
    LeftInvOn (f' ∘ g') (g ∘ f) s := fun x h =>
  calc
    (f' ∘ g') ((g ∘ f) x) = f' (f x) := congr_arg f' (hg' (hf h))
    _ = x := hf' h
#align set.left_inv_on.comp Set.LeftInvOn.comp

theorem mono (hf : LeftInvOn f' f s) (ht : s₁ ⊆ s) : LeftInvOn f' f s₁ := fun _ hx =>
  hf (ht hx)
#align set.left_inv_on.mono Set.LeftInvOn.mono

theorem image_inter' (hf : LeftInvOn f' f s) : f '' (s₁ ∩ s) = f' ⁻¹' s₁ ∩ f '' s := by
  apply Subset.antisymm
  · rintro _ ⟨x, ⟨h₁, h⟩, rfl⟩
    exact ⟨by rwa [mem_preimage, hf h], mem_image_of_mem _ h⟩
  · rintro _ ⟨h₁, ⟨x, h, rfl⟩⟩
    exact mem_image_of_mem _ ⟨by rwa [← hf h], h⟩
#align set.left_inv_on.image_inter' Set.LeftInvOn.image_inter'

theorem image_inter (hf : LeftInvOn f' f s) :
    f '' (s₁ ∩ s) = f' ⁻¹' (s₁ ∩ s) ∩ f '' s := by
  rw [hf.image_inter']
  refine Subset.antisymm ?_ (inter_subset_inter_left _ (preimage_mono inter_subset_left))
  rintro _ ⟨h₁, x, hx, rfl⟩; exact ⟨⟨h₁, by rwa [hf hx]⟩, mem_image_of_mem _ hx⟩
#align set.left_inv_on.image_inter Set.LeftInvOn.image_inter

theorem image_image (hf : LeftInvOn f' f s) : f' '' (f '' s) = s := by
  rw [Set.image_image, image_congr hf, image_id']
#align set.left_inv_on.image_image Set.LeftInvOn.image_image

theorem image_image' (hf : LeftInvOn f' f s) (hs : s₁ ⊆ s) : f' '' (f '' s₁) = s₁ :=
  (hf.mono hs).image_image
#align set.left_inv_on.image_image' Set.LeftInvOn.image_image'

end LeftInvOn

/-! ### Right inverse -/
section RightInvOn
namespace RightInvOn

theorem eqOn (h : RightInvOn f' f t) : EqOn (f ∘ f') id t :=
  h
#align set.right_inv_on.eq_on Set.RightInvOn.eqOn

theorem eq (h : RightInvOn f' f t) {y} (hy : y ∈ t) : f (f' y) = y :=
  h hy
#align set.right_inv_on.eq Set.RightInvOn.eq

theorem _root_.Set.LeftInvOn.rightInvOn_image (h : LeftInvOn f' f s) : RightInvOn f' f (f '' s) :=
  fun _y ⟨_x, hx, heq⟩ => heq ▸ (congr_arg f <| h.eq hx)
#align set.left_inv_on.right_inv_on_image Set.LeftInvOn.rightInvOn_image

theorem congr_left (h₁ : RightInvOn f₁' f t) (heq : EqOn f₁' f₂' t) :
    RightInvOn f₂' f t :=
  h₁.congr_right heq
#align set.right_inv_on.congr_left Set.RightInvOn.congr_left

theorem congr_right (h₁ : RightInvOn f' f₁ t) (hg : MapsTo f' t s) (heq : EqOn f₁ f₂ s) :
    RightInvOn f' f₂ t :=
  LeftInvOn.congr_left h₁ hg heq
#align set.right_inv_on.congr_right Set.RightInvOn.congr_right

theorem surjOn (hf : RightInvOn f' f t) (hf' : MapsTo f' t s) : SurjOn f s t :=
  LeftInvOn.surjOn hf hf'
#align set.right_inv_on.surj_on Set.RightInvOn.surjOn

theorem mapsTo (h : RightInvOn f' f t) (hf : SurjOn f' t s) : MapsTo f s t :=
  LeftInvOn.mapsTo h hf
#align set.right_inv_on.maps_to Set.RightInvOn.mapsTo

lemma _root_.Set.rightInvOn_id (s : Set α) : RightInvOn id id s := fun _ _ ↦ rfl
#align set.right_inv_on_id Set.rightInvOn_id

theorem comp (hf : RightInvOn f' f t) (hg : RightInvOn g' g p) (g'pt : MapsTo g' p t) :
    RightInvOn (f' ∘ g') (g ∘ f) p :=
  LeftInvOn.comp hg hf g'pt
#align set.right_inv_on.comp Set.RightInvOn.comp

theorem mono (hf : RightInvOn f' f t) (ht : t₁ ⊆ t) : RightInvOn f' f t₁ :=
  LeftInvOn.mono hf ht
#align set.right_inv_on.mono Set.RightInvOn.mono
end RightInvOn

theorem InjOn.rightInvOn_of_leftInvOn (hf : InjOn f s) (hf' : LeftInvOn f f' t)
    (h₁ : MapsTo f s t) (h₂ : MapsTo f' t s) : RightInvOn f f' s := fun _ h =>
  hf (h₂ <| h₁ h) h (hf' (h₁ h))
#align set.inj_on.right_inv_on_of_left_inv_on Set.InjOn.rightInvOn_of_leftInvOn

theorem eqOn_of_leftInvOn_of_rightInvOn (h₁ : LeftInvOn f₁' f s) (h₂ : RightInvOn f₂' f t)
    (h : MapsTo f₂' t s) : EqOn f₁' f₂' t := fun y hy =>
  calc
    f₁' y = (f₁' ∘ f ∘ f₂') y := congr_arg f₁' (h₂ hy).symm
    _ = f₂' y := h₁ (h hy)
#align set.eq_on_of_left_inv_on_of_right_inv_on Set.eqOn_of_leftInvOn_of_rightInvOn

theorem SurjOn.leftInvOn_of_rightInvOn (hf : SurjOn f s t) (hf' : RightInvOn f f' s) :
    LeftInvOn f f' t := fun y hy => by
  let ⟨x, hx, heq⟩ := hf hy
  rw [← heq, hf' hx]
#align set.surj_on.left_inv_on_of_right_inv_on Set.SurjOn.leftInvOn_of_rightInvOn

end RightInvOn

/-! ### Two-side inverses -/
namespace InvOn

lemma _root_.Set.invOn_id (s : Set α) : InvOn id id s s := ⟨s.leftInvOn_id, s.rightInvOn_id⟩
#align set.inv_on_id Set.invOn_id

lemma comp (hf : InvOn f' f s t) (hg : InvOn g' g t p) (fst : MapsTo f s t)
    (g'pt : MapsTo g' p t) :
    InvOn (f' ∘ g') (g ∘ f) s p :=
  ⟨hf.1.comp hg.1 fst, hf.2.comp hg.2 g'pt⟩
#align set.inv_on.comp Set.InvOn.comp

@[symm]
theorem symm (h : InvOn f' f s t) : InvOn f f' t s :=
  ⟨h.right, h.left⟩
#align set.inv_on.symm Set.InvOn.symm

theorem mono (h : InvOn f' f s t) (hs : s₁ ⊆ s) (ht : t₁ ⊆ t) : InvOn f' f s₁ t₁ :=
  ⟨h.1.mono hs, h.2.mono ht⟩
#align set.inv_on.mono Set.InvOn.mono

/-- If functions `f'` and `f` are inverse on `s` and `t`, `f` maps `s` into `t`, and `f'` maps `t`
into `s`, then `f` is a bijection between `s` and `t`. The `mapsTo` arguments can be deduced from
`surjOn` statements using `LeftInvOn.mapsTo` and `RightInvOn.mapsTo`. -/
theorem bijOn (h : InvOn f' f s t) (hf : MapsTo f s t) (hf' : MapsTo f' t s) : BijOn f s t :=
  ⟨hf, h.left.injOn, h.right.surjOn hf'⟩
#align set.inv_on.bij_on Set.InvOn.bijOn

end InvOn

end Set

/-! ### `invFunOn` is a left/right inverse -/
namespace Function

variable [Nonempty α] {s : Set α} {f : α → β} {a : α} {b : β}

attribute [local instance] Classical.propDecidable

/-- Construct the inverse for a function `f` on domain `s`. This function is a right inverse of `f`
on `f '' s`. For a computable version, see `Function.Embedding.invOfMemRange`. -/
noncomputable def invFunOn (f : α → β) (s : Set α) (b : β) : α :=
  if h : ∃ a, a ∈ s ∧ f a = b then Classical.choose h else Classical.choice ‹Nonempty α›
#align function.inv_fun_on Function.invFunOn

theorem invFunOn_pos (h : ∃ a ∈ s, f a = b) : invFunOn f s b ∈ s ∧ f (invFunOn f s b) = b := by
  rw [invFunOn, dif_pos h]
  exact Classical.choose_spec h
#align function.inv_fun_on_pos Function.invFunOn_pos

theorem invFunOn_mem (h : ∃ a ∈ s, f a = b) : invFunOn f s b ∈ s :=
  (invFunOn_pos h).left
#align function.inv_fun_on_mem Function.invFunOn_mem

theorem invFunOn_eq (h : ∃ a ∈ s, f a = b) : f (invFunOn f s b) = b :=
  (invFunOn_pos h).right
#align function.inv_fun_on_eq Function.invFunOn_eq

theorem invFunOn_neg (h : ¬∃ a ∈ s, f a = b) : invFunOn f s b = Classical.choice ‹Nonempty α› := by
  rw [invFunOn, dif_neg h]
#align function.inv_fun_on_neg Function.invFunOn_neg

@[simp]
theorem invFunOn_apply_mem (h : a ∈ s) : invFunOn f s (f a) ∈ s :=
  invFunOn_mem ⟨a, h, rfl⟩
#align function.inv_fun_on_apply_mem Function.invFunOn_apply_mem

theorem invFunOn_apply_eq (h : a ∈ s) : f (invFunOn f s (f a)) = f a :=
  invFunOn_eq ⟨a, h, rfl⟩
#align function.inv_fun_on_apply_eq Function.invFunOn_apply_eq

end Function

open Function

namespace Set

variable {s s₁ s₂ : Set α} {t : Set β} {f : α → β}

theorem InjOn.leftInvOn_invFunOn [Nonempty α] (h : InjOn f s) : LeftInvOn (invFunOn f s) f s :=
  fun _a ha => h (invFunOn_apply_mem ha) ha (invFunOn_apply_eq ha)
#align set.inj_on.left_inv_on_inv_fun_on Set.InjOn.leftInvOn_invFunOn

theorem InjOn.invFunOn_image [Nonempty α] (h : InjOn f s₂) (ht : s₁ ⊆ s₂) :
    invFunOn f s₂ '' (f '' s₁) = s₁ :=
  h.leftInvOn_invFunOn.image_image' ht
#align set.inj_on.inv_fun_on_image Set.InjOn.invFunOn_image

theorem _root_.Function.leftInvOn_invFunOn_of_subset_image_image [Nonempty α]
    (h : s ⊆ (invFunOn f s) '' (f '' s)) : LeftInvOn (invFunOn f s) f s :=
  fun x hx ↦ by
    obtain ⟨-, ⟨x, hx', rfl⟩, rfl⟩ := h hx
    rw [invFunOn_apply_eq (f := f) hx']

theorem injOn_iff_invFunOn_image_image_eq_self [Nonempty α] :
    InjOn f s ↔ (invFunOn f s) '' (f '' s) = s :=
  ⟨fun h ↦ h.invFunOn_image Subset.rfl, fun h ↦
    (Function.leftInvOn_invFunOn_of_subset_image_image h.symm.subset).injOn⟩

theorem _root_.Function.invFunOn_injOn_image [Nonempty α] (f : α → β) (s : Set α) :
    Set.InjOn (invFunOn f s) (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ he
  rw [← invFunOn_apply_eq (f := f) hx, he, invFunOn_apply_eq (f := f) hx']

theorem _root_.Function.invFunOn_image_image_subset [Nonempty α] (f : α → β) (s : Set α) :
    (invFunOn f s) '' (f '' s) ⊆ s := by
  rintro _ ⟨_, ⟨x,hx,rfl⟩, rfl⟩; exact invFunOn_apply_mem hx

theorem SurjOn.rightInvOn_invFunOn [Nonempty α] (h : SurjOn f s t) :
    RightInvOn (invFunOn f s) f t := fun _y hy => invFunOn_eq <| h hy
#align set.surj_on.right_inv_on_inv_fun_on Set.SurjOn.rightInvOn_invFunOn

theorem BijOn.invOn_invFunOn [Nonempty α] (h : BijOn f s t) : InvOn (invFunOn f s) f s t :=
  ⟨h.injOn.leftInvOn_invFunOn, h.surjOn.rightInvOn_invFunOn⟩
#align set.bij_on.inv_on_inv_fun_on Set.BijOn.invOn_invFunOn

theorem SurjOn.invOn_invFunOn [Nonempty α] (h : SurjOn f s t) :
    InvOn (invFunOn f s) f (invFunOn f s '' t) t := by
  refine ⟨?_, h.rightInvOn_invFunOn⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [h.rightInvOn_invFunOn hy]
#align set.surj_on.inv_on_inv_fun_on Set.SurjOn.invOn_invFunOn

theorem SurjOn.mapsTo_invFunOn [Nonempty α] (h : SurjOn f s t) : MapsTo (invFunOn f s) t s :=
  fun _y hy => mem_preimage.2 <| invFunOn_mem <| h hy
#align set.surj_on.maps_to_inv_fun_on Set.SurjOn.mapsTo_invFunOn

/-- This lemma is a special case of `rightInvOn_invFunOn.image_image'`; it may make more sense
to use the other lemma directly in an application. -/
theorem SurjOn.image_invFunOn_image_of_subset [Nonempty α] {r : Set β} (hf : SurjOn f s t)
    (hrt : r ⊆ t) : f '' (f.invFunOn s '' r) = r :=
  hf.rightInvOn_invFunOn.image_image' hrt

/-- This lemma is a special case of `rightInvOn_invFunOn.image_image`; it may make more sense
to use the other lemma directly in an application. -/
theorem SurjOn.image_invFunOn_image [Nonempty α] (hf : SurjOn f s t) :
    f '' (f.invFunOn s '' t) = t :=
  hf.rightInvOn_invFunOn.image_image

theorem SurjOn.bijOn_subset [Nonempty α] (h : SurjOn f s t) : BijOn f (invFunOn f s '' t) t := by
  refine h.invOn_invFunOn.bijOn ?_ (mapsTo_image _ _)
  rintro _ ⟨y, hy, rfl⟩
  rwa [h.rightInvOn_invFunOn hy]
#align set.surj_on.bij_on_subset Set.SurjOn.bijOn_subset

theorem surjOn_iff_exists_bijOn_subset : SurjOn f s t ↔ ∃ s' ⊆ s, BijOn f s' t := by
  constructor
  · rcases eq_empty_or_nonempty t with (rfl | ht)
    · exact fun _ => ⟨∅, empty_subset _, bijOn_empty f⟩
    · intro h
      haveI : Nonempty α := ⟨Classical.choose (h.comap_nonempty ht)⟩
      exact ⟨_, h.mapsTo_invFunOn.image_subset, h.bijOn_subset⟩
  · rintro ⟨s', hs', hfs'⟩
    exact hfs'.surjOn.mono hs' (Subset.refl _)
#align set.surj_on_iff_exists_bij_on_subset Set.surjOn_iff_exists_bijOn_subset

alias ⟨SurjOn.exists_bijOn_subset, _⟩ := Set.surjOn_iff_exists_bijOn_subset

variable (f s)

lemma exists_subset_bijOn : ∃ s' ⊆ s, BijOn f s' (f '' s) :=
  surjOn_iff_exists_bijOn_subset.mp (surjOn_image f s)

lemma exists_image_eq_and_injOn : ∃ u, f '' u =  f '' s ∧ InjOn f u :=
  let ⟨u, _, hfu⟩ := exists_subset_bijOn s f
  ⟨u, hfu.image_eq, hfu.injOn⟩

variable {f s}

lemma exists_image_eq_injOn_of_subset_range (ht : t ⊆ range f) :
    ∃ s, f '' s = t ∧ InjOn f s :=
  image_preimage_eq_of_subset ht ▸ exists_image_eq_and_injOn _ _

theorem preimage_invFun_of_mem [n : Nonempty α] {f : α → β} (hf : Injective f) {s : Set α}
    (h : Classical.choice n ∈ s) : invFun f ⁻¹' s = f '' s ∪ (range f)ᶜ := by
  ext x
  rcases em (x ∈ range f) with (⟨a, rfl⟩ | hx)
  · simp only [mem_preimage, mem_union, mem_compl_iff, mem_range_self, not_true, or_false,
      leftInverse_invFun hf _, hf.mem_set_image]
  · simp only [mem_preimage, invFun_neg hx, h, hx, mem_union, mem_compl_iff, not_false_iff, or_true]
#align set.preimage_inv_fun_of_mem Set.preimage_invFun_of_mem

theorem preimage_invFun_of_not_mem [n : Nonempty α] {f : α → β} (hf : Injective f) {s : Set α}
    (h : Classical.choice n ∉ s) : invFun f ⁻¹' s = f '' s := by
  ext x
  rcases em (x ∈ range f) with (⟨a, rfl⟩ | hx)
  · rw [mem_preimage, leftInverse_invFun hf, hf.mem_set_image]
  · have : x ∉ f '' s := fun h' => hx (image_subset_range _ _ h')
    simp only [mem_preimage, invFun_neg hx, h, this]
#align set.preimage_inv_fun_of_not_mem Set.preimage_invFun_of_not_mem

lemma BijOn.symm {g : β → α} (h : InvOn f g t s) (hf : BijOn f s t) : BijOn g t s :=
  ⟨h.2.mapsTo hf.surjOn, h.1.injOn, h.2.surjOn hf.mapsTo⟩
#align set.bij_on.symm Set.BijOn.symm

lemma bijOn_comm {g : β → α} (h : InvOn f g t s) : BijOn f s t ↔ BijOn g t s :=
  ⟨BijOn.symm h, BijOn.symm h.symm⟩
#align set.bij_on_comm Set.bijOn_comm

end Set

/-! ### Monotone -/
namespace Monotone

variable [Preorder α] [Preorder β] {f : α → β}

protected theorem restrict (h : Monotone f) (s : Set α) : Monotone (s.restrict f) := fun _ _ hxy =>
  h hxy
#align monotone.restrict Monotone.restrict

protected theorem codRestrict (h : Monotone f) {s : Set β} (hs : ∀ x, f x ∈ s) :
    Monotone (s.codRestrict f hs) :=
  h
#align monotone.cod_restrict Monotone.codRestrict

protected theorem rangeFactorization (h : Monotone f) : Monotone (Set.rangeFactorization f) :=
  h
#align monotone.range_factorization Monotone.rangeFactorization

end Monotone

/-! ### Piecewise defined function -/
namespace Set

variable {δ : α → Sort*} (s : Set α) (f g : ∀ i, δ i)

@[simp]
theorem piecewise_empty [∀ i : α, Decidable (i ∈ (∅ : Set α))] : piecewise ∅ f g = g := by
  ext i
  simp [piecewise]
#align set.piecewise_empty Set.piecewise_empty

@[simp]
theorem piecewise_univ [∀ i : α, Decidable (i ∈ (Set.univ : Set α))] :
    piecewise Set.univ f g = f := by
  ext i
  simp [piecewise]
#align set.piecewise_univ Set.piecewise_univ

--@[simp] -- Porting note: simpNF linter complains
theorem piecewise_insert_self {j : α} [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g j = f j := by simp [piecewise]
#align set.piecewise_insert_self Set.piecewise_insert_self

variable [∀ j, Decidable (j ∈ s)]

-- TODO: move!
instance Compl.decidableMem (j : α) : Decidable (j ∈ sᶜ) :=
  instDecidableNot
#align set.compl.decidable_mem Set.Compl.decidableMem

theorem piecewise_insert [DecidableEq α] (j : α) [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g = Function.update (s.piecewise f g) j (f j) := by
  simp (config := { unfoldPartialApp := true }) only [piecewise, mem_insert_iff]
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

theorem piecewise_eqOn (f g : α → β) : EqOn (s.piecewise f g) f s := fun _ =>
  piecewise_eq_of_mem _ _ _
#align set.piecewise_eq_on Set.piecewise_eqOn

theorem piecewise_eqOn_compl (f g : α → β) : EqOn (s.piecewise f g) g sᶜ := fun _ =>
  piecewise_eq_of_not_mem _ _ _
#align set.piecewise_eq_on_compl Set.piecewise_eqOn_compl

theorem piecewise_le {δ : α → Type*} [∀ i, Preorder (δ i)] {s : Set α} [∀ j, Decidable (j ∈ s)]
    {f₁ f₂ g : ∀ i, δ i} (h₁ : ∀ i ∈ s, f₁ i ≤ g i) (h₂ : ∀ i ∉ s, f₂ i ≤ g i) :
    s.piecewise f₁ f₂ ≤ g := fun i => if h : i ∈ s then by simp [*] else by simp [*]
#align set.piecewise_le Set.piecewise_le

theorem le_piecewise {δ : α → Type*} [∀ i, Preorder (δ i)] {s : Set α} [∀ j, Decidable (j ∈ s)]
    {f₁ f₂ g : ∀ i, δ i} (h₁ : ∀ i ∈ s, g i ≤ f₁ i) (h₂ : ∀ i ∉ s, g i ≤ f₂ i) :
    g ≤ s.piecewise f₁ f₂ :=
  @piecewise_le α (fun i => (δ i)ᵒᵈ) _ s _ _ _ _ h₁ h₂
#align set.le_piecewise Set.le_piecewise

theorem piecewise_le_piecewise {δ : α → Type*} [∀ i, Preorder (δ i)] {s : Set α}
    [∀ j, Decidable (j ∈ s)] {f₁ f₂ g₁ g₂ : ∀ i, δ i} (h₁ : ∀ i ∈ s, f₁ i ≤ g₁ i)
    (h₂ : ∀ i ∉ s, f₂ i ≤ g₂ i) : s.piecewise f₁ f₂ ≤ s.piecewise g₁ g₂ := by
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
theorem piecewise_range_comp {ι : Sort*} (f : ι → α) [∀ j, Decidable (j ∈ range f)]
    (g₁ g₂ : α → β) : (range f).piecewise g₁ g₂ ∘ f = g₁ ∘ f :=
  (piecewise_eqOn ..).comp_eq
#align set.piecewise_range_comp Set.piecewise_range_comp

theorem MapsTo.piecewise_ite {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {f₁ f₂ : α → β}
    [∀ i, Decidable (i ∈ s)] (h₁ : MapsTo f₁ (s₁ ∩ s) (t₁ ∩ t))
    (h₂ : MapsTo f₂ (s₂ ∩ sᶜ) (t₂ ∩ tᶜ)) :
    MapsTo (s.piecewise f₁ f₂) (s.ite s₁ s₂) (t.ite t₁ t₂) := by
  refine (h₁.congr ?_).union_union (h₂.congr ?_)
  exacts [(piecewise_eqOn s f₁ f₂).symm.mono inter_subset_right,
    (piecewise_eqOn_compl s f₁ f₂).symm.mono inter_subset_right]
#align set.maps_to.piecewise_ite Set.MapsTo.piecewise_ite

theorem eqOn_piecewise {f f' g : α → β} {t} :
    EqOn (s.piecewise f f') g t ↔ EqOn f g (t ∩ s) ∧ EqOn f' g (t ∩ sᶜ) := by
  simp only [EqOn, ← forall_and]
  refine forall_congr' fun a => ?_; by_cases a ∈ s <;> simp [*]
#align set.eq_on_piecewise Set.eqOn_piecewise

theorem EqOn.piecewise_ite' {f f' g : α → β} {t t'} (h : EqOn f g (t ∩ s))
    (h' : EqOn f' g (t' ∩ sᶜ)) : EqOn (s.piecewise f f') g (s.ite t t') := by
  simp [eqOn_piecewise, *]
#align set.eq_on.piecewise_ite' Set.EqOn.piecewise_ite'

theorem EqOn.piecewise_ite {f f' g : α → β} {t t'} (h : EqOn f g t) (h' : EqOn f' g t') :
    EqOn (s.piecewise f f') g (s.ite t t') :=
  (h.mono inter_subset_left).piecewise_ite' s (h'.mono inter_subset_left)
#align set.eq_on.piecewise_ite Set.EqOn.piecewise_ite

theorem piecewise_preimage (f g : α → β) (t) : s.piecewise f g ⁻¹' t = s.ite (f ⁻¹' t) (g ⁻¹' t) :=
  ext fun x => by by_cases x ∈ s <;> simp [*, Set.ite]
#align set.piecewise_preimage Set.piecewise_preimage

theorem apply_piecewise {δ' : α → Sort*} (h : ∀ i, δ i → δ' i) {x : α} :
    h x (s.piecewise f g x) = s.piecewise (fun x => h x (f x)) (fun x => h x (g x)) x := by
  by_cases hx : x ∈ s <;> simp [hx]
#align set.apply_piecewise Set.apply_piecewise

theorem apply_piecewise₂ {δ' δ'' : α → Sort*} (f' g' : ∀ i, δ' i) (h : ∀ i, δ i → δ' i → δ'' i)
    {x : α} :
    h x (s.piecewise f g x) (s.piecewise f' g' x) =
      s.piecewise (fun x => h x (f x) (f' x)) (fun x => h x (g x) (g' x)) x := by
  by_cases hx : x ∈ s <;> simp [hx]
#align set.apply_piecewise₂ Set.apply_piecewise₂

theorem piecewise_op {δ' : α → Sort*} (h : ∀ i, δ i → δ' i) :
    (s.piecewise (fun x => h x (f x)) fun x => h x (g x)) = fun x => h x (s.piecewise f g x) :=
  funext fun _ => (apply_piecewise _ _ _ _).symm
#align set.piecewise_op Set.piecewise_op

theorem piecewise_op₂ {δ' δ'' : α → Sort*} (f' g' : ∀ i, δ' i) (h : ∀ i, δ i → δ' i → δ'' i) :
    (s.piecewise (fun x => h x (f x) (f' x)) fun x => h x (g x) (g' x)) = fun x =>
      h x (s.piecewise f g x) (s.piecewise f' g' x) :=
  funext fun _ => (apply_piecewise₂ _ _ _ _ _ _).symm
#align set.piecewise_op₂ Set.piecewise_op₂

@[simp]
theorem piecewise_same : s.piecewise f f = f := by
  ext x
  by_cases hx : x ∈ s <;> simp [hx]
#align set.piecewise_same Set.piecewise_same

theorem range_piecewise (f g : α → β) : range (s.piecewise f g) = f '' s ∪ g '' sᶜ := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    by_cases h : x ∈ s <;> [left; right] <;> use x <;> simp [h]
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;> use x <;> simp_all
#align set.range_piecewise Set.range_piecewise

theorem injective_piecewise_iff {f g : α → β} :
    Injective (s.piecewise f g) ↔
      InjOn f s ∧ InjOn g sᶜ ∧ ∀ x ∈ s, ∀ y ∉ s, f x ≠ g y := by
  rw [injective_iff_injOn_univ, ← union_compl_self s, injOn_union (@disjoint_compl_right _ _ s),
    (piecewise_eqOn s f g).injOn_iff, (piecewise_eqOn_compl s f g).injOn_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl <| forall₄_congr fun x hx y hy => ?_)
  rw [piecewise_eq_of_mem s f g hx, piecewise_eq_of_not_mem s f g hy]
#align set.injective_piecewise_iff Set.injective_piecewise_iff

theorem piecewise_mem_pi {δ : α → Type*} {t : Set α} {t' : ∀ i, Set (δ i)} {f g} (hf : f ∈ pi t t')
    (hg : g ∈ pi t t') : s.piecewise f g ∈ pi t t' := by
  intro i ht
  by_cases hs : i ∈ s <;> simp [hf i ht, hg i ht, hs]
#align set.piecewise_mem_pi Set.piecewise_mem_pi

@[simp]
theorem pi_piecewise {ι : Type*} {α : ι → Type*} (s s' : Set ι) (t t' : ∀ i, Set (α i))
    [∀ x, Decidable (x ∈ s')] : pi s (s'.piecewise t t') = pi (s ∩ s') t ∩ pi (s \ s') t' :=
  pi_if _ _ _
#align set.pi_piecewise Set.pi_piecewise

-- Porting note (#10756): new lemma
theorem univ_pi_piecewise {ι : Type*} {α : ι → Type*} (s : Set ι) (t t' : ∀ i, Set (α i))
    [∀ x, Decidable (x ∈ s)] : pi univ (s.piecewise t t') = pi s t ∩ pi sᶜ t' := by
  simp [compl_eq_univ_diff]

theorem univ_pi_piecewise_univ {ι : Type*} {α : ι → Type*} (s : Set ι) (t : ∀ i, Set (α i))
    [∀ x, Decidable (x ∈ s)] : pi univ (s.piecewise t fun _ => univ) = pi s t := by simp
#align set.univ_pi_piecewise Set.univ_pi_piecewise_univ

end Set

section strictMono

theorem StrictMonoOn.injOn [LinearOrder α] [Preorder β] {f : α → β} {s : Set α}
    (H : StrictMonoOn f s) : s.InjOn f := fun x hx y hy hxy =>
  show Ordering.eq.Compares x y from (H.compares hx hy).1 hxy
#align strict_mono_on.inj_on StrictMonoOn.injOn

theorem StrictAntiOn.injOn [LinearOrder α] [Preorder β] {f : α → β} {s : Set α}
    (H : StrictAntiOn f s) : s.InjOn f :=
  @StrictMonoOn.injOn α βᵒᵈ _ _ f s H
#align strict_anti_on.inj_on StrictAntiOn.injOn

theorem StrictMonoOn.comp [Preorder α] [Preorder β] [Preorder γ] {g : β → γ} {f : α → β} {s : Set α}
    {t : Set β} (hg : StrictMonoOn g t) (hf : StrictMonoOn f s) (hs : Set.MapsTo f s t) :
    StrictMonoOn (g ∘ f) s := fun _x hx _y hy hxy => hg (hs hx) (hs hy) <| hf hx hy hxy
#align strict_mono_on.comp StrictMonoOn.comp

theorem StrictMonoOn.comp_strictAntiOn [Preorder α] [Preorder β] [Preorder γ] {g : β → γ}
    {f : α → β} {s : Set α} {t : Set β} (hg : StrictMonoOn g t) (hf : StrictAntiOn f s)
    (hs : Set.MapsTo f s t) : StrictAntiOn (g ∘ f) s := fun _x hx _y hy hxy =>
  hg (hs hy) (hs hx) <| hf hx hy hxy
#align strict_mono_on.comp_strict_anti_on StrictMonoOn.comp_strictAntiOn

theorem StrictAntiOn.comp [Preorder α] [Preorder β] [Preorder γ] {g : β → γ} {f : α → β} {s : Set α}
    {t : Set β} (hg : StrictAntiOn g t) (hf : StrictAntiOn f s) (hs : Set.MapsTo f s t) :
    StrictMonoOn (g ∘ f) s := fun _x hx _y hy hxy => hg (hs hy) (hs hx) <| hf hx hy hxy
#align strict_anti_on.comp StrictAntiOn.comp

theorem StrictAntiOn.comp_strictMonoOn [Preorder α] [Preorder β] [Preorder γ] {g : β → γ}
    {f : α → β} {s : Set α} {t : Set β} (hg : StrictAntiOn g t) (hf : StrictMonoOn f s)
    (hs : Set.MapsTo f s t) : StrictAntiOn (g ∘ f) s := fun _x hx _y hy hxy =>
  hg (hs hx) (hs hy) <| hf hx hy hxy
#align strict_anti_on.comp_strict_mono_on StrictAntiOn.comp_strictMonoOn

@[simp]
theorem strictMono_restrict [Preorder α] [Preorder β] {f : α → β} {s : Set α} :
    StrictMono (s.restrict f) ↔ StrictMonoOn f s := by simp [Set.restrict, StrictMono, StrictMonoOn]
#align strict_mono_restrict strictMono_restrict

alias ⟨_root_.StrictMono.of_restrict, _root_.StrictMonoOn.restrict⟩ := strictMono_restrict
#align strict_mono.of_restrict StrictMono.of_restrict
#align strict_mono_on.restrict StrictMonoOn.restrict

theorem StrictMono.codRestrict [Preorder α] [Preorder β] {f : α → β} (hf : StrictMono f)
    {s : Set β} (hs : ∀ x, f x ∈ s) : StrictMono (Set.codRestrict f s hs) :=
  hf
#align strict_mono.cod_restrict StrictMono.codRestrict

end strictMono

namespace Function

open Set

variable {fa : α → α} {fb : β → β} {f : α → β} {g : β → γ} {s t : Set α}

theorem Injective.comp_injOn (hg : Injective g) (hf : s.InjOn f) : s.InjOn (g ∘ f) :=
  hg.injOn.comp hf (mapsTo_univ _ _)
#align function.injective.comp_inj_on Function.Injective.comp_injOn

theorem Surjective.surjOn (hf : Surjective f) (s : Set β) : SurjOn f univ s :=
  (surjective_iff_surjOn_univ.1 hf).mono (Subset.refl _) (subset_univ _)
#align function.surjective.surj_on Function.Surjective.surjOn

theorem LeftInverse.leftInvOn {g : β → α} (h : LeftInverse f g) (s : Set β) : LeftInvOn f g s :=
  fun x _ => h x
#align function.left_inverse.left_inv_on Function.LeftInverse.leftInvOn

theorem RightInverse.rightInvOn {g : β → α} (h : RightInverse f g) (s : Set α) :
    RightInvOn f g s := fun x _ => h x
#align function.right_inverse.right_inv_on Function.RightInverse.rightInvOn

theorem LeftInverse.rightInvOn_range {g : β → α} (h : LeftInverse f g) :
    RightInvOn f g (range g) :=
  forall_mem_range.2 fun i => congr_arg g (h i)
#align function.left_inverse.right_inv_on_range Function.LeftInverse.rightInvOn_range

namespace Semiconj

theorem mapsTo_image (h : Semiconj f fa fb) (ha : MapsTo fa s t) : MapsTo fb (f '' s) (f '' t) :=
  fun _y ⟨x, hx, hy⟩ => hy ▸ ⟨fa x, ha hx, h x⟩
#align function.semiconj.maps_to_image Function.Semiconj.mapsTo_image

theorem mapsTo_range (h : Semiconj f fa fb) : MapsTo fb (range f) (range f) := fun _y ⟨x, hy⟩ =>
  hy ▸ ⟨fa x, h x⟩
#align function.semiconj.maps_to_range Function.Semiconj.mapsTo_range

theorem surjOn_image (h : Semiconj f fa fb) (ha : SurjOn fa s t) : SurjOn fb (f '' s) (f '' t) := by
  rintro y ⟨x, hxt, rfl⟩
  rcases ha hxt with ⟨x, hxs, rfl⟩
  rw [h x]
  exact mem_image_of_mem _ (mem_image_of_mem _ hxs)
#align function.semiconj.surj_on_image Function.Semiconj.surjOn_image

theorem surjOn_range (h : Semiconj f fa fb) (ha : Surjective fa) :
    SurjOn fb (range f) (range f) := by
  rw [← image_univ]
  exact h.surjOn_image (ha.surjOn univ)
#align function.semiconj.surj_on_range Function.Semiconj.surjOn_range

theorem injOn_image (h : Semiconj f fa fb) (ha : InjOn fa s) (hf : InjOn f (fa '' s)) :
    InjOn fb (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ H
  simp only [← h.eq] at H
  exact congr_arg f (ha hx hy <| hf (mem_image_of_mem fa hx) (mem_image_of_mem fa hy) H)
#align function.semiconj.inj_on_image Function.Semiconj.injOn_image

theorem injOn_range (h : Semiconj f fa fb) (ha : Injective fa) (hf : InjOn f (range fa)) :
    InjOn fb (range f) := by
  rw [← image_univ] at *
  exact h.injOn_image ha.injOn hf
#align function.semiconj.inj_on_range Function.Semiconj.injOn_range

theorem bijOn_image (h : Semiconj f fa fb) (ha : BijOn fa s t) (hf : InjOn f t) :
    BijOn fb (f '' s) (f '' t) :=
  ⟨h.mapsTo_image ha.mapsTo, h.injOn_image ha.injOn (ha.image_eq.symm ▸ hf),
    h.surjOn_image ha.surjOn⟩
#align function.semiconj.bij_on_image Function.Semiconj.bijOn_image

theorem bijOn_range (h : Semiconj f fa fb) (ha : Bijective fa) (hf : Injective f) :
    BijOn fb (range f) (range f) := by
  rw [← image_univ]
  exact h.bijOn_image (bijective_iff_bijOn_univ.1 ha) hf.injOn
#align function.semiconj.bij_on_range Function.Semiconj.bijOn_range

theorem mapsTo_preimage (h : Semiconj f fa fb) {s t : Set β} (hb : MapsTo fb s t) :
    MapsTo fa (f ⁻¹' s) (f ⁻¹' t) := fun x hx => by simp only [mem_preimage, h x, hb hx]
#align function.semiconj.maps_to_preimage Function.Semiconj.mapsTo_preimage

theorem injOn_preimage (h : Semiconj f fa fb) {s : Set β} (hb : InjOn fb s)
    (hf : InjOn f (f ⁻¹' s)) : InjOn fa (f ⁻¹' s) := by
  intro x hx y hy H
  have := congr_arg f H
  rw [h.eq, h.eq] at this
  exact hf hx hy (hb hx hy this)
#align function.semiconj.inj_on_preimage Function.Semiconj.injOn_preimage

end Semiconj

theorem update_comp_eq_of_not_mem_range' {α : Sort*} {β : Type*} {γ : β → Sort*} [DecidableEq β]
    (g : ∀ b, γ b) {f : α → β} {i : β} (a : γ i) (h : i ∉ Set.range f) :
    (fun j => update g i a (f j)) = fun j => g (f j) :=
  (update_comp_eq_of_forall_ne' _ _) fun x hx => h ⟨x, hx⟩
#align function.update_comp_eq_of_not_mem_range' Function.update_comp_eq_of_not_mem_range'

/-- Non-dependent version of `Function.update_comp_eq_of_not_mem_range'` -/
theorem update_comp_eq_of_not_mem_range {α : Sort*} {β : Type*} {γ : Sort*} [DecidableEq β]
    (g : β → γ) {f : α → β} {i : β} (a : γ) (h : i ∉ Set.range f) : update g i a ∘ f = g ∘ f :=
  update_comp_eq_of_not_mem_range' g a h
#align function.update_comp_eq_of_not_mem_range Function.update_comp_eq_of_not_mem_range

theorem insert_injOn (s : Set α) : sᶜ.InjOn fun a => insert a s := fun _a ha _ _ =>
  (insert_inj ha).1
#align function.insert_inj_on Function.insert_injOn

theorem monotoneOn_of_rightInvOn_of_mapsTo {α β : Type*} [PartialOrder α] [LinearOrder β]
    {φ : β → α} {ψ : α → β} {t : Set β} {s : Set α} (hφ : MonotoneOn φ t)
    (φψs : Set.RightInvOn ψ φ s) (ψts : Set.MapsTo ψ s t) : MonotoneOn ψ s := by
  rintro x xs y ys l
  rcases le_total (ψ x) (ψ y) with (ψxy|ψyx)
  · exact ψxy
  · have := hφ (ψts ys) (ψts xs) ψyx
    rw [φψs.eq ys, φψs.eq xs] at this
    induction le_antisymm l this
    exact le_refl _
#align function.monotone_on_of_right_inv_on_of_maps_to Function.monotoneOn_of_rightInvOn_of_mapsTo

theorem antitoneOn_of_rightInvOn_of_mapsTo [PartialOrder α] [LinearOrder β]
    {φ : β → α} {ψ : α → β} {t : Set β} {s : Set α} (hφ : AntitoneOn φ t)
    (φψs : Set.RightInvOn ψ φ s) (ψts : Set.MapsTo ψ s t) : AntitoneOn ψ s :=
  (monotoneOn_of_rightInvOn_of_mapsTo hφ.dual_left φψs ψts).dual_right
#align function.antitone_on_of_right_inv_on_of_maps_to Function.antitoneOn_of_rightInvOn_of_mapsTo

end Function

/-! ### Equivalences, permutations -/
namespace Set

variable {p : β → Prop} [DecidablePred p] {f : α ≃ Subtype p} {g g₁ g₂ : Perm α} {s t : Set α}

protected lemma MapsTo.extendDomain (h : MapsTo g s t) :
    MapsTo (g.extendDomain f) ((↑) ∘ f '' s) ((↑) ∘ f '' t) := by
  rintro _ ⟨a, ha, rfl⟩; exact ⟨_, h ha, by simp_rw [Function.comp_apply, extendDomain_apply_image]⟩
#align set.maps_to.extend_domain Set.MapsTo.extendDomain

protected lemma SurjOn.extendDomain (h : SurjOn g s t) :
    SurjOn (g.extendDomain f) ((↑) ∘ f '' s) ((↑) ∘ f '' t) := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨b, hb, rfl⟩ := h ha
  exact ⟨_, ⟨_, hb, rfl⟩, by simp_rw [Function.comp_apply, extendDomain_apply_image]⟩
#align set.surj_on.extend_domain Set.SurjOn.extendDomain

protected lemma BijOn.extendDomain (h : BijOn g s t) :
    BijOn (g.extendDomain f) ((↑) ∘ f '' s) ((↑) ∘ f '' t) :=
  ⟨h.mapsTo.extendDomain, (g.extendDomain f).injective.injOn, h.surjOn.extendDomain⟩
#align set.bij_on.extend_domain Set.BijOn.extendDomain

protected lemma LeftInvOn.extendDomain (h : LeftInvOn g₁ g₂ s) :
    LeftInvOn (g₁.extendDomain f) (g₂.extendDomain f) ((↑) ∘ f '' s) := by
  rintro _ ⟨a, ha, rfl⟩; simp_rw [Function.comp_apply, extendDomain_apply_image, h ha]
#align set.left_inv_on.extend_domain Set.LeftInvOn.extendDomain

protected lemma RightInvOn.extendDomain (h : RightInvOn g₁ g₂ t) :
    RightInvOn (g₁.extendDomain f) (g₂.extendDomain f) ((↑) ∘ f '' t) := by
  rintro _ ⟨a, ha, rfl⟩; simp_rw [Function.comp_apply, extendDomain_apply_image, h ha]
#align set.right_inv_on.extend_domain Set.RightInvOn.extendDomain

protected lemma InvOn.extendDomain (h : InvOn g₁ g₂ s t) :
    InvOn (g₁.extendDomain f) (g₂.extendDomain f) ((↑) ∘ f '' s) ((↑) ∘ f '' t) :=
  ⟨h.1.extendDomain, h.2.extendDomain⟩
#align set.inv_on.extend_domain Set.InvOn.extendDomain

end Set

namespace Set
variable {α₁ α₂ β₁ β₂ : Type*} {s₁ : Set α₁} {s₂ : Set α₂} {t₁ : Set β₁} {t₂ : Set β₂}
  {f₁ : α₁ → β₁} {f₂ : α₂ → β₂} {g₁ : β₁ → α₁} {g₂ : β₂ → α₂}

lemma InjOn.prodMap (h₁ : s₁.InjOn f₁) (h₂ : s₂.InjOn f₂) :
    (s₁ ×ˢ s₂).InjOn fun x ↦ (f₁ x.1, f₂ x.2) :=
  fun x hx y hy ↦ by simp_rw [Prod.ext_iff]; exact And.imp (h₁ hx.1 hy.1) (h₂ hx.2 hy.2)

lemma SurjOn.prodMap (h₁ : SurjOn f₁ s₁ t₁) (h₂ : SurjOn f₂ s₂ t₂) :
    SurjOn (fun x ↦ (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) := by
  rintro x hx
  obtain ⟨a₁, ha₁, hx₁⟩ := h₁ hx.1
  obtain ⟨a₂, ha₂, hx₂⟩ := h₂ hx.2
  exact ⟨(a₁, a₂), ⟨ha₁, ha₂⟩, Prod.ext hx₁ hx₂⟩

lemma MapsTo.prodMap (h₁ : MapsTo f₁ s₁ t₁) (h₂ : MapsTo f₂ s₂ t₂) :
    MapsTo (fun x ↦ (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) :=
  fun _x hx ↦ ⟨h₁ hx.1, h₂ hx.2⟩

lemma BijOn.prodMap (h₁ : BijOn f₁ s₁ t₁) (h₂ : BijOn f₂ s₂ t₂) :
    BijOn (fun x ↦ (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) :=
  ⟨h₁.mapsTo.prodMap h₂.mapsTo, h₁.injOn.prodMap h₂.injOn, h₁.surjOn.prodMap h₂.surjOn⟩

lemma LeftInvOn.prodMap (h₁ : LeftInvOn g₁ f₁ s₁) (h₂ : LeftInvOn g₂ f₂ s₂) :
    LeftInvOn (fun x ↦ (g₁ x.1, g₂ x.2)) (fun x ↦ (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) :=
  fun _x hx ↦ Prod.ext (h₁ hx.1) (h₂ hx.2)

lemma RightInvOn.prodMap (h₁ : RightInvOn g₁ f₁ t₁) (h₂ : RightInvOn g₂ f₂ t₂) :
    RightInvOn (fun x ↦ (g₁ x.1, g₂ x.2)) (fun x ↦ (f₁ x.1, f₂ x.2)) (t₁ ×ˢ t₂) :=
  fun _x hx ↦ Prod.ext (h₁ hx.1) (h₂ hx.2)

lemma InvOn.prodMap (h₁ : InvOn g₁ f₁ s₁ t₁) (h₂ : InvOn g₂ f₂ s₂ t₂) :
    InvOn (fun x ↦ (g₁ x.1, g₂ x.2)) (fun x ↦ (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) :=
  ⟨h₁.1.prodMap h₂.1, h₁.2.prodMap h₂.2⟩

end Set

namespace Equiv
open Set

variable (e : α ≃ β) {s : Set α} {t : Set β}

lemma bijOn' (h₁ : MapsTo e s t) (h₂ : MapsTo e.symm t s) : BijOn e s t :=
  ⟨h₁, e.injective.injOn, fun b hb ↦ ⟨e.symm b, h₂ hb, apply_symm_apply _ _⟩⟩
#align equiv.bij_on' Equiv.bijOn'

protected lemma bijOn (h : ∀ a, e a ∈ t ↔ a ∈ s) : BijOn e s t :=
  e.bijOn' (fun a ↦ (h _).2) fun b hb ↦ (h _).1 <| by rwa [apply_symm_apply]
#align equiv.bij_on Equiv.bijOn

lemma invOn : InvOn e e.symm t s :=
  ⟨e.rightInverse_symm.leftInvOn _, e.leftInverse_symm.leftInvOn _⟩
#align equiv.inv_on Equiv.invOn

lemma bijOn_image : BijOn e s (e '' s) := e.injective.injOn.bijOn_image
#align equiv.bij_on_image Equiv.bijOn_image
lemma bijOn_symm_image : BijOn e.symm (e '' s) s := e.bijOn_image.symm e.invOn
#align equiv.bij_on_symm_image Equiv.bijOn_symm_image

variable {e}

@[simp] lemma bijOn_symm : BijOn e.symm t s ↔ BijOn e s t := bijOn_comm e.symm.invOn
#align equiv.bij_on_symm Equiv.bijOn_symm

alias ⟨_root_.Set.BijOn.of_equiv_symm, _root_.Set.BijOn.equiv_symm⟩ := bijOn_symm
#align set.bij_on.of_equiv_symm Set.BijOn.of_equiv_symm
#align set.bij_on.equiv_symm Set.BijOn.equiv_symm

variable [DecidableEq α] {a b : α}

lemma bijOn_swap (ha : a ∈ s) (hb : b ∈ s) : BijOn (swap a b) s s :=
  (swap a b).bijOn fun x ↦ by
    obtain rfl | hxa := eq_or_ne x a <;>
    obtain rfl | hxb := eq_or_ne x b <;>
    simp [*, swap_apply_of_ne_of_ne]
#align equiv.bij_on_swap Equiv.bijOn_swap

end Equiv
