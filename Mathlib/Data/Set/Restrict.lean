/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Andrew Zipperer, Haitao Zhang, Minchao Wu, Yury Kudryashov
-/
import Mathlib.Data.Set.Image

/-!
# Restrict the domain of a function to a set

## Main definitions

* `Set.restrict f s` : restrict the domain of `f` to the set `s`;
* `Set.codRestrict f s h` : given `h : ∀ x, f x ∈ s`, restrict the codomain of `f` to the set `s`;
-/

variable {α β γ δ : Type*} {ι : Sort*} {π : α → Type*}

open Equiv Equiv.Perm Function

namespace Set

/-! ### Restrict -/
section restrict

/-- Restrict domain of a function `f` to a set `s`. Same as `Subtype.restrict` but this version
takes an argument `↥s` instead of `Subtype s`. -/
def restrict (s : Set α) (f : ∀ a : α, π a) : ∀ a : s, π a := fun x => f x

theorem restrict_def (s : Set α) : s.restrict (π := π) = fun f x ↦ f x := rfl

theorem restrict_eq (f : α → β) (s : Set α) : s.restrict f = f ∘ Subtype.val :=
  rfl

@[simp] lemma restrict_id (s : Set α) : restrict s id = Subtype.val := rfl

@[simp, grind =]
theorem restrict_apply (f : (a : α) → π a) (s : Set α) (x : s) : s.restrict f x = f x :=
  rfl

theorem restrict_eq_iff {f : ∀ a, π a} {s : Set α} {g : ∀ a : s, π a} :
    restrict s f = g ↔ ∀ (a) (ha : a ∈ s), f a = g ⟨a, ha⟩ :=
  funext_iff.trans Subtype.forall

theorem eq_restrict_iff {s : Set α} {f : ∀ a : s, π a} {g : ∀ a, π a} :
    f = restrict s g ↔ ∀ (a) (ha : a ∈ s), f ⟨a, ha⟩ = g a :=
  funext_iff.trans Subtype.forall

@[simp]
theorem range_restrict (f : α → β) (s : Set α) : Set.range (s.restrict f) = f '' s :=
  (range_comp _ _).trans <| congr_arg (f '' ·) Subtype.range_coe

theorem image_restrict (f : α → β) (s t : Set α) :
    s.restrict f '' (Subtype.val ⁻¹' t) = f '' (t ∩ s) := by
  rw [restrict_eq, image_comp, image_preimage_eq_inter_range, Subtype.range_coe]

@[simp]
theorem restrict_dite {s : Set α} [∀ x, Decidable (x ∈ s)] (f : ∀ a ∈ s, β)
    (g : ∀ a ∉ s, β) :
    (s.restrict fun a => if h : a ∈ s then f a h else g a h) = (fun a : s => f a a.2) :=
  funext fun a => dif_pos a.2

@[simp]
theorem restrict_dite_compl {s : Set α} [∀ x, Decidable (x ∈ s)] (f : ∀ a ∈ s, β)
    (g : ∀ a ∉ s, β) :
    (sᶜ.restrict fun a => if h : a ∈ s then f a h else g a h) = (fun a : (sᶜ : Set α) => g a a.2) :=
  funext fun a => dif_neg a.2

@[simp]
theorem restrict_ite (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    (s.restrict fun a => if a ∈ s then f a else g a) = s.restrict f :=
  restrict_dite _ _

@[simp]
theorem restrict_ite_compl (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    (sᶜ.restrict fun a => if a ∈ s then f a else g a) = sᶜ.restrict g :=
  restrict_dite_compl _ _

@[simp]
theorem restrict_piecewise (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    s.restrict (piecewise s f g) = s.restrict f :=
  restrict_ite _ _ _

@[simp]
theorem restrict_piecewise_compl (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    sᶜ.restrict (piecewise s f g) = sᶜ.restrict g :=
  restrict_ite_compl _ _ _

theorem restrict_extend_range (f : α → β) (g : α → γ) (g' : β → γ) :
    (range f).restrict (extend f g g') = fun x => g x.coe_prop.choose := by
  classical
  exact restrict_dite _ _

@[simp]
theorem restrict_extend_compl_range (f : α → β) (g : α → γ) (g' : β → γ) :
    (range f)ᶜ.restrict (extend f g g') = g' ∘ Subtype.val := by
  classical
  exact restrict_dite_compl _ _

/-- If a function `f` is restricted to a set `t`, and `s ⊆ t`, this is the restriction to `s`. -/
@[simp]
def restrict₂ {s t : Set α} (hst : s ⊆ t) (f : ∀ a : t, π a) : ∀ a : s, π a :=
  fun x => f ⟨x.1, hst x.2⟩

theorem restrict₂_def {s t : Set α} (hst : s ⊆ t) :
    restrict₂ (π := π) hst = fun f x ↦ f ⟨x.1, hst x.2⟩ := rfl

theorem restrict₂_comp_restrict {s t : Set α} (hst : s ⊆ t) :
    (restrict₂ (π := π) hst) ∘ t.restrict = s.restrict := rfl

theorem restrict₂_comp_restrict₂ {s t u : Set α} (hst : s ⊆ t) (htu : t ⊆ u) :
    (restrict₂ (π := π) hst) ∘ (restrict₂ htu) = restrict₂ (hst.trans htu) := rfl

theorem range_extend_subset (f : α → β) (g : α → γ) (g' : β → γ) :
    range (extend f g g') ⊆ range g ∪ g' '' (range f)ᶜ := by
  classical
  rintro _ ⟨y, rfl⟩
  rw [extend_def]
  split_ifs with h
  exacts [Or.inl (mem_range_self _), Or.inr (mem_image_of_mem _ h)]

theorem range_extend {f : α → β} (hf : Injective f) (g : α → γ) (g' : β → γ) :
    range (extend f g g') = range g ∪ g' '' (range f)ᶜ := by
  refine (range_extend_subset _ _ _).antisymm ?_
  rintro z (⟨x, rfl⟩ | ⟨y, hy, rfl⟩)
  exacts [⟨f x, hf.extend_apply _ _ _⟩, ⟨y, extend_apply' _ _ _ hy⟩]

/-- Restrict codomain of a function `f` to a set `s`. Same as `Subtype.coind` but this version
has codomain `↥s` instead of `Subtype s`. -/
def codRestrict (f : ι → α) (s : Set α) (h : ∀ x, f x ∈ s) : ι → s := fun x => ⟨f x, h x⟩

@[simp]
theorem val_codRestrict_apply (f : ι → α) (s : Set α) (h : ∀ x, f x ∈ s) (x : ι) :
    (codRestrict f s h x : α) = f x :=
  rfl

@[simp]
theorem restrict_comp_codRestrict {f : ι → α} {g : α → β} {b : Set α} (h : ∀ x, f x ∈ b) :
    b.restrict g ∘ b.codRestrict f h = g ∘ f :=
  rfl

@[simp]
theorem injective_codRestrict {f : ι → α} {s : Set α} (h : ∀ x, f x ∈ s) :
    Injective (codRestrict f s h) ↔ Injective f := by
  simp only [Injective, Subtype.ext_iff, val_codRestrict_apply]

alias ⟨_, _root_.Function.Injective.codRestrict⟩ := injective_codRestrict

theorem codRestrict_range_surjective (f : ι → α) :
    ((range f).codRestrict f mem_range_self).Surjective := by
  rintro ⟨b, ⟨a, rfl⟩⟩
  exact ⟨a, rfl⟩

variable {s : Set α} {f₁ f₂ : α → β}

@[simp]
theorem restrict_eq_restrict_iff : restrict s f₁ = restrict s f₂ ↔ EqOn f₁ f₂ s :=
  restrict_eq_iff

end restrict

variable {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {p : Set γ} {f f₁ f₂ : α → β} {g g₁ g₂ : β → γ}
  {f' f₁' f₂' : β → α} {g' : γ → β} {a : α} {b : β}

section MapsTo

theorem MapsTo.restrict_commutes (f : α → β) (s : Set α) (t : Set β) (h : MapsTo f s t) :
    Subtype.val ∘ h.restrict f s t = f ∘ Subtype.val :=
  rfl

@[simp]
theorem MapsTo.val_restrict_apply (h : MapsTo f s t) (x : s) : (h.restrict f s t x : β) = f x :=
  rfl

theorem MapsTo.coe_iterate_restrict {f : α → α} (h : MapsTo f s s) (x : s) (k : ℕ) :
    h.restrict^[k] x = f^[k] x := by
  induction k with
  | zero => simp
  | succ k ih => simp only [iterate_succ', comp_apply, val_restrict_apply, ih]

/-- Restricting the domain and then the codomain is the same as `MapsTo.restrict`. -/
@[simp]
theorem codRestrict_restrict (h : ∀ x : s, f x ∈ t) :
    codRestrict (s.restrict f) t h = MapsTo.restrict f s t fun x hx => h ⟨x, hx⟩ :=
  rfl

/-- Reverse of `Set.codRestrict_restrict`. -/
theorem MapsTo.restrict_eq_codRestrict (h : MapsTo f s t) :
    h.restrict f s t = codRestrict (s.restrict f) t fun x => h x.2 :=
  rfl

theorem MapsTo.coe_restrict (h : Set.MapsTo f s t) :
    Subtype.val ∘ h.restrict f s t = s.restrict f :=
  rfl

theorem MapsTo.range_restrict (f : α → β) (s : Set α) (t : Set β) (h : MapsTo f s t) :
    range (h.restrict f s t) = Subtype.val ⁻¹' (f '' s) :=
  Set.range_subtype_map f h

theorem mapsTo_iff_exists_map_subtype : MapsTo f s t ↔ ∃ g : s → t, ∀ x : s, f x = g x :=
  ⟨fun h => ⟨h.restrict f s t, fun _ => rfl⟩, fun ⟨g, hg⟩ x hx => by
    rw [hg ⟨x, hx⟩]
    apply Subtype.coe_prop⟩

theorem surjective_mapsTo_image_restrict (f : α → β) (s : Set α) :
    Surjective ((mapsTo_image f s).restrict f s (f '' s)) := fun ⟨_, x, hs, hxy⟩ =>
  ⟨⟨x, hs⟩, Subtype.ext hxy⟩

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

@[simp]
theorem restrictPreimage_mk (h : a ∈ f ⁻¹' t) : t.restrictPreimage f ⟨a, h⟩ = ⟨f a, h⟩ := rfl

theorem image_val_preimage_restrictPreimage {u : Set t} :
    Subtype.val '' (t.restrictPreimage f ⁻¹' u) = f ⁻¹' (Subtype.val '' u) := by
  ext
  simp

theorem preimage_restrictPreimage {u : Set t} :
    t.restrictPreimage f ⁻¹' u = (fun a : f ⁻¹' t ↦ f a) ⁻¹' (Subtype.val '' u) := by
  rw [← preimage_preimage (g := f) (f := Subtype.val), ← image_val_preimage_restrictPreimage,
    preimage_image_eq _ Subtype.val_injective]

lemma restrictPreimage_injective (hf : Injective f) : Injective (t.restrictPreimage f) :=
  fun _ _ e => Subtype.coe_injective <| hf <| Subtype.mk.inj e

lemma restrictPreimage_surjective (hf : Surjective f) : Surjective (t.restrictPreimage f) :=
  fun x => ⟨⟨_, ((hf x).choose_spec.symm ▸ x.2 : _ ∈ t)⟩, Subtype.ext (hf x).choose_spec⟩

lemma restrictPreimage_bijective (hf : Bijective f) : Bijective (t.restrictPreimage f) :=
  ⟨t.restrictPreimage_injective hf.1, t.restrictPreimage_surjective hf.2⟩

alias _root_.Function.Injective.restrictPreimage := Set.restrictPreimage_injective
alias _root_.Function.Surjective.restrictPreimage := Set.restrictPreimage_surjective
alias _root_.Function.Bijective.restrictPreimage := Set.restrictPreimage_bijective

end

/-! ### Injectivity on a set -/
section injOn

theorem injOn_iff_injective : InjOn f s ↔ Injective (s.restrict f) :=
  ⟨fun H a b h => Subtype.eq <| H a.2 b.2 h, fun H a as b bs h =>
    congr_arg Subtype.val <| @H ⟨a, as⟩ ⟨b, bs⟩ h⟩

alias ⟨InjOn.injective, _⟩ := Set.injOn_iff_injective

theorem MapsTo.restrict_inj (h : MapsTo f s t) : Injective (h.restrict f s t) ↔ InjOn f s := by
  rw [h.restrict_eq_codRestrict, injective_codRestrict, injOn_iff_injective]

end injOn

/-! ### Surjectivity on a set -/
section surjOn

theorem surjOn_iff_surjective : SurjOn f s univ ↔ Surjective (s.restrict f) :=
  ⟨fun H b =>
    let ⟨a, as, e⟩ := @H b trivial
    ⟨⟨a, as⟩, e⟩,
    fun H b _ =>
    let ⟨⟨a, as⟩, e⟩ := H b
    ⟨a, as, e⟩⟩

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

end surjOn

end Set
