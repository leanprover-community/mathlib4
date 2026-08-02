/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Andrew Zipperer, Haitao Zhang, Minchao Wu, Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Image

/-!
# Restrict the domain of a function to a set

## Main definitions

* `Set.domRestrict f s` : restrict the domain of `f` to the set `s`;
* `Set.codRestrict f s h` : given `h : ∀ x, f x ∈ s`, restrict the codomain of `f` to the set `s`;
-/

@[expose] public section

variable {α β γ δ : Type*} {ι : Sort*} {π : α → Type*}

open Equiv Equiv.Perm Function

namespace Set

/-! ### Domain restriction -/
section domRestrict

/-- Restrict domain of a function `f` to a set `s`. Same as `Subtype.restrict` but this version
takes an argument `↥s` instead of `Subtype s`. -/
def domRestrict (s : Set α) (f : ∀ a : α, π a) : ∀ a : s, π a := fun x => f x

theorem domRestrict_def (s : Set α) : s.domRestrict (π := π) = fun f x ↦ f x := rfl

theorem domRestrict_eq (f : α → β) (s : Set α) : s.domRestrict f = f ∘ Subtype.val :=
  rfl

@[simp] lemma domRestrict_id (s : Set α) : domRestrict s id = Subtype.val := rfl

@[simp, grind =]
theorem domRestrict_apply (f : (a : α) → π a) (s : Set α) (x : s) : s.domRestrict f x = f x :=
  rfl

theorem domRestrict_eq_iff {f : ∀ a, π a} {s : Set α} {g : ∀ a : s, π a} :
    domRestrict s f = g ↔ ∀ (a) (ha : a ∈ s), f a = g ⟨a, ha⟩ :=
  funext_iff.trans Subtype.forall

theorem eq_domRestrict_iff {s : Set α} {f : ∀ a : s, π a} {g : ∀ a, π a} :
    f = domRestrict s g ↔ ∀ (a) (ha : a ∈ s), f ⟨a, ha⟩ = g a :=
  funext_iff.trans Subtype.forall

@[simp]
theorem range_domRestrict (f : α → β) (s : Set α) : Set.range (s.domRestrict f) = f '' s :=
  (range_comp _ _).trans <| congr_arg (f '' ·) Subtype.range_coe

theorem image_domRestrict (f : α → β) (s t : Set α) :
    s.domRestrict f '' Subtype.val ⁻¹' t = f '' (t ∩ s) := by
  rw [domRestrict_eq, image_comp, image_preimage_eq_inter_range, Subtype.range_coe]

@[simp]
theorem domRestrict_dite {s : Set α} [∀ x, Decidable (x ∈ s)] (f : ∀ a ∈ s, β)
    (g : ∀ a ∉ s, β) :
    (s.domRestrict fun a => if h : a ∈ s then f a h else g a h) = (fun a : s => f a a.2) :=
  funext fun a => dif_pos a.2

@[simp]
theorem domRestrict_dite_compl {s : Set α} [∀ x, Decidable (x ∈ s)] (f : ∀ a ∈ s, β)
    (g : ∀ a ∉ s, β) :
    (sᶜ.domRestrict fun a => if h : a ∈ s then f a h else g a h) =
      (fun a : (sᶜ : Set α) => g a a.2) :=
  funext fun a => dif_neg a.2

@[simp]
theorem domRestrict_ite (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    (s.domRestrict fun a => if a ∈ s then f a else g a) = s.domRestrict f := domRestrict_dite _ _

@[simp]
theorem domRestrict_ite_compl (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    (sᶜ.domRestrict fun a => if a ∈ s then f a else g a) = sᶜ.domRestrict g :=
  domRestrict_dite_compl _ _

@[simp]
theorem domRestrict_piecewise (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    s.domRestrict (piecewise s f g) = s.domRestrict f := domRestrict_ite _ _ _

@[simp]
theorem domRestrict_piecewise_compl (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    sᶜ.domRestrict (piecewise s f g) = sᶜ.domRestrict g := domRestrict_ite_compl _ _ _

theorem domRestrict_extend_range (f : α → β) (g : α → γ) (g' : β → γ) :
    (range f).domRestrict (extend f g g') = fun x => g x.coe_prop.choose := by
  classical
  exact domRestrict_dite _ _

@[simp]
theorem domRestrict_extend_compl_range (f : α → β) (g : α → γ) (g' : β → γ) :
    (range f)ᶜ.domRestrict (extend f g g') = g' ∘ Subtype.val := by
  classical
  exact domRestrict_dite_compl _ _

/-- If a function `f` is restricted to a set `t`, and `s ⊆ t`, this is the restriction to `s`. -/
@[simp]
def domRestrict₂ {s t : Set α} (hst : s ⊆ t) (f : ∀ a : t, π a) : ∀ a : s, π a :=
  fun x => f ⟨x.1, hst x.2⟩

theorem domRestrict₂_def {s t : Set α} (hst : s ⊆ t) :
    domRestrict₂ (π := π) hst = fun f x ↦ f ⟨x.1, hst x.2⟩ := rfl

theorem domRestrict₂_comp_domRestrict {s t : Set α} (hst : s ⊆ t) :
    (domRestrict₂ (π := π) hst) ∘ t.domRestrict = s.domRestrict := rfl

theorem domRestrict₂_comp_domRestrict₂ {s t u : Set α} (hst : s ⊆ t) (htu : t ⊆ u) :
    (domRestrict₂ (π := π) hst) ∘ (domRestrict₂ htu) = domRestrict₂ (hst.trans htu) := rfl

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

/-- If `g` factors through `f` and `g` is injective, then `extend f g j` is injective on the
range of `f`. -/
lemma _root_.Function.FactorsThrough.extend_injOn {f : α → β} {g : α → γ} {j : β → γ}
    (hf : g.FactorsThrough f) (hg : g.Injective) :
    (range f).InjOn (extend f g j) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ heq
  rw [hf.extend_apply, hf.extend_apply] at heq
  rw [hg heq]

/-- If `f` and `g` are injective, then `extend f g j` is injective on the range of `f`. -/
lemma _root_.Function.Injective.extend_injOn {f : α → β} {g : α → γ} {j : β → γ}
    (hf : f.Injective) (hg : g.Injective) :
    (range f).InjOn (extend f g j) :=
  (hf.factorsThrough g).extend_injOn hg

/-- Restrict codomain of a function `f` to a set `s`. Same as `Subtype.coind` but this version
has codomain `↥s` instead of `Subtype s`. -/
def codRestrict (f : ι → α) (s : Set α) (h : ∀ x, f x ∈ s) : ι → s := fun x => ⟨f x, h x⟩

@[simp]
theorem val_codRestrict_apply (f : ι → α) (s : Set α) (h : ∀ x, f x ∈ s) (x : ι) :
    (codRestrict f s h x : α) = f x :=
  rfl

@[simp]
theorem domRestrict_comp_codRestrict {f : ι → α} {g : α → β} {b : Set α}
    (h : ∀ x, f x ∈ b) : b.domRestrict g ∘ b.codRestrict f h = g ∘ f :=
  rfl

@[simp]
theorem injective_codRestrict {f : ι → α} {s : Set α} (h : ∀ x, f x ∈ s) :
    Injective (codRestrict f s h) ↔ Injective f := by
  simp only [Injective, Subtype.ext_iff, val_codRestrict_apply]

alias ⟨_, _root_.Function.Injective.codRestrict⟩ := injective_codRestrict

@[simp] theorem range_codRestrict {f : ι → α} {s : Set α} (h : ∀ x, f x ∈ s) :
    range (s.codRestrict f h) = (↑) ⁻¹' range f := by
  ext; simp [Subtype.ext_iff]

theorem surjective_codRestrict {f : ι → α} {s : Set α} (h : ∀ x, f x ∈ s) :
    (s.codRestrict f h).Surjective ↔ range f = s := by
  simp [← range_eq_univ, Subset.antisymm_iff (a := range f), range_subset_iff, h]

theorem codRestrict_range_surjective (f : ι → α) :
    ((range f).codRestrict f mem_range_self).Surjective := by
  rintro ⟨b, ⟨a, rfl⟩⟩
  exact ⟨a, rfl⟩

variable {s : Set α} {f₁ f₂ : α → β}

@[simp]
theorem domRestrict_eq_domRestrict_iff :
    domRestrict s f₁ = domRestrict s f₂ ↔ EqOn f₁ f₂ s := domRestrict_eq_iff

@[deprecated (since := "2026-07-19")] alias restrict := domRestrict
@[deprecated (since := "2026-07-19")] alias restrict_def := domRestrict_def
@[deprecated (since := "2026-07-19")] alias restrict_eq := domRestrict_eq
@[deprecated (since := "2026-07-19")] alias restrict_id := domRestrict_id
@[deprecated (since := "2026-07-19")] alias restrict_apply := domRestrict_apply
@[deprecated (since := "2026-07-19")] alias restrict_eq_iff := domRestrict_eq_iff
@[deprecated (since := "2026-07-19")] alias eq_restrict_iff := eq_domRestrict_iff
@[deprecated (since := "2026-07-19")] alias range_restrict := range_domRestrict
@[deprecated (since := "2026-07-19")] alias image_restrict := image_domRestrict
@[deprecated (since := "2026-07-19")] alias restrict_dite := domRestrict_dite
@[deprecated (since := "2026-07-19")] alias restrict_dite_compl := domRestrict_dite_compl
@[deprecated (since := "2026-07-19")] alias restrict_ite := domRestrict_ite
@[deprecated (since := "2026-07-19")] alias restrict_ite_compl := domRestrict_ite_compl
@[deprecated (since := "2026-07-19")] alias restrict_piecewise := domRestrict_piecewise
@[deprecated (since := "2026-07-19")] alias restrict_piecewise_compl := domRestrict_piecewise_compl
@[deprecated (since := "2026-07-19")] alias restrict_extend_range := domRestrict_extend_range
@[deprecated (since := "2026-07-19")]
alias restrict_extend_compl_range := domRestrict_extend_compl_range
@[deprecated (since := "2026-07-19")] alias restrict₂ := domRestrict₂
@[deprecated (since := "2026-07-19")] alias restrict₂_def := domRestrict₂_def
@[deprecated (since := "2026-07-19")] alias restrict₂_comp_restrict := domRestrict₂_comp_domRestrict
@[deprecated (since := "2026-07-19")]
alias restrict₂_comp_restrict₂ := domRestrict₂_comp_domRestrict₂
@[deprecated (since := "2026-07-19")]
alias restrict_comp_codRestrict := domRestrict_comp_codRestrict
@[deprecated (since := "2026-07-19")]
alias restrict_eq_restrict_iff := domRestrict_eq_domRestrict_iff

end domRestrict

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
theorem codRestrict_domRestrict (h : ∀ x : s, f x ∈ t) :
    codRestrict (s.domRestrict f) t h = MapsTo.restrict f s t fun x hx => h ⟨x, hx⟩ :=
  rfl

@[deprecated (since := "2026-07-19")] alias codRestrict_restrict := codRestrict_domRestrict

/-- Reverse of `Set.codRestrict_domRestrict`. -/
theorem MapsTo.restrict_eq_codRestrict (h : MapsTo f s t) :
    h.restrict f s t = codRestrict (s.domRestrict f) t fun x => h x.2 :=
  rfl

theorem MapsTo.coe_restrict (h : Set.MapsTo f s t) :
    Subtype.val ∘ h.restrict f s t = s.domRestrict f :=
  rfl

theorem MapsTo.range_restrict (f : α → β) (s : Set α) (t : Set β) (h : MapsTo f s t) :
    range (h.restrict f s t) = Subtype.val ⁻¹' f '' s :=
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
    t.restrictPreimage f '' Subtype.val ⁻¹' s = Subtype.val ⁻¹' f '' s := by
  delta Set.restrictPreimage
  rw [← (Subtype.coe_injective).image_injective.eq_iff, ← image_comp, MapsTo.restrict_commutes,
    image_comp, Subtype.image_preimage_coe, Subtype.image_preimage_coe, image_preimage_inter]

variable (f) in
theorem range_restrictPreimage : range (t.restrictPreimage f) = Subtype.val ⁻¹' range f := by
  simp only [← image_univ, ← image_restrictPreimage, preimage_univ]

@[simp]
theorem restrictPreimage_mk (h : a ∈ f ⁻¹' t) : t.restrictPreimage f ⟨a, h⟩ = ⟨f a, h⟩ := rfl

theorem image_val_preimage_restrictPreimage {u : Set t} :
    Subtype.val '' t.restrictPreimage f ⁻¹' u = f ⁻¹' Subtype.val '' u := by
  ext
  simp

theorem preimage_restrictPreimage {u : Set t} :
    t.restrictPreimage f ⁻¹' u = (fun a : f ⁻¹' t ↦ f a) ⁻¹' Subtype.val '' u := by
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

theorem injOn_iff_injective : InjOn f s ↔ Injective (s.domRestrict f) :=
  ⟨fun H a b h => Subtype.ext <| H a.2 b.2 h, fun H a as b bs h =>
    congr_arg Subtype.val <| @H ⟨a, as⟩ ⟨b, bs⟩ h⟩

alias ⟨InjOn.injective, _⟩ := Set.injOn_iff_injective

set_option backward.isDefEq.respectTransparency false in
theorem MapsTo.restrict_inj (h : MapsTo f s t) : Injective (h.restrict f s t) ↔ InjOn f s := by
  rw [h.restrict_eq_codRestrict, injective_codRestrict, injOn_iff_injective]

end injOn

/-! ### Surjectivity on a set -/
section surjOn

theorem surjOn_iff_surjective : SurjOn f s univ ↔ Surjective (s.domRestrict f) :=
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
