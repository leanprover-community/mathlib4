/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module order.filter.extr
! leanprover-community/mathlib commit 1f0096e6caa61e9c849ec2adbd227e960e9dff58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Filter.Basic

/-!
# Minimum and maximum w.r.t. a filter and on a aet

## Main Definitions

This file defines six predicates of the form `is_A_B`, where `A` is `min`, `max`, or `extr`,
and `B` is `filter` or `on`.

* `is_min_filter f l a` means that `f a ≤ f x` in some `l`-neighborhood of `a`;
* `is_max_filter f l a` means that `f x ≤ f a` in some `l`-neighborhood of `a`;
* `is_extr_filter f l a` means `is_min_filter f l a` or `is_max_filter f l a`.

Similar predicates with `_on` suffix are particular cases for `l = 𝓟 s`.

## Main statements

### Change of the filter (set) argument

* `is_*_filter.filter_mono` : replace the filter with a smaller one;
* `is_*_filter.filter_inf` : replace a filter `l` with `l ⊓ l'`;
* `is_*_on.on_subset` : restrict to a smaller set;
* `is_*_on.inter` : replace a set `s` wtih `s ∩ t`.

### Composition

* `is_*_*.comp_mono` : if `x` is an extremum for `f` and `g` is a monotone function,
  then `x` is an extremum for `g ∘ f`;
* `is_*_*.comp_antitone` : similarly for the case of antitone `g`;
* `is_*_*.bicomp_mono` : if `x` is an extremum of the same type for `f` and `g`
  and a binary operation `op` is monotone in both arguments, then `x` is an extremum
  of the same type for `λ x, op (f x) (g x)`.
* `is_*_filter.comp_tendsto` : if `g x` is an extremum for `f` w.r.t. `l'` and `tendsto g l l'`,
  then `x` is an extremum for `f ∘ g` w.r.t. `l`.
* `is_*_on.on_preimage` : if `g x` is an extremum for `f` on `s`, then `x` is an extremum
  for `f ∘ g` on `g ⁻¹' s`.

### Algebraic operations

* `is_*_*.add` : if `x` is an extremum of the same type for two functions,
  then it is an extremum of the same type for their sum;
* `is_*_*.neg` : if `x` is an extremum for `f`, then it is an extremum
  of the opposite type for `-f`;
* `is_*_*.sub` : if `x` is an a minimum for `f` and a maximum for `g`,
  then it is a minimum for `f - g` and a maximum for `g - f`;
* `is_*_*.max`, `is_*_*.min`, `is_*_*.sup`, `is_*_*.inf` : similarly for `is_*_*.add`
  for pointwise `max`, `min`, `sup`, `inf`, respectively.


### Miscellaneous definitions

* `is_*_*_const` : any point is both a minimum and maximum for a constant function;
* `is_min/max_*.is_ext` : any minimum/maximum point is an extremum;
* `is_*_*.dual`, `is_*_*.undual`: conversion between codomains `α` and `dual α`;

## Missing features (TODO)

* Multiplication and division;
* `is_*_*.bicompl` : if `x` is a minimum for `f`, `y` is a minimum for `g`, and `op` is a monotone
  binary operation, then `(x, y)` is a minimum for `uncurry (bicompl op f g)`. From this point
  of view, `is_*_*.bicomp` is a composition
* It would be nice to have a tactic that specializes `comp_(anti)mono` or `bicomp_mono`
  based on a proof of monotonicity of a given (binary) function. The tactic should maintain a `meta`
  list of known (anti)monotone (binary) functions with their names, as well as a list of special
  types of filters, and define the missing lemmas once one of these two lists grows.
-/


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

open Set Filter

open Filter

section Preorder

variable [Preorder β] [Preorder γ]

variable (f : α → β) (s : Set α) (l : Filter α) (a : α)

/-! ### Definitions -/


/-- `is_min_filter f l a` means that `f a ≤ f x` in some `l`-neighborhood of `a` -/
def IsMinFilter : Prop :=
  ∀ᶠ x in l, f a ≤ f x
#align is_min_filter IsMinFilter

/-- `is_max_filter f l a` means that `f x ≤ f a` in some `l`-neighborhood of `a` -/
def IsMaxFilter : Prop :=
  ∀ᶠ x in l, f x ≤ f a
#align is_max_filter IsMaxFilter

/-- `is_extr_filter f l a` means `is_min_filter f l a` or `is_max_filter f l a` -/
def IsExtrFilter : Prop :=
  IsMinFilter f l a ∨ IsMaxFilter f l a
#align is_extr_filter IsExtrFilter

/-- `is_min_on f s a` means that `f a ≤ f x` for all `x ∈ a`. Note that we do not assume `a ∈ s`. -/
def IsMinOn :=
  IsMinFilter f (𝓟 s) a
#align is_min_on IsMinOn

/-- `is_max_on f s a` means that `f x ≤ f a` for all `x ∈ a`. Note that we do not assume `a ∈ s`. -/
def IsMaxOn :=
  IsMaxFilter f (𝓟 s) a
#align is_max_on IsMaxOn

/-- `is_extr_on f s a` means `is_min_on f s a` or `is_max_on f s a` -/
def IsExtrOn : Prop :=
  IsExtrFilter f (𝓟 s) a
#align is_extr_on IsExtrOn

variable {f s a l} {t : Set α} {l' : Filter α}

theorem IsExtrOn.elim {p : Prop} : IsExtrOn f s a → (IsMinOn f s a → p) → (IsMaxOn f s a → p) → p :=
  Or.elim
#align is_extr_on.elim IsExtrOn.elim

theorem isMinOn_iff : IsMinOn f s a ↔ ∀ x ∈ s, f a ≤ f x :=
  Iff.rfl
#align is_min_on_iff isMinOn_iff

theorem isMaxOn_iff : IsMaxOn f s a ↔ ∀ x ∈ s, f x ≤ f a :=
  Iff.rfl
#align is_max_on_iff isMaxOn_iff

theorem isMinOn_univ_iff : IsMinOn f univ a ↔ ∀ x, f a ≤ f x :=
  univ_subset_iff.trans eq_univ_iff_forall
#align is_min_on_univ_iff isMinOn_univ_iff

theorem isMaxOn_univ_iff : IsMaxOn f univ a ↔ ∀ x, f x ≤ f a :=
  univ_subset_iff.trans eq_univ_iff_forall
#align is_max_on_univ_iff isMaxOn_univ_iff

theorem IsMinFilter.tendsto_principal_ici (h : IsMinFilter f l a) : Tendsto f l (𝓟 <| Ici (f a)) :=
  tendsto_principal.2 h
#align is_min_filter.tendsto_principal_Ici IsMinFilter.tendsto_principal_ici

theorem IsMaxFilter.tendsto_principal_iic (h : IsMaxFilter f l a) : Tendsto f l (𝓟 <| Iic (f a)) :=
  tendsto_principal.2 h
#align is_max_filter.tendsto_principal_Iic IsMaxFilter.tendsto_principal_iic

/-! ### Conversion to `is_extr_*` -/


theorem IsMinFilter.is_extr : IsMinFilter f l a → IsExtrFilter f l a :=
  Or.inl
#align is_min_filter.is_extr IsMinFilter.is_extr

theorem IsMaxFilter.is_extr : IsMaxFilter f l a → IsExtrFilter f l a :=
  Or.inr
#align is_max_filter.is_extr IsMaxFilter.is_extr

theorem IsMinOn.is_extr (h : IsMinOn f s a) : IsExtrOn f s a :=
  h.is_extr
#align is_min_on.is_extr IsMinOn.is_extr

theorem IsMaxOn.is_extr (h : IsMaxOn f s a) : IsExtrOn f s a :=
  h.is_extr
#align is_max_on.is_extr IsMaxOn.is_extr

/-! ### Constant function -/


theorem isMinFilter_const {b : β} : IsMinFilter (fun _ => b) l a :=
  univ_mem' fun _ => le_rfl
#align is_min_filter_const isMinFilter_const

theorem isMaxFilter_const {b : β} : IsMaxFilter (fun _ => b) l a :=
  univ_mem' fun _ => le_rfl
#align is_max_filter_const isMaxFilter_const

theorem isExtrFilter_const {b : β} : IsExtrFilter (fun _ => b) l a :=
  isMinFilter_const.is_extr
#align is_extr_filter_const isExtrFilter_const

theorem isMinOn_const {b : β} : IsMinOn (fun _ => b) s a :=
  isMinFilter_const
#align is_min_on_const isMinOn_const

theorem isMaxOn_const {b : β} : IsMaxOn (fun _ => b) s a :=
  isMaxFilter_const
#align is_max_on_const isMaxOn_const

theorem isExtrOn_const {b : β} : IsExtrOn (fun _ => b) s a :=
  isExtrFilter_const
#align is_extr_on_const isExtrOn_const

/-! ### Order dual -/


open OrderDual (toDual)

theorem isMinFilter_dual_iff : IsMinFilter (to_dual ∘ f) l a ↔ IsMaxFilter f l a :=
  Iff.rfl
#align is_min_filter_dual_iff isMinFilter_dual_iff

theorem isMaxFilter_dual_iff : IsMaxFilter (to_dual ∘ f) l a ↔ IsMinFilter f l a :=
  Iff.rfl
#align is_max_filter_dual_iff isMaxFilter_dual_iff

theorem isExtrFilter_dual_iff : IsExtrFilter (to_dual ∘ f) l a ↔ IsExtrFilter f l a :=
  or_comm' _ _
#align is_extr_filter_dual_iff isExtrFilter_dual_iff

alias isMinFilter_dual_iff ↔ IsMinFilter.undual IsMaxFilter.dual
#align is_min_filter.undual IsMinFilter.undual
#align is_max_filter.dual IsMaxFilter.dual

alias isMaxFilter_dual_iff ↔ IsMaxFilter.undual IsMinFilter.dual
#align is_max_filter.undual IsMaxFilter.undual
#align is_min_filter.dual IsMinFilter.dual

alias isExtrFilter_dual_iff ↔ IsExtrFilter.undual IsExtrFilter.dual
#align is_extr_filter.undual IsExtrFilter.undual
#align is_extr_filter.dual IsExtrFilter.dual

theorem isMinOn_dual_iff : IsMinOn (to_dual ∘ f) s a ↔ IsMaxOn f s a :=
  Iff.rfl
#align is_min_on_dual_iff isMinOn_dual_iff

theorem isMaxOn_dual_iff : IsMaxOn (to_dual ∘ f) s a ↔ IsMinOn f s a :=
  Iff.rfl
#align is_max_on_dual_iff isMaxOn_dual_iff

theorem isExtrOn_dual_iff : IsExtrOn (to_dual ∘ f) s a ↔ IsExtrOn f s a :=
  or_comm' _ _
#align is_extr_on_dual_iff isExtrOn_dual_iff

alias isMinOn_dual_iff ↔ IsMinOn.undual IsMaxOn.dual
#align is_min_on.undual IsMinOn.undual
#align is_max_on.dual IsMaxOn.dual

alias isMaxOn_dual_iff ↔ IsMaxOn.undual IsMinOn.dual
#align is_max_on.undual IsMaxOn.undual
#align is_min_on.dual IsMinOn.dual

alias isExtrOn_dual_iff ↔ IsExtrOn.undual IsExtrOn.dual
#align is_extr_on.undual IsExtrOn.undual
#align is_extr_on.dual IsExtrOn.dual

/-! ### Operations on the filter/set -/


theorem IsMinFilter.filter_mono (h : IsMinFilter f l a) (hl : l' ≤ l) : IsMinFilter f l' a :=
  hl h
#align is_min_filter.filter_mono IsMinFilter.filter_mono

theorem IsMaxFilter.filter_mono (h : IsMaxFilter f l a) (hl : l' ≤ l) : IsMaxFilter f l' a :=
  hl h
#align is_max_filter.filter_mono IsMaxFilter.filter_mono

theorem IsExtrFilter.filter_mono (h : IsExtrFilter f l a) (hl : l' ≤ l) : IsExtrFilter f l' a :=
  h.elim (fun h => (h.filter_mono hl).is_extr) fun h => (h.filter_mono hl).is_extr
#align is_extr_filter.filter_mono IsExtrFilter.filter_mono

theorem IsMinFilter.filter_inf (h : IsMinFilter f l a) (l') : IsMinFilter f (l ⊓ l') a :=
  h.filter_mono inf_le_left
#align is_min_filter.filter_inf IsMinFilter.filter_inf

theorem IsMaxFilter.filter_inf (h : IsMaxFilter f l a) (l') : IsMaxFilter f (l ⊓ l') a :=
  h.filter_mono inf_le_left
#align is_max_filter.filter_inf IsMaxFilter.filter_inf

theorem IsExtrFilter.filter_inf (h : IsExtrFilter f l a) (l') : IsExtrFilter f (l ⊓ l') a :=
  h.filter_mono inf_le_left
#align is_extr_filter.filter_inf IsExtrFilter.filter_inf

theorem IsMinOn.on_subset (hf : IsMinOn f t a) (h : s ⊆ t) : IsMinOn f s a :=
  hf.filter_mono <| principal_mono.2 h
#align is_min_on.on_subset IsMinOn.on_subset

theorem IsMaxOn.on_subset (hf : IsMaxOn f t a) (h : s ⊆ t) : IsMaxOn f s a :=
  hf.filter_mono <| principal_mono.2 h
#align is_max_on.on_subset IsMaxOn.on_subset

theorem IsExtrOn.on_subset (hf : IsExtrOn f t a) (h : s ⊆ t) : IsExtrOn f s a :=
  hf.filter_mono <| principal_mono.2 h
#align is_extr_on.on_subset IsExtrOn.on_subset

theorem IsMinOn.inter (hf : IsMinOn f s a) (t) : IsMinOn f (s ∩ t) a :=
  hf.on_subset (inter_subset_left s t)
#align is_min_on.inter IsMinOn.inter

theorem IsMaxOn.inter (hf : IsMaxOn f s a) (t) : IsMaxOn f (s ∩ t) a :=
  hf.on_subset (inter_subset_left s t)
#align is_max_on.inter IsMaxOn.inter

theorem IsExtrOn.inter (hf : IsExtrOn f s a) (t) : IsExtrOn f (s ∩ t) a :=
  hf.on_subset (inter_subset_left s t)
#align is_extr_on.inter IsExtrOn.inter

/-! ### Composition with (anti)monotone functions -/


theorem IsMinFilter.comp_mono (hf : IsMinFilter f l a) {g : β → γ} (hg : Monotone g) :
    IsMinFilter (g ∘ f) l a :=
  mem_of_superset hf fun x hx => hg hx
#align is_min_filter.comp_mono IsMinFilter.comp_mono

theorem IsMaxFilter.comp_mono (hf : IsMaxFilter f l a) {g : β → γ} (hg : Monotone g) :
    IsMaxFilter (g ∘ f) l a :=
  mem_of_superset hf fun x hx => hg hx
#align is_max_filter.comp_mono IsMaxFilter.comp_mono

theorem IsExtrFilter.comp_mono (hf : IsExtrFilter f l a) {g : β → γ} (hg : Monotone g) :
    IsExtrFilter (g ∘ f) l a :=
  hf.elim (fun hf => (hf.comp_mono hg).is_extr) fun hf => (hf.comp_mono hg).is_extr
#align is_extr_filter.comp_mono IsExtrFilter.comp_mono

theorem IsMinFilter.comp_antitone (hf : IsMinFilter f l a) {g : β → γ} (hg : Antitone g) :
    IsMaxFilter (g ∘ f) l a :=
  hf.dual.comp_mono fun x y h => hg h
#align is_min_filter.comp_antitone IsMinFilter.comp_antitone

theorem IsMaxFilter.comp_antitone (hf : IsMaxFilter f l a) {g : β → γ} (hg : Antitone g) :
    IsMinFilter (g ∘ f) l a :=
  hf.dual.comp_mono fun x y h => hg h
#align is_max_filter.comp_antitone IsMaxFilter.comp_antitone

theorem IsExtrFilter.comp_antitone (hf : IsExtrFilter f l a) {g : β → γ} (hg : Antitone g) :
    IsExtrFilter (g ∘ f) l a :=
  hf.dual.comp_mono fun x y h => hg h
#align is_extr_filter.comp_antitone IsExtrFilter.comp_antitone

theorem IsMinOn.comp_mono (hf : IsMinOn f s a) {g : β → γ} (hg : Monotone g) :
    IsMinOn (g ∘ f) s a :=
  hf.comp_mono hg
#align is_min_on.comp_mono IsMinOn.comp_mono

theorem IsMaxOn.comp_mono (hf : IsMaxOn f s a) {g : β → γ} (hg : Monotone g) :
    IsMaxOn (g ∘ f) s a :=
  hf.comp_mono hg
#align is_max_on.comp_mono IsMaxOn.comp_mono

theorem IsExtrOn.comp_mono (hf : IsExtrOn f s a) {g : β → γ} (hg : Monotone g) :
    IsExtrOn (g ∘ f) s a :=
  hf.comp_mono hg
#align is_extr_on.comp_mono IsExtrOn.comp_mono

theorem IsMinOn.comp_antitone (hf : IsMinOn f s a) {g : β → γ} (hg : Antitone g) :
    IsMaxOn (g ∘ f) s a :=
  hf.comp_antitone hg
#align is_min_on.comp_antitone IsMinOn.comp_antitone

theorem IsMaxOn.comp_antitone (hf : IsMaxOn f s a) {g : β → γ} (hg : Antitone g) :
    IsMinOn (g ∘ f) s a :=
  hf.comp_antitone hg
#align is_max_on.comp_antitone IsMaxOn.comp_antitone

theorem IsExtrOn.comp_antitone (hf : IsExtrOn f s a) {g : β → γ} (hg : Antitone g) :
    IsExtrOn (g ∘ f) s a :=
  hf.comp_antitone hg
#align is_extr_on.comp_antitone IsExtrOn.comp_antitone

theorem IsMinFilter.bicomp_mono [Preorder δ] {op : β → γ → δ}
    (hop : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) op op) (hf : IsMinFilter f l a) {g : α → γ}
    (hg : IsMinFilter g l a) : IsMinFilter (fun x => op (f x) (g x)) l a :=
  mem_of_superset (inter_mem hf hg) fun x ⟨hfx, hgx⟩ => hop hfx hgx
#align is_min_filter.bicomp_mono IsMinFilter.bicomp_mono

theorem IsMaxFilter.bicomp_mono [Preorder δ] {op : β → γ → δ}
    (hop : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) op op) (hf : IsMaxFilter f l a) {g : α → γ}
    (hg : IsMaxFilter g l a) : IsMaxFilter (fun x => op (f x) (g x)) l a :=
  mem_of_superset (inter_mem hf hg) fun x ⟨hfx, hgx⟩ => hop hfx hgx
#align is_max_filter.bicomp_mono IsMaxFilter.bicomp_mono

-- No `extr` version because we need `hf` and `hg` to be of the same kind
theorem IsMinOn.bicomp_mono [Preorder δ] {op : β → γ → δ}
    (hop : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) op op) (hf : IsMinOn f s a) {g : α → γ}
    (hg : IsMinOn g s a) : IsMinOn (fun x => op (f x) (g x)) s a :=
  hf.bicomp_mono hop hg
#align is_min_on.bicomp_mono IsMinOn.bicomp_mono

theorem IsMaxOn.bicomp_mono [Preorder δ] {op : β → γ → δ}
    (hop : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) op op) (hf : IsMaxOn f s a) {g : α → γ}
    (hg : IsMaxOn g s a) : IsMaxOn (fun x => op (f x) (g x)) s a :=
  hf.bicomp_mono hop hg
#align is_max_on.bicomp_mono IsMaxOn.bicomp_mono

/-! ### Composition with `tendsto` -/


theorem IsMinFilter.comp_tendsto {g : δ → α} {l' : Filter δ} {b : δ} (hf : IsMinFilter f l (g b))
    (hg : Tendsto g l' l) : IsMinFilter (f ∘ g) l' b :=
  hg hf
#align is_min_filter.comp_tendsto IsMinFilter.comp_tendsto

theorem IsMaxFilter.comp_tendsto {g : δ → α} {l' : Filter δ} {b : δ} (hf : IsMaxFilter f l (g b))
    (hg : Tendsto g l' l) : IsMaxFilter (f ∘ g) l' b :=
  hg hf
#align is_max_filter.comp_tendsto IsMaxFilter.comp_tendsto

theorem IsExtrFilter.comp_tendsto {g : δ → α} {l' : Filter δ} {b : δ} (hf : IsExtrFilter f l (g b))
    (hg : Tendsto g l' l) : IsExtrFilter (f ∘ g) l' b :=
  hf.elim (fun hf => (hf.comp_tendsto hg).is_extr) fun hf => (hf.comp_tendsto hg).is_extr
#align is_extr_filter.comp_tendsto IsExtrFilter.comp_tendsto

theorem IsMinOn.on_preimage (g : δ → α) {b : δ} (hf : IsMinOn f s (g b)) :
    IsMinOn (f ∘ g) (g ⁻¹' s) b :=
  hf.comp_tendsto (tendsto_principal_principal.mpr <| Subset.refl _)
#align is_min_on.on_preimage IsMinOn.on_preimage

theorem IsMaxOn.on_preimage (g : δ → α) {b : δ} (hf : IsMaxOn f s (g b)) :
    IsMaxOn (f ∘ g) (g ⁻¹' s) b :=
  hf.comp_tendsto (tendsto_principal_principal.mpr <| Subset.refl _)
#align is_max_on.on_preimage IsMaxOn.on_preimage

theorem IsExtrOn.on_preimage (g : δ → α) {b : δ} (hf : IsExtrOn f s (g b)) :
    IsExtrOn (f ∘ g) (g ⁻¹' s) b :=
  hf.elim (fun hf => (hf.on_preimage g).is_extr) fun hf => (hf.on_preimage g).is_extr
#align is_extr_on.on_preimage IsExtrOn.on_preimage

theorem IsMinOn.comp_mapsTo {t : Set δ} {g : δ → α} {b : δ} (hf : IsMinOn f s a) (hg : MapsTo g t s)
    (ha : g b = a) : IsMinOn (f ∘ g) t b := fun y hy => by
  simpa only [mem_set_of_eq, ha, (· ∘ ·)] using hf (hg hy)
#align is_min_on.comp_maps_to IsMinOn.comp_mapsTo

theorem IsMaxOn.comp_mapsTo {t : Set δ} {g : δ → α} {b : δ} (hf : IsMaxOn f s a) (hg : MapsTo g t s)
    (ha : g b = a) : IsMaxOn (f ∘ g) t b :=
  hf.dual.comp_maps_to hg ha
#align is_max_on.comp_maps_to IsMaxOn.comp_mapsTo

theorem IsExtrOn.comp_mapsTo {t : Set δ} {g : δ → α} {b : δ} (hf : IsExtrOn f s a)
    (hg : MapsTo g t s) (ha : g b = a) : IsExtrOn (f ∘ g) t b :=
  hf.elim (fun h => Or.inl <| h.comp_maps_to hg ha) fun h => Or.inr <| h.comp_maps_to hg ha
#align is_extr_on.comp_maps_to IsExtrOn.comp_mapsTo

end Preorder

/-! ### Pointwise addition -/


section OrderedAddCommMonoid

variable [OrderedAddCommMonoid β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

theorem IsMinFilter.add (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) :
    IsMinFilter (fun x => f x + g x) l a :=
  show IsMinFilter (fun x => f x + g x) l a from
    hf.bicomp_mono (fun x x' hx y y' hy => add_le_add hx hy) hg
#align is_min_filter.add IsMinFilter.add

theorem IsMaxFilter.add (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) :
    IsMaxFilter (fun x => f x + g x) l a :=
  show IsMaxFilter (fun x => f x + g x) l a from
    hf.bicomp_mono (fun x x' hx y y' hy => add_le_add hx hy) hg
#align is_max_filter.add IsMaxFilter.add

theorem IsMinOn.add (hf : IsMinOn f s a) (hg : IsMinOn g s a) : IsMinOn (fun x => f x + g x) s a :=
  hf.add hg
#align is_min_on.add IsMinOn.add

theorem IsMaxOn.add (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) : IsMaxOn (fun x => f x + g x) s a :=
  hf.add hg
#align is_max_on.add IsMaxOn.add

end OrderedAddCommMonoid

/-! ### Pointwise negation and subtraction -/


section OrderedAddCommGroup

variable [OrderedAddCommGroup β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

theorem IsMinFilter.neg (hf : IsMinFilter f l a) : IsMaxFilter (fun x => -f x) l a :=
  hf.comp_antitone fun x y hx => neg_le_neg hx
#align is_min_filter.neg IsMinFilter.neg

theorem IsMaxFilter.neg (hf : IsMaxFilter f l a) : IsMinFilter (fun x => -f x) l a :=
  hf.comp_antitone fun x y hx => neg_le_neg hx
#align is_max_filter.neg IsMaxFilter.neg

theorem IsExtrFilter.neg (hf : IsExtrFilter f l a) : IsExtrFilter (fun x => -f x) l a :=
  hf.elim (fun hf => hf.neg.is_extr) fun hf => hf.neg.is_extr
#align is_extr_filter.neg IsExtrFilter.neg

theorem IsMinOn.neg (hf : IsMinOn f s a) : IsMaxOn (fun x => -f x) s a :=
  hf.comp_antitone fun x y hx => neg_le_neg hx
#align is_min_on.neg IsMinOn.neg

theorem IsMaxOn.neg (hf : IsMaxOn f s a) : IsMinOn (fun x => -f x) s a :=
  hf.comp_antitone fun x y hx => neg_le_neg hx
#align is_max_on.neg IsMaxOn.neg

theorem IsExtrOn.neg (hf : IsExtrOn f s a) : IsExtrOn (fun x => -f x) s a :=
  hf.elim (fun hf => hf.neg.is_extr) fun hf => hf.neg.is_extr
#align is_extr_on.neg IsExtrOn.neg

theorem IsMinFilter.sub (hf : IsMinFilter f l a) (hg : IsMaxFilter g l a) :
    IsMinFilter (fun x => f x - g x) l a := by simpa only [sub_eq_add_neg] using hf.add hg.neg
#align is_min_filter.sub IsMinFilter.sub

theorem IsMaxFilter.sub (hf : IsMaxFilter f l a) (hg : IsMinFilter g l a) :
    IsMaxFilter (fun x => f x - g x) l a := by simpa only [sub_eq_add_neg] using hf.add hg.neg
#align is_max_filter.sub IsMaxFilter.sub

theorem IsMinOn.sub (hf : IsMinOn f s a) (hg : IsMaxOn g s a) : IsMinOn (fun x => f x - g x) s a :=
  by simpa only [sub_eq_add_neg] using hf.add hg.neg
#align is_min_on.sub IsMinOn.sub

theorem IsMaxOn.sub (hf : IsMaxOn f s a) (hg : IsMinOn g s a) : IsMaxOn (fun x => f x - g x) s a :=
  by simpa only [sub_eq_add_neg] using hf.add hg.neg
#align is_max_on.sub IsMaxOn.sub

end OrderedAddCommGroup

/-! ### Pointwise `sup`/`inf` -/


section SemilatticeSup

variable [SemilatticeSup β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

theorem IsMinFilter.sup (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) :
    IsMinFilter (fun x => f x ⊔ g x) l a :=
  show IsMinFilter (fun x => f x ⊔ g x) l a from
    hf.bicomp_mono (fun x x' hx y y' hy => sup_le_sup hx hy) hg
#align is_min_filter.sup IsMinFilter.sup

theorem IsMaxFilter.sup (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) :
    IsMaxFilter (fun x => f x ⊔ g x) l a :=
  show IsMaxFilter (fun x => f x ⊔ g x) l a from
    hf.bicomp_mono (fun x x' hx y y' hy => sup_le_sup hx hy) hg
#align is_max_filter.sup IsMaxFilter.sup

theorem IsMinOn.sup (hf : IsMinOn f s a) (hg : IsMinOn g s a) : IsMinOn (fun x => f x ⊔ g x) s a :=
  hf.sup hg
#align is_min_on.sup IsMinOn.sup

theorem IsMaxOn.sup (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) : IsMaxOn (fun x => f x ⊔ g x) s a :=
  hf.sup hg
#align is_max_on.sup IsMaxOn.sup

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

theorem IsMinFilter.inf (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) :
    IsMinFilter (fun x => f x ⊓ g x) l a :=
  show IsMinFilter (fun x => f x ⊓ g x) l a from
    hf.bicomp_mono (fun x x' hx y y' hy => inf_le_inf hx hy) hg
#align is_min_filter.inf IsMinFilter.inf

theorem IsMaxFilter.inf (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) :
    IsMaxFilter (fun x => f x ⊓ g x) l a :=
  show IsMaxFilter (fun x => f x ⊓ g x) l a from
    hf.bicomp_mono (fun x x' hx y y' hy => inf_le_inf hx hy) hg
#align is_max_filter.inf IsMaxFilter.inf

theorem IsMinOn.inf (hf : IsMinOn f s a) (hg : IsMinOn g s a) : IsMinOn (fun x => f x ⊓ g x) s a :=
  hf.inf hg
#align is_min_on.inf IsMinOn.inf

theorem IsMaxOn.inf (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) : IsMaxOn (fun x => f x ⊓ g x) s a :=
  hf.inf hg
#align is_max_on.inf IsMaxOn.inf

end SemilatticeInf

/-! ### Pointwise `min`/`max` -/


section LinearOrder

variable [LinearOrder β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

theorem IsMinFilter.min (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) :
    IsMinFilter (fun x => min (f x) (g x)) l a :=
  show IsMinFilter (fun x => min (f x) (g x)) l a from
    hf.bicomp_mono (fun x x' hx y y' hy => min_le_min hx hy) hg
#align is_min_filter.min IsMinFilter.min

theorem IsMaxFilter.min (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) :
    IsMaxFilter (fun x => min (f x) (g x)) l a :=
  show IsMaxFilter (fun x => min (f x) (g x)) l a from
    hf.bicomp_mono (fun x x' hx y y' hy => min_le_min hx hy) hg
#align is_max_filter.min IsMaxFilter.min

theorem IsMinOn.min (hf : IsMinOn f s a) (hg : IsMinOn g s a) :
    IsMinOn (fun x => min (f x) (g x)) s a :=
  hf.min hg
#align is_min_on.min IsMinOn.min

theorem IsMaxOn.min (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) :
    IsMaxOn (fun x => min (f x) (g x)) s a :=
  hf.min hg
#align is_max_on.min IsMaxOn.min

theorem IsMinFilter.max (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) :
    IsMinFilter (fun x => max (f x) (g x)) l a :=
  show IsMinFilter (fun x => max (f x) (g x)) l a from
    hf.bicomp_mono (fun x x' hx y y' hy => max_le_max hx hy) hg
#align is_min_filter.max IsMinFilter.max

theorem IsMaxFilter.max (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) :
    IsMaxFilter (fun x => max (f x) (g x)) l a :=
  show IsMaxFilter (fun x => max (f x) (g x)) l a from
    hf.bicomp_mono (fun x x' hx y y' hy => max_le_max hx hy) hg
#align is_max_filter.max IsMaxFilter.max

theorem IsMinOn.max (hf : IsMinOn f s a) (hg : IsMinOn g s a) :
    IsMinOn (fun x => max (f x) (g x)) s a :=
  hf.max hg
#align is_min_on.max IsMinOn.max

theorem IsMaxOn.max (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) :
    IsMaxOn (fun x => max (f x) (g x)) s a :=
  hf.max hg
#align is_max_on.max IsMaxOn.max

end LinearOrder

section Eventually

/-! ### Relation with `eventually` comparisons of two functions -/


theorem Filter.EventuallyLe.isMaxFilter {α β : Type _} [Preorder β] {f g : α → β} {a : α}
    {l : Filter α} (hle : g ≤ᶠ[l] f) (hfga : f a = g a) (h : IsMaxFilter f l a) :
    IsMaxFilter g l a := by
  refine' hle.mp (h.mono fun x hf hgf => _)
  rw [← hfga]
  exact le_trans hgf hf
#align filter.eventually_le.is_max_filter Filter.EventuallyLe.isMaxFilter

theorem IsMaxFilter.congr {α β : Type _} [Preorder β] {f g : α → β} {a : α} {l : Filter α}
    (h : IsMaxFilter f l a) (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsMaxFilter g l a :=
  HEq.symm.le.IsMaxFilter hfga h
#align is_max_filter.congr IsMaxFilter.congr

theorem Filter.EventuallyEq.isMaxFilter_iff {α β : Type _} [Preorder β] {f g : α → β} {a : α}
    {l : Filter α} (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsMaxFilter f l a ↔ IsMaxFilter g l a :=
  ⟨fun h => h.congr HEq hfga, fun h => h.congr HEq.symm hfga.symm⟩
#align filter.eventually_eq.is_max_filter_iff Filter.EventuallyEq.isMaxFilter_iff

theorem Filter.EventuallyLe.isMinFilter {α β : Type _} [Preorder β] {f g : α → β} {a : α}
    {l : Filter α} (hle : f ≤ᶠ[l] g) (hfga : f a = g a) (h : IsMinFilter f l a) :
    IsMinFilter g l a :=
  @Filter.EventuallyLe.isMaxFilter _ βᵒᵈ _ _ _ _ _ hle hfga h
#align filter.eventually_le.is_min_filter Filter.EventuallyLe.isMinFilter

theorem IsMinFilter.congr {α β : Type _} [Preorder β] {f g : α → β} {a : α} {l : Filter α}
    (h : IsMinFilter f l a) (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsMinFilter g l a :=
  HEq.le.IsMinFilter hfga h
#align is_min_filter.congr IsMinFilter.congr

theorem Filter.EventuallyEq.isMinFilter_iff {α β : Type _} [Preorder β] {f g : α → β} {a : α}
    {l : Filter α} (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsMinFilter f l a ↔ IsMinFilter g l a :=
  ⟨fun h => h.congr HEq hfga, fun h => h.congr HEq.symm hfga.symm⟩
#align filter.eventually_eq.is_min_filter_iff Filter.EventuallyEq.isMinFilter_iff

theorem IsExtrFilter.congr {α β : Type _} [Preorder β] {f g : α → β} {a : α} {l : Filter α}
    (h : IsExtrFilter f l a) (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsExtrFilter g l a :=
  by
  rw [IsExtrFilter] at *
  rwa [← heq.is_max_filter_iff hfga, ← heq.is_min_filter_iff hfga]
#align is_extr_filter.congr IsExtrFilter.congr

theorem Filter.EventuallyEq.isExtrFilter_iff {α β : Type _} [Preorder β] {f g : α → β} {a : α}
    {l : Filter α} (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsExtrFilter f l a ↔ IsExtrFilter g l a :=
  ⟨fun h => h.congr HEq hfga, fun h => h.congr HEq.symm hfga.symm⟩
#align filter.eventually_eq.is_extr_filter_iff Filter.EventuallyEq.isExtrFilter_iff

end Eventually

/-! ### `is_max_on`/`is_min_on` imply `csupr`/`cinfi` -/


section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {f : β → α} {s : Set β} {x₀ : β}

theorem IsMaxOn.supᵢ_eq (hx₀ : x₀ ∈ s) (h : IsMaxOn f s x₀) : (⨆ x : s, f x) = f x₀ :=
  haveI : Nonempty s := ⟨⟨x₀, hx₀⟩⟩
  csupᵢ_eq_of_forall_le_of_forall_lt_exists_gt (fun x => h x.Prop) fun w hw => ⟨⟨x₀, hx₀⟩, hw⟩
#align is_max_on.supr_eq IsMaxOn.supᵢ_eq

theorem IsMinOn.infᵢ_eq (hx₀ : x₀ ∈ s) (h : IsMinOn f s x₀) : (⨅ x : s, f x) = f x₀ :=
  @IsMaxOn.supᵢ_eq αᵒᵈ β _ _ _ _ hx₀ h
#align is_min_on.infi_eq IsMinOn.infᵢ_eq

end ConditionallyCompleteLinearOrder

