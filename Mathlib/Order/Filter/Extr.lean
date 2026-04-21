/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Minimum and maximum w.r.t. a filter and on a set

## Main Definitions

This file defines six predicates of the form `isAB`, where `A` is `Min`, `Max`, or `Extr`,
and `B` is `Filter` or `On`.

* `isMinFilter f l a` means that `f a ≤ f x` in some `l`-neighborhood of `a`;
* `isMaxFilter f l a` means that `f x ≤ f a` in some `l`-neighborhood of `a`;
* `isExtrFilter f l a` means `isMinFilter f l a` or `isMaxFilter f l a`.

Similar predicates with `on` suffix are particular cases for `l = 𝓟 s`.

## Main statements

### Change of the filter (set) argument

* `is*Filter.filter_mono` : replace the filter with a smaller one;
* `is*Filter.filter_inf` : replace a filter `l` with `l ⊓ l'`;
* `is*On.on_subset` : restrict to a smaller set;
* `is*Pn.inter` : replace a set `s` with `s ∩ t`.

### Composition

* `is**.comp_mono` : if `x` is an extremum for `f` and `g` is a monotone function,
  then `x` is an extremum for `g ∘ f`;
* `is**.comp_antitone` : similarly for the case of antitone `g`;
* `is**.bicomp_mono` : if `x` is an extremum of the same type for `f` and `g`
  and a binary operation `op` is monotone in both arguments, then `x` is an extremum
  of the same type for `fun x => op (f x) (g x)`.
* `is*Filter.comp_tendsto` : if `g x` is an extremum for `f` w.r.t. `l'` and `Tendsto g l l'`,
  then `x` is an extremum for `f ∘ g` w.r.t. `l`.
* `is*On.on_preimage` : if `g x` is an extremum for `f` on `s`, then `x` is an extremum
  for `f ∘ g` on `g ⁻¹' s`.

### Algebraic operations

* `is**.add` : if `x` is an extremum of the same type for two functions,
  then it is an extremum of the same type for their sum;
* `is**.neg` : if `x` is an extremum for `f`, then it is an extremum
  of the opposite type for `-f`;
* `is**.sub` : if `x` is a minimum for `f` and a maximum for `g`,
  then it is a minimum for `f - g` and a maximum for `g - f`;
* `is**.max`, `is**.min`, `is**.sup`, `is**.inf` : similarly for `is**.add`
  for pointwise `max`, `min`, `sup`, `inf`, respectively.


### Miscellaneous definitions

* `is**_const` : any point is both a minimum and maximum for a constant function;
* `isMin/Max*.isExt` : any minimum/maximum point is an extremum;
* `is**.dual`, `is**.undual`: conversion between codomains `α` and `dual α`;

## Missing features (TODO)

* Multiplication and division;
* `is**.bicompl` : if `x` is a minimum for `f`, `y` is a minimum for `g`, and `op` is a monotone
  binary operation, then `(x, y)` is a minimum for `uncurry (bicompl op f g)`. From this point
  of view, `is**.bicomp` is a composition
* It would be nice to have a tactic that specializes `comp_(anti)mono` or `bicomp_mono`
  based on a proof of monotonicity of a given (binary) function. The tactic should maintain a `meta`
  list of known (anti)monotone (binary) functions with their names, as well as a list of special
  types of filters, and define the missing lemmas once one of these two lists grows.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

open Set Filter Relator

section Preorder

variable [Preorder β] [Preorder γ]
variable (f : α → β) (s : Set α) (l : Filter α) (a : α)

/-! ### Definitions -/


/-- `IsMinFilter f l a` means that `f a ≤ f x` for all `x` in some `l`-neighborhood of `a` -/
def IsMinFilter : Prop :=
  ∀ᶠ x in l, f a ≤ f x

/-- `is_maxFilter f l a` means that `f x ≤ f a` for all `x` in some `l`-neighborhood of `a` -/
def IsMaxFilter : Prop :=
  ∀ᶠ x in l, f x ≤ f a

/-- `IsExtrFilter f l a` means `IsMinFilter f l a` or `IsMaxFilter f l a` -/
def IsExtrFilter : Prop :=
  IsMinFilter f l a ∨ IsMaxFilter f l a

/-- `IsMinOn f s a` means that `f a ≤ f x` for all `x ∈ s`. Note that we do not assume `a ∈ s`. -/
def IsMinOn :=
  IsMinFilter f (𝓟 s) a

/-- `IsMaxOn f s a` means that `f x ≤ f a` for all `x ∈ s`. Note that we do not assume `a ∈ s`. -/
def IsMaxOn :=
  IsMaxFilter f (𝓟 s) a

/-- `IsExtrOn f s a` means `IsMinOn f s a` or `IsMaxOn f s a` -/
def IsExtrOn : Prop :=
  IsExtrFilter f (𝓟 s) a

variable {f s a l} {t : Set α} {l' : Filter α}

theorem IsExtrOn.elim {p : Prop} : IsExtrOn f s a → (IsMinOn f s a → p) → (IsMaxOn f s a → p) → p :=
  Or.elim

theorem isMinOn_iff : IsMinOn f s a ↔ ∀ x ∈ s, f a ≤ f x :=
  Iff.rfl

theorem isMaxOn_iff : IsMaxOn f s a ↔ ∀ x ∈ s, f x ≤ f a :=
  Iff.rfl

theorem isMinOn_univ_iff : IsMinOn f univ a ↔ ∀ x, f a ≤ f x :=
  univ_subset_iff.trans eq_univ_iff_forall

theorem isMaxOn_univ_iff : IsMaxOn f univ a ↔ ∀ x, f x ≤ f a :=
  univ_subset_iff.trans eq_univ_iff_forall

theorem IsMinOn.bddBelow (h : IsMinOn f s a) :
    BddBelow (f '' s) :=
  ⟨f a, by simpa [mem_lowerBounds] using h⟩

theorem IsMinOn.isGLB (ha : a ∈ s) (hfsa : IsMinOn f s a) :
    IsGLB {f x | x ∈ s} (f a) := by
  rw [isGLB_iff_le_iff]
  intro b
  simp only [mem_lowerBounds, mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact ⟨fun hba x hx ↦ le_trans hba (hfsa hx), fun hb ↦ hb a ha⟩

theorem IsMaxOn.isLUB (ha : a ∈ s) (hfsa : IsMaxOn f s a) :
    IsLUB {f x | x ∈ s} (f a) :=
  IsMinOn.isGLB (α := αᵒᵈ) (β := βᵒᵈ) ha hfsa

theorem IsMaxOn.bddAbove (h : IsMaxOn f s a) :
    BddAbove (f '' s) :=
  ⟨f a, by simpa [mem_upperBounds] using h⟩

theorem IsMinFilter.tendsto_principal_Ici (h : IsMinFilter f l a) : Tendsto f l (𝓟 <| Ici (f a)) :=
  tendsto_principal.2 h

theorem IsMaxFilter.tendsto_principal_Iic (h : IsMaxFilter f l a) : Tendsto f l (𝓟 <| Iic (f a)) :=
  tendsto_principal.2 h

/-! ### Conversion to `IsExtr*` -/


theorem IsMinFilter.isExtr : IsMinFilter f l a → IsExtrFilter f l a :=
  Or.inl

theorem IsMaxFilter.isExtr : IsMaxFilter f l a → IsExtrFilter f l a :=
  Or.inr

theorem IsMinOn.isExtr (h : IsMinOn f s a) : IsExtrOn f s a :=
  IsMinFilter.isExtr h

theorem IsMaxOn.isExtr (h : IsMaxOn f s a) : IsExtrOn f s a :=
  IsMaxFilter.isExtr h

/-! ### Constant function -/


theorem isMinFilter_const {b : β} : IsMinFilter (fun _ => b) l a :=
  univ_mem' fun _ => le_rfl

theorem isMaxFilter_const {b : β} : IsMaxFilter (fun _ => b) l a :=
  univ_mem' fun _ => le_rfl

theorem isExtrFilter_const {b : β} : IsExtrFilter (fun _ => b) l a :=
  isMinFilter_const.isExtr

theorem isMinOn_const {b : β} : IsMinOn (fun _ => b) s a :=
  isMinFilter_const

theorem isMaxOn_const {b : β} : IsMaxOn (fun _ => b) s a :=
  isMaxFilter_const

theorem isExtrOn_const {b : β} : IsExtrOn (fun _ => b) s a :=
  isExtrFilter_const

/-- If `f` has a minimum and a maximum both given by `f a` along the filter `l`, then it is
eventually equal to `f a` along the filter. -/
lemma eventuallyEq_of_isMinFilter_of_isMaxFilter {β : Type*} [PartialOrder β] {f : α → β}
    (h₁ : IsMinFilter f l a) (h₂ : IsMaxFilter f l a) : f =ᶠ[l] (fun _ ↦ f a) := by
  filter_upwards [h₁, h₂] using by grind

/-! ### Order dual -/


open OrderDual (toDual)

theorem isMinFilter_dual_iff : IsMinFilter (toDual ∘ f) l a ↔ IsMaxFilter f l a :=
  Iff.rfl

theorem isMaxFilter_dual_iff : IsMaxFilter (toDual ∘ f) l a ↔ IsMinFilter f l a :=
  Iff.rfl

theorem isExtrFilter_dual_iff : IsExtrFilter (toDual ∘ f) l a ↔ IsExtrFilter f l a :=
  or_comm

alias ⟨IsMinFilter.undual, IsMaxFilter.dual⟩ := isMinFilter_dual_iff

alias ⟨IsMaxFilter.undual, IsMinFilter.dual⟩ := isMaxFilter_dual_iff

alias ⟨IsExtrFilter.undual, IsExtrFilter.dual⟩ := isExtrFilter_dual_iff

theorem isMinOn_dual_iff : IsMinOn (toDual ∘ f) s a ↔ IsMaxOn f s a :=
  Iff.rfl

theorem isMaxOn_dual_iff : IsMaxOn (toDual ∘ f) s a ↔ IsMinOn f s a :=
  Iff.rfl

theorem isExtrOn_dual_iff : IsExtrOn (toDual ∘ f) s a ↔ IsExtrOn f s a :=
  or_comm

alias ⟨IsMinOn.undual, IsMaxOn.dual⟩ := isMinOn_dual_iff

alias ⟨IsMaxOn.undual, IsMinOn.dual⟩ := isMaxOn_dual_iff

alias ⟨IsExtrOn.undual, IsExtrOn.dual⟩ := isExtrOn_dual_iff

/-! ### Operations on the filter/set -/


theorem IsMinFilter.filter_mono (h : IsMinFilter f l a) (hl : l' ≤ l) : IsMinFilter f l' a :=
  hl h

theorem IsMaxFilter.filter_mono (h : IsMaxFilter f l a) (hl : l' ≤ l) : IsMaxFilter f l' a :=
  hl h

theorem IsExtrFilter.filter_mono (h : IsExtrFilter f l a) (hl : l' ≤ l) : IsExtrFilter f l' a :=
  h.elim (fun h => (h.filter_mono hl).isExtr) fun h => (h.filter_mono hl).isExtr

theorem IsMinFilter.filter_inf (h : IsMinFilter f l a) (l') : IsMinFilter f (l ⊓ l') a :=
  h.filter_mono inf_le_left

theorem IsMaxFilter.filter_inf (h : IsMaxFilter f l a) (l') : IsMaxFilter f (l ⊓ l') a :=
  h.filter_mono inf_le_left

theorem IsExtrFilter.filter_inf (h : IsExtrFilter f l a) (l') : IsExtrFilter f (l ⊓ l') a :=
  h.filter_mono inf_le_left

theorem IsMinOn.on_subset (hf : IsMinOn f t a) (h : s ⊆ t) : IsMinOn f s a :=
  hf.filter_mono <| principal_mono.2 h

theorem IsMaxOn.on_subset (hf : IsMaxOn f t a) (h : s ⊆ t) : IsMaxOn f s a :=
  hf.filter_mono <| principal_mono.2 h

theorem IsExtrOn.on_subset (hf : IsExtrOn f t a) (h : s ⊆ t) : IsExtrOn f s a :=
  hf.filter_mono <| principal_mono.2 h

theorem IsMinOn.inter (hf : IsMinOn f s a) (t) : IsMinOn f (s ∩ t) a :=
  hf.on_subset inter_subset_left

theorem IsMaxOn.inter (hf : IsMaxOn f s a) (t) : IsMaxOn f (s ∩ t) a :=
  hf.on_subset inter_subset_left

theorem IsExtrOn.inter (hf : IsExtrOn f s a) (t) : IsExtrOn f (s ∩ t) a :=
  hf.on_subset inter_subset_left

/-! ### Composition with (anti)monotone functions -/


theorem IsMinFilter.comp_mono (hf : IsMinFilter f l a) {g : β → γ} (hg : Monotone g) :
    IsMinFilter (g ∘ f) l a :=
  mem_of_superset hf fun _x hx => hg hx

theorem IsMaxFilter.comp_mono (hf : IsMaxFilter f l a) {g : β → γ} (hg : Monotone g) :
    IsMaxFilter (g ∘ f) l a :=
  mem_of_superset hf fun _x hx => hg hx

theorem IsExtrFilter.comp_mono (hf : IsExtrFilter f l a) {g : β → γ} (hg : Monotone g) :
    IsExtrFilter (g ∘ f) l a :=
  hf.elim (fun hf => (hf.comp_mono hg).isExtr) fun hf => (hf.comp_mono hg).isExtr

theorem IsMinFilter.comp_antitone (hf : IsMinFilter f l a) {g : β → γ} (hg : Antitone g) :
    IsMaxFilter (g ∘ f) l a :=
  hf.dual.comp_mono fun _ _ h => hg h

theorem IsMaxFilter.comp_antitone (hf : IsMaxFilter f l a) {g : β → γ} (hg : Antitone g) :
    IsMinFilter (g ∘ f) l a :=
  hf.dual.comp_mono fun _ _ h => hg h

theorem IsExtrFilter.comp_antitone (hf : IsExtrFilter f l a) {g : β → γ} (hg : Antitone g) :
    IsExtrFilter (g ∘ f) l a :=
  hf.dual.comp_mono fun _ _ h => hg h

theorem IsMinOn.comp_mono (hf : IsMinOn f s a) {g : β → γ} (hg : Monotone g) :
    IsMinOn (g ∘ f) s a :=
  IsMinFilter.comp_mono hf hg

theorem IsMaxOn.comp_mono (hf : IsMaxOn f s a) {g : β → γ} (hg : Monotone g) :
    IsMaxOn (g ∘ f) s a :=
  IsMaxFilter.comp_mono hf hg

theorem IsExtrOn.comp_mono (hf : IsExtrOn f s a) {g : β → γ} (hg : Monotone g) :
    IsExtrOn (g ∘ f) s a :=
  IsExtrFilter.comp_mono hf hg

theorem IsMinOn.comp_antitone (hf : IsMinOn f s a) {g : β → γ} (hg : Antitone g) :
    IsMaxOn (g ∘ f) s a :=
  IsMinFilter.comp_antitone hf hg

theorem IsMaxOn.comp_antitone (hf : IsMaxOn f s a) {g : β → γ} (hg : Antitone g) :
    IsMinOn (g ∘ f) s a :=
  IsMaxFilter.comp_antitone hf hg

theorem IsExtrOn.comp_antitone (hf : IsExtrOn f s a) {g : β → γ} (hg : Antitone g) :
    IsExtrOn (g ∘ f) s a :=
  IsExtrFilter.comp_antitone hf hg

theorem IsMinFilter.bicomp_mono [Preorder δ] {op : β → γ → δ}
    (hop : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) op op) (hf : IsMinFilter f l a) {g : α → γ}
    (hg : IsMinFilter g l a) : IsMinFilter (fun x => op (f x) (g x)) l a :=
  mem_of_superset (inter_mem hf hg) fun _x ⟨hfx, hgx⟩ => hop hfx hgx

theorem IsMaxFilter.bicomp_mono [Preorder δ] {op : β → γ → δ}
    (hop : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) op op) (hf : IsMaxFilter f l a) {g : α → γ}
    (hg : IsMaxFilter g l a) : IsMaxFilter (fun x => op (f x) (g x)) l a :=
  mem_of_superset (inter_mem hf hg) fun _x ⟨hfx, hgx⟩ => hop hfx hgx

-- No `Extr` version because we need `hf` and `hg` to be of the same kind
theorem IsMinOn.bicomp_mono [Preorder δ] {op : β → γ → δ}
    (hop : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) op op) (hf : IsMinOn f s a) {g : α → γ}
    (hg : IsMinOn g s a) : IsMinOn (fun x => op (f x) (g x)) s a :=
  IsMinFilter.bicomp_mono hop hf hg

theorem IsMaxOn.bicomp_mono [Preorder δ] {op : β → γ → δ}
    (hop : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) op op) (hf : IsMaxOn f s a) {g : α → γ}
    (hg : IsMaxOn g s a) : IsMaxOn (fun x => op (f x) (g x)) s a :=
  IsMaxFilter.bicomp_mono hop hf hg

/-! ### Composition with `Tendsto` -/


theorem IsMinFilter.comp_tendsto {g : δ → α} {l' : Filter δ} {b : δ} (hf : IsMinFilter f l (g b))
    (hg : Tendsto g l' l) : IsMinFilter (f ∘ g) l' b :=
  hg hf

theorem IsMaxFilter.comp_tendsto {g : δ → α} {l' : Filter δ} {b : δ} (hf : IsMaxFilter f l (g b))
    (hg : Tendsto g l' l) : IsMaxFilter (f ∘ g) l' b :=
  hg hf

theorem IsExtrFilter.comp_tendsto {g : δ → α} {l' : Filter δ} {b : δ} (hf : IsExtrFilter f l (g b))
    (hg : Tendsto g l' l) : IsExtrFilter (f ∘ g) l' b :=
  hf.elim (fun hf => (hf.comp_tendsto hg).isExtr) fun hf => (hf.comp_tendsto hg).isExtr

theorem IsMinOn.on_preimage (g : δ → α) {b : δ} (hf : IsMinOn f s (g b)) :
    IsMinOn (f ∘ g) (g ⁻¹' s) b :=
  hf.comp_tendsto (tendsto_principal_principal.mpr <| Subset.refl _)

theorem IsMaxOn.on_preimage (g : δ → α) {b : δ} (hf : IsMaxOn f s (g b)) :
    IsMaxOn (f ∘ g) (g ⁻¹' s) b :=
  hf.comp_tendsto (tendsto_principal_principal.mpr <| Subset.refl _)

theorem IsExtrOn.on_preimage (g : δ → α) {b : δ} (hf : IsExtrOn f s (g b)) :
    IsExtrOn (f ∘ g) (g ⁻¹' s) b :=
  hf.elim (fun hf => (hf.on_preimage g).isExtr) fun hf => (hf.on_preimage g).isExtr

theorem IsMinOn.comp_mapsTo {t : Set δ} {g : δ → α} {b : δ} (hf : IsMinOn f s a) (hg : MapsTo g t s)
    (ha : g b = a) : IsMinOn (f ∘ g) t b := fun y hy => by
  simpa only [ha, (· ∘ ·)] using hf (hg hy)

theorem IsMaxOn.comp_mapsTo {t : Set δ} {g : δ → α} {b : δ} (hf : IsMaxOn f s a) (hg : MapsTo g t s)
    (ha : g b = a) : IsMaxOn (f ∘ g) t b :=
  hf.dual.comp_mapsTo hg ha

theorem IsExtrOn.comp_mapsTo {t : Set δ} {g : δ → α} {b : δ} (hf : IsExtrOn f s a)
    (hg : MapsTo g t s) (ha : g b = a) : IsExtrOn (f ∘ g) t b :=
  hf.elim (fun h => Or.inl <| h.comp_mapsTo hg ha) fun h => Or.inr <| h.comp_mapsTo hg ha

end Preorder

/-! ### Pointwise addition -/


section OrderedAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
  {f g : α → β} {a : α} {s : Set α} {l : Filter α}

theorem IsMinFilter.add (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) :
    IsMinFilter (fun x => f x + g x) l a :=
  show IsMinFilter (fun x => f x + g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => add_le_add hx hy) hg

theorem IsMaxFilter.add (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) :
    IsMaxFilter (fun x => f x + g x) l a :=
  show IsMaxFilter (fun x => f x + g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => add_le_add hx hy) hg

theorem IsMinOn.add (hf : IsMinOn f s a) (hg : IsMinOn g s a) : IsMinOn (fun x => f x + g x) s a :=
  IsMinFilter.add hf hg

theorem IsMaxOn.add (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) : IsMaxOn (fun x => f x + g x) s a :=
  IsMaxFilter.add hf hg

end OrderedAddCommMonoid

/-! ### Pointwise negation and subtraction -/


section OrderedAddCommGroup

variable [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  {f g : α → β} {a : α} {s : Set α} {l : Filter α}

theorem IsMinFilter.neg (hf : IsMinFilter f l a) : IsMaxFilter (fun x => -f x) l a :=
  hf.comp_antitone fun _x _y hx => neg_le_neg hx

theorem IsMaxFilter.neg (hf : IsMaxFilter f l a) : IsMinFilter (fun x => -f x) l a :=
  hf.comp_antitone fun _x _y hx => neg_le_neg hx

theorem IsExtrFilter.neg (hf : IsExtrFilter f l a) : IsExtrFilter (fun x => -f x) l a :=
  hf.elim (fun hf => hf.neg.isExtr) fun hf => hf.neg.isExtr

theorem IsMinOn.neg (hf : IsMinOn f s a) : IsMaxOn (fun x => -f x) s a :=
  hf.comp_antitone fun _x _y hx => neg_le_neg hx

theorem IsMaxOn.neg (hf : IsMaxOn f s a) : IsMinOn (fun x => -f x) s a :=
  hf.comp_antitone fun _x _y hx => neg_le_neg hx

theorem IsExtrOn.neg (hf : IsExtrOn f s a) : IsExtrOn (fun x => -f x) s a :=
  hf.elim (fun hf => hf.neg.isExtr) fun hf => hf.neg.isExtr

theorem IsMinFilter.sub (hf : IsMinFilter f l a) (hg : IsMaxFilter g l a) :
    IsMinFilter (fun x => f x - g x) l a := by simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem IsMaxFilter.sub (hf : IsMaxFilter f l a) (hg : IsMinFilter g l a) :
    IsMaxFilter (fun x => f x - g x) l a := by simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem IsMinOn.sub (hf : IsMinOn f s a) (hg : IsMaxOn g s a) :
    IsMinOn (fun x => f x - g x) s a := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem IsMaxOn.sub (hf : IsMaxOn f s a) (hg : IsMinOn g s a) :
    IsMaxOn (fun x => f x - g x) s a := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

end OrderedAddCommGroup

/-! ### Pointwise `sup`/`inf` -/


section SemilatticeSup

variable [SemilatticeSup β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

theorem IsMinFilter.sup (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) :
    IsMinFilter (fun x => f x ⊔ g x) l a :=
  show IsMinFilter (fun x => f x ⊔ g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => sup_le_sup hx hy) hg

theorem IsMaxFilter.sup (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) :
    IsMaxFilter (fun x => f x ⊔ g x) l a :=
  show IsMaxFilter (fun x => f x ⊔ g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => sup_le_sup hx hy) hg

theorem IsMinOn.sup (hf : IsMinOn f s a) (hg : IsMinOn g s a) : IsMinOn (fun x => f x ⊔ g x) s a :=
  IsMinFilter.sup hf hg

theorem IsMaxOn.sup (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) : IsMaxOn (fun x => f x ⊔ g x) s a :=
  IsMaxFilter.sup hf hg

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

theorem IsMinFilter.inf (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) :
    IsMinFilter (fun x => f x ⊓ g x) l a :=
  show IsMinFilter (fun x => f x ⊓ g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => inf_le_inf hx hy) hg

theorem IsMaxFilter.inf (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) :
    IsMaxFilter (fun x => f x ⊓ g x) l a :=
  show IsMaxFilter (fun x => f x ⊓ g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => inf_le_inf hx hy) hg

theorem IsMinOn.inf (hf : IsMinOn f s a) (hg : IsMinOn g s a) : IsMinOn (fun x => f x ⊓ g x) s a :=
  IsMinFilter.inf hf hg

theorem IsMaxOn.inf (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) : IsMaxOn (fun x => f x ⊓ g x) s a :=
  IsMaxFilter.inf hf hg

end SemilatticeInf

/-! ### Pointwise `min`/`max` -/


section LinearOrder

variable [LinearOrder β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

theorem IsMinFilter.min (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) :
    IsMinFilter (fun x => min (f x) (g x)) l a :=
  show IsMinFilter (fun x => Min.min (f x) (g x)) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => min_le_min hx hy) hg

theorem IsMaxFilter.min (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) :
    IsMaxFilter (fun x => min (f x) (g x)) l a :=
  show IsMaxFilter (fun x => Min.min (f x) (g x)) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => min_le_min hx hy) hg

theorem IsMinOn.min (hf : IsMinOn f s a) (hg : IsMinOn g s a) :
    IsMinOn (fun x => min (f x) (g x)) s a :=
  IsMinFilter.min hf hg

theorem IsMaxOn.min (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) :
    IsMaxOn (fun x => min (f x) (g x)) s a :=
  IsMaxFilter.min hf hg

theorem IsMinFilter.max (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) :
    IsMinFilter (fun x => max (f x) (g x)) l a :=
  show IsMinFilter (fun x => Max.max (f x) (g x)) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => max_le_max hx hy) hg

theorem IsMaxFilter.max (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) :
    IsMaxFilter (fun x => max (f x) (g x)) l a :=
  show IsMaxFilter (fun x => Max.max (f x) (g x)) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => max_le_max hx hy) hg

theorem IsMinOn.max (hf : IsMinOn f s a) (hg : IsMinOn g s a) :
    IsMinOn (fun x => max (f x) (g x)) s a :=
  IsMinFilter.max hf hg

theorem IsMaxOn.max (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) :
    IsMaxOn (fun x => max (f x) (g x)) s a :=
  IsMaxFilter.max hf hg

/-! ### Extrema from monotonicity and antitonicity -/

variable {β : Type*} [LinearOrder α] [Preorder β] {a b c : α} {f : α → β}

/-- If `f` is monotone on `Ioc a b` and antitone on `Ico b c`, then the maximum of `f` on
`Ioo a c` is attained at `b`. -/
lemma isMaxOn_Ioo_of_mono_anti (h₀ : MonotoneOn f (Ioc a b)) (h₁ : AntitoneOn f (Ico b c)) :
    IsMaxOn f (Ioo a c) b := by
  intro x hx
  by_cases! g₀ : x ≤ b
  · exact h₀ ⟨hx.1, g₀⟩ (right_mem_Ioc.2 (g₀.trans_lt' hx.1)) g₀
  · refine h₁ (left_mem_Ico.2 (g₀.trans hx.2)) ⟨g₀.le, hx.2⟩ g₀.le

/-- If `f` is antitone on `Ioc a b` and monotone on `Ico b c`, then the minimum of `f` on
`Ioo a c` is attained at `b`. -/
lemma isMinOn_Ioo_of_anti_mono (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Ico b c)) :
    IsMinOn f (Ioo a c) b :=
  isMaxOn_Ioo_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `Icc a b` and antitone on `Ico b c`, then the maximum of `f` on
`Ico a c` is attained at `b`. -/
lemma isMaxOn_Ico_of_mono_anti (h₀ : MonotoneOn f (Icc a b)) (h₁ : AntitoneOn f (Ico b c)) :
    IsMaxOn f (Ico a c) b := by
  intro x hx
  by_cases! g₀ : x ≤ b
  · exact h₀ ⟨hx.1, g₀⟩ (right_mem_Icc.2 (hx.1.trans g₀)) g₀
  · exact h₁ (left_mem_Ico.2 (g₀.trans hx.2)) ⟨g₀.le, hx.2⟩ g₀.le

/-- If `f` is antitone on `Icc a b` and monotone on `Ico b c`, then the minimum of `f` on
`Ico a c` is attained at `b`. -/
lemma isMinOn_Ico_of_anti_mono (h₀ : AntitoneOn f (Icc a b)) (h₁ : MonotoneOn f (Ico b c)) :
    IsMinOn f (Ico a c) b :=
  isMaxOn_Ico_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `Ioc a b` and antitone on `Icc b c`, then the maximum of `f` on
`Ioc a c` is attained at `b`. -/
lemma isMaxOn_Ioc_of_mono_anti (h₀ : MonotoneOn f (Ioc a b)) (h₁ : AntitoneOn f (Icc b c)) :
    IsMaxOn f (Ioc a c) b := by
  intro x hx
  by_cases! g₀ : x ≤ b
  · exact h₀ ⟨hx.1, g₀⟩ (right_mem_Ioc.2 (g₀.trans_lt' hx.1)) g₀
  · exact h₁ (left_mem_Icc.2 (g₀.le.trans hx.2)) ⟨g₀.le, hx.2⟩ g₀.le

/-- If `f` is antitone on `Ioc a b` and monotone on `Icc b c`, then the minimum of `f` on
`Ioc a c` is attained at `b`. -/
lemma isMinOn_Ioc_of_anti_mono (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Icc b c)) :
    IsMinOn f (Ioc a c) b :=
  isMaxOn_Ioc_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `Icc a b` and antitone on `Icc b c`, then the maximum of `f` on
`Icc a c` is attained at `b`. -/
lemma isMaxOn_Icc_of_mono_anti (h₀ : MonotoneOn f (Icc a b)) (h₁ : AntitoneOn f (Icc b c)) :
    IsMaxOn f (Icc a c) b := by
  intro x hx
  by_cases! g₀ : x ≤ b
  · exact h₀ ⟨hx.1, g₀⟩ (right_mem_Icc.2 (hx.1.trans g₀)) g₀
  · exact h₁ (left_mem_Icc.2 (g₀.le.trans hx.2)) ⟨g₀.le, hx.2⟩ g₀.le

/-- If `f` is antitone on `Icc a b` and monotone on `Icc b c`, then the minimum of `f` on
`Icc a c` is attained at `b`. -/
lemma isMinOn_Icc_of_anti_mono (h₀ : AntitoneOn f (Icc a b)) (h₁ : MonotoneOn f (Icc b c)) :
    IsMinOn f (Icc a c) b :=
  isMaxOn_Icc_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `Ioc a b` and antitone on `Ici b`, then the maximum of `f` on `Ioi a` is
attained at `b`. -/
lemma isMaxOn_Ioi_of_mono_anti (h₀ : MonotoneOn f (Ioc a b)) (h₁ : AntitoneOn f (Ici b)) :
    IsMaxOn f (Ioi a) b := by
  intro x hx
  by_cases! g₀ : x ≤ b
  · exact h₀ ⟨hx, g₀⟩ (right_mem_Ioc.2 (g₀.trans_lt' hx)) g₀
  · exact h₁ self_mem_Ici g₀.le g₀.le

/-- If `f` is antitone on `Ioc a b` and monotone on `Ici b`, then the minimum of `f` on `Ioi a` is
attained at `b`. -/
lemma isMinOn_Ioi_of_anti_mono (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Ici b)) :
    IsMinOn f (Ioi a) b :=
  isMaxOn_Ioi_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `Icc a b` and antitone on `Ici b`, then the maximum of `f` on `Ici a` is
attained at `b`. -/
lemma isMaxOn_Ici_of_mono_anti (h₀ : MonotoneOn f (Icc a b)) (h₁ : AntitoneOn f (Ici b)) :
    IsMaxOn f (Ici a) b := by
  intro x hx
  by_cases! g₀ : x ≤ b
  · exact h₀ ⟨hx, g₀⟩ (right_mem_Icc.2 (hx.trans g₀)) g₀
  · exact h₁ self_mem_Ici g₀.le g₀.le

/-- If `f` is antitone on `Icc a b` and monotone on `Ici b`, then the minimum of `f` on `Ici a` is
attained at `b`. -/
lemma isMinOn_Ici_of_anti_mono (h₀ : AntitoneOn f (Icc a b)) (h₁ : MonotoneOn f (Ici b)) :
    IsMinOn f (Ici a) b :=
  isMaxOn_Ici_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `Iic b` and antitone on `Ico b a`, then the maximum of `f` on `Iio a`
is attained at `b`. -/
lemma isMaxOn_Iio_of_mono_anti (h₀ : MonotoneOn f (Iic b)) (h₁ : AntitoneOn f (Ico b a)) :
    IsMaxOn f (Iio a) b := by
  intro x hx
  by_cases! g₀ : x ≤ b
  · exact h₀ g₀ self_mem_Iic g₀
  · exact h₁ (left_mem_Ico.2 (g₀.trans hx)) ⟨g₀.le, hx⟩ g₀.le

/-- If `f` is antitone on `Iic b` and monotone on `Ico b a`, then the minimum of `f` on `Iio a`
is attained at `b`. -/
lemma isMinOn_Iio_of_anti_mono (h₀ : AntitoneOn f (Iic b)) (h₁ : MonotoneOn f (Ico b a)) :
    IsMinOn f (Iio a) b :=
  isMaxOn_Iio_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `Iic b` and antitone on `Icc b a`, then the maximum of `f` on `Iic a`
is attained at `b`. -/
lemma isMaxOn_Iic_of_mono_anti (h₀ : MonotoneOn f (Iic b)) (h₁ : AntitoneOn f (Icc b a)) :
    IsMaxOn f (Iic a) b := by
  intro x hx
  by_cases! g₀ : x ≤ b
  · exact h₀ g₀ self_mem_Iic g₀
  · exact h₁ (left_mem_Icc.2 (g₀.le.trans hx)) ⟨g₀.le, hx⟩ g₀.le

/-- If `f` is antitone on `Iic b` and monotone on `Icc b a`, then the minimum of `f` on `Iic a`
is attained at `b`. -/
lemma isMinOn_Iic_of_anti_mono (h₀ : AntitoneOn f (Iic b)) (h₁ : MonotoneOn f (Icc b a)) :
    IsMinOn f (Iic a) b :=
  isMaxOn_Iic_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `Iic b` and antitone on `Ici b`, then the maximum of `f` is attained
at `b`. -/
lemma isMaxOn_univ_of_mono_anti (h₀ : MonotoneOn f (Iic b)) (h₁ : AntitoneOn f (Ici b)) :
    IsMaxOn f univ b :=
  fun x _ => by rcases le_total x b <;> aesop

/-- If `f` is antitone on `Iic b` and monotone on `Ici b`, then the minimum of `f` is attained
at `b`. -/
lemma isMinOn_univ_of_anti_mono (h₀ : AntitoneOn f (Iic b)) (h₁ : MonotoneOn f (Ici b)) :
    IsMinOn f univ b :=
  isMaxOn_univ_of_mono_anti (β := βᵒᵈ) h₀ h₁

end LinearOrder

section Eventually

/-! ### Relation with `eventually` comparisons of two functions -/


theorem Filter.EventuallyLE.isMaxFilter {α β : Type*} [Preorder β] {f g : α → β} {a : α}
    {l : Filter α} (hle : g ≤ᶠ[l] f) (hfga : f a = g a) (h : IsMaxFilter f l a) :
    IsMaxFilter g l a := by
  refine hle.mp (h.mono fun x hf hgf => ?_)
  rw [← hfga]
  exact le_trans hgf hf

theorem IsMaxFilter.congr {α β : Type*} [Preorder β] {f g : α → β} {a : α} {l : Filter α}
    (h : IsMaxFilter f l a) (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsMaxFilter g l a :=
  heq.symm.le.isMaxFilter hfga h

theorem Filter.EventuallyEq.isMaxFilter_iff {α β : Type*} [Preorder β] {f g : α → β} {a : α}
    {l : Filter α} (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsMaxFilter f l a ↔ IsMaxFilter g l a :=
  ⟨fun h => h.congr heq hfga, fun h => h.congr heq.symm hfga.symm⟩

theorem Filter.EventuallyLE.isMinFilter {α β : Type*} [Preorder β] {f g : α → β} {a : α}
    {l : Filter α} (hle : f ≤ᶠ[l] g) (hfga : f a = g a) (h : IsMinFilter f l a) :
    IsMinFilter g l a :=
  @Filter.EventuallyLE.isMaxFilter _ βᵒᵈ _ _ _ _ _ hle hfga h

theorem IsMinFilter.congr {α β : Type*} [Preorder β] {f g : α → β} {a : α} {l : Filter α}
    (h : IsMinFilter f l a) (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsMinFilter g l a :=
  heq.le.isMinFilter hfga h

theorem Filter.EventuallyEq.isMinFilter_iff {α β : Type*} [Preorder β] {f g : α → β} {a : α}
    {l : Filter α} (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsMinFilter f l a ↔ IsMinFilter g l a :=
  ⟨fun h => h.congr heq hfga, fun h => h.congr heq.symm hfga.symm⟩

theorem IsExtrFilter.congr {α β : Type*} [Preorder β] {f g : α → β} {a : α} {l : Filter α}
    (h : IsExtrFilter f l a) (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsExtrFilter g l a := by
  rw [IsExtrFilter] at *
  rwa [← heq.isMaxFilter_iff hfga, ← heq.isMinFilter_iff hfga]

theorem Filter.EventuallyEq.isExtrFilter_iff {α β : Type*} [Preorder β] {f g : α → β} {a : α}
    {l : Filter α} (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsExtrFilter f l a ↔ IsExtrFilter g l a :=
  ⟨fun h => h.congr heq hfga, fun h => h.congr heq.symm hfga.symm⟩

end Eventually

/-! ### `isMaxOn`/`isMinOn` imply `ciSup`/`ciInf` -/


section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {f : β → α} {s : Set β} {x₀ : β}

theorem IsMaxOn.iSup_eq (hx₀ : x₀ ∈ s) (h : IsMaxOn f s x₀) : ⨆ x : s, f x = f x₀ :=
  haveI : Nonempty s := ⟨⟨x₀, hx₀⟩⟩
  ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun x => h x.2) fun _w hw => ⟨⟨x₀, hx₀⟩, hw⟩

theorem IsMinOn.iInf_eq (hx₀ : x₀ ∈ s) (h : IsMinOn f s x₀) : ⨅ x : s, f x = f x₀ :=
  @IsMaxOn.iSup_eq αᵒᵈ β _ _ _ _ hx₀ h

end ConditionallyCompleteLinearOrder

/-! ### Value of `Finset.sup` / `Finset.inf` -/

section SemilatticeSup

variable [SemilatticeSup β] [OrderBot β] {D : α → β} {s : Finset α}

theorem sup_eq_of_isMaxOn {a : α} (hmem : a ∈ s) (hmax : IsMaxOn D s a) : s.sup D = D a :=
  (Finset.sup_le hmax).antisymm (Finset.le_sup hmem)

theorem sup_eq_of_max [Nonempty α] {b : β} (hb : b ∈ Set.range D) (hmem : D.invFun b ∈ s)
    (hmax : ∀ a ∈ s, D a ≤ b) : s.sup D = b := by
  obtain ⟨a, rfl⟩ := hb
  rw [← Function.apply_invFun_apply (f := D)]
  apply sup_eq_of_isMaxOn hmem; intro
  rw [Function.apply_invFun_apply (f := D)]; apply hmax

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf β] [OrderTop β] {D : α → β} {s : Finset α}

theorem inf_eq_of_isMinOn {a : α} (hmem : a ∈ s) (hmax : IsMinOn D s a) : s.inf D = D a :=
  sup_eq_of_isMaxOn (α := αᵒᵈ) (β := βᵒᵈ) hmem hmax.dual

theorem inf_eq_of_min [Nonempty α] {b : β} (hb : b ∈ Set.range D) (hmem : D.invFun b ∈ s)
    (hmin : ∀ a ∈ s, b ≤ D a) : s.inf D = b :=
  sup_eq_of_max (α := αᵒᵈ) (β := βᵒᵈ) hb hmem hmin

end SemilatticeInf
