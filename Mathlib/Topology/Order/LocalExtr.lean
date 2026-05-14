/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.Extr
public import Mathlib.Topology.Defs.Filter
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Order.Filter.Map
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.NhdsWithin

/-!
# Local extrema of functions on topological spaces

## Main definitions

This file defines special versions of `Is*Filter f a l`, `*=Min/Max/Extr`, from
`Mathlib/Order/Filter/Extr.lean` for two kinds of filters: `nhdsWithin` and `nhds`.
These versions are called `IsLocal*On` and `IsLocal*`, respectively.

## Main statements

Many lemmas in this file restate those from `Mathlib/Order/Filter/Extr.lean`, and you can find
detailed documentation there. These convenience lemmas are provided only to make the dot notation
return propositions of expected types, not just `Is*Filter`.

Here is the list of statements specific to these two types of filters:

* `IsLocal*.on`, `IsLocal*On.on_subset`: restrict to a subset;
* `IsLocal*On.inter` : intersect the set with another one;
* `Is*On.localize` : a global extremum is a local extremum too.
* `Is[Local]*On.isLocal*` : if we have `IsLocal*On f s a` and `s ∈ 𝓝 a`, then we have
  `IsLocal* f a`.
-/

@[expose] public section


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} [TopologicalSpace α]

open Set Filter Topology

section Preorder

variable [Preorder β] [Preorder γ] (f : α → β) (s : Set α) (a : α)

/-- `IsLocalMinOn f s a` means that `f a ≤ f x` for all `x ∈ s` in some neighborhood of `a`. -/
def IsLocalMinOn :=
  IsMinFilter f (𝓝[s] a) a

/-- `IsLocalMaxOn f s a` means that `f x ≤ f a` for all `x ∈ s` in some neighborhood of `a`. -/
def IsLocalMaxOn :=
  IsMaxFilter f (𝓝[s] a) a

/-- `IsLocalExtrOn f s a` means `IsLocalMinOn f s a ∨ IsLocalMaxOn f s a`. -/
def IsLocalExtrOn :=
  IsExtrFilter f (𝓝[s] a) a

/-- `IsLocalMin f a` means that `f a ≤ f x` for all `x` in some neighborhood of `a`. -/
def IsLocalMin :=
  IsMinFilter f (𝓝 a) a

/-- `IsLocalMax f a` means that `f x ≤ f a` for all `x ∈ s` in some neighborhood of `a`. -/
def IsLocalMax :=
  IsMaxFilter f (𝓝 a) a

/-- `IsLocalExtr f s a` means `IsLocalMin f s a ∨ IsLocalMax f s a`. -/
def IsLocalExtr :=
  IsExtrFilter f (𝓝 a) a

variable {f s a}

theorem IsLocalExtrOn.elim {p : Prop} :
    IsLocalExtrOn f s a → (IsLocalMinOn f s a → p) → (IsLocalMaxOn f s a → p) → p :=
  Or.elim

theorem IsLocalExtr.elim {p : Prop} :
    IsLocalExtr f a → (IsLocalMin f a → p) → (IsLocalMax f a → p) → p :=
  Or.elim

/-! ### Restriction to (sub)sets -/

theorem IsLocalMin.on (h : IsLocalMin f a) (s) : IsLocalMinOn f s a :=
  h.filter_inf _

theorem IsLocalMax.on (h : IsLocalMax f a) (s) : IsLocalMaxOn f s a :=
  h.filter_inf _

theorem IsLocalExtr.on (h : IsLocalExtr f a) (s) : IsLocalExtrOn f s a :=
  h.filter_inf _

theorem IsLocalMinOn.on_subset {t : Set α} (hf : IsLocalMinOn f t a) (h : s ⊆ t) :
    IsLocalMinOn f s a :=
  hf.filter_mono <| nhdsWithin_mono a h

theorem IsLocalMaxOn.on_subset {t : Set α} (hf : IsLocalMaxOn f t a) (h : s ⊆ t) :
    IsLocalMaxOn f s a :=
  hf.filter_mono <| nhdsWithin_mono a h

theorem IsLocalExtrOn.on_subset {t : Set α} (hf : IsLocalExtrOn f t a) (h : s ⊆ t) :
    IsLocalExtrOn f s a :=
  hf.filter_mono <| nhdsWithin_mono a h

theorem IsLocalMinOn.inter (hf : IsLocalMinOn f s a) (t) : IsLocalMinOn f (s ∩ t) a :=
  hf.on_subset inter_subset_left

theorem IsLocalMaxOn.inter (hf : IsLocalMaxOn f s a) (t) : IsLocalMaxOn f (s ∩ t) a :=
  hf.on_subset inter_subset_left

theorem IsLocalExtrOn.inter (hf : IsLocalExtrOn f s a) (t) : IsLocalExtrOn f (s ∩ t) a :=
  hf.on_subset inter_subset_left

theorem IsMinOn.localize (hf : IsMinOn f s a) : IsLocalMinOn f s a :=
  hf.filter_mono <| inf_le_right

theorem IsMaxOn.localize (hf : IsMaxOn f s a) : IsLocalMaxOn f s a :=
  hf.filter_mono <| inf_le_right

theorem IsExtrOn.localize (hf : IsExtrOn f s a) : IsLocalExtrOn f s a :=
  hf.filter_mono <| inf_le_right

theorem IsLocalMinOn.isLocalMin (hf : IsLocalMinOn f s a) (hs : s ∈ 𝓝 a) : IsLocalMin f a :=
  have : 𝓝 a ≤ 𝓟 s := le_principal_iff.2 hs
  hf.filter_mono <| le_inf le_rfl this

theorem IsLocalMaxOn.isLocalMax (hf : IsLocalMaxOn f s a) (hs : s ∈ 𝓝 a) : IsLocalMax f a :=
  have : 𝓝 a ≤ 𝓟 s := le_principal_iff.2 hs
  hf.filter_mono <| le_inf le_rfl this

theorem IsLocalExtrOn.isLocalExtr (hf : IsLocalExtrOn f s a) (hs : s ∈ 𝓝 a) : IsLocalExtr f a :=
  hf.elim (fun hf => (hf.isLocalMin hs).isExtr) fun hf => (hf.isLocalMax hs).isExtr

lemma isLocalMinOn_univ_iff : IsLocalMinOn f univ a ↔ IsLocalMin f a := by
  simp only [IsLocalMinOn, IsLocalMin, nhdsWithin_univ]

lemma isLocalMaxOn_univ_iff : IsLocalMaxOn f univ a ↔ IsLocalMax f a := by
  simp only [IsLocalMaxOn, IsLocalMax, nhdsWithin_univ]

lemma isLocalExtrOn_univ_iff : IsLocalExtrOn f univ a ↔ IsLocalExtr f a :=
  isLocalMinOn_univ_iff.or isLocalMaxOn_univ_iff

theorem IsMinOn.isLocalMin (hf : IsMinOn f s a) (hs : s ∈ 𝓝 a) : IsLocalMin f a :=
  hf.localize.isLocalMin hs

theorem IsMaxOn.isLocalMax (hf : IsMaxOn f s a) (hs : s ∈ 𝓝 a) : IsLocalMax f a :=
  hf.localize.isLocalMax hs

theorem IsExtrOn.isLocalExtr (hf : IsExtrOn f s a) (hs : s ∈ 𝓝 a) : IsLocalExtr f a :=
  hf.localize.isLocalExtr hs

theorem IsLocalMinOn.not_nhds_le_map [TopologicalSpace β] (hf : IsLocalMinOn f s a)
    [NeBot (𝓝[<] f a)] : ¬𝓝 (f a) ≤ map f (𝓝[s] a) := fun hle =>
  have : ∀ᶠ y in 𝓝[<] f a, f a ≤ y := (eventually_map.2 hf).filter_mono (inf_le_left.trans hle)
  let ⟨_y, hy⟩ := (this.and self_mem_nhdsWithin).exists
  hy.1.not_gt hy.2

set_option backward.isDefEq.respectTransparency false in
theorem IsLocalMaxOn.not_nhds_le_map [TopologicalSpace β] (hf : IsLocalMaxOn f s a)
    [NeBot (𝓝[>] f a)] : ¬𝓝 (f a) ≤ map f (𝓝[s] a) :=
  @IsLocalMinOn.not_nhds_le_map α βᵒᵈ _ _ _ _ _ ‹_› hf ‹_›

theorem IsLocalExtrOn.not_nhds_le_map [TopologicalSpace β] (hf : IsLocalExtrOn f s a)
    [NeBot (𝓝[<] f a)] [NeBot (𝓝[>] f a)] : ¬𝓝 (f a) ≤ map f (𝓝[s] a) :=
  hf.elim (fun h => h.not_nhds_le_map) fun h => h.not_nhds_le_map

/-! ### Constant -/


theorem isLocalMinOn_const {b : β} : IsLocalMinOn (fun _ => b) s a :=
  isMinFilter_const

theorem isLocalMaxOn_const {b : β} : IsLocalMaxOn (fun _ => b) s a :=
  isMaxFilter_const

theorem isLocalExtrOn_const {b : β} : IsLocalExtrOn (fun _ => b) s a :=
  isExtrFilter_const

theorem isLocalMin_const {b : β} : IsLocalMin (fun _ => b) a :=
  isMinFilter_const

theorem isLocalMax_const {b : β} : IsLocalMax (fun _ => b) a :=
  isMaxFilter_const

theorem isLocalExtr_const {b : β} : IsLocalExtr (fun _ => b) a :=
  isExtrFilter_const

/-! ### Composition with (anti)monotone functions -/

nonrec theorem IsLocalMin.comp_mono (hf : IsLocalMin f a) {g : β → γ} (hg : Monotone g) :
    IsLocalMin (g ∘ f) a :=
  hf.comp_mono hg

nonrec theorem IsLocalMax.comp_mono (hf : IsLocalMax f a) {g : β → γ} (hg : Monotone g) :
    IsLocalMax (g ∘ f) a :=
  hf.comp_mono hg

nonrec theorem IsLocalExtr.comp_mono (hf : IsLocalExtr f a) {g : β → γ} (hg : Monotone g) :
    IsLocalExtr (g ∘ f) a :=
  hf.comp_mono hg

nonrec theorem IsLocalMin.comp_antitone (hf : IsLocalMin f a) {g : β → γ} (hg : Antitone g) :
    IsLocalMax (g ∘ f) a :=
  hf.comp_antitone hg

nonrec theorem IsLocalMax.comp_antitone (hf : IsLocalMax f a) {g : β → γ} (hg : Antitone g) :
    IsLocalMin (g ∘ f) a :=
  hf.comp_antitone hg

nonrec theorem IsLocalExtr.comp_antitone (hf : IsLocalExtr f a) {g : β → γ} (hg : Antitone g) :
    IsLocalExtr (g ∘ f) a :=
  hf.comp_antitone hg

nonrec theorem IsLocalMinOn.comp_mono (hf : IsLocalMinOn f s a) {g : β → γ} (hg : Monotone g) :
    IsLocalMinOn (g ∘ f) s a :=
  hf.comp_mono hg

nonrec theorem IsLocalMaxOn.comp_mono (hf : IsLocalMaxOn f s a) {g : β → γ} (hg : Monotone g) :
    IsLocalMaxOn (g ∘ f) s a :=
  hf.comp_mono hg

nonrec theorem IsLocalExtrOn.comp_mono (hf : IsLocalExtrOn f s a) {g : β → γ} (hg : Monotone g) :
    IsLocalExtrOn (g ∘ f) s a :=
  hf.comp_mono hg

nonrec theorem IsLocalMinOn.comp_antitone (hf : IsLocalMinOn f s a) {g : β → γ} (hg : Antitone g) :
    IsLocalMaxOn (g ∘ f) s a :=
  hf.comp_antitone hg

nonrec theorem IsLocalMaxOn.comp_antitone (hf : IsLocalMaxOn f s a) {g : β → γ} (hg : Antitone g) :
    IsLocalMinOn (g ∘ f) s a :=
  hf.comp_antitone hg

nonrec theorem IsLocalExtrOn.comp_antitone (hf : IsLocalExtrOn f s a) {g : β → γ}
    (hg : Antitone g) : IsLocalExtrOn (g ∘ f) s a :=
  hf.comp_antitone hg

open scoped Relator

nonrec theorem IsLocalMin.bicomp_mono [Preorder δ] {op : β → γ → δ}
    (hop : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) op op) (hf : IsLocalMin f a) {g : α → γ}
    (hg : IsLocalMin g a) : IsLocalMin (fun x => op (f x) (g x)) a :=
  hf.bicomp_mono hop hg

nonrec theorem IsLocalMax.bicomp_mono [Preorder δ] {op : β → γ → δ}
    (hop : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) op op) (hf : IsLocalMax f a) {g : α → γ}
    (hg : IsLocalMax g a) : IsLocalMax (fun x => op (f x) (g x)) a :=
  hf.bicomp_mono hop hg

nonrec theorem IsLocalMinOn.bicomp_mono [Preorder δ] {op : β → γ → δ}
    (hop : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) op op) (hf : IsLocalMinOn f s a) {g : α → γ}
    (hg : IsLocalMinOn g s a) : IsLocalMinOn (fun x => op (f x) (g x)) s a :=
  hf.bicomp_mono hop hg

nonrec theorem IsLocalMaxOn.bicomp_mono [Preorder δ] {op : β → γ → δ}
    (hop : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) op op) (hf : IsLocalMaxOn f s a) {g : α → γ}
    (hg : IsLocalMaxOn g s a) : IsLocalMaxOn (fun x => op (f x) (g x)) s a :=
  hf.bicomp_mono hop hg

/-! ### Composition with `ContinuousAt` -/


theorem IsLocalMin.comp_continuous [TopologicalSpace δ] {g : δ → α} {b : δ}
    (hf : IsLocalMin f (g b)) (hg : ContinuousAt g b) : IsLocalMin (f ∘ g) b :=
  hg hf

theorem IsLocalMax.comp_continuous [TopologicalSpace δ] {g : δ → α} {b : δ}
    (hf : IsLocalMax f (g b)) (hg : ContinuousAt g b) : IsLocalMax (f ∘ g) b :=
  hg hf

theorem IsLocalExtr.comp_continuous [TopologicalSpace δ] {g : δ → α} {b : δ}
    (hf : IsLocalExtr f (g b)) (hg : ContinuousAt g b) : IsLocalExtr (f ∘ g) b :=
  hf.comp_tendsto hg

theorem IsLocalMin.comp_continuousOn [TopologicalSpace δ] {s : Set δ} {g : δ → α} {b : δ}
    (hf : IsLocalMin f (g b)) (hg : ContinuousOn g s) (hb : b ∈ s) : IsLocalMinOn (f ∘ g) s b :=
  hf.comp_tendsto (hg b hb)

theorem IsLocalMax.comp_continuousOn [TopologicalSpace δ] {s : Set δ} {g : δ → α} {b : δ}
    (hf : IsLocalMax f (g b)) (hg : ContinuousOn g s) (hb : b ∈ s) : IsLocalMaxOn (f ∘ g) s b :=
  hf.comp_tendsto (hg b hb)

theorem IsLocalExtr.comp_continuousOn [TopologicalSpace δ] {s : Set δ} (g : δ → α) {b : δ}
    (hf : IsLocalExtr f (g b)) (hg : ContinuousOn g s) (hb : b ∈ s) : IsLocalExtrOn (f ∘ g) s b :=
  hf.elim (fun hf => (hf.comp_continuousOn hg hb).isExtr) fun hf =>
    (IsLocalMax.comp_continuousOn hf hg hb).isExtr

theorem IsLocalMinOn.comp_continuousOn [TopologicalSpace δ] {t : Set α} {s : Set δ} {g : δ → α}
    {b : δ} (hf : IsLocalMinOn f t (g b)) (hst : s ⊆ g ⁻¹' t) (hg : ContinuousOn g s) (hb : b ∈ s) :
    IsLocalMinOn (f ∘ g) s b :=
  hf.comp_tendsto
    (tendsto_nhdsWithin_mono_right (image_subset_iff.mpr hst)
      (ContinuousWithinAt.tendsto_nhdsWithin_image (hg b hb)))

theorem IsLocalMaxOn.comp_continuousOn [TopologicalSpace δ] {t : Set α} {s : Set δ} {g : δ → α}
    {b : δ} (hf : IsLocalMaxOn f t (g b)) (hst : s ⊆ g ⁻¹' t) (hg : ContinuousOn g s) (hb : b ∈ s) :
    IsLocalMaxOn (f ∘ g) s b :=
  hf.comp_tendsto
    (tendsto_nhdsWithin_mono_right (image_subset_iff.mpr hst)
      (ContinuousWithinAt.tendsto_nhdsWithin_image (hg b hb)))

theorem IsLocalExtrOn.comp_continuousOn [TopologicalSpace δ] {t : Set α} {s : Set δ} (g : δ → α)
    {b : δ} (hf : IsLocalExtrOn f t (g b)) (hst : s ⊆ g ⁻¹' t) (hg : ContinuousOn g s)
    (hb : b ∈ s) : IsLocalExtrOn (f ∘ g) s b :=
  hf.elim (fun hf => (hf.comp_continuousOn hst hg hb).isExtr) fun hf =>
    (IsLocalMaxOn.comp_continuousOn hf hst hg hb).isExtr

end Preorder

/-! ### Pointwise addition -/


section OrderedAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
  {f g : α → β} {a : α} {s : Set α} {l : Filter α}

nonrec theorem IsLocalMin.add (hf : IsLocalMin f a) (hg : IsLocalMin g a) :
    IsLocalMin (fun x => f x + g x) a :=
  hf.add hg

nonrec theorem IsLocalMax.add (hf : IsLocalMax f a) (hg : IsLocalMax g a) :
    IsLocalMax (fun x => f x + g x) a :=
  hf.add hg

nonrec theorem IsLocalMinOn.add (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMinOn (fun x => f x + g x) s a :=
  hf.add hg

nonrec theorem IsLocalMaxOn.add (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMaxOn (fun x => f x + g x) s a :=
  hf.add hg

end OrderedAddCommMonoid

/-! ### Pointwise negation and subtraction -/


section OrderedAddCommGroup

variable [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  {f g : α → β} {a : α} {s : Set α} {l : Filter α}

nonrec theorem IsLocalMin.neg (hf : IsLocalMin f a) : IsLocalMax (fun x => -f x) a :=
  hf.neg

nonrec theorem IsLocalMax.neg (hf : IsLocalMax f a) : IsLocalMin (fun x => -f x) a :=
  hf.neg

nonrec theorem IsLocalExtr.neg (hf : IsLocalExtr f a) : IsLocalExtr (fun x => -f x) a :=
  hf.neg

nonrec theorem IsLocalMinOn.neg (hf : IsLocalMinOn f s a) : IsLocalMaxOn (fun x => -f x) s a :=
  hf.neg

nonrec theorem IsLocalMaxOn.neg (hf : IsLocalMaxOn f s a) : IsLocalMinOn (fun x => -f x) s a :=
  hf.neg

nonrec theorem IsLocalExtrOn.neg (hf : IsLocalExtrOn f s a) : IsLocalExtrOn (fun x => -f x) s a :=
  hf.neg

nonrec theorem IsLocalMin.sub (hf : IsLocalMin f a) (hg : IsLocalMax g a) :
    IsLocalMin (fun x => f x - g x) a :=
  hf.sub hg

nonrec theorem IsLocalMax.sub (hf : IsLocalMax f a) (hg : IsLocalMin g a) :
    IsLocalMax (fun x => f x - g x) a :=
  hf.sub hg

nonrec theorem IsLocalMinOn.sub (hf : IsLocalMinOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMinOn (fun x => f x - g x) s a :=
  hf.sub hg

nonrec theorem IsLocalMaxOn.sub (hf : IsLocalMaxOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMaxOn (fun x => f x - g x) s a :=
  hf.sub hg

end OrderedAddCommGroup

/-! ### Pointwise `sup`/`inf` -/


section SemilatticeSup

variable [SemilatticeSup β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

nonrec theorem IsLocalMin.sup (hf : IsLocalMin f a) (hg : IsLocalMin g a) :
    IsLocalMin (fun x => f x ⊔ g x) a :=
  hf.sup hg

nonrec theorem IsLocalMax.sup (hf : IsLocalMax f a) (hg : IsLocalMax g a) :
    IsLocalMax (fun x => f x ⊔ g x) a :=
  hf.sup hg

nonrec theorem IsLocalMinOn.sup (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMinOn (fun x => f x ⊔ g x) s a :=
  hf.sup hg

nonrec theorem IsLocalMaxOn.sup (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMaxOn (fun x => f x ⊔ g x) s a :=
  hf.sup hg

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

nonrec theorem IsLocalMin.inf (hf : IsLocalMin f a) (hg : IsLocalMin g a) :
    IsLocalMin (fun x => f x ⊓ g x) a :=
  hf.inf hg

nonrec theorem IsLocalMax.inf (hf : IsLocalMax f a) (hg : IsLocalMax g a) :
    IsLocalMax (fun x => f x ⊓ g x) a :=
  hf.inf hg

nonrec theorem IsLocalMinOn.inf (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMinOn (fun x => f x ⊓ g x) s a :=
  hf.inf hg

nonrec theorem IsLocalMaxOn.inf (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMaxOn (fun x => f x ⊓ g x) s a :=
  hf.inf hg

end SemilatticeInf

/-! ### Pointwise `min`/`max` -/


section LinearOrder

variable [LinearOrder β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

nonrec theorem IsLocalMin.min (hf : IsLocalMin f a) (hg : IsLocalMin g a) :
    IsLocalMin (fun x => min (f x) (g x)) a :=
  hf.min hg

nonrec theorem IsLocalMax.min (hf : IsLocalMax f a) (hg : IsLocalMax g a) :
    IsLocalMax (fun x => min (f x) (g x)) a :=
  hf.min hg

nonrec theorem IsLocalMinOn.min (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMinOn (fun x => min (f x) (g x)) s a :=
  hf.min hg

nonrec theorem IsLocalMaxOn.min (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMaxOn (fun x => min (f x) (g x)) s a :=
  hf.min hg

nonrec theorem IsLocalMin.max (hf : IsLocalMin f a) (hg : IsLocalMin g a) :
    IsLocalMin (fun x => max (f x) (g x)) a :=
  hf.max hg

nonrec theorem IsLocalMax.max (hf : IsLocalMax f a) (hg : IsLocalMax g a) :
    IsLocalMax (fun x => max (f x) (g x)) a :=
  hf.max hg

nonrec theorem IsLocalMinOn.max (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMinOn (fun x => max (f x) (g x)) s a :=
  hf.max hg

nonrec theorem IsLocalMaxOn.max (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMaxOn (fun x => max (f x) (g x)) s a :=
  hf.max hg

end LinearOrder

section Eventually

/-! ### Relation with `eventually` comparisons of two functions -/


variable [Preorder β] {s : Set α}

theorem Filter.EventuallyLE.isLocalMaxOn {f g : α → β} {a : α} (hle : g ≤ᶠ[𝓝[s] a] f)
    (hfga : f a = g a) (h : IsLocalMaxOn f s a) : IsLocalMaxOn g s a :=
  hle.isMaxFilter hfga h

nonrec theorem IsLocalMaxOn.congr {f g : α → β} {a : α} (h : IsLocalMaxOn f s a)
    (heq : f =ᶠ[𝓝[s] a] g) (hmem : a ∈ s) : IsLocalMaxOn g s a :=
  h.congr heq <| heq.eq_of_nhdsWithin hmem

theorem Filter.EventuallyEq.isLocalMaxOn_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝[s] a] g)
    (hmem : a ∈ s) : IsLocalMaxOn f s a ↔ IsLocalMaxOn g s a :=
  heq.isMaxFilter_iff <| heq.eq_of_nhdsWithin hmem

theorem Filter.EventuallyLE.isLocalMinOn {f g : α → β} {a : α} (hle : f ≤ᶠ[𝓝[s] a] g)
    (hfga : f a = g a) (h : IsLocalMinOn f s a) : IsLocalMinOn g s a :=
  hle.isMinFilter hfga h

nonrec theorem IsLocalMinOn.congr {f g : α → β} {a : α} (h : IsLocalMinOn f s a)
    (heq : f =ᶠ[𝓝[s] a] g) (hmem : a ∈ s) : IsLocalMinOn g s a :=
  h.congr heq <| heq.eq_of_nhdsWithin hmem

nonrec theorem Filter.EventuallyEq.isLocalMinOn_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝[s] a] g)
    (hmem : a ∈ s) : IsLocalMinOn f s a ↔ IsLocalMinOn g s a :=
  heq.isMinFilter_iff <| heq.eq_of_nhdsWithin hmem

nonrec theorem IsLocalExtrOn.congr {f g : α → β} {a : α} (h : IsLocalExtrOn f s a)
    (heq : f =ᶠ[𝓝[s] a] g) (hmem : a ∈ s) : IsLocalExtrOn g s a :=
  h.congr heq <| heq.eq_of_nhdsWithin hmem

theorem Filter.EventuallyEq.isLocalExtrOn_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝[s] a] g)
    (hmem : a ∈ s) : IsLocalExtrOn f s a ↔ IsLocalExtrOn g s a :=
  heq.isExtrFilter_iff <| heq.eq_of_nhdsWithin hmem

theorem Filter.EventuallyLE.isLocalMax {f g : α → β} {a : α} (hle : g ≤ᶠ[𝓝 a] f) (hfga : f a = g a)
    (h : IsLocalMax f a) : IsLocalMax g a :=
  hle.isMaxFilter hfga h

nonrec theorem IsLocalMax.congr {f g : α → β} {a : α} (h : IsLocalMax f a) (heq : f =ᶠ[𝓝 a] g) :
    IsLocalMax g a :=
  h.congr heq heq.eq_of_nhds

theorem Filter.EventuallyEq.isLocalMax_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝 a] g) :
    IsLocalMax f a ↔ IsLocalMax g a :=
  heq.isMaxFilter_iff heq.eq_of_nhds

theorem Filter.EventuallyLE.isLocalMin {f g : α → β} {a : α} (hle : f ≤ᶠ[𝓝 a] g) (hfga : f a = g a)
    (h : IsLocalMin f a) : IsLocalMin g a :=
  hle.isMinFilter hfga h

nonrec theorem IsLocalMin.congr {f g : α → β} {a : α} (h : IsLocalMin f a) (heq : f =ᶠ[𝓝 a] g) :
    IsLocalMin g a :=
  h.congr heq heq.eq_of_nhds

theorem Filter.EventuallyEq.isLocalMin_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝 a] g) :
    IsLocalMin f a ↔ IsLocalMin g a :=
  heq.isMinFilter_iff heq.eq_of_nhds

nonrec theorem IsLocalExtr.congr {f g : α → β} {a : α} (h : IsLocalExtr f a) (heq : f =ᶠ[𝓝 a] g) :
    IsLocalExtr g a :=
  h.congr heq heq.eq_of_nhds

theorem Filter.EventuallyEq.isLocalExtr_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝 a] g) :
    IsLocalExtr f a ↔ IsLocalExtr g a :=
  heq.isExtrFilter_iff heq.eq_of_nhds

end Eventually

/-- If `f` is monotone to the left and antitone to the right, then it has a local maximum. -/
lemma isLocalMax_of_mono_anti' {α : Type*} [TopologicalSpace α] [LinearOrder α]
    {β : Type*} [Preorder β] {b : α} {f : α → β}
    {a : Set α} (ha : a ∈ 𝓝[≤] b) {c : Set α} (hc : c ∈ 𝓝[≥] b)
    (h₀ : MonotoneOn f a) (h₁ : AntitoneOn f c) : IsLocalMax f b :=
  have : b ∈ a := mem_of_mem_nhdsWithin (by simp) ha
  have : b ∈ c := mem_of_mem_nhdsWithin (by simp) hc
  mem_of_superset (nhds_of_Ici_Iic ha hc) (fun x _ => by rcases le_total x b <;> aesop)

/-- If `f` is antitone to the left and monotone to the right, then it has a local minimum. -/
lemma isLocalMin_of_anti_mono' {α : Type*} [TopologicalSpace α] [LinearOrder α]
    {β : Type*} [Preorder β] {b : α} {f : α → β}
    {a : Set α} (ha : a ∈ 𝓝[≤] b) {c : Set α} (hc : c ∈ 𝓝[≥] b)
    (h₀ : AntitoneOn f a) (h₁ : MonotoneOn f c) : IsLocalMin f b :=
  have : b ∈ a := mem_of_mem_nhdsWithin (by simp) ha
  have : b ∈ c := mem_of_mem_nhdsWithin (by simp) hc
  mem_of_superset (nhds_of_Ici_Iic ha hc) (fun x _ => by rcases le_total x b <;> aesop)
