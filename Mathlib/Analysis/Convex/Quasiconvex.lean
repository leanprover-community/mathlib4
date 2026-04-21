/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Antoine Chambert-Loir, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.PathConnected

/-!
# Quasiconvex and quasiconcave functions

This file defines quasiconvexity, quasiconcavity and quasilinearity of functions, which are
generalizations of unimodality and monotonicity. Convexity implies quasiconvexity, concavity implies
quasiconcavity, and monotonicity implies quasilinearity.

## Main declarations

* `QuasiconvexOn 𝕜 s f`: Quasiconvexity of the function `f` on the set `s` with scalars `𝕜`. This
  means that, for all `r`, `{x ∈ s | f x ≤ r}` is `𝕜`-convex.
* `QuasiconcaveOn 𝕜 s f`: Quasiconcavity of the function `f` on the set `s` with scalars `𝕜`. This
  means that, for all `r`, `{x ∈ s | r ≤ f x}` is `𝕜`-convex.
* `QuasilinearOn 𝕜 s f`: Quasilinearity of the function `f` on the set `s` with scalars `𝕜`. This
  means that `f` is both quasiconvex and quasiconcave.

## References

* https://en.wikipedia.org/wiki/Quasiconvex_function
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


open Function OrderDual Set

variable {𝕜 E β : Type*}

section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]

section LE_β

variable (𝕜) [LE β] [SMul 𝕜 E] (s : Set E) (f : E → β)

/-- A function is quasiconvex if all its sublevels are convex.
This means that, for all `r`, `{x ∈ s | f x ≤ r}` is `𝕜`-convex. -/
def QuasiconvexOn : Prop :=
  ∀ r, Convex 𝕜 ({ x ∈ s | f x ≤ r })

/-- A function is quasiconcave if all its superlevels are convex.
This means that, for all `r`, `{x ∈ s | r ≤ f x}` is `𝕜`-convex. -/
def QuasiconcaveOn : Prop :=
  ∀ r, Convex 𝕜 ({ x ∈ s | r ≤ f x })

/-- A function is quasilinear if it is both quasiconvex and quasiconcave.
This means that, for all `r`,
the sets `{x ∈ s | f x ≤ r}` and `{x ∈ s | r ≤ f x}` are `𝕜`-convex. -/
def QuasilinearOn : Prop :=
  QuasiconvexOn 𝕜 s f ∧ QuasiconcaveOn 𝕜 s f

variable {𝕜 s f}

theorem QuasiconvexOn.dual : QuasiconvexOn 𝕜 s f → QuasiconcaveOn 𝕜 s (toDual ∘ f) :=
  id

theorem QuasiconcaveOn.dual : QuasiconcaveOn 𝕜 s f → QuasiconvexOn 𝕜 s (toDual ∘ f) :=
  id

theorem QuasilinearOn.dual : QuasilinearOn 𝕜 s f → QuasilinearOn 𝕜 s (toDual ∘ f) :=
  And.symm

theorem Convex.quasiconvexOn_of_convex_le (hs : Convex 𝕜 s) (h : ∀ r, Convex 𝕜 { x | f x ≤ r }) :
    QuasiconvexOn 𝕜 s f := fun r => hs.inter (h r)

theorem Convex.quasiconcaveOn_of_convex_ge (hs : Convex 𝕜 s) (h : ∀ r, Convex 𝕜 { x | r ≤ f x }) :
    QuasiconcaveOn 𝕜 s f :=
  Convex.quasiconvexOn_of_convex_le (β := βᵒᵈ) hs h

theorem QuasiconvexOn.convex [IsDirectedOrder β] (hf : QuasiconvexOn 𝕜 s f) : Convex 𝕜 s :=
  fun x hx y hy _ _ ha hb hab =>
  let ⟨_, hxz, hyz⟩ := exists_ge_ge (f x) (f y)
  (hf _ ⟨hx, hxz⟩ ⟨hy, hyz⟩ ha hb hab).1

theorem QuasiconcaveOn.convex [IsCodirectedOrder β] (hf : QuasiconcaveOn 𝕜 s f) : Convex 𝕜 s :=
  hf.dual.convex

end LE_β

section Composition

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]
variable {β γ : Type*} [LinearOrder β] [Preorder γ]
variable {s : Set E} {f : E → β} {g : β → γ}

theorem QuasiconvexOn.monotone_comp
    (hg : Monotone g) (hf : QuasiconvexOn 𝕜 s f) :
    QuasiconvexOn 𝕜 s (g ∘ f) := fun c x hx y hy ↦ by
  simp only [Function.comp_apply, mem_setOf_eq] at hx hy
  intro a b ha hb hab
  simp only [Function.comp_apply, mem_setOf_eq]
  wlog h : f x ≤ f y
  · grind
  specialize hf (f y) ⟨hx.1, h⟩ ⟨hy.1, le_rfl⟩ ha hb hab
  simp only [mem_setOf_eq] at hf
  exact ⟨hf.1, le_trans (hg hf.2) hy.2⟩

theorem QuasiconvexOn.antitone_comp (hg : Antitone g) (hf : QuasiconvexOn 𝕜 s f) :
    QuasiconcaveOn 𝕜 s (g ∘ f) :=
  hf.monotone_comp (γ := γᵒᵈ) hg

theorem QuasiconcaveOn.monotone_comp (hg : Monotone g) (hf : QuasiconcaveOn 𝕜 s f) :
    QuasiconcaveOn 𝕜 s (g ∘ f) :=
  QuasiconvexOn.monotone_comp hg.dual hf

theorem QuasiconcaveOn.antitone_comp (hg : Antitone g) (hf : QuasiconcaveOn 𝕜 s f) :
    QuasiconvexOn 𝕜 s (g ∘ f) :=
  QuasiconvexOn.monotone_comp (β := βᵒᵈ) hg.dual hf

theorem QuasilinearOn.monotone_comp (hg : Monotone g) (hf : QuasilinearOn 𝕜 s f) :
    QuasilinearOn 𝕜 s (g ∘ f) :=
  ⟨hf.1.monotone_comp hg, hf.2.monotone_comp hg⟩

theorem QuasilinearOn.antitone_comp (hg : Antitone g) (hf : QuasilinearOn 𝕜 s f) :
    QuasilinearOn 𝕜 s (g ∘ f) :=
  ⟨hf.2.antitone_comp hg, hf.1.antitone_comp hg⟩

end Composition

section Restriction

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid E] [SMul 𝕜 E]
variable {β : Type*} [Preorder β]
variable {s : Set E} {f : E → β}

theorem Convex.quasiconvexOn_restrict {t : Set E} (hf : QuasiconvexOn 𝕜 s f) (hst : t ⊆ s)
    (ht : Convex 𝕜 t) : QuasiconvexOn 𝕜 t f := by
  intro b
  rw [Set.sep_eq_inter_sep hst]
  exact Convex.inter ht (hf b)

theorem Convex.quasiconcaveOn_restrict {t : Set E} (hf : QuasiconcaveOn 𝕜 s f) (hst : t ⊆ s)
    (ht : Convex 𝕜 t) : QuasiconcaveOn 𝕜 t f := by
  intro b
  rw [Set.sep_eq_inter_sep hst]
  exact Convex.inter ht (hf b)

end Restriction

section Preconnected

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

variable {β : Type*} [Preorder β] {f : E → β}

open scoped Set.Notation

/-- If `f` is quasiconcave, then its over-levels are connected. -/
theorem QuasiconcaveOn.isPreconnected_preimage_subtype {s : Set E} {t : β}
    (hfc : QuasiconcaveOn ℝ s f) :
    IsPreconnected (s ↓∩ (f ⁻¹' Ici t)) := by
  rw [← Topology.IsInducing.subtypeVal.isPreconnected_image,
    image_preimage_eq_inter_range,
    Subtype.range_coe, inter_comm]
  exact (hfc t).isPreconnected

/-- If `f` is quasiconcave, then its under-levels are connected. -/
theorem QuasiconvexOn.isPreconnected_preimage_subtype {s : Set E} {t : β}
    (hfc : QuasiconvexOn ℝ s f) :
    IsPreconnected (s ↓∩ (f ⁻¹' Iic t)) :=
  QuasiconcaveOn.isPreconnected_preimage_subtype (β := βᵒᵈ) hfc

theorem QuasilinearOn.isPreconnected_preimage_subtype {s : Set E} {t : β}
    (hfc : QuasilinearOn ℝ s f) :
    IsPreconnected (s ↓∩ f ⁻¹' Iic t) :=
  hfc.left.isPreconnected_preimage_subtype

end Preconnected

section Semilattice_β

variable [SMul 𝕜 E] {s : Set E} {f g : E → β}

theorem QuasiconvexOn.sup [SemilatticeSup β] (hf : QuasiconvexOn 𝕜 s f)
    (hg : QuasiconvexOn 𝕜 s g) : QuasiconvexOn 𝕜 s (f ⊔ g) := by
  intro r
  simp_rw [Pi.sup_def, sup_le_iff, Set.sep_and]
  exact (hf r).inter (hg r)

theorem QuasiconcaveOn.inf [SemilatticeInf β] (hf : QuasiconcaveOn 𝕜 s f)
    (hg : QuasiconcaveOn 𝕜 s g) : QuasiconcaveOn 𝕜 s (f ⊓ g) :=
  hf.dual.sup hg

end Semilattice_β

section LinearOrder_β

variable [LinearOrder β] [SMul 𝕜 E] {s : Set E} {f : E → β}

theorem quasiconvexOn_iff_le_max : QuasiconvexOn 𝕜 s f ↔ Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄,
    y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → f (a • x + b • y) ≤ max (f x) (f y) :=
  ⟨fun hf =>
    ⟨hf.convex, fun _ hx _ hy _ _ ha hb hab =>
      (hf _ ⟨hx, le_max_left _ _⟩ ⟨hy, le_max_right _ _⟩ ha hb hab).2⟩,
    fun hf _ _ hx _ hy _ _ ha hb hab =>
    ⟨hf.1 hx.1 hy.1 ha hb hab, (hf.2 hx.1 hy.1 ha hb hab).trans <| max_le hx.2 hy.2⟩⟩

theorem quasiconcaveOn_iff_min_le : QuasiconcaveOn 𝕜 s f ↔ Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄,
    y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → min (f x) (f y) ≤ f (a • x + b • y) :=
  quasiconvexOn_iff_le_max (β := βᵒᵈ)

theorem quasilinearOn_iff_mem_uIcc : QuasilinearOn 𝕜 s f ↔ Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄,
    y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → f (a • x + b • y) ∈ uIcc (f x) (f y) := by
  rw [QuasilinearOn, quasiconvexOn_iff_le_max, quasiconcaveOn_iff_min_le, and_and_and_comm,
    and_self_iff]
  apply and_congr_right'
  simp_rw [← forall_and, ← Icc_min_max, mem_Icc, and_comm]

theorem QuasiconvexOn.convex_lt (hf : QuasiconvexOn 𝕜 s f) (r : β) :
    Convex 𝕜 ({ x ∈ s | f x < r }) := by
  refine fun x hx y hy a b ha hb hab => ?_
  have h := hf _ ⟨hx.1, le_max_left _ _⟩ ⟨hy.1, le_max_right _ _⟩ ha hb hab
  exact ⟨h.1, h.2.trans_lt <| max_lt hx.2 hy.2⟩

theorem QuasiconcaveOn.convex_gt (hf : QuasiconcaveOn 𝕜 s f) (r : β) :
    Convex 𝕜 ({ x ∈ s | r < f x }) :=
  hf.dual.convex_lt r

end LinearOrder_β

section PosSMulMono

variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
  [Module 𝕜 E] [Module 𝕜 β] [PosSMulMono 𝕜 β]
  {s : Set E} {f : E → β}

theorem ConvexOn.quasiconvexOn (hf : ConvexOn 𝕜 s f) : QuasiconvexOn 𝕜 s f :=
  hf.convex_le

theorem ConcaveOn.quasiconcaveOn (hf : ConcaveOn 𝕜 s f) : QuasiconcaveOn 𝕜 s f :=
  hf.convex_ge

end PosSMulMono

section LinearOrder

variable [LinearOrder E] [IsOrderedAddMonoid E] [PartialOrder β] [Module 𝕜 E] [PosSMulMono 𝕜 E]
  {s : Set E} {f : E → β}

theorem MonotoneOn.quasiconvexOn (hf : MonotoneOn f s) (hs : Convex 𝕜 s) : QuasiconvexOn 𝕜 s f :=
  hf.convex_le hs

theorem MonotoneOn.quasiconcaveOn (hf : MonotoneOn f s) (hs : Convex 𝕜 s) : QuasiconcaveOn 𝕜 s f :=
  hf.convex_ge hs

theorem MonotoneOn.quasilinearOn (hf : MonotoneOn f s) (hs : Convex 𝕜 s) : QuasilinearOn 𝕜 s f :=
  ⟨hf.quasiconvexOn hs, hf.quasiconcaveOn hs⟩

theorem AntitoneOn.quasiconvexOn (hf : AntitoneOn f s) (hs : Convex 𝕜 s) : QuasiconvexOn 𝕜 s f :=
  hf.convex_le hs

theorem AntitoneOn.quasiconcaveOn (hf : AntitoneOn f s) (hs : Convex 𝕜 s) : QuasiconcaveOn 𝕜 s f :=
  hf.convex_ge hs

theorem AntitoneOn.quasilinearOn (hf : AntitoneOn f s) (hs : Convex 𝕜 s) : QuasilinearOn 𝕜 s f :=
  ⟨hf.quasiconvexOn hs, hf.quasiconcaveOn hs⟩

theorem Monotone.quasiconvexOn (hf : Monotone f) : QuasiconvexOn 𝕜 univ f :=
  (hf.monotoneOn _).quasiconvexOn convex_univ

theorem Monotone.quasiconcaveOn (hf : Monotone f) : QuasiconcaveOn 𝕜 univ f :=
  (hf.monotoneOn _).quasiconcaveOn convex_univ

theorem Monotone.quasilinearOn (hf : Monotone f) : QuasilinearOn 𝕜 univ f :=
  ⟨hf.quasiconvexOn, hf.quasiconcaveOn⟩

theorem Antitone.quasiconvexOn (hf : Antitone f) : QuasiconvexOn 𝕜 univ f :=
  (hf.antitoneOn _).quasiconvexOn convex_univ

theorem Antitone.quasiconcaveOn (hf : Antitone f) : QuasiconcaveOn 𝕜 univ f :=
  (hf.antitoneOn _).quasiconcaveOn convex_univ

theorem Antitone.quasilinearOn (hf : Antitone f) : QuasilinearOn 𝕜 univ f :=
  ⟨hf.quasiconvexOn, hf.quasiconcaveOn⟩

end LinearOrder
end OrderedSemiring

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜} {f : 𝕜 → β}

theorem QuasilinearOn.monotoneOn_or_antitoneOn [LinearOrder β] (hf : QuasilinearOn 𝕜 s f) :
    MonotoneOn f s ∨ AntitoneOn f s := by
  simp_rw [monotoneOn_or_antitoneOn_iff_uIcc, ← segment_eq_uIcc]
  rintro a ha b hb c _ h
  refine ⟨((hf.2 _).segment_subset ?_ ?_ h).2, ((hf.1 _).segment_subset ?_ ?_ h).2⟩ <;> simp [*]

theorem quasilinearOn_iff_monotoneOn_or_antitoneOn [LinearOrder β]
    (hs : Convex 𝕜 s) : QuasilinearOn 𝕜 s f ↔ MonotoneOn f s ∨ AntitoneOn f s :=
  ⟨fun h => h.monotoneOn_or_antitoneOn, fun h =>
    h.elim (fun h => h.quasilinearOn hs) fun h => h.quasilinearOn hs⟩

end LinearOrderedField
