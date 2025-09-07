/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, François Dupuis
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Order.Filter.Extr
import Mathlib.Tactic.NormNum

/-!
# Convex and concave functions

This file defines convex and concave functions in vector spaces and proves the finite Jensen
inequality. The integral version can be found in `Analysis.Convex.Integral`.

A function `f : E → β` is `ConvexOn` a set `s` if `s` is itself a convex set, and for any two
points `x y ∈ s`, the segment joining `(x, f x)` to `(y, f y)` is above the graph of `f`.
Equivalently, `ConvexOn 𝕜 f s` means that the epigraph `{p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2}` is
a convex set.

## Main declarations

* `ConvexOn 𝕜 s f`: The function `f` is convex on `s` with scalars `𝕜`.
* `ConcaveOn 𝕜 s f`: The function `f` is concave on `s` with scalars `𝕜`.
* `StrictConvexOn 𝕜 s f`: The function `f` is strictly convex on `s` with scalars `𝕜`.
* `StrictConcaveOn 𝕜 s f`: The function `f` is strictly concave on `s` with scalars `𝕜`.
-/

open LinearMap Set Convex Pointwise

variable {𝕜 E F α β ι : Type*}

section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F]

section OrderedAddCommMonoid

variable [AddCommMonoid α] [PartialOrder α] [AddCommMonoid β] [PartialOrder β]

section SMul

variable (𝕜) [SMul 𝕜 E] [SMul 𝕜 α] [SMul 𝕜 β] (s : Set E) (f : E → β) {g : β → α}

/-- Convexity of functions -/
def ConvexOn : Prop :=
  Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    f (a • x + b • y) ≤ a • f x + b • f y

/-- Concavity of functions -/
def ConcaveOn : Prop :=
  Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    a • f x + b • f y ≤ f (a • x + b • y)

/-- Strict convexity of functions -/
def StrictConvexOn : Prop :=
  Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
    f (a • x + b • y) < a • f x + b • f y

/-- Strict concavity of functions -/
def StrictConcaveOn : Prop :=
  Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
    a • f x + b • f y < f (a • x + b • y)

variable {𝕜 s f}

open OrderDual (toDual ofDual)

theorem ConvexOn.dual (hf : ConvexOn 𝕜 s f) : ConcaveOn 𝕜 s (toDual ∘ f) := hf

theorem ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (toDual ∘ f) := hf

theorem StrictConvexOn.dual (hf : StrictConvexOn 𝕜 s f) : StrictConcaveOn 𝕜 s (toDual ∘ f) := hf

theorem StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) : StrictConvexOn 𝕜 s (toDual ∘ f) := hf

theorem convexOn_id {s : Set β} (hs : Convex 𝕜 s) : ConvexOn 𝕜 s _root_.id :=
  ⟨hs, by
    intros
    rfl⟩

theorem concaveOn_id {s : Set β} (hs : Convex 𝕜 s) : ConcaveOn 𝕜 s _root_.id :=
  ⟨hs, by
    intros
    rfl⟩

section congr

variable {g : E → β}

theorem ConvexOn.congr (hf : ConvexOn 𝕜 s f) (hfg : EqOn f g s) : ConvexOn 𝕜 s g :=
  ⟨hf.1, fun x hx y hy a b ha hb hab => by
    simpa only [← hfg hx, ← hfg hy, ← hfg (hf.1 hx hy ha hb hab)] using hf.2 hx hy ha hb hab⟩

theorem ConcaveOn.congr (hf : ConcaveOn 𝕜 s f) (hfg : EqOn f g s) : ConcaveOn 𝕜 s g :=
  ⟨hf.1, fun x hx y hy a b ha hb hab => by
    simpa only [← hfg hx, ← hfg hy, ← hfg (hf.1 hx hy ha hb hab)] using hf.2 hx hy ha hb hab⟩

theorem StrictConvexOn.congr (hf : StrictConvexOn 𝕜 s f) (hfg : EqOn f g s) :
    StrictConvexOn 𝕜 s g :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab => by
    simpa only [← hfg hx, ← hfg hy, ← hfg (hf.1 hx hy ha.le hb.le hab)] using
      hf.2 hx hy hxy ha hb hab⟩

theorem StrictConcaveOn.congr (hf : StrictConcaveOn 𝕜 s f) (hfg : EqOn f g s) :
    StrictConcaveOn 𝕜 s g :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab => by
    simpa only [← hfg hx, ← hfg hy, ← hfg (hf.1 hx hy ha.le hb.le hab)] using
      hf.2 hx hy hxy ha hb hab⟩

end congr

theorem ConvexOn.subset {t : Set E} (hf : ConvexOn 𝕜 t f) (hst : s ⊆ t) (hs : Convex 𝕜 s) :
    ConvexOn 𝕜 s f :=
  ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩

theorem ConcaveOn.subset {t : Set E} (hf : ConcaveOn 𝕜 t f) (hst : s ⊆ t) (hs : Convex 𝕜 s) :
    ConcaveOn 𝕜 s f :=
  ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩

theorem StrictConvexOn.subset {t : Set E} (hf : StrictConvexOn 𝕜 t f) (hst : s ⊆ t)
    (hs : Convex 𝕜 s) : StrictConvexOn 𝕜 s f :=
  ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩

theorem StrictConcaveOn.subset {t : Set E} (hf : StrictConcaveOn 𝕜 t f) (hst : s ⊆ t)
    (hs : Convex 𝕜 s) : StrictConcaveOn 𝕜 s f :=
  ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩

theorem ConvexOn.comp (hg : ConvexOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f)
    (hg' : MonotoneOn g (f '' s)) : ConvexOn 𝕜 s (g ∘ f) :=
  ⟨hf.1, fun _ hx _ hy _ _ ha hb hab =>
    (hg' (mem_image_of_mem f <| hf.1 hx hy ha hb hab)
            (hg.1 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab) <|
          hf.2 hx hy ha hb hab).trans <|
      hg.2 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab⟩

theorem ConcaveOn.comp (hg : ConcaveOn 𝕜 (f '' s) g) (hf : ConcaveOn 𝕜 s f)
    (hg' : MonotoneOn g (f '' s)) : ConcaveOn 𝕜 s (g ∘ f) :=
  ⟨hf.1, fun _ hx _ hy _ _ ha hb hab =>
    (hg.2 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab).trans <|
      hg' (hg.1 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab)
          (mem_image_of_mem f <| hf.1 hx hy ha hb hab) <|
        hf.2 hx hy ha hb hab⟩

theorem ConvexOn.comp_concaveOn (hg : ConvexOn 𝕜 (f '' s) g) (hf : ConcaveOn 𝕜 s f)
    (hg' : AntitoneOn g (f '' s)) : ConvexOn 𝕜 s (g ∘ f) :=
  hg.dual.comp hf hg'

theorem ConcaveOn.comp_convexOn (hg : ConcaveOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f)
    (hg' : AntitoneOn g (f '' s)) : ConcaveOn 𝕜 s (g ∘ f) :=
  hg.dual.comp hf hg'

theorem StrictConvexOn.comp (hg : StrictConvexOn 𝕜 (f '' s) g) (hf : StrictConvexOn 𝕜 s f)
    (hg' : StrictMonoOn g (f '' s)) (hf' : s.InjOn f) : StrictConvexOn 𝕜 s (g ∘ f) :=
  ⟨hf.1, fun _ hx _ hy hxy _ _ ha hb hab =>
    (hg' (mem_image_of_mem f <| hf.1 hx hy ha.le hb.le hab)
            (hg.1 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha.le hb.le hab) <|
          hf.2 hx hy hxy ha hb hab).trans <|
      hg.2 (mem_image_of_mem f hx) (mem_image_of_mem f hy) (mt (hf' hx hy) hxy) ha hb hab⟩

theorem StrictConcaveOn.comp (hg : StrictConcaveOn 𝕜 (f '' s) g) (hf : StrictConcaveOn 𝕜 s f)
    (hg' : StrictMonoOn g (f '' s)) (hf' : s.InjOn f) : StrictConcaveOn 𝕜 s (g ∘ f) :=
  ⟨hf.1, fun _ hx _ hy hxy _ _ ha hb hab =>
    (hg.2 (mem_image_of_mem f hx) (mem_image_of_mem f hy) (mt (hf' hx hy) hxy) ha hb hab).trans <|
      hg' (hg.1 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha.le hb.le hab)
          (mem_image_of_mem f <| hf.1 hx hy ha.le hb.le hab) <|
        hf.2 hx hy hxy ha hb hab⟩

theorem StrictConvexOn.comp_strictConcaveOn (hg : StrictConvexOn 𝕜 (f '' s) g)
    (hf : StrictConcaveOn 𝕜 s f) (hg' : StrictAntiOn g (f '' s)) (hf' : s.InjOn f) :
    StrictConvexOn 𝕜 s (g ∘ f) :=
  hg.dual.comp hf hg' hf'

theorem StrictConcaveOn.comp_strictConvexOn (hg : StrictConcaveOn 𝕜 (f '' s) g)
    (hf : StrictConvexOn 𝕜 s f) (hg' : StrictAntiOn g (f '' s)) (hf' : s.InjOn f) :
    StrictConcaveOn 𝕜 s (g ∘ f) :=
  hg.dual.comp hf hg' hf'

end SMul

section DistribMulAction

variable [IsOrderedAddMonoid β] [SMul 𝕜 E] [DistribMulAction 𝕜 β] {s : Set E} {f g : E → β}

theorem ConvexOn.add (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : ConvexOn 𝕜 s (f + g) :=
  ⟨hf.1, fun x hx y hy a b ha hb hab =>
    calc
      f (a • x + b • y) + g (a • x + b • y) ≤ a • f x + b • f y + (a • g x + b • g y) :=
        add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
      _ = a • (f x + g x) + b • (f y + g y) := by rw [smul_add, smul_add, add_add_add_comm]
      ⟩

theorem ConcaveOn.add (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) : ConcaveOn 𝕜 s (f + g) :=
  hf.dual.add hg

end DistribMulAction

section Module

variable [SMul 𝕜 E] [Module 𝕜 β] {s : Set E} {f : E → β}

theorem convexOn_const (c : β) (hs : Convex 𝕜 s) : ConvexOn 𝕜 s fun _ : E => c :=
  ⟨hs, fun _ _ _ _ _ _ _ _ hab => (Convex.combo_self hab c).ge⟩

theorem concaveOn_const (c : β) (hs : Convex 𝕜 s) : ConcaveOn 𝕜 s fun _ => c :=
  convexOn_const (β := βᵒᵈ) _ hs

theorem ConvexOn.add_const [IsOrderedAddMonoid β] (hf : ConvexOn 𝕜 s f) (b : β) :
    ConvexOn 𝕜 s (f + fun _ => b) :=
  hf.add (convexOn_const _ hf.1)

theorem ConcaveOn.add_const [IsOrderedAddMonoid β] (hf : ConcaveOn 𝕜 s f) (b : β) :
    ConcaveOn 𝕜 s (f + fun _ => b) :=
  hf.add (concaveOn_const _ hf.1)

theorem convexOn_of_convex_epigraph (h : Convex 𝕜 { p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2 }) :
    ConvexOn 𝕜 s f :=
  ⟨fun x hx y hy a b ha hb hab => (@h (x, f x) ⟨hx, le_rfl⟩ (y, f y) ⟨hy, le_rfl⟩ a b ha hb hab).1,
    fun x hx y hy a b ha hb hab => (@h (x, f x) ⟨hx, le_rfl⟩ (y, f y) ⟨hy, le_rfl⟩ a b ha hb hab).2⟩

theorem concaveOn_of_convex_hypograph (h : Convex 𝕜 { p : E × β | p.1 ∈ s ∧ p.2 ≤ f p.1 }) :
    ConcaveOn 𝕜 s f :=
  convexOn_of_convex_epigraph (β := βᵒᵈ) h

end Module

section OrderedSMul

variable [IsOrderedAddMonoid β] [SMul 𝕜 E] [Module 𝕜 β] [OrderedSMul 𝕜 β] {s : Set E} {f : E → β}

theorem ConvexOn.convex_le (hf : ConvexOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x ∈ s | f x ≤ r }) :=
  fun x hx y hy a b ha hb hab =>
  ⟨hf.1 hx.1 hy.1 ha hb hab,
    calc
      f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx.1 hy.1 ha hb hab
      _ ≤ a • r + b • r := by
        gcongr
        · exact hx.2
        · exact hy.2
      _ = r := Convex.combo_self hab r
      ⟩

theorem ConcaveOn.convex_ge (hf : ConcaveOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x ∈ s | r ≤ f x }) :=
  hf.dual.convex_le r

theorem ConvexOn.convex_epigraph (hf : ConvexOn 𝕜 s f) :
    Convex 𝕜 { p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2 } := by
  rintro ⟨x, r⟩ ⟨hx, hr⟩ ⟨y, t⟩ ⟨hy, ht⟩ a b ha hb hab
  refine ⟨hf.1 hx hy ha hb hab, ?_⟩
  calc
    f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx hy ha hb hab
    _ ≤ a • r + b • t := by gcongr

theorem ConcaveOn.convex_hypograph (hf : ConcaveOn 𝕜 s f) :
    Convex 𝕜 { p : E × β | p.1 ∈ s ∧ p.2 ≤ f p.1 } :=
  hf.dual.convex_epigraph

theorem convexOn_iff_convex_epigraph :
    ConvexOn 𝕜 s f ↔ Convex 𝕜 { p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2 } :=
  ⟨ConvexOn.convex_epigraph, convexOn_of_convex_epigraph⟩

theorem concaveOn_iff_convex_hypograph :
    ConcaveOn 𝕜 s f ↔ Convex 𝕜 { p : E × β | p.1 ∈ s ∧ p.2 ≤ f p.1 } :=
  convexOn_iff_convex_epigraph (β := βᵒᵈ)

end OrderedSMul

section Module

variable [Module 𝕜 E] [SMul 𝕜 β] {s : Set E} {f : E → β}

/-- Right translation preserves convexity. -/
theorem ConvexOn.translate_right (hf : ConvexOn 𝕜 s f) (c : E) :
    ConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => c + z) :=
  ⟨hf.1.translate_preimage_right _, fun x hx y hy a b ha hb hab =>
    calc
      f (c + (a • x + b • y)) = f (a • (c + x) + b • (c + y)) := by
        rw [smul_add, smul_add, add_add_add_comm, Convex.combo_self hab]
      _ ≤ a • f (c + x) + b • f (c + y) := hf.2 hx hy ha hb hab
      ⟩

/-- Right translation preserves concavity. -/
theorem ConcaveOn.translate_right (hf : ConcaveOn 𝕜 s f) (c : E) :
    ConcaveOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => c + z) :=
  hf.dual.translate_right _

/-- Left translation preserves convexity. -/
theorem ConvexOn.translate_left (hf : ConvexOn 𝕜 s f) (c : E) :
    ConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => z + c) := by
  simpa only [add_comm c] using hf.translate_right c

/-- Left translation preserves concavity. -/
theorem ConcaveOn.translate_left (hf : ConcaveOn 𝕜 s f) (c : E) :
    ConcaveOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => z + c) :=
  hf.dual.translate_left _

end Module

section Module

variable [Module 𝕜 E] [Module 𝕜 β]

theorem convexOn_iff_forall_pos {s : Set E} {f : E → β} :
    ConvexOn 𝕜 s f ↔ Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b →
      a + b = 1 → f (a • x + b • y) ≤ a • f x + b • f y := by
  refine and_congr_right'
    ⟨fun h x hx y hy a b ha hb hab => h hx hy ha.le hb.le hab, fun h x hx y hy a b ha hb hab => ?_⟩
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_add] at hab
    subst b
    simp_rw [zero_smul, zero_add, one_smul, le_rfl]
  obtain rfl | hb' := hb.eq_or_lt
  · rw [add_zero] at hab
    subst a
    simp_rw [zero_smul, add_zero, one_smul, le_rfl]
  exact h hx hy ha' hb' hab

theorem concaveOn_iff_forall_pos {s : Set E} {f : E → β} :
    ConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
        a • f x + b • f y ≤ f (a • x + b • y) :=
  convexOn_iff_forall_pos (β := βᵒᵈ)

theorem convexOn_iff_pairwise_pos {s : Set E} {f : E → β} :
    ConvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        s.Pairwise fun x y =>
          ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → f (a • x + b • y) ≤ a • f x + b • f y := by
  rw [convexOn_iff_forall_pos]
  refine
    and_congr_right'
      ⟨fun h x hx y hy _ a b ha hb hab => h hx hy ha hb hab, fun h x hx y hy a b ha hb hab => ?_⟩
  obtain rfl | hxy := eq_or_ne x y
  · rw [Convex.combo_self hab, Convex.combo_self hab]
  exact h hx hy hxy ha hb hab

theorem concaveOn_iff_pairwise_pos {s : Set E} {f : E → β} :
    ConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        s.Pairwise fun x y =>
          ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • f x + b • f y ≤ f (a • x + b • y) :=
  convexOn_iff_pairwise_pos (β := βᵒᵈ)

/-- A linear map is convex. -/
theorem LinearMap.convexOn (f : E →ₗ[𝕜] β) {s : Set E} (hs : Convex 𝕜 s) : ConvexOn 𝕜 s f :=
  ⟨hs, fun _ _ _ _ _ _ _ _ _ => by rw [f.map_add, f.map_smul, f.map_smul]⟩

/-- A linear map is concave. -/
theorem LinearMap.concaveOn (f : E →ₗ[𝕜] β) {s : Set E} (hs : Convex 𝕜 s) : ConcaveOn 𝕜 s f :=
  ⟨hs, fun _ _ _ _ _ _ _ _ _ => by rw [f.map_add, f.map_smul, f.map_smul]⟩

theorem StrictConvexOn.convexOn {s : Set E} {f : E → β} (hf : StrictConvexOn 𝕜 s f) :
    ConvexOn 𝕜 s f :=
  convexOn_iff_pairwise_pos.mpr
    ⟨hf.1, fun _ hx _ hy hxy _ _ ha hb hab => (hf.2 hx hy hxy ha hb hab).le⟩

theorem StrictConcaveOn.concaveOn {s : Set E} {f : E → β} (hf : StrictConcaveOn 𝕜 s f) :
    ConcaveOn 𝕜 s f :=
  hf.dual.convexOn

section OrderedSMul

variable [IsOrderedAddMonoid β] [OrderedSMul 𝕜 β] {s : Set E} {f : E → β}

theorem StrictConvexOn.convex_lt (hf : StrictConvexOn 𝕜 s f) (r : β) :
    Convex 𝕜 ({ x ∈ s | f x < r }) :=
  convex_iff_pairwise_pos.2 fun x hx y hy hxy a b ha hb hab =>
    ⟨hf.1 hx.1 hy.1 ha.le hb.le hab,
      calc
        f (a • x + b • y) < a • f x + b • f y := hf.2 hx.1 hy.1 hxy ha hb hab
        _ ≤ a • r + b • r := by
          gcongr
          · exact hx.2.le
          · exact hy.2.le
        _ = r := Convex.combo_self hab r
        ⟩

theorem StrictConcaveOn.convex_gt (hf : StrictConcaveOn 𝕜 s f) (r : β) :
    Convex 𝕜 ({ x ∈ s | r < f x }) :=
  hf.dual.convex_lt r

end OrderedSMul

section LinearOrder

variable [LinearOrder E] {s : Set E} {f : E → β}

/-- For a function on a convex set in a linearly ordered space (where the order and the algebraic
structures aren't necessarily compatible), in order to prove that it is convex, it suffices to
verify the inequality `f (a • x + b • y) ≤ a • f x + b • f y` only for `x < y` and positive `a`,
`b`. The main use case is `E = 𝕜` however one can apply it, e.g., to `𝕜^n` with lexicographic order.
-/
theorem LinearOrder.convexOn_of_lt (hs : Convex 𝕜 s)
    (hf : ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x < y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
      f (a • x + b • y) ≤ a • f x + b • f y) :
    ConvexOn 𝕜 s f := by
  refine convexOn_iff_pairwise_pos.2 ⟨hs, fun x hx y hy hxy a b ha hb hab => ?_⟩
  wlog h : x < y
  · rw [add_comm (a • x), add_comm (a • f x)]
    rw [add_comm] at hab
    exact this hs hf y hy x hx hxy.symm b a hb ha hab (hxy.lt_or_gt.resolve_left h)
  exact hf hx hy h ha hb hab

/-- For a function on a convex set in a linearly ordered space (where the order and the algebraic
structures aren't necessarily compatible), in order to prove that it is concave it suffices to
verify the inequality `a • f x + b • f y ≤ f (a • x + b • y)` for `x < y` and positive `a`, `b`. The
main use case is `E = ℝ` however one can apply it, e.g., to `ℝ^n` with lexicographic order. -/
theorem LinearOrder.concaveOn_of_lt (hs : Convex 𝕜 s)
    (hf : ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x < y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
      a • f x + b • f y ≤ f (a • x + b • y)) :
    ConcaveOn 𝕜 s f :=
  LinearOrder.convexOn_of_lt (β := βᵒᵈ) hs hf

/-- For a function on a convex set in a linearly ordered space (where the order and the algebraic
structures aren't necessarily compatible), in order to prove that it is strictly convex, it suffices
to verify the inequality `f (a • x + b • y) < a • f x + b • f y` for `x < y` and positive `a`, `b`.
The main use case is `E = 𝕜` however one can apply it, e.g., to `𝕜^n` with lexicographic order. -/
theorem LinearOrder.strictConvexOn_of_lt (hs : Convex 𝕜 s)
    (hf : ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x < y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
      f (a • x + b • y) < a • f x + b • f y) :
    StrictConvexOn 𝕜 s f := by
  refine ⟨hs, fun x hx y hy hxy a b ha hb hab => ?_⟩
  wlog h : x < y
  · rw [add_comm (a • x), add_comm (a • f x)]
    rw [add_comm] at hab
    exact this hs hf y hy x hx hxy.symm b a hb ha hab (hxy.lt_or_gt.resolve_left h)
  exact hf hx hy h ha hb hab

/-- For a function on a convex set in a linearly ordered space (where the order and the algebraic
structures aren't necessarily compatible), in order to prove that it is strictly concave it suffices
to verify the inequality `a • f x + b • f y < f (a • x + b • y)` for `x < y` and positive `a`, `b`.
The main use case is `E = 𝕜` however one can apply it, e.g., to `𝕜^n` with lexicographic order. -/
theorem LinearOrder.strictConcaveOn_of_lt (hs : Convex 𝕜 s)
    (hf : ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x < y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
      a • f x + b • f y < f (a • x + b • y)) :
    StrictConcaveOn 𝕜 s f :=
  LinearOrder.strictConvexOn_of_lt (β := βᵒᵈ) hs hf

end LinearOrder

end Module

section Module

variable [Module 𝕜 E] [Module 𝕜 F] [SMul 𝕜 β]

/-- If `f` is convex on `s`, so is `(f ∘ g)` on `g ⁻¹' s` for a linear `g`. -/
theorem ConvexOn.comp_linearMap {f : F → β} {s : Set F} (hf : ConvexOn 𝕜 s f) (g : E →ₗ[𝕜] F) :
    ConvexOn 𝕜 (g ⁻¹' s) (f ∘ g) :=
  ⟨hf.1.linear_preimage _, fun x hx y hy a b ha hb hab =>
    calc
      f (g (a • x + b • y)) = f (a • g x + b • g y) := by rw [g.map_add, g.map_smul, g.map_smul]
      _ ≤ a • f (g x) + b • f (g y) := hf.2 hx hy ha hb hab⟩

/-- If `f` is concave on `s`, so is `(g ∘ f)` on `g ⁻¹' s` for a linear `g`. -/
theorem ConcaveOn.comp_linearMap {f : F → β} {s : Set F} (hf : ConcaveOn 𝕜 s f) (g : E →ₗ[𝕜] F) :
    ConcaveOn 𝕜 (g ⁻¹' s) (f ∘ g) :=
  hf.dual.comp_linearMap g

end Module

end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β] [IsOrderedCancelAddMonoid β]

section DistribMulAction

variable [SMul 𝕜 E] [DistribMulAction 𝕜 β] {s : Set E} {f g : E → β}

theorem StrictConvexOn.add_convexOn (hf : StrictConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f + g) :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab =>
    calc
      f (a • x + b • y) + g (a • x + b • y) < a • f x + b • f y + (a • g x + b • g y) :=
        add_lt_add_of_lt_of_le (hf.2 hx hy hxy ha hb hab) (hg.2 hx hy ha.le hb.le hab)
      _ = a • (f x + g x) + b • (f y + g y) := by rw [smul_add, smul_add, add_add_add_comm]⟩

theorem ConvexOn.add_strictConvexOn (hf : ConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f + g) :=
  add_comm g f ▸ hg.add_convexOn hf

theorem StrictConvexOn.add (hf : StrictConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f + g) :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab =>
    calc
      f (a • x + b • y) + g (a • x + b • y) < a • f x + b • f y + (a • g x + b • g y) :=
        add_lt_add (hf.2 hx hy hxy ha hb hab) (hg.2 hx hy hxy ha hb hab)
      _ = a • (f x + g x) + b • (f y + g y) := by rw [smul_add, smul_add, add_add_add_comm]⟩

theorem StrictConcaveOn.add_concaveOn (hf : StrictConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f + g) :=
  hf.dual.add_convexOn hg.dual

theorem ConcaveOn.add_strictConcaveOn (hf : ConcaveOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f + g) :=
  hf.dual.add_strictConvexOn hg.dual

theorem StrictConcaveOn.add (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f + g) :=
  hf.dual.add hg

theorem StrictConvexOn.add_const {γ : Type*} {f : E → γ}
    [AddCommMonoid γ] [PartialOrder γ] [IsOrderedCancelAddMonoid γ]
    [Module 𝕜 γ] (hf : StrictConvexOn 𝕜 s f) (b : γ) : StrictConvexOn 𝕜 s (f + fun _ => b) :=
  hf.add_convexOn (convexOn_const _ hf.1)

theorem StrictConcaveOn.add_const {γ : Type*} {f : E → γ}
    [AddCommMonoid γ] [PartialOrder γ] [IsOrderedCancelAddMonoid γ]
    [Module 𝕜 γ] (hf : StrictConcaveOn 𝕜 s f) (b : γ) : StrictConcaveOn 𝕜 s (f + fun _ => b) :=
  hf.add_concaveOn (concaveOn_const _ hf.1)

end DistribMulAction

section Module

variable [Module 𝕜 E] [Module 𝕜 β] [OrderedSMul 𝕜 β] {s : Set E} {f : E → β}

theorem ConvexOn.convex_lt (hf : ConvexOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x ∈ s | f x < r }) :=
  convex_iff_forall_pos.2 fun x hx y hy a b ha hb hab =>
    ⟨hf.1 hx.1 hy.1 ha.le hb.le hab,
      calc
        f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx.1 hy.1 ha.le hb.le hab
        _ < a • r + b • r :=
          (add_lt_add_of_lt_of_le (smul_lt_smul_of_pos_left hx.2 ha)
            (smul_le_smul_of_nonneg_left hy.2.le hb.le))
        _ = r := Convex.combo_self hab _⟩

theorem ConcaveOn.convex_gt (hf : ConcaveOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x ∈ s | r < f x }) :=
  hf.dual.convex_lt r

theorem ConvexOn.openSegment_subset_strict_epigraph (hf : ConvexOn 𝕜 s f) (p q : E × β)
    (hp : p.1 ∈ s ∧ f p.1 < p.2) (hq : q.1 ∈ s ∧ f q.1 ≤ q.2) :
    openSegment 𝕜 p q ⊆ { p : E × β | p.1 ∈ s ∧ f p.1 < p.2 } := by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  refine ⟨hf.1 hp.1 hq.1 ha.le hb.le hab, ?_⟩
  calc
    f (a • p.1 + b • q.1) ≤ a • f p.1 + b • f q.1 := hf.2 hp.1 hq.1 ha.le hb.le hab
    _ < a • p.2 + b • q.2 := add_lt_add_of_lt_of_le
       (smul_lt_smul_of_pos_left hp.2 ha) (smul_le_smul_of_nonneg_left hq.2 hb.le)

theorem ConcaveOn.openSegment_subset_strict_hypograph (hf : ConcaveOn 𝕜 s f) (p q : E × β)
    (hp : p.1 ∈ s ∧ p.2 < f p.1) (hq : q.1 ∈ s ∧ q.2 ≤ f q.1) :
    openSegment 𝕜 p q ⊆ { p : E × β | p.1 ∈ s ∧ p.2 < f p.1 } :=
  hf.dual.openSegment_subset_strict_epigraph p q hp hq

theorem ConvexOn.convex_strict_epigraph [ZeroLEOneClass 𝕜] (hf : ConvexOn 𝕜 s f) :
    Convex 𝕜 { p : E × β | p.1 ∈ s ∧ f p.1 < p.2 } :=
  convex_iff_openSegment_subset.mpr fun p hp q hq =>
    hf.openSegment_subset_strict_epigraph p q hp ⟨hq.1, hq.2.le⟩

theorem ConcaveOn.convex_strict_hypograph [ZeroLEOneClass 𝕜] (hf : ConcaveOn 𝕜 s f) :
    Convex 𝕜 { p : E × β | p.1 ∈ s ∧ p.2 < f p.1 } :=
  hf.dual.convex_strict_epigraph

end Module

end OrderedCancelAddCommMonoid

section LinearOrderedAddCommMonoid

variable [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
  [SMul 𝕜 E] [Module 𝕜 β] [OrderedSMul 𝕜 β] {s : Set E}
  {f g : E → β}

/-- The pointwise maximum of convex functions is convex. -/
theorem ConvexOn.sup (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : ConvexOn 𝕜 s (f ⊔ g) := by
  refine ⟨hf.left, fun x hx y hy a b ha hb hab => sup_le ?_ ?_⟩
  · calc
      f (a • x + b • y) ≤ a • f x + b • f y := hf.right hx hy ha hb hab
      _ ≤ a • (f x ⊔ g x) + b • (f y ⊔ g y) := by gcongr <;> apply le_sup_left
  · calc
      g (a • x + b • y) ≤ a • g x + b • g y := hg.right hx hy ha hb hab
      _ ≤ a • (f x ⊔ g x) + b • (f y ⊔ g y) := by gcongr <;> apply le_sup_right

/-- The pointwise minimum of concave functions is concave. -/
theorem ConcaveOn.inf (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) : ConcaveOn 𝕜 s (f ⊓ g) :=
  hf.dual.sup hg

/-- The pointwise maximum of strictly convex functions is strictly convex. -/
theorem StrictConvexOn.sup (hf : StrictConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f ⊔ g) :=
  ⟨hf.left, fun x hx y hy hxy a b ha hb hab =>
    max_lt
      (calc
        f (a • x + b • y) < a • f x + b • f y := hf.2 hx hy hxy ha hb hab
        _ ≤ a • (f x ⊔ g x) + b • (f y ⊔ g y) := by gcongr <;> apply le_sup_left)
      (calc
        g (a • x + b • y) < a • g x + b • g y := hg.2 hx hy hxy ha hb hab
        _ ≤ a • (f x ⊔ g x) + b • (f y ⊔ g y) := by gcongr <;> apply le_sup_right)⟩

/-- The pointwise minimum of strictly concave functions is strictly concave. -/
theorem StrictConcaveOn.inf (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f ⊓ g) :=
  hf.dual.sup hg

/-- A convex function on a segment is upper-bounded by the max of its endpoints. -/
theorem ConvexOn.le_on_segment' (hf : ConvexOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s) {a b : 𝕜}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : f (a • x + b • y) ≤ max (f x) (f y) :=
  calc
    f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx hy ha hb hab
    _ ≤ a • max (f x) (f y) + b • max (f x) (f y) := by
      gcongr
      · apply le_max_left
      · apply le_max_right
    _ = max (f x) (f y) := Convex.combo_self hab _

/-- A concave function on a segment is lower-bounded by the min of its endpoints. -/
theorem ConcaveOn.ge_on_segment' (hf : ConcaveOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : min (f x) (f y) ≤ f (a • x + b • y) :=
  hf.dual.le_on_segment' hx hy ha hb hab

/-- A convex function on a segment is upper-bounded by the max of its endpoints. -/
theorem ConvexOn.le_on_segment (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ [x -[𝕜] y]) : f z ≤ max (f x) (f y) :=
  let ⟨_, _, ha, hb, hab, hz⟩ := hz
  hz ▸ hf.le_on_segment' hx hy ha hb hab

/-- A concave function on a segment is lower-bounded by the min of its endpoints. -/
theorem ConcaveOn.ge_on_segment (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ [x -[𝕜] y]) : min (f x) (f y) ≤ f z :=
  hf.dual.le_on_segment hx hy hz

/-- A strictly convex function on an open segment is strictly upper-bounded by the max of its
endpoints. -/
theorem StrictConvexOn.lt_on_open_segment' (hf : StrictConvexOn 𝕜 s f) {x y : E} (hx : x ∈ s)
    (hy : y ∈ s) (hxy : x ≠ y) {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    f (a • x + b • y) < max (f x) (f y) :=
  calc
    f (a • x + b • y) < a • f x + b • f y := hf.2 hx hy hxy ha hb hab
    _ ≤ a • max (f x) (f y) + b • max (f x) (f y) := by
      gcongr
      · apply le_max_left
      · apply le_max_right
    _ = max (f x) (f y) := Convex.combo_self hab _

/-- A strictly concave function on an open segment is strictly lower-bounded by the min of its
endpoints. -/
theorem StrictConcaveOn.lt_on_open_segment' (hf : StrictConcaveOn 𝕜 s f) {x y : E} (hx : x ∈ s)
    (hy : y ∈ s) (hxy : x ≠ y) {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    min (f x) (f y) < f (a • x + b • y) :=
  hf.dual.lt_on_open_segment' hx hy hxy ha hb hab

/-- A strictly convex function on an open segment is strictly upper-bounded by the max of its
endpoints. -/
theorem StrictConvexOn.lt_on_openSegment (hf : StrictConvexOn 𝕜 s f) {x y z : E} (hx : x ∈ s)
    (hy : y ∈ s) (hxy : x ≠ y) (hz : z ∈ openSegment 𝕜 x y) : f z < max (f x) (f y) :=
  let ⟨_, _, ha, hb, hab, hz⟩ := hz
  hz ▸ hf.lt_on_open_segment' hx hy hxy ha hb hab

/-- A strictly concave function on an open segment is strictly lower-bounded by the min of its
endpoints. -/
theorem StrictConcaveOn.lt_on_openSegment (hf : StrictConcaveOn 𝕜 s f) {x y z : E} (hx : x ∈ s)
    (hy : y ∈ s) (hxy : x ≠ y) (hz : z ∈ openSegment 𝕜 x y) : min (f x) (f y) < f z :=
  hf.dual.lt_on_openSegment hx hy hxy hz

end LinearOrderedAddCommMonoid

section LinearOrderedCancelAddCommMonoid

variable [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]

section OrderedSMul

variable [SMul 𝕜 E] [Module 𝕜 β] [OrderedSMul 𝕜 β] {s : Set E} {f g : E → β}

theorem ConvexOn.le_left_of_right_le' (hf : ConvexOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    {a b : 𝕜} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) (hfy : f y ≤ f (a • x + b • y)) :
    f (a • x + b • y) ≤ f x :=
  le_of_not_gt fun h ↦ lt_irrefl (f (a • x + b • y)) <|
    calc
      f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx hy ha.le hb hab
      _ < a • f (a • x + b • y) + b • f (a • x + b • y) := add_lt_add_of_lt_of_le
          (smul_lt_smul_of_pos_left h ha) (smul_le_smul_of_nonneg_left hfy hb)
      _ = f (a • x + b • y) := Convex.combo_self hab _

theorem ConcaveOn.left_le_of_le_right' (hf : ConcaveOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    {a b : 𝕜} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) (hfy : f (a • x + b • y) ≤ f y) :
    f x ≤ f (a • x + b • y) :=
  hf.dual.le_left_of_right_le' hx hy ha hb hab hfy

theorem ConvexOn.le_right_of_left_le' (hf : ConvexOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x ∈ s)
    (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) (hfx : f x ≤ f (a • x + b • y)) :
    f (a • x + b • y) ≤ f y := by
  rw [add_comm] at hab hfx ⊢
  exact hf.le_left_of_right_le' hy hx hb ha hab hfx

theorem ConcaveOn.right_le_of_le_left' (hf : ConcaveOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x ∈ s)
    (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) (hfx : f (a • x + b • y) ≤ f x) :
    f y ≤ f (a • x + b • y) :=
  hf.dual.le_right_of_left_le' hx hy ha hb hab hfx

theorem ConvexOn.le_left_of_right_le (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ openSegment 𝕜 x y) (hyz : f y ≤ f z) : f z ≤ f x := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.le_left_of_right_le' hx hy ha hb.le hab hyz

theorem ConcaveOn.left_le_of_le_right (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ openSegment 𝕜 x y) (hyz : f z ≤ f y) : f x ≤ f z :=
  hf.dual.le_left_of_right_le hx hy hz hyz

theorem ConvexOn.le_right_of_left_le (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ openSegment 𝕜 x y) (hxz : f x ≤ f z) : f z ≤ f y := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.le_right_of_left_le' hx hy ha.le hb hab hxz

theorem ConcaveOn.right_le_of_le_left (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ openSegment 𝕜 x y) (hxz : f z ≤ f x) : f y ≤ f z :=
  hf.dual.le_right_of_left_le hx hy hz hxz

end OrderedSMul

section Module

variable [Module 𝕜 E] [Module 𝕜 β] [OrderedSMul 𝕜 β] {s : Set E} {f g : E → β}

/- The following lemmas don't require `Module 𝕜 E` if you add the hypothesis `x ≠ y`. At the time of
the writing, we decided the resulting lemmas wouldn't be useful. Feel free to reintroduce them. -/
theorem ConvexOn.lt_left_of_right_lt' (hf : ConvexOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfy : f y < f (a • x + b • y)) :
    f (a • x + b • y) < f x :=
  not_le.1 fun h ↦ lt_irrefl (f (a • x + b • y)) <|
    calc
      f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx hy ha.le hb.le hab
      _ < a • f (a • x + b • y) + b • f (a • x + b • y) := add_lt_add_of_le_of_lt
          (smul_le_smul_of_nonneg_left h ha.le) (smul_lt_smul_of_pos_left hfy hb)
      _ = f (a • x + b • y) := Convex.combo_self hab _

theorem ConcaveOn.left_lt_of_lt_right' (hf : ConcaveOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfy : f (a • x + b • y) < f y) :
    f x < f (a • x + b • y) :=
  hf.dual.lt_left_of_right_lt' hx hy ha hb hab hfy

theorem ConvexOn.lt_right_of_left_lt' (hf : ConvexOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x ∈ s)
    (hy : y ∈ s) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfx : f x < f (a • x + b • y)) :
    f (a • x + b • y) < f y := by
  rw [add_comm] at hab hfx ⊢
  exact hf.lt_left_of_right_lt' hy hx hb ha hab hfx

theorem ConcaveOn.lt_right_of_left_lt' (hf : ConcaveOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x ∈ s)
    (hy : y ∈ s) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfx : f (a • x + b • y) < f x) :
    f y < f (a • x + b • y) :=
  hf.dual.lt_right_of_left_lt' hx hy ha hb hab hfx

theorem ConvexOn.lt_left_of_right_lt (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ openSegment 𝕜 x y) (hyz : f y < f z) : f z < f x := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.lt_left_of_right_lt' hx hy ha hb hab hyz

theorem ConcaveOn.left_lt_of_lt_right (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ openSegment 𝕜 x y) (hyz : f z < f y) : f x < f z :=
  hf.dual.lt_left_of_right_lt hx hy hz hyz

theorem ConvexOn.lt_right_of_left_lt (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ openSegment 𝕜 x y) (hxz : f x < f z) : f z < f y := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.lt_right_of_left_lt' hx hy ha hb hab hxz

theorem ConcaveOn.lt_right_of_left_lt (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ openSegment 𝕜 x y) (hxz : f z < f x) : f y < f z :=
  hf.dual.lt_right_of_left_lt hx hy hz hxz

end Module

end LinearOrderedCancelAddCommMonoid

section OrderedAddCommGroup

variable [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [SMul 𝕜 E] [Module 𝕜 β]
  {s : Set E} {f g : E → β}

/-- A function `-f` is convex iff `f` is concave. -/
@[simp]
theorem neg_convexOn_iff : ConvexOn 𝕜 s (-f) ↔ ConcaveOn 𝕜 s f := by
  constructor
  · rintro ⟨hconv, h⟩
    refine ⟨hconv, fun x hx y hy a b ha hb hab => ?_⟩
    simp? [neg_apply, neg_le, add_comm] at h says
      simp only [Pi.neg_apply, smul_neg, le_add_neg_iff_add_le, add_comm,
        add_neg_le_iff_le_add] at h
    exact h hx hy ha hb hab
  · rintro ⟨hconv, h⟩
    refine ⟨hconv, fun x hx y hy a b ha hb hab => ?_⟩
    rw [← neg_le_neg_iff]
    simp_rw [neg_add, Pi.neg_apply, smul_neg, neg_neg]
    exact h hx hy ha hb hab

/-- A function `-f` is concave iff `f` is convex. -/
@[simp]
theorem neg_concaveOn_iff : ConcaveOn 𝕜 s (-f) ↔ ConvexOn 𝕜 s f := by
  rw [← neg_convexOn_iff, neg_neg f]

/-- A function `-f` is strictly convex iff `f` is strictly concave. -/
@[simp]
theorem neg_strictConvexOn_iff : StrictConvexOn 𝕜 s (-f) ↔ StrictConcaveOn 𝕜 s f := by
  constructor
  · rintro ⟨hconv, h⟩
    refine ⟨hconv, fun x hx y hy hxy a b ha hb hab => ?_⟩
    simp only [ne_eq, Pi.neg_apply, smul_neg, lt_add_neg_iff_add_lt, add_comm,
      add_neg_lt_iff_lt_add] at h
    exact h hx hy hxy ha hb hab
  · rintro ⟨hconv, h⟩
    refine ⟨hconv, fun x hx y hy hxy a b ha hb hab => ?_⟩
    rw [← neg_lt_neg_iff]
    simp_rw [neg_add, Pi.neg_apply, smul_neg, neg_neg]
    exact h hx hy hxy ha hb hab

/-- A function `-f` is strictly concave iff `f` is strictly convex. -/
@[simp]
theorem neg_strictConcaveOn_iff : StrictConcaveOn 𝕜 s (-f) ↔ StrictConvexOn 𝕜 s f := by
  rw [← neg_strictConvexOn_iff, neg_neg f]

alias ⟨_, ConcaveOn.neg⟩ := neg_convexOn_iff

alias ⟨_, ConvexOn.neg⟩ := neg_concaveOn_iff

alias ⟨_, StrictConcaveOn.neg⟩ := neg_strictConvexOn_iff

alias ⟨_, StrictConvexOn.neg⟩ := neg_strictConcaveOn_iff

theorem ConvexOn.sub (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) : ConvexOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

theorem ConcaveOn.sub (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : ConcaveOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

theorem StrictConvexOn.sub (hf : StrictConvexOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

theorem StrictConcaveOn.sub (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

theorem ConvexOn.sub_strictConcaveOn (hf : ConvexOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add_strictConvexOn hg.neg

theorem ConcaveOn.sub_strictConvexOn (hf : ConcaveOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add_strictConcaveOn hg.neg

theorem StrictConvexOn.sub_concaveOn (hf : StrictConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add_convexOn hg.neg

theorem StrictConcaveOn.sub_convexOn (hf : StrictConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add_concaveOn hg.neg

end OrderedAddCommGroup

end AddCommMonoid

section AddCancelCommMonoid

variable [AddCancelCommMonoid E] [AddCommMonoid β] [PartialOrder β] [Module 𝕜 E] [SMul 𝕜 β]
  {s : Set E}
  {f : E → β}

/-- Right translation preserves strict convexity. -/
theorem StrictConvexOn.translate_right (hf : StrictConvexOn 𝕜 s f) (c : E) :
    StrictConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => c + z) :=
  ⟨hf.1.translate_preimage_right _, fun x hx y hy hxy a b ha hb hab =>
    calc
      f (c + (a • x + b • y)) = f (a • (c + x) + b • (c + y)) := by
        rw [smul_add, smul_add, add_add_add_comm, Convex.combo_self hab]
      _ < a • f (c + x) + b • f (c + y) := hf.2 hx hy ((add_right_injective c).ne hxy) ha hb hab⟩

/-- Right translation preserves strict concavity. -/
theorem StrictConcaveOn.translate_right (hf : StrictConcaveOn 𝕜 s f) (c : E) :
    StrictConcaveOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => c + z) :=
  hf.dual.translate_right _

/-- Left translation preserves strict convexity. -/
theorem StrictConvexOn.translate_left (hf : StrictConvexOn 𝕜 s f) (c : E) :
    StrictConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => z + c) := by
  simpa only [add_comm] using hf.translate_right c

/-- Left translation preserves strict concavity. -/
theorem StrictConcaveOn.translate_left (hf : StrictConcaveOn 𝕜 s f) (c : E) :
    StrictConcaveOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => z + c) := by
  simpa only [add_comm] using hf.translate_right c

end AddCancelCommMonoid

end OrderedSemiring

section OrderedCommSemiring

variable [CommSemiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]

section OrderedAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β]

section Module

variable [SMul 𝕜 E] [Module 𝕜 β] [OrderedSMul 𝕜 β] {s : Set E} {f : E → β}

theorem ConvexOn.smul {c : 𝕜} (hc : 0 ≤ c) (hf : ConvexOn 𝕜 s f) : ConvexOn 𝕜 s fun x => c • f x :=
  ⟨hf.1, fun x hx y hy a b ha hb hab =>
    calc
      c • f (a • x + b • y) ≤ c • (a • f x + b • f y) :=
        smul_le_smul_of_nonneg_left (hf.2 hx hy ha hb hab) hc
      _ = a • c • f x + b • c • f y := by rw [smul_add, smul_comm c, smul_comm c]⟩

theorem ConcaveOn.smul {c : 𝕜} (hc : 0 ≤ c) (hf : ConcaveOn 𝕜 s f) :
    ConcaveOn 𝕜 s fun x => c • f x :=
  hf.dual.smul hc

end Module

end OrderedAddCommMonoid

end OrderedCommSemiring

section OrderedRing

variable [Field 𝕜] [LinearOrder 𝕜] [AddCommGroup E] [AddCommGroup F]

section OrderedAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β]

section Module

variable [Module 𝕜 E] [Module 𝕜 F] [SMul 𝕜 β]

/-- If a function is convex on `s`, it remains convex when precomposed by an affine map. -/
theorem ConvexOn.comp_affineMap {f : F → β} (g : E →ᵃ[𝕜] F) {s : Set F} (hf : ConvexOn 𝕜 s f) :
    ConvexOn 𝕜 (g ⁻¹' s) (f ∘ g) :=
  ⟨hf.1.affine_preimage _, fun x hx y hy a b ha hb hab =>
    calc
      (f ∘ g) (a • x + b • y) = f (g (a • x + b • y)) := rfl
      _ = f (a • g x + b • g y) := by rw [Convex.combo_affine_apply hab]
      _ ≤ a • f (g x) + b • f (g y) := hf.2 hx hy ha hb hab⟩

/-- If a function is concave on `s`, it remains concave when precomposed by an affine map. -/
theorem ConcaveOn.comp_affineMap {f : F → β} (g : E →ᵃ[𝕜] F) {s : Set F} (hf : ConcaveOn 𝕜 s f) :
    ConcaveOn 𝕜 (g ⁻¹' s) (f ∘ g) :=
  hf.dual.comp_affineMap g

end Module

end OrderedAddCommMonoid

end OrderedRing

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommMonoid E]

section OrderedAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β]

section SMul

variable [SMul 𝕜 E] [SMul 𝕜 β] {s : Set E}

theorem convexOn_iff_div {f : E → β} :
    ConvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → 0 < a + b →
        f ((a / (a + b)) • x + (b / (a + b)) • y) ≤ (a / (a + b)) • f x + (b / (a + b)) • f y :=
  and_congr Iff.rfl ⟨by
    intro h x hx y hy a b ha hb hab
    apply h hx hy (div_nonneg ha hab.le) (div_nonneg hb hab.le)
    rw [← add_div, div_self hab.ne'], by
    intro h x hx y hy a b ha hb hab
    simpa [hab, zero_lt_one] using h hx hy ha hb⟩

theorem concaveOn_iff_div {f : E → β} :
    ConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → 0 < a + b →
        (a / (a + b)) • f x + (b / (a + b)) • f y ≤ f ((a / (a + b)) • x + (b / (a + b)) • y) :=
  convexOn_iff_div (β := βᵒᵈ)

theorem strictConvexOn_iff_div {f : E → β} :
    StrictConvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b →
        f ((a / (a + b)) • x + (b / (a + b)) • y) < (a / (a + b)) • f x + (b / (a + b)) • f y :=
  and_congr Iff.rfl ⟨by
    intro h x hx y hy hxy a b ha hb
    have hab := add_pos ha hb
    apply h hx hy hxy (div_pos ha hab) (div_pos hb hab)
    rw [← add_div, div_self hab.ne'], by
    intro h x hx y hy hxy a b ha hb hab
    simpa [hab, zero_lt_one] using h hx hy hxy ha hb⟩

theorem strictConcaveOn_iff_div {f : E → β} :
    StrictConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b →
        (a / (a + b)) • f x + (b / (a + b)) • f y < f ((a / (a + b)) • x + (b / (a + b)) • y) :=
  strictConvexOn_iff_div (β := βᵒᵈ)

end SMul

end OrderedAddCommMonoid

end LinearOrderedField

section OrderIso

variable [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid α] [PartialOrder α] [SMul 𝕜 α]
  [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]

theorem OrderIso.strictConvexOn_symm (f : α ≃o β) (hf : StrictConcaveOn 𝕜 univ f) :
    StrictConvexOn 𝕜 univ f.symm := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  obtain ⟨x', hx''⟩ := f.surjective.exists.mp ⟨x, rfl⟩
  obtain ⟨y', hy''⟩ := f.surjective.exists.mp ⟨y, rfl⟩
  have hxy' : x' ≠ y' := by rw [← f.injective.ne_iff, ← hx'', ← hy'']; exact hxy
  simp only [hx'', hy'', OrderIso.symm_apply_apply, gt_iff_lt]
  rw [← f.lt_iff_lt, OrderIso.apply_symm_apply]
  exact hf.2 (by simp : x' ∈ univ) (by simp : y' ∈ univ) hxy' ha hb hab

theorem OrderIso.convexOn_symm (f : α ≃o β) (hf : ConcaveOn 𝕜 univ f) :
    ConvexOn 𝕜 univ f.symm := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨x', hx''⟩ := f.surjective.exists.mp ⟨x, rfl⟩
  obtain ⟨y', hy''⟩ := f.surjective.exists.mp ⟨y, rfl⟩
  simp only [hx'', hy'', OrderIso.symm_apply_apply]
  rw [← f.le_iff_le, OrderIso.apply_symm_apply]
  exact hf.2 (by simp : x' ∈ univ) (by simp : y' ∈ univ) ha hb hab

theorem OrderIso.strictConcaveOn_symm (f : α ≃o β) (hf : StrictConvexOn 𝕜 univ f) :
    StrictConcaveOn 𝕜 univ f.symm := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  obtain ⟨x', hx''⟩ := f.surjective.exists.mp ⟨x, rfl⟩
  obtain ⟨y', hy''⟩ := f.surjective.exists.mp ⟨y, rfl⟩
  have hxy' : x' ≠ y' := by rw [← f.injective.ne_iff, ← hx'', ← hy'']; exact hxy
  simp only [hx'', hy'', OrderIso.symm_apply_apply, gt_iff_lt]
  rw [← f.lt_iff_lt, OrderIso.apply_symm_apply]
  exact hf.2 (by simp : x' ∈ univ) (by simp : y' ∈ univ) hxy' ha hb hab

theorem OrderIso.concaveOn_symm (f : α ≃o β) (hf : ConvexOn 𝕜 univ f) :
    ConcaveOn 𝕜 univ f.symm := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨x', hx''⟩ := f.surjective.exists.mp ⟨x, rfl⟩
  obtain ⟨y', hy''⟩ := f.surjective.exists.mp ⟨y, rfl⟩
  simp only [hx'', hy'', OrderIso.symm_apply_apply]
  rw [← f.le_iff_le, OrderIso.apply_symm_apply]
  exact hf.2 (by simp : x' ∈ univ) (by simp : y' ∈ univ) ha hb hab

end OrderIso


section LinearOrderedField
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

section OrderedAddCommMonoid
variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
  [AddCommMonoid E] [SMul 𝕜 E] [Module 𝕜 β] [OrderedSMul 𝕜 β]
  {f : E → β} {s : Set E} {x y : E}

/-- A strictly convex function admits at most one global minimum. -/
lemma StrictConvexOn.eq_of_isMinOn (hf : StrictConvexOn 𝕜 s f) (hfx : IsMinOn f s x)
    (hfy : IsMinOn f s y) (hx : x ∈ s) (hy : y ∈ s) : x = y := by
  by_contra hxy
  let z := (2 : 𝕜)⁻¹ • x + (2 : 𝕜)⁻¹ • y
  have hz : z ∈ s := hf.1 hx hy (by simp) (by simp) <| by norm_num
  refine lt_irrefl (f z) ?_
  calc
    f z < _ := hf.2 hx hy hxy (by norm_num) (by norm_num) <| by norm_num
    _ ≤ (2 : 𝕜)⁻¹ • f z + (2 : 𝕜)⁻¹ • f z := by gcongr; exacts [hfx hz, hfy hz]
    _ = f z := by rw [← _root_.add_smul]; norm_num

/-- A strictly concave function admits at most one global maximum. -/
lemma StrictConcaveOn.eq_of_isMaxOn (hf : StrictConcaveOn 𝕜 s f) (hfx : IsMaxOn f s x)
    (hfy : IsMaxOn f s y) (hx : x ∈ s) (hy : y ∈ s) : x = y :=
  hf.dual.eq_of_isMinOn hfx hfy hx hy

end OrderedAddCommMonoid

section LinearOrderedCancelAddCommMonoid
variable [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]
  [Module 𝕜 β] [OrderedSMul 𝕜 β]
  {x y z : 𝕜} {s : Set 𝕜} {f : 𝕜 → β}

theorem ConvexOn.le_right_of_left_le'' (hf : ConvexOn 𝕜 s f) (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y)
    (hyz : y ≤ z) (h : f x ≤ f y) : f y ≤ f z :=
  hyz.eq_or_lt.elim (fun hyz => (congr_arg f hyz).le) fun hyz =>
    hf.le_right_of_left_le hx hz (Ioo_subset_openSegment ⟨hxy, hyz⟩) h

theorem ConvexOn.le_left_of_right_le'' (hf : ConvexOn 𝕜 s f) (hx : x ∈ s) (hz : z ∈ s) (hxy : x ≤ y)
    (hyz : y < z) (h : f z ≤ f y) : f y ≤ f x :=
  hxy.eq_or_lt.elim (fun hxy => (congr_arg f hxy).ge) fun hxy =>
    hf.le_left_of_right_le hx hz (Ioo_subset_openSegment ⟨hxy, hyz⟩) h

theorem ConcaveOn.right_le_of_le_left'' (hf : ConcaveOn 𝕜 s f) (hx : x ∈ s) (hz : z ∈ s)
    (hxy : x < y) (hyz : y ≤ z) (h : f y ≤ f x) : f z ≤ f y :=
  hf.dual.le_right_of_left_le'' hx hz hxy hyz h

theorem ConcaveOn.left_le_of_le_right'' (hf : ConcaveOn 𝕜 s f) (hx : x ∈ s) (hz : z ∈ s)
    (hxy : x ≤ y) (hyz : y < z) (h : f y ≤ f z) : f x ≤ f y :=
  hf.dual.le_left_of_right_le'' hx hz hxy hyz h

end LinearOrderedCancelAddCommMonoid
end LinearOrderedField
