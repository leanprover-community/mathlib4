/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Johannes Hölzl

! This file was ported from Lean 3 source module order.ord_continuous
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.ConditionallyCompleteLattice.Basic
import Mathbin.Order.RelIso.Basic

/-!
# Order continuity

We say that a function is *left order continuous* if it sends all least upper bounds
to least upper bounds. The order dual notion is called *right order continuity*.

For monotone functions `ℝ → ℝ` these notions correspond to the usual left and right continuity.

We prove some basic lemmas (`map_sup`, `map_Sup` etc) and prove that an `rel_iso` is both left
and right order continuous.
-/


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

open Function OrderDual Set

/-!
### Definitions
-/


/-- A function `f` between preorders is left order continuous if it preserves all suprema.  We
define it using `is_lub` instead of `Sup` so that the proof works both for complete lattices and
conditionally complete lattices. -/
def LeftOrdContinuous [Preorder α] [Preorder β] (f : α → β) :=
  ∀ ⦃s : Set α⦄ ⦃x⦄, IsLUB s x → IsLUB (f '' s) (f x)
#align left_ord_continuous LeftOrdContinuous

/-- A function `f` between preorders is right order continuous if it preserves all infima.  We
define it using `is_glb` instead of `Inf` so that the proof works both for complete lattices and
conditionally complete lattices. -/
def RightOrdContinuous [Preorder α] [Preorder β] (f : α → β) :=
  ∀ ⦃s : Set α⦄ ⦃x⦄, IsGLB s x → IsGLB (f '' s) (f x)
#align right_ord_continuous RightOrdContinuous

namespace LeftOrdContinuous

section Preorder

variable (α) [Preorder α] [Preorder β] [Preorder γ] {g : β → γ} {f : α → β}

protected theorem id : LeftOrdContinuous (id : α → α) := fun s x h => by
  simpa only [image_id] using h
#align left_ord_continuous.id LeftOrdContinuous.id

variable {α}

protected theorem order_dual : LeftOrdContinuous f → RightOrdContinuous (to_dual ∘ f ∘ of_dual) :=
  id
#align left_ord_continuous.order_dual LeftOrdContinuous.order_dual

theorem map_is_greatest (hf : LeftOrdContinuous f) {s : Set α} {x : α} (h : IsGreatest s x) :
    IsGreatest (f '' s) (f x) :=
  ⟨mem_image_of_mem f h.1, (hf h.IsLub).1⟩
#align left_ord_continuous.map_is_greatest LeftOrdContinuous.map_is_greatest

theorem mono (hf : LeftOrdContinuous f) : Monotone f := fun a₁ a₂ h =>
  have : IsGreatest {a₁, a₂} a₂ := ⟨Or.inr rfl, by simp [*]⟩
  (hf.map_is_greatest this).2 <| mem_image_of_mem _ (Or.inl rfl)
#align left_ord_continuous.mono LeftOrdContinuous.mono

theorem comp (hg : LeftOrdContinuous g) (hf : LeftOrdContinuous f) : LeftOrdContinuous (g ∘ f) :=
  fun s x h => by simpa only [image_image] using hg (hf h)
#align left_ord_continuous.comp LeftOrdContinuous.comp

protected theorem iterate {f : α → α} (hf : LeftOrdContinuous f) (n : ℕ) :
    LeftOrdContinuous (f^[n]) :=
  (Nat.recOn n (LeftOrdContinuous.id α)) fun n ihn => ihn.comp hf
#align left_ord_continuous.iterate LeftOrdContinuous.iterate

end Preorder

section SemilatticeSup

variable [SemilatticeSup α] [SemilatticeSup β] {f : α → β}

theorem map_sup (hf : LeftOrdContinuous f) (x y : α) : f (x ⊔ y) = f x ⊔ f y :=
  (hf isLUB_pair).unique <| by simp only [image_pair, isLUB_pair]
#align left_ord_continuous.map_sup LeftOrdContinuous.map_sup

theorem le_iff (hf : LeftOrdContinuous f) (h : Injective f) {x y} : f x ≤ f y ↔ x ≤ y := by
  simp only [← sup_eq_right, ← hf.map_sup, h.eq_iff]
#align left_ord_continuous.le_iff LeftOrdContinuous.le_iff

theorem lt_iff (hf : LeftOrdContinuous f) (h : Injective f) {x y} : f x < f y ↔ x < y := by
  simp only [lt_iff_le_not_le, hf.le_iff h]
#align left_ord_continuous.lt_iff LeftOrdContinuous.lt_iff

variable (f)

/-- Convert an injective left order continuous function to an order embedding. -/
def toOrderEmbedding (hf : LeftOrdContinuous f) (h : Injective f) : α ↪o β :=
  ⟨⟨f, h⟩, fun x y => hf.le_iff h⟩
#align left_ord_continuous.to_order_embedding LeftOrdContinuous.toOrderEmbedding

variable {f}

@[simp]
theorem coe_to_order_embedding (hf : LeftOrdContinuous f) (h : Injective f) :
    ⇑(hf.toOrderEmbedding f h) = f :=
  rfl
#align left_ord_continuous.coe_to_order_embedding LeftOrdContinuous.coe_to_order_embedding

end SemilatticeSup

section CompleteLattice

variable [CompleteLattice α] [CompleteLattice β] {f : α → β}

theorem map_Sup' (hf : LeftOrdContinuous f) (s : Set α) : f (supₛ s) = supₛ (f '' s) :=
  (hf <| is_lub_Sup s).Sup_eq.symm
#align left_ord_continuous.map_Sup' LeftOrdContinuous.map_Sup'

theorem map_Sup (hf : LeftOrdContinuous f) (s : Set α) : f (supₛ s) = ⨆ x ∈ s, f x := by
  rw [hf.map_Sup', supₛ_image]
#align left_ord_continuous.map_Sup LeftOrdContinuous.map_Sup

theorem map_supr (hf : LeftOrdContinuous f) (g : ι → α) : f (⨆ i, g i) = ⨆ i, f (g i) := by
  simp only [supᵢ, hf.map_Sup', ← range_comp]
#align left_ord_continuous.map_supr LeftOrdContinuous.map_supr

end CompleteLattice

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι] {f : α → β}

theorem map_cSup (hf : LeftOrdContinuous f) {s : Set α} (sne : s.Nonempty) (sbdd : BddAbove s) :
    f (supₛ s) = supₛ (f '' s) :=
  ((hf <| is_lub_cSup sne sbdd).cSup_eq <| sne.image f).symm
#align left_ord_continuous.map_cSup LeftOrdContinuous.map_cSup

theorem map_csupr (hf : LeftOrdContinuous f) {g : ι → α} (hg : BddAbove (range g)) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by
  simp only [supᵢ, hf.map_cSup (range_nonempty _) hg, ← range_comp]
#align left_ord_continuous.map_csupr LeftOrdContinuous.map_csupr

end ConditionallyCompleteLattice

end LeftOrdContinuous

namespace RightOrdContinuous

section Preorder

variable (α) [Preorder α] [Preorder β] [Preorder γ] {g : β → γ} {f : α → β}

protected theorem id : RightOrdContinuous (id : α → α) := fun s x h => by
  simpa only [image_id] using h
#align right_ord_continuous.id RightOrdContinuous.id

variable {α}

protected theorem order_dual : RightOrdContinuous f → LeftOrdContinuous (to_dual ∘ f ∘ of_dual) :=
  id
#align right_ord_continuous.order_dual RightOrdContinuous.order_dual

theorem map_is_least (hf : RightOrdContinuous f) {s : Set α} {x : α} (h : IsLeast s x) :
    IsLeast (f '' s) (f x) :=
  hf.OrderDual.map_is_greatest h
#align right_ord_continuous.map_is_least RightOrdContinuous.map_is_least

theorem mono (hf : RightOrdContinuous f) : Monotone f :=
  hf.OrderDual.mono.dual
#align right_ord_continuous.mono RightOrdContinuous.mono

theorem comp (hg : RightOrdContinuous g) (hf : RightOrdContinuous f) : RightOrdContinuous (g ∘ f) :=
  hg.OrderDual.comp hf.OrderDual
#align right_ord_continuous.comp RightOrdContinuous.comp

protected theorem iterate {f : α → α} (hf : RightOrdContinuous f) (n : ℕ) :
    RightOrdContinuous (f^[n]) :=
  hf.OrderDual.iterate n
#align right_ord_continuous.iterate RightOrdContinuous.iterate

end Preorder

section SemilatticeInf

variable [SemilatticeInf α] [SemilatticeInf β] {f : α → β}

theorem map_inf (hf : RightOrdContinuous f) (x y : α) : f (x ⊓ y) = f x ⊓ f y :=
  hf.OrderDual.map_sup x y
#align right_ord_continuous.map_inf RightOrdContinuous.map_inf

theorem le_iff (hf : RightOrdContinuous f) (h : Injective f) {x y} : f x ≤ f y ↔ x ≤ y :=
  hf.OrderDual.le_iff h
#align right_ord_continuous.le_iff RightOrdContinuous.le_iff

theorem lt_iff (hf : RightOrdContinuous f) (h : Injective f) {x y} : f x < f y ↔ x < y :=
  hf.OrderDual.lt_iff h
#align right_ord_continuous.lt_iff RightOrdContinuous.lt_iff

variable (f)

/-- Convert an injective left order continuous function to a `order_embedding`. -/
def toOrderEmbedding (hf : RightOrdContinuous f) (h : Injective f) : α ↪o β :=
  ⟨⟨f, h⟩, fun x y => hf.le_iff h⟩
#align right_ord_continuous.to_order_embedding RightOrdContinuous.toOrderEmbedding

variable {f}

@[simp]
theorem coe_to_order_embedding (hf : RightOrdContinuous f) (h : Injective f) :
    ⇑(hf.toOrderEmbedding f h) = f :=
  rfl
#align right_ord_continuous.coe_to_order_embedding RightOrdContinuous.coe_to_order_embedding

end SemilatticeInf

section CompleteLattice

variable [CompleteLattice α] [CompleteLattice β] {f : α → β}

theorem map_Inf' (hf : RightOrdContinuous f) (s : Set α) : f (infₛ s) = infₛ (f '' s) :=
  hf.OrderDual.map_Sup' s
#align right_ord_continuous.map_Inf' RightOrdContinuous.map_Inf'

theorem map_Inf (hf : RightOrdContinuous f) (s : Set α) : f (infₛ s) = ⨅ x ∈ s, f x :=
  hf.OrderDual.map_Sup s
#align right_ord_continuous.map_Inf RightOrdContinuous.map_Inf

theorem map_infi (hf : RightOrdContinuous f) (g : ι → α) : f (⨅ i, g i) = ⨅ i, f (g i) :=
  hf.OrderDual.map_supr g
#align right_ord_continuous.map_infi RightOrdContinuous.map_infi

end CompleteLattice

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι] {f : α → β}

theorem map_cInf (hf : RightOrdContinuous f) {s : Set α} (sne : s.Nonempty) (sbdd : BddBelow s) :
    f (infₛ s) = infₛ (f '' s) :=
  hf.OrderDual.map_cSup sne sbdd
#align right_ord_continuous.map_cInf RightOrdContinuous.map_cInf

theorem map_cinfi (hf : RightOrdContinuous f) {g : ι → α} (hg : BddBelow (range g)) :
    f (⨅ i, g i) = ⨅ i, f (g i) :=
  hf.OrderDual.map_csupr hg
#align right_ord_continuous.map_cinfi RightOrdContinuous.map_cinfi

end ConditionallyCompleteLattice

end RightOrdContinuous

namespace OrderIso

section Preorder

variable [Preorder α] [Preorder β] (e : α ≃o β) {s : Set α} {x : α}

protected theorem left_ord_continuous : LeftOrdContinuous e := fun s x hx =>
  ⟨Monotone.mem_upperBounds_image (fun x y => e.map_rel_iff.2) hx.1, fun y hy =>
    e.rel_symm_apply.1 <|
      (isLUB_le_iff hx).2 fun x' hx' => e.rel_symm_apply.2 <| hy <| mem_image_of_mem _ hx'⟩
#align order_iso.left_ord_continuous OrderIso.left_ord_continuous

protected theorem right_ord_continuous : RightOrdContinuous e :=
  OrderIso.left_ord_continuous e.dual
#align order_iso.right_ord_continuous OrderIso.right_ord_continuous

end Preorder

end OrderIso

