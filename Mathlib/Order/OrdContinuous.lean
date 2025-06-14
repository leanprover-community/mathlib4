/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Johannes Hölzl
-/
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.RelIso.Basic

/-!
# Order continuity

We say that a function is *left order continuous* if it sends all least upper bounds
to least upper bounds. The order dual notion is called *right order continuity*.

For monotone functions `ℝ → ℝ` these notions correspond to the usual left and right continuity.

We prove some basic lemmas (`map_sup`, `map_sSup` etc) and prove that a `RelIso` is both left
and right order continuous.
-/


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

open Function OrderDual Set

/-!
### Definitions
-/


/-- A function `f` between preorders is left order continuous if it preserves all suprema.  We
define it using `IsLUB` instead of `sSup` so that the proof works both for complete lattices and
conditionally complete lattices. -/
def LeftOrdContinuous [Preorder α] [Preorder β] (f : α → β) :=
  ∀ ⦃s : Set α⦄ ⦃x⦄, IsLUB s x → IsLUB (f '' s) (f x)

/-- A function `f` between preorders is right order continuous if it preserves all infima.  We
define it using `IsGLB` instead of `sInf` so that the proof works both for complete lattices and
conditionally complete lattices. -/
def RightOrdContinuous [Preorder α] [Preorder β] (f : α → β) :=
  ∀ ⦃s : Set α⦄ ⦃x⦄, IsGLB s x → IsGLB (f '' s) (f x)

namespace LeftOrdContinuous

section Preorder

variable (α) [Preorder α] [Preorder β] [Preorder γ] {g : β → γ} {f : α → β}

protected theorem id : LeftOrdContinuous (id : α → α) := fun s x h => by
  simpa only [image_id] using h

variable {α}

protected theorem rightOrdContinuous_dual :
    LeftOrdContinuous f → RightOrdContinuous (toDual ∘ f ∘ ofDual) :=
  id

@[deprecated (since := "2025-04-08")]
protected alias order_dual := LeftOrdContinuous.rightOrdContinuous_dual

theorem map_isGreatest (hf : LeftOrdContinuous f) {s : Set α} {x : α} (h : IsGreatest s x) :
    IsGreatest (f '' s) (f x) :=
  ⟨mem_image_of_mem f h.1, (hf h.isLUB).1⟩

theorem mono (hf : LeftOrdContinuous f) : Monotone f := fun a₁ a₂ h =>
  have : IsGreatest {a₁, a₂} a₂ := ⟨Or.inr rfl, by simp [*]⟩
  (hf.map_isGreatest this).2 <| mem_image_of_mem _ (Or.inl rfl)

theorem comp (hg : LeftOrdContinuous g) (hf : LeftOrdContinuous f) : LeftOrdContinuous (g ∘ f) :=
  fun s x h => by simpa only [image_image] using hg (hf h)

protected theorem iterate {f : α → α} (hf : LeftOrdContinuous f) (n : ℕ) :
    LeftOrdContinuous f^[n] :=
  match n with
  | 0 => LeftOrdContinuous.id α
  | (n + 1) => (LeftOrdContinuous.iterate hf n).comp hf

end Preorder

section SemilatticeSup

variable [SemilatticeSup α] [SemilatticeSup β] {f : α → β}

theorem map_sup (hf : LeftOrdContinuous f) (x y : α) : f (x ⊔ y) = f x ⊔ f y :=
  (hf isLUB_pair).unique <| by simp only [image_pair, isLUB_pair]

theorem le_iff (hf : LeftOrdContinuous f) (h : Injective f) {x y} : f x ≤ f y ↔ x ≤ y := by
  simp only [← sup_eq_right, ← hf.map_sup, h.eq_iff]

theorem lt_iff (hf : LeftOrdContinuous f) (h : Injective f) {x y} : f x < f y ↔ x < y := by
  simp only [lt_iff_le_not_ge, hf.le_iff h]

variable (f)

/-- Convert an injective left order continuous function to an order embedding. -/
def toOrderEmbedding (hf : LeftOrdContinuous f) (h : Injective f) : α ↪o β :=
  ⟨⟨f, h⟩, hf.le_iff h⟩

variable {f}

@[simp]
theorem coe_toOrderEmbedding (hf : LeftOrdContinuous f) (h : Injective f) :
    ⇑(hf.toOrderEmbedding f h) = f :=
  rfl

end SemilatticeSup

section CompleteLattice

variable [CompleteLattice α] [CompleteLattice β] {f : α → β}

theorem map_sSup' (hf : LeftOrdContinuous f) (s : Set α) : f (sSup s) = sSup (f '' s) :=
  (hf <| isLUB_sSup s).sSup_eq.symm

theorem map_sSup (hf : LeftOrdContinuous f) (s : Set α) : f (sSup s) = ⨆ x ∈ s, f x := by
  rw [hf.map_sSup', sSup_image]

theorem map_iSup (hf : LeftOrdContinuous f) (g : ι → α) : f (⨆ i, g i) = ⨆ i, f (g i) := by
  simp only [iSup, hf.map_sSup', ← range_comp]
  rfl

end CompleteLattice

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι] {f : α → β}

theorem map_csSup (hf : LeftOrdContinuous f) {s : Set α} (sne : s.Nonempty) (sbdd : BddAbove s) :
    f (sSup s) = sSup (f '' s) :=
  ((hf <| isLUB_csSup sne sbdd).csSup_eq <| sne.image f).symm

theorem map_ciSup (hf : LeftOrdContinuous f) {g : ι → α} (hg : BddAbove (range g)) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by
  simp only [iSup, hf.map_csSup (range_nonempty _) hg, ← range_comp]
  rfl

end ConditionallyCompleteLattice

end LeftOrdContinuous

namespace RightOrdContinuous

section Preorder

variable (α) [Preorder α] [Preorder β] [Preorder γ] {g : β → γ} {f : α → β}

protected theorem id : RightOrdContinuous (id : α → α) := fun s x h => by
  simpa only [image_id] using h

variable {α}

protected theorem orderDual : RightOrdContinuous f → LeftOrdContinuous (toDual ∘ f ∘ ofDual) :=
  id

theorem map_isLeast (hf : RightOrdContinuous f) {s : Set α} {x : α} (h : IsLeast s x) :
    IsLeast (f '' s) (f x) :=
  hf.orderDual.map_isGreatest h

theorem mono (hf : RightOrdContinuous f) : Monotone f :=
  hf.orderDual.mono.dual

theorem comp (hg : RightOrdContinuous g) (hf : RightOrdContinuous f) : RightOrdContinuous (g ∘ f) :=
  hg.orderDual.comp hf.orderDual

protected theorem iterate {f : α → α} (hf : RightOrdContinuous f) (n : ℕ) :
    RightOrdContinuous f^[n] :=
  hf.orderDual.iterate n

end Preorder

section SemilatticeInf

variable [SemilatticeInf α] [SemilatticeInf β] {f : α → β}

theorem map_inf (hf : RightOrdContinuous f) (x y : α) : f (x ⊓ y) = f x ⊓ f y :=
  hf.orderDual.map_sup x y

theorem le_iff (hf : RightOrdContinuous f) (h : Injective f) {x y} : f x ≤ f y ↔ x ≤ y :=
  hf.orderDual.le_iff h

theorem lt_iff (hf : RightOrdContinuous f) (h : Injective f) {x y} : f x < f y ↔ x < y :=
  hf.orderDual.lt_iff h

variable (f)

/-- Convert an injective left order continuous function to an `OrderEmbedding`. -/
def toOrderEmbedding (hf : RightOrdContinuous f) (h : Injective f) : α ↪o β :=
  ⟨⟨f, h⟩, hf.le_iff h⟩

variable {f}

@[simp]
theorem coe_toOrderEmbedding (hf : RightOrdContinuous f) (h : Injective f) :
    ⇑(hf.toOrderEmbedding f h) = f :=
  rfl

end SemilatticeInf

section CompleteLattice

variable [CompleteLattice α] [CompleteLattice β] {f : α → β}

theorem map_sInf' (hf : RightOrdContinuous f) (s : Set α) : f (sInf s) = sInf (f '' s) :=
  hf.orderDual.map_sSup' s

theorem map_sInf (hf : RightOrdContinuous f) (s : Set α) : f (sInf s) = ⨅ x ∈ s, f x :=
  hf.orderDual.map_sSup s

theorem map_iInf (hf : RightOrdContinuous f) (g : ι → α) : f (⨅ i, g i) = ⨅ i, f (g i) :=
  hf.orderDual.map_iSup g

end CompleteLattice

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι] {f : α → β}

theorem map_csInf (hf : RightOrdContinuous f) {s : Set α} (sne : s.Nonempty) (sbdd : BddBelow s) :
    f (sInf s) = sInf (f '' s) :=
  hf.orderDual.map_csSup sne sbdd

theorem map_ciInf (hf : RightOrdContinuous f) {g : ι → α} (hg : BddBelow (range g)) :
    f (⨅ i, g i) = ⨅ i, f (g i) :=
  hf.orderDual.map_ciSup hg

end ConditionallyCompleteLattice

end RightOrdContinuous

namespace GaloisConnection
variable [Preorder α] [Preorder β] {f : α → β} {g : β → α}

/-- A left adjoint in a Galois connection is left-continuous in the order-theoretic sense. -/
lemma leftOrdContinuous (gc : GaloisConnection f g) : LeftOrdContinuous f :=
  fun _ _ ↦ gc.isLUB_l_image

/-- A right adjoint in a Galois connection is right-continuous in the order-theoretic sense. -/
lemma rightOrdContinuous (gc : GaloisConnection f g) : RightOrdContinuous g :=
  fun _ _ ↦ gc.isGLB_u_image

end GaloisConnection

namespace OrderIso
variable [Preorder α] [Preorder β] (e : α ≃o β)

protected lemma leftOrdContinuous : LeftOrdContinuous e := e.to_galoisConnection.leftOrdContinuous

protected lemma rightOrdContinuous : RightOrdContinuous e :=
  e.symm.to_galoisConnection.rightOrdContinuous

end OrderIso
