/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Yury Kudryashov
-/
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Order.Hom.Order
import Mathlib.Order.OmegaCompletePartialOrder

/-!
# Fixed point construction on complete lattices

This file sets up the basic theory of fixed points of a monotone function in a complete lattice.

## Main definitions

* `OrderHom.lfp`: The least fixed point of a bundled monotone function.
* `OrderHom.gfp`: The greatest fixed point of a bundled monotone function.
* `OrderHom.prevFixed`: The greatest fixed point of a bundled monotone function smaller than or
  equal to a given element.
* `OrderHom.nextFixed`: The least fixed point of a bundled monotone function greater than or
  equal to a given element.
* `fixedPoints.completeLattice`: The Knaster-Tarski theorem: fixed points of a monotone
  self-map of a complete lattice form themselves a complete lattice.

## Tags

fixed point, complete lattice, monotone function
-/


universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

open Function (fixedPoints IsFixedPt)

namespace OrderHom

section Basic

variable [CompleteLattice α] (f : α →o α)

/-- Least fixed point of a monotone function -/
def lfp : (α →o α) →o α where
  toFun f := sInf { a | f a ≤ a }
  monotone' _ _ hle := sInf_le_sInf fun a ha => (hle a).trans ha

/-- Greatest fixed point of a monotone function -/
def gfp : (α →o α) →o α where
  toFun f := sSup { a | a ≤ f a }
  monotone' _ _ hle := sSup_le_sSup fun a ha => le_trans ha (hle a)

theorem lfp_le {a : α} (h : f a ≤ a) : f.lfp ≤ a :=
  sInf_le h

theorem lfp_le_fixed {a : α} (h : f a = a) : f.lfp ≤ a :=
  f.lfp_le h.le

theorem le_lfp {a : α} (h : ∀ b, f b ≤ b → a ≤ b) : a ≤ f.lfp :=
  le_sInf h

theorem map_le_lfp {a : α} (ha : a ≤ f.lfp) : f a ≤ f.lfp :=
  f.le_lfp fun _ hb => (f.mono <| le_sInf_iff.1 ha _ hb).trans hb

@[simp]
theorem map_lfp : f f.lfp = f.lfp :=
  have h : f f.lfp ≤ f.lfp := f.map_le_lfp le_rfl
  h.antisymm <| f.lfp_le <| f.mono h

theorem isFixedPt_lfp : IsFixedPt f f.lfp :=
  f.map_lfp

theorem lfp_le_map {a : α} (ha : f.lfp ≤ a) : f.lfp ≤ f a :=
  calc
    f.lfp = f f.lfp := f.map_lfp.symm
    _ ≤ f a := f.mono ha

theorem isLeast_lfp_le : IsLeast { a | f a ≤ a } f.lfp :=
  ⟨f.map_lfp.le, fun _ => f.lfp_le⟩

theorem isLeast_lfp : IsLeast (fixedPoints f) f.lfp :=
  ⟨f.isFixedPt_lfp, fun _ => f.lfp_le_fixed⟩

theorem lfp_induction {p : α → Prop} (step : ∀ a, p a → a ≤ f.lfp → p (f a))
    (hSup : ∀ s, (∀ a ∈ s, p a) → p (sSup s)) : p f.lfp := by
  set s := { a | a ≤ f.lfp ∧ p a }
  specialize hSup s fun a => And.right
  suffices sSup s = f.lfp from this ▸ hSup
  have h : sSup s ≤ f.lfp := sSup_le fun b => And.left
  have hmem : f (sSup s) ∈ s := ⟨f.map_le_lfp h, step _ hSup h⟩
  exact h.antisymm (f.lfp_le <| le_sSup hmem)

theorem le_gfp {a : α} (h : a ≤ f a) : a ≤ f.gfp :=
  le_sSup h

theorem gfp_le {a : α} (h : ∀ b, b ≤ f b → b ≤ a) : f.gfp ≤ a :=
  sSup_le h

theorem isFixedPt_gfp : IsFixedPt f f.gfp :=
  f.dual.isFixedPt_lfp

@[simp]
theorem map_gfp : f f.gfp = f.gfp :=
  f.dual.map_lfp

theorem map_le_gfp {a : α} (ha : a ≤ f.gfp) : f a ≤ f.gfp :=
  f.dual.lfp_le_map ha

theorem gfp_le_map {a : α} (ha : f.gfp ≤ a) : f.gfp ≤ f a :=
  f.dual.map_le_lfp ha

theorem isGreatest_gfp_le : IsGreatest { a | a ≤ f a } f.gfp :=
  f.dual.isLeast_lfp_le

theorem isGreatest_gfp : IsGreatest (fixedPoints f) f.gfp :=
  f.dual.isLeast_lfp

theorem gfp_induction {p : α → Prop} (step : ∀ a, p a → f.gfp ≤ a → p (f a))
    (hInf : ∀ s, (∀ a ∈ s, p a) → p (sInf s)) : p f.gfp :=
  f.dual.lfp_induction step hInf

end Basic

section Eqn

variable [CompleteLattice α] [CompleteLattice β] (f : β →o α) (g : α →o β)

-- Rolling rule
theorem map_lfp_comp : f (g.comp f).lfp = (f.comp g).lfp :=
  le_antisymm ((f.comp g).map_lfp ▸ f.mono (lfp_le_fixed _ <| congr_arg g (f.comp g).map_lfp)) <|
    lfp_le _ (congr_arg f (g.comp f).map_lfp).le

theorem map_gfp_comp : f (g.comp f).gfp = (f.comp g).gfp :=
  f.dual.map_lfp_comp g.dual

-- Diagonal rule
theorem lfp_lfp (h : α →o α →o α) : (lfp.comp h).lfp = h.onDiag.lfp := by
  let a := (lfp.comp h).lfp
  refine (lfp_le _ ?_).antisymm (lfp_le _ (Eq.le ?_))
  · exact lfp_le _ h.onDiag.map_lfp.le
  have ha : (lfp ∘ h) a = a := (lfp.comp h).map_lfp
  calc
    h a a = h a (h a).lfp := congr_arg (h a) ha.symm
    _ = (h a).lfp := (h a).map_lfp
    _ = a := ha

theorem gfp_gfp (h : α →o α →o α) : (gfp.comp h).gfp = h.onDiag.gfp :=
  @lfp_lfp αᵒᵈ _ <| (OrderHom.dualIso αᵒᵈ αᵒᵈ).symm.toOrderEmbedding.toOrderHom.comp h.dual

end Eqn

section PrevNext

variable [CompleteLattice α] (f : α →o α)

theorem gfp_const_inf_le (x : α) : (const α x ⊓ f).gfp ≤ x :=
  (gfp_le _) fun _ hb => hb.trans inf_le_left

/-- Previous fixed point of a monotone map. If `f` is a monotone self-map of a complete lattice and
`x` is a point such that `f x ≤ x`, then `f.prevFixed x hx` is the greatest fixed point of `f`
that is less than or equal to `x`. -/
def prevFixed (x : α) (hx : f x ≤ x) : fixedPoints f :=
  ⟨(const α x ⊓ f).gfp,
    calc
      f (const α x ⊓ f).gfp = x ⊓ f (const α x ⊓ f).gfp :=
        Eq.symm <| inf_of_le_right <| (f.mono <| f.gfp_const_inf_le x).trans hx
      _ = (const α x ⊓ f).gfp := (const α x ⊓ f).map_gfp
      ⟩

/-- Next fixed point of a monotone map. If `f` is a monotone self-map of a complete lattice and
`x` is a point such that `x ≤ f x`, then `f.nextFixed x hx` is the least fixed point of `f`
that is greater than or equal to `x`. -/
def nextFixed (x : α) (hx : x ≤ f x) : fixedPoints f :=
  { f.dual.prevFixed x hx with val := (const α x ⊔ f).lfp }

theorem prevFixed_le {x : α} (hx : f x ≤ x) : ↑(f.prevFixed x hx) ≤ x :=
  f.gfp_const_inf_le x

theorem le_nextFixed {x : α} (hx : x ≤ f x) : x ≤ f.nextFixed x hx :=
  f.dual.prevFixed_le hx

theorem nextFixed_le {x : α} (hx : x ≤ f x) {y : fixedPoints f} (h : x ≤ y) :
    f.nextFixed x hx ≤ y :=
  Subtype.coe_le_coe.1 <| lfp_le _ <| sup_le h y.2.le

@[simp]
theorem nextFixed_le_iff {x : α} (hx : x ≤ f x) {y : fixedPoints f} :
    f.nextFixed x hx ≤ y ↔ x ≤ y :=
  ⟨fun h => (f.le_nextFixed hx).trans h, f.nextFixed_le hx⟩

@[simp]
theorem le_prevFixed_iff {x : α} (hx : f x ≤ x) {y : fixedPoints f} :
    y ≤ f.prevFixed x hx ↔ ↑y ≤ x :=
  f.dual.nextFixed_le_iff hx

theorem le_prevFixed {x : α} (hx : f x ≤ x) {y : fixedPoints f} (h : ↑y ≤ x) :
    y ≤ f.prevFixed x hx :=
  (f.le_prevFixed_iff hx).2 h

theorem le_map_sup_fixedPoints (x y : fixedPoints f) : (x ⊔ y : α) ≤ f (x ⊔ y) :=
  calc
    (x ⊔ y : α) = f x ⊔ f y := congr_arg₂ (· ⊔ ·) x.2.symm y.2.symm
    _ ≤ f (x ⊔ y) := f.mono.le_map_sup x y

-- Porting note: `x ⊓ y` without the `.val`sw fails to synthesize `Inf` instance
theorem map_inf_fixedPoints_le (x y : fixedPoints f) : f (x ⊓ y) ≤ x.val ⊓ y.val :=
  f.dual.le_map_sup_fixedPoints x y

theorem le_map_sSup_subset_fixedPoints (A : Set α) (hA : A ⊆ fixedPoints f) :
    sSup A ≤ f (sSup A) :=
  sSup_le fun _ hx => hA hx ▸ (f.mono <| le_sSup hx)

theorem map_sInf_subset_fixedPoints_le (A : Set α) (hA : A ⊆ fixedPoints f) :
    f (sInf A) ≤ sInf A :=
  le_sInf fun _ hx => hA hx ▸ (f.mono <| sInf_le hx)

end PrevNext

end OrderHom

namespace fixedPoints

open OrderHom

variable [CompleteLattice α] (f : α →o α)

instance : SemilatticeSup (fixedPoints f) :=
  { Subtype.partialOrder _ with
    sup := fun x y => f.nextFixed (x ⊔ y) (f.le_map_sup_fixedPoints x y)
    le_sup_left := fun _ _ => Subtype.coe_le_coe.1 <| le_sup_left.trans (f.le_nextFixed _)
    le_sup_right := fun _ _ => Subtype.coe_le_coe.1 <| le_sup_right.trans (f.le_nextFixed _)
    sup_le := fun _ _ _ hxz hyz => f.nextFixed_le _ <| sup_le hxz hyz }

instance : SemilatticeInf (fixedPoints f) :=
  { OrderDual.instSemilatticeInf (fixedPoints f.dual) with
    inf := fun x y => f.prevFixed (x ⊓ y) (f.map_inf_fixedPoints_le x y) }

instance : CompleteSemilatticeSup (fixedPoints f) :=
  { Subtype.partialOrder _ with
    sSup := fun s =>
      f.nextFixed (sSup (Subtype.val '' s))
        (f.le_map_sSup_subset_fixedPoints (Subtype.val '' s)
          fun _ ⟨x, hx⟩ => hx.2 ▸ x.2)
    le_sSup := fun _ _ hx =>
      Subtype.coe_le_coe.1 <| le_trans (le_sSup <| Set.mem_image_of_mem _ hx) (f.le_nextFixed _)
    sSup_le := fun _ _ hx => f.nextFixed_le _ <| sSup_le <| Set.forall_mem_image.2 hx }

instance : CompleteSemilatticeInf (fixedPoints f) :=
  { Subtype.partialOrder _ with
    sInf := fun s =>
      f.prevFixed (sInf (Subtype.val '' s))
        (f.map_sInf_subset_fixedPoints_le (Subtype.val '' s) fun _ ⟨x, hx⟩ => hx.2 ▸ x.2)
    le_sInf := fun _ _ hx => f.le_prevFixed _ <| le_sInf <| Set.forall_mem_image.2 hx
    sInf_le := fun _ _ hx =>
      Subtype.coe_le_coe.1 <| le_trans (f.prevFixed_le _) (sInf_le <| Set.mem_image_of_mem _ hx) }

/-- **Knaster-Tarski Theorem**: The fixed points of `f` form a complete lattice. -/
instance completeLattice : CompleteLattice (fixedPoints f) where
  __ := inferInstanceAs (SemilatticeInf (fixedPoints f))
  __ := inferInstanceAs (SemilatticeSup (fixedPoints f))
  __ := inferInstanceAs (CompleteSemilatticeInf (fixedPoints f))
  __ := inferInstanceAs (CompleteSemilatticeSup (fixedPoints f))
  top := ⟨f.gfp, f.isFixedPt_gfp⟩
  bot := ⟨f.lfp, f.isFixedPt_lfp⟩
  le_top x := f.le_gfp x.2.ge
  bot_le x := f.lfp_le x.2.le

open OmegaCompletePartialOrder fixedPoints

/-- **Kleene's fixed point Theorem**: The least fixed point in a complete lattice is
the supremum of iterating a function on bottom arbitrary often. -/
theorem lfp_eq_sSup_iterate (h : ωScottContinuous f) :
    f.lfp = ⨆ n, f^[n] ⊥ := by
  apply le_antisymm
  · apply lfp_le_fixed
    exact Function.mem_fixedPoints.mp (ωSup_iterate_mem_fixedPoint
      ⟨f, h.map_ωSup_of_orderHom⟩ ⊥ bot_le)
  · apply le_lfp
    intro a h_a
    exact ωSup_iterate_le_prefixedPoint ⟨f, h.map_ωSup_of_orderHom⟩ ⊥ bot_le h_a bot_le

theorem gfp_eq_sInf_iterate (h : ωScottContinuous f.dual) :
    f.gfp = ⨅ n, f^[n] ⊤ :=
  lfp_eq_sSup_iterate f.dual h

end fixedPoints
