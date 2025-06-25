/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Junyan Xu
-/
import Mathlib.Data.DFinsupp.Defs

/-!
# Locus of unequal values of finitely supported dependent functions

Let `N : α → Type*` be a type family, assume that `N a` has a `0` for all `a : α` and let
`f g : Π₀ a, N a` be finitely supported dependent functions.

## Main definition

* `DFinsupp.neLocus f g : Finset α`, the finite subset of `α` where `f` and `g` differ.
  In the case in which `N a` is an additive group for all `a`, `DFinsupp.neLocus f g` coincides with
  `DFinsupp.support (f - g)`.
-/


variable {α : Type*} {N : α → Type*}

namespace DFinsupp

variable [DecidableEq α]

section NHasZero

variable [∀ a, DecidableEq (N a)] [∀ a, Zero (N a)] (f g : Π₀ a, N a)

/-- Given two finitely supported functions `f g : α →₀ N`, `Finsupp.neLocus f g` is the `Finset`
where `f` and `g` differ. This generalizes `(f - g).support` to situations without subtraction. -/
def neLocus (f g : Π₀ a, N a) : Finset α :=
  (f.support ∪ g.support).filter fun x ↦ f x ≠ g x

@[simp]
theorem mem_neLocus {f g : Π₀ a, N a} {a : α} : a ∈ f.neLocus g ↔ f a ≠ g a := by
  simpa only [neLocus, Finset.mem_filter, Finset.mem_union, mem_support_iff,
    and_iff_right_iff_imp] using Ne.ne_or_ne _

theorem notMem_neLocus {f g : Π₀ a, N a} {a : α} : a ∉ f.neLocus g ↔ f a = g a :=
  mem_neLocus.not.trans not_ne_iff

@[deprecated (since := "2025-05-23")] alias not_mem_neLocus := notMem_neLocus

@[simp]
theorem coe_neLocus : ↑(f.neLocus g) = { x | f x ≠ g x } :=
  Set.ext fun _x ↦ mem_neLocus

@[simp]
theorem neLocus_eq_empty {f g : Π₀ a, N a} : f.neLocus g = ∅ ↔ f = g :=
  ⟨fun h ↦
    ext fun a ↦ not_not.mp (mem_neLocus.not.mp (Finset.eq_empty_iff_forall_notMem.mp h a)),
    fun h ↦ h ▸ by simp only [neLocus, Ne, eq_self_iff_true, not_true, Finset.filter_False]⟩

@[simp]
theorem nonempty_neLocus_iff {f g : Π₀ a, N a} : (f.neLocus g).Nonempty ↔ f ≠ g :=
  Finset.nonempty_iff_ne_empty.trans neLocus_eq_empty.not

theorem neLocus_comm : f.neLocus g = g.neLocus f := by
  simp_rw [neLocus, Finset.union_comm, ne_comm]

@[simp]
theorem neLocus_zero_right : f.neLocus 0 = f.support := by
  ext
  rw [mem_neLocus, mem_support_iff, coe_zero, Pi.zero_apply]

@[simp]
theorem neLocus_zero_left : (0 : Π₀ a, N a).neLocus f = f.support :=
  (neLocus_comm _ _).trans (neLocus_zero_right _)

end NHasZero

section NeLocusAndMaps

variable {M P : α → Type*} [∀ a, Zero (N a)] [∀ a, Zero (M a)] [∀ a, Zero (P a)]

theorem subset_mapRange_neLocus [∀ a, DecidableEq (N a)] [∀ a, DecidableEq (M a)] (f g : Π₀ a, N a)
    {F : ∀ a, N a → M a} (F0 : ∀ a, F a 0 = 0) :
    (f.mapRange F F0).neLocus (g.mapRange F F0) ⊆ f.neLocus g := fun a ↦ by
  simpa only [mem_neLocus, mapRange_apply, not_imp_not] using congr_arg (F a)

theorem zipWith_neLocus_eq_left [∀ a, DecidableEq (N a)] [∀ a, DecidableEq (P a)]
    {F : ∀ a, M a → N a → P a} (F0 : ∀ a, F a 0 0 = 0) (f : Π₀ a, M a) (g₁ g₂ : Π₀ a, N a)
    (hF : ∀ a f, Function.Injective fun g ↦ F a f g) :
    (zipWith F F0 f g₁).neLocus (zipWith F F0 f g₂) = g₁.neLocus g₂ := by
  ext a
  simpa only [mem_neLocus] using (hF a _).ne_iff

theorem zipWith_neLocus_eq_right [∀ a, DecidableEq (M a)] [∀ a, DecidableEq (P a)]
    {F : ∀ a, M a → N a → P a} (F0 : ∀ a, F a 0 0 = 0) (f₁ f₂ : Π₀ a, M a) (g : Π₀ a, N a)
    (hF : ∀ a g, Function.Injective fun f ↦ F a f g) :
    (zipWith F F0 f₁ g).neLocus (zipWith F F0 f₂ g) = f₁.neLocus f₂ := by
  ext a
  simpa only [mem_neLocus] using (hF a _).ne_iff

theorem mapRange_neLocus_eq [∀ a, DecidableEq (N a)] [∀ a, DecidableEq (M a)] (f g : Π₀ a, N a)
    {F : ∀ a, N a → M a} (F0 : ∀ a, F a 0 = 0) (hF : ∀ a, Function.Injective (F a)) :
    (f.mapRange F F0).neLocus (g.mapRange F F0) = f.neLocus g := by
  ext a
  simpa only [mem_neLocus] using (hF a).ne_iff

end NeLocusAndMaps

variable [∀ a, DecidableEq (N a)]

@[simp]
theorem neLocus_add_left [∀ a, AddLeftCancelMonoid (N a)] (f g h : Π₀ a, N a) :
    (f + g).neLocus (f + h) = g.neLocus h :=
  zipWith_neLocus_eq_left _ _ _ _ fun _a ↦ add_right_injective

@[simp]
theorem neLocus_add_right [∀ a, AddRightCancelMonoid (N a)] (f g h : Π₀ a, N a) :
    (f + h).neLocus (g + h) = f.neLocus g :=
  zipWith_neLocus_eq_right _ _ _ _ fun _a ↦ add_left_injective

section AddGroup

variable [∀ a, AddGroup (N a)] (f f₁ f₂ g g₁ g₂ : Π₀ a, N a)

@[simp]
theorem neLocus_neg_neg : neLocus (-f) (-g) = f.neLocus g :=
  mapRange_neLocus_eq _ _ (fun _a ↦ neg_zero) fun _a ↦ neg_injective

theorem neLocus_neg : neLocus (-f) g = f.neLocus (-g) := by rw [← neLocus_neg_neg, neg_neg]

theorem neLocus_eq_support_sub : f.neLocus g = (f - g).support := by
  rw [← @neLocus_add_right α N _ _ _ _ _ (-g), add_neg_cancel, neLocus_zero_right, sub_eq_add_neg]

@[simp]
theorem neLocus_sub_left : neLocus (f - g₁) (f - g₂) = neLocus g₁ g₂ := by
  simp only [sub_eq_add_neg, @neLocus_add_left α N _ _ _, neLocus_neg_neg]

@[simp]
theorem neLocus_sub_right : neLocus (f₁ - g) (f₂ - g) = neLocus f₁ f₂ := by
  simpa only [sub_eq_add_neg] using @neLocus_add_right α N _ _ _ _ _ _

@[simp]
theorem neLocus_self_add_right : neLocus f (f + g) = g.support := by
  rw [← neLocus_zero_left, ← @neLocus_add_left α N _ _ _ f 0 g, add_zero]

@[simp]
theorem neLocus_self_add_left : neLocus (f + g) f = g.support := by
  rw [neLocus_comm, neLocus_self_add_right]

@[simp]
theorem neLocus_self_sub_right : neLocus f (f - g) = g.support := by
  rw [sub_eq_add_neg, neLocus_self_add_right, support_neg]

@[simp]
theorem neLocus_self_sub_left : neLocus (f - g) f = g.support := by
  rw [neLocus_comm, neLocus_self_sub_right]

end AddGroup

end DFinsupp
