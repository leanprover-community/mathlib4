/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kim Morrison
-/
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Data.Finsupp.Defs
import Mathlib.Tactic.FastInstance

/-!
# Additive monoid structure on `ι →₀ M`
-/

open Finset

noncomputable section

variable {ι F M N G H : Type*}

namespace Finsupp
section AddZeroClass
variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

instance instAdd : Add (ι →₀ M) where add := zipWith (· + ·) (add_zero 0)

@[simp, norm_cast] lemma coe_add (f g : ι →₀ M) : ⇑(f + g) = f + g := rfl

lemma add_apply (g₁ g₂ : ι →₀ M) (a : ι) : (g₁ + g₂) a = g₁ a + g₂ a := rfl

lemma support_add [DecidableEq ι] : (g₁ + g₂).support ⊆ g₁.support ∪ g₂.support := support_zipWith

lemma support_add_eq [DecidableEq ι] (h : Disjoint g₁.support g₂.support) :
    (g₁ + g₂).support = g₁.support ∪ g₂.support :=
  le_antisymm support_zipWith fun a ha =>
    (Finset.mem_union.1 ha).elim
      (fun ha => by
        have : a ∉ g₂.support := disjoint_left.1 h ha
        simp only [mem_support_iff, not_not] at *; simpa only [add_apply, this, add_zero] )
      fun ha => by
      have : a ∉ g₁.support := disjoint_right.1 h ha
      simp only [mem_support_iff, not_not] at *; simpa only [add_apply, this, zero_add]

instance instAddZeroClass : AddZeroClass (ι →₀ M) :=
  fast_instance% DFunLike.coe_injective.addZeroClass _ coe_zero coe_add

instance instIsLeftCancelAdd [IsLeftCancelAdd M] : IsLeftCancelAdd (ι →₀ M) where
  add_left_cancel _ _ _ h := ext fun x => add_left_cancel <| DFunLike.congr_fun h x

/-- When ι is finite and M is an AddMonoid,
  then Finsupp.equivFunOnFinite gives an AddEquiv -/
noncomputable def addEquivFunOnFinite {ι : Type*} [Finite ι] :
    (ι →₀ M) ≃+ (ι → M) where
  __ := Finsupp.equivFunOnFinite
  map_add' _ _ := rfl

/-- AddEquiv between (ι →₀ M) and M, when ι has a unique element -/
noncomputable def _root_.AddEquiv.finsuppUnique {ι : Type*} [Unique ι] :
    (ι →₀ M) ≃+ M where
  __ := Equiv.finsuppUnique
  map_add' _ _ := rfl

instance instIsRightCancelAdd [IsRightCancelAdd M] : IsRightCancelAdd (ι →₀ M) where
  add_right_cancel _ _ _ h := ext fun x => add_right_cancel <| DFunLike.congr_fun h x

instance instIsCancelAdd [IsCancelAdd M] : IsCancelAdd (ι →₀ M) where

/-- Evaluation of a function `f : ι →₀ M` at a point as an additive monoid homomorphism.

See `Finsupp.lapply` in `Mathlib/LinearAlgebra/Finsupp/Defs.lean` for the stronger version as a
linear map. -/
@[simps apply]
def applyAddHom (a : ι) : (ι →₀ M) →+ M where
  toFun g := g a
  map_zero' := zero_apply
  map_add' _ _ := add_apply _ _ _

/-- Coercion from a `Finsupp` to a function type is an `AddMonoidHom`. -/
@[simps]
noncomputable def coeFnAddHom : (ι →₀ M) →+ ι → M where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

lemma mapRange_add {hf : f 0 = 0} (hf' : ∀ x y, f (x + y) = f x + f y) (v₁ v₂ : ι →₀ M) :
    mapRange f hf (v₁ + v₂) = mapRange f hf v₁ + mapRange f hf v₂ :=
  ext fun _ => by simp only [hf', add_apply, mapRange_apply]

lemma mapRange_add' [FunLike F M N] [AddMonoidHomClass F M N] {f : F} (g₁ g₂ : ι →₀ M) :
    mapRange f (map_zero f) (g₁ + g₂) = mapRange f (map_zero f) g₁ + mapRange f (map_zero f) g₂ :=
  mapRange_add (map_add f) g₁ g₂

/-- Bundle `Finsupp.embDomain f` as an additive map from `ι →₀ M` to `F →₀ M`. -/
@[simps]
def embDomain.addMonoidHom (f : ι ↪ F) : (ι →₀ M) →+ F →₀ M where
  toFun v := embDomain f v
  map_zero' := by simp
  map_add' v w := by
    ext b
    by_cases h : b ∈ Set.range f
    · rcases h with ⟨a, rfl⟩
      simp
    · simp only [Set.mem_range, not_exists, coe_add, Pi.add_apply,
        embDomain_notin_range _ _ _ h, add_zero]

@[simp]
lemma embDomain_add (f : ι ↪ F) (v w : ι →₀ M) :
    embDomain f (v + w) = embDomain f v + embDomain f w := (embDomain.addMonoidHom f).map_add v w

end AddZeroClass

section AddMonoid
variable [AddMonoid M]

/-- Note the general `SMul` instance for `Finsupp` doesn't apply as `ℕ` is not distributive
unless `F i`'s addition is commutative. -/
instance instNatSMul : SMul ℕ (ι →₀ M) where smul n v := v.mapRange (n • ·) (nsmul_zero _)

instance instAddMonoid : AddMonoid (ι →₀ M) :=
  fast_instance% DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => rfl

end AddMonoid

instance instAddCommMonoid [AddCommMonoid M] : AddCommMonoid (ι →₀ M) :=
  fast_instance% DFunLike.coe_injective.addCommMonoid
    DFunLike.coe coe_zero coe_add (fun _ _ => rfl)

instance instNeg [NegZeroClass G] : Neg (ι →₀ G) where neg := mapRange Neg.neg neg_zero

@[simp, norm_cast] lemma coe_neg [NegZeroClass G] (g : ι →₀ G) : ⇑(-g) = -g := rfl

lemma neg_apply [NegZeroClass G] (g : ι →₀ G) (a : ι) : (-g) a = -g a :=
  rfl

lemma mapRange_neg [NegZeroClass G] [NegZeroClass H] {f : G → H} {hf : f 0 = 0}
    (hf' : ∀ x, f (-x) = -f x) (v : ι →₀ G) : mapRange f hf (-v) = -mapRange f hf v :=
  ext fun _ => by simp only [hf', neg_apply, mapRange_apply]

lemma mapRange_neg' [AddGroup G] [SubtractionMonoid H] [FunLike F G H] [AddMonoidHomClass F G H]
    {f : F} (v : ι →₀ G) :
    mapRange f (map_zero f) (-v) = -mapRange f (map_zero f) v :=
  mapRange_neg (map_neg f) v

instance instSub [SubNegZeroMonoid G] : Sub (ι →₀ G) :=
  ⟨zipWith Sub.sub (sub_zero _)⟩

@[simp, norm_cast] lemma coe_sub [SubNegZeroMonoid G] (g₁ g₂ : ι →₀ G) : ⇑(g₁ - g₂) = g₁ - g₂ := rfl

lemma sub_apply [SubNegZeroMonoid G] (g₁ g₂ : ι →₀ G) (a : ι) : (g₁ - g₂) a = g₁ a - g₂ a := rfl

lemma mapRange_sub [SubNegZeroMonoid G] [SubNegZeroMonoid H] {f : G → H} {hf : f 0 = 0}
    (hf' : ∀ x y, f (x - y) = f x - f y) (v₁ v₂ : ι →₀ G) :
    mapRange f hf (v₁ - v₂) = mapRange f hf v₁ - mapRange f hf v₂ :=
  ext fun _ => by simp only [hf', sub_apply, mapRange_apply]

lemma mapRange_sub' [AddGroup G] [SubtractionMonoid H] [FunLike F G H] [AddMonoidHomClass F G H]
    {f : F} (v₁ v₂ : ι →₀ G) :
    mapRange f (map_zero f) (v₁ - v₂) = mapRange f (map_zero f) v₁ - mapRange f (map_zero f) v₂ :=
  mapRange_sub (map_sub f) v₁ v₂

/-- Note the general `SMul` instance for `Finsupp` doesn't apply as `ℤ` is not distributive
unless `F i`'s addition is commutative. -/
instance instIntSMul [AddGroup G] : SMul ℤ (ι →₀ G) :=
  ⟨fun n v => v.mapRange (n • ·) (zsmul_zero _)⟩

instance instAddGroup [AddGroup G] : AddGroup (ι →₀ G) :=
  fast_instance% DFunLike.coe_injective.addGroup DFunLike.coe coe_zero coe_add coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

instance instAddCommGroup [AddCommGroup G] : AddCommGroup (ι →₀ G) :=
  fast_instance%  DFunLike.coe_injective.addCommGroup DFunLike.coe coe_zero coe_add coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

@[simp]
lemma support_neg [AddGroup G] (f : ι →₀ G) : support (-f) = support f :=
  Finset.Subset.antisymm support_mapRange
    (calc
      support f = support (- -f) := congr_arg support (neg_neg _).symm
      _ ⊆ support (-f) := support_mapRange
      )

lemma support_sub [DecidableEq ι] [AddGroup G] {f g : ι →₀ G} :
    support (f - g) ⊆ support f ∪ support g := by
  rw [sub_eq_add_neg, ← support_neg g]
  exact support_add

end Finsupp
