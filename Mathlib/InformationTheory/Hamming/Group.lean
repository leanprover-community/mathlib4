/-
Copyright (c) 2022 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/

import Mathlib.Algebra.Group.TransferInstance
import Mathlib.InformationTheory.Hamming.Defs

/-! ### Algebraic instances inherited from normal Pi types -/

namespace DHamming

variable {α ι : Type*} {β γ : ι → Type*} {f : ∀ i, β i → γ i} {x y : DHamming β}

/-! Instances inherited from normal Pi types. -/

@[simps!]
instance [∀ i, Zero (β i)] : Zero (DHamming β) := toPiEquiv.zero

theorem map_zero [∀ i, Zero (β i)] [∀ i, Zero (γ i)] (hf : ∀ i, f i 0 = 0) : map f 0 = 0 := by
  ext
  exact hf _

@[simps!]
instance [∀ i, Add (β i)] : Add (DHamming β) := toPiEquiv.add

/-- `Hamming.toPiEquiv` as an `AddEquiv`. -/
def ofAddEquiv [∀ i, Add (β i)] : DHamming β ≃+ ∀ i, β i := toPiEquiv.addEquiv

@[simps!]
instance [∀ i, Neg (β i)] : Neg (DHamming β) := toPiEquiv.Neg

@[simps!]
instance [∀ i, Sub (β i)] : Sub (DHamming β) := toPiEquiv.sub

@[simps!]
instance [∀ i, SMul α (β i)] : SMul α (DHamming β) := toPiEquiv.smul _

instance [∀ i, AddMonoid (β i)] : AddMonoid (DHamming β) := toPiEquiv.addMonoid
instance [∀ i, AddGroup (β i)] : AddGroup (DHamming β) := toPiEquiv.addGroup
instance [∀ i, AddSemigroup (β i)] : AddSemigroup (DHamming β) := toPiEquiv.addSemigroup
instance [∀ i, AddCommMonoid (β i)] : AddCommMonoid (DHamming β) := toPiEquiv.addCommMonoid
instance [∀ i, AddCommSemigroup (β i)] : AddCommSemigroup (DHamming β) := toPiEquiv.addCommSemigroup

instance [∀ i, AddCommGroup (β i)] : AddCommGroup (DHamming β) := toPiEquiv.addCommGroup

instance [Monoid α] [∀ i, MulAction α (β i)] : MulAction α (DHamming β) := toPiEquiv.mulAction _

section

variable [Fintype ι] [∀ i, DecidableEq (β i)] [∀ i, DecidableEq (γ i)] {x y : DHamming β}

theorem dist_smul_le_dist [∀ i, SMul α (β i)] {k : α} : dist (k • x) (k • y) ≤ dist x y :=
  dist_map_map_le_dist

theorem dist_smul [∀ i, SMul α (β i)] {k : α} (hk : ∀ i, IsSMulRegular (β i) k) :
    dist (k • x) (k • y) = dist x y := dist_map_map_of_injective hk
end

end DHamming
