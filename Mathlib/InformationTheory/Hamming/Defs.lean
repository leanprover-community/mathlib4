/-
Copyright (c) 2022 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/

import Mathlib.Topology.MetricSpace.Basic

/-!
# Hamming spaces

The Hamming metric counts the number of places two members of a (finite) Pi type
differ. The Hamming norm is the same as the Hamming metric over additive groups, and
counts the number of places a member of a (finite) Pi type differs from zero.

This is a useful notion in various applications, but in particular it is relevant
in coding theory, in which it is fundamental for defining the minimum distance of a
code.

## Main definitions

* `DHamming β`: a structure with one field containing a Pi type `Π i, β i`, representing
  the Pi type but equipped with the Hamming distance.
* `Hamming ι α`, the non-dependent Hamming type.
* `DHamming.toPi`, `DHamming.ofPi`: functions for casting between `DHamming β` and `Π i, β i`.
* The Hamming distance between `x` and `y`, the number of entries which differ between `x` and `y`.
-/

/-! ### The `Hamming` type synonym -/

/-- Type synonym for a Pi type which inherits the usual algebraic instances, but is equipped with
the Hamming metric and norm, instead of `Pi.normedAddCommGroup` which uses the sup norm. -/
structure DHamming {ι : Type*} (β : ι → Type*) where
  /-- Interpret a Pi type as a Hamming type. -/
  ofPi ::
  /-- The `i`-th coordinate of `x : Hamming β` is given by `x.toPi i`. -/
  toPi i : β i

/-- The non-dependent Hamming type. -/
abbrev Hamming (ι : Type*) (α : Type*) := DHamming fun _ : ι => α

namespace DHamming

variable {α ι : Type*} {β γ : ι → Type*}

/-- `Hamming.toPiEquiv` is the equivalence between `Hamming` and the corresponding Pi type. -/
@[simps]
def toPiEquiv : DHamming β ≃ ∀ i, β i where
  toFun := toPi
  invFun := ofPi

theorem ofPi_toPi : Function.LeftInverse (ofPi (β := β)) toPi := toPiEquiv.left_inv
theorem toPi_ofPi : Function.RightInverse (ofPi (β := β)) toPi := toPiEquiv.right_inv

@[ext] protected theorem ext {a b : DHamming β} (h : ∀ i, a.toPi i = b.toPi i) : a = b :=
  ofPi_toPi.injective <| funext h

/-- The map between Hamming types using a coordinate-wise map. -/
@[simps]
def map (f : ∀ i, β i → γ i) (x : DHamming β) : DHamming γ := ofPi <| Pi.map f x.toPi

instance [∀ i, Inhabited (β i)] : Inhabited (DHamming β) := toPiEquiv.inhabited

instance [DecidableEq ι] [Fintype ι] [∀ i, Fintype (β i)] : Fintype (DHamming β) :=
  Fintype.ofEquiv _ toPiEquiv.symm

instance [Inhabited ι] [∀ i, Nonempty (β i)] [Nontrivial (β default)] : Nontrivial (DHamming β) :=
  toPiEquiv.nontrivial

instance [Fintype ι] [∀ i, DecidableEq (β i)] : DecidableEq (DHamming β) := toPiEquiv.decidableEq

section

variable [Fintype ι] [∀ i, DecidableEq (β i)] [∀ i, DecidableEq (γ i)] {x y : DHamming β}
  {f : ∀ i, β i → γ i}

open Finset

instance : Dist (DHamming β) := ⟨fun x y => #{i | x.toPi i ≠ y.toPi i}⟩

open Finset

@[push_cast]
theorem dist_eq_card : dist x y = #{i | x.toPi i ≠ y.toPi i} := rfl

theorem dist_le_card : dist x y ≤ Fintype.card ι := by
  push_cast
  exact mod_cast card_le_univ _

theorem dist_le_of_fin {n : ℕ} [DecidableEq α] {x y : Hamming (Fin n) α} :
    dist x y ≤ n := dist_le_card.trans (by exact mod_cast (Fintype.card_fin _).le)

private theorem dist_eq_zero : dist x y = 0 ↔ x = y := by
    push_cast
    simp_rw [Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff,
      not_not, mem_univ, forall_const, DHamming.ext_iff]

theorem dist_lt_one : dist x y < 1 ↔ x = y := by
  rw [← dist_eq_zero]
  push_cast
  simp_rw [Nat.cast_lt_one, Nat.cast_eq_zero]

theorem dist_map_map_le_dist : dist (x.map f) (y.map f) ≤ dist x y := by
  push_cast
  exact mod_cast card_mono (monotone_filter_right _ fun i H1 H2 => H1 <| congr_arg (f i) H2)

theorem dist_map_map_of_injective (hf : ∀ i, Function.Injective (f i)) :
    dist (x.map f) (y.map f) = dist x y := by
  refine le_antisymm dist_map_map_le_dist ?_
  push_cast
  exact mod_cast card_mono (monotone_filter_right _ fun i H1 H2 => H1 <| hf i H2)

instance : MetricSpace (DHamming β) where
  dist_self _ := dist_eq_zero.mpr rfl
  eq_of_dist_eq_zero := dist_eq_zero.mp
  dist_comm _ _ := by
    push_cast
    simp_rw [ne_comm]
  dist_triangle _ _ _ := by
    push_cast
    simp_rw [← Nat.cast_add, Nat.cast_le]
    classical
      refine le_trans (card_mono ?_) (card_union_le _ _)
      rw [← filter_or]
      exact monotone_filter_right _ fun i h ↦ (h.ne_or_ne _).imp_right Ne.symm
  toUniformSpace := ⊥
  uniformity_dist := uniformity_dist_of_mem_uniformity _ _ fun s => by
    constructor
    · exact fun hs => ⟨1, zero_lt_one, fun hab => hs (dist_lt_one.mp hab)⟩
    · exact fun ⟨_, hε, hs⟩ ⟨_, _⟩ hab => hs (hε.trans_eq' <| dist_eq_zero.mpr hab)
  toBornology := ⟨⊥, bot_le⟩
  cobounded_sets := Set.ext <| fun _ =>
    iff_of_true (Filter.mem_sets.mpr Filter.mem_bot) ⟨Fintype.card ι, fun _ _ _ _ => dist_le_card⟩

@[push_cast]
theorem nndist_eq_hammingDist :
    nndist x y = #{i | x.toPi i ≠ y.toPi i} := rfl

instance : DiscreteTopology (DHamming β) := ⟨rfl⟩

end

end DHamming
