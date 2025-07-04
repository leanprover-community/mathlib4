/-
Copyright (c) 2022 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/

import Mathlib.Algebra.Equiv.TransferInstance
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Hamming spaces

The Hamming metric counts the number of places two members of a (finite) Pi type
differ. The Hamming norm is the same as the Hamming metric over additive groups, and
counts the number of places a member of a (finite) Pi type differs from zero.

This is a useful notion in various applications, but in particular it is relevant
in coding theory, in which it is fundamental for defining the minimum distance of a
code.

## Main definitions
* `hammingDist x y`: the Hamming distance between `x` and `y`, the number of entries which differ.
* `hammingNorm x`: the Hamming norm of `x`, the number of non-zero entries.
* `Hamming β`: a type synonym for `Π i, β i` with `dist` and `norm` provided by the above.
* `Hamming.toHamming`, `Hamming.ofHamming`: functions for casting between `Hamming β` and
`Π i, β i`.
* the Hamming norm forms a normed group on `Hamming β`.
-/


section HammingDistNorm

open Finset Function

variable {α ι : Type*} {β : ι → Type*} [Fintype ι] [∀ i, DecidableEq (β i)]
variable {γ : ι → Type*} [∀ i, DecidableEq (γ i)]

/-- The Hamming distance function to the naturals. -/
def hammingDist (x y : ∀ i, β i) : ℕ := #{i | x i ≠ y i}

/-- Corresponds to `dist_self`. -/
@[simp]
theorem hammingDist_self (x : ∀ i, β i) : hammingDist x x = 0 := by
  rw [hammingDist, card_eq_zero, filter_eq_empty_iff]
  exact fun _ _ H => H rfl

/-- Corresponds to `dist_nonneg`. -/
theorem hammingDist_nonneg {x y : ∀ i, β i} : 0 ≤ hammingDist x y :=
  zero_le _

/-- Corresponds to `dist_comm`. -/
theorem hammingDist_comm (x y : ∀ i, β i) : hammingDist x y = hammingDist y x := by
  simp_rw [hammingDist, ne_comm]

/-- Corresponds to `dist_triangle`. -/
theorem hammingDist_triangle (x y z : ∀ i, β i) :
    hammingDist x z ≤ hammingDist x y + hammingDist y z := by
  classical
    unfold hammingDist
    refine le_trans (card_mono ?_) (card_union_le _ _)
    rw [← filter_or]
    exact monotone_filter_right _ fun i h ↦ (h.ne_or_ne _).imp_right Ne.symm

/-- Corresponds to `dist_triangle_left`. -/
theorem hammingDist_triangle_left (x y z : ∀ i, β i) :
    hammingDist x y ≤ hammingDist z x + hammingDist z y := by
  rw [hammingDist_comm z]
  exact hammingDist_triangle _ _ _

/-- Corresponds to `dist_triangle_right`. -/
theorem hammingDist_triangle_right (x y z : ∀ i, β i) :
    hammingDist x y ≤ hammingDist x z + hammingDist y z := by
  rw [hammingDist_comm y]
  exact hammingDist_triangle _ _ _

/-- Corresponds to `swap_dist`. -/
theorem swap_hammingDist : swap (@hammingDist _ β _ _) = hammingDist := by
  funext x y
  exact hammingDist_comm _ _

/-- Corresponds to `eq_of_dist_eq_zero`. -/
theorem eq_of_hammingDist_eq_zero {x y : ∀ i, β i} : hammingDist x y = 0 → x = y := by
  simp_rw [hammingDist, card_eq_zero, filter_eq_empty_iff, Classical.not_not, funext_iff, mem_univ,
    forall_true_left, imp_self]

/-- Corresponds to `dist_eq_zero`. -/
@[simp]
theorem hammingDist_eq_zero {x y : ∀ i, β i} : hammingDist x y = 0 ↔ x = y :=
  ⟨eq_of_hammingDist_eq_zero, fun H => by
    rw [H]
    exact hammingDist_self _⟩

/-- Corresponds to `zero_eq_dist`. -/
@[simp]
theorem hamming_zero_eq_dist {x y : ∀ i, β i} : 0 = hammingDist x y ↔ x = y := by
  rw [eq_comm, hammingDist_eq_zero]

/-- Corresponds to `dist_ne_zero`. -/
theorem hammingDist_ne_zero {x y : ∀ i, β i} : hammingDist x y ≠ 0 ↔ x ≠ y :=
  hammingDist_eq_zero.not

/-- Corresponds to `dist_pos`. -/
@[simp]
theorem hammingDist_pos {x y : ∀ i, β i} : 0 < hammingDist x y ↔ x ≠ y := by
  rw [← hammingDist_ne_zero, iff_not_comm, not_lt, Nat.le_zero]

theorem hammingDist_lt_one {x y : ∀ i, β i} : hammingDist x y < 1 ↔ x = y := by
  rw [Nat.lt_one_iff, hammingDist_eq_zero]

theorem hammingDist_le_card_fintype {x y : ∀ i, β i} : hammingDist x y ≤ Fintype.card ι :=
  card_le_univ _

theorem hammingDist_map_map_le_hammingDist (f : ∀ i, β i → γ i) {x y : ∀ i, β i} :
    (hammingDist (Pi.map f x) (Pi.map f y)) ≤ hammingDist x y :=
  card_mono (monotone_filter_right _ fun i H1 H2 => H1 <| congr_arg (f i) H2)

theorem hammingDist_map_map_of_injective (f : ∀ i, β i → γ i) {x y : ∀ i, β i}
    (hf : ∀ i, Injective (f i)) : (hammingDist (Pi.map f x) (Pi.map f y)) = hammingDist x y :=
  le_antisymm (hammingDist_map_map_le_hammingDist _) <|
    card_mono (monotone_filter_right _ fun i H1 H2 => H1 <| hf i H2)

theorem hammingDist_smul_le_hammingDist [∀ i, SMul α (β i)] {k : α} {x y : ∀ i, β i} :
    hammingDist (k • x) (k • y) ≤ hammingDist x y :=
  hammingDist_map_map_le_hammingDist fun i => (k • · : β i → β i)

/-- Corresponds to `dist_smul` with the discrete norm on `α`. -/
theorem hammingDist_smul [∀ i, SMul α (β i)] {k : α} {x y : ∀ i, β i}
    (hk : ∀ i, IsSMulRegular (β i) k) : hammingDist (k • x) (k • y) = hammingDist x y :=
  hammingDist_map_map_of_injective (fun i => (k • · : β i → β i)) hk

section Zero

variable [∀ i, Zero (β i)] [∀ i, Zero (γ i)]

/-- The Hamming weight function to the naturals. -/
def hammingNorm (x : ∀ i, β i) : ℕ := #{i | x i ≠ 0}

/-- Corresponds to `dist_zero_right`. -/
@[simp]
theorem hammingDist_zero_right (x : ∀ i, β i) : hammingDist x 0 = hammingNorm x :=
  rfl

/-- Corresponds to `dist_zero_left`. -/
@[simp]
theorem hammingDist_zero_left : hammingDist (0 : ∀ i, β i) = hammingNorm :=
  funext fun x => by rw [hammingDist_comm, hammingDist_zero_right]

/-- Corresponds to `norm_nonneg`. -/
theorem hammingNorm_nonneg {x : ∀ i, β i} : 0 ≤ hammingNorm x :=
  zero_le _

/-- Corresponds to `norm_zero`. -/
@[simp]
theorem hammingNorm_zero : hammingNorm (0 : ∀ i, β i) = 0 :=
  hammingDist_self _

/-- Corresponds to `norm_eq_zero`. -/
@[simp]
theorem hammingNorm_eq_zero {x : ∀ i, β i} : hammingNorm x = 0 ↔ x = 0 :=
  hammingDist_eq_zero

/-- Corresponds to `norm_ne_zero_iff`. -/
theorem hammingNorm_ne_zero_iff {x : ∀ i, β i} : hammingNorm x ≠ 0 ↔ x ≠ 0 :=
  hammingNorm_eq_zero.not

/-- Corresponds to `norm_pos_iff`. -/
@[simp]
theorem hammingNorm_pos_iff {x : ∀ i, β i} : 0 < hammingNorm x ↔ x ≠ 0 :=
  hammingDist_pos

theorem hammingNorm_lt_one {x : ∀ i, β i} : hammingNorm x < 1 ↔ x = 0 :=
  hammingDist_lt_one

theorem hammingNorm_le_card_fintype {x : ∀ i, β i} : hammingNorm x ≤ Fintype.card ι :=
  hammingDist_le_card_fintype

theorem hammingNorm_map_le_hammingNorm (f : ∀ i, β i → γ i) {x : ∀ i, β i}
    (hf : ∀ i, f i 0 = 0) : (hammingNorm (Pi.map f x)) ≤ hammingNorm x := by
  simp_rw [← hammingDist_zero_right]
  convert hammingDist_map_map_le_hammingDist f (x := x) (y := 0)
  ext
  simp only [Pi.zero_apply, Pi.map_apply, hf]

theorem hammingNorm_map_of_injective (f : ∀ i, β i → γ i) {x : ∀ i, β i}
    (hf₁ : ∀ i, Injective (f i)) (hf₂ : ∀ i, f i 0 = 0) :
    (hammingNorm (Pi.map f x)) = hammingNorm x := by
  simp_rw [← hammingDist_zero_right]
  convert hammingDist_map_map_of_injective f (x := x) (y := 0) hf₁
  ext
  simp only [Pi.zero_apply, Pi.map_apply, hf₂]

theorem hammingNorm_smul_le_hammingNorm [Zero α] [∀ i, SMulWithZero α (β i)] {k : α}
    {x : ∀ i, β i} : hammingNorm (k • x) ≤ hammingNorm x :=
  hammingNorm_map_le_hammingNorm (fun i (c : β i) => k • c) fun i => by simp_rw [smul_zero]

theorem hammingNorm_smul [Zero α] [∀ i, SMulWithZero α (β i)] {k : α}
    (hk : ∀ i, IsSMulRegular (β i) k) {x : ∀ i, β i} : hammingNorm (k • x) = hammingNorm x :=
  hammingNorm_map_of_injective (fun i (c : β i) => k • c) hk fun i => by simp_rw [smul_zero]

end Zero

/-- Corresponds to `dist_eq_norm`. -/
theorem hammingDist_eq_hammingNorm [∀ i, AddGroup (β i)] (x y : ∀ i, β i) :
    hammingDist x y = hammingNorm (x - y) := by
  simp_rw [hammingNorm, hammingDist, Pi.sub_apply, sub_ne_zero]

end HammingDistNorm

/-! ### The `Hamming` type synonym -/

/-- Type synonym for a Pi type which inherits the usual algebraic instances, but is equipped with
the Hamming metric and norm, instead of `Pi.normedAddCommGroup` which uses the sup norm. -/
structure Hamming {ι : Type*} (β : ι → Type*) where
  /-- The `i`-th coordinate of the Hamming type. -/
  of (i : ι) : β i

namespace Hamming

variable {α ι : Type*} {β γ : ι → Type*}

/-- `Hamming.ofEquiv` is the equivalence between `Hamming` and the corresponding Pi type. -/
@[simps]
def ofEquiv : Hamming β ≃ ∀ i, β i where
  toFun := of
  invFun := mk

@[simp] theorem of_inj {a b : Hamming β} : a.of = b.of ↔ a = b := ofEquiv.injective.eq_iff

@[ext] protected theorem ext {a b : Hamming β} (h : a.of = b.of) : a = b := ofEquiv.injective h

/-- The coordinate-wise map between Hamming types. -/
@[simps]
def map (f : ∀ i, γ i → β i) (x : Hamming γ) : Hamming β where
  of := Pi.map f x.of

/-! Instances inherited from normal Pi types. -/

instance [∀ i, Inhabited (β i)] : Inhabited (Hamming β) := ofEquiv.inhabited

instance [DecidableEq ι] [Fintype ι] [∀ i, Fintype (β i)] : Fintype (Hamming β) :=
  Fintype.ofEquiv _ ofEquiv.symm

instance [Inhabited ι] [∀ i, Nonempty (β i)] [Nontrivial (β default)] : Nontrivial (Hamming β) :=
  ofEquiv.nontrivial

instance [Fintype ι] [∀ i, DecidableEq (β i)] : DecidableEq (Hamming β) := ofEquiv.decidableEq

instance [∀ i, Zero (β i)] : Zero (Hamming β) := ofEquiv.zero

instance [∀ i, Neg (β i)] : Neg (Hamming β) := ofEquiv.Neg

instance [∀ i, Add (β i)] : Add (Hamming β) := ofEquiv.add

instance [∀ i, Sub (β i)] : Sub (Hamming β) := ofEquiv.sub

instance [∀ i, SMul α (β i)] : SMul α (Hamming β) := ofEquiv.smul _

instance [Zero α] [∀ i, Zero (β i)] [∀ i, SMulWithZero α (β i)] : SMulWithZero α (Hamming β) where
  smul_zero _ := Hamming.ext <| funext <| fun _ => smul_zero _
  zero_smul _ := Hamming.ext <| funext <| fun _ => zero_smul _ _

instance [∀ i, AddMonoid (β i)] : AddMonoid (Hamming β) := ofEquiv.addMonoid

instance [∀ i, AddGroup (β i)] : AddGroup (Hamming β) := ofEquiv.addGroup

instance [∀ i, AddCommMonoid (β i)] : AddCommMonoid (Hamming β) := ofEquiv.addCommMonoid

instance [∀ i, AddCommGroup (β i)] : AddCommGroup (Hamming β) := ofEquiv.addCommGroup

instance [Semiring α] [∀ i, AddCommMonoid (β i)] [∀ i, Module α (β i)] :
    Module α (Hamming β) := ofEquiv.module α

/-- `Hamming.ofEquiv` as an `AddEquiv`. -/
def ofAddEquiv [∀ i, Add (β i)] : Hamming β ≃+ ∀ i, β i := ofEquiv.addEquiv

/-- `Hamming.ofEquiv` as a `LinearEquiv`. -/
def ofLinearEquiv (α) [Semiring α] [∀ i, AddCommMonoid (β i)] [∀ i, Module α (β i)] :
  Hamming β ≃ₗ[α] ∀ i, β i := ofEquiv.linearEquiv α

section

/-! Instances equipping `Hamming` with `hammingNorm` and `hammingDist`. -/

variable [Fintype ι] [∀ i, DecidableEq (β i)] [∀ i, DecidableEq (γ i)] {x y : Hamming β}
    (f : ∀ i, β i → γ i)

instance : Dist (Hamming β) :=
  ⟨fun x y => hammingDist x.of y.of⟩

@[push_cast]
theorem dist_eq_hammingDist :
    dist x y = hammingDist x.of y.of := rfl

theorem dist_lt_one : dist x y < 1 ↔ x = y := by
  rw [Hamming.ext_iff]
  push_cast
  exact mod_cast hammingDist_lt_one

theorem dist_le_card : dist x y ≤ Fintype.card ι := by
  push_cast
  exact mod_cast hammingDist_le_card_fintype

theorem dist_map_map_le_dist : dist (x.map f) (y.map f) ≤ dist x y := by
  push_cast
  exact mod_cast hammingDist_map_map_le_hammingDist f

theorem dist_map_map_of_injective (hf : ∀ i, Function.Injective (f i)) :
    dist (x.map f) (y.map f) = dist x y := by
  push_cast
  exact mod_cast hammingDist_map_map_of_injective f hf

theorem dist_smul_le_dist [∀ i, SMul α (β i)] {k : α} : dist (k • x) (k • y) ≤ dist x y := by
  push_cast
  exact mod_cast hammingDist_smul_le_hammingDist

theorem dist_smul [∀ i, SMul α (β i)] {k : α} (hk : ∀ i, IsSMulRegular (β i) k) :
    dist (k • x) (k • y) = dist x y := by
  push_cast
  exact mod_cast hammingDist_smul hk

instance : PseudoMetricSpace (Hamming β) where
  dist_self _ := by
    push_cast
    exact mod_cast hammingDist_self _
  dist_comm _ _ := by
    push_cast
    exact mod_cast hammingDist_comm _ _
  dist_triangle _ _ _ := by
    push_cast
    exact mod_cast hammingDist_triangle _ _ _
  toUniformSpace := ⊥
  uniformity_dist := uniformity_dist_of_mem_uniformity _ _ fun s => by
    constructor
    · exact fun hs => ⟨1, zero_lt_one, fun hab => hs (dist_lt_one.mp hab)⟩
    · rintro ⟨_, hε, hs⟩ ⟨_, _⟩ hab
      refine hs (hε.trans_eq' ?_)
      push_cast; exact mod_cast hammingDist_eq_zero.mpr <| of_inj.mpr hab
  toBornology := ⟨⊥, bot_le⟩
  cobounded_sets := Set.ext <| fun _ =>
    iff_of_true (Filter.mem_sets.mpr Filter.mem_bot) ⟨Fintype.card ι, fun _ _ _ _ => dist_le_card⟩

@[push_cast]
theorem nndist_eq_hammingDist :
    nndist x y = hammingDist x.of y.of :=
  rfl

instance : DiscreteTopology (Hamming β) := ⟨rfl⟩

instance : MetricSpace (Hamming β) := .ofT0PseudoMetricSpace _

section

variable [∀ i, Zero (β i)] [∀ i, Zero (γ i)]

instance : Norm (Hamming β) := ⟨fun x => hammingNorm x.of⟩

theorem norm_lt_one {x : Hamming β} : ‖x‖ < 1 ↔ x = 0 := dist_lt_one (y := 0)

theorem norm_le_card {x : Hamming β} : ‖x‖ ≤ Fintype.card ι := dist_le_card (y := 0)

@[push_cast] theorem norm_eq_hammingNorm : ‖x‖ = hammingNorm x.of := rfl

theorem norm_map_le_norm (hf : ∀ i, f i 0 = 0) : ‖x.map f‖ ≤ ‖x‖ := by
  push_cast
  exact mod_cast hammingNorm_map_le_hammingNorm f hf

theorem norm_map_of_injective (hf₁ : ∀ i, Function.Injective (f i)) (hf₂ : ∀ i, f i 0 = 0) :
    ‖x.map f‖ = ‖x‖ := by
  push_cast
  exact mod_cast hammingNorm_map_of_injective f hf₁ hf₂

theorem norm_smul_le_norm [Zero α] [∀ i, SMulWithZero α (β i)] {k : α} : ‖k • x‖ ≤ ‖x‖ := by
  push_cast
  exact mod_cast hammingNorm_smul_le_hammingNorm

theorem norm_smul [Zero α] [∀ i, SMulWithZero α (β i)] {k : α} (hk : ∀ i, IsSMulRegular (β i) k) :
    ‖k • x‖ = ‖x‖ := by
  push_cast
  exact mod_cast hammingNorm_smul hk

end

instance [∀ i, AddGroup (β i)] : NormedAddGroup (Hamming β) where
  dist_eq _ _ := by push_cast; exact mod_cast hammingDist_eq_hammingNorm _ _

instance [∀ i, AddCommGroup (β i)] : NormedAddCommGroup (Hamming β) where
  dist_eq := fun x y => NormedAddGroup.dist_eq x y

@[push_cast]
theorem nnnorm_eq_hammingNorm [∀ i, AddGroup (β i)] :
    ‖x‖₊ = hammingNorm x.of := rfl

end

end Hamming

