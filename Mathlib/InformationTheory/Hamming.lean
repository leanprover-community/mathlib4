/-
Copyright (c) 2022 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
import Mathlib.Analysis.Normed.Group.Basic

#align_import information_theory.hamming from "leanprover-community/mathlib"@"17ef379e997badd73e5eabb4d38f11919ab3c4b3"

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
def hammingDist (x y : ∀ i, β i) : ℕ :=
  (univ.filter fun i => x i ≠ y i).card
#align hamming_dist hammingDist

/-- Corresponds to `dist_self`. -/
@[simp]
theorem hammingDist_self (x : ∀ i, β i) : hammingDist x x = 0 := by
  rw [hammingDist, card_eq_zero, filter_eq_empty_iff]
  -- ⊢ ∀ (x_1 : ι), x_1 ∈ univ → ¬x x_1 ≠ x x_1
  exact fun _ _ H => H rfl
  -- 🎉 no goals
#align hamming_dist_self hammingDist_self

/-- Corresponds to `dist_nonneg`. -/
theorem hammingDist_nonneg {x y : ∀ i, β i} : 0 ≤ hammingDist x y :=
  zero_le _
#align hamming_dist_nonneg hammingDist_nonneg

/-- Corresponds to `dist_comm`. -/
theorem hammingDist_comm (x y : ∀ i, β i) : hammingDist x y = hammingDist y x := by
  simp_rw [hammingDist, ne_comm]
  -- 🎉 no goals
#align hamming_dist_comm hammingDist_comm

/-- Corresponds to `dist_triangle`. -/
theorem hammingDist_triangle (x y z : ∀ i, β i) :
    hammingDist x z ≤ hammingDist x y + hammingDist y z := by
  classical
    unfold hammingDist
    refine le_trans (card_mono ?_) (card_union_le _ _)
    rw [← filter_or]
    exact monotone_filter_right _ fun i h ↦ (h.ne_or_ne _).imp_right Ne.symm
#align hamming_dist_triangle hammingDist_triangle

/-- Corresponds to `dist_triangle_left`. -/
theorem hammingDist_triangle_left (x y z : ∀ i, β i) :
    hammingDist x y ≤ hammingDist z x + hammingDist z y := by
  rw [hammingDist_comm z]
  -- ⊢ hammingDist x y ≤ hammingDist x z + hammingDist z y
  exact hammingDist_triangle _ _ _
  -- 🎉 no goals
#align hamming_dist_triangle_left hammingDist_triangle_left

/-- Corresponds to `dist_triangle_right`. -/
theorem hammingDist_triangle_right (x y z : ∀ i, β i) :
    hammingDist x y ≤ hammingDist x z + hammingDist y z := by
  rw [hammingDist_comm y]
  -- ⊢ hammingDist x y ≤ hammingDist x z + hammingDist z y
  exact hammingDist_triangle _ _ _
  -- 🎉 no goals
#align hamming_dist_triangle_right hammingDist_triangle_right

/-- Corresponds to `swap_dist`. -/
theorem swap_hammingDist : swap (@hammingDist _ β _ _) = hammingDist := by
  funext x y
  -- ⊢ swap hammingDist x y = hammingDist x y
  exact hammingDist_comm _ _
  -- 🎉 no goals
#align swap_hamming_dist swap_hammingDist

/-- Corresponds to `eq_of_dist_eq_zero`. -/
theorem eq_of_hammingDist_eq_zero {x y : ∀ i, β i} : hammingDist x y = 0 → x = y := by
  simp_rw [hammingDist, card_eq_zero, filter_eq_empty_iff, Classical.not_not, funext_iff, mem_univ,
    forall_true_left, imp_self]
#align eq_of_hamming_dist_eq_zero eq_of_hammingDist_eq_zero

/-- Corresponds to `dist_eq_zero`. -/
@[simp]
theorem hammingDist_eq_zero {x y : ∀ i, β i} : hammingDist x y = 0 ↔ x = y :=
  ⟨eq_of_hammingDist_eq_zero, fun H => by
    rw [H]
    -- ⊢ hammingDist y y = 0
    exact hammingDist_self _⟩
    -- 🎉 no goals
#align hamming_dist_eq_zero hammingDist_eq_zero

/-- Corresponds to `zero_eq_dist`. -/
@[simp]
theorem hamming_zero_eq_dist {x y : ∀ i, β i} : 0 = hammingDist x y ↔ x = y := by
  rw [eq_comm, hammingDist_eq_zero]
  -- 🎉 no goals
#align hamming_zero_eq_dist hamming_zero_eq_dist

/-- Corresponds to `dist_ne_zero`. -/
theorem hammingDist_ne_zero {x y : ∀ i, β i} : hammingDist x y ≠ 0 ↔ x ≠ y :=
  hammingDist_eq_zero.not
#align hamming_dist_ne_zero hammingDist_ne_zero

/-- Corresponds to `dist_pos`. -/
@[simp]
theorem hammingDist_pos {x y : ∀ i, β i} : 0 < hammingDist x y ↔ x ≠ y := by
  rw [← hammingDist_ne_zero, iff_not_comm, not_lt, le_zero_iff]
  -- 🎉 no goals
#align hamming_dist_pos hammingDist_pos

-- @[simp] -- Porting note: simp can prove this
theorem hammingDist_lt_one {x y : ∀ i, β i} : hammingDist x y < 1 ↔ x = y := by
  rw [Nat.lt_one_iff, hammingDist_eq_zero]
  -- 🎉 no goals
#align hamming_dist_lt_one hammingDist_lt_one

theorem hammingDist_le_card_fintype {x y : ∀ i, β i} : hammingDist x y ≤ Fintype.card ι :=
  card_le_univ _
#align hamming_dist_le_card_fintype hammingDist_le_card_fintype

theorem hammingDist_comp_le_hammingDist (f : ∀ i, γ i → β i) {x y : ∀ i, γ i} :
    (hammingDist (fun i => f i (x i)) fun i => f i (y i)) ≤ hammingDist x y :=
  card_mono (monotone_filter_right _ fun i H1 H2 => H1 <| congr_arg (f i) H2)
#align hamming_dist_comp_le_hamming_dist hammingDist_comp_le_hammingDist

theorem hammingDist_comp (f : ∀ i, γ i → β i) {x y : ∀ i, γ i} (hf : ∀ i, Injective (f i)) :
    (hammingDist (fun i => f i (x i)) fun i => f i (y i)) = hammingDist x y :=
  le_antisymm (hammingDist_comp_le_hammingDist _) <|
    card_mono (monotone_filter_right _ fun i H1 H2 => H1 <| hf i H2)
#align hamming_dist_comp hammingDist_comp

theorem hammingDist_smul_le_hammingDist [∀ i, SMul α (β i)] {k : α} {x y : ∀ i, β i} :
    hammingDist (k • x) (k • y) ≤ hammingDist x y :=
  hammingDist_comp_le_hammingDist fun i => (k • · : β i → β i)
#align hamming_dist_smul_le_hamming_dist hammingDist_smul_le_hammingDist

/-- Corresponds to `dist_smul` with the discrete norm on `α`. -/
theorem hammingDist_smul [∀ i, SMul α (β i)] {k : α} {x y : ∀ i, β i}
    (hk : ∀ i, IsSMulRegular (β i) k) : hammingDist (k • x) (k • y) = hammingDist x y :=
  hammingDist_comp (fun i => (k • · : β i → β i)) hk
#align hamming_dist_smul hammingDist_smul

section Zero

variable [∀ i, Zero (β i)] [∀ i, Zero (γ i)]

/-- The Hamming weight function to the naturals. -/
def hammingNorm (x : ∀ i, β i) : ℕ :=
  (univ.filter (x · ≠ 0)).card
#align hamming_norm hammingNorm

/-- Corresponds to `dist_zero_right`. -/
@[simp]
theorem hammingDist_zero_right (x : ∀ i, β i) : hammingDist x 0 = hammingNorm x :=
  rfl
#align hamming_dist_zero_right hammingDist_zero_right

/-- Corresponds to `dist_zero_left`. -/
@[simp]
theorem hammingDist_zero_left : hammingDist (0 : ∀ i, β i) = hammingNorm :=
  funext fun x => by rw [hammingDist_comm, hammingDist_zero_right]
                     -- 🎉 no goals
#align hamming_dist_zero_left hammingDist_zero_left

/-- Corresponds to `norm_nonneg`. -/
-- @[simp] -- Porting note: simp can prove this
theorem hammingNorm_nonneg {x : ∀ i, β i} : 0 ≤ hammingNorm x :=
  zero_le _
#align hamming_norm_nonneg hammingNorm_nonneg

/-- Corresponds to `norm_zero`. -/
@[simp]
theorem hammingNorm_zero : hammingNorm (0 : ∀ i, β i) = 0 :=
  hammingDist_self _
#align hamming_norm_zero hammingNorm_zero

/-- Corresponds to `norm_eq_zero`. -/
@[simp]
theorem hammingNorm_eq_zero {x : ∀ i, β i} : hammingNorm x = 0 ↔ x = 0 :=
  hammingDist_eq_zero
#align hamming_norm_eq_zero hammingNorm_eq_zero

/-- Corresponds to `norm_ne_zero_iff`. -/
theorem hammingNorm_ne_zero_iff {x : ∀ i, β i} : hammingNorm x ≠ 0 ↔ x ≠ 0 :=
  hammingNorm_eq_zero.not
#align hamming_norm_ne_zero_iff hammingNorm_ne_zero_iff

/-- Corresponds to `norm_pos_iff`. -/
@[simp]
theorem hammingNorm_pos_iff {x : ∀ i, β i} : 0 < hammingNorm x ↔ x ≠ 0 :=
  hammingDist_pos
#align hamming_norm_pos_iff hammingNorm_pos_iff

-- @[simp] -- Porting note: simp can prove this
theorem hammingNorm_lt_one {x : ∀ i, β i} : hammingNorm x < 1 ↔ x = 0 :=
  hammingDist_lt_one
#align hamming_norm_lt_one hammingNorm_lt_one

theorem hammingNorm_le_card_fintype {x : ∀ i, β i} : hammingNorm x ≤ Fintype.card ι :=
  hammingDist_le_card_fintype
#align hamming_norm_le_card_fintype hammingNorm_le_card_fintype

theorem hammingNorm_comp_le_hammingNorm (f : ∀ i, γ i → β i) {x : ∀ i, γ i} (hf : ∀ i, f i 0 = 0) :
    (hammingNorm fun i => f i (x i)) ≤ hammingNorm x := by
  simpa only [← hammingDist_zero_right, hf] using hammingDist_comp_le_hammingDist f (y := fun _ ↦ 0)
  -- 🎉 no goals
#align hamming_norm_comp_le_hamming_norm hammingNorm_comp_le_hammingNorm

theorem hammingNorm_comp (f : ∀ i, γ i → β i) {x : ∀ i, γ i} (hf₁ : ∀ i, Injective (f i))
    (hf₂ : ∀ i, f i 0 = 0) : (hammingNorm fun i => f i (x i)) = hammingNorm x := by
  simpa only [← hammingDist_zero_right, hf₂] using hammingDist_comp f hf₁ (y := fun _ ↦ 0)
  -- 🎉 no goals
#align hamming_norm_comp hammingNorm_comp

theorem hammingNorm_smul_le_hammingNorm [Zero α] [∀ i, SMulWithZero α (β i)] {k : α}
    {x : ∀ i, β i} : hammingNorm (k • x) ≤ hammingNorm x :=
  hammingNorm_comp_le_hammingNorm (fun i (c : β i) => k • c) fun i => by simp_rw [smul_zero]
                                                                         -- 🎉 no goals
#align hamming_norm_smul_le_hamming_norm hammingNorm_smul_le_hammingNorm

theorem hammingNorm_smul [Zero α] [∀ i, SMulWithZero α (β i)] {k : α}
    (hk : ∀ i, IsSMulRegular (β i) k) (x : ∀ i, β i) : hammingNorm (k • x) = hammingNorm x :=
  hammingNorm_comp (fun i (c : β i) => k • c) hk fun i => by simp_rw [smul_zero]
                                                             -- 🎉 no goals
#align hamming_norm_smul hammingNorm_smul

end Zero

/-- Corresponds to `dist_eq_norm`. -/
theorem hammingDist_eq_hammingNorm [∀ i, AddGroup (β i)] (x y : ∀ i, β i) :
    hammingDist x y = hammingNorm (x - y) := by
  simp_rw [hammingNorm, hammingDist, Pi.sub_apply, sub_ne_zero]
  -- 🎉 no goals
#align hamming_dist_eq_hamming_norm hammingDist_eq_hammingNorm

end HammingDistNorm

/-! ### The `Hamming` type synonym -/


/-- Type synonym for a Pi type which inherits the usual algebraic instances, but is equipped with
the Hamming metric and norm, instead of `Pi.normedAddCommGroup` which uses the sup norm. -/
def Hamming {ι : Type*} (β : ι → Type*) : Type _ :=
  ∀ i, β i
#align hamming Hamming

namespace Hamming

variable {α ι : Type*} {β : ι → Type*}

/-! Instances inherited from normal Pi types. -/

instance [∀ i, Inhabited (β i)] : Inhabited (Hamming β) :=
  ⟨fun _ => default⟩

instance [DecidableEq ι] [Fintype ι] [∀ i, Fintype (β i)] : Fintype (Hamming β) :=
  Pi.fintype

instance [Inhabited ι] [∀ i, Nonempty (β i)] [Nontrivial (β default)] : Nontrivial (Hamming β) :=
  Pi.nontrivial

instance [Fintype ι] [∀ i, DecidableEq (β i)] : DecidableEq (Hamming β) :=
  Fintype.decidablePiFintype

instance [∀ i, Zero (β i)] : Zero (Hamming β) :=
  Pi.instZero

instance [∀ i, Neg (β i)] : Neg (Hamming β) :=
  Pi.instNeg

instance [∀ i, Add (β i)] : Add (Hamming β) :=
  Pi.instAdd

instance [∀ i, Sub (β i)] : Sub (Hamming β) :=
  Pi.instSub

instance [∀ i, SMul α (β i)] : SMul α (Hamming β) :=
  Pi.instSMul

instance [Zero α] [∀ i, Zero (β i)] [∀ i, SMulWithZero α (β i)] : SMulWithZero α (Hamming β) :=
  Pi.smulWithZero _

instance [∀ i, AddMonoid (β i)] : AddMonoid (Hamming β) :=
  Pi.addMonoid

instance [∀ i, AddCommMonoid (β i)] : AddCommMonoid (Hamming β) :=
  Pi.addCommMonoid

instance [∀ i, AddCommGroup (β i)] : AddCommGroup (Hamming β) :=
  Pi.addCommGroup

instance (α) [Semiring α] (β : ι → Type*) [∀ i, AddCommMonoid (β i)] [∀ i, Module α (β i)] :
    Module α (Hamming β) :=
  Pi.module _ _ _

/-! API to/from the type synonym. -/


/-- `Hamming.toHamming` is the identity function to the `Hamming` of a type.  -/
@[match_pattern]
def toHamming : (∀ i, β i) ≃ Hamming β :=
  Equiv.refl _
#align hamming.to_hamming Hamming.toHamming

/-- `Hamming.ofHamming` is the identity function from the `Hamming` of a type.  -/
@[match_pattern]
def ofHamming : Hamming β ≃ ∀ i, β i :=
  Equiv.refl _
#align hamming.of_hamming Hamming.ofHamming

@[simp]
theorem toHamming_symm_eq : (@toHamming _ β).symm = ofHamming :=
  rfl
#align hamming.to_hamming_symm_eq Hamming.toHamming_symm_eq

@[simp]
theorem ofHamming_symm_eq : (@ofHamming _ β).symm = toHamming :=
  rfl
#align hamming.of_hamming_symm_eq Hamming.ofHamming_symm_eq

@[simp]
theorem toHamming_ofHamming (x : Hamming β) : toHamming (ofHamming x) = x :=
  rfl
#align hamming.to_hamming_of_hamming Hamming.toHamming_ofHamming

@[simp]
theorem ofHamming_toHamming (x : ∀ i, β i) : ofHamming (toHamming x) = x :=
  rfl
#align hamming.of_hamming_to_hamming Hamming.ofHamming_toHamming

--@[simp] --Porting note: removing `simp`, `simp` can prove it and `dsimp` cannot use `Iff.rfl`
theorem toHamming_inj {x y : ∀ i, β i} : toHamming x = toHamming y ↔ x = y :=
  Iff.rfl
#align hamming.to_hamming_inj Hamming.toHamming_inj

--@[simp] --Porting note: removing `simp`, `simp` can prove it and `dsimp` cannot use `Iff.rfl`
theorem ofHamming_inj {x y : Hamming β} : ofHamming x = ofHamming y ↔ x = y :=
  Iff.rfl
#align hamming.of_hamming_inj Hamming.ofHamming_inj

@[simp]
theorem toHamming_zero [∀ i, Zero (β i)] : toHamming (0 : ∀ i, β i) = 0 :=
  rfl
#align hamming.to_hamming_zero Hamming.toHamming_zero

@[simp]
theorem ofHamming_zero [∀ i, Zero (β i)] : ofHamming (0 : Hamming β) = 0 :=
  rfl
#align hamming.of_hamming_zero Hamming.ofHamming_zero

@[simp]
theorem toHamming_neg [∀ i, Neg (β i)] {x : ∀ i, β i} : toHamming (-x) = -toHamming x :=
  rfl
#align hamming.to_hamming_neg Hamming.toHamming_neg

@[simp]
theorem ofHamming_neg [∀ i, Neg (β i)] {x : Hamming β} : ofHamming (-x) = -ofHamming x :=
  rfl
#align hamming.of_hamming_neg Hamming.ofHamming_neg

@[simp]
theorem toHamming_add [∀ i, Add (β i)] {x y : ∀ i, β i} :
    toHamming (x + y) = toHamming x + toHamming y :=
  rfl
#align hamming.to_hamming_add Hamming.toHamming_add

@[simp]
theorem ofHamming_add [∀ i, Add (β i)] {x y : Hamming β} :
    ofHamming (x + y) = ofHamming x + ofHamming y :=
  rfl
#align hamming.of_hamming_add Hamming.ofHamming_add

@[simp]
theorem toHamming_sub [∀ i, Sub (β i)] {x y : ∀ i, β i} :
    toHamming (x - y) = toHamming x - toHamming y :=
  rfl
#align hamming.to_hamming_sub Hamming.toHamming_sub

@[simp]
theorem ofHamming_sub [∀ i, Sub (β i)] {x y : Hamming β} :
    ofHamming (x - y) = ofHamming x - ofHamming y :=
  rfl
#align hamming.of_hamming_sub Hamming.ofHamming_sub

@[simp]
theorem toHamming_smul [∀ i, SMul α (β i)] {r : α} {x : ∀ i, β i} :
    toHamming (r • x) = r • toHamming x :=
  rfl
#align hamming.to_hamming_smul Hamming.toHamming_smul

@[simp]
theorem ofHamming_smul [∀ i, SMul α (β i)] {r : α} {x : Hamming β} :
    ofHamming (r • x) = r • ofHamming x :=
  rfl
#align hamming.of_hamming_smul Hamming.ofHamming_smul

section

/-! Instances equipping `Hamming` with `hammingNorm` and `hammingDist`. -/

variable [Fintype ι] [∀ i, DecidableEq (β i)]

instance : Dist (Hamming β) :=
  ⟨fun x y => hammingDist (ofHamming x) (ofHamming y)⟩

@[simp, push_cast]
theorem dist_eq_hammingDist (x y : Hamming β) :
    dist x y = hammingDist (ofHamming x) (ofHamming y) :=
  rfl
#align hamming.dist_eq_hamming_dist Hamming.dist_eq_hammingDist

instance : PseudoMetricSpace (Hamming β) where
  dist_self := by
    push_cast
    -- ⊢ ∀ (x : Hamming β), ↑(hammingDist (↑ofHamming x) (↑ofHamming x)) = 0
    exact_mod_cast hammingDist_self
    -- 🎉 no goals
  dist_comm := by
    push_cast
    -- ⊢ ∀ (x y : Hamming β), ↑(hammingDist (↑ofHamming x) (↑ofHamming y)) = ↑(hammin …
    exact_mod_cast hammingDist_comm
    -- 🎉 no goals
  dist_triangle := by
    push_cast
    -- ⊢ ∀ (x y z : Hamming β), ↑(hammingDist (↑ofHamming x) (↑ofHamming z)) ≤ ↑(hamm …
    exact_mod_cast hammingDist_triangle
    -- 🎉 no goals
  edist_dist _ _ := by exact ENNReal.coe_nnreal_eq _
                       -- 🎉 no goals
  toUniformSpace := ⊥
  uniformity_dist := uniformity_dist_of_mem_uniformity _ _ fun s => by
    push_cast
    -- ⊢ s ∈ uniformity (Hamming β) ↔ ∃ ε, ε > 0 ∧ ∀ {a b : Hamming β}, ↑(hammingDist …
    constructor
    -- ⊢ s ∈ uniformity (Hamming β) → ∃ ε, ε > 0 ∧ ∀ {a b : Hamming β}, ↑(hammingDist …
    · refine' fun hs => ⟨1, zero_lt_one, fun hab => _⟩
      -- ⊢ (a✝, b✝) ∈ s
      rw_mod_cast [hammingDist_lt_one] at hab
      -- ⊢ (a✝, b✝) ∈ s
      rw [ofHamming_inj, ← mem_idRel] at hab
      -- ⊢ (a✝, b✝) ∈ s
      exact hs hab
      -- 🎉 no goals
    · rintro ⟨_, hε, hs⟩ ⟨_, _⟩ hab
      -- ⊢ (fst✝, snd✝) ∈ s
      rw [mem_idRel] at hab
      -- ⊢ (fst✝, snd✝) ∈ s
      rw [hab]
      -- ⊢ (snd✝, snd✝) ∈ s
      refine' hs (lt_of_eq_of_lt _ hε)
      -- ⊢ ↑(hammingDist (↑ofHamming snd✝) (↑ofHamming snd✝)) = 0
      exact_mod_cast hammingDist_self _
      -- 🎉 no goals
  toBornology := ⟨⊥, bot_le⟩
  cobounded_sets := by
    ext
    -- ⊢ x✝ ∈ (Bornology.cobounded (Hamming β)).sets ↔ x✝ ∈ {s | ∃ C, ∀ (x : Hamming  …
    push_cast
    -- ⊢ x✝ ∈ (Bornology.cobounded (Hamming β)).sets ↔ x✝ ∈ {s | ∃ C, ∀ (x : Hamming  …
    refine' iff_of_true (Filter.mem_sets.mpr Filter.mem_bot) ⟨Fintype.card ι, fun _ _ _ _ => _⟩
    -- ⊢ ↑(hammingDist (↑ofHamming x✝³) (↑ofHamming x✝¹)) ≤ ↑(Fintype.card ι)
    exact_mod_cast hammingDist_le_card_fintype
    -- 🎉 no goals

@[simp, push_cast]
theorem nndist_eq_hammingDist (x y : Hamming β) :
    nndist x y = hammingDist (ofHamming x) (ofHamming y) :=
  rfl
#align hamming.nndist_eq_hamming_dist Hamming.nndist_eq_hammingDist

-- porting note: new
instance : DiscreteTopology (Hamming β) := ⟨rfl⟩

instance : MetricSpace (Hamming β) := .ofT0PseudoMetricSpace _

instance [∀ i, Zero (β i)] : Norm (Hamming β) :=
  ⟨fun x => hammingNorm (ofHamming x)⟩

@[simp, push_cast]
theorem norm_eq_hammingNorm [∀ i, Zero (β i)] (x : Hamming β) : ‖x‖ = hammingNorm (ofHamming x) :=
  rfl
#align hamming.norm_eq_hamming_norm Hamming.norm_eq_hammingNorm

-- porting note: merged `SeminormedAddCommGroup` and `NormedAddCommGroup` instances

instance [∀ i, AddCommGroup (β i)] : NormedAddCommGroup (Hamming β) where
  dist_eq := by push_cast; exact_mod_cast hammingDist_eq_hammingNorm
                -- ⊢ ∀ (x y : Hamming β), ↑(hammingDist (↑ofHamming x) (↑ofHamming y)) = ↑(hammin …
                           -- 🎉 no goals

@[simp, push_cast]
theorem nnnorm_eq_hammingNorm [∀ i, AddCommGroup (β i)] (x : Hamming β) :
    ‖x‖₊ = hammingNorm (ofHamming x) :=
  rfl
#align hamming.nnnorm_eq_hamming_norm Hamming.nnnorm_eq_hammingNorm

end

end Hamming
