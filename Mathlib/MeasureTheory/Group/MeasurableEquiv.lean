/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module measure_theory.group.measurable_equiv
! leanprover-community/mathlib commit 95413e23e3d29b45c701fcd31f2dbadaf1b79cba
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Group.Arithmetic

/-!
# (Scalar) multiplication and (vector) addition as measurable equivalences

In this file we define the following measurable equivalences:

* `measurable_equiv.smul`: if a group `G` acts on `α` by measurable maps, then each element `c : G`
  defines a measurable automorphism of `α`;
* `measurable_equiv.vadd`: additive version of `measurable_equiv.smul`;
* `measurable_equiv.smul₀`: if a group with zero `G` acts on `α` by measurable maps, then each
  nonzero element `c : G` defines a measurable automorphism of `α`;
* `measurable_equiv.mul_left`: if `G` is a group with measurable multiplication, then left
  multiplication by `g : G` is a measurable automorphism of `G`;
* `measurable_equiv.add_left`: additive version of `measurable_equiv.mul_left`;
* `measurable_equiv.mul_right`: if `G` is a group with measurable multiplication, then right
  multiplication by `g : G` is a measurable automorphism of `G`;
* `measurable_equiv.add_right`: additive version of `measurable_equiv.mul_right`;
* `measurable_equiv.mul_left₀`, `measurable_equiv.mul_right₀`: versions of
  `measurable_equiv.mul_left` and `measurable_equiv.mul_right` for groups with zero;
* `measurable_equiv.inv`: `has_inv.inv` as a measurable automorphism
  of a group (or a group with zero);
* `measurable_equiv.neg`: negation as a measurable automorphism of an additive group.

We also deduce that the corresponding maps are measurable embeddings.

## Tags

measurable, equivalence, group action
-/


namespace MeasurableEquiv

variable {G G₀ α : Type _} [MeasurableSpace G] [MeasurableSpace G₀] [MeasurableSpace α] [Group G]
  [GroupWithZero G₀] [MulAction G α] [MulAction G₀ α] [MeasurableSMul G α] [MeasurableSMul G₀ α]

/-- If a group `G` acts on `α` by measurable maps, then each element `c : G` defines a measurable
automorphism of `α`. -/
@[to_additive
      "If an additive group `G` acts on `α` by measurable maps, then each element `c : G`\ndefines a measurable automorphism of `α`.",
  simps (config := { fullyApplied := false }) toEquiv apply]
def smul (c : G) : α ≃ᵐ α where
  toEquiv := MulAction.toPerm c
  measurable_to_fun := measurable_const_smul c
  measurable_inv_fun := measurable_const_smul c⁻¹
#align measurable_equiv.smul MeasurableEquiv.smul
#align measurable_equiv.vadd MeasurableEquiv.vadd

@[to_additive]
theorem measurableEmbedding_const_smul (c : G) : MeasurableEmbedding ((· • ·) c : α → α) :=
  (smul c).MeasurableEmbedding
#align measurable_embedding_const_smul measurableEmbedding_const_smul
#align measurable_embedding_const_vadd measurableEmbedding_const_vadd

@[simp, to_additive]
theorem symm_smul (c : G) : (smul c : α ≃ᵐ α).symm = smul c⁻¹ :=
  ext rfl
#align measurable_equiv.symm_smul MeasurableEquiv.symm_smul
#align measurable_equiv.symm_vadd MeasurableEquiv.symm_vadd

/-- If a group with zero `G₀` acts on `α` by measurable maps, then each nonzero element `c : G₀`
defines a measurable automorphism of `α` -/
def smul₀ (c : G₀) (hc : c ≠ 0) : α ≃ᵐ α :=
  MeasurableEquiv.smul (Units.mk0 c hc)
#align measurable_equiv.smul₀ MeasurableEquiv.smul₀

@[simp]
theorem coe_smul₀ {c : G₀} (hc : c ≠ 0) : ⇑(smul₀ c hc : α ≃ᵐ α) = (· • ·) c :=
  rfl
#align measurable_equiv.coe_smul₀ MeasurableEquiv.coe_smul₀

@[simp]
theorem symm_smul₀ {c : G₀} (hc : c ≠ 0) :
    (smul₀ c hc : α ≃ᵐ α).symm = smul₀ c⁻¹ (inv_ne_zero hc) :=
  ext rfl
#align measurable_equiv.symm_smul₀ MeasurableEquiv.symm_smul₀

theorem measurableEmbedding_const_smul₀ {c : G₀} (hc : c ≠ 0) :
    MeasurableEmbedding ((· • ·) c : α → α) :=
  (smul₀ c hc).MeasurableEmbedding
#align measurable_embedding_const_smul₀ measurableEmbedding_const_smul₀

section Mul

variable [MeasurableMul G] [MeasurableMul G₀]

/-- If `G` is a group with measurable multiplication, then left multiplication by `g : G` is a
measurable automorphism of `G`. -/
@[to_additive
      "If `G` is an additive group with measurable addition, then addition of `g : G`\non the left is a measurable automorphism of `G`."]
def mulLeft (g : G) : G ≃ᵐ G :=
  smul g
#align measurable_equiv.mul_left MeasurableEquiv.mulLeft
#align measurable_equiv.add_left MeasurableEquiv.addLeft

@[simp, to_additive]
theorem coe_mulLeft (g : G) : ⇑(mulLeft g) = (· * ·) g :=
  rfl
#align measurable_equiv.coe_mul_left MeasurableEquiv.coe_mulLeft
#align measurable_equiv.coe_add_left MeasurableEquiv.coe_add_left

@[simp, to_additive]
theorem symm_mulLeft (g : G) : (mulLeft g).symm = mulLeft g⁻¹ :=
  ext rfl
#align measurable_equiv.symm_mul_left MeasurableEquiv.symm_mulLeft
#align measurable_equiv.symm_add_left MeasurableEquiv.symm_add_left

@[simp, to_additive]
theorem toEquiv_mulLeft (g : G) : (mulLeft g).toEquiv = Equiv.mulLeft g :=
  rfl
#align measurable_equiv.to_equiv_mul_left MeasurableEquiv.toEquiv_mulLeft
#align measurable_equiv.to_equiv_add_left MeasurableEquiv.toEquiv_add_left

@[to_additive]
theorem measurableEmbedding_mul_left (g : G) : MeasurableEmbedding ((· * ·) g) :=
  (mulLeft g).MeasurableEmbedding
#align measurable_embedding_mul_left measurableEmbedding_mul_left
#align measurable_embedding_add_left measurableEmbedding_add_left

/-- If `G` is a group with measurable multiplication, then right multiplication by `g : G` is a
measurable automorphism of `G`. -/
@[to_additive
      "If `G` is an additive group with measurable addition, then addition of `g : G`\non the right is a measurable automorphism of `G`."]
def mulRight (g : G) : G ≃ᵐ G where
  toEquiv := Equiv.mulRight g
  measurable_to_fun := measurable_mul_const g
  measurable_inv_fun := measurable_mul_const g⁻¹
#align measurable_equiv.mul_right MeasurableEquiv.mulRight
#align measurable_equiv.add_right MeasurableEquiv.addRight

@[to_additive]
theorem measurableEmbedding_mul_right (g : G) : MeasurableEmbedding fun x => x * g :=
  (mulRight g).MeasurableEmbedding
#align measurable_embedding_mul_right measurableEmbedding_mul_right
#align measurable_embedding_add_right measurableEmbedding_add_right

@[simp, to_additive]
theorem coe_mulRight (g : G) : ⇑(mulRight g) = fun x => x * g :=
  rfl
#align measurable_equiv.coe_mul_right MeasurableEquiv.coe_mulRight
#align measurable_equiv.coe_add_right MeasurableEquiv.coe_add_right

@[simp, to_additive]
theorem symm_mulRight (g : G) : (mulRight g).symm = mulRight g⁻¹ :=
  ext rfl
#align measurable_equiv.symm_mul_right MeasurableEquiv.symm_mulRight
#align measurable_equiv.symm_add_right MeasurableEquiv.symm_add_right

@[simp, to_additive]
theorem toEquiv_mulRight (g : G) : (mulRight g).toEquiv = Equiv.mulRight g :=
  rfl
#align measurable_equiv.to_equiv_mul_right MeasurableEquiv.toEquiv_mulRight
#align measurable_equiv.to_equiv_add_right MeasurableEquiv.toEquiv_add_right

/-- If `G₀` is a group with zero with measurable multiplication, then left multiplication by a
nonzero element `g : G₀` is a measurable automorphism of `G₀`. -/
def mulLeft₀ (g : G₀) (hg : g ≠ 0) : G₀ ≃ᵐ G₀ :=
  smul₀ g hg
#align measurable_equiv.mul_left₀ MeasurableEquiv.mulLeft₀

theorem measurableEmbedding_mul_left₀ {g : G₀} (hg : g ≠ 0) : MeasurableEmbedding ((· * ·) g) :=
  (mulLeft₀ g hg).MeasurableEmbedding
#align measurable_embedding_mul_left₀ measurableEmbedding_mul_left₀

@[simp]
theorem coe_mulLeft₀ {g : G₀} (hg : g ≠ 0) : ⇑(mulLeft₀ g hg) = (· * ·) g :=
  rfl
#align measurable_equiv.coe_mul_left₀ MeasurableEquiv.coe_mulLeft₀

@[simp]
theorem symm_mulLeft₀ {g : G₀} (hg : g ≠ 0) :
    (mulLeft₀ g hg).symm = mulLeft₀ g⁻¹ (inv_ne_zero hg) :=
  ext rfl
#align measurable_equiv.symm_mul_left₀ MeasurableEquiv.symm_mulLeft₀

@[simp]
theorem toEquiv_mulLeft₀ {g : G₀} (hg : g ≠ 0) : (mulLeft₀ g hg).toEquiv = Equiv.mulLeft₀ g hg :=
  rfl
#align measurable_equiv.to_equiv_mul_left₀ MeasurableEquiv.toEquiv_mulLeft₀

/-- If `G₀` is a group with zero with measurable multiplication, then right multiplication by a
nonzero element `g : G₀` is a measurable automorphism of `G₀`. -/
def mulRight₀ (g : G₀) (hg : g ≠ 0) : G₀ ≃ᵐ G₀
    where
  toEquiv := Equiv.mulRight₀ g hg
  measurable_to_fun := measurable_mul_const g
  measurable_inv_fun := measurable_mul_const g⁻¹
#align measurable_equiv.mul_right₀ MeasurableEquiv.mulRight₀

theorem measurableEmbedding_mul_right₀ {g : G₀} (hg : g ≠ 0) : MeasurableEmbedding fun x => x * g :=
  (mulRight₀ g hg).MeasurableEmbedding
#align measurable_embedding_mul_right₀ measurableEmbedding_mul_right₀

@[simp]
theorem coe_mulRight₀ {g : G₀} (hg : g ≠ 0) : ⇑(mulRight₀ g hg) = fun x => x * g :=
  rfl
#align measurable_equiv.coe_mul_right₀ MeasurableEquiv.coe_mulRight₀

@[simp]
theorem symm_mulRight₀ {g : G₀} (hg : g ≠ 0) :
    (mulRight₀ g hg).symm = mulRight₀ g⁻¹ (inv_ne_zero hg) :=
  ext rfl
#align measurable_equiv.symm_mul_right₀ MeasurableEquiv.symm_mulRight₀

@[simp]
theorem toEquiv_mulRight₀ {g : G₀} (hg : g ≠ 0) : (mulRight₀ g hg).toEquiv = Equiv.mulRight₀ g hg :=
  rfl
#align measurable_equiv.to_equiv_mul_right₀ MeasurableEquiv.toEquiv_mulRight₀

end Mul

/-- Inversion as a measurable automorphism of a group or group with zero. -/
@[to_additive "Negation as a measurable automorphism of an additive group.",
  simps (config := { fullyApplied := false }) toEquiv apply]
def inv (G) [MeasurableSpace G] [InvolutiveInv G] [MeasurableInv G] : G ≃ᵐ G
    where
  toEquiv := Equiv.inv G
  measurable_to_fun := measurable_inv
  measurable_inv_fun := measurable_inv
#align measurable_equiv.inv MeasurableEquiv.inv
#align measurable_equiv.neg MeasurableEquiv.neg

@[simp, to_additive]
theorem symm_inv {G} [MeasurableSpace G] [InvolutiveInv G] [MeasurableInv G] :
    (inv G).symm = inv G :=
  rfl
#align measurable_equiv.symm_inv MeasurableEquiv.symm_inv
#align measurable_equiv.symm_neg MeasurableEquiv.symm_neg

/-- `equiv.div_right` as a `measurable_equiv`. -/
@[to_additive " `equiv.sub_right` as a `measurable_equiv` "]
def divRight [MeasurableMul G] (g : G) : G ≃ᵐ G
    where
  toEquiv := Equiv.divRight g
  measurable_to_fun := measurable_div_const' g
  measurable_inv_fun := measurable_mul_const g
#align measurable_equiv.div_right MeasurableEquiv.divRight
#align measurable_equiv.sub_right MeasurableEquiv.subRight

/-- `equiv.div_left` as a `measurable_equiv` -/
@[to_additive " `equiv.sub_left` as a `measurable_equiv` "]
def divLeft [MeasurableMul G] [MeasurableInv G] (g : G) : G ≃ᵐ G
    where
  toEquiv := Equiv.divLeft g
  measurable_to_fun := measurable_id.const_div g
  measurable_inv_fun := measurable_inv.mul_const g
#align measurable_equiv.div_left MeasurableEquiv.divLeft
#align measurable_equiv.sub_left MeasurableEquiv.subLeft

end MeasurableEquiv

