/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa

! This file was ported from Lean 3 source module algebra.group.unique_prods
! leanprover-community/mathlib commit d6fad0e5bf2d6f48da9175d25c3dc5706b3834ce
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Preimage

/-!
#  Unique products and related notions

A group `G` has *unique products* if for any two non-empty finite subsets `A, B ⊂ G`, there is an
element `g ∈ A * B` that can be written uniquely as a product of an element of `A` and an element
of `B`.  We call the formalization this property `unique_prods`.  Since the condition requires no
property of the group operation, we define it for a Type simply satisfying `has_mul`.  We also
introduce the analogous "additive" companion, `unique_sums` and link the two so that `to_additive`
converts `unique_prods` into `unique_sums`.

Here you can see several examples of Types that have `unique_sums/prods`
(`apply_instance` uses `covariants.to_unique_prods` and `covariants.to_unique_sums`).
```lean
import data.real.basic

example : unique_sums ℕ   := by apply_instance
example : unique_sums ℕ+  := by apply_instance
example : unique_sums ℤ   := by apply_instance
example : unique_sums ℚ   := by apply_instance
example : unique_sums ℝ   := by apply_instance
example : unique_prods ℕ+ := by apply_instance
```
-/


/-- Let `G` be a Type with multiplication, let `A B : finset G` be finite subsets and
let `a0 b0 : G` be two elements.  `unique_mul A B a0 b0` asserts `a0 * b0` can be written in at
most one way as a product of an element of `A` and an element of `B`. -/
@[to_additive
      "Let `G` be a Type with addition, let `A B : finset G` be finite subsets and\nlet `a0 b0 : G` be two elements.  `unique_add A B a0 b0` asserts `a0 + b0` can be written in at\nmost one way as a sum of an element from `A` and an element from `B`."]
def UniqueMul {G} [Mul G] (A B : Finset G) (a0 b0 : G) : Prop :=
  ∀ ⦃a b⦄, a ∈ A → b ∈ B → a * b = a0 * b0 → a = a0 ∧ b = b0
#align unique_mul UniqueMul
#align unique_add UniqueAdd

namespace UniqueMul

variable {G H : Type _} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem mt {G} [Mul G] {A B : Finset G} {a0 b0 : G} (h : UniqueMul A B a0 b0) :
    ∀ ⦃a b⦄, a ∈ A → b ∈ B → a ≠ a0 ∨ b ≠ b0 → a * b ≠ a0 * b0 := fun _ _ ha hb k =>
  by
  contrapose! k
  exact h ha hb k
#align unique_mul.mt UniqueMul.mt

@[to_additive]
theorem subsingleton (A B : Finset G) (a0 b0 : G) (h : UniqueMul A B a0 b0) :
    Subsingleton { ab : G × G // ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 * ab.2 = a0 * b0 } :=
  ⟨fun ⟨⟨a, b⟩, ha, hb, ab⟩ ⟨⟨a', b'⟩, ha', hb', ab'⟩ =>
    Subtype.ext <|
      Prod.ext ((h ha hb ab).1.trans (h ha' hb' ab').1.symm) <|
        (h ha hb ab).2.trans (h ha' hb' ab').2.symm⟩
#align unique_mul.subsingleton UniqueMul.subsingleton
#align unique_add.subsingleton UniqueAdd.subsingleton

@[to_additive]
theorem set_subsingleton (A B : Finset G) (a0 b0 : G) (h : UniqueMul A B a0 b0) :
    Set.Subsingleton { ab : G × G | ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 * ab.2 = a0 * b0 } :=
  by
  rintro ⟨x1, y1⟩ (hx : x1 ∈ A ∧ y1 ∈ B ∧ x1 * y1 = a0 * b0) ⟨x2, y2⟩
    (hy : x2 ∈ A ∧ y2 ∈ B ∧ x2 * y2 = a0 * b0)
  rcases h hx.1 hx.2.1 hx.2.2 with ⟨rfl, rfl⟩
  rcases h hy.1 hy.2.1 hy.2.2 with ⟨rfl, rfl⟩
  rfl
#align unique_mul.set_subsingleton UniqueMul.set_subsingleton
#align unique_add.set_subsingleton UniqueAdd.set_subsingleton

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (ab «expr ∈ » [finset.product/multiset.product/set.prod/list.product](A, B)) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive]
theorem iff_existsUnique (aA : a0 ∈ A) (bB : b0 ∈ B) :
    UniqueMul A B a0 b0 ↔ ∃! (ab : _)(_ : ab ∈ A ×ˢ B), ab.1 * ab.2 = a0 * b0 :=
  ⟨fun _ => ⟨(a0, b0), ⟨Finset.mem_product.mpr ⟨aA, bB⟩, rfl, by simp⟩, by simpa⟩, fun h =>
    h.elim2
      (by
        rintro ⟨x1, x2⟩ _ _ J x y hx hy l
        rcases prod.mk.inj_iff.mp (J (a0, b0) (Finset.mk_mem_product aA bB) rfl) with ⟨rfl, rfl⟩
        exact prod.mk.inj_iff.mp (J (x, y) (Finset.mk_mem_product hx hy) l))⟩
#align unique_mul.iff_exists_unique UniqueMul.iff_existsUnique
#align unique_add.iff_exists_unique UniqueAdd.iff_existsUnique

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (ab «expr ∈ » [finset.product/multiset.product/set.prod/list.product](A, B)) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive]
theorem exists_iff_exists_existsUnique :
    (∃ a0 b0 : G, a0 ∈ A ∧ b0 ∈ B ∧ UniqueMul A B a0 b0) ↔
      ∃ g : G, ∃! (ab : _)(_ : ab ∈ A ×ˢ B), ab.1 * ab.2 = g :=
  ⟨fun ⟨a0, b0, hA, hB, h⟩ => ⟨_, (iff_existsUnique hA hB).mp h⟩, fun ⟨g, h⟩ =>
    by
    have h' := h
    rcases h' with ⟨⟨a, b⟩, ⟨hab, rfl, -⟩, -⟩
    cases' finset.mem_product.mp hab with ha hb
    exact ⟨a, b, ha, hb, (iff_exists_unique ha hb).mpr h⟩⟩
#align unique_mul.exists_iff_exists_exists_unique UniqueMul.exists_iff_exists_existsUnique
#align unique_add.exists_iff_exists_exists_unique UniqueAdd.exists_iff_exists_existsUnique

/-- `unique_mul` is preserved by inverse images under injective, multiplicative maps. -/
@[to_additive "`unique_add` is preserved by inverse images under injective, additive maps."]
theorem mulHom_preimage (f : G →ₙ* H) (hf : Function.Injective f) (a0 b0 : G) {A B : Finset H}
    (u : UniqueMul A B (f a0) (f b0)) :
    UniqueMul (A.Preimage f (Set.injOn_of_injective hf _))
      (B.Preimage f (Set.injOn_of_injective hf _)) a0 b0 :=
  by
  intro a b ha hb ab
  rw [← hf.eq_iff, ← hf.eq_iff]
  rw [← hf.eq_iff, map_mul, map_mul] at ab
  exact u (finset.mem_preimage.mp ha) (finset.mem_preimage.mp hb) ab
#align unique_mul.mul_hom_preimage UniqueMul.mulHom_preimage
#align unique_add.add_hom_preimage UniqueAdd.add_hom_preimage

/-- `unique_mul` is preserved under multiplicative maps that are injective.

See `unique_mul.mul_hom_map_iff` for a version with swapped bundling. -/
@[to_additive
      "`unique_add` is preserved under additive maps that are injective.\n\nSee `unique_add.add_hom_map_iff` for a version with swapped bundling."]
theorem mulHom_image_iff [DecidableEq H] (f : G →ₙ* H) (hf : Function.Injective f) :
    UniqueMul (A.image f) (B.image f) (f a0) (f b0) ↔ UniqueMul A B a0 b0 :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  · intro a b ha hb ab
    rw [← hf.eq_iff, ← hf.eq_iff]
    rw [← hf.eq_iff, map_mul, map_mul] at ab
    exact h (finset.mem_image.mpr ⟨_, ha, rfl⟩) (finset.mem_image.mpr ⟨_, hb, rfl⟩) ab
  · intro a b aA bB ab
    obtain ⟨a, ha, rfl⟩ : ∃ a' ∈ A, f a' = a := finset.mem_image.mp aA
    obtain ⟨b, hb, rfl⟩ : ∃ b' ∈ B, f b' = b := finset.mem_image.mp bB
    rw [hf.eq_iff, hf.eq_iff]
    rw [← map_mul, ← map_mul, hf.eq_iff] at ab
    exact h ha hb ab
#align unique_mul.mul_hom_image_iff UniqueMul.mulHom_image_iff
#align unique_add.add_hom_image_iff UniqueAdd.add_hom_image_iff

/-- `unique_mul` is preserved under embeddings that are multiplicative.

See `unique_mul.mul_hom_image_iff` for a version with swapped bundling. -/
@[to_additive
      "`unique_add` is preserved under embeddings that are additive.\n\nSee `unique_add.add_hom_image_iff` for a version with swapped bundling."]
theorem mul_hom_map_iff (f : G ↪ H) (mul : ∀ x y, f (x * y) = f x * f y) :
    UniqueMul (A.map f) (B.map f) (f a0) (f b0) ↔ UniqueMul A B a0 b0 := by
  classical convert mul_hom_image_iff ⟨f, mul⟩ f.2 <;>
      · ext
        simp only [Finset.mem_map, MulHom.coe_mk, Finset.mem_image]
#align unique_mul.mul_hom_map_iff UniqueMul.mul_hom_map_iff
#align unique_add.add_hom_map_iff UniqueAdd.add_hom_map_iff

end UniqueMul

/-- Let `G` be a Type with addition.  `unique_sums G` asserts that any two non-empty
finite subsets of `A` have the `unique_add` property, with respect to some element of their
sum `A + B`. -/
class UniqueSums (G) [Add G] : Prop where
  unique_add_of_nonempty :
    ∀ {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty), ∃ a0 ∈ A, ∃ b0 ∈ B, UniqueAdd A B a0 b0
#align unique_sums UniqueSums

/-- Let `G` be a Type with multiplication.  `unique_prods G` asserts that any two non-empty
finite subsets of `G` have the `unique_mul` property, with respect to some element of their
product `A * B`. -/
class UniqueProds (G) [Mul G] : Prop where
  unique_mul_of_nonempty :
    ∀ {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty), ∃ a0 ∈ A, ∃ b0 ∈ B, UniqueMul A B a0 b0
#align unique_prods UniqueProds

attribute [to_additive] UniqueProds

namespace Multiplicative

instance {M} [Add M] [UniqueSums M] : UniqueProds (Multiplicative M)
    where unique_mul_of_nonempty A B hA hB :=
    by
    let A' : Finset M := A
    have hA' : A'.Nonempty := hA
    obtain ⟨a0, hA0, b0, hB0, J⟩ := UniqueSums.uniqueAdd_of_nonempty hA' hB
    exact ⟨of_add a0, hA0, of_add b0, hB0, fun a b aA bB H => J aA bB H⟩

end Multiplicative

namespace Additive

instance {M} [Mul M] [UniqueProds M] : UniqueSums (Additive M)
    where unique_add_of_nonempty A B hA hB :=
    by
    let A' : Finset M := A
    have hA' : A'.Nonempty := hA
    obtain ⟨a0, hA0, b0, hB0, J⟩ := UniqueProds.uniqueMul_of_nonempty hA' hB
    exact ⟨of_mul a0, hA0, of_mul b0, hB0, fun a b aA bB H => J aA bB H⟩

end Additive

@[to_additive]
theorem eq_and_eq_of_le_of_le_of_mul_le {A} [Mul A] [LinearOrder A]
    [CovariantClass A A (· * ·) (· ≤ ·)] [CovariantClass A A (Function.swap (· * ·)) (· < ·)]
    [ContravariantClass A A (· * ·) (· ≤ ·)] {a b a0 b0 : A} (ha : a0 ≤ a) (hb : b0 ≤ b)
    (ab : a * b ≤ a0 * b0) : a = a0 ∧ b = b0 :=
  by
  haveI := Mul.to_covariantClass_right A
  have ha' : ¬a0 * b0 < a * b → ¬a0 < a := mt fun h => mul_lt_mul_of_lt_of_le h hb
  have hb' : ¬a0 * b0 < a * b → ¬b0 < b := mt fun h => mul_lt_mul_of_le_of_lt ha h
  push_neg  at ha' hb'
  exact ⟨ha.antisymm' (ha' ab), hb.antisymm' (hb' ab)⟩
#align eq_and_eq_of_le_of_le_of_mul_le eq_and_eq_of_le_of_le_of_mul_le
#align eq_and_eq_of_le_of_le_of_add_le eq_and_eq_of_le_of_le_of_add_le

-- see Note [lower instance priority]
/-- This instance asserts that if `A` has a multiplication, a linear order, and multiplication
is 'very monotone', then `A` also has `unique_prods`. -/
@[to_additive
      "This instance asserts that if `A` has an addition, a linear order, and addition\nis 'very monotone', then `A` also has `unique_sums`."]
instance (priority := 100) Covariants.to_uniqueProds {A} [Mul A] [LinearOrder A]
    [CovariantClass A A (· * ·) (· ≤ ·)] [CovariantClass A A (Function.swap (· * ·)) (· < ·)]
    [ContravariantClass A A (· * ·) (· ≤ ·)] : UniqueProds A
    where unique_mul_of_nonempty A B hA hB :=
    ⟨_, A.min'_mem ‹_›, _, B.min'_mem ‹_›, fun a b ha hb ab =>
      eq_and_eq_of_le_of_le_of_mul_le (Finset.min'_le _ _ ‹_›) (Finset.min'_le _ _ ‹_›) ab.le⟩
#align covariants.to_unique_prods Covariants.to_uniqueProds
#align covariants.to_unique_sums Covariants.to_unique_sums

