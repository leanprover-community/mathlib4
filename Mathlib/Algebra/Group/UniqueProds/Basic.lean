/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.DFinsupp.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Data.Finset.Preimage
public import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Group.ULift
import Mathlib.Data.Finset.Attr
import Mathlib.Data.ULift
import Mathlib.Init
meta import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive

/-!
# Unique products and related notions

A group `G` has *unique products* if for any two non-empty finite subsets `A, B ⊆ G`, there is an
element `g ∈ A * B` that can be written uniquely as a product of an element of `A` and an element
of `B`.  We call the formalization this property `UniqueProds`.  Since the condition requires no
property of the group operation, we define it for a Type simply satisfying `Mul`.  We also
introduce the analogous "additive" companion, `UniqueSums`, and link the two so that `to_additive`
converts `UniqueProds` into `UniqueSums`.

A common way of *proving* that a group satisfies the `UniqueProds/Sums` property is by assuming
the existence of some kind of ordering on the group that is well-behaved with respect to the
group operation and showing that minima/maxima are the "unique products/sums".
However, the order is just a convenience and is not part of the `UniqueProds/Sums` setup.

Here you can see several examples of Types that have `UniqueSums/Prods`
(`inferInstance` uses `Covariant.to_uniqueProds_left` and `Covariant.to_uniqueSums_left`).
```lean
import Mathlib.Data.Real.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Algebra.Group.UniqueProds.Basic

example : UniqueSums ℕ   := inferInstance
example : UniqueSums ℕ+  := inferInstance
example : UniqueSums ℤ   := inferInstance
example : UniqueSums ℚ   := inferInstance
example : UniqueSums ℝ   := inferInstance
example : UniqueProds ℕ+ := inferInstance
```

## Use in `(Add)MonoidAlgebra`s

`UniqueProds/Sums` allow to decouple certain arguments about `(Add)MonoidAlgebra`s into an argument
about the grading type and then a generic statement of the form "look at the coefficient of the
'unique product/sum'".
The file `Algebra/MonoidAlgebra/NoZeroDivisors` contains several examples of this use.
-/

@[expose] public section

assert_not_exists Cardinal Subsemiring Algebra Submodule StarModule FreeMonoid IsOrderedMonoid

open Finset

/-- Let `G` be a Type with multiplication, let `A B : Finset G` be finite subsets and
let `a0 b0 : G` be two elements.  `UniqueMul A B a0 b0` asserts `a0 * b0` can be written in at
most one way as a product of an element of `A` and an element of `B`. -/
@[to_additive
      /-- Let `G` be a Type with addition, let `A B : Finset G` be finite subsets and
let `a0 b0 : G` be two elements.  `UniqueAdd A B a0 b0` asserts `a0 + b0` can be written in at
most one way as a sum of an element from `A` and an element from `B`. -/]
def UniqueMul {G} [Mul G] (A B : Finset G) (a0 b0 : G) : Prop :=
  ∀ ⦃a b⦄, a ∈ A → b ∈ B → a * b = a0 * b0 → a = a0 ∧ b = b0

namespace UniqueMul

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

@[to_additive]
theorem mono {A' B' : Finset G} (hA : A ⊆ A') (hB : B ⊆ B') (h : UniqueMul A' B' a0 b0) :
    UniqueMul A B a0 b0 := fun _ _ ha hb he ↦ h (hA ha) (hB hb) he

@[to_additive (attr := nontriviality, simp)]
theorem of_subsingleton [Subsingleton G] : UniqueMul A B a0 b0 := by
  simp [UniqueMul, eq_iff_true_of_subsingleton]

@[to_additive of_card_le_one]
theorem of_card_le_one (hA : A.Nonempty) (hB : B.Nonempty) (hA1 : #A ≤ 1) (hB1 : #B ≤ 1) :
    ∃ a ∈ A, ∃ b ∈ B, UniqueMul A B a b := by
  rw [Finset.card_le_one_iff] at hA1 hB1
  obtain ⟨a, ha⟩ := hA; obtain ⟨b, hb⟩ := hB
  exact ⟨a, ha, b, hb, fun _ _ ha' hb' _ ↦ ⟨hA1 ha' ha, hB1 hb' hb⟩⟩

@[to_additive]
theorem mt (h : UniqueMul A B a0 b0) :
    ∀ ⦃a b⦄, a ∈ A → b ∈ B → a ≠ a0 ∨ b ≠ b0 → a * b ≠ a0 * b0 := fun _ _ ha hb k ↦ by
  contrapose! k
  exact h ha hb k

@[to_additive]
theorem subsingleton (h : UniqueMul A B a0 b0) :
    Subsingleton { ab : G × G // ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 * ab.2 = a0 * b0 } :=
  ⟨fun ⟨⟨_a, _b⟩, ha, hb, ab⟩ ⟨⟨_a', _b'⟩, ha', hb', ab'⟩ ↦
    Subtype.ext <|
      Prod.ext ((h ha hb ab).1.trans (h ha' hb' ab').1.symm) <|
        (h ha hb ab).2.trans (h ha' hb' ab').2.symm⟩

@[to_additive]
theorem set_subsingleton (h : UniqueMul A B a0 b0) :
    Set.Subsingleton { ab : G × G | ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 * ab.2 = a0 * b0 } := by
  rintro ⟨x1, y1⟩ (hx : x1 ∈ A ∧ y1 ∈ B ∧ x1 * y1 = a0 * b0) ⟨x2, y2⟩
    (hy : x2 ∈ A ∧ y2 ∈ B ∧ x2 * y2 = a0 * b0)
  rcases h hx.1 hx.2.1 hx.2.2 with ⟨rfl, rfl⟩
  rcases h hy.1 hy.2.1 hy.2.2 with ⟨rfl, rfl⟩
  rfl

@[to_additive]
theorem iff_existsUnique (aA : a0 ∈ A) (bB : b0 ∈ B) :
    UniqueMul A B a0 b0 ↔ ∃! ab, ab ∈ A ×ˢ B ∧ ab.1 * ab.2 = a0 * b0 :=
  ⟨fun _ ↦ ⟨(a0, b0), ⟨Finset.mk_mem_product aA bB, rfl⟩, by simpa⟩,
    fun h ↦ h.elim
      (by
        rintro ⟨x1, x2⟩ _ J x y hx hy l
        rcases Prod.mk_inj.mp (J (a0, b0) ⟨Finset.mk_mem_product aA bB, rfl⟩) with ⟨rfl, rfl⟩
        exact Prod.mk_inj.mp (J (x, y) ⟨Finset.mk_mem_product hx hy, l⟩))⟩

open Finset in
@[to_additive iff_card_le_one]
theorem iff_card_le_one [DecidableEq G] (ha0 : a0 ∈ A) (hb0 : b0 ∈ B) :
    UniqueMul A B a0 b0 ↔ #{p ∈ A ×ˢ B | p.1 * p.2 = a0 * b0} ≤ 1 := by
  simp_rw [card_le_one_iff, mem_filter, mem_product]
  refine ⟨fun h p1 p2 ⟨⟨ha1, hb1⟩, he1⟩ ⟨⟨ha2, hb2⟩, he2⟩ ↦ ?_, fun h a b ha hb he ↦ ?_⟩
  · have h1 := h ha1 hb1 he1; have h2 := h ha2 hb2 he2
    grind
  · exact Prod.ext_iff.1 (@h (a, b) (a0, b0) ⟨⟨ha, hb⟩, he⟩ ⟨⟨ha0, hb0⟩, rfl⟩)

@[to_additive]
theorem exists_iff_exists_existsUnique :
    (∃ a0 b0 : G, a0 ∈ A ∧ b0 ∈ B ∧ UniqueMul A B a0 b0) ↔
      ∃ g : G, ∃! ab, ab ∈ A ×ˢ B ∧ ab.1 * ab.2 = g :=
  ⟨fun ⟨_, _, hA, hB, h⟩ ↦ ⟨_, (iff_existsUnique hA hB).mp h⟩, fun ⟨g, h⟩ ↦ by
    have h' := h
    rcases h' with ⟨⟨a, b⟩, ⟨hab, rfl, -⟩, -⟩
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    exact ⟨a, b, ha, hb, (iff_existsUnique ha hb).mpr h⟩⟩

/-- `UniqueMul` is preserved by inverse images under injective, multiplicative maps. -/
@[to_additive /-- `UniqueAdd` is preserved by inverse images under injective, additive maps. -/]
theorem mulHom_preimage (f : G →ₙ* H) (hf : Function.Injective f) (a0 b0 : G) {A B : Finset H}
    (u : UniqueMul A B (f a0) (f b0)) :
    UniqueMul (A.preimage f hf.injOn) (B.preimage f hf.injOn) a0 b0 := by
  intro a b ha hb ab
  simp only [← hf.eq_iff, map_mul] at ab ⊢
  exact u (Finset.mem_preimage.mp ha) (Finset.mem_preimage.mp hb) ab

@[to_additive] theorem of_mulHom_image [DecidableEq H] (f : G →ₙ* H)
    (hf : ∀ ⦃a b c d : G⦄, a * b = c * d → f a = f c ∧ f b = f d → a = c ∧ b = d)
    (h : UniqueMul (A.image f) (B.image f) (f a0) (f b0)) : UniqueMul A B a0 b0 :=
  fun a b ha hb ab ↦ hf ab
    (h (Finset.mem_image_of_mem f ha) (Finset.mem_image_of_mem f hb) <| by simp_rw [← map_mul, ab])

/-- `Unique_Mul` is preserved under multiplicative maps that are injective.

See `UniqueMul.mulHom_map_iff` for a version with swapped bundling. -/
@[to_additive
      /-- `UniqueAdd` is preserved under additive maps that are injective.

See `UniqueAdd.addHom_map_iff` for a version with swapped bundling. -/]
theorem mulHom_image_iff [DecidableEq H] (f : G →ₙ* H) (hf : Function.Injective f) :
    UniqueMul (A.image f) (B.image f) (f a0) (f b0) ↔ UniqueMul A B a0 b0 :=
  ⟨of_mulHom_image f fun _ _ _ _ _ ↦ .imp (hf ·) (hf ·), fun h _ _ ↦ by
    simp_rw [Finset.mem_image]
    rintro ⟨a, aA, rfl⟩ ⟨b, bB, rfl⟩ ab
    simp_rw [← map_mul, hf.eq_iff] at ab ⊢
    exact h aA bB ab⟩

/-- `UniqueMul` is preserved under embeddings that are multiplicative.

See `UniqueMul.mulHom_image_iff` for a version with swapped bundling. -/
@[to_additive
      /-- `UniqueAdd` is preserved under embeddings that are additive.

See `UniqueAdd.addHom_image_iff` for a version with swapped bundling. -/]
theorem mulHom_map_iff (f : G ↪ H) (mul : ∀ x y, f (x * y) = f x * f y) :
    UniqueMul (A.map f) (B.map f) (f a0) (f b0) ↔ UniqueMul A B a0 b0 := by
  classical simp_rw [← mulHom_image_iff ⟨f, mul⟩ f.2, Finset.map_eq_image]; rfl

section Opposites
open Finset MulOpposite

@[to_additive]
theorem of_mulOpposite
    (h : UniqueMul (B.map ⟨_, op_injective⟩) (A.map ⟨_, op_injective⟩) (op b0) (op a0)) :
    UniqueMul A B a0 b0 := fun a b aA bB ab ↦ by
  simpa [and_comm] using h (mem_map_of_mem _ bB) (mem_map_of_mem _ aA) (congr_arg op ab)

@[to_additive]
theorem to_mulOpposite (h : UniqueMul A B a0 b0) :
    UniqueMul (B.map ⟨_, op_injective⟩) (A.map ⟨_, op_injective⟩) (op b0) (op a0) :=
  of_mulOpposite (by simp_rw [map_map]; exact (mulHom_map_iff _ fun _ _ ↦ by rfl).mpr h)

@[to_additive]
theorem iff_mulOpposite :
    UniqueMul (B.map ⟨_, op_injective⟩) (A.map ⟨_, op_injective⟩) (op b0) (op a0) ↔
      UniqueMul A B a0 b0 :=
  ⟨of_mulOpposite, to_mulOpposite⟩

end Opposites

open Finset in
@[to_additive]
theorem of_image_filter [DecidableEq H]
    (f : G →ₙ* H) {A B : Finset G} {aG bG : G} {aH bH : H} (hae : f aG = aH) (hbe : f bG = bH)
    (huH : UniqueMul (A.image f) (B.image f) aH bH)
    (huG : UniqueMul {a ∈ A | f a = aH} {b ∈ B | f b = bH} aG bG) :
    UniqueMul A B aG bG := fun a b ha hb he ↦ by
  specialize huH (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)
  rw [← map_mul, he, map_mul, hae, hbe] at huH
  refine huG ?_ ?_ he <;> rw [mem_filter]
  exacts [⟨ha, (huH rfl).1⟩, ⟨hb, (huH rfl).2⟩]

end UniqueMul

/-- Let `G` be a Type with addition.  `UniqueSums G` asserts that any two non-empty
finite subsets of `G` have the `UniqueAdd` property, with respect to some element of their
sum `A + B`. -/
class UniqueSums (G) [Add G] : Prop where
/-- For `A B` two nonempty finite sets, there always exist `a0 ∈ A, b0 ∈ B` such that
`UniqueAdd A B a0 b0` -/
  uniqueAdd_of_nonempty :
    ∀ {A B : Finset G}, A.Nonempty → B.Nonempty → ∃ a0 ∈ A, ∃ b0 ∈ B, UniqueAdd A B a0 b0

/-- Let `G` be a Type with multiplication.  `UniqueProds G` asserts that any two non-empty
finite subsets of `G` have the `UniqueMul` property, with respect to some element of their
product `A * B`. -/
class UniqueProds (G) [Mul G] : Prop where
/-- For `A B` two nonempty finite sets, there always exist `a0 ∈ A, b0 ∈ B` such that
`UniqueMul A B a0 b0` -/
  uniqueMul_of_nonempty :
    ∀ {A B : Finset G}, A.Nonempty → B.Nonempty → ∃ a0 ∈ A, ∃ b0 ∈ B, UniqueMul A B a0 b0

attribute [to_additive] UniqueProds

/-- Let `G` be a Type with addition. `TwoUniqueSums G` asserts that any two non-empty
finite subsets of `G`, at least one of which is not a singleton, possesses at least two pairs
of elements satisfying the `UniqueAdd` property. -/
class TwoUniqueSums (G) [Add G] : Prop where
/-- For `A B` two finite sets whose product has cardinality at least 2,
  we can find at least two unique pairs. -/
  uniqueAdd_of_one_lt_card : ∀ {A B : Finset G}, 1 < #A * #B →
    ∃ p1 ∈ A ×ˢ B, ∃ p2 ∈ A ×ˢ B, p1 ≠ p2 ∧ UniqueAdd A B p1.1 p1.2 ∧ UniqueAdd A B p2.1 p2.2

/-- Let `G` be a Type with multiplication. `TwoUniqueProds G` asserts that any two non-empty
finite subsets of `G`, at least one of which is not a singleton, possesses at least two pairs
of elements satisfying the `UniqueMul` property. -/
class TwoUniqueProds (G) [Mul G] : Prop where
/-- For `A B` two finite sets whose product has cardinality at least 2,
  we can find at least two unique pairs. -/
  uniqueMul_of_one_lt_card : ∀ {A B : Finset G}, 1 < #A * #B →
    ∃ p1 ∈ A ×ˢ B, ∃ p2 ∈ A ×ˢ B, p1 ≠ p2 ∧ UniqueMul A B p1.1 p1.2 ∧ UniqueMul A B p2.1 p2.2

attribute [to_additive] TwoUniqueProds

@[to_additive]
lemma uniqueMul_of_twoUniqueMul {G} [Mul G] {A B : Finset G} (h : 1 < #A * #B →
    ∃ p1 ∈ A ×ˢ B, ∃ p2 ∈ A ×ˢ B, p1 ≠ p2 ∧ UniqueMul A B p1.1 p1.2 ∧ UniqueMul A B p2.1 p2.2)
    (hA : A.Nonempty) (hB : B.Nonempty) : ∃ a ∈ A, ∃ b ∈ B, UniqueMul A B a b := by
  by_cases! +distrib hc : #A ≤ 1 ∧ #B ≤ 1
  · exact UniqueMul.of_card_le_one hA hB hc.1 hc.2
  rw [← Finset.card_pos] at hA hB
  obtain ⟨p, hp, _, _, _, hu, _⟩ := h (Nat.one_lt_mul_iff.mpr ⟨hA, hB, hc⟩)
  rw [Finset.mem_product] at hp
  exact ⟨p.1, hp.1, p.2, hp.2, hu⟩

@[to_additive] instance TwoUniqueProds.toUniqueProds (G) [Mul G] [TwoUniqueProds G] :
    UniqueProds G where
  uniqueMul_of_nonempty := uniqueMul_of_twoUniqueMul uniqueMul_of_one_lt_card

namespace Multiplicative

instance {M} [Add M] [UniqueSums M] : UniqueProds (Multiplicative M) where
  uniqueMul_of_nonempty := UniqueSums.uniqueAdd_of_nonempty (G := M)

instance {M} [Add M] [TwoUniqueSums M] : TwoUniqueProds (Multiplicative M) where
  uniqueMul_of_one_lt_card := TwoUniqueSums.uniqueAdd_of_one_lt_card (G := M)

end Multiplicative

namespace Additive

instance {M} [Mul M] [UniqueProds M] : UniqueSums (Additive M) where
  uniqueAdd_of_nonempty := UniqueProds.uniqueMul_of_nonempty (G := M)

instance {M} [Mul M] [TwoUniqueProds M] : TwoUniqueSums (Additive M) where
  uniqueAdd_of_one_lt_card := TwoUniqueProds.uniqueMul_of_one_lt_card (G := M)

end Additive

universe u v
variable (G : Type u) (H : Type v) [Mul G] [Mul H]

private abbrev I : Bool → Type max u v := Bool.rec (ULift.{v} G) (ULift.{u} H)
@[to_additive] private instance : ∀ b, Mul (I G H b) := Bool.rec ULift.mul ULift.mul
@[to_additive] private def Prod.upMulHom : G × H →ₙ* ∀ b, I G H b :=
  ⟨fun x ↦ Bool.rec ⟨x.1⟩ ⟨x.2⟩, fun x y ↦ by ext (_ | _) <;> rfl⟩
@[to_additive] private def downMulHom : ULift G →ₙ* G := ⟨ULift.down, fun _ _ ↦ rfl⟩

variable {G H}

namespace UniqueProds

open Finset

@[to_additive] theorem of_mulHom (f : H →ₙ* G)
    (hf : ∀ ⦃a b c d : H⦄, a * b = c * d → f a = f c ∧ f b = f d → a = c ∧ b = d)
    [UniqueProds G] : UniqueProds H where
  uniqueMul_of_nonempty {A B} A0 B0 := by
    classical
    obtain ⟨a0, ha0, b0, hb0, h⟩ := uniqueMul_of_nonempty (A0.image f) (B0.image f)
    obtain ⟨a', ha', rfl⟩ := mem_image.mp ha0
    obtain ⟨b', hb', rfl⟩ := mem_image.mp hb0
    exact ⟨a', ha', b', hb', UniqueMul.of_mulHom_image f hf h⟩

@[to_additive]
theorem of_injective_mulHom (f : H →ₙ* G) (hf : Function.Injective f) (_ : UniqueProds G) :
    UniqueProds H := of_mulHom f (fun _ _ _ _ _ ↦ .imp (hf ·) (hf ·))

/-- `UniqueProd` is preserved under multiplicative equivalences. -/
@[to_additive /-- `UniqueSums` is preserved under additive equivalences. -/]
theorem _root_.MulEquiv.uniqueProds_iff (f : G ≃* H) : UniqueProds G ↔ UniqueProds H :=
  ⟨of_injective_mulHom f.symm f.symm.injective, of_injective_mulHom f f.injective⟩

open Finset MulOpposite in
@[to_additive]
theorem of_mulOpposite (h : UniqueProds Gᵐᵒᵖ) : UniqueProds G where
  uniqueMul_of_nonempty hA hB :=
    let f : G ↪ Gᵐᵒᵖ := ⟨op, op_injective⟩
    let ⟨y, yB, x, xA, hxy⟩ := h.uniqueMul_of_nonempty (hB.map (f := f)) (hA.map (f := f))
    ⟨unop x, (mem_map' _).mp xA, unop y, (mem_map' _).mp yB, hxy.of_mulOpposite⟩

@[to_additive] instance [h : UniqueProds G] : UniqueProds Gᵐᵒᵖ :=
  of_mulOpposite <| (MulEquiv.opOp G).uniqueProds_iff.mp h

@[to_additive] private theorem toIsLeftCancelMul [UniqueProds G] : IsLeftCancelMul G where
  mul_left_cancel a b1 b2 he := by
    classical
    have := mem_insert_self b1 {b2}
    obtain ⟨a, ha, b, hb, hu⟩ := uniqueMul_of_nonempty ⟨a, mem_singleton_self a⟩ ⟨b1, this⟩
    cases mem_singleton.mp ha
    simp_rw [mem_insert, mem_singleton] at hb
    obtain rfl | rfl := hb
    · exact (hu ha (mem_insert_of_mem <| mem_singleton_self b2) he.symm).2.symm
    · exact (hu ha this he).2

open MulOpposite in
@[to_additive] theorem toIsCancelMul [UniqueProds G] : IsCancelMul G where
  mul_left_cancel := toIsLeftCancelMul.mul_left_cancel
  mul_right_cancel _ _ _ h :=
    op_injective <| toIsLeftCancelMul.mul_left_cancel _ <| unop_injective h

/-! Two theorems in [Andrzej Strojnowski, *A note on u.p. groups*][Strojnowski1980] -/

/-- `UniqueProds G` says that for any two nonempty `Finset`s `A` and `B` in `G`, `A × B`
  contains a unique pair with the `UniqueMul` property. Strojnowski showed that if `G` is
  a group, then we only need to check this when `A = B`.
  Here we generalize the result to cancellative semigroups.
  Non-cancellative counterexample: the AddMonoid `{0,1}` with 1+1=1. -/
@[to_additive] theorem of_same {G} [Semigroup G] [IsCancelMul G]
    (h : ∀ {A : Finset G}, A.Nonempty → ∃ a1 ∈ A, ∃ a2 ∈ A, UniqueMul A A a1 a2) :
    UniqueProds G where
  uniqueMul_of_nonempty {A B} hA hB := by
    classical
    obtain ⟨g1, h1, g2, h2, hu⟩ := h (hB.mul hA)
    obtain ⟨b1, hb1, a1, ha1, rfl⟩ := mem_mul.mp h1
    obtain ⟨b2, hb2, a2, ha2, rfl⟩ := mem_mul.mp h2
    refine ⟨a1, ha1, b2, hb2, fun a b ha hb he => ?_⟩
    specialize hu (mul_mem_mul hb1 ha) (mul_mem_mul hb ha2) _
    · rw [mul_assoc b1, ← mul_assoc a, he, mul_assoc a1, ← mul_assoc b1]
    exact ⟨mul_left_cancel hu.1, mul_right_cancel hu.2⟩

/-- If a group has `UniqueProds`, then it actually has `TwoUniqueProds`.
  For an example of a semigroup `G` embeddable into a group that has `UniqueProds`
  but not `TwoUniqueProds`, see Example 10.13 in
  [J. Okniński, *Semigroup Algebras*][Okninski1991]. -/
@[to_additive] theorem toTwoUniqueProds_of_group {G}
    [Group G] [UniqueProds G] : TwoUniqueProds G where
  uniqueMul_of_one_lt_card {A B} hc := by
    simp_rw [Nat.one_lt_mul_iff, card_pos] at hc
    obtain ⟨a, ha, b, hb, hu⟩ := uniqueMul_of_nonempty hc.1 hc.2.1
    let C := A.map ⟨_, mul_right_injective a⁻¹⟩ -- C = a⁻¹A
    let D := B.map ⟨_, mul_left_injective b⁻¹⟩  -- D = Bb⁻¹
    have hcard : 1 < #C ∨ 1 < #D := by simp_rw [C, D, card_map]; exact hc.2.2
    have hC : 1 ∈ C := mem_map.mpr ⟨a, ha, inv_mul_cancel a⟩
    have hD : 1 ∈ D := mem_map.mpr ⟨b, hb, mul_inv_cancel b⟩
    suffices ∃ c ∈ C, ∃ d ∈ D, (c ≠ 1 ∨ d ≠ 1) ∧ UniqueMul C D c d by
      simp_rw [mem_product]
      obtain ⟨c, hc, d, hd, hne, hu'⟩ := this
      obtain ⟨a0, ha0, rfl⟩ := mem_map.mp hc
      obtain ⟨b0, hb0, rfl⟩ := mem_map.mp hd
      refine ⟨(_, _), ⟨ha0, hb0⟩, (a, b), ⟨ha, hb⟩, ?_, fun a' b' ha' hb' he => ?_, hu⟩
      · simp_rw [Function.Embedding.coeFn_mk, Ne, inv_mul_eq_one, mul_inv_eq_one] at hne
        rwa [Ne, Prod.mk_inj, not_and_or, eq_comm]
      specialize hu' (mem_map_of_mem _ ha') (mem_map_of_mem _ hb')
      simp_rw [Function.Embedding.coeFn_mk, mul_left_cancel_iff, mul_right_cancel_iff] at hu'
      rw [mul_assoc, ← mul_assoc a', he, mul_assoc, mul_assoc] at hu'
      exact hu' rfl
    classical
    let _ := Finset.mul (α := G)              -- E = D⁻¹C, F = DC⁻¹
    have := uniqueMul_of_nonempty (A := D.image (·⁻¹) * C) (B := D * C.image (·⁻¹)) ?_ ?_
    · obtain ⟨e, he, f, hf, hu⟩ := this
      clear_value C D
      simp only [UniqueMul, mem_mul, mem_image] at he hf hu
      obtain ⟨_, ⟨d1, hd1, rfl⟩, c1, hc1, rfl⟩ := he
      obtain ⟨d2, hd2, _, ⟨c2, hc2, rfl⟩, rfl⟩ := hf
      by_cases! h12 : c1 ≠ 1 ∨ d2 ≠ 1
      · refine ⟨c1, hc1, d2, hd2, h12, fun c3 d3 hc3 hd3 he => ?_⟩
        specialize hu ⟨_, ⟨_, hd1, rfl⟩, _, hc3, rfl⟩ ⟨_, hd3, _, ⟨_, hc2, rfl⟩, rfl⟩
        rw [mul_left_cancel_iff, mul_right_cancel_iff,
            mul_assoc, ← mul_assoc c3, he, mul_assoc, mul_assoc] at hu; exact hu rfl
      obtain ⟨rfl, rfl⟩ := h12
      by_cases! h21 : c2 ≠ 1 ∨ d1 ≠ 1
      · refine ⟨c2, hc2, d1, hd1, h21, fun c4 d4 hc4 hd4 he => ?_⟩
        specialize hu ⟨_, ⟨_, hd4, rfl⟩, _, hC, rfl⟩ ⟨_, hD, _, ⟨_, hc4, rfl⟩, rfl⟩
        simpa only [mul_one, one_mul, ← mul_inv_rev, he, true_imp_iff, inv_inj, and_comm] using hu
      obtain ⟨rfl, rfl⟩ := h21
      rcases hcard with hC | hD
      · obtain ⟨c, hc, hc1⟩ := exists_mem_ne hC 1
        refine (hc1 ?_).elim
        simpa using hu ⟨_, ⟨_, hD, rfl⟩, _, hc, rfl⟩ ⟨_, hD, _, ⟨_, hc, rfl⟩, rfl⟩
      · obtain ⟨d, hd, hd1⟩ := exists_mem_ne hD 1
        refine (hd1 ?_).elim
        simpa using hu ⟨_, ⟨_, hd, rfl⟩, _, hC, rfl⟩ ⟨_, hd, _, ⟨_, hC, rfl⟩, rfl⟩
    all_goals apply_rules [Nonempty.mul, Nonempty.image, Finset.Nonempty.map, hc.1, hc.2.1]

open UniqueMul in
@[to_additive] instance instForall {ι} (G : ι → Type*) [∀ i, Mul (G i)] [∀ i, UniqueProds (G i)] :
    UniqueProds (∀ i, G i) where
  uniqueMul_of_nonempty {A} := by
    classical
    let _ := isWellFounded_ssubset (α := ∀ i, G i) -- why need this?
    apply IsWellFounded.induction (· ⊂ ·) A; intro A ihA B hA
    apply IsWellFounded.induction (· ⊂ ·) B; intro B ihB hB
    by_cases! +distrib hc : #A ≤ 1 ∧ #B ≤ 1
    · exact of_card_le_one hA hB hc.1 hc.2
    obtain ⟨i, hc⟩ := exists_or.mpr (hc.imp exists_of_one_lt_card_pi exists_of_one_lt_card_pi)
    obtain ⟨ai, hA, bi, hB, hi⟩ := uniqueMul_of_nonempty (hA.image (· i)) (hB.image (· i))
    rw [mem_image, ← filter_nonempty_iff] at hA hB
    let A' := {a ∈ A | a i = ai}; let B' := {b ∈ B | b i = bi}
    obtain ⟨a0, ha0, b0, hb0, hu⟩ : ∃ a0 ∈ A', ∃ b0 ∈ B', UniqueMul A' B' a0 b0 := by
      rcases hc with hc | hc; · exact ihA A' (hc.2 ai) hA hB
      by_cases hA' : A' = A
      · rw [hA']
        exact ihB B' (hc.2 bi) hB
      · exact ihA A' ((A.filter_subset _).ssubset_of_ne hA') hA hB
    rw [mem_filter] at ha0 hb0
    exact ⟨a0, ha0.1, b0, hb0.1, of_image_filter (Pi.evalMulHom G i) ha0.2 hb0.2 hi hu⟩

open ULift in
@[to_additive] instance _root_.Prod.instUniqueProds [UniqueProds G] [UniqueProds H] :
    UniqueProds (G × H) := by
  have : ∀ b, UniqueProds (I G H b) := Bool.rec ?_ ?_
  · exact of_injective_mulHom (downMulHom H) down_injective ‹_›
  · refine of_injective_mulHom (Prod.upMulHom G H) (fun x y he => Prod.ext ?_ ?_)
      (UniqueProds.instForall <| I G H) <;> apply up_injective
    exacts [congr_fun he false, congr_fun he true]
  · exact of_injective_mulHom (downMulHom G) down_injective ‹_›

end UniqueProds

instance {ι} (G : ι → Type*) [∀ i, AddZeroClass (G i)] [∀ i, UniqueSums (G i)] :
    UniqueSums (Π₀ i, G i) :=
  UniqueSums.of_injective_addHom
    DFinsupp.coeFnAddMonoidHom.toAddHom DFunLike.coe_injective inferInstance

instance {ι G} [AddZeroClass G] [UniqueSums G] : UniqueSums (ι →₀ G) :=
  UniqueSums.of_injective_addHom
    Finsupp.coeFnAddHom.toAddHom DFunLike.coe_injective inferInstance

namespace TwoUniqueProds

open Finset

@[to_additive] theorem of_mulHom (f : H →ₙ* G)
    (hf : ∀ ⦃a b c d : H⦄, a * b = c * d → f a = f c ∧ f b = f d → a = c ∧ b = d)
    [TwoUniqueProds G] : TwoUniqueProds H where
  uniqueMul_of_one_lt_card {A B} hc := by
    classical
    obtain hc' | hc' := lt_or_ge 1 (#(A.image f) * #(B.image f))
    · obtain ⟨⟨a1, b1⟩, h1, ⟨a2, b2⟩, h2, hne, hu1, hu2⟩ := uniqueMul_of_one_lt_card hc'
      simp_rw [mem_product, mem_image] at h1 h2 ⊢
      obtain ⟨⟨a1, ha1, rfl⟩, b1, hb1, rfl⟩ := h1
      obtain ⟨⟨a2, ha2, rfl⟩, b2, hb2, rfl⟩ := h2
      exact ⟨(a1, b1), ⟨ha1, hb1⟩, (a2, b2), ⟨ha2, hb2⟩, mt (congr_arg (Prod.map f f)) hne,
        UniqueMul.of_mulHom_image f hf hu1, UniqueMul.of_mulHom_image f hf hu2⟩
    rw [← card_product] at hc hc'
    obtain ⟨p1, h1, p2, h2, hne⟩ := one_lt_card_iff_nontrivial.mp hc
    refine ⟨p1, h1, p2, h2, hne, ?_⟩
    cases mem_product.mp h1; cases mem_product.mp h2
    constructor <;> refine UniqueMul.of_mulHom_image f hf
      ((UniqueMul.iff_card_le_one ?_ ?_).mpr <| (card_filter_le _ _).trans hc') <;>
    apply mem_image_of_mem <;> assumption

@[to_additive]
theorem of_injective_mulHom (f : H →ₙ* G) (hf : Function.Injective f)
    (_ : TwoUniqueProds G) : TwoUniqueProds H :=
  of_mulHom f (fun _ _ _ _ _ ↦ .imp (hf ·) (hf ·))

/-- `TwoUniqueProd` is preserved under multiplicative equivalences. -/
@[to_additive /-- `TwoUniqueSums` is preserved under additive equivalences. -/]
theorem _root_.MulEquiv.twoUniqueProds_iff (f : G ≃* H) : TwoUniqueProds G ↔ TwoUniqueProds H :=
  ⟨of_injective_mulHom f.symm f.symm.injective, of_injective_mulHom f f.injective⟩

@[to_additive]
instance instForall {ι} (G : ι → Type*) [∀ i, Mul (G i)] [∀ i, TwoUniqueProds (G i)] :
    TwoUniqueProds (∀ i, G i) where
  uniqueMul_of_one_lt_card {A} := by
    classical
    let _ := isWellFounded_ssubset (α := ∀ i, G i) -- why need this?
    apply IsWellFounded.induction (· ⊂ ·) A; intro A ihA B
    apply IsWellFounded.induction (· ⊂ ·) B; intro B ihB hc
    obtain ⟨hA, hB, hc⟩ := Nat.one_lt_mul_iff.mp hc
    rw [card_pos] at hA hB
    obtain ⟨i, hc⟩ := exists_or.mpr (hc.imp exists_of_one_lt_card_pi exists_of_one_lt_card_pi)
    obtain ⟨p1, h1, p2, h2, hne, hi1, hi2⟩ := uniqueMul_of_one_lt_card (Nat.one_lt_mul_iff.mpr
      ⟨card_pos.2 (hA.image _), card_pos.2 (hB.image _), hc.imp And.left And.left⟩)
    simp_rw [mem_product, mem_image, ← filter_nonempty_iff] at h1 h2
    replace h1 := uniqueMul_of_twoUniqueMul ?_ h1.1 h1.2
    on_goal 1 => replace h2 := uniqueMul_of_twoUniqueMul ?_ h2.1 h2.2
    · obtain ⟨a1, ha1, b1, hb1, hu1⟩ := h1
      obtain ⟨a2, ha2, b2, hb2, hu2⟩ := h2
      rw [mem_filter] at ha1 hb1 ha2 hb2
      simp_rw [mem_product]
      refine ⟨(a1, b1), ⟨ha1.1, hb1.1⟩, (a2, b2), ⟨ha2.1, hb2.1⟩, ?_,
        UniqueMul.of_image_filter (Pi.evalMulHom G i) ha1.2 hb1.2 hi1 hu1,
        UniqueMul.of_image_filter (Pi.evalMulHom G i) ha2.2 hb2.2 hi2 hu2⟩
      grind
    all_goals rcases hc with hc | hc; · exact ihA _ (hc.2 _)
    · by_cases hA : {a ∈ A | a i = p2.1} = A
      · rw [hA]
        exact ihB _ (hc.2 _)
      · exact ihA _ ((A.filter_subset _).ssubset_of_ne hA)
    · by_cases hA : {a ∈ A | a i = p1.1} = A
      · rw [hA]
        exact ihB _ (hc.2 _)
      · exact ihA _ ((A.filter_subset _).ssubset_of_ne hA)

open ULift in
@[to_additive]
instance _root_.Prod.instTwoUniqueProds [TwoUniqueProds G] [TwoUniqueProds H] :
    TwoUniqueProds (G × H) := by
  have : ∀ b, TwoUniqueProds (I G H b) := Bool.rec ?_ ?_
  · exact of_injective_mulHom (downMulHom H) down_injective ‹_›
  · refine of_injective_mulHom (Prod.upMulHom G H) (fun x y he ↦ Prod.ext ?_ ?_)
      (TwoUniqueProds.instForall <| I G H) <;> apply up_injective
    exacts [congr_fun he false, congr_fun he true]
  · exact of_injective_mulHom (downMulHom G) down_injective ‹_›

open MulOpposite in
@[to_additive]
theorem of_mulOpposite (h : TwoUniqueProds Gᵐᵒᵖ) : TwoUniqueProds G where
  uniqueMul_of_one_lt_card hc := by
    let f : G ↪ Gᵐᵒᵖ := ⟨op, op_injective⟩
    rw [← card_map f, ← card_map f, mul_comm] at hc
    obtain ⟨p1, h1, p2, h2, hne, hu1, hu2⟩ := h.uniqueMul_of_one_lt_card hc
    simp_rw [mem_product] at h1 h2 ⊢
    refine ⟨(_, _), ⟨?_, ?_⟩, (_, _), ⟨?_, ?_⟩, ?_, hu1.of_mulOpposite, hu2.of_mulOpposite⟩
    pick_goal 5
    · contrapose hne; rw [Prod.ext_iff] at hne ⊢
      exact ⟨unop_injective hne.2, unop_injective hne.1⟩
    all_goals apply (mem_map' f).mp
    exacts [h1.2, h1.1, h2.2, h2.1]

@[to_additive] instance [h : TwoUniqueProds G] : TwoUniqueProds Gᵐᵒᵖ :=
  of_mulOpposite <| (MulEquiv.opOp G).twoUniqueProds_iff.mp h

-- see Note [lower instance priority]
/-- This instance asserts that if `G` has a right-cancellative multiplication, a linear order, and
  multiplication is strictly monotone w.r.t. the second argument, then `G` has `TwoUniqueProds`. -/
@[to_additive
  /-- This instance asserts that if `G` has a right-cancellative addition, a linear order,
  and addition is strictly monotone w.r.t. the second argument, then `G` has `TwoUniqueSums`. -/]
instance (priority := 100) of_covariant_right [IsRightCancelMul G]
    [LinearOrder G] [MulLeftStrictMono G] :
    TwoUniqueProds G where
  uniqueMul_of_one_lt_card {A B} hc := by
    obtain ⟨hA, hB, -⟩ := Nat.one_lt_mul_iff.mp hc
    rw [card_pos] at hA hB
    rw [← card_product] at hc
    obtain ⟨a0, ha0, b0, hb0, he0⟩ := mem_mul.mp (max'_mem _ <| hA.mul hB)
    obtain ⟨a1, ha1, b1, hb1, he1⟩ := mem_mul.mp (min'_mem _ <| hA.mul hB)
    have : UniqueMul A B a0 b0 := by
      intro a b ha hb he
      obtain hl | rfl | hl := lt_trichotomy b b0
      · exact ((he0 ▸ he ▸ mul_lt_mul_right hl a).not_ge <| le_max' _ _ <| mul_mem_mul ha hb0).elim
      · exact ⟨mul_right_cancel he, rfl⟩
      · exact ((he0 ▸ mul_lt_mul_right hl a0).not_ge <| le_max' _ _ <| mul_mem_mul ha0 hb).elim
    refine ⟨_, mk_mem_product ha0 hb0, _, mk_mem_product ha1 hb1, fun he ↦ ?_, this, ?_⟩
    · rw [Prod.mk_inj] at he; rw [he.1, he.2, he1] at he0
      obtain ⟨⟨a2, b2⟩, h2, hne⟩ := exists_mem_ne hc (a0, b0)
      rw [mem_product] at h2
      refine (min'_lt_max' _ (mul_mem_mul ha0 hb0) (mul_mem_mul h2.1 h2.2) fun he ↦ hne ?_).ne he0
      exact Prod.ext_iff.mpr (this h2.1 h2.2 he.symm)
    · intro a b ha hb he
      obtain hl | rfl | hl := lt_trichotomy b b1
      · exact ((he1 ▸ mul_lt_mul_right hl a1).not_ge <| min'_le _ _ <| mul_mem_mul ha1 hb).elim
      · exact ⟨mul_right_cancel he, rfl⟩
      · exact ((he1 ▸ he ▸ mul_lt_mul_right hl a).not_ge <| min'_le _ _ <| mul_mem_mul ha hb1).elim

open MulOpposite in
-- see Note [lower instance priority]
/-- This instance asserts that if `G` has a left-cancellative multiplication, a linear order, and
  multiplication is strictly monotone w.r.t. the first argument, then `G` has `TwoUniqueProds`. -/
@[to_additive
  /-- This instance asserts that if `G` has a left-cancellative addition, a linear order, and
  addition is strictly monotone w.r.t. the first argument, then `G` has `TwoUniqueSums`. -/]
instance (priority := 100) of_covariant_left [IsLeftCancelMul G]
    [LinearOrder G] [MulRightStrictMono G] :
    TwoUniqueProds G :=
  let _ := LinearOrder.lift' (unop : Gᵐᵒᵖ → G) unop_injective
  let _ : MulLeftStrictMono Gᵐᵒᵖ :=
    { elim := fun _ _ _ bc ↦ mul_lt_mul_left (α := G) bc (unop _) }
  of_mulOpposite of_covariant_right

end TwoUniqueProds

instance {ι} (G : ι → Type*) [∀ i, AddZeroClass (G i)] [∀ i, TwoUniqueSums (G i)] :
    TwoUniqueSums (Π₀ i, G i) :=
  TwoUniqueSums.of_injective_addHom
    DFinsupp.coeFnAddMonoidHom.toAddHom DFunLike.coe_injective inferInstance

instance {ι G} [AddZeroClass G] [TwoUniqueSums G] : TwoUniqueSums (ι →₀ G) :=
  TwoUniqueSums.of_injective_addHom
    Finsupp.coeFnAddHom.toAddHom DFunLike.coe_injective inferInstance
