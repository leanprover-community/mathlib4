/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Data.DFinsupp.Basic
import Mathlib.Data.Finset.Pointwise
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finsupp.Defs

#align_import algebra.group.unique_prods from "leanprover-community/mathlib"@"d6fad0e5bf2d6f48da9175d25c3dc5706b3834ce"

/-!
# Unique products and related notions

A group `G` has *unique products* if for any two non-empty finite subsets `A, B ⊂ G`, there is an
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
import Mathlib.Algebra.Group.UniqueProds

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

/-- Let `G` be a Type with multiplication, let `A B : Finset G` be finite subsets and
let `a0 b0 : G` be two elements.  `UniqueMul A B a0 b0` asserts `a0 * b0` can be written in at
most one way as a product of an element of `A` and an element of `B`. -/
@[to_additive
      "Let `G` be a Type with addition, let `A B : Finset G` be finite subsets and
let `a0 b0 : G` be two elements.  `UniqueAdd A B a0 b0` asserts `a0 + b0` can be written in at
most one way as a sum of an element from `A` and an element from `B`."]
def UniqueMul {G} [Mul G] (A B : Finset G) (a0 b0 : G) : Prop :=
  ∀ ⦃a b⦄, a ∈ A → b ∈ B → a * b = a0 * b0 → a = a0 ∧ b = b0
#align unique_mul UniqueMul
#align unique_add UniqueAdd

namespace UniqueMul

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

@[to_additive (attr := nontriviality, simp)]
theorem of_subsingleton [Subsingleton G] : UniqueMul A B a0 b0 := by simp [UniqueMul]

@[to_additive]
theorem mt {G} [Mul G] {A B : Finset G} {a0 b0 : G} (h : UniqueMul A B a0 b0) :
    ∀ ⦃a b⦄, a ∈ A → b ∈ B → a ≠ a0 ∨ b ≠ b0 → a * b ≠ a0 * b0 := fun _ _ ha hb k ↦ by
  contrapose! k
  exact h ha hb k
#align unique_mul.mt UniqueMul.mt

@[to_additive]
theorem subsingleton (A B : Finset G) (a0 b0 : G) (h : UniqueMul A B a0 b0) :
    Subsingleton { ab : G × G // ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 * ab.2 = a0 * b0 } :=
  ⟨fun ⟨⟨_a, _b⟩, ha, hb, ab⟩ ⟨⟨_a', _b'⟩, ha', hb', ab'⟩ ↦
    Subtype.ext <|
      Prod.ext ((h ha hb ab).1.trans (h ha' hb' ab').1.symm) <|
        (h ha hb ab).2.trans (h ha' hb' ab').2.symm⟩
#align unique_mul.subsingleton UniqueMul.subsingleton
#align unique_add.subsingleton UniqueAdd.subsingleton

@[to_additive]
theorem set_subsingleton (A B : Finset G) (a0 b0 : G) (h : UniqueMul A B a0 b0) :
    Set.Subsingleton { ab : G × G | ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 * ab.2 = a0 * b0 } := by
  rintro ⟨x1, y1⟩ (hx : x1 ∈ A ∧ y1 ∈ B ∧ x1 * y1 = a0 * b0) ⟨x2, y2⟩
    (hy : x2 ∈ A ∧ y2 ∈ B ∧ x2 * y2 = a0 * b0)
  rcases h hx.1 hx.2.1 hx.2.2 with ⟨rfl, rfl⟩
  rcases h hy.1 hy.2.1 hy.2.2 with ⟨rfl, rfl⟩
  rfl
#align unique_mul.set_subsingleton UniqueMul.set_subsingleton
#align unique_add.set_subsingleton UniqueAdd.set_subsingleton

-- Porting note: mathport warning: expanding binder collection
--  (ab «expr ∈ » [finset.product/multiset.product/set.prod/list.product](A, B)) -/
@[to_additive]
theorem iff_existsUnique (aA : a0 ∈ A) (bB : b0 ∈ B) :
    UniqueMul A B a0 b0 ↔ ∃! (ab : _) (_ : ab ∈ A ×ˢ B), ab.1 * ab.2 = a0 * b0 :=
  ⟨fun _ ↦ ⟨(a0, b0), ⟨Finset.mem_product.mpr ⟨aA, bB⟩, rfl, by simp⟩, by simpa⟩,
    fun h ↦ h.elim₂
      (by
        rintro ⟨x1, x2⟩ _ _ J x y hx hy l
        rcases Prod.mk.inj_iff.mp (J (a0, b0) (Finset.mk_mem_product aA bB) rfl) with ⟨rfl, rfl⟩
        exact Prod.mk.inj_iff.mp (J (x, y) (Finset.mk_mem_product hx hy) l))⟩
#align unique_mul.iff_exists_unique UniqueMul.iff_existsUnique
#align unique_add.iff_exists_unique UniqueAdd.iff_existsUnique

-- Porting note: mathport warning: expanding binder collection
--  (ab «expr ∈ » [finset.product/multiset.product/set.prod/list.product](A, B)) -/
@[to_additive]
theorem exists_iff_exists_existsUnique :
    (∃ a0 b0 : G, a0 ∈ A ∧ b0 ∈ B ∧ UniqueMul A B a0 b0) ↔
      ∃ g : G, ∃! (ab : _) (_ : ab ∈ A ×ˢ B), ab.1 * ab.2 = g :=
  ⟨fun ⟨a0, b0, hA, hB, h⟩ ↦ ⟨_, (iff_existsUnique hA hB).mp h⟩, fun ⟨g, h⟩ ↦ by
    have h' := h
    rcases h' with ⟨⟨a, b⟩, ⟨hab, rfl, -⟩, -⟩
    cases' Finset.mem_product.mp hab with ha hb
    exact ⟨a, b, ha, hb, (iff_existsUnique ha hb).mpr h⟩⟩
#align unique_mul.exists_iff_exists_exists_unique UniqueMul.exists_iff_exists_existsUnique
#align unique_add.exists_iff_exists_exists_unique UniqueAdd.exists_iff_exists_existsUnique

/-- `UniqueMul` is preserved by inverse images under injective, multiplicative maps. -/
@[to_additive "`UniqueAdd` is preserved by inverse images under injective, additive maps."]
theorem mulHom_preimage (f : G →ₙ* H) (hf : Function.Injective f) (a0 b0 : G) {A B : Finset H}
    (u : UniqueMul A B (f a0) (f b0)) :
    UniqueMul (A.preimage f (Set.injOn_of_injective hf _))
      (B.preimage f (Set.injOn_of_injective hf _)) a0 b0 := by
  intro a b ha hb ab
  simp only [← hf.eq_iff, map_mul] at ab ⊢
  exact u (Finset.mem_preimage.mp ha) (Finset.mem_preimage.mp hb) ab
#align unique_mul.mul_hom_preimage UniqueMul.mulHom_preimage
#align unique_add.add_hom_preimage UniqueAdd.addHom_preimage

/-- `Unique_Mul` is preserved under multiplicative maps that are injective.

See `UniqueMul.mulHom_map_iff` for a version with swapped bundling. -/
@[to_additive
      "`UniqueAdd` is preserved under additive maps that are injective.

See `UniqueAdd.addHom_map_iff` for a version with swapped bundling."]
theorem mulHom_image_iff [DecidableEq H] (f : G →ₙ* H) (hf : Function.Injective f) :
    UniqueMul (A.image f) (B.image f) (f a0) (f b0) ↔ UniqueMul A B a0 b0 := by
  simp_rw [UniqueMul, Finset.mem_image]
  refine' ⟨fun h a b ha hb ab ↦ _, fun h ↦ _⟩
  · rw [← hf.eq_iff, map_mul, map_mul] at ab
    have := h ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ab
    exact ⟨hf this.1, hf this.2⟩
  · rintro _ _ ⟨a, aA, rfl⟩ ⟨b, bB, rfl⟩ ab
    simp only [← map_mul, hf.eq_iff] at ab ⊢
    exact h aA bB ab
#align unique_mul.mul_hom_image_iff UniqueMul.mulHom_image_iff
#align unique_add.add_hom_image_iff UniqueAdd.addHom_image_iff

/-- `UniqueMul` is preserved under embeddings that are multiplicative.

See `UniqueMul.mulHom_image_iff` for a version with swapped bundling. -/
@[to_additive
      "`UniqueAdd` is preserved under embeddings that are additive.

See `UniqueAdd.addHom_image_iff` for a version with swapped bundling."]
theorem mulHom_map_iff (f : G ↪ H) (mul : ∀ x y, f (x * y) = f x * f y) :
    UniqueMul (A.map f) (B.map f) (f a0) (f b0) ↔ UniqueMul A B a0 b0 := by
  classical
  convert @mulHom_image_iff G H _ _ A B a0 b0 _ ⟨f, mul⟩ f.2 using 2 <;>
    · ext
      simp only [Finset.mem_map, MulHom.coe_mk, Finset.mem_image]
#align unique_mul.mul_hom_map_iff UniqueMul.mulHom_map_iff
#align unique_add.add_hom_map_iff UniqueAdd.addHom_map_iff

section Opposites
open Finset MulOpposite

@[to_additive]
theorem of_mulOpposite
    (h : UniqueMul (B.map ⟨_, op_injective⟩) (A.map ⟨_, op_injective⟩) (op b0) (op a0)) :
    UniqueMul A B a0 b0 := by
  intros a b aA bB ab
  have := h (mem_map_of_mem _ bB) (mem_map_of_mem _ aA) (by simpa using congr_arg op ab)
  simpa [and_comm] using this

@[to_additive]
theorem to_mulOpposite (h : UniqueMul A B a0 b0) :
    UniqueMul (B.map ⟨_, op_injective⟩) (A.map ⟨_, op_injective⟩) (op b0) (op a0) := by
  refine of_mulOpposite (G := MulOpposite G) <| fun a b ha hb hab ↦ ?_
  simp only [mem_map, Function.Embedding.coeFn_mk, exists_exists_and_eq_and] at ha hb
  rcases ha with ⟨a, ha, rfl⟩
  rcases hb with ⟨b, hb, rfl⟩
  rw [op_inj, op_inj, op_inj, op_inj]
  apply h ha hb ?_
  apply_fun op ∘ op using op_injective.comp op_injective
  exact hab

@[to_additive]
theorem iff_mulOpposite :
    UniqueMul (B.map ⟨_, op_injective⟩) (A.map ⟨_, op_injective⟩) (op b0) (op a0) ↔
      UniqueMul A B a0 b0 :=
⟨of_mulOpposite, to_mulOpposite⟩

end Opposites

end UniqueMul

/-- Let `G` be a Type with addition.  `UniqueSums G` asserts that any two non-empty
finite subsets of `G` have the `UniqueAdd` property, with respect to some element of their
sum `A + B`. -/
class UniqueSums (G) [Add G] : Prop where
/-- For `A B` two nonempty finite sets, there always exist `a0 ∈ A, b0 ∈ B` such that
`UniqueAdd A B a0 b0` -/
  uniqueAdd_of_nonempty :
    ∀ {A B : Finset G} (_ : A.Nonempty) (_ : B.Nonempty), ∃ a0 ∈ A, ∃ b0 ∈ B, UniqueAdd A B a0 b0
#align unique_sums UniqueSums

/-- Let `G` be a Type with multiplication.  `UniqueProds G` asserts that any two non-empty
finite subsets of `G` have the `UniqueMul` property, with respect to some element of their
product `A * B`. -/
class UniqueProds (G) [Mul G] : Prop where
/-- For `A B` two nonempty finite sets, there always exist `a0 ∈ A, b0 ∈ B` such that
`UniqueMul A B a0 b0` -/
  uniqueMul_of_nonempty :
    ∀ {A B : Finset G} (_ : A.Nonempty) (_ : B.Nonempty), ∃ a0 ∈ A, ∃ b0 ∈ B, UniqueMul A B a0 b0
#align unique_prods UniqueProds

attribute [to_additive] UniqueProds

namespace Multiplicative

instance {M} [Add M] [UniqueSums M] : UniqueProds (Multiplicative M) where
  uniqueMul_of_nonempty := UniqueSums.uniqueAdd_of_nonempty (G := M)

end Multiplicative

namespace Additive

instance {M} [Mul M] [UniqueProds M] : UniqueSums (Additive M) where
  uniqueAdd_of_nonempty := UniqueProds.uniqueMul_of_nonempty (G := M)

end Additive

#noalign covariants.to_unique_prods
#noalign covariants.to_unique_sums

namespace UniqueProds

variable {G H : Type*} [Mul G] [Mul H]

open Finset MulOpposite in
@[to_additive]
theorem of_mulOpposite (h : @UniqueProds Gᵐᵒᵖ (MulOpposite.mul G)) :
    UniqueProds G :=
⟨fun hA hB =>
  let f : G ↪ Gᵐᵒᵖ := ⟨op, op_injective⟩
  let ⟨y, yB, x, xA, hxy⟩ := h.uniqueMul_of_nonempty (hB.map (f := f)) (hA.map (f := f))
  ⟨unop x, (mem_map' _).mp xA, unop y, (mem_map' _).mp yB, hxy.of_mulOpposite⟩⟩

-- see Note [lower instance priority]
/-- This instance asserts that if `G` has a right-cancellative multiplication, a linear order,
  and multiplication is strictly monotone w.r.t. the second argument, then `G` has `UniqueProds`. -/
@[to_additive
  "This instance asserts that if `G` has a right-cancellative addition, a linear order,
  and addition is strictly monotone w.r.t. the second argument, then `G` has `UniqueSums`." ]
instance (priority := 100) of_Covariant_right [IsRightCancelMul G]
    [LinearOrder G] [CovariantClass G G (· * ·) (· < ·)] :
    UniqueProds G where
  uniqueMul_of_nonempty {A B} hA hB := by
    obtain ⟨a0, b0, ha0, hb0, he⟩ := Finset.mem_mul.mp (Finset.max'_mem _ <| hA.mul hB)
    refine ⟨a0, ha0, b0, hb0, fun a b ha hb he' => ?_⟩
    obtain hl | rfl | hl := lt_trichotomy b b0
    · refine ((he'.trans he ▸ mul_lt_mul_left' hl a).not_le <| Finset.le_max' _ (a * b0) ?_).elim
      exact Finset.mem_mul.mpr ⟨a, b0, ha, hb0, rfl⟩
    · exact ⟨mul_right_cancel he', rfl⟩
    · refine ((he ▸ mul_lt_mul_left' hl a0).not_le <| Finset.le_max' _ (a0 * b) ?_).elim
      exact Finset.mem_mul.mpr ⟨a0, b, ha0, hb, rfl⟩

open MulOpposite in
-- see Note [lower instance priority]
/-- This instance asserts that if `G` has a left-cancellative multiplication, a linear order,
  and multiplication is strictly monotone w.r.t. the first argument, then `G` has `UniqueProds`. -/
@[to_additive
  "This instance asserts that if `G` has a left-cancellative addition, a linear order,
  and addition is strictly monotone w.r.t. the first argument, then `G` has `UniqueSums`." ]
instance (priority := 100) of_Covariant_left [IsLeftCancelMul G]
    [LinearOrder G] [CovariantClass G G (Function.swap (· * ·)) (· < ·)] :
    UniqueProds G :=
let _ := LinearOrder.lift' (unop : Gᵐᵒᵖ → G) unop_injective
let _ : CovariantClass Gᵐᵒᵖ Gᵐᵒᵖ (· * ·) (· < ·) :=
{ elim := fun _ _ _ bc =>
          have : StrictMono (unop (α := G)) := fun _ _ => id
          mul_lt_mul_right' (α := G) bc (unop _) }
of_mulOpposite of_Covariant_right

open Finset
@[to_additive]
theorem mulHom_image_of_injective (f : H →ₙ* G) (hf : Function.Injective f) (uG : UniqueProds G) :
    UniqueProds H := by
  refine ⟨fun {A B} A0 B0 => ?_⟩
  classical
  obtain ⟨a0, ha0, b0, hb0, h⟩ := uG.uniqueMul_of_nonempty (A0.image f) (B0.image f)
  rcases mem_image.mp ha0 with ⟨a', ha', rfl⟩
  rcases mem_image.mp hb0 with ⟨b', hb', rfl⟩
  exact ⟨a', ha', b', hb', (UniqueMul.mulHom_image_iff f hf).mp h⟩

/-- `UniqueProd` is preserved under multiplicative equivalences. -/
@[to_additive "`UniqueSums` is preserved under additive equivalences."]
theorem mulHom_image_iff (f : G ≃* H) :
    UniqueProds G ↔ UniqueProds H :=
⟨mulHom_image_of_injective f.symm f.symm.injective, mulHom_image_of_injective f f.injective⟩

@[to_additive] instance [UniqueProds G] [UniqueProds H] : UniqueProds (G × H) where
  uniqueMul_of_nonempty {A B} hA hB := by
    classical
    obtain ⟨aG, hA, bG, hB, hG⟩ := uniqueMul_of_nonempty (hA.image Prod.fst) (hB.image Prod.fst)
    rw [mem_image, ← filter_nonempty_iff] at hA hB
    obtain ⟨aH, hA, bH, hB, hH⟩ := uniqueMul_of_nonempty (hA.image Prod.snd) (hB.image Prod.snd)
    simp_rw [mem_image, mem_filter] at hA hB
    refine ⟨(aG, aH), ?_, (bG, bH), ?_, fun a b ha hb he => ?_⟩
    · obtain ⟨a, ⟨ha, rfl⟩, rfl⟩ := hA; exact ha
    · obtain ⟨b, ⟨hb, rfl⟩, rfl⟩ := hB; exact hb
    rw [Prod.ext_iff] at he
    specialize hG (mem_image.mpr ⟨a, ha, rfl⟩) (mem_image.mpr ⟨b, hb, rfl⟩) he.1
    specialize hH _ _ he.2
    all_goals try simp_rw [mem_image, mem_filter]
    exacts [⟨a, ⟨ha, hG.1⟩, rfl⟩, ⟨b, ⟨hb, hG.2⟩, rfl⟩, ⟨Prod.ext hG.1 hH.1, Prod.ext hG.2 hH.2⟩]

@[to_additive] instance {ι} (G : ι → Type*) [∀ i, Mul (G i)] [∀ i, UniqueProds (G i)] :
    UniqueProds (∀ i, G i) where
  uniqueMul_of_nonempty {A} := by
    classical
    let _ := Finset.isWellFounded_ssubset (α := ∀ i, G i) -- why need this?
    apply IsWellFounded.induction (· ⊂ ·) A; intro A ihA B hA
    apply IsWellFounded.induction (· ⊂ ·) B; intro B ihB hB
    obtain hc | ⟨i, hc⟩ : (A.card ≤ 1 ∧ B.card ≤ 1) ∨
      ∃ i, (∃ a1 ∈ A, ∃ a2 ∈ A, a1 i ≠ a2 i) ∨ (∃ b1 ∈ B, ∃ b2 ∈ B, b1 i ≠ b2 i)
    · obtain hA1 | h1A := le_or_lt A.card 1
      · obtain hB1 | h1B := le_or_lt B.card 1
        · exact Or.inl ⟨hA1, hB1⟩
        obtain ⟨b1, h1, b2, h2, hne⟩ := Finset.one_lt_card.mp h1B
        obtain ⟨i, hne⟩ := Function.ne_iff.mp hne
        exact Or.inr ⟨i, Or.inr ⟨b1, h1, b2, h2, hne⟩⟩
      obtain ⟨a1, h1, a2, h2, hne⟩ := Finset.one_lt_card.mp h1A
      obtain ⟨i, hne⟩ := Function.ne_iff.mp hne
      exact Or.inr ⟨i, Or.inl ⟨a1, h1, a2, h2, hne⟩⟩
    · obtain ⟨a0, ha0⟩ := hA; obtain ⟨b0, hb0⟩ := hB
      simp_rw [Finset.card_le_one_iff] at hc
      exact ⟨a0, ha0, b0, hb0, fun a b ha hb _ => ⟨hc.1 ha ha0, hc.2 hb hb0⟩⟩
    obtain ⟨ai, hA, bi, hB, hi⟩ := uniqueMul_of_nonempty (hA.image (· i)) (hB.image (· i))
    rw [mem_image, ← filter_nonempty_iff] at hA hB
    let A' := A.filter (· i = ai); let B' := B.filter (· i = bi)
    obtain ⟨a0, ha0, b0, hb0, hu⟩ : ∃ a0 ∈ A', ∃ b0 ∈ B', UniqueMul A' B' a0 b0
    · rcases hc with ⟨a1, h1, a2, h2, hne⟩ | ⟨b1, h1, b2, h2, hne⟩
      · refine ihA _ ⟨A.filter_subset _, fun h => ?_⟩ hA hB
        obtain rfl | hai := eq_or_ne (a1 i) ai
        exacts [hne (mem_filter.mp <| h h2).2.symm, hai (mem_filter.mp <| h h1).2]
      by_cases hA' : A' = A
      · rw [hA']; refine ihB _ ⟨B.filter_subset _, fun h => ?_⟩ hB
        obtain rfl | hbi := eq_or_ne (b1 i) bi
        exacts [hne (mem_filter.mp <| h h2).2.symm, hbi (mem_filter.mp <| h h1).2]
      exact ihA A' ((A.filter_subset _).ssubset_of_ne hA') hA hB
    rw [mem_filter] at ha0 hb0
    refine ⟨a0, ha0.1, b0, hb0.1, fun a b ha hb he => ?_⟩
    specialize hi (mem_image_of_mem _ ha) (mem_image_of_mem _ hb) ?_
    · refine (congr_arg (· i) he).trans ?_; rw [← ha0.2, ← hb0.2]; rfl
    exact hu (mem_filter.mpr ⟨ha, hi.1⟩) (mem_filter.mpr ⟨hb, hi.2⟩) he

end UniqueProds

instance {ι} (G : ι → Type*) [∀ i, AddZeroClass (G i)] [∀ i, UniqueSums (G i)] :
    UniqueSums (Π₀ i, G i) :=
  UniqueSums.addHom_image_of_injective
    DFinsupp.coeFnAddMonoidHom.toAddHom FunLike.coe_injective inferInstance

instance {ι G} [AddZeroClass G] [UniqueSums G] : UniqueSums (ι →₀ G) :=
  UniqueSums.addHom_image_of_injective
    Finsupp.coeFnAddHom.toAddHom FunLike.coe_injective inferInstance
