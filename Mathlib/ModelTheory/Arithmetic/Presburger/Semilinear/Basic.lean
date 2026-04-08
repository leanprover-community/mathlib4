/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Defs

import Mathlib.Algebra.Group.Submonoid.Finsupp
import Mathlib.Algebra.Order.Group.Ideal
import Mathlib.Algebra.Order.Pi
import Mathlib.Algebra.Order.Sub.Prod
import Mathlib.Algebra.Order.Sub.Unbundled.Hom
import Mathlib.Data.Pi.Interval
import Mathlib.Data.Rat.Floor
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Localization.Module

/-!
# Semilinear sets are closed under intersection, set difference and complement

This file proves that the semilinear sets in any commutative monoid are closed under intersection
and set difference. They are also closed under complement if the monoid is finitely generated. We
prove these results on `ℕ ^ k` first (which are private APIs in this file) and then generalize to
any commutative monoid.

## Main Results

- `isSemilinearSet_setOf_eq`: the set of solutions to a linear equation `a + f x = b + g y` is
  semilinear.
- `IsSemilinearSet.inter`, `IsSemilinearSet.diff`: semilinear sets are closed under intersection and
  set difference.
- `IsSemilinearSet.compl`: semilinear sets in a finitely generated commutative monoid are closed
  under complement.

## References

* [Seymour Ginsburg and Edwin H. Spanier, *Bounded ALGOL-Like Languages*][ginsburg1964]
* [Samuel Eilenberg and M. P. Schützenberger, *Rational Sets in Commutative Monoids*][eilenberg1969]
-/

open Set Pointwise AddSubmonoid Matrix

/-!
### Semilinearity from slice property

A set `s` is said to have slice property if `a + b + c ∈ s` whenever `a ∈ s`, `a + b ∈ s` and
`a + c ∈ s`. In `ℕ ^ k`, any set that has slice property is a semilinear set. This is an important
lemma to prove the semilinearity of linear equation solutions.
-/

private def IsSlice {M : Type*} [Add M] (s : Set M) :=
  ∀ a ∈ s, ∀ b c, a + b ∈ s → a + c ∈ s → a + b + c ∈ s

namespace IsSlice

private theorem sep_apply_eq {ι : Type*} {M : ι → Type*} [∀ i, Add (M i)] {s : Set (∀ i, M i)}
    (hs : IsSlice s) (i : ι) (a : M i) : IsSlice { x ∈ s | x i = a } := by
  intro x ⟨hx, hxi⟩ y z ⟨hxy, hxyi⟩ ⟨hxz, hxzi⟩
  refine ⟨hs _ hx _ _ hxy hxz, ?_⟩
  simp only [Pi.add_apply] at *
  rw [hxyi, ← hxi, hxzi, hxi]

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [WellQuasiOrderedLE M]
  [IsOrderedCancelAddMonoid M] [CanonicallyOrderedAdd M]

private theorem exists_isSemilinearSet_setOf_le {s : Set M} (hs : IsSlice s) (hs' : s.Nonempty) :
    ∃ x ∈ s, IsSemilinearSet { y ∈ s | x ≤ y } := by
  classical
  let f (x : M) : AddSubmonoid M :=
    if hx : x ∈ s then
      { carrier := { y | x + y ∈ s }
        zero_mem' := by simpa
        add_mem' := by
          intro a b ha hb
          simp only [mem_setOf_eq] at *
          rw [← add_assoc]
          exact hs _ hx _ _ ha hb }
    else ⊥
  have hf : ∀ x ∈ s, ∀ y, y ∈ f x ↔ x + y ∈ s := by simp_all [f]
  let g (x : M) : AddSemigroupIdeal M := .closure (f x \ {0})
  have hg : ∀ x ∈ s, ∀ y ∈ s, x ≤ y → g x ≤ g y := by
    intro x hx y hy hxy z hz
    rw [le_iff_exists_add] at hxy
    rcases hxy with ⟨y, rfl⟩
    simp only [AddSemigroupIdeal.mem_closure'', mem_diff, SetLike.mem_coe, mem_singleton_iff,
      g] at hz ⊢
    rcases hz with ⟨y', z, ⟨hz₁, hz₂⟩, rfl⟩
    rw [hf _ hx] at hz₁
    refine ⟨y', z, ⟨?_, hz₂⟩, rfl⟩
    rw [hf _ hy]
    exact hs _ hx _ _ hy hz₁
  rcases exists_maximalFor_of_wellFoundedGT (· ∈ s) g hs' with ⟨a, ha⟩
  refine ⟨a, ha.1, ?_⟩
  convert_to IsSemilinearSet (a +ᵥ (f a : Set M))
  · ext x
    simp only [le_iff_exists_add, mem_setOf_eq, ha.1, ↓reduceDIte, coe_set_mk,
      AddSubsemigroup.coe_set_mk, mem_vadd_set, vadd_eq_add, f]
    grind
  · refine IsSemilinearSet.vadd a (.of_fg (AddSubmonoid.fg_of_subtractive ?_))
    intro x hx y hxy
    rw [hf _ ha.1] at hx
    rw [hf _ ha.1, ← add_assoc] at hxy
    by_cases hy : y = 0
    · simp [hy]
    replace hy : y ∈ g (a + x) := by
      apply AddSemigroupIdeal.subset_closure
      refine Set.mem_diff_of_mem ?_ hy
      rwa [SetLike.mem_coe, hf _ hx]
    apply ha.2 hx (hg _ ha.1 _ hx le_self_add) at hy
    simp only [g, AddSemigroupIdeal.mem_closure'', Set.mem_diff, SetLike.mem_coe,
      Set.notMem_singleton_iff] at hy
    rcases hy with ⟨w, u, ⟨hu₁, hu₂⟩, rfl⟩
    induction w using WellQuasiOrderedLE.to_wellFoundedLT.induction (α := M) generalizing u with
      | _ w ih
    by_cases hw₁ : w = 0
    · simpa [hw₁]
    have hxu : a + x + u ∈ s := hs _ ha.1 _ _ hx (by rwa [hf _ ha.1] at hu₁)
    have hw₂ : w ∈ g (a + x + u) := by
      apply AddSemigroupIdeal.subset_closure
      refine Set.mem_diff_of_mem ?_ hw₁
      rwa [SetLike.mem_coe, hf _ hxu, add_assoc, add_comm u w]
    apply ha.2 hxu (hg _ ha.1 _ hxu (le_add_right le_self_add)) at hw₂
    simp only [g, AddSemigroupIdeal.mem_closure'', Set.mem_diff, SetLike.mem_coe,
      Set.notMem_singleton_iff] at hw₂
    rcases hw₂ with ⟨w', u', ⟨hu'₁, hu'₂⟩, rfl⟩
    rw [add_assoc]
    apply ih
    · exact lt_add_of_pos_right _ (pos_of_ne_zero hu'₂)
    · exact add_mem hu'₁ hu₁
    · simp [hu₂, hu'₂]
    · rwa [← add_assoc w']

end IsSlice

private theorem Nat.isSemilinearSet_of_isSlice {ι : Type*} [Finite ι] {s : Set (ι → ℕ)}
    (hs : IsSlice s) : IsSemilinearSet s := by
  classical
  suffices h : ∀ (a : ι → ℕ) (t : Finset ι), (∀ x ∈ s, ∀ i ∉ t, x i = a i) → IsSemilinearSet s by
    haveI := Fintype.ofFinite ι
    exact h 0 Finset.univ (by simp)
  intro a t ht
  induction t using Finset.strongInductionOn generalizing s a with | _ t ih
  obtain rfl | hs' := s.eq_empty_or_nonempty
  · exact .empty
  rcases hs.exists_isSemilinearSet_setOf_le hs' with ⟨x, hx, hx'⟩
  convert_to IsSemilinearSet ({ y ∈ s | x ≤ y } ∪ ⋃ i ∈ t, ⋃ j ∈ Finset.range (x i),
    { y ∈ s | y i = j })
  · ext y
    simp only [Finset.mem_range, mem_union, mem_setOf_eq, mem_iUnion, Pi.le_def]
    grind
  · refine hx'.union (.biUnion_finset fun i hi => .biUnion_finset fun j hj => ?_)
    simp only [Finset.mem_range] at hj
    apply ih _ (Finset.erase_ssubset hi) (hs.sep_apply_eq _ _) (Function.update a i j)
    grind [Function.update]

/-! ### Semilinearity of linear equations and preimages -/

variable {M N ι κ : Type*} [AddCommMonoid M] [AddCommMonoid N] {s s₁ s₂ : Set M}

private theorem Nat.isSemilinearSet_setOf_eq [Finite ι] {F G : Type*}
    [FunLike F (ι → ℕ) M] [AddMonoidHomClass F (ι → ℕ) M] [FunLike G (ι → ℕ) M]
    [AddMonoidHomClass G (ι → ℕ) M] (a b : M) (f : F) (g : G) :
    IsSemilinearSet { x | a + f x = b + g x } := by
  apply isSemilinearSet_of_isSlice
  intro x hx y z hy hz
  simp only [mem_setOf, map_add, ← add_assoc] at *
  conv_lhs => rw [hy, ← hx, add_right_comm _ (g y) (f z), hz, add_right_comm _ (g z)]

/-- The set of solutions to a linear equation `a + f x = b + g y` in a finitely generated monoid is
semilinear. -/
public theorem isSemilinearSet_setOf_eq [AddMonoid.FG M] {F G : Type*} [FunLike F M N]
    [AddMonoidHomClass F M N] [FunLike G M N] [AddMonoidHomClass G M N] (a b : N) (f : F) (g : G) :
    IsSemilinearSet { x | a + f x = b + g x } := by
  rcases fg_iff_exists_fin_addMonoidHom.1 (AddMonoid.FG.fg_top (M := M)) with ⟨n, h, hh⟩
  rw [AddMonoidHom.mrange_eq_top] at hh
  rw [← image_preimage_eq { x | a + f x = b + g x } hh, preimage_setOf_eq]
  apply IsSemilinearSet.image
  exact Nat.isSemilinearSet_setOf_eq a b (AddMonoidHom.comp f h) (AddMonoidHom.comp g h)

/-- Matrix version of `isSemilinearSet_setOf_eq`. -/
public theorem Nat.isSemilinearSet_setOf_mulVec_eq [Fintype κ] (u v : ι → ℕ) (A B : Matrix ι κ ℕ) :
    IsSemilinearSet { x | u + A *ᵥ x = v + B *ᵥ x } :=
  isSemilinearSet_setOf_eq u v A.mulVecLin B.mulVecLin

public theorem isLinearSet_iff_exists_fin_addMonoidHom {s : Set M} :
    IsLinearSet s ↔ ∃ (a : M) (n : ℕ) (f : (Fin n → ℕ) →+ M), s = a +ᵥ Set.range f := by
  simp_rw [isLinearSet_iff_exists_fg_eq_vadd, fg_iff_exists_fin_addMonoidHom,
    ← AddMonoidHom.coe_mrange]
  congr! with a
  refine ⟨fun ⟨P, ⟨n, f, hf⟩, hs⟩ => ⟨n, f, ?_⟩, fun ⟨n, f, hs⟩ => ⟨_, ⟨n, f, rfl⟩, ?_⟩⟩
  · rw [hf, hs]
  · rw [hs]

public theorem Nat.isLinearSet_iff_exists_matrix {s : Set (ι → ℕ)} :
    IsLinearSet s ↔ ∃ (v : ι → ℕ) (n : ℕ) (A : Matrix ι (Fin n) ℕ), s = { v + A *ᵥ x | x } := by
  rw [isLinearSet_iff_exists_fin_addMonoidHom]
  refine exists₂_congr fun v n => ⟨fun ⟨f, hf⟩ => ⟨f.toNatLinearMap.toMatrix', ?_⟩, fun ⟨A, hA⟩ =>
    ⟨A.mulVecLin, ?_⟩⟩ <;> ext <;> simp [*, mem_vadd_set]

private lemma Nat.isSemilinearSet_preimage_of_isLinearSet [Finite ι] {F : Type*}
    [FunLike F (ι → ℕ) M] [AddMonoidHomClass F (ι → ℕ) M] {s : Set M} (hs : IsLinearSet s) (f : F) :
    IsSemilinearSet (f ⁻¹' s) := by
  rw [isLinearSet_iff_exists_fin_addMonoidHom] at hs
  rcases hs with ⟨a, n, g, rfl⟩
  change IsSemilinearSet { x | f x ∈ _ }
  simp only [mem_vadd_set, mem_range, vadd_eq_add, exists_exists_eq_and]
  apply IsSemilinearSet.proj'
  convert isSemilinearSet_setOf_eq a 0 (g.comp (LinearMap.funLeft ℕ ℕ Sum.inr).toAddMonoidHom)
    ((f : (ι → ℕ) →+ M).comp (LinearMap.funLeft ℕ ℕ Sum.inl).toAddMonoidHom)
  simp [LinearMap.funLeft]

private theorem Nat.isSemilinearSet_preimage [Finite ι] {F : Type*}
    [FunLike F (ι → ℕ) M] [AddMonoidHomClass F (ι → ℕ) M] {s : Set M} (hs : IsSemilinearSet s)
    (f : F) : IsSemilinearSet (f ⁻¹' s) := by
  rcases hs with ⟨S, hS, hS', rfl⟩
  simp_rw [sUnion_eq_biUnion, preimage_iUnion]
  exact .biUnion hS fun s hs => isSemilinearSet_preimage_of_isLinearSet (hS' s hs) f

/-- The preimage of a semilinear set under a homomorphism in a finitely generated monoid is
semilinear. -/
public theorem IsSemilinearSet.preimage [AddMonoid.FG M] {F : Type*} [FunLike F M N]
    [AddMonoidHomClass F M N] {s : Set N} (hs : IsSemilinearSet s) (f : F) :
    IsSemilinearSet (f ⁻¹' s) := by
  rcases fg_iff_exists_fin_addMonoidHom.1 (AddMonoid.FG.fg_top (M := M)) with ⟨n, g, hg⟩
  rw [AddMonoidHom.mrange_eq_top] at hg
  rw [← image_preimage_eq (f ⁻¹' s) hg]
  apply image
  rw [← preimage_comp, ← AddMonoidHom.coe_coe, ← AddMonoidHom.coe_comp]
  exact Nat.isSemilinearSet_preimage hs _

/-! ### Semilinear sets are included in finitely generated submonoids -/

public lemma IsLinearSet.exists_fg_eq_subtypeVal (hs : IsLinearSet s) :
    ∃ (P : AddSubmonoid M) (s' : Set P), P.FG ∧ IsLinearSet s' ∧ s = Subtype.val '' s' := by
  rcases hs with ⟨a, t, ht, rfl⟩
  refine ⟨_, _, (fg_iff _).2 ⟨insert a t, rfl, ht.insert a⟩,
    ⟨⟨_, mem_closure_of_mem (mem_insert a t)⟩, _, ht.preimage Subtype.val_injective.injOn, rfl⟩, ?_⟩
  rw [← coe_subtype, image_vadd_distrib, subtype_apply, ← coe_map, AddMonoidHom.map_mclosure]
  congr
  ext x
  simpa using mem_closure_of_mem ∘ mem_insert_of_mem a

public lemma IsSemilinearSet.exists_fg_eq_subtypeVal (hs : IsSemilinearSet s) :
    ∃ (P : AddSubmonoid M) (s' : Set P), P.FG ∧ IsSemilinearSet s' ∧ s = Subtype.val '' s' := by
  rcases hs with ⟨S, hS, hS', rfl⟩
  choose! P t hP ht ht' using fun s hs => (hS' s hs).exists_fg_eq_subtypeVal
  haveI : Finite S := hS
  refine ⟨⨆ s : S, P s, ⋃ (s : S), AddSubmonoid.inclusion (le_iSup _ s) '' t s.1,
    .iSup _ fun s => hP s s.2, .iUnion fun s => (ht s s.2).isSemilinearSet.image _, ?_⟩
  simp_rw [sUnion_eq_iUnion, image_iUnion, image_image, AddSubmonoid.coe_inclusion,
    fun s : S => ht' s s.2]

public lemma IsSemilinearSet.exists_fg_eq_subtypeVal₂ (hs₁ : IsSemilinearSet s₁)
    (hs₂ : IsSemilinearSet s₂) :
    ∃ (P : AddSubmonoid M) (s₁' s₂' : Set P), P.FG ∧ IsSemilinearSet s₁' ∧ s₁ = Subtype.val '' s₁'
      ∧ IsSemilinearSet s₂' ∧ s₂ = Subtype.val '' s₂' := by
  rcases hs₁.exists_fg_eq_subtypeVal with ⟨P₁, s₁', hP₁, hs₁', rfl⟩
  rcases hs₂.exists_fg_eq_subtypeVal with ⟨P₂, s₂', hP₂, hs₂', rfl⟩
  refine ⟨P₁ ⊔ P₂, (AddSubmonoid.inclusion le_sup_left) '' s₁',
    (AddSubmonoid.inclusion le_sup_right) '' s₂', hP₁.sup hP₂, hs₁'.image _, ?_, hs₂'.image _, ?_⟩
    <;> simp_rw [image_image, AddSubmonoid.coe_inclusion]

/-! ### Semilinearity of intersection -/

private lemma Nat.isSemilinearSet_inter_of_isLinearSet [Finite ι] {s₁ s₂ : Set (ι → ℕ)}
    (hs₁ : IsLinearSet s₁) (hs₂ : IsLinearSet s₂) : IsSemilinearSet (s₁ ∩ s₂) := by
  classical
  haveI := Fintype.ofFinite ι
  rw [isLinearSet_iff_exists_matrix] at hs₁ hs₂
  rcases hs₁ with ⟨u, n, A, rfl⟩
  rcases hs₂ with ⟨v, m, B, rfl⟩
  simp_rw [← setOf_and, exists_and_exists_comm]
  refine IsSemilinearSet.proj' (IsSemilinearSet.proj' ?_)
  convert isSemilinearSet_setOf_mulVec_eq (κ := (ι ⊕ Fin n) ⊕ Fin m) (Sum.elim u v) 0
    (fromBlocks (fromCols 0 A) 0 0 B) (fromBlocks (fromCols 1 0) 0 (fromCols 1 0) 0)
  simp [fromBlocks_mulVec, fromCols_mulVec, ← Sum.elim_add_add, Sum.elim_eq_iff]

private theorem Nat.isSemilinearSet_inter [Finite ι] {s₁ s₂ : Set (ι → ℕ)}
    (hs₁ : IsSemilinearSet s₁) (hs₂ : IsSemilinearSet s₂) : IsSemilinearSet (s₁ ∩ s₂) := by
  rcases hs₁ with ⟨S₁, hS₁, hS₁', rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, hS₂', rfl⟩
  rw [sUnion_inter_sUnion]
  exact .biUnion (hS₁.prod hS₂) fun s hs =>
    isSemilinearSet_inter_of_isLinearSet (hS₁' _ hs.1) (hS₂' _ hs.2)

/-- Semilinear sets are closed under intersection. -/
public theorem IsSemilinearSet.inter (hs₁ : IsSemilinearSet s₁) (hs₂ : IsSemilinearSet s₂) :
    IsSemilinearSet (s₁ ∩ s₂) := by
  rcases hs₁.exists_fg_eq_subtypeVal₂ hs₂ with ⟨P, s₁', s₂', hP, hs₁', rfl, hs₂', rfl⟩
  rw [← image_inter Subtype.val_injective]
  apply image (f := P.subtype)
  rw [← AddMonoid.fg_iff_addSubmonoid_fg, AddMonoid.fg_def, fg_iff_exists_fin_addMonoidHom] at hP
  rcases hP with ⟨n, f, hf⟩
  rw [AddMonoidHom.mrange_eq_top] at hf
  rw [← image_preimage_eq (s₁' ∩ s₂') hf, preimage_inter]
  apply image
  apply Nat.isSemilinearSet_inter <;> apply Nat.isSemilinearSet_preimage <;> assumption

public theorem IsSemilinearSet.sInter [AddMonoid.FG M] {S : Set (Set M)} (hS : S.Finite)
    (hS' : ∀ s ∈ S, IsSemilinearSet s) : IsSemilinearSet (⋂₀ S) := by
  induction S, hS using Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    simp_rw [mem_insert_iff, forall_eq_or_imp] at hS'
    simpa using hS'.1.inter (ih hS'.2)

public theorem IsSemilinearSet.iInter [AddMonoid.FG M] [Finite ι] {s : ι → Set M}
    (hs : ∀ i, IsSemilinearSet (s i)) : IsSemilinearSet (⋂ i, s i) := by
  rw [← sInter_range]
  apply sInter (finite_range s)
  simpa

public theorem IsSemilinearSet.biInter [AddMonoid.FG M] {s : Set ι} {t : ι → Set M} (hs : s.Finite)
    (ht : ∀ i ∈ s, IsSemilinearSet (t i)) : IsSemilinearSet (⋂ i ∈ s, t i) := by
  rw [← sInter_image]
  apply sInter (hs.image t)
  simpa

public theorem IsSemilinearSet.biInter_finset [AddMonoid.FG M] {s : Finset ι} {t : ι → Set M}
    (ht : ∀ i ∈ s, IsSemilinearSet (t i)) : IsSemilinearSet (⋂ i ∈ s, t i) :=
  biInter s.finite_toSet ht

/-!
### Semilinearity of complement and set difference

We first show that the complement of a proper linear set `s` in `ℕ ^ k` is semilinear, through
several private definitions:

1. `base`, `periods`: the base vector and the set of periods of the proper linear set `s`.
2. `basisSet`, `basis`: the linearly independent periods of `s` can be extended to a basis of
  `ℚ ^ k`.
3. `fundamentalDomain`: the set of vectors in `ℕ ^ k`, starting from `base`, with coordinates under
  `basis` in `[0, 1) ^ k`.
4. `floor`, `fract`: every vector in `ℕ ^ k` can be decomposed into a `ℤ`-linear combination of
  `basisSet` and a vector in `fundamentalDomain`.
5. `setOfFractNe`, `setOfFloorNeg`, `setOfFloorPos`: the complement of `s` is decomposed into three
  semilinear sets.

Closure of semilinear sets under complement and set difference follows.
-/

private def toRatVec : (ι → ℕ) →+ (ι → ℚ) :=
  (Nat.castAddMonoidHom ℚ).compLeft ι

private theorem toRatVec_inj (x y : ι → ℕ) : toRatVec x = toRatVec y ↔ x = y := by
  refine ⟨fun h => ?_, congr_arg toRatVec⟩
  ext i
  simpa [toRatVec] using congr_fun h i

private theorem toRatVec_mono (x y : ι → ℕ) : toRatVec x ≤ toRatVec y ↔ x ≤ y := by
  apply forall_congr'
  simp [toRatVec]

private theorem toRatVec_nonneg (x : ι → ℕ) : 0 ≤ toRatVec x := by
  rw [← map_zero toRatVec, toRatVec_mono]
  simp

private theorem linearIndepOn_toRatVec {s : Set (ι → ℕ)} (hs : LinearIndepOn ℕ id s) :
    LinearIndepOn ℚ toRatVec s := by
  rw [LinearIndepOn, ← LinearIndependent.iff_fractionRing ℤ ℚ, ← LinearIndepOn, linearIndepOn_iff'']
  intro t f ht hf heq i hi
  rw [linearIndepOn_iff_linearIndepOn_finset] at hs
  specialize hs t ht
  rw [linearIndepOn_finset_iffₛ] at hs
  specialize hs (Int.toNat ∘ f) (Int.toNat ∘ (-·) ∘ f) ?_ i hi
  · simp_rw [← toRatVec_inj, map_sum]
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← heq]
    refine Finset.sum_congr rfl fun j hj => ?_
    conv_rhs => rw [← (f j).toNat_sub_toNat_neg]
    simp only [sub_smul, map_nsmul, natCast_zsmul, Function.comp_apply, id_eq]
  · rw [← (f i).toNat_sub_toNat_neg, sub_eq_zero, Int.natCast_inj]
    simpa using hs

namespace IsProperLinearSet

variable {s : Set (ι → ℕ)} (hs : IsProperLinearSet s)

open Module Submodule

private noncomputable def base : ι → ℕ := hs.choose

private noncomputable def periods : Set (ι → ℕ) := hs.choose_spec.choose

private theorem finite_periods : hs.periods.Finite := hs.choose_spec.choose_spec.1

private theorem linearIndepOn_periods : LinearIndepOn ℕ id (hs.periods : Set (ι → ℕ)) :=
  hs.choose_spec.choose_spec.2.1

private theorem eq_base_vadd_closure_periods : s = hs.base +ᵥ (closure hs.periods : Set (ι → ℕ)) :=
  hs.choose_spec.choose_spec.2.2

variable [Finite ι]

private noncomputable def basisSet : Set (ι → ℕ) :=
  (linearIndepOn_toRatVec hs.linearIndepOn_periods).extend
    (@subset_union_left _ hs.periods <| range (Pi.basisFun ℕ ι))

private theorem periods_subset_basisSet : hs.periods ⊆ hs.basisSet :=
  (linearIndepOn_toRatVec hs.linearIndepOn_periods).subset_extend _

private theorem basisSet_subset_union : hs.basisSet ⊆ hs.periods ∪ range (Pi.basisFun ℕ ι) :=
  (linearIndepOn_toRatVec hs.linearIndepOn_periods).extend_subset _

private theorem finite_basisSet : hs.basisSet.Finite :=
  (hs.finite_periods.union (finite_range _)).subset hs.basisSet_subset_union

private noncomputable local instance : Fintype hs.basisSet :=
  hs.finite_basisSet.fintype

private theorem linearIndepOn_basisSet : LinearIndepOn ℚ toRatVec hs.basisSet :=
  (linearIndepOn_toRatVec hs.linearIndepOn_periods).linearIndepOn_extend _

private theorem span_basisSet : span ℚ (toRatVec '' hs.basisSet) = ⊤ := by
  classical
  rw [basisSet, (linearIndepOn_toRatVec hs.linearIndepOn_periods).span_image_extend_eq_span_image,
    ← top_le_iff]
  apply (span_mono (image_mono subset_union_right)).trans'
  rw [top_le_iff]
  convert (Pi.basisFun ℚ ι).span_eq
  ext
  simp only [mem_image, mem_range, exists_exists_eq_and]
  congr!
  ext
  simp [toRatVec, Pi.basisFun_apply, Pi.single_apply]

private noncomputable def basis : Basis hs.basisSet ℚ (ι → ℚ) :=
  Basis.mk hs.linearIndepOn_basisSet (image_eq_range _ _ ▸ top_le_iff.2 hs.span_basisSet)

private theorem basis_apply (i) : hs.basis i = toRatVec i.1 := by
  simp [basis]

private noncomputable def fundamentalDomain : Set (ι → ℕ) :=
  { x | ∀ i, hs.basis.repr (toRatVec x - toRatVec hs.base) i ∈ Ico 0 1 }

private theorem finite_fundamentalDomain : hs.fundamentalDomain.Finite := by
  classical
  haveI := Fintype.ofFinite ι
  apply (finite_Iic (hs.base + ∑ i : hs.basisSet, i.1)).subset
  intro x hx
  rw [mem_Iic, ← toRatVec_mono, map_add, map_sum, ← add_sub_cancel (toRatVec hs.base) (toRatVec x),
    add_le_add_iff_left, ← hs.basis.sum_repr (toRatVec x - toRatVec hs.base)]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [← hs.basis_apply i]
  apply smul_le_of_le_one_left
  · rw [hs.basis_apply]
    exact toRatVec_nonneg _
  · exact (hx i).2.le

private noncomputable def floor (x i) :=
  ⌊hs.basis.repr (toRatVec x - toRatVec hs.base) i⌋

private noncomputable def fract (x) :=
  x + ∑ i, (-hs.floor x i).toNat • i.1 - ∑ i, (hs.floor x i).toNat • i.1

private theorem floor_base (i) : hs.floor hs.base i = 0 := by simp [floor]

private theorem fract_base : hs.fract hs.base = hs.base := by simp [fract, hs.floor_base]

private theorem floor_add_nsmul_self {x i} {n : ℕ} :
    hs.floor (x + n • i.1) i = hs.floor x i + n := by
  simp only [floor]
  rw [map_add, ← sub_add_eq_add_sub]
  simp [-nsmul_eq_mul, ← hs.basis_apply]

private theorem floor_add_sum {f : (ι → ℕ) → ℕ} {x i} :
    hs.floor (x + ∑ j : hs.basisSet, f j • j.1) i = hs.floor x i + f i.1 := by
  classical
  simp only [floor]
  rw [map_add, ← sub_add_eq_add_sub, ← Finset.sum_coe_sort]
  simp [-nsmul_eq_mul, ← hs.basis_apply, Finsupp.single_apply]

private theorem floor_le_floor_add_of_mem_closure {x y i} (hy : y ∈ closure hs.basisSet) :
    hs.floor x i ≤ hs.floor (x + y) i := by
  classical
  simp only [floor]
  apply Int.floor_le_floor
  simp_rw [map_add, add_sub_right_comm, map_add, Finsupp.add_apply, le_add_iff_nonneg_right]
  rw [mem_closure_iff_of_fintype] at hy
  rcases hy with ⟨f, rfl⟩
  simp_rw [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
  apply Finset.sum_nonneg
  simp [-nsmul_eq_mul, ← hs.basis_apply, Finsupp.single_apply, ite_nonneg]

private theorem floor_add_of_mem_closure {x y i t} (ht : t ⊆ hs.basisSet) (hi : i.1 ∉ t)
    (hy : y ∈ closure t) : hs.floor (x + y) i = hs.floor x i := by
  classical
  suffices hs.basis.repr (toRatVec y) i = 0 by
    simp [floor, this]
  induction hy using AddSubmonoid.closure_induction with
  | mem y hy =>
    rw [← hs.basis_apply ⟨y, ht hy⟩]
    simpa [Finsupp.single_apply, ← Subtype.val_inj] using ne_of_mem_of_not_mem hy hi
  | zero => simp
  | add _ _ _ _ ih₁ ih₂ => simp [ih₁, ih₂]

private theorem floor_toNat_sum_le (x) :
    ∑ i, (hs.floor x i).toNat • i.1 ≤ x + ∑ i, (-hs.floor x i).toNat • i.1 := by
  rw [← toRatVec_mono]
  simp only [floor, map_add, map_sum, map_nsmul]
  rw [← sub_le_iff_le_add, ← Finset.sum_sub_distrib]
  conv =>
    enter [1, 2, _]
    rw [← Nat.cast_smul_eq_nsmul ℤ, ← Nat.cast_smul_eq_nsmul ℤ, ← sub_smul,
      Int.toNat_sub_toNat_neg, ← Int.cast_smul_eq_zsmul ℚ]
  trans toRatVec x - toRatVec hs.base
  · conv => rhs; rw [← hs.basis.sum_repr (toRatVec x - toRatVec hs.base)]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [basis_apply]
    exact smul_le_smul_of_nonneg_right (Int.floor_le _) (toRatVec_nonneg _)
  · simp [toRatVec_nonneg]

private theorem add_floor_neg_toNat_sum_eq (x) :
    x + ∑ i, (-hs.floor x i).toNat • i.1 = hs.fract x + ∑ i, (hs.floor x i).toNat • i.1 := by
  simp only [fract]
  rw [tsub_add_cancel_of_le (hs.floor_toNat_sum_le x)]

private theorem toRatVec_fract_eq (x) :
    toRatVec (hs.fract x) = toRatVec hs.base +
      ∑ i, Int.fract (hs.basis.repr (toRatVec x - toRatVec hs.base) i) • toRatVec i.1 := by
  simp only [fract]
  rw [← map_tsub_of_le _ _ _ (hs.floor_toNat_sum_le x)]
  simp only [map_add, map_sum, map_nsmul]
  rw [← sub_add_eq_add_sub, sub_add, ← Finset.sum_sub_distrib]
  conv =>
    enter [1, 2, 2, _]
    rw [← Nat.cast_smul_eq_nsmul ℤ, ← Nat.cast_smul_eq_nsmul ℤ, ← sub_smul,
      Int.toNat_sub_toNat_neg]
  rw [sub_eq_iff_eq_add, add_assoc, ← sub_eq_iff_eq_add', ← Finset.sum_add_distrib]
  simp only [floor]
  conv =>
    enter [2, 2, _]
    rw [← Int.cast_smul_eq_zsmul ℚ, ← add_smul, Int.fract_add_floor, ← hs.basis_apply]
  rw [hs.basis.sum_repr]

private theorem fract_add_of_mem_closure {x y} (hy : y ∈ closure hs.basisSet) :
    hs.fract (x + y) = hs.fract x := by
  classical
  rw [mem_closure_iff_of_fintype] at hy
  rcases hy with ⟨f, t, ht, hf, rfl⟩
  rw [← toRatVec_inj, hs.toRatVec_fract_eq, hs.toRatVec_fract_eq]
  congr! 3
  rw [map_add, ← sub_add_eq_add_sub]
  simp [-nsmul_eq_mul, ← hs.basis_apply, Finsupp.single_apply]

private theorem fract_mem_fundamentalDomain (x) : hs.fract x ∈ hs.fundamentalDomain := by
  classical
  intro i
  constructor
  · rw [hs.toRatVec_fract_eq, add_sub_cancel_left]
    simp [← hs.basis_apply, Finsupp.single_apply]
  · rw [hs.toRatVec_fract_eq, add_sub_cancel_left]
    simp [← hs.basis_apply, Finsupp.single_apply, Int.fract_lt_one]

private theorem fract_eq_self_of_mem_fundamentalDomain {x} (hx : x ∈ hs.fundamentalDomain) :
    hs.fract x = x := by
  rw [← toRatVec_inj, hs.toRatVec_fract_eq]
  conv_lhs =>
    enter [2, 2, i]
    rw [Int.fract_eq_self.2 (hx i), ← hs.basis_apply]
  rw [hs.basis.sum_repr]
  simp

private theorem mem_iff_fract_eq_and_floor_nonneg (x) :
    x ∈ s ↔
      hs.fract x = hs.base ∧ ∀ i, 0 ≤ hs.floor x i ∧ (i.1 ∉ hs.periods → hs.floor x i = 0) := by
  classical
  nth_rw 1 [hs.eq_base_vadd_closure_periods]
  simp only [mem_vadd_set, SetLike.mem_coe, vadd_eq_add]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, fun i => ⟨?_, fun hi => ?_⟩⟩
    · rw [hs.fract_add_of_mem_closure, hs.fract_base]
      exact closure_mono hs.periods_subset_basisSet hy
    · rw [← hs.floor_base i]
      exact hs.floor_le_floor_add_of_mem_closure (closure_mono hs.periods_subset_basisSet hy)
    · rw [hs.floor_add_of_mem_closure hs.periods_subset_basisSet hi hy, hs.floor_base]
  · intro ⟨hx₁, hx₂⟩
    refine ⟨∑ i : hs.basisSet with i.1 ∈ hs.periods, (hs.floor x i).toNat • i.1,
      sum_mem fun i hi => nsmul_mem (mem_closure_of_mem (Finset.mem_filter.1 hi).2) _, ?_⟩
    rw [Finset.sum_filter, ← hx₁]
    conv_rhs =>
      rw [← add_zero x, ← Finset.sum_const_zero (ι := hs.basisSet) (s := Finset.univ)]
    convert (hs.add_floor_neg_toNat_sum_eq x).symm using 3 with i _ i
    · split_ifs with hi
      · simp
      · simp [(hx₂ i).2 hi]
    · simp [fun i => Int.toNat_eq_zero.2 (neg_nonpos.2 (hx₂ i).1)]

private noncomputable def setOfFractNe : Set (ι → ℕ) := { x | hs.fract x ≠ hs.base }

private theorem isSemilinearSet_setOfFractNe : IsSemilinearSet hs.setOfFractNe := by
  convert_to IsSemilinearSet (⋃ u ∈ hs.fundamentalDomain \ {hs.base}, { x |
    ∃ y ∈ closure hs.basisSet, ∃ y' ∈ closure hs.basisSet, x + y' = u + y }) using 1
  · ext x
    simp only [setOfFractNe, mem_iUnion, mem_setOf_eq, exists_prop]
    constructor
    · intro hx
      refine ⟨hs.fract x, ⟨hs.fract_mem_fundamentalDomain x, hx⟩, ∑ i, (hs.floor x i).toNat • i.1,
        ?_, ∑ i, (-hs.floor x i).toNat • i.1, ?_, ?_⟩
      · exact sum_mem fun i _ => nsmul_mem (mem_closure_of_mem i.2) _
      · exact sum_mem fun i _ => nsmul_mem (mem_closure_of_mem i.2) _
      · exact hs.add_floor_neg_toNat_sum_eq x
    · rintro ⟨u, ⟨hu, hu'⟩, y, hy, y', hy', heq⟩
      apply congr_arg hs.fract at heq
      rw [hs.fract_add_of_mem_closure hy', hs.fract_add_of_mem_closure hy,
        hs.fract_eq_self_of_mem_fundamentalDomain hu] at heq
      rwa [heq]
  · refine .biUnion hs.finite_fundamentalDomain.diff fun i hi => .proj' ?_
    rw [setOf_and]
    apply Nat.isSemilinearSet_inter <| Nat.isSemilinearSet_preimage
      (.closure_of_finite hs.finite_basisSet) (LinearMap.funLeft ℕ ℕ Sum.inr)
    apply IsSemilinearSet.proj'
    rw [setOf_and]
    apply Nat.isSemilinearSet_inter <| Nat.isSemilinearSet_preimage
      (.closure_of_finite hs.finite_basisSet) (LinearMap.funLeft ℕ ℕ Sum.inr)
    classical
    haveI := Fintype.ofFinite ι
    convert Nat.isSemilinearSet_setOf_mulVec_eq (κ := (ι ⊕ ι) ⊕ ι) 0 i
      (Matrix.fromCols (Matrix.fromCols 1 0) 1) (Matrix.fromCols (Matrix.fromCols 0 1) 0)
      using 4 <;> simp [fromCols_mulVec]

private noncomputable def setOfFloorNeg : Set (ι → ℕ) :=
  { x | hs.fract x = hs.base ∧ ∃ i, hs.floor x i < 0 }

private theorem isSemilinearSet_setOfFloorNeg : IsSemilinearSet hs.setOfFloorNeg := by
  classical
  convert_to IsSemilinearSet (⋃ i : hs.basisSet, { x | ∃ y ∈ closure {i.1},
    ∃ z ∈ closure (hs.basisSet \ {i.1}), ∃ z' ∈ closure (hs.basisSet \ {i.1}),
      x + i.1 + y + z' = hs.base + z }) using 1
  · ext x
    simp only [setOfFloorNeg, mem_iUnion, mem_setOf_eq]
    constructor
    · intro ⟨hx, i, hi⟩
      refine ⟨i, ((- hs.floor x i).toNat - 1) • i.1, ?_,
        ∑ j ∈ Finset.univ.erase i, (hs.floor x j).toNat • j.1, ?_,
        ∑ j ∈ Finset.univ.erase i, (- hs.floor x j).toNat • j.1, ?_, ?_⟩
      · exact nsmul_mem (mem_closure_of_mem (mem_singleton i.1)) _
      · refine sum_mem fun j hj => nsmul_mem (mem_closure_of_mem ?_) _
        simpa [Subtype.val_inj] using hj
      · refine sum_mem fun j hj => nsmul_mem (mem_closure_of_mem ?_) _
        simpa [Subtype.val_inj] using hj
      · rw [add_assoc x, ← succ_nsmul',
          tsub_add_cancel_of_le
            ((Int.le_toNat (neg_pos.2 hi).le).2 (le_neg.1 (Int.cast_le_neg_one_of_neg hi))),
          add_assoc x,
          Finset.add_sum_erase _ (fun j => (-hs.floor x j).toNat • j.1) (Finset.mem_univ i),
          ← add_zero (Finset.sum (Finset.univ.erase i) _),
          ← zero_nsmul i.1, ← Int.toNat_eq_zero.2 hi.le,
          Finset.sum_erase_add _ _ (Finset.mem_univ i), ← hx]
        exact hs.add_floor_neg_toNat_sum_eq x
    · intro ⟨i, y, hy, z, hz, z', hz', heq⟩
      refine ⟨?_, i, ?_⟩
      · apply congr_arg hs.fract at heq
        rwa [hs.fract_add_of_mem_closure (closure_mono diff_subset hz'),
          hs.fract_add_of_mem_closure (closure_mono (singleton_subset_iff.2 i.2) hy),
          hs.fract_add_of_mem_closure (mem_closure_of_mem i.2),
          hs.fract_add_of_mem_closure (closure_mono diff_subset hz), hs.fract_base] at heq
      · rw [mem_closure_singleton] at hy
        rcases hy with ⟨n, rfl⟩
        apply congr_arg (hs.floor · i) at heq
        rw [hs.floor_add_of_mem_closure diff_subset (notMem_diff_of_mem (mem_singleton i.1)) hz,
          hs.floor_add_of_mem_closure diff_subset (notMem_diff_of_mem (mem_singleton i.1)) hz',
          hs.floor_base, add_assoc x, ← succ_nsmul', hs.floor_add_nsmul_self,
          ← eq_neg_iff_add_eq_zero] at heq
        simpa [heq] using neg_one_lt_zero.trans_le (Nat.cast_nonneg _)
  · refine .iUnion fun i => .proj' ?_
    rw [setOf_and]
    apply Nat.isSemilinearSet_inter <| Nat.isSemilinearSet_preimage
      (.closure_of_finite (finite_singleton _)) (LinearMap.funLeft ℕ ℕ Sum.inr)
    apply IsSemilinearSet.proj'
    rw [setOf_and]
    apply Nat.isSemilinearSet_inter <| Nat.isSemilinearSet_preimage
      (.closure_of_finite hs.finite_basisSet.diff) (LinearMap.funLeft ℕ ℕ Sum.inr)
    apply IsSemilinearSet.proj'
    rw [setOf_and]
    apply Nat.isSemilinearSet_inter <| Nat.isSemilinearSet_preimage
      (.closure_of_finite hs.finite_basisSet.diff) (LinearMap.funLeft ℕ ℕ Sum.inr)
    haveI := Fintype.ofFinite ι
    convert Nat.isSemilinearSet_setOf_mulVec_eq (κ := ((ι ⊕ ι) ⊕ ι) ⊕ ι) i.1 hs.base
      (Matrix.fromCols (Matrix.fromCols (Matrix.fromCols 1 1) 0) 1)
      (Matrix.fromCols (Matrix.fromCols (Matrix.fromCols 0 0) 1) 0) using 4
      <;> simp [add_comm _ i.1, add_assoc, fromCols_mulVec]

private noncomputable def setOfFloorPos : Set (ι → ℕ) :=
  { x | hs.fract x = hs.base ∧ ∃ i, i.1 ∉ hs.periods ∧ 0 < hs.floor x i }

private theorem isSemilinearSet_setOfFloorPos : IsSemilinearSet hs.setOfFloorPos := by
  classical
  convert_to IsSemilinearSet (⋃ i ∈ { i : hs.basisSet | i.1 ∉ hs.periods },
    { x | ∃ y ∈ closure {i.1}, ∃ z ∈ closure (hs.basisSet \ {i.1}),
      ∃ z' ∈ closure (hs.basisSet \ {i.1}), x + z' = hs.base + i.1 + y + z }) using 1
  · ext x
    simp only [setOfFloorPos, mem_iUnion, mem_setOf_eq, exists_prop]
    constructor
    · intro ⟨hx, i, hi, hi'⟩
      refine ⟨i, hi, ((hs.floor x i).toNat - 1) • i.1, ?_,
          ∑ j ∈ Finset.univ.erase i, (hs.floor x j).toNat • j.1, ?_,
          ∑ j ∈ Finset.univ.erase i, (- hs.floor x j).toNat • j.1, ?_, ?_⟩
      · exact nsmul_mem (mem_closure_of_mem (mem_singleton i.1)) _
      · refine sum_mem fun j hj => nsmul_mem (mem_closure_of_mem ?_) _
        simpa [Subtype.val_inj] using hj
      · refine sum_mem fun j hj => nsmul_mem (mem_closure_of_mem ?_) _
        simpa [Subtype.val_inj] using hj
      · rw [add_assoc hs.base, ← succ_nsmul',
          tsub_add_cancel_of_le ((Int.le_toNat hi'.le).2 (Int.add_one_le_of_lt hi')),
          add_assoc hs.base,
          Finset.add_sum_erase _ (fun j => (hs.floor x j).toNat • j.1) (Finset.mem_univ i),
          ← add_zero (Finset.sum (Finset.univ.erase i) _),
          ← zero_nsmul i.1, ← Int.toNat_eq_zero.2 (neg_neg_iff_pos.2 hi').le,
          Finset.sum_erase_add _ _ (Finset.mem_univ i), ← hx]
        exact hs.add_floor_neg_toNat_sum_eq x
    · intro ⟨i, hi, y, hy, z, hz, z', hz', heq⟩
      refine ⟨?_, i, hi, ?_⟩
      · apply congr_arg hs.fract at heq
        rwa [hs.fract_add_of_mem_closure (closure_mono diff_subset hz'),
          hs.fract_add_of_mem_closure (closure_mono diff_subset hz),
          hs.fract_add_of_mem_closure (closure_mono (singleton_subset_iff.2 i.2) hy),
          hs.fract_add_of_mem_closure (mem_closure_of_mem i.2), hs.fract_base] at heq
      · rw [mem_closure_singleton] at hy
        rcases hy with ⟨n, rfl⟩
        apply congr_arg (hs.floor · i) at heq
        rw [hs.floor_add_of_mem_closure diff_subset (notMem_diff_of_mem (mem_singleton i.1)) hz,
          hs.floor_add_of_mem_closure diff_subset (notMem_diff_of_mem (mem_singleton i.1)) hz',
          add_assoc hs.base, ← succ_nsmul', hs.floor_add_nsmul_self, hs.floor_base, zero_add] at heq
        simp [heq]
  · refine .biUnion (toFinite _) fun i hi => .proj' ?_
    rw [setOf_and]
    apply Nat.isSemilinearSet_inter <| Nat.isSemilinearSet_preimage
      (.closure_of_finite (finite_singleton _)) (LinearMap.funLeft ℕ ℕ Sum.inr)
    apply IsSemilinearSet.proj'
    rw [setOf_and]
    apply Nat.isSemilinearSet_inter <| Nat.isSemilinearSet_preimage
      (.closure_of_finite hs.finite_basisSet.diff) (LinearMap.funLeft ℕ ℕ Sum.inr)
    apply IsSemilinearSet.proj'
    rw [setOf_and]
    apply Nat.isSemilinearSet_inter <| Nat.isSemilinearSet_preimage
      (.closure_of_finite hs.finite_basisSet.diff) (LinearMap.funLeft ℕ ℕ Sum.inr)
    haveI := Fintype.ofFinite ι
    convert Nat.isSemilinearSet_setOf_mulVec_eq (κ := ((ι ⊕ ι) ⊕ ι) ⊕ ι) 0 (hs.base + i.1)
        (Matrix.fromCols (Matrix.fromCols (Matrix.fromCols 1 0) 0) 1)
        (Matrix.fromCols (Matrix.fromCols (Matrix.fromCols 0 1) 1) 0) using 4
      <;> simp [add_assoc, fromCols_mulVec]

end IsProperLinearSet

private lemma Nat.isSemilinearSet_compl_of_isProperLinearSet [Finite ι] {s : Set (ι → ℕ)}
    (hs : IsProperLinearSet s) : IsSemilinearSet sᶜ := by
  convert hs.isSemilinearSet_setOfFractNe.union <| hs.isSemilinearSet_setOfFloorNeg.union <|
    hs.isSemilinearSet_setOfFloorPos using 1
  ext
  simp only [mem_compl_iff, hs.mem_iff_fract_eq_and_floor_nonneg, IsProperLinearSet.setOfFractNe,
    IsProperLinearSet.setOfFloorNeg, IsProperLinearSet.setOfFloorPos, mem_union, mem_setOf_eq]
  grind

private theorem Nat.isSemilinearSet_compl [Finite ι] {s : Set (ι → ℕ)} (hs : IsSemilinearSet s) :
    IsSemilinearSet sᶜ := by
  rcases hs.isProperSemilinearSet with ⟨S, hS, hS', rfl⟩
  simp_rw [sUnion_eq_biUnion, compl_iUnion]
  exact .biInter hS fun s hs => isSemilinearSet_compl_of_isProperLinearSet (hS' s hs)

private theorem Nat.isSemilinearSet_diff [Finite ι] {s₁ s₂ : Set (ι → ℕ)} (hs₁ : IsSemilinearSet s₁)
    (hs₂ : IsSemilinearSet s₂) : IsSemilinearSet (s₁ \ s₂) :=
  isSemilinearSet_inter hs₁ (isSemilinearSet_compl hs₂)

/-- Semilinear sets are closed under set difference. -/
public theorem IsSemilinearSet.diff (hs₁ : IsSemilinearSet s₁) (hs₂ : IsSemilinearSet s₂) :
    IsSemilinearSet (s₁ \ s₂) := by
  rcases hs₁.exists_fg_eq_subtypeVal₂ hs₂ with ⟨P, s₁', s₂', hP, hs₁', rfl, hs₂', rfl⟩
  rw [← image_diff Subtype.val_injective]
  apply image (f := P.subtype)
  rw [← AddMonoid.fg_iff_addSubmonoid_fg, AddMonoid.fg_def, fg_iff_exists_fin_addMonoidHom] at hP
  rcases hP with ⟨n, f, hf⟩
  rw [AddMonoidHom.mrange_eq_top] at hf
  rw [← image_preimage_eq (s₁' \ s₂') hf, preimage_diff]
  apply image
  apply Nat.isSemilinearSet_diff <;> apply Nat.isSemilinearSet_preimage <;> assumption

/-- Semilinear sets in a finitely generated monoid are closed under complement. -/
public theorem IsSemilinearSet.compl [AddMonoid.FG M] (hs : IsSemilinearSet s) :
    IsSemilinearSet sᶜ := by
  rw [compl_eq_univ_diff]
  exact diff .univ hs
