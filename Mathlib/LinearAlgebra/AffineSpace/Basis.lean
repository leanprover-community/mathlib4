/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.AffineSpace.Centroid
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.AffineSpace.Pointwise
import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Affine bases and barycentric coordinates

Suppose `P` is an affine space modelled on the module `V` over the ring `k`, and `p : ι → P` is an
affine-independent family of points spanning `P`. Given this data, each point `q : P` may be written
uniquely as an affine combination: `q = w₀ p₀ + w₁ p₁ + ⋯` for some (finitely-supported) weights
`wᵢ`. For each `i : ι`, we thus have an affine map `P →ᵃ[k] k`, namely `q ↦ wᵢ`. This family of
maps is known as the family of barycentric coordinates. It is defined in this file.

## The construction

Fixing `i : ι`, and allowing `j : ι` to range over the values `j ≠ i`, we obtain a basis `bᵢ` of `V`
defined by `bᵢ j = p j -ᵥ p i`. Let `fᵢ j : V →ₗ[k] k` be the corresponding dual basis and let
`fᵢ = ∑ j, fᵢ j : V →ₗ[k] k` be the corresponding "sum of all coordinates" form. Then the `i`th
barycentric coordinate of `q : P` is `1 - fᵢ (q -ᵥ p i)`.

## Main definitions

* `AffineBasis`: a structure representing an affine basis of an affine space.
* `AffineBasis.coord`: the map `P →ᵃ[k] k` corresponding to `i : ι`.
* `AffineBasis.coord_apply_eq`: the behaviour of `AffineBasis.coord i` on `p i`.
* `AffineBasis.coord_apply_ne`: the behaviour of `AffineBasis.coord i` on `p j` when `j ≠ i`.
* `AffineBasis.coord_apply`: the behaviour of `AffineBasis.coord i` on `p j` for general `j`.
* `AffineBasis.coord_apply_combination`: the characterisation of `AffineBasis.coord i` in terms
  of affine combinations, i.e., `AffineBasis.coord i (w₀ p₀ + w₁ p₁ + ⋯) = wᵢ`.

## TODO

* Construct the affine equivalence between `P` and `{ f : ι →₀ k | f.sum = 1 }`.

-/

open Affine Module Set
open scoped Pointwise

universe u₁ u₂ u₃ u₄

/-- An affine basis is a family of affine-independent points whose span is the top subspace. -/
structure AffineBasis (ι : Type u₁) (k : Type u₂) {V : Type u₃} (P : Type u₄) [AddCommGroup V]
  [AffineSpace V P] [Ring k] [Module k V] where
  protected toFun : ι → P
  protected ind' : AffineIndependent k toFun
  protected tot' : affineSpan k (range toFun) = ⊤

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AffineSpace V P]

namespace AffineBasis

section Ring

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

/-- The unique point in a single-point space is the simplest example of an affine basis. -/
instance : Inhabited (AffineBasis PUnit k PUnit) :=
  ⟨⟨id, affineIndependent_of_subsingleton k id, by simp⟩⟩

instance instFunLike : FunLike (AffineBasis ι k P) ι P where
  coe := AffineBasis.toFun
  coe_injective' f g h := by cases f; cases g; congr

@[ext]
theorem ext {b₁ b₂ : AffineBasis ι k P} (h : (b₁ : ι → P) = b₂) : b₁ = b₂ :=
  DFunLike.coe_injective h

theorem ind : AffineIndependent k b :=
  b.ind'

theorem tot : affineSpan k (range b) = ⊤ :=
  b.tot'

include b in
protected theorem nonempty : Nonempty ι :=
  not_isEmpty_iff.mp fun hι => by
    simpa only [@range_eq_empty _ _ hι, AffineSubspace.span_empty, bot_ne_top] using b.tot

/-- Composition of an affine basis and an equivalence of index types. -/
def reindex (e : ι ≃ ι') : AffineBasis ι' k P :=
  ⟨b ∘ e.symm, b.ind.comp_embedding e.symm.toEmbedding, by
    rw [e.symm.surjective.range_comp]
    exact b.3⟩

@[simp, norm_cast]
theorem coe_reindex : ⇑(b.reindex e) = b ∘ e.symm :=
  rfl

@[simp]
theorem reindex_apply (i' : ι') : b.reindex e i' = b (e.symm i') :=
  rfl

@[simp]
theorem reindex_refl : b.reindex (Equiv.refl _) = b :=
  ext rfl

/-- Given an affine basis for an affine space `P`, if we single out one member of the family, we
obtain a linear basis for the model space `V`.

The linear basis corresponding to the singled-out member `i : ι` is indexed by `{j : ι // j ≠ i}`
and its `j`th element is `b j -ᵥ b i`. (See `basisOf_apply`.) -/
noncomputable def basisOf (i : ι) : Basis { j : ι // j ≠ i } k V :=
  Basis.mk ((affineIndependent_iff_linearIndependent_vsub k b i).mp b.ind)
    (by
      suffices
        Submodule.span k (range fun j : { x // x ≠ i } => b ↑j -ᵥ b i) = vectorSpan k (range b) by
        rw [this, ← direction_affineSpan, b.tot, AffineSubspace.direction_top]
      conv_rhs => rw [← image_univ]
      rw [vectorSpan_image_eq_span_vsub_set_right_ne k b (mem_univ i)]
      congr
      ext v
      simp)

@[simp]
theorem basisOf_apply (i : ι) (j : { j : ι // j ≠ i }) : b.basisOf i j = b ↑j -ᵥ b i := by
  simp [basisOf]

@[simp]
theorem basisOf_reindex (i : ι') :
    (b.reindex e).basisOf i =
      (b.basisOf <| e.symm i).reindex (e.subtypeEquiv fun _ => e.eq_symm_apply.not) := by
  ext j
  simp

/-- The `i`th barycentric coordinate of a point. -/
noncomputable def coord (i : ι) : P →ᵃ[k] k where
  toFun q := 1 - (b.basisOf i).sumCoords (q -ᵥ b i)
  linear := -(b.basisOf i).sumCoords
  map_vadd' q v := by
    rw [vadd_vsub_assoc, LinearMap.map_add, vadd_eq_add, LinearMap.neg_apply,
      sub_add_eq_sub_sub_swap, add_comm, sub_eq_add_neg]

@[simp]
theorem linear_eq_sumCoords (i : ι) : (b.coord i).linear = -(b.basisOf i).sumCoords :=
  rfl

@[simp]
theorem coord_reindex (i : ι') : (b.reindex e).coord i = b.coord (e.symm i) := by
  ext
  classical simp [AffineBasis.coord]

@[simp]
theorem coord_apply_eq (i : ι) : b.coord i (b i) = 1 := by
  simp only [coord, Basis.coe_sumCoords, LinearEquiv.map_zero, sub_zero,
    AffineMap.coe_mk, Finsupp.sum_zero_index, vsub_self]

@[simp]
theorem coord_apply_ne (h : i ≠ j) : b.coord i (b j) = 0 := by
  rw [coord, AffineMap.coe_mk, ← Subtype.coe_mk (p := (· ≠ i)) j h.symm, ← b.basisOf_apply,
    Basis.sumCoords_self_apply, sub_self]

theorem coord_apply [DecidableEq ι] (i j : ι) : b.coord i (b j) = if i = j then 1 else 0 := by
  rcases eq_or_ne i j with h | h <;> simp [h]

@[simp]
theorem coord_apply_combination_of_mem (hi : i ∈ s) {w : ι → k} (hw : s.sum w = 1) :
    b.coord i (s.affineCombination k b w) = w i := by
  classical simp only [coord_apply, hi, Finset.affineCombination_eq_linear_combination, if_true,
      mul_boole, hw, Function.comp_apply, smul_eq_mul, s.sum_ite_eq,
      s.map_affineCombination b w hw]

@[simp]
theorem coord_apply_combination_of_notMem (hi : i ∉ s) {w : ι → k} (hw : s.sum w = 1) :
    b.coord i (s.affineCombination k b w) = 0 := by
  classical simp only [coord_apply, hi, Finset.affineCombination_eq_linear_combination, if_false,
      mul_boole, hw, Function.comp_apply, smul_eq_mul, s.sum_ite_eq,
      s.map_affineCombination b w hw]

@[deprecated (since := "2025-05-23")]
alias coord_apply_combination_of_not_mem := coord_apply_combination_of_notMem

@[simp]
theorem sum_coord_apply_eq_one [Fintype ι] (q : P) : ∑ i, b.coord i q = 1 := by
  have hq : q ∈ affineSpan k (range b) := by
    rw [b.tot]
    exact AffineSubspace.mem_top k V q
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hq
  convert hw
  exact b.coord_apply_combination_of_mem (Finset.mem_univ _) hw

@[simp]
theorem affineCombination_coord_eq_self [Fintype ι] (q : P) :
    (Finset.univ.affineCombination k b fun i => b.coord i q) = q := by
  have hq : q ∈ affineSpan k (range b) := by
    rw [b.tot]
    exact AffineSubspace.mem_top k V q
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hq
  congr
  ext i
  exact b.coord_apply_combination_of_mem (Finset.mem_univ i) hw

/-- A variant of `AffineBasis.affineCombination_coord_eq_self` for the special case when the
affine space is a module so we can talk about linear combinations. -/
@[simp]
theorem linear_combination_coord_eq_self [Fintype ι] (b : AffineBasis ι k V) (v : V) :
    ∑ i, b.coord i v • b i = v := by
  have hb := b.affineCombination_coord_eq_self v
  rwa [Finset.univ.affineCombination_eq_linear_combination _ _ (b.sum_coord_apply_eq_one v)] at hb

theorem ext_elem [Finite ι] {q₁ q₂ : P} (h : ∀ i, b.coord i q₁ = b.coord i q₂) : q₁ = q₂ := by
  cases nonempty_fintype ι
  rw [← b.affineCombination_coord_eq_self q₁, ← b.affineCombination_coord_eq_self q₂]
  simp only [h]

@[simp]
theorem coe_coord_of_subsingleton_eq_one [Subsingleton ι] (i : ι) : (b.coord i : P → k) = 1 := by
  ext q
  have hp : (range b).Subsingleton := by
    rw [← image_univ]
    apply Subsingleton.image
    apply subsingleton_of_subsingleton
  haveI := AffineSubspace.subsingleton_of_subsingleton_span_eq_top hp b.tot
  let s : Finset ι := {i}
  have hi : i ∈ s := by simp [s]
  have hw : s.sum (Function.const ι (1 : k)) = 1 := by simp [s]
  have hq : q = s.affineCombination k b (Function.const ι (1 : k)) := by
    simp [eq_iff_true_of_subsingleton]
  rw [Pi.one_apply, hq, b.coord_apply_combination_of_mem hi hw, Function.const_apply]

theorem surjective_coord [Nontrivial ι] (i : ι) : Function.Surjective <| b.coord i := by
  classical
    intro x
    obtain ⟨j, hij⟩ := exists_ne i
    let s : Finset ι := {i, j}
    have hi : i ∈ s := by simp [s]
    let w : ι → k := fun j' => if j' = i then x else 1 - x
    have hw : s.sum w = 1 := by simp [s, w, Finset.sum_ite, Finset.filter_insert, hij,
      Finset.filter_true_of_mem, Finset.filter_false_of_mem]
    use s.affineCombination k b w
    simp [w, b.coord_apply_combination_of_mem hi hw]

/-- Barycentric coordinates as an affine map. -/
noncomputable def coords : P →ᵃ[k] ι → k where
  toFun q i := b.coord i q
  linear :=
    { toFun := fun v i => -(b.basisOf i).sumCoords v
      map_add' := fun v w => by ext; simp only [LinearMap.map_add, Pi.add_apply, neg_add]
      map_smul' := fun t v => by ext; simp }
  map_vadd' p v := by ext; simp

@[simp]
theorem coords_apply (q : P) (i : ι) : b.coords q i = b.coord i q :=
  rfl

instance instVAdd : VAdd V (AffineBasis ι k P) where
  vadd x b :=
    { toFun := x +ᵥ ⇑b,
      ind' := b.ind'.vadd,
      tot' := by rw [Pi.vadd_def, ← vadd_set_range, ← AffineSubspace.pointwise_vadd_span, b.tot,
        AffineSubspace.pointwise_vadd_top] }

@[simp, norm_cast] lemma coe_vadd (v : V) (b : AffineBasis ι k P) : ⇑(v +ᵥ b) = v +ᵥ ⇑b := rfl

@[simp] lemma basisOf_vadd (v : V) (b : AffineBasis ι k P) : (v +ᵥ b).basisOf = b.basisOf := by
  ext
  simp

instance instAddAction : AddAction V (AffineBasis ι k P) :=
  DFunLike.coe_injective.addAction _ coe_vadd

@[simp] lemma coord_vadd (v : V) (b : AffineBasis ι k P) :
    (v +ᵥ b).coord i = (b.coord i).comp (AffineEquiv.constVAdd k P v).symm := by
  ext p
  simp only [coord, ne_eq, basisOf_vadd, coe_vadd, Pi.vadd_apply, Basis.coe_sumCoords,
    AffineMap.coe_mk, AffineEquiv.constVAdd_symm, AffineMap.coe_comp, AffineEquiv.coe_toAffineMap,
    Function.comp_apply, AffineEquiv.constVAdd_apply, sub_right_inj]
  congr! 1
  rw [vadd_vsub_assoc, neg_add_eq_sub, vsub_vadd_eq_vsub_sub]

section SMul
variable [Group G] [Group G']
variable [DistribMulAction G V] [DistribMulAction G' V]
variable [SMulCommClass G k V] [SMulCommClass G' k V]

/-- In an affine space that is also a vector space, an `AffineBasis` can be scaled.

TODO: generalize to include `SMul (P ≃ᵃ[k] P) (AffineBasis ι k P)`, which acts on `P` with a `VAdd`
version of a `DistribMulAction`. -/
instance instSMul : SMul G (AffineBasis ι k V) where
  smul a b :=
    { toFun := a • ⇑b,
      ind' := b.ind'.smul,
      tot' := by
        rw [Pi.smul_def, ← smul_set_range, ← AffineSubspace.smul_span, b.tot,
          AffineSubspace.smul_top (Group.isUnit a)] }

@[simp, norm_cast] lemma coe_smul (a : G) (b : AffineBasis ι k V) : ⇑(a • b) = a • ⇑b := rfl

/-- TODO: generalize to include `SMul (P ≃ᵃ[k] P) (AffineBasis ι k P)`, which acts on `P` with a
`VAdd` version of a `DistribMulAction`. -/
instance [SMulCommClass G G' V] : SMulCommClass G G' (AffineBasis ι k V) where
  smul_comm _g _g' _b := DFunLike.ext _ _ fun _ => smul_comm _ _ _

/-- TODO: generalize to include `SMul (P ≃ᵃ[k] P) (AffineBasis ι k P)`, which acts on `P` with a
`VAdd` version of a `DistribMulAction`. -/
instance [SMul G G'] [IsScalarTower G G' V] : IsScalarTower G G' (AffineBasis ι k V) where
  smul_assoc _g _g' _b := DFunLike.ext _ _ fun _ => smul_assoc _ _ _

@[simp] lemma basisOf_smul (a : G) (b : AffineBasis ι k V) (i : ι) :
    (a • b).basisOf i = a • b.basisOf i := by ext j; simp [smul_sub]

@[simp] lemma reindex_smul (a : G) (b : AffineBasis ι k V) (e : ι ≃ ι') :
    (a • b).reindex e = a • b.reindex e :=
  rfl

@[simp] lemma coord_smul (a : G) (b : AffineBasis ι k V) (i : ι) :
    (a • b).coord i = (b.coord i).comp (DistribMulAction.toLinearEquiv _ _ a).symm.toAffineMap := by
  ext v; simp [map_sub, coord]

/-- TODO: generalize to include `SMul (P ≃ᵃ[k] P) (AffineBasis ι k P)`, which acts on `P` with a
`VAdd` version of a `DistribMulAction`. -/
instance instMulAction : MulAction G (AffineBasis ι k V) :=
  DFunLike.coe_injective.mulAction _ coe_smul

end SMul
end Ring

section DivisionRing

variable [DivisionRing k] [Module k V]

@[simp]
theorem coord_apply_centroid [CharZero k] (b : AffineBasis ι k P) {s : Finset ι} {i : ι}
    (hi : i ∈ s) : b.coord i (s.centroid k b) = (s.card : k)⁻¹ := by
  rw [Finset.centroid,
    b.coord_apply_combination_of_mem hi (s.sum_centroidWeights_eq_one_of_nonempty _ ⟨i, hi⟩),
    Finset.centroidWeights, Function.const_apply]

theorem exists_affine_subbasis {t : Set P} (ht : affineSpan k t = ⊤) :
    ∃ s ⊆ t, ∃ b : AffineBasis s k P, ⇑b = ((↑) : s → P) := by
  obtain ⟨s, hst, h_tot, h_ind⟩ := exists_affineIndependent k V t
  refine ⟨s, hst, ⟨(↑), h_ind, ?_⟩, rfl⟩
  rw [Subtype.range_coe, h_tot, ht]

variable (k V P)

theorem exists_affineBasis : ∃ (s : Set P) (b : AffineBasis (↥s) k P), ⇑b = ((↑) : s → P) :=
  let ⟨s, _, hs⟩ := exists_affine_subbasis (AffineSubspace.span_univ k V P)
  ⟨s, hs⟩

end DivisionRing

end AffineBasis
