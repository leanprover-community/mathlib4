/-
Copyright (c) 2023 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import Mathlib.FieldTheory.Normal
import Mathlib.Order.Closure
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
/-!
# Normal closures

## Main definitions

Given field extensions `K/F` and `L/F`, the predicate `IsNormalClosure F K L` says that the
minimal polynomial of every element of `K` over `F` splits in `L`, and that `L` is generated
by the roots of such minimal polynomials. These conditions uniquely characterize `L/F` up to
`F`-algebra isomorphisms (`IsNormalClosure.equiv`).

The explicit construction `normalClosure F K L` of a field extension `K/F` inside another
field extension `L/F` is the smallest intermediate field of `L/F` that contains the image
of every `F`-algebra embedding `K →ₐ[F] L`. It satisfies the `IsNormalClosure` predicate
if `L/F` satisfies the abovementioned splitting condition, in particular if `L/K/F` form
a tower and `L/F` is normal.
-/

open IntermediateField IsScalarTower Polynomial

variable (F K L : Type*) [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]

/-- `L/F` is a normal closure of `K/F` if the minimal polynomial of every element of `K` over `F`
  splits in `L`, and `L` is generated by roots of such minimal polynomials over `F`.
  (Since the minimal polynomial of a transcendental element is 0,
  the normal closure of `K/F` is the same as the normal closure over `F`
  of the algebraic closure of `F` in `K`.) -/
class IsNormalClosure : Prop where
  splits (x : K) : (minpoly F x).Splits (algebraMap F L)
  adjoin_rootSet : ⨆ x : K, adjoin F ((minpoly F x).rootSet L) = ⊤
/- TODO: show `IsNormalClosure F K L ↔ IsNormalClosure F (integralClosure F K) L`; we can't state
  this yet because `integralClosure F K` needs to have a `Field` instance. -/

/-- The normal closure of `K/F` in `L/F`. -/
noncomputable def normalClosure : IntermediateField F L :=
  ⨆ f : K →ₐ[F] L, f.fieldRange

lemma normalClosure_def : normalClosure F K L = ⨆ f : K →ₐ[F] L, f.fieldRange :=
  rfl

variable {F K L}

/-- A normal closure is always normal. -/
lemma IsNormalClosure.normal [h : IsNormalClosure F K L] : Normal F L :=
  Normal.of_algEquiv topEquiv (h := h.adjoin_rootSet ▸ IntermediateField.normal_iSup (h :=
    fun _ ↦ Normal.of_isSplittingField (hFEp := adjoin_rootSet_isSplittingField <| h.splits _)))

lemma normalClosure_le_iff {K' : IntermediateField F L} :
    normalClosure F K L ≤ K' ↔ ∀ f : K →ₐ[F] L, f.fieldRange ≤ K' :=
  iSup_le_iff

lemma AlgHom.fieldRange_le_normalClosure (f : K →ₐ[F] L) : f.fieldRange ≤ normalClosure F K L :=
  le_iSup AlgHom.fieldRange f

namespace Algebra.IsAlgebraic
variable [Algebra.IsAlgebraic F K]

lemma normalClosure_le_iSup_adjoin :
    normalClosure F K L ≤ ⨆ x : K, IntermediateField.adjoin F ((minpoly F x).rootSet L) :=
  iSup_le fun f _ ⟨x, hx⟩ ↦ le_iSup (α := IntermediateField F L) _ x <|
    IntermediateField.subset_adjoin F _ <| by
      rw [mem_rootSet_of_ne (minpoly.ne_zero (Algebra.IsIntegral.isIntegral x)), ← hx,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_algHom_apply, minpoly.aeval, map_zero]

variable (splits : ∀ x : K, (minpoly F x).Splits (algebraMap F L))

include splits in
lemma normalClosure_eq_iSup_adjoin_of_splits :
    normalClosure F K L = ⨆ x : K, IntermediateField.adjoin F ((minpoly F x).rootSet L) :=
  normalClosure_le_iSup_adjoin.antisymm <|
    iSup_le fun x ↦ IntermediateField.adjoin_le_iff.mpr fun _ hy ↦
      let ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval
        (fun x ↦ ⟨Algebra.IsIntegral.isIntegral x, splits x⟩) (mem_rootSet.mp hy).2
      le_iSup AlgHom.fieldRange φ ⟨x, hφ⟩

/-- If `K/F` is algebraic, the "generated by roots" condition in IsNormalClosure can be replaced
  by "generated by images of embeddings". -/
lemma isNormalClosure_iff : IsNormalClosure F K L ↔
    (∀ x : K, (minpoly F x).Splits (algebraMap F L)) ∧ normalClosure F K L = ⊤ := by
  refine ⟨fun ⟨splits, h⟩ ↦ ⟨splits, ?_⟩, fun ⟨splits, h⟩ ↦ ⟨splits, ?_⟩⟩ <;>
    simpa only [normalClosure_eq_iSup_adjoin_of_splits splits] using h
-- TODO: IntermediateField.isNormalClosure_iff similar to IntermediateField.isSplittingField_iff

include splits in
/-- `normalClosure F K L` is a valid normal closure if `K/F` is algebraic
  and all minimal polynomials of `K/F` splits in `L/F`. -/
lemma isNormalClosure_normalClosure : IsNormalClosure F K (normalClosure F K L) := by
  rw [isNormalClosure_iff]; constructor
  · rw [normalClosure_eq_iSup_adjoin_of_splits splits]
    exact fun x ↦ splits_of_splits (splits x) ((IntermediateField.subset_adjoin F _).trans <|
      SetLike.coe_subset_coe.mpr <| by apply le_iSup _ x)
  simp_rw [normalClosure, ← top_le_iff]
  refine fun x _ ↦ (IntermediateField.val _).injective.mem_set_image.mp ?_
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_val, ← IntermediateField.coe_val,
    ← IntermediateField.coe_map, IntermediateField.map_iSup]
  refine (iSup_le fun f ↦ ?_ : normalClosure F K L ≤ _) x.2
  refine le_iSup_of_le (f.codRestrict _ fun x ↦ f.fieldRange_le_normalClosure ⟨x, rfl⟩) ?_
  rw [AlgHom.map_fieldRange, val, AlgHom.val_comp_codRestrict]

end Algebra.IsAlgebraic

/-- A normal closure of `K/F` embeds into any `L/F`
  where the minimal polynomials of `K/F` splits. -/
noncomputable def IsNormalClosure.lift [h : IsNormalClosure F K L] {L'} [Field L'] [Algebra F L']
    (splits : ∀ x : K, (minpoly F x).Splits (algebraMap F L')) : L →ₐ[F] L' := by
  have := h.adjoin_rootSet; rw [← gc.l_iSup] at this
  refine Nonempty.some <| nonempty_algHom_of_adjoin_splits
    (fun x hx ↦ ⟨isAlgebraic_iff_isIntegral.mp ((h.normal).isAlgebraic x), ?_⟩) this
  obtain ⟨y, hx⟩ := Set.mem_iUnion.mp hx
  by_cases iy : IsIntegral F y
  · exact splits_of_splits_of_dvd _ (minpoly.ne_zero iy)
      (splits y) (minpoly.dvd F x (mem_rootSet.mp hx).2)
  · simp [minpoly.eq_zero iy] at hx

/-- Normal closures of `K/F` are unique up to F-algebra isomorphisms. -/
noncomputable def IsNormalClosure.equiv {L'} [Field L'] [Algebra F L']
    [h : IsNormalClosure F K L] [h' : IsNormalClosure F K L'] : L ≃ₐ[F] L' :=
  have := h.normal
  AlgEquiv.ofBijective _ <| And.left <|
    Normal.toIsAlgebraic.algHom_bijective₂
      (IsNormalClosure.lift fun _ : K ↦ h'.splits _)
      (IsNormalClosure.lift fun _ : K ↦ h.splits _)

variable (F K L)

instance isNormalClosure_normalClosure [ne : Nonempty (K →ₐ[F] L)] [h : Normal F L] :
    IsNormalClosure F K (normalClosure F K L) := by
  have ⟨φ⟩ := ne
  apply (h.toIsAlgebraic.of_injective φ φ.injective).isNormalClosure_normalClosure
  simp_rw [← minpoly.algHom_eq _ φ.injective]
  exact fun _ ↦ h.splits _

theorem normalClosure_eq_iSup_adjoin' [ne : Nonempty (K →ₐ[F] L)] [h : Normal F L] :
    normalClosure F K L = ⨆ x : K, adjoin F ((minpoly F x).rootSet L) := by
  have ⟨φ⟩ := ne
  refine h.toIsAlgebraic.of_injective φ φ.injective
    |>.normalClosure_eq_iSup_adjoin_of_splits fun x ↦ ?_
  rw [← minpoly.algHom_eq _ φ.injective]
  apply h.splits

theorem normalClosure_eq_iSup_adjoin [Algebra K L] [IsScalarTower F K L] [Normal F L] :
    normalClosure F K L = ⨆ x : K, adjoin F ((minpoly F x).rootSet L) :=
  normalClosure_eq_iSup_adjoin' (ne := ⟨IsScalarTower.toAlgHom F K L⟩)

namespace normalClosure

/-- All `F`-`AlgHom`s from `K` to `L` factor through the normal closure of `K/F` in `L/F`. -/
noncomputable def algHomEquiv : (K →ₐ[F] normalClosure F K L) ≃ (K →ₐ[F] L) where
  toFun := (normalClosure F K L).val.comp
  invFun f := f.codRestrict _ fun x ↦ f.fieldRange_le_normalClosure ⟨x, rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance normal [h : Normal F L] : Normal F (normalClosure F K L) := by
  obtain _ | φ := isEmpty_or_nonempty (K →ₐ[F] L)
  · rw [normalClosure, iSup_of_empty]; exact Normal.of_algEquiv (botEquiv F L).symm
  · exact (isNormalClosure_normalClosure F K L).normal

instance is_finiteDimensional [FiniteDimensional F K] :
    FiniteDimensional F (normalClosure F K L) := by
  haveI : ∀ f : K →ₐ[F] L, FiniteDimensional F f.fieldRange := fun f ↦
    f.toLinearMap.finiteDimensional_range
  apply IntermediateField.finiteDimensional_iSup_of_finite

variable [Algebra K L] [IsScalarTower F K L]

noncomputable instance algebra :
    Algebra K (normalClosure F K L) :=
  IntermediateField.algebra'
    { ⨆ f : K →ₐ[F] L, f.fieldRange with
      algebraMap_mem' := fun r ↦ (toAlgHom F K L).fieldRange_le_normalClosure ⟨r, rfl⟩ }

instance : IsScalarTower F K (normalClosure F K L) := by
  apply of_algebraMap_eq'
  ext x
  exact algebraMap_apply F K L x

instance : IsScalarTower K (normalClosure F K L) L :=
  of_algebraMap_eq' rfl

lemma restrictScalars_eq :
    (toAlgHom K (normalClosure F K L) L).fieldRange.restrictScalars F = normalClosure F K L :=
  SetLike.ext' Subtype.range_val

end normalClosure

variable {F K L}

open Cardinal in
/-- An extension `L/F` in which every minimal polynomial of `K/F` splits is maximal with respect
  to `F`-embeddings of `K`, in the sense that `K →ₐ[F] L` achieves maximal cardinality.
  We construct an explicit injective function from an arbitrary `K →ₐ[F] L'` into `K →ₐ[F] L`,
  using an embedding of `normalClosure F K L'` into `L`. -/
noncomputable def Algebra.IsAlgebraic.algHomEmbeddingOfSplits [Algebra.IsAlgebraic F K]
    (h : ∀ x : K, (minpoly F x).Splits (algebraMap F L)) (L' : Type*) [Field L'] [Algebra F L'] :
    (K →ₐ[F] L') ↪ (K →ₐ[F] L) :=
  let φ : ↑(⨆ x : K, IntermediateField.adjoin F ((minpoly F x).rootSet L')) →ₐ[F] L :=
    Nonempty.some <| by
      rw [← gc.l_iSup]
      refine nonempty_algHom_adjoin_of_splits fun x hx ↦ ?_
      obtain ⟨y, hx⟩ := Set.mem_iUnion.mp hx
      refine ⟨isAlgebraic_iff_isIntegral.mp (isAlgebraic_of_mem_rootSet hx), ?_⟩
      by_cases iy : IsIntegral F y
      · exact splits_of_splits_of_dvd _ (minpoly.ne_zero iy)
          (h y) (minpoly.dvd F x (mem_rootSet.mp hx).2)
      · simp [minpoly.eq_zero iy] at hx
  let φ' := (φ.comp <| inclusion normalClosure_le_iSup_adjoin)
  { toFun := φ'.comp ∘ (normalClosure.algHomEquiv F K L').symm
    inj' := fun _ _ h ↦ (normalClosure.algHomEquiv F K L').symm.injective <| by
      rw [DFunLike.ext'_iff] at h ⊢
      exact φ'.injective.comp_left h }

namespace IntermediateField

variable (K K' : IntermediateField F L)

lemma le_normalClosure : K ≤ normalClosure F K L :=
  K.fieldRange_val.symm.trans_le K.val.fieldRange_le_normalClosure

lemma normalClosure_of_normal [Normal F K] : normalClosure F K L = K := by
  simp only [normalClosure_def, AlgHom.fieldRange_of_normal, iSup_const]

variable [Normal F L]

lemma normalClosure_def' : normalClosure F K L = ⨆ f : L →ₐ[F] L, K.map f := by
  refine (normalClosure_def F K L).trans (le_antisymm (iSup_le (fun f ↦ ?_)) (iSup_le (fun f ↦ ?_)))
  · exact le_iSup_of_le (f.liftNormal L) (fun b ⟨a, h⟩ ↦ ⟨a, a.2, h ▸ f.liftNormal_commutes L a⟩)
  · exact le_iSup_of_le (f.comp K.val) (fun b ⟨a, h⟩ ↦ ⟨⟨a, h.1⟩, h.2⟩)

lemma normalClosure_def'' : normalClosure F K L = ⨆ f : L ≃ₐ[F] L, K.map f := by
  refine (normalClosure_def' K).trans (le_antisymm (iSup_le (fun f ↦ ?_)) (iSup_le (fun f ↦ ?_)))
  · exact le_iSup_of_le (f.restrictNormal' L)
      (fun b ⟨a, h⟩ ↦ ⟨a, h.1, h.2 ▸ f.restrictNormal_commutes L a⟩)
  · exact le_iSup_of_le f le_rfl

lemma normalClosure_mono (h : K ≤ K') : normalClosure F K L ≤ normalClosure F K' L := by
  rw [normalClosure_def', normalClosure_def']
  exact iSup_mono (fun f ↦ map_mono f h)

variable (F L)

/-- `normalClosure` as a `ClosureOperator`. -/
@[simps]
noncomputable def closureOperator : ClosureOperator (IntermediateField F L) where
  toFun := fun K ↦ normalClosure F K L
  monotone' := fun K K' ↦ normalClosure_mono K K'
  le_closure' := le_normalClosure
  idempotent' := fun K ↦ normalClosure_of_normal (normalClosure F K L)

variable {K : IntermediateField F L} {F L}

lemma normal_iff_normalClosure_eq : Normal F K ↔ normalClosure F K L = K :=
⟨@normalClosure_of_normal (K := K), fun h ↦ h ▸ normalClosure.normal F K L⟩

lemma normal_iff_normalClosure_le : Normal F K ↔ normalClosure F K L ≤ K :=
normal_iff_normalClosure_eq.trans (le_normalClosure K).le_iff_eq.symm

lemma normal_iff_forall_fieldRange_le : Normal F K ↔ ∀ σ : K →ₐ[F] L, σ.fieldRange ≤ K := by
  rw [normal_iff_normalClosure_le, normalClosure_def, iSup_le_iff]

lemma normal_iff_forall_map_le : Normal F K ↔ ∀ σ : L →ₐ[F] L, K.map σ ≤ K := by
  rw [normal_iff_normalClosure_le, normalClosure_def', iSup_le_iff]

lemma normal_iff_forall_map_le' : Normal F K ↔ ∀ σ : L ≃ₐ[F] L, K.map ↑σ ≤ K := by
  rw [normal_iff_normalClosure_le, normalClosure_def'', iSup_le_iff]

lemma normal_iff_forall_fieldRange_eq : Normal F K ↔ ∀ σ : K →ₐ[F] L, σ.fieldRange = K :=
⟨@AlgHom.fieldRange_of_normal (E := K), normal_iff_forall_fieldRange_le.2 ∘ fun h σ ↦ (h σ).le⟩

lemma normal_iff_forall_map_eq : Normal F K ↔ ∀ σ : L →ₐ[F] L, K.map σ = K :=
⟨fun h σ ↦ (K.fieldRange_val ▸ AlgHom.map_fieldRange K.val σ).trans
  (normal_iff_forall_fieldRange_eq.1 h _), fun h ↦ normal_iff_forall_map_le.2 (fun σ ↦ (h σ).le)⟩

lemma normal_iff_forall_map_eq' : Normal F K ↔ ∀ σ : L ≃ₐ[F] L, K.map ↑σ = K :=
⟨fun h σ ↦ normal_iff_forall_map_eq.1 h σ, fun h ↦ normal_iff_forall_map_le'.2 (fun σ ↦ (h σ).le)⟩

end IntermediateField
