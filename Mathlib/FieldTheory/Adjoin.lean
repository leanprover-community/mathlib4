/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
import Mathlib.FieldTheory.IntermediateField
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.RingTheory.TensorProduct

#align_import field_theory.adjoin from "leanprover-community/mathlib"@"df76f43357840485b9d04ed5dee5ab115d420e87"

/-!
# Adjoining Elements to Fields

In this file we introduce the notion of adjoining elements to fields.
This isn't quite the same as adjoining elements to rings.
For example, `Algebra.adjoin K {x}` might not include `x⁻¹`.

## Main results

- `adjoin_adjoin_left`: adjoining S and then T is the same as adjoining `S ∪ T`.
- `bot_eq_top_of_rank_adjoin_eq_one`: if `F⟮x⟯` has dimension `1` over `F` for every `x`
  in `E` then `F = E`

## Notation

 - `F⟮α⟯`: adjoin a single element `α` to `F` (in scope `IntermediateField`).
-/

set_option autoImplicit true


open FiniteDimensional Polynomial

open scoped Classical Polynomial

namespace IntermediateField

section AdjoinDef

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] (S : Set E)

--Porting note: not adding `neg_mem'` causes an error.
/-- `adjoin F S` extends a field `F` by adjoining a set `S ⊆ E`. -/
def adjoin : IntermediateField F E :=
  { Subfield.closure (Set.range (algebraMap F E) ∪ S) with
    algebraMap_mem' := fun x => Subfield.subset_closure (Or.inl (Set.mem_range_self x)) }
#align intermediate_field.adjoin IntermediateField.adjoin

variable {S}

theorem mem_adjoin_iff (x : E) :
    x ∈ adjoin F S ↔ ∃ r s : MvPolynomial S F,
      x = MvPolynomial.aeval Subtype.val r / MvPolynomial.aeval Subtype.val s := by
  simp only [adjoin, mem_mk, Subring.mem_toSubsemiring, Subfield.mem_toSubring,
    Subfield.mem_closure_iff, ← Algebra.adjoin_eq_ring_closure, Subalgebra.mem_toSubring,
    Algebra.adjoin_eq_range, AlgHom.mem_range, exists_exists_eq_and]
  tauto

theorem mem_adjoin_simple_iff {α : E} (x : E) :
    x ∈ adjoin F {α} ↔ ∃ r s : F[X], x = aeval α r / aeval α s := by
  simp only [adjoin, mem_mk, Subring.mem_toSubsemiring, Subfield.mem_toSubring,
    Subfield.mem_closure_iff, ← Algebra.adjoin_eq_ring_closure, Subalgebra.mem_toSubring,
    Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range, exists_exists_eq_and]
  tauto

end AdjoinDef

section Lattice

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

@[simp]
theorem adjoin_le_iff {S : Set E} {T : IntermediateField F E} : adjoin F S ≤ T ↔ S ≤ T :=
  ⟨fun H => le_trans (le_trans (Set.subset_union_right _ _) Subfield.subset_closure) H, fun H =>
    (@Subfield.closure_le E _ (Set.range (algebraMap F E) ∪ S) T.toSubfield).mpr
      (Set.union_subset (IntermediateField.set_range_subset T) H)⟩
#align intermediate_field.adjoin_le_iff IntermediateField.adjoin_le_iff

theorem gc : GaloisConnection (adjoin F : Set E → IntermediateField F E)
    (fun (x : IntermediateField F E) => (x : Set E)) := fun _ _ =>
  adjoin_le_iff
#align intermediate_field.gc IntermediateField.gc

/-- Galois insertion between `adjoin` and `coe`. -/
def gi : GaloisInsertion (adjoin F : Set E → IntermediateField F E)
    (fun (x : IntermediateField F E) => (x : Set E)) where
  choice s hs := (adjoin F s).copy s <| le_antisymm (gc.le_u_l s) hs
  gc := IntermediateField.gc
  le_l_u S := (IntermediateField.gc (S : Set E) (adjoin F S)).1 <| le_rfl
  choice_eq _ _ := copy_eq _ _ _
#align intermediate_field.gi IntermediateField.gi

instance : CompleteLattice (IntermediateField F E) where
  __ := GaloisInsertion.liftCompleteLattice IntermediateField.gi
  bot :=
    { toSubalgebra := ⊥
      inv_mem' := by rintro x ⟨r, rfl⟩; exact ⟨r⁻¹, map_inv₀ _ _⟩ }
  bot_le x := (bot_le : ⊥ ≤ x.toSubalgebra)

instance : Inhabited (IntermediateField F E) :=
  ⟨⊤⟩

theorem coe_bot : ↑(⊥ : IntermediateField F E) = Set.range (algebraMap F E) := rfl
#align intermediate_field.coe_bot IntermediateField.coe_bot

theorem mem_bot {x : E} : x ∈ (⊥ : IntermediateField F E) ↔ x ∈ Set.range (algebraMap F E) :=
  Iff.rfl
#align intermediate_field.mem_bot IntermediateField.mem_bot

@[simp]
theorem bot_toSubalgebra : (⊥ : IntermediateField F E).toSubalgebra = ⊥ := rfl
#align intermediate_field.bot_to_subalgebra IntermediateField.bot_toSubalgebra

@[simp]
theorem coe_top : ↑(⊤ : IntermediateField F E) = (Set.univ : Set E) :=
  rfl
#align intermediate_field.coe_top IntermediateField.coe_top

@[simp]
theorem mem_top {x : E} : x ∈ (⊤ : IntermediateField F E) :=
  trivial
#align intermediate_field.mem_top IntermediateField.mem_top

@[simp]
theorem top_toSubalgebra : (⊤ : IntermediateField F E).toSubalgebra = ⊤ :=
  rfl
#align intermediate_field.top_to_subalgebra IntermediateField.top_toSubalgebra

@[simp]
theorem top_toSubfield : (⊤ : IntermediateField F E).toSubfield = ⊤ :=
  rfl
#align intermediate_field.top_to_subfield IntermediateField.top_toSubfield

@[simp, norm_cast]
theorem coe_inf (S T : IntermediateField F E) : (↑(S ⊓ T) : Set E) = (S : Set E) ∩ T :=
  rfl
#align intermediate_field.coe_inf IntermediateField.coe_inf

@[simp]
theorem mem_inf {S T : IntermediateField F E} {x : E} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T :=
  Iff.rfl
#align intermediate_field.mem_inf IntermediateField.mem_inf

@[simp]
theorem inf_toSubalgebra (S T : IntermediateField F E) :
    (S ⊓ T).toSubalgebra = S.toSubalgebra ⊓ T.toSubalgebra :=
  rfl
#align intermediate_field.inf_to_subalgebra IntermediateField.inf_toSubalgebra

@[simp]
theorem inf_toSubfield (S T : IntermediateField F E) :
    (S ⊓ T).toSubfield = S.toSubfield ⊓ T.toSubfield :=
  rfl
#align intermediate_field.inf_to_subfield IntermediateField.inf_toSubfield

@[simp, norm_cast]
theorem coe_sInf (S : Set (IntermediateField F E)) : (↑(sInf S) : Set E) =
    sInf ((fun (x : IntermediateField F E) => (x : Set E)) '' S) :=
  rfl
#align intermediate_field.coe_Inf IntermediateField.coe_sInf

@[simp]
theorem sInf_toSubalgebra (S : Set (IntermediateField F E)) :
    (sInf S).toSubalgebra = sInf (toSubalgebra '' S) :=
  SetLike.coe_injective <| by simp [Set.sUnion_image]
#align intermediate_field.Inf_to_subalgebra IntermediateField.sInf_toSubalgebra

@[simp]
theorem sInf_toSubfield (S : Set (IntermediateField F E)) :
    (sInf S).toSubfield = sInf (toSubfield '' S) :=
  SetLike.coe_injective <| by simp [Set.sUnion_image]
#align intermediate_field.Inf_to_subfield IntermediateField.sInf_toSubfield

@[simp, norm_cast]
theorem coe_iInf {ι : Sort*} (S : ι → IntermediateField F E) : (↑(iInf S) : Set E) = ⋂ i, S i := by
  simp [iInf]
#align intermediate_field.coe_infi IntermediateField.coe_iInf

@[simp]
theorem iInf_toSubalgebra {ι : Sort*} (S : ι → IntermediateField F E) :
    (iInf S).toSubalgebra = ⨅ i, (S i).toSubalgebra :=
  SetLike.coe_injective <| by simp [iInf]
#align intermediate_field.infi_to_subalgebra IntermediateField.iInf_toSubalgebra

@[simp]
theorem iInf_toSubfield {ι : Sort*} (S : ι → IntermediateField F E) :
    (iInf S).toSubfield = ⨅ i, (S i).toSubfield :=
  SetLike.coe_injective <| by simp [iInf]
#align intermediate_field.infi_to_subfield IntermediateField.iInf_toSubfield

/-- Construct an algebra isomorphism from an equality of intermediate fields -/
@[simps! apply]
def equivOfEq {S T : IntermediateField F E} (h : S = T) : S ≃ₐ[F] T :=
  Subalgebra.equivOfEq _ _ (congr_arg toSubalgebra h)
#align intermediate_field.equiv_of_eq IntermediateField.equivOfEq

@[simp]
theorem equivOfEq_symm {S T : IntermediateField F E} (h : S = T) :
    (equivOfEq h).symm = equivOfEq h.symm :=
  rfl
#align intermediate_field.equiv_of_eq_symm IntermediateField.equivOfEq_symm

@[simp]
theorem equivOfEq_rfl (S : IntermediateField F E) : equivOfEq (rfl : S = S) = AlgEquiv.refl := by
  ext; rfl
#align intermediate_field.equiv_of_eq_rfl IntermediateField.equivOfEq_rfl

@[simp]
theorem equivOfEq_trans {S T U : IntermediateField F E} (hST : S = T) (hTU : T = U) :
    (equivOfEq hST).trans (equivOfEq hTU) = equivOfEq (_root_.trans hST hTU) :=
  rfl
#align intermediate_field.equiv_of_eq_trans IntermediateField.equivOfEq_trans

variable (F E)

/-- The bottom intermediate_field is isomorphic to the field. -/
noncomputable def botEquiv : (⊥ : IntermediateField F E) ≃ₐ[F] F :=
  (Subalgebra.equivOfEq _ _ bot_toSubalgebra).trans (Algebra.botEquiv F E)
#align intermediate_field.bot_equiv IntermediateField.botEquiv

variable {F E}

-- Porting note: this was tagged `simp`.
theorem botEquiv_def (x : F) : botEquiv F E (algebraMap F (⊥ : IntermediateField F E) x) = x :=
  by simp
#align intermediate_field.bot_equiv_def IntermediateField.botEquiv_def

@[simp]
theorem botEquiv_symm (x : F) : (botEquiv F E).symm x = algebraMap F _ x :=
  rfl
#align intermediate_field.bot_equiv_symm IntermediateField.botEquiv_symm

noncomputable instance algebraOverBot : Algebra (⊥ : IntermediateField F E) F :=
  (IntermediateField.botEquiv F E).toAlgHom.toRingHom.toAlgebra
#align intermediate_field.algebra_over_bot IntermediateField.algebraOverBot

theorem coe_algebraMap_over_bot :
    (algebraMap (⊥ : IntermediateField F E) F : (⊥ : IntermediateField F E) → F) =
      IntermediateField.botEquiv F E :=
  rfl
#align intermediate_field.coe_algebra_map_over_bot IntermediateField.coe_algebraMap_over_bot

instance isScalarTower_over_bot : IsScalarTower (⊥ : IntermediateField F E) F E :=
  IsScalarTower.of_algebraMap_eq
    (by
      intro x
      obtain ⟨y, rfl⟩ := (botEquiv F E).symm.surjective x
      rw [coe_algebraMap_over_bot, (botEquiv F E).apply_symm_apply, botEquiv_symm,
        IsScalarTower.algebraMap_apply F (⊥ : IntermediateField F E) E])
#align intermediate_field.is_scalar_tower_over_bot IntermediateField.isScalarTower_over_bot

/-- The top `IntermediateField` is isomorphic to the field.

This is the intermediate field version of `Subalgebra.topEquiv`. -/
@[simps!]
def topEquiv : (⊤ : IntermediateField F E) ≃ₐ[F] E :=
  (Subalgebra.equivOfEq _ _ top_toSubalgebra).trans Subalgebra.topEquiv
#align intermediate_field.top_equiv IntermediateField.topEquiv

-- Porting note: this theorem is now generated by the `@[simps!]` above.
#align intermediate_field.top_equiv_symm_apply_coe IntermediateField.topEquiv_symm_apply_coe

@[simp]
theorem restrictScalars_bot_eq_self (K : IntermediateField F E) :
    (⊥ : IntermediateField K E).restrictScalars _ = K :=
  SetLike.coe_injective Subtype.range_coe
#align intermediate_field.restrict_scalars_bot_eq_self IntermediateField.restrictScalars_bot_eq_self

@[simp]
theorem restrictScalars_top {K : Type*} [Field K] [Algebra K E] [Algebra K F]
    [IsScalarTower K F E] : (⊤ : IntermediateField F E).restrictScalars K = ⊤ :=
  rfl
#align intermediate_field.restrict_scalars_top IntermediateField.restrictScalars_top

@[simp]
theorem map_bot {K : Type*} [Field K] [Algebra F K] (f : E →ₐ[F] K) :
    IntermediateField.map f ⊥ = ⊥ :=
  toSubalgebra_injective <| Algebra.map_bot _

theorem _root_.AlgHom.fieldRange_eq_map {K : Type*} [Field K] [Algebra F K] (f : E →ₐ[F] K) :
    f.fieldRange = IntermediateField.map f ⊤ :=
  SetLike.ext' Set.image_univ.symm
#align alg_hom.field_range_eq_map AlgHom.fieldRange_eq_map

theorem _root_.AlgHom.map_fieldRange {K L : Type*} [Field K] [Field L] [Algebra F K] [Algebra F L]
    (f : E →ₐ[F] K) (g : K →ₐ[F] L) : f.fieldRange.map g = (g.comp f).fieldRange :=
  SetLike.ext' (Set.range_comp g f).symm
#align alg_hom.map_field_range AlgHom.map_fieldRange

theorem _root_.AlgHom.fieldRange_eq_top {K : Type*} [Field K] [Algebra F K] {f : E →ₐ[F] K} :
    f.fieldRange = ⊤ ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans Set.range_iff_surjective
#align alg_hom.field_range_eq_top AlgHom.fieldRange_eq_top

@[simp]
theorem _root_.AlgEquiv.fieldRange_eq_top {K : Type*} [Field K] [Algebra F K] (f : E ≃ₐ[F] K) :
    (f : E →ₐ[F] K).fieldRange = ⊤ :=
  AlgHom.fieldRange_eq_top.mpr f.surjective
#align alg_equiv.field_range_eq_top AlgEquiv.fieldRange_eq_top

end Lattice

section AdjoinDef

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] (S : Set E)

theorem adjoin_eq_range_algebraMap_adjoin :
    (adjoin F S : Set E) = Set.range (algebraMap (adjoin F S) E) :=
  Subtype.range_coe.symm
#align intermediate_field.adjoin_eq_range_algebra_map_adjoin IntermediateField.adjoin_eq_range_algebraMap_adjoin

theorem adjoin.algebraMap_mem (x : F) : algebraMap F E x ∈ adjoin F S :=
  IntermediateField.algebraMap_mem (adjoin F S) x
#align intermediate_field.adjoin.algebra_map_mem IntermediateField.adjoin.algebraMap_mem

theorem adjoin.range_algebraMap_subset : Set.range (algebraMap F E) ⊆ adjoin F S := by
  intro x hx
  cases' hx with f hf
  rw [← hf]
  exact adjoin.algebraMap_mem F S f
#align intermediate_field.adjoin.range_algebra_map_subset IntermediateField.adjoin.range_algebraMap_subset

instance adjoin.fieldCoe : CoeTC F (adjoin F S) where
  coe x := ⟨algebraMap F E x, adjoin.algebraMap_mem F S x⟩
#align intermediate_field.adjoin.field_coe IntermediateField.adjoin.fieldCoe

theorem subset_adjoin : S ⊆ adjoin F S := fun _ hx => Subfield.subset_closure (Or.inr hx)
#align intermediate_field.subset_adjoin IntermediateField.subset_adjoin

instance adjoin.setCoe : CoeTC S (adjoin F S) where coe x := ⟨x, subset_adjoin F S (Subtype.mem x)⟩
#align intermediate_field.adjoin.set_coe IntermediateField.adjoin.setCoe

@[mono]
theorem adjoin.mono (T : Set E) (h : S ⊆ T) : adjoin F S ≤ adjoin F T :=
  GaloisConnection.monotone_l gc h
#align intermediate_field.adjoin.mono IntermediateField.adjoin.mono

theorem adjoin_contains_field_as_subfield (F : Subfield E) : (F : Set E) ⊆ adjoin F S := fun x hx =>
  adjoin.algebraMap_mem F S ⟨x, hx⟩
#align intermediate_field.adjoin_contains_field_as_subfield IntermediateField.adjoin_contains_field_as_subfield

theorem subset_adjoin_of_subset_left {F : Subfield E} {T : Set E} (HT : T ⊆ F) : T ⊆ adjoin F S :=
  fun x hx => (adjoin F S).algebraMap_mem ⟨x, HT hx⟩
#align intermediate_field.subset_adjoin_of_subset_left IntermediateField.subset_adjoin_of_subset_left

theorem subset_adjoin_of_subset_right {T : Set E} (H : T ⊆ S) : T ⊆ adjoin F S := fun _ hx =>
  subset_adjoin F S (H hx)
#align intermediate_field.subset_adjoin_of_subset_right IntermediateField.subset_adjoin_of_subset_right

@[simp]
theorem adjoin_empty (F E : Type*) [Field F] [Field E] [Algebra F E] : adjoin F (∅ : Set E) = ⊥ :=
  eq_bot_iff.mpr (adjoin_le_iff.mpr (Set.empty_subset _))
#align intermediate_field.adjoin_empty IntermediateField.adjoin_empty

@[simp]
theorem adjoin_univ (F E : Type*) [Field F] [Field E] [Algebra F E] :
    adjoin F (Set.univ : Set E) = ⊤ :=
  eq_top_iff.mpr <| subset_adjoin _ _
#align intermediate_field.adjoin_univ IntermediateField.adjoin_univ

/-- If `K` is a field with `F ⊆ K` and `S ⊆ K` then `adjoin F S ≤ K`. -/
theorem adjoin_le_subfield {K : Subfield E} (HF : Set.range (algebraMap F E) ⊆ K) (HS : S ⊆ K) :
    (adjoin F S).toSubfield ≤ K := by
  apply Subfield.closure_le.mpr
  rw [Set.union_subset_iff]
  exact ⟨HF, HS⟩
#align intermediate_field.adjoin_le_subfield IntermediateField.adjoin_le_subfield

theorem adjoin_subset_adjoin_iff {F' : Type*} [Field F'] [Algebra F' E] {S S' : Set E} :
    (adjoin F S : Set E) ⊆ adjoin F' S' ↔
      Set.range (algebraMap F E) ⊆ adjoin F' S' ∧ S ⊆ adjoin F' S' :=
  ⟨fun h => ⟨_root_.trans (adjoin.range_algebraMap_subset _ _) h, _root_.trans
    (subset_adjoin _ _) h⟩, fun ⟨hF, hS⟩ =>
      (Subfield.closure_le (t := (adjoin F' S').toSubfield)).mpr (Set.union_subset hF hS)⟩
#align intermediate_field.adjoin_subset_adjoin_iff IntermediateField.adjoin_subset_adjoin_iff

/-- `F[S][T] = F[S ∪ T]` -/
theorem adjoin_adjoin_left (T : Set E) :
    (adjoin (adjoin F S) T).restrictScalars _ = adjoin F (S ∪ T) := by
  rw [SetLike.ext'_iff]
  change (↑(adjoin (adjoin F S) T) : Set E) = _
  apply Set.eq_of_subset_of_subset <;> rw [adjoin_subset_adjoin_iff] <;> constructor
  · rintro _ ⟨⟨x, hx⟩, rfl⟩; exact adjoin.mono _ _ _ (Set.subset_union_left _ _) hx
  · exact subset_adjoin_of_subset_right _ _ (Set.subset_union_right _ _)
-- Porting note: orginal proof times out
  · rintro x ⟨f, rfl⟩
    refine' Subfield.subset_closure _
    left
    exact ⟨f, rfl⟩
-- Porting note: orginal proof times out
  · refine' Set.union_subset (fun x hx => Subfield.subset_closure _)
      (fun x hx => Subfield.subset_closure _)
    · left
      refine' ⟨⟨x, Subfield.subset_closure _⟩, rfl⟩
      right
      exact hx
    · right
      exact hx
#align intermediate_field.adjoin_adjoin_left IntermediateField.adjoin_adjoin_left

@[simp]
theorem adjoin_insert_adjoin (x : E) :
    adjoin F (insert x (adjoin F S : Set E)) = adjoin F (insert x S) :=
  le_antisymm
    (adjoin_le_iff.mpr
      (Set.insert_subset_iff.mpr
        ⟨subset_adjoin _ _ (Set.mem_insert _ _),
          adjoin_le_iff.mpr (subset_adjoin_of_subset_right _ _ (Set.subset_insert _ _))⟩))
    (adjoin.mono _ _ _ (Set.insert_subset_insert (subset_adjoin _ _)))
#align intermediate_field.adjoin_insert_adjoin IntermediateField.adjoin_insert_adjoin

/-- `F[S][T] = F[T][S]` -/
theorem adjoin_adjoin_comm (T : Set E) :
    (adjoin (adjoin F S) T).restrictScalars F = (adjoin (adjoin F T) S).restrictScalars F := by
  rw [adjoin_adjoin_left, adjoin_adjoin_left, Set.union_comm]
#align intermediate_field.adjoin_adjoin_comm IntermediateField.adjoin_adjoin_comm

theorem adjoin_map {E' : Type*} [Field E'] [Algebra F E'] (f : E →ₐ[F] E') :
    (adjoin F S).map f = adjoin F (f '' S) := by
  ext x
  show
    x ∈ (Subfield.closure (Set.range (algebraMap F E) ∪ S)).map (f : E →+* E') ↔
      x ∈ Subfield.closure (Set.range (algebraMap F E') ∪ f '' S)
  rw [RingHom.map_field_closure, Set.image_union, ← Set.range_comp, ← RingHom.coe_comp,
    f.comp_algebraMap]
  rfl
#align intermediate_field.adjoin_map IntermediateField.adjoin_map

@[simp]
theorem lift_adjoin (K : IntermediateField F E) (S : Set K) :
    lift (adjoin F S) = adjoin F (Subtype.val '' S) :=
  adjoin_map _ _ _

theorem lift_adjoin_simple (K : IntermediateField F E) (α : K) :
    lift (adjoin F {α}) = adjoin F {α.1} := by
  simp only [lift_adjoin, Set.image_singleton]

@[simp]
theorem lift_bot (K : IntermediateField F E) :
    lift (F := K) ⊥ = ⊥ := map_bot _

@[simp]
theorem lift_top (K : IntermediateField F E) :
    lift (F := K) ⊤ = K := by rw [lift, ←AlgHom.fieldRange_eq_map, fieldRange_val]

@[simp]
theorem adjoin_self (K : IntermediateField F E) :
    adjoin F K = K := le_antisymm (adjoin_le_iff.2 fun _ ↦ id) (subset_adjoin F _)

theorem restrictScalars_adjoin (K : IntermediateField F E) (S : Set E) :
    restrictScalars F (adjoin K S) = adjoin F (K ∪ S) := by
  rw [← adjoin_self _ K, adjoin_adjoin_left, adjoin_self _ K]

theorem algebra_adjoin_le_adjoin : Algebra.adjoin F S ≤ (adjoin F S).toSubalgebra :=
  Algebra.adjoin_le (subset_adjoin _ _)
#align intermediate_field.algebra_adjoin_le_adjoin IntermediateField.algebra_adjoin_le_adjoin

theorem adjoin_eq_algebra_adjoin (inv_mem : ∀ x ∈ Algebra.adjoin F S, x⁻¹ ∈ Algebra.adjoin F S) :
    (adjoin F S).toSubalgebra = Algebra.adjoin F S :=
  le_antisymm
    (show adjoin F S ≤
        { Algebra.adjoin F S with
          inv_mem' := inv_mem }
      from adjoin_le_iff.mpr Algebra.subset_adjoin)
    (algebra_adjoin_le_adjoin _ _)
#align intermediate_field.adjoin_eq_algebra_adjoin IntermediateField.adjoin_eq_algebra_adjoin

theorem eq_adjoin_of_eq_algebra_adjoin (K : IntermediateField F E)
    (h : K.toSubalgebra = Algebra.adjoin F S) : K = adjoin F S := by
  apply toSubalgebra_injective
  rw [h]
  refine' (adjoin_eq_algebra_adjoin F _ _).symm
  intro x
  convert K.inv_mem (x := x) <;> rw [← h] <;> rfl
#align intermediate_field.eq_adjoin_of_eq_algebra_adjoin IntermediateField.eq_adjoin_of_eq_algebra_adjoin

theorem adjoin_eq_top_of_algebra (hS : Algebra.adjoin F S = ⊤) : adjoin F S = ⊤ :=
  top_le_iff.mp (hS.symm.trans_le <| algebra_adjoin_le_adjoin F S)

@[elab_as_elim]
theorem adjoin_induction {s : Set E} {p : E → Prop} {x} (h : x ∈ adjoin F s) (Hs : ∀ x ∈ s, p x)
    (Hmap : ∀ x, p (algebraMap F E x)) (Hadd : ∀ x y, p x → p y → p (x + y))
    (Hneg : ∀ x, p x → p (-x)) (Hinv : ∀ x, p x → p x⁻¹) (Hmul : ∀ x y, p x → p y → p (x * y)) :
    p x :=
  Subfield.closure_induction h (fun x hx => Or.casesOn hx (fun ⟨x, hx⟩ => hx ▸ Hmap x) (Hs x))
    ((algebraMap F E).map_one ▸ Hmap 1) Hadd Hneg Hinv Hmul
#align intermediate_field.adjoin_induction IntermediateField.adjoin_induction

/- Porting note (kmill): this notation is replacing the typeclass-based one I had previously
written, and it gives true `{x₁, x₂, ..., xₙ}` sets in the `adjoin` term. -/

open Lean in
/-- Supporting function for the `F⟮x₁,x₂,...,xₙ⟯` adjunction notation. -/
private partial def mkInsertTerm [Monad m] [MonadQuotation m] (xs : TSyntaxArray `term) : m Term :=
  run 0
where
  run (i : Nat) : m Term := do
    if i + 1 == xs.size then
      ``(singleton $(xs[i]!))
    else if i < xs.size then
      ``(insert $(xs[i]!) $(← run (i + 1)))
    else
      ``(EmptyCollection.emptyCollection)

/-- If `x₁ x₂ ... xₙ : E` then `F⟮x₁,x₂,...,xₙ⟯` is the `IntermediateField F E`
generated by these elements. -/
scoped macro:max K:term "⟮" xs:term,* "⟯" : term => do ``(adjoin $K $(← mkInsertTerm xs.getElems))

open Lean PrettyPrinter.Delaborator SubExpr in
@[delab app.IntermediateField.adjoin]
partial def delabAdjoinNotation : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  guard <| e.isAppOfArity ``adjoin 6
  let F ← withNaryArg 0 delab
  let xs ← withNaryArg 5 delabInsertArray
  `($F⟮$(xs.toArray),*⟯)
where
  delabInsertArray : DelabM (List Term) := do
    let e ← getExpr
    if e.isAppOfArity ``EmptyCollection.emptyCollection 2 then
      return []
    else if e.isAppOfArity ``singleton 4 then
      let x ← withNaryArg 3 delab
      return [x]
    else if e.isAppOfArity ``insert 5 then
      let x ← withNaryArg 3 delab
      let xs ← withNaryArg 4 delabInsertArray
      return x :: xs
    else failure

section AdjoinSimple

variable (α : E)

-- Porting note: in all the theorems below, mathport translated `F⟮α⟯` into `F⟮⟯`.
theorem mem_adjoin_simple_self : α ∈ F⟮α⟯ :=
  subset_adjoin F {α} (Set.mem_singleton α)
#align intermediate_field.mem_adjoin_simple_self IntermediateField.mem_adjoin_simple_self

/-- generator of `F⟮α⟯` -/
def AdjoinSimple.gen : F⟮α⟯ :=
  ⟨α, mem_adjoin_simple_self F α⟩
#align intermediate_field.adjoin_simple.gen IntermediateField.AdjoinSimple.gen

@[simp]
theorem AdjoinSimple.algebraMap_gen : algebraMap F⟮α⟯ E (AdjoinSimple.gen F α) = α :=
  rfl
#align intermediate_field.adjoin_simple.algebra_map_gen IntermediateField.AdjoinSimple.algebraMap_gen

@[simp]
theorem AdjoinSimple.isIntegral_gen : IsIntegral F (AdjoinSimple.gen F α) ↔ IsIntegral F α := by
  conv_rhs => rw [← AdjoinSimple.algebraMap_gen F α]
  rw [isIntegral_algebraMap_iff (algebraMap F⟮α⟯ E).injective]
#align intermediate_field.adjoin_simple.is_integral_gen IntermediateField.AdjoinSimple.isIntegral_gen

theorem adjoin_simple_adjoin_simple (β : E) : F⟮α⟯⟮β⟯.restrictScalars F = F⟮α, β⟯ :=
  adjoin_adjoin_left _ _ _
#align intermediate_field.adjoin_simple_adjoin_simple IntermediateField.adjoin_simple_adjoin_simple

theorem adjoin_simple_comm (β : E) : F⟮α⟯⟮β⟯.restrictScalars F = F⟮β⟯⟮α⟯.restrictScalars F :=
  adjoin_adjoin_comm _ _ _
#align intermediate_field.adjoin_simple_comm IntermediateField.adjoin_simple_comm

variable {F} {α}

theorem adjoin_algebraic_toSubalgebra {S : Set E} (hS : ∀ x ∈ S, IsAlgebraic F x) :
    (IntermediateField.adjoin F S).toSubalgebra = Algebra.adjoin F S := by
  simp only [isAlgebraic_iff_isIntegral] at hS
  have : Algebra.IsIntegral F (Algebra.adjoin F S) := by
    rwa [← le_integralClosure_iff_isIntegral, Algebra.adjoin_le_iff]
  have := isField_of_isIntegral_of_isField' this (Field.toIsField F)
  rw [← ((Algebra.adjoin F S).toIntermediateField' this).eq_adjoin_of_eq_algebra_adjoin F S] <;> rfl
#align intermediate_field.adjoin_algebraic_to_subalgebra IntermediateField.adjoin_algebraic_toSubalgebra

theorem adjoin_simple_toSubalgebra_of_integral (hα : IsIntegral F α) :
    F⟮α⟯.toSubalgebra = Algebra.adjoin F {α} := by
  apply adjoin_algebraic_toSubalgebra
  rintro x (rfl : x = α)
  rwa [isAlgebraic_iff_isIntegral]
#align intermediate_field.adjoin_simple_to_subalgebra_of_integral IntermediateField.adjoin_simple_toSubalgebra_of_integral

theorem isSplittingField_iff {p : F[X]} {K : IntermediateField F E} :
    p.IsSplittingField F K ↔ p.Splits (algebraMap F K) ∧ K = adjoin F (p.rootSet E) := by
  suffices _ → (Algebra.adjoin F (p.rootSet K) = ⊤ ↔ K = adjoin F (p.rootSet E)) by
    exact ⟨fun h => ⟨h.1, (this h.1).mp h.2⟩, fun h => ⟨h.1, (this h.1).mpr h.2⟩⟩
  simp_rw [SetLike.ext_iff, ← mem_toSubalgebra, ← SetLike.ext_iff]
  rw [adjoin_algebraic_toSubalgebra fun x => isAlgebraic_of_mem_rootSet]
  refine' fun hp => (adjoin_rootSet_eq_range hp K.val).symm.trans _
  rw [← K.range_val, eq_comm]
#align intermediate_field.is_splitting_field_iff IntermediateField.isSplittingField_iff

theorem adjoin_rootSet_isSplittingField {p : F[X]} (hp : p.Splits (algebraMap F E)) :
    p.IsSplittingField F (adjoin F (p.rootSet E)) :=
  isSplittingField_iff.mpr ⟨splits_of_splits hp fun _ hx => subset_adjoin F (p.rootSet E) hx, rfl⟩
#align intermediate_field.adjoin_root_set_is_splitting_field IntermediateField.adjoin_rootSet_isSplittingField

open scoped BigOperators

section Supremum

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (E1 E2 : IntermediateField K L)

theorem le_sup_toSubalgebra : E1.toSubalgebra ⊔ E2.toSubalgebra ≤ (E1 ⊔ E2).toSubalgebra :=
  sup_le (show E1 ≤ E1 ⊔ E2 from le_sup_left) (show E2 ≤ E1 ⊔ E2 from le_sup_right)
#align intermediate_field.le_sup_to_subalgebra IntermediateField.le_sup_toSubalgebra

theorem sup_toSubalgebra [h1 : FiniteDimensional K E1] [h2 : FiniteDimensional K E2] :
    (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra := by
  let S1 := E1.toSubalgebra
  let S2 := E2.toSubalgebra
  refine'
    le_antisymm
      (show _ ≤ (S1 ⊔ S2).toIntermediateField _ from
        sup_le (show S1 ≤ _ from le_sup_left) (show S2 ≤ _ from le_sup_right))
      (le_sup_toSubalgebra E1 E2)
  suffices IsField (S1 ⊔ S2 : Subalgebra K L) by
    intro x hx
    by_cases hx' : (⟨x, hx⟩ : (S1 ⊔ S2 : Subalgebra K L)) = 0
    · rw [← Subtype.coe_mk x, hx', Subalgebra.coe_zero, inv_zero]
      exact (S1 ⊔ S2).zero_mem
    · obtain ⟨y, h⟩ := this.mul_inv_cancel hx'
      exact (congr_arg (· ∈ S1 ⊔ S2) <| eq_inv_of_mul_eq_one_right <| Subtype.ext_iff.mp h).mp y.2
  exact
    isField_of_isIntegral_of_isField'
      (isIntegral_sup.mpr ⟨Algebra.isIntegral_of_finite K E1, Algebra.isIntegral_of_finite K E2⟩)
      (Field.toIsField K)
#align intermediate_field.sup_to_subalgebra IntermediateField.sup_toSubalgebra

instance finiteDimensional_sup [h1 : FiniteDimensional K E1] [h2 : FiniteDimensional K E2] :
    FiniteDimensional K (E1 ⊔ E2 : IntermediateField K L) := by
  let g := Algebra.TensorProduct.productMap E1.val E2.val
  suffices g.range = (E1 ⊔ E2).toSubalgebra by
    have h : FiniteDimensional K (Subalgebra.toSubmodule g.range) :=
      g.toLinearMap.finiteDimensional_range
    rwa [this] at h
  rw [Algebra.TensorProduct.productMap_range, E1.range_val, E2.range_val, sup_toSubalgebra]
#align intermediate_field.finite_dimensional_sup IntermediateField.finiteDimensional_sup

variable {ι : Type*} {t : ι → IntermediateField K L}

theorem coe_iSup_of_directed [Nonempty ι] (dir : Directed (· ≤ ·) t) :
    ↑(iSup t) = ⋃ i, (t i : Set L) :=
  let M : IntermediateField K L :=
    { __ := Subalgebra.copy _ _ (Subalgebra.coe_iSup_of_directed dir).symm
      inv_mem' := fun _ hx ↦ have ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        Set.mem_iUnion.mpr ⟨i, (t i).inv_mem hi⟩ }
  have : iSup t = M := le_antisymm
    (iSup_le fun i ↦ le_iSup (fun i ↦ (t i : Set L)) i) (Set.iUnion_subset fun _ ↦ le_iSup t _)
  this.symm ▸ rfl

theorem toSubalgebra_iSup_of_directed (dir : Directed (· ≤ ·) t) :
    (iSup t).toSubalgebra = ⨆ i, (t i).toSubalgebra := by
  cases isEmpty_or_nonempty ι
  · simp_rw [iSup_of_empty, bot_toSubalgebra]
  · exact SetLike.ext' ((coe_iSup_of_directed dir).trans (Subalgebra.coe_iSup_of_directed dir).symm)

instance finiteDimensional_iSup_of_finite [h : Finite ι] [∀ i, FiniteDimensional K (t i)] :
    FiniteDimensional K (⨆ i, t i : IntermediateField K L) := by
  rw [← iSup_univ]
  let P : Set ι → Prop := fun s => FiniteDimensional K (⨆ i ∈ s, t i : IntermediateField K L)
  change P Set.univ
  apply Set.Finite.induction_on
  all_goals dsimp only
  · exact Set.finite_univ
  · rw [iSup_emptyset]
    exact (botEquiv K L).symm.toLinearEquiv.finiteDimensional
  · intro _ s _ _ hs
    rw [iSup_insert]
    exact IntermediateField.finiteDimensional_sup _ _
#align intermediate_field.finite_dimensional_supr_of_finite IntermediateField.finiteDimensional_iSup_of_finite

instance finiteDimensional_iSup_of_finset
    /-Porting note: changed `h` from `∀ i ∈ s, FiniteDimensional K (t i)` because this caused an
      error. See `finiteDimensional_iSup_of_finset'` for a stronger version, that was the one
      used in mathlib3.-/
    {s : Finset ι} [∀ i, FiniteDimensional K (t i)] :
    FiniteDimensional K (⨆ i ∈ s, t i : IntermediateField K L) :=
  iSup_subtype'' s t ▸ IntermediateField.finiteDimensional_iSup_of_finite
#align intermediate_field.finite_dimensional_supr_of_finset IntermediateField.finiteDimensional_iSup_of_finset

theorem finiteDimensional_iSup_of_finset'
    /-Porting note: this was the mathlib3 version. Using `[h : ...]`, as in mathlib3, causes the
    error "invalid parametric local instance".-/
    {s : Finset ι} (h : ∀ i, i ∈ s → FiniteDimensional K (t i)) :
    FiniteDimensional K (⨆ i ∈ s, t i : IntermediateField K L) :=
  have := Subtype.forall'.mp h
  iSup_subtype'' s t ▸ IntermediateField.finiteDimensional_iSup_of_finite

/-- A compositum of splitting fields is a splitting field -/
theorem isSplittingField_iSup {p : ι → K[X]}
    {s : Finset ι} (h0 : ∏ i in s, p i ≠ 0) (h : ∀ i ∈ s, (p i).IsSplittingField K (t i)) :
    (∏ i in s, p i).IsSplittingField K (⨆ i ∈ s, t i : IntermediateField K L) := by
  let F : IntermediateField K L := ⨆ i ∈ s, t i
  have hF : ∀ i ∈ s, t i ≤ F := fun i hi ↦ le_iSup_of_le i (le_iSup (fun _ ↦ t i) hi)
  simp only [isSplittingField_iff] at h ⊢
  refine'
    ⟨splits_prod (algebraMap K F) fun i hi ↦
        splits_comp_of_splits (algebraMap K (t i)) (inclusion (hF i hi)).toRingHom
          (h i hi).1,
      _⟩
  simp only [rootSet_prod p s h0, ← Set.iSup_eq_iUnion, (@gc K _ L _ _).l_iSup₂]
  exact iSup_congr fun i ↦ iSup_congr fun hi ↦ (h i hi).2
#align intermediate_field.is_splitting_field_supr IntermediateField.isSplittingField_iSup

end Supremum

open Set CompleteLattice

/- Porting note: this was tagged `simp`, but the LHS can be simplified now that the notation
has been improved. -/
theorem adjoin_simple_le_iff {K : IntermediateField F E} : F⟮α⟯ ≤ K ↔ α ∈ K := by simp
#align intermediate_field.adjoin_simple_le_iff IntermediateField.adjoin_simple_le_iff

theorem biSup_adjoin_simple : ⨆ x ∈ S, F⟮x⟯ = adjoin F S :=
  le_antisymm (iSup_le fun _ ↦ iSup_le fun hx ↦ adjoin_simple_le_iff.mpr <| subset_adjoin F S hx) <|
    adjoin_le_iff.mpr fun x hx ↦ adjoin_simple_le_iff.mp (le_iSup_of_le x (le_iSup_of_le hx le_rfl))

/-- Adjoining a single element is compact in the lattice of intermediate fields. -/
theorem adjoin_simple_isCompactElement (x : E) : IsCompactElement F⟮x⟯ := by
  simp_rw [isCompactElement_iff_le_of_directed_sSup_le,
    adjoin_simple_le_iff, sSup_eq_iSup', ← exists_prop]
  intro s hne hs hx
  have := hne.to_subtype
  rwa [← SetLike.mem_coe, coe_iSup_of_directed hs.directed_val, mem_iUnion, Subtype.exists] at hx
#align intermediate_field.adjoin_simple_is_compact_element IntermediateField.adjoin_simple_isCompactElement

-- Porting note: original proof times out.
/-- Adjoining a finite subset is compact in the lattice of intermediate fields. -/
theorem adjoin_finset_isCompactElement (S : Finset E) :
    IsCompactElement (adjoin F S : IntermediateField F E) := by
  rw [← biSup_adjoin_simple]
  simp_rw [Finset.mem_coe, ← Finset.sup_eq_iSup]
  exact finset_sup_compact_of_compact S fun x _ => adjoin_simple_isCompactElement x
#align intermediate_field.adjoin_finset_is_compact_element IntermediateField.adjoin_finset_isCompactElement

/-- Adjoining a finite subset is compact in the lattice of intermediate fields. -/
theorem adjoin_finite_isCompactElement {S : Set E} (h : S.Finite) : IsCompactElement (adjoin F S) :=
  Finite.coe_toFinset h ▸ adjoin_finset_isCompactElement h.toFinset
#align intermediate_field.adjoin_finite_is_compact_element IntermediateField.adjoin_finite_isCompactElement

/-- The lattice of intermediate fields is compactly generated. -/
instance : IsCompactlyGenerated (IntermediateField F E) :=
  ⟨fun s =>
    ⟨(fun x => F⟮x⟯) '' s,
      ⟨by rintro t ⟨x, _, rfl⟩; exact adjoin_simple_isCompactElement x,
        sSup_image.trans <| (biSup_adjoin_simple _).trans <|
          le_antisymm (adjoin_le_iff.mpr le_rfl) <| subset_adjoin F (s : Set E)⟩⟩⟩

theorem exists_finset_of_mem_iSup {ι : Type*} {f : ι → IntermediateField F E} {x : E}
    (hx : x ∈ ⨆ i, f i) : ∃ s : Finset ι, x ∈ ⨆ i ∈ s, f i := by
  have := (adjoin_simple_isCompactElement x : IsCompactElement F⟮x⟯).exists_finset_of_le_iSup
    (IntermediateField F E) f
  simp only [adjoin_simple_le_iff] at this
  exact this hx
#align intermediate_field.exists_finset_of_mem_supr IntermediateField.exists_finset_of_mem_iSup

theorem exists_finset_of_mem_supr' {ι : Type*} {f : ι → IntermediateField F E} {x : E}
    (hx : x ∈ ⨆ i, f i) : ∃ s : Finset (Σ i, f i), x ∈ ⨆ i ∈ s, F⟮(i.2 : E)⟯ := by
-- Porting note: writing `fun i x h => ...` does not work.
  refine exists_finset_of_mem_iSup (SetLike.le_def.mp (iSup_le fun i ↦ ?_) hx)
  exact fun x h ↦ SetLike.le_def.mp (le_iSup_of_le ⟨i, x, h⟩ (by simp)) (mem_adjoin_simple_self F x)
#align intermediate_field.exists_finset_of_mem_supr' IntermediateField.exists_finset_of_mem_supr'

theorem exists_finset_of_mem_supr'' {ι : Type*} {f : ι → IntermediateField F E}
    (h : ∀ i, Algebra.IsAlgebraic F (f i)) {x : E} (hx : x ∈ ⨆ i, f i) :
    ∃ s : Finset (Σ i, f i), x ∈ ⨆ i ∈ s, adjoin F ((minpoly F (i.2 : _)).rootSet E) := by
-- Porting note: writing `fun i x1 hx1 => ...` does not work.
  refine' exists_finset_of_mem_iSup (SetLike.le_def.mp (iSup_le (fun i => _)) hx)
  intro x1 hx1
  refine' SetLike.le_def.mp (le_iSup_of_le ⟨i, x1, hx1⟩ _)
    (subset_adjoin F (rootSet (minpoly F x1) E) _)
  · rw [IntermediateField.minpoly_eq, Subtype.coe_mk]
  · rw [mem_rootSet_of_ne, minpoly.aeval]
    exact minpoly.ne_zero (isIntegral_iff.mp (isAlgebraic_iff_isIntegral.mp (h i ⟨x1, hx1⟩)))
#align intermediate_field.exists_finset_of_mem_supr'' IntermediateField.exists_finset_of_mem_supr''

end AdjoinSimple

end AdjoinDef

section AdjoinIntermediateFieldLattice

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E] {α : E} {S : Set E}

@[simp]
theorem adjoin_eq_bot_iff : adjoin F S = ⊥ ↔ S ⊆ (⊥ : IntermediateField F E) := by
  rw [eq_bot_iff, adjoin_le_iff]; rfl
#align intermediate_field.adjoin_eq_bot_iff IntermediateField.adjoin_eq_bot_iff

/- Porting note: this was tagged `simp`. -/
theorem adjoin_simple_eq_bot_iff : F⟮α⟯ = ⊥ ↔ α ∈ (⊥ : IntermediateField F E) := by
  simp
#align intermediate_field.adjoin_simple_eq_bot_iff IntermediateField.adjoin_simple_eq_bot_iff

@[simp]
theorem adjoin_zero : F⟮(0 : E)⟯ = ⊥ :=
  adjoin_simple_eq_bot_iff.mpr (zero_mem ⊥)
#align intermediate_field.adjoin_zero IntermediateField.adjoin_zero

@[simp]
theorem adjoin_one : F⟮(1 : E)⟯ = ⊥ :=
  adjoin_simple_eq_bot_iff.mpr (one_mem ⊥)
#align intermediate_field.adjoin_one IntermediateField.adjoin_one

@[simp]
theorem adjoin_int (n : ℤ) : F⟮(n : E)⟯ = ⊥ := by
  refine' adjoin_simple_eq_bot_iff.mpr (coe_int_mem ⊥ n)
#align intermediate_field.adjoin_int IntermediateField.adjoin_int

@[simp]
theorem adjoin_nat (n : ℕ) : F⟮(n : E)⟯ = ⊥ :=
  adjoin_simple_eq_bot_iff.mpr (coe_nat_mem ⊥ n)
#align intermediate_field.adjoin_nat IntermediateField.adjoin_nat

section AdjoinRank

open FiniteDimensional Module

variable {K L : IntermediateField F E}

@[simp]
theorem rank_eq_one_iff : Module.rank F K = 1 ↔ K = ⊥ := by
  rw [← toSubalgebra_eq_iff, ← rank_eq_rank_subalgebra, Subalgebra.rank_eq_one_iff,
    bot_toSubalgebra]
#align intermediate_field.rank_eq_one_iff IntermediateField.rank_eq_one_iff

@[simp]
theorem finrank_eq_one_iff : finrank F K = 1 ↔ K = ⊥ := by
  rw [← toSubalgebra_eq_iff, ← finrank_eq_finrank_subalgebra, Subalgebra.finrank_eq_one_iff,
    bot_toSubalgebra]
#align intermediate_field.finrank_eq_one_iff IntermediateField.finrank_eq_one_iff

@[simp]
theorem rank_bot : Module.rank F (⊥ : IntermediateField F E) = 1 := by rw [rank_eq_one_iff]
#align intermediate_field.rank_bot IntermediateField.rank_bot

@[simp]
theorem finrank_bot : finrank F (⊥ : IntermediateField F E) = 1 := by rw [finrank_eq_one_iff]
#align intermediate_field.finrank_bot IntermediateField.finrank_bot

theorem rank_adjoin_eq_one_iff : Module.rank F (adjoin F S) = 1 ↔ S ⊆ (⊥ : IntermediateField F E) :=
  Iff.trans rank_eq_one_iff adjoin_eq_bot_iff
#align intermediate_field.rank_adjoin_eq_one_iff IntermediateField.rank_adjoin_eq_one_iff

theorem rank_adjoin_simple_eq_one_iff : Module.rank F F⟮α⟯ = 1 ↔ α ∈ (⊥ : IntermediateField F E) :=
  by rw [rank_adjoin_eq_one_iff]; exact Set.singleton_subset_iff
#align intermediate_field.rank_adjoin_simple_eq_one_iff IntermediateField.rank_adjoin_simple_eq_one_iff

theorem finrank_adjoin_eq_one_iff : finrank F (adjoin F S) = 1 ↔ S ⊆ (⊥ : IntermediateField F E) :=
  Iff.trans finrank_eq_one_iff adjoin_eq_bot_iff
#align intermediate_field.finrank_adjoin_eq_one_iff IntermediateField.finrank_adjoin_eq_one_iff

theorem finrank_adjoin_simple_eq_one_iff :
    finrank F F⟮α⟯ = 1 ↔ α ∈ (⊥ : IntermediateField F E) := by
  rw [finrank_adjoin_eq_one_iff]; exact Set.singleton_subset_iff
#align intermediate_field.finrank_adjoin_simple_eq_one_iff IntermediateField.finrank_adjoin_simple_eq_one_iff

/-- If `F⟮x⟯` has dimension `1` over `F` for every `x ∈ E` then `F = E`. -/
theorem bot_eq_top_of_rank_adjoin_eq_one (h : ∀ x : E, Module.rank F F⟮x⟯ = 1) :
    (⊥ : IntermediateField F E) = ⊤ := by
  ext y
  rw [iff_true_right IntermediateField.mem_top]
  exact rank_adjoin_simple_eq_one_iff.mp (h y)
#align intermediate_field.bot_eq_top_of_rank_adjoin_eq_one IntermediateField.bot_eq_top_of_rank_adjoin_eq_one

theorem bot_eq_top_of_finrank_adjoin_eq_one (h : ∀ x : E, finrank F F⟮x⟯ = 1) :
    (⊥ : IntermediateField F E) = ⊤ := by
  ext y
  rw [iff_true_right IntermediateField.mem_top]
  exact finrank_adjoin_simple_eq_one_iff.mp (h y)
#align intermediate_field.bot_eq_top_of_finrank_adjoin_eq_one IntermediateField.bot_eq_top_of_finrank_adjoin_eq_one

theorem subsingleton_of_rank_adjoin_eq_one (h : ∀ x : E, Module.rank F F⟮x⟯ = 1) :
    Subsingleton (IntermediateField F E) :=
  subsingleton_of_bot_eq_top (bot_eq_top_of_rank_adjoin_eq_one h)
#align intermediate_field.subsingleton_of_rank_adjoin_eq_one IntermediateField.subsingleton_of_rank_adjoin_eq_one

theorem subsingleton_of_finrank_adjoin_eq_one (h : ∀ x : E, finrank F F⟮x⟯ = 1) :
    Subsingleton (IntermediateField F E) :=
  subsingleton_of_bot_eq_top (bot_eq_top_of_finrank_adjoin_eq_one h)
#align intermediate_field.subsingleton_of_finrank_adjoin_eq_one IntermediateField.subsingleton_of_finrank_adjoin_eq_one

/-- If `F⟮x⟯` has dimension `≤1` over `F` for every `x ∈ E` then `F = E`. -/
theorem bot_eq_top_of_finrank_adjoin_le_one [FiniteDimensional F E]
    (h : ∀ x : E, finrank F F⟮x⟯ ≤ 1) : (⊥ : IntermediateField F E) = ⊤ := by
  apply bot_eq_top_of_finrank_adjoin_eq_one
  exact fun x => by linarith [h x, show 0 < finrank F F⟮x⟯ from finrank_pos]
#align intermediate_field.bot_eq_top_of_finrank_adjoin_le_one IntermediateField.bot_eq_top_of_finrank_adjoin_le_one

theorem subsingleton_of_finrank_adjoin_le_one [FiniteDimensional F E]
    (h : ∀ x : E, finrank F F⟮x⟯ ≤ 1) : Subsingleton (IntermediateField F E) :=
  subsingleton_of_bot_eq_top (bot_eq_top_of_finrank_adjoin_le_one h)
#align intermediate_field.subsingleton_of_finrank_adjoin_le_one IntermediateField.subsingleton_of_finrank_adjoin_le_one

end AdjoinRank

end AdjoinIntermediateFieldLattice

section AdjoinIntegralElement

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] {α : E}

variable {K : Type*} [Field K] [Algebra F K]

theorem minpoly_gen (α : E) :
    minpoly F (AdjoinSimple.gen F α) = minpoly F α := by
  rw [← minpoly.algebraMap_eq (algebraMap F⟮α⟯ E).injective, AdjoinSimple.algebraMap_gen]
#align intermediate_field.minpoly_gen IntermediateField.minpoly_genₓ

theorem aeval_gen_minpoly (α : E) : aeval (AdjoinSimple.gen F α) (minpoly F α) = 0 := by
  ext
  convert minpoly.aeval F α
  conv in aeval α => rw [← AdjoinSimple.algebraMap_gen F α]
  exact (aeval_algebraMap_apply E (AdjoinSimple.gen F α) _).symm
#align intermediate_field.aeval_gen_minpoly IntermediateField.aeval_gen_minpoly

--Porting note: original proof used `Exists.cases_on`.
/-- algebra isomorphism between `AdjoinRoot` and `F⟮α⟯` -/
noncomputable def adjoinRootEquivAdjoin (h : IsIntegral F α) :
    AdjoinRoot (minpoly F α) ≃ₐ[F] F⟮α⟯ :=
  AlgEquiv.ofBijective
    (AdjoinRoot.liftHom (minpoly F α) (AdjoinSimple.gen F α) (aeval_gen_minpoly F α))
    (by
      set f := AdjoinRoot.lift _ _ (aeval_gen_minpoly F α : _)
      haveI := Fact.mk (minpoly.irreducible h)
      constructor
      · exact RingHom.injective f
      · suffices F⟮α⟯.toSubfield ≤ RingHom.fieldRange (F⟮α⟯.toSubfield.subtype.comp f) by
          intro x
          obtain ⟨y, hy⟩ := (this (Subtype.mem x))
          exact ⟨y, Subtype.ext hy⟩
        refine' Subfield.closure_le.mpr (Set.union_subset (fun x hx => _) _)
        · obtain ⟨y, hy⟩ := hx
          refine' ⟨y, _⟩
          -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
          erw [RingHom.comp_apply, AdjoinRoot.lift_of (aeval_gen_minpoly F α)]
          exact hy
        · refine' Set.singleton_subset_iff.mpr ⟨AdjoinRoot.root (minpoly F α), _⟩
          -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
          erw [RingHom.comp_apply, AdjoinRoot.lift_root (aeval_gen_minpoly F α)]
          rfl)
#align intermediate_field.adjoin_root_equiv_adjoin IntermediateField.adjoinRootEquivAdjoin

theorem adjoinRootEquivAdjoin_apply_root (h : IsIntegral F α) :
    adjoinRootEquivAdjoin F h (AdjoinRoot.root (minpoly F α)) = AdjoinSimple.gen F α :=
  AdjoinRoot.lift_root (aeval_gen_minpoly F α)
#align intermediate_field.adjoin_root_equiv_adjoin_apply_root IntermediateField.adjoinRootEquivAdjoin_apply_root

section PowerBasis

variable {L : Type*} [Field L] [Algebra K L]

/-- The elements `1, x, ..., x ^ (d - 1)` form a basis for `K⟮x⟯`,
where `d` is the degree of the minimal polynomial of `x`. -/
noncomputable def powerBasisAux {x : L} (hx : IsIntegral K x) :
    Basis (Fin (minpoly K x).natDegree) K K⟮x⟯ :=
  (AdjoinRoot.powerBasis (minpoly.ne_zero hx)).basis.map (adjoinRootEquivAdjoin K hx).toLinearEquiv
#align intermediate_field.power_basis_aux IntermediateField.powerBasisAux

/-- The power basis `1, x, ..., x ^ (d - 1)` for `K⟮x⟯`,
where `d` is the degree of the minimal polynomial of `x`. -/
@[simps]
noncomputable def adjoin.powerBasis {x : L} (hx : IsIntegral K x) : PowerBasis K K⟮x⟯ where
  gen := AdjoinSimple.gen K x
  dim := (minpoly K x).natDegree
  basis := powerBasisAux hx
  basis_eq_pow i := by
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [powerBasisAux, Basis.map_apply, PowerBasis.basis_eq_pow, AlgEquiv.toLinearEquiv_apply,
      AlgEquiv.map_pow, AdjoinRoot.powerBasis_gen, adjoinRootEquivAdjoin_apply_root]
#align intermediate_field.adjoin.power_basis IntermediateField.adjoin.powerBasis

theorem adjoin.finiteDimensional {x : L} (hx : IsIntegral K x) : FiniteDimensional K K⟮x⟯ :=
  PowerBasis.finiteDimensional (adjoin.powerBasis hx)
#align intermediate_field.adjoin.finite_dimensional IntermediateField.adjoin.finiteDimensional

theorem isAlgebraic_adjoin_simple {x : L} (hx : IsIntegral K x) : Algebra.IsAlgebraic K K⟮x⟯ :=
  have := adjoin.finiteDimensional hx; Algebra.isAlgebraic_of_finite K K⟮x⟯

theorem adjoin.finrank {x : L} (hx : IsIntegral K x) :
    FiniteDimensional.finrank K K⟮x⟯ = (minpoly K x).natDegree := by
  rw [PowerBasis.finrank (adjoin.powerBasis hx : _)]
  rfl
#align intermediate_field.adjoin.finrank IntermediateField.adjoin.finrank

/-- If `K / E / F` is a field extension tower, `S ⊂ K` is such that `F(S) = K`,
then `E(S) = K`. -/
theorem adjoin_eq_top_of_adjoin_eq_top [Algebra E K] [IsScalarTower F E K]
    {S : Set K} (hprim : adjoin F S = ⊤) : adjoin E S = ⊤ :=
  restrictScalars_injective F <| by
    rw [restrictScalars_top, ← top_le_iff, ← hprim, adjoin_le_iff,
      coe_restrictScalars, ← adjoin_le_iff]

/-- If `E / F` is a finite extension such that `E = F(α)`, then for any intermediate field `K`, the
`F` adjoin the coefficients of `minpoly K α` is equal to `K` itself. -/
theorem adjoin_minpoly_coeff_of_exists_primitive_element
    [FiniteDimensional F E] (hprim : adjoin F {α} = ⊤) (K : IntermediateField F E) :
    adjoin F ((minpoly K α).map (algebraMap K E)).frange = K := by
  set g := (minpoly K α).map (algebraMap K E)
  set K' : IntermediateField F E := adjoin F g.frange
  have hsub : K' ≤ K := by
    refine adjoin_le_iff.mpr fun x ↦ ?_
    rw [Finset.mem_coe, mem_frange_iff]
    rintro ⟨n, -, rfl⟩
    rw [coeff_map]
    apply Subtype.mem
  have g_lifts : g ∈ lifts (algebraMap K' E) := by
    refine g.lifts_iff_coeff_lifts.mpr fun n ↦ ?_
    erw [Subtype.range_val]
    by_cases hn : n ∈ g.support
    · exact subset_adjoin F _ (mem_frange_iff.mpr ⟨n, hn, rfl⟩)
    · exact not_mem_support_iff.mp hn ▸ zero_mem K'
  obtain ⟨p, hp⟩ := g.lifts_and_natDegree_eq_and_monic
    g_lifts ((minpoly.monic <| isIntegral_of_finite K α).map _)
  have dvd_p : minpoly K' α ∣ p
  · apply minpoly.dvd
    rw [aeval_def, eval₂_eq_eval_map, hp.1, ← eval₂_eq_eval_map, ← aeval_def]
    exact minpoly.aeval K α
  have finrank_eq : ∀ K : IntermediateField F E, finrank K E = natDegree (minpoly K α)
  · intro K
    have := adjoin.finrank (isIntegral_of_finite K α)
    erw [adjoin_eq_top_of_adjoin_eq_top F hprim, finrank_top K E] at this
    exact this
  refine eq_of_le_of_finrank_le' hsub ?_
  simp_rw [finrank_eq]
  convert natDegree_le_of_dvd dvd_p hp.2.2.ne_zero using 1
  rw [hp.2.1, natDegree_map]

theorem _root_.minpoly.natDegree_le (x : L) [FiniteDimensional K L] :
    (minpoly K x).natDegree ≤ finrank K L :=
  le_of_eq_of_le (IntermediateField.adjoin.finrank (isIntegral_of_finite _ _)).symm
    K⟮x⟯.toSubmodule.finrank_le
#align minpoly.nat_degree_le minpoly.natDegree_le

theorem _root_.minpoly.degree_le (x : L) [FiniteDimensional K L] :
    (minpoly K x).degree ≤ finrank K L :=
  degree_le_of_natDegree_le (minpoly.natDegree_le x)
#align minpoly.degree_le minpoly.degree_le

/-- A compositum of algebraic extensions is algebraic -/
theorem isAlgebraic_iSup {ι : Type*} {t : ι → IntermediateField K L}
    (h : ∀ i, Algebra.IsAlgebraic K (t i)) :
    Algebra.IsAlgebraic K (⨆ i, t i : IntermediateField K L) := by
  rintro ⟨x, hx⟩
  obtain ⟨s, hx⟩ := exists_finset_of_mem_supr' hx
  rw [isAlgebraic_iff, Subtype.coe_mk, ← Subtype.coe_mk (p := (· ∈ _)) x hx, ← isAlgebraic_iff]
  haveI : ∀ i : Σ i, t i, FiniteDimensional K K⟮(i.2 : L)⟯ := fun ⟨i, x⟩ ↦
    adjoin.finiteDimensional (isIntegral_iff.1 (isAlgebraic_iff_isIntegral.1 (h i x)))
  apply Algebra.isAlgebraic_of_finite
#align intermediate_field.is_algebraic_supr IntermediateField.isAlgebraic_iSup

theorem isAlgebraic_adjoin {S : Set L} (hS : ∀ x ∈ S, IsIntegral K x) :
    Algebra.IsAlgebraic K (adjoin K S) := by
  rw [← biSup_adjoin_simple, ← iSup_subtype'']
  exact isAlgebraic_iSup fun x ↦ isAlgebraic_adjoin_simple (hS x x.2)

/-- If `L / K` is a field extension, `S` is a finite subset of `L`, such that every element of `S`
is integral (= algebraic) over `K`, then `K(S) / K` is a finite extension.
A direct corollary of `finiteDimensional_iSup_of_finite`. -/
theorem finiteDimensional_adjoin {S : Set L} [Finite S] (hS : ∀ x ∈ S, IsIntegral K x) :
    FiniteDimensional K (adjoin K S) := by
  rw [← biSup_adjoin_simple, ← iSup_subtype'']
  haveI (x : S) := adjoin.finiteDimensional (hS x.1 x.2)
  exact finiteDimensional_iSup_of_finite

end PowerBasis

/-- Algebra homomorphism `F⟮α⟯ →ₐ[F] K` are in bijection with the set of roots
of `minpoly α` in `K`. -/
noncomputable def algHomAdjoinIntegralEquiv (h : IsIntegral F α) :
    (F⟮α⟯ →ₐ[F] K) ≃ { x // x ∈ (minpoly F α).aroots K } :=
  (adjoin.powerBasis h).liftEquiv'.trans
    ((Equiv.refl _).subtypeEquiv fun x => by
      rw [adjoin.powerBasis_gen, minpoly_gen, Equiv.refl_apply])
#align intermediate_field.alg_hom_adjoin_integral_equiv IntermediateField.algHomAdjoinIntegralEquiv

lemma algHomAdjoinIntegralEquiv_symm_apply_gen (h : IsIntegral F α)
    (x : { x // x ∈ (minpoly F α).aroots K }) :
    (algHomAdjoinIntegralEquiv F h).symm x (AdjoinSimple.gen F α) = x :=
  (adjoin.powerBasis h).lift_gen x.val <| by
    rw [adjoin.powerBasis_gen, minpoly_gen]; exact (mem_aroots.mp x.2).2

/-- Fintype of algebra homomorphism `F⟮α⟯ →ₐ[F] K` -/
noncomputable def fintypeOfAlgHomAdjoinIntegral (h : IsIntegral F α) : Fintype (F⟮α⟯ →ₐ[F] K) :=
  PowerBasis.AlgHom.fintype (adjoin.powerBasis h)
#align intermediate_field.fintype_of_alg_hom_adjoin_integral IntermediateField.fintypeOfAlgHomAdjoinIntegral

theorem card_algHom_adjoin_integral (h : IsIntegral F α) (h_sep : (minpoly F α).Separable)
    (h_splits : (minpoly F α).Splits (algebraMap F K)) :
    @Fintype.card (F⟮α⟯ →ₐ[F] K) (fintypeOfAlgHomAdjoinIntegral F h) = (minpoly F α).natDegree := by
  rw [AlgHom.card_of_powerBasis] <;>
    simp only [adjoin.powerBasis_dim, adjoin.powerBasis_gen, minpoly_gen, h_sep, h_splits]
#align intermediate_field.card_alg_hom_adjoin_integral IntermediateField.card_algHom_adjoin_integral

end AdjoinIntegralElement

section Induction

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

/-- An intermediate field `S` is finitely generated if there exists `t : Finset E` such that
`IntermediateField.adjoin F t = S`. -/
def FG (S : IntermediateField F E) : Prop :=
  ∃ t : Finset E, adjoin F ↑t = S
#align intermediate_field.fg IntermediateField.FG

theorem fg_adjoin_finset (t : Finset E) : (adjoin F (↑t : Set E)).FG :=
  ⟨t, rfl⟩
#align intermediate_field.fg_adjoin_finset IntermediateField.fg_adjoin_finset

theorem fg_def {S : IntermediateField F E} : S.FG ↔ ∃ t : Set E, Set.Finite t ∧ adjoin F t = S :=
  Iff.symm Set.exists_finite_iff_finset
#align intermediate_field.fg_def IntermediateField.fg_def

theorem fg_bot : (⊥ : IntermediateField F E).FG :=
  -- porting note: was `⟨∅, adjoin_empty F E⟩`
  ⟨∅, by simp only [Finset.coe_empty, adjoin_empty]⟩
#align intermediate_field.fg_bot IntermediateField.fg_bot

theorem fG_of_fG_toSubalgebra (S : IntermediateField F E) (h : S.toSubalgebra.FG) : S.FG := by
  cases' h with t ht
  exact ⟨t, (eq_adjoin_of_eq_algebra_adjoin _ _ _ ht.symm).symm⟩
#align intermediate_field.fg_of_fg_to_subalgebra IntermediateField.fG_of_fG_toSubalgebra

theorem fg_of_noetherian (S : IntermediateField F E) [IsNoetherian F E] : S.FG :=
  S.fG_of_fG_toSubalgebra S.toSubalgebra.fg_of_noetherian
#align intermediate_field.fg_of_noetherian IntermediateField.fg_of_noetherian

theorem induction_on_adjoin_finset (S : Finset E) (P : IntermediateField F E → Prop) (base : P ⊥)
    (ih : ∀ (K : IntermediateField F E), ∀ x ∈ S, P K → P (K⟮x⟯.restrictScalars F)) :
    P (adjoin F S) := by
  refine' Finset.induction_on' S _ (fun ha _ _ h => _)
  · simp [base]
  · rw [Finset.coe_insert, Set.insert_eq, Set.union_comm, ← adjoin_adjoin_left]
    exact ih (adjoin F _) _ ha h
#align intermediate_field.induction_on_adjoin_finset IntermediateField.induction_on_adjoin_finset

theorem induction_on_adjoin_fg (P : IntermediateField F E → Prop) (base : P ⊥)
    (ih : ∀ (K : IntermediateField F E) (x : E), P K → P (K⟮x⟯.restrictScalars F))
    (K : IntermediateField F E) (hK : K.FG) : P K := by
  obtain ⟨S, rfl⟩ := hK
  exact induction_on_adjoin_finset S P base fun K x _ hK => ih K x hK
#align intermediate_field.induction_on_adjoin_fg IntermediateField.induction_on_adjoin_fg

theorem induction_on_adjoin [FiniteDimensional F E] (P : IntermediateField F E → Prop)
    (base : P ⊥) (ih : ∀ (K : IntermediateField F E) (x : E), P K → P (K⟮x⟯.restrictScalars F))
    (K : IntermediateField F E) : P K :=
  letI : IsNoetherian F E := IsNoetherian.iff_fg.2 inferInstance
  induction_on_adjoin_fg P base ih K K.fg_of_noetherian
#align intermediate_field.induction_on_adjoin IntermediateField.induction_on_adjoin

end Induction

section AlgHomMkAdjoinSplits

variable (F E K : Type*) [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K] {S : Set E}

/-- Lifts `L → K` of `F → K` -/
structure Lifts where
  /-- The domain of a lift. -/
  carrier : IntermediateField F E
  /-- The lifted RingHom, expressed as an AlgHom. -/
  emb : carrier →ₐ[F] K
#align intermediate_field.lifts IntermediateField.Lifts

variable {F E K}

instance : PartialOrder (Lifts F E K) where
  le L₁ L₂ := ∃ h : L₁.carrier ≤ L₂.carrier, ∀ x, L₂.emb (inclusion h x) = L₁.emb x
  le_refl L := ⟨le_rfl, by simp⟩
  le_trans L₁ L₂ L₃ := by
    rintro ⟨h₁₂, h₁₂'⟩ ⟨h₂₃, h₂₃'⟩
    refine ⟨h₁₂.trans h₂₃, fun _ ↦ ?_⟩
    rw [← inclusion_inclusion h₁₂ h₂₃, h₂₃', h₁₂']
  le_antisymm := by
    rintro ⟨L₁, e₁⟩ ⟨L₂, e₂⟩ ⟨h₁₂, h₁₂'⟩ ⟨h₂₁, h₂₁'⟩
    obtain rfl : L₁ = L₂ := h₁₂.antisymm h₂₁
    congr
    exact AlgHom.ext h₂₁'

noncomputable instance : OrderBot (Lifts F E K) where
  bot := ⟨⊥, (Algebra.ofId F K).comp (botEquiv F E)⟩
  bot_le L := ⟨bot_le, fun x ↦ by
    obtain ⟨x, rfl⟩ := (botEquiv F E).symm.surjective x
    simp_rw [AlgHom.comp_apply, AlgHom.coe_coe, AlgEquiv.apply_symm_apply]
    exact L.emb.commutes x⟩

noncomputable instance : Inhabited (Lifts F E K) :=
  ⟨⊥⟩

/-- A chain of lifts has an upper bound. -/
theorem Lifts.exists_upper_bound (c : Set (Lifts F E K)) (hc : IsChain (· ≤ ·) c) :
    ∃ ub, ∀ a ∈ c, a ≤ ub := by
  let t (i : ↑(insert ⊥ c)) := i.val.carrier
  let t' (i) := (t i).toSubalgebra
  have hc := hc.insert fun _ _ _ ↦ .inl bot_le
  have dir : Directed (· ≤ ·) t := hc.directedOn.directed_val.mono_comp _ fun _ _ h ↦ h.1
  refine ⟨⟨iSup t, (Subalgebra.iSupLift t' dir (fun i ↦ i.val.emb) (fun i j h ↦ ?_) _ rfl).comp
      (Subalgebra.equivOfEq _ _ <| toSubalgebra_iSup_of_directed dir)⟩,
    fun L hL ↦ have hL := Set.mem_insert_of_mem ⊥ hL; ⟨le_iSup t ⟨L, hL⟩, fun x ↦ ?_⟩⟩
  · refine AlgHom.ext fun x ↦ (hc.total i.2 j.2).elim (fun hij ↦ (hij.snd x).symm) fun hji ↦ ?_
    erw [AlgHom.comp_apply, ← hji.snd (Subalgebra.inclusion h x),
         inclusion_inclusion, inclusion_self, AlgHom.id_apply x]
  · dsimp only [AlgHom.comp_apply]
    exact Subalgebra.iSupLift_inclusion (K := t') (i := ⟨L, hL⟩) x (le_iSup t' ⟨L, hL⟩)
#align intermediate_field.lifts.exists_upper_bound IntermediateField.Lifts.exists_upper_bound

/-- Given an element `s : E` whose conjugates are all in `K`, any lift can be extended to one
  whose carrier contains `s`. -/
theorem Lifts.exists_lift_of_splits (x : Lifts F E K) {s : E} (h1 : IsIntegral F s)
    (h2 : (minpoly F s).Splits (algebraMap F K)) : ∃ y, x ≤ y ∧ s ∈ y.carrier :=
  have I1 : IsIntegral x.carrier s := isIntegral_of_isScalarTower h1
  have I2 := (minpoly.degree_pos I1).ne'
  have key : (minpoly x.carrier s).Splits x.emb.toRingHom :=
    splits_of_splits_of_dvd _ (map_ne_zero (minpoly.ne_zero h1))
      ((splits_map_iff _ _).2 (x.emb.comp_algebraMap ▸ h2)) (minpoly.dvd_map_of_isScalarTower _ _ _)
  letI : Algebra x.carrier K := x.emb.toRingHom.toAlgebra
  let carrier := x.carrier⟮s⟯.restrictScalars F
  letI : Algebra x.carrier carrier := x.carrier⟮s⟯.toSubalgebra.algebra
  let φ : carrier →ₐ[x.carrier] K := ((algHomAdjoinIntegralEquiv x.carrier I1).symm
    ⟨rootOfSplits x.emb.toRingHom key I2, by
      rw [mem_aroots, and_iff_right (minpoly.ne_zero I1)]
      exact map_rootOfSplits x.emb.toRingHom key I2⟩)
  ⟨⟨carrier, (@algHomEquivSigma F x.carrier carrier K _ _ _ _ _ _ _ _
      (IsScalarTower.of_algebraMap_eq fun _ ↦ rfl)).symm ⟨x.emb, φ⟩⟩,
    ⟨fun z hz ↦ algebraMap_mem x.carrier⟮s⟯ ⟨z, hz⟩, φ.commutes⟩,
    mem_adjoin_simple_self x.carrier s⟩
#align intermediate_field.lifts.exists_lift_of_splits IntermediateField.Lifts.exists_lift_of_splits

variable (hK : ∀ s ∈ S, IsIntegral F s ∧ (minpoly F s).Splits (algebraMap F K))
        (hK' : ∀ s : E, IsIntegral F s ∧ (minpoly F s).Splits (algebraMap F K))
        {L : IntermediateField F E} (f : L →ₐ[F] K) (hL : L ≤ adjoin F S)

-- The following uses the hypothesis `hK`.

theorem exists_algHom_adjoin_of_splits : ∃ φ : adjoin F S →ₐ[F] K, φ.comp (inclusion hL) = f := by
  obtain ⟨φ, hfφ, hφ⟩ := zorn_nonempty_Ici₀ _
    (fun c _ hc _ _ ↦ Lifts.exists_upper_bound c hc) ⟨L, f⟩ le_rfl
  refine ⟨φ.emb.comp (inclusion <| adjoin_le_iff.mpr fun s hs ↦ ?_), ?_⟩
  · rcases φ.exists_lift_of_splits (hK s hs).1 (hK s hs).2 with ⟨y, h1, h2⟩
    exact (hφ y h1).1 h2
  · ext; apply hfφ.2

theorem nonempty_algHom_adjoin_of_splits : Nonempty (adjoin F S →ₐ[F] K) :=
  have ⟨φ, _⟩ := exists_algHom_adjoin_of_splits hK (⊥ : Lifts F E K).emb bot_le; ⟨φ⟩
#align intermediate_field.alg_hom_mk_adjoin_splits IntermediateField.nonempty_algHom_adjoin_of_splits

variable (hS : adjoin F S = ⊤)

theorem exists_algHom_of_adjoin_splits : ∃ φ : E →ₐ[F] K, φ.comp L.val = f :=
  have ⟨φ, hφ⟩ := exists_algHom_adjoin_of_splits hK f (hS.symm ▸ le_top)
  ⟨φ.comp ((equivOfEq hS).trans topEquiv).symm.toAlgHom, hφ⟩

theorem nonempty_algHom_of_adjoin_splits : Nonempty (E →ₐ[F] K) :=
  have ⟨φ, _⟩ := exists_algHom_of_adjoin_splits hK (⊥ : Lifts F E K).emb hS; ⟨φ⟩
#align intermediate_field.alg_hom_mk_adjoin_splits' IntermediateField.nonempty_algHom_of_adjoin_splits

variable {x : E} (hx : x ∈ adjoin F S) {y : K} (hy : aeval y (minpoly F x) = 0)

theorem exists_algHom_adjoin_of_splits_of_aeval : ∃ φ : adjoin F S →ₐ[F] K, φ ⟨x, hx⟩ = y := by
  have ix := isAlgebraic_adjoin (fun s hs ↦ (hK s hs).1) ⟨x, hx⟩
  rw [isAlgebraic_iff_isIntegral, isIntegral_iff] at ix
  obtain ⟨φ, hφ⟩ := exists_algHom_adjoin_of_splits hK ((algHomAdjoinIntegralEquiv F ix).symm
    ⟨y, mem_aroots.mpr ⟨minpoly.ne_zero ix, hy⟩⟩) (adjoin_simple_le_iff.mpr hx)
  exact ⟨φ, (FunLike.congr_fun hφ <| AdjoinSimple.gen F x).trans <|
    algHomAdjoinIntegralEquiv_symm_apply_gen F ix _⟩

theorem exists_algHom_of_adjoin_splits_of_aeval : ∃ φ : E →ₐ[F] K, φ x = y :=
  have ⟨φ, hφ⟩ := exists_algHom_adjoin_of_splits_of_aeval hK (hS ▸ mem_top) hy
  ⟨φ.comp ((equivOfEq hS).trans topEquiv).symm.toAlgHom, hφ⟩

/- The following uses the hypothesis
   (hK' : ∀ s : E, IsIntegral F s ∧ (minpoly F s).Splits (algebraMap F K)) -/

theorem exists_algHom_of_splits : ∃ φ : E →ₐ[F] K, φ.comp L.val = f :=
  exists_algHom_of_adjoin_splits (fun x _ ↦ hK' x) f (adjoin_univ F E)

theorem nonempty_algHom_of_splits : Nonempty (E →ₐ[F] K) :=
  nonempty_algHom_of_adjoin_splits (fun x _ ↦ hK' x) (adjoin_univ F E)

theorem exists_algHom_of_splits_of_aeval : ∃ φ : E →ₐ[F] K, φ x = y :=
  exists_algHom_of_adjoin_splits_of_aeval (fun x _ ↦ hK' x) (adjoin_univ F E) hy

end AlgHomMkAdjoinSplits

end IntermediateField

section PowerBasis

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

namespace PowerBasis

open IntermediateField

/-- `pb.equivAdjoinSimple` is the equivalence between `K⟮pb.gen⟯` and `L` itself. -/
noncomputable def equivAdjoinSimple (pb : PowerBasis K L) : K⟮pb.gen⟯ ≃ₐ[K] L :=
  (adjoin.powerBasis pb.isIntegral_gen).equivOfMinpoly pb <| by
    rw [adjoin.powerBasis_gen, minpoly_gen]
#align power_basis.equiv_adjoin_simple PowerBasis.equivAdjoinSimple

@[simp]
theorem equivAdjoinSimple_aeval (pb : PowerBasis K L) (f : K[X]) :
    pb.equivAdjoinSimple (aeval (AdjoinSimple.gen K pb.gen) f) = aeval pb.gen f :=
  equivOfMinpoly_aeval _ pb _ f
#align power_basis.equiv_adjoin_simple_aeval PowerBasis.equivAdjoinSimple_aeval

@[simp]
theorem equivAdjoinSimple_gen (pb : PowerBasis K L) :
    pb.equivAdjoinSimple (AdjoinSimple.gen K pb.gen) = pb.gen :=
  equivOfMinpoly_gen _ pb _
#align power_basis.equiv_adjoin_simple_gen PowerBasis.equivAdjoinSimple_gen

@[simp]
theorem equivAdjoinSimple_symm_aeval (pb : PowerBasis K L) (f : K[X]) :
    pb.equivAdjoinSimple.symm (aeval pb.gen f) = aeval (AdjoinSimple.gen K pb.gen) f := by
  rw [equivAdjoinSimple, equivOfMinpoly_symm, equivOfMinpoly_aeval, adjoin.powerBasis_gen]
#align power_basis.equiv_adjoin_simple_symm_aeval PowerBasis.equivAdjoinSimple_symm_aeval

@[simp]
theorem equivAdjoinSimple_symm_gen (pb : PowerBasis K L) :
    pb.equivAdjoinSimple.symm pb.gen = AdjoinSimple.gen K pb.gen := by
  rw [equivAdjoinSimple, equivOfMinpoly_symm, equivOfMinpoly_gen, adjoin.powerBasis_gen]
#align power_basis.equiv_adjoin_simple_symm_gen PowerBasis.equivAdjoinSimple_symm_gen

end PowerBasis

end PowerBasis
