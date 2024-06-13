/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
import Mathlib.Algebra.Algebra.Subalgebra.Directed
import Mathlib.FieldTheory.IntermediateField
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.RingTheory.TensorProduct.Basic

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

-- Porting note: not adding `neg_mem'` causes an error.
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
  ⟨fun H => le_trans (le_trans Set.subset_union_right Subfield.subset_closure) H, fun H =>
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

instance : Unique (IntermediateField F F) :=
  { inferInstanceAs (Inhabited (IntermediateField F F)) with
    uniq := fun _ ↦ toSubalgebra_injective <| Subsingleton.elim _ _ }

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
    (equivOfEq hST).trans (equivOfEq hTU) = equivOfEq (hST.trans hTU) :=
  rfl
#align intermediate_field.equiv_of_eq_trans IntermediateField.equivOfEq_trans

variable (F E)

/-- The bottom intermediate_field is isomorphic to the field. -/
noncomputable def botEquiv : (⊥ : IntermediateField F E) ≃ₐ[F] F :=
  (Subalgebra.equivOfEq _ _ bot_toSubalgebra).trans (Algebra.botEquiv F E)
#align intermediate_field.bot_equiv IntermediateField.botEquiv

variable {F E}

-- Porting note: this was tagged `simp`.
theorem botEquiv_def (x : F) : botEquiv F E (algebraMap F (⊥ : IntermediateField F E) x) = x := by
  simp
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

variable {K : Type*} [Field K] [Algebra F K]

@[simp]
theorem map_bot (f : E →ₐ[F] K) :
    IntermediateField.map f ⊥ = ⊥ :=
  toSubalgebra_injective <| Algebra.map_bot _

theorem map_sup (s t : IntermediateField F E) (f : E →ₐ[F] K) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
  (gc_map_comap f).l_sup

theorem map_iSup {ι : Sort*} (f : E →ₐ[F] K) (s : ι → IntermediateField F E) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup

theorem _root_.AlgHom.fieldRange_eq_map (f : E →ₐ[F] K) :
    f.fieldRange = IntermediateField.map f ⊤ :=
  SetLike.ext' Set.image_univ.symm
#align alg_hom.field_range_eq_map AlgHom.fieldRange_eq_map

theorem _root_.AlgHom.map_fieldRange {L : Type*} [Field L] [Algebra F L]
    (f : E →ₐ[F] K) (g : K →ₐ[F] L) : f.fieldRange.map g = (g.comp f).fieldRange :=
  SetLike.ext' (Set.range_comp g f).symm
#align alg_hom.map_field_range AlgHom.map_fieldRange

theorem _root_.AlgHom.fieldRange_eq_top {f : E →ₐ[F] K} :
    f.fieldRange = ⊤ ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans Set.range_iff_surjective
#align alg_hom.field_range_eq_top AlgHom.fieldRange_eq_top

@[simp]
theorem _root_.AlgEquiv.fieldRange_eq_top (f : E ≃ₐ[F] K) :
    (f : E →ₐ[F] K).fieldRange = ⊤ :=
  AlgHom.fieldRange_eq_top.mpr f.surjective
#align alg_equiv.field_range_eq_top AlgEquiv.fieldRange_eq_top

end Lattice

section equivMap

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
  {K : Type*} [Field K] [Algebra F K] (L : IntermediateField F E) (f : E →ₐ[F] K)

theorem fieldRange_comp_val : (f.comp L.val).fieldRange = L.map f := toSubalgebra_injective <| by
  rw [toSubalgebra_map, AlgHom.fieldRange_toSubalgebra, AlgHom.range_comp, range_val]

/-- An intermediate field is isomorphic to its image under an `AlgHom`
(which is automatically injective) -/
noncomputable def equivMap : L ≃ₐ[F] L.map f :=
  (AlgEquiv.ofInjective _ (f.comp L.val).injective).trans (equivOfEq (fieldRange_comp_val L f))

@[simp]
theorem coe_equivMap_apply (x : L) : ↑(equivMap L f x) = f x := rfl

end equivMap

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
  ⟨fun h => ⟨(adjoin.range_algebraMap_subset _ _).trans h,
    (subset_adjoin _ _).trans h⟩, fun ⟨hF, hS⟩ =>
      (Subfield.closure_le (t := (adjoin F' S').toSubfield)).mpr (Set.union_subset hF hS)⟩
#align intermediate_field.adjoin_subset_adjoin_iff IntermediateField.adjoin_subset_adjoin_iff

/-- `F[S][T] = F[S ∪ T]` -/
theorem adjoin_adjoin_left (T : Set E) :
    (adjoin (adjoin F S) T).restrictScalars _ = adjoin F (S ∪ T) := by
  rw [SetLike.ext'_iff]
  change (↑(adjoin (adjoin F S) T) : Set E) = _
  apply Set.eq_of_subset_of_subset <;> rw [adjoin_subset_adjoin_iff] <;> constructor
  · rintro _ ⟨⟨x, hx⟩, rfl⟩; exact adjoin.mono _ _ _ Set.subset_union_left hx
  · exact subset_adjoin_of_subset_right _ _ Set.subset_union_right
-- Porting note: orginal proof times out
  · rintro x ⟨f, rfl⟩
    refine Subfield.subset_closure ?_
    left
    exact ⟨f, rfl⟩
-- Porting note: orginal proof times out
  · refine Set.union_subset (fun x hx => Subfield.subset_closure ?_)
      (fun x hx => Subfield.subset_closure ?_)
    · left
      refine ⟨⟨x, Subfield.subset_closure ?_⟩, rfl⟩
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
    lift (F := K) ⊤ = K := by rw [lift, ← AlgHom.fieldRange_eq_map, fieldRange_val]

@[simp]
theorem adjoin_self (K : IntermediateField F E) :
    adjoin F K = K := le_antisymm (adjoin_le_iff.2 fun _ ↦ id) (subset_adjoin F _)

theorem restrictScalars_adjoin (K : IntermediateField F E) (S : Set E) :
    restrictScalars F (adjoin K S) = adjoin F (K ∪ S) := by
  rw [← adjoin_self _ K, adjoin_adjoin_left, adjoin_self _ K]

variable {F} in
theorem extendScalars_adjoin {K : IntermediateField F E} {S : Set E} (h : K ≤ adjoin F S) :
    extendScalars h = adjoin K S := restrictScalars_injective F <| by
  rw [extendScalars_restrictScalars, restrictScalars_adjoin]
  exact le_antisymm (adjoin.mono F S _ Set.subset_union_right) <| adjoin_le_iff.2 <|
    Set.union_subset h (subset_adjoin F S)

variable {F} in
/-- If `E / L / F` and `E / L' / F` are two field extension towers, `L ≃ₐ[F] L'` is an isomorphism
compatible with `E / L` and `E / L'`, then for any subset `S` of `E`, `L(S)` and `L'(S)` are
equal as intermediate fields of `E / F`. -/
theorem restrictScalars_adjoin_of_algEquiv
    {L L' : Type*} [Field L] [Field L']
    [Algebra F L] [Algebra L E] [Algebra F L'] [Algebra L' E]
    [IsScalarTower F L E] [IsScalarTower F L' E] (i : L ≃ₐ[F] L')
    (hi : algebraMap L E = (algebraMap L' E) ∘ i) (S : Set E) :
    (adjoin L S).restrictScalars F = (adjoin L' S).restrictScalars F := by
  apply_fun toSubfield using (fun K K' h ↦ by
    ext x; change x ∈ K.toSubfield ↔ x ∈ K'.toSubfield; rw [h])
  change Subfield.closure _ = Subfield.closure _
  congr
  ext x
  exact ⟨fun ⟨y, h⟩ ↦ ⟨i y, by rw [← h, hi]; rfl⟩,
    fun ⟨y, h⟩ ↦ ⟨i.symm y, by rw [← h, hi, Function.comp_apply, AlgEquiv.apply_symm_apply]⟩⟩

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
  refine (adjoin_eq_algebra_adjoin F _ ?_).symm
  intro x
  convert K.inv_mem (x := x) <;> rw [← h] <;> rfl
#align intermediate_field.eq_adjoin_of_eq_algebra_adjoin IntermediateField.eq_adjoin_of_eq_algebra_adjoin

theorem adjoin_eq_top_of_algebra (hS : Algebra.adjoin F S = ⊤) : adjoin F S = ⊤ :=
  top_le_iff.mp (hS.symm.trans_le <| algebra_adjoin_le_adjoin F S)

@[elab_as_elim]
theorem adjoin_induction {s : Set E} {p : E → Prop} {x} (h : x ∈ adjoin F s) (mem : ∀ x ∈ s, p x)
    (algebraMap : ∀ x, p (algebraMap F E x)) (add : ∀ x y, p x → p y → p (x + y))
    (neg : ∀ x, p x → p (-x)) (inv : ∀ x, p x → p x⁻¹) (mul : ∀ x y, p x → p y → p (x * y)) :
    p x :=
  Subfield.closure_induction h
    (fun x hx => Or.casesOn hx (fun ⟨x, hx⟩ => hx ▸ algebraMap x) (mem x))
    ((_root_.algebraMap F E).map_one ▸ algebraMap 1) add neg inv mul
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
theorem AdjoinSimple.coe_gen : (AdjoinSimple.gen F α : E) = α :=
  rfl

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
  have : IsField (Algebra.adjoin F S) := isField_of_isIntegral_of_isField' (Field.toIsField F)
  rw [← ((Algebra.adjoin F S).toIntermediateField' this).eq_adjoin_of_eq_algebra_adjoin F S] <;> rfl
#align intermediate_field.adjoin_algebraic_to_subalgebra IntermediateField.adjoin_algebraic_toSubalgebra

theorem adjoin_simple_toSubalgebra_of_integral (hα : IsIntegral F α) :
    F⟮α⟯.toSubalgebra = Algebra.adjoin F {α} := by
  apply adjoin_algebraic_toSubalgebra
  rintro x (rfl : x = α)
  rwa [isAlgebraic_iff_isIntegral]
#align intermediate_field.adjoin_simple_to_subalgebra_of_integral IntermediateField.adjoin_simple_toSubalgebra_of_integral

/-- Characterize `IsSplittingField` with `IntermediateField.adjoin` instead of `Algebra.adjoin`. -/
theorem _root_.isSplittingField_iff_intermediateField {p : F[X]} :
    p.IsSplittingField F E ↔ p.Splits (algebraMap F E) ∧ adjoin F (p.rootSet E) = ⊤ := by
  rw [← toSubalgebra_injective.eq_iff,
      adjoin_algebraic_toSubalgebra fun _ ↦ isAlgebraic_of_mem_rootSet]
  exact ⟨fun ⟨spl, adj⟩ ↦ ⟨spl, adj⟩, fun ⟨spl, adj⟩ ↦ ⟨spl, adj⟩⟩

-- Note: p.Splits (algebraMap F E) also works
theorem isSplittingField_iff {p : F[X]} {K : IntermediateField F E} :
    p.IsSplittingField F K ↔ p.Splits (algebraMap F K) ∧ K = adjoin F (p.rootSet E) := by
  suffices _ → (Algebra.adjoin F (p.rootSet K) = ⊤ ↔ K = adjoin F (p.rootSet E)) by
    exact ⟨fun h ↦ ⟨h.1, (this h.1).mp h.2⟩, fun h ↦ ⟨h.1, (this h.1).mpr h.2⟩⟩
  rw [← toSubalgebra_injective.eq_iff,
      adjoin_algebraic_toSubalgebra fun x ↦ isAlgebraic_of_mem_rootSet]
  refine fun hp ↦ (adjoin_rootSet_eq_range hp K.val).symm.trans ?_
  rw [← K.range_val, eq_comm]
#align intermediate_field.is_splitting_field_iff IntermediateField.isSplittingField_iff

theorem adjoin_rootSet_isSplittingField {p : F[X]} (hp : p.Splits (algebraMap F E)) :
    p.IsSplittingField F (adjoin F (p.rootSet E)) :=
  isSplittingField_iff.mpr ⟨splits_of_splits hp fun _ hx ↦ subset_adjoin F (p.rootSet E) hx, rfl⟩
#align intermediate_field.adjoin_root_set_is_splitting_field IntermediateField.adjoin_rootSet_isSplittingField

section Supremum

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (E1 E2 : IntermediateField K L)

theorem le_sup_toSubalgebra : E1.toSubalgebra ⊔ E2.toSubalgebra ≤ (E1 ⊔ E2).toSubalgebra :=
  sup_le (show E1 ≤ E1 ⊔ E2 from le_sup_left) (show E2 ≤ E1 ⊔ E2 from le_sup_right)
#align intermediate_field.le_sup_to_subalgebra IntermediateField.le_sup_toSubalgebra

theorem sup_toSubalgebra_of_isAlgebraic_right [Algebra.IsAlgebraic K E2] :
    (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra := by
  have : (adjoin E1 (E2 : Set L)).toSubalgebra = _ := adjoin_algebraic_toSubalgebra fun x h ↦
    IsAlgebraic.tower_top E1 (isAlgebraic_iff.1
      (Algebra.IsAlgebraic.isAlgebraic (⟨x, h⟩ : E2)))
  apply_fun Subalgebra.restrictScalars K at this
  erw [← restrictScalars_toSubalgebra, restrictScalars_adjoin,
    Algebra.restrictScalars_adjoin] at this
  exact this

theorem sup_toSubalgebra_of_isAlgebraic_left [Algebra.IsAlgebraic K E1] :
    (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra := by
  have := sup_toSubalgebra_of_isAlgebraic_right E2 E1
  rwa [sup_comm (a := E1), sup_comm (a := E1.toSubalgebra)]

/-- The compositum of two intermediate fields is equal to the compositum of them
as subalgebras, if one of them is algebraic over the base field. -/
theorem sup_toSubalgebra_of_isAlgebraic
    (halg : Algebra.IsAlgebraic K E1 ∨ Algebra.IsAlgebraic K E2) :
    (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra :=
  halg.elim (fun _ ↦ sup_toSubalgebra_of_isAlgebraic_left E1 E2)
    (fun _ ↦ sup_toSubalgebra_of_isAlgebraic_right E1 E2)

theorem sup_toSubalgebra_of_left [FiniteDimensional K E1] :
    (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra :=
  sup_toSubalgebra_of_isAlgebraic_left E1 E2
#align intermediate_field.sup_to_subalgebra IntermediateField.sup_toSubalgebra_of_left

@[deprecated (since := "2024-01-19")] alias sup_toSubalgebra := sup_toSubalgebra_of_left

theorem sup_toSubalgebra_of_right [FiniteDimensional K E2] :
    (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra :=
  sup_toSubalgebra_of_isAlgebraic_right E1 E2

instance finiteDimensional_sup [FiniteDimensional K E1] [FiniteDimensional K E2] :
    FiniteDimensional K (E1 ⊔ E2 : IntermediateField K L) := by
  let g := Algebra.TensorProduct.productMap E1.val E2.val
  suffices g.range = (E1 ⊔ E2).toSubalgebra by
    have h : FiniteDimensional K (Subalgebra.toSubmodule g.range) :=
      g.toLinearMap.finiteDimensional_range
    rwa [this] at h
  rw [Algebra.TensorProduct.productMap_range, E1.range_val, E2.range_val, sup_toSubalgebra_of_left]
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
  all_goals dsimp only [P]
  · exact Set.finite_univ
  · rw [iSup_emptyset]
    exact (botEquiv K L).symm.toLinearEquiv.finiteDimensional
  · intro _ s _ _ hs
    rw [iSup_insert]
    exact IntermediateField.finiteDimensional_sup _ _
#align intermediate_field.finite_dimensional_supr_of_finite IntermediateField.finiteDimensional_iSup_of_finite

instance finiteDimensional_iSup_of_finset
    /- Porting note: changed `h` from `∀ i ∈ s, FiniteDimensional K (t i)` because this caused an
      error. See `finiteDimensional_iSup_of_finset'` for a stronger version, that was the one
      used in mathlib3. -/
    {s : Finset ι} [∀ i, FiniteDimensional K (t i)] :
    FiniteDimensional K (⨆ i ∈ s, t i : IntermediateField K L) :=
  iSup_subtype'' s t ▸ IntermediateField.finiteDimensional_iSup_of_finite
#align intermediate_field.finite_dimensional_supr_of_finset IntermediateField.finiteDimensional_iSup_of_finset

theorem finiteDimensional_iSup_of_finset'
    /- Porting note: this was the mathlib3 version. Using `[h : ...]`, as in mathlib3, causes the
    error "invalid parametric local instance". -/
    {s : Finset ι} (h : ∀ i ∈ s, FiniteDimensional K (t i)) :
    FiniteDimensional K (⨆ i ∈ s, t i : IntermediateField K L) :=
  have := Subtype.forall'.mp h
  iSup_subtype'' s t ▸ IntermediateField.finiteDimensional_iSup_of_finite

/-- A compositum of splitting fields is a splitting field -/
theorem isSplittingField_iSup {p : ι → K[X]}
    {s : Finset ι} (h0 : ∏ i ∈ s, p i ≠ 0) (h : ∀ i ∈ s, (p i).IsSplittingField K (t i)) :
    (∏ i ∈ s, p i).IsSplittingField K (⨆ i ∈ s, t i : IntermediateField K L) := by
  let F : IntermediateField K L := ⨆ i ∈ s, t i
  have hF : ∀ i ∈ s, t i ≤ F := fun i hi ↦ le_iSup_of_le i (le_iSup (fun _ ↦ t i) hi)
  simp only [isSplittingField_iff] at h ⊢
  refine
    ⟨splits_prod (algebraMap K F) fun i hi ↦
        splits_comp_of_splits (algebraMap K (t i)) (inclusion (hF i hi)).toRingHom
          (h i hi).1,
      ?_⟩
  simp only [rootSet_prod p s h0, ← Set.iSup_eq_iUnion, (@gc K _ L _ _).l_iSup₂]
  exact iSup_congr fun i ↦ iSup_congr fun hi ↦ (h i hi).2
#align intermediate_field.is_splitting_field_supr IntermediateField.isSplittingField_iSup

end Supremum

section Tower

variable (E)
variable {K : Type*} [Field K] [Algebra F K] [Algebra E K] [IsScalarTower F E K]

/-- If `K / E / F` is a field extension tower, `L` is an intermediate field of `K / F`, such that
either `E / F` or `L / F` is algebraic, then `E(L) = E[L]`. -/
theorem adjoin_toSubalgebra_of_isAlgebraic (L : IntermediateField F K)
    (halg : Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebraic F L) :
    (adjoin E (L : Set K)).toSubalgebra = Algebra.adjoin E (L : Set K) := by
  let i := IsScalarTower.toAlgHom F E K
  let E' := i.fieldRange
  let i' : E ≃ₐ[F] E' := AlgEquiv.ofInjectiveField i
  have hi : algebraMap E K = (algebraMap E' K) ∘ i' := by ext x; rfl
  apply_fun _ using Subalgebra.restrictScalars_injective F
  erw [← restrictScalars_toSubalgebra, restrictScalars_adjoin_of_algEquiv i' hi,
    Algebra.restrictScalars_adjoin_of_algEquiv i' hi, restrictScalars_adjoin,
    Algebra.restrictScalars_adjoin]
  exact E'.sup_toSubalgebra_of_isAlgebraic L (halg.imp
    (fun (_ : Algebra.IsAlgebraic F E) ↦ i'.isAlgebraic) id)

theorem adjoin_toSubalgebra_of_isAlgebraic_left (L : IntermediateField F K)
    [halg : Algebra.IsAlgebraic F E] :
    (adjoin E (L : Set K)).toSubalgebra = Algebra.adjoin E (L : Set K) :=
  adjoin_toSubalgebra_of_isAlgebraic E L (Or.inl halg)

theorem adjoin_toSubalgebra_of_isAlgebraic_right (L : IntermediateField F K)
    [halg : Algebra.IsAlgebraic F L] :
    (adjoin E (L : Set K)).toSubalgebra = Algebra.adjoin E (L : Set K) :=
  adjoin_toSubalgebra_of_isAlgebraic E L (Or.inr halg)

/-- If `K / E / F` is a field extension tower, `L` is an intermediate field of `K / F`, such that
either `E / F` or `L / F` is algebraic, then `[E(L) : E] ≤ [L : F]`. A corollary of
`Subalgebra.adjoin_rank_le` since in this case `E(L) = E[L]`. -/
theorem adjoin_rank_le_of_isAlgebraic (L : IntermediateField F K)
    (halg : Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebraic F L) :
    Module.rank E (adjoin E (L : Set K)) ≤ Module.rank F L := by
  have h : (adjoin E (L.toSubalgebra : Set K)).toSubalgebra =
      Algebra.adjoin E (L.toSubalgebra : Set K) :=
    L.adjoin_toSubalgebra_of_isAlgebraic E halg
  have := L.toSubalgebra.adjoin_rank_le E
  rwa [(Subalgebra.equivOfEq _ _ h).symm.toLinearEquiv.rank_eq] at this

theorem adjoin_rank_le_of_isAlgebraic_left (L : IntermediateField F K)
    [halg : Algebra.IsAlgebraic F E] :
    Module.rank E (adjoin E (L : Set K)) ≤ Module.rank F L :=
  adjoin_rank_le_of_isAlgebraic E L (Or.inl halg)

theorem adjoin_rank_le_of_isAlgebraic_right (L : IntermediateField F K)
    [halg : Algebra.IsAlgebraic F L] :
    Module.rank E (adjoin E (L : Set K)) ≤ Module.rank F L :=
  adjoin_rank_le_of_isAlgebraic E L (Or.inr halg)

end Tower

open Set CompleteLattice

/- Porting note: this was tagged `simp`, but the LHS can be simplified now that the notation
has been improved. -/
theorem adjoin_simple_le_iff {K : IntermediateField F E} : F⟮α⟯ ≤ K ↔ α ∈ K := by simp
#align intermediate_field.adjoin_simple_le_iff IntermediateField.adjoin_simple_le_iff

theorem biSup_adjoin_simple : ⨆ x ∈ S, F⟮x⟯ = adjoin F S := by
  rw [← iSup_subtype'', ← gc.l_iSup, iSup_subtype'']; congr; exact S.biUnion_of_singleton

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
  exact isCompactElement_finsetSup S fun x _ => adjoin_simple_isCompactElement x
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
  have := (adjoin_simple_isCompactElement x).exists_finset_of_le_iSup (IntermediateField F E) f
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
  refine exists_finset_of_mem_iSup (SetLike.le_def.mp (iSup_le (fun i => ?_)) hx)
  intro x1 hx1
  refine SetLike.le_def.mp (le_iSup_of_le ⟨i, x1, hx1⟩ ?_)
    (subset_adjoin F (rootSet (minpoly F x1) E) ?_)
  · rw [IntermediateField.minpoly_eq, Subtype.coe_mk]
  · rw [mem_rootSet_of_ne, minpoly.aeval]
    exact minpoly.ne_zero (isIntegral_iff.mp (Algebra.IsIntegral.isIntegral (⟨x1, hx1⟩ : f i)))
#align intermediate_field.exists_finset_of_mem_supr'' IntermediateField.exists_finset_of_mem_supr''

theorem exists_finset_of_mem_adjoin {S : Set E} {x : E} (hx : x ∈ adjoin F S) :
    ∃ T : Finset E, (T : Set E) ⊆ S ∧ x ∈ adjoin F (T : Set E) := by
  simp_rw [← biSup_adjoin_simple S, ← iSup_subtype''] at hx
  obtain ⟨s, hx'⟩ := exists_finset_of_mem_iSup hx
  refine ⟨s.image Subtype.val, by simp, SetLike.le_def.mp ?_ hx'⟩
  simp_rw [Finset.coe_image, iSup_le_iff, adjoin_le_iff]
  rintro _ h _ rfl
  exact subset_adjoin F _ ⟨_, h, rfl⟩

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
theorem adjoin_intCast (n : ℤ) : F⟮(n : E)⟯ = ⊥ := by
  exact adjoin_simple_eq_bot_iff.mpr (intCast_mem ⊥ n)
#align intermediate_field.adjoin_int IntermediateField.adjoin_intCast

@[simp]
theorem adjoin_natCast (n : ℕ) : F⟮(n : E)⟯ = ⊥ :=
  adjoin_simple_eq_bot_iff.mpr (natCast_mem ⊥ n)
#align intermediate_field.adjoin_nat IntermediateField.adjoin_natCast

@[deprecated (since := "2024-04-05")] alias adjoin_int := adjoin_intCast
@[deprecated (since := "2024-04-05")] alias adjoin_nat := adjoin_natCast

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

@[simp] protected
theorem rank_bot : Module.rank F (⊥ : IntermediateField F E) = 1 := by rw [rank_eq_one_iff]
#align intermediate_field.rank_bot IntermediateField.rank_bot

@[simp] protected
theorem finrank_bot : finrank F (⊥ : IntermediateField F E) = 1 := by rw [finrank_eq_one_iff]
#align intermediate_field.finrank_bot IntermediateField.finrank_bot

@[simp] theorem rank_bot' : Module.rank (⊥ : IntermediateField F E) E = Module.rank F E := by
  rw [← rank_mul_rank F (⊥ : IntermediateField F E) E, IntermediateField.rank_bot, one_mul]

@[simp] theorem finrank_bot' : finrank (⊥ : IntermediateField F E) E = finrank F E :=
  congr(Cardinal.toNat $(rank_bot'))

@[simp] protected theorem rank_top : Module.rank (⊤ : IntermediateField F E) E = 1 :=
  Subalgebra.bot_eq_top_iff_rank_eq_one.mp <| top_le_iff.mp fun x _ ↦ ⟨⟨x, trivial⟩, rfl⟩

@[simp] protected theorem finrank_top : finrank (⊤ : IntermediateField F E) E = 1 :=
  rank_eq_one_iff_finrank_eq_one.mp IntermediateField.rank_top

@[simp] theorem rank_top' : Module.rank F (⊤ : IntermediateField F E) = Module.rank F E :=
  rank_top F E

@[simp] theorem finrank_top' : finrank F (⊤ : IntermediateField F E) = finrank F E :=
  finrank_top F E

theorem rank_adjoin_eq_one_iff : Module.rank F (adjoin F S) = 1 ↔ S ⊆ (⊥ : IntermediateField F E) :=
  Iff.trans rank_eq_one_iff adjoin_eq_bot_iff
#align intermediate_field.rank_adjoin_eq_one_iff IntermediateField.rank_adjoin_eq_one_iff

theorem rank_adjoin_simple_eq_one_iff :
    Module.rank F F⟮α⟯ = 1 ↔ α ∈ (⊥ : IntermediateField F E) := by
  rw [rank_adjoin_eq_one_iff]; exact Set.singleton_subset_iff
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

universe u

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] {α : E}
variable {K : Type u} [Field K] [Algebra F K]

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

-- Porting note: original proof used `Exists.cases_on`.
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
          obtain ⟨y, hy⟩ := this (Subtype.mem x)
          exact ⟨y, Subtype.ext hy⟩
        refine Subfield.closure_le.mpr (Set.union_subset (fun x hx => ?_) ?_)
        · obtain ⟨y, hy⟩ := hx
          refine ⟨y, ?_⟩
          -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
          erw [RingHom.comp_apply, AdjoinRoot.lift_of (aeval_gen_minpoly F α)]
          exact hy
        · refine Set.singleton_subset_iff.mpr ⟨AdjoinRoot.root (minpoly F α), ?_⟩
          -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
          erw [RingHom.comp_apply, AdjoinRoot.lift_root (aeval_gen_minpoly F α)]
          rfl)
#align intermediate_field.adjoin_root_equiv_adjoin IntermediateField.adjoinRootEquivAdjoin

theorem adjoinRootEquivAdjoin_apply_root (h : IsIntegral F α) :
    adjoinRootEquivAdjoin F h (AdjoinRoot.root (minpoly F α)) = AdjoinSimple.gen F α :=
  AdjoinRoot.lift_root (aeval_gen_minpoly F α)
#align intermediate_field.adjoin_root_equiv_adjoin_apply_root IntermediateField.adjoinRootEquivAdjoin_apply_root

theorem adjoin_root_eq_top (p : K[X]) [Fact (Irreducible p)] : K⟮AdjoinRoot.root p⟯ = ⊤ :=
  (eq_adjoin_of_eq_algebra_adjoin K _ ⊤ (AdjoinRoot.adjoinRoot_eq_top (f := p)).symm).symm

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
  (adjoin.powerBasis hx).finite
#align intermediate_field.adjoin.finite_dimensional IntermediateField.adjoin.finiteDimensional

theorem isAlgebraic_adjoin_simple {x : L} (hx : IsIntegral K x) : Algebra.IsAlgebraic K K⟮x⟯ :=
  have := adjoin.finiteDimensional hx; Algebra.IsAlgebraic.of_finite K K⟮x⟯

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
    adjoin F ((minpoly K α).map (algebraMap K E)).coeffs = K := by
  set g := (minpoly K α).map (algebraMap K E)
  set K' : IntermediateField F E := adjoin F g.coeffs
  have hsub : K' ≤ K := by
    refine adjoin_le_iff.mpr fun x ↦ ?_
    rw [Finset.mem_coe, mem_coeffs_iff]
    rintro ⟨n, -, rfl⟩
    rw [coeff_map]
    apply Subtype.mem
  have dvd_g : minpoly K' α ∣ g.toSubring K'.toSubring (subset_adjoin F _) := by
    apply minpoly.dvd
    erw [aeval_def, eval₂_eq_eval_map, g.map_toSubring K'.toSubring, eval_map, ← aeval_def]
    exact minpoly.aeval K α
  have finrank_eq : ∀ K : IntermediateField F E, finrank K E = natDegree (minpoly K α) := by
    intro K
    have := adjoin.finrank (.of_finite K α)
    erw [adjoin_eq_top_of_adjoin_eq_top F hprim, finrank_top K E] at this
    exact this
  refine eq_of_le_of_finrank_le' hsub ?_
  simp_rw [finrank_eq]
  convert natDegree_le_of_dvd dvd_g
    ((g.monic_toSubring _ _).mpr <| (minpoly.monic <| .of_finite K α).map _).ne_zero using 1
  rw [natDegree_toSubring, natDegree_map]

variable {F} in
/-- If `E / F` is an infinite algebraic extension, then there exists an intermediate field
`L / F` with arbitrarily large finite extension degree. -/
theorem exists_lt_finrank_of_infinite_dimensional
    [Algebra.IsAlgebraic F E] (hnfd : ¬ FiniteDimensional F E) (n : ℕ) :
    ∃ L : IntermediateField F E, FiniteDimensional F L ∧ n < finrank F L := by
  induction' n with n ih
  · exact ⟨⊥, Subalgebra.finite_bot, finrank_pos⟩
  obtain ⟨L, fin, hn⟩ := ih
  obtain ⟨x, hx⟩ : ∃ x : E, x ∉ L := by
    contrapose! hnfd
    rw [show L = ⊤ from eq_top_iff.2 fun x _ ↦ hnfd x] at fin
    exact topEquiv.toLinearEquiv.finiteDimensional
  let L' := L ⊔ F⟮x⟯
  haveI := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := F) x)
  refine ⟨L', inferInstance, by_contra fun h ↦ ?_⟩
  have h1 : L = L' := eq_of_le_of_finrank_le le_sup_left ((not_lt.1 h).trans hn)
  have h2 : F⟮x⟯ ≤ L' := le_sup_right
  exact hx <| (h1.symm ▸ h2) <| mem_adjoin_simple_self F x

theorem _root_.minpoly.natDegree_le (x : L) [FiniteDimensional K L] :
    (minpoly K x).natDegree ≤ finrank K L :=
  le_of_eq_of_le (IntermediateField.adjoin.finrank (.of_finite _ _)).symm
    K⟮x⟯.toSubmodule.finrank_le
#align minpoly.nat_degree_le minpoly.natDegree_le

theorem _root_.minpoly.degree_le (x : L) [FiniteDimensional K L] :
    (minpoly K x).degree ≤ finrank K L :=
  degree_le_of_natDegree_le (minpoly.natDegree_le x)
#align minpoly.degree_le minpoly.degree_le

-- TODO: generalize to `Sort`
/-- A compositum of algebraic extensions is algebraic -/
theorem isAlgebraic_iSup {ι : Type*} {t : ι → IntermediateField K L}
    (h : ∀ i, Algebra.IsAlgebraic K (t i)) :
    Algebra.IsAlgebraic K (⨆ i, t i : IntermediateField K L) := by
  constructor
  rintro ⟨x, hx⟩
  obtain ⟨s, hx⟩ := exists_finset_of_mem_supr' hx
  rw [isAlgebraic_iff, Subtype.coe_mk, ← Subtype.coe_mk (p := (· ∈ _)) x hx, ← isAlgebraic_iff]
  haveI : ∀ i : Σ i, t i, FiniteDimensional K K⟮(i.2 : L)⟯ := fun ⟨i, x⟩ ↦
    adjoin.finiteDimensional (isIntegral_iff.1 (Algebra.IsIntegral.isIntegral x))
  apply IsAlgebraic.of_finite
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

-- Apparently `K⟮root f⟯ →+* K⟮root f⟯` is expensive to unify during instance synthesis.
open FiniteDimensional AdjoinRoot in
/-- Let `f, g` be monic polynomials over `K`. If `f` is irreducible, and `g(x) - α` is irreducible
in `K⟮α⟯` with `α` a root of `f`, then `f(g(x))` is irreducible. -/
theorem _root_.Polynomial.irreducible_comp {f g : K[X]} (hfm : f.Monic) (hgm : g.Monic)
    (hf : Irreducible f)
    (hg : ∀ (E : Type u) [Field E] [Algebra K E] (x : E) (hx : minpoly K x = f),
      Irreducible (g.map (algebraMap _ _) - C (AdjoinSimple.gen K x))) :
    Irreducible (f.comp g) := by
  have hf' : natDegree f ≠ 0 :=
    fun e ↦ not_irreducible_C (f.coeff 0) (eq_C_of_natDegree_eq_zero e ▸ hf)
  have hg' : natDegree g ≠ 0 := by
    have := Fact.mk hf
    intro e
    apply not_irreducible_C ((g.map (algebraMap _ _)).coeff 0 - AdjoinSimple.gen K (root f))
    -- Needed to specialize `map_sub` to avoid a timeout #8386
    rw [RingHom.map_sub, coeff_map, ← map_C, ← eq_C_of_natDegree_eq_zero e]
    apply hg (AdjoinRoot f)
    rw [AdjoinRoot.minpoly_root hf.ne_zero, hfm, inv_one, map_one, mul_one]
  have H₁ : f.comp g ≠ 0 := fun h ↦ by simpa [hf', hg', natDegree_comp] using congr_arg natDegree h
  have H₂ : ¬ IsUnit (f.comp g) := fun h ↦
    by simpa [hf', hg', natDegree_comp] using natDegree_eq_zero_of_isUnit h
  have ⟨p, hp₁, hp₂⟩ := WfDvdMonoid.exists_irreducible_factor H₂ H₁
  suffices natDegree p = natDegree f * natDegree g from (associated_of_dvd_of_natDegree_le hp₂ H₁
    (this.trans natDegree_comp.symm).ge).irreducible hp₁
  have := Fact.mk hp₁
  let Kx := AdjoinRoot p
  letI := (AdjoinRoot.powerBasis hp₁.ne_zero).finite
  have key₁ : f = minpoly K (aeval (root p) g) := by
    refine minpoly.eq_of_irreducible_of_monic hf ?_ hfm
    rw [← aeval_comp]
    exact aeval_eq_zero_of_dvd_aeval_eq_zero hp₂ (AdjoinRoot.eval₂_root p)
  have key₁' : finrank K K⟮aeval (root p) g⟯ = natDegree f := by
    rw [adjoin.finrank, ← key₁]
    exact IsIntegral.of_finite _ _
  have key₂ : g.map (algebraMap _ _) - C (AdjoinSimple.gen K (aeval (root p) g)) =
      minpoly K⟮aeval (root p) g⟯ (root p) :=
    minpoly.eq_of_irreducible_of_monic (hg _ _ key₁.symm) (by simp [AdjoinSimple.gen])
      (Monic.sub_of_left (hgm.map _) (degree_lt_degree (by simpa [Nat.pos_iff_ne_zero] using hg')))
  have key₂' : finrank K⟮aeval (root p) g⟯ Kx = natDegree g := by
    trans natDegree (minpoly K⟮aeval (root p) g⟯ (root p))
    · have : K⟮aeval (root p) g⟯⟮root p⟯ = ⊤ := by
        apply restrictScalars_injective K
        rw [restrictScalars_top, adjoin_adjoin_left, Set.union_comm, ← adjoin_adjoin_left,
          adjoin_root_eq_top p, restrictScalars_adjoin]
        simp
      rw [← finrank_top', ← this, adjoin.finrank]
      exact IsIntegral.of_finite _ _
    · simp [← key₂]
  have := FiniteDimensional.finrank_mul_finrank K K⟮aeval (root p) g⟯ Kx
  rwa [key₁', key₂', (AdjoinRoot.powerBasis hp₁.ne_zero).finrank, powerBasis_dim, eq_comm] at this

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
  -- Porting note: was `⟨∅, adjoin_empty F E⟩`
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
  refine Finset.induction_on' S ?_ (fun ha _ _ h => ?_)
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

end IntermediateField

section Minpoly

open AlgEquiv

variable {K L : Type _} [Field K] [Field L] [Algebra K L]
namespace AdjoinRoot

/-- The canonical algebraic equivalence between `AdjoinRoot p` and `AdjoinRoot q`, where
  the two polynomial `p q : K[X]` are equal.-/
noncomputable def algHomOfDvd {p q : K[X]} (hpq : q ∣ p) :
    AdjoinRoot p →ₐ[K] AdjoinRoot q :=
  (liftHom p (root q) (by simp only [aeval_eq, mk_eq_zero, hpq]))

theorem coe_algHomOfDvd {p q : K[X]} (hpq : q ∣ p) :
    (algHomOfDvd hpq).toFun = liftHom p (root q) (by simp only [aeval_eq, mk_eq_zero, hpq]) :=
  rfl

/-- `algHomOfDvd` sends `AdjoinRoot.root p` to `AdjoinRoot.root q`. -/
theorem algHomOfDvd_apply_root {p q : K[X]} (hpq : q ∣ p) :
    algHomOfDvd hpq (root p) = root q := by
  rw [algHomOfDvd, liftHom_root]

/-- The canonical algebraic equivalence between `AdjoinRoot p` and `AdjoinRoot q`, where
  the two polynomial `p q : K[X]` are equal.-/
noncomputable def algEquivOfEq {p q : K[X]} (hp : p ≠ 0) (h_eq : p = q) :
    AdjoinRoot p ≃ₐ[K] AdjoinRoot q :=
  ofAlgHom (algHomOfDvd (dvd_of_eq h_eq.symm)) (algHomOfDvd (dvd_of_eq h_eq))
    (PowerBasis.algHom_ext (powerBasis (h_eq ▸ hp))
      (by rw [algHomOfDvd, powerBasis_gen (h_eq ▸ hp), AlgHom.coe_comp, Function.comp_apply,
        algHomOfDvd, liftHom_root, liftHom_root, AlgHom.coe_id, id_eq]))
    (PowerBasis.algHom_ext (powerBasis hp)
      (by rw [algHomOfDvd, powerBasis_gen hp, AlgHom.coe_comp, Function.comp_apply, algHomOfDvd,
          liftHom_root, liftHom_root, AlgHom.coe_id, id_eq]))

theorem coe_algEquivOfEq {p q : K[X]} (hp : p ≠ 0) (h_eq : p = q) :
    (algEquivOfEq hp h_eq).toFun = liftHom p (root q) (by rw [h_eq, aeval_eq, mk_self]) :=
  rfl

theorem algEquivOfEq_toAlgHom {p q : K[X]} (hp : p ≠ 0) (h_eq : p = q) :
    (algEquivOfEq hp h_eq).toAlgHom = liftHom p (root q) (by rw [h_eq, aeval_eq, mk_self]) :=
  rfl

/-- `algEquivOfEq` sends `AdjoinRoot.root p` to `AdjoinRoot.root q`. -/
theorem algEquivOfEq_apply_root {p q : K[X]} (hp : p ≠ 0) (h_eq : p = q) :
    algEquivOfEq hp h_eq (root p) = root q := by
  rw [← coe_algHom, algEquivOfEq_toAlgHom, liftHom_root]

/-- The canonical algebraic equivalence between `AdjoinRoot p` and `AdjoinRoot q`, where
  the two polynomial `p q : K[X]` are associated.-/
noncomputable def algEquivOfAssociated {p q : K[X]} (hp : p ≠ 0) (hpq : Associated p q) :
    AdjoinRoot p ≃ₐ[K] AdjoinRoot q :=
  ofAlgHom (liftHom p (root q) (by simp only [aeval_eq, mk_eq_zero, hpq.symm.dvd] ))
    (liftHom q (root p) (by simp only [aeval_eq, mk_eq_zero, hpq.dvd]))
    ( PowerBasis.algHom_ext (powerBasis (hpq.ne_zero_iff.mp hp))
        (by rw [powerBasis_gen (hpq.ne_zero_iff.mp hp), AlgHom.coe_comp, Function.comp_apply,
          liftHom_root, liftHom_root, AlgHom.coe_id, id_eq]))
    (PowerBasis.algHom_ext (powerBasis hp)
      (by rw [powerBasis_gen hp, AlgHom.coe_comp, Function.comp_apply, liftHom_root, liftHom_root,
          AlgHom.coe_id, id_eq]))

theorem coe_algEquivOfAssociated {p q : K[X]} (hp : p ≠ 0) (hpq : Associated p q) :
    (algEquivOfAssociated hp hpq).toFun =
      liftHom p (root q) (by simp only [aeval_eq, mk_eq_zero, hpq.symm.dvd]) :=
  rfl

theorem algEquivOfAssociated_toAlgHom {p q : K[X]} (hp : p ≠ 0) (hpq : Associated p q) :
    (algEquivOfAssociated hp hpq).toAlgHom =
      liftHom p (root q) (by simp only [aeval_eq, mk_eq_zero, hpq.symm.dvd]) :=
  rfl

/-- `algEquivOfAssociated` sends `AdjoinRoot.root p` to `AdjoinRoot.root q`. -/
theorem algEquivOfAssociated_apply_root {p q : K[X]} (hp : p ≠ 0) (hpq : Associated p q) :
    algEquivOfAssociated hp hpq (root p) = root q := by
  rw [← coe_algHom, algEquivOfAssociated_toAlgHom, liftHom_root]

end AdjoinRoot

namespace minpoly

open IntermediateField

/-- If `y : L` is a root of `minpoly K x`, then `minpoly K y = minpoly K x`. -/
theorem eq_of_root {x y : L} (hx : IsAlgebraic K x)
    (h_ev : (Polynomial.aeval y) (minpoly K x) = 0) : minpoly K y = minpoly K x := by
  have hy : IsAlgebraic K y := ⟨minpoly K x, ne_zero hx.isIntegral, h_ev⟩
  exact Polynomial.eq_of_monic_of_associated (monic hy.isIntegral) (monic hx.isIntegral)
    (Irreducible.associated_of_dvd (irreducible hy.isIntegral)
      (irreducible hx.isIntegral) (dvd K y h_ev))

/-- The canonical `algEquiv` between `K⟮x⟯`and `K⟮y⟯`, sending `x` to `y`, where `x` and `y` have
  the same minimal polynomial over `K`. -/
noncomputable def algEquiv {x y : L} (hx : IsAlgebraic K x)
    (h_mp : minpoly K x = minpoly K y) : K⟮x⟯ ≃ₐ[K] K⟮y⟯ := by
  have hy : IsAlgebraic K y := ⟨minpoly K x, ne_zero hx.isIntegral, (h_mp ▸ aeval _ _)⟩
  exact AlgEquiv.trans (adjoinRootEquivAdjoin K hx.isIntegral).symm
    (AlgEquiv.trans (AdjoinRoot.algEquivOfEq (ne_zero hx.isIntegral) h_mp)
      (adjoinRootEquivAdjoin K hy.isIntegral))

/-- `minpoly.algEquiv` sends the generator of `K⟮x⟯` to the generator of `K⟮y⟯`. -/
theorem algEquiv_apply {x y : L} (hx : IsAlgebraic K x) (h_mp : minpoly K x = minpoly K y) :
    algEquiv hx h_mp (AdjoinSimple.gen K x) = AdjoinSimple.gen K y := by
  have hy : IsAlgebraic K y := ⟨minpoly K x, ne_zero hx.isIntegral, (h_mp ▸ aeval _ _)⟩
  rw [algEquiv, trans_apply, ← adjoinRootEquivAdjoin_apply_root K hx.isIntegral,
    symm_apply_apply, trans_apply, AdjoinRoot.algEquivOfEq_apply_root,
    adjoinRootEquivAdjoin_apply_root K hy.isIntegral]

end minpoly

end Minpoly

namespace PowerBasis

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

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
