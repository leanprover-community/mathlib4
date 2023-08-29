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

 - `F⟮α⟯`: adjoin a single element `α` to `F`.
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

instance : CompleteLattice (IntermediateField F E) :=
  GaloisInsertion.liftCompleteLattice IntermediateField.gi

instance : Inhabited (IntermediateField F E) :=
  ⟨⊤⟩

theorem coe_bot : ↑(⊥ : IntermediateField F E) = Set.range (algebraMap F E) := by
  change ↑(Subfield.closure (Set.range (algebraMap F E) ∪ ∅)) = Set.range (algebraMap F E)
  -- ⊢ ↑(Subfield.closure (Set.range ↑(algebraMap F E) ∪ ∅)) = Set.range ↑(algebraM …
  rw [Set.union_empty, ← Set.image_univ, ← RingHom.map_field_closure]
  -- ⊢ ↑(Subfield.map (algebraMap F E) (Subfield.closure Set.univ)) = ↑(algebraMap  …
  simp
  -- 🎉 no goals
#align intermediate_field.coe_bot IntermediateField.coe_bot

theorem mem_bot {x : E} : x ∈ (⊥ : IntermediateField F E) ↔ x ∈ Set.range (algebraMap F E) :=
  Set.ext_iff.mp coe_bot x
#align intermediate_field.mem_bot IntermediateField.mem_bot

@[simp]
theorem bot_toSubalgebra : (⊥ : IntermediateField F E).toSubalgebra = ⊥ := by
  ext
  -- ⊢ x✝ ∈ ⊥.toSubalgebra ↔ x✝ ∈ ⊥
  rw [mem_toSubalgebra, Algebra.mem_bot, mem_bot]
  -- 🎉 no goals
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
                              -- 🎉 no goals
#align intermediate_field.Inf_to_subalgebra IntermediateField.sInf_toSubalgebra

@[simp]
theorem sInf_toSubfield (S : Set (IntermediateField F E)) :
    (sInf S).toSubfield = sInf (toSubfield '' S) :=
  SetLike.coe_injective <| by simp [Set.sUnion_image]
                              -- 🎉 no goals
#align intermediate_field.Inf_to_subfield IntermediateField.sInf_toSubfield

@[simp, norm_cast]
theorem coe_iInf {ι : Sort*} (S : ι → IntermediateField F E) : (↑(iInf S) : Set E) = ⋂ i, S i := by
  simp [iInf]
  -- 🎉 no goals
#align intermediate_field.coe_infi IntermediateField.coe_iInf

@[simp]
theorem iInf_toSubalgebra {ι : Sort*} (S : ι → IntermediateField F E) :
    (iInf S).toSubalgebra = ⨅ i, (S i).toSubalgebra :=
  SetLike.coe_injective <| by simp [iInf]
                              -- 🎉 no goals
#align intermediate_field.infi_to_subalgebra IntermediateField.iInf_toSubalgebra

@[simp]
theorem iInf_toSubfield {ι : Sort*} (S : ι → IntermediateField F E) :
    (iInf S).toSubfield = ⨅ i, (S i).toSubfield :=
  SetLike.coe_injective <| by simp [iInf]
                              -- 🎉 no goals
#align intermediate_field.infi_to_subfield IntermediateField.iInf_toSubfield

--Porting note: `left_inv`, `right_inv`, `map_mul'`, `map_add'` and `commutes` were not needed.
/-- Construct an algebra isomorphism from an equality of intermediate fields -/
@[simps apply]
def equivOfEq {S T : IntermediateField F E} (h : S = T) : S ≃ₐ[F] T := by
  refine'
      { toFun := fun x => ⟨x, _⟩
        invFun := fun x => ⟨x, _⟩
        left_inv := fun _ => by ext; simp
        right_inv := fun _ => by ext; simp
        map_mul' := fun _ _ => by ext; simp
        map_add' := fun _ _ => by ext; simp
        commutes' := fun _ => by ext; rfl } <;> aesop
                                                -- 🎉 no goals
                                                -- 🎉 no goals

#align intermediate_field.equiv_of_eq IntermediateField.equivOfEq

@[simp]
theorem equivOfEq_symm {S T : IntermediateField F E} (h : S = T) :
    (equivOfEq h).symm = equivOfEq h.symm :=
  rfl
#align intermediate_field.equiv_of_eq_symm IntermediateField.equivOfEq_symm

@[simp]
theorem equivOfEq_rfl (S : IntermediateField F E) : equivOfEq (rfl : S = S) = AlgEquiv.refl := by
  ext; rfl
  -- ⊢ ↑(↑(equivOfEq (_ : S = S)) a✝) = ↑(↑AlgEquiv.refl a✝)
       -- 🎉 no goals
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
     -- 🎉 no goals
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
      -- ⊢ ↑(algebraMap { x // x ∈ ⊥ } E) x = ↑(algebraMap F E) (↑(algebraMap { x // x  …
      obtain ⟨y, rfl⟩ := (botEquiv F E).symm.surjective x
      -- ⊢ ↑(algebraMap { x // x ∈ ⊥ } E) (↑(AlgEquiv.symm (botEquiv F E)) y) = ↑(algeb …
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
    (⊥ : IntermediateField K E).restrictScalars _ = K := by
  ext x
  -- ⊢ x ∈ restrictScalars F ⊥ ↔ x ∈ K
  rw [mem_restrictScalars, mem_bot];
  -- ⊢ x ∈ Set.range ↑(algebraMap { x // x ∈ K } E) ↔ x ∈ K
  exact Set.ext_iff.mp Subtype.range_coe x
  -- 🎉 no goals
#align intermediate_field.restrict_scalars_bot_eq_self IntermediateField.restrictScalars_bot_eq_self

@[simp]
theorem restrictScalars_top {K : Type*} [Field K] [Algebra K E] [Algebra K F]
    [IsScalarTower K F E] : (⊤ : IntermediateField F E).restrictScalars K = ⊤ :=
  rfl
#align intermediate_field.restrict_scalars_top IntermediateField.restrictScalars_top

theorem AlgHom.fieldRange_eq_map {K : Type*} [Field K] [Algebra F K] (f : E →ₐ[F] K) :
    f.fieldRange = IntermediateField.map f ⊤ :=
  SetLike.ext' Set.image_univ.symm
#align alg_hom.field_range_eq_map IntermediateField.AlgHom.fieldRange_eq_map

theorem AlgHom.map_fieldRange {K L : Type*} [Field K] [Field L] [Algebra F K] [Algebra F L]
    (f : E →ₐ[F] K) (g : K →ₐ[F] L) : f.fieldRange.map g = (g.comp f).fieldRange :=
  SetLike.ext' (Set.range_comp g f).symm
#align alg_hom.map_field_range IntermediateField.AlgHom.map_fieldRange

theorem AlgHom.fieldRange_eq_top {K : Type*} [Field K] [Algebra F K] {f : E →ₐ[F] K} :
    f.fieldRange = ⊤ ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans Set.range_iff_surjective
#align alg_hom.field_range_eq_top IntermediateField.AlgHom.fieldRange_eq_top

@[simp]
theorem AlgEquiv.fieldRange_eq_top {K : Type*} [Field K] [Algebra F K] (f : E ≃ₐ[F] K) :
    (f : E →ₐ[F] K).fieldRange = ⊤ :=
  AlgHom.fieldRange_eq_top.mpr f.surjective
#align alg_equiv.field_range_eq_top IntermediateField.AlgEquiv.fieldRange_eq_top

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
  -- ⊢ x ∈ ↑(adjoin F S)
  cases' hx with f hf
  -- ⊢ x ∈ ↑(adjoin F S)
  rw [← hf]
  -- ⊢ ↑(algebraMap F E) f ∈ ↑(adjoin F S)
  exact adjoin.algebraMap_mem F S f
  -- 🎉 no goals
#align intermediate_field.adjoin.range_algebra_map_subset IntermediateField.adjoin.range_algebraMap_subset

instance adjoin.fieldCoe : CoeTC F (adjoin F S)
    where coe x := ⟨algebraMap F E x, adjoin.algebraMap_mem F S x⟩
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
  -- ⊢ Set.range ↑(algebraMap F E) ∪ S ⊆ ↑K
  rw [Set.union_subset_iff]
  -- ⊢ Set.range ↑(algebraMap F E) ⊆ ↑K ∧ S ⊆ ↑K
  exact ⟨HF, HS⟩
  -- 🎉 no goals
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
  -- ⊢ ↑(restrictScalars F (adjoin { x // x ∈ adjoin F S } T)) = ↑(adjoin F (S ∪ T))
  change (↑(adjoin (adjoin F S) T) : Set E) = _
  -- ⊢ ↑(adjoin { x // x ∈ adjoin F S } T) = ↑(adjoin F (S ∪ T))
  apply Set.eq_of_subset_of_subset <;> rw [adjoin_subset_adjoin_iff] <;> constructor
  -- ⊢ ↑(adjoin { x // x ∈ adjoin F S } T) ⊆ ↑(adjoin F (S ∪ T))
                                       -- ⊢ Set.range ↑(algebraMap { x // x ∈ adjoin F S } E) ⊆ ↑(adjoin F (S ∪ T)) ∧ T  …
                                       -- ⊢ Set.range ↑(algebraMap F E) ⊆ ↑(adjoin { x // x ∈ adjoin F S } T) ∧ S ∪ T ⊆  …
                                                                         -- ⊢ Set.range ↑(algebraMap { x // x ∈ adjoin F S } E) ⊆ ↑(adjoin F (S ∪ T))
                                                                         -- ⊢ Set.range ↑(algebraMap F E) ⊆ ↑(adjoin { x // x ∈ adjoin F S } T)
  · rintro _ ⟨⟨x, hx⟩, rfl⟩; exact adjoin.mono _ _ _ (Set.subset_union_left _ _) hx
    -- ⊢ ↑(algebraMap { x // x ∈ adjoin F S } E) { val := x, property := hx } ∈ ↑(adj …
                             -- 🎉 no goals
  · exact subset_adjoin_of_subset_right _ _ (Set.subset_union_right _ _)
    -- 🎉 no goals
-- Porting note: orginal proof times out
  · rintro x ⟨f, rfl⟩
    -- ⊢ ↑(algebraMap F E) f ∈ ↑(adjoin { x // x ∈ adjoin F S } T)
    refine' Subfield.subset_closure _
    -- ⊢ ↑(algebraMap F E) f ∈ Set.range ↑(algebraMap { x // x ∈ adjoin F S } E) ∪ T
    left
    -- ⊢ ↑(algebraMap F E) f ∈ Set.range ↑(algebraMap { x // x ∈ adjoin F S } E)
    exact ⟨f, rfl⟩
    -- 🎉 no goals
-- Porting note: orginal proof times out
  · refine' Set.union_subset (fun x hx => Subfield.subset_closure _)
      (fun x hx => Subfield.subset_closure _)
    · left
      -- ⊢ x ∈ Set.range ↑(algebraMap { x // x ∈ adjoin F S } E)
      refine' ⟨⟨x, Subfield.subset_closure _⟩, rfl⟩
      -- ⊢ x ∈ Set.range ↑(algebraMap F E) ∪ S
      right
      -- ⊢ x ∈ S
      exact hx
      -- 🎉 no goals
    · right
      -- ⊢ x ∈ T
      exact hx
      -- 🎉 no goals
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
  -- 🎉 no goals
#align intermediate_field.adjoin_adjoin_comm IntermediateField.adjoin_adjoin_comm

theorem adjoin_map {E' : Type*} [Field E'] [Algebra F E'] (f : E →ₐ[F] E') :
    (adjoin F S).map f = adjoin F (f '' S) := by
  ext x
  -- ⊢ x ∈ map f (adjoin F S) ↔ x ∈ adjoin F (↑f '' S)
  show
    x ∈ (Subfield.closure (Set.range (algebraMap F E) ∪ S)).map (f : E →+* E') ↔
      x ∈ Subfield.closure (Set.range (algebraMap F E') ∪ f '' S)
  rw [RingHom.map_field_closure, Set.image_union, ← Set.range_comp, ← RingHom.coe_comp,
    f.comp_algebraMap]
  rfl
  -- 🎉 no goals
#align intermediate_field.adjoin_map IntermediateField.adjoin_map

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
  -- ⊢ K.toSubalgebra = (adjoin F S).toSubalgebra
  rw [h]
  -- ⊢ Algebra.adjoin F S = (adjoin F S).toSubalgebra
  refine' (adjoin_eq_algebra_adjoin F _ _).symm
  -- ⊢ ∀ (x : E), x ∈ Algebra.adjoin F S → x⁻¹ ∈ Algebra.adjoin F S
  intro x
  -- ⊢ x ∈ Algebra.adjoin F S → x⁻¹ ∈ Algebra.adjoin F S
  convert K.inv_mem (x := x) <;> rw [← h] <;> rfl
  -- ⊢ x ∈ Algebra.adjoin F S ↔ x ∈ K
                                 -- ⊢ x ∈ K.toSubalgebra ↔ x ∈ K
                                 -- ⊢ x⁻¹ ∈ K.toSubalgebra ↔ x⁻¹ ∈ K
                                              -- 🎉 no goals
                                              -- 🎉 no goals
#align intermediate_field.eq_adjoin_of_eq_algebra_adjoin IntermediateField.eq_adjoin_of_eq_algebra_adjoin


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
macro:max K:term "⟮" xs:term,* "⟯" : term => do ``(adjoin $K $(← mkInsertTerm xs.getElems))

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
  -- ⊢ IsIntegral F (gen F α) ↔ IsIntegral F (↑(algebraMap { x // x ∈ F⟮α⟯ } E) (ge …
  rw [isIntegral_algebraMap_iff (algebraMap F⟮α⟯ E).injective]
  -- 🎉 no goals
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
  -- ⊢ (adjoin F S).toSubalgebra = Algebra.adjoin F S
  have : Algebra.IsIntegral F (Algebra.adjoin F S) := by
    rwa [← le_integralClosure_iff_isIntegral, Algebra.adjoin_le_iff]
  have := isField_of_isIntegral_of_isField' this (Field.toIsField F)
  -- ⊢ (adjoin F S).toSubalgebra = Algebra.adjoin F S
  rw [← ((Algebra.adjoin F S).toIntermediateField' this).eq_adjoin_of_eq_algebra_adjoin F S] <;> rfl
  -- ⊢ (Subalgebra.toIntermediateField' (Algebra.adjoin F S) this).toSubalgebra = A …
                                                                                                 -- 🎉 no goals
                                                                                                 -- 🎉 no goals
#align intermediate_field.adjoin_algebraic_to_subalgebra IntermediateField.adjoin_algebraic_toSubalgebra

theorem adjoin_simple_toSubalgebra_of_integral (hα : IsIntegral F α) :
    F⟮α⟯.toSubalgebra = Algebra.adjoin F {α} := by
  apply adjoin_algebraic_toSubalgebra
  -- ⊢ ∀ (x : E), x ∈ {α} → IsAlgebraic F x
  rintro x (rfl : x = α)
  -- ⊢ IsAlgebraic F x
  rwa [isAlgebraic_iff_isIntegral]
  -- 🎉 no goals
#align intermediate_field.adjoin_simple_to_subalgebra_of_integral IntermediateField.adjoin_simple_toSubalgebra_of_integral

theorem isSplittingField_iff {p : F[X]} {K : IntermediateField F E} :
    p.IsSplittingField F K ↔ p.Splits (algebraMap F K) ∧ K = adjoin F (p.rootSet E) := by
  suffices _ → (Algebra.adjoin F (p.rootSet K) = ⊤ ↔ K = adjoin F (p.rootSet E)) by
    exact ⟨fun h => ⟨h.1, (this h.1).mp h.2⟩, fun h => ⟨h.1, (this h.1).mpr h.2⟩⟩
  simp_rw [SetLike.ext_iff, ← mem_toSubalgebra, ← SetLike.ext_iff]
  -- ⊢ Splits (algebraMap F { x // x ∈ K }) p → (Algebra.adjoin F (rootSet p { x // …
  rw [adjoin_algebraic_toSubalgebra fun x => isAlgebraic_of_mem_rootSet]
  -- ⊢ Splits (algebraMap F { x // x ∈ K }) p → (Algebra.adjoin F (rootSet p { x // …
  refine' fun hp => (adjoin_rootSet_eq_range hp K.val).symm.trans _
  -- ⊢ Algebra.adjoin F (rootSet p E) = AlgHom.range (val K) ↔ K.toSubalgebra = Alg …
  rw [← K.range_val, eq_comm]
  -- 🎉 no goals
#align intermediate_field.is_splitting_field_iff IntermediateField.isSplittingField_iff

theorem adjoin_rootSet_isSplittingField {p : F[X]} (hp : p.Splits (algebraMap F E)) :
    p.IsSplittingField F (adjoin F (p.rootSet E)) :=
  isSplittingField_iff.mpr ⟨splits_of_splits hp fun _ hx => subset_adjoin F (p.rootSet E) hx, rfl⟩
#align intermediate_field.adjoin_root_set_is_splitting_field IntermediateField.adjoin_rootSet_isSplittingField

open scoped BigOperators

/-- A compositum of splitting fields is a splitting field -/
theorem isSplittingField_iSup {ι : Type*} {t : ι → IntermediateField F E} {p : ι → F[X]}
    {s : Finset ι} (h0 : ∏ i in s, p i ≠ 0) (h : ∀ i ∈ s, (p i).IsSplittingField F (t i)) :
    (∏ i in s, p i).IsSplittingField F (⨆ i ∈ s, t i : IntermediateField F E) := by
  let K : IntermediateField F E := ⨆ i ∈ s, t i
  -- ⊢ IsSplittingField F { x // x ∈ ⨆ (i : ι) (_ : i ∈ s), t i } (∏ i in s, p i)
  have hK : ∀ i ∈ s, t i ≤ K := fun i hi => le_iSup_of_le i (le_iSup (fun _ => t i) hi)
  -- ⊢ IsSplittingField F { x // x ∈ ⨆ (i : ι) (_ : i ∈ s), t i } (∏ i in s, p i)
  simp only [isSplittingField_iff] at h ⊢
  -- ⊢ Splits (algebraMap F { x // x ∈ ⨆ (i : ι) (_ : i ∈ s), t i }) (∏ i in s, p i …
  refine'
    ⟨splits_prod (algebraMap F K) fun i hi =>
        Polynomial.splits_comp_of_splits (algebraMap F (t i)) (inclusion (hK i hi)).toRingHom
          (h i hi).1,
      _⟩
  simp only [rootSet_prod p s h0, ← Set.iSup_eq_iUnion, (@gc F _ E _ _).l_iSup₂]
  -- ⊢ ⨆ (i : ι) (_ : i ∈ s), t i = ⨆ (i : ι) (_ : i ∈ s), adjoin F (rootSet (p i) E)
  exact iSup_congr fun i => iSup_congr fun hi => (h i hi).2
  -- 🎉 no goals
#align intermediate_field.is_splitting_field_supr IntermediateField.isSplittingField_iSup

open Set CompleteLattice

/- Porting note: this was tagged `simp`, but the LHS can be simplified now that the notation
has been improved. -/
theorem adjoin_simple_le_iff {K : IntermediateField F E} : F⟮α⟯ ≤ K ↔ α ∈ K := by simp
                                                                                  -- 🎉 no goals
#align intermediate_field.adjoin_simple_le_iff IntermediateField.adjoin_simple_le_iff

/-- Adjoining a single element is compact in the lattice of intermediate fields. -/
theorem adjoin_simple_isCompactElement (x : E) : IsCompactElement F⟮x⟯ := by
  rw [isCompactElement_iff_le_of_directed_sSup_le]
  -- ⊢ ∀ (s : Set (IntermediateField F E)), Set.Nonempty s → DirectedOn (fun x x_1  …
  rintro s ⟨F₀, hF₀⟩ hs hx
  -- ⊢ ∃ x_1, x_1 ∈ s ∧ F⟮x⟯ ≤ x_1
  simp only [adjoin_simple_le_iff] at hx ⊢
  -- ⊢ ∃ x_1, x_1 ∈ s ∧ x ∈ x_1
  let F : IntermediateField F E :=
    { carrier := ⋃ E ∈ s, ↑E
      add_mem' := by
        rintro x₁ x₂ ⟨-, ⟨F₁, rfl⟩, ⟨-, ⟨hF₁, rfl⟩, hx₁⟩⟩ ⟨-, ⟨F₂, rfl⟩, ⟨-, ⟨hF₂, rfl⟩, hx₂⟩⟩
        obtain ⟨F₃, hF₃, h₁₃, h₂₃⟩ := hs F₁ hF₁ F₂ hF₂
        exact mem_iUnion_of_mem F₃ (mem_iUnion_of_mem hF₃ (F₃.add_mem (h₁₃ hx₁) (h₂₃ hx₂)))
      mul_mem' := by
        rintro x₁ x₂ ⟨-, ⟨F₁, rfl⟩, ⟨-, ⟨hF₁, rfl⟩, hx₁⟩⟩ ⟨-, ⟨F₂, rfl⟩, ⟨-, ⟨hF₂, rfl⟩, hx₂⟩⟩
        obtain ⟨F₃, hF₃, h₁₃, h₂₃⟩ := hs F₁ hF₁ F₂ hF₂
        exact mem_iUnion_of_mem F₃ (mem_iUnion_of_mem hF₃ (F₃.mul_mem (h₁₃ hx₁) (h₂₃ hx₂)))
      inv_mem' := by
        rintro x ⟨-, ⟨E, rfl⟩, ⟨-, ⟨hE, rfl⟩, hx⟩⟩
        exact mem_iUnion_of_mem E (mem_iUnion_of_mem hE (E.inv_mem hx))
      algebraMap_mem' := fun x =>
        mem_iUnion_of_mem F₀ (mem_iUnion_of_mem hF₀ (F₀.algebraMap_mem x)) }
-- Porting note: original proof of `key` was
-- `sSup_le fun E1 hE1 => Set.subset_iUnion_of_subset E1 (subset_iUnion _ hE1)`
  have key : sSup s ≤ F := sSup_le fun E1 hE1 => by
    refine' Set.subset_iUnion_of_subset E1 _
    intro x hx
    simpa [hE1] using hx
  obtain ⟨-, ⟨E, rfl⟩, -, ⟨hE, rfl⟩, hx⟩ := key hx
  -- ⊢ ∃ x_1, x_1 ∈ s ∧ x ∈ x_1
  exact ⟨E, hE, hx⟩
  -- 🎉 no goals
#align intermediate_field.adjoin_simple_is_compact_element IntermediateField.adjoin_simple_isCompactElement

-- Porting note: original proof times out.
/-- Adjoining a finite subset is compact in the lattice of intermediate fields. -/
theorem adjoin_finset_isCompactElement (S : Finset E) :
    IsCompactElement (adjoin F S : IntermediateField F E) := by
  have key : adjoin F ↑S = ⨆ x ∈ S, F⟮x⟯ := by
-- Porting note: `exact` or `apply` timeout here
    refine' le_antisymm (adjoin_le_iff.mpr fun x hx => SetLike.mem_coe.mpr
      (adjoin_simple_le_iff.mp (le_iSup_of_le x (le_iSup_iff.2 (fun E1 hE1 => hE1 hx)))))
        (iSup_le fun x => iSup_le fun hx => adjoin_simple_le_iff.mpr (subset_adjoin F S hx))
  rw [key, ← Finset.sup_eq_iSup]
  -- ⊢ IsCompactElement (Finset.sup S fun x => F⟮x⟯)
  exact finset_sup_compact_of_compact S fun x _ => adjoin_simple_isCompactElement x
  -- 🎉 no goals
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
          -- ⊢ IsCompactElement ((fun x => F⟮x⟯) x)
                                -- 🎉 no goals
        sSup_image.trans
          (le_antisymm (iSup_le fun i => iSup_le fun hi => adjoin_simple_le_iff.mpr hi) fun x hx =>
            adjoin_simple_le_iff.mp (le_iSup_of_le x (le_iSup_of_le hx le_rfl)))⟩⟩⟩

theorem exists_finset_of_mem_iSup {ι : Type*} {f : ι → IntermediateField F E} {x : E}
    (hx : x ∈ ⨆ i, f i) : ∃ s : Finset ι, x ∈ ⨆ i ∈ s, f i := by
  have := (adjoin_simple_isCompactElement x : IsCompactElement F⟮x⟯).exists_finset_of_le_iSup
    (IntermediateField F E) f
  simp only [adjoin_simple_le_iff] at this
  -- ⊢ ∃ s, x ∈ ⨆ (i : ι) (_ : i ∈ s), f i
  exact this hx
  -- 🎉 no goals
#align intermediate_field.exists_finset_of_mem_supr IntermediateField.exists_finset_of_mem_iSup

theorem exists_finset_of_mem_supr' {ι : Type*} {f : ι → IntermediateField F E} {x : E}
    (hx : x ∈ ⨆ i, f i) : ∃ s : Finset (Σ i, f i), x ∈ ⨆ i ∈ s, F⟮(i.2 : E)⟯ := by
-- Porting note: writing `fun i x h => ...` does not work.
    refine' exists_finset_of_mem_iSup (SetLike.le_def.mp (iSup_le (fun i => _)) hx)
    -- ⊢ f i ≤ ⨆ (i : (i : ι) × { x // x ∈ f i }), F⟮↑i.snd⟯
    intro x h
    -- ⊢ x ∈ ⨆ (i : (i : ι) × { x // x ∈ f i }), F⟮↑i.snd⟯
    exact SetLike.le_def.mp (le_iSup_of_le ⟨i, x, h⟩ (by simp)) (mem_adjoin_simple_self F x)
    -- 🎉 no goals
#align intermediate_field.exists_finset_of_mem_supr' IntermediateField.exists_finset_of_mem_supr'

theorem exists_finset_of_mem_supr'' {ι : Type*} {f : ι → IntermediateField F E}
    (h : ∀ i, Algebra.IsAlgebraic F (f i)) {x : E} (hx : x ∈ ⨆ i, f i) :
    ∃ s : Finset (Σ i, f i), x ∈ ⨆ i ∈ s, adjoin F ((minpoly F (i.2 : _)).rootSet E) := by
-- Porting note: writing `fun i x1 hx1 => ...` does not work.
  refine' exists_finset_of_mem_iSup (SetLike.le_def.mp (iSup_le (fun i => _)) hx)
  -- ⊢ f i ≤ ⨆ (i : (i : ι) × { x // x ∈ f i }), adjoin F (rootSet (minpoly F i.snd …
  intro x1 hx1
  -- ⊢ x1 ∈ ⨆ (i : (i : ι) × { x // x ∈ f i }), adjoin F (rootSet (minpoly F i.snd) …
  refine' SetLike.le_def.mp (le_iSup_of_le ⟨i, x1, hx1⟩ _)
    (subset_adjoin F (rootSet (minpoly F x1) E) _)
  · rw [IntermediateField.minpoly_eq, Subtype.coe_mk]
    -- 🎉 no goals
  · rw [mem_rootSet_of_ne, minpoly.aeval]
    -- ⊢ minpoly F x1 ≠ 0
    exact minpoly.ne_zero (isIntegral_iff.mp (isAlgebraic_iff_isIntegral.mp (h i ⟨x1, hx1⟩)))
    -- 🎉 no goals
#align intermediate_field.exists_finset_of_mem_supr'' IntermediateField.exists_finset_of_mem_supr''

end AdjoinSimple

end AdjoinDef

section AdjoinIntermediateFieldLattice

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E] {α : E} {S : Set E}

@[simp]
theorem adjoin_eq_bot_iff : adjoin F S = ⊥ ↔ S ⊆ (⊥ : IntermediateField F E) := by
  rw [eq_bot_iff, adjoin_le_iff]; rfl
  -- ⊢ S ≤ ↑⊥ ↔ S ⊆ ↑⊥
                                  -- 🎉 no goals
#align intermediate_field.adjoin_eq_bot_iff IntermediateField.adjoin_eq_bot_iff

/- Porting note: this was tagged `simp`. -/
theorem adjoin_simple_eq_bot_iff : F⟮α⟯ = ⊥ ↔ α ∈ (⊥ : IntermediateField F E) := by
  simp
  -- 🎉 no goals
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
  -- 🎉 no goals
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
                                                                       -- 🎉 no goals
#align intermediate_field.rank_bot IntermediateField.rank_bot

@[simp]
theorem finrank_bot : finrank F (⊥ : IntermediateField F E) = 1 := by rw [finrank_eq_one_iff]
                                                                      -- 🎉 no goals
#align intermediate_field.finrank_bot IntermediateField.finrank_bot

theorem rank_adjoin_eq_one_iff : Module.rank F (adjoin F S) = 1 ↔ S ⊆ (⊥ : IntermediateField F E) :=
  Iff.trans rank_eq_one_iff adjoin_eq_bot_iff
#align intermediate_field.rank_adjoin_eq_one_iff IntermediateField.rank_adjoin_eq_one_iff

theorem rank_adjoin_simple_eq_one_iff : Module.rank F F⟮α⟯ = 1 ↔ α ∈ (⊥ : IntermediateField F E) :=
  by rw [rank_adjoin_eq_one_iff]; exact Set.singleton_subset_iff
     -- ⊢ {α} ⊆ ↑⊥ ↔ α ∈ ⊥
                                  -- 🎉 no goals
#align intermediate_field.rank_adjoin_simple_eq_one_iff IntermediateField.rank_adjoin_simple_eq_one_iff

theorem finrank_adjoin_eq_one_iff : finrank F (adjoin F S) = 1 ↔ S ⊆ (⊥ : IntermediateField F E) :=
  Iff.trans finrank_eq_one_iff adjoin_eq_bot_iff
#align intermediate_field.finrank_adjoin_eq_one_iff IntermediateField.finrank_adjoin_eq_one_iff

theorem finrank_adjoin_simple_eq_one_iff :
    finrank F F⟮α⟯ = 1 ↔ α ∈ (⊥ : IntermediateField F E) := by
  rw [finrank_adjoin_eq_one_iff]; exact Set.singleton_subset_iff
  -- ⊢ {α} ⊆ ↑⊥ ↔ α ∈ ⊥
                                  -- 🎉 no goals
#align intermediate_field.finrank_adjoin_simple_eq_one_iff IntermediateField.finrank_adjoin_simple_eq_one_iff

/-- If `F⟮x⟯` has dimension `1` over `F` for every `x ∈ E` then `F = E`. -/
theorem bot_eq_top_of_rank_adjoin_eq_one (h : ∀ x : E, Module.rank F F⟮x⟯ = 1) :
    (⊥ : IntermediateField F E) = ⊤ := by
  ext y
  -- ⊢ y ∈ ⊥ ↔ y ∈ ⊤
  rw [iff_true_right IntermediateField.mem_top]
  -- ⊢ y ∈ ⊥
  exact rank_adjoin_simple_eq_one_iff.mp (h y)
  -- 🎉 no goals
#align intermediate_field.bot_eq_top_of_rank_adjoin_eq_one IntermediateField.bot_eq_top_of_rank_adjoin_eq_one

theorem bot_eq_top_of_finrank_adjoin_eq_one (h : ∀ x : E, finrank F F⟮x⟯ = 1) :
    (⊥ : IntermediateField F E) = ⊤ := by
  ext y
  -- ⊢ y ∈ ⊥ ↔ y ∈ ⊤
  rw [iff_true_right IntermediateField.mem_top]
  -- ⊢ y ∈ ⊥
  exact finrank_adjoin_simple_eq_one_iff.mp (h y)
  -- 🎉 no goals
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
  -- ⊢ ∀ (x : E), finrank F { x_1 // x_1 ∈ F⟮x⟯ } = 1
  exact fun x => by linarith [h x, show 0 < finrank F F⟮x⟯ from finrank_pos]
  -- 🎉 no goals
#align intermediate_field.bot_eq_top_of_finrank_adjoin_le_one IntermediateField.bot_eq_top_of_finrank_adjoin_le_one

theorem subsingleton_of_finrank_adjoin_le_one [FiniteDimensional F E]
    (h : ∀ x : E, finrank F F⟮x⟯ ≤ 1) : Subsingleton (IntermediateField F E) :=
  subsingleton_of_bot_eq_top (bot_eq_top_of_finrank_adjoin_le_one h)
#align intermediate_field.subsingleton_of_finrank_adjoin_le_one
  IntermediateField.subsingleton_of_finrank_adjoin_le_one

end AdjoinRank

end AdjoinIntermediateFieldLattice

section AdjoinIntegralElement

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E] {α : E}

variable {K : Type*} [Field K] [Algebra F K]

theorem minpoly_gen {α : E} (h : IsIntegral F α) :
    minpoly F (AdjoinSimple.gen F α) = minpoly F α := by
  rw [← AdjoinSimple.algebraMap_gen F α] at h
  -- ⊢ minpoly F (AdjoinSimple.gen F α) = minpoly F α
  have inj := (algebraMap F⟮α⟯ E).injective
  -- ⊢ minpoly F (AdjoinSimple.gen F α) = minpoly F α
  exact
    minpoly.eq_of_algebraMap_eq inj ((isIntegral_algebraMap_iff inj).mp h)
      (AdjoinSimple.algebraMap_gen _ _).symm
#align intermediate_field.minpoly_gen IntermediateField.minpoly_gen

variable (F)

theorem aeval_gen_minpoly (α : E) : aeval (AdjoinSimple.gen F α) (minpoly F α) = 0 := by
  ext
  -- ⊢ ↑(↑(aeval (AdjoinSimple.gen F α)) (minpoly F α)) = ↑0
  convert minpoly.aeval F α
  -- ⊢ ↑(↑(aeval (AdjoinSimple.gen F α)) (minpoly F α)) = ↑(aeval α) (minpoly F α)
  conv in aeval α => rw [← AdjoinSimple.algebraMap_gen F α]
  -- ⊢ ↑(↑(aeval (AdjoinSimple.gen F α)) (minpoly F α)) = ↑(aeval (↑(algebraMap { x …
  exact (aeval_algebraMap_apply E (AdjoinSimple.gen F α) _).symm
  -- 🎉 no goals
#align intermediate_field.aeval_gen_minpoly IntermediateField.aeval_gen_minpoly

--Porting note: original proof used `Exists.cases_on`.
/-- algebra isomorphism between `AdjoinRoot` and `F⟮α⟯` -/
noncomputable def adjoinRootEquivAdjoin (h : IsIntegral F α) :
    AdjoinRoot (minpoly F α) ≃ₐ[F] F⟮α⟯ :=
  AlgEquiv.ofBijective
    (AdjoinRoot.liftHom (minpoly F α) (AdjoinSimple.gen F α) (aeval_gen_minpoly F α))
    (by
      set f := AdjoinRoot.lift _ _ (aeval_gen_minpoly F α : _)
      -- ⊢ Function.Bijective ↑(AdjoinRoot.liftHom (minpoly F α) (AdjoinSimple.gen F α) …
      haveI := Fact.mk (minpoly.irreducible h)
      -- ⊢ Function.Bijective ↑(AdjoinRoot.liftHom (minpoly F α) (AdjoinSimple.gen F α) …
      constructor
      -- ⊢ Function.Injective ↑(AdjoinRoot.liftHom (minpoly F α) (AdjoinSimple.gen F α) …
      · exact RingHom.injective f
        -- 🎉 no goals
      · suffices F⟮α⟯.toSubfield ≤ RingHom.fieldRange (F⟮α⟯.toSubfield.subtype.comp f) by
          intro x
          obtain ⟨y, hy⟩ := (this (Subtype.mem x))
          exact ⟨y, Subtype.ext hy⟩
        refine' Subfield.closure_le.mpr (Set.union_subset (fun x hx => _) _)
        -- ⊢ x ∈ ↑(RingHom.fieldRange (RingHom.comp (Subfield.subtype (toSubfield F⟮α⟯))  …
        · obtain ⟨y, hy⟩ := hx
          -- ⊢ x ∈ ↑(RingHom.fieldRange (RingHom.comp (Subfield.subtype (toSubfield F⟮α⟯))  …
          refine' ⟨y, _⟩
          -- ⊢ ↑(RingHom.comp (Subfield.subtype (toSubfield F⟮α⟯)) f) (↑(AdjoinRoot.of (min …
          rw [RingHom.comp_apply, AdjoinRoot.lift_of (aeval_gen_minpoly F α)]
          -- ⊢ ↑(Subfield.subtype (toSubfield F⟮α⟯)) (↑(algebraMap F { x // x ∈ F⟮α⟯ }) y)  …
          exact hy
          -- 🎉 no goals
        · refine' Set.singleton_subset_iff.mpr ⟨AdjoinRoot.root (minpoly F α), _⟩
          -- ⊢ ↑(RingHom.comp (Subfield.subtype (toSubfield F⟮α⟯)) f) (AdjoinRoot.root (min …
          rw [RingHom.comp_apply, AdjoinRoot.lift_root (aeval_gen_minpoly F α)]
          -- ⊢ ↑(Subfield.subtype (toSubfield F⟮α⟯)) (AdjoinSimple.gen F α) = α
          rfl)
          -- 🎉 no goals
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
    rw [powerBasisAux, Basis.map_apply, PowerBasis.basis_eq_pow, AlgEquiv.toLinearEquiv_apply,
      AlgEquiv.map_pow, AdjoinRoot.powerBasis_gen, adjoinRootEquivAdjoin_apply_root]
#align intermediate_field.adjoin.power_basis IntermediateField.adjoin.powerBasis

theorem adjoin.finiteDimensional {x : L} (hx : IsIntegral K x) : FiniteDimensional K K⟮x⟯ :=
  PowerBasis.finiteDimensional (adjoin.powerBasis hx)
#align intermediate_field.adjoin.finite_dimensional IntermediateField.adjoin.finiteDimensional

theorem adjoin.finrank {x : L} (hx : IsIntegral K x) :
    FiniteDimensional.finrank K K⟮x⟯ = (minpoly K x).natDegree := by
  rw [PowerBasis.finrank (adjoin.powerBasis hx : _)]
  -- ⊢ (powerBasis hx).dim = natDegree (minpoly K x)
  rfl
  -- 🎉 no goals
#align intermediate_field.adjoin.finrank IntermediateField.adjoin.finrank

theorem _root_.minpoly.natDegree_le (x : L) [FiniteDimensional K L] :
    (minpoly K x).natDegree ≤ finrank K L :=
  le_of_eq_of_le (IntermediateField.adjoin.finrank (isIntegral_of_finite _ _)).symm
    K⟮x⟯.toSubmodule.finrank_le
#align minpoly.nat_degree_le minpoly.natDegree_le

theorem _root_.minpoly.degree_le (x : L) [FiniteDimensional K L] :
    (minpoly K x).degree ≤ finrank K L :=
  degree_le_of_natDegree_le (minpoly.natDegree_le x)
#align minpoly.degree_le minpoly.degree_le

end PowerBasis

/-- Algebra homomorphism `F⟮α⟯ →ₐ[F] K` are in bijection with the set of roots
of `minpoly α` in `K`. -/
noncomputable def algHomAdjoinIntegralEquiv (h : IsIntegral F α) :
    (F⟮α⟯ →ₐ[F] K) ≃ { x // x ∈ ((minpoly F α).map (algebraMap F K)).roots } :=
  (adjoin.powerBasis h).liftEquiv'.trans
    ((Equiv.refl _).subtypeEquiv fun x => by
      rw [adjoin.powerBasis_gen, minpoly_gen h, Equiv.refl_apply])
      -- 🎉 no goals
#align intermediate_field.alg_hom_adjoin_integral_equiv IntermediateField.algHomAdjoinIntegralEquiv

/-- Fintype of algebra homomorphism `F⟮α⟯ →ₐ[F] K` -/
noncomputable def fintypeOfAlgHomAdjoinIntegral (h : IsIntegral F α) : Fintype (F⟮α⟯ →ₐ[F] K) :=
  PowerBasis.AlgHom.fintype (adjoin.powerBasis h)
#align intermediate_field.fintype_of_alg_hom_adjoin_integral IntermediateField.fintypeOfAlgHomAdjoinIntegral

theorem card_algHom_adjoin_integral (h : IsIntegral F α) (h_sep : (minpoly F α).Separable)
    (h_splits : (minpoly F α).Splits (algebraMap F K)) :
    @Fintype.card (F⟮α⟯ →ₐ[F] K) (fintypeOfAlgHomAdjoinIntegral F h) = (minpoly F α).natDegree := by
  rw [AlgHom.card_of_powerBasis] <;>
    simp only [adjoin.powerBasis_dim, adjoin.powerBasis_gen, minpoly_gen h, h_sep, h_splits]
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
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
         -- 🎉 no goals
#align intermediate_field.fg_bot IntermediateField.fg_bot

theorem fG_of_fG_toSubalgebra (S : IntermediateField F E) (h : S.toSubalgebra.FG) : S.FG := by
  cases' h with t ht
  -- ⊢ FG S
  exact ⟨t, (eq_adjoin_of_eq_algebra_adjoin _ _ _ ht.symm).symm⟩
  -- 🎉 no goals
#align intermediate_field.fg_of_fg_to_subalgebra IntermediateField.fG_of_fG_toSubalgebra

theorem fg_of_noetherian (S : IntermediateField F E) [IsNoetherian F E] : S.FG :=
  S.fG_of_fG_toSubalgebra S.toSubalgebra.fg_of_noetherian
#align intermediate_field.fg_of_noetherian IntermediateField.fg_of_noetherian

theorem induction_on_adjoin_finset (S : Finset E) (P : IntermediateField F E → Prop) (base : P ⊥)
    (ih : ∀ (K : IntermediateField F E), ∀ x ∈ S, P K → P (K⟮x⟯.restrictScalars F)) :
    P (adjoin F ↑S) := by
  refine' Finset.induction_on' S _ (fun ha _ _ h => _)
  -- ⊢ P (adjoin F ↑∅)
  · simp [base]
    -- 🎉 no goals
  · rw [Finset.coe_insert, Set.insert_eq, Set.union_comm, ← adjoin_adjoin_left]
    -- ⊢ P (restrictScalars F { x // x ∈ adjoin F ↑s✝ }⟮a✝⟯)
    exact ih (adjoin F _) _ ha h
    -- 🎉 no goals
#align intermediate_field.induction_on_adjoin_finset IntermediateField.induction_on_adjoin_finset

theorem induction_on_adjoin_fg (P : IntermediateField F E → Prop) (base : P ⊥)
    (ih : ∀ (K : IntermediateField F E) (x : E), P K → P (K⟮x⟯.restrictScalars F))
    (K : IntermediateField F E) (hK : K.FG) : P K := by
  obtain ⟨S, rfl⟩ := hK
  -- ⊢ P (adjoin F ↑S)
  exact induction_on_adjoin_finset S P base fun K x _ hK => ih K x hK
  -- 🎉 no goals
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
def Lifts :=
  Σ L : IntermediateField F E, L →ₐ[F] K
#align intermediate_field.lifts IntermediateField.Lifts

variable {F E K}

instance : PartialOrder (Lifts F E K) where
  le x y := x.1 ≤ y.1 ∧ ∀ (s : x.1) (t : y.1), (s : E) = t → x.2 s = y.2 t
  le_refl x := ⟨le_refl x.1, fun s t hst => congr_arg x.2 (Subtype.ext hst)⟩
  le_trans x y z hxy hyz :=
    ⟨le_trans hxy.1 hyz.1, fun s u hsu =>
      Eq.trans (hxy.2 s ⟨s, hxy.1 s.mem⟩ rfl) (hyz.2 ⟨s, hxy.1 s.mem⟩ u hsu)⟩
  le_antisymm := by
    rintro ⟨x1, x2⟩ ⟨y1, y2⟩ ⟨hxy1, hxy2⟩ ⟨hyx1, hyx2⟩
    -- ⊢ { fst := x1, snd := x2 } = { fst := y1, snd := y2 }
    obtain rfl : x1 = y1 := le_antisymm hxy1 hyx1
    -- ⊢ { fst := x1, snd := x2 } = { fst := x1, snd := y2 }
    congr
    -- ⊢ x2 = y2
    exact AlgHom.ext fun s => hxy2 s s rfl
    -- 🎉 no goals

noncomputable instance : OrderBot (Lifts F E K) where
  bot := ⟨⊥, (Algebra.ofId F K).comp (botEquiv F E).toAlgHom⟩
  bot_le x :=
    ⟨bot_le, fun s t hst => by
      cases' IntermediateField.mem_bot.mp s.mem with u hu
      -- ⊢ ↑⊥.snd s = ↑x.snd t
      rw [show s = (algebraMap F _) u from Subtype.ext hu.symm, AlgHom.commutes]
      -- ⊢ ↑(algebraMap F K) u = ↑x.snd t
      rw [show t = (algebraMap F _) u from Subtype.ext (Eq.trans hu hst).symm, AlgHom.commutes]⟩
      -- 🎉 no goals

noncomputable instance : Inhabited (Lifts F E K) :=
  ⟨⊥⟩

theorem Lifts.eq_of_le {x y : Lifts F E K} (hxy : x ≤ y) (s : x.1) : x.2 s = y.2 ⟨s, hxy.1 s.mem⟩ :=
  hxy.2 s ⟨s, hxy.1 s.mem⟩ rfl
#align intermediate_field.lifts.eq_of_le IntermediateField.Lifts.eq_of_le

theorem Lifts.exists_max_two {c : Set (Lifts F E K)} {x y : Lifts F E K} (hc : IsChain (· ≤ ·) c)
    (hx : x ∈ insert ⊥ c) (hy : y ∈ insert ⊥ c) :
    ∃ z : Lifts F E K, z ∈ insert ⊥ c ∧ x ≤ z ∧ y ≤ z := by
  cases' (hc.insert fun _ _ _ => Or.inl bot_le).total hx hy with hxy hyx
  -- ⊢ ∃ z, z ∈ insert ⊥ c ∧ x ≤ z ∧ y ≤ z
  · exact ⟨y, hy, hxy, le_refl y⟩
    -- 🎉 no goals
  · exact ⟨x, hx, le_refl x, hyx⟩
    -- 🎉 no goals
#align intermediate_field.lifts.exists_max_two IntermediateField.Lifts.exists_max_two

theorem Lifts.exists_max_three {c : Set (Lifts F E K)} {x y z : Lifts F E K}
    (hc : IsChain (· ≤ ·) c) (hx : x ∈ insert ⊥ c) (hy : y ∈ insert ⊥ c)
    (hz : z ∈ insert ⊥ c) :
    ∃ w : Lifts F E K, w ∈ insert ⊥ c ∧ x ≤ w ∧ y ≤ w ∧ z ≤ w := by
  obtain ⟨v, hv, hxv, hyv⟩ := Lifts.exists_max_two hc hx hy
  -- ⊢ ∃ w, w ∈ insert ⊥ c ∧ x ≤ w ∧ y ≤ w ∧ z ≤ w
  obtain ⟨w, hw, hzw, hvw⟩ := Lifts.exists_max_two hc hz hv
  -- ⊢ ∃ w, w ∈ insert ⊥ c ∧ x ≤ w ∧ y ≤ w ∧ z ≤ w
  exact ⟨w, hw, le_trans hxv hvw, le_trans hyv hvw, hzw⟩
  -- 🎉 no goals
#align intermediate_field.lifts.exists_max_three IntermediateField.Lifts.exists_max_three

/-- An upper bound on a chain of lifts -/
def Lifts.upperBoundIntermediateField {c : Set (Lifts F E K)} (hc : IsChain (· ≤ ·) c) :
    IntermediateField F E where
  carrier s := ∃ x : Lifts F E K, x ∈ insert ⊥ c ∧ (s ∈ x.1 : Prop)
  zero_mem' := ⟨⊥, Set.mem_insert ⊥ c, zero_mem ⊥⟩
  one_mem' := ⟨⊥, Set.mem_insert ⊥ c, one_mem ⊥⟩
  inv_mem' := by rintro _ ⟨x, y, h⟩; exact ⟨x, ⟨y, x.1.inv_mem h⟩⟩
                 -- ⊢ x✝⁻¹ ∈ { toSubsemiring := { toSubmonoid := { toSubsemigroup := { carrier :=  …
                                     -- 🎉 no goals
    -- ⊢ a✝ + b✝ ∈ { toSubsemigroup := { carrier := fun s => ∃ x, x ∈ insert ⊥ c ∧ s  …
  add_mem' := by
    -- ⊢ a✝ + b✝ ∈ { toSubsemigroup := { carrier := fun s => ∃ x, x ∈ insert ⊥ c ∧ s  …
    rintro _ _ ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
    -- ⊢ a✝ * b✝ ∈ fun s => ∃ x, x ∈ insert ⊥ c ∧ s ∈ x.fst
    -- 🎉 no goals
    -- ⊢ a✝ * b✝ ∈ fun s => ∃ x, x ∈ insert ⊥ c ∧ s ∈ x.fst
    obtain ⟨z, hz, hxz, hyz⟩ := Lifts.exists_max_two hc hx hy
    -- 🎉 no goals
    exact ⟨z, hz, z.1.add_mem (hxz.1 ha) (hyz.1 hb)⟩
  mul_mem' := by
    rintro _ _ ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
    obtain ⟨z, hz, hxz, hyz⟩ := Lifts.exists_max_two hc hx hy
    exact ⟨z, hz, z.1.mul_mem (hxz.1 ha) (hyz.1 hb)⟩
  algebraMap_mem' s := ⟨⊥, Set.mem_insert ⊥ c, algebraMap_mem ⊥ s⟩
#align intermediate_field.lifts.upper_bound_intermediate_field IntermediateField.Lifts.upperBoundIntermediateField

/-- The lift on the upper bound on a chain of lifts -/
noncomputable def Lifts.upperBoundAlgHom {c : Set (Lifts F E K)} (hc : IsChain (· ≤ ·) c) :
    Lifts.upperBoundIntermediateField hc →ₐ[F] K where
  toFun s := (Classical.choose s.mem).2 ⟨s, (Classical.choose_spec s.mem).2⟩
  map_zero' := AlgHom.map_zero _
  map_one' := AlgHom.map_one _
  map_add' s t := by
    obtain ⟨w, _, hxw, hyw, hzw⟩ :=
      Lifts.exists_max_three hc (Classical.choose_spec s.mem).1 (Classical.choose_spec t.mem).1
        (Classical.choose_spec (s + t).mem).1

    simp only [Subsemiring.coe_add, Subalgebra.coe_toSubsemiring, coe_toSubalgebra,
        Lifts.eq_of_le hzw, Lifts.eq_of_le hxw, Lifts.eq_of_le hyw, ← w.2.map_add,
          AddMemClass.mk_add_mk]
  map_mul' s t := by
    obtain ⟨w, _, hxw, hyw, hzw⟩ :=
      Lifts.exists_max_three hc (Classical.choose_spec s.mem).1 (Classical.choose_spec t.mem).1
        (Classical.choose_spec (s * t).mem).1
    simp only [Submonoid.coe_mul, Subsemiring.coe_toSubmonoid, Subalgebra.coe_toSubsemiring,
      coe_toSubalgebra, Lifts.eq_of_le hzw, Lifts.eq_of_le hxw, Lifts.eq_of_le hyw, ← w.2.map_mul,
        Submonoid.mk_mul_mk]

  commutes' _ := AlgHom.commutes _ _
#align intermediate_field.lifts.upper_bound_alg_hom IntermediateField.Lifts.upperBoundAlgHom

/-- An upper bound on a chain of lifts -/
noncomputable def Lifts.upperBound {c : Set (Lifts F E K)} (hc : IsChain (· ≤ ·) c) : Lifts F E K :=
  ⟨Lifts.upperBoundIntermediateField hc, Lifts.upperBoundAlgHom hc⟩
#align intermediate_field.lifts.upper_bound IntermediateField.Lifts.upperBound

theorem Lifts.exists_upper_bound (c : Set (Lifts F E K)) (hc : IsChain (· ≤ ·) c) :
    ∃ ub, ∀ a ∈ c, a ≤ ub :=
  ⟨Lifts.upperBound hc, by
    intro x hx
    -- ⊢ x ≤ upperBound hc
    constructor
    -- ⊢ x.fst ≤ (upperBound hc).fst
    · exact fun s hs => ⟨x, Set.mem_insert_of_mem ⊥ hx, hs⟩
      -- 🎉 no goals
    · intro s t hst
      -- ⊢ ↑x.snd s = ↑(upperBound hc).snd t
      change x.2 s = (Classical.choose t.mem).2 ⟨t, (Classical.choose_spec t.mem).2⟩
      -- ⊢ ↑x.snd s = ↑(Classical.choose (_ : ↑t ∈ ↑(upperBound hc).fst)).snd { val :=  …
      obtain ⟨z, _, hxz, hyz⟩ :=
        Lifts.exists_max_two hc (Set.mem_insert_of_mem ⊥ hx) (Classical.choose_spec t.mem).1
      rw [Lifts.eq_of_le hxz, Lifts.eq_of_le hyz]
      -- ⊢ ↑z.snd { val := ↑s, property := (_ : ↑s ∈ z.fst) } = ↑z.snd { val := ↑{ val  …
      exact congr_arg z.2 (Subtype.ext hst)⟩
      -- 🎉 no goals
#align intermediate_field.lifts.exists_upper_bound IntermediateField.Lifts.exists_upper_bound

set_option maxHeartbeats 350000 in
-- Porting note: instance `alg` added by hand. The proof is very slow.
/-- Extend a lift `x : Lifts F E K` to an element `s : E` whose conjugates are all in `K` -/
noncomputable def Lifts.liftOfSplits (x : Lifts F E K) {s : E} (h1 : IsIntegral F s)
    (h2 : (minpoly F s).Splits (algebraMap F K)) : Lifts F E K :=
  let h3 : IsIntegral x.1 s := isIntegral_of_isScalarTower h1
  let key : (minpoly x.1 s).Splits x.2.toRingHom :=
    splits_of_splits_of_dvd _ (map_ne_zero (minpoly.ne_zero h1))
     ((splits_map_iff _ _).mpr (by convert h2; exact RingHom.ext fun y => x.2.commutes y))
                                   -- ⊢ RingHom.comp (↑x.snd) (algebraMap F { x_1 // x_1 ∈ x.fst }) = algebraMap F K
                                               -- 🎉 no goals
      (minpoly.dvd_map_of_isScalarTower _ _ _)
  let alg : Algebra {y // y ∈ x.fst} {y // y ∈ restrictScalars F {z // z ∈ x.fst}⟮s⟯} :=
    {z // z ∈ x.fst}⟮s⟯.toSubalgebra.algebra
  ⟨x.1⟮s⟯.restrictScalars F,
    (@algHomEquivSigma F x.1 (x.1⟮s⟯.restrictScalars F) K _ _ _ _ _ _ _
          (IntermediateField.algebra x.1⟮s⟯) (IsScalarTower.of_algebraMap_eq fun _ => rfl)).invFun
      ⟨x.2,
        (@algHomAdjoinIntegralEquiv x.1 _ E _ _ s K _ x.2.toRingHom.toAlgebra h3).invFun
          ⟨rootOfSplits x.2.toRingHom key (ne_of_gt (minpoly.degree_pos h3)), by
            rw [mem_roots (map_ne_zero (minpoly.ne_zero h3)), IsRoot, ← eval₂_eq_eval_map]
            -- ⊢ eval₂ (algebraMap { x_1 // x_1 ∈ x.fst } K) (rootOfSplits (↑x.snd) key (_ :  …
            exact map_rootOfSplits x.2.toRingHom key (ne_of_gt (minpoly.degree_pos h3))⟩⟩⟩
            -- 🎉 no goals
#align intermediate_field.lifts.lift_of_splits IntermediateField.Lifts.liftOfSplits

-- Porting note: instance `alg` added by hand.
-- Porting note: Lean3 is able to guess `φ`
theorem Lifts.le_lifts_of_splits (x : Lifts F E K) {s : E} (h1 : IsIntegral F s)
    (h2 : (minpoly F s).Splits (algebraMap F K)) : x ≤ x.liftOfSplits h1 h2 :=
  ⟨fun z hz => algebraMap_mem x.1⟮s⟯ ⟨z, hz⟩, fun t u htu =>
    Eq.symm
      (by
        let alg : Algebra x.1 x.1⟮s⟯ := x.1⟮s⟯.toSubalgebra.algebra
        -- ⊢ ↑(liftOfSplits x h1 h2).snd u = ↑x.snd t
        rw [← show algebraMap x.1 x.1⟮s⟯ t = u from Subtype.ext htu]
        -- ⊢ ↑(liftOfSplits x h1 h2).snd (↑(algebraMap { x_1 // x_1 ∈ x.fst } { x_1 // x_ …
        letI : Algebra x.1 K := x.2.toRingHom.toAlgebra
        -- ⊢ ↑(liftOfSplits x h1 h2).snd (↑(algebraMap { x_1 // x_1 ∈ x.fst } { x_1 // x_ …
        let I1 : IsIntegral x.1 s := isIntegral_of_isScalarTower h1
        -- ⊢ ↑(liftOfSplits x h1 h2).snd (↑(algebraMap { x_1 // x_1 ∈ x.fst } { x_1 // x_ …
        let key : (minpoly x.1 s).Splits x.2.toRingHom :=
          splits_of_splits_of_dvd _ (map_ne_zero (minpoly.ne_zero h1))
            ((splits_map_iff _ _).mpr (by convert h2; exact RingHom.ext fun y => x.2.commutes y))
              (minpoly.dvd_map_of_isScalarTower _ _ _)
        have I2 := (ne_of_gt (minpoly.degree_pos I1))
        -- ⊢ ↑(liftOfSplits x h1 h2).snd (↑(algebraMap { x_1 // x_1 ∈ x.fst } { x_1 // x_ …
        have I3 : rootOfSplits (AlgHom.toRingHom x.2) key (ne_of_gt (minpoly.degree_pos I1)) ∈
            (Polynomial.map (algebraMap x.1 K) (minpoly x.1 s)).roots := by
          rw [mem_roots (map_ne_zero (minpoly.ne_zero I1)), IsRoot, ← eval₂_eq_eval_map]
          exact map_rootOfSplits x.2.toRingHom key (ne_of_gt (minpoly.degree_pos I1))
        let φ : x.1⟮s⟯ →ₐ[x.1] K := ((algHomAdjoinIntegralEquiv x.1 I1).invFun
          ⟨rootOfSplits (AlgHom.toRingHom x.2) key I2, I3⟩)

        exact AlgHom.commutes φ t)⟩
        -- 🎉 no goals
#align intermediate_field.lifts.le_lifts_of_splits IntermediateField.Lifts.le_lifts_of_splits

theorem Lifts.mem_lifts_of_splits (x : Lifts F E K) {s : E} (h1 : IsIntegral F s)
    (h2 : (minpoly F s).Splits (algebraMap F K)) : s ∈ (x.liftOfSplits h1 h2).1 :=
  mem_adjoin_simple_self x.1 s
#align intermediate_field.lifts.mem_lifts_of_splits IntermediateField.Lifts.mem_lifts_of_splits

theorem Lifts.exists_lift_of_splits (x : Lifts F E K) {s : E} (h1 : IsIntegral F s)
    (h2 : (minpoly F s).Splits (algebraMap F K)) : ∃ y, x ≤ y ∧ s ∈ y.1 :=
  ⟨x.liftOfSplits h1 h2, x.le_lifts_of_splits h1 h2, x.mem_lifts_of_splits h1 h2⟩
#align intermediate_field.lifts.exists_lift_of_splits IntermediateField.Lifts.exists_lift_of_splits

theorem algHom_mk_adjoin_splits
    (hK : ∀ s ∈ S, IsIntegral F (s : E) ∧ (minpoly F s).Splits (algebraMap F K)) :
    Nonempty (adjoin F S →ₐ[F] K) := by
  obtain ⟨x, hx⟩ : ∃ m : Lifts F E K, ∀ a, m ≤ a → a = m :=
    zorn_partialOrder Lifts.exists_upper_bound
  refine'
    ⟨{ toFun := (fun s => x.2 ⟨s, adjoin_le_iff.mpr (fun s hs => _) s.mem⟩)
       map_one' := x.2.map_one
       map_mul' := (fun s t => x.2.map_mul ⟨s, _⟩ ⟨t, _⟩)
       map_zero' := x.2.map_zero
       map_add' := (fun s t => x.2.map_add ⟨s, _⟩ ⟨t, _⟩)
       commutes' := x.2.commutes }⟩
  rcases x.exists_lift_of_splits (hK s hs).1 (hK s hs).2 with ⟨y, h1, h2⟩
  -- ⊢ s ∈ ↑x.fst
  rwa [hx y h1] at h2
  -- 🎉 no goals
#align intermediate_field.alg_hom_mk_adjoin_splits IntermediateField.algHom_mk_adjoin_splits

theorem algHom_mk_adjoin_splits' (hS : adjoin F S = ⊤)
    (hK : ∀ x ∈ S, IsIntegral F (x : E) ∧ (minpoly F x).Splits (algebraMap F K)) :
    Nonempty (E →ₐ[F] K) := by
  cases' algHom_mk_adjoin_splits hK with ϕ
  -- ⊢ Nonempty (E →ₐ[F] K)
  rw [hS] at ϕ
  -- ⊢ Nonempty (E →ₐ[F] K)
  exact ⟨ϕ.comp topEquiv.symm.toAlgHom⟩
  -- 🎉 no goals
#align intermediate_field.alg_hom_mk_adjoin_splits' IntermediateField.algHom_mk_adjoin_splits'

end AlgHomMkAdjoinSplits

section Supremum

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (E1 E2 : IntermediateField K L)

theorem le_sup_toSubalgebra : E1.toSubalgebra ⊔ E2.toSubalgebra ≤ (E1 ⊔ E2).toSubalgebra :=
  sup_le (show E1 ≤ E1 ⊔ E2 from le_sup_left) (show E2 ≤ E1 ⊔ E2 from le_sup_right)
#align intermediate_field.le_sup_to_subalgebra IntermediateField.le_sup_toSubalgebra

theorem sup_toSubalgebra [h1 : FiniteDimensional K E1] [h2 : FiniteDimensional K E2] :
    (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra := by
  let S1 := E1.toSubalgebra
  -- ⊢ (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra
  let S2 := E2.toSubalgebra
  -- ⊢ (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra
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

set_option synthInstance.maxHeartbeats 30000 in
instance finiteDimensional_sup [h1 : FiniteDimensional K E1] [h2 : FiniteDimensional K E2] :
    FiniteDimensional K (E1 ⊔ E2 : IntermediateField K L) := by
  let g := Algebra.TensorProduct.productMap E1.val E2.val
  -- ⊢ FiniteDimensional K { x // x ∈ E1 ⊔ E2 }
  suffices g.range = (E1 ⊔ E2).toSubalgebra by
    have h : FiniteDimensional K (Subalgebra.toSubmodule g.range) :=
      g.toLinearMap.finiteDimensional_range
    rwa [this] at h
  rw [Algebra.TensorProduct.productMap_range, E1.range_val, E2.range_val, sup_toSubalgebra]
  -- 🎉 no goals
#align intermediate_field.finite_dimensional_sup IntermediateField.finiteDimensional_sup

instance finiteDimensional_iSup_of_finite {ι : Type*} {t : ι → IntermediateField K L}
    [h : Finite ι] [∀ i, FiniteDimensional K (t i)] :
    FiniteDimensional K (⨆ i, t i : IntermediateField K L) := by
  rw [← iSup_univ]
  -- ⊢ FiniteDimensional K { x // x ∈ ⨆ (x : ι) (_ : x ∈ Set.univ), t x }
  let P : Set ι → Prop := fun s => FiniteDimensional K (⨆ i ∈ s, t i : IntermediateField K L)
  -- ⊢ FiniteDimensional K { x // x ∈ ⨆ (x : ι) (_ : x ∈ Set.univ), t x }
  change P Set.univ
  -- ⊢ P Set.univ
  apply Set.Finite.induction_on
  all_goals dsimp only
  · exact Set.finite_univ
    -- 🎉 no goals
  · rw [iSup_emptyset]
    -- ⊢ FiniteDimensional K { x // x ∈ ⊥ }
    exact (botEquiv K L).symm.toLinearEquiv.finiteDimensional
    -- 🎉 no goals
  · intro _ s _ _ hs
    -- ⊢ FiniteDimensional K { x // x ∈ ⨆ (i : ι) (_ : i ∈ insert a✝² s), t i }
    rw [iSup_insert]
    -- ⊢ FiniteDimensional K { x // x ∈ t a✝² ⊔ ⨆ (x : ι) (_ : x ∈ s), t x }
    exact IntermediateField.finiteDimensional_sup _ _
    -- 🎉 no goals
#align intermediate_field.finite_dimensional_supr_of_finite IntermediateField.finiteDimensional_iSup_of_finite

instance finiteDimensional_iSup_of_finset {ι : Type*} {f : ι → IntermediateField K L}
    /-Porting note: changed `h` from `∀ i ∈ s, FiniteDimensional K (f i)` because this caused an
      error. See `finiteDimensional_iSup_of_finset'` for a stronger version, that was the one
      used in mathlib3.-/
    {s : Finset ι} [h : ∀ i, FiniteDimensional K (f i)] :
    FiniteDimensional K (⨆ i ∈ s, f i : IntermediateField K L) := by
  haveI : ∀ i : { i // i ∈ s }, FiniteDimensional K (f i) := fun i => h i
  -- ⊢ FiniteDimensional K { x // x ∈ ⨆ (i : ι) (_ : i ∈ s), f i }
  have : ⨆ i ∈ s, f i = ⨆ i : { i // i ∈ s }, f i :=
    le_antisymm (iSup_le fun i => iSup_le fun h => le_iSup (fun i : { i // i ∈ s } => f i) ⟨i, h⟩)
      (iSup_le fun i => le_iSup_of_le i (le_iSup_of_le i.2 le_rfl))
  exact this.symm ▸ IntermediateField.finiteDimensional_iSup_of_finite
  -- 🎉 no goals
#align intermediate_field.finite_dimensional_supr_of_finset IntermediateField.finiteDimensional_iSup_of_finset

theorem finiteDimensional_iSup_of_finset' {ι : Type*} {f : ι → IntermediateField K L}
    /-Porting note: this was the mathlib3 version. Using `[h : ...]`, as in mathlib3, causes the
    error "invalid parametric local instance".-/
    {s : Finset ι} (h : ∀ i, i ∈ s → FiniteDimensional K (f i)) :
    FiniteDimensional K (⨆ i ∈ s, f i : IntermediateField K L) := by
  haveI : ∀ i : { i // i ∈ s }, FiniteDimensional K (f i) := fun i => h i i.2
  -- ⊢ FiniteDimensional K { x // x ∈ ⨆ (i : ι) (_ : i ∈ s), f i }
  have : ⨆ i ∈ s, f i = ⨆ i : { i // i ∈ s }, f i :=
    le_antisymm (iSup_le fun i => iSup_le fun h => le_iSup (fun i : { i // i ∈ s } => f i) ⟨i, h⟩)
      (iSup_le fun i => le_iSup_of_le i (le_iSup_of_le i.2 le_rfl))
  exact this.symm ▸ IntermediateField.finiteDimensional_iSup_of_finite
  -- 🎉 no goals

/-- A compositum of algebraic extensions is algebraic -/
theorem isAlgebraic_iSup {ι : Type*} {f : ι → IntermediateField K L}
    (h : ∀ i, Algebra.IsAlgebraic K (f i)) :
    Algebra.IsAlgebraic K (⨆ i, f i : IntermediateField K L) := by
  rintro ⟨x, hx⟩
  -- ⊢ IsAlgebraic K { val := x, property := hx }
  obtain ⟨s, hx⟩ := exists_finset_of_mem_supr' hx
  -- ⊢ IsAlgebraic K { val := x, property := hx✝ }
  rw [isAlgebraic_iff, Subtype.coe_mk, ← Subtype.coe_mk (p := fun x => x ∈ _) x hx,
    ← isAlgebraic_iff]
  haveI : ∀ i : Σ i, f i, FiniteDimensional K K⟮(i.2 : L)⟯ := fun ⟨i, x⟩ =>
    adjoin.finiteDimensional (isIntegral_iff.1 (isAlgebraic_iff_isIntegral.1 (h i x)))
  apply Algebra.isAlgebraic_of_finite
  -- 🎉 no goals
#align intermediate_field.is_algebraic_supr IntermediateField.isAlgebraic_iSup

end Supremum

end IntermediateField

section PowerBasis

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

namespace PowerBasis

open IntermediateField

/-- `pb.equivAdjoinSimple` is the equivalence between `K⟮pb.gen⟯` and `L` itself. -/
noncomputable def equivAdjoinSimple (pb : PowerBasis K L) : K⟮pb.gen⟯ ≃ₐ[K] L :=
  (adjoin.powerBasis pb.isIntegral_gen).equivOfMinpoly pb
    (minpoly.eq_of_algebraMap_eq (algebraMap K⟮pb.gen⟯ L).injective
      (adjoin.powerBasis pb.isIntegral_gen).isIntegral_gen
      (by rw [adjoin.powerBasis_gen, AdjoinSimple.algebraMap_gen]))
          -- 🎉 no goals
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
  -- 🎉 no goals
#align power_basis.equiv_adjoin_simple_symm_aeval PowerBasis.equivAdjoinSimple_symm_aeval

@[simp]
theorem equivAdjoinSimple_symm_gen (pb : PowerBasis K L) :
    pb.equivAdjoinSimple.symm pb.gen = AdjoinSimple.gen K pb.gen := by
  rw [equivAdjoinSimple, equivOfMinpoly_symm, equivOfMinpoly_gen, adjoin.powerBasis_gen]
  -- 🎉 no goals
#align power_basis.equiv_adjoin_simple_symm_gen PowerBasis.equivAdjoinSimple_symm_gen

end PowerBasis

end PowerBasis
