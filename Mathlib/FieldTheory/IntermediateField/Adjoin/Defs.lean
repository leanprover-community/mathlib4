/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
import Mathlib.FieldTheory.IntermediateField.Basic

/-!
# Adjoining Elements to Fields

In this file we introduce the notion of adjoining elements to fields.
This isn't quite the same as adjoining elements to rings.
For example, `Algebra.adjoin K {x}` might not include `x⁻¹`.

## Notation

- `F⟮α⟯`: adjoin a single element `α` to `F` (in scope `IntermediateField`).
-/

open Module Polynomial

namespace IntermediateField

section AdjoinDef

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] (S : Set E)

/-- `adjoin F S` extends a field `F` by adjoining a set `S ⊆ E`. -/
@[stacks 09FZ "first part"]
def adjoin : IntermediateField F E :=
  { Subfield.closure (Set.range (algebraMap F E) ∪ S) with
    algebraMap_mem' := fun x => Subfield.subset_closure (Or.inl (Set.mem_range_self x)) }

@[simp]
theorem adjoin_toSubfield :
    (adjoin F S).toSubfield = Subfield.closure (Set.range (algebraMap F E) ∪ S) := rfl

variable {F S} in
theorem mem_adjoin_iff_div {x : E} : x ∈ adjoin F S ↔
    ∃ r ∈ Algebra.adjoin F S, ∃ s ∈ Algebra.adjoin F S, x = r / s := by
  simp_rw [adjoin, mem_mk, Subring.mem_toSubsemiring, Subfield.mem_toSubring,
    Subfield.mem_closure_iff, ← Algebra.adjoin_eq_ring_closure, Subalgebra.mem_toSubring, eq_comm]

end AdjoinDef

section Lattice

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

@[simp]
theorem adjoin_le_iff {S : Set E} {T : IntermediateField F E} : adjoin F S ≤ T ↔ S ⊆ T :=
  ⟨fun H => le_trans (le_trans Set.subset_union_right Subfield.subset_closure) H, fun H =>
    (@Subfield.closure_le E _ (Set.range (algebraMap F E) ∪ S) T.toSubfield).mpr
      (Set.union_subset (IntermediateField.set_range_subset T) H)⟩

theorem gc : GaloisConnection (adjoin F : Set E → IntermediateField F E)
    (fun (x : IntermediateField F E) => (x : Set E)) := fun _ _ =>
  adjoin_le_iff

/-- Galois insertion between `adjoin` and `coe`. -/
def gi : GaloisInsertion (adjoin F : Set E → IntermediateField F E)
    (fun (x : IntermediateField F E) => (x : Set E)) where
  choice s hs := (adjoin F s).copy s <| le_antisymm (gc.le_u_l s) hs
  gc := IntermediateField.gc
  le_l_u S := (IntermediateField.gc (S : Set E) (adjoin F S)).1 <| le_rfl
  choice_eq _ _ := copy_eq _ _ _

instance : CompleteLattice (IntermediateField F E) where
  __ := GaloisInsertion.liftCompleteLattice IntermediateField.gi
  bot :=
    { toSubalgebra := ⊥
      inv_mem' := by rintro x ⟨r, rfl⟩; exact ⟨r⁻¹, map_inv₀ _ _⟩ }
  bot_le x := (bot_le : ⊥ ≤ x.toSubalgebra)

theorem sup_def (S T : IntermediateField F E) : S ⊔ T = adjoin F (S ∪ T : Set E) := rfl

theorem sSup_def (S : Set (IntermediateField F E)) :
    sSup S = adjoin F (⋃₀ (SetLike.coe '' S)) := rfl

instance : Inhabited (IntermediateField F E) :=
  ⟨⊤⟩

instance : Unique (IntermediateField F F) :=
  { inferInstanceAs (Inhabited (IntermediateField F F)) with
    uniq := fun _ ↦ toSubalgebra_injective <| Subsingleton.elim _ _ }

theorem coe_bot : ↑(⊥ : IntermediateField F E) = Set.range (algebraMap F E) := rfl

theorem mem_bot {x : E} : x ∈ (⊥ : IntermediateField F E) ↔ x ∈ Set.range (algebraMap F E) :=
  Iff.rfl

@[simp]
theorem bot_toSubalgebra : (⊥ : IntermediateField F E).toSubalgebra = ⊥ := rfl

theorem bot_toSubfield : (⊥ : IntermediateField F E).toSubfield = (algebraMap F E).fieldRange :=
  rfl

@[simp]
theorem coe_top : ↑(⊤ : IntermediateField F E) = (Set.univ : Set E) :=
  rfl

@[simp]
theorem mem_top {x : E} : x ∈ (⊤ : IntermediateField F E) :=
  trivial

@[simp]
theorem top_toSubalgebra : (⊤ : IntermediateField F E).toSubalgebra = ⊤ :=
  rfl

@[simp]
theorem top_toSubfield : (⊤ : IntermediateField F E).toSubfield = ⊤ :=
  rfl

@[simp, norm_cast]
theorem coe_inf (S T : IntermediateField F E) : (↑(S ⊓ T) : Set E) = (S : Set E) ∩ T :=
  rfl

@[simp]
theorem mem_inf {S T : IntermediateField F E} {x : E} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T :=
  Iff.rfl

@[simp]
theorem inf_toSubalgebra (S T : IntermediateField F E) :
    (S ⊓ T).toSubalgebra = S.toSubalgebra ⊓ T.toSubalgebra :=
  rfl

@[simp]
theorem inf_toSubfield (S T : IntermediateField F E) :
    (S ⊓ T).toSubfield = S.toSubfield ⊓ T.toSubfield :=
  rfl

@[simp]
theorem sup_toSubfield (S T : IntermediateField F E) :
    (S ⊔ T).toSubfield = S.toSubfield ⊔ T.toSubfield := by
  rw [← S.toSubfield.closure_eq, ← T.toSubfield.closure_eq, ← Subfield.closure_union]
  simp_rw [sup_def, adjoin_toSubfield, coe_toSubfield]
  congr 1
  rw [Set.union_eq_right]
  rintro _ ⟨x, rfl⟩
  exact Set.mem_union_left _ (algebraMap_mem S x)

@[simp, norm_cast]
theorem coe_sInf (S : Set (IntermediateField F E)) : (↑(sInf S) : Set E) =
    sInf ((fun (x : IntermediateField F E) => (x : Set E)) '' S) :=
  rfl

@[simp]
theorem sInf_toSubalgebra (S : Set (IntermediateField F E)) :
    (sInf S).toSubalgebra = sInf (toSubalgebra '' S) :=
  SetLike.coe_injective <| by simp

@[simp]
theorem sInf_toSubfield (S : Set (IntermediateField F E)) :
    (sInf S).toSubfield = sInf (toSubfield '' S) :=
  SetLike.coe_injective <| by simp

@[simp]
theorem sSup_toSubfield (S : Set (IntermediateField F E)) (hS : S.Nonempty) :
    (sSup S).toSubfield = sSup (toSubfield '' S) := by
  have h : toSubfield '' S = Subfield.closure '' (SetLike.coe '' S) := by
    rw [Set.image_image]
    congr! with x
    exact x.toSubfield.closure_eq.symm
  rw [h, sSup_image, ← Subfield.closure_sUnion, sSup_def, adjoin_toSubfield]
  congr 1
  rw [Set.union_eq_right]
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hS
  simp only [Set.mem_sUnion, Set.mem_image, exists_exists_and_eq_and, SetLike.mem_coe]
  exact ⟨y, hy, algebraMap_mem y x⟩

@[simp, norm_cast]
theorem coe_iInf {ι : Sort*} (S : ι → IntermediateField F E) : (↑(iInf S) : Set E) = ⋂ i, S i := by
  simp [iInf]

@[simp]
theorem iInf_toSubalgebra {ι : Sort*} (S : ι → IntermediateField F E) :
    (iInf S).toSubalgebra = ⨅ i, (S i).toSubalgebra :=
  SetLike.coe_injective <| by simp [iInf]

@[simp]
theorem iInf_toSubfield {ι : Sort*} (S : ι → IntermediateField F E) :
    (iInf S).toSubfield = ⨅ i, (S i).toSubfield :=
  SetLike.coe_injective <| by simp [iInf]

@[simp]
theorem iSup_toSubfield {ι : Sort*} [Nonempty ι] (S : ι → IntermediateField F E) :
    (iSup S).toSubfield = ⨆ i, (S i).toSubfield := by
  simp only [iSup, Set.range_nonempty, sSup_toSubfield, ← Set.range_comp, Function.comp_def]

variable (F E)

/-- The bottom intermediate_field is isomorphic to the field. -/
noncomputable def botEquiv : (⊥ : IntermediateField F E) ≃ₐ[F] F :=
  (Subalgebra.equivOfEq _ _ bot_toSubalgebra).trans (Algebra.botEquiv F E)

variable {F E}

theorem botEquiv_def (x : F) : botEquiv F E (algebraMap F (⊥ : IntermediateField F E) x) = x := by
  simp

@[simp]
theorem botEquiv_symm (x : F) : (botEquiv F E).symm x = algebraMap F _ x :=
  rfl

noncomputable instance algebraOverBot : Algebra (⊥ : IntermediateField F E) F :=
  (IntermediateField.botEquiv F E).toAlgHom.toRingHom.toAlgebra

theorem coe_algebraMap_over_bot :
    (algebraMap (⊥ : IntermediateField F E) F : (⊥ : IntermediateField F E) → F) =
      IntermediateField.botEquiv F E :=
  rfl

instance isScalarTower_over_bot : IsScalarTower (⊥ : IntermediateField F E) F E :=
  IsScalarTower.of_algebraMap_eq
    (by
      intro x
      obtain ⟨y, rfl⟩ := (botEquiv F E).symm.surjective x
      rw [coe_algebraMap_over_bot, (botEquiv F E).apply_symm_apply, botEquiv_symm,
        IsScalarTower.algebraMap_apply F (⊥ : IntermediateField F E) E])

/-- The top `IntermediateField` is isomorphic to the field.

This is the intermediate field version of `Subalgebra.topEquiv`. -/
@[simps!]
def topEquiv : (⊤ : IntermediateField F E) ≃ₐ[F] E :=
  Subalgebra.topEquiv

section RestrictScalars

@[simp]
theorem restrictScalars_bot_eq_self (K : IntermediateField F E) :
    (⊥ : IntermediateField K E).restrictScalars _ = K :=
  SetLike.coe_injective Subtype.range_coe

variable {K : Type*} [Field K] [Algebra K E] [Algebra K F] [IsScalarTower K F E]

@[simp]
theorem restrictScalars_top : (⊤ : IntermediateField F E).restrictScalars K = ⊤ :=
  rfl

variable (K)
variable (L L' : IntermediateField F E)

theorem restrictScalars_sup :
    L.restrictScalars K ⊔ L'.restrictScalars K = (L ⊔ L').restrictScalars K :=
  toSubfield_injective (by simp)

theorem restrictScalars_inf :
    L.restrictScalars K ⊓ L'.restrictScalars K = (L ⊓ L').restrictScalars K := rfl

end RestrictScalars

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

theorem map_inf (s t : IntermediateField F E) (f : E →ₐ[F] K) :
    (s ⊓ t).map f = s.map f ⊓ t.map f := SetLike.coe_injective (Set.image_inter f.injective)

theorem map_iInf {ι : Sort*} [Nonempty ι] (f : E →ₐ[F] K) (s : ι → IntermediateField F E) :
    (iInf s).map f = ⨅ i, (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective f.injective).image_iInter_eq (s := SetLike.coe ∘ s)

theorem _root_.AlgHom.fieldRange_eq_map (f : E →ₐ[F] K) :
    f.fieldRange = IntermediateField.map f ⊤ :=
  SetLike.ext' Set.image_univ.symm

theorem _root_.AlgHom.map_fieldRange {L : Type*} [Field L] [Algebra F L]
    (f : E →ₐ[F] K) (g : K →ₐ[F] L) : f.fieldRange.map g = (g.comp f).fieldRange :=
  SetLike.ext' (Set.range_comp g f).symm

theorem _root_.AlgHom.fieldRange_eq_top {f : E →ₐ[F] K} :
    f.fieldRange = ⊤ ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans Set.range_eq_univ

@[simp]
theorem _root_.AlgEquiv.fieldRange_eq_top (f : E ≃ₐ[F] K) :
    (f : E →ₐ[F] K).fieldRange = ⊤ :=
  AlgHom.fieldRange_eq_top.mpr f.surjective

end Lattice

section AdjoinDef

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] (S : Set E)

theorem adjoin_eq_range_algebraMap_adjoin :
    (adjoin F S : Set E) = Set.range (algebraMap (adjoin F S) E) :=
  Subtype.range_coe.symm

theorem adjoin.algebraMap_mem (x : F) : algebraMap F E x ∈ adjoin F S :=
  IntermediateField.algebraMap_mem (adjoin F S) x

theorem adjoin.range_algebraMap_subset : Set.range (algebraMap F E) ⊆ adjoin F S := by
  intro x hx
  obtain ⟨f, hf⟩ := hx
  rw [← hf]
  exact adjoin.algebraMap_mem F S f

instance adjoin.fieldCoe : CoeTC F (adjoin F S) where
  coe x := ⟨algebraMap F E x, adjoin.algebraMap_mem F S x⟩

theorem subset_adjoin : S ⊆ adjoin F S := fun _ hx => Subfield.subset_closure (Or.inr hx)

instance adjoin.setCoe : CoeTC S (adjoin F S) where coe x := ⟨x, subset_adjoin F S (Subtype.mem x)⟩

@[mono, gcongr]
theorem adjoin.mono (T : Set E) (h : S ⊆ T) : adjoin F S ≤ adjoin F T :=
  GaloisConnection.monotone_l gc h

theorem adjoin_contains_field_as_subfield (F : Subfield E) : (F : Set E) ⊆ adjoin F S := fun x hx =>
  adjoin.algebraMap_mem F S ⟨x, hx⟩

theorem subset_adjoin_of_subset_left {F : Subfield E} {T : Set E} (HT : T ⊆ F) : T ⊆ adjoin F S :=
  fun x hx => (adjoin F S).algebraMap_mem ⟨x, HT hx⟩

theorem subset_adjoin_of_subset_right {T : Set E} (H : T ⊆ S) : T ⊆ adjoin F S := fun _ hx =>
  subset_adjoin F S (H hx)

@[simp]
theorem adjoin_empty (F E : Type*) [Field F] [Field E] [Algebra F E] : adjoin F (∅ : Set E) = ⊥ :=
  eq_bot_iff.mpr (adjoin_le_iff.mpr (Set.empty_subset _))

@[simp]
theorem adjoin_univ (F E : Type*) [Field F] [Field E] [Algebra F E] :
    adjoin F (Set.univ : Set E) = ⊤ :=
  eq_top_iff.mpr <| subset_adjoin _ _

/-- If `K` is a field with `F ⊆ K` and `S ⊆ K` then `adjoin F S ≤ K`. -/
theorem adjoin_le_subfield {K : Subfield E} (HF : Set.range (algebraMap F E) ⊆ K) (HS : S ⊆ K) :
    (adjoin F S).toSubfield ≤ K := by
  apply Subfield.closure_le.mpr
  rw [Set.union_subset_iff]
  exact ⟨HF, HS⟩

theorem adjoin_subset_adjoin_iff {F' : Type*} [Field F'] [Algebra F' E] {S S' : Set E} :
    (adjoin F S : Set E) ⊆ adjoin F' S' ↔
      Set.range (algebraMap F E) ⊆ adjoin F' S' ∧ S ⊆ adjoin F' S' :=
  ⟨fun h => ⟨(adjoin.range_algebraMap_subset _ _).trans h,
    (subset_adjoin _ _).trans h⟩, fun ⟨hF, hS⟩ =>
      (Subfield.closure_le (t := (adjoin F' S').toSubfield)).mpr (Set.union_subset hF hS)⟩

/-- Adjoining S and then T is the same as adjoining `S ∪ T`. -/
theorem adjoin_adjoin_left (T : Set E) :
    (adjoin (adjoin F S) T).restrictScalars _ = adjoin F (S ∪ T) := by
  rw [SetLike.ext'_iff]
  change (adjoin (adjoin F S) T : Set E) = _
  apply subset_antisymm <;> rw [adjoin_subset_adjoin_iff] <;> constructor
  · rintro _ ⟨⟨x, hx⟩, rfl⟩; exact adjoin.mono _ _ _ Set.subset_union_left hx
  · exact subset_adjoin_of_subset_right _ _ Set.subset_union_right
  · exact Set.range_subset_iff.mpr fun f ↦ Subfield.subset_closure (.inl ⟨f, rfl⟩)
  · exact Set.union_subset
      (fun x hx ↦ Subfield.subset_closure <| .inl ⟨⟨x, Subfield.subset_closure (.inr hx)⟩, rfl⟩)
      (fun x hx ↦ Subfield.subset_closure <| .inr hx)

@[simp]
theorem adjoin_insert_adjoin (x : E) :
    adjoin F (insert x (adjoin F S : Set E)) = adjoin F (insert x S) :=
  le_antisymm
    (adjoin_le_iff.mpr
      (Set.insert_subset_iff.mpr
        ⟨subset_adjoin _ _ (Set.mem_insert _ _),
          adjoin_le_iff.mpr (subset_adjoin_of_subset_right _ _ (Set.subset_insert _ _))⟩))
    (by grw [← subset_adjoin])

/-- `F[S][T] = F[T][S]` -/
theorem adjoin_adjoin_comm (T : Set E) :
    (adjoin (adjoin F S) T).restrictScalars F = (adjoin (adjoin F T) S).restrictScalars F := by
  rw [adjoin_adjoin_left, adjoin_adjoin_left, Set.union_comm]

theorem adjoin_map {E' : Type*} [Field E'] [Algebra F E'] (f : E →ₐ[F] E') :
    (adjoin F S).map f = adjoin F (f '' S) :=
  le_antisymm
    (map_le_iff_le_comap.mpr <| adjoin_le_iff.mpr fun x hx ↦ subset_adjoin _ _ ⟨x, hx, rfl⟩)
    (adjoin_le_iff.mpr <| Set.monotone_image <| subset_adjoin _ _)

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

theorem adjoin_union {S T : Set E} : adjoin F (S ∪ T) = adjoin F S ⊔ adjoin F T :=
  gc.l_sup

theorem restrictScalars_adjoin_eq_sup (K : IntermediateField F E) (S : Set E) :
    restrictScalars F (adjoin K S) = K ⊔ adjoin F S := by
  rw [restrictScalars_adjoin, adjoin_union, adjoin_self]

theorem adjoin_iUnion {ι} (f : ι → Set E) : adjoin F (⋃ i, f i) = ⨆ i, adjoin F (f i) :=
  gc.l_iSup

theorem iSup_eq_adjoin {ι} (f : ι → IntermediateField F E) :
    ⨆ i, f i = adjoin F (⋃ i, f i : Set E) := by
  simp_rw [adjoin_iUnion, adjoin_self]

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

@[elab_as_elim]
theorem adjoin_induction {s : Set E} {p : ∀ x ∈ adjoin F s, Prop}
    (mem : ∀ x hx, p x (subset_adjoin _ _ hx))
    (algebraMap : ∀ x, p (algebraMap F E x) (algebraMap_mem _ _))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (inv : ∀ x hx, p x hx → p x⁻¹ (inv_mem hx))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    {x} (h : x ∈ adjoin F s) : p x h :=
  Subfield.closure_induction
    (fun x hx ↦ Or.casesOn hx (fun ⟨x, hx⟩ ↦ hx ▸ algebraMap x) (mem x))
    (by simp_rw [← (_root_.algebraMap F E).map_one]; exact algebraMap 1) add
    (fun x _ h ↦ by
      simp_rw [← neg_one_smul F x, Algebra.smul_def]; exact mul _ _ _ _ (algebraMap _) h) inv mul h

section

variable {K : Type*} [Semiring K] [Algebra F K]

theorem adjoin_algHom_ext {s : Set E} ⦃φ₁ φ₂ : adjoin F s →ₐ[F] K⦄
    (h : ∀ x hx, φ₁ ⟨x, subset_adjoin _ _ hx⟩ = φ₂ ⟨x, subset_adjoin _ _ hx⟩) :
    φ₁ = φ₂ :=
  AlgHom.ext fun ⟨x, hx⟩ ↦ adjoin_induction _ h (fun _ ↦ φ₂.commutes _ ▸ φ₁.commutes _)
    (fun _ _ _ _ h₁ h₂ ↦ by convert congr_arg₂ (· + ·) h₁ h₂ <;> rw [← map_add] <;> rfl)
    (fun _ _ ↦ eq_on_inv₀ _ _)
    (fun _ _ _ _ h₁ h₂ ↦ by convert congr_arg₂ (· * ·) h₁ h₂ <;> rw [← map_mul] <;> rfl)
    hx

theorem algHom_ext_of_eq_adjoin {S : IntermediateField F E} {s : Set E} (hS : S = adjoin F s)
    ⦃φ₁ φ₂ : S →ₐ[F] K⦄
    (h : ∀ x hx, φ₁ ⟨x, hS.ge (subset_adjoin _ _ hx)⟩ = φ₂ ⟨x, hS.ge (subset_adjoin _ _ hx)⟩) :
    φ₁ = φ₂ := by
  subst hS; exact adjoin_algHom_ext F h

end

/- Porting note (kmill): this notation is replacing the typeclass-based one I had previously
written, and it gives true `{x₁, x₂, ..., xₙ}` sets in the `adjoin` term. -/

open Lean in
/-- Supporting function for the `F⟮x₁,x₂,...,xₙ⟯` adjunction notation. -/
private partial def mkInsertTerm {m : Type → Type} [Monad m] [MonadQuotation m]
    (xs : TSyntaxArray `term) : m Term := run 0 where
  run (i : Nat) : m Term := do
    if h : i + 1 = xs.size then
      ``(singleton $(xs[i]))
    else if h : i < xs.size then
      ``(insert $(xs[i]) $(← run (i + 1)))
    else
      ``(EmptyCollection.emptyCollection)

/-- If `x₁ x₂ ... xₙ : E` then `F⟮x₁,x₂,...,xₙ⟯` is the `IntermediateField F E`
generated by these elements. -/
scoped macro:max K:term "⟮" xs:term,* "⟯" : term => do ``(adjoin $K $(← mkInsertTerm xs.getElems))

open Lean PrettyPrinter.Delaborator SubExpr in
@[app_delab IntermediateField.adjoin]
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

theorem mem_adjoin_simple_self : α ∈ F⟮α⟯ :=
  subset_adjoin F {α} (Set.mem_singleton α)

/-- generator of `F⟮α⟯` -/
def AdjoinSimple.gen : F⟮α⟯ :=
  ⟨α, mem_adjoin_simple_self F α⟩

@[simp]
theorem AdjoinSimple.coe_gen : (AdjoinSimple.gen F α : E) = α :=
  rfl

theorem AdjoinSimple.algebraMap_gen : algebraMap F⟮α⟯ E (AdjoinSimple.gen F α) = α :=
  rfl

theorem adjoin_simple_adjoin_simple (β : E) : F⟮α⟯⟮β⟯.restrictScalars F = F⟮α, β⟯ :=
  adjoin_adjoin_left _ _ _

theorem adjoin_simple_comm (β : E) : F⟮α⟯⟮β⟯.restrictScalars F = F⟮β⟯⟮α⟯.restrictScalars F :=
  adjoin_adjoin_comm _ _ _

variable {F} {α}

theorem adjoin_simple_le_iff {K : IntermediateField F E} : F⟮α⟯ ≤ K ↔ α ∈ K := by simp

theorem biSup_adjoin_simple : ⨆ x ∈ S, F⟮x⟯ = adjoin F S := by
  rw [← iSup_subtype'', ← gc.l_iSup, iSup_subtype'']; congr; exact S.biUnion_of_singleton

end AdjoinSimple

end AdjoinDef

section AdjoinIntermediateFieldLattice

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E] {α : E} {S : Set E}

@[simp]
theorem adjoin_eq_bot_iff : adjoin F S = ⊥ ↔ S ⊆ (⊥ : IntermediateField F E) := by
  rw [eq_bot_iff, adjoin_le_iff]

theorem adjoin_simple_eq_bot_iff : F⟮α⟯ = ⊥ ↔ α ∈ (⊥ : IntermediateField F E) := by
  simp

@[simp]
theorem adjoin_zero : F⟮(0 : E)⟯ = ⊥ :=
  adjoin_simple_eq_bot_iff.mpr (zero_mem ⊥)

@[simp]
theorem adjoin_one : F⟮(1 : E)⟯ = ⊥ :=
  adjoin_simple_eq_bot_iff.mpr (one_mem ⊥)

@[simp]
theorem adjoin_intCast (n : ℤ) : F⟮(n : E)⟯ = ⊥ := by
  exact adjoin_simple_eq_bot_iff.mpr (intCast_mem ⊥ n)

@[simp]
theorem adjoin_natCast (n : ℕ) : F⟮(n : E)⟯ = ⊥ :=
  adjoin_simple_eq_bot_iff.mpr (natCast_mem ⊥ n)

end AdjoinIntermediateFieldLattice

section Induction

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

/-- An intermediate field `S` is finitely generated if there exists `t : Finset E` such that
`IntermediateField.adjoin F t = S`. -/
@[stacks 09FZ "second part"]
def FG (S : IntermediateField F E) : Prop :=
  ∃ t : Finset E, adjoin F ↑t = S

theorem fg_adjoin_finset (t : Finset E) : (adjoin F (↑t : Set E)).FG :=
  ⟨t, rfl⟩

theorem fg_def {S : IntermediateField F E} : S.FG ↔ ∃ t : Set E, Set.Finite t ∧ adjoin F t = S :=
  Iff.symm Set.exists_finite_iff_finset

theorem fg_adjoin_of_finite {t : Set E} (h : Set.Finite t) : (adjoin F t).FG :=
  fg_def.mpr ⟨t, h, rfl⟩

theorem fg_bot : (⊥ : IntermediateField F E).FG :=
  ⟨∅, by simp only [Finset.coe_empty, adjoin_empty]⟩

theorem fg_sup {S T : IntermediateField F E} (hS : S.FG) (hT : T.FG) : (S ⊔ T).FG := by
  obtain ⟨s, rfl⟩ := hS; obtain ⟨t, rfl⟩ := hT
  classical rw [← adjoin_union, ← Finset.coe_union]
  exact fg_adjoin_finset _

theorem fg_iSup {ι : Sort*} [Finite ι] {S : ι → IntermediateField F E} (h : ∀ i, (S i).FG) :
    (⨆ i, S i).FG := by
  choose s hs using h
  simp_rw [← hs, ← adjoin_iUnion]
  exact fg_adjoin_of_finite (Set.finite_iUnion fun _ ↦ Finset.finite_toSet _)

theorem induction_on_adjoin_finset (S : Finset E) (P : IntermediateField F E → Prop) (base : P ⊥)
    (ih : ∀ (K : IntermediateField F E), ∀ x ∈ S, P K → P (K⟮x⟯.restrictScalars F)) :
    P (adjoin F S) := by
  classical
  refine Finset.induction_on' S ?_ (fun _ _ ha _ _ h => ?_)
  · simp [base]
  · rw [Finset.coe_insert, Set.insert_eq, Set.union_comm, ← adjoin_adjoin_left]
    exact ih (adjoin F _) _ ha h

theorem induction_on_adjoin_fg (P : IntermediateField F E → Prop) (base : P ⊥)
    (ih : ∀ (K : IntermediateField F E) (x : E), P K → P (K⟮x⟯.restrictScalars F))
    (K : IntermediateField F E) (hK : K.FG) : P K := by
  obtain ⟨S, rfl⟩ := hK
  exact induction_on_adjoin_finset S P base fun K x _ hK => ih K x hK

end Induction

end IntermediateField

namespace IntermediateField

variable {K L L' : Type*} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']

theorem map_comap_eq (f : L →ₐ[K] L') (S : IntermediateField K L') :
    (S.comap f).map f = S ⊓ f.fieldRange :=
  SetLike.coe_injective Set.image_preimage_eq_inter_range

theorem map_comap_eq_self {f : L →ₐ[K] L'} {S : IntermediateField K L'} (h : S ≤ f.fieldRange) :
    (S.comap f).map f = S := by
  simpa only [inf_of_le_left h] using map_comap_eq f S

theorem map_comap_eq_self_of_surjective {f : L →ₐ[K] L'} (hf : Function.Surjective f)
    (S : IntermediateField K L') : (S.comap f).map f = S :=
  SetLike.coe_injective (Set.image_preimage_eq _ hf)

theorem comap_map (f : L →ₐ[K] L') (S : IntermediateField K L) : (S.map f).comap f = S :=
  SetLike.coe_injective (Set.preimage_image_eq _ f.injective)

end IntermediateField

section ExtendScalars

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]

namespace Subfield

variable (F : Subfield L)

@[simp]
theorem extendScalars_self : extendScalars (le_refl F) = ⊥ := by
  ext x
  rw [mem_extendScalars, IntermediateField.mem_bot]
  refine ⟨fun h ↦ ⟨⟨x, h⟩, rfl⟩, ?_⟩
  rintro ⟨y, rfl⟩
  exact y.2

@[simp]
theorem extendScalars_top : extendScalars (le_top : F ≤ ⊤) = ⊤ :=
  IntermediateField.toSubfield_injective (by simp)

variable {F}
variable {E E' : Subfield L} (h : F ≤ E) (h' : F ≤ E')

theorem extendScalars_sup :
    extendScalars h ⊔ extendScalars h' = extendScalars (le_sup_of_le_left h : F ≤ E ⊔ E') :=
  ((extendScalars.orderIso F).map_sup ⟨_, h⟩ ⟨_, h'⟩).symm

theorem extendScalars_inf : extendScalars h ⊓ extendScalars h' = extendScalars (le_inf h h') :=
  ((extendScalars.orderIso F).map_inf ⟨_, h⟩ ⟨_, h'⟩).symm

end Subfield

namespace IntermediateField

variable (F : IntermediateField K L)

@[simp]
theorem extendScalars_self : extendScalars (le_refl F) = ⊥ :=
  restrictScalars_injective K (by simp)

@[simp]
theorem extendScalars_top : extendScalars (le_top : F ≤ ⊤) = ⊤ :=
  restrictScalars_injective K (by simp)

variable {F}
variable {E E' : IntermediateField K L} (h : F ≤ E) (h' : F ≤ E')

theorem extendScalars_sup :
    extendScalars h ⊔ extendScalars h' = extendScalars (le_sup_of_le_left h : F ≤ E ⊔ E') :=
  ((extendScalars.orderIso F).map_sup ⟨_, h⟩ ⟨_, h'⟩).symm

theorem extendScalars_inf : extendScalars h ⊓ extendScalars h' = extendScalars (le_inf h h') :=
  ((extendScalars.orderIso F).map_inf ⟨_, h⟩ ⟨_, h'⟩).symm

end IntermediateField

end ExtendScalars
