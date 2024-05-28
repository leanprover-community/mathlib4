/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.FieldTheory.Tower

#align_import field_theory.intermediate_field from "leanprover-community/mathlib"@"c596622fccd6e0321979d94931c964054dea2d26"

/-!
# Intermediate fields

Let `L / K` be a field extension, given as an instance `Algebra K L`.
This file defines the type of fields in between `K` and `L`, `IntermediateField K L`.
An `IntermediateField K L` is a subfield of `L` which contains (the image of) `K`,
i.e. it is a `Subfield L` and a `Subalgebra K L`.

## Main definitions

* `IntermediateField K L` : the type of intermediate fields between `K` and `L`.
* `Subalgebra.to_intermediateField`: turns a subalgebra closed under `⁻¹`
  into an intermediate field
* `Subfield.to_intermediateField`: turns a subfield containing the image of `K`
  into an intermediate field
* `IntermediateField.map`: map an intermediate field along an `AlgHom`
* `IntermediateField.restrict_scalars`: restrict the scalars of an intermediate field to a smaller
  field in a tower of fields.

## Implementation notes

Intermediate fields are defined with a structure extending `Subfield` and `Subalgebra`.
A `Subalgebra` is closed under all operations except `⁻¹`,

## Tags
intermediate field, field extension
-/


open FiniteDimensional Polynomial

open Polynomial

variable (K L L' : Type*) [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']

/-- `S : IntermediateField K L` is a subset of `L` such that there is a field
tower `L / S / K`. -/
structure IntermediateField extends Subalgebra K L where
  inv_mem' : ∀ x ∈ carrier, x⁻¹ ∈ carrier
#align intermediate_field IntermediateField

/-- Reinterpret an `IntermediateField` as a `Subalgebra`. -/
add_decl_doc IntermediateField.toSubalgebra

variable {K L L'}
variable (S : IntermediateField K L)

namespace IntermediateField

instance : SetLike (IntermediateField K L) L :=
  ⟨fun S => S.toSubalgebra.carrier, by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
    simp ⟩

protected theorem neg_mem {x : L} (hx : x ∈ S) : -x ∈ S := by
  show -x ∈S.toSubalgebra; simpa
#align intermediate_field.neg_mem IntermediateField.neg_mem

/-- Reinterpret an `IntermediateField` as a `Subfield`. -/
def toSubfield : Subfield L :=
  { S.toSubalgebra with
    neg_mem' := S.neg_mem,
    inv_mem' := S.inv_mem' }
#align intermediate_field.to_subfield IntermediateField.toSubfield

instance : SubfieldClass (IntermediateField K L) L where
  add_mem {s} := s.add_mem'
  zero_mem {s} := s.zero_mem'
  neg_mem {s} := s.neg_mem
  mul_mem {s} := s.mul_mem'
  one_mem {s} := s.one_mem'
  inv_mem {s} := s.inv_mem' _

--@[simp] Porting note (#10618): simp can prove it
theorem mem_carrier {s : IntermediateField K L} {x : L} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl
#align intermediate_field.mem_carrier IntermediateField.mem_carrier

/-- Two intermediate fields are equal if they have the same elements. -/
@[ext]
theorem ext {S T : IntermediateField K L} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h
#align intermediate_field.ext IntermediateField.ext

@[simp]
theorem coe_toSubalgebra : (S.toSubalgebra : Set L) = S :=
  rfl
#align intermediate_field.coe_to_subalgebra IntermediateField.coe_toSubalgebra

@[simp]
theorem coe_toSubfield : (S.toSubfield : Set L) = S :=
  rfl
#align intermediate_field.coe_to_subfield IntermediateField.coe_toSubfield

@[simp]
theorem mem_mk (s : Subsemiring L) (hK : ∀ x, algebraMap K L x ∈ s) (hi) (x : L) :
    x ∈ IntermediateField.mk (Subalgebra.mk s hK) hi ↔ x ∈ s :=
  Iff.rfl
#align intermediate_field.mem_mk IntermediateField.mem_mkₓ

@[simp]
theorem mem_toSubalgebra (s : IntermediateField K L) (x : L) : x ∈ s.toSubalgebra ↔ x ∈ s :=
  Iff.rfl
#align intermediate_field.mem_to_subalgebra IntermediateField.mem_toSubalgebra

@[simp]
theorem mem_toSubfield (s : IntermediateField K L) (x : L) : x ∈ s.toSubfield ↔ x ∈ s :=
  Iff.rfl
#align intermediate_field.mem_to_subfield IntermediateField.mem_toSubfield

/-- Copy of an intermediate field with a new `carrier` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (S : IntermediateField K L) (s : Set L) (hs : s = ↑S) :
    IntermediateField K L where
  toSubalgebra := S.toSubalgebra.copy s (hs : s = S.toSubalgebra.carrier)
  inv_mem' :=
    have hs' : (S.toSubalgebra.copy s hs).carrier = S.toSubalgebra.carrier := hs
    hs'.symm ▸ S.inv_mem'
#align intermediate_field.copy IntermediateField.copy

@[simp]
theorem coe_copy (S : IntermediateField K L) (s : Set L) (hs : s = ↑S) :
    (S.copy s hs : Set L) = s :=
  rfl
#align intermediate_field.coe_copy IntermediateField.coe_copy

theorem copy_eq (S : IntermediateField K L) (s : Set L) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs
#align intermediate_field.copy_eq IntermediateField.copy_eq

section InheritedLemmas

/-! ### Lemmas inherited from more general structures

The declarations in this section derive from the fact that an `IntermediateField` is also a
subalgebra or subfield. Their use should be replaceable with the corresponding lemma from a
subobject class.
-/


/-- An intermediate field contains the image of the smaller field. -/
theorem algebraMap_mem (x : K) : algebraMap K L x ∈ S :=
  S.algebraMap_mem' x
#align intermediate_field.algebra_map_mem IntermediateField.algebraMap_mem

/-- An intermediate field is closed under scalar multiplication. -/
theorem smul_mem {y : L} : y ∈ S → ∀ {x : K}, x • y ∈ S :=
  S.toSubalgebra.smul_mem
#align intermediate_field.smul_mem IntermediateField.smul_mem

/-- An intermediate field contains the ring's 1. -/
protected theorem one_mem : (1 : L) ∈ S :=
  one_mem S
#align intermediate_field.one_mem IntermediateField.one_mem

/-- An intermediate field contains the ring's 0. -/
protected theorem zero_mem : (0 : L) ∈ S :=
  zero_mem S
#align intermediate_field.zero_mem IntermediateField.zero_mem

/-- An intermediate field is closed under multiplication. -/
protected theorem mul_mem {x y : L} : x ∈ S → y ∈ S → x * y ∈ S :=
  mul_mem
#align intermediate_field.mul_mem IntermediateField.mul_mem

/-- An intermediate field is closed under addition. -/
protected theorem add_mem {x y : L} : x ∈ S → y ∈ S → x + y ∈ S :=
  add_mem
#align intermediate_field.add_mem IntermediateField.add_mem

/-- An intermediate field is closed under subtraction -/
protected theorem sub_mem {x y : L} : x ∈ S → y ∈ S → x - y ∈ S :=
  sub_mem
#align intermediate_field.sub_mem IntermediateField.sub_mem

/-- An intermediate field is closed under inverses. -/
protected theorem inv_mem {x : L} : x ∈ S → x⁻¹ ∈ S :=
  inv_mem
#align intermediate_field.inv_mem IntermediateField.inv_mem

/-- An intermediate field is closed under division. -/
protected theorem div_mem {x y : L} : x ∈ S → y ∈ S → x / y ∈ S :=
  div_mem
#align intermediate_field.div_mem IntermediateField.div_mem

/-- Product of a list of elements in an intermediate_field is in the intermediate_field. -/
protected theorem list_prod_mem {l : List L} : (∀ x ∈ l, x ∈ S) → l.prod ∈ S :=
  list_prod_mem
#align intermediate_field.list_prod_mem IntermediateField.list_prod_mem

/-- Sum of a list of elements in an intermediate field is in the intermediate_field. -/
protected theorem list_sum_mem {l : List L} : (∀ x ∈ l, x ∈ S) → l.sum ∈ S :=
  list_sum_mem
#align intermediate_field.list_sum_mem IntermediateField.list_sum_mem

/-- Product of a multiset of elements in an intermediate field is in the intermediate_field. -/
protected theorem multiset_prod_mem (m : Multiset L) : (∀ a ∈ m, a ∈ S) → m.prod ∈ S :=
  multiset_prod_mem m
#align intermediate_field.multiset_prod_mem IntermediateField.multiset_prod_mem

/-- Sum of a multiset of elements in an `IntermediateField` is in the `IntermediateField`. -/
protected theorem multiset_sum_mem (m : Multiset L) : (∀ a ∈ m, a ∈ S) → m.sum ∈ S :=
  multiset_sum_mem m
#align intermediate_field.multiset_sum_mem IntermediateField.multiset_sum_mem

/-- Product of elements of an intermediate field indexed by a `Finset` is in the intermediate_field.
-/
protected theorem prod_mem {ι : Type*} {t : Finset ι} {f : ι → L} (h : ∀ c ∈ t, f c ∈ S) :
    (∏ i ∈ t, f i) ∈ S :=
  prod_mem h
#align intermediate_field.prod_mem IntermediateField.prod_mem

/-- Sum of elements in an `IntermediateField` indexed by a `Finset` is in the `IntermediateField`.
-/
protected theorem sum_mem {ι : Type*} {t : Finset ι} {f : ι → L} (h : ∀ c ∈ t, f c ∈ S) :
    (∑ i ∈ t, f i) ∈ S :=
  sum_mem h
#align intermediate_field.sum_mem IntermediateField.sum_mem

protected theorem pow_mem {x : L} (hx : x ∈ S) (n : ℤ) : x ^ n ∈ S :=
  zpow_mem hx n
#align intermediate_field.pow_mem IntermediateField.pow_mem

protected theorem zsmul_mem {x : L} (hx : x ∈ S) (n : ℤ) : n • x ∈ S :=
  zsmul_mem hx n
#align intermediate_field.zsmul_mem IntermediateField.zsmul_mem

protected theorem intCast_mem (n : ℤ) : (n : L) ∈ S :=
  intCast_mem S n
#align intermediate_field.coe_int_mem IntermediateField.intCast_mem

protected theorem coe_add (x y : S) : (↑(x + y) : L) = ↑x + ↑y :=
  rfl
#align intermediate_field.coe_add IntermediateField.coe_add

protected theorem coe_neg (x : S) : (↑(-x) : L) = -↑x :=
  rfl
#align intermediate_field.coe_neg IntermediateField.coe_neg

protected theorem coe_mul (x y : S) : (↑(x * y) : L) = ↑x * ↑y :=
  rfl
#align intermediate_field.coe_mul IntermediateField.coe_mul

protected theorem coe_inv (x : S) : (↑x⁻¹ : L) = (↑x)⁻¹ :=
  rfl
#align intermediate_field.coe_inv IntermediateField.coe_inv

protected theorem coe_zero : ((0 : S) : L) = 0 :=
  rfl
#align intermediate_field.coe_zero IntermediateField.coe_zero

protected theorem coe_one : ((1 : S) : L) = 1 :=
  rfl
#align intermediate_field.coe_one IntermediateField.coe_one

protected theorem coe_pow (x : S) (n : ℕ) : (↑(x ^ n : S) : L) = (x : L) ^ n :=
  SubmonoidClass.coe_pow x n
#align intermediate_field.coe_pow IntermediateField.coe_pow

end InheritedLemmas

theorem natCast_mem (n : ℕ) : (n : L) ∈ S := by simpa using intCast_mem S n
#align intermediate_field.coe_nat_mem IntermediateField.natCast_mem

-- 2024-04-05
@[deprecated _root_.natCast_mem] alias coe_nat_mem := natCast_mem
@[deprecated _root_.intCast_mem] alias coe_int_mem := intCast_mem

end IntermediateField

/-- Turn a subalgebra closed under inverses into an intermediate field -/
def Subalgebra.toIntermediateField (S : Subalgebra K L) (inv_mem : ∀ x ∈ S, x⁻¹ ∈ S) :
    IntermediateField K L :=
  { S with
    inv_mem' := inv_mem }
#align subalgebra.to_intermediate_field Subalgebra.toIntermediateField

@[simp]
theorem toSubalgebra_toIntermediateField (S : Subalgebra K L) (inv_mem : ∀ x ∈ S, x⁻¹ ∈ S) :
    (S.toIntermediateField inv_mem).toSubalgebra = S := by
  ext
  rfl
#align to_subalgebra_to_intermediate_field toSubalgebra_toIntermediateField

@[simp]
theorem toIntermediateField_toSubalgebra (S : IntermediateField K L) :
    (S.toSubalgebra.toIntermediateField fun x => S.inv_mem) = S := by
  ext
  rfl
#align to_intermediate_field_to_subalgebra toIntermediateField_toSubalgebra

/-- Turn a subalgebra satisfying `IsField` into an intermediate_field -/
def Subalgebra.toIntermediateField' (S : Subalgebra K L) (hS : IsField S) : IntermediateField K L :=
  S.toIntermediateField fun x hx => by
    by_cases hx0 : x = 0
    · rw [hx0, inv_zero]
      exact S.zero_mem
    letI hS' := hS.toField
    obtain ⟨y, hy⟩ := hS.mul_inv_cancel (show (⟨x, hx⟩ : S) ≠ 0 from Subtype.coe_ne_coe.1 hx0)
    rw [Subtype.ext_iff, S.coe_mul, S.coe_one, Subtype.coe_mk, mul_eq_one_iff_inv_eq₀ hx0] at hy
    exact hy.symm ▸ y.2
#align subalgebra.to_intermediate_field' Subalgebra.toIntermediateField'

@[simp]
theorem toSubalgebra_toIntermediateField' (S : Subalgebra K L) (hS : IsField S) :
    (S.toIntermediateField' hS).toSubalgebra = S := by
  ext
  rfl
#align to_subalgebra_to_intermediate_field' toSubalgebra_toIntermediateField'

@[simp]
theorem toIntermediateField'_toSubalgebra (S : IntermediateField K L) :
    S.toSubalgebra.toIntermediateField' (Field.toIsField S) = S := by
  ext
  rfl
#align to_intermediate_field'_to_subalgebra toIntermediateField'_toSubalgebra

/-- Turn a subfield of `L` containing the image of `K` into an intermediate field -/
def Subfield.toIntermediateField (S : Subfield L) (algebra_map_mem : ∀ x, algebraMap K L x ∈ S) :
    IntermediateField K L :=
  { S with
    algebraMap_mem' := algebra_map_mem }
#align subfield.to_intermediate_field Subfield.toIntermediateField

namespace IntermediateField

/-- An intermediate field inherits a field structure -/
instance toField : Field S :=
  S.toSubfield.toField
#align intermediate_field.to_field IntermediateField.toField

@[simp, norm_cast]
theorem coe_sum {ι : Type*} [Fintype ι] (f : ι → S) : (↑(∑ i, f i) : L) = ∑ i, (f i : L) := by
  classical
    induction' (Finset.univ : Finset ι) using Finset.induction_on with i s hi H
    · simp
    · rw [Finset.sum_insert hi, AddMemClass.coe_add, H, Finset.sum_insert hi]
#align intermediate_field.coe_sum IntermediateField.coe_sum

@[norm_cast] --Porting note (#10618): `simp` can prove it
theorem coe_prod {ι : Type*} [Fintype ι] (f : ι → S) : (↑(∏ i, f i) : L) = ∏ i, (f i : L) := by
  classical
    induction' (Finset.univ : Finset ι) using Finset.induction_on with i s hi H
    · simp
    · rw [Finset.prod_insert hi, MulMemClass.coe_mul, H, Finset.prod_insert hi]
#align intermediate_field.coe_prod IntermediateField.coe_prod

/-! `IntermediateField`s inherit structure from their `Subalgebra` coercions. -/


instance module' {R} [Semiring R] [SMul R K] [Module R L] [IsScalarTower R K L] : Module R S :=
  S.toSubalgebra.module'
#align intermediate_field.module' IntermediateField.module'

instance module : Module K S :=
  inferInstanceAs (Module K S.toSubsemiring)
#align intermediate_field.module IntermediateField.module

instance isScalarTower {R} [Semiring R] [SMul R K] [Module R L] [IsScalarTower R K L] :
    IsScalarTower R K S :=
  inferInstanceAs (IsScalarTower R K S.toSubsemiring)
#align intermediate_field.is_scalar_tower IntermediateField.isScalarTower

@[simp]
theorem coe_smul {R} [Semiring R] [SMul R K] [Module R L] [IsScalarTower R K L] (r : R) (x : S) :
    ↑(r • x : S) = (r • (x : L)) :=
  rfl
#align intermediate_field.coe_smul IntermediateField.coe_smul

#noalign intermediate_field.algebra'

instance algebra : Algebra K S :=
  inferInstanceAs (Algebra K S.toSubsemiring)
#align intermediate_field.algebra IntermediateField.algebra

#noalign intermediate_field.to_algebra

@[simp] lemma algebraMap_apply (x : S) : algebraMap S L x = x := rfl

@[simp] lemma coe_algebraMap_apply (x : K) : ↑(algebraMap K S x) = algebraMap K L x := rfl

instance isScalarTower_bot {R : Type*} [Semiring R] [Algebra L R] : IsScalarTower S L R :=
  IsScalarTower.subalgebra _ _ _ S.toSubalgebra
#align intermediate_field.is_scalar_tower_bot IntermediateField.isScalarTower_bot

instance isScalarTower_mid {R : Type*} [Semiring R] [Algebra L R] [Algebra K R]
    [IsScalarTower K L R] : IsScalarTower K S R :=
  IsScalarTower.subalgebra' _ _ _ S.toSubalgebra
#align intermediate_field.is_scalar_tower_mid IntermediateField.isScalarTower_mid

/-- Specialize `is_scalar_tower_mid` to the common case where the top field is `L` -/
instance isScalarTower_mid' : IsScalarTower K S L :=
  S.isScalarTower_mid
#align intermediate_field.is_scalar_tower_mid' IntermediateField.isScalarTower_mid'

section shortcut_instances
variable {E} [Field E] [Algebra L E] (T : IntermediateField S E) {S}
instance : Algebra S T := T.algebra
instance : Module S T := Algebra.toModule
instance : SMul S T := Algebra.toSMul
instance [Algebra K E] [IsScalarTower K L E] : IsScalarTower K S T := T.isScalarTower
end shortcut_instances

/-- Given `f : L →ₐ[K] L'`, `S.comap f` is the intermediate field between `K` and `L`
  such that `f x ∈ S ↔ x ∈ S.comap f`. -/
def comap (f : L →ₐ[K] L') (S : IntermediateField K L') : IntermediateField K L where
  __ := S.toSubalgebra.comap f
  inv_mem' x hx := show f x⁻¹ ∈ S by rw [map_inv₀ f x]; exact S.inv_mem hx

/-- Given `f : L →ₐ[K] L'`, `S.map f` is the intermediate field between `K` and `L'`
such that `x ∈ S ↔ f x ∈ S.map f`. -/
def map (f : L →ₐ[K] L') (S : IntermediateField K L) : IntermediateField K L' where
  __ := S.toSubalgebra.map f
  inv_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, S.inv_mem hx, map_inv₀ f x⟩
#align intermediate_field.map IntermediateField.map

@[simp]
theorem coe_map (f : L →ₐ[K] L') : (S.map f : Set L') = f '' S :=
  rfl
#align intermediate_field.coe_map IntermediateField.coe_map

@[simp]
theorem toSubalgebra_map (f : L →ₐ[K] L') : (S.map f).toSubalgebra = S.toSubalgebra.map f :=
  rfl

@[simp]
theorem toSubfield_map (f : L →ₐ[K] L') : (S.map f).toSubfield = S.toSubfield.map f :=
  rfl

theorem map_map {K L₁ L₂ L₃ : Type*} [Field K] [Field L₁] [Algebra K L₁] [Field L₂] [Algebra K L₂]
    [Field L₃] [Algebra K L₃] (E : IntermediateField K L₁) (f : L₁ →ₐ[K] L₂) (g : L₂ →ₐ[K] L₃) :
    (E.map f).map g = E.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _
#align intermediate_field.map_map IntermediateField.map_map

theorem map_mono (f : L →ₐ[K] L') {S T : IntermediateField K L} (h : S ≤ T) :
    S.map f ≤ T.map f :=
  SetLike.coe_mono (Set.image_subset f h)

theorem map_le_iff_le_comap {f : L →ₐ[K] L'}
    {s : IntermediateField K L} {t : IntermediateField K L'} :
    s.map f ≤ t ↔ s ≤ t.comap f :=
  Set.image_subset_iff

theorem gc_map_comap (f :L →ₐ[K] L') : GaloisConnection (map f) (comap f) :=
  fun _ _ ↦ map_le_iff_le_comap

/-- Given an equivalence `e : L ≃ₐ[K] L'` of `K`-field extensions and an intermediate
field `E` of `L/K`, `intermediateFieldMap e E` is the induced equivalence
between `E` and `E.map e` -/
def intermediateFieldMap (e : L ≃ₐ[K] L') (E : IntermediateField K L) : E ≃ₐ[K] E.map e.toAlgHom :=
  e.subalgebraMap E.toSubalgebra
#align intermediate_field.intermediate_field_map IntermediateField.intermediateFieldMap

/- We manually add these two simp lemmas because `@[simps]` before `intermediate_field_map`
  led to a timeout. -/
-- This lemma has always been bad, but the linter only noticed after lean4#2644.
@[simp, nolint simpNF]
theorem intermediateFieldMap_apply_coe (e : L ≃ₐ[K] L') (E : IntermediateField K L) (a : E) :
    ↑(intermediateFieldMap e E a) = e a :=
  rfl
#align intermediate_field.intermediate_field_map_apply_coe IntermediateField.intermediateFieldMap_apply_coe

-- This lemma has always been bad, but the linter only noticed after lean4#2644.
@[simp, nolint simpNF]
theorem intermediateFieldMap_symm_apply_coe (e : L ≃ₐ[K] L') (E : IntermediateField K L)
    (a : E.map e.toAlgHom) : ↑((intermediateFieldMap e E).symm a) = e.symm a :=
  rfl
#align intermediate_field.intermediate_field_map_symm_apply_coe IntermediateField.intermediateFieldMap_symm_apply_coe

end IntermediateField

namespace AlgHom

variable (f : L →ₐ[K] L')

/-- The range of an algebra homomorphism, as an intermediate field. -/
@[simps toSubalgebra]
def fieldRange : IntermediateField K L' :=
  { f.range, (f : L →+* L').fieldRange with }
#align alg_hom.field_range AlgHom.fieldRange

@[simp]
theorem coe_fieldRange : ↑f.fieldRange = Set.range f :=
  rfl
#align alg_hom.coe_field_range AlgHom.coe_fieldRange

@[simp]
theorem fieldRange_toSubfield : f.fieldRange.toSubfield = (f : L →+* L').fieldRange :=
  rfl
#align alg_hom.field_range_to_subfield AlgHom.fieldRange_toSubfield

variable {f}

@[simp]
theorem mem_fieldRange {y : L'} : y ∈ f.fieldRange ↔ ∃ x, f x = y :=
  Iff.rfl
#align alg_hom.mem_field_range AlgHom.mem_fieldRange

end AlgHom

namespace IntermediateField

/-- The embedding from an intermediate field of `L / K` to `L`. -/
def val : S →ₐ[K] L :=
  S.toSubalgebra.val
#align intermediate_field.val IntermediateField.val

@[simp]
theorem coe_val : ⇑S.val = ((↑) : S → L) :=
  rfl
#align intermediate_field.coe_val IntermediateField.coe_val

@[simp]
theorem val_mk {x : L} (hx : x ∈ S) : S.val ⟨x, hx⟩ = x :=
  rfl
#align intermediate_field.val_mk IntermediateField.val_mk

theorem range_val : S.val.range = S.toSubalgebra :=
  S.toSubalgebra.range_val
#align intermediate_field.range_val IntermediateField.range_val

@[simp]
theorem fieldRange_val : S.val.fieldRange = S :=
  SetLike.ext' Subtype.range_val
#align intermediate_field.field_range_val IntermediateField.fieldRange_val

instance AlgHom.inhabited : Inhabited (S →ₐ[K] L) :=
  ⟨S.val⟩
#align intermediate_field.alg_hom.inhabited IntermediateField.AlgHom.inhabited

theorem aeval_coe {R : Type*} [CommRing R] [Algebra R K] [Algebra R L] [IsScalarTower R K L]
    (x : S) (P : R[X]) : aeval (x : L) P = aeval x P := by
  refine Polynomial.induction_on' P (fun f g hf hg => ?_) fun n r => ?_
  · rw [aeval_add, aeval_add, AddMemClass.coe_add, hf, hg]
  · simp only [MulMemClass.coe_mul, aeval_monomial, SubmonoidClass.coe_pow, mul_eq_mul_right_iff]
    left
    rfl
#align intermediate_field.aeval_coe IntermediateField.aeval_coe

theorem coe_isIntegral_iff {R : Type*} [CommRing R] [Algebra R K] [Algebra R L]
    [IsScalarTower R K L] {x : S} : IsIntegral R (x : L) ↔ IsIntegral R x := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨P, hPmo, hProot⟩ := h
    refine ⟨P, hPmo, (injective_iff_map_eq_zero _).1 (algebraMap (↥S) L).injective _ ?_⟩
    letI : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq (congr_fun rfl)
    rw [eval₂_eq_eval_map, ← eval₂_at_apply, eval₂_eq_eval_map, Polynomial.map_map, ←
      IsScalarTower.algebraMap_eq, ← eval₂_eq_eval_map]
    exact hProot
  · obtain ⟨P, hPmo, hProot⟩ := h
    refine ⟨P, hPmo, ?_⟩
    rw [← aeval_def, aeval_coe, aeval_def, hProot, ZeroMemClass.coe_zero]
#align intermediate_field.coe_is_integral_iff IntermediateField.coe_isIntegral_iff

/-- The map `E → F` when `E` is an intermediate field contained in the intermediate field `F`.

This is the intermediate field version of `Subalgebra.inclusion`. -/
def inclusion {E F : IntermediateField K L} (hEF : E ≤ F) : E →ₐ[K] F :=
  Subalgebra.inclusion hEF
#align intermediate_field.inclusion IntermediateField.inclusion

theorem inclusion_injective {E F : IntermediateField K L} (hEF : E ≤ F) :
    Function.Injective (inclusion hEF) :=
  Subalgebra.inclusion_injective hEF
#align intermediate_field.inclusion_injective IntermediateField.inclusion_injective

@[simp]
theorem inclusion_self {E : IntermediateField K L} : inclusion (le_refl E) = AlgHom.id K E :=
  Subalgebra.inclusion_self
#align intermediate_field.inclusion_self IntermediateField.inclusion_self

@[simp]
theorem inclusion_inclusion {E F G : IntermediateField K L} (hEF : E ≤ F) (hFG : F ≤ G) (x : E) :
    inclusion hFG (inclusion hEF x) = inclusion (le_trans hEF hFG) x :=
  Subalgebra.inclusion_inclusion hEF hFG x
#align intermediate_field.inclusion_inclusion IntermediateField.inclusion_inclusion

@[simp]
theorem coe_inclusion {E F : IntermediateField K L} (hEF : E ≤ F) (e : E) :
    (inclusion hEF e : L) = e :=
  rfl
#align intermediate_field.coe_inclusion IntermediateField.coe_inclusion

variable {S}

theorem toSubalgebra_injective :
    Function.Injective (IntermediateField.toSubalgebra : IntermediateField K L → _) := by
  intro S S' h
  ext
  rw [← mem_toSubalgebra, ← mem_toSubalgebra, h]
#align intermediate_field.to_subalgebra_injective IntermediateField.toSubalgebra_injective

theorem map_injective (f : L →ₐ[K] L'):
    Function.Injective (map f) := by
  intro _ _ h
  rwa [← toSubalgebra_injective.eq_iff, toSubalgebra_map, toSubalgebra_map,
    (Subalgebra.map_injective f.injective).eq_iff, toSubalgebra_injective.eq_iff] at h

variable (S)

theorem set_range_subset : Set.range (algebraMap K L) ⊆ S :=
  S.toSubalgebra.range_subset
#align intermediate_field.set_range_subset IntermediateField.set_range_subset

theorem fieldRange_le : (algebraMap K L).fieldRange ≤ S.toSubfield := fun x hx =>
  S.toSubalgebra.range_subset (by rwa [Set.mem_range, ← RingHom.mem_fieldRange])
#align intermediate_field.field_range_le IntermediateField.fieldRange_le

@[simp]
theorem toSubalgebra_le_toSubalgebra {S S' : IntermediateField K L} :
    S.toSubalgebra ≤ S'.toSubalgebra ↔ S ≤ S' :=
  Iff.rfl
#align intermediate_field.to_subalgebra_le_to_subalgebra IntermediateField.toSubalgebra_le_toSubalgebra

@[simp]
theorem toSubalgebra_lt_toSubalgebra {S S' : IntermediateField K L} :
    S.toSubalgebra < S'.toSubalgebra ↔ S < S' :=
  Iff.rfl
#align intermediate_field.to_subalgebra_lt_to_subalgebra IntermediateField.toSubalgebra_lt_toSubalgebra

variable {S}

section Tower

/-- Lift an intermediate_field of an intermediate_field -/
def lift {F : IntermediateField K L} (E : IntermediateField K F) : IntermediateField K L :=
  E.map (val F)
#align intermediate_field.lift IntermediateField.lift

-- Porting note: change from `HasLiftT` to `CoeOut`
instance hasLift {F : IntermediateField K L} :
    CoeOut (IntermediateField K F) (IntermediateField K L) :=
  ⟨lift⟩
#align intermediate_field.has_lift IntermediateField.hasLift

theorem lift_injective (F : IntermediateField K L) : Function.Injective F.lift :=
  map_injective F.val

section RestrictScalars

variable (K)
variable [Algebra L' L] [IsScalarTower K L' L]

/-- Given a tower `L / ↥E / L' / K` of field extensions, where `E` is an `L'`-intermediate field of
`L`, reinterpret `E` as a `K`-intermediate field of `L`. -/
def restrictScalars (E : IntermediateField L' L) : IntermediateField K L :=
  { E.toSubfield, E.toSubalgebra.restrictScalars K with
    carrier := E.carrier }
#align intermediate_field.restrict_scalars IntermediateField.restrictScalars

@[simp]
theorem coe_restrictScalars {E : IntermediateField L' L} :
    (restrictScalars K E : Set L) = (E : Set L) :=
  rfl
#align intermediate_field.coe_restrict_scalars IntermediateField.coe_restrictScalars

@[simp]
theorem restrictScalars_toSubalgebra {E : IntermediateField L' L} :
    (E.restrictScalars K).toSubalgebra = E.toSubalgebra.restrictScalars K :=
  SetLike.coe_injective rfl
#align intermediate_field.restrict_scalars_to_subalgebra IntermediateField.restrictScalars_toSubalgebra

@[simp]
theorem restrictScalars_toSubfield {E : IntermediateField L' L} :
    (E.restrictScalars K).toSubfield = E.toSubfield :=
  SetLike.coe_injective rfl
#align intermediate_field.restrict_scalars_to_subfield IntermediateField.restrictScalars_toSubfield

@[simp]
theorem mem_restrictScalars {E : IntermediateField L' L} {x : L} :
    x ∈ restrictScalars K E ↔ x ∈ E :=
  Iff.rfl
#align intermediate_field.mem_restrict_scalars IntermediateField.mem_restrictScalars

theorem restrictScalars_injective :
    Function.Injective (restrictScalars K : IntermediateField L' L → IntermediateField K L) :=
  fun U V H => ext fun x => by rw [← mem_restrictScalars K, H, mem_restrictScalars]
#align intermediate_field.restrict_scalars_injective IntermediateField.restrictScalars_injective

end RestrictScalars

/-- This was formerly an instance called `lift2_alg`, but an instance above already provides it. -/
example {F : IntermediateField K L} {E : IntermediateField F L} : Algebra K E := by infer_instance

section ExtendScalars

variable {F E E' : IntermediateField K L} (h : F ≤ E) (h' : F ≤ E') {x : L}

/-- If `F ≤ E` are two intermediate fields of `L / K`, then `E` is also an intermediate field of
`L / F`. It can be viewed as an inverse to `IntermediateField.restrictScalars`. -/
def extendScalars : IntermediateField F L := E.toSubfield.toIntermediateField fun ⟨_, hf⟩ ↦ h hf

@[simp]
theorem coe_extendScalars : (extendScalars h : Set L) = (E : Set L) := rfl

@[simp]
theorem extendScalars_toSubfield : (extendScalars h).toSubfield = E.toSubfield :=
  SetLike.coe_injective rfl

@[simp]
theorem mem_extendScalars : x ∈ extendScalars h ↔ x ∈ E := Iff.rfl

@[simp]
theorem extendScalars_restrictScalars : (extendScalars h).restrictScalars K = E := rfl

theorem extendScalars_le_extendScalars_iff : extendScalars h ≤ extendScalars h' ↔ E ≤ E' := Iff.rfl

theorem extendScalars_le_iff (E' : IntermediateField F L) :
    extendScalars h ≤ E' ↔ E ≤ E'.restrictScalars K := Iff.rfl

theorem le_extendScalars_iff (E' : IntermediateField F L) :
    E' ≤ extendScalars h ↔ E'.restrictScalars K ≤ E := Iff.rfl

variable (F)

/-- `IntermediateField.extendScalars` is an order isomorphism from
`{ E : IntermediateField K L // F ≤ E }` to `IntermediateField F L`. Its inverse is
`IntermediateField.restrictScalars`. -/
def extendScalars.orderIso : { E : IntermediateField K L // F ≤ E } ≃o IntermediateField F L where
  toFun E := extendScalars E.2
  invFun E := ⟨E.restrictScalars K, fun x hx ↦ E.algebraMap_mem ⟨x, hx⟩⟩
  left_inv E := rfl
  right_inv E := rfl
  map_rel_iff' {E E'} := by
    simp only [Equiv.coe_fn_mk]
    exact extendScalars_le_extendScalars_iff _ _

theorem extendScalars_injective :
    Function.Injective fun E : { E : IntermediateField K L // F ≤ E } ↦ extendScalars E.2 :=
  (extendScalars.orderIso F).injective

end ExtendScalars

end Tower

section FiniteDimensional

variable (F E : IntermediateField K L)

instance finiteDimensional_left [FiniteDimensional K L] : FiniteDimensional K F :=
  left K F L
#align intermediate_field.finite_dimensional_left IntermediateField.finiteDimensional_left

instance finiteDimensional_right [FiniteDimensional K L] : FiniteDimensional F L :=
  right K F L
#align intermediate_field.finite_dimensional_right IntermediateField.finiteDimensional_right

@[simp]
theorem rank_eq_rank_subalgebra : Module.rank K F.toSubalgebra = Module.rank K F :=
  rfl
#align intermediate_field.rank_eq_rank_subalgebra IntermediateField.rank_eq_rank_subalgebra

@[simp]
theorem finrank_eq_finrank_subalgebra : finrank K F.toSubalgebra = finrank K F :=
  rfl
#align intermediate_field.finrank_eq_finrank_subalgebra IntermediateField.finrank_eq_finrank_subalgebra

variable {F} {E}

@[simp]
theorem toSubalgebra_eq_iff : F.toSubalgebra = E.toSubalgebra ↔ F = E := by
  rw [SetLike.ext_iff, SetLike.ext'_iff, Set.ext_iff]
  rfl
#align intermediate_field.to_subalgebra_eq_iff IntermediateField.toSubalgebra_eq_iff

/-- If `F ≤ E` are two intermediate fields of `L / K` such that `[E : K] ≤ [F : K]` are finite,
then `F = E`. -/
theorem eq_of_le_of_finrank_le [hfin : FiniteDimensional K E] (h_le : F ≤ E)
    (h_finrank : finrank K E ≤ finrank K F) : F = E :=
  haveI : Module.Finite K E.toSubalgebra := hfin
  toSubalgebra_injective <| Subalgebra.eq_of_le_of_finrank_le h_le h_finrank
#align intermediate_field.eq_of_le_of_finrank_le IntermediateField.eq_of_le_of_finrank_le

/-- If `F ≤ E` are two intermediate fields of `L / K` such that `[F : K] = [E : K]` are finite,
then `F = E`. -/
theorem eq_of_le_of_finrank_eq [FiniteDimensional K E] (h_le : F ≤ E)
    (h_finrank : finrank K F = finrank K E) : F = E :=
  eq_of_le_of_finrank_le h_le h_finrank.ge
#align intermediate_field.eq_of_le_of_finrank_eq IntermediateField.eq_of_le_of_finrank_eq

-- If `F ≤ E` are two intermediate fields of a finite extension `L / K` such that
-- `[L : F] ≤ [L : E]`, then `F = E`. Marked as private since it's a direct corollary of
-- `eq_of_le_of_finrank_le'` (the `FiniteDimensional K L` implies `FiniteDimensional F L`
-- automatically by typeclass resolution).
private theorem eq_of_le_of_finrank_le'' [FiniteDimensional K L] (h_le : F ≤ E)
    (h_finrank : finrank F L ≤ finrank E L) : F = E := by
  apply eq_of_le_of_finrank_le h_le
  have h1 := finrank_mul_finrank K F L
  have h2 := finrank_mul_finrank K E L
  have h3 : 0 < finrank E L := finrank_pos
  nlinarith

/-- If `F ≤ E` are two intermediate fields of `L / K` such that `[L : F] ≤ [L : E]` are finite,
then `F = E`. -/
theorem eq_of_le_of_finrank_le' [FiniteDimensional F L] (h_le : F ≤ E)
    (h_finrank : finrank F L ≤ finrank E L) : F = E := by
  refine le_antisymm h_le (fun l hl ↦ ?_)
  rwa [← mem_extendScalars (le_refl F), eq_of_le_of_finrank_le''
    ((extendScalars_le_extendScalars_iff (le_refl F) h_le).2 h_le) h_finrank, mem_extendScalars]
#align intermediate_field.eq_of_le_of_finrank_le' IntermediateField.eq_of_le_of_finrank_le'

/-- If `F ≤ E` are two intermediate fields of `L / K` such that `[L : F] = [L : E]` are finite,
then `F = E`. -/
theorem eq_of_le_of_finrank_eq' [FiniteDimensional F L] (h_le : F ≤ E)
    (h_finrank : finrank F L = finrank E L) : F = E :=
  eq_of_le_of_finrank_le' h_le h_finrank.le
#align intermediate_field.eq_of_le_of_finrank_eq' IntermediateField.eq_of_le_of_finrank_eq'

end FiniteDimensional

theorem isAlgebraic_iff {x : S} : IsAlgebraic K x ↔ IsAlgebraic K (x : L) :=
  (isAlgebraic_algebraMap_iff (algebraMap S L).injective).symm
#align intermediate_field.is_algebraic_iff IntermediateField.isAlgebraic_iff

theorem isIntegral_iff {x : S} : IsIntegral K x ↔ IsIntegral K (x : L) := by
  rw [← isAlgebraic_iff_isIntegral, isAlgebraic_iff, isAlgebraic_iff_isIntegral]
#align intermediate_field.is_integral_iff IntermediateField.isIntegral_iff

theorem minpoly_eq (x : S) : minpoly K x = minpoly K (x : L) :=
  (minpoly.algebraMap_eq (algebraMap S L).injective x).symm
#align intermediate_field.minpoly_eq IntermediateField.minpoly_eq

end IntermediateField

/-- If `L/K` is algebraic, the `K`-subalgebras of `L` are all fields.  -/
def subalgebraEquivIntermediateField [Algebra.IsAlgebraic K L] :
    Subalgebra K L ≃o IntermediateField K L where
  toFun S := S.toIntermediateField fun x hx => S.inv_mem_of_algebraic
    (Algebra.IsAlgebraic.isAlgebraic ((⟨x, hx⟩ : S) : L))
  invFun S := S.toSubalgebra
  left_inv _ := toSubalgebra_toIntermediateField _ _
  right_inv := toIntermediateField_toSubalgebra
  map_rel_iff' := Iff.rfl
#align subalgebra_equiv_intermediate_field subalgebraEquivIntermediateField

@[simp]
theorem mem_subalgebraEquivIntermediateField [Algebra.IsAlgebraic K L] {S : Subalgebra K L}
    {x : L} : x ∈ subalgebraEquivIntermediateField S ↔ x ∈ S :=
  Iff.rfl
#align mem_subalgebra_equiv_intermediate_field mem_subalgebraEquivIntermediateField

@[simp]
theorem mem_subalgebraEquivIntermediateField_symm [Algebra.IsAlgebraic K L]
    {S : IntermediateField K L} {x : L} :
    x ∈ subalgebraEquivIntermediateField.symm S ↔ x ∈ S :=
  Iff.rfl
#align mem_subalgebra_equiv_intermediate_field_symm mem_subalgebraEquivIntermediateField_symm
