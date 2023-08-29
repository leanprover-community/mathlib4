/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Field.InjSurj

#align_import field_theory.subfield from "leanprover-community/mathlib"@"28aa996fc6fb4317f0083c4e6daf79878d81be33"

/-!
# Subfields

Let `K` be a field. This file defines the "bundled" subfield type `Subfield K`, a type
whose terms correspond to subfields of `K`. This is the preferred way to talk
about subfields in mathlib. Unbundled subfields (`s : Set K` and `IsSubfield s`)
are not in this file, and they will ultimately be deprecated.

We prove that subfields are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `Set R` to `Subfield R`, sending a subset of `R`
to the subfield it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(K : Type u) [Field K] (L : Type u) [Field L] (f g : K →+* L)`
`(A : Subfield K) (B : Subfield L) (s : Set K)`

* `Subfield R` : the type of subfields of a ring `R`.

* `instance : CompleteLattice (Subfield R)` : the complete lattice structure on the subfields.

* `Subfield.closure` : subfield closure of a set, i.e., the smallest subfield that includes the set.

* `Subfield.gi` : `closure : Set M → Subfield M` and coercion `(↑) : Subfield M → Set M`
  form a `GaloisInsertion`.

* `comap f B : Subfield K` : the preimage of a subfield `B` along the ring homomorphism `f`

* `map f A : Subfield L` : the image of a subfield `A` along the ring homomorphism `f`.

* `prod A B : Subfield (K × L)` : the product of subfields

* `f.fieldRange : Subfield B` : the range of the ring homomorphism `f`.

* `eqLocusField f g : Subfield K` : given ring homomorphisms `f g : K →+* R`,
     the subfield of `K` where `f x = g x`

## Implementation notes

A subfield is implemented as a subring which is closed under `⁻¹`.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a subfield's underlying set.

## Tags
subfield, subfields
-/


open BigOperators

universe u v w

variable {K : Type u} {L : Type v} {M : Type w} [Field K] [Field L] [Field M]

/-- `SubfieldClass S K` states `S` is a type of subsets `s ⊆ K` closed under field operations. -/
class SubfieldClass (S K : Type*) [Field K] [SetLike S K] extends SubringClass S K,
  InvMemClass S K : Prop
#align subfield_class SubfieldClass

namespace SubfieldClass

variable (S : Type*) [SetLike S K] [h : SubfieldClass S K]

-- See note [lower instance priority]
/-- A subfield contains `1`, products and inverses.

Be assured that we're not actually proving that subfields are subgroups:
`SubgroupClass` is really an abbreviation of `SubgroupWithOrWithoutZeroClass`.
 -/
instance (priority := 100) toSubgroupClass : SubgroupClass S K :=
  { h with }
#align subfield_class.subfield_class.to_subgroup_class SubfieldClass.toSubgroupClass

variable {S}

theorem coe_rat_mem (s : S) (x : ℚ) : (x : K) ∈ s := by
  simpa only [Rat.cast_def] using div_mem (coe_int_mem s x.num) (coe_nat_mem s x.den)
  -- 🎉 no goals
#align subfield_class.coe_rat_mem SubfieldClass.coe_rat_mem

instance (s : S) : RatCast s :=
  ⟨fun x => ⟨↑x, coe_rat_mem s x⟩⟩

@[simp]
theorem coe_rat_cast (s : S) (x : ℚ) : ((x : s) : K) = x :=
  rfl
#align subfield_class.coe_rat_cast SubfieldClass.coe_rat_cast

-- Porting note: Mistranslated: used to be (a • x : K) ∈ s
theorem rat_smul_mem (s : S) (a : ℚ) (x : s) : a • (x : K) ∈ s := by
  simpa only [Rat.smul_def] using mul_mem (coe_rat_mem s a) x.prop
  -- 🎉 no goals
#align subfield_class.rat_smul_mem SubfieldClass.rat_smul_mem

instance (s : S) : SMul ℚ s :=
  ⟨fun a x => ⟨a • (x : K), rat_smul_mem s a x⟩⟩

@[simp]
theorem coe_rat_smul (s : S) (a : ℚ) (x : s) : (a • x : K) = a • (x : K) :=
  rfl
#align subfield_class.coe_rat_smul SubfieldClass.coe_rat_smul

variable (S)

-- Prefer subclasses of `Field` over subclasses of `SubfieldClass`.
/-- A subfield inherits a field structure -/
instance (priority := 75) toField (s : S) : Field s :=
  Subtype.coe_injective.field ((↑) : s → K)
    (by rfl) (by rfl) (by intros _ _; rfl) (by intros _ _; rfl) (by intros _; rfl)
        -- 🎉 no goals
                 -- 🎉 no goals
                          -- ⊢ ↑(x✝ + y✝) = ↑x✝ + ↑y✝
                                      -- 🎉 no goals
                                               -- ⊢ ↑(x✝ * y✝) = ↑x✝ * ↑y✝
                                                           -- 🎉 no goals
                                                                    -- ⊢ ↑(-x✝) = -↑x✝
                                                                              -- 🎉 no goals
    (by intros _ _; rfl) (by intros _; rfl) (by intros _ _; rfl) (by intros _ _; rfl)
        -- ⊢ ↑(x✝ - y✝) = ↑x✝ - ↑y✝
                    -- 🎉 no goals
                             -- ⊢ ↑x✝⁻¹ = (↑x✝)⁻¹
                                       -- 🎉 no goals
                                                -- ⊢ ↑(x✝ / y✝) = ↑x✝ / ↑y✝
                                                            -- 🎉 no goals
                                                                     -- ⊢ ↑(n✝ • x✝) = n✝ • ↑x✝
                                                                                 -- 🎉 no goals
    (by intros _ _; rfl) (by intros _ _; rfl) (by intros _ _; rfl) (by intros _ _; rfl)
        -- ⊢ ↑(n✝ • x✝) = n✝ • ↑x✝
                    -- 🎉 no goals
                             -- ⊢ ↑(n✝ • x✝) = n✝ • ↑x✝
                                         -- 🎉 no goals
                                                  -- ⊢ ↑(x✝ ^ n✝) = ↑x✝ ^ n✝
                                                              -- 🎉 no goals
                                                                       -- ⊢ ↑(x✝ ^ n✝) = ↑x✝ ^ n✝
                                                                                   -- 🎉 no goals
    (by intros _; rfl) (by intros _; rfl) (by intros _; rfl)
        -- ⊢ ↑↑n✝ = ↑n✝
                  -- 🎉 no goals
                           -- ⊢ ↑↑n✝ = ↑n✝
                                     -- 🎉 no goals
                                              -- ⊢ ↑↑n✝ = ↑n✝
                                                        -- 🎉 no goals
#align subfield_class.to_field SubfieldClass.toField

-- Prefer subclasses of `Field` over subclasses of `SubfieldClass`.
/-- A subfield of a `LinearOrderedField` is a `LinearOrderedField`. -/
instance (priority := 75) toLinearOrderedField {K} [LinearOrderedField K] [SetLike S K]
    [SubfieldClass S K] (s : S) : LinearOrderedField s :=
  Subtype.coe_injective.linearOrderedField (↑) rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align subfield_class.to_linear_ordered_field SubfieldClass.toLinearOrderedField

end SubfieldClass

/-- `Subfield R` is the type of subfields of `R`. A subfield of `R` is a subset `s` that is a
  multiplicative submonoid and an additive subgroup. Note in particular that it shares the
  same 0 and 1 as R. -/
structure Subfield (K : Type u) [Field K] extends Subring K where
  /-- A subfield is closed under multiplicative inverses. -/
  inv_mem' : ∀ x ∈ carrier, x⁻¹ ∈ carrier
#align subfield Subfield

/-- Reinterpret a `Subfield` as a `Subring`. -/
add_decl_doc Subfield.toSubring

namespace Subfield

/-- The underlying `AddSubgroup` of a subfield. -/
def toAddSubgroup (s : Subfield K) : AddSubgroup K :=
  { s.toSubring.toAddSubgroup with }
#align subfield.to_add_subgroup Subfield.toAddSubgroup

-- Porting note: toSubmonoid already exists
-- /-- The underlying submonoid of a subfield. -/
-- def toSubmonoid (s : Subfield K) : Submonoid K :=
--   { s.toSubring.toSubmonoid with }
-- #align subfield.to_submonoid Subfield.toSubmonoid

instance : SetLike (Subfield K) K where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h
                             -- ⊢ { toSubring := toSubring✝, inv_mem' := inv_mem'✝ } = q
                                      -- ⊢ { toSubring := toSubring✝¹, inv_mem' := inv_mem'✝¹ } = { toSubring := toSubr …
                                               -- ⊢ toSubring✝¹ = toSubring✝
                                                      -- 🎉 no goals

instance : SubfieldClass (Subfield K) K where
  add_mem {s} := s.add_mem'
  zero_mem s := s.zero_mem'
  neg_mem {s} := s.neg_mem'
  mul_mem {s} := s.mul_mem'
  one_mem s := s.one_mem'
  inv_mem {s} := s.inv_mem' _

-- @[simp] -- Porting note: simp can prove this (with `coe_toSubring`, which comes later)
theorem mem_carrier {s : Subfield K} {x : K} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl
#align subfield.mem_carrier Subfield.mem_carrier

-- Porting note: in lean 3, `S` was type `Set K`
@[simp]
theorem mem_mk {S : Subring K} {x : K} (h) : x ∈ (⟨S, h⟩ : Subfield K) ↔ x ∈ S :=
  Iff.rfl
#align subfield.mem_mk Subfield.mem_mk

@[simp]
theorem coe_set_mk (S : Subring K) (h) : ((⟨S, h⟩ : Subfield K) : Set K) = S :=
  rfl
#align subfield.coe_set_mk Subfield.coe_set_mk

@[simp]
theorem mk_le_mk {S S' : Subring K} (h h') : (⟨S, h⟩ : Subfield K) ≤ (⟨S', h'⟩ : Subfield K) ↔
      S ≤ S' :=
  Iff.rfl
#align subfield.mk_le_mk Subfield.mk_le_mk

/-- Two subfields are equal if they have the same elements. -/
@[ext]
theorem ext {S T : Subfield K} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h
#align subfield.ext Subfield.ext

/-- Copy of a subfield with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (S : Subfield K) (s : Set K) (hs : s = ↑S) : Subfield K :=
  { S.toSubring.copy s hs with
    carrier := s
    inv_mem' := hs.symm ▸ S.inv_mem' }
#align subfield.copy Subfield.copy

@[simp]
theorem coe_copy (S : Subfield K) (s : Set K) (hs : s = ↑S) : (S.copy s hs : Set K) = s :=
  rfl
#align subfield.coe_copy Subfield.coe_copy

theorem copy_eq (S : Subfield K) (s : Set K) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs
#align subfield.copy_eq Subfield.copy_eq

@[simp]
theorem coe_toSubring (s : Subfield K) : (s.toSubring : Set K) = s :=
  rfl
#align subfield.coe_to_subring Subfield.coe_toSubring

@[simp]
theorem mem_toSubring (s : Subfield K) (x : K) : x ∈ s.toSubring ↔ x ∈ s :=
  Iff.rfl
#align subfield.mem_to_subring Subfield.mem_toSubring

end Subfield

/-- A `Subring` containing inverses is a `Subfield`. -/
def Subring.toSubfield (s : Subring K) (hinv : ∀ x ∈ s, x⁻¹ ∈ s) : Subfield K :=
  { s with inv_mem' := hinv }
#align subring.to_subfield Subring.toSubfield

namespace Subfield

variable (s t : Subfield K)

section DerivedFromSubfieldClass

/-- A subfield contains the field's 1. -/
protected theorem one_mem : (1 : K) ∈ s :=
  one_mem s
#align subfield.one_mem Subfield.one_mem

/-- A subfield contains the field's 0. -/
protected theorem zero_mem : (0 : K) ∈ s :=
  zero_mem s
#align subfield.zero_mem Subfield.zero_mem

/-- A subfield is closed under multiplication. -/
protected theorem mul_mem {x y : K} : x ∈ s → y ∈ s → x * y ∈ s :=
  mul_mem
#align subfield.mul_mem Subfield.mul_mem

/-- A subfield is closed under addition. -/
protected theorem add_mem {x y : K} : x ∈ s → y ∈ s → x + y ∈ s :=
  add_mem
#align subfield.add_mem Subfield.add_mem

/-- A subfield is closed under negation. -/
protected theorem neg_mem {x : K} : x ∈ s → -x ∈ s :=
  neg_mem
#align subfield.neg_mem Subfield.neg_mem

/-- A subfield is closed under subtraction. -/
protected theorem sub_mem {x y : K} : x ∈ s → y ∈ s → x - y ∈ s :=
  sub_mem
#align subfield.sub_mem Subfield.sub_mem

/-- A subfield is closed under inverses. -/
protected theorem inv_mem {x : K} : x ∈ s → x⁻¹ ∈ s :=
  inv_mem
#align subfield.inv_mem Subfield.inv_mem

/-- A subfield is closed under division. -/
protected theorem div_mem {x y : K} : x ∈ s → y ∈ s → x / y ∈ s :=
  div_mem
#align subfield.div_mem Subfield.div_mem

/-- Product of a list of elements in a subfield is in the subfield. -/
protected theorem list_prod_mem {l : List K} : (∀ x ∈ l, x ∈ s) → l.prod ∈ s :=
  list_prod_mem
#align subfield.list_prod_mem Subfield.list_prod_mem

/-- Sum of a list of elements in a subfield is in the subfield. -/
protected theorem list_sum_mem {l : List K} : (∀ x ∈ l, x ∈ s) → l.sum ∈ s :=
  list_sum_mem
#align subfield.list_sum_mem Subfield.list_sum_mem

/-- Product of a multiset of elements in a subfield is in the subfield. -/
protected theorem multiset_prod_mem (m : Multiset K) : (∀ a ∈ m, a ∈ s) → m.prod ∈ s :=
  multiset_prod_mem m
#align subfield.multiset_prod_mem Subfield.multiset_prod_mem

/-- Sum of a multiset of elements in a `Subfield` is in the `Subfield`. -/
protected theorem multiset_sum_mem (m : Multiset K) : (∀ a ∈ m, a ∈ s) → m.sum ∈ s :=
  multiset_sum_mem m
#align subfield.multiset_sum_mem Subfield.multiset_sum_mem

/-- Product of elements of a subfield indexed by a `Finset` is in the subfield. -/
protected theorem prod_mem {ι : Type*} {t : Finset ι} {f : ι → K} (h : ∀ c ∈ t, f c ∈ s) :
    (∏ i in t, f i) ∈ s :=
  prod_mem h
#align subfield.prod_mem Subfield.prod_mem

/-- Sum of elements in a `Subfield` indexed by a `Finset` is in the `Subfield`. -/
protected theorem sum_mem {ι : Type*} {t : Finset ι} {f : ι → K} (h : ∀ c ∈ t, f c ∈ s) :
    (∑ i in t, f i) ∈ s :=
  sum_mem h
#align subfield.sum_mem Subfield.sum_mem

protected theorem pow_mem {x : K} (hx : x ∈ s) (n : ℕ) : x ^ n ∈ s :=
  pow_mem hx n
#align subfield.pow_mem Subfield.pow_mem

protected theorem zsmul_mem {x : K} (hx : x ∈ s) (n : ℤ) : n • x ∈ s :=
  zsmul_mem hx n
#align subfield.zsmul_mem Subfield.zsmul_mem

protected theorem coe_int_mem (n : ℤ) : (n : K) ∈ s :=
  coe_int_mem s n
#align subfield.coe_int_mem Subfield.coe_int_mem

theorem zpow_mem {x : K} (hx : x ∈ s) (n : ℤ) : x ^ n ∈ s := by
  cases n
  -- ⊢ x ^ Int.ofNat a✝ ∈ s
  · simpa using s.pow_mem hx _
    -- 🎉 no goals
  · simpa [pow_succ] using s.inv_mem (s.mul_mem hx (s.pow_mem hx _))
    -- 🎉 no goals
#align subfield.zpow_mem Subfield.zpow_mem

instance : Ring s :=
  s.toSubring.toRing

instance : Div s :=
  ⟨fun x y => ⟨x / y, s.div_mem x.2 y.2⟩⟩

instance : Inv s :=
  ⟨fun x => ⟨x⁻¹, s.inv_mem x.2⟩⟩

instance : Pow s ℤ :=
  ⟨fun x z => ⟨x ^ z, s.zpow_mem x.2 z⟩⟩

/-- A subfield inherits a field structure -/
instance toField : Field s :=
  Subtype.coe_injective.field ((↑) : s → K) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) fun _ => rfl
#align subfield.to_field Subfield.toField

/-- A subfield of a `LinearOrderedField` is a `LinearOrderedField`. -/
instance toLinearOrderedField {K} [LinearOrderedField K] (s : Subfield K) : LinearOrderedField s :=
  Subtype.coe_injective.linearOrderedField (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align subfield.to_linear_ordered_field Subfield.toLinearOrderedField

@[simp, norm_cast]
theorem coe_add (x y : s) : (↑(x + y) : K) = ↑x + ↑y :=
  rfl
#align subfield.coe_add Subfield.coe_add

@[simp, norm_cast]
theorem coe_sub (x y : s) : (↑(x - y) : K) = ↑x - ↑y :=
  rfl
#align subfield.coe_sub Subfield.coe_sub

@[simp, norm_cast]
theorem coe_neg (x : s) : (↑(-x) : K) = -↑x :=
  rfl
#align subfield.coe_neg Subfield.coe_neg

@[simp, norm_cast]
theorem coe_mul (x y : s) : (↑(x * y) : K) = ↑x * ↑y :=
  rfl
#align subfield.coe_mul Subfield.coe_mul

@[simp, norm_cast]
theorem coe_div (x y : s) : (↑(x / y) : K) = ↑x / ↑y :=
  rfl
#align subfield.coe_div Subfield.coe_div

@[simp, norm_cast]
theorem coe_inv (x : s) : (↑x⁻¹ : K) = (↑x)⁻¹ :=
  rfl
#align subfield.coe_inv Subfield.coe_inv

@[simp, norm_cast]
theorem coe_zero : ((0 : s) : K) = 0 :=
  rfl
#align subfield.coe_zero Subfield.coe_zero

@[simp, norm_cast]
theorem coe_one : ((1 : s) : K) = 1 :=
  rfl
#align subfield.coe_one Subfield.coe_one

end DerivedFromSubfieldClass

/-- The embedding from a subfield of the field `K` to `K`. -/
def subtype (s : Subfield K) : s →+* K :=
  { s.toSubmonoid.subtype, s.toAddSubgroup.subtype with toFun := (↑) }
#align subfield.subtype Subfield.subtype

instance toAlgebra : Algebra s K :=
  RingHom.toAlgebra s.subtype
#align subfield.to_algebra Subfield.toAlgebra

@[simp]
theorem coe_subtype : ⇑(s.subtype) = ((↑) : s → K)  :=
  rfl
#align subfield.coe_subtype Subfield.coe_subtype

theorem toSubring_subtype_eq_subtype (F : Type*) [Field F] (S : Subfield F) :
    S.toSubring.subtype = S.subtype :=
  rfl
#align subfield.to_subring.subtype_eq_subtype Subfield.toSubring_subtype_eq_subtype

/-! # Partial order -/


--@[simp] -- Porting note: simp can prove this
theorem mem_toSubmonoid {s : Subfield K} {x : K} : x ∈ s.toSubmonoid ↔ x ∈ s :=
  Iff.rfl
#align subfield.mem_to_submonoid Subfield.mem_toSubmonoid

@[simp]
theorem coe_toSubmonoid : (s.toSubmonoid : Set K) = s :=
  rfl
#align subfield.coe_to_submonoid Subfield.coe_toSubmonoid

@[simp]
theorem mem_toAddSubgroup {s : Subfield K} {x : K} : x ∈ s.toAddSubgroup ↔ x ∈ s :=
  Iff.rfl
#align subfield.mem_to_add_subgroup Subfield.mem_toAddSubgroup

@[simp]
theorem coe_toAddSubgroup : (s.toAddSubgroup : Set K) = s :=
  rfl
#align subfield.coe_to_add_subgroup Subfield.coe_toAddSubgroup

/-! # top -/


/-- The subfield of `K` containing all elements of `K`. -/
instance : Top (Subfield K) :=
  ⟨{ (⊤ : Subring K) with inv_mem' := fun x _ => Subring.mem_top x }⟩

instance : Inhabited (Subfield K) :=
  ⟨⊤⟩

@[simp]
theorem mem_top (x : K) : x ∈ (⊤ : Subfield K) :=
  Set.mem_univ x
#align subfield.mem_top Subfield.mem_top

@[simp]
theorem coe_top : ((⊤ : Subfield K) : Set K) = Set.univ :=
  rfl
#align subfield.coe_top Subfield.coe_top

/-- The ring equiv between the top element of `Subfield K` and `K`. -/
@[simps!]
def topEquiv : (⊤ : Subfield K) ≃+* K :=
  Subsemiring.topEquiv
#align subfield.top_equiv Subfield.topEquiv

/-! # comap -/


variable (f : K →+* L)

/-- The preimage of a subfield along a ring homomorphism is a subfield. -/
def comap (s : Subfield L) : Subfield K :=
  { s.toSubring.comap f with
    inv_mem' := fun x hx =>
      show f x⁻¹ ∈ s by
        rw [map_inv₀ f]
        -- ⊢ (↑f x)⁻¹ ∈ s
        exact s.inv_mem hx }
        -- 🎉 no goals
#align subfield.comap Subfield.comap

@[simp]
theorem coe_comap (s : Subfield L) : (s.comap f : Set K) = f ⁻¹' s :=
  rfl
#align subfield.coe_comap Subfield.coe_comap

@[simp]
theorem mem_comap {s : Subfield L} {f : K →+* L} {x : K} : x ∈ s.comap f ↔ f x ∈ s :=
  Iff.rfl
#align subfield.mem_comap Subfield.mem_comap

theorem comap_comap (s : Subfield M) (g : L →+* M) (f : K →+* L) :
    (s.comap g).comap f = s.comap (g.comp f) :=
  rfl
#align subfield.comap_comap Subfield.comap_comap

/-! # map -/


/-- The image of a subfield along a ring homomorphism is a subfield. -/
def map (s : Subfield K) : Subfield L :=
  { s.toSubring.map f with
    inv_mem' := by
      rintro _ ⟨x, hx, rfl⟩
      -- ⊢ (↑f x)⁻¹ ∈ { toSubsemiring := src✝.toSubsemiring, neg_mem' := (_ : ∀ {x : L} …
      exact ⟨x⁻¹, s.inv_mem hx, map_inv₀ f x⟩ }
      -- 🎉 no goals
#align subfield.map Subfield.map

@[simp]
theorem coe_map : (s.map f : Set L) = f '' s :=
  rfl
#align subfield.coe_map Subfield.coe_map

@[simp]
theorem mem_map {f : K →+* L} {s : Subfield K} {y : L} : y ∈ s.map f ↔ ∃ x ∈ s, f x = y := by
  unfold map
  -- ⊢ (y ∈
  simp only [mem_mk, Subring.mem_mk, Subring.mem_toSubsemiring, Subring.mem_map, mem_toSubring]
  -- 🎉 no goals
#align subfield.mem_map Subfield.mem_map

theorem map_map (g : L →+* M) (f : K →+* L) : (s.map f).map g = s.map (g.comp f) :=
  SetLike.ext' <| Set.image_image _ _ _
#align subfield.map_map Subfield.map_map

theorem map_le_iff_le_comap {f : K →+* L} {s : Subfield K} {t : Subfield L} :
    s.map f ≤ t ↔ s ≤ t.comap f :=
  Set.image_subset_iff
#align subfield.map_le_iff_le_comap Subfield.map_le_iff_le_comap

theorem gc_map_comap (f : K →+* L) : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap
#align subfield.gc_map_comap Subfield.gc_map_comap

end Subfield

namespace RingHom

variable (g : L →+* M) (f : K →+* L)

/-! # range -/


/-- The range of a ring homomorphism, as a subfield of the target. See Note [range copy pattern]. -/
def fieldRange : Subfield L :=
  ((⊤ : Subfield K).map f).copy (Set.range f) Set.image_univ.symm
#align ring_hom.field_range RingHom.fieldRange

@[simp]
theorem coe_fieldRange : (f.fieldRange : Set L) = Set.range f :=
  rfl
#align ring_hom.coe_field_range RingHom.coe_fieldRange

@[simp]
theorem mem_fieldRange {f : K →+* L} {y : L} : y ∈ f.fieldRange ↔ ∃ x, f x = y :=
  Iff.rfl
#align ring_hom.mem_field_range RingHom.mem_fieldRange

theorem fieldRange_eq_map : f.fieldRange = Subfield.map f ⊤ := by
  ext
  -- ⊢ x✝ ∈ fieldRange f ↔ x✝ ∈ Subfield.map f ⊤
  simp
  -- 🎉 no goals
#align ring_hom.field_range_eq_map RingHom.fieldRange_eq_map

theorem map_fieldRange : f.fieldRange.map g = (g.comp f).fieldRange := by
  simpa only [fieldRange_eq_map] using (⊤ : Subfield K).map_map g f
  -- 🎉 no goals
#align ring_hom.map_field_range RingHom.map_fieldRange

/-- The range of a morphism of fields is a fintype, if the domain is a fintype.

Note that this instance can cause a diamond with `Subtype.Fintype` if `L` is also a fintype.-/
instance fintypeFieldRange [Fintype K] [DecidableEq L] (f : K →+* L) : Fintype f.fieldRange :=
  Set.fintypeRange f
#align ring_hom.fintype_field_range RingHom.fintypeFieldRange

end RingHom

namespace Subfield

/-! # inf -/


/-- The inf of two subfields is their intersection. -/
instance : Inf (Subfield K) :=
  ⟨fun s t =>
    { s.toSubring ⊓ t.toSubring with
      inv_mem' := fun _ hx =>
        Subring.mem_inf.mpr
          ⟨s.inv_mem (Subring.mem_inf.mp hx).1, t.inv_mem (Subring.mem_inf.mp hx).2⟩ }⟩

@[simp]
theorem coe_inf (p p' : Subfield K) : ((p ⊓ p' : Subfield K) : Set K) = p.carrier ∩ p'.carrier :=
  rfl
#align subfield.coe_inf Subfield.coe_inf

@[simp]
theorem mem_inf {p p' : Subfield K} {x : K} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl
#align subfield.mem_inf Subfield.mem_inf

instance : InfSet (Subfield K) :=
  ⟨fun S =>
    { sInf (Subfield.toSubring '' S) with
      inv_mem' := by
        rintro x hx
        -- ⊢ x⁻¹ ∈ { toSubsemiring := src✝.toSubsemiring, neg_mem' := (_ : ∀ {x : K}, x ∈ …
        apply Subring.mem_sInf.mpr
        -- ⊢ ∀ (p : Subring K), p ∈ toSubring '' S → x⁻¹ ∈ p
        rintro _ ⟨p, p_mem, rfl⟩
        -- ⊢ x⁻¹ ∈ p.toSubring
        exact p.inv_mem (Subring.mem_sInf.mp hx p.toSubring ⟨p, p_mem, rfl⟩) }⟩
        -- 🎉 no goals

@[simp, norm_cast]
theorem coe_sInf (S : Set (Subfield K)) : ((sInf S : Subfield K) : Set K) = ⋂ s ∈ S, ↑s :=
  show ((sInf (Subfield.toSubring '' S) : Subring K) : Set K) = ⋂ s ∈ S, ↑s by
    ext x
    -- ⊢ x ∈ ↑(sInf (toSubring '' S)) ↔ x ∈ ⋂ (s : Subfield K) (_ : s ∈ S), ↑s
    rw [Subring.coe_sInf, Set.mem_iInter, Set.mem_iInter]
    -- ⊢ (∀ (i : Subring K), x ∈ ⋂ (_ : i ∈ toSubring '' S), ↑i) ↔ ∀ (i : Subfield K) …
    exact
      ⟨fun h s s' ⟨s_mem, s'_eq⟩ => h s.toSubring _ ⟨⟨s, s_mem, rfl⟩, s'_eq⟩,
        fun h s s' ⟨⟨s'', s''_mem, s_eq⟩, (s'_eq : ↑s = s')⟩ =>
        h s'' _ ⟨s''_mem, by simp [← s_eq, ← s'_eq]⟩⟩
#align subfield.coe_Inf Subfield.coe_sInf

theorem mem_sInf {S : Set (Subfield K)} {x : K} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Subring.mem_sInf.trans
    ⟨fun h p hp => h p.toSubring ⟨p, hp, rfl⟩, fun h _ ⟨p', hp', p_eq⟩ => p_eq ▸ h p' hp'⟩
#align subfield.mem_Inf Subfield.mem_sInf

@[simp]
theorem sInf_toSubring (s : Set (Subfield K)) :
    (sInf s).toSubring = ⨅ t ∈ s, Subfield.toSubring t := by
  ext x
  -- ⊢ x ∈ (sInf s).toSubring ↔ x ∈ ⨅ (t : Subfield K) (_ : t ∈ s), t.toSubring
  rw [mem_toSubring, mem_sInf]
  -- ⊢ (∀ (p : Subfield K), p ∈ s → x ∈ p) ↔ x ∈ ⨅ (t : Subfield K) (_ : t ∈ s), t. …
  erw [Subring.mem_sInf]
  -- ⊢ (∀ (p : Subfield K), p ∈ s → x ∈ p) ↔ ∀ (p : Subring K), (p ∈ Set.range fun  …
  exact
    ⟨fun h p ⟨p', hp⟩ => hp ▸ Subring.mem_sInf.mpr fun p ⟨hp', hp⟩ => hp ▸ h _ hp', fun h p hp =>
      h p.toSubring
        ⟨p,
          Subring.ext fun x =>
            ⟨fun hx => Subring.mem_sInf.mp hx _ ⟨hp, rfl⟩, fun hx =>
              Subring.mem_sInf.mpr fun p' ⟨_, p'_eq⟩ => p'_eq ▸ hx⟩⟩⟩
#align subfield.Inf_to_subring Subfield.sInf_toSubring

theorem isGLB_sInf (S : Set (Subfield K)) : IsGLB S (sInf S) := by
  have : ∀ {s t : Subfield K}, (s : Set K) ≤ t ↔ s ≤ t := by simp [SetLike.coe_subset_coe]
  -- ⊢ IsGLB S (sInf S)
  refine' IsGLB.of_image this _
  -- ⊢ IsGLB ((fun {x} => ↑x) '' S) ↑(sInf S)
  convert isGLB_biInf (s := S) (f := SetLike.coe)
  -- ⊢ ↑(sInf S) = ⨅ (x : Subfield K) (_ : x ∈ S), ↑x
  exact coe_sInf _
  -- 🎉 no goals
#align subfield.is_glb_Inf Subfield.isGLB_sInf

/-- Subfields of a ring form a complete lattice. -/
instance : CompleteLattice (Subfield K) :=
  { completeLatticeOfInf (Subfield K) isGLB_sInf with
    top := ⊤
    le_top := fun _ _ _ => trivial
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right
    le_inf := fun _ _ _ h₁ h₂ _ hx => ⟨h₁ hx, h₂ hx⟩ }

/-! # subfield closure of a subset -/

/-- The `Subfield` generated by a set. -/
def closure (s : Set K) : Subfield K where
  carrier := {z : K | ∃ (x : K) (_ : x ∈ Subring.closure s) (y : K)
    (_ : y ∈ Subring.closure s), x / y = z}
  zero_mem' := ⟨0, Subring.zero_mem _, 1, Subring.one_mem _, div_one _⟩
  one_mem' := ⟨1, Subring.one_mem _, 1, Subring.one_mem _, div_one _⟩
  neg_mem' {x} := by
    rintro ⟨y, hy, z, hz, x_eq⟩
    -- ⊢ -x ∈ { toSubmonoid := { toSubsemigroup := { carrier := {z | ∃ x x_1 y x_2, x …
    exact ⟨-y, Subring.neg_mem _ hy, z, hz, x_eq ▸ neg_div _ _⟩
    -- 🎉 no goals
  inv_mem' x := by rintro ⟨y, hy, z, hz, x_eq⟩; exact ⟨z, hz, y, hy, x_eq ▸ (inv_div _ _).symm ⟩
    -- ⊢ nx / dx + b✝ ∈ { toSubsemigroup := { carrier := {z | ∃ x x_1 y x_2, x / y =  …
                   -- ⊢ x⁻¹ ∈ { toSubsemiring := { toSubmonoid := { toSubsemigroup := { carrier := { …
    -- ⊢ nx / dx + ny / dy ∈ { toSubsemigroup := { carrier := {z | ∃ x x_1 y x_2, x / …
                                                -- 🎉 no goals
    -- ⊢ nx / dx + ny / dy ∈ { toSubsemigroup := { carrier := {z | ∃ x x_1 y x_2, x / …
                             -- 🎉 no goals
  add_mem' x_mem y_mem := by
    -- ⊢ nx / dx + ny / dy ∈ { toSubsemigroup := { carrier := {z | ∃ x x_1 y x_2, x / …
    -- ⊢ nx / dx * b✝ ∈ {z | ∃ x x_1 y x_2, x / y = z}
                             -- 🎉 no goals
    -- ⊢ nx / dx * (ny / dy) ∈ {z | ∃ x x_1 y x_2, x / y = z}
    obtain ⟨nx, hnx, dx, hdx, rfl⟩ := id x_mem
    obtain ⟨ny, hny, dy, hdy, rfl⟩ := id y_mem
    by_cases hx0 : dx = 0; · rwa [hx0, div_zero, zero_add]
    by_cases hy0 : dy = 0; · rwa [hy0, div_zero, add_zero]
    exact
      ⟨nx * dy + dx * ny, Subring.add_mem _ (Subring.mul_mem _ hnx hdy) (Subring.mul_mem _ hdx hny),
        dx * dy, Subring.mul_mem _ hdx hdy, (div_add_div nx ny hx0 hy0).symm⟩
  mul_mem' x_mem y_mem := by
    obtain ⟨nx, hnx, dx, hdx, rfl⟩ := id x_mem
    obtain ⟨ny, hny, dy, hdy, rfl⟩ := id y_mem
    exact
      ⟨nx * ny, Subring.mul_mem _ hnx hny, dx * dy, Subring.mul_mem _ hdx hdy,
        (div_mul_div_comm _ _ _ _).symm⟩
#align subfield.closure Subfield.closure

theorem mem_closure_iff {s : Set K} {x} :
    x ∈ closure s ↔ ∃ y ∈ Subring.closure s, ∃ z ∈ Subring.closure s, y / z = x := by
  change x ∈ (closure s).carrier ↔ ∃ y ∈ Subring.closure s, ∃ z ∈ Subring.closure s, y / z = x
  -- ⊢ x ∈ (closure s).toSubring.toSubsemiring.toSubmonoid.toSubsemigroup.carrier ↔ …
  simp only [closure, exists_prop, Set.mem_setOf_eq]
  -- 🎉 no goals
#align subfield.mem_closure_iff Subfield.mem_closure_iff

theorem subring_closure_le (s : Set K) : Subring.closure s ≤ (closure s).toSubring := fun x hx =>
  ⟨x, hx, 1, Subring.one_mem _, div_one x⟩
#align subfield.subring_closure_le Subfield.subring_closure_le

/-- The subfield generated by a set includes the set. -/
@[simp]
theorem subset_closure {s : Set K} : s ⊆ closure s :=
  Set.Subset.trans Subring.subset_closure (subring_closure_le s)
#align subfield.subset_closure Subfield.subset_closure

theorem not_mem_of_not_mem_closure {s : Set K} {P : K} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)
#align subfield.not_mem_of_not_mem_closure Subfield.not_mem_of_not_mem_closure

theorem mem_closure {x : K} {s : Set K} : x ∈ closure s ↔ ∀ S : Subfield K, s ⊆ S → x ∈ S :=
  ⟨fun ⟨_, hy, _, hz, x_eq⟩ t le =>
    x_eq ▸
      t.div_mem (Subring.mem_closure.mp hy t.toSubring le)
        (Subring.mem_closure.mp hz t.toSubring le),
    fun h => h (closure s) subset_closure⟩
#align subfield.mem_closure Subfield.mem_closure

/-- A subfield `t` includes `closure s` if and only if it includes `s`. -/
@[simp]
theorem closure_le {s : Set K} {t : Subfield K} : closure s ≤ t ↔ s ⊆ t :=
  ⟨Set.Subset.trans subset_closure, fun h _ hx => mem_closure.mp hx t h⟩
#align subfield.closure_le Subfield.closure_le

/-- Subfield closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
theorem closure_mono ⦃s t : Set K⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Set.Subset.trans h subset_closure
#align subfield.closure_mono Subfield.closure_mono

theorem closure_eq_of_le {s : Set K} {t : Subfield K} (h₁ : s ⊆ t) (h₂ : t ≤ closure s) :
    closure s = t :=
  le_antisymm (closure_le.2 h₁) h₂
#align subfield.closure_eq_of_le Subfield.closure_eq_of_le

/-- An induction principle for closure membership. If `p` holds for `1`, and all elements
of `s`, and is preserved under addition, negation, and multiplication, then `p` holds for all
elements of the closure of `s`. -/
@[elab_as_elim]
theorem closure_induction {s : Set K} {p : K → Prop} {x} (h : x ∈ closure s) (Hs : ∀ x ∈ s, p x)
    (H1 : p 1) (Hadd : ∀ x y, p x → p y → p (x + y)) (Hneg : ∀ x, p x → p (-x))
    (Hinv : ∀ x, p x → p x⁻¹) (Hmul : ∀ x y, p x → p y → p (x * y)) : p x := by
    letI : Subfield K :=
      ⟨⟨⟨⟨⟨p, by intro _ _; exact Hmul _ _⟩, H1⟩,
        by intro _ _; exact Hadd _ _, @add_neg_self K _ 1 ▸ Hadd _ _ H1 (Hneg _ H1)⟩,
          by intro _; exact Hneg _⟩, Hinv⟩
    exact (closure_le (t := this)).2 Hs h
    -- 🎉 no goals
#align subfield.closure_induction Subfield.closure_induction

variable (K)

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : GaloisInsertion (@closure K _) (↑) where
  choice s _ := closure s
  gc _ _ := closure_le
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl
#align subfield.gi Subfield.gi

variable {K}

/-- Closure of a subfield `S` equals `S`. -/
theorem closure_eq (s : Subfield K) : closure (s : Set K) = s :=
  (Subfield.gi K).l_u_eq s
#align subfield.closure_eq Subfield.closure_eq

@[simp]
theorem closure_empty : closure (∅ : Set K) = ⊥ :=
  (Subfield.gi K).gc.l_bot
#align subfield.closure_empty Subfield.closure_empty

@[simp]
theorem closure_univ : closure (Set.univ : Set K) = ⊤ :=
  @coe_top K _ ▸ closure_eq ⊤
#align subfield.closure_univ Subfield.closure_univ

theorem closure_union (s t : Set K) : closure (s ∪ t) = closure s ⊔ closure t :=
  (Subfield.gi K).gc.l_sup
#align subfield.closure_union Subfield.closure_union

theorem closure_iUnion {ι} (s : ι → Set K) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Subfield.gi K).gc.l_iSup
#align subfield.closure_Union Subfield.closure_iUnion

theorem closure_sUnion (s : Set (Set K)) : closure (⋃₀ s) = ⨆ t ∈ s, closure t :=
  (Subfield.gi K).gc.l_sSup
#align subfield.closure_sUnion Subfield.closure_sUnion

theorem map_sup (s t : Subfield K) (f : K →+* L) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
  (gc_map_comap f).l_sup
#align subfield.map_sup Subfield.map_sup

theorem map_iSup {ι : Sort*} (f : K →+* L) (s : ι → Subfield K) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup
#align subfield.map_supr Subfield.map_iSup

theorem comap_inf (s t : Subfield L) (f : K →+* L) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
  (gc_map_comap f).u_inf
#align subfield.comap_inf Subfield.comap_inf

theorem comap_iInf {ι : Sort*} (f : K →+* L) (s : ι → Subfield L) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf
#align subfield.comap_infi Subfield.comap_iInf

@[simp]
theorem map_bot (f : K →+* L) : (⊥ : Subfield K).map f = ⊥ :=
  (gc_map_comap f).l_bot
#align subfield.map_bot Subfield.map_bot

@[simp]
theorem comap_top (f : K →+* L) : (⊤ : Subfield L).comap f = ⊤ :=
  (gc_map_comap f).u_top
#align subfield.comap_top Subfield.comap_top

/-- The underlying set of a non-empty directed sSup of subfields is just a union of the subfields.
  Note that this fails without the directedness assumption (the union of two subfields is
  typically not a subfield) -/
theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subfield K} (hS : Directed (· ≤ ·) S)
    {x : K} : (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  refine' ⟨_, fun ⟨i, hi⟩ => (SetLike.le_def.1 <| le_iSup S i) hi⟩
  -- ⊢ x ∈ ⨆ (i : ι), S i → ∃ i, x ∈ S i
  suffices x ∈ closure (⋃ i, (S i : Set K)) → ∃ i, x ∈ S i by
    simpa only [closure_iUnion, closure_eq]
  refine' fun hx => closure_induction hx (fun x => Set.mem_iUnion.mp) _ _ _ _ _
  · exact hι.elim fun i => ⟨i, (S i).one_mem⟩
    -- 🎉 no goals
  · rintro x y ⟨i, hi⟩ ⟨j, hj⟩
    -- ⊢ ∃ i, x + y ∈ S i
    obtain ⟨k, hki, hkj⟩ := hS i j
    -- ⊢ ∃ i, x + y ∈ S i
    exact ⟨k, (S k).add_mem (hki hi) (hkj hj)⟩
    -- 🎉 no goals
  · rintro x ⟨i, hi⟩
    -- ⊢ ∃ i, -x ∈ S i
    exact ⟨i, (S i).neg_mem hi⟩
    -- 🎉 no goals
  · rintro x ⟨i, hi⟩
    -- ⊢ ∃ i, x⁻¹ ∈ S i
    exact ⟨i, (S i).inv_mem hi⟩
    -- 🎉 no goals
  · rintro x y ⟨i, hi⟩ ⟨j, hj⟩
    -- ⊢ ∃ i, x * y ∈ S i
    obtain ⟨k, hki, hkj⟩ := hS i j
    -- ⊢ ∃ i, x * y ∈ S i
    exact ⟨k, (S k).mul_mem (hki hi) (hkj hj)⟩
    -- 🎉 no goals
#align subfield.mem_supr_of_directed Subfield.mem_iSup_of_directed

theorem coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subfield K} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Subfield K) : Set K) = ⋃ i, ↑(S i) :=
  Set.ext fun x => by simp [mem_iSup_of_directed hS]
                      -- 🎉 no goals
#align subfield.coe_supr_of_directed Subfield.coe_iSup_of_directed

theorem mem_sSup_of_directedOn {S : Set (Subfield K)} (Sne : S.Nonempty) (hS : DirectedOn (· ≤ ·) S)
    {x : K} : x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  haveI : Nonempty S := Sne.to_subtype
  -- ⊢ x ∈ sSup S ↔ ∃ s, s ∈ S ∧ x ∈ s
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, Subtype.exists, exists_prop]
  -- 🎉 no goals
#align subfield.mem_Sup_of_directed_on Subfield.mem_sSup_of_directedOn

theorem coe_sSup_of_directedOn {S : Set (Subfield K)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(sSup S) : Set K) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]
                      -- 🎉 no goals
#align subfield.coe_Sup_of_directed_on Subfield.coe_sSup_of_directedOn

end Subfield

namespace RingHom

variable {s : Subfield K}

open Subfield

/-- Restriction of a ring homomorphism to its range interpreted as a subfield. -/
def rangeRestrictField (f : K →+* L) : K →+* f.fieldRange :=
  f.rangeSRestrict
#align ring_hom.range_restrict_field RingHom.rangeRestrictField

@[simp]
theorem coe_rangeRestrictField (f : K →+* L) (x : K) : (f.rangeRestrictField x : L) = f x :=
  rfl
#align ring_hom.coe_range_restrict_field RingHom.coe_rangeRestrictField

/-- The subfield of elements `x : R` such that `f x = g x`, i.e.,
the equalizer of f and g as a subfield of R -/
def eqLocusField (f g : K →+* L) : Subfield K :=
  { (f : K →+* L).eqLocus g with
    inv_mem' := fun x (hx : f x = g x) => show f x⁻¹ = g x⁻¹ by rw [map_inv₀ f, map_inv₀ g, hx]
                                                                -- 🎉 no goals
    carrier := { x | f x = g x } }
#align ring_hom.eq_locus_field RingHom.eqLocusField

/-- If two ring homomorphisms are equal on a set, then they are equal on its subfield closure. -/
theorem eqOn_field_closure {f g : K →+* L} {s : Set K} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocusField g from closure_le.2 h
#align ring_hom.eq_on_field_closure RingHom.eqOn_field_closure

theorem eq_of_eqOn_subfield_top {f g : K →+* L} (h : Set.EqOn f g (⊤ : Subfield K)) : f = g :=
  ext fun _ => h trivial
#align ring_hom.eq_of_eq_on_subfield_top RingHom.eq_of_eqOn_subfield_top

theorem eq_of_eqOn_of_field_closure_eq_top {s : Set K} (hs : closure s = ⊤) {f g : K →+* L}
    (h : s.EqOn f g) : f = g :=
  eq_of_eqOn_subfield_top <| hs ▸ eqOn_field_closure h
#align ring_hom.eq_of_eq_on_of_field_closure_eq_top RingHom.eq_of_eqOn_of_field_closure_eq_top

theorem field_closure_preimage_le (f : K →+* L) (s : Set L) :
    closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _ hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx
#align ring_hom.field_closure_preimage_le RingHom.field_closure_preimage_le

/-- The image under a ring homomorphism of the subfield generated by a set equals
the subfield generated by the image of the set. -/
theorem map_field_closure (f : K →+* L) (s : Set K) : (closure s).map f = closure (f '' s) :=
  le_antisymm
    (map_le_iff_le_comap.2 <|
      le_trans (closure_mono <| Set.subset_preimage_image _ _) (field_closure_preimage_le _ _))
    (closure_le.2 <| Set.image_subset _ subset_closure)
#align ring_hom.map_field_closure RingHom.map_field_closure

end RingHom

namespace Subfield

open RingHom

/-- The ring homomorphism associated to an inclusion of subfields. -/
def inclusion {S T : Subfield K} (h : S ≤ T) : S →+* T :=
  S.subtype.codRestrict _ fun x => h x.2
#align subfield.inclusion Subfield.inclusion

@[simp]
theorem fieldRange_subtype (s : Subfield K) : s.subtype.fieldRange = s :=
  SetLike.ext' <| (coe_rangeS _).trans Subtype.range_coe
#align subfield.field_range_subtype Subfield.fieldRange_subtype

end Subfield

namespace RingEquiv

variable {s t : Subfield K}

/-- Makes the identity isomorphism from a proof two subfields of a multiplicative
    monoid are equal. -/
def subfieldCongr (h : s = t) : s ≃+* t :=
  { Equiv.setCongr <| SetLike.ext'_iff.1 h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }
#align ring_equiv.subfield_congr RingEquiv.subfieldCongr

end RingEquiv

namespace Subfield

variable {s : Set K}

theorem closure_preimage_le (f : K →+* L) (s : Set L) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _ hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx
#align subfield.closure_preimage_le Subfield.closure_preimage_le

end Subfield
