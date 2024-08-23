/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Data.Rat.Cast.Defs

/-!
# Subfields

Let `K` be a division ring, for example a field.
This file defines the "bundled" subfield type `Subfield K`, a type
whose terms correspond to subfields of `K`. Note we do not require the "subfields" to be
commutative, so they are really sub-division rings / skew fields. This is the preferred way to talk
about subfields in mathlib. Unbundled subfields (`s : Set K` and `IsSubfield s`)
are not in this file, and they will ultimately be deprecated.

We prove that subfields are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `Set K` to `Subfield K`, sending a subset of `K`
to the subfield it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(K : Type u) [DivisionRing K] (L : Type u) [DivisionRing L] (f g : K →+* L)`
`(A : Subfield K) (B : Subfield L) (s : Set K)`

* `Subfield K` : the type of subfields of a division ring `K`.

* `instance : CompleteLattice (Subfield K)` : the complete lattice structure on the subfields.

* `Subfield.closure` : subfield closure of a set, i.e., the smallest subfield that includes the set.

* `Subfield.gi` : `closure : Set M → Subfield M` and coercion `(↑) : Subfield M → Set M`
  form a `GaloisInsertion`.

* `comap f B : Subfield K` : the preimage of a subfield `B` along the ring homomorphism `f`

* `map f A : Subfield L` : the image of a subfield `A` along the ring homomorphism `f`.

* `f.fieldRange : Subfield L` : the range of the ring homomorphism `f`.

* `eqLocusField f g : Subfield K` : given ring homomorphisms `f g : K →+* R`,
     the subfield of `K` where `f x = g x`

## Implementation notes

A subfield is implemented as a subring which is closed under `⁻¹`.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a subfield's underlying set.

## Tags
subfield, subfields
-/


universe u v w

variable {K : Type u} {L : Type v} {M : Type w}
variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

/-- `SubfieldClass S K` states `S` is a type of subsets `s ⊆ K` closed under field operations. -/
class SubfieldClass (S K : Type*) [DivisionRing K] [SetLike S K] extends SubringClass S K,
  InvMemClass S K : Prop

namespace SubfieldClass

variable (S : Type*) [SetLike S K] [h : SubfieldClass S K]

-- See note [lower instance priority]
/-- A subfield contains `1`, products and inverses.

Be assured that we're not actually proving that subfields are subgroups:
`SubgroupClass` is really an abbreviation of `SubgroupWithOrWithoutZeroClass`.
 -/
instance (priority := 100) toSubgroupClass : SubgroupClass S K :=
  { h with }

variable {S} {x : K}

@[aesop safe apply (rule_sets := [SetLike])]
lemma nnratCast_mem (s : S) (q : ℚ≥0) : (q : K) ∈ s := by
  simpa only [NNRat.cast_def] using div_mem (natCast_mem s q.num) (natCast_mem s q.den)

@[aesop safe apply (rule_sets := [SetLike])]
lemma ratCast_mem (s : S) (q : ℚ) : (q : K) ∈ s := by
  simpa only [Rat.cast_def] using div_mem (intCast_mem s q.num) (natCast_mem s q.den)

instance instNNRatCast (s : S) : NNRatCast s where nnratCast q := ⟨q, nnratCast_mem s q⟩
instance instRatCast (s : S) : RatCast s where ratCast q := ⟨q, ratCast_mem s q⟩

@[simp, norm_cast] lemma coe_nnratCast (s : S) (q : ℚ≥0) : ((q : s) : K) = q := rfl
@[simp, norm_cast] lemma coe_ratCast (s : S) (x : ℚ) : ((x : s) : K) = x := rfl

@[aesop safe apply (rule_sets := [SetLike])]
lemma nnqsmul_mem (s : S) (q : ℚ≥0) (hx : x ∈ s) : q • x ∈ s := by
  simpa only [NNRat.smul_def] using mul_mem (nnratCast_mem _ _) hx

@[aesop safe apply (rule_sets := [SetLike])]
lemma qsmul_mem (s : S) (q : ℚ) (hx : x ∈ s) : q • x ∈ s := by
  simpa only [Rat.smul_def] using mul_mem (ratCast_mem _ _) hx

@[deprecated (since := "2024-04-05")] alias coe_rat_cast := coe_ratCast
@[deprecated (since := "2024-04-05")] alias coe_rat_mem := ratCast_mem
@[deprecated (since := "2024-04-05")] alias rat_smul_mem := qsmul_mem

@[aesop safe apply (rule_sets := [SetLike])]
lemma ofScientific_mem (s : S) {b : Bool} {n m : ℕ} :
    (OfScientific.ofScientific n b m : K) ∈ s :=
  SubfieldClass.nnratCast_mem s (OfScientific.ofScientific n b m)

instance instSMulNNRat (s : S) : SMul ℚ≥0 s where smul q x := ⟨q • x, nnqsmul_mem s q x.2⟩
instance instSMulRat (s : S) : SMul ℚ s where smul q x := ⟨q • x, qsmul_mem s q x.2⟩

@[simp, norm_cast] lemma coe_nnqsmul (s : S) (q : ℚ≥0) (x : s) : ↑(q • x) = q • (x : K) := rfl
@[simp, norm_cast] lemma coe_qsmul (s : S) (q : ℚ) (x : s) : ↑(q • x) = q • (x : K) := rfl

variable (S)

/-- A subfield inherits a division ring structure -/
instance (priority := 75) toDivisionRing (s : S) : DivisionRing s :=
  Subtype.coe_injective.divisionRing ((↑) : s → K)
    (by rfl) (by rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intros; rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intros; rfl) (coe_nnqsmul _) (coe_qsmul _) (by intros; rfl) (by intros; rfl)
    (by intros; rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl)

-- Prefer subclasses of `Field` over subclasses of `SubfieldClass`.
/-- A subfield of a field inherits a field structure -/
instance (priority := 75) toField {K} [Field K] [SetLike S K] [SubfieldClass S K] (s : S) :
    Field s :=
  Subtype.coe_injective.field ((↑) : s → K)
    (by rfl) (by rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intros; rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (coe_nnqsmul _) (coe_qsmul _) (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)

end SubfieldClass

/-- `Subfield R` is the type of subfields of `R`. A subfield of `R` is a subset `s` that is a
  multiplicative submonoid and an additive subgroup. Note in particular that it shares the
  same 0 and 1 as R.

  [Stacks: Definition 09FD, second part](https://stacks.math.columbia.edu/tag/09FD) -/
structure Subfield (K : Type u) [DivisionRing K] extends Subring K where
  /-- A subfield is closed under multiplicative inverses. -/
  inv_mem' : ∀ x ∈ carrier, x⁻¹ ∈ carrier

/-- Reinterpret a `Subfield` as a `Subring`. -/
add_decl_doc Subfield.toSubring

namespace Subfield

/-- The underlying `AddSubgroup` of a subfield. -/
def toAddSubgroup (s : Subfield K) : AddSubgroup K :=
  { s.toSubring.toAddSubgroup with }

-- Porting note: toSubmonoid already exists
-- /-- The underlying submonoid of a subfield. -/
-- def toSubmonoid (s : Subfield K) : Submonoid K :=
--   { s.toSubring.toSubmonoid with }

instance : SetLike (Subfield K) K where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

instance : SubfieldClass (Subfield K) K where
  add_mem {s} := s.add_mem'
  zero_mem s := s.zero_mem'
  neg_mem {s} := s.neg_mem'
  mul_mem {s} := s.mul_mem'
  one_mem s := s.one_mem'
  inv_mem {s} := s.inv_mem' _

-- @[simp] -- Porting note (#10618): simp can prove this (with `coe_toSubring`, which comes later)
theorem mem_carrier {s : Subfield K} {x : K} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

-- Porting note: in lean 3, `S` was type `Set K`
@[simp]
theorem mem_mk {S : Subring K} {x : K} (h) : x ∈ (⟨S, h⟩ : Subfield K) ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_set_mk (S : Subring K) (h) : ((⟨S, h⟩ : Subfield K) : Set K) = S :=
  rfl

@[simp]
theorem mk_le_mk {S S' : Subring K} (h h') : (⟨S, h⟩ : Subfield K) ≤ (⟨S', h'⟩ : Subfield K) ↔
    S ≤ S' :=
  Iff.rfl

/-- Two subfields are equal if they have the same elements. -/
@[ext]
theorem ext {S T : Subfield K} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy of a subfield with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (S : Subfield K) (s : Set K) (hs : s = ↑S) : Subfield K :=
  { S.toSubring.copy s hs with
    carrier := s
    inv_mem' := hs.symm ▸ S.inv_mem' }

@[simp]
theorem coe_copy (S : Subfield K) (s : Set K) (hs : s = ↑S) : (S.copy s hs : Set K) = s :=
  rfl

theorem copy_eq (S : Subfield K) (s : Set K) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

@[simp]
theorem coe_toSubring (s : Subfield K) : (s.toSubring : Set K) = s :=
  rfl

@[simp]
theorem mem_toSubring (s : Subfield K) (x : K) : x ∈ s.toSubring ↔ x ∈ s :=
  Iff.rfl

end Subfield

/-- A `Subring` containing inverses is a `Subfield`. -/
def Subring.toSubfield (s : Subring K) (hinv : ∀ x ∈ s, x⁻¹ ∈ s) : Subfield K :=
  { s with inv_mem' := hinv }

namespace Subfield

variable (s t : Subfield K)

section DerivedFromSubfieldClass

/-- A subfield contains the field's 1. -/
protected theorem one_mem : (1 : K) ∈ s :=
  one_mem s

/-- A subfield contains the field's 0. -/
protected theorem zero_mem : (0 : K) ∈ s :=
  zero_mem s

/-- A subfield is closed under multiplication. -/
protected theorem mul_mem {x y : K} : x ∈ s → y ∈ s → x * y ∈ s :=
  mul_mem

/-- A subfield is closed under addition. -/
protected theorem add_mem {x y : K} : x ∈ s → y ∈ s → x + y ∈ s :=
  add_mem

/-- A subfield is closed under negation. -/
protected theorem neg_mem {x : K} : x ∈ s → -x ∈ s :=
  neg_mem

/-- A subfield is closed under subtraction. -/
protected theorem sub_mem {x y : K} : x ∈ s → y ∈ s → x - y ∈ s :=
  sub_mem

/-- A subfield is closed under inverses. -/
protected theorem inv_mem {x : K} : x ∈ s → x⁻¹ ∈ s :=
  inv_mem

/-- A subfield is closed under division. -/
protected theorem div_mem {x y : K} : x ∈ s → y ∈ s → x / y ∈ s :=
  div_mem

/-- Product of a list of elements in a subfield is in the subfield. -/
protected theorem list_prod_mem {l : List K} : (∀ x ∈ l, x ∈ s) → l.prod ∈ s :=
  list_prod_mem

/-- Sum of a list of elements in a subfield is in the subfield. -/
protected theorem list_sum_mem {l : List K} : (∀ x ∈ l, x ∈ s) → l.sum ∈ s :=
  list_sum_mem

/-- Sum of a multiset of elements in a `Subfield` is in the `Subfield`. -/
protected theorem multiset_sum_mem (m : Multiset K) : (∀ a ∈ m, a ∈ s) → m.sum ∈ s :=
  multiset_sum_mem m

/-- Sum of elements in a `Subfield` indexed by a `Finset` is in the `Subfield`. -/
protected theorem sum_mem {ι : Type*} {t : Finset ι} {f : ι → K} (h : ∀ c ∈ t, f c ∈ s) :
    (∑ i ∈ t, f i) ∈ s :=
  sum_mem h

protected theorem pow_mem {x : K} (hx : x ∈ s) (n : ℕ) : x ^ n ∈ s :=
  pow_mem hx n

protected theorem zsmul_mem {x : K} (hx : x ∈ s) (n : ℤ) : n • x ∈ s :=
  zsmul_mem hx n

protected theorem intCast_mem (n : ℤ) : (n : K) ∈ s := intCast_mem s n

@[deprecated (since := "2024-04-05")] alias coe_int_mem := intCast_mem

theorem zpow_mem {x : K} (hx : x ∈ s) (n : ℤ) : x ^ n ∈ s := by
  cases n
  · simpa using s.pow_mem hx _
  · simpa [pow_succ'] using s.inv_mem (s.mul_mem hx (s.pow_mem hx _))

instance : Ring s :=
  s.toSubring.toRing

instance : Div s :=
  ⟨fun x y => ⟨x / y, s.div_mem x.2 y.2⟩⟩

instance : Inv s :=
  ⟨fun x => ⟨x⁻¹, s.inv_mem x.2⟩⟩

instance : Pow s ℤ :=
  ⟨fun x z => ⟨x ^ z, s.zpow_mem x.2 z⟩⟩

-- TODO: Those are just special cases of `SubfieldClass.toDivisionRing`/`SubfieldClass.toField`
instance toDivisionRing (s : Subfield K) : DivisionRing s :=
  Subtype.coe_injective.divisionRing ((↑) : s → K) rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (by intros; rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
    (by intros; rfl) fun _ ↦ rfl

/-- A subfield inherits a field structure -/
instance toField {K} [Field K] (s : Subfield K) : Field s :=
  Subtype.coe_injective.field ((↑) : s → K) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (by intros; rfl)  (fun _ => rfl)
    (fun _ => rfl) (by intros; rfl) fun _ => rfl

@[simp, norm_cast]
theorem coe_add (x y : s) : (↑(x + y) : K) = ↑x + ↑y :=
  rfl

@[simp, norm_cast]
theorem coe_sub (x y : s) : (↑(x - y) : K) = ↑x - ↑y :=
  rfl

@[simp, norm_cast]
theorem coe_neg (x : s) : (↑(-x) : K) = -↑x :=
  rfl

@[simp, norm_cast]
theorem coe_mul (x y : s) : (↑(x * y) : K) = ↑x * ↑y :=
  rfl

@[simp, norm_cast]
theorem coe_div (x y : s) : (↑(x / y) : K) = ↑x / ↑y :=
  rfl

@[simp, norm_cast]
theorem coe_inv (x : s) : (↑x⁻¹ : K) = (↑x)⁻¹ :=
  rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : s) : K) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_one : ((1 : s) : K) = 1 :=
  rfl

end DerivedFromSubfieldClass

/-- The embedding from a subfield of the field `K` to `K`. -/
def subtype (s : Subfield K) : s →+* K :=
  { s.toSubmonoid.subtype, s.toAddSubgroup.subtype with toFun := (↑) }

@[simp]
theorem coe_subtype : ⇑(s.subtype) = ((↑) : s → K) :=
  rfl

variable (K) in
theorem toSubring_subtype_eq_subtype (S : Subfield K) :
    S.toSubring.subtype = S.subtype :=
  rfl

/-! # Partial order -/


--@[simp] -- Porting note (#10618): simp can prove this
theorem mem_toSubmonoid {s : Subfield K} {x : K} : x ∈ s.toSubmonoid ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem coe_toSubmonoid : (s.toSubmonoid : Set K) = s :=
  rfl

@[simp]
theorem mem_toAddSubgroup {s : Subfield K} {x : K} : x ∈ s.toAddSubgroup ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem coe_toAddSubgroup : (s.toAddSubgroup : Set K) = s :=
  rfl

/-! # top -/


/-- The subfield of `K` containing all elements of `K`. -/
instance : Top (Subfield K) :=
  ⟨{ (⊤ : Subring K) with inv_mem' := fun x _ => Subring.mem_top x }⟩

instance : Inhabited (Subfield K) :=
  ⟨⊤⟩

@[simp]
theorem mem_top (x : K) : x ∈ (⊤ : Subfield K) :=
  Set.mem_univ x

@[simp]
theorem coe_top : ((⊤ : Subfield K) : Set K) = Set.univ :=
  rfl

/-- The ring equiv between the top element of `Subfield K` and `K`. -/
def topEquiv : (⊤ : Subfield K) ≃+* K :=
  Subsemiring.topEquiv

/-! # comap -/


variable (f : K →+* L)

/-- The preimage of a subfield along a ring homomorphism is a subfield. -/
def comap (s : Subfield L) : Subfield K :=
  { s.toSubring.comap f with
    inv_mem' := fun x hx =>
      show f x⁻¹ ∈ s by
        rw [map_inv₀ f]
        exact s.inv_mem hx }

@[simp]
theorem coe_comap (s : Subfield L) : (s.comap f : Set K) = f ⁻¹' s :=
  rfl

@[simp]
theorem mem_comap {s : Subfield L} {f : K →+* L} {x : K} : x ∈ s.comap f ↔ f x ∈ s :=
  Iff.rfl

theorem comap_comap (s : Subfield M) (g : L →+* M) (f : K →+* L) :
    (s.comap g).comap f = s.comap (g.comp f) :=
  rfl

/-! # map -/


/-- The image of a subfield along a ring homomorphism is a subfield. -/
def map (s : Subfield K) : Subfield L :=
  { s.toSubring.map f with
    inv_mem' := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x⁻¹, s.inv_mem hx, map_inv₀ f x⟩ }

@[simp]
theorem coe_map : (s.map f : Set L) = f '' s :=
  rfl

@[simp]
theorem mem_map {f : K →+* L} {s : Subfield K} {y : L} : y ∈ s.map f ↔ ∃ x ∈ s, f x = y := by
  unfold map
  simp only [mem_mk, Subring.mem_mk, Subring.mem_toSubsemiring, Subring.mem_map, mem_toSubring]

theorem map_map (g : L →+* M) (f : K →+* L) : (s.map f).map g = s.map (g.comp f) :=
  SetLike.ext' <| Set.image_image _ _ _

theorem map_le_iff_le_comap {f : K →+* L} {s : Subfield K} {t : Subfield L} :
    s.map f ≤ t ↔ s ≤ t.comap f :=
  Set.image_subset_iff

theorem gc_map_comap (f : K →+* L) : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap

end Subfield

namespace RingHom

variable (g : L →+* M) (f : K →+* L)

/-! # range -/


/-- The range of a ring homomorphism, as a subfield of the target. See Note [range copy pattern]. -/
def fieldRange : Subfield L :=
  ((⊤ : Subfield K).map f).copy (Set.range f) Set.image_univ.symm

@[simp]
theorem coe_fieldRange : (f.fieldRange : Set L) = Set.range f :=
  rfl

@[simp]
theorem mem_fieldRange {f : K →+* L} {y : L} : y ∈ f.fieldRange ↔ ∃ x, f x = y :=
  Iff.rfl

theorem fieldRange_eq_map : f.fieldRange = Subfield.map f ⊤ := by
  ext
  simp

theorem map_fieldRange : f.fieldRange.map g = (g.comp f).fieldRange := by
  simpa only [fieldRange_eq_map] using (⊤ : Subfield K).map_map g f

/-- The range of a morphism of fields is a fintype, if the domain is a fintype.

Note that this instance can cause a diamond with `Subtype.Fintype` if `L` is also a fintype. -/
instance fintypeFieldRange [Fintype K] [DecidableEq L] (f : K →+* L) : Fintype f.fieldRange :=
  Set.fintypeRange f

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

@[simp]
theorem mem_inf {p p' : Subfield K} {x : K} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl

instance : InfSet (Subfield K) :=
  ⟨fun S =>
    { sInf (Subfield.toSubring '' S) with
      inv_mem' := by
        rintro x hx
        apply Subring.mem_sInf.mpr
        rintro _ ⟨p, p_mem, rfl⟩
        exact p.inv_mem (Subring.mem_sInf.mp hx p.toSubring ⟨p, p_mem, rfl⟩) }⟩

@[simp, norm_cast]
theorem coe_sInf (S : Set (Subfield K)) : ((sInf S : Subfield K) : Set K) = ⋂ s ∈ S, ↑s :=
  show ((sInf (Subfield.toSubring '' S) : Subring K) : Set K) = ⋂ s ∈ S, ↑s by
    ext x
    rw [Subring.coe_sInf, Set.mem_iInter, Set.mem_iInter]
    exact
      ⟨fun h s s' ⟨s_mem, s'_eq⟩ => h s.toSubring _ ⟨⟨s, s_mem, rfl⟩, s'_eq⟩,
        fun h s s' ⟨⟨s'', s''_mem, s_eq⟩, (s'_eq : ↑s = s')⟩ =>
        h s'' _ ⟨s''_mem, by simp [← s_eq, ← s'_eq]⟩⟩

theorem mem_sInf {S : Set (Subfield K)} {x : K} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Subring.mem_sInf.trans
    ⟨fun h p hp => h p.toSubring ⟨p, hp, rfl⟩, fun h _ ⟨p', hp', p_eq⟩ => p_eq ▸ h p' hp'⟩

@[simp]
theorem sInf_toSubring (s : Set (Subfield K)) :
    (sInf s).toSubring = ⨅ t ∈ s, Subfield.toSubring t := by
  ext x
  rw [mem_toSubring, mem_sInf]
  erw [Subring.mem_sInf]
  exact
    ⟨fun h p ⟨p', hp⟩ => hp ▸ Subring.mem_sInf.mpr fun p ⟨hp', hp⟩ => hp ▸ h _ hp', fun h p hp =>
      h p.toSubring
        ⟨p,
          Subring.ext fun x =>
            ⟨fun hx => Subring.mem_sInf.mp hx _ ⟨hp, rfl⟩, fun hx =>
              Subring.mem_sInf.mpr fun p' ⟨_, p'_eq⟩ => p'_eq ▸ hx⟩⟩⟩

theorem isGLB_sInf (S : Set (Subfield K)) : IsGLB S (sInf S) := by
  have : ∀ {s t : Subfield K}, (s : Set K) ≤ t ↔ s ≤ t := by simp [SetLike.coe_subset_coe]
  refine IsGLB.of_image this ?_
  convert isGLB_biInf (s := S) (f := SetLike.coe)
  exact coe_sInf _

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
def closure (s : Set K) : Subfield K := sInf {S | s ⊆ S}

theorem mem_closure {x : K} {s : Set K} : x ∈ closure s ↔ ∀ S : Subfield K, s ⊆ S → x ∈ S :=
  mem_sInf

/-- The subfield generated by a set includes the set. -/
@[simp, aesop safe 20 apply (rule_sets := [SetLike])]
theorem subset_closure {s : Set K} : s ⊆ closure s := fun _ hx => mem_closure.2 fun _ hS => hS hx

theorem subring_closure_le (s : Set K) : Subring.closure s ≤ (closure s).toSubring :=
  Subring.closure_le.mpr subset_closure

theorem not_mem_of_not_mem_closure {s : Set K} {P : K} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)

/-- A subfield `t` includes `closure s` if and only if it includes `s`. -/
@[simp]
theorem closure_le {s : Set K} {t : Subfield K} : closure s ≤ t ↔ s ⊆ t :=
  ⟨Set.Subset.trans subset_closure, fun h _ hx => mem_closure.mp hx t h⟩

/-- Subfield closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
theorem closure_mono ⦃s t : Set K⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Set.Subset.trans h subset_closure

theorem closure_eq_of_le {s : Set K} {t : Subfield K} (h₁ : s ⊆ t) (h₂ : t ≤ closure s) :
    closure s = t :=
  le_antisymm (closure_le.2 h₁) h₂

/-- An induction principle for closure membership. If `p` holds for `1`, and all elements
of `s`, and is preserved under addition, negation, and multiplication, then `p` holds for all
elements of the closure of `s`. -/
@[elab_as_elim]
theorem closure_induction {s : Set K} {p : K → Prop} {x} (h : x ∈ closure s) (mem : ∀ x ∈ s, p x)
    (one : p 1) (add : ∀ x y, p x → p y → p (x + y)) (neg : ∀ x, p x → p (-x))
    (inv : ∀ x, p x → p x⁻¹) (mul : ∀ x y, p x → p y → p (x * y)) : p x := by
    letI : Subfield K :=
      ⟨⟨⟨⟨⟨p, by intro _ _; exact mul _ _⟩, one⟩,
        by intro _ _; exact add _ _, @add_neg_cancel K _ 1 ▸ add _ _ one (neg _ one)⟩,
          by intro _; exact neg _⟩, inv⟩
    exact (closure_le (t := this)).2 mem h

variable (K)

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : GaloisInsertion (@closure K _) (↑) where
  choice s _ := closure s
  gc _ _ := closure_le
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl

variable {K}

/-- Closure of a subfield `S` equals `S`. -/
theorem closure_eq (s : Subfield K) : closure (s : Set K) = s :=
  (Subfield.gi K).l_u_eq s

@[simp]
theorem closure_empty : closure (∅ : Set K) = ⊥ :=
  (Subfield.gi K).gc.l_bot

@[simp]
theorem closure_univ : closure (Set.univ : Set K) = ⊤ :=
  @coe_top K _ ▸ closure_eq ⊤

theorem closure_union (s t : Set K) : closure (s ∪ t) = closure s ⊔ closure t :=
  (Subfield.gi K).gc.l_sup

theorem closure_iUnion {ι} (s : ι → Set K) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Subfield.gi K).gc.l_iSup

theorem closure_sUnion (s : Set (Set K)) : closure (⋃₀ s) = ⨆ t ∈ s, closure t :=
  (Subfield.gi K).gc.l_sSup

theorem map_sup (s t : Subfield K) (f : K →+* L) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
  (gc_map_comap f).l_sup

theorem map_iSup {ι : Sort*} (f : K →+* L) (s : ι → Subfield K) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup

theorem comap_inf (s t : Subfield L) (f : K →+* L) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
  (gc_map_comap f).u_inf

theorem comap_iInf {ι : Sort*} (f : K →+* L) (s : ι → Subfield L) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[simp]
theorem map_bot (f : K →+* L) : (⊥ : Subfield K).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
theorem comap_top (f : K →+* L) : (⊤ : Subfield L).comap f = ⊤ :=
  (gc_map_comap f).u_top

/-- The underlying set of a non-empty directed sSup of subfields is just a union of the subfields.
  Note that this fails without the directedness assumption (the union of two subfields is
  typically not a subfield) -/
theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subfield K} (hS : Directed (· ≤ ·) S)
    {x : K} : (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  let s : Subfield K :=
    { __ := Subring.copy _ _ (Subring.coe_iSup_of_directed hS).symm
      inv_mem' := fun _ hx ↦ have ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        Set.mem_iUnion.mpr ⟨i, (S i).inv_mem hi⟩ }
  have : iSup S = s := le_antisymm
    (iSup_le fun i ↦ le_iSup (fun i ↦ (S i : Set K)) i) (Set.iUnion_subset fun _ ↦ le_iSup S _)
  exact this ▸ Set.mem_iUnion

theorem coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subfield K} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Subfield K) : Set K) = ⋃ i, ↑(S i) :=
  Set.ext fun x => by simp [mem_iSup_of_directed hS]

theorem mem_sSup_of_directedOn {S : Set (Subfield K)} (Sne : S.Nonempty) (hS : DirectedOn (· ≤ ·) S)
    {x : K} : x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  haveI : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, Subtype.exists, exists_prop]

theorem coe_sSup_of_directedOn {S : Set (Subfield K)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(sSup S) : Set K) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]

end Subfield

namespace RingHom

variable {s : Subfield K}

open Subfield

/-- Restriction of a ring homomorphism to its range interpreted as a subfield. -/
def rangeRestrictField (f : K →+* L) : K →+* f.fieldRange :=
  f.rangeSRestrict

@[simp]
theorem coe_rangeRestrictField (f : K →+* L) (x : K) : (f.rangeRestrictField x : L) = f x :=
  rfl

section eqLocus

variable {L : Type v} [Semiring L]

/-- The subfield of elements `x : R` such that `f x = g x`, i.e.,
the equalizer of f and g as a subfield of R -/
def eqLocusField (f g : K →+* L) : Subfield K where
  __ := (f : K →+* L).eqLocus g
  inv_mem' _ := eq_on_inv₀ f g
  carrier := { x | f x = g x }

/-- If two ring homomorphisms are equal on a set, then they are equal on its subfield closure. -/
theorem eqOn_field_closure {f g : K →+* L} {s : Set K} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocusField g from closure_le.2 h

theorem eq_of_eqOn_subfield_top {f g : K →+* L} (h : Set.EqOn f g (⊤ : Subfield K)) : f = g :=
  ext fun _ => h trivial

theorem eq_of_eqOn_of_field_closure_eq_top {s : Set K} (hs : closure s = ⊤) {f g : K →+* L}
    (h : s.EqOn f g) : f = g :=
  eq_of_eqOn_subfield_top <| hs ▸ eqOn_field_closure h

end eqLocus

theorem field_closure_preimage_le (f : K →+* L) (s : Set L) :
    closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _ hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

/-- The image under a ring homomorphism of the subfield generated by a set equals
the subfield generated by the image of the set. -/
theorem map_field_closure (f : K →+* L) (s : Set K) : (closure s).map f = closure (f '' s) :=
  le_antisymm
    (map_le_iff_le_comap.2 <|
      le_trans (closure_mono <| Set.subset_preimage_image _ _) (field_closure_preimage_le _ _))
    (closure_le.2 <| Set.image_subset _ subset_closure)

end RingHom

namespace Subfield

open RingHom

/-- The ring homomorphism associated to an inclusion of subfields. -/
def inclusion {S T : Subfield K} (h : S ≤ T) : S →+* T :=
  S.subtype.codRestrict _ fun x => h x.2

@[simp]
theorem fieldRange_subtype (s : Subfield K) : s.subtype.fieldRange = s :=
  SetLike.ext' <| (coe_rangeS _).trans Subtype.range_coe

end Subfield

namespace RingEquiv

variable {s t : Subfield K}

/-- Makes the identity isomorphism from a proof two subfields of a multiplicative
    monoid are equal. -/
def subfieldCongr (h : s = t) : s ≃+* t :=
  { Equiv.setCongr <| SetLike.ext'_iff.1 h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

end RingEquiv

namespace Subfield

variable {s : Set K}

theorem closure_preimage_le (f : K →+* L) (s : Set L) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _ hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

section Commutative

variable {K : Type u} [Field K] (s : Subfield K)

/-- Product of a multiset of elements in a subfield is in the subfield. -/
protected theorem multiset_prod_mem (m : Multiset K) : (∀ a ∈ m, a ∈ s) → m.prod ∈ s :=
  multiset_prod_mem m

/-- Product of elements of a subfield indexed by a `Finset` is in the subfield. -/
protected theorem prod_mem {ι : Type*} {t : Finset ι} {f : ι → K} (h : ∀ c ∈ t, f c ∈ s) :
    (∏ i ∈ t, f i) ∈ s :=
  prod_mem h

instance toAlgebra : Algebra s K :=
  RingHom.toAlgebra s.subtype

/-- The `Subfield` generated by a set in a field. -/
private def commClosure (s : Set K) : Subfield K where
  carrier := {z : K | ∃ x ∈ Subring.closure s, ∃ y ∈ Subring.closure s, x / y = z}
  zero_mem' := ⟨0, Subring.zero_mem _, 1, Subring.one_mem _, div_one _⟩
  one_mem' := ⟨1, Subring.one_mem _, 1, Subring.one_mem _, div_one _⟩
  neg_mem' {x} := by
    rintro ⟨y, hy, z, hz, x_eq⟩
    exact ⟨-y, Subring.neg_mem _ hy, z, hz, x_eq ▸ neg_div _ _⟩
  inv_mem' x := by rintro ⟨y, hy, z, hz, x_eq⟩; exact ⟨z, hz, y, hy, x_eq ▸ (inv_div _ _).symm⟩
  add_mem' x_mem y_mem := by
    -- Use `id` in the next 2 `obtain`s so that assumptions stay there for the `rwa`s below
    obtain ⟨nx, hnx, dx, hdx, rfl⟩ := id x_mem
    obtain ⟨ny, hny, dy, hdy, rfl⟩ := id y_mem
    by_cases hx0 : dx = 0; · rwa [hx0, div_zero, zero_add]
    by_cases hy0 : dy = 0; · rwa [hy0, div_zero, add_zero]
    exact
      ⟨nx * dy + dx * ny, Subring.add_mem _ (Subring.mul_mem _ hnx hdy) (Subring.mul_mem _ hdx hny),
        dx * dy, Subring.mul_mem _ hdx hdy, (div_add_div nx ny hx0 hy0).symm⟩
  mul_mem' := by
    rintro _ _ ⟨nx, hnx, dx, hdx, rfl⟩ ⟨ny, hny, dy, hdy, rfl⟩
    exact ⟨nx * ny, Subring.mul_mem _ hnx hny, dx * dy, Subring.mul_mem _ hdx hdy,
      (div_mul_div_comm _ _ _ _).symm⟩

private theorem commClosure_eq_closure {s : Set K} : commClosure s = closure s :=
  le_antisymm
    (fun _ ⟨_, hy, _, hz, eq⟩ ↦ eq ▸ div_mem (subring_closure_le s hy) (subring_closure_le s hz))
    (closure_le.mpr fun x hx ↦ ⟨x, Subring.subset_closure hx, 1, Subring.one_mem _, div_one x⟩)

theorem mem_closure_iff {s : Set K} {x} :
    x ∈ closure s ↔ ∃ y ∈ Subring.closure s, ∃ z ∈ Subring.closure s, y / z = x := by
  rw [← commClosure_eq_closure]; rfl

end Commutative

end Subfield

namespace Subfield

theorem map_comap_eq (f : K →+* L) (s : Subfield L) : (s.comap f).map f = s ⊓ f.fieldRange :=
  SetLike.coe_injective Set.image_preimage_eq_inter_range

theorem map_comap_eq_self
    {f : K →+* L} {s : Subfield L} (h : s ≤ f.fieldRange) : (s.comap f).map f = s := by
  simpa only [inf_of_le_left h] using map_comap_eq f s

theorem map_comap_eq_self_of_surjective
    {f : K →+* L} (hf : Function.Surjective f) (s : Subfield L) : (s.comap f).map f = s :=
  SetLike.coe_injective (Set.image_preimage_eq _ hf)

theorem comap_map (f : K →+* L) (s : Subfield K) : (s.map f).comap f = s :=
  SetLike.coe_injective (Set.preimage_image_eq _ f.injective)

end Subfield
