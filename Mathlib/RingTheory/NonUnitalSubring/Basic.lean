/-
Copyright (c) 2020 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux

! This file was ported from Lean 3 source module main
-/
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.RingTheory.NonUnitalSubsemiring.Basic

/-!
# non_unital_subrings

Let `R` be a non-unital ring. This file defines the "bundled" non-unital subring type
`non_unital_subring R`, a type whose terms correspond to non-unital subrings of `R`.
This is the preferred way to talk about non-unital non-unital subrings in mathlib.

We prove that non-unital subrings are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `set R` to `non_unital_subring R`, sending a subset of
`R` to the non-unital subring it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(R : Type u) [non_unital_ring R] (S : Type u) [non_unital_ring S] (f g : R →ₙ+* S)`
`(A : non_unital_subring R) (B : non_unital_subring S) (s : set R)`

* `non_unital_subring R` : the type of non-unital subrings of a ring `R`.

* `instance : complete_lattice (non_unital_subring R)` : the complete lattice structure on the
  non-unital subrings.

* `non_unital_subring.center` : the center of a non-unital ring `R`.

* `non_unital_subring.closure` : non-unital subring closure of a set, i.e., the smallest
  non-unital subring that includes the set.

* `non_unital_subring.gi` : `closure : set M → non_unital_subring M` and coercion
  `coe : non_unital_subring M → set M`
  form a `galois_insertion`.

* `comap f B : non_unital_subring A` : the preimage of a non-unital subring `B` along the
  non-unital ring homomorphism `f`

* `map f A : non_unital_subring B` : the image of a non-unital subring `A` along the
  non-unital ring homomorphism `f`.

* `prod A B : non_unital_subring (R × S)` : the product of non-unital subrings

* `f.range : non_unital_subring B` : the range of the non-unital ring homomorphism `f`.

* `eq_locus f g : non_unital_subring R` : given non-unital ring homomorphisms `f g : R →ₙ+* S`,
     the non-unital subring of `R` where `f x = g x`

## Implementation notes

A non-unital subring is implemented as a non-unital non_unital_subsemiring which is also an additive subgroup.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a non_unital_subring's underlying set.

## Tags
non-unital subring
-/


open scoped BigOperators

universe u v w

section Basic

variable {R : Type u} {S : Type v} {T : Type w} [NonUnitalRing R]

section NonUnitalSubringClass

/-- `non_unital_subring_class S R` states that `S` is a type of subsets `s ⊆ R` that
are both a multiplicative submonoid and an additive subgroup. -/
class NonUnitalSubringClass (S : Type _) (R : Type u) [NonUnitalRing R] [SetLike S R] extends
    NonUnitalSubsemiringClass S R, NegMemClass S R : Prop where

-- See note [lower instance priority]
instance (priority := 100) NonUnitalSubringClass.addSubgroupClass (S : Type _) (R : Type u)
    [SetLike S R] [NonUnitalRing R] [h : NonUnitalSubringClass S R] : AddSubgroupClass S R :=
  { h with }

variable [SetLike S R] [hSR : NonUnitalSubringClass S R] (s : S)

namespace NonUnitalSubringClass

-- Prefer subclasses of `non_unital_ring` over subclasses of `non_unital_subring_class`.
/-- A non-unital subring of a non-unital ring inherits a non-unital ring structure -/
instance (priority := 75) toNonUnitalRing : NonUnitalRing s :=
  Subtype.val_injective.nonUnitalRing _ rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

-- Prefer subclasses of `non_unital_ring` over subclasses of `non_unital_subring_class`.
/-- A non-unital subring of a `non_unital_comm_ring` is a `non_unital_comm_ring`. -/
instance (priority := 75) toNonUnitalCommRing {R} [NonUnitalCommRing R] [SetLike S R]
    [NonUnitalSubringClass S R] : NonUnitalCommRing s :=
  Subtype.val_injective.nonUnitalCommRing _ rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

-- TODO: `is_domain` should be generalized to `non_unital_non_assoc_semiring`
/- A non_unital_subring of a domain is a domain.
@[priority 75] -- Prefer subclasses of `ring` over subclasses of `non_unital_subring_class`.
instance {R} [ring R] [is_domain R] [set_like S R] [non_unital_subring_class S R] : is_domain s :=
no_zero_divisors.to_is_domain _ -/

/-- The natural ring hom from a non-unital subring of non-unital ring `R` to `R`. -/
def subtype (s : S) : s →ₙ+* R :=
  { NonUnitalSubsemiringClass.subtype s,
    AddSubgroupClass.subtype s with
    toFun := Subtype.val }

@[simp]
theorem coeSubtype : (subtype s : s → R) = Subtype.val :=
  rfl

end NonUnitalSubringClass

end NonUnitalSubringClass

variable [NonUnitalRing S] [NonUnitalRing T]

/-- `non_unital_subring R` is the type of non-unital subrings of `R`. A non-unital subring of `R`
is a subset `s` that is a multiplicative subsemigroup and an additive subgroup. Note in particular
that it shares the same 0 as R. -/
structure NonUnitalSubring (R : Type u) [NonUnitalRing R] extends
  NonUnitalSubsemiring R, AddSubgroup R

/-- Reinterpret a `non_unital_subring` as a `non_unital_subsemiring`. -/
add_decl_doc NonUnitalSubring.toNonUnitalSubsemiring

/-- Reinterpret a `non_unital_subring` as an `add_subgroup`. -/
add_decl_doc NonUnitalSubring.toAddSubgroup

namespace NonUnitalSubring

/-- The underlying submonoid of a non_unital_subring. -/
def toSubsemigroup (s : NonUnitalSubring R) : Subsemigroup R :=
  { s.toNonUnitalSubsemiring.toSubsemigroup with carrier := s.carrier }

instance : SetLike (NonUnitalSubring R) R
    where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

instance : NonUnitalSubringClass (NonUnitalSubring R) R
    where
  zero_mem s := s.zero_mem'
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  neg_mem {s} := s.neg_mem'

@[simp]
theorem mem_carrier {s : NonUnitalSubring R} {x : R} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem mem_mk {S : NonUnitalSubsemiring R} {x : R} (h) :
    x ∈ (⟨S, h⟩ : NonUnitalSubring R) ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_set_mk (S : NonUnitalSubsemiring R) (h) :
    ((⟨S, h⟩ : NonUnitalSubring R) : Set R) = S :=
  rfl

@[simp]
theorem mk_le_mk {S S' : NonUnitalSubsemiring R} (h h') :
    (⟨S, h⟩ : NonUnitalSubring R) ≤ (⟨S', h'⟩ : NonUnitalSubring R) ↔ S ≤ S' :=
  Iff.rfl

/-- Two non-unital subrings are equal if they have the same elements. -/
@[ext]
theorem ext {S T : NonUnitalSubring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy of a non-unital subring with a new `carrier` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (S : NonUnitalSubring R) (s : Set R) (hs : s = ↑S) : NonUnitalSubring R :=
  { S.toNonUnitalSubsemiring.copy s hs with
    carrier := s
    neg_mem' := hs.symm ▸ S.neg_mem' }

@[simp]
theorem coe_copy (S : NonUnitalSubring R) (s : Set R) (hs : s = ↑S) : (S.copy s hs : Set R) = s :=
  rfl

theorem copy_eq (S : NonUnitalSubring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

theorem toNonUnitalSubsemiring_injective :
    Function.Injective (toNonUnitalSubsemiring : NonUnitalSubring R → NonUnitalSubsemiring R)
  | _r, _s, h => ext (SetLike.ext_iff.mp h : _)

@[mono]
theorem toNonUnitalSubsemiring_strictMono :
    StrictMono (toNonUnitalSubsemiring : NonUnitalSubring R → NonUnitalSubsemiring R) := fun _ _ =>
  id

@[mono]
theorem toNonUnitalSubsemiring_mono :
    Monotone (toNonUnitalSubsemiring : NonUnitalSubring R → NonUnitalSubsemiring R) :=
  toNonUnitalSubsemiring_strictMono.monotone

theorem toAddSubgroup_injective :
    Function.Injective (toAddSubgroup : NonUnitalSubring R → AddSubgroup R)
  | _r, _s, h => ext (SetLike.ext_iff.mp h : _)

@[mono]
theorem toAddSubgroup_strictMono :
    StrictMono (toAddSubgroup : NonUnitalSubring R → AddSubgroup R) := fun _ _ => id

@[mono]
theorem toAddSubgroup_mono : Monotone (toAddSubgroup : NonUnitalSubring R → AddSubgroup R) :=
  toAddSubgroup_strictMono.monotone

theorem toSubsemigroup_injective :
    Function.Injective (toSubsemigroup : NonUnitalSubring R → Subsemigroup R)
  | _r, _s, h => ext (SetLike.ext_iff.mp h : _)

@[mono]
theorem toSubsemigroup_strictMono :
    StrictMono (toSubsemigroup : NonUnitalSubring R → Subsemigroup R) := fun _ _ => id

@[mono]
theorem toSubsemigroup_mono : Monotone (toSubsemigroup : NonUnitalSubring R → Subsemigroup R) :=
  toSubsemigroup_strictMono.monotone

/-- Construct a `non_unital_subring R` from a set `s`, a subsemigroup `sm`, and an additive
subgroup `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`. -/
protected def mk' (s : Set R) (sm : Subsemigroup R) (sa : AddSubgroup R) (hm : ↑sm = s)
    (ha : ↑sa = s) : NonUnitalSubring R :=
  { sm.copy s hm.symm, sa.copy s ha.symm with }

@[simp]
theorem coe_mk' {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : AddSubgroup R}
    (ha : ↑sa = s) : (NonUnitalSubring.mk' s sm sa hm ha : Set R) = s :=
  rfl

@[simp]
theorem mem_mk' {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : AddSubgroup R} (ha : ↑sa = s)
    {x : R} : x ∈ NonUnitalSubring.mk' s sm sa hm ha ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem mk'_toSubsemigroup {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : AddSubgroup R}
    (ha : ↑sa = s) : (NonUnitalSubring.mk' s sm sa hm ha).toSubsemigroup = sm :=
  SetLike.coe_injective hm.symm

@[simp]
theorem mk'_toAddSubgroup {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : AddSubgroup R}
    (ha : ↑sa = s) : (NonUnitalSubring.mk' s sm sa hm ha).toAddSubgroup = sa :=
  SetLike.coe_injective ha.symm

end NonUnitalSubring

namespace NonUnitalSubring

variable (s : NonUnitalSubring R)

/-- A non-unital subring contains the ring's 0. -/
protected theorem zero_mem : (0 : R) ∈ s :=
  zero_mem _

/-- A non-unital subring is closed under multiplication. -/
protected theorem mul_mem {x y : R} : x ∈ s → y ∈ s → x * y ∈ s :=
  mul_mem

/-- A non-unital subring is closed under addition. -/
protected theorem add_mem {x y : R} : x ∈ s → y ∈ s → x + y ∈ s :=
  add_mem

/-- A non-unital subring is closed under negation. -/
protected theorem neg_mem {x : R} : x ∈ s → -x ∈ s :=
  neg_mem

/-- A non-unital subring is closed under subtraction -/
protected theorem sub_mem {x y : R} (hx : x ∈ s) (hy : y ∈ s) : x - y ∈ s :=
  sub_mem hx hy

/-- Sum of a list of elements in a non-unital subring is in the non-unital subring. -/
protected theorem list_sum_mem {l : List R} : (∀ x ∈ l, x ∈ s) → l.sum ∈ s :=
  list_sum_mem

/-- Sum of a multiset of elements in an `non_unital_subring` of a `non_unital_ring` is
in the `non_unital_subring`. -/
protected theorem multiset_sum_mem {R} [NonUnitalRing R] (s : NonUnitalSubring R) (m : Multiset R) :
    (∀ a ∈ m, a ∈ s) → m.sum ∈ s :=
  multiset_sum_mem _

/-- Sum of elements in a `non_unital_subring` of a `non_unital_ring` indexed by a `finset`
is in the `non_unital_subring`. -/
protected theorem sum_mem {R : Type _} [NonUnitalRing R] (s : NonUnitalSubring R) {ι : Type _}
    {t : Finset ι} {f : ι → R} (h : ∀ c ∈ t, f c ∈ s) : (∑ i in t, f i) ∈ s :=
  sum_mem h

/-- A non-unital subring of a non-unital ring inherits a non-unital ring structure -/
instance toNonUnitalRing : NonUnitalRing s :=
  Subtype.coe_injective.nonUnitalRing _ rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

protected theorem zsmul_mem {x : R} (hx : x ∈ s) (n : ℤ) : n • x ∈ s :=
  zsmul_mem hx n

@[simp, norm_cast]
theorem val_add (x y : s) : (↑(x + y) : R) = ↑x + ↑y :=
  rfl

@[simp, norm_cast]
theorem val_neg (x : s) : (↑(-x) : R) = -↑x :=
  rfl

@[simp, norm_cast]
theorem val_mul (x y : s) : (↑(x * y) : R) = ↑x * ↑y :=
  rfl

@[simp, norm_cast]
theorem val_zero : ((0 : s) : R) = 0 :=
  rfl

-- TODO: can be generalized to `add_submonoid_class`
@[simp]
theorem coe_eq_zero_iff {x : s} : (x : R) = 0 ↔ x = 0 :=
  ⟨fun h => Subtype.ext (h.trans s.val_zero.symm), fun h => h.symm ▸ s.val_zero⟩

/-- A non-unital subring of a `non_unital_comm_ring` is a `non_unital_comm_ring`. -/
instance toNonUnitalCommRing {R} [NonUnitalCommRing R] (s : NonUnitalSubring R) :
    NonUnitalCommRing s :=
  Subtype.coe_injective.nonUnitalCommRing _ rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

/-! ## Partial order -/


@[simp]
theorem mem_toSubsemigroup {s : NonUnitalSubring R} {x : R} : x ∈ s.toSubsemigroup ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem coe_toSubsemigroup (s : NonUnitalSubring R) : (s.toSubsemigroup : Set R) = s :=
  rfl

@[simp]
theorem mem_toAddSubgroup {s : NonUnitalSubring R} {x : R} : x ∈ s.toAddSubgroup ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem coe_toAddSubgroup (s : NonUnitalSubring R) : (s.toAddSubgroup : Set R) = s :=
  rfl

/-! ## top -/


/-- The non-unital subring `R` of the ring `R`. -/
instance : Top (NonUnitalSubring R) :=
  ⟨{ (⊤ : Subsemigroup R), (⊤ : AddSubgroup R) with }⟩

@[simp]
theorem mem_top (x : R) : x ∈ (⊤ : NonUnitalSubring R) :=
  Set.mem_univ x

@[simp]
theorem coe_top : ((⊤ : NonUnitalSubring R) : Set R) = Set.univ :=
  rfl

/- TODO: FIX ME
/-- The ring equiv between the top element of `non_unital_subring R` and `R`. -/
@[simps]
def top_equiv : (⊤ : non_unital_subring R) ≃+* R := non_unital_subsemiring.top_equiv
-/
end NonUnitalSubring

end Basic

section Hom

namespace NonUnitalSubring

variable {F : Type w} {R : Type u} {S : Type v} {T : Type _} {SR : Type _}

variable [NonUnitalRing R] [NonUnitalRing S] [NonUnitalRing T]

variable [NonUnitalRingHomClass F R S] (s : NonUnitalSubring R)

/-! ## comap -/


/-- The preimage of a non_unital_subring along a ring homomorphism is a non_unital_subring. -/
def comap {F : Type w} {R : Type u} {S : Type v} [NonUnitalRing R] [NonUnitalRing S]
    [NonUnitalRingHomClass F R S] (f : F) (s : NonUnitalSubring S) : NonUnitalSubring R :=
  { s.toSubsemigroup.comap (f : R →ₙ* S), s.toAddSubgroup.comap (f : R →+ S) with
    carrier := f ⁻¹' s.carrier }

@[simp]
theorem coe_comap (s : NonUnitalSubring S) (f : F) : (s.comap f : Set R) = f ⁻¹' s :=
  rfl

@[simp]
theorem mem_comap {s : NonUnitalSubring S} {f : F} {x : R} : x ∈ s.comap f ↔ f x ∈ s :=
  Iff.rfl

theorem comap_comap (s : NonUnitalSubring T) (g : S →ₙ+* T) (f : R →ₙ+* S) :
    (s.comap g).comap f = s.comap (g.comp f) :=
  rfl

/-! ## map -/


/-- The image of a non_unital_subring along a ring homomorphism is a non_unital_subring. -/
def map {F : Type w} {R : Type u} {S : Type v} [NonUnitalRing R] [NonUnitalRing S]
    [NonUnitalRingHomClass F R S] (f : F) (s : NonUnitalSubring R) : NonUnitalSubring S :=
  { s.toSubsemigroup.map (f : R →ₙ* S), s.toAddSubgroup.map (f : R →+ S) with
    carrier := f '' s.carrier }

@[simp]
theorem coe_map (f : F) (s : NonUnitalSubring R) : (s.map f : Set S) = f '' s :=
  rfl

@[simp]
theorem mem_map {f : F} {s : NonUnitalSubring R} {y : S} : y ∈ s.map f ↔ ∃ x ∈ s, f x = y :=
  Set.mem_image _ _ _

@[simp]
theorem map_id : s.map (NonUnitalRingHom.id R) = s :=
  SetLike.coe_injective <| Set.image_id _

theorem map_map (g : S →ₙ+* T) (f : R →ₙ+* S) : (s.map f).map g = s.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _

theorem map_le_iff_le_comap {f : F} {s : NonUnitalSubring R} {t : NonUnitalSubring S} :
    s.map f ≤ t ↔ s ≤ t.comap f :=
  Set.image_subset_iff

theorem gc_map_comap (f : F) :
    GaloisConnection (map f : NonUnitalSubring R → NonUnitalSubring S) (comap f) := fun _S _T =>
  map_le_iff_le_comap

/-- A non_unital_subring is isomorphic to its image under an injective function -/
noncomputable def equivMapOfInjective (f : F) (hf : Function.Injective (f : R → S)) :
    s ≃+* s.map f :=
  {
    Equiv.Set.image f s
      hf with
    map_mul' := fun _ _ => Subtype.ext (map_mul f _ _)
    map_add' := fun _ _ => Subtype.ext (map_add f _ _) }

@[simp]
theorem coe_equivMapOfInjective_apply (f : F) (hf : Function.Injective f) (x : s) :
    (equivMapOfInjective s f hf x : S) = f x :=
  rfl

end NonUnitalSubring

namespace NonUnitalRingHom

variable {R : Type u} {S : Type v} {T : Type _}

variable [NonUnitalRing R] [NonUnitalRing S] [NonUnitalRing T]

variable (g : S →ₙ+* T) (f : R →ₙ+* S)

/-! ## range -/


/--
The range of a ring homomorphism, as a non_unital_subring of the target. See Note [range copy pattern]. -/
def range {R : Type u} {S : Type v} [NonUnitalRing R] [NonUnitalRing S] (f : R →ₙ+* S) :
    NonUnitalSubring S :=
  ((⊤ : NonUnitalSubring R).map f).copy (Set.range f) Set.image_univ.symm

@[simp]
theorem coe_range : (f.range : Set S) = Set.range f :=
  rfl

@[simp]
theorem mem_range {f : R →ₙ+* S} {y : S} : y ∈ f.range ↔ ∃ x, f x = y :=
  Iff.rfl

theorem range_eq_map (f : R →ₙ+* S) : f.range = NonUnitalSubring.map f ⊤ := by ext; simp

theorem mem_range_self (f : R →ₙ+* S) (x : R) : f x ∈ f.range :=
  mem_range.mpr ⟨x, rfl⟩

theorem map_range : f.range.map g = (g.comp f).range := by
  simpa only [range_eq_map] using (⊤ : NonUnitalSubring R).map_map g f

/-- The range of a ring homomorphism is a fintype, if the domain is a fintype.
Note: this instance can form a diamond with `subtype.fintype` in the
  presence of `fintype S`. -/
instance fintypeRange [Fintype R] [DecidableEq S] (f : R →ₙ+* S) : Fintype (range f) :=
  Set.fintypeRange f

end NonUnitalRingHom

namespace NonUnitalSubring

variable {F : Type w} {R : Type u} {S : Type v} {T : Type _}

variable [NonUnitalRing R] [NonUnitalRing S] [NonUnitalRing T]

variable [NonUnitalRingHomClass F R S]

variable (g : S →ₙ+* T) (f : R →ₙ+* S)

/-! ## bot -/


instance : Bot (NonUnitalSubring R) :=
  ⟨(0 : R →ₙ+* R).range⟩

instance : Inhabited (NonUnitalSubring R) :=
  ⟨⊥⟩

theorem coe_bot : ((⊥ : NonUnitalSubring R) : Set R) = {0} :=
  (NonUnitalRingHom.coe_range (0 : R →ₙ+* R)).trans (@Set.range_const R R _ 0)

theorem mem_bot {x : R} : x ∈ (⊥ : NonUnitalSubring R) ↔ x = 0 :=
  show x ∈ ((⊥ : NonUnitalSubring R) : Set R) ↔ x = 0 by rw [coe_bot, Set.mem_singleton_iff]

/-! ## inf -/


/-- The inf of two non_unital_subrings is their intersection. -/
instance : Inf (NonUnitalSubring R) :=
  ⟨fun s t =>
    { s.toSubsemigroup ⊓ t.toSubsemigroup, s.toAddSubgroup ⊓ t.toAddSubgroup with
      carrier := s ∩ t }⟩

@[simp]
theorem coe_inf (p p' : NonUnitalSubring R) :
  ((p ⊓ p' : NonUnitalSubring R) : Set R) = (p : Set R) ∩ p' :=
  rfl

@[simp]
theorem mem_inf {p p' : NonUnitalSubring R} {x : R} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl

instance : InfSet (NonUnitalSubring R) :=
  ⟨fun s =>
    NonUnitalSubring.mk' (⋂ t ∈ s, ↑t) (⨅ t ∈ s, NonUnitalSubring.toSubsemigroup t)
      (⨅ t ∈ s, NonUnitalSubring.toAddSubgroup t) (by simp) (by simp)⟩

@[simp, norm_cast]
theorem coe_sInf (S : Set (NonUnitalSubring R)) :
    ((sInf S : NonUnitalSubring R) : Set R) = ⋂ s ∈ S, ↑s :=
  rfl

theorem mem_sInf {S : Set (NonUnitalSubring R)} {x : R} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂

@[simp, norm_cast]
theorem coe_iInf {ι : Sort _} {S : ι → NonUnitalSubring R} : (↑(⨅ i, S i) : Set R) = ⋂ i, S i := by
  simp only [iInf, coe_sInf, Set.biInter_range]

theorem mem_iInf {ι : Sort _} {S : ι → NonUnitalSubring R} {x : R} :
    (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by simp only [iInf, mem_sInf, Set.forall_range_iff]

@[simp]
theorem sInf_toSubsemigroup (s : Set (NonUnitalSubring R)) :
    (sInf s).toSubsemigroup = ⨅ t ∈ s, NonUnitalSubring.toSubsemigroup t :=
  mk'_toSubsemigroup _ _

@[simp]
theorem sInf_toAddSubgroup (s : Set (NonUnitalSubring R)) :
    (sInf s).toAddSubgroup = ⨅ t ∈ s, NonUnitalSubring.toAddSubgroup t :=
  mk'_toAddSubgroup _ _

/-- non_unital_subrings of a ring form a complete lattice. -/
instance : CompleteLattice (NonUnitalSubring R) :=
  { completeLatticeOfInf (NonUnitalSubring R) fun _s =>
      IsGLB.of_image (@fun _ _ : NonUnitalSubring R => SetLike.coe_subset_coe)
        isGLB_biInf with
    bot := ⊥
    bot_le := fun s _x hx => (mem_bot.mp hx).symm ▸ zero_mem s
    top := ⊤
    le_top := fun _ _ _ => trivial
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right
    le_inf := fun _s _t₁ _t₂ h₁ h₂ _x hx => ⟨h₁ hx, h₂ hx⟩ }

theorem eq_top_iff' (A : NonUnitalSubring R) : A = ⊤ ↔ ∀ x : R, x ∈ A :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩

/-! ## Center of a ring -/


section

variable (R)

-- this needs to go elsewhere, or rather just generalize `set.neg_mem_center`
@[simp]
theorem Set.neg_mem_center' {R : Type _} [NonUnitalNonAssocRing R] {a : R} (ha : a ∈ Set.center R) :
    -a ∈ Set.center R := fun c => by rw [← neg_mul_comm, ha (-c), neg_mul_comm]

/-- The center of a ring `R` is the set of elements that commute with everything in `R` -/
def center : NonUnitalSubring R :=
  { NonUnitalSubsemiring.center R with
    carrier := Set.center R
    neg_mem' := Set.neg_mem_center' }

theorem coe_center : ↑(center R) = Set.center R :=
  rfl

@[simp]
theorem center_toNonUnitalSubsemiring :
    (center R).toNonUnitalSubsemiring = NonUnitalSubsemiring.center R :=
  rfl

variable {R}

theorem mem_center_iff {z : R} : z ∈ center R ↔ ∀ g, g * z = z * g :=
  Iff.rfl

instance decidableMemCenter [DecidableEq R] [Fintype R] : DecidablePred (· ∈ center R) := fun _ =>
  decidable_of_iff' _ mem_center_iff

@[simp]
theorem center_eq_top (R) [NonUnitalCommRing R] : center R = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ R)

/-- The center is commutative. -/
instance center.instNonUnitalCommRing : NonUnitalCommRing (center R) :=
  { NonUnitalSubsemiring.center.instNonUnitalCommSemiring,
    (center R).toNonUnitalRing with }

end

/-! ## non_unital_subring closure of a subset -/


/-- The `non_unital_subring` generated by a set. -/
def closure (s : Set R) : NonUnitalSubring R :=
  sInf {S | s ⊆ S}

theorem mem_closure {x : R} {s : Set R} : x ∈ closure s ↔ ∀ S : NonUnitalSubring R, s ⊆ S → x ∈ S :=
  mem_sInf

/-- The non_unital_subring generated by a set includes the set. -/
@[simp]
theorem subset_closure {s : Set R} : s ⊆ closure s := fun _x hx => mem_closure.2 fun _S hS => hS hx

theorem not_mem_of_not_mem_closure {s : Set R} {P : R} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)

/-- A non_unital_subring `t` includes `closure s` if and only if it includes `s`. -/
@[simp]
theorem closure_le {s : Set R} {t : NonUnitalSubring R} : closure s ≤ t ↔ s ⊆ t :=
  ⟨Set.Subset.trans subset_closure, fun h => sInf_le h⟩

/-- non_unital_subring closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
theorem closure_mono ⦃s t : Set R⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Set.Subset.trans h subset_closure

theorem closure_eq_of_le {s : Set R} {t : NonUnitalSubring R} (h₁ : s ⊆ t) (h₂ : t ≤ closure s) :
    closure s = t :=
  le_antisymm (closure_le.2 h₁) h₂

/-- An induction principle for closure membership. If `p` holds for `0`, `1`, and all elements
of `s`, and is preserved under addition, negation, and multiplication, then `p` holds for all
elements of the closure of `s`. -/
@[elab_as_elim]
theorem closure_induction {s : Set R} {p : R → Prop} {x} (h : x ∈ closure s) (Hs : ∀ x ∈ s, p x)
    (H0 : p 0) (Hadd : ∀ x y, p x → p y → p (x + y)) (Hneg : ∀ x : R, p x → p (-x))
    (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
  (@closure_le _ _ _ ⟨⟨⟨⟨p, Hadd _ _⟩, H0⟩, Hmul _ _⟩, Hneg _⟩).2 Hs h

/-- The difference with `non_unital_subring.closure_induction` is that this acts on the
subtype. -/
@[elab_as_elim]
theorem closure_induction' {s : Set R} {p : closure s → Prop} (a : closure s)
    (Hs : ∀ (x) (hx : x ∈ s), p ⟨x, subset_closure hx⟩) (H0 : p 0)
    (Hadd : ∀ x y, p x → p y → p (x + y)) (Hneg : ∀ x, p x → p (-x))
    (Hmul : ∀ x y, p x → p y → p (x * y)) : p a :=
  Subtype.recOn a fun b hb =>
    by
    refine' Exists.elim _ fun (hb : b ∈ closure s) (hc : p ⟨b, hb⟩) => hc
    refine'
      closure_induction hb (fun x hx => ⟨subset_closure hx, Hs x hx⟩) ⟨zero_mem (closure s), H0⟩ _ _
        _
    · rintro x y ⟨hx, hpx⟩ ⟨hy, hpy⟩
      exact ⟨add_mem hx hy, Hadd _ _ hpx hpy⟩
    · rintro x ⟨hx, hpx⟩
      exact ⟨neg_mem hx, Hneg _ hpx⟩
    · rintro x y ⟨hx, hpx⟩ ⟨hy, hpy⟩
      exact ⟨mul_mem hx hy, Hmul _ _ hpx hpy⟩

/-- An induction principle for closure membership, for predicates with two arguments. -/
@[elab_as_elim]
theorem closure_induction₂ {s : Set R} {p : R → R → Prop} {a b : R} (ha : a ∈ closure s)
    (hb : b ∈ closure s) (Hs : ∀ x ∈ s, ∀ y ∈ s, p x y) (H0_left : ∀ x, p 0 x)
    (H0_right : ∀ x, p x 0) (Hneg_left : ∀ x y, p x y → p (-x) y)
    (Hneg_right : ∀ x y, p x y → p x (-y)) (Hadd_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ + x₂) y)
    (Hadd_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ + y₂))
    (Hmul_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ * x₂) y)
    (Hmul_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ * y₂)) : p a b :=
  by
  refine' closure_induction hb _ (H0_right _) (Hadd_right a) (Hneg_right a) (Hmul_right a)
  refine' closure_induction ha Hs (fun x _ => H0_left x) _ _ _
  · exact fun x y H₁ H₂ z zs => Hadd_left x y z (H₁ z zs) (H₂ z zs)
  · exact fun x hx z zs => Hneg_left x z (hx z zs)
  · exact fun x y H₁ H₂ z zs => Hmul_left x y z (H₁ z zs) (H₂ z zs)

theorem mem_closure_iff {s : Set R} {x} :
    x ∈ closure s ↔ x ∈ AddSubgroup.closure (Subsemigroup.closure s : Set R) :=
  ⟨fun h =>
    closure_induction h (fun x hx => AddSubgroup.subset_closure <| Subsemigroup.subset_closure hx)
      (AddSubgroup.zero_mem _) (fun x y hx hy => AddSubgroup.add_mem _ hx hy)
      (fun x hx => AddSubgroup.neg_mem _ hx) fun x y hx hy =>
      AddSubgroup.closure_induction hy
        (fun q hq =>
          AddSubgroup.closure_induction hx
            (fun p hp => AddSubgroup.subset_closure ((Subsemigroup.closure s).mul_mem hp hq))
            (by rw [MulZeroClass.zero_mul q]; apply AddSubgroup.zero_mem _)
            (fun p₁ p₂ ihp₁ ihp₂ => by rw [add_mul p₁ p₂ q]; apply AddSubgroup.add_mem _ ihp₁ ihp₂)
            fun x hx => by
            have f : -x * q = -(x * q) := by simp
            rw [f]; apply AddSubgroup.neg_mem _ hx)
        (by rw [MulZeroClass.mul_zero x]; apply AddSubgroup.zero_mem _)
        (fun q₁ q₂ ihq₁ ihq₂ => by rw [mul_add x q₁ q₂]; apply AddSubgroup.add_mem _ ihq₁ ihq₂)
        fun z hz => by
        have f : x * -z = -(x * z) := by simp
        rw [f]; apply AddSubgroup.neg_mem _ hz,
    fun h =>
    AddSubgroup.closure_induction h
      (fun x hx =>
        Subsemigroup.closure_induction hx (fun x hx => subset_closure hx) fun x y hx hy =>
          mul_mem hx hy)
      (zero_mem _) (fun x y hx hy => add_mem hx hy) fun x hx => neg_mem hx⟩

/-- If all elements of `s : set A` commute pairwise, then `closure s` is a commutative ring.  -/
def closureNonUnitalCommRingOfComm {s : Set R} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    NonUnitalCommRing (closure s) :=
  { (closure s).toNonUnitalRing with
    mul_comm := fun x y => by
      ext
      simp only [NonUnitalSubring.val_mul]
      refine'
        closure_induction₂ x.prop y.prop hcomm
          (fun x => by simp only [MulZeroClass.mul_zero, MulZeroClass.zero_mul])
          (fun x => by simp only [MulZeroClass.mul_zero, MulZeroClass.zero_mul])
          (fun x y hxy => by simp only [mul_neg, neg_mul, hxy])
          (fun x y hxy => by simp only [mul_neg, neg_mul, hxy])
          (fun x₁ x₂ y h₁ h₂ => by simp only [add_mul, mul_add, h₁, h₂])
          (fun x₁ x₂ y h₁ h₂ => by simp only [add_mul, mul_add, h₁, h₂])
          (fun x₁ x₂ y h₁ h₂ => by rw [← mul_assoc, ← h₁, mul_assoc x₁ y x₂, ← h₂, mul_assoc])
          fun x₁ x₂ y h₁ h₂ => by rw [← mul_assoc, h₁, mul_assoc, h₂, ← mul_assoc] }

/- probably there is a version if `x ≠ 0`, but we don't have `list.prod`
theorem exists_list_of_mem_closure {s : set R} {x : R} (h : x ∈ closure s) :
  (∃ L : list (list R), (∀ t ∈ L, ∀ y ∈ t, y ∈ s ∨ y = (-1:R)) ∧ (L.map list.prod).sum = x) :=
add_subgroup.closure_induction (mem_closure_iff.1 h)
  (λ x hx, let ⟨l, hl, h⟩ :=submonoid.exists_list_of_mem_closure hx in ⟨[l], by simp [h];
    clear_aux_decl; tauto!⟩)
  ⟨[], by simp⟩
  (λ x y ⟨l, hl1, hl2⟩ ⟨m, hm1, hm2⟩, ⟨l ++ m, λ t ht, (list.mem_append.1 ht).elim (hl1 t) (hm1 t),
    by simp [hl2, hm2]⟩)
  (λ x ⟨L, hL⟩, ⟨L.map (list.cons (-1)), list.forall_mem_map_iff.2 $ λ j hj, list.forall_mem_cons.2
    ⟨or.inr rfl, hL.1 j hj⟩, hL.2 ▸ list.rec_on L (by simp)
      (by simp [list.map_cons, add_comm] {contextual := tt})⟩)
-/
variable (R)


/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : GaloisInsertion (@closure R _) SetLike.coe
    where
  choice s _ := closure s
  gc _s _t := closure_le
  le_l_u _s := subset_closure
  choice_eq _s _h := rfl

variable {R}

/-- Closure of a non_unital_subring `S` equals `S`. -/
theorem closure_eq (s : NonUnitalSubring R) : closure (s : Set R) = s :=
  (NonUnitalSubring.gi R).l_u_eq s

@[simp]
theorem closure_empty : closure (∅ : Set R) = ⊥ :=
  (NonUnitalSubring.gi R).gc.l_bot

@[simp]
theorem closure_univ : closure (Set.univ : Set R) = ⊤ :=
  @coe_top R _ ▸ closure_eq ⊤

theorem closure_union (s t : Set R) : closure (s ∪ t) = closure s ⊔ closure t :=
  (NonUnitalSubring.gi R).gc.l_sup

theorem closure_iUnion {ι} (s : ι → Set R) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (NonUnitalSubring.gi R).gc.l_iSup

theorem closure_sUnion (s : Set (Set R)) : closure (⋃₀ s) = ⨆ t ∈ s, closure t :=
  (NonUnitalSubring.gi R).gc.l_sSup

theorem map_sup (s t : NonUnitalSubring R) (f : F) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
  (@gc_map_comap F R S _ _ _ f).l_sup

theorem map_iSup {ι : Sort _} (f : F) (s : ι → NonUnitalSubring R) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (@gc_map_comap F R S _ _ _ f).l_iSup

theorem comap_inf (s t : NonUnitalSubring S) (f : F) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
  (@gc_map_comap F R S _ _ _ f).u_inf

theorem comap_iInf {ι : Sort _} (f : F) (s : ι → NonUnitalSubring S) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (@gc_map_comap F R S _ _ _ f).u_iInf

@[simp]
theorem map_bot (f : R →ₙ+* S) : (⊥ : NonUnitalSubring R).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
theorem comap_top (f : R →ₙ+* S) : (⊤ : NonUnitalSubring S).comap f = ⊤ :=
  (gc_map_comap f).u_top

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Given `non_unital_subring`s `s`, `t` of rings `R`, `S` respectively, `s.prod t` is `s ×̂ t`
as a non_unital_subring of `R × S`. -/
def prod (s : NonUnitalSubring R) (t : NonUnitalSubring S) : NonUnitalSubring (R × S) :=
  { s.toSubsemigroup.prod t.toSubsemigroup, s.toAddSubgroup.prod t.toAddSubgroup with
    carrier := s ×ˢ t }

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[norm_cast]
theorem coe_prod (s : NonUnitalSubring R) (t : NonUnitalSubring S) :
    (s.prod t : Set (R × S)) = (s : Set R) ×ˢ t :=
  rfl

theorem mem_prod {s : NonUnitalSubring R} {t : NonUnitalSubring S} {p : R × S} :
    p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl

@[mono]
theorem prod_mono ⦃s₁ s₂ : NonUnitalSubring R⦄ (hs : s₁ ≤ s₂) ⦃t₁ t₂ : NonUnitalSubring S⦄
    (ht : t₁ ≤ t₂) : s₁.prod t₁ ≤ s₂.prod t₂ :=
  Set.prod_mono hs ht

theorem prod_mono_right (s : NonUnitalSubring R) :
    Monotone fun t : NonUnitalSubring S => s.prod t :=
  prod_mono (le_refl s)

theorem prod_mono_left (t : NonUnitalSubring S) : Monotone fun s : NonUnitalSubring R => s.prod t :=
  fun _s₁ _s₂ hs => prod_mono hs (le_refl t)

theorem prod_top (s : NonUnitalSubring R) :
    s.prod (⊤ : NonUnitalSubring S) = s.comap (NonUnitalRingHom.fst R S) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_fst]

theorem top_prod (s : NonUnitalSubring S) :
    (⊤ : NonUnitalSubring R).prod s = s.comap (NonUnitalRingHom.snd R S) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_snd]

@[simp]
theorem top_prod_top : (⊤ : NonUnitalSubring R).prod (⊤ : NonUnitalSubring S) = ⊤ :=
  (top_prod _).trans <| comap_top _

/-- Product of non_unital_subrings is isomorphic to their product as rings. -/
def prodEquiv (s : NonUnitalSubring R) (t : NonUnitalSubring S) : s.prod t ≃+* s × t :=
  { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

/-- The underlying set of a non-empty directed Sup of non_unital_subrings is just a union of the
non_unital_subrings. Note that this fails without the directedness assumption (the union of two
non_unital_subrings is typically not a non_unital_subring) -/
theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → NonUnitalSubring R}
    (hS : Directed (· ≤ ·) S) {x : R} : (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i :=
  by
  refine' ⟨_, fun ⟨i, hi⟩ => (SetLike.le_def.1 <| le_iSup S i) hi⟩
  let U : NonUnitalSubring R :=
    NonUnitalSubring.mk' (⋃ i, (S i : Set R)) (⨆ i, (S i).toSubsemigroup) (⨆ i, (S i).toAddSubgroup)
      (Subsemigroup.coe_iSup_of_directed <| hS.mono_comp _ fun _ _ => id)
      (AddSubgroup.coe_iSup_of_directed <| hS.mono_comp _ fun _ _ => id)
  suffices (⨆ i, S i) ≤ U by simpa using @this x
  exact iSup_le fun i x hx => Set.mem_iUnion.2 ⟨i, hx⟩

theorem coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → NonUnitalSubring R}
    (hS : Directed (· ≤ ·) S) : ((⨆ i, S i : NonUnitalSubring R) : Set R) = ⋃ i, ↑(S i) :=
  Set.ext fun x => by simp [mem_iSup_of_directed hS]

theorem mem_sSup_of_directedOn {S : Set (NonUnitalSubring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) {x : R} : x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  haveI : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, SetCoe.exists, Subtype.coe_mk,
    exists_prop]

theorem coe_sSup_of_directedOn {S : Set (NonUnitalSubring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(sSup S) : Set R) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]

theorem mem_map_equiv {f : R ≃+* S} {K : NonUnitalSubring R} {x : S} :
    x ∈ K.map (f : R →ₙ+* S) ↔ f.symm x ∈ K :=
  @Set.mem_image_equiv _ _ (K : Set R) f.toEquiv x

theorem map_equiv_eq_comap_symm (f : R ≃+* S) (K : NonUnitalSubring R) :
    K.map (f : R →ₙ+* S) = K.comap f.symm :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage K)

theorem comap_equiv_eq_map_symm (f : R ≃+* S) (K : NonUnitalSubring S) :
    K.comap (f : R →ₙ+* S) = K.map f.symm :=
  (map_equiv_eq_comap_symm f.symm K).symm

end NonUnitalSubring

/-
namespace non_unital_ring_hom

variables {F : Type w} {R : Type u} {S : Type v} {T : Type*}
variables [non_unital_ring R] [non_unital_ring S] [non_unital_ring T]
variables [non_unital_ring_hom_class F R S]
variables (g : S →ₙ+* T) (f : R →ₙ+* S)
variables {s : non_unital_subring R}

open non_unital_subring

/-- Restriction of a ring homomorphism to its range interpreted as a non_unital_subsemiring.

This is the bundled version of `set.range_factorization`. -/
def range_restrict (f : R →ₙ+* S) : R →ₙ+* f.range :=
f.cod_restrict f.range $ λ x, ⟨x, rfl⟩

@[simp] lemma coe_range_restrict (f : R →ₙ+* S) (x : R) : (f.range_restrict x : S) = f x := rfl

lemma range_restrict_surjective (f : R →ₙ+* S) : function.surjective f.range_restrict :=
λ ⟨y, hy⟩, let ⟨x, hx⟩ := mem_range.mp hy in ⟨x, subtype.ext hx⟩

lemma range_top_iff_surjective {f : R →ₙ+* S} :
  f.range = (⊤ : non_unital_subring S) ↔ function.surjective f :=
set_like.ext'_iff.trans $ iff.trans (by rw [coe_range, coe_top]) set.range_iff_surjective

/-- The range of a surjective ring homomorphism is the whole of the codomain. -/
lemma range_top_of_surjective (f : R →ₙ+* S) (hf : function.surjective f) :
  f.range = (⊤ : non_unital_subring S) :=
range_top_iff_surjective.2 hf

/-- The non_unital_subring of elements `x : R` such that `f x = g x`, i.e.,
  the equalizer of f and g as a non_unital_subring of R -/
def eq_locus (f g : R →ₙ+* S) : non_unital_subring R :=
{ carrier := {x | f x = g x}, .. (f : R →ₙ* S).eq_mlocus g, .. (f : R →+ S).eq_locus g }

@[simp] lemma eq_locus_same (f : R →ₙ+* S) : f.eq_locus f = ⊤ :=
set_like.ext $ λ _, eq_self_iff_true _

/-- If two ring homomorphisms are equal on a set, then they are equal on its non_unital_subring closure. -/
lemma eq_on_set_closure {f g : R →ₙ+* S} {s : set R} (h : set.eq_on f g s) :
  set.eq_on f g (closure s) :=
show closure s ≤ f.eq_locus g, from closure_le.2 h

lemma eq_of_eq_on_set_top {f g : R →ₙ+* S} (h : set.eq_on f g (⊤ : non_unital_subring R)) :
  f = g :=
ext $ λ x, h trivial

lemma eq_of_eq_on_set_dense {s : set R} (hs : closure s = ⊤) {f g : R →ₙ+* S} (h : s.eq_on f g) :
  f = g :=
eq_of_eq_on_set_top $ hs ▸ eq_on_set_closure h

lemma closure_preimage_le (f : R →ₙ+* S) (s : set S) :
  closure (f ⁻¹' s) ≤ (closure s).comap f :=
closure_le.2 $ λ x hx, set_like.mem_coe.2 $ mem_comap.2 $ subset_closure hx

/-- The image under a ring homomorphism of the non_unital_subring generated by a set equals
the non_unital_subring generated by the image of the set. -/
lemma map_closure (f : R →ₙ+* S) (s : set R) :
  (closure s).map f = closure (f '' s) :=
le_antisymm
  (map_le_iff_le_comap.2 $ le_trans (closure_mono $ set.subset_preimage_image _ _)
    (closure_preimage_le _ _))
  (closure_le.2 $ set.image_subset _ subset_closure)

end non_unital_ring_hom

namespace non_unital_subring

variables {F : Type w} {R : Type u} {S : Type v} {T : Type*}
variables [non_unital_ring R] [non_unital_ring S] [non_unital_ring T]
variables [non_unital_ring_hom_class F R S]
variables (g : S →ₙ+* T) (f : R →ₙ+* S)
variables {s : non_unital_subring R}

open non_unital_ring_hom

/-- The ring homomorphism associated to an inclusion of non_unital_subrings. -/
def inclusion {S T : non_unital_subring R} (h : S ≤ T) : S →ₙ+* T :=
(non_unital_subring_class.subtype S).cod_restrict _ (λ x, h x.2)

@[simp] lemma range_subtype (s : non_unital_subring R) :
  (non_unital_subring_class.subtype s).range = s :=
set_like.coe_injective $ (coe_srange _).trans subtype.range_coe

@[simp]
lemma range_fst : (fst R S).srange = ⊤ :=
(fst R S).srange_top_of_surjective $ prod.fst_surjective

@[simp]
lemma range_snd : (snd R S).srange = ⊤ :=
(snd R S).srange_top_of_surjective $ prod.snd_surjective

end non_unital_subring

namespace ring_equiv

variables {F : Type w} {R : Type u} {S : Type v} {T : Type*}
variables [non_unital_ring R] [non_unital_ring S] [non_unital_ring T]
variables [non_unital_ring_hom_class F R S]
variables (g : S →ₙ+* T) (f : R →ₙ+* S)
variables {s t : non_unital_subring R}

/-- Makes the identity isomorphism from a proof two non_unital_subrings of a multiplicative
    monoid are equal. -/
def non_unital_subring_congr (h : s = t) : s ≃+* t :=
{ map_mul' :=  λ _ _, rfl, map_add' := λ _ _, rfl, ..equiv.set_congr $ congr_arg _ h }

/-- Restrict a ring homomorphism with a left inverse to a ring isomorphism to its
`ring_hom.range`. -/
def of_left_inverse' {g : S → R} {f : R →ₙ+* S} (h : function.left_inverse g f) :
  R ≃+* f.range :=
{ to_fun := λ x, f.range_restrict x,
  inv_fun := λ x, (g ∘ (non_unital_subring_class.subtype f.range)) x,
  left_inv := h,
  right_inv := λ x, subtype.ext $
    let ⟨x', hx'⟩ := non_unital_ring_hom.mem_range.mp x.prop in
    show f (g x) = x, by rw [←hx', h x'],
  ..f.range_restrict }

@[simp] lemma of_left_inverse'_apply
  {g : S → R} {f : R →ₙ+* S} (h : function.left_inverse g f) (x : R) :
  ↑(of_left_inverse' h x) = f x := rfl

@[simp] lemma of_left_inverse'_symm_apply
  {g : S → R} {f : R →ₙ+* S} (h : function.left_inverse g f) (x : f.range) :
  (of_left_inverse' h).symm x = g x := rfl

/-
/-- Given an equivalence `e : R ≃+* S` of rings and a non_unital_subring `s` of `R`,
`non_unital_subring_equiv_map e s` is the induced equivalence between `s` and `s.map e` -/
@[simps] def non_unital_subring_map (e : R ≃+* S) :
  s ≃+* s.map e.to_ring_hom :=
e.non_unital_subsemiring_map s.to_non_unital_subsemiring
-/

end ring_equiv

namespace non_unital_subring

variables {F : Type w} {R : Type u} {S : Type v}
variables [non_unital_ring R] [non_unital_ring S]
variables [non_unital_ring_hom_class F R S]

lemma closure_preimage_le (f : F) (s : set S) :
  closure ((f : R → S) ⁻¹' s) ≤ (closure s).comap f :=
closure_le.2 $ λ x hx, set_like.mem_coe.2 $ mem_comap.2 $ subset_closure hx

end non_unital_subring
-/
end Hom
