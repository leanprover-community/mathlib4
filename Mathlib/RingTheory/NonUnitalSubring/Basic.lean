/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.RingTheory.NonUnitalSubsemiring.Basic

/-!
# `NonUnitalSubring`s

Let `R` be a non-unital ring. This file defines the "bundled" non-unital subring type
`NonUnitalSubring R`, a type whose terms correspond to non-unital subrings of `R`.
This is the preferred way to talk about non-unital subrings in mathlib.

We prove that non-unital subrings are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `Set R` to `NonUnitalSubring R`, sending a subset of
`R` to the non-unital subring it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(R : Type u) [NonUnitalRing R] (S : Type u) [NonUnitalRing S] (f g : R →ₙ+* S)`
`(A : NonUnitalSubring R) (B : NonUnitalSubring S) (s : Set R)`

* `NonUnitalSubring R` : the type of non-unital subrings of a ring `R`.

* `instance : CompleteLattice (NonUnitalSubring R)` : the complete lattice structure on the
  non-unital subrings.

* `NonUnitalSubring.center` : the center of a non-unital ring `R`.

* `NonUnitalSubring.closure` : non-unital subring closure of a set, i.e., the smallest
  non-unital subring that includes the set.

* `NonUnitalSubring.gi` : `closure : Set M → NonUnitalSubring M` and coercion
  `coe : NonUnitalSubring M → Set M`
  form a `GaloisInsertion`.

* `comap f B : NonUnitalSubring A` : the preimage of a non-unital subring `B` along the
  non-unital ring homomorphism `f`

* `map f A : NonUnitalSubring B` : the image of a non-unital subring `A` along the
  non-unital ring homomorphism `f`.

* `Prod A B : NonUnitalSubring (R × S)` : the product of non-unital subrings

* `f.range : NonUnitalSubring B` : the range of the non-unital ring homomorphism `f`.

* `eq_locus f g : NonUnitalSubring R` : given non-unital ring homomorphisms `f g : R →ₙ+* S`,
     the non-unital subring of `R` where `f x = g x`

## Implementation notes

A non-unital subring is implemented as a `NonUnitalSubsemiring` which is also an
additive subgroup.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a non-unital subring's underlying set.

## Tags
non-unital subring
-/


open scoped BigOperators

universe u v w

section Basic

variable {R : Type u} {S : Type v} {T : Type w} [NonUnitalNonAssocRing R]

section NonUnitalSubringClass

/-- `NonUnitalSubringClass S R` states that `S` is a type of subsets `s ⊆ R` that
are both a multiplicative submonoid and an additive subgroup. -/
class NonUnitalSubringClass (S : Type*) (R : Type u) [NonUnitalNonAssocRing R]
    [SetLike S R] extends NonUnitalSubsemiringClass S R, NegMemClass S R : Prop where

-- See note [lower instance priority]
instance (priority := 100) NonUnitalSubringClass.addSubgroupClass (S : Type*) (R : Type u)
    [SetLike S R] [NonUnitalNonAssocRing R] [h : NonUnitalSubringClass S R] :
    AddSubgroupClass S R :=
  { h with }

variable [SetLike S R] [hSR : NonUnitalSubringClass S R] (s : S)

namespace NonUnitalSubringClass

-- Prefer subclasses of `NonUnitalRing` over subclasses of `NonUnitalSubringClass`.
/-- A non-unital subring of a non-unital ring inherits a non-unital ring structure -/
instance (priority := 75) toNonUnitalNonAssocRing : NonUnitalNonAssocRing s :=
  Subtype.val_injective.nonUnitalNonAssocRing _ rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

-- Prefer subclasses of `NonUnitalRing` over subclasses of `NonUnitalSubringClass`.
/-- A non-unital subring of a non-unital ring inherits a non-unital ring structure -/
instance (priority := 75) toNonUnitalRing {R : Type*} [NonUnitalRing R] [SetLike S R]
    [NonUnitalSubringClass S R] (s : S) : NonUnitalRing s :=
  Subtype.val_injective.nonUnitalRing _ rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

-- Prefer subclasses of `NonUnitalRing` over subclasses of `NonUnitalSubringClass`.
/-- A non-unital subring of a `NonUnitalCommRing` is a `NonUnitalCommRing`. -/
instance (priority := 75) toNonUnitalCommRing {R} [NonUnitalCommRing R] [SetLike S R]
    [NonUnitalSubringClass S R] : NonUnitalCommRing s :=
  Subtype.val_injective.nonUnitalCommRing _ rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

/-- The natural non-unital ring hom from a non-unital subring of a non-unital ring `R` to `R`. -/
def subtype (s : S) : s →ₙ+* R :=
  { NonUnitalSubsemiringClass.subtype s,
    AddSubgroupClass.subtype s with
    toFun := Subtype.val }

@[simp]
theorem coe_subtype : (subtype s : s → R) = Subtype.val :=
  rfl

end NonUnitalSubringClass

end NonUnitalSubringClass

variable [NonUnitalNonAssocRing S] [NonUnitalNonAssocRing T]

/-- `NonUnitalSubring R` is the type of non-unital subrings of `R`. A non-unital subring of `R`
is a subset `s` that is a multiplicative subsemigroup and an additive subgroup. Note in particular
that it shares the same 0 as R. -/
structure NonUnitalSubring (R : Type u) [NonUnitalNonAssocRing R] extends
  NonUnitalSubsemiring R, AddSubgroup R

/-- Reinterpret a `NonUnitalSubring` as a `NonUnitalSubsemiring`. -/
add_decl_doc NonUnitalSubring.toNonUnitalSubsemiring

/-- Reinterpret a `NonUnitalSubring` as an `AddSubgroup`. -/
add_decl_doc NonUnitalSubring.toAddSubgroup

namespace NonUnitalSubring

/-- The underlying submonoid of a `NonUnitalSubring`. -/
def toSubsemigroup (s : NonUnitalSubring R) : Subsemigroup R :=
  { s.toNonUnitalSubsemiring.toSubsemigroup with carrier := s.carrier }

instance : SetLike (NonUnitalSubring R) R
    where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective h
                             -- ⊢ { toNonUnitalSubsemiring := toNonUnitalSubsemiring✝, neg_mem' := neg_mem'✝ } …
                                      -- ⊢ { toNonUnitalSubsemiring := toNonUnitalSubsemiring✝¹, neg_mem' := neg_mem'✝¹ …
                                               -- ⊢ toNonUnitalSubsemiring✝¹ = toNonUnitalSubsemiring✝
                                                      -- 🎉 no goals

instance : NonUnitalSubringClass (NonUnitalSubring R) R
    where
  zero_mem s := s.zero_mem'
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  neg_mem {s} := s.neg_mem'

theorem mem_carrier {s : NonUnitalSubring R} {x : R} : x ∈ s.toNonUnitalSubsemiring ↔ x ∈ s :=
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

/-- Construct a `NonUnitalSubring R` from a set `s`, a subsemigroup `sm`, and an additive
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

/-- Sum of a multiset of elements in a `NonUnitalSubring` of a `NonUnitalRing` is
in the `NonUnitalSubring`. -/
protected theorem multiset_sum_mem {R} [NonUnitalNonAssocRing R] (s : NonUnitalSubring R)
    (m : Multiset R) : (∀ a ∈ m, a ∈ s) → m.sum ∈ s :=
  multiset_sum_mem _

/-- Sum of elements in a `NonUnitalSubring` of a `NonUnitalRing` indexed by a `Finset`
is in the `NonUnitalSubring`. -/
protected theorem sum_mem {R : Type*} [NonUnitalNonAssocRing R] (s : NonUnitalSubring R)
    {ι : Type*} {t : Finset ι} {f : ι → R} (h : ∀ c ∈ t, f c ∈ s) : (∑ i in t, f i) ∈ s :=
  sum_mem h

/-- A non-unital subring of a non-unital ring inherits a non-unital ring structure -/
instance toNonUnitalRing {R : Type*} [NonUnitalRing R] (s : NonUnitalSubring R) :
    NonUnitalRing s :=
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

theorem coe_eq_zero_iff {x : s} : (x : R) = 0 ↔ x = 0 := by
  simp
  -- 🎉 no goals

/-- A non-unital subring of a `NonUnitalCommRing` is a `NonUnitalCommRing`. -/
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

@[simp]
theorem mem_toNonUnitalSubsemiring {s : NonUnitalSubring R} {x : R} :
    x ∈ s.toNonUnitalSubsemiring ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem coe_toNonUnitalSubsemiring (s : NonUnitalSubring R) :
    (s.toNonUnitalSubsemiring : Set R) = s :=
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

/-- The ring equiv between the top element of `NonUnitalSubring R` and `R`. -/
@[simps!]
def topEquiv : (⊤ : NonUnitalSubring R) ≃+* R := NonUnitalSubsemiring.topEquiv

end NonUnitalSubring

end Basic

section Hom

namespace NonUnitalSubring

variable {F : Type w} {R : Type u} {S : Type v} {T : Type*} {SR : Type*}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] [NonUnitalNonAssocRing T]
  [NonUnitalRingHomClass F R S] (s : NonUnitalSubring R)

/-! ## comap -/


/-- The preimage of a `NonUnitalSubring` along a ring homomorphism is a `NonUnitalSubring`. -/
def comap {F : Type w} {R : Type u} {S : Type v} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
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

/-- The image of a `NonUnitalSubring` along a ring homomorphism is a `NonUnitalSubring`. -/
def map {F : Type w} {R : Type u} {S : Type v} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
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

/-- A `NonUnitalSubring` is isomorphic to its image under an injective function -/
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

variable {R : Type u} {S : Type v} {T : Type*}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] [NonUnitalNonAssocRing T]
  (g : S →ₙ+* T) (f : R →ₙ+* S)

/-! ## range -/

/-- The range of a ring homomorphism, as a `NonUnitalSubring` of the target.
See Note [range copy pattern]. -/
def range {R : Type u} {S : Type v} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
    (f : R →ₙ+* S) : NonUnitalSubring S :=
  ((⊤ : NonUnitalSubring R).map f).copy (Set.range f) Set.image_univ.symm

@[simp]
theorem coe_range : (f.range : Set S) = Set.range f :=
  rfl

@[simp]
theorem mem_range {f : R →ₙ+* S} {y : S} : y ∈ f.range ↔ ∃ x, f x = y :=
  Iff.rfl

theorem range_eq_map (f : R →ₙ+* S) : f.range = NonUnitalSubring.map f ⊤ := by ext; simp
                                                                               -- ⊢ x✝ ∈ range f ↔ x✝ ∈ NonUnitalSubring.map f ⊤
                                                                                    -- 🎉 no goals

theorem mem_range_self (f : R →ₙ+* S) (x : R) : f x ∈ f.range :=
  mem_range.mpr ⟨x, rfl⟩

theorem map_range : f.range.map g = (g.comp f).range := by
  simpa only [range_eq_map] using (⊤ : NonUnitalSubring R).map_map g f
  -- 🎉 no goals

/-- The range of a ring homomorphism is a fintype, if the domain is a fintype.
Note: this instance can form a diamond with `Subtype.fintype` in the
  presence of `Fintype S`. -/
instance fintypeRange [Fintype R] [DecidableEq S] (f : R →ₙ+* S) : Fintype (range f) :=
  Set.fintypeRange f

end NonUnitalRingHom

namespace NonUnitalSubring

section Order

variable {F : Type w} {R : Type u} {S : Type v} {T : Type*}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] [NonUnitalNonAssocRing T]
  [NonUnitalRingHomClass F R S]
  (g : S →ₙ+* T) (f : R →ₙ+* S)

/-! ## bot -/


instance : Bot (NonUnitalSubring R) :=
  ⟨(0 : R →ₙ+* R).range⟩

instance : Inhabited (NonUnitalSubring R) :=
  ⟨⊥⟩

theorem coe_bot : ((⊥ : NonUnitalSubring R) : Set R) = {0} :=
  (NonUnitalRingHom.coe_range (0 : R →ₙ+* R)).trans (@Set.range_const R R _ 0)

theorem mem_bot {x : R} : x ∈ (⊥ : NonUnitalSubring R) ↔ x = 0 :=
  show x ∈ ((⊥ : NonUnitalSubring R) : Set R) ↔ x = 0 by rw [coe_bot, Set.mem_singleton_iff]
                                                         -- 🎉 no goals

/-! ## inf -/

/-- The inf of two `NonUnitalSubring`s is their intersection. -/
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
                                                      -- 🎉 no goals
                                                                -- 🎉 no goals

@[simp, norm_cast]
theorem coe_sInf (S : Set (NonUnitalSubring R)) :
    ((sInf S : NonUnitalSubring R) : Set R) = ⋂ s ∈ S, ↑s :=
  rfl

theorem mem_sInf {S : Set (NonUnitalSubring R)} {x : R} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂

@[simp, norm_cast]
theorem coe_iInf {ι : Sort*} {S : ι → NonUnitalSubring R} : (↑(⨅ i, S i) : Set R) = ⋂ i, S i := by
  simp only [iInf, coe_sInf, Set.biInter_range]
  -- 🎉 no goals

theorem mem_iInf {ι : Sort*} {S : ι → NonUnitalSubring R} {x : R} :
    (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by simp only [iInf, mem_sInf, Set.forall_range_iff]
                                        -- 🎉 no goals

@[simp]
theorem sInf_toSubsemigroup (s : Set (NonUnitalSubring R)) :
    (sInf s).toSubsemigroup = ⨅ t ∈ s, NonUnitalSubring.toSubsemigroup t :=
  mk'_toSubsemigroup _ _

@[simp]
theorem sInf_toAddSubgroup (s : Set (NonUnitalSubring R)) :
    (sInf s).toAddSubgroup = ⨅ t ∈ s, NonUnitalSubring.toAddSubgroup t :=
  mk'_toAddSubgroup _ _

/-- `NonUnitalSubring`s of a ring form a complete lattice. -/
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

end Order

/-! ## Center of a ring -/

section

variable {R : Type u} [NonUnitalRing R]

variable (R)

/-- The center of a ring `R` is the set of elements that commute with everything in `R` -/
def center : NonUnitalSubring R :=
  { NonUnitalSubsemiring.center R with
    carrier := Set.center R
    neg_mem' := Set.neg_mem_center }

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

/-! ## `NonUnitalSubring` closure of a subset -/

variable {F : Type w} {R : Type u} {S : Type v} {T : Type*}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] [NonUnitalNonAssocRing T]
  [NonUnitalRingHomClass F R S]
  (g : S →ₙ+* T) (f : R →ₙ+* S)

/-- The `NonUnitalSubring` generated by a set. -/
def closure (s : Set R) : NonUnitalSubring R :=
  sInf {S | s ⊆ S}

theorem mem_closure {x : R} {s : Set R} : x ∈ closure s ↔ ∀ S : NonUnitalSubring R, s ⊆ S → x ∈ S :=
  mem_sInf

/-- The `NonUnitalSubring` generated by a set includes the set. -/
@[simp]
theorem subset_closure {s : Set R} : s ⊆ closure s := fun _x hx => mem_closure.2 fun _S hS => hS hx

theorem not_mem_of_not_mem_closure {s : Set R} {P : R} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)

/-- A `NonUnitalSubring` `t` includes `closure s` if and only if it includes `s`. -/
@[simp]
theorem closure_le {s : Set R} {t : NonUnitalSubring R} : closure s ≤ t ↔ s ⊆ t :=
  ⟨Set.Subset.trans subset_closure, fun h => sInf_le h⟩

/-- `NonUnitalSubring` closure of a set is monotone in its argument: if `s ⊆ t`,
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

/-- The difference with `NonUnitalSubring.closure_induction` is that this acts on the
subtype. -/
@[elab_as_elim]
theorem closure_induction' {s : Set R} {p : closure s → Prop} (a : closure s)
    (Hs : ∀ (x) (hx : x ∈ s), p ⟨x, subset_closure hx⟩) (H0 : p 0)
    (Hadd : ∀ x y, p x → p y → p (x + y)) (Hneg : ∀ x, p x → p (-x))
    (Hmul : ∀ x y, p x → p y → p (x * y)) : p a :=
  Subtype.recOn a fun b hb => by
    refine' Exists.elim _ fun (hb : b ∈ closure s) (hc : p ⟨b, hb⟩) => hc
    -- ⊢ ∃ x, p { val := b, property := x }
    refine'
      closure_induction hb (fun x hx => ⟨subset_closure hx, Hs x hx⟩) ⟨zero_mem (closure s), H0⟩ _ _
        _
    · rintro x y ⟨hx, hpx⟩ ⟨hy, hpy⟩
      -- ⊢ ∃ x_1, p { val := x + y, property := x_1 }
      exact ⟨add_mem hx hy, Hadd _ _ hpx hpy⟩
      -- 🎉 no goals
    · rintro x ⟨hx, hpx⟩
      -- ⊢ ∃ x_1, p { val := -x, property := x_1 }
      exact ⟨neg_mem hx, Hneg _ hpx⟩
      -- 🎉 no goals
    · rintro x y ⟨hx, hpx⟩ ⟨hy, hpy⟩
      -- ⊢ ∃ x_1, p { val := x * y, property := x_1 }
      exact ⟨mul_mem hx hy, Hmul _ _ hpx hpy⟩
      -- 🎉 no goals

/-- An induction principle for closure membership, for predicates with two arguments. -/
@[elab_as_elim]
theorem closure_induction₂ {s : Set R} {p : R → R → Prop} {a b : R} (ha : a ∈ closure s)
    (hb : b ∈ closure s) (Hs : ∀ x ∈ s, ∀ y ∈ s, p x y) (H0_left : ∀ x, p 0 x)
    (H0_right : ∀ x, p x 0) (Hneg_left : ∀ x y, p x y → p (-x) y)
    (Hneg_right : ∀ x y, p x y → p x (-y)) (Hadd_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ + x₂) y)
    (Hadd_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ + y₂))
    (Hmul_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ * x₂) y)
    (Hmul_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ * y₂)) : p a b := by
  refine' closure_induction hb _ (H0_right _) (Hadd_right a) (Hneg_right a) (Hmul_right a)
  -- ⊢ ∀ (x : R), x ∈ s → p a x
  refine' closure_induction ha Hs (fun x _ => H0_left x) _ _ _
  · exact fun x y H₁ H₂ z zs => Hadd_left x y z (H₁ z zs) (H₂ z zs)
    -- 🎉 no goals
  · exact fun x hx z zs => Hneg_left x z (hx z zs)
    -- 🎉 no goals
  · exact fun x y H₁ H₂ z zs => Hmul_left x y z (H₁ z zs) (H₂ z zs)
    -- 🎉 no goals

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
            (by rw [zero_mul q]; apply AddSubgroup.zero_mem _)
                -- ⊢ 0 ∈ AddSubgroup.closure ↑(Subsemigroup.closure s)
                                 -- 🎉 no goals
            (fun p₁ p₂ ihp₁ ihp₂ => by rw [add_mul p₁ p₂ q]; apply AddSubgroup.add_mem _ ihp₁ ihp₂)
                                       -- ⊢ p₁ * q + p₂ * q ∈ AddSubgroup.closure ↑(Subsemigroup.closure s)
                                                             -- 🎉 no goals
            fun x hx => by
            have f : -x * q = -(x * q) := by simp
            -- ⊢ -x * q ∈ AddSubgroup.closure ↑(Subsemigroup.closure s)
            rw [f]; apply AddSubgroup.neg_mem _ hx)
            -- ⊢ -(x * q) ∈ AddSubgroup.closure ↑(Subsemigroup.closure s)
                    -- 🎉 no goals
        (by rw [mul_zero x]; apply AddSubgroup.zero_mem _)
            -- ⊢ 0 ∈ AddSubgroup.closure ↑(Subsemigroup.closure s)
                             -- 🎉 no goals
        (fun q₁ q₂ ihq₁ ihq₂ => by rw [mul_add x q₁ q₂]; apply AddSubgroup.add_mem _ ihq₁ ihq₂)
                                   -- ⊢ x * q₁ + x * q₂ ∈ AddSubgroup.closure ↑(Subsemigroup.closure s)
                                                         -- 🎉 no goals
        fun z hz => by
        have f : x * -z = -(x * z) := by simp
        -- ⊢ x * -z ∈ AddSubgroup.closure ↑(Subsemigroup.closure s)
        rw [f]; apply AddSubgroup.neg_mem _ hz,
        -- ⊢ -(x * z) ∈ AddSubgroup.closure ↑(Subsemigroup.closure s)
                -- 🎉 no goals
    fun h =>
    AddSubgroup.closure_induction h
      (fun x hx =>
        Subsemigroup.closure_induction hx (fun x hx => subset_closure hx) fun x y hx hy =>
          mul_mem hx hy)
      (zero_mem _) (fun x y hx hy => add_mem hx hy) fun x hx => neg_mem hx⟩

/-- If all elements of `s : Set A` commute pairwise, then `closure s` is a commutative ring.  -/
def closureNonUnitalCommRingOfComm {R : Type u} [NonUnitalRing R] {s : Set R}
    (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) : NonUnitalCommRing (closure s) :=
  { (closure s).toNonUnitalRing with
    mul_comm := fun x y => by
      ext
      -- ⊢ ↑(x * y) = ↑(y * x)
      simp only [NonUnitalSubring.val_mul]
      -- ⊢ ↑x * ↑y = ↑y * ↑x
      refine'
        closure_induction₂ x.prop y.prop hcomm
          (fun x => by simp only [mul_zero, zero_mul])
          (fun x => by simp only [mul_zero, zero_mul])
          (fun x y hxy => by simp only [mul_neg, neg_mul, hxy])
          (fun x y hxy => by simp only [mul_neg, neg_mul, hxy])
          (fun x₁ x₂ y h₁ h₂ => by simp only [add_mul, mul_add, h₁, h₂])
          (fun x₁ x₂ y h₁ h₂ => by simp only [add_mul, mul_add, h₁, h₂])
          (fun x₁ x₂ y h₁ h₂ => by rw [← mul_assoc, ← h₁, mul_assoc x₁ y x₂, ← h₂, mul_assoc])
          fun x₁ x₂ y h₁ h₂ => by rw [← mul_assoc, h₁, mul_assoc, h₂, ← mul_assoc] }

variable (R)

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : GaloisInsertion (@closure R _) SetLike.coe
    where
  choice s _ := closure s
  gc _s _t := closure_le
  le_l_u _s := subset_closure
  choice_eq _s _h := rfl

variable {R}

/-- Closure of a `NonUnitalSubring` `S` equals `S`. -/
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

theorem map_iSup {ι : Sort*} (f : F) (s : ι → NonUnitalSubring R) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (@gc_map_comap F R S _ _ _ f).l_iSup

theorem comap_inf (s t : NonUnitalSubring S) (f : F) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
  (@gc_map_comap F R S _ _ _ f).u_inf

theorem comap_iInf {ι : Sort*} (f : F) (s : ι → NonUnitalSubring S) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (@gc_map_comap F R S _ _ _ f).u_iInf

@[simp]
theorem map_bot (f : R →ₙ+* S) : (⊥ : NonUnitalSubring R).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
theorem comap_top (f : R →ₙ+* S) : (⊤ : NonUnitalSubring S).comap f = ⊤ :=
  (gc_map_comap f).u_top

/-- Given `NonUnitalSubring`s `s`, `t` of rings `R`, `S` respectively, `s.prod t` is `s ×ˢ t`
as a `NonUnitalSubring` of `R × S`. -/
def prod (s : NonUnitalSubring R) (t : NonUnitalSubring S) : NonUnitalSubring (R × S) :=
  { s.toSubsemigroup.prod t.toSubsemigroup, s.toAddSubgroup.prod t.toAddSubgroup with
    carrier := s ×ˢ t }

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
                  -- 🎉 no goals

theorem top_prod (s : NonUnitalSubring S) :
    (⊤ : NonUnitalSubring R).prod s = s.comap (NonUnitalRingHom.snd R S) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_snd]
                  -- 🎉 no goals

@[simp]
theorem top_prod_top : (⊤ : NonUnitalSubring R).prod (⊤ : NonUnitalSubring S) = ⊤ :=
  (top_prod _).trans <| comap_top _

/-- Product of `NonUnitalSubring`s is isomorphic to their product as rings. -/
def prodEquiv (s : NonUnitalSubring R) (t : NonUnitalSubring S) : s.prod t ≃+* s × t :=
  { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

/-- The underlying set of a non-empty directed Sup of `NonUnitalSubring`s is just a union of the
`NonUnitalSubring`s. Note that this fails without the directedness assumption (the union of two
`NonUnitalSubring`s is typically not a `NonUnitalSubring`) -/
theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → NonUnitalSubring R}
    (hS : Directed (· ≤ ·) S) {x : R} : (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  refine' ⟨_, fun ⟨i, hi⟩ => (SetLike.le_def.1 <| le_iSup S i) hi⟩
  -- ⊢ x ∈ ⨆ (i : ι), S i → ∃ i, x ∈ S i
  let U : NonUnitalSubring R :=
    NonUnitalSubring.mk' (⋃ i, (S i : Set R)) (⨆ i, (S i).toSubsemigroup) (⨆ i, (S i).toAddSubgroup)
      (Subsemigroup.coe_iSup_of_directed <| hS.mono_comp _ fun _ _ => id)
      (AddSubgroup.coe_iSup_of_directed <| hS.mono_comp _ fun _ _ => id)
  suffices (⨆ i, S i) ≤ U by simpa using @this x
  -- ⊢ ⨆ (i : ι), S i ≤ U
  exact iSup_le fun i x hx => Set.mem_iUnion.2 ⟨i, hx⟩
  -- 🎉 no goals

theorem coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → NonUnitalSubring R}
    (hS : Directed (· ≤ ·) S) : ((⨆ i, S i : NonUnitalSubring R) : Set R) = ⋃ i, ↑(S i) :=
  Set.ext fun x => by simp [mem_iSup_of_directed hS]
                      -- 🎉 no goals

theorem mem_sSup_of_directedOn {S : Set (NonUnitalSubring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) {x : R} : x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  haveI : Nonempty S := Sne.to_subtype
  -- ⊢ x ∈ sSup S ↔ ∃ s, s ∈ S ∧ x ∈ s
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, SetCoe.exists, Subtype.coe_mk,
    exists_prop]

theorem coe_sSup_of_directedOn {S : Set (NonUnitalSubring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(sSup S) : Set R) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]
                      -- 🎉 no goals

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

namespace NonUnitalRingHom

variable {F : Type w} {R : Type u} {S : Type v} {T : Type*}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] [NonUnitalNonAssocRing T]
  [NonUnitalRingHomClass F R S]
  (g : S →ₙ+* T) (f : R →ₙ+* S)
  {s : NonUnitalSubring R}

open NonUnitalSubring

/-- Restriction of a ring homomorphism to its range interpreted as a `NonUnitalSubring`.

This is the bundled version of `Set.rangeFactorization`. -/
def rangeRestrict (f : R →ₙ+* S) : R →ₙ+* f.range :=
  NonUnitalRingHom.codRestrict f f.range fun x => ⟨x, rfl⟩

@[simp]
theorem coe_rangeRestrict (f : R →ₙ+* S) (x : R) : (f.rangeRestrict x : S) = f x :=
  rfl

theorem rangeRestrict_surjective (f : R →ₙ+* S) : Function.Surjective f.rangeRestrict :=
  fun ⟨_y, hy⟩ =>
  let ⟨x, hx⟩ := mem_range.mp hy
  ⟨x, Subtype.ext hx⟩

theorem range_top_iff_surjective {f : R →ₙ+* S} :
    f.range = (⊤ : NonUnitalSubring S) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_range, coe_top]) Set.range_iff_surjective
                                          -- 🎉 no goals

/-- The range of a surjective ring homomorphism is the whole of the codomain. -/
@[simp]
theorem range_top_of_surjective (f : R →ₙ+* S) (hf : Function.Surjective f) :
    f.range = (⊤ : NonUnitalSubring S) :=
  range_top_iff_surjective.2 hf

/-- The `NonUnitalSubring` of elements `x : R` such that `f x = g x`, i.e.,
  the equalizer of f and g as a `NonUnitalSubring` of R -/
def eqLocus (f g : R →ₙ+* S) : NonUnitalSubring R :=
  { (f : R →ₙ* S).eqLocus g, (f : R →+ S).eqLocus g with carrier := {x | f x = g x} }

@[simp]
theorem eqLocus_same (f : R →ₙ+* S) : f.eqLocus f = ⊤ :=
  SetLike.ext fun _ => eq_self_iff_true _

/-- If two ring homomorphisms are equal on a set, then they are equal on its
`NonUnitalSubring` closure. -/
theorem eqOn_set_closure {f g : R →ₙ+* S} {s : Set R} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocus g from closure_le.2 h

theorem eq_of_eqOn_set_top {f g : R →ₙ+* S} (h : Set.EqOn f g (⊤ : NonUnitalSubring R)) : f = g :=
  ext fun _x => h trivial

theorem eq_of_eqOn_set_dense {s : Set R} (hs : closure s = ⊤) {f g : R →ₙ+* S} (h : s.EqOn f g) :
    f = g :=
  eq_of_eqOn_set_top <| hs ▸ eqOn_set_closure h

theorem closure_preimage_le (f : R →ₙ+* S) (s : Set S) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _x hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

/-- The image under a ring homomorphism of the `NonUnitalSubring` generated by a set equals
the `NonUnitalSubring` generated by the image of the set. -/
theorem map_closure (f : R →ₙ+* S) (s : Set R) : (closure s).map f = closure (f '' s) :=
  le_antisymm
    (map_le_iff_le_comap.2 <|
      le_trans (closure_mono <| Set.subset_preimage_image _ _) (closure_preimage_le _ _))
    (closure_le.2 <| Set.image_subset _ subset_closure)

end NonUnitalRingHom

namespace NonUnitalSubring

variable {F : Type w} {R : Type u} {S : Type v} {T : Type*}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] [NonUnitalNonAssocRing T]
  [NonUnitalRingHomClass F R S]
  (g : S →ₙ+* T) (f : R →ₙ+* S)
  {s : NonUnitalSubring R}

open NonUnitalRingHom

/-- The ring homomorphism associated to an inclusion of `NonUnitalSubring`s. -/
def inclusion {S T : NonUnitalSubring R} (h : S ≤ T) : S →ₙ+* T :=
  NonUnitalRingHom.codRestrict (NonUnitalSubringClass.subtype S) _ fun x => h x.2

@[simp]
theorem range_subtype (s : NonUnitalSubring R) : (NonUnitalSubringClass.subtype s).range = s :=
  SetLike.coe_injective <| (coe_srange _).trans Subtype.range_coe

theorem range_fst : NonUnitalRingHom.srange (fst R S) = ⊤ :=
  NonUnitalSubsemiring.range_fst

theorem range_snd : NonUnitalRingHom.srange (snd R S) = ⊤ :=
  NonUnitalSubsemiring.range_snd

end NonUnitalSubring

namespace RingEquiv

variable {F : Type w} {R : Type u} {S : Type v} {T : Type*}
  [NonUnitalRing R] [NonUnitalRing S] [NonUnitalRing T]
  [NonUnitalRingHomClass F R S]
  (g : S →ₙ+* T) (f : R →ₙ+* S)
  {s t : NonUnitalSubring R}

/-- Makes the identity isomorphism from a proof two `NonUnitalSubring`s of a multiplicative
    monoid are equal. -/
def nonUnitalSubringCongr (h : s = t) : s ≃+* t :=
  {
    Equiv.setCongr <| congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

/-- Restrict a ring homomorphism with a left inverse to a ring isomorphism to its
`RingHom.range`. -/
def ofLeftInverse' {g : S → R} {f : R →ₙ+* S} (h : Function.LeftInverse g f) : R ≃+* f.range :=
  { f.rangeRestrict with
    toFun := fun x => f.rangeRestrict x
    invFun := fun x => (g ∘ NonUnitalSubringClass.subtype f.range) x
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := NonUnitalRingHom.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }
                            -- 🎉 no goals

@[simp]
theorem ofLeftInverse'_apply {g : S → R} {f : R →ₙ+* S} (h : Function.LeftInverse g f) (x : R) :
    ↑(ofLeftInverse' h x) = f x :=
  rfl

@[simp]
theorem ofLeftInverse'_symm_apply {g : S → R} {f : R →ₙ+* S} (h : Function.LeftInverse g f)
    (x : f.range) : (ofLeftInverse' h).symm x = g x :=
  rfl

end RingEquiv

namespace NonUnitalSubring

variable {F : Type w} {R : Type u} {S : Type v}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
  [NonUnitalRingHomClass F R S]

theorem closure_preimage_le (f : F) (s : Set S) :
    closure ((f : R → S) ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _x hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

end NonUnitalSubring

end Hom
