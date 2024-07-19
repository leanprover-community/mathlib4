/-
Copyright (c) 2020 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Ring.Subsemiring.Basic

/-!
# Subrings

Let `R` be a ring. This file defines the "bundled" subring type `Subring R`, a type
whose terms correspond to subrings of `R`. This is the preferred way to talk
about subrings in mathlib. Unbundled subrings (`s : Set R` and `IsSubring s`)
are not in this file, and they will ultimately be deprecated.

We prove that subrings are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `Set R` to `Subring R`, sending a subset of `R`
to the subring it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(R : Type u) [Ring R] (S : Type u) [Ring S] (f g : R →+* S)`
`(A : Subring R) (B : Subring S) (s : Set R)`

* `Subring R` : the type of subrings of a ring `R`.

* `instance : CompleteLattice (Subring R)` : the complete lattice structure on the subrings.

* `Subring.center` : the center of a ring `R`.

* `Subring.closure` : subring closure of a set, i.e., the smallest subring that includes the set.

* `Subring.gi` : `closure : Set M → Subring M` and coercion `(↑) : Subring M → et M`
  form a `GaloisInsertion`.

* `comap f B : Subring A` : the preimage of a subring `B` along the ring homomorphism `f`

* `map f A : Subring B` : the image of a subring `A` along the ring homomorphism `f`.

* `prod A B : Subring (R × S)` : the product of subrings

* `f.range : Subring B` : the range of the ring homomorphism `f`.

* `eqLocus f g : Subring R` : given ring homomorphisms `f g : R →+* S`,
     the subring of `R` where `f x = g x`

## Implementation notes

A subring is implemented as a subsemiring which is also an additive subgroup.
The initial PR was as a submonoid which is also an additive subgroup.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a subring's underlying set.

## Tags
subring, subrings
-/

assert_not_exists OrderedRing

universe u v w

variable {R : Type u} {S : Type v} {T : Type w} [Ring R]

section SubringClass

/-- `SubringClass S R` states that `S` is a type of subsets `s ⊆ R` that
are both a multiplicative submonoid and an additive subgroup. -/
class SubringClass (S : Type*) (R : Type u) [Ring R] [SetLike S R] extends
  SubsemiringClass S R, NegMemClass S R : Prop

-- See note [lower instance priority]
instance (priority := 100) SubringClass.addSubgroupClass (S : Type*) (R : Type u)
    [SetLike S R] [Ring R] [h : SubringClass S R] : AddSubgroupClass S R :=
  { h with }

variable [SetLike S R] [hSR : SubringClass S R] (s : S)

@[aesop safe apply (rule_sets := [SetLike])]
theorem intCast_mem (n : ℤ) : (n : R) ∈ s := by simp only [← zsmul_one, zsmul_mem, one_mem]

@[deprecated _root_.intCast_mem (since := "2024-04-05")] alias coe_int_mem := intCast_mem

namespace SubringClass

instance (priority := 75) toHasIntCast : IntCast s :=
  ⟨fun n => ⟨n, intCast_mem s n⟩⟩

-- Prefer subclasses of `Ring` over subclasses of `SubringClass`.
/-- A subring of a ring inherits a ring structure -/
instance (priority := 75) toRing : Ring s :=
  Subtype.coe_injective.ring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

-- Prefer subclasses of `Ring` over subclasses of `SubringClass`.
/-- A subring of a `CommRing` is a `CommRing`. -/
instance (priority := 75) toCommRing {R} [CommRing R] [SetLike S R] [SubringClass S R] :
    CommRing s :=
  Subtype.coe_injective.commRing (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

-- Prefer subclasses of `Ring` over subclasses of `SubringClass`.
/-- A subring of a domain is a domain. -/
instance (priority := 75) {R} [Ring R] [IsDomain R] [SetLike S R] [SubringClass S R] : IsDomain s :=
  NoZeroDivisors.to_isDomain _

/-- The natural ring hom from a subring of ring `R` to `R`. -/
def subtype (s : S) : s →+* R :=
  { SubmonoidClass.subtype s, AddSubgroupClass.subtype s with
    toFun := (↑) }

@[simp]
theorem coeSubtype : (subtype s : s → R) = ((↑) : s → R) :=
  rfl

@[simp, norm_cast]
theorem coe_natCast (n : ℕ) : ((n : s) : R) = n :=
  map_natCast (subtype s) n

@[simp, norm_cast]
theorem coe_intCast (n : ℤ) : ((n : s) : R) = n :=
  map_intCast (subtype s) n

end SubringClass

end SubringClass

variable [Ring S] [Ring T]

/-- `Subring R` is the type of subrings of `R`. A subring of `R` is a subset `s` that is a
  multiplicative submonoid and an additive subgroup. Note in particular that it shares the
  same 0 and 1 as R. -/
structure Subring (R : Type u) [Ring R] extends Subsemiring R, AddSubgroup R

/-- Reinterpret a `Subring` as a `Subsemiring`. -/
add_decl_doc Subring.toSubsemiring

/-- Reinterpret a `Subring` as an `AddSubgroup`. -/
add_decl_doc Subring.toAddSubgroup

namespace Subring

-- Porting note: there is no `Subring.toSubmonoid` but we can't define it because there is a
-- projection `s.toSubmonoid`

instance : SetLike (Subring R) R where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

instance : SubringClass (Subring R) R where
  zero_mem s := s.zero_mem'
  add_mem {s} := s.add_mem'
  one_mem s := s.one_mem'
  mul_mem {s} := s.mul_mem'
  neg_mem {s} := s.neg_mem'

@[simp]
theorem mem_toSubsemiring {s : Subring R} {x : R} : x ∈ s.toSubsemiring ↔ x ∈ s := Iff.rfl

theorem mem_carrier {s : Subring R} {x : R} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem mem_mk {S : Subsemiring R} {x : R} (h) : x ∈ (⟨S, h⟩ : Subring R) ↔ x ∈ S := Iff.rfl

@[simp] theorem coe_set_mk (S : Subsemiring R) (h) : ((⟨S, h⟩ : Subring R) : Set R) = S := rfl

@[simp]
theorem mk_le_mk {S S' : Subsemiring R} (h₁ h₂) :
    (⟨S, h₁⟩ : Subring R) ≤ (⟨S', h₂⟩ : Subring R) ↔ S ≤ S' :=
  Iff.rfl

/-- Two subrings are equal if they have the same elements. -/
@[ext]
theorem ext {S T : Subring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy of a subring with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (S : Subring R) (s : Set R) (hs : s = ↑S) : Subring R :=
  { S.toSubsemiring.copy s hs with
    carrier := s
    neg_mem' := hs.symm ▸ S.neg_mem' }

@[simp]
theorem coe_copy (S : Subring R) (s : Set R) (hs : s = ↑S) : (S.copy s hs : Set R) = s :=
  rfl

theorem copy_eq (S : Subring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

theorem toSubsemiring_injective : Function.Injective (toSubsemiring : Subring R → Subsemiring R)
  | _, _, h => ext (SetLike.ext_iff.mp h : _)

@[mono]
theorem toSubsemiring_strictMono : StrictMono (toSubsemiring : Subring R → Subsemiring R) :=
  fun _ _ => id

@[mono]
theorem toSubsemiring_mono : Monotone (toSubsemiring : Subring R → Subsemiring R) :=
  toSubsemiring_strictMono.monotone

theorem toAddSubgroup_injective : Function.Injective (toAddSubgroup : Subring R → AddSubgroup R)
  | _, _, h => ext (SetLike.ext_iff.mp h : _)

@[mono]
theorem toAddSubgroup_strictMono : StrictMono (toAddSubgroup : Subring R → AddSubgroup R) :=
  fun _ _ => id

@[mono]
theorem toAddSubgroup_mono : Monotone (toAddSubgroup : Subring R → AddSubgroup R) :=
  toAddSubgroup_strictMono.monotone

theorem toSubmonoid_injective : Function.Injective (fun s : Subring R => s.toSubmonoid)
  | _, _, h => ext (SetLike.ext_iff.mp h : _)

@[mono]
theorem toSubmonoid_strictMono : StrictMono (fun s : Subring R => s.toSubmonoid) := fun _ _ => id

@[mono]
theorem toSubmonoid_mono : Monotone (fun s : Subring R => s.toSubmonoid) :=
  toSubmonoid_strictMono.monotone

/-- Construct a `Subring R` from a set `s`, a submonoid `sm`, and an additive
subgroup `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`. -/
protected def mk' (s : Set R) (sm : Submonoid R) (sa : AddSubgroup R) (hm : ↑sm = s)
    (ha : ↑sa = s) : Subring R :=
  { sm.copy s hm.symm, sa.copy s ha.symm with }

@[simp]
theorem coe_mk' {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R} (ha : ↑sa = s) :
    (Subring.mk' s sm sa hm ha : Set R) = s :=
  rfl

@[simp]
theorem mem_mk' {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R} (ha : ↑sa = s)
    {x : R} : x ∈ Subring.mk' s sm sa hm ha ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem mk'_toSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R}
    (ha : ↑sa = s) : (Subring.mk' s sm sa hm ha).toSubmonoid = sm :=
  SetLike.coe_injective hm.symm

@[simp]
theorem mk'_toAddSubgroup {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R}
    (ha : ↑sa = s) : (Subring.mk' s sm sa hm ha).toAddSubgroup = sa :=
  SetLike.coe_injective ha.symm

end Subring

/-- A `Subsemiring` containing -1 is a `Subring`. -/
def Subsemiring.toSubring (s : Subsemiring R) (hneg : (-1 : R) ∈ s) : Subring R where
  toSubsemiring := s
  neg_mem' h := by
    rw [← neg_one_mul]
    exact mul_mem hneg h

namespace Subring

variable (s : Subring R)

/-- A subring contains the ring's 1. -/
protected theorem one_mem : (1 : R) ∈ s :=
  one_mem _

/-- A subring contains the ring's 0. -/
protected theorem zero_mem : (0 : R) ∈ s :=
  zero_mem _

/-- A subring is closed under multiplication. -/
protected theorem mul_mem {x y : R} : x ∈ s → y ∈ s → x * y ∈ s :=
  mul_mem

/-- A subring is closed under addition. -/
protected theorem add_mem {x y : R} : x ∈ s → y ∈ s → x + y ∈ s :=
  add_mem

/-- A subring is closed under negation. -/
protected theorem neg_mem {x : R} : x ∈ s → -x ∈ s :=
  neg_mem

/-- A subring is closed under subtraction -/
protected theorem sub_mem {x y : R} (hx : x ∈ s) (hy : y ∈ s) : x - y ∈ s :=
  sub_mem hx hy

/-- Product of a list of elements in a subring is in the subring. -/
protected theorem list_prod_mem {l : List R} : (∀ x ∈ l, x ∈ s) → l.prod ∈ s :=
  list_prod_mem

/-- Sum of a list of elements in a subring is in the subring. -/
protected theorem list_sum_mem {l : List R} : (∀ x ∈ l, x ∈ s) → l.sum ∈ s :=
  list_sum_mem

/-- Product of a multiset of elements in a subring of a `CommRing` is in the subring. -/
protected theorem multiset_prod_mem {R} [CommRing R] (s : Subring R) (m : Multiset R) :
    (∀ a ∈ m, a ∈ s) → m.prod ∈ s :=
  multiset_prod_mem _

/-- Sum of a multiset of elements in a `Subring` of a `Ring` is
in the `Subring`. -/
protected theorem multiset_sum_mem {R} [Ring R] (s : Subring R) (m : Multiset R) :
    (∀ a ∈ m, a ∈ s) → m.sum ∈ s :=
  multiset_sum_mem _

/-- Product of elements of a subring of a `CommRing` indexed by a `Finset` is in the
    subring. -/
protected theorem prod_mem {R : Type*} [CommRing R] (s : Subring R) {ι : Type*} {t : Finset ι}
    {f : ι → R} (h : ∀ c ∈ t, f c ∈ s) : (∏ i ∈ t, f i) ∈ s :=
  prod_mem h

/-- Sum of elements in a `Subring` of a `Ring` indexed by a `Finset`
is in the `Subring`. -/
protected theorem sum_mem {R : Type*} [Ring R] (s : Subring R) {ι : Type*} {t : Finset ι}
    {f : ι → R} (h : ∀ c ∈ t, f c ∈ s) : (∑ i ∈ t, f i) ∈ s :=
  sum_mem h

/-- A subring of a ring inherits a ring structure -/
instance toRing : Ring s := SubringClass.toRing s

protected theorem zsmul_mem {x : R} (hx : x ∈ s) (n : ℤ) : n • x ∈ s :=
  zsmul_mem hx n

protected theorem pow_mem {x : R} (hx : x ∈ s) (n : ℕ) : x ^ n ∈ s :=
  pow_mem hx n

@[simp, norm_cast]
theorem coe_add (x y : s) : (↑(x + y) : R) = ↑x + ↑y :=
  rfl

@[simp, norm_cast]
theorem coe_neg (x : s) : (↑(-x) : R) = -↑x :=
  rfl

@[simp, norm_cast]
theorem coe_mul (x y : s) : (↑(x * y) : R) = ↑x * ↑y :=
  rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : s) : R) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_one : ((1 : s) : R) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_pow (x : s) (n : ℕ) : ↑(x ^ n) = (x : R) ^ n :=
  SubmonoidClass.coe_pow x n

-- TODO: can be generalized to `AddSubmonoidClass`
-- @[simp] -- Porting note (#10618): simp can prove this
theorem coe_eq_zero_iff {x : s} : (x : R) = 0 ↔ x = 0 :=
  ⟨fun h => Subtype.ext (Trans.trans h s.coe_zero.symm), fun h => h.symm ▸ s.coe_zero⟩

/-- A subring of a `CommRing` is a `CommRing`. -/
instance toCommRing {R} [CommRing R] (s : Subring R) : CommRing s :=
  SubringClass.toCommRing s

/-- A subring of a non-trivial ring is non-trivial. -/
instance {R} [Ring R] [Nontrivial R] (s : Subring R) : Nontrivial s :=
  s.toSubsemiring.nontrivial

/-- A subring of a ring with no zero divisors has no zero divisors. -/
instance {R} [Ring R] [NoZeroDivisors R] (s : Subring R) : NoZeroDivisors s :=
  s.toSubsemiring.noZeroDivisors

/-- A subring of a domain is a domain. -/
instance {R} [Ring R] [IsDomain R] (s : Subring R) : IsDomain s :=
  NoZeroDivisors.to_isDomain _

/-- The natural ring hom from a subring of ring `R` to `R`. -/
def subtype (s : Subring R) : s →+* R :=
  { s.toSubmonoid.subtype, s.toAddSubgroup.subtype with toFun := (↑) }

@[simp]
theorem coeSubtype : ⇑s.subtype = ((↑) : s → R) :=
  rfl

@[norm_cast] -- Porting note (#10618): simp can prove this (removed `@[simp]`)
theorem coe_natCast : ∀ n : ℕ, ((n : s) : R) = n :=
  map_natCast s.subtype

@[norm_cast] -- Porting note (#10618): simp can prove this (removed `@[simp]`)
theorem coe_intCast : ∀ n : ℤ, ((n : s) : R) = n :=
  map_intCast s.subtype

/-! ## Partial order -/

@[simp]
theorem coe_toSubsemiring (s : Subring R) : (s.toSubsemiring : Set R) = s :=
  rfl

@[simp, nolint simpNF] -- Porting note (#10675): dsimp can not prove this
theorem mem_toSubmonoid {s : Subring R} {x : R} : x ∈ s.toSubmonoid ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem coe_toSubmonoid (s : Subring R) : (s.toSubmonoid : Set R) = s :=
  rfl

@[simp, nolint simpNF] -- Porting note (#10675): dsimp can not prove this
theorem mem_toAddSubgroup {s : Subring R} {x : R} : x ∈ s.toAddSubgroup ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem coe_toAddSubgroup (s : Subring R) : (s.toAddSubgroup : Set R) = s :=
  rfl

/-! ## top -/


/-- The subring `R` of the ring `R`. -/
instance : Top (Subring R) :=
  ⟨{ (⊤ : Submonoid R), (⊤ : AddSubgroup R) with }⟩

@[simp]
theorem mem_top (x : R) : x ∈ (⊤ : Subring R) :=
  Set.mem_univ x

@[simp]
theorem coe_top : ((⊤ : Subring R) : Set R) = Set.univ :=
  rfl

/-- The ring equiv between the top element of `Subring R` and `R`. -/
@[simps!]
def topEquiv : (⊤ : Subring R) ≃+* R :=
  Subsemiring.topEquiv

theorem card_top (R) [Ring R] [Fintype R] : Fintype.card (⊤ : Subring R) = Fintype.card R :=
  Fintype.card_congr topEquiv.toEquiv

/-! ## comap -/


/-- The preimage of a subring along a ring homomorphism is a subring. -/
def comap {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) (s : Subring S) : Subring R :=
  { s.toSubmonoid.comap (f : R →* S), s.toAddSubgroup.comap (f : R →+ S) with
    carrier := f ⁻¹' s.carrier }

@[simp]
theorem coe_comap (s : Subring S) (f : R →+* S) : (s.comap f : Set R) = f ⁻¹' s :=
  rfl

@[simp]
theorem mem_comap {s : Subring S} {f : R →+* S} {x : R} : x ∈ s.comap f ↔ f x ∈ s :=
  Iff.rfl

theorem comap_comap (s : Subring T) (g : S →+* T) (f : R →+* S) :
    (s.comap g).comap f = s.comap (g.comp f) :=
  rfl

/-! ## map -/


/-- The image of a subring along a ring homomorphism is a subring. -/
def map {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) (s : Subring R) : Subring S :=
  { s.toSubmonoid.map (f : R →* S), s.toAddSubgroup.map (f : R →+ S) with
    carrier := f '' s.carrier }

@[simp]
theorem coe_map (f : R →+* S) (s : Subring R) : (s.map f : Set S) = f '' s :=
  rfl

@[simp]
theorem mem_map {f : R →+* S} {s : Subring R} {y : S} : y ∈ s.map f ↔ ∃ x ∈ s, f x = y := Iff.rfl

@[simp]
theorem map_id : s.map (RingHom.id R) = s :=
  SetLike.coe_injective <| Set.image_id _

theorem map_map (g : S →+* T) (f : R →+* S) : (s.map f).map g = s.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _

theorem map_le_iff_le_comap {f : R →+* S} {s : Subring R} {t : Subring S} :
    s.map f ≤ t ↔ s ≤ t.comap f :=
  Set.image_subset_iff

theorem gc_map_comap (f : R →+* S) : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap

/-- A subring is isomorphic to its image under an injective function -/
noncomputable def equivMapOfInjective (f : R →+* S) (hf : Function.Injective f) : s ≃+* s.map f :=
  { Equiv.Set.image f s hf with
    map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _)
    map_add' := fun _ _ => Subtype.ext (f.map_add _ _) }

@[simp]
theorem coe_equivMapOfInjective_apply (f : R →+* S) (hf : Function.Injective f) (x : s) :
    (equivMapOfInjective s f hf x : S) = f x :=
  rfl

end Subring

namespace RingHom

variable (g : S →+* T) (f : R →+* S)

/-! ## range -/


/-- The range of a ring homomorphism, as a subring of the target. See Note [range copy pattern]. -/
def range {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) : Subring S :=
  ((⊤ : Subring R).map f).copy (Set.range f) Set.image_univ.symm

@[simp]
theorem coe_range : (f.range : Set S) = Set.range f :=
  rfl

@[simp]
theorem mem_range {f : R →+* S} {y : S} : y ∈ f.range ↔ ∃ x, f x = y :=
  Iff.rfl

theorem range_eq_map (f : R →+* S) : f.range = Subring.map f ⊤ := by
  ext
  simp

theorem mem_range_self (f : R →+* S) (x : R) : f x ∈ f.range :=
  mem_range.mpr ⟨x, rfl⟩

theorem map_range : f.range.map g = (g.comp f).range := by
  simpa only [range_eq_map] using (⊤ : Subring R).map_map g f

/-- The range of a ring homomorphism is a fintype, if the domain is a fintype.
Note: this instance can form a diamond with `Subtype.fintype` in the
  presence of `Fintype S`. -/
instance fintypeRange [Fintype R] [DecidableEq S] (f : R →+* S) : Fintype (range f) :=
  Set.fintypeRange f

end RingHom

namespace Subring

/-! ## bot -/


instance : Bot (Subring R) :=
  ⟨(Int.castRingHom R).range⟩

instance : Inhabited (Subring R) :=
  ⟨⊥⟩

theorem coe_bot : ((⊥ : Subring R) : Set R) = Set.range ((↑) : ℤ → R) :=
  RingHom.coe_range (Int.castRingHom R)

theorem mem_bot {x : R} : x ∈ (⊥ : Subring R) ↔ ∃ n : ℤ, ↑n = x :=
  RingHom.mem_range

/-! ## inf -/


/-- The inf of two subrings is their intersection. -/
instance : Inf (Subring R) :=
  ⟨fun s t =>
    { s.toSubmonoid ⊓ t.toSubmonoid, s.toAddSubgroup ⊓ t.toAddSubgroup with carrier := s ∩ t }⟩

@[simp]
theorem coe_inf (p p' : Subring R) : ((p ⊓ p' : Subring R) : Set R) = (p : Set R) ∩ p' :=
  rfl

@[simp]
theorem mem_inf {p p' : Subring R} {x : R} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl

instance : InfSet (Subring R) :=
  ⟨fun s =>
    Subring.mk' (⋂ t ∈ s, ↑t) (⨅ t ∈ s, t.toSubmonoid) (⨅ t ∈ s, Subring.toAddSubgroup t)
      (by simp) (by simp)⟩

@[simp, norm_cast]
theorem coe_sInf (S : Set (Subring R)) : ((sInf S : Subring R) : Set R) = ⋂ s ∈ S, ↑s :=
  rfl

theorem mem_sInf {S : Set (Subring R)} {x : R} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂

@[simp, norm_cast]
theorem coe_iInf {ι : Sort*} {S : ι → Subring R} : (↑(⨅ i, S i) : Set R) = ⋂ i, S i := by
  simp only [iInf, coe_sInf, Set.biInter_range]

theorem mem_iInf {ι : Sort*} {S : ι → Subring R} {x : R} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp]
theorem sInf_toSubmonoid (s : Set (Subring R)) :
    (sInf s).toSubmonoid = ⨅ t ∈ s, t.toSubmonoid :=
  mk'_toSubmonoid _ _

@[simp]
theorem sInf_toAddSubgroup (s : Set (Subring R)) :
    (sInf s).toAddSubgroup = ⨅ t ∈ s, Subring.toAddSubgroup t :=
  mk'_toAddSubgroup _ _

/-- Subrings of a ring form a complete lattice. -/
instance : CompleteLattice (Subring R) :=
  { completeLatticeOfInf (Subring R) fun _ =>
      IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf with
    bot := ⊥
    bot_le := fun s _x hx =>
      let ⟨n, hn⟩ := mem_bot.1 hx
      hn ▸ intCast_mem s n
    top := ⊤
    le_top := fun _s _x _hx => trivial
    inf := (· ⊓ ·)
    inf_le_left := fun _s _t _x => And.left
    inf_le_right := fun _s _t _x => And.right
    le_inf := fun _s _t₁ _t₂ h₁ h₂ _x hx => ⟨h₁ hx, h₂ hx⟩ }

theorem eq_top_iff' (A : Subring R) : A = ⊤ ↔ ∀ x : R, x ∈ A :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩

/-! ## Center of a ring -/


section

variable (R)

/-- The center of a ring `R` is the set of elements that commute with everything in `R` -/
def center : Subring R :=
  { Subsemiring.center R with
    carrier := Set.center R
    neg_mem' := Set.neg_mem_center }

theorem coe_center : ↑(center R) = Set.center R :=
  rfl

@[simp]
theorem center_toSubsemiring : (center R).toSubsemiring = Subsemiring.center R :=
  rfl

variable {R}

theorem mem_center_iff {z : R} : z ∈ center R ↔ ∀ g, g * z = z * g :=
  Subsemigroup.mem_center_iff

instance decidableMemCenter [DecidableEq R] [Fintype R] : DecidablePred (· ∈ center R) := fun _ =>
  decidable_of_iff' _ mem_center_iff

@[simp]
theorem center_eq_top (R) [CommRing R] : center R = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ R)

/-- The center is commutative. -/
instance : CommRing (center R) :=
  { inferInstanceAs (CommSemiring (Subsemiring.center R)), (center R).toRing with }

end

section DivisionRing

variable {K : Type u} [DivisionRing K]

instance instField : Field (center K) where
  inv a := ⟨a⁻¹, Set.inv_mem_center a.prop⟩
  mul_inv_cancel a ha := Subtype.ext <| mul_inv_cancel <| Subtype.coe_injective.ne ha
  div a b := ⟨a / b, Set.div_mem_center a.prop b.prop⟩
  div_eq_mul_inv a b := Subtype.ext <| div_eq_mul_inv _ _
  inv_zero := Subtype.ext inv_zero
  -- TODO: use a nicer defeq
  nnqsmul := _
  qsmul := _

@[simp]
theorem center.coe_inv (a : center K) : ((a⁻¹ : center K) : K) = (a : K)⁻¹ :=
  rfl

@[simp]
theorem center.coe_div (a b : center K) : ((a / b : center K) : K) = (a : K) / (b : K) :=
  rfl

end DivisionRing

section Centralizer

/-- The centralizer of a set inside a ring as a `Subring`. -/
def centralizer (s : Set R) : Subring R :=
  { Subsemiring.centralizer s with neg_mem' := Set.neg_mem_centralizer }

@[simp, norm_cast]
theorem coe_centralizer (s : Set R) : (centralizer s : Set R) = s.centralizer :=
  rfl

theorem centralizer_toSubmonoid (s : Set R) :
    (centralizer s).toSubmonoid = Submonoid.centralizer s :=
  rfl

theorem centralizer_toSubsemiring (s : Set R) :
    (centralizer s).toSubsemiring = Subsemiring.centralizer s :=
  rfl

theorem mem_centralizer_iff {s : Set R} {z : R} : z ∈ centralizer s ↔ ∀ g ∈ s, g * z = z * g :=
  Iff.rfl

theorem center_le_centralizer (s) : center R ≤ centralizer s :=
  s.center_subset_centralizer

theorem centralizer_le (s t : Set R) (h : s ⊆ t) : centralizer t ≤ centralizer s :=
  Set.centralizer_subset h

@[simp]
theorem centralizer_eq_top_iff_subset {s : Set R} : centralizer s = ⊤ ↔ s ⊆ center R :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[simp]
theorem centralizer_univ : centralizer Set.univ = center R :=
  SetLike.ext' (Set.centralizer_univ R)

end Centralizer

/-! ## subring closure of a subset -/


/-- The `Subring` generated by a set. -/
def closure (s : Set R) : Subring R :=
  sInf { S | s ⊆ S }

theorem mem_closure {x : R} {s : Set R} : x ∈ closure s ↔ ∀ S : Subring R, s ⊆ S → x ∈ S :=
  mem_sInf

/-- The subring generated by a set includes the set. -/
@[simp, aesop safe 20 apply (rule_sets := [SetLike])]
theorem subset_closure {s : Set R} : s ⊆ closure s := fun _ hx => mem_closure.2 fun _ hS => hS hx

theorem not_mem_of_not_mem_closure {s : Set R} {P : R} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)

/-- A subring `t` includes `closure s` if and only if it includes `s`. -/
@[simp]
theorem closure_le {s : Set R} {t : Subring R} : closure s ≤ t ↔ s ⊆ t :=
  ⟨Set.Subset.trans subset_closure, fun h => sInf_le h⟩

/-- Subring closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
theorem closure_mono ⦃s t : Set R⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Set.Subset.trans h subset_closure

theorem closure_eq_of_le {s : Set R} {t : Subring R} (h₁ : s ⊆ t) (h₂ : t ≤ closure s) :
    closure s = t :=
  le_antisymm (closure_le.2 h₁) h₂

/-- An induction principle for closure membership. If `p` holds for `0`, `1`, and all elements
of `s`, and is preserved under addition, negation, and multiplication, then `p` holds for all
elements of the closure of `s`. -/
@[elab_as_elim]
theorem closure_induction {s : Set R} {p : R → Prop} {x} (h : x ∈ closure s) (Hs : ∀ x ∈ s, p x)
    (zero : p 0) (one : p 1) (add : ∀ x y, p x → p y → p (x + y)) (neg : ∀ x : R, p x → p (-x))
    (mul : ∀ x y, p x → p y → p (x * y)) : p x :=
  (@closure_le _ _ _ ⟨⟨⟨⟨p, @mul⟩, one⟩, @add, zero⟩, @neg⟩).2 Hs h

@[elab_as_elim]
theorem closure_induction' {s : Set R} {p : ∀ x, x ∈ closure s → Prop}
    (mem : ∀ (x) (h : x ∈ s), p x (subset_closure h))
    (zero : p 0 (zero_mem _)) (one : p 1 (one_mem _))
    (add : ∀ x hx y hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (neg : ∀ x hx, p x hx → p (-x) (neg_mem hx))
    (mul : ∀ x hx y hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    {a : R} (ha : a ∈ closure s) : p a ha := by
  refine Exists.elim ?_ fun (ha : a ∈ closure s) (hc : p a ha) => hc
  refine
    closure_induction ha (fun m hm => ⟨subset_closure hm, mem m hm⟩) ⟨zero_mem _, zero⟩
      ⟨one_mem _, one⟩ ?_ (fun x hx => hx.elim fun hx' hx => ⟨neg_mem hx', neg _ _ hx⟩) ?_
  · exact (fun x y hx hy => hx.elim fun hx' hx => hy.elim fun hy' hy =>
      ⟨add_mem hx' hy', add _ _ _ _ hx hy⟩)
  · exact (fun x y hx hy => hx.elim fun hx' hx => hy.elim fun hy' hy =>
      ⟨mul_mem hx' hy', mul _ _ _ _ hx hy⟩)

/-- An induction principle for closure membership, for predicates with two arguments. -/
@[elab_as_elim]
theorem closure_induction₂ {s : Set R} {p : R → R → Prop} {a b : R} (ha : a ∈ closure s)
    (hb : b ∈ closure s) (Hs : ∀ x ∈ s, ∀ y ∈ s, p x y) (H0_left : ∀ x, p 0 x)
    (H0_right : ∀ x, p x 0) (H1_left : ∀ x, p 1 x) (H1_right : ∀ x, p x 1)
    (Hneg_left : ∀ x y, p x y → p (-x) y) (Hneg_right : ∀ x y, p x y → p x (-y))
    (Hadd_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ + x₂) y)
    (Hadd_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ + y₂))
    (Hmul_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ * x₂) y)
    (Hmul_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ * y₂)) : p a b := by
  refine
    closure_induction hb ?_ (H0_right _) (H1_right _) (Hadd_right a) (Hneg_right a) (Hmul_right a)
  refine closure_induction ha Hs (fun x _ => H0_left x) (fun x _ => H1_left x) ?_ ?_ ?_
  · exact fun x y H₁ H₂ z zs => Hadd_left x y z (H₁ z zs) (H₂ z zs)
  · exact fun x hx z zs => Hneg_left x z (hx z zs)
  · exact fun x y H₁ H₂ z zs => Hmul_left x y z (H₁ z zs) (H₂ z zs)

theorem mem_closure_iff {s : Set R} {x} :
    x ∈ closure s ↔ x ∈ AddSubgroup.closure (Submonoid.closure s : Set R) :=
  ⟨fun h =>
    closure_induction h (fun x hx => AddSubgroup.subset_closure <| Submonoid.subset_closure hx)
      (AddSubgroup.zero_mem _)
      (AddSubgroup.subset_closure (Submonoid.one_mem (Submonoid.closure s)))
      (fun x y hx hy => AddSubgroup.add_mem _ hx hy) (fun x hx => AddSubgroup.neg_mem _ hx)
      fun x y hx hy =>
      AddSubgroup.closure_induction hy
        (fun q hq =>
          AddSubgroup.closure_induction hx
            (fun p hp => AddSubgroup.subset_closure ((Submonoid.closure s).mul_mem hp hq))
            (by rw [zero_mul q]; apply AddSubgroup.zero_mem _)
            (fun p₁ p₂ ihp₁ ihp₂ => by rw [add_mul p₁ p₂ q]; apply AddSubgroup.add_mem _ ihp₁ ihp₂)
            fun x hx => by
            have f : -x * q = -(x * q) := by simp
            rw [f]; apply AddSubgroup.neg_mem _ hx)
        (by rw [mul_zero x]; apply AddSubgroup.zero_mem _)
        (fun q₁ q₂ ihq₁ ihq₂ => by rw [mul_add x q₁ q₂]; apply AddSubgroup.add_mem _ ihq₁ ihq₂)
        fun z hz => by
        have f : x * -z = -(x * z) := by simp
        rw [f]; apply AddSubgroup.neg_mem _ hz,
    fun h =>
    AddSubgroup.closure_induction (p := (· ∈ closure s)) h
      (fun x hx =>
        Submonoid.closure_induction hx (fun x hx => subset_closure hx) (one_mem _) fun x y hx hy =>
          mul_mem hx hy)
      (zero_mem _) (fun x y hx hy => add_mem hx hy) fun x hx => neg_mem hx⟩

/-- If all elements of `s : Set A` commute pairwise, then `closure s` is a commutative ring.  -/
def closureCommRingOfComm {s : Set R} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    CommRing (closure s) :=
  { (closure s).toRing with
    mul_comm := fun x y => by
      ext
      simp only [Subring.coe_mul]
      refine
        closure_induction₂ x.prop y.prop hcomm (fun x => by simp only [mul_zero, zero_mul])
          (fun x => by simp only [mul_zero, zero_mul]) (fun x => by simp only [mul_one, one_mul])
          (fun x => by simp only [mul_one, one_mul])
          (fun x y hxy => by simp only [mul_neg, neg_mul, hxy])
          (fun x y hxy => by simp only [mul_neg, neg_mul, hxy])
          (fun x₁ x₂ y h₁ h₂ => by simp only [add_mul, mul_add, h₁, h₂])
          (fun x₁ x₂ y h₁ h₂ => by simp only [add_mul, mul_add, h₁, h₂])
          (fun x₁ x₂ y h₁ h₂ => by rw [← mul_assoc, ← h₁, mul_assoc x₁ y x₂, ← h₂, mul_assoc])
          fun x₁ x₂ y h₁ h₂ => by rw [← mul_assoc, h₁, mul_assoc, h₂, ← mul_assoc] }

theorem exists_list_of_mem_closure {s : Set R} {x : R} (h : x ∈ closure s) :
    ∃ L : List (List R), (∀ t ∈ L, ∀ y ∈ t, y ∈ s ∨ y = (-1 : R)) ∧ (L.map List.prod).sum = x :=
  AddSubgroup.closure_induction (G := R)
    (p := (∃ L : List (List R), (∀ t ∈ L, ∀ y ∈ t, y ∈ s ∨ y = -1) ∧ (L.map List.prod).sum = ·))
    (mem_closure_iff.1 h)
    (fun x hx =>
      let ⟨l, hl, h⟩ := Submonoid.exists_list_of_mem_closure hx
      ⟨[l], by simp [h]; clear_aux_decl; tauto⟩)
    ⟨[], by simp⟩
    (fun x y ⟨l, hl1, hl2⟩ ⟨m, hm1, hm2⟩ =>
      ⟨l ++ m, fun t ht => (List.mem_append.1 ht).elim (hl1 t) (hm1 t), by simp [hl2, hm2]⟩)
    fun x ⟨L, hL⟩ =>
    ⟨L.map (List.cons (-1)),
      List.forall_mem_map_iff.2 fun j hj => List.forall_mem_cons.2 ⟨Or.inr rfl, hL.1 j hj⟩,
      hL.2 ▸
        List.recOn L (by simp)
          (by simp (config := { contextual := true }) [List.map_cons, add_comm])⟩

variable (R)

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : GaloisInsertion (@closure R _) (↑) where
  choice s _ := closure s
  gc _s _t := closure_le
  le_l_u _s := subset_closure
  choice_eq _s _h := rfl

variable {R}

/-- Closure of a subring `S` equals `S`. -/
theorem closure_eq (s : Subring R) : closure (s : Set R) = s :=
  (Subring.gi R).l_u_eq s

@[simp]
theorem closure_empty : closure (∅ : Set R) = ⊥ :=
  (Subring.gi R).gc.l_bot

@[simp]
theorem closure_univ : closure (Set.univ : Set R) = ⊤ :=
  @coe_top R _ ▸ closure_eq ⊤

theorem closure_union (s t : Set R) : closure (s ∪ t) = closure s ⊔ closure t :=
  (Subring.gi R).gc.l_sup

theorem closure_iUnion {ι} (s : ι → Set R) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Subring.gi R).gc.l_iSup

theorem closure_sUnion (s : Set (Set R)) : closure (⋃₀ s) = ⨆ t ∈ s, closure t :=
  (Subring.gi R).gc.l_sSup

theorem map_sup (s t : Subring R) (f : R →+* S) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
  (gc_map_comap f).l_sup

theorem map_iSup {ι : Sort*} (f : R →+* S) (s : ι → Subring R) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup

theorem comap_inf (s t : Subring S) (f : R →+* S) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
  (gc_map_comap f).u_inf

theorem comap_iInf {ι : Sort*} (f : R →+* S) (s : ι → Subring S) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[simp]
theorem map_bot (f : R →+* S) : (⊥ : Subring R).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
theorem comap_top (f : R →+* S) : (⊤ : Subring S).comap f = ⊤ :=
  (gc_map_comap f).u_top

/-- Given `Subring`s `s`, `t` of rings `R`, `S` respectively, `s.prod t` is `s ×̂ t`
as a subring of `R × S`. -/
def prod (s : Subring R) (t : Subring S) : Subring (R × S) :=
  { s.toSubmonoid.prod t.toSubmonoid, s.toAddSubgroup.prod t.toAddSubgroup with carrier := s ×ˢ t }

@[norm_cast]
theorem coe_prod (s : Subring R) (t : Subring S) :
    (s.prod t : Set (R × S)) = (s : Set R) ×ˢ (t : Set S) :=
  rfl

theorem mem_prod {s : Subring R} {t : Subring S} {p : R × S} : p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl

@[mono]
theorem prod_mono ⦃s₁ s₂ : Subring R⦄ (hs : s₁ ≤ s₂) ⦃t₁ t₂ : Subring S⦄ (ht : t₁ ≤ t₂) :
    s₁.prod t₁ ≤ s₂.prod t₂ :=
  Set.prod_mono hs ht

theorem prod_mono_right (s : Subring R) : Monotone fun t : Subring S => s.prod t :=
  prod_mono (le_refl s)

theorem prod_mono_left (t : Subring S) : Monotone fun s : Subring R => s.prod t := fun _ _ hs =>
  prod_mono hs (le_refl t)

theorem prod_top (s : Subring R) : s.prod (⊤ : Subring S) = s.comap (RingHom.fst R S) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_fst]

theorem top_prod (s : Subring S) : (⊤ : Subring R).prod s = s.comap (RingHom.snd R S) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_snd]

@[simp]
theorem top_prod_top : (⊤ : Subring R).prod (⊤ : Subring S) = ⊤ :=
  (top_prod _).trans <| comap_top _

/-- Product of subrings is isomorphic to their product as rings. -/
def prodEquiv (s : Subring R) (t : Subring S) : s.prod t ≃+* s × t :=
  { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _x _y => rfl
    map_add' := fun _x _y => rfl }

/-- The underlying set of a non-empty directed sSup of subrings is just a union of the subrings.
  Note that this fails without the directedness assumption (the union of two subrings is
  typically not a subring) -/
theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subring R} (hS : Directed (· ≤ ·) S)
    {x : R} : (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  refine ⟨?_, fun ⟨i, hi⟩ ↦ le_iSup S i hi⟩
  let U : Subring R :=
    Subring.mk' (⋃ i, (S i : Set R)) (⨆ i, (S i).toSubmonoid) (⨆ i, (S i).toAddSubgroup)
      (Submonoid.coe_iSup_of_directed hS) (AddSubgroup.coe_iSup_of_directed hS)
  suffices ⨆ i, S i ≤ U by simpa [U] using @this x
  exact iSup_le fun i x hx ↦ Set.mem_iUnion.2 ⟨i, hx⟩

theorem coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subring R} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Subring R) : Set R) = ⋃ i, S i :=
  Set.ext fun x ↦ by simp [mem_iSup_of_directed hS]

theorem mem_sSup_of_directedOn {S : Set (Subring R)} (Sne : S.Nonempty) (hS : DirectedOn (· ≤ ·) S)
    {x : R} : x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  haveI : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, SetCoe.exists, Subtype.coe_mk,
    exists_prop]

theorem coe_sSup_of_directedOn {S : Set (Subring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(sSup S) : Set R) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]

theorem mem_map_equiv {f : R ≃+* S} {K : Subring R} {x : S} :
    x ∈ K.map (f : R →+* S) ↔ f.symm x ∈ K :=
  @Set.mem_image_equiv _ _ (K : Set R) f.toEquiv x

theorem map_equiv_eq_comap_symm (f : R ≃+* S) (K : Subring R) :
    K.map (f : R →+* S) = K.comap f.symm :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage K)

theorem comap_equiv_eq_map_symm (f : R ≃+* S) (K : Subring S) :
    K.comap (f : R →+* S) = K.map f.symm :=
  (map_equiv_eq_comap_symm f.symm K).symm

end Subring

namespace RingHom

variable {s : Subring R}

open Subring

/-- Restriction of a ring homomorphism to its range interpreted as a subsemiring.

This is the bundled version of `Set.rangeFactorization`. -/
def rangeRestrict (f : R →+* S) : R →+* f.range :=
  f.codRestrict f.range fun x => ⟨x, rfl⟩

@[simp]
theorem coe_rangeRestrict (f : R →+* S) (x : R) : (f.rangeRestrict x : S) = f x :=
  rfl

theorem rangeRestrict_surjective (f : R →+* S) : Function.Surjective f.rangeRestrict :=
  fun ⟨_y, hy⟩ =>
  let ⟨x, hx⟩ := mem_range.mp hy
  ⟨x, Subtype.ext hx⟩

theorem range_top_iff_surjective {f : R →+* S} :
    f.range = (⊤ : Subring S) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_range, coe_top]) Set.range_iff_surjective

/-- The range of a surjective ring homomorphism is the whole of the codomain. -/
@[simp]
theorem range_top_of_surjective (f : R →+* S) (hf : Function.Surjective f) :
    f.range = (⊤ : Subring S) :=
  range_top_iff_surjective.2 hf

section eqLocus

variable {S : Type v} [Semiring S]

/-- The subring of elements `x : R` such that `f x = g x`, i.e.,
  the equalizer of f and g as a subring of R -/
def eqLocus (f g : R →+* S) : Subring R :=
  { (f : R →* S).eqLocusM g, (f : R →+ S).eqLocus g with carrier := { x | f x = g x } }

@[simp]
theorem eqLocus_same (f : R →+* S) : f.eqLocus f = ⊤ :=
  SetLike.ext fun _ => eq_self_iff_true _

/-- If two ring homomorphisms are equal on a set, then they are equal on its subring closure. -/
theorem eqOn_set_closure {f g : R →+* S} {s : Set R} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocus g from closure_le.2 h

theorem eq_of_eqOn_set_top {f g : R →+* S} (h : Set.EqOn f g (⊤ : Subring R)) : f = g :=
  ext fun _x => h trivial

theorem eq_of_eqOn_set_dense {s : Set R} (hs : closure s = ⊤) {f g : R →+* S} (h : s.EqOn f g) :
    f = g :=
  eq_of_eqOn_set_top <| hs ▸ eqOn_set_closure h

end eqLocus

theorem closure_preimage_le (f : R →+* S) (s : Set S) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _ hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

/-- The image under a ring homomorphism of the subring generated by a set equals
the subring generated by the image of the set. -/
theorem map_closure (f : R →+* S) (s : Set R) : (closure s).map f = closure (f '' s) :=
  le_antisymm
    (map_le_iff_le_comap.2 <|
      le_trans (closure_mono <| Set.subset_preimage_image _ _) (closure_preimage_le _ _))
    (closure_le.2 <| Set.image_subset _ subset_closure)

end RingHom

namespace Subring

open RingHom

/-- The ring homomorphism associated to an inclusion of subrings. -/
def inclusion {S T : Subring R} (h : S ≤ T) : S →+* T :=
  S.subtype.codRestrict _ fun x => h x.2

@[simp]
theorem range_subtype (s : Subring R) : s.subtype.range = s :=
  SetLike.coe_injective <| (coe_rangeS _).trans Subtype.range_coe

-- @[simp] -- Porting note (#10618): simp can prove this
theorem range_fst : (fst R S).rangeS = ⊤ :=
  (fst R S).rangeS_top_of_surjective <| Prod.fst_surjective

-- @[simp] -- Porting note (#10618): simp can prove this
theorem range_snd : (snd R S).rangeS = ⊤ :=
  (snd R S).rangeS_top_of_surjective <| Prod.snd_surjective

@[simp]
theorem prod_bot_sup_bot_prod (s : Subring R) (t : Subring S) : s.prod ⊥ ⊔ prod ⊥ t = s.prod t :=
  le_antisymm (sup_le (prod_mono_right s bot_le) (prod_mono_left t bot_le)) fun p hp =>
    Prod.fst_mul_snd p ▸
      mul_mem
        ((le_sup_left : s.prod ⊥ ≤ s.prod ⊥ ⊔ prod ⊥ t) ⟨hp.1, SetLike.mem_coe.2 <| one_mem ⊥⟩)
        ((le_sup_right : prod ⊥ t ≤ s.prod ⊥ ⊔ prod ⊥ t) ⟨SetLike.mem_coe.2 <| one_mem ⊥, hp.2⟩)

end Subring

namespace RingEquiv

variable {s t : Subring R}

/-- Makes the identity isomorphism from a proof two subrings of a multiplicative
    monoid are equal. -/
def subringCongr (h : s = t) : s ≃+* t :=
  { Equiv.setCongr <| congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

/-- Restrict a ring homomorphism with a left inverse to a ring isomorphism to its
`RingHom.range`. -/
def ofLeftInverse {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f) : R ≃+* f.range :=
  { f.rangeRestrict with
    toFun := fun x => f.rangeRestrict x
    invFun := fun x => (g ∘ f.range.subtype) x
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := RingHom.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]
theorem ofLeftInverse_apply {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f) (x : R) :
    ↑(ofLeftInverse h x) = f x :=
  rfl

@[simp]
theorem ofLeftInverse_symm_apply {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f)
    (x : f.range) : (ofLeftInverse h).symm x = g x :=
  rfl

/-- Given an equivalence `e : R ≃+* S` of rings and a subring `s` of `R`,
`subringMap e s` is the induced equivalence between `s` and `s.map e` -/
@[simps!]
def subringMap (e : R ≃+* S) : s ≃+* s.map e.toRingHom :=
  e.subsemiringMap s.toSubsemiring

-- These lemmas have always been bad (#7657), but lean4#2644 made `simp` start noticing
attribute [nolint simpNF] RingEquiv.subringMap_symm_apply_coe
  RingEquiv.subringMap_apply_coe

end RingEquiv

namespace Subring

variable {s : Set R}

-- attribute [local reducible] closure -- Porting note: not available in Lean4

@[elab_as_elim]
protected theorem InClosure.recOn {C : R → Prop} {x : R} (hx : x ∈ closure s) (h1 : C 1)
    (hneg1 : C (-1)) (hs : ∀ z ∈ s, ∀ n, C n → C (z * n)) (ha : ∀ {x y}, C x → C y → C (x + y)) :
    C x := by
  have h0 : C 0 := add_neg_self (1 : R) ▸ ha h1 hneg1
  rcases exists_list_of_mem_closure hx with ⟨L, HL, rfl⟩
  clear hx
  induction' L with hd tl ih
  · exact h0
  rw [List.forall_mem_cons] at HL
  suffices C (List.prod hd) by
    rw [List.map_cons, List.sum_cons]
    exact ha this (ih HL.2)
  replace HL := HL.1
  clear ih tl
  rsuffices ⟨L, HL', HP | HP⟩ :
    ∃ L : List R, (∀ x ∈ L, x ∈ s) ∧ (List.prod hd = List.prod L ∨ List.prod hd = -List.prod L)
  · rw [HP]
    clear HP HL hd
    induction' L with hd tl ih
    · exact h1
    rw [List.forall_mem_cons] at HL'
    rw [List.prod_cons]
    exact hs _ HL'.1 _ (ih HL'.2)
  · rw [HP]
    clear HP HL hd
    induction' L with hd tl ih
    · exact hneg1
    rw [List.prod_cons, neg_mul_eq_mul_neg]
    rw [List.forall_mem_cons] at HL'
    exact hs _ HL'.1 _ (ih HL'.2)
  induction' hd with hd tl ih
  · exact ⟨[], List.forall_mem_nil _, Or.inl rfl⟩
  rw [List.forall_mem_cons] at HL
  rcases ih HL.2 with ⟨L, HL', HP | HP⟩ <;> cases' HL.1 with hhd hhd
  · exact
      ⟨hd::L, List.forall_mem_cons.2 ⟨hhd, HL'⟩,
        Or.inl <| by rw [List.prod_cons, List.prod_cons, HP]⟩
  · exact ⟨L, HL', Or.inr <| by rw [List.prod_cons, hhd, neg_one_mul, HP]⟩
  · exact
      ⟨hd::L, List.forall_mem_cons.2 ⟨hhd, HL'⟩,
        Or.inr <| by rw [List.prod_cons, List.prod_cons, HP, neg_mul_eq_mul_neg]⟩
  · exact ⟨L, HL', Or.inl <| by rw [List.prod_cons, hhd, HP, neg_one_mul, neg_neg]⟩

theorem closure_preimage_le (f : R →+* S) (s : Set S) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _ hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

end Subring

theorem AddSubgroup.int_mul_mem {G : AddSubgroup R} (k : ℤ) {g : R} (h : g ∈ G) :
    (k : R) * g ∈ G := by
  convert AddSubgroup.zsmul_mem G h k using 1
  simp

/-! ## Actions by `Subring`s

These are just copies of the definitions about `Subsemiring` starting from
`Subsemiring.MulAction`.

When `R` is commutative, `Algebra.ofSubring` provides a stronger result than those found in
this file, which uses the same scalar action.
-/


section Actions

namespace Subring

variable {α β : Type*}


-- Porting note: Lean can find this instance already
/-- The action by a subring is the action by the underlying ring. -/
instance [SMul R α] (S : Subring R) : SMul S α :=
  inferInstanceAs (SMul S.toSubsemiring α)

theorem smul_def [SMul R α] {S : Subring R} (g : S) (m : α) : g • m = (g : R) • m :=
  rfl

-- Porting note: Lean can find this instance already
instance smulCommClass_left [SMul R β] [SMul α β] [SMulCommClass R α β] (S : Subring R) :
    SMulCommClass S α β :=
  inferInstanceAs (SMulCommClass S.toSubsemiring α β)

-- Porting note: Lean can find this instance already
instance smulCommClass_right [SMul α β] [SMul R β] [SMulCommClass α R β] (S : Subring R) :
    SMulCommClass α S β :=
  inferInstanceAs (SMulCommClass α S.toSubsemiring β)

-- Porting note: Lean can find this instance already
/-- Note that this provides `IsScalarTower S R R` which is needed by `smul_mul_assoc`. -/
instance [SMul α β] [SMul R α] [SMul R β] [IsScalarTower R α β] (S : Subring R) :
    IsScalarTower S α β :=
  inferInstanceAs (IsScalarTower S.toSubsemiring α β)

-- Porting note: Lean can find this instance already
instance [SMul R α] [FaithfulSMul R α] (S : Subring R) : FaithfulSMul S α :=
  inferInstanceAs (FaithfulSMul S.toSubsemiring α)

-- Porting note: Lean can find this instance already
/-- The action by a subring is the action by the underlying ring. -/
instance [MulAction R α] (S : Subring R) : MulAction S α :=
  inferInstanceAs (MulAction S.toSubsemiring α)

-- Porting note: Lean can find this instance already
/-- The action by a subring is the action by the underlying ring. -/
instance [AddMonoid α] [DistribMulAction R α] (S : Subring R) : DistribMulAction S α :=
  inferInstanceAs (DistribMulAction S.toSubsemiring α)

-- Porting note: Lean can find this instance already
/-- The action by a subring is the action by the underlying ring. -/
instance [Monoid α] [MulDistribMulAction R α] (S : Subring R) : MulDistribMulAction S α :=
  inferInstanceAs (MulDistribMulAction S.toSubsemiring α)

-- Porting note: Lean can find this instance already
/-- The action by a subring is the action by the underlying ring. -/
instance [Zero α] [SMulWithZero R α] (S : Subring R) : SMulWithZero S α :=
  inferInstanceAs (SMulWithZero S.toSubsemiring α)

/-- The action by a subring is the action by the underlying ring. -/
instance [Zero α] [MulActionWithZero R α] (S : Subring R) : MulActionWithZero S α :=
  -- inferInstanceAs (MulActionWithZero S.toSubsemiring α) -- Porting note: does not work
  Subsemiring.mulActionWithZero S.toSubsemiring

/-- The action by a subring is the action by the underlying ring. -/
instance [AddCommMonoid α] [Module R α] (S : Subring R) : Module S α :=
  -- inferInstanceAs (Module S.toSubsemiring α) -- Porting note: does not work
  Subsemiring.module S.toSubsemiring

-- Porting note: Lean can find this instance already
/-- The action by a subsemiring is the action by the underlying ring. -/
instance [Semiring α] [MulSemiringAction R α] (S : Subring R) : MulSemiringAction S α :=
  inferInstanceAs (MulSemiringAction S.toSubmonoid α)

/-- The center of a semiring acts commutatively on that semiring. -/
instance center.smulCommClass_left : SMulCommClass (center R) R R :=
  Subsemiring.center.smulCommClass_left

/-- The center of a semiring acts commutatively on that semiring. -/
instance center.smulCommClass_right : SMulCommClass R (center R) R :=
  Subsemiring.center.smulCommClass_right

end Subring

end Actions
