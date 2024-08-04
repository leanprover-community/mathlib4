/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Ring.Action.Subobjects
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.Set.Finite
import Mathlib.GroupTheory.Submonoid.Centralizer
import Mathlib.RingTheory.NonUnitalSubsemiring.Basic

/-!
# Bundled subsemirings

We define bundled subsemirings and some standard constructions: `CompleteLattice` structure,
`Subtype` and `inclusion` ring homomorphisms, subsemiring `map`, `comap` and range (`rangeS`) of
a `RingHom` etc.
-/


universe u v w

section AddSubmonoidWithOneClass

/-- `AddSubmonoidWithOneClass S R` says `S` is a type of subsets `s ≤ R` that contain `0`, `1`,
and are closed under `(+)` -/
class AddSubmonoidWithOneClass (S R : Type*) [AddMonoidWithOne R]
  [SetLike S R] extends AddSubmonoidClass S R, OneMemClass S R : Prop

variable {S R : Type*} [AddMonoidWithOne R] [SetLike S R] (s : S)

@[aesop safe apply (rule_sets := [SetLike])]
theorem natCast_mem [AddSubmonoidWithOneClass S R] (n : ℕ) : (n : R) ∈ s := by
  induction n <;> simp [zero_mem, add_mem, one_mem, *]

@[deprecated (since := "2024-04-05")] alias coe_nat_mem := natCast_mem

@[aesop safe apply (rule_sets := [SetLike])]
lemma ofNat_mem [AddSubmonoidWithOneClass S R] (s : S) (n : ℕ) [n.AtLeastTwo] :
    no_index (OfNat.ofNat n) ∈ s := by
  rw [← Nat.cast_eq_ofNat]; exact natCast_mem s n

instance (priority := 74) AddSubmonoidWithOneClass.toAddMonoidWithOne
    [AddSubmonoidWithOneClass S R] : AddMonoidWithOne s :=
  { AddSubmonoidClass.toAddMonoid s with
    one := ⟨_, one_mem s⟩
    natCast := fun n => ⟨n, natCast_mem s n⟩
    natCast_zero := Subtype.ext Nat.cast_zero
    natCast_succ := fun _ => Subtype.ext (Nat.cast_succ _) }

end AddSubmonoidWithOneClass

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

section SubsemiringClass

/-- `SubsemiringClass S R` states that `S` is a type of subsets `s ⊆ R` that
are both a multiplicative and an additive submonoid. -/
class SubsemiringClass (S : Type*) (R : Type u) [NonAssocSemiring R]
  [SetLike S R] extends SubmonoidClass S R, AddSubmonoidClass S R : Prop

-- See note [lower instance priority]
instance (priority := 100) SubsemiringClass.addSubmonoidWithOneClass (S : Type*)
    (R : Type u) [NonAssocSemiring R] [SetLike S R] [h : SubsemiringClass S R] :
    AddSubmonoidWithOneClass S R :=
  { h with }

variable [SetLike S R] [hSR : SubsemiringClass S R] (s : S)

namespace SubsemiringClass

-- Prefer subclasses of `NonAssocSemiring` over subclasses of `SubsemiringClass`.
/-- A subsemiring of a `NonAssocSemiring` inherits a `NonAssocSemiring` structure -/
instance (priority := 75) toNonAssocSemiring : NonAssocSemiring s :=
  Subtype.coe_injective.nonAssocSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

instance nontrivial [Nontrivial R] : Nontrivial s :=
  nontrivial_of_ne 0 1 fun H => zero_ne_one (congr_arg Subtype.val H)

instance noZeroDivisors [NoZeroDivisors R] : NoZeroDivisors s :=
  Subtype.coe_injective.noZeroDivisors _ rfl fun _ _ => rfl

/-- The natural ring hom from a subsemiring of semiring `R` to `R`. -/
def subtype : s →+* R :=
  { SubmonoidClass.subtype s, AddSubmonoidClass.subtype s with toFun := (↑) }

@[simp]
theorem coe_subtype : (subtype s : s → R) = ((↑) : s → R) :=
  rfl

-- Prefer subclasses of `Semiring` over subclasses of `SubsemiringClass`.
/-- A subsemiring of a `Semiring` is a `Semiring`. -/
instance (priority := 75) toSemiring {R} [Semiring R] [SetLike S R] [SubsemiringClass S R] :
    Semiring s :=
  Subtype.coe_injective.semiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

@[simp, norm_cast]
theorem coe_pow {R} [Semiring R] [SetLike S R] [SubsemiringClass S R] (x : s) (n : ℕ) :
    ((x ^ n : s) : R) = (x : R) ^ n := by
  induction' n with n ih
  · simp
  · simp [pow_succ, ih]

/-- A subsemiring of a `CommSemiring` is a `CommSemiring`. -/
instance toCommSemiring {R} [CommSemiring R] [SetLike S R] [SubsemiringClass S R] :
    CommSemiring s :=
  Subtype.coe_injective.commSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

instance instCharZero [CharZero R] : CharZero s :=
  ⟨Function.Injective.of_comp (f := Subtype.val) (g := Nat.cast (R := s)) Nat.cast_injective⟩

end SubsemiringClass

end SubsemiringClass

variable [NonAssocSemiring S] [NonAssocSemiring T]

/-- A subsemiring of a semiring `R` is a subset `s` that is both a multiplicative and an additive
submonoid. -/
structure Subsemiring (R : Type u) [NonAssocSemiring R] extends Submonoid R, AddSubmonoid R

/-- Reinterpret a `Subsemiring` as a `Submonoid`. -/
add_decl_doc Subsemiring.toSubmonoid

/-- Reinterpret a `Subsemiring` as an `AddSubmonoid`. -/
add_decl_doc Subsemiring.toAddSubmonoid

namespace Subsemiring

instance : SetLike (Subsemiring R) R where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective' h

instance : SubsemiringClass (Subsemiring R) R where
  zero_mem := zero_mem'
  add_mem {s} := AddSubsemigroup.add_mem' s.toAddSubmonoid.toAddSubsemigroup
  one_mem {s} := Submonoid.one_mem' s.toSubmonoid
  mul_mem {s} := Subsemigroup.mul_mem' s.toSubmonoid.toSubsemigroup

@[simp]
theorem mem_toSubmonoid {s : Subsemiring R} {x : R} : x ∈ s.toSubmonoid ↔ x ∈ s :=
  Iff.rfl

-- `@[simp]` -- Porting note (#10618): simp can prove thisrove this
theorem mem_carrier {s : Subsemiring R} {x : R} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

/-- Two subsemirings are equal if they have the same elements. -/
@[ext]
theorem ext {S T : Subsemiring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy of a subsemiring with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (S : Subsemiring R) (s : Set R) (hs : s = ↑S) : Subsemiring R :=
  { S.toAddSubmonoid.copy s hs, S.toSubmonoid.copy s hs with carrier := s }

@[simp]
theorem coe_copy (S : Subsemiring R) (s : Set R) (hs : s = ↑S) : (S.copy s hs : Set R) = s :=
  rfl

theorem copy_eq (S : Subsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

theorem toSubmonoid_injective : Function.Injective (toSubmonoid : Subsemiring R → Submonoid R)
  | _, _, h => ext (SetLike.ext_iff.mp h : _)

@[mono]
theorem toSubmonoid_strictMono : StrictMono (toSubmonoid : Subsemiring R → Submonoid R) :=
  fun _ _ => id

@[mono]
theorem toSubmonoid_mono : Monotone (toSubmonoid : Subsemiring R → Submonoid R) :=
  toSubmonoid_strictMono.monotone

theorem toAddSubmonoid_injective :
    Function.Injective (toAddSubmonoid : Subsemiring R → AddSubmonoid R)
  | _, _, h => ext (SetLike.ext_iff.mp h : _)

@[mono]
theorem toAddSubmonoid_strictMono : StrictMono (toAddSubmonoid : Subsemiring R → AddSubmonoid R) :=
  fun _ _ => id

@[mono]
theorem toAddSubmonoid_mono : Monotone (toAddSubmonoid : Subsemiring R → AddSubmonoid R) :=
  toAddSubmonoid_strictMono.monotone

/-- Construct a `Subsemiring R` from a set `s`, a submonoid `sm`, and an additive
submonoid `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`. -/
protected def mk' (s : Set R) (sm : Submonoid R) (hm : ↑sm = s) (sa : AddSubmonoid R)
    (ha : ↑sa = s) : Subsemiring R where
  carrier := s
  zero_mem' := by exact ha ▸ sa.zero_mem
  one_mem' := by exact hm ▸ sm.one_mem
  add_mem' {x y} := by simpa only [← ha] using sa.add_mem
  mul_mem' {x y} := by simpa only [← hm] using sm.mul_mem

@[simp]
theorem coe_mk' {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R} (ha : ↑sa = s) :
    (Subsemiring.mk' s sm hm sa ha : Set R) = s :=
  rfl

@[simp]
theorem mem_mk' {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R} (ha : ↑sa = s)
    {x : R} : x ∈ Subsemiring.mk' s sm hm sa ha ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem mk'_toSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) : (Subsemiring.mk' s sm hm sa ha).toSubmonoid = sm :=
  SetLike.coe_injective hm.symm

@[simp]
theorem mk'_toAddSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) : (Subsemiring.mk' s sm hm sa ha).toAddSubmonoid = sa :=
  SetLike.coe_injective ha.symm

end Subsemiring

namespace Subsemiring

variable (s : Subsemiring R)

/-- A subsemiring contains the semiring's 1. -/
protected theorem one_mem : (1 : R) ∈ s :=
  one_mem s

/-- A subsemiring contains the semiring's 0. -/
protected theorem zero_mem : (0 : R) ∈ s :=
  zero_mem s

/-- A subsemiring is closed under multiplication. -/
protected theorem mul_mem {x y : R} : x ∈ s → y ∈ s → x * y ∈ s :=
  mul_mem

/-- A subsemiring is closed under addition. -/
protected theorem add_mem {x y : R} : x ∈ s → y ∈ s → x + y ∈ s :=
  add_mem

/-- Product of a list of elements in a `Subsemiring` is in the `Subsemiring`. -/
nonrec theorem list_prod_mem {R : Type*} [Semiring R] (s : Subsemiring R) {l : List R} :
    (∀ x ∈ l, x ∈ s) → l.prod ∈ s :=
  list_prod_mem

/-- Sum of a list of elements in a `Subsemiring` is in the `Subsemiring`. -/
protected theorem list_sum_mem {l : List R} : (∀ x ∈ l, x ∈ s) → l.sum ∈ s :=
  list_sum_mem

/-- Product of a multiset of elements in a `Subsemiring` of a `CommSemiring`
    is in the `Subsemiring`. -/
protected theorem multiset_prod_mem {R} [CommSemiring R] (s : Subsemiring R) (m : Multiset R) :
    (∀ a ∈ m, a ∈ s) → m.prod ∈ s :=
  multiset_prod_mem m

/-- Sum of a multiset of elements in a `Subsemiring` of a `Semiring` is
in the `add_subsemiring`. -/
protected theorem multiset_sum_mem (m : Multiset R) : (∀ a ∈ m, a ∈ s) → m.sum ∈ s :=
  multiset_sum_mem m

/-- Product of elements of a subsemiring of a `CommSemiring` indexed by a `Finset` is in the
    subsemiring. -/
protected theorem prod_mem {R : Type*} [CommSemiring R] (s : Subsemiring R) {ι : Type*}
    {t : Finset ι} {f : ι → R} (h : ∀ c ∈ t, f c ∈ s) : (∏ i ∈ t, f i) ∈ s :=
  prod_mem h

/-- Sum of elements in a `Subsemiring` of a `Semiring` indexed by a `Finset`
is in the `add_subsemiring`. -/
protected theorem sum_mem (s : Subsemiring R) {ι : Type*} {t : Finset ι} {f : ι → R}
    (h : ∀ c ∈ t, f c ∈ s) : (∑ i ∈ t, f i) ∈ s :=
  sum_mem h

/-- A subsemiring of a `NonAssocSemiring` inherits a `NonAssocSemiring` structure -/
instance toNonAssocSemiring : NonAssocSemiring s :=
  -- Porting note: this used to be a specialized instance which needed to be expensively unified.
  SubsemiringClass.toNonAssocSemiring _

@[simp, norm_cast]
theorem coe_one : ((1 : s) : R) = (1 : R) :=
  rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : s) : R) = (0 : R) :=
  rfl

@[simp, norm_cast]
theorem coe_add (x y : s) : ((x + y : s) : R) = (x + y : R) :=
  rfl

@[simp, norm_cast]
theorem coe_mul (x y : s) : ((x * y : s) : R) = (x * y : R) :=
  rfl

instance nontrivial [Nontrivial R] : Nontrivial s :=
  nontrivial_of_ne 0 1 fun H => zero_ne_one (congr_arg Subtype.val H)

protected theorem pow_mem {R : Type*} [Semiring R] (s : Subsemiring R) {x : R} (hx : x ∈ s)
    (n : ℕ) : x ^ n ∈ s :=
  pow_mem hx n

instance noZeroDivisors [NoZeroDivisors R] : NoZeroDivisors s where
  eq_zero_or_eq_zero_of_mul_eq_zero {_ _} h :=
    (eq_zero_or_eq_zero_of_mul_eq_zero <| Subtype.ext_iff.mp h).imp Subtype.eq Subtype.eq

/-- A subsemiring of a `Semiring` is a `Semiring`. -/
instance toSemiring {R} [Semiring R] (s : Subsemiring R) : Semiring s :=
  { s.toNonAssocSemiring, s.toSubmonoid.toMonoid with }

@[simp, norm_cast]
theorem coe_pow {R} [Semiring R] (s : Subsemiring R) (x : s) (n : ℕ) :
    ((x ^ n : s) : R) = (x : R) ^ n := by
  induction' n with n ih
  · simp
  · simp [pow_succ, ih]

/-- A subsemiring of a `CommSemiring` is a `CommSemiring`. -/
instance toCommSemiring {R} [CommSemiring R] (s : Subsemiring R) : CommSemiring s :=
  { s.toSemiring with mul_comm := fun _ _ => Subtype.eq <| mul_comm _ _ }

/-- The natural ring hom from a subsemiring of semiring `R` to `R`. -/
def subtype : s →+* R :=
  { s.toSubmonoid.subtype, s.toAddSubmonoid.subtype with toFun := (↑) }

@[simp]
theorem coe_subtype : ⇑s.subtype = ((↑) : s → R) :=
  rfl

protected theorem nsmul_mem {x : R} (hx : x ∈ s) (n : ℕ) : n • x ∈ s :=
  nsmul_mem hx n

@[simp]
theorem coe_toSubmonoid (s : Subsemiring R) : (s.toSubmonoid : Set R) = s :=
  rfl

-- Porting note: adding this as `simp`-normal form for `coe_toAddSubmonoid`
@[simp]
theorem coe_carrier_toSubmonoid (s : Subsemiring R) : (s.toSubmonoid.carrier : Set R) = s :=
  rfl

-- Porting note: can be proven using `SetLike` so removing `@[simp]`
theorem mem_toAddSubmonoid {s : Subsemiring R} {x : R} : x ∈ s.toAddSubmonoid ↔ x ∈ s :=
  Iff.rfl

-- Porting note: new normal form is `coe_carrier_toSubmonoid` so removing `@[simp]`
theorem coe_toAddSubmonoid (s : Subsemiring R) : (s.toAddSubmonoid : Set R) = s :=
  rfl

/-- The subsemiring `R` of the semiring `R`. -/
instance : Top (Subsemiring R) :=
  ⟨{ (⊤ : Submonoid R), (⊤ : AddSubmonoid R) with }⟩

@[simp]
theorem mem_top (x : R) : x ∈ (⊤ : Subsemiring R) :=
  Set.mem_univ x

@[simp]
theorem coe_top : ((⊤ : Subsemiring R) : Set R) = Set.univ :=
  rfl

/-- The ring equiv between the top element of `Subsemiring R` and `R`. -/
@[simps]
def topEquiv : (⊤ : Subsemiring R) ≃+* R where
  toFun r := r
  invFun r := ⟨r, Subsemiring.mem_top r⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' := (⊤ : Subsemiring R).coe_mul
  map_add' := (⊤ : Subsemiring R).coe_add

/-- The preimage of a subsemiring along a ring homomorphism is a subsemiring. -/
def comap (f : R →+* S) (s : Subsemiring S) : Subsemiring R :=
  { s.toSubmonoid.comap (f : R →* S), s.toAddSubmonoid.comap (f : R →+ S) with carrier := f ⁻¹' s }

@[simp]
theorem coe_comap (s : Subsemiring S) (f : R →+* S) : (s.comap f : Set R) = f ⁻¹' s :=
  rfl

@[simp]
theorem mem_comap {s : Subsemiring S} {f : R →+* S} {x : R} : x ∈ s.comap f ↔ f x ∈ s :=
  Iff.rfl

theorem comap_comap (s : Subsemiring T) (g : S →+* T) (f : R →+* S) :
    (s.comap g).comap f = s.comap (g.comp f) :=
  rfl

/-- The image of a subsemiring along a ring homomorphism is a subsemiring. -/
def map (f : R →+* S) (s : Subsemiring R) : Subsemiring S :=
  { s.toSubmonoid.map (f : R →* S), s.toAddSubmonoid.map (f : R →+ S) with carrier := f '' s }

@[simp]
theorem coe_map (f : R →+* S) (s : Subsemiring R) : (s.map f : Set S) = f '' s :=
  rfl

@[simp]
lemma mem_map {f : R →+* S} {s : Subsemiring R} {y : S} : y ∈ s.map f ↔ ∃ x ∈ s, f x = y := Iff.rfl

@[simp]
theorem map_id : s.map (RingHom.id R) = s :=
  SetLike.coe_injective <| Set.image_id _

theorem map_map (g : S →+* T) (f : R →+* S) : (s.map f).map g = s.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _

theorem map_le_iff_le_comap {f : R →+* S} {s : Subsemiring R} {t : Subsemiring S} :
    s.map f ≤ t ↔ s ≤ t.comap f :=
  Set.image_subset_iff

theorem gc_map_comap (f : R →+* S) : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap

/-- A subsemiring is isomorphic to its image under an injective function -/
noncomputable def equivMapOfInjective (f : R →+* S) (hf : Function.Injective f) : s ≃+* s.map f :=
  { Equiv.Set.image f s hf with
    map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _)
    map_add' := fun _ _ => Subtype.ext (f.map_add _ _) }

@[simp]
theorem coe_equivMapOfInjective_apply (f : R →+* S) (hf : Function.Injective f) (x : s) :
    (equivMapOfInjective s f hf x : S) = f x :=
  rfl

end Subsemiring

namespace RingHom

variable (g : S →+* T) (f : R →+* S)

/-- The range of a ring homomorphism is a subsemiring. See Note [range copy pattern]. -/
def rangeS : Subsemiring S :=
  ((⊤ : Subsemiring R).map f).copy (Set.range f) Set.image_univ.symm

@[simp]
theorem coe_rangeS : (f.rangeS : Set S) = Set.range f :=
  rfl

@[simp]
theorem mem_rangeS {f : R →+* S} {y : S} : y ∈ f.rangeS ↔ ∃ x, f x = y :=
  Iff.rfl

theorem rangeS_eq_map (f : R →+* S) : f.rangeS = (⊤ : Subsemiring R).map f := by
  ext
  simp

theorem mem_rangeS_self (f : R →+* S) (x : R) : f x ∈ f.rangeS :=
  mem_rangeS.mpr ⟨x, rfl⟩

theorem map_rangeS : f.rangeS.map g = (g.comp f).rangeS := by
  simpa only [rangeS_eq_map] using (⊤ : Subsemiring R).map_map g f

/-- The range of a morphism of semirings is a fintype, if the domain is a fintype.
Note: this instance can form a diamond with `Subtype.fintype` in the
  presence of `Fintype S`. -/
instance fintypeRangeS [Fintype R] [DecidableEq S] (f : R →+* S) : Fintype (rangeS f) :=
  Set.fintypeRange f

end RingHom

namespace Subsemiring

instance : Bot (Subsemiring R) :=
  ⟨(Nat.castRingHom R).rangeS⟩

instance : Inhabited (Subsemiring R) :=
  ⟨⊥⟩

theorem coe_bot : ((⊥ : Subsemiring R) : Set R) = Set.range ((↑) : ℕ → R) :=
  (Nat.castRingHom R).coe_rangeS

theorem mem_bot {x : R} : x ∈ (⊥ : Subsemiring R) ↔ ∃ n : ℕ, ↑n = x :=
  RingHom.mem_rangeS

/-- The inf of two subsemirings is their intersection. -/
instance : Inf (Subsemiring R) :=
  ⟨fun s t =>
    { s.toSubmonoid ⊓ t.toSubmonoid, s.toAddSubmonoid ⊓ t.toAddSubmonoid with carrier := s ∩ t }⟩

@[simp]
theorem coe_inf (p p' : Subsemiring R) : ((p ⊓ p' : Subsemiring R) : Set R) = (p : Set R) ∩ p' :=
  rfl

@[simp]
theorem mem_inf {p p' : Subsemiring R} {x : R} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl

instance : InfSet (Subsemiring R) :=
  ⟨fun s =>
    Subsemiring.mk' (⋂ t ∈ s, ↑t) (⨅ t ∈ s, Subsemiring.toSubmonoid t) (by simp)
      (⨅ t ∈ s, Subsemiring.toAddSubmonoid t)
      (by simp)⟩

@[simp, norm_cast]
theorem coe_sInf (S : Set (Subsemiring R)) : ((sInf S : Subsemiring R) : Set R) = ⋂ s ∈ S, ↑s :=
  rfl

theorem mem_sInf {S : Set (Subsemiring R)} {x : R} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂

@[simp]
theorem sInf_toSubmonoid (s : Set (Subsemiring R)) :
    (sInf s).toSubmonoid = ⨅ t ∈ s, Subsemiring.toSubmonoid t :=
  mk'_toSubmonoid _ _

@[simp]
theorem sInf_toAddSubmonoid (s : Set (Subsemiring R)) :
    (sInf s).toAddSubmonoid = ⨅ t ∈ s, Subsemiring.toAddSubmonoid t :=
  mk'_toAddSubmonoid _ _

/-- Subsemirings of a semiring form a complete lattice. -/
instance : CompleteLattice (Subsemiring R) :=
  { completeLatticeOfInf (Subsemiring R) fun _ =>
      IsGLB.of_image
        (fun {s t : Subsemiring R} => show (s : Set R) ⊆ t ↔ s ≤ t from SetLike.coe_subset_coe)
        isGLB_biInf with
    bot := ⊥
    bot_le := fun s _ hx =>
      let ⟨n, hn⟩ := mem_bot.1 hx
      hn ▸ natCast_mem s n
    top := ⊤
    le_top := fun _ _ _ => trivial
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right
    le_inf := fun _ _ _ h₁ h₂ _ hx => ⟨h₁ hx, h₂ hx⟩ }

theorem eq_top_iff' (A : Subsemiring R) : A = ⊤ ↔ ∀ x : R, x ∈ A :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩

section NonAssocSemiring

variable (R)

/-- The center of a non-associative semiring `R` is the set of elements that commute and associate
with everything in `R` -/
def center : Subsemiring R :=
  { NonUnitalSubsemiring.center R with
    one_mem' := Set.one_mem_center }

theorem coe_center : ↑(center R) = Set.center R :=
  rfl

@[simp]
theorem center_toSubmonoid : (center R).toSubmonoid = Submonoid.center R :=
  rfl

/-- The center is commutative and associative.

This is not an instance as it forms a non-defeq diamond with
`NonUnitalSubringClass.tNonUnitalring ` in the `npow` field. -/
abbrev center.commSemiring' : CommSemiring (center R) :=
  { Submonoid.center.commMonoid', (center R).toNonAssocSemiring with }

end NonAssocSemiring

section Semiring

/-- The center is commutative. -/
instance center.commSemiring {R} [Semiring R] : CommSemiring (center R) :=
  { Submonoid.center.commMonoid, (center R).toSemiring with }

-- no instance diamond, unlike the primed version
example {R} [Semiring R] :
    center.commSemiring.toSemiring = Subsemiring.toSemiring (center R) := by
  with_reducible_and_instances rfl

theorem mem_center_iff {R} [Semiring R] {z : R} : z ∈ center R ↔ ∀ g, g * z = z * g :=
  Subsemigroup.mem_center_iff

instance decidableMemCenter {R} [Semiring R] [DecidableEq R] [Fintype R] :
    DecidablePred (· ∈ center R) := fun _ => decidable_of_iff' _ mem_center_iff

@[simp]
theorem center_eq_top (R) [CommSemiring R] : center R = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ R)


end Semiring

section Centralizer

/-- The centralizer of a set as subsemiring. -/
def centralizer {R} [Semiring R] (s : Set R) : Subsemiring R :=
  { Submonoid.centralizer s with
    carrier := s.centralizer
    zero_mem' := Set.zero_mem_centralizer
    add_mem' := Set.add_mem_centralizer }

@[simp, norm_cast]
theorem coe_centralizer {R} [Semiring R] (s : Set R) : (centralizer s : Set R) = s.centralizer :=
  rfl

theorem centralizer_toSubmonoid {R} [Semiring R] (s : Set R) :
    (centralizer s).toSubmonoid = Submonoid.centralizer s :=
  rfl

theorem mem_centralizer_iff {R} [Semiring R] {s : Set R} {z : R} :
    z ∈ centralizer s ↔ ∀ g ∈ s, g * z = z * g :=
  Iff.rfl

theorem center_le_centralizer {R} [Semiring R] (s) : center R ≤ centralizer s :=
  s.center_subset_centralizer

theorem centralizer_le {R} [Semiring R] (s t : Set R) (h : s ⊆ t) : centralizer t ≤ centralizer s :=
  Set.centralizer_subset h

@[simp]
theorem centralizer_eq_top_iff_subset {R} [Semiring R] {s : Set R} :
    centralizer s = ⊤ ↔ s ⊆ center R :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[simp]
theorem centralizer_univ {R} [Semiring R] : centralizer Set.univ = center R :=
  SetLike.ext' (Set.centralizer_univ R)

lemma le_centralizer_centralizer {R} [Semiring R] {s : Subsemiring R} :
    s ≤ centralizer (centralizer (s : Set R)) :=
  Set.subset_centralizer_centralizer

@[simp]
lemma centralizer_centralizer_centralizer {R} [Semiring R] {s : Set R} :
    centralizer s.centralizer.centralizer = centralizer s := by
  apply SetLike.coe_injective
  simp only [coe_centralizer, Set.centralizer_centralizer_centralizer]

end Centralizer

/-- The `Subsemiring` generated by a set. -/
def closure (s : Set R) : Subsemiring R :=
  sInf { S | s ⊆ S }

theorem mem_closure {x : R} {s : Set R} : x ∈ closure s ↔ ∀ S : Subsemiring R, s ⊆ S → x ∈ S :=
  mem_sInf

/-- The subsemiring generated by a set includes the set. -/
@[simp, aesop safe 20 apply (rule_sets := [SetLike])]
theorem subset_closure {s : Set R} : s ⊆ closure s := fun _ hx => mem_closure.2 fun _ hS => hS hx

theorem not_mem_of_not_mem_closure {s : Set R} {P : R} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)

/-- A subsemiring `S` includes `closure s` if and only if it includes `s`. -/
@[simp]
theorem closure_le {s : Set R} {t : Subsemiring R} : closure s ≤ t ↔ s ⊆ t :=
  ⟨Set.Subset.trans subset_closure, fun h => sInf_le h⟩

/-- Subsemiring closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
theorem closure_mono ⦃s t : Set R⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Set.Subset.trans h subset_closure

theorem closure_eq_of_le {s : Set R} {t : Subsemiring R} (h₁ : s ⊆ t) (h₂ : t ≤ closure s) :
    closure s = t :=
  le_antisymm (closure_le.2 h₁) h₂

theorem mem_map_equiv {f : R ≃+* S} {K : Subsemiring R} {x : S} :
    x ∈ K.map (f : R →+* S) ↔ f.symm x ∈ K := by
  convert @Set.mem_image_equiv _ _ (↑K) f.toEquiv x using 1

theorem map_equiv_eq_comap_symm (f : R ≃+* S) (K : Subsemiring R) :
    K.map (f : R →+* S) = K.comap f.symm :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage K)

theorem comap_equiv_eq_map_symm (f : R ≃+* S) (K : Subsemiring S) :
    K.comap (f : R →+* S) = K.map f.symm :=
  (map_equiv_eq_comap_symm f.symm K).symm

end Subsemiring

namespace Submonoid

/-- The additive closure of a submonoid is a subsemiring. -/
def subsemiringClosure (M : Submonoid R) : Subsemiring R :=
  { AddSubmonoid.closure (M : Set R) with
    one_mem' := AddSubmonoid.mem_closure.mpr fun _ hy => hy M.one_mem
    mul_mem' := MulMemClass.mul_mem_add_closure }

theorem subsemiringClosure_coe :
    (M.subsemiringClosure : Set R) = AddSubmonoid.closure (M : Set R) :=
  rfl

theorem subsemiringClosure_toAddSubmonoid :
    M.subsemiringClosure.toAddSubmonoid = AddSubmonoid.closure (M : Set R) :=
  rfl

/-- The `Subsemiring` generated by a multiplicative submonoid coincides with the
`Subsemiring.closure` of the submonoid itself . -/
theorem subsemiringClosure_eq_closure : M.subsemiringClosure = Subsemiring.closure (M : Set R) := by
  ext
  refine
    ⟨fun hx => ?_, fun hx =>
      (Subsemiring.mem_closure.mp hx) M.subsemiringClosure fun s sM => ?_⟩
  <;> rintro - ⟨H1, rfl⟩
  <;> rintro - ⟨H2, rfl⟩
  · exact AddSubmonoid.mem_closure.mp hx H1.toAddSubmonoid H2
  · exact H2 sM

end Submonoid

namespace Subsemiring

@[simp]
theorem closure_submonoid_closure (s : Set R) : closure ↑(Submonoid.closure s) = closure s :=
  le_antisymm
    (closure_le.mpr fun _ hy =>
      (Submonoid.mem_closure.mp hy) (closure s).toSubmonoid subset_closure)
    (closure_mono Submonoid.subset_closure)

/-- The elements of the subsemiring closure of `M` are exactly the elements of the additive closure
of a multiplicative submonoid `M`. -/
theorem coe_closure_eq (s : Set R) :
    (closure s : Set R) = AddSubmonoid.closure (Submonoid.closure s : Set R) := by
  simp [← Submonoid.subsemiringClosure_toAddSubmonoid, Submonoid.subsemiringClosure_eq_closure]

theorem mem_closure_iff {s : Set R} {x} :
    x ∈ closure s ↔ x ∈ AddSubmonoid.closure (Submonoid.closure s : Set R) :=
  Set.ext_iff.mp (coe_closure_eq s) x

@[simp]
theorem closure_addSubmonoid_closure {s : Set R} :
    closure ↑(AddSubmonoid.closure s) = closure s := by
  ext x
  refine ⟨fun hx => ?_, fun hx => closure_mono AddSubmonoid.subset_closure hx⟩
  rintro - ⟨H, rfl⟩
  rintro - ⟨J, rfl⟩
  refine (AddSubmonoid.mem_closure.mp (mem_closure_iff.mp hx)) H.toAddSubmonoid fun y hy => ?_
  refine (Submonoid.mem_closure.mp hy) H.toSubmonoid fun z hz => ?_
  exact (AddSubmonoid.mem_closure.mp hz) H.toAddSubmonoid fun w hw => J hw

/-- An induction principle for closure membership. If `p` holds for `0`, `1`, and all elements
of `s`, and is preserved under addition and multiplication, then `p` holds for all elements
of the closure of `s`. -/
@[elab_as_elim]
theorem closure_induction {s : Set R} {p : R → Prop} {x} (h : x ∈ closure s) (mem : ∀ x ∈ s, p x)
    (zero : p 0) (one : p 1) (add : ∀ x y, p x → p y → p (x + y))
    (mul : ∀ x y, p x → p y → p (x * y)) : p x :=
  (@closure_le _ _ _ ⟨⟨⟨p, @mul⟩, one⟩, @add, zero⟩).2 mem h

@[elab_as_elim]
theorem closure_induction' {s : Set R} {p : ∀ x, x ∈ closure s → Prop}
    (mem : ∀ (x) (h : x ∈ s), p x (subset_closure h))
    (zero : p 0 (zero_mem _)) (one : p 1 (one_mem _))
    (add : ∀ x hx y hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (mul : ∀ x hx y hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    {a : R} (ha : a ∈ closure s) : p a ha := by
  refine Exists.elim ?_ fun (ha : a ∈ closure s) (hc : p a ha) => hc
  refine
    closure_induction ha (fun m hm => ⟨subset_closure hm, mem m hm⟩) ⟨zero_mem _, zero⟩
      ⟨one_mem _, one⟩ ?_ ?_
  · exact (fun x y hx hy => hx.elim fun hx' hx => hy.elim fun hy' hy =>
      ⟨add_mem hx' hy', add _ _ _ _ hx hy⟩)
  · exact (fun x y hx hy => hx.elim fun hx' hx => hy.elim fun hy' hy =>
      ⟨mul_mem hx' hy', mul _ _ _ _ hx hy⟩)

/-- An induction principle for closure membership for predicates with two arguments. -/
@[elab_as_elim]
theorem closure_induction₂ {s : Set R} {p : R → R → Prop} {x} {y : R} (hx : x ∈ closure s)
    (hy : y ∈ closure s) (Hs : ∀ x ∈ s, ∀ y ∈ s, p x y) (H0_left : ∀ x, p 0 x)
    (H0_right : ∀ x, p x 0) (H1_left : ∀ x, p 1 x) (H1_right : ∀ x, p x 1)
    (Hadd_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ + x₂) y)
    (Hadd_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ + y₂))
    (Hmul_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ * x₂) y)
    (Hmul_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ * y₂)) : p x y :=
  closure_induction hx
    (fun x₁ x₁s =>
      closure_induction hy (Hs x₁ x₁s) (H0_right x₁) (H1_right x₁) (Hadd_right x₁) (Hmul_right x₁))
    (H0_left y) (H1_left y) (fun z z' => Hadd_left z z' y) fun z z' => Hmul_left z z' y

theorem mem_closure_iff_exists_list {R} [Semiring R] {s : Set R} {x} :
    x ∈ closure s ↔ ∃ L : List (List R), (∀ t ∈ L, ∀ y ∈ t, y ∈ s) ∧ (L.map List.prod).sum = x := by
  constructor
  · intro hx
    -- Porting note: needed explicit `p`
    let p : R → Prop := fun x =>
      ∃ (L : List (List R)),
        (∀ (t : List R), t ∈ L → ∀ (y : R), y ∈ t → y ∈ s) ∧ (List.map List.prod L).sum = x
    exact AddSubmonoid.closure_induction (p := p) (mem_closure_iff.1 hx)
      (fun x hx =>
        suffices ∃ t : List R, (∀ y ∈ t, y ∈ s) ∧ t.prod = x from
          let ⟨t, ht1, ht2⟩ := this
          ⟨[t], List.forall_mem_singleton.2 ht1, by
            rw [List.map_singleton, List.sum_singleton, ht2]⟩
        Submonoid.closure_induction hx
          (fun x hx => ⟨[x], List.forall_mem_singleton.2 hx, one_mul x⟩)
          ⟨[], List.forall_mem_nil _, rfl⟩ fun x y ⟨t, ht1, ht2⟩ ⟨u, hu1, hu2⟩ =>
          ⟨t ++ u, List.forall_mem_append.2 ⟨ht1, hu1⟩, by rw [List.prod_append, ht2, hu2]⟩)
      ⟨[], List.forall_mem_nil _, rfl⟩ fun x y ⟨L, HL1, HL2⟩ ⟨M, HM1, HM2⟩ =>
      ⟨L ++ M, List.forall_mem_append.2 ⟨HL1, HM1⟩, by
        rw [List.map_append, List.sum_append, HL2, HM2]⟩
  · rintro ⟨L, HL1, HL2⟩
    exact HL2 ▸
      list_sum_mem fun r hr =>
        let ⟨t, ht1, ht2⟩ := List.mem_map.1 hr
        ht2 ▸ list_prod_mem _ fun y hy => subset_closure <| HL1 t ht1 y hy

variable (R)

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : GaloisInsertion (@closure R _) (↑) where
  choice s _ := closure s
  gc _ _ := closure_le
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl

variable {R}

/-- Closure of a subsemiring `S` equals `S`. -/
theorem closure_eq (s : Subsemiring R) : closure (s : Set R) = s :=
  (Subsemiring.gi R).l_u_eq s

@[simp]
theorem closure_empty : closure (∅ : Set R) = ⊥ :=
  (Subsemiring.gi R).gc.l_bot

@[simp]
theorem closure_univ : closure (Set.univ : Set R) = ⊤ :=
  @coe_top R _ ▸ closure_eq ⊤

theorem closure_union (s t : Set R) : closure (s ∪ t) = closure s ⊔ closure t :=
  (Subsemiring.gi R).gc.l_sup

theorem closure_iUnion {ι} (s : ι → Set R) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Subsemiring.gi R).gc.l_iSup

theorem closure_sUnion (s : Set (Set R)) : closure (⋃₀ s) = ⨆ t ∈ s, closure t :=
  (Subsemiring.gi R).gc.l_sSup

theorem map_sup (s t : Subsemiring R) (f : R →+* S) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
  (gc_map_comap f).l_sup

theorem map_iSup {ι : Sort*} (f : R →+* S) (s : ι → Subsemiring R) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup

theorem comap_inf (s t : Subsemiring S) (f : R →+* S) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
  (gc_map_comap f).u_inf

theorem comap_iInf {ι : Sort*} (f : R →+* S) (s : ι → Subsemiring S) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[simp]
theorem map_bot (f : R →+* S) : (⊥ : Subsemiring R).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
theorem comap_top (f : R →+* S) : (⊤ : Subsemiring S).comap f = ⊤ :=
  (gc_map_comap f).u_top

/-- Given `Subsemiring`s `s`, `t` of semirings `R`, `S` respectively, `s.prod t` is `s × t`
as a subsemiring of `R × S`. -/
def prod (s : Subsemiring R) (t : Subsemiring S) : Subsemiring (R × S) :=
  { s.toSubmonoid.prod t.toSubmonoid, s.toAddSubmonoid.prod t.toAddSubmonoid with
    carrier := s ×ˢ t }

@[norm_cast]
theorem coe_prod (s : Subsemiring R) (t : Subsemiring S) :
    (s.prod t : Set (R × S)) = (s : Set R) ×ˢ (t : Set S) :=
  rfl

theorem mem_prod {s : Subsemiring R} {t : Subsemiring S} {p : R × S} :
    p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl

@[mono]
theorem prod_mono ⦃s₁ s₂ : Subsemiring R⦄ (hs : s₁ ≤ s₂) ⦃t₁ t₂ : Subsemiring S⦄ (ht : t₁ ≤ t₂) :
    s₁.prod t₁ ≤ s₂.prod t₂ :=
  Set.prod_mono hs ht

theorem prod_mono_right (s : Subsemiring R) : Monotone fun t : Subsemiring S => s.prod t :=
  prod_mono (le_refl s)

theorem prod_mono_left (t : Subsemiring S) : Monotone fun s : Subsemiring R => s.prod t :=
  fun _ _ hs => prod_mono hs (le_refl t)

theorem prod_top (s : Subsemiring R) : s.prod (⊤ : Subsemiring S) = s.comap (RingHom.fst R S) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_fst]

theorem top_prod (s : Subsemiring S) : (⊤ : Subsemiring R).prod s = s.comap (RingHom.snd R S) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_snd]

@[simp]
theorem top_prod_top : (⊤ : Subsemiring R).prod (⊤ : Subsemiring S) = ⊤ :=
  (top_prod _).trans <| comap_top _

/-- Product of subsemirings is isomorphic to their product as monoids. -/
def prodEquiv (s : Subsemiring R) (t : Subsemiring S) : s.prod t ≃+* s × t :=
  { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subsemiring R} (hS : Directed (· ≤ ·) S)
    {x : R} : (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  refine ⟨?_, fun ⟨i, hi⟩ ↦ le_iSup S i hi⟩
  let U : Subsemiring R :=
    Subsemiring.mk' (⋃ i, (S i : Set R))
      (⨆ i, (S i).toSubmonoid) (Submonoid.coe_iSup_of_directed hS)
      (⨆ i, (S i).toAddSubmonoid) (AddSubmonoid.coe_iSup_of_directed hS)
  -- Porting note: gave the hypothesis an explicit name because `@this` doesn't work
  suffices h : ⨆ i, S i ≤ U by simpa [U] using @h x
  exact iSup_le fun i x hx ↦ Set.mem_iUnion.2 ⟨i, hx⟩

theorem coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subsemiring R}
    (hS : Directed (· ≤ ·) S) : ((⨆ i, S i : Subsemiring R) : Set R) = ⋃ i, S i :=
  Set.ext fun x ↦ by simp [mem_iSup_of_directed hS]

theorem mem_sSup_of_directedOn {S : Set (Subsemiring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) {x : R} : x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  haveI : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, SetCoe.exists, Subtype.coe_mk,
    exists_prop]

theorem coe_sSup_of_directedOn {S : Set (Subsemiring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(sSup S) : Set R) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]

end Subsemiring

namespace RingHom

variable [NonAssocSemiring T] {s : Subsemiring R}
variable {σR σS : Type*}
variable [SetLike σR R] [SetLike σS S] [SubsemiringClass σR R] [SubsemiringClass σS S]

open Subsemiring

/-- Restriction of a ring homomorphism to a subsemiring of the domain. -/
def domRestrict (f : R →+* S) (s : σR) : s →+* S :=
  f.comp <| SubsemiringClass.subtype s

@[simp]
theorem restrict_apply (f : R →+* S) {s : σR} (x : s) : f.domRestrict s x = f x :=
  rfl

/-- Restriction of a ring homomorphism to a subsemiring of the codomain. -/
def codRestrict (f : R →+* S) (s : σS) (h : ∀ x, f x ∈ s) : R →+* s :=
  { (f : R →* S).codRestrict s h, (f : R →+ S).codRestrict s h with toFun := fun n => ⟨f n, h n⟩ }

/-- The ring homomorphism from the preimage of `s` to `s`. -/
def restrict (f : R →+* S) (s' : σR) (s : σS) (h : ∀ x ∈ s', f x ∈ s) : s' →+* s :=
  (f.domRestrict s').codRestrict s fun x => h x x.2

@[simp]
theorem coe_restrict_apply (f : R →+* S) (s' : σR) (s : σS) (h : ∀ x ∈ s', f x ∈ s) (x : s') :
    (f.restrict s' s h x : S) = f x :=
  rfl

@[simp]
theorem comp_restrict (f : R →+* S) (s' : σR) (s : σS) (h : ∀ x ∈ s', f x ∈ s) :
    (SubsemiringClass.subtype s).comp (f.restrict s' s h) = f.comp (SubsemiringClass.subtype s') :=
  rfl

/-- Restriction of a ring homomorphism to its range interpreted as a subsemiring.

This is the bundled version of `Set.rangeFactorization`. -/
def rangeSRestrict (f : R →+* S) : R →+* f.rangeS :=
  f.codRestrict (R := R) (S := S) (σS := Subsemiring S) f.rangeS f.mem_rangeS_self

@[simp]
theorem coe_rangeSRestrict (f : R →+* S) (x : R) : (f.rangeSRestrict x : S) = f x :=
  rfl

theorem rangeSRestrict_surjective (f : R →+* S) : Function.Surjective f.rangeSRestrict :=
  fun ⟨_, hy⟩ =>
  let ⟨x, hx⟩ := mem_rangeS.mp hy
  ⟨x, Subtype.ext hx⟩

theorem rangeS_top_iff_surjective {f : R →+* S} :
    f.rangeS = (⊤ : Subsemiring S) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_rangeS, coe_top]) Set.range_iff_surjective

/-- The range of a surjective ring homomorphism is the whole of the codomain. -/
@[simp]
theorem rangeS_top_of_surjective (f : R →+* S) (hf : Function.Surjective f) :
    f.rangeS = (⊤ : Subsemiring S) :=
  rangeS_top_iff_surjective.2 hf

/-- The subsemiring of elements `x : R` such that `f x = g x` -/
def eqLocusS (f g : R →+* S) : Subsemiring R :=
  { (f : R →* S).eqLocusM g, (f : R →+ S).eqLocusM g with carrier := { x | f x = g x } }

@[simp]
theorem eqLocusS_same (f : R →+* S) : f.eqLocusS f = ⊤ :=
  SetLike.ext fun _ => eq_self_iff_true _

/-- If two ring homomorphisms are equal on a set, then they are equal on its subsemiring closure. -/
theorem eqOn_sclosure {f g : R →+* S} {s : Set R} (h : Set.EqOn f g s) : Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocusS g from closure_le.2 h

theorem eq_of_eqOn_stop {f g : R →+* S} (h : Set.EqOn f g (⊤ : Subsemiring R)) : f = g :=
  ext fun _ => h trivial

theorem eq_of_eqOn_sdense {s : Set R} (hs : closure s = ⊤) {f g : R →+* S} (h : s.EqOn f g) :
    f = g :=
  eq_of_eqOn_stop <| hs ▸ eqOn_sclosure h

theorem sclosure_preimage_le (f : R →+* S) (s : Set S) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _ hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

/-- The image under a ring homomorphism of the subsemiring generated by a set equals
the subsemiring generated by the image of the set. -/
theorem map_closureS (f : R →+* S) (s : Set R) : (closure s).map f = closure (f '' s) :=
  le_antisymm
    (map_le_iff_le_comap.2 <|
      le_trans (closure_mono <| Set.subset_preimage_image _ _) (sclosure_preimage_le _ _))
    (closure_le.2 <| Set.image_subset _ subset_closure)

end RingHom

namespace Subsemiring

open RingHom

/-- The ring homomorphism associated to an inclusion of subsemirings. -/
def inclusion {S T : Subsemiring R} (h : S ≤ T) : S →+* T :=
  S.subtype.codRestrict _ fun x => h x.2

@[simp]
theorem rangeS_subtype (s : Subsemiring R) : s.subtype.rangeS = s :=
  SetLike.coe_injective <| (coe_rangeS _).trans Subtype.range_coe

@[simp]
theorem range_fst : (fst R S).rangeS = ⊤ :=
  (fst R S).rangeS_top_of_surjective <| Prod.fst_surjective

@[simp]
theorem range_snd : (snd R S).rangeS = ⊤ :=
  (snd R S).rangeS_top_of_surjective <| Prod.snd_surjective

@[simp]
theorem prod_bot_sup_bot_prod (s : Subsemiring R) (t : Subsemiring S) :
    s.prod ⊥ ⊔ prod ⊥ t = s.prod t :=
  le_antisymm (sup_le (prod_mono_right s bot_le) (prod_mono_left t bot_le)) fun p hp =>
    Prod.fst_mul_snd p ▸
      mul_mem
        ((le_sup_left : s.prod ⊥ ≤ s.prod ⊥ ⊔ prod ⊥ t) ⟨hp.1, SetLike.mem_coe.2 <| one_mem ⊥⟩)
        ((le_sup_right : prod ⊥ t ≤ s.prod ⊥ ⊔ prod ⊥ t) ⟨SetLike.mem_coe.2 <| one_mem ⊥, hp.2⟩)

end Subsemiring

namespace RingEquiv

variable {s t : Subsemiring R}

/-- Makes the identity isomorphism from a proof two subsemirings of a multiplicative
    monoid are equal. -/
def subsemiringCongr (h : s = t) : s ≃+* t :=
  {
    Equiv.setCongr <| congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

/-- Restrict a ring homomorphism with a left inverse to a ring isomorphism to its
`RingHom.rangeS`. -/
def ofLeftInverseS {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f) : R ≃+* f.rangeS :=
  { f.rangeSRestrict with
    toFun := fun x => f.rangeSRestrict x
    invFun := fun x => (g ∘ f.rangeS.subtype) x
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := RingHom.mem_rangeS.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]
theorem ofLeftInverseS_apply {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f) (x : R) :
    ↑(ofLeftInverseS h x) = f x :=
  rfl

@[simp]
theorem ofLeftInverseS_symm_apply {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f)
    (x : f.rangeS) : (ofLeftInverseS h).symm x = g x :=
  rfl

/-- Given an equivalence `e : R ≃+* S` of semirings and a subsemiring `s` of `R`,
`subsemiring_map e s` is the induced equivalence between `s` and `s.map e` -/
@[simps!]
def subsemiringMap (e : R ≃+* S) (s : Subsemiring R) : s ≃+* s.map e.toRingHom :=
  { e.toAddEquiv.addSubmonoidMap s.toAddSubmonoid, e.toMulEquiv.submonoidMap s.toSubmonoid with }

-- These lemmas have always been bad (#7657), but lean4#2644 made `simp` start noticing
attribute [nolint simpNF] RingEquiv.subsemiringMap_symm_apply_coe RingEquiv.subsemiringMap_apply_coe

end RingEquiv

/-! ### Actions by `Subsemiring`s

These are just copies of the definitions about `Submonoid` starting from `submonoid.mul_action`.
The only new result is `subsemiring.module`.

When `R` is commutative, `Algebra.ofSubsemiring` provides a stronger result than those found in
this file, which uses the same scalar action.
-/


section Actions

namespace Subsemiring

variable {R' α β : Type*}

section NonAssocSemiring

variable [NonAssocSemiring R']

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance smul [SMul R' α] (S : Subsemiring R') : SMul S α :=
  S.toSubmonoid.smul

theorem smul_def [SMul R' α] {S : Subsemiring R'} (g : S) (m : α) : g • m = (g : R') • m :=
  rfl

instance smulCommClass_left [SMul R' β] [SMul α β] [SMulCommClass R' α β] (S : Subsemiring R') :
    SMulCommClass S α β :=
  S.toSubmonoid.smulCommClass_left

instance smulCommClass_right [SMul α β] [SMul R' β] [SMulCommClass α R' β] (S : Subsemiring R') :
    SMulCommClass α S β :=
  S.toSubmonoid.smulCommClass_right

/-- Note that this provides `IsScalarTower S R R` which is needed by `smul_mul_assoc`. -/
instance isScalarTower [SMul α β] [SMul R' α] [SMul R' β] [IsScalarTower R' α β]
    (S : Subsemiring R') :
    IsScalarTower S α β :=
  S.toSubmonoid.isScalarTower

instance faithfulSMul [SMul R' α] [FaithfulSMul R' α] (S : Subsemiring R') : FaithfulSMul S α :=
  S.toSubmonoid.faithfulSMul

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance [Zero α] [SMulWithZero R' α] (S : Subsemiring R') : SMulWithZero S α :=
  SMulWithZero.compHom _ S.subtype.toMonoidWithZeroHom.toZeroHom

end NonAssocSemiring

variable [Semiring R']

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance mulAction [MulAction R' α] (S : Subsemiring R') : MulAction S α :=
  S.toSubmonoid.mulAction

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance distribMulAction [AddMonoid α] [DistribMulAction R' α] (S : Subsemiring R') :
    DistribMulAction S α :=
  S.toSubmonoid.distribMulAction

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance mulDistribMulAction [Monoid α] [MulDistribMulAction R' α] (S : Subsemiring R') :
    MulDistribMulAction S α :=
  S.toSubmonoid.mulDistribMulAction

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance mulActionWithZero [Zero α] [MulActionWithZero R' α] (S : Subsemiring R') :
    MulActionWithZero S α :=
  MulActionWithZero.compHom _ S.subtype.toMonoidWithZeroHom

-- Porting note: instance named explicitly for use in `RingTheory/Subring/Basic`
/-- The action by a subsemiring is the action by the underlying semiring. -/
instance module [AddCommMonoid α] [Module R' α] (S : Subsemiring R') : Module S α :=
  -- Porting note: copying over the `smul` field causes a timeout
  -- { Module.compHom _ S.subtype with smul := (· • ·) }
  Module.compHom _ S.subtype

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance [Semiring α] [MulSemiringAction R' α] (S : Subsemiring R') : MulSemiringAction S α :=
  S.toSubmonoid.mulSemiringAction

/-- The center of a semiring acts commutatively on that semiring. -/
instance center.smulCommClass_left : SMulCommClass (center R') R' R' :=
  Submonoid.center.smulCommClass_left

/-- The center of a semiring acts commutatively on that semiring. -/
instance center.smulCommClass_right : SMulCommClass R' (center R') R' :=
  Submonoid.center.smulCommClass_right

/-- If all the elements of a set `s` commute, then `closure s` is a commutative monoid. -/
def closureCommSemiringOfComm {s : Set R'} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    CommSemiring (closure s) :=
  { (closure s).toSemiring with
    mul_comm := fun x y => by
      ext
      simp only [Subsemiring.coe_mul]
      refine
        closure_induction₂ x.prop y.prop hcomm (fun x => by simp only [zero_mul, mul_zero])
          (fun x => by simp only [zero_mul, mul_zero]) (fun x => by simp only [one_mul, mul_one])
          (fun x => by simp only [one_mul, mul_one])
          (fun x y z h₁ h₂ => by simp only [add_mul, mul_add, h₁, h₂])
          (fun x y z h₁ h₂ => by simp only [add_mul, mul_add, h₁, h₂])
          (fun x y z h₁ h₂ => by rw [mul_assoc, h₂, ← mul_assoc, h₁, mul_assoc]) fun x y z h₁ h₂ =>
          by rw [← mul_assoc, h₁, mul_assoc, h₂, ← mul_assoc] }

end Subsemiring

end Actions

namespace Subsemiring

theorem map_comap_eq (f : R →+* S) (t : Subsemiring S) : (t.comap f).map f = t ⊓ f.rangeS :=
  SetLike.coe_injective Set.image_preimage_eq_inter_range

theorem map_comap_eq_self
    {f : R →+* S} {t : Subsemiring S} (h : t ≤ f.rangeS) : (t.comap f).map f = t := by
  simpa only [inf_of_le_left h] using map_comap_eq f t

theorem map_comap_eq_self_of_surjective
    {f : R →+* S} (hf : Function.Surjective f) (t : Subsemiring S) : (t.comap f).map f = t :=
  map_comap_eq_self <| by simp [hf]

theorem comap_map_eq_self_of_injective
    {f : R →+* S} (hf : Function.Injective f) (s : Subsemiring R) : (s.map f).comap f = s :=
  SetLike.coe_injective (Set.preimage_image_eq _ hf)

end Subsemiring
