/-
Copyright (c) 2022 Jireh Loreaux All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.Set.Finite
import Mathlib.GroupTheory.Submonoid.Membership
import Mathlib.GroupTheory.Subsemigroup.Membership
import Mathlib.GroupTheory.Subsemigroup.Centralizer

#align_import ring_theory.non_unital_subsemiring.basic from "leanprover-community/mathlib"@"b915e9392ecb2a861e1e766f0e1df6ac481188ca"

/-!
# Bundled non-unital subsemirings

We define bundled non-unital subsemirings and some standard constructions:
`CompleteLattice` structure, `subtype` and `inclusion` ring homomorphisms, non-unital subsemiring
`map`, `comap` and range (`srange`) of a `NonUnitalRingHom` etc.
-/


open BigOperators

universe u v w

variable {R : Type u} {S : Type v} {T : Type w} [NonUnitalNonAssocSemiring R] (M : Subsemigroup R)

/-- `NonUnitalSubsemiringClass S R` states that `S` is a type of subsets `s ⊆ R` that
are both an additive submonoid and also a multiplicative subsemigroup. -/
class NonUnitalSubsemiringClass (S : Type*) (R : Type u) [NonUnitalNonAssocSemiring R]
  [SetLike S R] extends AddSubmonoidClass S R : Prop where
  mul_mem : ∀ {s : S} {a b : R}, a ∈ s → b ∈ s → a * b ∈ s
#align non_unital_subsemiring_class NonUnitalSubsemiringClass

-- See note [lower instance priority]
instance (priority := 100) NonUnitalSubsemiringClass.mulMemClass (S : Type*) (R : Type u)
    [NonUnitalNonAssocSemiring R] [SetLike S R] [h : NonUnitalSubsemiringClass S R] :
    MulMemClass S R :=
  { h with }
#align non_unital_subsemiring_class.mul_mem_class NonUnitalSubsemiringClass.mulMemClass

namespace NonUnitalSubsemiringClass

variable [SetLike S R] [NonUnitalSubsemiringClass S R] (s : S)

open AddSubmonoidClass

/- Prefer subclasses of `NonUnitalNonAssocSemiring` over subclasses of
`NonUnitalSubsemiringClass`. -/
/-- A non-unital subsemiring of a `NonUnitalNonAssocSemiring` inherits a
`NonUnitalNonAssocSemiring` structure -/
instance (priority := 75) toNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring s :=
  Subtype.coe_injective.nonUnitalNonAssocSemiring (↑) rfl (by simp) (fun _ _ => rfl) fun _ _ => rfl
                                                              -- 🎉 no goals
#align non_unital_subsemiring_class.to_non_unital_non_assoc_semiring NonUnitalSubsemiringClass.toNonUnitalNonAssocSemiring

instance noZeroDivisors [NoZeroDivisors R] : NoZeroDivisors s :=
  Subtype.coe_injective.noZeroDivisors (↑) rfl fun _ _ => rfl
#align non_unital_subsemiring_class.no_zero_divisors NonUnitalSubsemiringClass.noZeroDivisors

/-- The natural non-unital ring hom from a non-unital subsemiring of a non-unital semiring `R` to
`R`. -/
def subtype : s →ₙ+* R :=
  { AddSubmonoidClass.subtype s, MulMemClass.subtype s with toFun := (↑) }
#align non_unital_subsemiring_class.subtype NonUnitalSubsemiringClass.subtype

@[simp]
theorem coeSubtype : (subtype s : s → R) = ((↑) : s → R) :=
  rfl
#align non_unital_subsemiring_class.coe_subtype NonUnitalSubsemiringClass.coeSubtype

/-- A non-unital subsemiring of a `NonUnitalSemiring` is a `NonUnitalSemiring`. -/
instance toNonUnitalSemiring {R} [NonUnitalSemiring R] [SetLike S R]
    [NonUnitalSubsemiringClass S R] : NonUnitalSemiring s :=
  Subtype.coe_injective.nonUnitalSemiring (↑) rfl (by simp) (fun _ _ => rfl) fun _ _ => rfl
                                                      -- 🎉 no goals
#align non_unital_subsemiring_class.to_non_unital_semiring NonUnitalSubsemiringClass.toNonUnitalSemiring

/-- A non-unital subsemiring of a `NonUnitalCommSemiring` is a `NonUnitalCommSemiring`. -/
instance toNonUnitalCommSemiring {R} [NonUnitalCommSemiring R] [SetLike S R]
    [NonUnitalSubsemiringClass S R] : NonUnitalCommSemiring s :=
  Subtype.coe_injective.nonUnitalCommSemiring (↑) rfl (by simp) (fun _ _ => rfl) fun _ _ => rfl
                                                          -- 🎉 no goals
#align non_unital_subsemiring_class.to_non_unital_comm_semiring NonUnitalSubsemiringClass.toNonUnitalCommSemiring

/-! Note: currently, there are no ordered versions of non-unital rings. -/


end NonUnitalSubsemiringClass

variable [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring T]

/-- A non-unital subsemiring of a non-unital semiring `R` is a subset `s` that is both an additive
submonoid and a semigroup. -/
structure NonUnitalSubsemiring (R : Type u) [NonUnitalNonAssocSemiring R] extends AddSubmonoid R,
  Subsemigroup R
#align non_unital_subsemiring NonUnitalSubsemiring

/-- Reinterpret a `NonUnitalSubsemiring` as a `Subsemigroup`. -/
add_decl_doc NonUnitalSubsemiring.toSubsemigroup

/-- Reinterpret a `NonUnitalSubsemiring` as an `AddSubmonoid`. -/
add_decl_doc NonUnitalSubsemiring.toAddSubmonoid

namespace NonUnitalSubsemiring

instance : SetLike (NonUnitalSubsemiring R) R where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective' h
                             -- ⊢ { toAddSubmonoid := toAddSubmonoid✝, mul_mem' := mul_mem'✝ } = q
                                      -- ⊢ { toAddSubmonoid := toAddSubmonoid✝¹, mul_mem' := mul_mem'✝¹ } = { toAddSubm …
                                               -- ⊢ toAddSubmonoid✝¹ = toAddSubmonoid✝
                                                      -- 🎉 no goals

instance : NonUnitalSubsemiringClass (NonUnitalSubsemiring R) R where
  zero_mem {s} := AddSubmonoid.zero_mem' s.toAddSubmonoid
  add_mem {s} := AddSubsemigroup.add_mem' s.toAddSubmonoid.toAddSubsemigroup
  mul_mem {s} := mul_mem' s

theorem mem_carrier {s : NonUnitalSubsemiring R} {x : R} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl
#align non_unital_subsemiring.mem_carrier NonUnitalSubsemiring.mem_carrier

/-- Two non-unital subsemirings are equal if they have the same elements. -/
@[ext]
theorem ext {S T : NonUnitalSubsemiring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h
#align non_unital_subsemiring.ext NonUnitalSubsemiring.ext

/-- Copy of a non-unital subsemiring with a new `carrier` equal to the old one. Useful to fix
definitional equalities.-/
protected def copy (S : NonUnitalSubsemiring R) (s : Set R) (hs : s = ↑S) :
    NonUnitalSubsemiring R :=
  { S.toAddSubmonoid.copy s hs, S.toSubsemigroup.copy s hs with carrier := s }
#align non_unital_subsemiring.copy NonUnitalSubsemiring.copy

@[simp]
theorem coe_copy (S : NonUnitalSubsemiring R) (s : Set R) (hs : s = ↑S) :
    (S.copy s hs : Set R) = s :=
  rfl
#align non_unital_subsemiring.coe_copy NonUnitalSubsemiring.coe_copy

theorem copy_eq (S : NonUnitalSubsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs
#align non_unital_subsemiring.copy_eq NonUnitalSubsemiring.copy_eq

theorem toSubsemigroup_injective :
    Function.Injective (toSubsemigroup : NonUnitalSubsemiring R → Subsemigroup R)
  | _, _, h => ext (SetLike.ext_iff.mp h : _)
#align non_unital_subsemiring.to_subsemigroup_injective NonUnitalSubsemiring.toSubsemigroup_injective

@[mono]
theorem toSubsemigroup_strictMono :
    StrictMono (toSubsemigroup : NonUnitalSubsemiring R → Subsemigroup R) := fun _ _ => id
#align non_unital_subsemiring.to_subsemigroup_strict_mono NonUnitalSubsemiring.toSubsemigroup_strictMono

@[mono]
theorem toSubsemigroup_mono : Monotone (toSubsemigroup : NonUnitalSubsemiring R → Subsemigroup R) :=
  toSubsemigroup_strictMono.monotone
#align non_unital_subsemiring.to_subsemigroup_mono NonUnitalSubsemiring.toSubsemigroup_mono

theorem toAddSubmonoid_injective :
    Function.Injective (toAddSubmonoid : NonUnitalSubsemiring R → AddSubmonoid R)
  | _, _, h => ext (SetLike.ext_iff.mp h : _)
#align non_unital_subsemiring.to_add_submonoid_injective NonUnitalSubsemiring.toAddSubmonoid_injective

@[mono]
theorem toAddSubmonoid_strictMono :
    StrictMono (toAddSubmonoid : NonUnitalSubsemiring R → AddSubmonoid R) := fun _ _ => id
#align non_unital_subsemiring.to_add_submonoid_strict_mono NonUnitalSubsemiring.toAddSubmonoid_strictMono

@[mono]
theorem toAddSubmonoid_mono : Monotone (toAddSubmonoid : NonUnitalSubsemiring R → AddSubmonoid R) :=
  toAddSubmonoid_strictMono.monotone
#align non_unital_subsemiring.to_add_submonoid_mono NonUnitalSubsemiring.toAddSubmonoid_mono

/-- Construct a `NonUnitalSubsemiring R` from a set `s`, a subsemigroup `sg`, and an additive
submonoid `sa` such that `x ∈ s ↔ x ∈ sg ↔ x ∈ sa`. -/
protected def mk' (s : Set R) (sg : Subsemigroup R) (hg : ↑sg = s) (sa : AddSubmonoid R)
    (ha : ↑sa = s) : NonUnitalSubsemiring R where
  carrier := s
  zero_mem' := by subst ha; exact sa.zero_mem
                  -- ⊢ 0 ∈ { carrier := ↑sa, add_mem' := (_ : ∀ {a b : R}, a ∈ ↑sa → b ∈ ↑sa → a +  …
                 -- ⊢ ∀ {a b : R}, a ∈ ↑sa → b ∈ ↑sa → a + b ∈ ↑sa
                           -- 🎉 no goals
                            -- 🎉 no goals
  add_mem' := by subst ha; exact sa.add_mem
  mul_mem' := by subst hg; exact sg.mul_mem
                 -- ⊢ ∀ {a b : R}, a ∈ { toAddSubsemigroup := { carrier := ↑sg, add_mem' := (_ : ∀ …
                           -- 🎉 no goals
#align non_unital_subsemiring.mk' NonUnitalSubsemiring.mk'

@[simp]
theorem coe_mk' {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) : (NonUnitalSubsemiring.mk' s sg hg sa ha : Set R) = s :=
  rfl
#align non_unital_subsemiring.coe_mk' NonUnitalSubsemiring.coe_mk'

@[simp]
theorem mem_mk' {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) {x : R} : x ∈ NonUnitalSubsemiring.mk' s sg hg sa ha ↔ x ∈ s :=
  Iff.rfl
#align non_unital_subsemiring.mem_mk' NonUnitalSubsemiring.mem_mk'

@[simp]
theorem mk'_toSubsemigroup {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) : (NonUnitalSubsemiring.mk' s sg hg sa ha).toSubsemigroup = sg :=
  SetLike.coe_injective hg.symm
#align non_unital_subsemiring.mk'_to_subsemigroup NonUnitalSubsemiring.mk'_toSubsemigroup

@[simp]
theorem mk'_toAddSubmonoid {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) : (NonUnitalSubsemiring.mk' s sg hg sa ha).toAddSubmonoid = sa :=
  SetLike.coe_injective ha.symm
#align non_unital_subsemiring.mk'_to_add_submonoid NonUnitalSubsemiring.mk'_toAddSubmonoid

end NonUnitalSubsemiring

namespace NonUnitalSubsemiring

variable {F G : Type*} [NonUnitalRingHomClass F R S] [NonUnitalRingHomClass G S T]
  (s : NonUnitalSubsemiring R)

@[simp, norm_cast]
theorem coe_zero : ((0 : s) : R) = (0 : R) :=
  rfl
#align non_unital_subsemiring.coe_zero NonUnitalSubsemiring.coe_zero

@[simp, norm_cast]
theorem coe_add (x y : s) : ((x + y : s) : R) = (x + y : R) :=
  rfl
#align non_unital_subsemiring.coe_add NonUnitalSubsemiring.coe_add

@[simp, norm_cast]
theorem coe_mul (x y : s) : ((x * y : s) : R) = (x * y : R) :=
  rfl
#align non_unital_subsemiring.coe_mul NonUnitalSubsemiring.coe_mul

/-! Note: currently, there are no ordered versions of non-unital rings. -/


@[simp high]
theorem mem_toSubsemigroup {s : NonUnitalSubsemiring R} {x : R} : x ∈ s.toSubsemigroup ↔ x ∈ s :=
  Iff.rfl
#align non_unital_subsemiring.mem_to_subsemigroup NonUnitalSubsemiring.mem_toSubsemigroup

@[simp high]
theorem coe_toSubsemigroup (s : NonUnitalSubsemiring R) : (s.toSubsemigroup : Set R) = s :=
  rfl
#align non_unital_subsemiring.coe_to_subsemigroup NonUnitalSubsemiring.coe_toSubsemigroup

@[simp]
theorem mem_toAddSubmonoid {s : NonUnitalSubsemiring R} {x : R} : x ∈ s.toAddSubmonoid ↔ x ∈ s :=
  Iff.rfl
#align non_unital_subsemiring.mem_to_add_submonoid NonUnitalSubsemiring.mem_toAddSubmonoid

@[simp]
theorem coe_toAddSubmonoid (s : NonUnitalSubsemiring R) : (s.toAddSubmonoid : Set R) = s :=
  rfl
#align non_unital_subsemiring.coe_to_add_submonoid NonUnitalSubsemiring.coe_toAddSubmonoid

/-- The non-unital subsemiring `R` of the non-unital semiring `R`. -/
instance : Top (NonUnitalSubsemiring R) :=
  ⟨{ (⊤ : Subsemigroup R), (⊤ : AddSubmonoid R) with }⟩

@[simp]
theorem mem_top (x : R) : x ∈ (⊤ : NonUnitalSubsemiring R) :=
  Set.mem_univ x
#align non_unital_subsemiring.mem_top NonUnitalSubsemiring.mem_top

@[simp]
theorem coe_top : ((⊤ : NonUnitalSubsemiring R) : Set R) = Set.univ :=
  rfl
#align non_unital_subsemiring.coe_top NonUnitalSubsemiring.coe_top

/-- The ring equiv between the top element of `NonUnitalSubsemiring R` and `R`. -/
@[simps!]
def topEquiv : (⊤ : NonUnitalSubsemiring R) ≃+* R :=
  { Subsemigroup.topEquiv, AddSubmonoid.topEquiv with }

/-- The preimage of a non-unital subsemiring along a non-unital ring homomorphism is a
non-unital subsemiring. -/
def comap (f : F) (s : NonUnitalSubsemiring S) : NonUnitalSubsemiring R :=
  { s.toSubsemigroup.comap (f : MulHom R S), s.toAddSubmonoid.comap (f : R →+ S) with
    carrier := f ⁻¹' s }
#align non_unital_subsemiring.comap NonUnitalSubsemiring.comap

@[simp]
theorem coe_comap (s : NonUnitalSubsemiring S) (f : F) : (s.comap f : Set R) = f ⁻¹' s :=
  rfl
#align non_unital_subsemiring.coe_comap NonUnitalSubsemiring.coe_comap

@[simp]
theorem mem_comap {s : NonUnitalSubsemiring S} {f : F} {x : R} : x ∈ s.comap f ↔ f x ∈ s :=
  Iff.rfl
#align non_unital_subsemiring.mem_comap NonUnitalSubsemiring.mem_comap

-- this has some nasty coercions, how to deal with it?
theorem comap_comap (s : NonUnitalSubsemiring T) (g : G) (f : F) :
    ((s.comap g : NonUnitalSubsemiring S).comap f : NonUnitalSubsemiring R) =
      s.comap ((g : S →ₙ+* T).comp (f : R →ₙ+* S)) :=
  rfl
#align non_unital_subsemiring.comap_comap NonUnitalSubsemiring.comap_comap

/-- The image of a non-unital subsemiring along a ring homomorphism is a non-unital subsemiring. -/
def map (f : F) (s : NonUnitalSubsemiring R) : NonUnitalSubsemiring S :=
  { s.toSubsemigroup.map (f : R →ₙ* S), s.toAddSubmonoid.map (f : R →+ S) with carrier := f '' s }
#align non_unital_subsemiring.map NonUnitalSubsemiring.map

@[simp]
theorem coe_map (f : F) (s : NonUnitalSubsemiring R) : (s.map f : Set S) = f '' s :=
  rfl
#align non_unital_subsemiring.coe_map NonUnitalSubsemiring.coe_map

@[simp]
theorem mem_map {f : F} {s : NonUnitalSubsemiring R} {y : S} : y ∈ s.map f ↔ ∃ x ∈ s, f x = y := by
  convert Set.mem_image_iff_bex
  -- ⊢ x✝ ∈ s ∧ ↑f x✝ = y ↔ ∃ x, ↑f x✝ = y
  simp
  -- 🎉 no goals
#align non_unital_subsemiring.mem_map NonUnitalSubsemiring.mem_map

@[simp]
theorem map_id : s.map (NonUnitalRingHom.id R) = s :=
  SetLike.coe_injective <| Set.image_id _
#align non_unital_subsemiring.map_id NonUnitalSubsemiring.map_id

-- unavoidable coercions?
theorem map_map (g : G) (f : F) :
    (s.map (f : R →ₙ+* S)).map (g : S →ₙ+* T) = s.map ((g : S →ₙ+* T).comp (f : R →ₙ+* S)) :=
  SetLike.coe_injective <| Set.image_image _ _ _
#align non_unital_subsemiring.map_map NonUnitalSubsemiring.map_map

theorem map_le_iff_le_comap {f : F} {s : NonUnitalSubsemiring R} {t : NonUnitalSubsemiring S} :
    s.map f ≤ t ↔ s ≤ t.comap f :=
  Set.image_subset_iff
#align non_unital_subsemiring.map_le_iff_le_comap NonUnitalSubsemiring.map_le_iff_le_comap

theorem gc_map_comap (f : F) :
    @GaloisConnection (NonUnitalSubsemiring R) (NonUnitalSubsemiring S) _ _ (map f) (comap f) :=
  fun _ _ => map_le_iff_le_comap
#align non_unital_subsemiring.gc_map_comap NonUnitalSubsemiring.gc_map_comap

/-- A non-unital subsemiring is isomorphic to its image under an injective function -/
noncomputable def equivMapOfInjective (f : F) (hf : Function.Injective (f : R → S)) :
    s ≃+* s.map f :=
  { Equiv.Set.image f s hf with
    map_mul' := fun _ _ => Subtype.ext (map_mul f _ _)
    map_add' := fun _ _ => Subtype.ext (map_add f _ _) }
#align non_unital_subsemiring.equiv_map_of_injective NonUnitalSubsemiring.equivMapOfInjective

@[simp]
theorem coe_equivMapOfInjective_apply (f : F) (hf : Function.Injective f) (x : s) :
    (equivMapOfInjective s f hf x : S) = f x :=
  rfl
#align non_unital_subsemiring.coe_equiv_map_of_injective_apply NonUnitalSubsemiring.coe_equivMapOfInjective_apply

end NonUnitalSubsemiring

namespace NonUnitalRingHom

open NonUnitalSubsemiring

variable {F G : Type*} [NonUnitalRingHomClass F R S] [NonUnitalRingHomClass G S T] (f : F) (g : G)

/-- The range of a non-unital ring homomorphism is a non-unital subsemiring.
See note [range copy pattern]. -/
def srange : NonUnitalSubsemiring S :=
  ((⊤ : NonUnitalSubsemiring R).map (f : R →ₙ+* S)).copy (Set.range f) Set.image_univ.symm
#align non_unital_ring_hom.srange NonUnitalRingHom.srange

@[simp]
theorem coe_srange : (@srange R S _ _ _ _ f : Set S) = Set.range f :=
  rfl
#align non_unital_ring_hom.coe_srange NonUnitalRingHom.coe_srange

@[simp]
theorem mem_srange {f : F} {y : S} : y ∈ @srange R S _ _ _ _ f ↔ ∃ x, f x = y :=
  Iff.rfl
#align non_unital_ring_hom.mem_srange NonUnitalRingHom.mem_srange

theorem srange_eq_map : @srange R S _ _ _ _ f = (⊤ : NonUnitalSubsemiring R).map f := by
  ext
  -- ⊢ x✝ ∈ srange f ↔ x✝ ∈ map f ⊤
  simp
  -- 🎉 no goals
#align non_unital_ring_hom.srange_eq_map NonUnitalRingHom.srange_eq_map

theorem mem_srange_self (f : F) (x : R) : f x ∈ @srange R S _ _ _ _ f :=
  mem_srange.mpr ⟨x, rfl⟩
#align non_unital_ring_hom.mem_srange_self NonUnitalRingHom.mem_srange_self

theorem map_srange (g : S →ₙ+* T) (f : R →ₙ+* S) : map g (srange f) = srange (g.comp f) := by
  simpa only [srange_eq_map] using (⊤ : NonUnitalSubsemiring R).map_map g f
  -- 🎉 no goals
#align non_unital_ring_hom.map_srange NonUnitalRingHom.map_srange

/-- The range of a morphism of non-unital semirings is finite if the domain is a finite. -/
instance finite_srange [Finite R] (f : F) : Finite (srange f : NonUnitalSubsemiring S) :=
  (Set.finite_range f).to_subtype
#align non_unital_ring_hom.finite_srange NonUnitalRingHom.finite_srange

end NonUnitalRingHom

namespace NonUnitalSubsemiring

-- should we define this as the range of the zero homomorphism?
instance : Bot (NonUnitalSubsemiring R) :=
  ⟨{  carrier := {0}
      add_mem' := fun _ _ => by simp_all
                                -- 🎉 no goals
      zero_mem' := Set.mem_singleton 0
      mul_mem' := fun _ _ => by simp_all }⟩
                                -- 🎉 no goals

instance : Inhabited (NonUnitalSubsemiring R) :=
  ⟨⊥⟩

theorem coe_bot : ((⊥ : NonUnitalSubsemiring R) : Set R) = {0} :=
  rfl
#align non_unital_subsemiring.coe_bot NonUnitalSubsemiring.coe_bot

theorem mem_bot {x : R} : x ∈ (⊥ : NonUnitalSubsemiring R) ↔ x = 0 :=
  Set.mem_singleton_iff
#align non_unital_subsemiring.mem_bot NonUnitalSubsemiring.mem_bot

/-- The inf of two non-unital subsemirings is their intersection. -/
instance : Inf (NonUnitalSubsemiring R) :=
  ⟨fun s t =>
    { s.toSubsemigroup ⊓ t.toSubsemigroup, s.toAddSubmonoid ⊓ t.toAddSubmonoid with
      carrier := s ∩ t }⟩

@[simp]
theorem coe_inf (p p' : NonUnitalSubsemiring R) :
    ((p ⊓ p' : NonUnitalSubsemiring R) : Set R) = (p : Set R) ∩ p' :=
  rfl
#align non_unital_subsemiring.coe_inf NonUnitalSubsemiring.coe_inf

@[simp]
theorem mem_inf {p p' : NonUnitalSubsemiring R} {x : R} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl
#align non_unital_subsemiring.mem_inf NonUnitalSubsemiring.mem_inf

instance : InfSet (NonUnitalSubsemiring R) :=
  ⟨fun s =>
    NonUnitalSubsemiring.mk' (⋂ t ∈ s, ↑t) (⨅ t ∈ s, NonUnitalSubsemiring.toSubsemigroup t)
      (by simp) (⨅ t ∈ s, NonUnitalSubsemiring.toAddSubmonoid t) (by simp)⟩
          -- 🎉 no goals
                                                                     -- 🎉 no goals

@[simp, norm_cast]
theorem coe_sInf (S : Set (NonUnitalSubsemiring R)) :
    ((sInf S : NonUnitalSubsemiring R) : Set R) = ⋂ s ∈ S, ↑s :=
  rfl
#align non_unital_subsemiring.coe_Inf NonUnitalSubsemiring.coe_sInf

theorem mem_sInf {S : Set (NonUnitalSubsemiring R)} {x : R} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂
#align non_unital_subsemiring.mem_Inf NonUnitalSubsemiring.mem_sInf

@[simp]
theorem sInf_toSubsemigroup (s : Set (NonUnitalSubsemiring R)) :
    (sInf s).toSubsemigroup = ⨅ t ∈ s, NonUnitalSubsemiring.toSubsemigroup t :=
  mk'_toSubsemigroup _ _
#align non_unital_subsemiring.Inf_to_subsemigroup NonUnitalSubsemiring.sInf_toSubsemigroup

@[simp]
theorem sInf_toAddSubmonoid (s : Set (NonUnitalSubsemiring R)) :
    (sInf s).toAddSubmonoid = ⨅ t ∈ s, NonUnitalSubsemiring.toAddSubmonoid t :=
  mk'_toAddSubmonoid _ _
#align non_unital_subsemiring.Inf_to_add_submonoid NonUnitalSubsemiring.sInf_toAddSubmonoid

/-- Non-unital subsemirings of a non-unital semiring form a complete lattice. -/
instance : CompleteLattice (NonUnitalSubsemiring R) :=
  { completeLatticeOfInf (NonUnitalSubsemiring R)
      fun _ => IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf with
    bot := ⊥
    bot_le := fun s _ hx => (mem_bot.mp hx).symm ▸ zero_mem s
    top := ⊤
    le_top := fun _ _ _ => trivial
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right
    le_inf := fun _ _ _ h₁ h₂ _ hx => ⟨h₁ hx, h₂ hx⟩ }

theorem eq_top_iff' (A : NonUnitalSubsemiring R) : A = ⊤ ↔ ∀ x : R, x ∈ A :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩
#align non_unital_subsemiring.eq_top_iff' NonUnitalSubsemiring.eq_top_iff'

section Center

/-- The center of a semiring `R` is the set of elements that commute with everything in `R` -/
def center (R) [NonUnitalSemiring R] : NonUnitalSubsemiring R :=
  { Subsemigroup.center R with
    carrier := Set.center R
    zero_mem' := Set.zero_mem_center R
    add_mem' := Set.add_mem_center }
#align non_unital_subsemiring.center NonUnitalSubsemiring.center

theorem coe_center (R) [NonUnitalSemiring R] : ↑(center R) = Set.center R :=
  rfl
#align non_unital_subsemiring.coe_center NonUnitalSubsemiring.coe_center

@[simp]
theorem center_toSubsemigroup (R) [NonUnitalSemiring R] :
    (center R).toSubsemigroup = Subsemigroup.center R :=
  rfl
#align non_unital_subsemiring.center_to_subsemigroup NonUnitalSubsemiring.center_toSubsemigroup

theorem mem_center_iff {R} [NonUnitalSemiring R] {z : R} : z ∈ center R ↔ ∀ g, g * z = z * g :=
  Iff.rfl
#align non_unital_subsemiring.mem_center_iff NonUnitalSubsemiring.mem_center_iff

instance decidableMemCenter {R} [NonUnitalSemiring R] [DecidableEq R] [Fintype R] :
    DecidablePred (· ∈ center R) := fun _ => decidable_of_iff' _ mem_center_iff
#align non_unital_subsemiring.decidable_mem_center NonUnitalSubsemiring.decidableMemCenter

@[simp]
theorem center_eq_top (R) [NonUnitalCommSemiring R] : center R = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ R)
#align non_unital_subsemiring.center_eq_top NonUnitalSubsemiring.center_eq_top

/-- The center is commutative. -/
instance center.instNonUnitalCommSemiring {R} [NonUnitalSemiring R] :
    NonUnitalCommSemiring (center R) :=
  { Subsemigroup.center.commSemigroup,
    NonUnitalSubsemiringClass.toNonUnitalSemiring (center R) with }

end Center

section Centralizer

/-- The centralizer of a set as non-unital subsemiring. -/
def centralizer {R} [NonUnitalSemiring R] (s : Set R) : NonUnitalSubsemiring R :=
  { Subsemigroup.centralizer s with
    carrier := s.centralizer
    zero_mem' := Set.zero_mem_centralizer _
    add_mem' := Set.add_mem_centralizer }
#align non_unital_subsemiring.centralizer NonUnitalSubsemiring.centralizer

@[simp, norm_cast]
theorem coe_centralizer {R} [NonUnitalSemiring R] (s : Set R) :
    (centralizer s : Set R) = s.centralizer :=
  rfl
#align non_unital_subsemiring.coe_centralizer NonUnitalSubsemiring.coe_centralizer

theorem centralizer_toSubsemigroup {R} [NonUnitalSemiring R] (s : Set R) :
    (centralizer s).toSubsemigroup = Subsemigroup.centralizer s :=
  rfl
#align non_unital_subsemiring.centralizer_to_subsemigroup NonUnitalSubsemiring.centralizer_toSubsemigroup

theorem mem_centralizer_iff {R} [NonUnitalSemiring R] {s : Set R} {z : R} :
    z ∈ centralizer s ↔ ∀ g ∈ s, g * z = z * g :=
  Iff.rfl
#align non_unital_subsemiring.mem_centralizer_iff NonUnitalSubsemiring.mem_centralizer_iff

theorem center_le_centralizer {R} [NonUnitalSemiring R] (s) : center R ≤ centralizer s :=
  s.center_subset_centralizer
#align non_unital_subsemiring.center_le_centralizer NonUnitalSubsemiring.center_le_centralizer

theorem centralizer_le {R} [NonUnitalSemiring R] (s t : Set R) (h : s ⊆ t) :
    centralizer t ≤ centralizer s :=
  Set.centralizer_subset h
#align non_unital_subsemiring.centralizer_le NonUnitalSubsemiring.centralizer_le

@[simp]
theorem centralizer_eq_top_iff_subset {R} [NonUnitalSemiring R] {s : Set R} :
    centralizer s = ⊤ ↔ s ⊆ center R :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset
#align non_unital_subsemiring.centralizer_eq_top_iff_subset NonUnitalSubsemiring.centralizer_eq_top_iff_subset

@[simp]
theorem centralizer_univ {R} [NonUnitalSemiring R] : centralizer Set.univ = center R :=
  SetLike.ext' (Set.centralizer_univ R)
#align non_unital_subsemiring.centralizer_univ NonUnitalSubsemiring.centralizer_univ

end Centralizer

/-- The `NonUnitalSubsemiring` generated by a set. -/
def closure (s : Set R) : NonUnitalSubsemiring R :=
  sInf { S | s ⊆ S }
#align non_unital_subsemiring.closure NonUnitalSubsemiring.closure

theorem mem_closure {x : R} {s : Set R} :
    x ∈ closure s ↔ ∀ S : NonUnitalSubsemiring R, s ⊆ S → x ∈ S :=
  mem_sInf
#align non_unital_subsemiring.mem_closure NonUnitalSubsemiring.mem_closure

/-- The non-unital subsemiring generated by a set includes the set. -/
@[simp]
theorem subset_closure {s : Set R} : s ⊆ closure s := fun _ hx => mem_closure.2 fun _ hS => hS hx
#align non_unital_subsemiring.subset_closure NonUnitalSubsemiring.subset_closure

theorem not_mem_of_not_mem_closure {s : Set R} {P : R} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)
#align non_unital_subsemiring.not_mem_of_not_mem_closure NonUnitalSubsemiring.not_mem_of_not_mem_closure

/-- A non-unital subsemiring `S` includes `closure s` if and only if it includes `s`. -/
@[simp]
theorem closure_le {s : Set R} {t : NonUnitalSubsemiring R} : closure s ≤ t ↔ s ⊆ t :=
  ⟨Set.Subset.trans subset_closure, fun h => sInf_le h⟩
#align non_unital_subsemiring.closure_le NonUnitalSubsemiring.closure_le

/-- Subsemiring closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
theorem closure_mono ⦃s t : Set R⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Set.Subset.trans h subset_closure
#align non_unital_subsemiring.closure_mono NonUnitalSubsemiring.closure_mono

theorem closure_eq_of_le {s : Set R} {t : NonUnitalSubsemiring R} (h₁ : s ⊆ t)
    (h₂ : t ≤ closure s) : closure s = t :=
  le_antisymm (closure_le.2 h₁) h₂
#align non_unital_subsemiring.closure_eq_of_le NonUnitalSubsemiring.closure_eq_of_le

theorem mem_map_equiv {f : R ≃+* S} {K : NonUnitalSubsemiring R} {x : S} :
    x ∈ K.map (f : R →ₙ+* S) ↔ f.symm x ∈ K := by
  convert @Set.mem_image_equiv _ _ (↑K) f.toEquiv x
  -- 🎉 no goals
#align non_unital_subsemiring.mem_map_equiv NonUnitalSubsemiring.mem_map_equiv

theorem map_equiv_eq_comap_symm (f : R ≃+* S) (K : NonUnitalSubsemiring R) :
    K.map (f : R →ₙ+* S) = K.comap f.symm :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage K)
#align non_unital_subsemiring.map_equiv_eq_comap_symm NonUnitalSubsemiring.map_equiv_eq_comap_symm

theorem comap_equiv_eq_map_symm (f : R ≃+* S) (K : NonUnitalSubsemiring S) :
    K.comap (f : R →ₙ+* S) = K.map f.symm :=
  (map_equiv_eq_comap_symm f.symm K).symm
#align non_unital_subsemiring.comap_equiv_eq_map_symm NonUnitalSubsemiring.comap_equiv_eq_map_symm

end NonUnitalSubsemiring

namespace Subsemigroup

/-- The additive closure of a non-unital subsemigroup is a non-unital subsemiring. -/
def nonUnitalSubsemiringClosure (M : Subsemigroup R) : NonUnitalSubsemiring R :=
  { AddSubmonoid.closure (M : Set R) with mul_mem' := MulMemClass.mul_mem_add_closure }
#align subsemigroup.non_unital_subsemiring_closure Subsemigroup.nonUnitalSubsemiringClosure

theorem nonUnitalSubsemiringClosure_coe :
    (M.nonUnitalSubsemiringClosure : Set R) = AddSubmonoid.closure (M : Set R) :=
  rfl
#align subsemigroup.non_unital_subsemiring_closure_coe Subsemigroup.nonUnitalSubsemiringClosure_coe

theorem nonUnitalSubsemiringClosure_toAddSubmonoid :
    M.nonUnitalSubsemiringClosure.toAddSubmonoid = AddSubmonoid.closure (M : Set R) :=
  rfl
#align subsemigroup.non_unital_subsemiring_closure_to_add_submonoid Subsemigroup.nonUnitalSubsemiringClosure_toAddSubmonoid

/-- The `NonUnitalSubsemiring` generated by a multiplicative subsemigroup coincides with the
`NonUnitalSubsemiring.closure` of the subsemigroup itself . -/
theorem nonUnitalSubsemiringClosure_eq_closure :
    M.nonUnitalSubsemiringClosure = NonUnitalSubsemiring.closure (M : Set R) := by
  ext
  -- ⊢ x✝ ∈ nonUnitalSubsemiringClosure M ↔ x✝ ∈ NonUnitalSubsemiring.closure ↑M
  refine ⟨fun hx => ?_,
    fun hx => (NonUnitalSubsemiring.mem_closure.mp hx) M.nonUnitalSubsemiringClosure fun s sM => ?_⟩
  <;> rintro - ⟨H1, rfl⟩
      -- ⊢ x✝ ∈ (fun t => ⋂ (_ : t ∈ {S | ↑M ⊆ ↑S}), ↑t) H1
      -- ⊢ s ∈ (fun t => ⋂ (_ : t ∈ {S | ↑M ⊆ ↑S}), ↑t) H1
  <;> rintro - ⟨H2, rfl⟩
      -- ⊢ x✝ ∈ (fun h => ↑H1) H2
      -- ⊢ s ∈ (fun h => ↑H1) H2
  · exact AddSubmonoid.mem_closure.mp hx H1.toAddSubmonoid H2
    -- 🎉 no goals
  · exact H2 sM
    -- 🎉 no goals
#align subsemigroup.non_unital_subsemiring_closure_eq_closure Subsemigroup.nonUnitalSubsemiringClosure_eq_closure

end Subsemigroup

namespace NonUnitalSubsemiring

@[simp]
theorem closure_subsemigroup_closure (s : Set R) : closure ↑(Subsemigroup.closure s) = closure s :=
  le_antisymm
    (closure_le.mpr fun _ hy =>
      (Subsemigroup.mem_closure.mp hy) (closure s).toSubsemigroup subset_closure)
    (closure_mono Subsemigroup.subset_closure)
#align non_unital_subsemiring.closure_subsemigroup_closure NonUnitalSubsemiring.closure_subsemigroup_closure

/-- The elements of the non-unital subsemiring closure of `M` are exactly the elements of the
additive closure of a multiplicative subsemigroup `M`. -/
theorem coe_closure_eq (s : Set R) :
    (closure s : Set R) = AddSubmonoid.closure (Subsemigroup.closure s : Set R) := by
  simp [← Subsemigroup.nonUnitalSubsemiringClosure_toAddSubmonoid,
    Subsemigroup.nonUnitalSubsemiringClosure_eq_closure]
#align non_unital_subsemiring.coe_closure_eq NonUnitalSubsemiring.coe_closure_eq

theorem mem_closure_iff {s : Set R} {x} :
    x ∈ closure s ↔ x ∈ AddSubmonoid.closure (Subsemigroup.closure s : Set R) :=
  Set.ext_iff.mp (coe_closure_eq s) x
#align non_unital_subsemiring.mem_closure_iff NonUnitalSubsemiring.mem_closure_iff

@[simp]
theorem closure_addSubmonoid_closure {s : Set R} :
    closure ↑(AddSubmonoid.closure s) = closure s := by
  ext x
  -- ⊢ x ∈ closure ↑(AddSubmonoid.closure s) ↔ x ∈ closure s
  refine' ⟨fun hx => _, fun hx => closure_mono AddSubmonoid.subset_closure hx⟩
  -- ⊢ x ∈ closure s
  rintro - ⟨H, rfl⟩
  -- ⊢ x ∈ (fun t => ⋂ (_ : t ∈ {S | s ⊆ ↑S}), ↑t) H
  rintro - ⟨J, rfl⟩
  -- ⊢ x ∈ (fun h => ↑H) J
  refine' (AddSubmonoid.mem_closure.mp (mem_closure_iff.mp hx)) H.toAddSubmonoid fun y hy => _
  -- ⊢ y ∈ ↑H.toAddSubmonoid
  refine' (Subsemigroup.mem_closure.mp hy) H.toSubsemigroup fun z hz => _
  -- ⊢ z ∈ ↑(toSubsemigroup H)
  exact (AddSubmonoid.mem_closure.mp hz) H.toAddSubmonoid fun w hw => J hw
  -- 🎉 no goals
#align non_unital_subsemiring.closure_add_submonoid_closure NonUnitalSubsemiring.closure_addSubmonoid_closure

/-- An induction principle for closure membership. If `p` holds for `0`, `1`, and all elements
of `s`, and is preserved under addition and multiplication, then `p` holds for all elements
of the closure of `s`. -/
@[elab_as_elim]
theorem closure_induction {s : Set R} {p : R → Prop} {x} (h : x ∈ closure s) (Hs : ∀ x ∈ s, p x)
    (H0 : p 0) (Hadd : ∀ x y, p x → p y → p (x + y)) (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
  (@closure_le _ _ _ ⟨⟨⟨p, fun {a b} => Hadd a b⟩, H0⟩, fun {a b} => Hmul a b⟩).2 Hs h
#align non_unital_subsemiring.closure_induction NonUnitalSubsemiring.closure_induction

/-- An induction principle for closure membership for predicates with two arguments. -/
@[elab_as_elim]
theorem closure_induction₂ {s : Set R} {p : R → R → Prop} {x} {y : R} (hx : x ∈ closure s)
    (hy : y ∈ closure s) (Hs : ∀ x ∈ s, ∀ y ∈ s, p x y) (H0_left : ∀ x, p 0 x)
    (H0_right : ∀ x, p x 0) (Hadd_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ + x₂) y)
    (Hadd_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ + y₂))
    (Hmul_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ * x₂) y)
    (Hmul_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ * y₂)) : p x y :=
  closure_induction hx
    (fun x₁ x₁s => closure_induction hy (Hs x₁ x₁s) (H0_right x₁) (Hadd_right x₁) (Hmul_right x₁))
    (H0_left y) (fun z z' => Hadd_left z z' y) fun z z' => Hmul_left z z' y
#align non_unital_subsemiring.closure_induction₂ NonUnitalSubsemiring.closure_induction₂

variable (R)

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : GaloisInsertion (@closure R _) (↑) where
  choice s _ := closure s
  gc _ _ := closure_le
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl
#align non_unital_subsemiring.gi NonUnitalSubsemiring.gi

variable {R}
variable {F : Type*} [NonUnitalRingHomClass F R S]

/-- Closure of a non-unital subsemiring `S` equals `S`. -/
theorem closure_eq (s : NonUnitalSubsemiring R) : closure (s : Set R) = s :=
  (NonUnitalSubsemiring.gi R).l_u_eq s
#align non_unital_subsemiring.closure_eq NonUnitalSubsemiring.closure_eq

@[simp]
theorem closure_empty : closure (∅ : Set R) = ⊥ :=
  (NonUnitalSubsemiring.gi R).gc.l_bot
#align non_unital_subsemiring.closure_empty NonUnitalSubsemiring.closure_empty

@[simp]
theorem closure_univ : closure (Set.univ : Set R) = ⊤ :=
  @coe_top R _ ▸ closure_eq ⊤
#align non_unital_subsemiring.closure_univ NonUnitalSubsemiring.closure_univ

theorem closure_union (s t : Set R) : closure (s ∪ t) = closure s ⊔ closure t :=
  (NonUnitalSubsemiring.gi R).gc.l_sup
#align non_unital_subsemiring.closure_union NonUnitalSubsemiring.closure_union

theorem closure_iUnion {ι} (s : ι → Set R) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (NonUnitalSubsemiring.gi R).gc.l_iSup
#align non_unital_subsemiring.closure_Union NonUnitalSubsemiring.closure_iUnion

theorem closure_sUnion (s : Set (Set R)) : closure (⋃₀ s) = ⨆ t ∈ s, closure t :=
  (NonUnitalSubsemiring.gi R).gc.l_sSup
#align non_unital_subsemiring.closure_sUnion NonUnitalSubsemiring.closure_sUnion

theorem map_sup (s t : NonUnitalSubsemiring R) (f : F) :
    (map f (s ⊔ t) : NonUnitalSubsemiring S) = map f s ⊔ map f t :=
  @GaloisConnection.l_sup _ _ s t _ _ _ _ (gc_map_comap f)
#align non_unital_subsemiring.map_sup NonUnitalSubsemiring.map_sup

theorem map_iSup {ι : Sort*} (f : F) (s : ι → NonUnitalSubsemiring R) :
    (map f (iSup s) : NonUnitalSubsemiring S) = ⨆ i, map f (s i) :=
  @GaloisConnection.l_iSup _ _ _ _ _ _ _ (gc_map_comap f) s
#align non_unital_subsemiring.map_supr NonUnitalSubsemiring.map_iSup

theorem comap_inf (s t : NonUnitalSubsemiring S) (f : F) :
    (comap f (s ⊓ t) : NonUnitalSubsemiring R) = comap f s ⊓ comap f t :=
  @GaloisConnection.u_inf _ _ s t _ _ _ _ (gc_map_comap f)
#align non_unital_subsemiring.comap_inf NonUnitalSubsemiring.comap_inf

theorem comap_iInf {ι : Sort*} (f : F) (s : ι → NonUnitalSubsemiring S) :
    (comap f (iInf s) : NonUnitalSubsemiring R) = ⨅ i, comap f (s i) :=
  @GaloisConnection.u_iInf _ _ _ _ _ _ _ (gc_map_comap f) s
#align non_unital_subsemiring.comap_infi NonUnitalSubsemiring.comap_iInf

@[simp]
theorem map_bot (f : F) : map f (⊥ : NonUnitalSubsemiring R) = (⊥ : NonUnitalSubsemiring S) :=
  (gc_map_comap f).l_bot
#align non_unital_subsemiring.map_bot NonUnitalSubsemiring.map_bot

@[simp]
theorem comap_top (f : F) : comap f (⊤ : NonUnitalSubsemiring S) = (⊤ : NonUnitalSubsemiring R) :=
  (gc_map_comap f).u_top
#align non_unital_subsemiring.comap_top NonUnitalSubsemiring.comap_top

/-- Given `NonUnitalSubsemiring`s `s`, `t` of semirings `R`, `S` respectively, `s.prod t` is
`s × t` as a non-unital subsemiring of `R × S`. -/
def prod (s : NonUnitalSubsemiring R) (t : NonUnitalSubsemiring S) : NonUnitalSubsemiring (R × S) :=
  { s.toSubsemigroup.prod t.toSubsemigroup, s.toAddSubmonoid.prod t.toAddSubmonoid with
    carrier := (s : Set R) ×ˢ (t : Set S) }
#align non_unital_subsemiring.prod NonUnitalSubsemiring.prod

@[norm_cast]
theorem coe_prod (s : NonUnitalSubsemiring R) (t : NonUnitalSubsemiring S) :
    (s.prod t : Set (R × S)) = (s : Set R) ×ˢ (t : Set S) :=
  rfl
#align non_unital_subsemiring.coe_prod NonUnitalSubsemiring.coe_prod

theorem mem_prod {s : NonUnitalSubsemiring R} {t : NonUnitalSubsemiring S} {p : R × S} :
    p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl
#align non_unital_subsemiring.mem_prod NonUnitalSubsemiring.mem_prod

@[mono]
theorem prod_mono ⦃s₁ s₂ : NonUnitalSubsemiring R⦄ (hs : s₁ ≤ s₂) ⦃t₁ t₂ : NonUnitalSubsemiring S⦄
    (ht : t₁ ≤ t₂) : s₁.prod t₁ ≤ s₂.prod t₂ :=
  Set.prod_mono hs ht
#align non_unital_subsemiring.prod_mono NonUnitalSubsemiring.prod_mono

theorem prod_mono_right (s : NonUnitalSubsemiring R) :
    Monotone fun t : NonUnitalSubsemiring S => s.prod t :=
  prod_mono (le_refl s)
#align non_unital_subsemiring.prod_mono_right NonUnitalSubsemiring.prod_mono_right

theorem prod_mono_left (t : NonUnitalSubsemiring S) :
    Monotone fun s : NonUnitalSubsemiring R => s.prod t := fun _ _ hs => prod_mono hs (le_refl t)
#align non_unital_subsemiring.prod_mono_left NonUnitalSubsemiring.prod_mono_left

theorem prod_top (s : NonUnitalSubsemiring R) :
    s.prod (⊤ : NonUnitalSubsemiring S) = s.comap (NonUnitalRingHom.fst R S) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_fst]
                  -- 🎉 no goals
#align non_unital_subsemiring.prod_top NonUnitalSubsemiring.prod_top

theorem top_prod (s : NonUnitalSubsemiring S) :
    (⊤ : NonUnitalSubsemiring R).prod s = s.comap (NonUnitalRingHom.snd R S) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_snd]
                  -- 🎉 no goals
#align non_unital_subsemiring.top_prod NonUnitalSubsemiring.top_prod

@[simp]
theorem top_prod_top : (⊤ : NonUnitalSubsemiring R).prod (⊤ : NonUnitalSubsemiring S) = ⊤ :=
  (top_prod _).trans <| comap_top _
#align non_unital_subsemiring.top_prod_top NonUnitalSubsemiring.top_prod_top

/-- Product of non-unital subsemirings is isomorphic to their product as semigroups. -/
def prodEquiv (s : NonUnitalSubsemiring R) (t : NonUnitalSubsemiring S) : s.prod t ≃+* s × t :=
  { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }
#align non_unital_subsemiring.prod_equiv NonUnitalSubsemiring.prodEquiv

theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → NonUnitalSubsemiring R}
    (hS : Directed (· ≤ ·) S) {x : R} : (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  refine' ⟨_, fun ⟨i, hi⟩ => (SetLike.le_def.1 <| le_iSup S i) hi⟩
  -- ⊢ x ∈ ⨆ (i : ι), S i → ∃ i, x ∈ S i
  let U : NonUnitalSubsemiring R :=
    NonUnitalSubsemiring.mk' (⋃ i, (S i : Set R)) (⨆ i, (S i).toSubsemigroup)
      (Subsemigroup.coe_iSup_of_directed <| hS.mono_comp _ fun _ _ => id)
      (⨆ i, (S i).toAddSubmonoid)
      (AddSubmonoid.coe_iSup_of_directed <| hS.mono_comp _ fun _ _ => id)
  -- Porting note `@this` doesn't work
  suffices H : ⨆ i, S i ≤ U; simpa using @H x
  -- ⊢ x ∈ ⨆ (i : ι), S i → ∃ i, x ∈ S i
                             -- ⊢ ⨆ (i : ι), S i ≤ U
  exact iSup_le fun i x hx => Set.mem_iUnion.2 ⟨i, hx⟩
  -- 🎉 no goals
#align non_unital_subsemiring.mem_supr_of_directed NonUnitalSubsemiring.mem_iSup_of_directed

theorem coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → NonUnitalSubsemiring R}
    (hS : Directed (· ≤ ·) S) : ((⨆ i, S i : NonUnitalSubsemiring R) : Set R) = ⋃ i, ↑(S i) :=
  Set.ext fun x => by simp [mem_iSup_of_directed hS]
                      -- 🎉 no goals
#align non_unital_subsemiring.coe_supr_of_directed NonUnitalSubsemiring.coe_iSup_of_directed

theorem mem_sSup_of_directedOn {S : Set (NonUnitalSubsemiring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) {x : R} : x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  haveI : Nonempty S := Sne.to_subtype
  -- ⊢ x ∈ sSup S ↔ ∃ s, s ∈ S ∧ x ∈ s
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, Subtype.exists, exists_prop]
  -- 🎉 no goals
#align non_unital_subsemiring.mem_Sup_of_directed_on NonUnitalSubsemiring.mem_sSup_of_directedOn

theorem coe_sSup_of_directedOn {S : Set (NonUnitalSubsemiring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(sSup S) : Set R) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]
                      -- 🎉 no goals
#align non_unital_subsemiring.coe_Sup_of_directed_on NonUnitalSubsemiring.coe_sSup_of_directedOn

end NonUnitalSubsemiring

namespace NonUnitalRingHom

variable {F : Type*} [NonUnitalNonAssocSemiring T] [NonUnitalRingHomClass F R S]
  {S' : Type*} [SetLike S' S] [NonUnitalSubsemiringClass S' S]
  {s : NonUnitalSubsemiring R}

open NonUnitalSubsemiringClass NonUnitalSubsemiring

/-- Restriction of a non-unital ring homomorphism to a non-unital subsemiring of the codomain. -/
def codRestrict (f : F) (s : S') (h : ∀ x, f x ∈ s) : R →ₙ+* s where
  toFun n := ⟨f n, h n⟩
  map_mul' x y := Subtype.eq (map_mul f x y)
  map_add' x y := Subtype.eq (map_add f x y)
  map_zero' := Subtype.eq (map_zero f)
#align non_unital_ring_hom.cod_restrict NonUnitalRingHom.codRestrictₓ

/-- Restriction of a non-unital ring homomorphism to its range interpreted as a
non-unital subsemiring.

This is the bundled version of `Set.rangeFactorization`. -/
def srangeRestrict (f : F) : R →ₙ+* (srange f : NonUnitalSubsemiring S) :=
  codRestrict f (srange f) (mem_srange_self f)
#align non_unital_ring_hom.srange_restrict NonUnitalRingHom.srangeRestrict

@[simp]
theorem coe_srangeRestrict (f : F) (x : R) : (srangeRestrict f x : S) = f x :=
  rfl
#align non_unital_ring_hom.coe_srange_restrict NonUnitalRingHom.coe_srangeRestrict

theorem srangeRestrict_surjective (f : F) :
    Function.Surjective (srangeRestrict f : R → (srange f : NonUnitalSubsemiring S)) :=
  fun ⟨_, hy⟩ =>
  let ⟨x, hx⟩ := mem_srange.mp hy
  ⟨x, Subtype.ext hx⟩
#align non_unital_ring_hom.srange_restrict_surjective NonUnitalRingHom.srangeRestrict_surjective

theorem srange_top_iff_surjective {f : F} :
    srange f = (⊤ : NonUnitalSubsemiring S) ↔ Function.Surjective (f : R → S) :=
  SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_srange, coe_top]) Set.range_iff_surjective
                                          -- 🎉 no goals
#align non_unital_ring_hom.srange_top_iff_surjective NonUnitalRingHom.srange_top_iff_surjective

/-- The range of a surjective non-unital ring homomorphism is the whole of the codomain. -/
@[simp]
theorem srange_top_of_surjective (f : F) (hf : Function.Surjective (f : R → S)) :
    srange f = (⊤ : NonUnitalSubsemiring S) :=
  srange_top_iff_surjective.2 hf
#align non_unital_ring_hom.srange_top_of_surjective NonUnitalRingHom.srange_top_of_surjective

/-- The non-unital subsemiring of elements `x : R` such that `f x = g x` -/
def eqSlocus (f g : F) : NonUnitalSubsemiring R :=
  { (f : R →ₙ* S).eqLocus (g : R →ₙ* S), (f : R →+ S).eqLocusM g with
    carrier := { x | f x = g x } }
#align non_unital_ring_hom.eq_slocus NonUnitalRingHom.eqSlocus

/-- If two non-unital ring homomorphisms are equal on a set, then they are equal on its
non-unital subsemiring closure. -/
theorem eqOn_sclosure {f g : F} {s : Set R} (h : Set.EqOn (f : R → S) (g : R → S) s) :
    Set.EqOn f g (closure s) :=
  show closure s ≤ eqSlocus f g from closure_le.2 h
#align non_unital_ring_hom.eq_on_sclosure NonUnitalRingHom.eqOn_sclosure

theorem eq_of_eqOn_stop {f g : F}
    (h : Set.EqOn (f : R → S) (g : R → S) (⊤ : NonUnitalSubsemiring R)) : f = g :=
  FunLike.ext _ _ fun _ => h trivial
#align non_unital_ring_hom.eq_of_eq_on_stop NonUnitalRingHom.eq_of_eqOn_stop

theorem eq_of_eqOn_sdense {s : Set R} (hs : closure s = ⊤) {f g : F}
    (h : s.EqOn (f : R → S) (g : R → S)) : f = g :=
  eq_of_eqOn_stop <| hs ▸ eqOn_sclosure h
#align non_unital_ring_hom.eq_of_eq_on_sdense NonUnitalRingHom.eq_of_eqOn_sdense

theorem sclosure_preimage_le (f : F) (s : Set S) :
    closure ((f : R → S) ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _ hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx
#align non_unital_ring_hom.sclosure_preimage_le NonUnitalRingHom.sclosure_preimage_le

/-- The image under a ring homomorphism of the subsemiring generated by a set equals
the subsemiring generated by the image of the set. -/
theorem map_sclosure (f : F) (s : Set R) : (closure s).map f = closure ((f : R → S) '' s) :=
  le_antisymm
    (map_le_iff_le_comap.2 <|
      le_trans (closure_mono <| Set.subset_preimage_image _ _) (sclosure_preimage_le _ _))
    (closure_le.2 <| Set.image_subset _ subset_closure)
#align non_unital_ring_hom.map_sclosure NonUnitalRingHom.map_sclosure

end NonUnitalRingHom

namespace NonUnitalSubsemiring

open NonUnitalRingHom NonUnitalSubsemiringClass

/-- The non-unital ring homomorphism associated to an inclusion of
non-unital subsemirings. -/
def inclusion {S T : NonUnitalSubsemiring R} (h : S ≤ T) : S →ₙ+* T :=
  codRestrict (subtype S) _ fun x => h x.2
#align non_unital_subsemiring.inclusion NonUnitalSubsemiring.inclusion

@[simp]
theorem srange_subtype (s : NonUnitalSubsemiring R) : NonUnitalRingHom.srange (subtype s) = s :=
  SetLike.coe_injective <| (coe_srange _).trans Subtype.range_coe
#align non_unital_subsemiring.srange_subtype NonUnitalSubsemiring.srange_subtype

@[simp]
theorem range_fst : NonUnitalRingHom.srange (fst R S) = ⊤ :=
  NonUnitalRingHom.srange_top_of_surjective (fst R S) Prod.fst_surjective
#align non_unital_subsemiring.range_fst NonUnitalSubsemiring.range_fst

@[simp]
theorem range_snd : NonUnitalRingHom.srange (snd R S) = ⊤ :=
  NonUnitalRingHom.srange_top_of_surjective (snd R S) <| Prod.snd_surjective
#align non_unital_subsemiring.range_snd NonUnitalSubsemiring.range_snd

end NonUnitalSubsemiring

namespace RingEquiv

open NonUnitalRingHom NonUnitalSubsemiringClass

variable {s t : NonUnitalSubsemiring R}

variable {F : Type*} [NonUnitalRingHomClass F R S]

/-- Makes the identity isomorphism from a proof two non-unital subsemirings of a multiplicative
monoid are equal. -/
def nonUnitalSubsemiringCongr (h : s = t) : s ≃+* t :=
  { Equiv.setCongr <| congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }
#align ring_equiv.non_unital_subsemiring_congr RingEquiv.nonUnitalSubsemiringCongr

/-- Restrict a non-unital ring homomorphism with a left inverse to a ring isomorphism to its
`NonUnitalRingHom.srange`. -/
def sofLeftInverse' {g : S → R} {f : F} (h : Function.LeftInverse g f) : R ≃+* srange f :=
  { srangeRestrict f with
    toFun := srangeRestrict f
    invFun := fun x => g (subtype (srange f) x)
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := NonUnitalRingHom.mem_srange.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }
                            -- 🎉 no goals
#align ring_equiv.sof_left_inverse' RingEquiv.sofLeftInverse'

@[simp]
theorem sofLeftInverse'_apply {g : S → R} {f : F} (h : Function.LeftInverse g f) (x : R) :
    ↑(sofLeftInverse' h x) = f x :=
  rfl
#align ring_equiv.sof_left_inverse'_apply RingEquiv.sofLeftInverse'_apply

@[simp]
theorem sofLeftInverse'_symm_apply {g : S → R} {f : F} (h : Function.LeftInverse g f)
    (x : srange f) : (sofLeftInverse' h).symm x = g x :=
  rfl
#align ring_equiv.sof_left_inverse'_symm_apply RingEquiv.sofLeftInverse'_symm_apply

/-- Given an equivalence `e : R ≃+* S` of non-unital semirings and a non-unital subsemiring
`s` of `R`, `non_unital_subsemiring_map e s` is the induced equivalence between `s` and
`s.map e` -/
@[simps!]
def nonUnitalSubsemiringMap (e : R ≃+* S) (s : NonUnitalSubsemiring R) :
    s ≃+* NonUnitalSubsemiring.map e.toNonUnitalRingHom s :=
  { e.toAddEquiv.addSubmonoidMap s.toAddSubmonoid,
    e.toMulEquiv.subsemigroupMap s.toSubsemigroup with }
#align ring_equiv.non_unital_subsemiring_map RingEquiv.nonUnitalSubsemiringMap

end RingEquiv
