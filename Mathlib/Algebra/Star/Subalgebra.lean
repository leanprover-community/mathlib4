/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Jireh Loreaux
-/
import Mathlib.Algebra.Star.Center
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Star.Pointwise
import Mathlib.Algebra.Star.Module
import Mathlib.RingTheory.Adjoin.Basic

#align_import algebra.star.subalgebra from "leanprover-community/mathlib"@"160ef3e338a2a4f21a280e4c152d4016156e516d"

/-!
# Star subalgebras

A *-subalgebra is a subalgebra of a *-algebra which is closed under *.

The centralizer of a *-closed set is a *-subalgebra.
-/


universe u v

/-- A *-subalgebra is a subalgebra of a *-algebra which is closed under *. -/
structure StarSubalgebra (R : Type u) (A : Type v) [CommSemiring R] [StarRing R] [Semiring A]
  [StarRing A] [Algebra R A] [StarModule R A] extends Subalgebra R A : Type v where
  /-- The `carrier` is closed under the `star` operation. -/
  star_mem' {a} : a ∈ carrier → star a ∈ carrier
#align star_subalgebra StarSubalgebra

namespace StarSubalgebra

/-- Forgetting that a *-subalgebra is closed under *.
-/
add_decl_doc StarSubalgebra.toSubalgebra

variable {F R A B C : Type*} [CommSemiring R] [StarRing R]
variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]
variable [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]
variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

instance setLike : SetLike (StarSubalgebra R A) A where
  coe S := S.carrier
  coe_injective' p q h := by obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩ := p; cases q; congr

instance starMemClass : StarMemClass (StarSubalgebra R A) A where
  star_mem {s} := s.star_mem'


instance subsemiringClass : SubsemiringClass (StarSubalgebra R A) A where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  one_mem {s} := s.one_mem'
  zero_mem {s} := s.zero_mem'

instance smulMemClass : SMulMemClass (StarSubalgebra R A) R A where
  smul_mem {s} r a (ha : a ∈ s.toSubalgebra) :=
    (SMulMemClass.smul_mem r ha : r • a ∈ s.toSubalgebra)

instance subringClass {R A} [CommRing R] [StarRing R] [Ring A] [StarRing A] [Algebra R A]
    [StarModule R A] : SubringClass (StarSubalgebra R A) A where
  neg_mem {s a} ha := show -a ∈ s.toSubalgebra from neg_mem ha

-- this uses the `Star` instance `s` inherits from `StarMemClass (StarSubalgebra R A) A`
instance starRing (s : StarSubalgebra R A) : StarRing s :=
  { StarMemClass.instStar s with
    star_involutive := fun r => Subtype.ext (star_star (r : A))
    star_mul := fun r₁ r₂ => Subtype.ext (star_mul (r₁ : A) (r₂ : A))
    star_add := fun r₁ r₂ => Subtype.ext (star_add (r₁ : A) (r₂ : A)) }

instance algebra (s : StarSubalgebra R A) : Algebra R s :=
  s.toSubalgebra.algebra'

instance starModule (s : StarSubalgebra R A) : StarModule R s where
  star_smul r a := Subtype.ext (star_smul r (a : A))

@[simp, nolint simpNF] -- porting note (#10618): `simpNF` says `simp` can prove this, but it can't
theorem mem_carrier {s : StarSubalgebra R A} {x : A} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl
#align star_subalgebra.mem_carrier StarSubalgebra.mem_carrier

@[ext]
theorem ext {S T : StarSubalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h
#align star_subalgebra.ext StarSubalgebra.ext

@[simp]
lemma coe_mk (S : Subalgebra R A) (h) : ((⟨S, h⟩ : StarSubalgebra R A) : Set A) = S := rfl

@[simp]
theorem mem_toSubalgebra {S : StarSubalgebra R A} {x} : x ∈ S.toSubalgebra ↔ x ∈ S :=
  Iff.rfl
#align star_subalgebra.mem_to_subalgebra StarSubalgebra.mem_toSubalgebra

@[simp]
theorem coe_toSubalgebra (S : StarSubalgebra R A) : (S.toSubalgebra : Set A) = S :=
  rfl
#align star_subalgebra.coe_to_subalgebra StarSubalgebra.coe_toSubalgebra

theorem toSubalgebra_injective :
    Function.Injective (toSubalgebra : StarSubalgebra R A → Subalgebra R A) := fun S T h =>
  ext fun x => by rw [← mem_toSubalgebra, ← mem_toSubalgebra, h]
#align star_subalgebra.to_subalgebra_injective StarSubalgebra.toSubalgebra_injective

theorem toSubalgebra_inj {S U : StarSubalgebra R A} : S.toSubalgebra = U.toSubalgebra ↔ S = U :=
  toSubalgebra_injective.eq_iff
#align star_subalgebra.to_subalgebra_inj StarSubalgebra.toSubalgebra_inj

theorem toSubalgebra_le_iff {S₁ S₂ : StarSubalgebra R A} :
    S₁.toSubalgebra ≤ S₂.toSubalgebra ↔ S₁ ≤ S₂ :=
  Iff.rfl
#align star_subalgebra.to_subalgebra_le_iff StarSubalgebra.toSubalgebra_le_iff

/-- Copy of a star subalgebra with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (S : StarSubalgebra R A) (s : Set A) (hs : s = ↑S) : StarSubalgebra R A where
  toSubalgebra := Subalgebra.copy S.toSubalgebra s hs
  star_mem' := @fun a ha => hs ▸ (S.star_mem' (by simpa [hs] using ha) : star a ∈ (S : Set A))
  -- Porting note: the old proof kept crashing Lean
#align star_subalgebra.copy StarSubalgebra.copy

@[simp]
theorem coe_copy (S : StarSubalgebra R A) (s : Set A) (hs : s = ↑S) : (S.copy s hs : Set A) = s :=
  rfl
#align star_subalgebra.coe_copy StarSubalgebra.coe_copy

theorem copy_eq (S : StarSubalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs
#align star_subalgebra.copy_eq StarSubalgebra.copy_eq

variable (S : StarSubalgebra R A)

theorem algebraMap_mem (r : R) : algebraMap R A r ∈ S :=
  S.algebraMap_mem' r
#align star_subalgebra.algebra_map_mem StarSubalgebra.algebraMap_mem

theorem rangeS_le : (algebraMap R A).rangeS ≤ S.toSubalgebra.toSubsemiring := fun _x ⟨r, hr⟩ =>
  hr ▸ S.algebraMap_mem r
#align star_subalgebra.srange_le StarSubalgebra.rangeS_le

theorem range_subset : Set.range (algebraMap R A) ⊆ S := fun _x ⟨r, hr⟩ => hr ▸ S.algebraMap_mem r
#align star_subalgebra.range_subset StarSubalgebra.range_subset

theorem range_le : Set.range (algebraMap R A) ≤ S :=
  S.range_subset
#align star_subalgebra.range_le StarSubalgebra.range_le

protected theorem smul_mem {x : A} (hx : x ∈ S) (r : R) : r • x ∈ S :=
  (Algebra.smul_def r x).symm ▸ mul_mem (S.algebraMap_mem r) hx
#align star_subalgebra.smul_mem StarSubalgebra.smul_mem

/-- Embedding of a subalgebra into the algebra. -/
def subtype : S →⋆ₐ[R] A where
  toFun := ((↑) : S → A)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl
#align star_subalgebra.subtype StarSubalgebra.subtype

@[simp]
theorem coe_subtype : (S.subtype : S → A) = Subtype.val :=
  rfl
#align star_subalgebra.coe_subtype StarSubalgebra.coe_subtype

theorem subtype_apply (x : S) : S.subtype x = (x : A) :=
  rfl
#align star_subalgebra.subtype_apply StarSubalgebra.subtype_apply

@[simp]
theorem toSubalgebra_subtype : S.toSubalgebra.val = S.subtype.toAlgHom :=
  rfl
#align star_subalgebra.to_subalgebra_subtype StarSubalgebra.toSubalgebra_subtype

/-- The inclusion map between `StarSubalgebra`s given by `Subtype.map id` as a `StarAlgHom`. -/
@[simps]
def inclusion {S₁ S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂) : S₁ →⋆ₐ[R] S₂ where
  toFun := Subtype.map id h
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl
#align star_subalgebra.inclusion StarSubalgebra.inclusion

theorem inclusion_injective {S₁ S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂) :
    Function.Injective <| inclusion h :=
  Set.inclusion_injective h
#align star_subalgebra.inclusion_injective StarSubalgebra.inclusion_injective

@[simp]
theorem subtype_comp_inclusion {S₁ S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂) :
    S₂.subtype.comp (inclusion h) = S₁.subtype :=
  rfl
#align star_subalgebra.subtype_comp_inclusion StarSubalgebra.subtype_comp_inclusion

section Map

/-- Transport a star subalgebra via a star algebra homomorphism. -/
def map (f : A →⋆ₐ[R] B) (S : StarSubalgebra R A) : StarSubalgebra R B :=
  { S.toSubalgebra.map f.toAlgHom with
    star_mem' := by
      rintro _ ⟨a, ha, rfl⟩
      exact map_star f a ▸ Set.mem_image_of_mem _ (S.star_mem' ha) }
#align star_subalgebra.map StarSubalgebra.map

theorem map_mono {S₁ S₂ : StarSubalgebra R A} {f : A →⋆ₐ[R] B} : S₁ ≤ S₂ → S₁.map f ≤ S₂.map f :=
  Set.image_subset f
#align star_subalgebra.map_mono StarSubalgebra.map_mono

theorem map_injective {f : A →⋆ₐ[R] B} (hf : Function.Injective f) : Function.Injective (map f) :=
  fun _S₁ _S₂ ih =>
  ext <| Set.ext_iff.1 <| Set.image_injective.2 hf <| Set.ext <| SetLike.ext_iff.mp ih
#align star_subalgebra.map_injective StarSubalgebra.map_injective

@[simp]
theorem map_id (S : StarSubalgebra R A) : S.map (StarAlgHom.id R A) = S :=
  SetLike.coe_injective <| Set.image_id _
#align star_subalgebra.map_id StarSubalgebra.map_id

theorem map_map (S : StarSubalgebra R A) (g : B →⋆ₐ[R] C) (f : A →⋆ₐ[R] B) :
    (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _
#align star_subalgebra.map_map StarSubalgebra.map_map

@[simp]
theorem mem_map {S : StarSubalgebra R A} {f : A →⋆ₐ[R] B} {y : B} :
    y ∈ map f S ↔ ∃ x ∈ S, f x = y :=
  Subsemiring.mem_map
#align star_subalgebra.mem_map StarSubalgebra.mem_map

theorem map_toSubalgebra {S : StarSubalgebra R A} {f : A →⋆ₐ[R] B} :
    (S.map f).toSubalgebra = S.toSubalgebra.map f.toAlgHom :=
  SetLike.coe_injective rfl
#align star_subalgebra.map_to_subalgebra StarSubalgebra.map_toSubalgebra

@[simp]
theorem coe_map (S : StarSubalgebra R A) (f : A →⋆ₐ[R] B) : (S.map f : Set B) = f '' S :=
  rfl
#align star_subalgebra.coe_map StarSubalgebra.coe_map

/-- Preimage of a star subalgebra under a star algebra homomorphism. -/
def comap (f : A →⋆ₐ[R] B) (S : StarSubalgebra R B) : StarSubalgebra R A :=
  { S.toSubalgebra.comap f.toAlgHom with
    star_mem' := @fun a ha => show f (star a) ∈ S from (map_star f a).symm ▸ star_mem ha }
#align star_subalgebra.comap StarSubalgebra.comap

theorem map_le_iff_le_comap {S : StarSubalgebra R A} {f : A →⋆ₐ[R] B} {U : StarSubalgebra R B} :
    map f S ≤ U ↔ S ≤ comap f U :=
  Set.image_subset_iff
#align star_subalgebra.map_le_iff_le_comap StarSubalgebra.map_le_iff_le_comap

theorem gc_map_comap (f : A →⋆ₐ[R] B) : GaloisConnection (map f) (comap f) := fun _S _U =>
  map_le_iff_le_comap
#align star_subalgebra.gc_map_comap StarSubalgebra.gc_map_comap

theorem comap_mono {S₁ S₂ : StarSubalgebra R B} {f : A →⋆ₐ[R] B} :
    S₁ ≤ S₂ → S₁.comap f ≤ S₂.comap f :=
  Set.preimage_mono
#align star_subalgebra.comap_mono StarSubalgebra.comap_mono

theorem comap_injective {f : A →⋆ₐ[R] B} (hf : Function.Surjective f) :
    Function.Injective (comap f) := fun _S₁ _S₂ h =>
  ext fun b =>
    let ⟨x, hx⟩ := hf b
    let this := SetLike.ext_iff.1 h x
    hx ▸ this
#align star_subalgebra.comap_injective StarSubalgebra.comap_injective

@[simp]
theorem comap_id (S : StarSubalgebra R A) : S.comap (StarAlgHom.id R A) = S :=
  SetLike.coe_injective <| Set.preimage_id
#align star_subalgebra.comap_id StarSubalgebra.comap_id

theorem comap_comap (S : StarSubalgebra R C) (g : B →⋆ₐ[R] C) (f : A →⋆ₐ[R] B) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  SetLike.coe_injective <| by exact Set.preimage_preimage
  -- Porting note: the `by exact` trick still works sometimes
#align star_subalgebra.comap_comap StarSubalgebra.comap_comap

@[simp]
theorem mem_comap (S : StarSubalgebra R B) (f : A →⋆ₐ[R] B) (x : A) : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl
#align star_subalgebra.mem_comap StarSubalgebra.mem_comap

@[simp, norm_cast]
theorem coe_comap (S : StarSubalgebra R B) (f : A →⋆ₐ[R] B) :
    (S.comap f : Set A) = f ⁻¹' (S : Set B) :=
  rfl
#align star_subalgebra.coe_comap StarSubalgebra.coe_comap

end Map

section Centralizer

variable (R)

/-- The centralizer, or commutant, of the star-closure of a set as a star subalgebra. -/
def centralizer (s : Set A) : StarSubalgebra R A where
  toSubalgebra := Subalgebra.centralizer R (s ∪ star s)
  star_mem' := Set.star_mem_centralizer
#align star_subalgebra.centralizer StarSubalgebra.centralizer

@[simp, norm_cast]
theorem coe_centralizer (s : Set A) : (centralizer R s : Set A) = (s ∪ star s).centralizer :=
  rfl
#align star_subalgebra.coe_centralizer StarSubalgebra.coe_centralizer

theorem mem_centralizer_iff {s : Set A} {z : A} :
    z ∈ centralizer R s ↔ ∀ g ∈ s, g * z = z * g ∧ star g * z = z * star g := by
  show (∀ g ∈ s ∪ star s, g * z = z * g) ↔ ∀ g ∈ s, g * z = z * g ∧ star g * z = z * star g
  simp only [Set.mem_union, or_imp, forall_and, and_congr_right_iff]
  exact fun _ =>
    ⟨fun hz a ha => hz _ (Set.star_mem_star.mpr ha), fun hz a ha => star_star a ▸ hz _ ha⟩
#align star_subalgebra.mem_centralizer_iff StarSubalgebra.mem_centralizer_iff

theorem centralizer_le (s t : Set A) (h : s ⊆ t) : centralizer R t ≤ centralizer R s :=
  Set.centralizer_subset (Set.union_subset_union h <| Set.preimage_mono h)
#align star_subalgebra.centralizer_le StarSubalgebra.centralizer_le

end Centralizer

end StarSubalgebra

/-! ### The star closure of a subalgebra -/


namespace Subalgebra

open Pointwise

variable {F R A B : Type*} [CommSemiring R] [StarRing R]
variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]
variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

/-- The pointwise `star` of a subalgebra is a subalgebra. -/
instance involutiveStar : InvolutiveStar (Subalgebra R A) where
  star S :=
    { carrier := star S.carrier
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_star, Subalgebra.mem_carrier] at *
        exact (star_mul x y).symm ▸ mul_mem hy hx
      one_mem' := Set.mem_star.mp ((star_one A).symm ▸ one_mem S : star (1 : A) ∈ S)
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_star, Subalgebra.mem_carrier] at *
        exact (star_add x y).symm ▸ add_mem hx hy
      zero_mem' := Set.mem_star.mp ((star_zero A).symm ▸ zero_mem S : star (0 : A) ∈ S)
      algebraMap_mem' := fun r => by
        simpa only [Set.mem_star, Subalgebra.mem_carrier, ← algebraMap_star_comm] using
          S.algebraMap_mem (star r) }
  star_involutive S :=
    Subalgebra.ext fun x =>
      ⟨fun hx => star_star x ▸ hx, fun hx => ((star_star x).symm ▸ hx : star (star x) ∈ S)⟩

@[simp]
theorem mem_star_iff (S : Subalgebra R A) (x : A) : x ∈ star S ↔ star x ∈ S :=
  Iff.rfl
#align subalgebra.mem_star_iff Subalgebra.mem_star_iff

-- Porting note: removed `@[simp]` tag because `simp` can prove this
theorem star_mem_star_iff (S : Subalgebra R A) (x : A) : star x ∈ star S ↔ x ∈ S := by
  simp only [mem_star_iff, star_star]
#align subalgebra.star_mem_star_iff Subalgebra.star_mem_star_iff

@[simp]
theorem coe_star (S : Subalgebra R A) : ((star S : Subalgebra R A) : Set A) = star (S : Set A) :=
  rfl
#align subalgebra.coe_star Subalgebra.coe_star

theorem star_mono : Monotone (star : Subalgebra R A → Subalgebra R A) := fun _ _ h _ hx => h hx
#align subalgebra.star_mono Subalgebra.star_mono

variable (R)

/-- The star operation on `Subalgebra` commutes with `Algebra.adjoin`. -/
theorem star_adjoin_comm (s : Set A) : star (Algebra.adjoin R s) = Algebra.adjoin R (star s) :=
  have this : ∀ t : Set A, Algebra.adjoin R (star t) ≤ star (Algebra.adjoin R t) := fun t =>
    Algebra.adjoin_le fun x hx => Algebra.subset_adjoin hx
  le_antisymm (by simpa only [star_star] using Subalgebra.star_mono (this (star s))) (this s)
#align subalgebra.star_adjoin_comm Subalgebra.star_adjoin_comm

variable {R}

/-- The `StarSubalgebra` obtained from `S : Subalgebra R A` by taking the smallest subalgebra
containing both `S` and `star S`. -/
@[simps!]
def starClosure (S : Subalgebra R A) : StarSubalgebra R A where
  toSubalgebra := S ⊔ star S
  star_mem' := fun {a} ha => by
    simp only [Subalgebra.mem_carrier, ← (@Algebra.gi R A _ _ _).l_sup_u _ _] at *
    rw [← mem_star_iff _ a, star_adjoin_comm, sup_comm]
    simpa using ha
#align subalgebra.star_closure Subalgebra.starClosure

theorem starClosure_toSubalgebra (S : Subalgebra R A) : S.starClosure.toSubalgebra = S ⊔ star S :=
  rfl

theorem starClosure_le {S₁ : Subalgebra R A} {S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂.toSubalgebra) :
    S₁.starClosure ≤ S₂ :=
  StarSubalgebra.toSubalgebra_le_iff.1 <|
    sup_le h fun x hx =>
      (star_star x ▸ star_mem (show star x ∈ S₂ from h <| (S₁.mem_star_iff _).1 hx) : x ∈ S₂)
#align subalgebra.star_closure_le Subalgebra.starClosure_le

theorem starClosure_le_iff {S₁ : Subalgebra R A} {S₂ : StarSubalgebra R A} :
    S₁.starClosure ≤ S₂ ↔ S₁ ≤ S₂.toSubalgebra :=
  ⟨fun h => le_sup_left.trans h, starClosure_le⟩
#align subalgebra.star_closure_le_iff Subalgebra.starClosure_le_iff

end Subalgebra

/-! ### The star subalgebra generated by a set -/


namespace StarAlgebra

open StarSubalgebra

variable {F R A B : Type*} [CommSemiring R] [StarRing R]
variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]
variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]
variable (R)

/-- The minimal star subalgebra that contains `s`. -/
@[simps!]
def adjoin (s : Set A) : StarSubalgebra R A :=
  { Algebra.adjoin R (s ∪ star s) with
    star_mem' := fun hx => by
      rwa [Subalgebra.mem_carrier, ← Subalgebra.mem_star_iff, Subalgebra.star_adjoin_comm,
        Set.union_star, star_star, Set.union_comm] }
#align star_subalgebra.adjoin StarAlgebra.adjoin

theorem adjoin_eq_starClosure_adjoin (s : Set A) : adjoin R s = (Algebra.adjoin R s).starClosure :=
  toSubalgebra_injective <|
    show Algebra.adjoin R (s ∪ star s) = Algebra.adjoin R s ⊔ star (Algebra.adjoin R s) from
      (Subalgebra.star_adjoin_comm R s).symm ▸ Algebra.adjoin_union s (star s)
#align star_subalgebra.adjoin_eq_star_closure_adjoin StarAlgebra.adjoin_eq_starClosure_adjoin

theorem adjoin_toSubalgebra (s : Set A) :
    (adjoin R s).toSubalgebra = Algebra.adjoin R (s ∪ star s) :=
  rfl
#align star_subalgebra.adjoin_to_subalgebra StarAlgebra.adjoin_toSubalgebra

@[aesop safe 20 apply (rule_sets := [SetLike])]
theorem subset_adjoin (s : Set A) : s ⊆ adjoin R s :=
  (Set.subset_union_left s (star s)).trans Algebra.subset_adjoin
#align star_subalgebra.subset_adjoin StarAlgebra.subset_adjoin

theorem star_subset_adjoin (s : Set A) : star s ⊆ adjoin R s :=
  (Set.subset_union_right s (star s)).trans Algebra.subset_adjoin
#align star_subalgebra.star_subset_adjoin StarAlgebra.star_subset_adjoin

theorem self_mem_adjoin_singleton (x : A) : x ∈ adjoin R ({x} : Set A) :=
  Algebra.subset_adjoin <| Set.mem_union_left _ (Set.mem_singleton x)
#align star_subalgebra.self_mem_adjoin_singleton StarAlgebra.self_mem_adjoin_singleton

theorem star_self_mem_adjoin_singleton (x : A) : star x ∈ adjoin R ({x} : Set A) :=
  star_mem <| self_mem_adjoin_singleton R x
#align star_subalgebra.star_self_mem_adjoin_singleton StarAlgebra.star_self_mem_adjoin_singleton

variable {R}

protected theorem gc : GaloisConnection (adjoin R : Set A → StarSubalgebra R A) (↑) := by
  intro s S
  rw [← toSubalgebra_le_iff, adjoin_toSubalgebra, Algebra.adjoin_le_iff, coe_toSubalgebra]
  exact
    ⟨fun h => (Set.subset_union_left s _).trans h, fun h =>
      Set.union_subset h fun x hx => star_star x ▸ star_mem (show star x ∈ S from h hx)⟩
#align star_subalgebra.gc StarAlgebra.gc

/-- Galois insertion between `adjoin` and `coe`. -/
protected def gi : GaloisInsertion (adjoin R : Set A → StarSubalgebra R A) (↑) where
  choice s hs := (adjoin R s).copy s <| le_antisymm (StarAlgebra.gc.le_u_l s) hs
  gc := StarAlgebra.gc
  le_l_u S := (StarAlgebra.gc (S : Set A) (adjoin R S)).1 <| le_rfl
  choice_eq _ _ := StarSubalgebra.copy_eq _ _ _
#align star_subalgebra.gi StarAlgebra.gi

theorem adjoin_le {S : StarSubalgebra R A} {s : Set A} (hs : s ⊆ S) : adjoin R s ≤ S :=
  StarAlgebra.gc.l_le hs
#align star_subalgebra.adjoin_le StarAlgebra.adjoin_le

theorem adjoin_le_iff {S : StarSubalgebra R A} {s : Set A} : adjoin R s ≤ S ↔ s ⊆ S :=
  StarAlgebra.gc _ _
#align star_subalgebra.adjoin_le_iff StarAlgebra.adjoin_le_iff

lemma adjoin_eq (S : StarSubalgebra R A) : adjoin R (S : Set A) = S :=
  le_antisymm (adjoin_le le_rfl) (subset_adjoin R (S : Set A))

open Submodule in
lemma adjoin_eq_span (s : Set A) :
    Subalgebra.toSubmodule (adjoin R s).toSubalgebra = span R (Submonoid.closure (s ∪ star s)) := by
  rw [adjoin_toSubalgebra, Algebra.adjoin_eq_span]

theorem _root_.Subalgebra.starClosure_eq_adjoin (S : Subalgebra R A) :
    S.starClosure = adjoin R (S : Set A) :=
  le_antisymm (Subalgebra.starClosure_le_iff.2 <| subset_adjoin R (S : Set A))
    (adjoin_le (le_sup_left : S ≤ S ⊔ star S))
#align subalgebra.star_closure_eq_adjoin Subalgebra.starClosure_eq_adjoin

/-- If some predicate holds for all `x ∈ (s : Set A)` and this predicate is closed under the
`algebraMap`, addition, multiplication and star operations, then it holds for `a ∈ adjoin R s`. -/
@[elab_as_elim]
theorem adjoin_induction {s : Set A} {p : A → Prop} {a : A} (h : a ∈ adjoin R s)
    (mem : ∀ x : A, x ∈ s → p x) (algebraMap : ∀ r : R, p (algebraMap R A r))
    (add : ∀ x y : A, p x → p y → p (x + y)) (mul : ∀ x y : A, p x → p y → p (x * y))
    (star : ∀ x : A, p x → p (star x)) : p a :=
  Algebra.adjoin_induction h
    (fun x hx => hx.elim (fun hx => mem x hx) fun hx => star_star x ▸ star _ (mem _ hx))
    algebraMap add mul
#align star_subalgebra.adjoin_induction StarAlgebra.adjoin_induction

@[elab_as_elim]
theorem adjoin_induction₂ {s : Set A} {p : A → A → Prop} {a b : A} (ha : a ∈ adjoin R s)
    (hb : b ∈ adjoin R s) (Hs : ∀ x : A, x ∈ s → ∀ y : A, y ∈ s → p x y)
    (Halg : ∀ r₁ r₂ : R, p (algebraMap R A r₁) (algebraMap R A r₂))
    (Halg_left : ∀ (r : R) (x : A), x ∈ s → p (algebraMap R A r) x)
    (Halg_right : ∀ (r : R) (x : A), x ∈ s → p x (algebraMap R A r))
    (Hadd_left : ∀ x₁ x₂ y : A, p x₁ y → p x₂ y → p (x₁ + x₂) y)
    (Hadd_right : ∀ x y₁ y₂ : A, p x y₁ → p x y₂ → p x (y₁ + y₂))
    (Hmul_left : ∀ x₁ x₂ y : A, p x₁ y → p x₂ y → p (x₁ * x₂) y)
    (Hmul_right : ∀ x y₁ y₂ : A, p x y₁ → p x y₂ → p x (y₁ * y₂))
    (Hstar : ∀ x y : A, p x y → p (star x) (star y)) (Hstar_left : ∀ x y : A, p x y → p (star x) y)
    (Hstar_right : ∀ x y : A, p x y → p x (star y)) : p a b := by
  refine
    Algebra.adjoin_induction₂ ha hb (fun x hx y hy => ?_) Halg (fun r x hx => ?_) (fun r x hx => ?_)
      Hadd_left Hadd_right Hmul_left Hmul_right
  · cases' hx with hx hx <;> cases' hy with hy hy
    · exact Hs x hx y hy
    · exact star_star y ▸ Hstar_right _ _ (Hs _ hx _ hy)
    · exact star_star x ▸ Hstar_left _ _ (Hs _ hx _ hy)
    · exact star_star x ▸ star_star y ▸ Hstar _ _ (Hs _ hx _ hy)
  · cases' hx with hx hx
    · exact Halg_left _ _ hx
    · exact star_star x ▸ Hstar_right _ _ (Halg_left r _ hx)
  · cases' hx with hx hx
    · exact Halg_right _ _ hx
    · exact star_star x ▸ Hstar_left _ _ (Halg_right r _ hx)
#align star_subalgebra.adjoin_induction₂ StarAlgebra.adjoin_induction₂

/-- The difference with `StarSubalgebra.adjoin_induction` is that this acts on the subtype. -/
@[elab_as_elim]
theorem adjoin_induction' {s : Set A} {p : adjoin R s → Prop} (a : adjoin R s)
    (mem : ∀ (x) (h : x ∈ s), p ⟨x, subset_adjoin R s h⟩) (algebraMap : ∀ r, p (algebraMap R _ r))
    (add : ∀ x y, p x → p y → p (x + y)) (mul : ∀ x y, p x → p y → p (x * y))
    (star : ∀ x, p x → p (star x)) : p a :=
  Subtype.recOn a fun b hb => by
    refine Exists.elim ?_ fun (hb : b ∈ adjoin R s) (hc : p ⟨b, hb⟩) => hc
    refine adjoin_induction hb ?_ ?_ ?_ ?_ ?_
    exacts [fun x hx => ⟨subset_adjoin R s hx, mem x hx⟩, fun r =>
      ⟨StarSubalgebra.algebraMap_mem _ r, algebraMap r⟩, fun x y hx hy =>
      Exists.elim hx fun hx' hx => Exists.elim hy fun hy' hy => ⟨add_mem hx' hy', add _ _ hx hy⟩,
      fun x y hx hy =>
      Exists.elim hx fun hx' hx => Exists.elim hy fun hy' hy => ⟨mul_mem hx' hy', mul _ _ hx hy⟩,
      fun x hx => Exists.elim hx fun hx' hx => ⟨star_mem hx', star _ hx⟩]
#align star_subalgebra.adjoin_induction' StarAlgebra.adjoin_induction'

variable (R)

/-- If all elements of `s : Set A` commute pairwise and also commute pairwise with elements of
`star s`, then `StarSubalgebra.adjoin R s` is commutative. See note [reducible non-instances]. -/
abbrev adjoinCommSemiringOfComm {s : Set A}
    (hcomm : ∀ a : A, a ∈ s → ∀ b : A, b ∈ s → a * b = b * a)
    (hcomm_star : ∀ a : A, a ∈ s → ∀ b : A, b ∈ s → a * star b = star b * a) :
    CommSemiring (adjoin R s) :=
  { (adjoin R s).toSubalgebra.toSemiring with
    mul_comm := by
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      ext
      simp only [MulMemClass.mk_mul_mk]
      rw [← mem_toSubalgebra, adjoin_toSubalgebra] at hx hy
      letI : CommSemiring (Algebra.adjoin R (s ∪ star s)) :=
        Algebra.adjoinCommSemiringOfComm R
          (by
            intro a ha b hb
            cases' ha with ha ha <;> cases' hb with hb hb
            · exact hcomm _ ha _ hb
            · exact star_star b ▸ hcomm_star _ ha _ hb
            · exact star_star a ▸ (hcomm_star _ hb _ ha).symm
            · simpa only [star_mul, star_star] using congr_arg star (hcomm _ hb _ ha))
      exact congr_arg Subtype.val (mul_comm (⟨x, hx⟩ : Algebra.adjoin R (s ∪ star s)) ⟨y, hy⟩) }
#align star_subalgebra.adjoin_comm_semiring_of_comm StarAlgebra.adjoinCommSemiringOfComm

/-- If all elements of `s : Set A` commute pairwise and also commute pairwise with elements of
`star s`, then `StarSubalgebra.adjoin R s` is commutative. See note [reducible non-instances]. -/
abbrev adjoinCommRingOfComm (R : Type u) {A : Type v} [CommRing R] [StarRing R] [Ring A]
    [Algebra R A] [StarRing A] [StarModule R A] {s : Set A}
    (hcomm : ∀ a : A, a ∈ s → ∀ b : A, b ∈ s → a * b = b * a)
    (hcomm_star : ∀ a : A, a ∈ s → ∀ b : A, b ∈ s → a * star b = star b * a) :
    CommRing (adjoin R s) :=
  { StarAlgebra.adjoinCommSemiringOfComm R hcomm hcomm_star,
    (adjoin R s).toSubalgebra.toRing with }
#align star_subalgebra.adjoin_comm_ring_of_comm StarAlgebra.adjoinCommRingOfComm

/-- The star subalgebra `StarSubalgebra.adjoin R {x}` generated by a single `x : A` is commutative
if `x` is normal. -/
instance adjoinCommSemiringOfIsStarNormal (x : A) [IsStarNormal x] :
    CommSemiring (adjoin R ({x} : Set A)) :=
  adjoinCommSemiringOfComm R
    (fun a ha b hb => by
      rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb])
    fun a ha b hb => by
    rw [Set.mem_singleton_iff] at ha hb
    simpa only [ha, hb] using (star_comm_self' x).symm
#align star_subalgebra.adjoin_comm_semiring_of_is_star_normal StarAlgebra.adjoinCommSemiringOfIsStarNormal

/-- The star subalgebra `StarSubalgebra.adjoin R {x}` generated by a single `x : A` is commutative
if `x` is normal. -/
instance adjoinCommRingOfIsStarNormal (R : Type u) {A : Type v} [CommRing R] [StarRing R] [Ring A]
    [Algebra R A] [StarRing A] [StarModule R A] (x : A) [IsStarNormal x] :
    CommRing (adjoin R ({x} : Set A)) :=
  { (adjoin R ({x} : Set A)).toSubalgebra.toRing with mul_comm := mul_comm }
#align star_subalgebra.adjoin_comm_ring_of_is_star_normal StarAlgebra.adjoinCommRingOfIsStarNormal

/-! ### Complete lattice structure -/

end StarAlgebra

namespace StarSubalgebra

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

instance completeLattice : CompleteLattice (StarSubalgebra R A) where
  __ := GaloisInsertion.liftCompleteLattice StarAlgebra.gi
  bot := { toSubalgebra := ⊥, star_mem' := fun ⟨r, hr⟩ => ⟨star r, hr ▸ algebraMap_star_comm _⟩ }
  bot_le S := (bot_le : ⊥ ≤ S.toSubalgebra)

instance inhabited : Inhabited (StarSubalgebra R A) :=
  ⟨⊤⟩

@[simp]
theorem coe_top : (↑(⊤ : StarSubalgebra R A) : Set A) = Set.univ :=
  rfl
#align star_subalgebra.coe_top StarSubalgebra.coe_top

@[simp]
theorem mem_top {x : A} : x ∈ (⊤ : StarSubalgebra R A) :=
  Set.mem_univ x
#align star_subalgebra.mem_top StarSubalgebra.mem_top

@[simp]
theorem top_toSubalgebra : (⊤ : StarSubalgebra R A).toSubalgebra = ⊤ := by ext; simp
-- Porting note: Lean can no longer prove this by `rfl`, it times out
#align star_subalgebra.top_to_subalgebra StarSubalgebra.top_toSubalgebra

@[simp]
theorem toSubalgebra_eq_top {S : StarSubalgebra R A} : S.toSubalgebra = ⊤ ↔ S = ⊤ :=
  StarSubalgebra.toSubalgebra_injective.eq_iff' top_toSubalgebra
#align star_subalgebra.to_subalgebra_eq_top StarSubalgebra.toSubalgebra_eq_top

theorem mem_sup_left {S T : StarSubalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S ⊔ T :=
  have : S ≤ S ⊔ T := le_sup_left; (this ·) -- Porting note: need `have` instead of `show`
#align star_subalgebra.mem_sup_left StarSubalgebra.mem_sup_left

theorem mem_sup_right {S T : StarSubalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S ⊔ T :=
  have : T ≤ S ⊔ T := le_sup_right; (this ·) -- Porting note: need `have` instead of `show`
#align star_subalgebra.mem_sup_right StarSubalgebra.mem_sup_right

theorem mul_mem_sup {S T : StarSubalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ T) :
    x * y ∈ S ⊔ T :=
  mul_mem (mem_sup_left hx) (mem_sup_right hy)
#align star_subalgebra.mul_mem_sup StarSubalgebra.mul_mem_sup

theorem map_sup (f : A →⋆ₐ[R] B) (S T : StarSubalgebra R A) : map f (S ⊔ T) = map f S ⊔ map f T :=
  (StarSubalgebra.gc_map_comap f).l_sup
#align star_subalgebra.map_sup StarSubalgebra.map_sup

@[simp, norm_cast]
theorem coe_inf (S T : StarSubalgebra R A) : (↑(S ⊓ T) : Set A) = (S : Set A) ∩ T :=
  rfl
#align star_subalgebra.coe_inf StarSubalgebra.coe_inf

@[simp]
theorem mem_inf {S T : StarSubalgebra R A} {x : A} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T :=
  Iff.rfl
#align star_subalgebra.mem_inf StarSubalgebra.mem_inf

@[simp]
theorem inf_toSubalgebra (S T : StarSubalgebra R A) :
    (S ⊓ T).toSubalgebra = S.toSubalgebra ⊓ T.toSubalgebra := by
  ext; simp
-- Porting note: Lean can no longer prove this by `rfl`, it times out
#align star_subalgebra.inf_to_subalgebra StarSubalgebra.inf_toSubalgebra

@[simp, norm_cast]
theorem coe_sInf (S : Set (StarSubalgebra R A)) : (↑(sInf S) : Set A) = ⋂ s ∈ S, ↑s :=
  sInf_image
#align star_subalgebra.coe_Inf StarSubalgebra.coe_sInf

theorem mem_sInf {S : Set (StarSubalgebra R A)} {x : A} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]
#align star_subalgebra.mem_Inf StarSubalgebra.mem_sInf

@[simp]
theorem sInf_toSubalgebra (S : Set (StarSubalgebra R A)) :
    (sInf S).toSubalgebra = sInf (StarSubalgebra.toSubalgebra '' S) :=
  SetLike.coe_injective <| by simp
#align star_subalgebra.Inf_to_subalgebra StarSubalgebra.sInf_toSubalgebra

@[simp, norm_cast]
theorem coe_iInf {ι : Sort*} {S : ι → StarSubalgebra R A} : (↑(⨅ i, S i) : Set A) = ⋂ i, S i := by
  simp [iInf]
#align star_subalgebra.coe_infi StarSubalgebra.coe_iInf

theorem mem_iInf {ι : Sort*} {S : ι → StarSubalgebra R A} {x : A} :
    (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by simp only [iInf, mem_sInf, Set.forall_mem_range]
#align star_subalgebra.mem_infi StarSubalgebra.mem_iInf

@[simp]
theorem iInf_toSubalgebra {ι : Sort*} (S : ι → StarSubalgebra R A) :
    (⨅ i, S i).toSubalgebra = ⨅ i, (S i).toSubalgebra :=
  SetLike.coe_injective <| by simp
#align star_subalgebra.infi_to_subalgebra StarSubalgebra.iInf_toSubalgebra

theorem bot_toSubalgebra : (⊥ : StarSubalgebra R A).toSubalgebra = ⊥ := rfl
#align star_subalgebra.bot_to_subalgebra StarSubalgebra.bot_toSubalgebra

theorem mem_bot {x : A} : x ∈ (⊥ : StarSubalgebra R A) ↔ x ∈ Set.range (algebraMap R A) := Iff.rfl
#align star_subalgebra.mem_bot StarSubalgebra.mem_bot

@[simp]
theorem coe_bot : ((⊥ : StarSubalgebra R A) : Set A) = Set.range (algebraMap R A) := rfl
#align star_subalgebra.coe_bot StarSubalgebra.coe_bot

theorem eq_top_iff {S : StarSubalgebra R A} : S = ⊤ ↔ ∀ x : A, x ∈ S :=
  ⟨fun h x => by rw [h]; exact mem_top,
  fun h => by ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩
#align star_subalgebra.eq_top_iff StarSubalgebra.eq_top_iff

end StarSubalgebra

namespace StarAlgHom

open StarSubalgebra StarAlgebra

variable {F R A B : Type*} [CommSemiring R] [StarRing R]
variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]
variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]
variable [FunLike F A B] [AlgHomClass F R A B] [StarAlgHomClass F R A B] (f g : F)

/-- The equalizer of two star `R`-algebra homomorphisms. -/
def equalizer : StarSubalgebra R A :=
  { toSubalgebra := AlgHom.equalizer (f : A →ₐ[R] B) g
    star_mem' := @fun a (ha : f a = g a) => by simpa only [← map_star] using congrArg star ha }
-- Porting note: much like `StarSubalgebra.copy` the old proof was broken and hard to fix
#align star_alg_hom.equalizer StarAlgHom.equalizer

@[simp]
theorem mem_equalizer (x : A) : x ∈ StarAlgHom.equalizer f g ↔ f x = g x :=
  Iff.rfl
#align star_alg_hom.mem_equalizer StarAlgHom.mem_equalizer

theorem adjoin_le_equalizer {s : Set A} (h : s.EqOn f g) : adjoin R s ≤ StarAlgHom.equalizer f g :=
  adjoin_le h
#align star_alg_hom.adjoin_le_equalizer StarAlgHom.adjoin_le_equalizer

theorem ext_of_adjoin_eq_top {s : Set A} (h : adjoin R s = ⊤) ⦃f g : F⦄ (hs : s.EqOn f g) : f = g :=
  DFunLike.ext f g fun _x => StarAlgHom.adjoin_le_equalizer f g hs <| h.symm ▸ trivial
#align star_alg_hom.ext_of_adjoin_eq_top StarAlgHom.ext_of_adjoin_eq_top

theorem map_adjoin (f : A →⋆ₐ[R] B) (s : Set A) :
    map f (adjoin R s) = adjoin R (f '' s) :=
  GaloisConnection.l_comm_of_u_comm Set.image_preimage (gc_map_comap f) StarAlgebra.gc
    StarAlgebra.gc fun _ => rfl
#align star_alg_hom.map_adjoin StarAlgHom.map_adjoin

theorem ext_adjoin {s : Set A} [FunLike F (adjoin R s) B]
    [AlgHomClass F R (adjoin R s) B] [StarAlgHomClass F R (adjoin R s) B] {f g : F}
    (h : ∀ x : adjoin R s, (x : A) ∈ s → f x = g x) : f = g := by
  refine DFunLike.ext f g fun a =>
    adjoin_induction' (p := fun y => f y = g y) a (fun x hx => ?_) (fun r => ?_)
    (fun x y hx hy => ?_) (fun x y hx hy => ?_) fun x hx => ?_
  · exact h ⟨x, subset_adjoin R s hx⟩ hx
  · simp only [AlgHomClass.commutes]
  · simp only [map_add, map_add, hx, hy]
  · simp only [map_mul, map_mul, hx, hy]
  · simp only [map_star, hx]
#align star_alg_hom.ext_adjoin StarAlgHom.ext_adjoin

theorem ext_adjoin_singleton {a : A} [FunLike F (adjoin R ({a} : Set A)) B]
    [AlgHomClass F R (adjoin R ({a} : Set A)) B] [StarAlgHomClass F R (adjoin R ({a} : Set A)) B]
    {f g : F} (h : f ⟨a, self_mem_adjoin_singleton R a⟩ = g ⟨a, self_mem_adjoin_singleton R a⟩) :
    f = g :=
  ext_adjoin fun x hx =>
    (show x = ⟨a, self_mem_adjoin_singleton R a⟩ from
          Subtype.ext <| Set.mem_singleton_iff.mp hx).symm ▸
      h
#align star_alg_hom.ext_adjoin_singleton StarAlgHom.ext_adjoin_singleton

/-- Range of a `StarAlgHom` as a star subalgebra. -/
protected def range
    (φ : A →⋆ₐ[R] B) : StarSubalgebra R B where
  toSubalgebra := φ.toAlgHom.range
  star_mem' := by rintro _ ⟨b, rfl⟩; exact ⟨star b, map_star φ b⟩

theorem range_eq_map_top (φ : A →⋆ₐ[R] B) : φ.range = (⊤ : StarSubalgebra R A).map φ :=
  StarSubalgebra.ext fun x =>
    ⟨by rintro ⟨a, ha⟩; exact ⟨a, by simp, ha⟩, by rintro ⟨a, -, ha⟩; exact ⟨a, ha⟩⟩

/-- Restriction of the codomain of a `StarAlgHom` to a star subalgebra containing the range. -/
protected def codRestrict (f : A →⋆ₐ[R] B) (S : StarSubalgebra R B) (hf : ∀ x, f x ∈ S) :
    A →⋆ₐ[R] S where
  toAlgHom := AlgHom.codRestrict f.toAlgHom S.toSubalgebra hf
  map_star' := fun x => Subtype.ext (map_star f x)

@[simp]
theorem coe_codRestrict (f : A →⋆ₐ[R] B) (S : StarSubalgebra R B) (hf : ∀ x, f x ∈ S) (x : A) :
    ↑(f.codRestrict S hf x) = f x :=
  rfl

@[simp]
theorem subtype_comp_codRestrict (f : A →⋆ₐ[R] B) (S : StarSubalgebra R B)
    (hf : ∀ x : A, f x ∈ S) : S.subtype.comp (f.codRestrict S hf) = f :=
  StarAlgHom.ext <| coe_codRestrict _ S hf

theorem injective_codRestrict (f : A →⋆ₐ[R] B) (S : StarSubalgebra R B) (hf : ∀ x : A, f x ∈ S) :
    Function.Injective (StarAlgHom.codRestrict f S hf) ↔ Function.Injective f :=
  ⟨fun H _x _y hxy => H <| Subtype.eq hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy : _)⟩

/-- Restriction of the codomain of a `StarAlgHom` to its range. -/
def rangeRestrict (f : A →⋆ₐ[R] B) : A →⋆ₐ[R] f.range :=
  StarAlgHom.codRestrict f _ fun x => ⟨x, rfl⟩

/-- The `StarAlgEquiv` onto the range corresponding to an injective `StarAlgHom`. -/
@[simps]
noncomputable def _root_.StarAlgEquiv.ofInjective (f : A →⋆ₐ[R] B)
    (hf : Function.Injective f) : A ≃⋆ₐ[R] f.range :=
  { AlgEquiv.ofInjective (f : A →ₐ[R] B) hf with
    toFun := f.rangeRestrict
    map_star' := fun a => Subtype.ext (map_star f a)
    map_smul' := fun r a => Subtype.ext (map_smul f r a) }
end StarAlgHom


section RestrictScalars

variable (R : Type*) {S A B : Type*} [CommSemiring R]
  [CommSemiring S] [Semiring A] [Semiring B] [Algebra R S] [Algebra S A] [Algebra S B]
  [Algebra R A] [Algebra R B] [IsScalarTower R S A] [IsScalarTower R S B] [Star A] [Star B]

@[simps!]
def StarAlgHom.restrictScalars (f : A →⋆ₐ[S] B) : A →⋆ₐ[R] B where
  toAlgHom := f.toAlgHom.restrictScalars R
  map_star' := map_star f

theorem StarAlgHom.restrictScalars_injective :
    Function.Injective (StarAlgHom.restrictScalars R : (A →⋆ₐ[S] B) → A →⋆ₐ[R] B) :=
  fun f g h => StarAlgHom.ext fun x =>
    show f.restrictScalars R x = g.restrictScalars R x from DFunLike.congr_fun h x

@[simps]
def StarAlgEquiv.restrictScalars (f : A ≃⋆ₐ[S] B) : A ≃⋆ₐ[R] B :=
  { (f : A →⋆ₐ[S] B).restrictScalars R, f with
    toFun := f
    map_smul' := map_smul ((f : A →⋆ₐ[S] B).restrictScalars R) }

theorem StarAlgEquiv.restrictScalars_injective :
    Function.Injective (StarAlgEquiv.restrictScalars R : (A ≃⋆ₐ[S] B) → A ≃⋆ₐ[R] B) :=
  fun f g h => StarAlgEquiv.ext fun x =>
    show f.restrictScalars R x = g.restrictScalars R x from DFunLike.congr_fun h x

end RestrictScalars
