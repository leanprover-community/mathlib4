/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Jireh Loreaux
-/
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.NonUnitalSubalgebra

/-!
# Star subalgebras

A *-subalgebra is a subalgebra of a *-algebra which is closed under *.

The centralizer of a *-closed set is a *-subalgebra.
-/

universe u v

/-- A *-subalgebra is a subalgebra of a *-algebra which is closed under *. -/
structure StarSubalgebra (R : Type u) (A : Type v) [CommSemiring R] [StarRing R] [Semiring A]
    [StarRing A] [Algebra R A] [StarModule R A] : Type v extends Subalgebra R A where
  /-- The `carrier` is closed under the `star` operation. -/
  star_mem' {a} : a ∈ carrier → star a ∈ carrier

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

/-- The actual `StarSubalgebra` obtained from an element of a type satisfying `SubsemiringClass`,
`SMulMemClass` and `StarMemClass`. -/
@[simps]
def ofClass {S R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [StarRing R] [StarRing A]
    [StarModule R A] [SetLike S A] [SubsemiringClass S A] [SMulMemClass S R A] [StarMemClass S A]
    (s : S) : StarSubalgebra R A where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  one_mem' := one_mem _
  algebraMap_mem' := algebraMap_mem s
  star_mem' := star_mem

instance (priority := 100) : CanLift (Set A) (StarSubalgebra R A) (↑)
    (fun s ↦ (∀ {x y}, x ∈ s → y ∈ s → x + y ∈ s) ∧ (∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s) ∧
      (∀ (r : R), algebraMap R A r ∈ s) ∧ ∀ {x}, x ∈ s → star x ∈ s) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := by simpa using h.2.2.1 0
        add_mem' := h.1
        one_mem' := by simpa using h.2.2.1 1
        mul_mem' := h.2.1
        algebraMap_mem' := h.2.2.1
        star_mem' := h.2.2.2 },
      rfl ⟩

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

/-- Turn a `StarSubalgebra` into a `NonUnitalStarSubalgebra` by forgetting that it contains `1`. -/
def toNonUnitalStarSubalgebra (S : StarSubalgebra R A) : NonUnitalStarSubalgebra R A where
  __ := S
  smul_mem' r _x hx := S.smul_mem hx r

lemma one_mem_toNonUnitalStarSubalgebra (S : StarSubalgebra R A) :
    1 ∈ S.toNonUnitalStarSubalgebra := S.one_mem'

theorem mem_carrier {s : StarSubalgebra R A} {x : A} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[ext]
theorem ext {S T : StarSubalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
lemma coe_mk (S : Subalgebra R A) (h) : ((⟨S, h⟩ : StarSubalgebra R A) : Set A) = S := rfl

@[simp]
theorem mem_toSubalgebra {S : StarSubalgebra R A} {x} : x ∈ S.toSubalgebra ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_toSubalgebra (S : StarSubalgebra R A) : (S.toSubalgebra : Set A) = S :=
  rfl

theorem toSubalgebra_injective :
    Function.Injective (toSubalgebra : StarSubalgebra R A → Subalgebra R A) := fun S T h =>
  ext fun x => by rw [← mem_toSubalgebra, ← mem_toSubalgebra, h]

theorem toSubalgebra_inj {S U : StarSubalgebra R A} : S.toSubalgebra = U.toSubalgebra ↔ S = U :=
  toSubalgebra_injective.eq_iff

theorem toSubalgebra_le_iff {S₁ S₂ : StarSubalgebra R A} :
    S₁.toSubalgebra ≤ S₂.toSubalgebra ↔ S₁ ≤ S₂ :=
  Iff.rfl

/-- Copy of a star subalgebra with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (S : StarSubalgebra R A) (s : Set A) (hs : s = ↑S) : StarSubalgebra R A where
  toSubalgebra := Subalgebra.copy S.toSubalgebra s hs
  star_mem' {a} ha := hs ▸ S.star_mem' (by simpa [hs] using ha)

@[simp, norm_cast]
theorem coe_copy (S : StarSubalgebra R A) (s : Set A) (hs : s = ↑S) : (S.copy s hs : Set A) = s :=
  rfl

theorem copy_eq (S : StarSubalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

variable (S : StarSubalgebra R A)

protected theorem algebraMap_mem (r : R) : algebraMap R A r ∈ S :=
  S.algebraMap_mem' r

theorem rangeS_le : (algebraMap R A).rangeS ≤ S.toSubalgebra.toSubsemiring := fun _x ⟨r, hr⟩ =>
  hr ▸ S.algebraMap_mem r

theorem range_subset : Set.range (algebraMap R A) ⊆ S := fun _x ⟨r, hr⟩ => hr ▸ S.algebraMap_mem r

theorem range_le : Set.range (algebraMap R A) ≤ S :=
  S.range_subset

protected theorem smul_mem {x : A} (hx : x ∈ S) (r : R) : r • x ∈ S :=
  (Algebra.smul_def r x).symm ▸ mul_mem (S.algebraMap_mem r) hx

/-- Embedding of a subalgebra into the algebra. -/
def subtype : S →⋆ₐ[R] A where
  toFun := ((↑) : S → A)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp]
theorem coe_subtype : (S.subtype : S → A) = Subtype.val :=
  rfl

theorem subtype_apply (x : S) : S.subtype x = (x : A) :=
  rfl

@[simp]
theorem toSubalgebra_subtype : S.toSubalgebra.val = S.subtype.toAlgHom :=
  rfl

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

theorem inclusion_injective {S₁ S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂) :
    Function.Injective <| inclusion h :=
  Set.inclusion_injective h

@[simp]
theorem subtype_comp_inclusion {S₁ S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂) :
    S₂.subtype.comp (inclusion h) = S₁.subtype :=
  rfl

section Map

/-- Transport a star subalgebra via a star algebra homomorphism. -/
def map (f : A →⋆ₐ[R] B) (S : StarSubalgebra R A) : StarSubalgebra R B :=
  { S.toSubalgebra.map f.toAlgHom with
    star_mem' := by
      rintro _ ⟨a, ha, rfl⟩
      exact map_star f a ▸ Set.mem_image_of_mem _ (S.star_mem' ha) }

theorem map_mono {S₁ S₂ : StarSubalgebra R A} {f : A →⋆ₐ[R] B} : S₁ ≤ S₂ → S₁.map f ≤ S₂.map f :=
  Set.image_mono

theorem map_injective {f : A →⋆ₐ[R] B} (hf : Function.Injective f) : Function.Injective (map f) :=
  fun _S₁ _S₂ ih =>
  ext <| Set.ext_iff.1 <| Set.image_injective.2 hf <| Set.ext <| SetLike.ext_iff.mp ih

@[simp]
theorem map_id (S : StarSubalgebra R A) : S.map (StarAlgHom.id R A) = S :=
  SetLike.coe_injective <| Set.image_id _

theorem map_map (S : StarSubalgebra R A) (g : B →⋆ₐ[R] C) (f : A →⋆ₐ[R] B) :
    (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _

@[simp]
theorem mem_map {S : StarSubalgebra R A} {f : A →⋆ₐ[R] B} {y : B} :
    y ∈ map f S ↔ ∃ x ∈ S, f x = y :=
  Subsemiring.mem_map

theorem map_toSubalgebra {S : StarSubalgebra R A} {f : A →⋆ₐ[R] B} :
    (S.map f).toSubalgebra = S.toSubalgebra.map f.toAlgHom :=
  SetLike.coe_injective rfl

@[simp, norm_cast]
theorem coe_map (S : StarSubalgebra R A) (f : A →⋆ₐ[R] B) : (S.map f : Set B) = f '' S :=
  rfl

/-- Preimage of a star subalgebra under a star algebra homomorphism. -/
def comap (f : A →⋆ₐ[R] B) (S : StarSubalgebra R B) : StarSubalgebra R A :=
  { S.toSubalgebra.comap f.toAlgHom with
    star_mem' := @fun a ha => show f (star a) ∈ S from (map_star f a).symm ▸ star_mem ha }

theorem map_le_iff_le_comap {S : StarSubalgebra R A} {f : A →⋆ₐ[R] B} {U : StarSubalgebra R B} :
    map f S ≤ U ↔ S ≤ comap f U :=
  Set.image_subset_iff

theorem gc_map_comap (f : A →⋆ₐ[R] B) : GaloisConnection (map f) (comap f) := fun _S _U =>
  map_le_iff_le_comap

theorem comap_mono {S₁ S₂ : StarSubalgebra R B} {f : A →⋆ₐ[R] B} :
    S₁ ≤ S₂ → S₁.comap f ≤ S₂.comap f :=
  Set.preimage_mono

theorem comap_injective {f : A →⋆ₐ[R] B} (hf : Function.Surjective f) :
    Function.Injective (comap f) := fun _S₁ _S₂ h =>
  ext fun b =>
    let ⟨x, hx⟩ := hf b
    let this := SetLike.ext_iff.1 h x
    hx ▸ this

@[simp]
theorem comap_id (S : StarSubalgebra R A) : S.comap (StarAlgHom.id R A) = S :=
  SetLike.coe_injective <| Set.preimage_id

theorem comap_comap (S : StarSubalgebra R C) (g : B →⋆ₐ[R] C) (f : A →⋆ₐ[R] B) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  SetLike.coe_injective <| by exact Set.preimage_preimage

@[simp]
theorem mem_comap (S : StarSubalgebra R B) (f : A →⋆ₐ[R] B) (x : A) : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_comap (S : StarSubalgebra R B) (f : A →⋆ₐ[R] B) :
    (S.comap f : Set A) = f ⁻¹' (S : Set B) :=
  rfl

end Map

section Centralizer

variable (R)

/-- The centralizer, or commutant, of the star-closure of a set as a star subalgebra. -/
def centralizer (s : Set A) : StarSubalgebra R A where
  toSubalgebra := Subalgebra.centralizer R (s ∪ star s)
  star_mem' := Set.star_mem_centralizer

@[simp, norm_cast]
theorem coe_centralizer (s : Set A) : (centralizer R s : Set A) = (s ∪ star s).centralizer :=
  rfl

open Set in
nonrec theorem mem_centralizer_iff {s : Set A} {z : A} :
    z ∈ centralizer R s ↔ ∀ g ∈ s, g * z = z * g ∧ star g * z = z * star g := by
  simp [← SetLike.mem_coe, centralizer_union, ← image_star, mem_centralizer_iff, forall_and]

theorem centralizer_le (s t : Set A) (h : s ⊆ t) : centralizer R t ≤ centralizer R s :=
  Set.centralizer_subset (Set.union_subset_union h <| Set.preimage_mono h)

theorem centralizer_toSubalgebra (s : Set A) :
    (centralizer R s).toSubalgebra = Subalgebra.centralizer R (s ∪ star s):=
  rfl

theorem coe_centralizer_centralizer (s : Set A) :
    (centralizer R (centralizer R s : Set A)) = (s ∪ star s).centralizer.centralizer := by
  rw [coe_centralizer, StarMemClass.star_coe_eq, Set.union_self, coe_centralizer]

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

theorem star_mem_star_iff (S : Subalgebra R A) (x : A) : star x ∈ star S ↔ x ∈ S := by
  simp

@[simp]
theorem coe_star (S : Subalgebra R A) : ((star S : Subalgebra R A) : Set A) = star (S : Set A) :=
  rfl

theorem star_mono : Monotone (star : Subalgebra R A → Subalgebra R A) := fun _ _ h _ hx => h hx

variable (R) in
/-- The star operation on `Subalgebra` commutes with `Algebra.adjoin`. -/
theorem star_adjoin_comm (s : Set A) : star (Algebra.adjoin R s) = Algebra.adjoin R (star s) :=
  have this : ∀ t : Set A, Algebra.adjoin R (star t) ≤ star (Algebra.adjoin R t) := fun _ =>
    Algebra.adjoin_le fun _ hx => Algebra.subset_adjoin hx
  le_antisymm (by simpa only [star_star] using Subalgebra.star_mono (this (star s))) (this s)

/-- The `StarSubalgebra` obtained from `S : Subalgebra R A` by taking the smallest subalgebra
containing both `S` and `star S`. -/
def starClosure (S : Subalgebra R A) : StarSubalgebra R A where
  toSubalgebra := S ⊔ star S
  star_mem' := fun {a} ha => by
    simp only [Subalgebra.mem_carrier, ← (@Algebra.gi R A _ _ _).l_sup_u _ _] at *
    rw [← mem_star_iff _ a, star_adjoin_comm, sup_comm]
    simpa using ha

@[simp]
theorem coe_starClosure (S : Subalgebra R A) :
    (S.starClosure : Set A) = (S ⊔ star S : Subalgebra R A) := rfl

@[simp]
theorem mem_starClosure (S : Subalgebra R A) {x : A} :
    x ∈ S.starClosure ↔ x ∈ S ⊔ star S := Iff.rfl

theorem starClosure_toSubalgebra (S : Subalgebra R A) :
    S.starClosure.toSubalgebra = S ⊔ star S := rfl

theorem starClosure_le {S₁ : Subalgebra R A} {S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂.toSubalgebra) :
    S₁.starClosure ≤ S₂ :=
  StarSubalgebra.toSubalgebra_le_iff.1 <|
    sup_le h fun x hx =>
      (star_star x ▸ star_mem (show star x ∈ S₂ from h <| (S₁.mem_star_iff _).1 hx) : x ∈ S₂)

theorem starClosure_le_iff {S₁ : Subalgebra R A} {S₂ : StarSubalgebra R A} :
    S₁.starClosure ≤ S₂ ↔ S₁ ≤ S₂.toSubalgebra :=
  ⟨fun h => le_sup_left.trans h, starClosure_le⟩

end Subalgebra

/-! ### The star subalgebra generated by a set -/


namespace StarAlgebra

open StarSubalgebra

variable {F R A B : Type*} [CommSemiring R] [StarRing R]
variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]
variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]
variable (R)

/-- The minimal star subalgebra that contains `s`. -/
def adjoin (s : Set A) : StarSubalgebra R A :=
  { Algebra.adjoin R (s ∪ star s) with
    star_mem' := fun hx => by
      rwa [Subalgebra.mem_carrier, ← Subalgebra.mem_star_iff, Subalgebra.star_adjoin_comm,
        Set.union_star, star_star, Set.union_comm] }

theorem adjoin_eq_starClosure_adjoin (s : Set A) : adjoin R s = (Algebra.adjoin R s).starClosure :=
  toSubalgebra_injective <|
    show Algebra.adjoin R (s ∪ star s) = Algebra.adjoin R s ⊔ star (Algebra.adjoin R s) from
      (Subalgebra.star_adjoin_comm R s).symm ▸ Algebra.adjoin_union s (star s)

theorem adjoin_toSubalgebra (s : Set A) :
    (adjoin R s).toSubalgebra = Algebra.adjoin R (s ∪ star s) := rfl

@[simp, aesop safe 20 (rule_sets := [SetLike])]
theorem subset_adjoin (s : Set A) : s ⊆ adjoin R s :=
  Set.subset_union_left.trans Algebra.subset_adjoin

@[simp, aesop safe 20 (rule_sets := [SetLike])]
theorem star_subset_adjoin (s : Set A) : star s ⊆ adjoin R s :=
  Set.subset_union_right.trans Algebra.subset_adjoin

@[aesop 80% (rule_sets := [SetLike])]
theorem mem_adjoin_of_mem {s : Set A} {x : A} (hx : x ∈ s) : x ∈ adjoin R s := subset_adjoin R s hx

theorem self_mem_adjoin_singleton (x : A) : x ∈ adjoin R ({x} : Set A) :=
  Algebra.subset_adjoin <| Set.mem_union_left _ (Set.mem_singleton x)

theorem star_self_mem_adjoin_singleton (x : A) : star x ∈ adjoin R ({x} : Set A) :=
  star_mem <| self_mem_adjoin_singleton R x

variable {R}

protected theorem gc : GaloisConnection (adjoin R : Set A → StarSubalgebra R A) (↑) := by
  intro s S
  rw [← toSubalgebra_le_iff, adjoin_toSubalgebra, Algebra.adjoin_le_iff, coe_toSubalgebra]
  exact
    ⟨fun h => Set.subset_union_left.trans h, fun h =>
      Set.union_subset h fun x hx => star_star x ▸ star_mem (show star x ∈ S from h hx)⟩

/-- Galois insertion between `adjoin` and `coe`. -/
protected def gi : GaloisInsertion (adjoin R : Set A → StarSubalgebra R A) (↑) where
  choice s hs := (adjoin R s).copy s <| le_antisymm (StarAlgebra.gc.le_u_l s) hs
  gc := StarAlgebra.gc
  le_l_u S := (StarAlgebra.gc (S : Set A) (adjoin R S)).1 <| le_rfl
  choice_eq _ _ := StarSubalgebra.copy_eq _ _ _

theorem adjoin_le {S : StarSubalgebra R A} {s : Set A} (hs : s ⊆ S) : adjoin R s ≤ S :=
  StarAlgebra.gc.l_le hs

@[simp]
theorem adjoin_le_iff {S : StarSubalgebra R A} {s : Set A} : adjoin R s ≤ S ↔ s ⊆ S :=
  StarAlgebra.gc _ _

@[gcongr]
theorem adjoin_mono {s t : Set A} (H : s ⊆ t) : adjoin R s ≤ adjoin R t :=
  StarAlgebra.gc.monotone_l H

@[simp]
lemma adjoin_eq (S : StarSubalgebra R A) : adjoin R (S : Set A) = S :=
  le_antisymm (adjoin_le le_rfl) (subset_adjoin R (S : Set A))

open Submodule in
lemma adjoin_eq_span (s : Set A) :
    Subalgebra.toSubmodule (adjoin R s).toSubalgebra = span R (Submonoid.closure (s ∪ star s)) := by
  rw [adjoin_toSubalgebra, Algebra.adjoin_eq_span]

open Submodule in
lemma adjoin_nonUnitalStarSubalgebra_eq_span (s : NonUnitalStarSubalgebra R A) :
    (adjoin R (s : Set A)).toSubalgebra.toSubmodule = span R {1} ⊔ s.toSubmodule := by
  rw [adjoin_eq_span, Submonoid.closure_eq_one_union, span_union,
    ← NonUnitalStarAlgebra.adjoin_eq_span, NonUnitalStarAlgebra.adjoin_eq]

theorem _root_.Subalgebra.starClosure_eq_adjoin (S : Subalgebra R A) :
    S.starClosure = adjoin R (S : Set A) :=
  le_antisymm (Subalgebra.starClosure_le_iff.2 <| subset_adjoin R (S : Set A))
    (adjoin_le (le_sup_left : S ≤ S ⊔ star S))

/-- If some predicate holds for all `x ∈ (s : Set A)` and this predicate is closed under the
`algebraMap`, addition, multiplication and star operations, then it holds for `a ∈ adjoin R s`. -/
@[elab_as_elim]
theorem adjoin_induction {s : Set A} {p : (x : A) → x ∈ adjoin R s → Prop}
    (mem : ∀ (x) (h : x ∈ s), p x (subset_adjoin R s h))
    (algebraMap : ∀ r, p (_root_.algebraMap R _ r) (_root_.algebraMap_mem _ r))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    (star : ∀ x hx, p x hx → p (star x) (star_mem hx))
    {a : A} (ha : a ∈ adjoin R s) : p a ha := by
  refine Algebra.adjoin_induction (fun x hx ↦ ?_) algebraMap add mul ha
  simp only [Set.mem_union, Set.mem_star] at hx
  obtain (hx | hx) := hx
  · exact mem x hx
  · simpa using star _ (Algebra.subset_adjoin (by simpa using Or.inl hx)) (mem _ hx)

@[elab_as_elim]
theorem adjoin_induction₂ {s : Set A} {p : (x y : A) → x ∈ adjoin R s → y ∈ adjoin R s → Prop}
    (mem_mem : ∀ (x) (y) (hx : x ∈ s) (hy : y ∈ s), p x y (subset_adjoin R s hx)
      (subset_adjoin R s hy))
    (algebraMap_both : ∀ r₁ r₂, p (algebraMap R A r₁) (algebraMap R A r₂)
      (_root_.algebraMap_mem _ r₁) (_root_.algebraMap_mem _ r₂))
    (algebraMap_left : ∀ (r) (x) (hx : x ∈ s), p (algebraMap R A r) x (_root_.algebraMap_mem _ r)
      (subset_adjoin R s hx))
    (algebraMap_right : ∀ (r) (x) (hx : x ∈ s), p x (algebraMap R A r) (subset_adjoin R s hx)
      (_root_.algebraMap_mem _ r))
    (add_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x + y) z (add_mem hx hy) hz)
    (add_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y + z) hx (add_mem hy hz))
    (mul_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x * y) z (mul_mem hx hy) hz)
    (mul_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y * z) hx (mul_mem hy hz))
    (star_left : ∀ x y hx hy, p x y hx hy → p (star x) y (star_mem hx) hy)
    (star_right : ∀ x y hx hy, p x y hx hy → p x (star y) hx (star_mem hy))
    {a b : A} (ha : a ∈ adjoin R s) (hb : b ∈ adjoin R s) :
    p a b ha hb := by
  induction hb using adjoin_induction with
  | mem z hz => induction ha using adjoin_induction with
    | mem _ h => exact mem_mem _ _ h hz
    | algebraMap _ => exact algebraMap_left _ _ hz
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
    | star _ _ h => exact star_left _ _ _ _ h
  | algebraMap r =>
    induction ha using adjoin_induction with
    | mem _ h => exact algebraMap_right _ _ h
    | algebraMap _ => exact algebraMap_both _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
    | star _ _ h => exact star_left _ _ _ _ h
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂
  | star _ _ h => exact star_right _ _ _ _ h

/-- The difference with `StarSubalgebra.adjoin_induction` is that this acts on the subtype. -/
@[elab_as_elim]
theorem adjoin_induction_subtype {s : Set A} {p : adjoin R s → Prop} (a : adjoin R s)
    (mem : ∀ (x) (h : x ∈ s), p ⟨x, subset_adjoin R s h⟩) (algebraMap : ∀ r, p (algebraMap R _ r))
    (add : ∀ x y, p x → p y → p (x + y)) (mul : ∀ x y, p x → p y → p (x * y))
    (star : ∀ x, p x → p (star x)) : p a :=
  Subtype.recOn a fun b hb => by
    induction hb using adjoin_induction with
    | mem _ h => exact mem _ h
    | algebraMap _ => exact algebraMap _
    | mul _ _ _ _ h₁ h₂ => exact mul _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add _ _ h₁ h₂
    | star _ _ h => exact star _ h

variable (R)

lemma adjoin_le_centralizer_centralizer (s : Set A) :
    adjoin R s ≤ centralizer R (centralizer R s) := by
  rw [← toSubalgebra_le_iff, centralizer_toSubalgebra, adjoin_toSubalgebra]
  convert Algebra.adjoin_le_centralizer_centralizer R (s ∪ star s)
  rw [StarMemClass.star_coe_eq]
  simp

/-- If all elements of `s : Set A` commute pairwise and also commute pairwise with elements of
`star s`, then `StarSubalgebra.adjoin R s` is commutative. See note [reducible non-instances]. -/
abbrev adjoinCommSemiringOfComm {s : Set A}
    (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a)
    (hcomm_star : ∀ a ∈ s, ∀ b ∈ s, a * star b = star b * a) :
    CommSemiring (adjoin R s) :=
  { (adjoin R s).toSemiring with
    mul_comm := fun ⟨_, h₁⟩ ⟨_, h₂⟩ ↦ by
      have hcomm : ∀ a ∈ s ∪ star s, ∀ b ∈ s ∪ star s, a * b = b * a := fun a ha b hb ↦
        Set.union_star_self_comm (fun _ ha _ hb ↦ hcomm _ hb _ ha)
          (fun _ ha _ hb ↦ hcomm_star _ hb _ ha) b hb a ha
      have := adjoin_le_centralizer_centralizer R s
      apply this at h₁
      apply this at h₂
      rw [← SetLike.mem_coe, coe_centralizer_centralizer] at h₁ h₂
      exact Subtype.ext <| Set.centralizer_centralizer_comm_of_comm hcomm _ h₁ _ h₂ }

/-- If all elements of `s : Set A` commute pairwise and also commute pairwise with elements of
`star s`, then `StarSubalgebra.adjoin R s` is commutative. See note [reducible non-instances]. -/
abbrev adjoinCommRingOfComm (R : Type u) {A : Type v} [CommRing R] [StarRing R] [Ring A]
    [Algebra R A] [StarRing A] [StarModule R A] {s : Set A}
    (hcomm : ∀ a : A, a ∈ s → ∀ b : A, b ∈ s → a * b = b * a)
    (hcomm_star : ∀ a : A, a ∈ s → ∀ b : A, b ∈ s → a * star b = star b * a) :
    CommRing (adjoin R s) :=
  { StarAlgebra.adjoinCommSemiringOfComm R hcomm hcomm_star,
    (adjoin R s).toSubalgebra.toRing with }

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

/-- The star subalgebra `StarSubalgebra.adjoin R {x}` generated by a single `x : A` is commutative
if `x` is normal. -/
instance adjoinCommRingOfIsStarNormal (R : Type u) {A : Type v} [CommRing R] [StarRing R] [Ring A]
    [Algebra R A] [StarRing A] [StarModule R A] (x : A) [IsStarNormal x] :
    CommRing (adjoin R ({x} : Set A)) :=
  { (adjoin R ({x} : Set A)).toSubalgebra.toRing with mul_comm := mul_comm }

end StarAlgebra

/-! ### Complete lattice structure -/

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

@[simp, norm_cast]
theorem coe_top : (↑(⊤ : StarSubalgebra R A) : Set A) = Set.univ :=
  rfl

@[simp]
theorem mem_top {x : A} : x ∈ (⊤ : StarSubalgebra R A) :=
  Set.mem_univ x

@[simp]
theorem top_toSubalgebra : (⊤ : StarSubalgebra R A).toSubalgebra = ⊤ := by ext; simp
-- Porting note: Lean can no longer prove this by `rfl`, it times out

@[simp]
theorem toSubalgebra_eq_top {S : StarSubalgebra R A} : S.toSubalgebra = ⊤ ↔ S = ⊤ :=
  StarSubalgebra.toSubalgebra_injective.eq_iff' top_toSubalgebra

theorem mem_sup_left {S T : StarSubalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S ⊔ T :=
  have : S ≤ S ⊔ T := le_sup_left; (this ·)

theorem mem_sup_right {S T : StarSubalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S ⊔ T :=
  have : T ≤ S ⊔ T := le_sup_right; (this ·)

theorem mul_mem_sup {S T : StarSubalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ T) :
    x * y ∈ S ⊔ T :=
  mul_mem (mem_sup_left hx) (mem_sup_right hy)

theorem map_sup (f : A →⋆ₐ[R] B) (S T : StarSubalgebra R A) : map f (S ⊔ T) = map f S ⊔ map f T :=
  (StarSubalgebra.gc_map_comap f).l_sup

theorem map_inf (f : A →⋆ₐ[R] B) (hf : Function.Injective f) (S T : StarSubalgebra R A) :
    map f (S ⊓ T) = map f S ⊓ map f T := SetLike.coe_injective (Set.image_inter hf)

@[simp, norm_cast]
theorem coe_inf (S T : StarSubalgebra R A) : (↑(S ⊓ T) : Set A) = (S : Set A) ∩ T :=
  rfl

@[simp]
theorem mem_inf {S T : StarSubalgebra R A} {x : A} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T :=
  Iff.rfl

@[simp]
theorem inf_toSubalgebra (S T : StarSubalgebra R A) :
    (S ⊓ T).toSubalgebra = S.toSubalgebra ⊓ T.toSubalgebra := by
  ext; simp
-- Porting note: Lean can no longer prove this by `rfl`, it times out

@[simp, norm_cast]
theorem coe_sInf (S : Set (StarSubalgebra R A)) : (↑(sInf S) : Set A) = ⋂ s ∈ S, ↑s :=
  sInf_image

theorem mem_sInf {S : Set (StarSubalgebra R A)} {x : A} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]

@[simp]
theorem sInf_toSubalgebra (S : Set (StarSubalgebra R A)) :
    (sInf S).toSubalgebra = sInf (StarSubalgebra.toSubalgebra '' S) :=
  SetLike.coe_injective <| by simp

@[simp, norm_cast]
theorem coe_iInf {ι : Sort*} {S : ι → StarSubalgebra R A} : (↑(⨅ i, S i) : Set A) = ⋂ i, S i := by
  simp [iInf]

theorem mem_iInf {ι : Sort*} {S : ι → StarSubalgebra R A} {x : A} :
    (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by simp only [iInf, mem_sInf, Set.forall_mem_range]

theorem map_iInf {ι : Sort*} [Nonempty ι] (f : A →⋆ₐ[R] B) (hf : Function.Injective f)
    (s : ι → StarSubalgebra R A) : map f (iInf s) = ⨅ (i : ι), map f (s i) := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

@[simp]
theorem iInf_toSubalgebra {ι : Sort*} (S : ι → StarSubalgebra R A) :
    (⨅ i, S i).toSubalgebra = ⨅ i, (S i).toSubalgebra :=
  SetLike.coe_injective <| by simp

theorem bot_toSubalgebra : (⊥ : StarSubalgebra R A).toSubalgebra = ⊥ := rfl

theorem mem_bot {x : A} : x ∈ (⊥ : StarSubalgebra R A) ↔ x ∈ Set.range (algebraMap R A) := Iff.rfl

@[simp, norm_cast]
theorem coe_bot : ((⊥ : StarSubalgebra R A) : Set A) = Set.range (algebraMap R A) := rfl

theorem eq_top_iff {S : StarSubalgebra R A} : S = ⊤ ↔ ∀ x : A, x ∈ S :=
  ⟨fun h x => by rw [h]; exact mem_top,
  fun h => by ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩

end StarSubalgebra

namespace StarAlgHom

open StarSubalgebra StarAlgebra

variable {F R A B : Type*} [CommSemiring R] [StarRing R]
variable [Semiring A] [Algebra R A] [StarRing A]
variable [Semiring B] [Algebra R B] [StarRing B]

section
variable [StarModule R A]

theorem ext_adjoin {s : Set A} [FunLike F (adjoin R s) B]
    [AlgHomClass F R (adjoin R s) B] [StarHomClass F (adjoin R s) B] {f g : F}
    (h : ∀ x : adjoin R s, (x : A) ∈ s → f x = g x) : f = g := by
  refine DFunLike.ext f g fun a =>
    adjoin_induction_subtype (p := fun y => f y = g y) a (fun x hx => ?_) (fun r => ?_)
    (fun x y hx hy => ?_) (fun x y hx hy => ?_) fun x hx => ?_
  · exact h ⟨x, subset_adjoin R s hx⟩ hx
  · simp only [AlgHomClass.commutes]
  · simp only [map_add, map_add, hx, hy]
  · simp only [map_mul, map_mul, hx, hy]
  · simp only [map_star, hx]

theorem ext_adjoin_singleton {a : A} [FunLike F (adjoin R ({a} : Set A)) B]
    [AlgHomClass F R (adjoin R ({a} : Set A)) B] [StarHomClass F (adjoin R ({a} : Set A)) B]
    {f g : F} (h : f ⟨a, self_mem_adjoin_singleton R a⟩ = g ⟨a, self_mem_adjoin_singleton R a⟩) :
    f = g :=
  ext_adjoin fun x hx =>
    (show x = ⟨a, self_mem_adjoin_singleton R a⟩ from
          Subtype.ext <| Set.mem_singleton_iff.mp hx).symm ▸
      h

variable [FunLike F A B] [AlgHomClass F R A B] [StarHomClass F A B] (f g : F)

/-- The equalizer of two star `R`-algebra homomorphisms. -/
def equalizer : StarSubalgebra R A where
  toSubalgebra := AlgHom.equalizer (f : A →ₐ[R] B) g
  star_mem' {a} (ha : f a = g a) := by simpa only [← map_star] using congrArg star ha

@[simp]
theorem mem_equalizer (x : A) : x ∈ StarAlgHom.equalizer f g ↔ f x = g x :=
  Iff.rfl

theorem adjoin_le_equalizer {s : Set A} (h : s.EqOn f g) : adjoin R s ≤ StarAlgHom.equalizer f g :=
  adjoin_le h

theorem ext_of_adjoin_eq_top {s : Set A} (h : adjoin R s = ⊤) ⦃f g : F⦄ (hs : s.EqOn f g) : f = g :=
  DFunLike.ext f g fun _x => StarAlgHom.adjoin_le_equalizer f g hs <| h.symm ▸ trivial


variable [StarModule R B]

theorem map_adjoin (f : A →⋆ₐ[R] B) (s : Set A) :
    map f (adjoin R s) = adjoin R (f '' s) :=
  GaloisConnection.l_comm_of_u_comm Set.image_preimage (gc_map_comap f) StarAlgebra.gc
    StarAlgebra.gc fun _ => rfl

/-- Range of a `StarAlgHom` as a star subalgebra. -/
protected def range
    (φ : A →⋆ₐ[R] B) : StarSubalgebra R B where
  toSubalgebra := φ.toAlgHom.range
  star_mem' := by rintro _ ⟨b, rfl⟩; exact ⟨star b, map_star φ b⟩

theorem range_eq_map_top (φ : A →⋆ₐ[R] B) : φ.range = (⊤ : StarSubalgebra R A).map φ :=
  StarSubalgebra.ext fun x =>
    ⟨by rintro ⟨a, ha⟩; exact ⟨a, by simp, ha⟩, by rintro ⟨a, -, ha⟩; exact ⟨a, ha⟩⟩

end

variable [StarModule R B]
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
  ⟨fun H _x _y hxy => H <| Subtype.ext hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy :)⟩

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

variable {R A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A] [Algebra R A]
  [StarModule R A]

/-- Turn a non-unital star subalgebra containing `1` into a `StarSubalgebra`. -/
def NonUnitalStarSubalgebra.toStarSubalgebra (S : NonUnitalStarSubalgebra R A) (h1 : 1 ∈ S) :
    StarSubalgebra R A where
  __ := S
  one_mem' := h1
  algebraMap_mem' r :=
    (Algebra.algebraMap_eq_smul_one (R := R) (A := A) r).symm ▸ SMulMemClass.smul_mem r h1

lemma StarSubalgebra.toNonUnitalStarSubalgebra_toStarSubalgebra (S : StarSubalgebra R A) :
    S.toNonUnitalStarSubalgebra.toStarSubalgebra S.one_mem' = S := by cases S; rfl

lemma NonUnitalStarSubalgebra.toStarSubalgebra_toNonUnitalStarSubalgebra
    (S : NonUnitalStarSubalgebra R A) (h1 : (1 : A) ∈ S) :
    (S.toStarSubalgebra h1).toNonUnitalStarSubalgebra = S := by
  cases S; rfl

variable (R)

lemma NonUnitalStarAlgebra.adjoin_le_starAlgebra_adjoin (s : Set A) :
    adjoin R s ≤ (StarAlgebra.adjoin R s).toNonUnitalStarSubalgebra :=
  adjoin_le <| StarAlgebra.subset_adjoin R s

lemma StarAlgebra.adjoin_nonUnitalStarSubalgebra (s : Set A) :
    adjoin R (NonUnitalStarAlgebra.adjoin R s : Set A) = adjoin R s :=
  le_antisymm
    (adjoin_le <| NonUnitalStarAlgebra.adjoin_le_starAlgebra_adjoin R s)
    (adjoin_le <| (NonUnitalStarAlgebra.subset_adjoin R s).trans <| subset_adjoin R _)
