/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.JacobsonIdeal
import Mathlib.Logic.Equiv.TransferInstance
import Mathlib.Tactic.TFAE

#align_import ring_theory.ideal.local_ring from "leanprover-community/mathlib"@"ec1c7d810034d4202b0dd239112d1792be9f6fdc"

/-!

# Local rings

Define local rings as commutative rings having a unique maximal ideal.

## Main definitions

* `LocalRing`: A predicate on commutative semirings, stating that for any pair of elements that
  adds up to `1`, one of them is a unit. This is shown to be equivalent to the condition that there
  exists a unique maximal ideal.
* `LocalRing.maximalIdeal`: The unique maximal ideal for a local rings. Its carrier set is the
  set of non units.
* `IsLocalRingHom`: A predicate on semiring homomorphisms, requiring that it maps nonunits
  to nonunits. For local rings, this means that the image of the unique maximal ideal is again
  contained in the unique maximal ideal.
* `LocalRing.ResidueField`: The quotient of a local ring by its maximal ideal.

-/


universe u v w u'

variable {R : Type u} {S : Type v} {T : Type w} {K : Type u'}

/-- A semiring is local if it is nontrivial and `a` or `b` is a unit whenever `a + b = 1`.
Note that `LocalRing` is a predicate. -/
class LocalRing (R : Type u) [Semiring R] extends Nontrivial R : Prop where
  of_is_unit_or_is_unit_of_add_one ::
  /-- in a local ring `R`, if `a + b = 1`, then either `a` is a unit or `b` is a unit. In another
    word, for every `a : R`, either `a` is a unit or `1 - a` is a unit. -/
  isUnit_or_isUnit_of_add_one {a b : R} (h : a + b = 1) : IsUnit a ∨ IsUnit b
#align local_ring LocalRing

section CommSemiring

variable [CommSemiring R]

namespace LocalRing

theorem of_isUnit_or_isUnit_of_isUnit_add [Nontrivial R]
    (h : ∀ a b : R, IsUnit (a + b) → IsUnit a ∨ IsUnit b) : LocalRing R :=
  ⟨fun {a b} hab => h a b <| hab.symm ▸ isUnit_one⟩
#align local_ring.of_is_unit_or_is_unit_of_is_unit_add LocalRing.of_isUnit_or_isUnit_of_isUnit_add

/-- A semiring is local if it is nontrivial and the set of nonunits is closed under the addition. -/
theorem of_nonunits_add [Nontrivial R]
    (h : ∀ a b : R, a ∈ nonunits R → b ∈ nonunits R → a + b ∈ nonunits R) : LocalRing R :=
  ⟨fun {a b} hab => or_iff_not_and_not.2 fun H => h a b H.1 H.2 <| hab.symm ▸ isUnit_one⟩
#align local_ring.of_nonunits_add LocalRing.of_nonunits_add

/-- A semiring is local if it has a unique maximal ideal. -/
theorem of_unique_max_ideal (h : ∃! I : Ideal R, I.IsMaximal) : LocalRing R :=
  @of_nonunits_add _ _
    (nontrivial_of_ne (0 : R) 1 <|
      let ⟨I, Imax, _⟩ := h
      fun H : 0 = 1 => Imax.1.1 <| I.eq_top_iff_one.2 <| H ▸ I.zero_mem)
    fun x y hx hy H =>
    let ⟨I, Imax, Iuniq⟩ := h
    let ⟨Ix, Ixmax, Hx⟩ := exists_max_ideal_of_mem_nonunits hx
    let ⟨Iy, Iymax, Hy⟩ := exists_max_ideal_of_mem_nonunits hy
    have xmemI : x ∈ I := Iuniq Ix Ixmax ▸ Hx
    have ymemI : y ∈ I := Iuniq Iy Iymax ▸ Hy
    Imax.1.1 <| I.eq_top_of_isUnit_mem (I.add_mem xmemI ymemI) H
#align local_ring.of_unique_max_ideal LocalRing.of_unique_max_ideal

theorem of_unique_nonzero_prime (h : ∃! P : Ideal R, P ≠ ⊥ ∧ Ideal.IsPrime P) : LocalRing R :=
  of_unique_max_ideal
    (by
      rcases h with ⟨P, ⟨hPnonzero, hPnot_top, _⟩, hPunique⟩
      refine ⟨P, ⟨⟨hPnot_top, ?_⟩⟩, fun M hM => hPunique _ ⟨?_, Ideal.IsMaximal.isPrime hM⟩⟩
      · refine Ideal.maximal_of_no_maximal fun M hPM hM => ne_of_lt hPM ?_
        exact (hPunique _ ⟨ne_bot_of_gt hPM, Ideal.IsMaximal.isPrime hM⟩).symm
      · rintro rfl
        exact hPnot_top (hM.1.2 P (bot_lt_iff_ne_bot.2 hPnonzero)))
#align local_ring.of_unique_nonzero_prime LocalRing.of_unique_nonzero_prime

variable [LocalRing R]

theorem isUnit_or_isUnit_of_isUnit_add {a b : R} (h : IsUnit (a + b)) : IsUnit a ∨ IsUnit b := by
  rcases h with ⟨u, hu⟩
  rw [← Units.inv_mul_eq_one, mul_add] at hu
  apply Or.imp _ _ (isUnit_or_isUnit_of_add_one hu) <;> exact isUnit_of_mul_isUnit_right
#align local_ring.is_unit_or_is_unit_of_is_unit_add LocalRing.isUnit_or_isUnit_of_isUnit_add

theorem nonunits_add {a b : R} (ha : a ∈ nonunits R) (hb : b ∈ nonunits R) : a + b ∈ nonunits R :=
  fun H => not_or_of_not ha hb (isUnit_or_isUnit_of_isUnit_add H)
#align local_ring.nonunits_add LocalRing.nonunits_add

variable (R)

/-- The ideal of elements that are not units. -/
def maximalIdeal : Ideal R where
  carrier := nonunits R
  zero_mem' := zero_mem_nonunits.2 <| zero_ne_one
  add_mem' {_ _} hx hy := nonunits_add hx hy
  smul_mem' _ _ := mul_mem_nonunits_right
#align local_ring.maximal_ideal LocalRing.maximalIdeal

instance maximalIdeal.isMaximal : (maximalIdeal R).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  constructor
  · intro h
    apply h
    exact isUnit_one
  · intro I x _ hx H
    erw [Classical.not_not] at hx
    rcases hx with ⟨u, rfl⟩
    simpa using I.mul_mem_left (↑u⁻¹) H
#align local_ring.maximal_ideal.is_maximal LocalRing.maximalIdeal.isMaximal

theorem maximal_ideal_unique : ∃! I : Ideal R, I.IsMaximal :=
  ⟨maximalIdeal R, maximalIdeal.isMaximal R, fun I hI =>
    hI.eq_of_le (maximalIdeal.isMaximal R).1.1 fun _ hx => hI.1.1 ∘ I.eq_top_of_isUnit_mem hx⟩
#align local_ring.maximal_ideal_unique LocalRing.maximal_ideal_unique

variable {R}

theorem eq_maximalIdeal {I : Ideal R} (hI : I.IsMaximal) : I = maximalIdeal R :=
  ExistsUnique.unique (maximal_ideal_unique R) hI <| maximalIdeal.isMaximal R
#align local_ring.eq_maximal_ideal LocalRing.eq_maximalIdeal

theorem le_maximalIdeal {J : Ideal R} (hJ : J ≠ ⊤) : J ≤ maximalIdeal R := by
  rcases Ideal.exists_le_maximal J hJ with ⟨M, hM1, hM2⟩
  rwa [← eq_maximalIdeal hM1]
#align local_ring.le_maximal_ideal LocalRing.le_maximalIdeal

@[simp]
theorem mem_maximalIdeal (x) : x ∈ maximalIdeal R ↔ x ∈ nonunits R :=
  Iff.rfl
#align local_ring.mem_maximal_ideal LocalRing.mem_maximalIdeal

theorem isField_iff_maximalIdeal_eq : IsField R ↔ maximalIdeal R = ⊥ :=
  not_iff_not.mp
    ⟨Ring.ne_bot_of_isMaximal_of_not_isField inferInstance, fun h =>
      Ring.not_isField_iff_exists_prime.mpr ⟨_, h, Ideal.IsMaximal.isPrime' _⟩⟩
#align local_ring.is_field_iff_maximal_ideal_eq LocalRing.isField_iff_maximalIdeal_eq

end LocalRing

end CommSemiring

section CommRing

variable [CommRing R]

namespace LocalRing

theorem of_isUnit_or_isUnit_one_sub_self [Nontrivial R] (h : ∀ a : R, IsUnit a ∨ IsUnit (1 - a)) :
    LocalRing R :=
  ⟨fun {a b} hab => add_sub_cancel_left a b ▸ hab.symm ▸ h a⟩
#align local_ring.of_is_unit_or_is_unit_one_sub_self LocalRing.of_isUnit_or_isUnit_one_sub_self

variable [LocalRing R]

theorem isUnit_or_isUnit_one_sub_self (a : R) : IsUnit a ∨ IsUnit (1 - a) :=
  isUnit_or_isUnit_of_isUnit_add <| (add_sub_cancel a 1).symm ▸ isUnit_one
#align local_ring.is_unit_or_is_unit_one_sub_self LocalRing.isUnit_or_isUnit_one_sub_self

theorem isUnit_of_mem_nonunits_one_sub_self (a : R) (h : 1 - a ∈ nonunits R) : IsUnit a :=
  or_iff_not_imp_right.1 (isUnit_or_isUnit_one_sub_self a) h
#align local_ring.is_unit_of_mem_nonunits_one_sub_self LocalRing.isUnit_of_mem_nonunits_one_sub_self

theorem isUnit_one_sub_self_of_mem_nonunits (a : R) (h : a ∈ nonunits R) : IsUnit (1 - a) :=
  or_iff_not_imp_left.1 (isUnit_or_isUnit_one_sub_self a) h
#align local_ring.is_unit_one_sub_self_of_mem_nonunits LocalRing.isUnit_one_sub_self_of_mem_nonunits

theorem of_surjective' [CommRing S] [Nontrivial S] (f : R →+* S) (hf : Function.Surjective f) :
    LocalRing S :=
  of_isUnit_or_isUnit_one_sub_self (by
    intro b
    obtain ⟨a, rfl⟩ := hf b
    apply (isUnit_or_isUnit_one_sub_self a).imp <| RingHom.isUnit_map _
    rw [← f.map_one, ← f.map_sub]
    apply f.isUnit_map)
#align local_ring.of_surjective' LocalRing.of_surjective'

theorem maximalIdeal_le_jacobson (I : Ideal R) :
    LocalRing.maximalIdeal R ≤ I.jacobson :=
  le_sInf fun _ ⟨_, h⟩ => le_of_eq (LocalRing.eq_maximalIdeal h).symm

theorem jacobson_eq_maximalIdeal (I : Ideal R) (h : I ≠ ⊤) :
    I.jacobson = LocalRing.maximalIdeal R :=
  le_antisymm (sInf_le ⟨le_maximalIdeal h, maximalIdeal.isMaximal R⟩)
              (maximalIdeal_le_jacobson I)
#align local_ring.jacobson_eq_maximal_ideal LocalRing.jacobson_eq_maximalIdeal

end LocalRing

end CommRing

/-- A local ring homomorphism is a homomorphism `f` between local rings such that `a` in the domain
  is a unit if `f a` is a unit for any `a`. See `LocalRing.local_hom_TFAE` for other equivalent
  definitions. -/
class IsLocalRingHom [Semiring R] [Semiring S] (f : R →+* S) : Prop where
  /-- A local ring homomorphism `f : R ⟶ S` will send nonunits of `R` to nonunits of `S`. -/
  map_nonunit : ∀ a, IsUnit (f a) → IsUnit a
#align is_local_ring_hom IsLocalRingHom

section

variable [Semiring R] [Semiring S] [Semiring T]

instance isLocalRingHom_id (R : Type*) [Semiring R] : IsLocalRingHom (RingHom.id R) where
  map_nonunit _ := id
#align is_local_ring_hom_id isLocalRingHom_id

@[simp]
theorem isUnit_map_iff (f : R →+* S) [IsLocalRingHom f] (a) : IsUnit (f a) ↔ IsUnit a :=
  ⟨IsLocalRingHom.map_nonunit a, f.isUnit_map⟩
#align is_unit_map_iff isUnit_map_iff

-- Porting note: as this can be proved by other `simp` lemmas, this is marked as high priority.
@[simp (high)]
theorem map_mem_nonunits_iff (f : R →+* S) [IsLocalRingHom f] (a) :
    f a ∈ nonunits S ↔ a ∈ nonunits R :=
  ⟨fun h ha => h <| (isUnit_map_iff f a).mpr ha, fun h ha => h <| (isUnit_map_iff f a).mp ha⟩
#align map_mem_nonunits_iff map_mem_nonunits_iff

instance isLocalRingHom_comp (g : S →+* T) (f : R →+* S) [IsLocalRingHom g] [IsLocalRingHom f] :
    IsLocalRingHom (g.comp f) where
  map_nonunit a := IsLocalRingHom.map_nonunit a ∘ IsLocalRingHom.map_nonunit (f a)
#align is_local_ring_hom_comp isLocalRingHom_comp

instance isLocalRingHom_equiv (f : R ≃+* S) : IsLocalRingHom (f : R →+* S) where
  map_nonunit a ha := by
    convert RingHom.isUnit_map (f.symm : S →+* R) ha
    exact (RingEquiv.symm_apply_apply f a).symm
#align is_local_ring_hom_equiv isLocalRingHom_equiv

@[simp]
theorem isUnit_of_map_unit (f : R →+* S) [IsLocalRingHom f] (a) (h : IsUnit (f a)) : IsUnit a :=
  IsLocalRingHom.map_nonunit a h
#align is_unit_of_map_unit isUnit_of_map_unit

theorem of_irreducible_map (f : R →+* S) [h : IsLocalRingHom f] {x} (hfx : Irreducible (f x)) :
    Irreducible x :=
  ⟨fun h => hfx.not_unit <| IsUnit.map f h, fun p q hx =>
    let ⟨H⟩ := h
    Or.imp (H p) (H q) <| hfx.isUnit_or_isUnit <| f.map_mul p q ▸ congr_arg f hx⟩
#align of_irreducible_map of_irreducible_map

theorem isLocalRingHom_of_comp (f : R →+* S) (g : S →+* T) [IsLocalRingHom (g.comp f)] :
    IsLocalRingHom f :=
  ⟨fun _ ha => (isUnit_map_iff (g.comp f) _).mp (g.isUnit_map ha)⟩
#align is_local_ring_hom_of_comp isLocalRingHom_of_comp

/-- If `f : R →+* S` is a local ring hom, then `R` is a local ring if `S` is. -/
theorem RingHom.domain_localRing {R S : Type*} [CommSemiring R] [CommSemiring S] [H : LocalRing S]
    (f : R →+* S) [IsLocalRingHom f] : LocalRing R := by
  haveI : Nontrivial R := pullback_nonzero f f.map_zero f.map_one
  apply LocalRing.of_nonunits_add
  intro a b
  simp_rw [← map_mem_nonunits_iff f, f.map_add]
  exact LocalRing.nonunits_add
#align ring_hom.domain_local_ring RingHom.domain_localRing

end

section

open LocalRing

variable [CommSemiring R] [LocalRing R] [CommSemiring S] [LocalRing S]

/--
The image of the maximal ideal of the source is contained within the maximal ideal of the target.
-/
theorem map_nonunit (f : R →+* S) [IsLocalRingHom f] (a : R) (h : a ∈ maximalIdeal R) :
    f a ∈ maximalIdeal S := fun H => h <| isUnit_of_map_unit f a H
#align map_nonunit map_nonunit

end

namespace LocalRing

section

variable [CommSemiring R] [LocalRing R] [CommSemiring S] [LocalRing S]

/-- A ring homomorphism between local rings is a local ring hom iff it reflects units,
i.e. any preimage of a unit is still a unit. https://stacks.math.columbia.edu/tag/07BJ
-/
theorem local_hom_TFAE (f : R →+* S) :
    List.TFAE
      [IsLocalRingHom f, f '' (maximalIdeal R).1 ⊆ maximalIdeal S,
        (maximalIdeal R).map f ≤ maximalIdeal S, maximalIdeal R ≤ (maximalIdeal S).comap f,
        (maximalIdeal S).comap f = maximalIdeal R] := by
  tfae_have 1 → 2
  · rintro _ _ ⟨a, ha, rfl⟩
    exact map_nonunit f a ha
  tfae_have 2 → 4
  · exact Set.image_subset_iff.1
  tfae_have 3 ↔ 4
  · exact Ideal.map_le_iff_le_comap
  tfae_have 4 → 1
  · intro h
    constructor
    exact fun x => not_imp_not.1 (@h x)
  tfae_have 1 → 5
  · intro
    ext
    exact not_iff_not.2 (isUnit_map_iff f _)
  tfae_have 5 → 4
  · exact fun h => le_of_eq h.symm
  tfae_finish
#align local_ring.local_hom_tfae LocalRing.local_hom_TFAE

end

theorem of_surjective [CommSemiring R] [LocalRing R] [CommSemiring S] [Nontrivial S] (f : R →+* S)
    [IsLocalRingHom f] (hf : Function.Surjective f) : LocalRing S :=
  of_isUnit_or_isUnit_of_isUnit_add (by
    intro a b hab
    obtain ⟨a, rfl⟩ := hf a
    obtain ⟨b, rfl⟩ := hf b
    rw [← map_add] at hab
    exact
      (isUnit_or_isUnit_of_isUnit_add <| IsLocalRingHom.map_nonunit _ hab).imp f.isUnit_map
        f.isUnit_map)
#align local_ring.of_surjective LocalRing.of_surjective

/-- If `f : R →+* S` is a surjective local ring hom, then the induced units map is surjective. -/
theorem surjective_units_map_of_local_ringHom [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (h : IsLocalRingHom f) :
    Function.Surjective (Units.map <| f.toMonoidHom) := by
  intro a
  obtain ⟨b, hb⟩ := hf (a : S)
  use (isUnit_of_map_unit f b (by rw [hb]; exact Units.isUnit _)).unit
  ext
  exact hb
#align local_ring.surjective_units_map_of_local_ring_hom LocalRing.surjective_units_map_of_local_ringHom

section

variable (R) [CommRing R] [LocalRing R] [CommRing S] [LocalRing S] [CommRing T] [LocalRing T]

/-- The residue field of a local ring is the quotient of the ring by its maximal ideal. -/
def ResidueField :=
  R ⧸ maximalIdeal R
#align local_ring.residue_field LocalRing.ResidueField

-- Porting note: failed at `deriving` instances automatically
instance ResidueFieldCommRing : CommRing (ResidueField R) :=
  show CommRing (R ⧸ maximalIdeal R) from inferInstance

instance ResidueFieldInhabited : Inhabited (ResidueField R) :=
  show Inhabited (R ⧸ maximalIdeal R) from inferInstance

noncomputable instance ResidueField.field : Field (ResidueField R) :=
  Ideal.Quotient.field (maximalIdeal R)
#align local_ring.residue_field.field LocalRing.ResidueField.field

/-- The quotient map from a local ring to its residue field. -/
def residue : R →+* ResidueField R :=
  Ideal.Quotient.mk _
#align local_ring.residue LocalRing.residue

instance ResidueField.algebra : Algebra R (ResidueField R) :=
  Ideal.Quotient.algebra _
#align local_ring.residue_field.algebra LocalRing.ResidueField.algebra

theorem ResidueField.algebraMap_eq : algebraMap R (ResidueField R) = residue R :=
  rfl
#align local_ring.residue_field.algebra_map_eq LocalRing.ResidueField.algebraMap_eq

instance : IsLocalRingHom (LocalRing.residue R) :=
  ⟨fun _ ha =>
    Classical.not_not.mp (Ideal.Quotient.eq_zero_iff_mem.not.mp (isUnit_iff_ne_zero.mp ha))⟩

variable {R}

namespace ResidueField

/-- A local ring homomorphism into a field can be descended onto the residue field. -/
def lift {R S : Type*} [CommRing R] [LocalRing R] [Field S] (f : R →+* S) [IsLocalRingHom f] :
    LocalRing.ResidueField R →+* S :=
  Ideal.Quotient.lift _ f fun a ha =>
    by_contradiction fun h => ha (isUnit_of_map_unit f a (isUnit_iff_ne_zero.mpr h))
#align local_ring.residue_field.lift LocalRing.ResidueField.lift

theorem lift_comp_residue {R S : Type*} [CommRing R] [LocalRing R] [Field S] (f : R →+* S)
    [IsLocalRingHom f] : (lift f).comp (residue R) = f :=
  RingHom.ext fun _ => rfl
#align local_ring.residue_field.lift_comp_residue LocalRing.ResidueField.lift_comp_residue

@[simp]
theorem lift_residue_apply {R S : Type*} [CommRing R] [LocalRing R] [Field S] (f : R →+* S)
    [IsLocalRingHom f] (x) : lift f (residue R x) = f x :=
  rfl
#align local_ring.residue_field.lift_residue_apply LocalRing.ResidueField.lift_residue_apply

/-- The map on residue fields induced by a local homomorphism between local rings -/
def map (f : R →+* S) [IsLocalRingHom f] : ResidueField R →+* ResidueField S :=
  Ideal.Quotient.lift (maximalIdeal R) ((Ideal.Quotient.mk _).comp f) fun a ha => by
    erw [Ideal.Quotient.eq_zero_iff_mem]
    exact map_nonunit f a ha
#align local_ring.residue_field.map LocalRing.ResidueField.map

/-- Applying `LocalRing.ResidueField.map` to the identity ring homomorphism gives the identity
ring homomorphism. -/
@[simp]
theorem map_id :
    LocalRing.ResidueField.map (RingHom.id R) = RingHom.id (LocalRing.ResidueField R) :=
  Ideal.Quotient.ringHom_ext <| RingHom.ext fun _ => rfl
#align local_ring.residue_field.map_id LocalRing.ResidueField.map_id

/-- The composite of two `LocalRing.ResidueField.map`s is the `LocalRing.ResidueField.map` of the
composite. -/
theorem map_comp (f : T →+* R) (g : R →+* S) [IsLocalRingHom f] [IsLocalRingHom g] :
    LocalRing.ResidueField.map (g.comp f) =
      (LocalRing.ResidueField.map g).comp (LocalRing.ResidueField.map f) :=
  Ideal.Quotient.ringHom_ext <| RingHom.ext fun _ => rfl
#align local_ring.residue_field.map_comp LocalRing.ResidueField.map_comp

theorem map_comp_residue (f : R →+* S) [IsLocalRingHom f] :
    (ResidueField.map f).comp (residue R) = (residue S).comp f :=
  rfl
#align local_ring.residue_field.map_comp_residue LocalRing.ResidueField.map_comp_residue

theorem map_residue (f : R →+* S) [IsLocalRingHom f] (r : R) :
    ResidueField.map f (residue R r) = residue S (f r) :=
  rfl
#align local_ring.residue_field.map_residue LocalRing.ResidueField.map_residue

theorem map_id_apply (x : ResidueField R) : map (RingHom.id R) x = x :=
  DFunLike.congr_fun map_id x
#align local_ring.residue_field.map_id_apply LocalRing.ResidueField.map_id_apply

@[simp]
theorem map_map (f : R →+* S) (g : S →+* T) (x : ResidueField R) [IsLocalRingHom f]
    [IsLocalRingHom g] : map g (map f x) = map (g.comp f) x :=
  DFunLike.congr_fun (map_comp f g).symm x
#align local_ring.residue_field.map_map LocalRing.ResidueField.map_map

/-- A ring isomorphism defines an isomorphism of residue fields. -/
@[simps apply]
def mapEquiv (f : R ≃+* S) : LocalRing.ResidueField R ≃+* LocalRing.ResidueField S where
  toFun := map (f : R →+* S)
  invFun := map (f.symm : S →+* R)
  left_inv x := by simp only [map_map, RingEquiv.symm_comp, map_id, RingHom.id_apply]
  right_inv x := by simp only [map_map, RingEquiv.comp_symm, map_id, RingHom.id_apply]
  map_mul' := RingHom.map_mul _
  map_add' := RingHom.map_add _
#align local_ring.residue_field.map_equiv LocalRing.ResidueField.mapEquiv

@[simp]
theorem mapEquiv.symm (f : R ≃+* S) : (mapEquiv f).symm = mapEquiv f.symm :=
  rfl
#align local_ring.residue_field.map_equiv.symm LocalRing.ResidueField.mapEquiv.symm

@[simp]
theorem mapEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* T) :
    mapEquiv (e₁.trans e₂) = (mapEquiv e₁).trans (mapEquiv e₂) :=
  RingEquiv.toRingHom_injective <| map_comp (e₁ : R →+* S) (e₂ : S →+* T)
#align local_ring.residue_field.map_equiv_trans LocalRing.ResidueField.mapEquiv_trans

@[simp]
theorem mapEquiv_refl : mapEquiv (RingEquiv.refl R) = RingEquiv.refl _ :=
  RingEquiv.toRingHom_injective map_id
#align local_ring.residue_field.map_equiv_refl LocalRing.ResidueField.mapEquiv_refl

/-- The group homomorphism from `RingAut R` to `RingAut k` where `k`
is the residue field of `R`. -/
@[simps]
def mapAut : RingAut R →* RingAut (LocalRing.ResidueField R) where
  toFun := mapEquiv
  map_mul' e₁ e₂ := mapEquiv_trans e₂ e₁
  map_one' := mapEquiv_refl
#align local_ring.residue_field.map_aut LocalRing.ResidueField.mapAut

section MulSemiringAction

variable (G : Type*) [Group G] [MulSemiringAction G R]

/-- If `G` acts on `R` as a `MulSemiringAction`, then it also acts on `LocalRing.ResidueField R`. -/
instance : MulSemiringAction G (LocalRing.ResidueField R) :=
  MulSemiringAction.compHom _ <| mapAut.comp (MulSemiringAction.toRingAut G R)

@[simp]
theorem residue_smul (g : G) (r : R) : residue R (g • r) = g • residue R r :=
  rfl
#align local_ring.residue_field.residue_smul LocalRing.ResidueField.residue_smul

end MulSemiringAction

end ResidueField

theorem ker_eq_maximalIdeal [Field K] (φ : R →+* K) (hφ : Function.Surjective φ) :
    RingHom.ker φ = maximalIdeal R :=
  LocalRing.eq_maximalIdeal <| (RingHom.ker_isMaximal_of_surjective φ) hφ
#align local_ring.ker_eq_maximal_ideal LocalRing.ker_eq_maximalIdeal

theorem isLocalRingHom_residue : IsLocalRingHom (LocalRing.residue R) := by
  constructor
  intro a ha
  by_contra h
  erw [Ideal.Quotient.eq_zero_iff_mem.mpr ((LocalRing.mem_maximalIdeal _).mpr h)] at ha
  exact ha.ne_zero rfl
#align local_ring.is_local_ring_hom_residue LocalRing.isLocalRingHom_residue

end

end LocalRing

namespace Field

variable (K) [Field K]

open scoped Classical

-- see Note [lower instance priority]
instance (priority := 100) : LocalRing K :=
  LocalRing.of_isUnit_or_isUnit_one_sub_self fun a =>
    if h : a = 0 then Or.inr (by rw [h, sub_zero]; exact isUnit_one)
    else Or.inl <| IsUnit.mk0 a h

end Field

theorem LocalRing.maximalIdeal_eq_bot {R : Type*} [Field R] : LocalRing.maximalIdeal R = ⊥ :=
  LocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField R)
#align local_ring.maximal_ideal_eq_bot LocalRing.maximalIdeal_eq_bot

namespace RingEquiv

protected theorem localRing {A B : Type*} [CommSemiring A] [LocalRing A] [CommSemiring B]
    (e : A ≃+* B) : LocalRing B :=
  haveI := e.symm.toEquiv.nontrivial
  LocalRing.of_surjective (e : A →+* B) e.surjective
#align ring_equiv.local_ring RingEquiv.localRing

end RingEquiv
