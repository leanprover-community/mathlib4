/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Defs

#align_import ring_theory.ideal.local_ring from "leanprover-community/mathlib"@"ec1c7d810034d4202b0dd239112d1792be9f6fdc"

/-!

# Local rings

## Main definitions

* `LocalRing.ResidueField`: The quotient of a local ring by its maximal ideal.

-/


universe u v w u'

variable {R : Type u} {S : Type v} {T : Type w} {K : Type u'}

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

-- see Note [lower instance priority]
/-- Every ring hom `f : K →+* R` from a division ring `K` to a nontrivial ring `R` is a
local ring hom. -/
instance (priority := 100) {K R} [DivisionRing K] [CommRing R] [Nontrivial R]
    (f : K →+* R) : IsLocalRingHom f where
  map_nonunit r hr := by simpa only [isUnit_iff_ne_zero, ne_eq, map_eq_zero] using hr.ne_zero

section

variable (R) [CommRing R] [LocalRing R] [CommRing S] [LocalRing S] [CommRing T] [LocalRing T]

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

namespace RingEquiv

protected theorem localRing {A B : Type*} [CommSemiring A] [LocalRing A] [CommSemiring B]
    (e : A ≃+* B) : LocalRing B :=
  haveI := e.symm.toEquiv.nontrivial
  LocalRing.of_surjective (e : A →+* B) e.surjective
#align ring_equiv.local_ring RingEquiv.localRing

end RingEquiv
