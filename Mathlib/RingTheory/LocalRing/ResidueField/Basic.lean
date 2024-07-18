/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import Mathlib.RingTheory.LocalRing.ResidueField.Defs

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

end

namespace LocalRing

-- see Note [lower instance priority]
/-- Every ring hom `f : K →+* R` from a division ring `K` to a nontrivial ring `R` is a
local ring hom. -/
instance (priority := 100) {K R} [DivisionRing K] [CommRing R] [Nontrivial R]
    (f : K →+* R) : IsLocalRingHom f where
  map_nonunit r hr := by simpa only [isUnit_iff_ne_zero, ne_eq, map_eq_zero] using hr.ne_zero

section

variable (R) [CommRing R] [LocalRing R] [CommRing S] [LocalRing S] [CommRing T] [LocalRing T]

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

variable {R}

lemma ker_residue : RingHom.ker (residue R) = maximalIdeal R :=
  Ideal.mk_ker

@[simp]
lemma residue_eq_zero_iff (x : R) : residue R x = 0 ↔ x ∈ maximalIdeal R := by
  rw [← RingHom.mem_ker, ker_residue]

lemma residue_ne_zero_iff_isUnit (x : R) : residue R x ≠ 0 ↔ IsUnit x := by
  simp

variable (R)

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
