/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!

# Residue Field of local rings

We prove basic properties of the residue field of a local ring.

-/

variable {R S T : Type*}

namespace LocalRing

section

variable [CommRing R] [LocalRing R] [CommRing S] [LocalRing S] [CommRing T] [LocalRing T]

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

theorem ResidueField.algebraMap_eq : algebraMap R (ResidueField R) = residue R :=
  rfl

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

theorem lift_comp_residue {R S : Type*} [CommRing R] [LocalRing R] [Field S] (f : R →+* S)
    [IsLocalRingHom f] : (lift f).comp (residue R) = f :=
  RingHom.ext fun _ => rfl

@[simp]
theorem lift_residue_apply {R S : Type*} [CommRing R] [LocalRing R] [Field S] (f : R →+* S)
    [IsLocalRingHom f] (x) : lift f (residue R x) = f x :=
  rfl

/-- The map on residue fields induced by a local homomorphism between local rings -/
def map (f : R →+* S) [IsLocalRingHom f] : ResidueField R →+* ResidueField S :=
  Ideal.Quotient.lift (maximalIdeal R) ((Ideal.Quotient.mk _).comp f) fun a ha => by
    erw [Ideal.Quotient.eq_zero_iff_mem]
    exact map_nonunit f a ha

/-- Applying `LocalRing.ResidueField.map` to the identity ring homomorphism gives the identity
ring homomorphism. -/
@[simp]
theorem map_id :
    LocalRing.ResidueField.map (RingHom.id R) = RingHom.id (LocalRing.ResidueField R) :=
  Ideal.Quotient.ringHom_ext <| RingHom.ext fun _ => rfl

/-- The composite of two `LocalRing.ResidueField.map`s is the `LocalRing.ResidueField.map` of the
composite. -/
theorem map_comp (f : T →+* R) (g : R →+* S) [IsLocalRingHom f] [IsLocalRingHom g] :
    LocalRing.ResidueField.map (g.comp f) =
      (LocalRing.ResidueField.map g).comp (LocalRing.ResidueField.map f) :=
  Ideal.Quotient.ringHom_ext <| RingHom.ext fun _ => rfl

theorem map_comp_residue (f : R →+* S) [IsLocalRingHom f] :
    (ResidueField.map f).comp (residue R) = (residue S).comp f :=
  rfl

theorem map_residue (f : R →+* S) [IsLocalRingHom f] (r : R) :
    ResidueField.map f (residue R r) = residue S (f r) :=
  rfl

theorem map_id_apply (x : ResidueField R) : map (RingHom.id R) x = x :=
  DFunLike.congr_fun map_id x

@[simp]
theorem map_map (f : R →+* S) (g : S →+* T) (x : ResidueField R) [IsLocalRingHom f]
    [IsLocalRingHom g] : map g (map f x) = map (g.comp f) x :=
  DFunLike.congr_fun (map_comp f g).symm x

/-- A ring isomorphism defines an isomorphism of residue fields. -/
@[simps apply]
def mapEquiv (f : R ≃+* S) : LocalRing.ResidueField R ≃+* LocalRing.ResidueField S where
  toFun := map (f : R →+* S)
  invFun := map (f.symm : S →+* R)
  left_inv x := by simp only [map_map, RingEquiv.symm_comp, map_id, RingHom.id_apply]
  right_inv x := by simp only [map_map, RingEquiv.comp_symm, map_id, RingHom.id_apply]
  map_mul' := RingHom.map_mul _
  map_add' := RingHom.map_add _

@[simp]
theorem mapEquiv.symm (f : R ≃+* S) : (mapEquiv f).symm = mapEquiv f.symm :=
  rfl

@[simp]
theorem mapEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* T) :
    mapEquiv (e₁.trans e₂) = (mapEquiv e₁).trans (mapEquiv e₂) :=
  RingEquiv.toRingHom_injective <| map_comp (e₁ : R →+* S) (e₂ : S →+* T)

@[simp]
theorem mapEquiv_refl : mapEquiv (RingEquiv.refl R) = RingEquiv.refl _ :=
  RingEquiv.toRingHom_injective map_id

/-- The group homomorphism from `RingAut R` to `RingAut k` where `k`
is the residue field of `R`. -/
@[simps]
def mapAut : RingAut R →* RingAut (LocalRing.ResidueField R) where
  toFun := mapEquiv
  map_mul' e₁ e₂ := mapEquiv_trans e₂ e₁
  map_one' := mapEquiv_refl

section MulSemiringAction

variable (G : Type*) [Group G] [MulSemiringAction G R]

/-- If `G` acts on `R` as a `MulSemiringAction`, then it also acts on `LocalRing.ResidueField R`. -/
instance : MulSemiringAction G (LocalRing.ResidueField R) :=
  MulSemiringAction.compHom _ <| mapAut.comp (MulSemiringAction.toRingAut G R)

@[simp]
theorem residue_smul (g : G) (r : R) : residue R (g • r) = g • residue R r :=
  rfl

end MulSemiringAction

section FiniteDimensional

variable [Algebra R S] [IsLocalRingHom (algebraMap R S)]

noncomputable instance : Algebra (ResidueField R) (ResidueField S) :=
  (ResidueField.map (algebraMap R S)).toAlgebra

noncomputable instance : Algebra R (ResidueField S) :=
  ((ResidueField.map <| algebraMap R S).comp <| residue R).toAlgebra

instance : IsScalarTower R (ResidueField R) (ResidueField S) :=
  IsScalarTower.of_algebraMap_eq (congrFun rfl)

instance finiteDimensional_of_noetherian [IsNoetherian R S] :
    FiniteDimensional (ResidueField R) (ResidueField S) := by
  apply IsNoetherian.iff_fg.mp <|
    isNoetherian_of_tower R (S := ResidueField R) (M := ResidueField S) _
  convert isNoetherian_of_surjective S (Ideal.Quotient.mkₐ R (maximalIdeal S)).toLinearMap
    (LinearMap.range_eq_top.mpr Ideal.Quotient.mk_surjective)
  exact Algebra.algebra_ext _ _ (fun r => rfl)

lemma finite_of_finite [IsNoetherian R S] (hfin : Finite (ResidueField R)) :
    Finite (ResidueField S) := by
  have := @finiteDimensional_of_noetherian R S
  exact FiniteDimensional.finite_of_finite (ResidueField R) (ResidueField S)

end FiniteDimensional

end ResidueField

theorem isLocalRingHom_residue : IsLocalRingHom (LocalRing.residue R) := by
  constructor
  intro a ha
  by_contra h
  erw [Ideal.Quotient.eq_zero_iff_mem.mpr ((LocalRing.mem_maximalIdeal _).mpr h)] at ha
  exact ha.ne_zero rfl

end

end LocalRing
