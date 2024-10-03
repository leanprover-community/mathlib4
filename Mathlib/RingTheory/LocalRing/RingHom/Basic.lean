/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Logic.Equiv.TransferInstance

/-!

# Local rings homomorphisms

We prove basic properties of local rings homomorphisms.

-/

variable {R S T : Type*}
section

variable [Semiring R] [Semiring S] [Semiring T]

instance isLocalRingHom_id (R : Type*) [Semiring R] : IsLocalRingHom (RingHom.id R) where
  map_nonunit _ := id

instance isLocalRingHom_comp (g : S →+* T) (f : R →+* S) [IsLocalRingHom g] [IsLocalRingHom f] :
    IsLocalRingHom (g.comp f) where
  map_nonunit a := IsLocalRingHom.map_nonunit a ∘ IsLocalRingHom.map_nonunit (f a)

instance isLocalRingHom_equiv (f : R ≃+* S) : IsLocalRingHom (f : R →+* S) where
  map_nonunit a ha := by
    convert RingHom.isUnit_map (f.symm : S →+* R) ha
    exact (RingEquiv.symm_apply_apply f a).symm

@[simp]
theorem isUnit_of_map_unit (f : R →+* S) [IsLocalRingHom f] (a) (h : IsUnit (f a)) : IsUnit a :=
  IsLocalRingHom.map_nonunit a h

theorem of_irreducible_map (f : R →+* S) [h : IsLocalRingHom f] {x} (hfx : Irreducible (f x)) :
    Irreducible x :=
  ⟨fun h => hfx.not_unit <| IsUnit.map f h, fun p q hx =>
    let ⟨H⟩ := h
    Or.imp (H p) (H q) <| hfx.isUnit_or_isUnit <| f.map_mul p q ▸ congr_arg f hx⟩

theorem isLocalRingHom_of_comp (f : R →+* S) (g : S →+* T) [IsLocalRingHom (g.comp f)] :
    IsLocalRingHom f :=
  ⟨fun _ ha => (isUnit_map_iff (g.comp f) _).mp (g.isUnit_map ha)⟩

/-- If `f : R →+* S` is a local ring hom, then `R` is a local ring if `S` is. -/
theorem RingHom.domain_localRing {R S : Type*} [CommSemiring R] [CommSemiring S] [H : LocalRing S]
    (f : R →+* S) [IsLocalRingHom f] : LocalRing R := by
  haveI : Nontrivial R := pullback_nonzero f f.map_zero f.map_one
  apply LocalRing.of_nonunits_add
  intro a b
  simp_rw [← map_mem_nonunits_iff f, f.map_add]
  exact LocalRing.nonunits_add

end

section

open LocalRing

variable [CommSemiring R] [LocalRing R] [CommSemiring S] [LocalRing S]

/--
The image of the maximal ideal of the source is contained within the maximal ideal of the target.
-/
theorem map_nonunit (f : R →+* S) [IsLocalRingHom f] (a : R) (h : a ∈ maximalIdeal R) :
    f a ∈ maximalIdeal S := fun H => h <| isUnit_of_map_unit f a H

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
  | _, _, ⟨a, ha, rfl⟩ => map_nonunit f a ha
  tfae_have 2 → 4 := Set.image_subset_iff.1
  tfae_have 3 ↔ 4 := Ideal.map_le_iff_le_comap
  tfae_have 4 → 1 := fun h ↦ ⟨fun x => not_imp_not.1 (@h x)⟩
  tfae_have 1 → 5
  | _ => by ext; exact not_iff_not.2 (isUnit_map_iff f _)
  tfae_have 5 → 4 := fun h ↦ le_of_eq h.symm
  tfae_finish

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

/-- If `f : R →+* S` is a surjective local ring hom, then the induced units map is surjective. -/
theorem surjective_units_map_of_local_ringHom [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (h : IsLocalRingHom f) :
    Function.Surjective (Units.map <| f.toMonoidHom) := by
  intro a
  obtain ⟨b, hb⟩ := hf (a : S)
  use (isUnit_of_map_unit f b (by rw [hb]; exact Units.isUnit _)).unit
  ext
  exact hb

-- see Note [lower instance priority]
/-- Every ring hom `f : K →+* R` from a division ring `K` to a nontrivial ring `R` is a
local ring hom. -/
instance (priority := 100) {K R} [DivisionRing K] [CommRing R] [Nontrivial R]
    (f : K →+* R) : IsLocalRingHom f where
  map_nonunit r hr := by simpa only [isUnit_iff_ne_zero, ne_eq, map_eq_zero] using hr.ne_zero

end LocalRing

namespace RingEquiv

protected theorem localRing {A B : Type*} [CommSemiring A] [LocalRing A] [CommSemiring B]
    (e : A ≃+* B) : LocalRing B :=
  haveI := e.symm.toEquiv.nontrivial
  LocalRing.of_surjective (e : A →+* B) e.surjective

end RingEquiv
