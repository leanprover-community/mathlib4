/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Maps

/-!

# Local rings homomorphisms

We prove basic properties of local rings homomorphisms.

-/

variable {R S T : Type*}
section

variable [Semiring R] [Semiring S] [Semiring T]

@[instance]
theorem isLocalHom_id (R : Type*) [Semiring R] : IsLocalHom (RingHom.id R) where
  map_nonunit _ := id

-- see note [lower instance priority]
@[instance 100]
theorem isLocalHom_toRingHom {F : Type*} [FunLike F R S]
    [RingHomClass F R S] (f : F) [IsLocalHom f] : IsLocalHom (f : R →+* S) :=
  ⟨IsLocalHom.map_nonunit (f := f)⟩

@[instance]
theorem RingHom.isLocalHom_comp (g : S →+* T) (f : R →+* S) [IsLocalHom g]
    [IsLocalHom f] : IsLocalHom (g.comp f) where
  map_nonunit a := IsLocalHom.map_nonunit a ∘ IsLocalHom.map_nonunit (f := g) (f a)

theorem isLocalHom_of_comp (f : R →+* S) (g : S →+* T) [IsLocalHom (g.comp f)] :
    IsLocalHom f :=
  ⟨fun _ ha => (isUnit_map_iff (g.comp f) _).mp (g.isUnit_map ha)⟩

/-- If `f : R →+* S` is a local ring hom, then `R` is a local ring if `S` is. -/
theorem RingHom.domain_isLocalRing {R S : Type*} [Semiring R] [CommSemiring S] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] : IsLocalRing R := by
  haveI : Nontrivial R := f.domain_nontrivial
  apply IsLocalRing.of_nonunits_add
  intro a b
  simp_rw [← map_mem_nonunits_iff f, f.map_add]
  exact IsLocalRing.nonunits_add

end

section

open IsLocalRing

variable [CommSemiring R] [IsLocalRing R] [CommSemiring S] [IsLocalRing S]

/--
The image of the maximal ideal of the source is contained within the maximal ideal of the target.
-/
theorem map_nonunit (f : R →+* S) [IsLocalHom f] (a : R) (h : a ∈ maximalIdeal R) :
    f a ∈ maximalIdeal S := fun H => h <| isUnit_of_map_unit f a H

end

namespace IsLocalRing

section

variable [CommSemiring R] [IsLocalRing R] [CommSemiring S] [IsLocalRing S]

/-- A ring homomorphism between local rings is a local ring hom iff it reflects units,
i.e. any preimage of a unit is still a unit. -/
@[stacks 07BJ]
theorem local_hom_TFAE (f : R →+* S) :
    List.TFAE
      [IsLocalHom f, f '' (maximalIdeal R).1 ⊆ maximalIdeal S,
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

theorem of_surjective [CommSemiring R] [IsLocalRing R] [Semiring S] [Nontrivial S] (f : R →+* S)
    [IsLocalHom f] (hf : Function.Surjective f) : IsLocalRing S :=
  of_isUnit_or_isUnit_of_isUnit_add (by
    intro a b hab
    obtain ⟨a, rfl⟩ := hf a
    obtain ⟨b, rfl⟩ := hf b
    rw [← map_add] at hab
    exact
      (isUnit_or_isUnit_of_isUnit_add <| IsLocalHom.map_nonunit _ hab).imp f.isUnit_map
        f.isUnit_map)

lemma _root_.IsLocalHom.of_surjective [CommRing R] [CommRing S] [Nontrivial S] [IsLocalRing R]
    (f : R →+* S) (hf : Function.Surjective f) :
    IsLocalHom f := by
  have := IsLocalRing.of_surjective' f ‹_›
  refine ((local_hom_TFAE f).out 3 0).mp ?_
  have := Ideal.comap_isMaximal_of_surjective f hf (K := maximalIdeal S)
  exact ((maximal_ideal_unique R).unique (inferInstanceAs (maximalIdeal R).IsMaximal) this).le

alias _root_.Function.Surjective.isLocalHom := _root_.IsLocalHom.of_surjective

/-- If `f : R →+* S` is a surjective local ring hom, then the induced units map is surjective. -/
theorem surjective_units_map_of_local_ringHom [Semiring R] [Semiring S] (f : R →+* S)
    (hf : Function.Surjective f) (h : IsLocalHom f) :
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
    (f : K →+* R) : IsLocalHom f where
  map_nonunit r hr := by simpa only [isUnit_iff_ne_zero, ne_eq, map_eq_zero] using hr.ne_zero

end IsLocalRing

namespace RingEquiv

protected theorem isLocalRing {A B : Type*} [CommSemiring A] [IsLocalRing A] [Semiring B]
    (e : A ≃+* B) : IsLocalRing B :=
  haveI := e.symm.toEquiv.nontrivial
  IsLocalRing.of_surjective (e : A →+* B) e.surjective

end RingEquiv

instance {R : Type*} [CommRing R] [IsLocalRing R] {n : ℕ} [Nontrivial (ZMod n)] (f : R →+* ZMod n) :
    IsLocalHom f :=
  (ZMod.ringHom_surjective f).isLocalHom
