/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

module


import Mathlib.Algebra.Ring.Subring.Units
import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.Defs

/-!
# Local Ring Properties of Equalizers and Pullbacks

In this file we provide basic lemmas for the equalizers the pullbacks and of ring homomorphisms
and algebra homomorphisms. We show that they preserve the property of being a local ring under
suitable conditions.

## Main definitions

* `RingHom.pullback`: The pullback of two ring homomorphisms `f : R →+* T` and `g : S →+* T`,
  defined as the subring of `R × S` consisting of pairs `(r, s)` such that `f r = g s`.

* `RingHom.pullbackFst`, `RingHom.pullbackSnd`: The canonical projection maps from the
  pullback to `R` and `S`.

## Main results

* `RingHom.isLocalRing_eqLocus`: The equalizer of two ring homomorphisms from a local
  ring is again a local ring.

* `RingHom.isLocalRing_pullback`: The pullback of `f : R →+* T` and `g : S →+* T` is a
  local ring, provided that `R` is a local ring and `g` is a local homomorphism.

-/

@[expose] public section

namespace RingHom

variable {R S T : Type*} [Ring R] [Ring S] [Semiring T]

theorem isLocalRing_eqLocus [IsLocalRing R] (f g : R →+* T) : IsLocalRing (f.eqLocus g) :=
  (f.eqLocus g).subtype.domain_isLocalRing

/-- The subring of pairs `(r, s) : R × S` such that `f r = g s`, i.e.,
  the pullback of `f : R →+* T` and `g : S →+* T` as a subring of `R × S`. -/
abbrev pullback (f : R →+* T) (g : S →+* T) : Subring (R × S) :=
  (f.comp (RingHom.fst R S)).eqLocus <| g.comp (RingHom.snd R S)

/-- The first projection from the pullback of `f : R →+* T` and `g : S →+* T` to `R`. -/
abbrev pullbackFst (f : R →+* T) (g : S →+* T) : f.pullback g →+* R :=
  (RingHom.fst R S).comp (RingHom.pullback f g).subtype

/-- The second projection from the pullback of `f : R →+* T` and `g : S →+* T` to `S`. -/
abbrev pullbackSnd (f : R →+* T) (g : S →+* T) : f.pullback g →+* S :=
  (RingHom.snd R S).comp (f.pullback g).subtype

theorem pullback_comm_sq (f : R →+* T) (g : S →+* T) :
    f.comp (f.pullbackFst g) = g.comp (f.pullbackSnd g) :=
  ext fun x ↦ x.prop

set_option backward.isDefEq.respectTransparency.types false in
theorem isUnit_pullback_mk_iff (f : R →+* T) (g : S →+* T) {a : R × S} (a_in : a ∈ f.pullback g) :
    IsUnit (⟨a, a_in⟩ : f.pullback g) ↔ IsUnit a.1 ∧ IsUnit a.2 := by
  rw [isUnit_eqLocus_mk_iff, Prod.isUnit_iff]

instance isLocalHom_pullbackFst (f : R →+* T) (g : S →+* T) [IsLocalHom g] :
    IsLocalHom (f.pullbackFst g) where
  map_nonunit := fun ⟨⟨_, _⟩, h_in⟩ ha ↦
    (isUnit_pullback_mk_iff f g h_in).mpr ⟨ha, isUnit_of_map_unit g _ (h_in ▸ ha.map f)⟩

instance isLocalHom_pullbackSnd (f : R →+* T) (g : S →+* T) [IsLocalHom f] :
    IsLocalHom (f.pullbackSnd g) where
  map_nonunit := fun ⟨⟨_, _⟩, h_in⟩ ha ↦
    (isUnit_pullback_mk_iff f g h_in).mpr ⟨isUnit_of_map_unit f _ (h_in.symm ▸ ha.map g), ha⟩

theorem surjective_pullbackFst_of_surjective (f : R →+* T) (g : S →+* T)
    (h : Function.Surjective g) : Function.Surjective (f.pullbackFst g) :=
  fun r ↦ by simpa [eq_comm] using h (f r)

theorem surjective_pullbackSnd_of_surjective (f : R →+* T) (g : S →+* T)
    (h : Function.Surjective f) : Function.Surjective (f.pullbackSnd g) :=
  fun s ↦ by simpa [eq_comm] using h (g s)

theorem map_pullbackSnd_ker_pullbackFst_eq (f : R →+* T) (g : S →+* T) :
    Ideal.map (f.pullbackSnd g) (RingHom.ker (f.pullbackFst g)) = RingHom.ker g := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    rintro ⟨⟨_, _⟩, h⟩
    simp at h ⊢; grind
  · intro s hs
    exact Ideal.mem_map_of_mem (f.pullbackSnd g) (x := ⟨(0, s), by simpa using hs.symm⟩)
      (I := RingHom.ker (f.pullbackFst g)) (by simp)

theorem isLocalRing_pullback [IsLocalRing R] (f : R →+* T) (g : S →+* T) [IsLocalHom g] :
    IsLocalRing (f.pullback g) := (f.pullbackFst g).domain_isLocalRing

end RingHom

namespace AlgHom

variable {R A B C : Type*} [CommSemiring R]

section Semiring

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

/-- The subalgebra of pairs `(a, b) : A × B` such that `f a = g b`, i.e.,
  the pullback of f and g as a subalgebra of A × B. -/
abbrev pullback (f : A →ₐ[R] C) (g : B →ₐ[R] C) : Subalgebra R (A × B) := equalizer
  (f.comp (fst R A B)) (g.comp (snd R A B))

/-- The first projection from the pullback of `f` and `g` to `A`. -/
abbrev pullbackFst (f : A →ₐ[R] C) (g : B →ₐ[R] C) : pullback f g →ₐ[R] A :=
  (fst R A B).comp (pullback f g).val

/-- The second projection from the pullback of `f` and `g` to `B`. -/
abbrev pullbackSnd (f : A →ₐ[R] C) (g : B →ₐ[R] C) : pullback f g →ₐ[R] B :=
  (snd R A B).comp (pullback f g).val

theorem pullback_comm_sq (f : A →ₐ[R] C) (g : B →ₐ[R] C) :
    f.comp (pullbackFst f g) = g.comp (pullbackSnd f g) :=
  AlgHom.ext fun x ↦ x.prop

end Semiring

section Ring

variable [Ring A] [Algebra R A] [Ring B] [Algebra R B] [Semiring C] [Algebra R C]

theorem isUnit_pullback_mk_iff (f : A →ₐ[R] C) (g : B →ₐ[R] C) {a : A × B}
    (a_in : a ∈ f.pullback g) : IsUnit (⟨a, a_in⟩ : f.pullback g) ↔
      IsUnit a.1 ∧ IsUnit a.2 :=
  RingHom.isUnit_pullback_mk_iff (f : A →+* C) (g : B →+* C) a_in

theorem surjective_pullbackFst_of_surjective (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h : Function.Surjective g) : Function.Surjective (pullbackFst f g) :=
  RingHom.surjective_pullbackFst_of_surjective (f : A →+* C) (g : B →+* C) h

theorem surjective_pullbackSnd_of_surjective (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h : Function.Surjective f) : Function.Surjective (pullbackSnd f g) :=
  RingHom.surjective_pullbackSnd_of_surjective (f : A →+* C) (g : B →+* C) h

theorem isLocalRing_pullback [IsLocalRing A] (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    [IsLocalHom g] : IsLocalRing (f.pullback g) :=
  RingHom.isLocalRing_pullback (f : A →+* C) (g : B →+* C)

end Ring

end AlgHom
