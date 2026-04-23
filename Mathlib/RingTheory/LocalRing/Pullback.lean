/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

module

public import Mathlib.Algebra.AddTorsor.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Local Ring Properties of Equalizers and Pullbacks

In this file we provide basic lemmas for the equalizers the pullbacks and of ring homomorphisms
and algebra homomorphisms. We show that they preserve the property of being a local ring
under suitable conditions.

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

theorem isUnit_eqLocus_mk_iff (f g : R →+* T) {r : R} (r_in : r ∈ f.eqLocus g) :
    IsUnit (⟨r, r_in⟩ : f.eqLocus g) ↔ IsUnit r := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp [isUnit_iff_exists, ← Subtype.val_inj] at h ⊢
    grind
  rw [mem_eqLocus] at r_in
  obtain ⟨s, hs⟩ := isUnit_iff_exists.mp h
  simp only [isUnit_iff_exists, ← Subtype.val_inj, Subring.coe_mul, OneMemClass.coe_one,
    Subtype.exists, mem_eqLocus, exists_and_left, exists_prop]
  refine ⟨s, hs.left, ?_, hs.right⟩
  rw [← mul_one (f s), ← map_one g, ← hs.left, map_mul, ← mul_assoc, ← r_in, ← map_mul, hs.right,
    map_one, one_mul]

theorem isLocalRing_eqLocus [IsLocalRing R] (f g : R →+* T) : IsLocalRing (f.eqLocus g) :=
  Subring.isLocalRing_of_unit _ fun _ h ↦ (RingHom.isUnit_eqLocus_mk_iff f g h).mpr

/-- The subring of pairs `(r, s) : R × S` such that `f r = g s`, i.e.,
  the pullback of f and g as a subring of R × S. -/
abbrev pullback (f : R →+* T) (g : S →+* T) : Subring (R × S) :=
  (f.comp (RingHom.fst R S)).eqLocus <| g.comp (RingHom.snd R S)

/-- The first projection from the pullback of `f` and `g` to `A`. -/
abbrev pullbackFst (f : R →+* T) (g : S →+* T) : f.pullback g →+* R :=
  (RingHom.fst R S).comp (RingHom.pullback f g).subtype

/-- The second projection from the pullback of `f` and `g` to `B`. -/
abbrev pullbackSnd (f : R →+* T) (g : S →+* T) : f.pullback g →+* S :=
  (RingHom.snd R S).comp (f.pullback g).subtype

theorem pullback_comm_sq (f : R →+* T) (g : S →+* T) :
    f.comp (f.pullbackFst g) = g.comp (f.pullbackSnd g) := ext fun x ↦ x.prop

theorem isUnit_pullback_mk_iff (f : R →+* T) (g : S →+* T) {a : R × S} (a_in : a ∈ f.pullback g) :
    IsUnit (⟨a, a_in⟩ : f.pullback g) ↔ IsUnit a.1 ∧ IsUnit a.2 := by
  rw [isUnit_eqLocus_mk_iff, Prod.isUnit_iff]

theorem isLocalHom_pullbackFst (f : R →+* T) (g : S →+* T) [IsLocalHom g] :
    IsLocalHom (f.pullbackFst g) where
  map_nonunit a ha := by
    rcases a with ⟨⟨r, s⟩, hrs⟩
    exact (isUnit_pullback_mk_iff f g _).mpr ⟨ha, isUnit_of_map_unit g _ (hrs ▸ ha.map f)⟩

theorem isLocalHom_pullbackSnd (f : R →+* T) (g : S →+* T) [IsLocalHom f] :
    IsLocalHom (f.pullbackSnd g) where
  map_nonunit a ha := by
    rcases a with ⟨⟨r, s⟩, hrs⟩
    exact (isUnit_pullback_mk_iff f g _).mpr ⟨isUnit_of_map_unit f _ (hrs.symm ▸ ha.map g), ha⟩

theorem surjective_pullbackFst_of_surjective (f : R →+* T) (g : S →+* T)
    (h : Function.Surjective g) : Function.Surjective (f.pullbackFst g) :=
  fun r ↦ by simpa [eq_comm] using h (f r)

theorem surjective_pullbackSnd_of_surjective (f : R →+* T) (g : S →+* T)
    (h : Function.Surjective f) : Function.Surjective (f.pullbackSnd g) :=
  fun s ↦ by simpa [eq_comm] using h (g s)

theorem isLocalRing_pullback [IsLocalRing R] (f : R →+* T) (g : S →+* T) (hg : IsLocalHom g) :
    IsLocalRing (RingHom.pullback (f : R →+* T) (g : S →+* T)) where
  isUnit_or_isUnit_of_add_one {a b} h := by
    rcases a with ⟨⟨u, v⟩, huv⟩; rcases b with ⟨⟨s, t⟩, hst⟩
    simp only [AddMemClass.mk_add_mk, Prod.mk_add_mk, ← Subtype.val_inj, OneMemClass.coe_one,
      Prod.mk_eq_one] at h
    simp only [RingHom.mem_eqLocus, RingHom.coe_comp, RingHom.coe_fst, Function.comp_apply,
      RingHom.coe_snd] at huv hst
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one h.left with hu | hs
    · have : IsUnit (g v) := by rw [← huv]; exact IsUnit.map f hu
      apply IsLocalHom.map_nonunit at this
      left; simpa [isUnit_pullback_mk_iff] using ⟨hu, this⟩
    have : IsUnit (g t) := by rw [← hst]; exact IsUnit.map f hs
    apply IsLocalHom.map_nonunit at this
    right; simpa [isUnit_pullback_mk_iff] using ⟨hs, this⟩

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

theorem isLocalRing_pullback [IsLocalRing A] (f : A →ₐ[R] C) (g : B →ₐ[R] C) (hg : IsLocalHom g) :
    IsLocalRing (AlgHom.pullback f g) :=
  RingHom.isLocalRing_pullback f.toRingHom g.toRingHom ⟨hg.map_nonunit⟩

end Ring

end AlgHom
