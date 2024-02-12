/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

#align_import ring_theory.bezout from "leanprover-community/mathlib"@"6623e6af705e97002a9054c1c05a980180276fc1"

/-!

# Bézout rings

A Bézout ring (Bezout ring) is a ring whose finitely generated ideals are principal.
Notable examples include principal ideal rings, valuation rings, and the ring of algebraic integers.

## Main results
- `IsBezout.iff_span_pair_isPrincipal`: It suffices to verify every `span {x, y}` is principal.
- `IsBezout.toGCDDomain`: Every Bézout domain is a GCD domain. This is not an instance.
- `IsBezout.TFAE`: For a Bézout domain, noetherian ↔ PID ↔ UFD ↔ ACCP

-/


universe u v

variable (R : Type u) [CommRing R]

/-- A Bézout ring is a ring whose finitely generated ideals are principal. -/
class IsBezout : Prop where
  /-- Any finitely generated ideal is principal. -/
  isPrincipal_of_FG : ∀ I : Ideal R, I.FG → I.IsPrincipal
#align is_bezout IsBezout

namespace IsBezout

variable {R}

instance span_pair_isPrincipal [IsBezout R] (x y : R) : (Ideal.span {x, y} : Ideal R).IsPrincipal :=
  by classical exact isPrincipal_of_FG (Ideal.span {x, y}) ⟨{x, y}, by simp⟩
#align is_bezout.span_pair_is_principal IsBezout.span_pair_isPrincipal

theorem iff_span_pair_isPrincipal :
    IsBezout R ↔ ∀ x y : R, (Ideal.span {x, y} : Ideal R).IsPrincipal := by
  classical
    constructor
    · intro H x y; infer_instance
    · intro H
      constructor
      apply Submodule.fg_induction
      · exact fun _ => ⟨⟨_, rfl⟩⟩
      · rintro _ _ ⟨⟨x, rfl⟩⟩ ⟨⟨y, rfl⟩⟩; rw [← Submodule.span_insert]; exact H _ _
#align is_bezout.iff_span_pair_is_principal IsBezout.iff_span_pair_isPrincipal

section Gcd

variable [IsBezout R]

/-- The gcd of two elements in a bezout domain. -/
noncomputable def gcd (x y : R) : R := Submodule.IsPrincipal.generator (Ideal.span {x, y})
#align is_bezout.gcd IsBezout.gcd

theorem span_gcd (x y : R) : (Ideal.span {gcd x y} : Ideal R) = Ideal.span {x, y} :=
  Ideal.span_singleton_generator _
#align is_bezout.span_gcd IsBezout.span_gcd

theorem gcd_dvd_left (x y : R) : gcd x y ∣ x :=
  (Submodule.IsPrincipal.mem_iff_generator_dvd _).mp (Ideal.subset_span (by simp))
#align is_bezout.gcd_dvd_left IsBezout.gcd_dvd_left

theorem gcd_dvd_right (x y : R) : gcd x y ∣ y :=
  (Submodule.IsPrincipal.mem_iff_generator_dvd _).mp (Ideal.subset_span (by simp))
#align is_bezout.gcd_dvd_right IsBezout.gcd_dvd_right

theorem dvd_gcd {x y z : R} (hx : z ∣ x) (hy : z ∣ y) : z ∣ gcd x y := by
  rw [← Ideal.span_singleton_le_span_singleton] at hx hy ⊢
  rw [span_gcd, Ideal.span_insert, sup_le_iff]
  exact ⟨hx, hy⟩
#align is_bezout.dvd_gcd IsBezout.dvd_gcd

theorem gcd_eq_sum (x y : R) : ∃ a b : R, a * x + b * y = gcd x y :=
  Ideal.mem_span_pair.mp (by rw [← span_gcd]; apply Ideal.subset_span; simp)
#align is_bezout.gcd_eq_sum IsBezout.gcd_eq_sum

variable (R)

/-- Any bezout domain is a GCD domain. This is not an instance since `GCDMonoid` contains data,
and this might not be how we would like to construct it. -/
noncomputable def toGCDDomain [IsDomain R] [DecidableEq R] : GCDMonoid R :=
  gcdMonoidOfGCD gcd gcd_dvd_left gcd_dvd_right fun hac hab => dvd_gcd hac hab
#align is_bezout.to_gcd_domain IsBezout.toGCDDomain

end Gcd

attribute [local instance] toGCDDomain

-- Note that the proof depends on the `attribute [local instance]` above, and is thus necessary to
-- be stated.
instance (priority := 100) [IsDomain R] [IsBezout R] : IsIntegrallyClosed R := by
  classical exact GCDMonoid.toIsIntegrallyClosed

theorem _root_.Function.Surjective.isBezout {S : Type v} [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) [IsBezout R] : IsBezout S := by
  rw [iff_span_pair_isPrincipal]
  intro x y
  obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := hf x, hf y
  use f (gcd x y)
  trans Ideal.map f (Ideal.span {gcd x y})
  · rw [span_gcd, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  · rw [Ideal.map_span, Set.image_singleton]; rfl
#align function.surjective.is_bezout Function.Surjective.isBezout

instance (priority := 100) of_isPrincipalIdealRing [IsPrincipalIdealRing R] : IsBezout R :=
  ⟨fun I _ => IsPrincipalIdealRing.principal I⟩
#align is_bezout.of_is_principal_ideal_ring IsBezout.of_isPrincipalIdealRing

theorem TFAE [IsBezout R] [IsDomain R] :
    List.TFAE
    [IsNoetherianRing R, IsPrincipalIdealRing R, UniqueFactorizationMonoid R, WfDvdMonoid R] := by
  classical
    tfae_have 1 → 2
    · intro H; exact ⟨fun I => isPrincipal_of_FG _ (IsNoetherian.noetherian _)⟩
    tfae_have 2 → 3
    · intro; infer_instance
    tfae_have 3 → 4
    · intro; infer_instance
    tfae_have 4 → 1
    · rintro ⟨h⟩
      rw [isNoetherianRing_iff, isNoetherian_iff_fg_wellFounded]
      apply RelEmbedding.wellFounded _ h
      have : ∀ I : { J : Ideal R // J.FG }, ∃ x : R, (I : Ideal R) = Ideal.span {x} :=
        fun ⟨I, hI⟩ => (IsBezout.isPrincipal_of_FG I hI).1
      choose f hf using this
      exact
        { toFun := f
          inj' := fun x y e => by ext1; rw [hf, hf, e]
          map_rel_iff' := by
            dsimp
            intro a b
            rw [← Ideal.span_singleton_lt_span_singleton, ← hf, ← hf]
            rfl }
    tfae_finish
#align is_bezout.tfae IsBezout.TFAE

end IsBezout
