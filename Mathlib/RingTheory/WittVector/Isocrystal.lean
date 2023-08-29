/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.RingTheory.WittVector.FrobeniusFractionField

#align_import ring_theory.witt_vector.isocrystal from "leanprover-community/mathlib"@"6d584f1709bedbed9175bd9350df46599bdd7213"

/-!

## F-isocrystals over a perfect field

When `k` is an integral domain, so is `𝕎 k`, and we can consider its field of fractions `K(p, k)`.
The endomorphism `WittVector.frobenius` lifts to `φ : K(p, k) → K(p, k)`; if `k` is perfect, `φ` is
an automorphism.

Let `k` be a perfect integral domain. Let `V` be a vector space over `K(p,k)`.
An *isocrystal* is a bijective map `V → V` that is `φ`-semilinear.
A theorem of Dieudonné and Manin classifies the finite-dimensional isocrystals over algebraically
closed fields. In the one-dimensional case, this classification states that the isocrystal
structures are parametrized by their "slope" `m : ℤ`.
Any one-dimensional isocrystal is isomorphic to `φ(p^m • x) : K(p,k) → K(p,k)` for some `m`.

This file proves this one-dimensional case of the classification theorem.
The construction is described in Dupuis, Lewis, and Macbeth,
[Formalized functional analysis via semilinear maps][dupuis-lewis-macbeth2022].

## Main declarations

* `WittVector.Isocrystal`: a vector space over the field `K(p, k)` additionally equipped with a
  Frobenius-linear automorphism.
* `WittVector.isocrystal_classification`: a one-dimensional isocrystal admits an isomorphism to one
  of the standard one-dimensional isocrystals.

## Notation

This file introduces notation in the locale `isocrystal`.
* `K(p, k)`: `FractionRing (WittVector p k)`
* `φ(p, k)`: `WittVector.FractionRing.frobeniusRingHom p k`
* `M →ᶠˡ[p, k] M₂`: `LinearMap (WittVector.FractionRing.frobeniusRingHom p k) M M₂`
* `M ≃ᶠˡ[p, k] M₂`: `LinearEquiv (WittVector.FractionRing.frobeniusRingHom p k) M M₂`
* `Φ(p, k)`: `WittVector.Isocrystal.frobenius p k`
* `M →ᶠⁱ[p, k] M₂`: `WittVector.IsocrystalHom p k M M₂`
* `M ≃ᶠⁱ[p, k] M₂`: `WittVector.IsocrystalEquiv p k M M₂`

## References

* [Formalized functional analysis via semilinear maps][dupuis-lewis-macbeth2022]
* [Theory of commutative formal groups over fields of finite characteristic][manin1963]
* <https://www.math.ias.edu/~lurie/205notes/Lecture26-Isocrystals.pdf>

-/

set_option autoImplicit true


noncomputable section

open FiniteDimensional

namespace WittVector

variable (p : ℕ) [Fact p.Prime]

variable (k : Type*) [CommRing k]

scoped[Isocrystal] notation "K(" p ", " k ")" => FractionRing (WittVector p k)

open Isocrystal

section PerfectRing

variable [IsDomain k] [CharP k p] [PerfectRing k p]

/-! ### Frobenius-linear maps -/


/-- The Frobenius automorphism of `k` induces an automorphism of `K`. -/
def FractionRing.frobenius : K(p, k) ≃+* K(p, k) :=
  IsFractionRing.fieldEquivOfRingEquiv (frobeniusEquiv p k)
#align witt_vector.fraction_ring.frobenius WittVector.FractionRing.frobenius

/-- The Frobenius automorphism of `k` induces an endomorphism of `K`. For notation purposes. -/
def FractionRing.frobeniusRingHom : K(p, k) →+* K(p, k) :=
  FractionRing.frobenius p k
#align witt_vector.fraction_ring.frobenius_ring_hom WittVector.FractionRing.frobeniusRingHom

scoped[Isocrystal] notation "φ(" p ", " k ")" => WittVector.FractionRing.frobeniusRingHom p k

instance inv_pair₁ : RingHomInvPair φ(p, k) (FractionRing.frobenius p k).symm :=
  RingHomInvPair.of_ringEquiv (FractionRing.frobenius p k)
#align witt_vector.inv_pair₁ WittVector.inv_pair₁

instance inv_pair₂ : RingHomInvPair ((FractionRing.frobenius p k).symm : K(p, k) →+* K(p, k))
    (FractionRing.frobenius p k) :=
  RingHomInvPair.of_ringEquiv (FractionRing.frobenius p k).symm
#align witt_vector.inv_pair₂ WittVector.inv_pair₂

scoped[Isocrystal]
  notation:50 M " →ᶠˡ[" p ", " k "] " M₂ =>
    LinearMap (WittVector.FractionRing.frobeniusRingHom p k) M M₂

scoped[Isocrystal]
  notation:50 M " ≃ᶠˡ[" p ", " k "] " M₂ =>
    LinearEquiv (WittVector.FractionRing.frobeniusRingHom p k) M M₂

/-! ### Isocrystals -/


/-- An isocrystal is a vector space over the field `K(p, k)` additionally equipped with a
Frobenius-linear automorphism.
-/
class Isocrystal (V : Type*) [AddCommGroup V] extends Module K(p, k) V where
  frob : V ≃ᶠˡ[p, k] V
#align witt_vector.isocrystal WittVector.Isocrystal

open WittVector

variable (V : Type*) [AddCommGroup V] [Isocrystal p k V]

variable (V₂ : Type*) [AddCommGroup V₂] [Isocrystal p k V₂]

variable {V}

/--
Project the Frobenius automorphism from an isocrystal. Denoted by `Φ(p, k)` when V can be inferred.
-/
def Isocrystal.frobenius : V ≃ᶠˡ[p, k] V :=
  @Isocrystal.frob p _ k _ _ _ _ _ _ _
#align witt_vector.isocrystal.frobenius WittVector.Isocrystal.frobenius

variable (V)

scoped[Isocrystal] notation "Φ(" p ", " k ")" => WittVector.Isocrystal.frobenius p k

/-- A homomorphism between isocrystals respects the Frobenius map. -/
-- Porting note(https://github.com/leanprover-community/mathlib4/issues/5171):
-- removed @[nolint has_nonempty_instance]
structure IsocrystalHom extends V →ₗ[K(p, k)] V₂ where
  frob_equivariant : ∀ x : V, Φ(p, k) (toLinearMap x) = toLinearMap (Φ(p, k) x)
#align witt_vector.isocrystal_hom WittVector.IsocrystalHom

/-- An isomorphism between isocrystals respects the Frobenius map. -/
-- Porting note(https://github.com/leanprover-community/mathlib4/issues/5171):
-- removed @[nolint has_nonempty_instance]
structure IsocrystalEquiv extends V ≃ₗ[K(p, k)] V₂ where
  frob_equivariant : ∀ x : V, Φ(p, k) (toLinearEquiv x) = toLinearEquiv (Φ(p, k) x)
#align witt_vector.isocrystal_equiv WittVector.IsocrystalEquiv

scoped[Isocrystal] notation:50 M " →ᶠⁱ[" p ", " k "] " M₂ => WittVector.IsocrystalHom p k M M₂

scoped[Isocrystal] notation:50 M " ≃ᶠⁱ[" p ", " k "] " M₂ => WittVector.IsocrystalEquiv p k M M₂

end PerfectRing

open scoped Isocrystal

/-! ### Classification of isocrystals in dimension 1 -/


/-- A helper instance for type class inference. -/
@[local instance]
def FractionRing.module : Module K(p, k) K(p, k) :=
  Semiring.toModule
#align witt_vector.fraction_ring.module WittVector.FractionRing.module

/-- Type synonym for `K(p, k)` to carry the standard 1-dimensional isocrystal structure
of slope `m : ℤ`.
-/
@[nolint unusedArguments]
-- Porting note(https://github.com/leanprover-community/mathlib4/issues/5171):
-- removed @[nolint has_nonempty_instance]
def StandardOneDimIsocrystal (_m : ℤ) : Type _ :=
  K(p, k)
#align witt_vector.standard_one_dim_isocrystal WittVector.StandardOneDimIsocrystal

-- Porting note(https://github.com/leanprover-community/mathlib4/issues/5020): added
section Deriving

instance : AddCommGroup (StandardOneDimIsocrystal p k m) :=
  inferInstanceAs (AddCommGroup K(p, k))
instance : Module K(p, k) (StandardOneDimIsocrystal p k m) :=
  inferInstanceAs (Module K(p, k) K(p, k))

end Deriving

section PerfectRing

variable [IsDomain k] [CharP k p] [PerfectRing k p]

/-- The standard one-dimensional isocrystal of slope `m : ℤ` is an isocrystal. -/
instance (m : ℤ) : Isocrystal p k (StandardOneDimIsocrystal p k m) where
  frob :=
    (FractionRing.frobenius p k).toSemilinearEquiv.trans
      (LinearEquiv.smulOfNeZero _ _ _ (zpow_ne_zero m (WittVector.FractionRing.p_nonzero p k)))

@[simp]
theorem StandardOneDimIsocrystal.frobenius_apply (m : ℤ) (x : StandardOneDimIsocrystal p k m) :
    Φ(p, k) x = (p : K(p, k)) ^ m • φ(p, k) x := by
  -- Porting note: was just `rfl`
  erw [smul_eq_mul]
  -- ⊢ ↑Φ(p, k) x = ↑(IsFractionRing.lift (_ : Function.Injective ↑(algebraMap (Wit …
  simp only [map_zpow₀, map_natCast]
  -- ⊢ ↑Φ(p, k) x = ↑p ^ m * ↑φ(p, k) x
  rfl
  -- 🎉 no goals
#align witt_vector.standard_one_dim_isocrystal.frobenius_apply WittVector.StandardOneDimIsocrystal.frobenius_apply

end PerfectRing

/-- A one-dimensional isocrystal over an algebraically closed field
admits an isomorphism to one of the standard (indexed by `m : ℤ`) one-dimensional isocrystals. -/
theorem isocrystal_classification (k : Type*) [Field k] [IsAlgClosed k] [CharP k p] (V : Type*)
    [AddCommGroup V] [Isocrystal p k V] (h_dim : finrank K(p, k) V = 1) :
    ∃ m : ℤ, Nonempty (StandardOneDimIsocrystal p k m ≃ᶠⁱ[p, k] V) := by
  haveI : Nontrivial V := FiniteDimensional.nontrivial_of_finrank_eq_succ h_dim
  -- ⊢ ∃ m, Nonempty (StandardOneDimIsocrystal p k m ≃ᶠⁱ[p, k] V)
  obtain ⟨x, hx⟩ : ∃ x : V, x ≠ 0 := exists_ne 0
  -- ⊢ ∃ m, Nonempty (StandardOneDimIsocrystal p k m ≃ᶠⁱ[p, k] V)
  have : Φ(p, k) x ≠ 0 := by simpa only [map_zero] using Φ(p, k).injective.ne hx
  -- ⊢ ∃ m, Nonempty (StandardOneDimIsocrystal p k m ≃ᶠⁱ[p, k] V)
  obtain ⟨a, ha, hax⟩ : ∃ a : K(p, k), a ≠ 0 ∧ Φ(p, k) x = a • x := by
    rw [finrank_eq_one_iff_of_nonzero' x hx] at h_dim
    obtain ⟨a, ha⟩ := h_dim (Φ(p, k) x)
    refine' ⟨a, _, ha.symm⟩
    intro ha'
    apply this
    simp only [← ha, ha', zero_smul]
  obtain ⟨b, hb, m, hmb⟩ := WittVector.exists_frobenius_solution_fractionRing p ha
  -- ⊢ ∃ m, Nonempty (StandardOneDimIsocrystal p k m ≃ᶠⁱ[p, k] V)
  replace hmb : φ(p, k) b * a = (p : K(p, k)) ^ m * b := by convert hmb
  -- ⊢ ∃ m, Nonempty (StandardOneDimIsocrystal p k m ≃ᶠⁱ[p, k] V)
  use m
  -- ⊢ Nonempty (StandardOneDimIsocrystal p k m ≃ᶠⁱ[p, k] V)
  let F₀ : StandardOneDimIsocrystal p k m →ₗ[K(p, k)] V := LinearMap.toSpanSingleton K(p, k) V x
  -- ⊢ Nonempty (StandardOneDimIsocrystal p k m ≃ᶠⁱ[p, k] V)
  let F : StandardOneDimIsocrystal p k m ≃ₗ[K(p, k)] V := by
    refine' LinearEquiv.ofBijective F₀ ⟨_, _⟩
    · rw [← LinearMap.ker_eq_bot]
      exact LinearMap.ker_toSpanSingleton K(p, k) V hx
    · rw [← LinearMap.range_eq_top]
      rw [← (finrank_eq_one_iff_of_nonzero x hx).mp h_dim]
      rw [LinearMap.span_singleton_eq_range]
  -- Porting note: `refine'` below gets confused when this is inlined.
  let E := (LinearEquiv.smulOfNeZero K(p, k) _ _ hb).trans F
  -- ⊢ Nonempty (StandardOneDimIsocrystal p k m ≃ᶠⁱ[p, k] V)
  refine' ⟨⟨E, _⟩⟩
  -- ⊢ ∀ (x : StandardOneDimIsocrystal p k m), ↑Φ(p, k) (↑E x) = ↑E (↑Φ(p, k) x)
  simp only
  -- ⊢ ∀ (x_1 : StandardOneDimIsocrystal p k m), ↑Φ(p, k) (↑(LinearEquiv.trans (Lin …
  intro c
  -- ⊢ ↑Φ(p, k) (↑(LinearEquiv.trans (LinearEquiv.smulOfNeZero K(p, k) (StandardOne …
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply,
    LinearEquiv.smulOfNeZero_apply, LinearEquiv.map_smul, LinearEquiv.map_smul]
  -- Porting note: was
  -- simp only [hax, LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply,
  --   LinearEquiv.map_smulₛₗ, StandardOneDimIsocrystal.frobenius_apply, Algebra.id.smul_eq_mul]
  rw [LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply]
  -- ⊢ ↑Φ(p, k) (b • ↑(LinearMap.toSpanSingleton K(p, k) V x) c) = b • ↑(LinearMap. …
  erw [LinearMap.toSpanSingleton_apply K(p, k) V x c, LinearMap.toSpanSingleton_apply K(p, k) V x]
  -- ⊢ ↑Φ(p, k) (b • c • x) = b • ↑Φ(p, k) c • x
  simp only [hax, LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply,
    LinearEquiv.map_smulₛₗ, StandardOneDimIsocrystal.frobenius_apply, Algebra.id.smul_eq_mul]
  simp only [← mul_smul]
  -- ⊢ (↑φ(p, k) b * (↑φ(p, k) c * a)) • x = (b * ↑p ^ m • ↑φ(p, k) c) • x
  congr 1
  -- ⊢ ↑φ(p, k) b * (↑φ(p, k) c * a) = b * ↑p ^ m • ↑φ(p, k) c
  -- Porting note: added the next two lines
  erw [smul_eq_mul]
  -- ⊢ ↑φ(p, k) b * (↑φ(p, k) c * a) = b * (↑(IsFractionRing.lift (_ : Function.Inj …
  simp only [map_zpow₀, map_natCast]
  -- ⊢ ↑φ(p, k) b * (↑φ(p, k) c * a) = b * (↑p ^ m * ↑φ(p, k) c)
  linear_combination φ(p, k) c * hmb
  -- 🎉 no goals
#align witt_vector.isocrystal_classification WittVector.isocrystal_classification

end WittVector
