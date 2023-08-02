/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li
-/

import Mathlib.Order.RelSeries
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.WithBot
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.Module.LocalizedModule

/-!
# Krull dimension of a preordered set

If `α` is a preordered set, then `krullDim α` is defined to be `sup {n | a₀ < a₁ < ... < aₙ}`.
In case that `α` is empty, then its Krull dimension is defined to be negative infinity; if the
length of all series `a₀ < a₁ < ... < aₙ` is unbounded, then its Krull dimension is defined to
be positive infinity.

For `a : α`, its height is defined to be the krull dimension of the subset `(-∞, a]` while its
coheight is defined to be the krull dimension of `[a, +∞)`.

## Implementation notes
Krull dimensions are defined to take value in `WithBot (WithTop ℕ)` so that `(-∞) + (+∞)` is
also negative infinity. This is because we want Krull dimensions to be additive with respect
to product of varieties so that `-∞` being the Krull dimension of empty variety is equal to
sum of `-∞` and the Krull dimension of any other varieties.
-/

variable (α : Type _) [Preorder α]

/--
Krull dimension of a preorder `α` is the supremum of the rightmost index of all relation
series of `α` order by `<`. If there is no series `a₀ < a₁ < ... < aₙ` in `α`, then its Krull
dimension is defined to be negative infinity; if the length of all series `a₀ < a₁ < ... < aₙ` is
unbounded, its Krull dimension is defined to be positive infinity.
-/
noncomputable def krullDim : WithBot (WithTop ℕ) :=
  ⨆ (p : LTSeries α), p.length

/--
Height of an element `a` of a preordered set `α` is the Krull dimension of the subset `(-∞, a]`
-/
noncomputable def height (a : α) : WithBot (WithTop ℕ) := krullDim (Set.Iic a)

/--
Coheight of an element `a` of a pre-ordered set `α` is the Krull dimension of the subset `[a, +∞)`
-/
noncomputable def coheight (a : α) : WithBot (WithTop ℕ) := krullDim (Set.Ici a)

noncomputable

section Preorder

variable {α β : Type _}

variable [Preorder α] [Preorder β]

lemma krullDim_le_of_StrictMono (f : α → β) (hf : StrictMono f) : krullDim α ≤ krullDim β :=
  iSup_le $ λ p ↦ le_sSup ⟨p.map f hf, rfl⟩

end Preorder

/--
The ring theoretic Krull dimension is the Krull dimension of prime spectrum ordered by inclusion.
-/
noncomputable def ringKrullDim (R : Type _) [CommRing R] : WithBot (WithTop ℕ) :=
  krullDim (PrimeSpectrum R)

namespace ringKrullDim

/--
If `R ⟶ S` is a surjective ring homomorphism, then `ringKrullDim S ≤ ringKrullDim R`.
-/
theorem le_of_Surj (R S : Type _) [CommRing R] [CommRing S] (f : R →+* S)
  (hf : Function.Surjective f) : ringKrullDim S ≤ ringKrullDim R := by
{ refine' krullDim_le_of_StrictMono (PrimeSpectrum.comap f)
    (Monotone.strictMono_of_injective ?_ (PrimeSpectrum.comap_injective_of_surjective f hf))
  · intro a b hab
    change ((PrimeSpectrum.comap f) a).asIdeal ≤ ((PrimeSpectrum.comap f) b).asIdeal
    rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal]
    exact Ideal.comap_mono hab }

/--
If `I` is an ideal of `R`, then `ringKrullDim (R ⧸ I) ≤ ringKrullDim R`.
-/
theorem le_of_Quot (R : Type _) [CommRing R] (I : PrimeSpectrum R) :
  ringKrullDim (R ⧸ I.asIdeal) ≤ ringKrullDim R :=
le_of_Surj _ _ (Ideal.Quotient.mk I.asIdeal) Ideal.Quotient.mk_surjective

/--
If `R` and `S` are isomorphic, then `ringKrullDim R = ringKrullDim S`.
-/
theorem eq_of_RingEquiv (R S : Type _) [CommRing R] [CommRing S] (e : R ≃+* S) :
  ringKrullDim R = ringKrullDim S :=
le_antisymm (le_of_Surj S R (RingEquiv.symm e) (EquivLike.surjective (RingEquiv.symm e)))
  (le_of_Surj R S e (EquivLike.surjective e))

/-
Here we aim to show that for any prime ideal `I` of a commutative ring `R`, the
height of `I` equals the krull dimension of `Localization.AtPrime I.asIdeal`.
-/
section aboutHeightAndLocalization

variable {R : Type _} [CommRing R] (I : PrimeSpectrum R) (J : Ideal R)

@[reducible] def IdealImageSpan := J.map (algebraMap R (Localization.AtPrime I.asIdeal))

/-- The canonical map from the ideal J of R to its image JR_I in the localisation. -/
@[simps apply] def Map_from_Ideal_to_IdealImageSpan : J →ₗ[R] IdealImageSpan I J where
  toFun := λ x ↦ ⟨Localization.mk x 1, Submodule.subset_span ⟨_, x.2, rfl⟩⟩
  map_add' := λ _ _ ↦ Subtype.ext (Localization.add_mk_self _ _ _).symm
  map_smul' := λ _ _ ↦ Subtype.ext (Localization.smul_mk _ _ _).symm

@[simps!] def LocalizationAtPrime_div_by (s : I.asIdeal.primeCompl) :
  Module.End (Localization.AtPrime I.asIdeal) (Localization.AtPrime I.asIdeal) where
    toFun := λ x ↦ (Localization.mk 1 s) * x
    map_add' := mul_add _
    map_smul' := λ r x ↦ by
      dsimp
      ring

lemma LocalizationAtPrime_div_by_range (s) (x) (hx : x ∈ IdealImageSpan I J) :
  (LocalizationAtPrime_div_by I s) x ∈ IdealImageSpan I J := by
{ simp only [LocalizationAtPrime_div_by_apply]
  exact Ideal.mul_mem_left (Ideal.map (algebraMap R (Localization.AtPrime I.asIdeal)) J)
    (Submonoid.LocalizationMap.mk' (Localization.monoidOf (Ideal.primeCompl I.asIdeal)) 1 s) hx }

variable {I}

def Module.End.inv (s : { x // x ∈ Ideal.primeCompl I.asIdeal }) :
  Module.End R (IdealImageSpan I J) :=
(LinearMap.restrict _ $ LocalizationAtPrime_div_by_range I J s).restrictScalars R

lemma Module.End.inv_left (s : I.asIdeal.primeCompl) :
  algebraMap R _ s * Module.End.inv J s = 1 :=
LinearMap.ext $ λ x ↦ show (s : R) • Module.End.inv J s x = x from Subtype.ext $
  show (s : R) • (Localization.mk 1 s * x) = x by rw [←smul_mul_assoc, Localization.smul_mk,
    smul_eq_mul, mul_one, Localization.mk_self, one_mul]

lemma Module.End.inv_right (s : I.asIdeal.primeCompl) :
  (Module.End.inv J s) * algebraMap R _ s = 1 :=
LinearMap.ext $ λ x ↦ Subtype.ext $ show Localization.mk 1 s * ((s : R) • x) = x
  by erw [mul_smul_comm, ←smul_mul_assoc, Localization.smul_mk, smul_eq_mul, mul_one,
    Localization.mk_self, one_mul]

lemma Map_from_Ideal_to_IdealImageSpan_exist_eq (y) :
  ∃ (x : J × I.asIdeal.primeCompl), (x.2 : R) • y = Map_from_Ideal_to_IdealImageSpan I J x.1 :=
sorry

lemma Map_from_Ideal_to_IdealImageSpan_apply_eq_iff (x₁ x₂) :
  (Map_from_Ideal_to_IdealImageSpan I J) x₁ = (Map_from_Ideal_to_IdealImageSpan I J) x₂ ↔
    ∃ (c : (I.asIdeal.primeCompl)), (c : R) • x₂ = (c : R) • x₁ :=
Subtype.ext_iff.trans $ Localization.mk_eq_mk_iff.trans $ Localization.r_iff_exists.trans $
  exists_congr $ λ x ↦ eq_comm.trans $ Iff.symm $ Subtype.ext_iff.trans $ by simp [smul_eq_mul]

instance : IsLocalizedModule I.asIdeal.primeCompl (Map_from_Ideal_to_IdealImageSpan I J) where
  map_units := λ s ↦ ⟨⟨_, _, Module.End.inv_left _ s, Module.End.inv_right _ s⟩, rfl⟩
  surj' := Map_from_Ideal_to_IdealImageSpan_exist_eq J
  eq_iff_exists' := by exact Map_from_Ideal_to_IdealImageSpan_apply_eq_iff J _ _

variable (I)

noncomputable

def Equiv_between_LocalizedModule_and_IdealImageSpan :
  (LocalizedModule I.asIdeal.primeCompl J) ≃ₗ[R] IdealImageSpan I J :=
IsLocalizedModule.iso _ $ Map_from_Ideal_to_IdealImageSpan I J

lemma Equiv_between_LocalizedModule_and_IdealImageSpan_apply (a b) :
  Equiv_between_LocalizedModule_and_IdealImageSpan I J (LocalizedModule.mk a b) =
⟨Localization.mk a b, by simpa only [show Localization.mk (a : R) b =
  (Localization.mk 1 b) * (Localization.mk ↑a 1) by rw [Localization.mk_mul, one_mul, mul_one]]
    using Ideal.mul_mem_left _ _ (Ideal.apply_coe_mem_map _ J a)⟩ := sorry

@[simps!]
def IdealImageSpan' : Ideal (Localization.AtPrime I.asIdeal) where
  carrier := { x | ∃ (a : J) (b : I.asIdeal.primeCompl), x = Localization.mk ↑a b }
  add_mem' := sorry
  zero_mem' := ⟨0, ⟨1, by
    simp only [ZeroMemClass.coe_zero, Localization.mk_eq_monoidOf_mk']
    rw [Submonoid.LocalizationMap.mk']
    simp only [map_one, inv_one, Units.val_one, mul_one]
    rw [Submonoid.LocalizationMap.toMap]
    exact Eq.symm (Localization.mk_zero 1)⟩⟩
  smul_mem' := λ c ↦ Localization.induction_on c $ by
    rintro ⟨c1, c2⟩ ⟨j, ⟨a, rfl⟩⟩
    exact ⟨⟨_, J.mul_mem_left c1 (SetLike.coe_mem j)⟩, ⟨c2 * a, Localization.mk_mul _ _ _ _⟩⟩

lemma MemIdealImageSpan'_iff (x : Localization.AtPrime I.asIdeal) :
  x ∈ IdealImageSpan' I J ↔ ∃ (a : J) (b : I.asIdeal.primeCompl), x = Localization.mk ↑a b :=
Iff.rfl

lemma MemIdealImageSpan'_of_MemIdealImageSpan :
  ∀ x, x ∈ IdealImageSpan I J → x ∈ IdealImageSpan' I J := sorry

lemma IdealImageSpan'_eq_IdealImageSpan :
  IdealImageSpan' I J = IdealImageSpan I J := sorry

instance IdealImageSpan'IsPrime (J : Set.Iic I) :
  (IdealImageSpan' I J.1.asIdeal).IsPrime where
ne_top' := λ hit ↦ by
  rw [Ideal.eq_top_iff_one, MemIdealImageSpan'_iff] at hit
  rcases hit with ⟨a, ⟨b, hb⟩⟩
  exact (IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime I.asIdeal) _
    (a : R) b).mp (by simpa only [←Localization.mk_eq_mk', ←hb] using isUnit_one) (J.2 a.2)
mem_or_mem' := sorry

/--
There is a canonical map from `Set.Iic I` to `PrimeSpectrum (Localization.AtPrime I.asIdeal)`.
-/
@[simp]
def LocalizationPrimeSpectrumMap :
  Set.Iic I → PrimeSpectrum (Localization.AtPrime I.asIdeal) :=
λ I' ↦ ⟨IdealImageSpan' I I'.1.asIdeal, by exact IdealImageSpan'IsPrime I I'⟩

end aboutHeightAndLocalization

end ringKrullDim
