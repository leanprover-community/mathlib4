/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Unramified.Locus

/-!
# Frobenius elements

In algebraic number theory, if `L/K` is a finite Galois extension of number fields, with rings of
integers `𝓞L/𝓞K`, and if `q` is prime ideal of `𝓞L` lying over a prime ideal `p` of `𝓞K`, then
there exists a **Frobenius element** `Frob p` in `Gal(L/K)` with the property that
`Frob p x ≡ x ^ #(𝓞K/p) (mod q)` for all `x ∈ 𝓞L`.

Following `RingTheory/Invariant.lean`, we develop the theory in the setting that
there is a finite group `G` acting on a ring `S`, and `R` is the fixed subring of `S`.

## Main results

Let `S/R` be an extension of rings, `Q` be a prime of `S`,
and `P := R ∩ Q` with finite residue field of cardinality `q`.

- `AlgHom.IsArithFrobAt`: We say that a `φ : S →ₐ[R] S` is an (arithmetic) Frobenius at `Q`
  if `φ x ≡ x ^ q (mod Q)` for all `x : S`.
- `AlgHom.IsArithFrobAt.apply_of_pow_eq_one`:
  Suppose `S` is a domain and `φ` is a Frobenius at `Q`,
  then `φ ζ = ζ ^ q` for any `m`-th root of unity `ζ` with `q ∤ m`.
- `AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`:
  Suppose `S` is Noetherian, `Q` contains all zero-divisors, and the extension is unramified at `Q`.
  Then the Frobenius is unique (if exists).

Let `G` be a finite group acting on a ring `S`, and `R` is the fixed subring of `S`.

- `IsArithFrobAt`: We say that a `σ : G` is an (arithmetic) Frobenius at `Q`
  if `σ • x ≡ x ^ q (mod Q)` for all `x : S`.
- `IsArithFrobAt.mul_inv_mem_inertia`:
  Two Frobenius elements at `Q` differ by an element in the inertia subgroup of `Q`.
- `IsArithFrobAt.conj`: If `σ` is a Frobenius at `Q`, then `τστ⁻¹` is a Frobenius at `σ • Q`.
- `IsArithFrobAt.exists_of_isInvariant`: Frobenius element exists.
-/

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- `φ : S →ₐ[R] S` is an (arithmetic) Frobenius at `Q` if
`φ x ≡ x ^ #(R/p) (mod Q)` for all `x : S` (`AlgHom.IsArithFrobAt`). -/
def AlgHom.IsArithFrobAt (φ : S →ₐ[R] S) (Q : Ideal S) : Prop :=
  ∀ x, φ x - x ^ Nat.card (R ⧸ Q.under R) ∈ Q

namespace AlgHom.IsArithFrobAt

variable {φ ψ : S →ₐ[R] S} {Q : Ideal S} (H : φ.IsArithFrobAt Q)

include H

lemma mk_apply (x) : Ideal.Quotient.mk Q (φ x) = x ^ Nat.card (R ⧸ Q.under R) := by
  rw [← map_pow, Ideal.Quotient.eq]
  exact H x

lemma finite_quotient : _root_.Finite (R ⧸ Q.under R) := by
  by_contra! h
  obtain rfl : Q = ⊤ := by simpa [Nat.card_eq_zero_of_infinite, ← Ideal.eq_top_iff_one] using H 0
  simp only [Ideal.comap_top] at h
  exact not_finite (R ⧸ (⊤ : Ideal R))

lemma card_pos : 0 < Nat.card (R ⧸ Q.under R) :=
  have := H.finite_quotient
  Nat.card_pos

lemma le_comap : Q ≤ Q.comap φ := by
  intro x hx
  simp_all only [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem (I := Q), H.mk_apply,
    zero_pow_eq, ite_eq_right_iff, H.card_pos.ne', false_implies]

/-- A Frobenius element at `Q` restricts to the Frobenius map on `S ⧸ Q`. -/
def restrict : S ⧸ Q →ₐ[R ⧸ Q.under R] S ⧸ Q where
  toRingHom := Ideal.quotientMap Q φ H.le_comap
  commutes' x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact DFunLike.congr_arg (Ideal.Quotient.mk Q) (φ.commutes x)

lemma restrict_apply (x : S ⧸ Q) :
    H.restrict x = x ^ Nat.card (R ⧸ Q.under R) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact H.mk_apply x

lemma restrict_mk (x : S) : H.restrict ↑x = ↑(φ x) := rfl

lemma restrict_injective [Q.IsPrime] :
    Function.Injective H.restrict := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  simpa [restrict_apply, H.card_pos.ne'] using hx

lemma comap_eq [Q.IsPrime] : Q.comap φ = Q := by
  refine le_antisymm (fun x hx ↦ ?_) H.le_comap
  rwa [← Ideal.Quotient.eq_zero_iff_mem, ← H.restrict_injective.eq_iff, map_zero, restrict_mk,
    Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap]

/-- Suppose `S` is a domain, and `φ : S →ₐ[R] S` is a Frobenius at `Q : Ideal S`.
Let `ζ` be a `m`-th root of unity with `Q ∤ m`, then `φ` sends `ζ` to `ζ ^ q`. -/
lemma apply_of_pow_eq_one [IsDomain S] {ζ : S} {m : ℕ} (hζ : ζ ^ m = 1) (hk' : ↑m ∉ Q) :
    φ ζ = ζ ^ Nat.card (R ⧸ Q.under R) := by
  set q := Nat.card (R ⧸ Q.under R)
  have hm : m ≠ 0 := by rintro rfl; exact hk' (by simp)
  obtain ⟨k, hk, hζ⟩ := IsPrimitiveRoot.exists_pos hζ hm
  have hk' : ↑k ∉ Q := fun h ↦ hk' (Q.mem_of_dvd (Nat.cast_dvd_cast (hζ.2 m ‹_›)) h)
  have : NeZero k := ⟨hk.ne'⟩
  obtain ⟨i, hi, e⟩ := hζ.eq_pow_of_pow_eq_one (ξ := φ ζ) (by rw [← map_pow, hζ.1, map_one])
  have (j : _) : 1 - ζ ^ ((q + k - i) * j) ∈ Q := by
    rw [← Ideal.mul_unit_mem_iff_mem _ ((hζ.isUnit k.pos_of_neZero).pow (i * j)),
      sub_mul, one_mul, ← pow_add, ← add_mul, tsub_add_cancel_of_le (by linarith), add_mul,
        pow_add, pow_mul _ k, hζ.1, one_pow, mul_one, pow_mul, e, ← map_pow, mul_comm, pow_mul]
    exact H _
  have h₁ := sum_mem (t := Finset.range k) fun j _ ↦ this j
  have h₂ := geom_sum_mul (ζ ^ (q + k - i)) k
  rw [pow_right_comm, hζ.1, one_pow, sub_self, mul_eq_zero, sub_eq_zero] at h₂
  rcases h₂ with h₂ | h₂
  · simp [h₂, pow_mul, hk'] at h₁
  replace h₂ := congr($h₂ * ζ ^ i)
  rw [one_mul, ← pow_add, tsub_add_cancel_of_le (by linarith), pow_add, hζ.1, mul_one] at h₂
  rw [h₂, e]

/-- A Frobenius element at `Q` restricts to an automorphism of `S_Q`. -/
noncomputable
def localize [Q.IsPrime] : Localization.AtPrime Q →ₐ[R] Localization.AtPrime Q where
  toRingHom := Localization.localRingHom _ _ φ H.comap_eq.symm
  commutes' x := by
    simp [IsScalarTower.algebraMap_apply R S (Localization.AtPrime Q),
      Localization.localRingHom_to_map]

@[simp]
lemma localize_algebraMap [Q.IsPrime] (x : S) :
    H.localize (algebraMap _ _ x) = algebraMap _ _ (φ x) :=
  Localization.localRingHom_to_map _ _ _ H.comap_eq.symm _

open IsLocalRing nonZeroDivisors

lemma isArithFrobAt_localize [Q.IsPrime] : H.localize.IsArithFrobAt (maximalIdeal _) := by
  have h : Nat.card (R ⧸ (maximalIdeal _).comap (algebraMap R (Localization.AtPrime Q))) =
      Nat.card (R ⧸ Q.under R) := by
    congr 2
    rw [IsScalarTower.algebraMap_eq R S (Localization.AtPrime Q), ← Ideal.comap_comap,
      Localization.AtPrime.comap_maximalIdeal]
  intro x
  obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl x
  simp only [localize, coe_mk, Localization.localRingHom_mk', RingHom.coe_coe, h,
    ← IsLocalization.mk'_pow]
  rw [← IsLocalization.mk'_sub,
    IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime Q) Q]
  simp only [SubmonoidClass.coe_pow, ← Ideal.Quotient.eq_zero_iff_mem]
  simp [H.mk_apply]

/-- Suppose `S` is Noetherian and `Q` is a prime of `S` containing all zero divisors.
If `S/R` is unramified at `Q`, then the Frobenius `φ : S →ₐ[R] S` over `Q` is unique. -/
lemma eq_of_isUnramifiedAt
    (H' : ψ.IsArithFrobAt Q) [Q.IsPrime] (hQ : Q.primeCompl ≤ S⁰)
    [Algebra.IsUnramifiedAt R Q] [IsNoetherianRing S] : φ = ψ := by
  have : H.localize = H'.localize := by
    have : IsNoetherianRing (Localization.AtPrime Q) :=
      IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
    apply Algebra.FormallyUnramified.ext_of_iInf _
      (Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal _) Ideal.IsPrime.ne_top')
    intro x
    rw [H.isArithFrobAt_localize.mk_apply, H'.isArithFrobAt_localize.mk_apply]
  ext x
  apply IsLocalization.injective (Localization.AtPrime Q) hQ
  rw [← H.localize_algebraMap, ← H'.localize_algebraMap, this]

end AlgHom.IsArithFrobAt

variable (R) in
/--
Suppose `S` is an `R` algebra, `M` is a monoid acting on `S` whose action is trivial on `R`
`σ : M` is an (arithmetic) Frobenius at an ideal `Q` of `S` if `σ • x ≡ x ^ q (mod Q)` for all `x`.
-/
abbrev IsArithFrobAt {M : Type*} [Monoid M] [MulSemiringAction M S] [SMulCommClass M R S]
    (σ : M) (Q : Ideal S) : Prop :=
  (MulSemiringAction.toAlgHom R S σ).IsArithFrobAt Q

namespace IsArithFrobAt

open scoped Pointwise

variable {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
variable {Q : Ideal S} {σ σ' : G}

lemma mul_inv_mem_inertia (H : IsArithFrobAt R σ Q) (H' : IsArithFrobAt R σ' Q) :
    σ * σ'⁻¹ ∈ Q.toAddSubgroup.inertia G := by
  intro x
  simpa [mul_smul] using sub_mem (H (σ'⁻¹ • x)) (H' (σ'⁻¹ • x))

lemma conj (H : IsArithFrobAt R σ Q) (τ : G) : IsArithFrobAt R (τ * σ * τ⁻¹) (τ • Q) := by
  intro x
  have : (Q.map (MulSemiringAction.toRingEquiv G S τ)).under R = Q.under R := by
    rw [← Ideal.comap_symm, ← Ideal.comap_coe, Ideal.under, Ideal.comap_comap]
    congr 1
    exact (MulSemiringAction.toAlgEquiv R S τ).symm.toAlgHom.comp_algebraMap
  rw [Ideal.pointwise_smul_eq_comap, Ideal.mem_comap]
  simpa [smul_sub, mul_smul, this] using H (τ⁻¹ • x)

variable [Finite G] [Algebra.IsInvariant R S G]

variable (R G Q) in
attribute [local instance] Ideal.Quotient.field in
/-- Let `G` be a finite group acting on `S`, and `R` be the fixed subring.
If `Q` is a prime of `S` with finite residue field,
then there exists a Frobenius element `σ : G` at `Q`. -/
lemma exists_of_isInvariant [Q.IsPrime] [Finite (S ⧸ Q)] : ∃ σ : G, IsArithFrobAt R σ Q := by
  let P := Q.under R
  have := Algebra.IsInvariant.isIntegral R S G
  have : Q.IsMaximal := Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (S ⧸ Q))
  have : P.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
  obtain ⟨p, hc⟩ := CharP.exists (R ⧸ P)
  have : Finite (R ⧸ P) := .of_injective _ Ideal.algebraMap_quotient_injective
  cases nonempty_fintype (R ⧸ P)
  obtain ⟨k, hp, hk⟩ := FiniteField.card (R ⧸ P) p
  have := CharP.of_ringHom_of_ne_zero (algebraMap (R ⧸ P) (S ⧸ Q)) p hp.ne_zero
  have : ExpChar (S ⧸ Q) p := .prime hp
  let l : (S ⧸ Q) ≃ₐ[R ⧸ P] S ⧸ Q :=
    { __ := iterateFrobeniusEquiv (S ⧸ Q) p k,
      commutes' r := by
        dsimp [iterateFrobenius_def]
        rw [← map_pow, ← hk, FiniteField.pow_card] }
  obtain ⟨σ, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective G P Q l
  refine ⟨σ, fun x ↦ ?_⟩
  rw [← Ideal.Quotient.eq, Nat.card_eq_fintype_card, hk]
  exact DFunLike.congr_fun hσ (Ideal.Quotient.mk Q x)

variable (S G) in
lemma exists_primesOver_isConj (P : Ideal R)
    (hP : ∃ Q : Ideal.primesOver P S, Finite (S ⧸ Q.1)) :
    ∃ σ : Ideal.primesOver P S → G, (∀ Q, IsArithFrobAt R (σ Q) Q.1) ∧
      (∀ Q₁ Q₂, IsConj (σ Q₁) (σ Q₂)) := by
  obtain ⟨⟨Q, hQ₁, hQ₂⟩, hQ₃⟩ := hP
  have (Q' : Ideal.primesOver P S) : ∃ σ : G, Q'.1 = σ • Q :=
    Algebra.IsInvariant.exists_smul_of_under_eq R S G _ _ (hQ₂.over.symm.trans Q'.2.2.over)
  choose τ hτ using this
  obtain ⟨σ, hσ⟩ := exists_of_isInvariant R G Q
  refine ⟨fun Q' ↦ τ Q' * σ * (τ Q')⁻¹, fun Q' ↦ hτ Q' ▸ hσ.conj (τ Q'), fun Q₁ Q₂ ↦
    .trans (.symm (isConj_iff.mpr ⟨τ Q₁, rfl⟩)) (isConj_iff.mpr ⟨τ Q₂, rfl⟩)⟩

variable (R G Q)

/-- Let `G` be a finite group acting on `S`, `R` be the fixed subring, and `Q` be a prime of `S`
with finite residue field. This is an arbitrary choice of a Frobenius over `Q`. It is chosen so that
the Frobenius elements of `Q₁` and `Q₂` are conjugate if they lie over the same prime. -/
noncomputable
def _root_.arithFrobAt [Q.IsPrime] [Finite (S ⧸ Q)] : G :=
  (exists_primesOver_isConj S G (Q.under R)
    ⟨⟨Q, ‹_›, ⟨rfl⟩⟩, ‹Finite (S ⧸ Q)›⟩).choose ⟨Q, ‹_›, ⟨rfl⟩⟩

protected lemma arithFrobAt [Q.IsPrime] [Finite (S ⧸ Q)] : IsArithFrobAt R (arithFrobAt R G Q) Q :=
  (exists_primesOver_isConj S G (Q.under R)
    ⟨⟨Q, ‹_›, ⟨rfl⟩⟩, ‹Finite (S ⧸ Q)›⟩).choose_spec.1 ⟨Q, ‹_›, ⟨rfl⟩⟩

lemma _root_.isConj_arithFrobAt
    [Q.IsPrime] [Finite (S ⧸ Q)] (Q' : Ideal S) [Q'.IsPrime] [Finite (S ⧸ Q')]
    (H : Q.under R = Q'.under R) : IsConj (arithFrobAt R G Q) (arithFrobAt R G Q') := by
  obtain ⟨P, hP, h₁, h₂⟩ : ∃ P : Ideal R, P.IsPrime ∧ P = Q.under R ∧ P = Q'.under R :=
    ⟨Q.under R, inferInstance, rfl, H⟩
  convert (exists_primesOver_isConj S G P
      ⟨⟨Q, ‹_›, ⟨h₁⟩⟩, ‹Finite (S ⧸ Q)›⟩).choose_spec.2 ⟨Q, ‹_›, ⟨h₁⟩⟩ ⟨Q', ‹_›, ⟨h₂⟩⟩
  · subst h₁; rfl
  · subst h₂; rfl

end IsArithFrobAt
