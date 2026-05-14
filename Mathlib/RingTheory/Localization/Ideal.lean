/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Ideal.IsPrimary
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Defs
public import Mathlib.Algebra.Algebra.Tower

/-!
# Ideals in localizations of commutative rings

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags

localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions

-/

@[expose] public section


namespace IsLocalization

section CommSemiring

variable {R : Type*} [CommSemiring R] (M : Submonoid R) (S : Type*) [CommSemiring S]
variable [Algebra R S] [IsLocalization M S]

variable {M S} in
theorem mk'_mem_iff {x} {y : M} {I : Ideal S} : mk' S x y ∈ I ↔ algebraMap R S x ∈ I := by
  constructor <;> intro h
  · rw [← mk'_spec S x y, mul_comm]
    exact I.mul_mem_left ((algebraMap R S) y) h
  · rw [← mk'_spec S x y] at h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 (map_units S y)
    have := I.mul_mem_left b h
    rwa [mul_comm, mul_assoc, hb, mul_one] at this

/-- Explicit characterization of the ideal given by `Ideal.map (algebraMap R S) I`.
In practice, this ideal differs only in that the carrier set is defined explicitly.
This definition is only meant to be used in proving `mem_map_algebraMap_iff`,
and any proof that needs to refer to the explicit carrier set should use that theorem. -/
-- TODO: golf this using `Submodule.localized'`
private def map_ideal (I : Ideal R) : Ideal S where
  carrier := { z : S | ∃ x : I × M, z * algebraMap R S x.2 = algebraMap R S x.1 }
  zero_mem' := ⟨⟨0, 1⟩, by simp⟩
  add_mem' := by
    rintro a b ⟨a', ha⟩ ⟨b', hb⟩
    let Z : { x // x ∈ I } := ⟨(a'.2 : R) * (b'.1 : R) + (b'.2 : R) * (a'.1 : R),
      I.add_mem (I.mul_mem_left _ b'.1.2) (I.mul_mem_left _ a'.1.2)⟩
    use ⟨Z, a'.2 * b'.2⟩
    simp only [Z, map_add, Submonoid.coe_mul, map_mul]
    rw [add_mul, ← mul_assoc a, ha, mul_comm (algebraMap R S a'.2) (algebraMap R S b'.2), ←
      mul_assoc b, hb]
    ring
  smul_mem' := by
    rintro c x ⟨x', hx⟩
    obtain ⟨c', hc⟩ := IsLocalization.surj M c
    let Z : { x // x ∈ I } := ⟨c'.1 * x'.1, I.mul_mem_left c'.1 x'.1.2⟩
    use ⟨Z, c'.2 * x'.2⟩
    simp only [Z, ← hx, ← hc, smul_eq_mul, Submonoid.coe_mul, map_mul]
    ring

theorem mem_map_algebraMap_iff {I : Ideal R} {z} : z ∈ Ideal.map (algebraMap R S) I ↔
    ∃ x : I × M, z * algebraMap R S x.2 = algebraMap R S x.1 := by
  constructor
  · change _ → z ∈ map_ideal M S I
    refine fun h => Ideal.mem_sInf.1 h fun z hz => ?_
    obtain ⟨y, hy⟩ := hz
    let Z : { x // x ∈ I } := ⟨y, hy.left⟩
    use ⟨Z, 1⟩
    simp [Z, hy.right]
  · rintro ⟨⟨a, s⟩, h⟩
    rw [← Ideal.unit_mul_mem_iff_mem _ (map_units S s), mul_comm]
    exact h.symm ▸ Ideal.mem_map_of_mem _ a.2

lemma mk'_mem_map_algebraMap_iff (I : Ideal R) (x : R) (s : M) :
    IsLocalization.mk' S x s ∈ I.map (algebraMap R S) ↔ ∃ s ∈ M, s * x ∈ I := by
  rw [← Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S s), IsLocalization.mk'_spec',
    IsLocalization.mem_map_algebraMap_iff M]
  simp_rw [← map_mul, IsLocalization.eq_iff_exists M, mul_comm x, ← mul_assoc, ← Submonoid.coe_mul]
  exact ⟨fun ⟨⟨y, t⟩, c, h⟩ ↦ ⟨_, (c * t).2, h ▸ I.mul_mem_left c.1 y.2⟩, fun ⟨s, hs, h⟩ ↦
    ⟨⟨⟨_, h⟩, ⟨s, hs⟩⟩, 1, by simp⟩⟩

lemma algebraMap_mem_map_algebraMap_iff (I : Ideal R) (x : R) :
    algebraMap R S x ∈ I.map (algebraMap R S) ↔
      ∃ m ∈ M, m * x ∈ I := by
  rw [← IsLocalization.mk'_one (M := M), mk'_mem_map_algebraMap_iff]

lemma map_algebraMap_ne_top_iff_disjoint (I : Ideal R) :
    I.map (algebraMap R S) ≠ ⊤ ↔ Disjoint (M : Set R) (I : Set R) := by
  simp only [ne_eq, Ideal.eq_top_iff_one, ← map_one (algebraMap R S), not_iff_comm,
    IsLocalization.algebraMap_mem_map_algebraMap_iff M]
  simp [Set.disjoint_left]

include M in
protected theorem map_inf (I J : Ideal R) :
    (I ⊓ J).map (algebraMap R S) = I.map (algebraMap R S) ⊓ J.map (algebraMap R S) := by
  refine le_antisymm (Ideal.map_inf_le (algebraMap R S)) fun x hx ↦ ?_
  simp only [Ideal.mem_inf, IsLocalization.mem_map_algebraMap_iff M, Prod.exists] at hx ⊢
  obtain ⟨⟨⟨i, hi⟩, mi, hi'⟩, ⟨j, hj⟩, mj, hj'⟩ := hx
  simp only [← IsLocalization.eq_mk'_iff_mul_eq] at hi' hj'
  obtain ⟨m, hm⟩ := IsLocalization.eq.mp (hi'.symm.trans hj')
  rw [← mul_assoc, ← mul_assoc, mul_comm, ← mul_comm (j : R)] at hm
  refine ⟨⟨i * (m * mj : M), I.mul_mem_right _ hi, hm ▸ J.mul_mem_right _ hj⟩, mi * (m * mj), ?_⟩
  rwa [← IsLocalization.eq_mk'_iff_mul_eq, Subtype.coe_mk, IsLocalization.mk'_cancel]

/-- `IsLocalization.map_inf` as an `FrameHom`. -/
def mapFrameHom : FrameHom (Ideal R) (Ideal S) where
  toFun := Ideal.map (algebraMap R S)
  map_inf' := IsLocalization.map_inf M S
  map_top' := Ideal.map_top (algebraMap R S)
  map_sSup' _ := (Ideal.gc_map_comap (algebraMap R S)).l_sSup.trans sSup_image.symm

@[simp]
lemma mapFrameHom_apply (I : Ideal R) :
    IsLocalization.mapFrameHom M S I = I.map (algebraMap R S) :=
  rfl

include M in
theorem map_under (J : Ideal S) :
    Ideal.map (algebraMap R S) (J.under R) = J :=
  le_antisymm (Ideal.map_le_iff_le_comap.2 le_rfl) fun x hJ => by
    obtain ⟨r, s, hx⟩ := exists_mk'_eq M x
    rw [← hx] at hJ ⊢
    exact
      Ideal.mul_mem_right _ _
        (Ideal.mem_map_of_mem _
          (show (algebraMap R S) r ∈ J from
            mk'_spec S r s ▸ J.mul_mem_right ((algebraMap R S) s) hJ))

@[deprecated (since := "2026-04-09")] alias map_comap := map_under

theorem under_map_of_isPrimary_disjoint
    {I : Ideal R} (hI : I.IsPrimary) (hM : Disjoint (M : Set R) I) :
    (Ideal.map (algebraMap R S) I).under R = I := by
  have key : Disjoint (M : Set R) I.radical := by
    contrapose hM
    rw [Set.not_disjoint_iff] at hM ⊢
    obtain ⟨a, ha, k, hk⟩ := hM
    exact ⟨a ^ k, pow_mem ha k, hk⟩
  refine le_antisymm (fun a ha ↦ ?_) Ideal.le_comap_map
  rw [Ideal.mem_comap, IsLocalization.mem_map_algebraMap_iff M S] at ha
  obtain ⟨⟨b, s⟩, h⟩ := ha
  replace h : algebraMap R S (s * a) = algebraMap R S b := by
    simpa only [← map_mul, mul_comm] using h
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M S).1 h
  have : a * (c * s : M) ∈ I := by
    rw [mul_comm, Submonoid.coe_mul, mul_assoc, hc]
    exact I.mul_mem_left c b.2
  exact ((Ideal.isPrimary_iff.mp hI).2 this).resolve_right (Set.disjoint_left.mp key (c * s).2)

@[deprecated (since := "2026-04-09")] alias comap_map_of_isPrimary_disjoint :=
  under_map_of_isPrimary_disjoint

theorem under_map_of_isPrime_disjoint {I : Ideal R} (hI : I.IsPrime) (hM : Disjoint (M : Set R) I) :
    (Ideal.map (algebraMap R S) I).under R = I :=
  under_map_of_isPrimary_disjoint M S hI.isPrimary hM

@[deprecated (since := "2026-04-09")] alias comap_map_of_isPrime_disjoint :=
  under_map_of_isPrime_disjoint

/-- If `S` is the localization of `R` at a submonoid, the ordering of ideals of `S` is
embedded in the ordering of ideals of `R`. -/
def orderEmbedding : Ideal S ↪o Ideal R where
  toFun J := J.under R
  inj' := Function.LeftInverse.injective (map_under M S)
  map_rel_iff' := by
    rintro J₁ J₂
    constructor
    · exact fun hJ => (map_under M S) J₁ ▸ (map_under M S) J₂ ▸ Ideal.map_mono hJ
    · exact fun hJ => Ideal.comap_mono hJ

include M in
theorem under_le_under_iff {I J : Ideal S} :
    I.under R ≤ J.under R ↔ I ≤ J := by
  exact (IsLocalization.orderEmbedding M S).le_iff_le

@[deprecated (since := "2026-04-09")] alias comap_le_comap_iff := under_le_under_iff

/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M`.
This lemma gives the particular case for an ideal and its comap,
see `le_rel_iso_of_prime` for the more general relation isomorphism -/
theorem isPrime_iff_isPrime_disjoint (J : Ideal S) :
    J.IsPrime ↔ (J.under R).IsPrime ∧ Disjoint (M : Set R) (J.under R) := by
  constructor
  · refine fun h =>
      ⟨⟨?_, ?_⟩,
        Set.disjoint_left.mpr fun m hm1 hm2 =>
          h.ne_top (Ideal.eq_top_of_isUnit_mem _ hm2 (map_units S ⟨m, hm1⟩))⟩
    · refine fun hJ => h.ne_top ?_
      rw [eq_top_iff, ← (orderEmbedding M S).le_iff_le]
      exact le_of_eq hJ.symm
    · intro x y hxy
      rw [Ideal.mem_comap, map_mul] at hxy
      exact h.mem_or_mem hxy
  · refine fun h => ⟨fun hJ => h.left.ne_top (eq_top_iff.2 ?_), ?_⟩
    · rwa [eq_top_iff, ← (orderEmbedding M S).le_iff_le] at hJ
    · intro x y hxy
      obtain ⟨a, s, ha⟩ := exists_mk'_eq M x
      obtain ⟨b, t, hb⟩ := exists_mk'_eq M y
      have : mk' S (a * b) (s * t) ∈ J := by rwa [mk'_mul, ha, hb]
      rw [mk'_mem_iff, ← Ideal.mem_comap] at this
      have this₂ := (h.1).mul_mem_iff_mem_or_mem.1 this
      rw [Ideal.mem_comap, Ideal.mem_comap] at this₂
      rwa [← ha, ← hb, mk'_mem_iff, mk'_mem_iff]

/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M`.
This lemma gives the particular case for an ideal and its map,
see `le_rel_iso_of_prime` for the more general relation isomorphism, and the reverse implication -/
theorem isPrime_of_isPrime_disjoint (I : Ideal R) (hp : I.IsPrime) (hd : Disjoint (M : Set R) ↑I) :
    (Ideal.map (algebraMap R S) I).IsPrime := by
  rw [isPrime_iff_isPrime_disjoint M S, under_map_of_isPrime_disjoint M S hp hd]
  exact ⟨hp, hd⟩

theorem disjoint_under_iff (J : Ideal S) :
    Disjoint (M : Set R) (J.under R) ↔ J ≠ ⊤ := by
  rw [← iff_not_comm, Set.not_disjoint_iff]
  constructor
  · rintro rfl
    exact ⟨1, M.one_mem, ⟨⟩⟩
  · rintro ⟨x, hxM, hxJ⟩
    exact J.eq_top_of_isUnit_mem hxJ (IsLocalization.map_units S ⟨x, hxM⟩)

@[deprecated (since := "2026-04-09")] alias disjoint_comap_iff := disjoint_under_iff

/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M` -/
@[simps] def orderIsoOfPrime :
    { p : Ideal S // p.IsPrime } ≃o { p : Ideal R // p.IsPrime ∧ Disjoint (M : Set R) ↑p } where
  toFun p := ⟨p.1.under R, (isPrime_iff_isPrime_disjoint M S p.1).1 p.2⟩
  invFun p := ⟨Ideal.map (algebraMap R S) p.1, isPrime_of_isPrime_disjoint M S p.1 p.2.1 p.2.2⟩
  left_inv J := Subtype.ext (map_under M S J)
  right_inv I := Subtype.ext (under_map_of_isPrime_disjoint M S I.2.1 I.2.2)
  map_rel_iff' {I I'} := by
    constructor
    · exact fun h => show I.val ≤ I'.val from map_under M S I.val ▸
        map_under M S I'.val ▸ Ideal.map_mono h
    exact fun h x hx => h hx

/-- The prime spectrum of the localization of a ring at a submonoid `M` are in
order-preserving bijection with subset of the prime spectrum of the ring consisting of
prime ideals disjoint from `M`. -/
@[simps!] def primeSpectrumOrderIso :
    PrimeSpectrum S ≃o {p : PrimeSpectrum R // Disjoint (M : Set R) p.asIdeal} :=
  (PrimeSpectrum.equivSubtype S).trans <| (orderIsoOfPrime M S).trans
    ⟨⟨fun p ↦ ⟨⟨p, p.2.1⟩, p.2.2⟩, fun p ↦ ⟨p.1.1, p.1.2, p.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩, .rfl⟩

include M in
lemma map_radical (I : Ideal R) :
    I.radical.map (algebraMap R S) = (I.map (algebraMap R S)).radical := by
  refine (I.map_radical_le (algebraMap R S)).antisymm ?_
  rintro x ⟨n, hn⟩
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  simp only [← IsLocalization.mk'_pow, IsLocalization.mk'_mem_map_algebraMap_iff M] at hn ⊢
  obtain ⟨s, hs, h⟩ := hn
  refine ⟨s, hs, n + 1, by convert I.mul_mem_left (s ^ n * x) h; ring⟩

theorem ideal_eq_iInf_under_map_away {S : Finset R} (hS : Ideal.span (α := R) S = ⊤) (I : Ideal R) :
    I = ⨅ f ∈ S, (I.map (algebraMap R (Localization.Away f))).under R := by
  apply le_antisymm
  · simp only [le_iInf₂_iff, ← Ideal.map_le_iff_le_comap, le_refl, implies_true]
  · intro x hx
    apply Submodule.mem_of_span_eq_top_of_smul_pow_mem _ _ hS
    rintro ⟨s, hs⟩
    simp only [Ideal.mem_iInf, Ideal.mem_comap] at hx
    obtain ⟨⟨y, ⟨_, n, rfl⟩⟩, e⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (.powers s) _).mp (hx s hs)
    dsimp only at e
    rw [← map_mul, IsLocalization.eq_iff_exists (.powers s)] at e
    obtain ⟨⟨_, m, rfl⟩, e⟩ := e
    use m + n
    dsimp at e ⊢
    rw [pow_add, mul_assoc, ← mul_comm x, e]
    exact I.mul_mem_left _ y.2

@[deprecated (since := "2026-04-09")] alias ideal_eq_iInf_comap_map_away :=
  ideal_eq_iInf_under_map_away

lemma map_eq_top_of_not_subset {I : Ideal R} (hle : ¬ (I : Set R) ⊆ Mᶜ) :
    Ideal.map (algebraMap R S) I = ⊤ := by
  simp only [Set.not_subset_iff_exists_mem_notMem, Set.mem_compl_iff, not_not] at hle
  obtain ⟨y, hy, hny⟩ := hle
  apply Ideal.eq_top_of_isUnit_mem
  · exact Ideal.mem_map_of_mem (algebraMap R _) hy
  · exact IsLocalization.map_units _ (⟨y, hny⟩ : M)

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] (M : Submonoid R) (S : Type*) [CommRing S]
variable [Algebra R S] [IsLocalization M S]

include M in
/-- `quotientMap` applied to maximal ideals of a localization is `surjective`.
The quotient by a maximal ideal is a field, so inverses to elements already exist,
and the localization necessarily maps the equivalence class of the inverse in the localization -/
theorem surjective_quotientMap_of_maximal_of_localization {I : Ideal S} [I.IsPrime] {J : Ideal R}
    {H : J ≤ I.under R} (hI : (I.under R).IsMaximal) :
    Function.Surjective (Ideal.quotientMap I (algebraMap R S) H) := by
  intro s
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨r, ⟨m, hm⟩, rfl⟩ := exists_mk'_eq M s
  by_cases hM : (Ideal.Quotient.mk (I.comap (algebraMap R S))) m = 0
  · have : I = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap] at hM
      convert I.mul_mem_right (mk' S (1 : R) ⟨m, hm⟩) hM
      rw [← mk'_eq_mul_mk'_one, mk'_self]
    exact ⟨0, eq_comm.1 (by simp [Ideal.Quotient.eq_zero_iff_mem, this])⟩
  · rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient] at hI
    obtain ⟨n, hn⟩ := hI.3 hM
    obtain ⟨rn, rfl⟩ := Ideal.Quotient.mk_surjective n
    refine ⟨(Ideal.Quotient.mk J) (r * rn), ?_⟩
    -- The rest of the proof is essentially just algebraic manipulations to prove the equality
    replace hn := congr_arg (Ideal.quotientMap I (algebraMap R S) le_rfl) hn
    rw [map_one, map_mul] at hn
    rw [Ideal.quotientMap_mk, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, ←
      Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, mk'_eq_mul_mk'_one]
    simp only [mul_eq_mul_left_iff, map_mul]
    refine
      Or.inl
        (mul_left_cancel₀ (M₀ := S ⧸ I)
          (fun hn =>
            hM
              (Ideal.Quotient.eq_zero_iff_mem.2
                (Ideal.mem_comap.2 (Ideal.Quotient.eq_zero_iff_mem.1 hn))))
          (_root_.trans hn ?_))
    rw [← map_mul, ← mk'_eq_mul_mk'_one, mk'_self, map_one]

open nonZeroDivisors

theorem bot_lt_under_prime [IsDomain R] (hM : M ≤ R⁰) (p : Ideal S) [hpp : p.IsPrime]
    (hp0 : p ≠ ⊥) : ⊥ < p.under R := by
  haveI : IsDomain S := isDomain_of_le_nonZeroDivisors _ hM
  rw [← Ideal.comap_bot_of_injective (algebraMap R S) (IsLocalization.injective _ hM)]
  convert (orderIsoOfPrime M S).lt_iff_lt.mpr (show (⟨⊥, Ideal.isPrime_bot⟩ :
    { p : Ideal S // p.IsPrime }) < ⟨p, hpp⟩ from hp0.bot_lt)

@[deprecated (since := "2026-04-09")] alias bot_lt_comap_prime := bot_lt_under_prime

variable (R) in
lemma _root_.Module.IsTorsionFree.of_isLocalization [IsDomain R] [IsDomain S] {Rₚ Sₚ : Type*}
    [CommRing Rₚ] [IsDomain Rₚ] [CommRing Sₚ] [Algebra R Rₚ] [Algebra R Sₚ] [Algebra S Sₚ]
    [Algebra Rₚ Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ] {M : Submonoid R} (hM : M ≤ R⁰)
    [IsLocalization M Rₚ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₚ]
    [Module.IsTorsionFree R S] : Module.IsTorsionFree Rₚ Sₚ := by
  have e : Algebra.algebraMapSubmonoid S M ≤ S⁰ :=
    Submonoid.map_le_of_le_comap _ <| hM.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective _ _))
  have : IsDomain Sₚ := IsLocalization.isDomain_of_le_nonZeroDivisors _ e
  have : algebraMap Rₚ Sₚ = IsLocalization.map (T := Algebra.algebraMapSubmonoid S M) Sₚ
    (algebraMap R S) (Submonoid.le_comap_map M) := by
    apply IsLocalization.ringHom_ext M
    simp only [IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]
  rw [Module.isTorsionFree_iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot,
    RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  simp only [IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff,
    Subtype.exists, exists_prop, this] at hx ⊢
  obtain ⟨_, ⟨a, ha, rfl⟩, H⟩ := hx
  simp only [← map_mul,
    (injective_iff_map_eq_zero' _).mp (FaithfulSMul.algebraMap_injective R S)] at H
  exact ⟨a, ha, H⟩

lemma of_surjective {R' S' : Type*} [CommRing R'] [CommRing S'] [Algebra R' S']
    (f : R →+* R') (hf : Function.Surjective f) (g : S →+* S') (hg : Function.Surjective g)
    (H : g.comp (algebraMap R S) = (algebraMap _ _).comp f)
    (H' : RingHom.ker g ≤ (RingHom.ker f).map (algebraMap R S)) : IsLocalization (M.map f) S' where
  map_units := by
    rintro ⟨_, y, hy, rfl⟩
    simpa only [← RingHom.comp_apply, H] using (IsLocalization.map_units S ⟨y, hy⟩).map g
  surj := by
    intro z
    obtain ⟨z, rfl⟩ := hg z
    obtain ⟨⟨r, s⟩, e⟩ := IsLocalization.surj M z
    refine ⟨⟨f r, _, s.1, s.2, rfl⟩, ?_⟩
    simpa only [map_mul, ← RingHom.comp_apply, H] using DFunLike.congr_arg g e
  exists_of_eq := by
    intro x y e
    obtain ⟨x, rfl⟩ := hf x
    obtain ⟨y, rfl⟩ := hf y
    rw [← sub_eq_zero, ← map_sub, ← map_sub, ← RingHom.comp_apply, ← H, RingHom.comp_apply,
      ← IsLocalization.mk'_one (M := M)] at e
    obtain ⟨r, hr, hr'⟩ := (IsLocalization.mk'_mem_map_algebraMap_iff M _ _ _ _).mp (H' e)
    exact ⟨⟨_, r, hr, rfl⟩, by simpa [sub_eq_zero, mul_sub] using hr'⟩

instance (I : Ideal R) :
    IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) M) (S ⧸ I.map (algebraMap R S)) :=
  of_surjective M S (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (I.map (algebraMap R S))) Ideal.Quotient.mk_surjective rfl (by simp)

open Algebra in
instance {P : Ideal R} [P.IsPrime] [IsDomain R] [IsDomain S] [FaithfulSMul R S] :
    IsDomain (Localization (algebraMapSubmonoid S P.primeCompl)) :=
  isDomain_localization (map_le_nonZeroDivisors_of_injective _
    (FaithfulSMul.algebraMap_injective R S) P.primeCompl_le_nonZeroDivisors)

end CommRing

end IsLocalization
