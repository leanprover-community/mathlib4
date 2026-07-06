import Mathlib.AlgebraicGeometry.AlgebraicCycle.Sheaf
import Mathlib.AlgebraicGeometry.AlgebraicCycle.UFD
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# The stalk of `𝒪ₓ(D)` at a point with factorial local ring

This file computes stalks of the divisorial sheaf `𝒪ₓ(D)` at points `x` of arbitrary
codimension whose local ring is a UFD, generalizing the codimension-one (DVR) computation
`stalkEquiv` of `Mathlib.AlgebraicGeometry.AlgebraicCycle.Sheaf`.

The dictionary between prime elements of `𝒪_{X,x}` and codimension-one points `z ⤳ x`:

- `exists_coheight_eq_one_specializes_of_prime`: every prime element `ϖ` of `𝒪_{X,x}` determines
  a codimension-one point `z ⤳ x` such that germs at `z` are `ϖ`-integral fractions over
  `𝒪_{X,x}` (i.e. the local ring at `z` is the localization of `𝒪_{X,x}` at `(ϖ)`).
- `mem_range_algebraMap_stalk_iff_forall_ord_nonneg` (geometric Hartogs): for a UFD stalk,
  a rational function lies in `𝒪_{X,x}` iff it has nonnegative order of vanishing at every
  codimension-one point specializing to `x`.
- `exists_prime_ord_eq_one_of_specializes`: conversely, every codimension-one `z ⤳ x` has a
  local equation at `x`: a prime of `𝒪_{X,x}` vanishing to order one at `z` and to order zero
  at every other codimension-one point specializing to `x`.

The stalk computation:

- `exists_functionField_ord_eq`: every divisor `D` admits a local equation `g` at `x`, i.e.
  `X.ord g z = D z` for all codimension-one `z ⤳ x` (Weil divisors are locally principal at
  factorial points).
- `stalkEquivUFD`: multiplication by `g` identifies the stalk of `𝒪ₓ(D)` at `x` with
  `𝒪_{X,x}` as `𝒪_{X,x}`-modules; `algebraMap_stalkEquivUFD_apply` is its defining property.
-/

open AlgebraicGeometry Scheme CategoryTheory Order Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/--
Every prime element `ϖ` of the local ring at `x` determines a codimension-one point `z`
specializing to `x`, whose germs are exactly the `ϖ`-integral fractions over `𝒪_{X,x}`: `z` is
the image of the height-one prime `(ϖ)` under `Spec 𝒪_{X,x} → X`, computed in an affine chart.
-/
lemma exists_coheight_eq_one_specializes_of_prime {x : X} {ϖ : X.presheaf.stalk x}
    (hϖ : Prime ϖ) :
    ∃ z : X, coheight z = 1 ∧ z ⤳ x ∧
      ∀ f : X.functionField, f ∈ (algebraMap (X.presheaf.stalk z) X.functionField).range →
        ∃ a b : X.presheaf.stalk x, ¬ ϖ ∣ b ∧
          f * algebraMap (X.presheaf.stalk x) X.functionField b =
            algebraMap (X.presheaf.stalk x) X.functionField a := by
  -- Work in an affine chart `U ∋ x`, where the stalk at `x` is the localization of `R := Γ(X, U)`
  -- at the prime of `x`.
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (trivial : x ∈ ⊤)
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
  haveI hLocx := hU.isLocalization_stalk ⟨x, hxU⟩
  -- The prime of `R` corresponding to `(ϖ)`, and the corresponding point `z` of `X`.
  have hspanP : (Ideal.span {ϖ}).IsPrime := (Ideal.span_singleton_prime hϖ.ne_zero).mpr hϖ
  set 𝔮 : PrimeSpectrum Γ(X, U) :=
    ⟨(Ideal.span {ϖ}).comap (algebraMap Γ(X, U) (X.presheaf.stalk x)), hspanP.comap _⟩ with h𝔮
  set z : X := hU.fromSpec 𝔮 with hz
  have hzU : z ∈ U := by
    change z ∈ (U : Set X)
    rw [← hU.range_fromSpec]
    exact ⟨𝔮, rfl⟩
  -- The prime of `z` in the chart is `𝔮` (round trip through `fromSpec`).
  have hround : hU.primeIdealOf ⟨z, hzU⟩ = 𝔮 :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf ⟨z, hzU⟩)
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨z, hzU⟩ : U)
  haveI hLocz : IsLocalization.AtPrime (X.presheaf.stalk z) 𝔮.asIdeal := by
    have := hU.isLocalization_stalk ⟨z, hzU⟩
    rwa [hround] at this
  -- `𝔮 ≤ 𝔭ₓ`, so `z ⤳ x`.
  have hle : 𝔮.asIdeal ≤ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
    intro r hr
    have hm : Ideal.span {ϖ} ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
      IsLocalRing.le_maximalIdeal fun hT => hϖ.not_unit (Ideal.span_singleton_eq_top.mp hT)
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal r).mp (hm hr)
  have hzx : z ⤳ x := by
    have hspec : (𝔮 : PrimeSpectrum Γ(X, U)) ⤳ hU.primeIdealOf ⟨x, hxU⟩ :=
      (PrimeSpectrum.le_iff_specializes _ _).mp hle
    have := hspec.map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf ⟨x, hxU⟩] at this
  -- `coheight z = 1`: the stalk at `z` is the localization of `R` at `𝔮`, whose Krull dimension
  -- is `ht 𝔮 = ht (ϖ) = 1`.
  have hcoh : coheight z = 1 := by
    have h1 : ringKrullDim (X.presheaf.stalk z) = 𝔮.asIdeal.height :=
      IsLocalization.AtPrime.ringKrullDim_eq_height _ _
    have h2 : 𝔮.asIdeal.height = (Ideal.span {ϖ}).height :=
      IsLocalization.height_under (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl _
    have h3 : (Ideal.span {ϖ} : Ideal (X.presheaf.stalk x)).height = 1 :=
      Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero) hϖ.not_unit
    have h4 := ringKrullDim_stalk_eq_coheight z
    rw [h1, h2, h3] at h4
    exact_mod_cast h4.symm
  refine ⟨z, hcoh, hzx, ?_⟩
  -- Germs at `z` are fractions `r / s` with `s ∉ 𝔮`, i.e. `ϖ ∤ s` in the stalk at `x`.
  rintro f ⟨g, rfl⟩
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (M := 𝔮.asIdeal.primeCompl) g
  refine ⟨algebraMap Γ(X, U) (X.presheaf.stalk x) r, algebraMap Γ(X, U) (X.presheaf.stalk x) s,
    fun hdvd => s.2 (Ideal.mem_comap.mpr (Ideal.mem_span_singleton.mpr hdvd)), ?_⟩
  -- Push `g * s = r` from the stalk at `z` into the function field, collapsing the towers
  -- `R → 𝒪_{X,z} → K` and `R → 𝒪_{X,x} → K`.
  haveI := functionField_isScalarTower X U (⟨z, hzU⟩ : U)
  haveI := functionField_isScalarTower X U (⟨x, hxU⟩ : U)
  have hpush := congrArg (algebraMap (X.presheaf.stalk z) X.functionField) hrs
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at hpush
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  exact hpush

/--
**Geometric Hartogs for factorial stalks.** If the local ring of `X` at `x` is a UFD, then a
rational function belongs to `𝒪_{X,x}` if and only if it has nonnegative order of vanishing at
every codimension-one point specializing to `x`.
-/
lemma mem_range_algebraMap_stalk_iff_forall_ord_nonneg [IsRegularInCodimensionOne X] {x : X}
    [UniqueFactorizationMonoid (X.presheaf.stalk x)] (f : X.functionField) :
    f ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range ↔
      (f ≠ 0 → ∀ z, coheight z = 1 → z ⤳ x → 0 ≤ X.ord f z) := by
  constructor
  · -- A germ at `x` restricts to a germ at every `z ⤳ x`, where sections have
    -- nonnegative order.
    rintro ⟨a, rfl⟩ hne z hz hzx
    obtain ⟨W, hxW, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf a
    haveI : Nonempty W := ⟨⟨x, hxW⟩⟩
    have hzW : z ∈ W := hzx.mem_open W.2 hxW
    have hcompat : algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W x hxW s) =
        algebraMap (X.presheaf.stalk z) X.functionField (X.presheaf.germ W z hzW s) := by
      rw [Scheme.algebraMap_germ_eq_germToFunctionField hxW,
        Scheme.algebraMap_germ_eq_germToFunctionField hzW]
    exact (mem_range_algebraMap_iff_ord_nonneg hz _).mp
      ⟨X.presheaf.germ W z hzW s, hcompat.symm⟩ hne
  · -- Conversely, apply Hartogs for UFDs: each prime `ϖ` of the stalk has a corresponding
    -- codimension-one point `z ⤳ x` where the order bound gives a `ϖ`-integral representation.
    intro h
    rcases eq_or_ne f 0 with rfl | hne
    · exact ⟨0, map_zero _⟩
    refine ufd_hartogs fun ϖ hϖ => ?_
    obtain ⟨z, hz, hzx, hrep⟩ := exists_coheight_eq_one_specializes_of_prime hϖ
    exact hrep f ((mem_range_algebraMap_iff_ord_nonneg hz f).mpr
      (fun _ => h hne z hz hzx))

/-- The image in the function field of a unit of the local ring at a codimension-one point has
order of vanishing zero. -/
lemma ord_algebraMap_eq_zero_of_isUnit [IsRegularInCodimensionOne X] {z : X}
    (hz : coheight z = 1) {a : X.presheaf.stalk z} (ha : IsUnit a) :
    X.ord (algebraMap (X.presheaf.stalk z) X.functionField a) z = 0 := by
  have hane : a ≠ 0 := ha.ne_zero
  refine le_antisymm ?_ (ord_algebraMap_nonneg hz hane)
  by_contra hlt
  push Not at hlt
  exact mem_nonunits_iff.mp ((mem_maximalIdeal_iff_one_le_ord hz hane).mpr (by omega)) ha

/--
**Local equations for prime divisors.** If the local ring of `X` at `x` is a UFD, then every
codimension-one point `z ⤳ x` admits a local equation at `x`: a prime element `ϖ` of `𝒪_{X,x}`
vanishing to order exactly one at `z` and to order zero at every other codimension-one point
specializing to `x`. It is a generator of the height-one prime of `𝒪_{X,x}` corresponding
to `z`.
-/
lemma exists_prime_ord_eq_one_of_specializes [IsRegularInCodimensionOne X] {x z : X}
    [UniqueFactorizationMonoid (X.presheaf.stalk x)] (hz : coheight z = 1) (hzx : z ⤳ x) :
    ∃ ϖ : X.presheaf.stalk x, Prime ϖ ∧
      X.ord (algebraMap (X.presheaf.stalk x) X.functionField ϖ) z = 1 ∧
      ∀ z' : X, coheight z' = 1 → z' ⤳ x → z' ≠ z →
        X.ord (algebraMap (X.presheaf.stalk x) X.functionField ϖ) z' = 0 := by
  -- Work in an affine chart `U ∋ x`; every point specializing to `x` lies in `U`.
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (trivial : x ∈ ⊤)
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
  haveI hLocx := hU.isLocalization_stalk ⟨x, hxU⟩
  haveI := functionField_isScalarTower X U (⟨x, hxU⟩ : U)
  -- For `w ⤳ x` in `U`, the chart prime of `w` is contained in that of `x`, and its extension
  -- to the stalk at `x` is a prime lying over it, of height `coheight w`.
  have hkey : ∀ w, w ⤳ x → ∀ hwU : w ∈ U,
      (hU.primeIdealOf ⟨w, hwU⟩).asIdeal ≤ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ∧
      ((hU.primeIdealOf ⟨w, hwU⟩).asIdeal.map
          (algebraMap Γ(X, U) (X.presheaf.stalk x))).IsPrime ∧
      Ideal.comap (algebraMap Γ(X, U) (X.presheaf.stalk x))
          ((hU.primeIdealOf ⟨w, hwU⟩).asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk x))) =
        (hU.primeIdealOf ⟨w, hwU⟩).asIdeal ∧
      (coheight w = 1 → ((hU.primeIdealOf ⟨w, hwU⟩).asIdeal.map
          (algebraMap Γ(X, U) (X.presheaf.stalk x))).height = 1) := by
    intro w hwx hwU
    have hle : (hU.primeIdealOf ⟨w, hwU⟩).asIdeal ≤ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
      refine (PrimeSpectrum.le_iff_specializes _ _).mpr
        (hU.fromSpec.isOpenEmbedding.toIsEmbedding.toIsInducing.specializes_iff.mp ?_)
      rw [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf]
      exact hwx
    have hdisj : Disjoint ((hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl : Set Γ(X, U))
        ((hU.primeIdealOf ⟨w, hwU⟩).asIdeal : Set Γ(X, U)) :=
      Set.disjoint_left.mpr fun t ht ht' => ht (hle ht')
    have hprime := IsLocalization.isPrime_of_isPrime_disjoint
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨w, hwU⟩).asIdeal (hU.primeIdealOf ⟨w, hwU⟩).2 hdisj
    have hcomap : Ideal.comap (algebraMap Γ(X, U) (X.presheaf.stalk x))
        ((hU.primeIdealOf ⟨w, hwU⟩).asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk x))) =
        (hU.primeIdealOf ⟨w, hwU⟩).asIdeal :=
      IsLocalization.under_map_of_isPrime_disjoint
        (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (X.presheaf.stalk x)
        (hU.primeIdealOf ⟨w, hwU⟩).2 hdisj
    refine ⟨hle, hprime, hcomap, fun hw => ?_⟩
    -- The height of the extension equals `coheight w`, computed via the stalk at `w`.
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨w, hwU⟩ : U)
    haveI hLocw := hU.isLocalization_stalk ⟨w, hwU⟩
    haveI := hprime
    have hhu : (Ideal.comap (algebraMap Γ(X, U) (X.presheaf.stalk x))
        ((hU.primeIdealOf ⟨w, hwU⟩).asIdeal.map
          (algebraMap Γ(X, U) (X.presheaf.stalk x)))).height =
        ((hU.primeIdealOf ⟨w, hwU⟩).asIdeal.map
          (algebraMap Γ(X, U) (X.presheaf.stalk x))).height :=
      IsLocalization.height_under (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl _
    rw [hcomap] at hhu
    have h2 : ringKrullDim (X.presheaf.stalk w) =
        (hU.primeIdealOf ⟨w, hwU⟩).asIdeal.height :=
      IsLocalization.AtPrime.ringKrullDim_eq_height _ _
    have h3 := ringKrullDim_stalk_eq_coheight w
    rw [hw] at h3
    rw [h3] at h2
    rw [← hhu]
    exact_mod_cast h2.symm
  -- The height-one prime of the stalk corresponding to `z`, and a prime generator `ϖ`.
  have hzU : z ∈ U := hzx.mem_open U.2 hxU
  obtain ⟨hlez, hprimez, hcomapz, hhtz⟩ := hkey z hzx hzU
  haveI := hprimez
  obtain ⟨ϖ, hϖ, hq⟩ := Ideal.exists_prime_span_of_height_eq_one (hhtz hz)
  -- Write `ϖ = r / s` over `R = Γ(X, U)` with `s` invertible near `x`.
  obtain ⟨⟨r, s⟩, hrs⟩ :=
    IsLocalization.surj (M := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl) ϖ
  have hsA : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) (s : Γ(X, U))) :=
    IsLocalization.map_units (X.presheaf.stalk x) s
  have hϖK : algebraMap (X.presheaf.stalk x) X.functionField ϖ ≠ 0 :=
    algebraMap_functionField_ne_zero hϖ.ne_zero
  have hsK : algebraMap Γ(X, U) X.functionField (s : Γ(X, U)) ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk x) X.functionField]
    exact algebraMap_functionField_ne_zero hsA.ne_zero
  -- The defining equation `ϖ * s = r` in the function field.
  have hK : algebraMap (X.presheaf.stalk x) X.functionField ϖ *
      algebraMap Γ(X, U) X.functionField (s : Γ(X, U)) =
      algebraMap Γ(X, U) X.functionField r := by
    rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk x) X.functionField,
      IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk x) X.functionField r, ← map_mul]
    exact congrArg _ hrs
  have hrK : algebraMap Γ(X, U) X.functionField r ≠ 0 := hK ▸ mul_ne_zero hϖK hsK
  -- `r` lies in the chart prime of `z`.
  have hr𝔮z : r ∈ (hU.primeIdealOf ⟨z, hzU⟩).asIdeal := by
    rw [← hcomapz]
    refine Ideal.mem_comap.mpr ?_
    rw [hq]
    exact Ideal.mem_span_singleton.mpr ⟨_, hrs.symm⟩
  -- At every codimension-one `w ⤳ x`, `ord ϖ = ord r` since `s` is a unit near `x`.
  have hordEq : ∀ w, coheight w = 1 → ∀ hwx : w ⤳ x, ∀ hwU : w ∈ U,
      X.ord (algebraMap (X.presheaf.stalk x) X.functionField ϖ) w =
      X.ord (algebraMap Γ(X, U) X.functionField r) w := by
    intro w hw hwx hwU
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨w, hwU⟩ : U)
    haveI hLocw := hU.isLocalization_stalk ⟨w, hwU⟩
    haveI := functionField_isScalarTower X U (⟨w, hwU⟩ : U)
    have hsW : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk w) (s : Γ(X, U))) := by
      by_contra hns
      exact s.2 ((hkey w hwx hwU).1 ((IsLocalization.AtPrime.to_map_mem_maximal_iff _
        (hU.primeIdealOf ⟨w, hwU⟩).asIdeal (s : Γ(X, U))).mp
        (mem_nonunits_iff.mpr hns)))
    have hs0 : X.ord (algebraMap Γ(X, U) X.functionField (s : Γ(X, U))) w = 0 := by
      rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk w) X.functionField]
      exact ord_algebraMap_eq_zero_of_isUnit hw hsW
    have hmul := X.ord_mul hw hϖK hsK
    rw [hK, hs0] at hmul
    omega
  refine ⟨ϖ, hϖ, ?_, ?_⟩
  · -- At `z` the order is exactly one: `r` maps to a uniformizer of the DVR stalk, since
    -- `r ∈ 𝔮z` but `r ∉ 𝔮z²` (else `ϖ` would divide a unit times a non-multiple).
    rw [hordEq z hz hzx hzU]
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨z, hzU⟩ : U)
    haveI hLocz := hU.isLocalization_stalk ⟨z, hzU⟩
    haveI := functionField_isScalarTower X U (⟨z, hzU⟩ : U)
    haveI : IsDiscreteValuationRing (X.presheaf.stalk z) :=
      IsRegularInCodimensionOne.stalk_dvr z hz
    have hrZ0 : algebraMap Γ(X, U) (X.presheaf.stalk z) r ≠ 0 := by
      intro h0
      apply hrK
      rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk z) X.functionField, h0,
        map_zero]
    obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk z)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hrZ0 hϖ'
    have hordr : X.ord (algebraMap Γ(X, U) X.functionField r) z = n := by
      have hne1 : algebraMap (X.presheaf.stalk z) X.functionField (u : X.presheaf.stalk z) ≠ 0 :=
        algebraMap_functionField_ne_zero u.isUnit.ne_zero
      have hne2 : (algebraMap (X.presheaf.stalk z) X.functionField ϖ') ^ n ≠ 0 :=
        pow_ne_zero n (algebraMap_functionField_ne_zero hϖ'.ne_zero)
      rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk z) X.functionField, hu,
        map_mul, map_pow, X.ord_mul hz hne1 hne2,
        ord_algebraMap_eq_zero_of_isUnit hz u.isUnit,
        ← zpow_natCast (algebraMap (X.presheaf.stalk z) X.functionField ϖ') n,
        ord_zpow_algebraMap_irreducible hz hϖ' (n : ℤ), zero_add]
    -- `n ≥ 1` since `r` vanishes at `z`.
    have hrZmem : algebraMap Γ(X, U) (X.presheaf.stalk z) r ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk z) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _
        (hU.primeIdealOf ⟨z, hzU⟩).asIdeal r).mpr hr𝔮z
    have hn1 : 1 ≤ n := by
      by_contra hn
      push Not at hn
      obtain rfl : n = 0 := Nat.lt_one_iff.mp hn
      rw [pow_zero, mul_one] at hu
      exact mem_nonunits_iff.mp (hu ▸ hrZmem) u.isUnit
    -- `n ≤ 1`: otherwise `r ∈ 𝔮z²` descends to a factorization contradicting primality of `ϖ`.
    have hn2 : n ≤ 1 := by
      by_contra hn
      push Not at hn
      have hn' : 2 ≤ n := hn
      have hmem2 : algebraMap Γ(X, U) (X.presheaf.stalk z) r ∈
          ((hU.primeIdealOf ⟨z, hzU⟩).asIdeal ^ 2).map
            (algebraMap Γ(X, U) (X.presheaf.stalk z)) := by
        rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal
          (hU.primeIdealOf ⟨z, hzU⟩).asIdeal (X.presheaf.stalk z), hϖ'.maximalIdeal_eq,
          Ideal.span_singleton_pow, Ideal.mem_span_singleton]
        exact dvd_trans (pow_dvd_pow ϖ' hn') ⟨↑u, by rw [hu]; ring⟩
      -- Descend to the chart: `r * t ∈ 𝔮z ^ 2` for some `t ∉ 𝔮z`.
      obtain ⟨⟨⟨v, hv⟩, ⟨t, ht⟩⟩, hvt⟩ := (IsLocalization.mem_map_algebraMap_iff
        (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl (X.presheaf.stalk z)).mp hmem2
      have hvt' : algebraMap Γ(X, U) (X.presheaf.stalk z) (r * t) =
          algebraMap Γ(X, U) (X.presheaf.stalk z) v := by
        rw [map_mul]; exact hvt
      have hrt : r * t = v := by
        obtain ⟨⟨c, hcmem⟩, hc⟩ := (IsLocalization.eq_iff_exists
          (M := (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl)
          (S := X.presheaf.stalk z)).mp hvt'
        have hc0 : c ≠ 0 := fun h0 =>
          hcmem (by rw [h0]; exact (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.zero_mem)
        exact mul_left_cancel₀ hc0 hc
      -- Push into the stalk at `x`: `ϖ²` divides `ϖ * s * t` with `s` a unit and `ϖ ∤ t`.
      have hvq : algebraMap Γ(X, U) (X.presheaf.stalk x) v ∈ Ideal.span {ϖ} ^ 2 := by
        rw [← hq, ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hv
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hvq
      obtain ⟨d, hd⟩ := hvq
      have hst : algebraMap Γ(X, U) (X.presheaf.stalk x) (s : Γ(X, U)) *
          algebraMap Γ(X, U) (X.presheaf.stalk x) t = ϖ * d := by
        apply mul_left_cancel₀ hϖ.ne_zero
        calc ϖ * (algebraMap Γ(X, U) (X.presheaf.stalk x) (s : Γ(X, U)) *
              algebraMap Γ(X, U) (X.presheaf.stalk x) t)
            = (ϖ * algebraMap Γ(X, U) (X.presheaf.stalk x) (s : Γ(X, U))) *
              algebraMap Γ(X, U) (X.presheaf.stalk x) t := by ring
          _ = algebraMap Γ(X, U) (X.presheaf.stalk x) (r * t) := by
              rw [map_mul, hrs]
          _ = algebraMap Γ(X, U) (X.presheaf.stalk x) v := by rw [hrt]
          _ = ϖ ^ 2 * d := hd
          _ = ϖ * (ϖ * d) := by ring
      rcases hϖ.2.2 _ _ ⟨d, hst⟩ with hdvd | hdvd
      · exact hϖ.not_unit (isUnit_of_dvd_unit hdvd hsA)
      · have ht𝔮 : t ∈ (hU.primeIdealOf ⟨z, hzU⟩).asIdeal := by
          rw [← hcomapz]
          exact Ideal.mem_comap.mpr (by rw [hq]; exact Ideal.mem_span_singleton.mpr hdvd)
        exact ht ht𝔮
    rw [hordr]
    omega
  · -- At `z' ≠ z` the order vanishes: a positive order would put `ϖ` in the height-one prime
    -- of `z'`, forcing the primes (hence the points) to coincide.
    intro z' hz' hz'x hne
    have hz'U : z' ∈ U := hz'x.mem_open U.2 hxU
    obtain ⟨hlez', hprimez', hcomapz', hhtz'⟩ := hkey z' hz'x hz'U
    rw [hordEq z' hz' hz'x hz'U]
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨z', hz'U⟩ : U)
    haveI hLocz' := hU.isLocalization_stalk ⟨z', hz'U⟩
    haveI := functionField_isScalarTower X U (⟨z', hz'U⟩ : U)
    have hrZ'0 : algebraMap Γ(X, U) (X.presheaf.stalk z') r ≠ 0 := by
      intro h0
      apply hrK
      rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk z') X.functionField, h0,
        map_zero]
    have hnonneg : 0 ≤ X.ord (algebraMap Γ(X, U) X.functionField r) z' := by
      rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk z') X.functionField]
      exact ord_algebraMap_nonneg hz' hrZ'0
    by_contra hne0
    have hr𝔮z' : r ∈ (hU.primeIdealOf ⟨z', hz'U⟩).asIdeal := by
      have hmem := (mem_maximalIdeal_iff_one_le_ord hz' hrZ'0).mpr (by
        rw [← IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk z') X.functionField]
        omega)
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _
        (hU.primeIdealOf ⟨z', hz'U⟩).asIdeal r).mp hmem
    haveI := hprimez'
    have hϖq' : ϖ ∈ (hU.primeIdealOf ⟨z', hz'U⟩).asIdeal.map
        (algebraMap Γ(X, U) (X.presheaf.stalk x)) := by
      have hrq' := Ideal.mem_map_of_mem (algebraMap Γ(X, U) (X.presheaf.stalk x)) hr𝔮z'
      rw [← hrs] at hrq'
      rcases hprimez'.mem_or_mem hrq' with h | h
      · exact h
      · exact absurd (Ideal.eq_top_of_isUnit_mem _ h hsA) hprimez'.ne_top
    have hq' : (hU.primeIdealOf ⟨z', hz'U⟩).asIdeal.map
        (algebraMap Γ(X, U) (X.presheaf.stalk x)) = Ideal.span {ϖ} :=
      Ideal.eq_span_singleton_of_height_eq_one (hhtz' hz') hϖq' hϖ
    have hPeq : hU.primeIdealOf ⟨z', hz'U⟩ = hU.primeIdealOf ⟨z, hzU⟩ := by
      refine PrimeSpectrum.ext ?_
      rw [← hcomapz', ← hcomapz, hq', hq]
    have h1 := hU.fromSpec_primeIdealOf ⟨z', hz'U⟩
    have h2 := hU.fromSpec_primeIdealOf ⟨z, hzU⟩
    rw [hPeq] at h1
    exact hne (h1.symm.trans h2)

/-- The order of vanishing of an integer power is the multiple of the order. -/
lemma ord_zpow {z : X} (hz : coheight z = 1) {f : X.functionField} (hf : f ≠ 0) (n : ℤ) :
    X.ord (f ^ n) z = n * X.ord f z := by
  have h1 : X.ordHom z hz f = WithZero.exp (X.ord f z) := by
    rw [WithZero.exp_eq_coe_ofAdd]
    exact (X.ord_eq_iff hz hf).mp rfl
  rw [X.ord_eq_iff hz (zpow_ne_zero n hf), map_zpow₀, h1, ← WithZero.exp_zsmul,
    smul_eq_mul, WithZero.exp_eq_coe_ofAdd]

/-- The order of vanishing of a finite product of nonzero rational functions is the sum of
the orders. -/
lemma ord_prod {ι : Type*} (T : Finset ι) (F : ι → X.functionField)
    (hF : ∀ i ∈ T, F i ≠ 0) {z : X} (hz : coheight z = 1) :
    X.ord (∏ i ∈ T, F i) z = ∑ i ∈ T, X.ord (F i) z := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have h2 := X.ord_mul hz (one_ne_zero (α := X.functionField)) one_ne_zero
    rw [mul_one] at h2
    simpa using by omega
  | insert a T haT ih =>
    have hprod : (∏ i ∈ T, F i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi => hF i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert haT, Finset.sum_insert haT,
      X.ord_mul hz (hF a (Finset.mem_insert_self a T)) hprod,
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

/--
**Local equations for divisors at factorial points.** If the local ring of `X` at `x` is a UFD,
then every divisor `D` admits a local equation at `x`: a rational function `g` whose order of
vanishing at every codimension-one point specializing to `x` agrees with `D`. It is the product
of the local equations of the finitely many prime divisors through `x` appearing in `D`.
-/
lemma exists_functionField_ord_eq [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ)
    {x : X} [UniqueFactorizationMonoid (X.presheaf.stalk x)] :
    ∃ g : X.functionField, g ≠ 0 ∧ ∀ z, coheight z = 1 → z ⤳ x → X.ord g z = D z := by
  classical
  -- The codimension-one points through `x` in the support of `D` form a finite set.
  obtain ⟨t, ht, htfin⟩ := D.supportLocallyFiniteWithinDomain x (Set.mem_univ x)
  have hSfin : {z : X | coheight z = 1 ∧ z ⤳ x ∧ D z ≠ 0}.Finite := by
    refine htfin.subset fun z hz => ⟨?_, Function.mem_support.mpr hz.2.2⟩
    obtain ⟨t₀, ht₀sub, ht₀open, hxt₀⟩ := mem_nhds_iff.mp ht
    exact ht₀sub (hz.2.1.mem_open ht₀open hxt₀)
  set S := hSfin.toFinset with hSdef
  -- Choose a local equation for each of them.
  have hchoice : ∀ z ∈ S, ∃ ϖK : X.functionField, ϖK ≠ 0 ∧ X.ord ϖK z = 1 ∧
      ∀ z', coheight z' = 1 → z' ⤳ x → z' ≠ z → X.ord ϖK z' = 0 := by
    intro z hzS
    rw [hSdef, Set.Finite.mem_toFinset] at hzS
    obtain ⟨ϖ, hϖ, h1, h0⟩ := exists_prime_ord_eq_one_of_specializes hzS.1 hzS.2.1
    exact ⟨algebraMap (X.presheaf.stalk x) X.functionField ϖ,
      algebraMap_functionField_ne_zero hϖ.ne_zero, h1, h0⟩
  choose ϖK hϖKne hϖK1 hϖK0 using hchoice
  refine ⟨∏ i ∈ S.attach, (ϖK i.1 i.2) ^ (D i.1), Finset.prod_ne_zero_iff.mpr
    fun i _ => zpow_ne_zero _ (hϖKne i.1 i.2), fun w hw hwx => ?_⟩
  rw [ord_prod _ _ (fun i _ => zpow_ne_zero _ (hϖKne i.1 i.2)) hw,
    Finset.sum_congr rfl fun i _ => ord_zpow hw (hϖKne i.1 i.2) (D i.1)]
  by_cases hwS : w ∈ S
  · -- Only the `w`-term contributes, giving `D w * 1`.
    rw [Finset.sum_eq_single (⟨w, hwS⟩ : {z // z ∈ S})]
    · rw [hϖK1 w hwS, mul_one]
    · rintro ⟨b, hb⟩ - hbw
      rw [hϖK0 b hb w hw hwx fun hEq => hbw (Subtype.ext hEq.symm), mul_zero]
    · intro habs
      exact absurd (Finset.mem_attach S ⟨w, hwS⟩) habs
  · -- All terms vanish, and `D w = 0` since `w` is not in the support.
    have hDw : D w = 0 := by
      by_contra hD0
      exact hwS (by rw [hSdef, Set.Finite.mem_toFinset]; exact ⟨hw, hwx, hD0⟩)
    rw [hDw]
    exact Finset.sum_eq_zero fun i _ => by
      rw [hϖK0 i.1 i.2 w hw hwx fun hEq => hwS (hEq.symm ▸ i.2), mul_zero]

/--
At a point `x` with factorial local ring, multiplication by a local equation `g` for `D`
carries the stalk of `𝒪ₓ(D)` at `x` onto the image of `𝒪_{X,x}` in the function field.
-/
lemma range_linearMap_eq_range_mulLeft_stalkToFunctionFieldLinearMap_of_ord_eq
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ)
    (hD : D.support ⊆ {x | coheight x = 1}) (x : X)
    [UniqueFactorizationMonoid (X.presheaf.stalk x)]
    {g : X.functionField} (hg0 : g ≠ 0)
    (hgord : ∀ z, coheight z = 1 → z ⤳ x → X.ord g z = D z) :
    LinearMap.range (Algebra.linearMap (X.presheaf.stalk x) X.functionField) =
      LinearMap.range ((LinearMap.mulLeft (X.presheaf.stalk x) g) ∘ₗ
        D.stalkToFunctionFieldLinearMap x) := by
  apply SetLike.coe_injective
  simp only [LinearMap.range_comp, Submodule.map_coe, LinearMap.coe_range]
  have range_eq : Set.range (D.stalkToFunctionFieldLinearMap x) =
      {f : X.functionField | f ≠ 0 → ∀ z, coheight z = 1 → z ⤳ x → - D z ≤ X.ord f z} := by
    simp only [stalkToFunctionFieldLinearMap]
    erw [range_stalkToFunctionField D hD x]
  rw [range_eq]
  ext w
  simp only [Set.mem_range, Algebra.linearMap_apply, Set.mem_image, Set.mem_setOf_eq,
    LinearMap.mulLeft_apply]
  have hHar := mem_range_algebraMap_stalk_iff_forall_ord_nonneg (X := X) (x := x) w
  -- The order of `g⁻¹` at every relevant point is `- D z`.
  have hginv : ∀ z, coheight z = 1 → z ⤳ x → X.ord g⁻¹ z = - D z := by
    intro z hz hzx
    have h1 := X.ord_mul hz hg0 (inv_ne_zero hg0)
    rw [mul_inv_cancel₀ hg0] at h1
    have h2 := X.ord_mul hz (one_ne_zero (α := X.functionField)) one_ne_zero
    rw [mul_one] at h2
    have h3 := hgord z hz hzx
    omega
  constructor
  · -- A function with everywhere-nonnegative order is `g` times a section of `𝒪ₓ(D)`.
    intro hw
    have hcond := hHar.mp (RingHom.mem_range.mpr hw)
    refine ⟨g⁻¹ * w, fun hf z hz hzx => ?_, ?_⟩
    · have hw0 : w ≠ 0 := right_ne_zero_of_mul hf
      rw [X.ord_mul hz (inv_ne_zero hg0) hw0, hginv z hz hzx]
      have h3 := hcond hw0 z hz hzx
      omega
    · rw [← mul_assoc, mul_inv_cancel₀ hg0, one_mul]
  · -- Conversely, `g` times a section of `𝒪ₓ(D)` has everywhere-nonnegative order.
    rintro ⟨r, hr, rfl⟩
    refine RingHom.mem_range.mp (hHar.mpr fun hne z hz hzx => ?_)
    have hr0 : r ≠ 0 := right_ne_zero_of_mul hne
    rw [X.ord_mul hz hg0 hr0, hgord z hz hzx]
    have h3 := hr hr0 z hz hzx
    omega

/--
The stalk of `𝒪ₓ(D)` at a point `x` with factorial local ring maps into `𝒪_{X,x}` by
multiplication by a local equation `g` for `D`; see `stalkMapUFD_bijective`.
-/
noncomputable def stalkMapUFD [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ)
    (hD : D.support ⊆ {x | coheight x = 1}) (x : X)
    [UniqueFactorizationMonoid (X.presheaf.stalk x)]
    {g : X.functionField} (hg0 : g ≠ 0)
    (hgord : ∀ z, coheight z = 1 → z ⤳ x → X.ord g z = D z) :
    ↑(TopCat.Presheaf.stalk D.sheaf.val.presheaf x) →ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x := by
  let f := (LinearMap.mulLeft (X.presheaf.stalk x) g) ∘ₗ D.stalkToFunctionFieldLinearMap x
  let a := Algebra.linearMap (X.presheaf.stalk x) X.functionField
  have hinj : Function.Injective a := FaithfulSMul.algebraMap_injective _ _
  have range_eq : f.range = a.range :=
    (range_linearMap_eq_range_mulLeft_stalkToFunctionFieldLinearMap_of_ord_eq
      D hD x hg0 hgord).symm
  let equiv := (Submodule.comap_equiv_self_of_inj_of_le (p := f.range) hinj range_eq.le).symm
  let equiv2 : (Submodule.comap a f.range) ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
    (LinearEquiv.ofEq _ ⊤ (by rw [range_eq, ← Submodule.map_top,
      Submodule.comap_map_eq_of_injective hinj])).trans Submodule.topEquiv
  exact equiv2 ∘ₗ equiv.toLinearMap ∘ₗ f.rangeRestrict

lemma stalkMapUFD_bijective [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ)
    (hD : D.support ⊆ {x | coheight x = 1}) (x : X)
    [UniqueFactorizationMonoid (X.presheaf.stalk x)]
    {g : X.functionField} (hg0 : g ≠ 0)
    (hgord : ∀ z, coheight z = 1 → z ⤳ x → X.ord g z = D z) :
    Function.Bijective (stalkMapUFD D hD x hg0 hgord) := by
  have hf : Function.Injective ⇑((LinearMap.mulLeft (X.presheaf.stalk x) g) ∘ₗ
      D.stalkToFunctionFieldLinearMap x) := by
    rw [LinearMap.coe_comp]
    exact Function.Injective.comp (fun a b hab => mul_left_cancel₀ hg0 hab)
      (fun a b hab => stalkToFunctionField_injective D x hab)
  unfold stalkMapUFD
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact (LinearEquiv.bijective _).comp <| (LinearEquiv.bijective _).comp
    ⟨(LinearMap.injective_rangeRestrict_iff _).mpr hf, LinearMap.surjective_rangeRestrict _⟩

/--
**The stalk of `𝒪ₓ(D)` at a factorial point.** At a point `x` whose local ring is a UFD, the
stalk of `𝒪ₓ(D)` is isomorphic to `𝒪_{X,x}` as an `𝒪_{X,x}`-module, via multiplication by a
local equation `g` for `D` at `x` (which exists by `exists_functionField_ord_eq`). This
generalizes `stalkEquiv` from codimension-one points to arbitrary factorial points.
-/
noncomputable def stalkEquivUFD [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ)
    (hD : D.support ⊆ {x | coheight x = 1}) (x : X)
    [UniqueFactorizationMonoid (X.presheaf.stalk x)]
    {g : X.functionField} (hg0 : g ≠ 0)
    (hgord : ∀ z, coheight z = 1 → z ⤳ x → X.ord g z = D z) :
    ↑(TopCat.Presheaf.stalk D.sheaf.val.presheaf x) ≃ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x :=
  LinearEquiv.ofBijective (stalkMapUFD D hD x hg0 hgord) (stalkMapUFD_bijective D hD x hg0 hgord)

/--
The defining property of `stalkEquivUFD`: its value on a stalk element `m` is the unique
element of `𝒪_{X,x}` whose image in the function field is `g` times the function-field
realization of `m`.
-/
lemma algebraMap_stalkEquivUFD_apply [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ)
    (hD : D.support ⊆ {x | coheight x = 1}) (x : X)
    [UniqueFactorizationMonoid (X.presheaf.stalk x)]
    {g : X.functionField} (hg0 : g ≠ 0)
    (hgord : ∀ z, coheight z = 1 → z ⤳ x → X.ord g z = D z)
    (m : ↑(TopCat.Presheaf.stalk D.sheaf.val.presheaf x)) :
    algebraMap (X.presheaf.stalk x) X.functionField (stalkEquivUFD D hD x hg0 hgord m) =
      g * D.stalkToFunctionFieldLinearMap x m := by
  set f := (LinearMap.mulLeft (X.presheaf.stalk x) g) ∘ₗ D.stalkToFunctionFieldLinearMap x
    with hf_def
  set a := Algebra.linearMap (X.presheaf.stalk x) X.functionField with ha_def
  have hinj : Function.Injective a := FaithfulSMul.algebraMap_injective _ _
  have range_eq : LinearMap.range f = LinearMap.range a :=
    (range_linearMap_eq_range_mulLeft_stalkToFunctionFieldLinearMap_of_ord_eq
      D hD x hg0 hgord).symm
  set e := Submodule.comap_equiv_self_of_inj_of_le (p := LinearMap.range f) hinj range_eq.le
    with he_def
  have h1 : stalkEquivUFD D hD x hg0 hgord m = ((e.symm (f.rangeRestrict m)) :
      ↑(X.presheaf.stalk x)) := by
    unfold stalkEquivUFD stalkMapUFD
    rfl
  have h2 : a ((e.symm (f.rangeRestrict m)) : ↑(X.presheaf.stalk x)) =
      ((f.rangeRestrict m) : X.functionField) := by
    have h3 := congrArg Subtype.val (e.apply_symm_apply (f.rangeRestrict m))
    rwa [he_def, Submodule.comap_equiv_self_of_inj_of_le_apply] at h3
  rw [h1]
  exact h2

end AlgebraicGeometry.AlgebraicCycle
