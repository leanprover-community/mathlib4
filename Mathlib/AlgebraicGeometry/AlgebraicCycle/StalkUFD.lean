import Mathlib.AlgebraicGeometry.AlgebraicCycle.Sheaf
import Mathlib.RingTheory.UniqueFactorizationDomain.Hartogs
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# The stalk of `𝒪ₓ(D)` at a point with factorial local ring

This file computes stalks of the divisorial sheaf `𝒪ₓ(D)` at points `x` of arbitrary
codimension whose local ring is a UFD. The codimension-one computation `stalkEquiv` (where the
stalk is a DVR and the local equation is a power of a uniformizer) is derived at the end of the
file as a special case.

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
- `stalkEquiv`, `algebraMap_stalkEquiv_apply`: the specialization to a codimension-one point,
  where the local equation is `ϖ ^ D x` for a uniformizer `ϖ`.

Auxiliary API: `isPrime_map_of_le`/`comap_map_of_le`/`height_map_of_le` (primes below `𝔭`
extend to primes of the localization at `𝔭`, preserving height; TODO upstream),
`height_primeIdealOf`/`primeIdealOf_le_primeIdealOf_iff` (the prime attached to a point of an
affine chart remembers its coheight and the specialization order), and arithmetic of the order
of vanishing (`ord_one`, `ord_inv`, `ord_zpow`, `ord_prod`).
-/

open AlgebraicGeometry Scheme CategoryTheory Order Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicCycle

section LocalizationAtPrime

/-!
### Extensions of primes to a localization at a prime

Primes contained in `𝔭` correspond to primes of the localization at `𝔭`; we record the
resulting API for the extension `𝔮 ↦ 𝔮.map (algebraMap R A)`.

TODO: upstream to `Mathlib.RingTheory.Localization.Ideal`.
-/

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- If the image of `r` in a localization of `R` lies in the extension of an ideal `I`,
then `r * t ∈ I` for some `t` in the localizing submonoid. -/
lemma exists_mul_mem_of_algebraMap_mem_map (M : Submonoid R) [IsLocalization M A]
    {I : Ideal R} {r : R} (h : algebraMap R A r ∈ I.map (algebraMap R A)) :
    ∃ t ∈ M, r * t ∈ I := by
  obtain ⟨⟨⟨v, hv⟩, ⟨t, ht⟩⟩, hvt⟩ := (IsLocalization.mem_map_algebraMap_iff M A).mp h
  have hvt' : algebraMap R A (r * t) = algebraMap R A v := by
    rw [map_mul]; exact hvt
  obtain ⟨⟨c, hc⟩, hcc⟩ := (IsLocalization.eq_iff_exists (M := M) (S := A)).mp hvt' 
  refine ⟨t * c, mul_mem ht hc, ?_⟩
  have hrtc : r * (t * c) = v * c := by
    rw [show r * (t * c) = c * (r * t) by ring, hcc]
    ring
  rw [hrtc]
  exact I.mul_mem_right c hv

variable (A) {𝔭 : Ideal R} [𝔭.IsPrime] [IsLocalization.AtPrime A 𝔭] {𝔮 : Ideal R} [𝔮.IsPrime]

omit [𝔮.IsPrime] in
lemma disjoint_primeCompl_of_le (h : 𝔮 ≤ 𝔭) :
    Disjoint (𝔭.primeCompl : Set R) (𝔮 : Set R) :=
  Set.disjoint_left.mpr fun _ ht ht' => ht (h ht')

/-- The extension of a prime `𝔮 ≤ 𝔭` to the localization at `𝔭` is prime. -/
lemma isPrime_map_of_le (h : 𝔮 ≤ 𝔭) : (𝔮.map (algebraMap R A)).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint 𝔭.primeCompl A 𝔮 inferInstance
    (disjoint_primeCompl_of_le h)

/-- A prime `𝔮 ≤ 𝔭` is recovered from its extension to the localization at `𝔭`. -/
lemma comap_map_of_le (h : 𝔮 ≤ 𝔭) :
    ((𝔮.map (algebraMap R A)).comap (algebraMap R A) : Ideal R) = 𝔮 :=
  IsLocalization.under_map_of_isPrime_disjoint 𝔭.primeCompl A inferInstance
    (disjoint_primeCompl_of_le h)

/-- Extending a prime `𝔮 ≤ 𝔭` to the localization at `𝔭` preserves its height. -/
lemma height_map_of_le (h : 𝔮 ≤ 𝔭) : (𝔮.map (algebraMap R A)).height = 𝔮.height := by
  haveI := isPrime_map_of_le A h
  have h1 := IsLocalization.height_under 𝔭.primeCompl (𝔮.map (algebraMap R A))
  have h2 : (Ideal.under R (𝔮.map (algebraMap R A)) : Ideal R) = 𝔮 := comap_map_of_le A h
  rw [h2] at h1
  exact h1.symm

end LocalizationAtPrime

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

section ChartPrimes

/-!
### Prime ideals attached to points of an affine chart

For an affine open `U` and a point `w : U`, the stalk at `w` is the localization of `Γ(X, U)`
at `hU.primeIdealOf w`; we record that this prime remembers the coheight of `w` and the
specialization order.
-/

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- The height of the prime ideal attached to a point of an affine open is the coheight of
the point: both compute the Krull dimension of the local ring. -/
lemma height_primeIdealOf {U : X.Opens} (hU : IsAffineOpen U) (w : U) :
    (hU.primeIdealOf w).asIdeal.height = coheight (w : X) := by
  haveI : Nonempty U := ⟨w⟩
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf w
  haveI := hU.isLocalization_stalk w
  have h1 : ringKrullDim (X.presheaf.stalk (w : X)) = (hU.primeIdealOf w).asIdeal.height :=
    IsLocalization.AtPrime.ringKrullDim_eq_height _ _
  have h2 := ringKrullDim_stalk_eq_coheight (w : X)
  rw [h1] at h2
  exact_mod_cast h2

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- Specialization of points of an affine chart corresponds to inclusion of the attached
prime ideals. -/
lemma primeIdealOf_le_primeIdealOf_iff {U : X.Opens} (hU : IsAffineOpen U) (w x : U) :
    (hU.primeIdealOf w).asIdeal ≤ (hU.primeIdealOf x).asIdeal ↔ (w : X) ⤳ (x : X) := by
  constructor
  · intro h
    have := ((PrimeSpectrum.le_iff_specializes _ _).mp h).map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at this
  · intro h
    refine (PrimeSpectrum.le_iff_specializes _ _).mpr
      (hU.fromSpec.isOpenEmbedding.toIsEmbedding.toIsInducing.specializes_iff.mp ?_)
    rw [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf]
    exact h

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- Distinct points of an affine chart have distinct attached prime ideals. -/
lemma primeIdealOf_injective {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Injective hU.primeIdealOf := fun w x h => by
  have h1 := hU.fromSpec_primeIdealOf w
  rw [h, hU.fromSpec_primeIdealOf] at h1
  exact Subtype.ext h1.symm

end ChartPrimes

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
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]
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
  have hzx : z ⤳ x :=
    (primeIdealOf_le_primeIdealOf_iff hU ⟨z, hzU⟩ ⟨x, hxU⟩).mp (by rw [hround]; exact hle)
  -- `coheight z = 1`: the prime of `z` in the chart is `𝔮`, of height `ht (ϖ) = 1`.
  have hcoh : coheight z = 1 := by
    have h0 := height_primeIdealOf hU ⟨z, hzU⟩
    rw [hround,
      show 𝔮.asIdeal.height = (Ideal.span {ϖ}).height from
        IsLocalization.height_under (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl _,
      Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero) hϖ.not_unit] at h0
    exact h0.symm
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

omit [IsLocallyNoetherian X] in
/-- The image of a germ in the function field does not depend on the point at which the germ
is taken. -/
lemma algebraMap_germ_eq_algebraMap_germ {W : X.Opens} {x z : X} (hxW : x ∈ W) (hzW : z ∈ W)
    (s : Γ(X, W)) :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W x hxW s) =
      algebraMap (X.presheaf.stalk z) X.functionField (X.presheaf.germ W z hzW s) := by
  haveI : Nonempty W := ⟨⟨x, hxW⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField hxW,
    Scheme.algebraMap_germ_eq_germToFunctionField hzW]

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
    have hzW : z ∈ W := hzx.mem_open W.2 hxW
    exact (mem_range_algebraMap_iff_ord_nonneg hz _).mp
      ⟨X.presheaf.germ W z hzW s, (algebraMap_germ_eq_algebraMap_germ hxW hzW s).symm⟩ hne
  · -- Conversely, apply Hartogs for UFDs: each prime `ϖ` of the stalk has a corresponding
    -- codimension-one point `z ⤳ x` where the order bound gives a `ϖ`-integral representation.
    intro h
    rcases eq_or_ne f 0 with rfl | hne
    · exact ⟨0, map_zero _⟩
    refine UniqueFactorizationMonoid.hartogs fun ϖ hϖ => ?_
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

/-- The image in the function field of `u * ϖ ^ n`, for `u` a unit and `ϖ` irreducible in the
local ring at a codimension-one point, has order of vanishing `n`. -/
lemma ord_algebraMap_unit_mul_pow [IsRegularInCodimensionOne X] {z : X}
    (hz : coheight z = 1) {ϖ : X.presheaf.stalk z} (hϖ : Irreducible ϖ)
    (u : (X.presheaf.stalk z)ˣ) (n : ℕ) :
    X.ord (algebraMap (X.presheaf.stalk z) X.functionField ((u : X.presheaf.stalk z) * ϖ ^ n))
      z = n := by
  have hne1 : algebraMap (X.presheaf.stalk z) X.functionField (u : X.presheaf.stalk z) ≠ 0 :=
    algebraMap_functionField_ne_zero u.isUnit.ne_zero
  have hne2 : (algebraMap (X.presheaf.stalk z) X.functionField ϖ) ^ n ≠ 0 :=
    pow_ne_zero n (algebraMap_functionField_ne_zero hϖ.ne_zero)
  rw [map_mul, map_pow, X.ord_mul hz hne1 hne2, ord_algebraMap_eq_zero_of_isUnit hz u.isUnit,
    ← zpow_natCast (algebraMap (X.presheaf.stalk z) X.functionField ϖ) n,
    ord_zpow_algebraMap_irreducible hz hϖ (n : ℤ), zero_add]

section SectionOrd

/-!
### Orders of vanishing of sections of a chart

For a section `r : Γ(X, U)` with nonzero image in the function field, membership of `r` in the
prime attached to a codimension-one point `w` of the chart measures whether (the image of) `r`
vanishes at `w`. Stating these at subtype points `w : U` lets the ambient
`algebra_section_stalk` instances apply.
-/

variable {U : X.Opens} [Nonempty U]

omit [IsLocallyNoetherian X] in
/-- A section with nonzero image in the function field has nonzero germs. -/
lemma algebraMap_section_stalk_ne_zero (w : U) {r : Γ(X, U)}
    (hr : algebraMap Γ(X, U) X.functionField r ≠ 0) :
    algebraMap Γ(X, U) (X.presheaf.stalk (w : X)) r ≠ 0 := fun h0 =>
  hr (by rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk (w : X)) X.functionField,
    h0, map_zero])

/-- Sections have nonnegative order of vanishing at every codimension-one point of the chart. -/
lemma ord_algebraMap_section_nonneg [IsRegularInCodimensionOne X] (w : U)
    (hw : coheight (w : X) = 1) {r : Γ(X, U)}
    (hr : algebraMap Γ(X, U) X.functionField r ≠ 0) :
    0 ≤ X.ord (algebraMap Γ(X, U) X.functionField r) (w : X) := by
  rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk (w : X)) X.functionField]
  exact ord_algebraMap_nonneg hw (algebraMap_section_stalk_ne_zero w hr)

/-- A section vanishes at a codimension-one point of an affine chart if and only if it lies
in the attached prime ideal. -/
lemma one_le_ord_algebraMap_section_iff [IsRegularInCodimensionOne X] (hU : IsAffineOpen U)
    (w : U) (hw : coheight (w : X) = 1) {r : Γ(X, U)}
    (hr : algebraMap Γ(X, U) X.functionField r ≠ 0) :
    1 ≤ X.ord (algebraMap Γ(X, U) X.functionField r) (w : X) ↔
      r ∈ (hU.primeIdealOf w).asIdeal := by
  haveI := hU.isLocalization_stalk w
  rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk (w : X)) X.functionField,
    ← mem_maximalIdeal_iff_one_le_ord hw (algebraMap_section_stalk_ne_zero w hr)]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff _ (hU.primeIdealOf w).asIdeal r

/-- A section not in the prime attached to a codimension-one point of an affine chart has
order of vanishing zero there. -/
lemma ord_algebraMap_section_eq_zero_of_notMem [IsRegularInCodimensionOne X]
    (hU : IsAffineOpen U) (w : U) (hw : coheight (w : X) = 1) {r : Γ(X, U)}
    (hr : algebraMap Γ(X, U) X.functionField r ≠ 0)
    (hmem : r ∉ (hU.primeIdealOf w).asIdeal) :
    X.ord (algebraMap Γ(X, U) X.functionField r) (w : X) = 0 := by
  have h1 := ord_algebraMap_section_nonneg w hw hr
  have h2 : ¬ 1 ≤ X.ord (algebraMap Γ(X, U) X.functionField r) (w : X) := fun h =>
    hmem ((one_le_ord_algebraMap_section_iff hU w hw hr).mp h)
  omega

end SectionOrd

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
  -- `ϖ` is a generator of the extension of the chart prime of `z` to the stalk at `x`,
  -- which is a height-one prime.
  have hzU : z ∈ U := hzx.mem_open U.2 hxU
  have hlez := (primeIdealOf_le_primeIdealOf_iff hU ⟨z, hzU⟩ ⟨x, hxU⟩).mpr hzx
  haveI := isPrime_map_of_le (X.presheaf.stalk x) hlez
  have hcomapz := comap_map_of_le (X.presheaf.stalk x) hlez
  have hhtz : ((hU.primeIdealOf ⟨z, hzU⟩).asIdeal.map
      (algebraMap Γ(X, U) (X.presheaf.stalk x))).height = 1 := by
    rw [height_map_of_le (X.presheaf.stalk x) hlez, height_primeIdealOf hU ⟨z, hzU⟩]
    exact hz
  obtain ⟨ϖ, hϖ, hq⟩ := Ideal.exists_prime_span_of_height_eq_one hhtz
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
    exact Ideal.mem_comap.mpr (by rw [hq]; exact Ideal.mem_span_singleton.mpr ⟨_, hrs.symm⟩)
  -- At every codimension-one `w ⤳ x`, `ord ϖ = ord r` since `s` is a unit near `x`.
  have hordEq : ∀ w, coheight w = 1 → w ⤳ x →
      X.ord (algebraMap (X.presheaf.stalk x) X.functionField ϖ) w =
      X.ord (algebraMap Γ(X, U) X.functionField r) w := by
    intro w hw hwx
    have hwU : w ∈ U := hwx.mem_open U.2 hxU
    have hs0 : X.ord (algebraMap Γ(X, U) X.functionField (s : Γ(X, U))) w = 0 :=
      ord_algebraMap_section_eq_zero_of_notMem hU ⟨w, hwU⟩ hw hsK fun hmem =>
        s.2 ((primeIdealOf_le_primeIdealOf_iff hU ⟨w, hwU⟩ ⟨x, hxU⟩).mpr hwx hmem)
    have hmul := X.ord_mul hw hϖK hsK
    rw [hK, hs0] at hmul
    omega
  refine ⟨ϖ, hϖ, ?_, ?_⟩
  · -- At `z` the order is exactly one: at least one since `r ∈ 𝔮z`, and at most one since
    -- `r ∈ 𝔮z²` would descend to a factorization contradicting the primality of `ϖ`.
    rw [hordEq z hz hzx]
    have hn1 : 1 ≤ X.ord (algebraMap Γ(X, U) X.functionField r) z :=
      (one_le_ord_algebraMap_section_iff hU ⟨z, hzU⟩ hz hrK).mpr hr𝔮z
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨z, hzU⟩ : U)
    haveI hLocz := hU.isLocalization_stalk ⟨z, hzU⟩
    haveI := functionField_isScalarTower X U (⟨z, hzU⟩ : U)
    haveI : IsDiscreteValuationRing (X.presheaf.stalk z) :=
      IsRegularInCodimensionOne.stalk_dvr z hz
    -- Factor the image of `r` in the DVR at `z` as a unit times a power of a uniformizer.
    have hrZ0 : algebraMap Γ(X, U) (X.presheaf.stalk z) r ≠ 0 :=
      algebraMap_section_stalk_ne_zero (⟨z, hzU⟩ : U) hrK
    obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk z)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hrZ0 hϖ'
    have hordr : X.ord (algebraMap Γ(X, U) X.functionField r) z = n := by
      rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk z) X.functionField, hu]
      exact ord_algebraMap_unit_mul_pow hz hϖ' u n
    rw [hordr] at hn1 ⊢
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
      obtain ⟨t, ht, hrt⟩ := exists_mul_mem_of_algebraMap_mem_map
        (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl hmem2
      -- Push into the stalk at `x`: `ϖ²` divides `ϖ * s * t` with `s` a unit and `ϖ ∤ t`.
      have hdvd2 : ϖ ^ 2 ∣ algebraMap Γ(X, U) (X.presheaf.stalk x) (r * t) := by
        rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow, ← hq, ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hrt
      obtain ⟨d, hd⟩ := hdvd2
      have hst : algebraMap Γ(X, U) (X.presheaf.stalk x) (s : Γ(X, U)) *
          algebraMap Γ(X, U) (X.presheaf.stalk x) t = ϖ * d := by
        apply mul_left_cancel₀ hϖ.ne_zero
        calc ϖ * (algebraMap Γ(X, U) (X.presheaf.stalk x) (s : Γ(X, U)) *
              algebraMap Γ(X, U) (X.presheaf.stalk x) t)
            = (ϖ * algebraMap Γ(X, U) (X.presheaf.stalk x) (s : Γ(X, U))) *
              algebraMap Γ(X, U) (X.presheaf.stalk x) t := by ring
          _ = algebraMap Γ(X, U) (X.presheaf.stalk x) (r * t) := by
              rw [map_mul, hrs]
          _ = ϖ ^ 2 * d := hd
          _ = ϖ * (ϖ * d) := by ring
      rcases hϖ.2.2 _ _ ⟨d, hst⟩ with hdvd | hdvd
      · exact hϖ.not_unit (isUnit_of_dvd_unit hdvd hsA)
      · exact ht (by
          rw [← hcomapz]
          exact Ideal.mem_comap.mpr (by rw [hq]; exact Ideal.mem_span_singleton.mpr hdvd))
    omega
  · -- At `z' ≠ z` the order vanishes: a positive order would put `ϖ` in the height-one prime
    -- of `z'`, forcing the primes (hence the points) to coincide.
    intro z' hz' hz'x hne
    have hz'U : z' ∈ U := hz'x.mem_open U.2 hxU
    have hlez' := (primeIdealOf_le_primeIdealOf_iff hU ⟨z', hz'U⟩ ⟨x, hxU⟩).mpr hz'x
    haveI hprimez' := isPrime_map_of_le (X.presheaf.stalk x) hlez'
    rw [hordEq z' hz' hz'x]
    have hnonneg : 0 ≤ X.ord (algebraMap Γ(X, U) X.functionField r) z' :=
      ord_algebraMap_section_nonneg (⟨z', hz'U⟩ : U) hz' hrK
    by_contra hne0
    have h1 : 1 ≤ X.ord (algebraMap Γ(X, U) X.functionField r) z' := by omega
    have hr𝔮z' := (one_le_ord_algebraMap_section_iff hU ⟨z', hz'U⟩ hz' hrK).mp h1
    -- `ϖ ∈ q'` since `ϖ * (unit) = image of r`, so `q' = (ϖ)` by comparing heights.
    have hϖq' : ϖ ∈ (hU.primeIdealOf ⟨z', hz'U⟩).asIdeal.map
        (algebraMap Γ(X, U) (X.presheaf.stalk x)) := by
      have hrq' := Ideal.mem_map_of_mem (algebraMap Γ(X, U) (X.presheaf.stalk x)) hr𝔮z'
      rw [← hrs] at hrq'
      exact (hprimez'.mem_or_mem hrq').resolve_right fun h =>
        hprimez'.ne_top (Ideal.eq_top_of_isUnit_mem _ h hsA)
    have hhtz' : ((hU.primeIdealOf ⟨z', hz'U⟩).asIdeal.map
        (algebraMap Γ(X, U) (X.presheaf.stalk x))).height = 1 := by
      rw [height_map_of_le (X.presheaf.stalk x) hlez', height_primeIdealOf hU ⟨z', hz'U⟩]
      exact hz'
    refine hne (congrArg Subtype.val (show (⟨z', hz'U⟩ : U) = ⟨z, hzU⟩ from
      primeIdealOf_injective hU (PrimeSpectrum.ext ?_)))
    rw [← comap_map_of_le (X.presheaf.stalk x) hlez', ← hcomapz,
      Ideal.eq_span_singleton_of_height_eq_one hhtz' hϖq' hϖ, hq]

/-- The order of vanishing of `1` is zero. -/
@[simp]
lemma ord_one {z : X} : X.ord 1 z = 0 := by
  by_cases hz : coheight z = 1
  · have h := X.ord_mul hz (one_ne_zero (α := X.functionField)) one_ne_zero
    rw [mul_one] at h
    omega
  · exact X.ord_eq_zero_of_coheight_neq_one hz 1

/-- The order of vanishing of an inverse is the negative of the order. -/
lemma ord_inv {z : X} (hz : coheight z = 1) {f : X.functionField} (hf : f ≠ 0) :
    X.ord f⁻¹ z = - X.ord f z := by
  have h := X.ord_mul hz hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, ord_one] at h
  omega

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
  | empty => simp
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
    rw [coe_stalkToFunctionFieldLinearMap]
    exact range_stalkToFunctionField D hD x
  rw [range_eq]
  ext w
  simp only [Set.mem_range, Algebra.linearMap_apply, Set.mem_image, Set.mem_setOf_eq,
    LinearMap.mulLeft_apply]
  have hHar := mem_range_algebraMap_stalk_iff_forall_ord_nonneg (X := X) (x := x) w
  -- The order of `g⁻¹` at every relevant point is `- D z`.
  have hginv : ∀ z, coheight z = 1 → z ⤳ x → X.ord g⁻¹ z = - D z := fun z hz hzx => by
    rw [ord_inv hz hg0, hgord z hz hzx]
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

/-!
At a codimension-one point `x` the stalk is a discrete valuation ring — in particular a UFD —
and `ϖ ^ D x` is already a local equation for `D` at `x`, since the only codimension-one point
specializing to `x` is `x` itself. The classical stalk computation is therefore a special case
of `stalkEquivUFD`.
-/

/-- At a codimension-one point `x`, `ϖ ^ D x` is a local equation for `D` at `x`. -/
lemma ord_zpow_algebraMap_irreducible_of_specializes [IsRegularInCodimensionOne X]
    (D : AlgebraicCycle X ℤ) (x : X) (hx : coheight x = 1)
    {ϖ : X.presheaf.stalk x} (hϖ : Irreducible ϖ) :
    ∀ z, coheight z = 1 → z ⤳ x →
      X.ord ((algebraMap (X.presheaf.stalk x) X.functionField ϖ) ^ (D x)) z = D z :=
  fun z hz hzx => by
    rw [hzx.eq_of_coheight_eq_one hz hx]
    exact ord_zpow_algebraMap_irreducible hx hϖ (D x)

/--
The stalk of `𝒪ₓ(D)` at a codimension-one point `x` is isomorphic to `𝒪_{X,x}` as an
`𝒪_{X,x}`-module, via multiplication by `ϖ ^ D x` for a uniformizer `ϖ` of the DVR `𝒪_{X,x}`.
This is the special case of `stalkEquivUFD` where the local equation is a power of a single
uniformizer.
-/
noncomputable def stalkEquiv [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ)
    (hD : D.support ⊆ {x | coheight x = 1})
    (x : X) (hx : coheight x = 1)
    (ϖ : X.presheaf.stalk x) (hϖ : Irreducible ϖ) :
    ↑(TopCat.Presheaf.stalk D.sheaf.val.presheaf x) ≃ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x :=
  haveI : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    IsRegularInCodimensionOne.stalk_dvr x hx
  stalkEquivUFD D hD x
    (zpow_ne_zero (D x) (algebraMap_functionField_ne_zero hϖ.ne_zero))
    (ord_zpow_algebraMap_irreducible_of_specializes D x hx hϖ)

/--
The defining property of `stalkEquiv`: its value on a stalk element `m` is the unique element
of the structure sheaf stalk whose image in the function field is `ϖ ^ D x` times the
function-field realization of `m`.
-/
lemma algebraMap_stalkEquiv_apply [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ)
    (hD : D.support ⊆ {x | coheight x = 1})
    (x : X) (hx : coheight x = 1)
    (ϖ : X.presheaf.stalk x) (hϖ : Irreducible ϖ)
    (m : ↑(TopCat.Presheaf.stalk D.sheaf.val.presheaf x)) :
    algebraMap (X.presheaf.stalk x) X.functionField (stalkEquiv D hD x hx ϖ hϖ m) =
      (algebraMap (X.presheaf.stalk x) X.functionField ϖ) ^ (D x) *
        D.stalkToFunctionFieldLinearMap x m := by
  haveI : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    IsRegularInCodimensionOne.stalk_dvr x hx
  exact algebraMap_stalkEquivUFD_apply D hD x
    (zpow_ne_zero (D x) (algebraMap_functionField_ne_zero hϖ.ne_zero))
    (ord_zpow_algebraMap_irreducible_of_specializes D x hx hϖ) m

end AlgebraicGeometry.AlgebraicCycle
