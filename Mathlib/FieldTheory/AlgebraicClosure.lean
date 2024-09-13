import Mathlib.FieldTheory.NormalClosure
import Mathlib.FieldTheory.Galois

/-!
# Algebraic Closure

In this file we construct the relative algebraic closure of a field extension.

## Main Definitions

- `algebraicClosure F E` is the relative algebraic closure (i.e. the maximal algebraic subextension)
  of the field extension `E / F`, which is defined to be the integral closure of `F` in `E`.

-/
noncomputable section

open Polynomial

section algebraicClosure

open FiniteDimensional IntermediateField Field

variable (F E : Type*) [Field F] [Field E] [Algebra F E]
variable {K : Type*} [Field K] [Algebra F K]

/--
The relative algebraic closure of `F` in `E`, or called maximal algebraic subextension
of `E / F`, is defined to be the integral closure of `F` in `E`.
The previous results prove that the integral closure is indeed an intermediate field.
This is the same as the intermediate field of `E / F` consisting of all integral/algebraic elements.
-/
def algebraicClosure
    : IntermediateField F E where
  toSubalgebra := _root_.integralClosure F E
  inv_mem' x hx := Subalgebra.inv_mem_of_algebraic (x := ⟨x, hx⟩)
    (isAlgebraic_iff_isIntegral.mpr hx)

variable {F E}
/-- An element is contained in the algebraic closure of `F` in `E` if and only if
it is an integral element. -/
theorem mem_algebraicClosure_iff' {x : E} :
    x ∈ algebraicClosure F E ↔ IsIntegral F x := Iff.rfl

/-- An element is contained in the algebraic closure of `F` in `E` if and only if
it is an algebraic element. -/
theorem mem_algebraicClosure_iff {x : E} :
    x ∈ algebraicClosure F E ↔ IsAlgebraic F x := isAlgebraic_iff_isIntegral.symm

/-- If `i` is an `F`-algebra homomorphism from `E` to `K`, then `i x` is contained in
`algebraicClosure F K` if and only if `x` is contained in `algebraicClosure F E`. -/
theorem map_mem_algebraicClosure_iff (i : E →ₐ[F] K) {x : E} :
    i x ∈ algebraicClosure F K ↔ x ∈ algebraicClosure F E := by
  simp_rw [mem_algebraicClosure_iff', ← minpoly.ne_zero_iff, minpoly.algHom_eq i i.injective]

namespace algebraicClosure
/-- If `i` is an `F`-algebra homomorphism from `E` to `K`, then the preimage of
`algebraicClosure F K` under the map `i` is equal to `algebraicClosure F E`. -/
theorem comap_eq_of_algHom (i : E →ₐ[F] K) :
    (algebraicClosure F K).comap i = algebraicClosure F E := by
  ext x
  exact map_mem_algebraicClosure_iff i

/-- If `i` is an `F`-algebra homomorphism from `E` to `K`, then the image of `algebraicClosure F E`
under the map `i` is contained in `algebraicClosure F K`. -/
theorem map_le_of_algHom (i : E →ₐ[F] K) :
    (algebraicClosure F E).map i ≤ algebraicClosure F K :=
  map_le_iff_le_comap.2 (comap_eq_of_algHom i).ge

variable (F) in
/-- If `K / E / F` is a field extension tower, such that `K / E` has no non-trivial algebraic
subextensions (this means that it is purely trancendental),
then the image of `algebraicClosure F E` in `K` is equal to `algebraicClosure F K`. -/
theorem map_eq_of_algebraicClosure_eq_bot [Algebra E K] [IsScalarTower F E K]
    (h : algebraicClosure E K = ⊥) :
    (algebraicClosure F E).map (IsScalarTower.toAlgHom F E K) = algebraicClosure F K := by
  refine le_antisymm (map_le_of_algHom _) (fun x hx ↦ ?_)
  obtain ⟨y, rfl⟩ := mem_bot.1 <| h ▸ mem_algebraicClosure_iff'.2
    (IsIntegral.tower_top <| mem_algebraicClosure_iff'.1 hx)
  exact ⟨y, (map_mem_algebraicClosure_iff <| IsScalarTower.toAlgHom F E K).mp hx, rfl⟩

/-- If `i` is an `F`-algebra isomorphism of `E` and `K`, then the image of `algebraicClosure F E`
under the map `i` is equal to `algebraicClosure F K`. -/
theorem map_eq_of_algEquiv (i : E ≃ₐ[F] K) :
    (algebraicClosure F E).map i = algebraicClosure F K :=
  (map_le_of_algHom i.toAlgHom).antisymm
    (fun x h ↦ ⟨_, (map_mem_algebraicClosure_iff i.symm).2 h, by simp⟩)

/-- If `E` and `K` are isomorphic as `F`-algebras, then `algebraicClosure F E` and
`algebraicClosure F K` are also isomorphic as `F`-algebras. -/
def algEquivOfAlgEquiv (i : E ≃ₐ[F] K) :
    algebraicClosure F E ≃ₐ[F] algebraicClosure F K :=
  (intermediateFieldMap i _).trans (equivOfEq (map_eq_of_algEquiv i))

alias AlgEquiv.algebraicClosure := algebraicClosure.algEquivOfAlgEquiv

variable (F E K)

/-- The algebraic closure of `F` in `E` is algebraic over `F`. -/
instance isAlgebraic : Algebra.IsAlgebraic F (algebraicClosure F E) :=
  ⟨fun x ↦
    isAlgebraic_iff.mpr (IsAlgebraic.isIntegral (mem_algebraicClosure_iff.mp x.2)).isAlgebraic⟩

/-- The algebraic closure of `F` in `E` is the integral closure of `F` in `E`. -/
instance isIntegralClosure : IsIntegralClosure (algebraicClosure F E) F E :=
  inferInstanceAs (IsIntegralClosure (integralClosure F E) F E)

end algebraicClosure

variable (F E K)

/-- An intermediate field of `E / F` is contained in the algebraic closure of `F` in `E`
if all of its elements are algebraic over `F`. -/
theorem le_algebraicClosure' {L : IntermediateField F E} (hs : ∀ x : L, IsAlgebraic F x) :
    L ≤ algebraicClosure F E := fun x h ↦ by
    simpa only [mem_algebraicClosure_iff, IsAlgebraic, ne_eq, ← aeval_algebraMap_eq_zero_iff E,
      Algebra.id.map_eq_id, RingHom.id_apply, IntermediateField.algebraMap_apply] using hs ⟨x, h⟩

/-- An intermediate field of `E / F` is contained in the algebraic closure of `F` in `E`
if it is algebraic over `F`. -/
theorem le_algebraicClosure (L : IntermediateField F E) [Algebra.IsAlgebraic F L] :
    L ≤ algebraicClosure F E := le_algebraicClosure' F E (Algebra.IsAlgebraic.isAlgebraic)

/-- An intermediate field of `E / F` is contained in the algebraic closure of `F` in `E`
if and only if it is algebraic over `F`. -/
theorem le_algebraicClosure_iff (L : IntermediateField F E) :
    L ≤ algebraicClosure F E ↔ Algebra.IsAlgebraic F L :=
  ⟨fun h ↦ ⟨fun x ↦ by simpa only [IsAlgebraic, ne_eq, ← aeval_algebraMap_eq_zero_iff E,
    IntermediateField.algebraMap_apply,
    Algebra.id.map_eq_id, RingHomCompTriple.comp_apply, mem_algebraicClosure_iff] using h x.2⟩,
    fun _ ↦ le_algebraicClosure _ _ _⟩

/-- The algebraic closure in `E` of the algebraic closure of `F` in `E` is equal to itself. -/
theorem algebraicClosure.algebraicClosure_eq_bot :
    algebraicClosure (algebraicClosure F E) E = ⊥ :=
  bot_unique fun x hx ↦ mem_bot.2
    ⟨⟨x, isIntegral_trans x (mem_algebraicClosure_iff'.1 hx)⟩, rfl⟩


/-- The normal closure in `E/F` of the algebraic closure of `F` in `E` is equal to itself. -/
theorem algebraicClosure.normalClosure_eq_self :
    normalClosure F (algebraicClosure F E) E = algebraicClosure F E :=
  le_antisymm (normalClosure_le_iff.2 fun i ↦
    haveI : Algebra.IsAlgebraic F i.fieldRange := (AlgEquiv.ofInjectiveField i).isAlgebraic
    le_algebraicClosure F E _) (le_normalClosure _)

/-- If `E` is normal over `F`, then the algebraic closure of `F` in `E` is Galois (i.e.
normal and algebraic) over `F`. -/
instance algebraicClosure.isGalois [Normal F E] : IsGalois F (algebraicClosure F E) where
  to_isAlgebraic := algebraicClosure.isAlgebraic F E
  to_normal := by
    rw [← algebraicClosure.normalClosure_eq_self]
    exact normalClosure.normal F _ E

/-- If `E / F` is a field extension and `E` is separably closed, then the algebraic closure
of `F` in `E` is equal to `F` if and only if `F` is separably closed. -/
theorem IsSepClosed.algebraicClosure_eq_bot_iff [IsSepClosed E] :
    algebraicClosure F E = ⊥ ↔ IsSepClosed F := by
  refine ⟨fun h ↦ IsSepClosed.of_exists_root _ fun p _ hirr hsep ↦ ?_,
    fun _ ↦ IntermediateField.eq_bot_of_isSepClosed_of_isAlgebraic _⟩
  obtain ⟨x, hx⟩ := IsSepClosed.exists_aeval_eq_zero E p (degree_pos_of_irreducible hirr).ne' hsep
  obtain ⟨x, rfl⟩ := h ▸ mem_algebraicClosure_iff.2 (hsep.of_dvd <| minpoly.dvd _ x hx)
  exact ⟨x, by simpa [Algebra.ofId_apply] using hx⟩

/-- If `E` is separably closed, then the algebraic closure of `F` in `E` is an absolute
algebraic closure of `F`. -/
instance algebraicClosure.isSepClosure [IsSepClosed E] : IsSepClosure F (algebraicClosure F E) :=
  ⟨(IsSepClosed.algebraicClosure_eq_bot_iff _ E).mp (algebraicClosure.algebraicClosure_eq_bot F E),
    isAlgebraic F E⟩

/-- If `K / E / F` is a field extension tower, such that `E / F` is algebraic, then
`algebraicClosure F K` is equal to `algebraicClosure E K`. -/
theorem algebraicClosure.eq_restrictScalars_of_isAlgebraic [Algebra E K] [IsScalarTower F E K]
    [Algebra.IsAlgebraic F E] : algebraicClosure F K = (algebraicClosure E K).restrictScalars F :=
  (algebraicClosure.le_restrictScalars F E K).antisymm fun _ h ↦
    IsAlgebraic.of_algebra_isAlgebraic_of_isAlgebraic F h

/-- If `K / E / F` is a field extension tower, then `E` adjoin `algebraicClosure F K` is contained
in `algebraicClosure E K`. -/
theorem algebraicClosure.adjoin_le [Algebra E K] [IsScalarTower F E K] :
    adjoin E (algebraicClosure F K) ≤ algebraicClosure E K :=
  adjoin_le_iff.2 <| le_restrictScalars F E K

/-- A compositum of two algebraic extensions is algebraic. -/
instance IntermediateField.isAlgebraic_sup (L1 L2 : IntermediateField F E)
    [h1 : Algebra.IsAlgebraic F L1] [h2 : Algebra.IsAlgebraic F L2] :
    Algebra.IsAlgebraic F (L1 ⊔ L2 : IntermediateField F E) := by
  rw [← le_algebraicClosure_iff] at h1 h2 ⊢
  exact sup_le h1 h2

/-- A compositum of algebraic extensions is algebraic. -/
instance IntermediateField.isAlgebraic_iSup {ι : Type*} {t : ι → IntermediateField F E}
    [h : ∀ i, Algebra.IsAlgebraic F (t i)] :
    Algebra.IsAlgebraic F (⨆ i, t i : IntermediateField F E) := by
  simp_rw [← le_algebraicClosure_iff] at h ⊢
  exact iSup_le h

end algebraicClosure
