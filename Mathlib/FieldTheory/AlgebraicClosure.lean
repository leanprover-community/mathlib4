/-
Copyright (c) 2024 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Jiedong Jiang
-/
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic

/-!
# Relative Algebraic Closure

In this file we construct the relative algebraic closure of a field extension.

## Main Definitions

- `algebraicClosure F E` is the relative algebraic closure (i.e. the maximal algebraic subextension)
  of the field extension `E / F`, which is defined to be the integral closure of `F` in `E`.

-/
noncomputable section

open Polynomial FiniteDimensional IntermediateField Field

variable (F E : Type*) [Field F] [Field E] [Algebra F E]
variable {K : Type*} [Field K] [Algebra F K]

/--
The *relative algebraic closure* of a field `F` in a field extension `E`,
also called the *maximal algebraic subextension* of `E / F`,
is defined to be the subalgebra `integralClosure F E`
upgraded to an intermediate field (since `F` and `E` are both fields).
This is exactly the intermediate field of `E / F` consisting of all integral/algebraic elements.
-/
@[stacks 09GI]
def algebraicClosure : IntermediateField F E :=
  Algebra.IsAlgebraic.toIntermediateField (integralClosure F E)

variable {F E}

theorem algebraicClosure_toSubalgebra :
  (algebraicClosure F E).toSubalgebra = integralClosure F E := rfl

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
subextensions (this means that it is purely transcendental),
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

alias _root_.AlgEquiv.algebraicClosure := algEquivOfAlgEquiv

variable (F E K)

/-- The algebraic closure of `F` in `E` is algebraic over `F`. -/
instance isAlgebraic : Algebra.IsAlgebraic F (algebraicClosure F E) :=
  ⟨fun x ↦ isAlgebraic_iff.mpr x.2.isAlgebraic⟩

/-- The algebraic closure of `F` in `E` is the integral closure of `F` in `E`. -/
instance isIntegralClosure : IsIntegralClosure (algebraicClosure F E) F E :=
  inferInstanceAs (IsIntegralClosure (integralClosure F E) F E)

end algebraicClosure

protected theorem Transcendental.algebraicClosure {a : E} (ha : Transcendental F a) :
    Transcendental (algebraicClosure F E) a :=
  ha.extendScalars _

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

namespace algebraicClosure

/-- The algebraic closure in `E` of the algebraic closure of `F` in `E` is equal to itself. -/
theorem algebraicClosure_eq_bot :
    algebraicClosure (algebraicClosure F E) E = ⊥ :=
  bot_unique fun x hx ↦ mem_bot.2
    ⟨⟨x, isIntegral_trans x (mem_algebraicClosure_iff'.1 hx)⟩, rfl⟩

/-- The normal closure in `E/F` of the algebraic closure of `F` in `E` is equal to itself. -/
theorem normalClosure_eq_self :
    normalClosure F (algebraicClosure F E) E = algebraicClosure F E :=
  le_antisymm (normalClosure_le_iff.2 fun i ↦
    haveI : Algebra.IsAlgebraic F i.fieldRange := (AlgEquiv.ofInjectiveField i).isAlgebraic
    le_algebraicClosure F E _) (le_normalClosure _)

end algebraicClosure

/-- If `E / F` is a field extension and `E` is algebraically closed, then the algebraic closure
of `F` in `E` is equal to `F` if and only if `F` is algebraically closed. -/
theorem IsAlgClosed.algebraicClosure_eq_bot_iff [IsAlgClosed E] :
    algebraicClosure F E = ⊥ ↔ IsAlgClosed F := by
  refine ⟨fun h ↦ IsAlgClosed.of_exists_root _ fun p hmon hirr ↦ ?_,
    fun _ ↦ IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _⟩
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero E p (degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, rfl⟩ := h ▸ mem_algebraicClosure_iff'.2 (minpoly.ne_zero_iff.1 <|
    ne_zero_of_dvd_ne_zero hmon.ne_zero (minpoly.dvd _ x hx))
  exact ⟨x, by simpa [Algebra.ofId_apply] using hx⟩

/-- `F(S) / F` is a algebraic extension if and only if all elements of `S` are
algebraic elements. -/
theorem IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic {S : Set E} :
    Algebra.IsAlgebraic F (adjoin F S) ↔ ∀ x ∈ S, IsAlgebraic F x :=
  ((le_algebraicClosure_iff F E _).symm.trans (adjoin_le_iff.trans <| forall_congr' <|
    fun _ => Iff.imp Iff.rfl mem_algebraicClosure_iff))

namespace algebraicClosure

/-- If `E` is algebraically closed, then the algebraic closure of `F` in `E` is an absolute
algebraic closure of `F`. -/
instance isAlgClosure [IsAlgClosed E] : IsAlgClosure F (algebraicClosure F E) :=
  ⟨(IsAlgClosed.algebraicClosure_eq_bot_iff _ E).mp (algebraicClosure_eq_bot F E),
    isAlgebraic F E⟩

/-- The algebraic closure of `F` in `E` is equal to `E` if and only if `E / F` is
algebraic. -/
theorem eq_top_iff : algebraicClosure F E = ⊤ ↔ Algebra.IsAlgebraic F E :=
  ⟨fun h ↦ ⟨fun _ ↦ mem_algebraicClosure_iff.1 (h ▸ mem_top)⟩,
    fun _ ↦ top_unique fun x _ ↦ mem_algebraicClosure_iff.2 (Algebra.IsAlgebraic.isAlgebraic x)⟩

/-- If `K / E / F` is a field extension tower, then `algebraicClosure F K` is contained in
`algebraicClosure E K`. -/
theorem le_restrictScalars [Algebra E K] [IsScalarTower F E K] :
    algebraicClosure F K ≤ (algebraicClosure E K).restrictScalars F :=
  fun _ h ↦ mem_algebraicClosure_iff.2 <| IsAlgebraic.tower_top E (mem_algebraicClosure_iff.1 h)

/-- If `K / E / F` is a field extension tower, such that `E / F` is algebraic, then
`algebraicClosure F K` is equal to `algebraicClosure E K`. -/
theorem eq_restrictScalars_of_isAlgebraic [Algebra E K] [IsScalarTower F E K]
    [Algebra.IsAlgebraic F E] : algebraicClosure F K = (algebraicClosure E K).restrictScalars F :=
  (algebraicClosure.le_restrictScalars F E K).antisymm fun _ h ↦
    isIntegral_trans _ h

/-- If `K / E / F` is a field extension tower, then `E` adjoin `algebraicClosure F K` is contained
in `algebraicClosure E K`. -/
theorem adjoin_le [Algebra E K] [IsScalarTower F E K] :
    adjoin E (algebraicClosure F K) ≤ algebraicClosure E K :=
  adjoin_le_iff.2 <| le_restrictScalars F E K

end algebraicClosure

variable {F}
/--
Let `E / F` be a field extension. If a polynomial `p`
splits in `E`, then it splits in the relative algebraic closure of `F` in `E` already.
-/
theorem Splits.algebraicClosure {p : F[X]} (h : p.Splits (algebraMap F E)) :
    p.Splits (algebraMap F (algebraicClosure F E)) :=
  splits_of_splits h fun _ hx ↦ (isAlgebraic_of_mem_rootSet hx).isIntegral
