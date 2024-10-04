/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.Algebraic
import Mathlib.FieldTheory.Tower
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Results on finite dimensionality and algebraicity of intermediate fields.
-/

open Module

variable {K L N: Type*} [Field K] [Field L] [Field N] [Algebra K L] [Algebra K N]
  {S : IntermediateField K L}

theorem IntermediateField.coe_isIntegral_iff {R : Type*} [CommRing R] [Algebra R K] [Algebra R L]
    [IsScalarTower R K L] {x : S} : IsIntegral R (x : L) ↔ IsIntegral R x :=
  isIntegral_algHom_iff (S.val.restrictScalars R) Subtype.val_injective

/-- Turn an algebraic subalgebra into an intermediate field, `Subalgebra.IsAlgebraic` version. -/
def Subalgebra.IsAlgebraic.toIntermediateField {S : Subalgebra K L} (hS : S.IsAlgebraic) :
    IntermediateField K L where
  toSubalgebra := S
  inv_mem' x hx := Algebra.adjoin_le_iff.mpr
    (Set.singleton_subset_iff.mpr hx) (hS x hx).isIntegral.inv_mem_adjoin

/-- Turn an algebraic subalgebra into an intermediate field, `Algebra.IsAlgebraic` version. -/
abbrev Algebra.IsAlgebraic.toIntermediateField (S : Subalgebra K L) [Algebra.IsAlgebraic K S] :
    IntermediateField K L := (S.isAlgebraic_iff.mpr ‹_›).toIntermediateField

/-- The relative algebraic closure of a field `K` in an extension `L`, or called maximal algebraic subextension
of `L / K`, is defined to be the subalgebra `integralClosure K L`
upgraded to an intermediate field (when `K` and `L` are both fields). -/
def algebraicClosure : IntermediateField K L :=
  Algebra.IsAlgebraic.toIntermediateField (integralClosure K L)

variable {K L}
/-- An element is contained in the algebraic closure of `K` in `L` if and only if
it is an integral element. -/
theorem mem_algebraicClosure_iff' {x : L} :
    x ∈ algebraicClosure K L ↔ IsIntegral K x := Iff.rfl

/-- An element is contained in the algebraic closure of `K` in `L` if and only if
it is an algebraic element. -/
theorem mem_algebraicClosure_iff {x : L} :
    x ∈ algebraicClosure K L ↔ IsAlgebraic K x := isAlgebraic_iff_isIntegral.symm

/-- If `i` is an `K`-algebra homomorphism from `L` to `N`, then `i x` is contained in
`algebraicClosure K N` if and only if `x` is contained in `algebraicClosure K L`. -/
theorem map_mem_algebraicClosure_iff (i : L →ₐ[K] N) {x : L} :
    i x ∈ algebraicClosure K N ↔ x ∈ algebraicClosure K L := by
  simp_rw [mem_algebraicClosure_iff', ← minpoly.ne_zero_iff, minpoly.algHom_eq i i.injective]

namespace algebraicClosure
/-- If `i` is an `K`-algebra homomorphism from `L` to `N`, then the preimage of
`algebraicClosure K N` under the map `i` is equal to `algebraicClosure K L`. -/
theorem comap_eq_of_algHom (i : L →ₐ[K] N) :
    (algebraicClosure K N).comap i = algebraicClosure K L := by
  ext x
  exact map_mem_algebraicClosure_iff i

/-- If `i` is an `K`-algebra homomorphism from `L` to `N`, then the image of `algebraicClosure K L`
under the map `i` is contained in `algebraicClosure K N`. -/
theorem map_le_of_algHom (i : L →ₐ[K] N) :
    (algebraicClosure K L).map i ≤ algebraicClosure K N :=
  map_le_iff_le_comap.2 (comap_eq_of_algHom i).ge

variable (K) in
/-- If `N / L / K` is a field extension tower, such that `N / L` has no non-trivial algebraic
subextensions (this means that it is purely trancendental),
then the image of `algebraicClosure K L` in `N` is equal to `algebraicClosure K N`. -/
theorem map_eq_of_algebraicClosure_eq_bot [Algebra L N] [IsScalarTower K L N]
    (h : algebraicClosure L N = ⊥) :
    (algebraicClosure K L).map (IsScalarTower.toAlgHom K L N) = algebraicClosure K N := by
  refine le_antisymm (map_le_of_algHom _) (fun x hx ↦ ?_)
  obtain ⟨y, rfl⟩ := mem_bot.1 <| h ▸ mem_algebraicClosure_iff'.2
    (IsIntegral.tower_top <| mem_algebraicClosure_iff'.1 hx)
  exact ⟨y, (map_mem_algebraicClosure_iff <| IsScalarTower.toAlgHom K L N).mp hx, rfl⟩

/-- If `i` is an `K`-algebra isomorphism of `L` and `N`, then the image of `algebraicClosure K L`
under the map `i` is equal to `algebraicClosure K N`. -/
theorem map_eq_of_algEquiv (i : L ≃ₐ[K] N) :
    (algebraicClosure K L).map i = algebraicClosure K N :=
  (map_le_of_algHom i.toAlgHom).antisymm
    (fun x h ↦ ⟨_, (map_mem_algebraicClosure_iff i.symm).2 h, by simp⟩)

/-- If `L` and `N` are isomorphic as `K`-algebras, then `algebraicClosure K L` and
`algebraicClosure K N` are also isomorphic as `K`-algebras. -/
def algEquivOfAlgEquiv (i : L ≃ₐ[K] N) :
    algebraicClosure K L ≃ₐ[K] algebraicClosure K N :=
  (intermediateFieldMap i _).trans (equivOfEq (map_eq_of_algEquiv i))

alias AlgEquiv.algebraicClosure := algebraicClosure.algEquivOfAlgEquiv

variable (K L N)

/-- The algebraic closure of `K` in `L` is algebraic over `K`. -/
instance isAlgebraic : Algebra.IsAlgebraic K (algebraicClosure K L) :=
  ⟨fun x ↦
    isAlgebraic_iff.mpr (IsAlgebraic.isIntegral (mem_algebraicClosure_iff.mp x.2)).isAlgebraic⟩

/-- The algebraic closure of `K` in `L` is the integral closure of `K` in `L`. -/
instance isIntegralClosure : IsIntegralClosure (algebraicClosure K L) K L :=
  inferInstanceAs (IsIntegralClosure (integralClosure K L) K L)

end algebraicClosure

variable (K L N)

/-- An intermediate field of `L / K` is contained in the algebraic closure of `K` in `L`
if all of its elements are algebraic over `K`. -/
theorem le_algebraicClosure' {L : IntermediateField K L} (hs : ∀ x : L, IsAlgebraic K x) :
    L ≤ algebraicClosure K L := fun x h ↦ by
    simpa only [mem_algebraicClosure_iff, IsAlgebraic, ne_eq, ← aeval_algebraMap_eq_zero_iff L,
      Algebra.id.map_eq_id, RingHom.id_apply, IntermediateField.algebraMap_apply] using hs ⟨x, h⟩

/-- An intermediate field of `L / K` is contained in the algebraic closure of `K` in `L`
if it is algebraic over `K`. -/
theorem le_algebraicClosure (L : IntermediateField K L) [Algebra.IsAlgebraic K L] :
    L ≤ algebraicClosure K L := le_algebraicClosure' K L (Algebra.IsAlgebraic.isAlgebraic)

/-- An intermediate field of `L / K` is contained in the algebraic closure of `K` in `L`
if and only if it is algebraic over `K`. -/
theorem le_algebraicClosure_iff (L : IntermediateField K L) :
    L ≤ algebraicClosure K L ↔ Algebra.IsAlgebraic K L :=
  ⟨fun h ↦ ⟨fun x ↦ by simpa only [IsAlgebraic, ne_eq, ← aeval_algebraMap_eq_zero_iff L,
    IntermediateField.algebraMap_apply,
    Algebra.id.map_eq_id, RingHomCompTriple.comp_apply, mem_algebraicClosure_iff] using h x.2⟩,
    fun _ ↦ le_algebraicClosure _ _ _⟩

namespace algebraicClosure
/-- The algebraic closure in `L` of the algebraic closure of `K` in `L` is equal to itself. -/
theorem algebraicClosure_eq_bot :
    algebraicClosure (algebraicClosure K L) L = ⊥ :=
  bot_unique fun x hx ↦ mem_bot.2
    ⟨⟨x, isIntegral_trans x (mem_algebraicClosure_iff'.1 hx)⟩, rfl⟩

/-- The normal closure in `L / K` of the algebraic closure of `K` in `L` is equal to itself. -/
theorem normalClosure_eq_self :
    normalClosure K (algebraicClosure K L) L = algebraicClosure K L :=
  le_antisymm (normalClosure_le_iff.2 fun i ↦
    haveI : Algebra.IsAlgebraic K i.fieldRange := (AlgEquiv.ofInjectiveField i).isAlgebraic
    le_algebraicClosure K L _) (le_normalClosure _)

end algebraicClosure

/-- If `L / K` is a field extension and `L` is algebraically closed, then the algebraic closure
of `K` in `L` is equal to `K` if and only if `K` is algebraically closed. -/
theorem IsAlgClosed.algebraicClosure_eq_bot_iff [IsAlgClosed L] :
    algebraicClosure K L = ⊥ ↔ IsAlgClosed K := by
  refine ⟨fun h ↦ IsAlgClosed.of_exists_root _ fun p hmon hirr ↦ ?_,
    fun _ ↦ IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _⟩
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero L p (degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, rfl⟩ := h ▸ mem_algebraicClosure_iff'.2 (minpoly.ne_zero_iff.1 <|
    ne_zero_of_dvd_ne_zero hmon.ne_zero (minpoly.dvd _ x hx))
  exact ⟨x, by simpa [Algebra.ofId_apply] using hx⟩

/-- `K(S) / K` is a algebraic extension if and only if all elements of `S` are
algebraic elements. -/
theorem IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic {S : Set L} :
    Algebra.IsAlgebraic K (adjoin K S) ↔ ∀ x ∈ S, IsAlgebraic K x :=
  ((le_algebraicClosure_iff K L _).symm.trans (adjoin_le_iff.trans <| forall_congr' <|
    fun _ => Iff.imp Iff.rfl mem_algebraicClosure_iff))

namespace algebraicClosure
/-- If `L` is algebraically closed, then the algebraic closure of `K` in `L` is an absolute
algebraic closure of `K`. -/
instance isAlgClosure [IsAlgClosed L] : IsAlgClosure K (algebraicClosure K L) :=
  ⟨(IsAlgClosed.algebraicClosure_eq_bot_iff _ L).mp (algebraicClosure_eq_bot K L),
    isAlgebraic K L⟩

/-- The algebraic closure of `K` in `L` is equal to `L` if and only if `L / K` is
algebraic. -/
theorem eq_top_iff : algebraicClosure K L = ⊤ ↔ Algebra.IsAlgebraic K L :=
  ⟨fun h ↦ ⟨fun _ ↦ mem_algebraicClosure_iff.1 (h ▸ mem_top)⟩,
    fun _ ↦ top_unique fun x _ ↦ mem_algebraicClosure_iff.2 (Algebra.IsAlgebraic.isAlgebraic x)⟩

/-- If `N / L / K` is a field extension tower, then `algebraicClosure K N` is contained in
`algebraicClosure L N`. -/
theorem le_restrictScalars [Algebra L N] [IsScalarTower K L N] :
    algebraicClosure K N ≤ (algebraicClosure L N).restrictScalars K :=
  fun _ h ↦ mem_algebraicClosure_iff.2 <| IsAlgebraic.tower_top L (mem_algebraicClosure_iff.1 h)

/-- If `N / L / K` is a field extension tower, such that `L / K` is algebraic, then
`algebraicClosure K N` is equal to `algebraicClosure L N`. -/
theorem eq_restrictScalars_of_isAlgebraic [Algebra L N] [IsScalarTower K L N]
    [Algebra.IsAlgebraic K L] : algebraicClosure K N = (algebraicClosure L N).restrictScalars K :=
  (algebraicClosure.le_restrictScalars K L N).antisymm fun _ h ↦
    isIntegral_trans _ h

/-- If `N / L / K` is a field extension tower, then `L` adjoin `algebraicClosure K N` is contained
in `algebraicClosure L N`. -/
theorem adjoin_le [Algebra L N] [IsScalarTower K L N] :
    adjoin L (algebraicClosure K N) ≤ algebraicClosure L N :=
  adjoin_le_iff.2 <| le_restrictScalars K L N

end algebraicClosure


namespace IntermediateField

section FiniteDimensional

variable (F E : IntermediateField K L)

instance finiteDimensional_left [FiniteDimensional K L] : FiniteDimensional K F := .left K F L
instance finiteDimensional_right [FiniteDimensional K L] : FiniteDimensional F L := .right K F L

@[simp]
theorem rank_eq_rank_subalgebra : Module.rank K F.toSubalgebra = Module.rank K F :=
  rfl

@[simp]
theorem finrank_eq_finrank_subalgebra : finrank K F.toSubalgebra = finrank K F :=
  rfl

variable {F} {E}

@[simp]
theorem toSubalgebra_eq_iff : F.toSubalgebra = E.toSubalgebra ↔ F = E := by
  rw [SetLike.ext_iff, SetLike.ext'_iff, Set.ext_iff]
  rfl

/-- If `F ≤ E` are two intermediate fields of `L / K` such that `[E : K] ≤ [F : K]` are finite,
then `F = E`. -/
theorem eq_of_le_of_finrank_le [hfin : FiniteDimensional K E] (h_le : F ≤ E)
    (h_finrank : finrank K E ≤ finrank K F) : F = E :=
  haveI : Module.Finite K E.toSubalgebra := hfin
  toSubalgebra_injective <| Subalgebra.eq_of_le_of_finrank_le h_le h_finrank

/-- If `F ≤ E` are two intermediate fields of `L / K` such that `[F : K] = [E : K]` are finite,
then `F = E`. -/
theorem eq_of_le_of_finrank_eq [FiniteDimensional K E] (h_le : F ≤ E)
    (h_finrank : finrank K F = finrank K E) : F = E :=
  eq_of_le_of_finrank_le h_le h_finrank.ge

-- If `F ≤ E` are two intermediate fields of a finite extension `L / K` such that
-- `[L : F] ≤ [L : E]`, then `F = E`. Marked as private since it's a direct corollary of
-- `eq_of_le_of_finrank_le'` (the `FiniteDimensional K L` implies `FiniteDimensional F L`
-- automatically by typeclass resolution).
private theorem eq_of_le_of_finrank_le'' [FiniteDimensional K L] (h_le : F ≤ E)
    (h_finrank : finrank F L ≤ finrank E L) : F = E := by
  apply eq_of_le_of_finrank_le h_le
  have h1 := finrank_mul_finrank K F L
  have h2 := finrank_mul_finrank K E L
  have h3 : 0 < finrank E L := finrank_pos
  nlinarith

/-- If `F ≤ E` are two intermediate fields of `L / K` such that `[L : F] ≤ [L : E]` are finite,
then `F = E`. -/
theorem eq_of_le_of_finrank_le' [FiniteDimensional F L] (h_le : F ≤ E)
    (h_finrank : finrank F L ≤ finrank E L) : F = E := by
  refine le_antisymm h_le (fun l hl ↦ ?_)
  rwa [← mem_extendScalars (le_refl F), eq_of_le_of_finrank_le''
    ((extendScalars_le_extendScalars_iff (le_refl F) h_le).2 h_le) h_finrank, mem_extendScalars]

/-- If `F ≤ E` are two intermediate fields of `L / K` such that `[L : F] = [L : E]` are finite,
then `F = E`. -/
theorem eq_of_le_of_finrank_eq' [FiniteDimensional F L] (h_le : F ≤ E)
    (h_finrank : finrank F L = finrank E L) : F = E :=
  eq_of_le_of_finrank_le' h_le h_finrank.le

end FiniteDimensional

theorem isAlgebraic_iff {x : S} : IsAlgebraic K x ↔ IsAlgebraic K (x : L) :=
  (isAlgebraic_algebraMap_iff (algebraMap S L).injective).symm

theorem isIntegral_iff {x : S} : IsIntegral K x ↔ IsIntegral K (x : L) :=
  (isIntegral_algHom_iff S.val S.val.injective).symm

theorem minpoly_eq (x : S) : minpoly K x = minpoly K (x : L) :=
  (minpoly.algebraMap_eq (algebraMap S L).injective x).symm

end IntermediateField

/-- If `L/K` is algebraic, the `K`-subalgebras of `L` are all fields. -/
def subalgebraEquivIntermediateField [Algebra.IsAlgebraic K L] :
    Subalgebra K L ≃o IntermediateField K L where
  toFun S := S.toIntermediateField fun x hx => S.inv_mem_of_algebraic
    (Algebra.IsAlgebraic.isAlgebraic ((⟨x, hx⟩ : S) : L))
  invFun S := S.toSubalgebra
  left_inv _ := toSubalgebra_toIntermediateField _ _
  right_inv := toIntermediateField_toSubalgebra
  map_rel_iff' := Iff.rfl

@[simp]
theorem mem_subalgebraEquivIntermediateField [Algebra.IsAlgebraic K L] {S : Subalgebra K L}
    {x : L} : x ∈ subalgebraEquivIntermediateField S ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem mem_subalgebraEquivIntermediateField_symm [Algebra.IsAlgebraic K L]
    {S : IntermediateField K L} {x : L} :
    x ∈ subalgebraEquivIntermediateField.symm S ↔ x ∈ S :=
  Iff.rfl
