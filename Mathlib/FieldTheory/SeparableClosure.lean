/-
Copyright (c) 2023 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.FieldTheory.IsSepClosed

/-!

# Separable closure

This file contains basics about the (relative) separable closure of a field extension.

## Main definitions

- `separableClosure`: the (relative) separable closure of `E / F`, or called maximal separable
  subextension of `E / F`, is defined to be the intermediate field of `E / F` consisting of all
  separable elements.

- `SeparableClosure`: the (absolute) separable closure, defined to be the (relative) separable
  closure inside the algebraic closure.

- `Field.sepDegree F E`: the (infinite) separable degree $[E:F]_s$ of an algebraic extension
  `E / F` of fields, defined to be the degree of `separableClosure F E / F`. Later we will show
  that (`Field.finSepDegree_eq`, not in this file), if `Field.Emb F E` is finite, then this
  coincides with `Field.finSepDegree F E`.

- `Field.insepDegree F E`: the (infinite) inseparable degree $[E:F]_i$ of an algebraic extension
  `E / F` of fields, defined to be the degree of `E / separableClosure F E`.

- `Field.finInsepDegree F E`: the (finite) inseparable degree $[E:F]_i$ of an algebraic extension
  `E / F` of fields, defined to be the degree of `E / separableClosure F E` as a natural number.
  It is zero if such field extension is not finite.

## Main results

- `le_separableClosure_iff`: an intermediate field of `E / F` is contained in the (relative)
  separable closure of `E / F` if and only if it is separable over `F`.

- `separableClosure.normalClosure_eq_self`: the normal closure of the (relative) separable
  closure of `E / F` is equal to itself.

- `separableClosure.normal`: the (relative) separable closure of a normal extension is normal.

- `separableClosure.isSepClosure`: the (relative) separable closure of a separably closed extension
  is a separable closure of the base field.

- `IntermediateField.isSeparable_adjoin_iff_separable`: `F(S) / F` is a separable extension if and
  only if all elements of `S` are separable elements.

- `separableClosure.eq_top_iff`: the (relative) separable closure of `E / F` is equal to `E`
  if and only if `E / F` is separable.

## Tags

separable degree, degree, separable closure

-/

open scoped Classical Polynomial

open FiniteDimensional Polynomial IntermediateField Field

noncomputable section

universe u v w

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

variable (K : Type w) [Field K] [Algebra F K]

section separableClosure

/-- The (relative) separable closure of `E / F`, or called maximal separable subextension
of `E / F`, is defined to be the intermediate field of `E / F` consisting of all separable
elements. The previous results prove that these elements are closed under field operations. -/
def separableClosure : IntermediateField F E where
  carrier := {x | (minpoly F x).Separable}
  mul_mem' := separable_mul
  one_mem' := map_one (algebraMap F E) ▸ separable_algebraMap E 1
  add_mem' := separable_add
  zero_mem' := map_zero (algebraMap F E) ▸ separable_algebraMap E 0
  algebraMap_mem' := separable_algebraMap E
  inv_mem' := separable_inv

/-- An element is contained in the (relative) separable closure of `E / F` if and only if
it is a separable element. -/
theorem mem_separableClosure_iff {x : E} :
    x ∈ separableClosure F E ↔ (minpoly F x).Separable := Iff.rfl

/-- If `i` is an `F`-algebra homomorphism from `E` to `K`, then `i x` is contained in
`separableClosure F K` if and only if `x` is contained in `separableClosure F E`. -/
theorem map_mem_separableClosure_iff (i : E →ₐ[F] K) {x : E} :
    i x ∈ separableClosure F K ↔ x ∈ separableClosure F E := by
  simp_rw [mem_separableClosure_iff, minpoly.algHom_eq i i.injective]

/-- If `i` is an `F`-algebra homomorphism from `E` to `K`, then `separableClosure F E` is equal to
the preimage of `separableClosure F K` under the map `i`. -/
theorem separableClosure.eq_comap_of_algHom (i : E →ₐ[F] K) :
    separableClosure F E = (separableClosure F K).comap i := by
  ext x
  exact (map_mem_separableClosure_iff F E K i).symm

/-- If `i` is an `F`-algebra homomorphism from `E` to `K`, then `separableClosure F K` contains
the image of `separableClosure F E` under the map `i`. -/
theorem separableClosure.map_le_of_algHom (i : E →ₐ[F] K) :
    (separableClosure F E).map i ≤ separableClosure F K :=
  map_le_iff_le_comap.2 (eq_comap_of_algHom F E K i).le

/-- If `K / E / F` is a field extension tower, such that `K / E` has no non-trivial separable
subextensions (when `K / E` is algebraic, this means that it is purely inseparable),
then `separableClosure F K` is equal to `separableClosure F E`. -/
theorem separableClosure.eq_map_of_separableClosure_eq_bot [Algebra E K] [IsScalarTower F E K]
    (h : separableClosure E K = ⊥) :
    separableClosure F K = (separableClosure F E).map (IsScalarTower.toAlgHom F E K) := by
  refine le_antisymm (fun x hx ↦ ?_) (map_le_of_algHom F E K _)
  obtain ⟨y, rfl⟩ := mem_bot.1 <| h ▸ (mem_separableClosure_iff E K).2
    (mem_separableClosure_iff _ _ |>.mp hx |>.map_minpoly E)
  exact ⟨y, (map_mem_separableClosure_iff _ _ _ <| IsScalarTower.toAlgHom F E K).mp hx, rfl⟩

/-- If `i` is an `F`-algebra isomorphism of `E` and `K`, then `separableClosure F K` is equal to
the image of `separableClosure F E` under the map `i`. -/
theorem separableClosure.eq_map_of_algEquiv (i : E ≃ₐ[F] K) :
    separableClosure F K = (separableClosure F E).map i :=
  le_antisymm (fun x h ↦ ⟨_, (map_mem_separableClosure_iff F K E i.symm).2 h, i.right_inv x⟩)
    (map_le_of_algHom F E K i)

/-- If `E` and `K` are isomorphic as `F`-algebras, then `separableClosure F E` and
`separableClosure F K` are also isomorphic as `F`-algebras. -/
def separableClosure.algEquivOfAlgEquiv (i : E ≃ₐ[F] K) :
    separableClosure F E ≃ₐ[F] separableClosure F K :=
  ((separableClosure F E).intermediateFieldMap i).trans
    (equivOfEq (eq_map_of_algEquiv F E K i).symm)

/-- The (relative) separable closure of `E / F` is algebraic over `F`. -/
theorem separableClosure.isAlgebraic : Algebra.IsAlgebraic F (separableClosure F E) :=
  fun x ↦ isAlgebraic_iff.2 x.2.isIntegral.isAlgebraic

/-- The (relative) separable closure of `E / F` is separable over `F`. -/
instance separableClosure.isSeparable : IsSeparable F (separableClosure F E) :=
  ⟨fun x ↦ by simpa only [minpoly_eq] using x.2⟩

/-- An intermediate field of `E / F` is contained in the (relative) separable closure of `E / F`
if all of its elements are separable over `F`. -/
theorem le_separableClosure' {L : IntermediateField F E} (hs : ∀ x : L, (minpoly F x).Separable) :
    L ≤ separableClosure F E := fun x h ↦ by simpa only [minpoly_eq] using hs ⟨x, h⟩

/-- An intermediate field of `E / F` is contained in the (relative) separable closure of `E / F`
if it is separable over `F`. -/
theorem le_separableClosure (L : IntermediateField F E) [IsSeparable F L] :
    L ≤ separableClosure F E := le_separableClosure' F E (IsSeparable.separable F)

/-- An intermediate field of `E / F` is contained in the (relative) separable closure of `E / F`
if and only if it is separable over `F`. -/
theorem le_separableClosure_iff (L : IntermediateField F E) :
    L ≤ separableClosure F E ↔ IsSeparable F L :=
  ⟨fun h ↦ ⟨fun x ↦ by simpa only [minpoly_eq] using h x.2⟩, fun _ ↦ le_separableClosure _ _ _⟩

/-- The (relative) separable closure of the (relative) separable closure of `E / F` is equal to
itself. -/
theorem separableClosure.separableClosure_eq_bot :
    separableClosure (separableClosure F E) E = ⊥ := bot_unique fun x hx ↦ by
  rw [mem_separableClosure_iff, ← isSeparable_adjoin_simple_iff_separable] at hx
  set L := separableClosure F E
  haveI : IsSeparable F (L⟮x⟯.restrictScalars F) := IsSeparable.trans F L L⟮x⟯
  exact mem_bot.2 ⟨⟨x, (mem_separableClosure_iff F E).2 (separable_of_mem_isSeparable F E <|
    show x ∈ L⟮x⟯.restrictScalars F from mem_adjoin_simple_self L x)⟩, rfl⟩

/-- The normal closure of the (relative) separable closure of `E / F` is equal to itself. -/
theorem separableClosure.normalClosure_eq_self :
    normalClosure F (separableClosure F E) E = separableClosure F E :=
  le_antisymm (normalClosure_le_iff.2 fun i ↦
    haveI : IsSeparable F i.fieldRange := (AlgEquiv.ofInjectiveField i).isSeparable
    le_separableClosure F E _) (le_normalClosure _)

/-- If `E` is normal over `F`, then the (relative) separable closure of `E / F` is also normal
over `F`. -/
instance separableClosure.normal [Normal F E] : Normal F (separableClosure F E) := by
  rw [← separableClosure.normalClosure_eq_self]
  exact normalClosure.normal F _ E

/-- If `E` is separably closed, then the (relative) separable closure of `E / F` is a
separable closure of `F`. -/
instance separableClosure.isSepClosure [IsSepClosed E] : IsSepClosure F (separableClosure F E) := by
  refine ⟨IsSepClosed.of_exists_root _ fun p _ hirr hsep ↦ ?_, isSeparable F E⟩
  obtain ⟨x, hx⟩ := IsSepClosed.exists_aeval_eq_zero E p (degree_pos_of_irreducible hirr).ne' hsep
  haveI := (isSeparable_adjoin_simple_iff_separable _ E).2 <| hsep.of_dvd <| minpoly.dvd _ x hx
  let L := separableClosure F E
  haveI : IsSeparable F (restrictScalars F L⟮x⟯) := IsSeparable.trans F L L⟮x⟯
  have : x ∈ restrictScalars F L⟮x⟯ := mem_adjoin_simple_self _ x
  use ⟨x, le_separableClosure F E (restrictScalars F L⟮x⟯) this⟩
  apply_fun algebraMap L E using (algebraMap L E).injective
  rwa [map_zero, ← aeval_algebraMap_apply_eq_algebraMap_eval]

/-- The (absolute) separable closure is defined to be the (relative) separable closure inside the
algebraic closure. -/
abbrev SeparableClosure : Type _ := separableClosure F (AlgebraicClosure F)

/-- `F(S) / F` is a separable extension if and only if all elements of `S` are
separable elements. -/
theorem IntermediateField.isSeparable_adjoin_iff_separable {S : Set E} :
    IsSeparable F (adjoin F S) ↔ ∀ x ∈ S, (minpoly F x).Separable :=
  (le_separableClosure_iff F E _).symm.trans adjoin_le_iff

/-- The (relative) separable closure of `E / F` is equal to `E` if and only if `E / F` is
separable. -/
theorem separableClosure.eq_top_iff : separableClosure F E = ⊤ ↔ IsSeparable F E :=
  ⟨fun h ↦ ⟨fun _ ↦ (mem_separableClosure_iff F E).1 (h ▸ mem_top)⟩,
    fun _ ↦ top_unique fun x _ ↦ (mem_separableClosure_iff F E).2 (IsSeparable.separable _ x)⟩

/-- If `K / E / F` is a field extension tower, then `separableClosure F K` is contained in
`separableClosure E K`. -/
theorem separableClosure.le_restrictScalars [Algebra E K] [IsScalarTower F E K] :
    separableClosure F K ≤ (separableClosure E K).restrictScalars F := fun _ h ↦ h.map_minpoly E

/-- If `K / E / F` is a field extension tower, such that `E / F` is separable, then
`separableClosure F K` is equal to `separableClosure E K`. -/
theorem separableClosure.eq_restrictScalars_of_isSeparable [Algebra E K] [IsScalarTower F E K]
    [IsSeparable F E] : separableClosure F K = (separableClosure E K).restrictScalars F := by
  refine le_antisymm (separableClosure.le_restrictScalars F E K) fun x hx ↦ ?_
  rw [mem_restrictScalars, mem_separableClosure_iff,
    ← isSeparable_adjoin_simple_iff_separable] at hx
  haveI : IsSeparable F (E⟮x⟯.restrictScalars F) := IsSeparable.trans F E E⟮x⟯
  have h : x ∈ E⟮x⟯.restrictScalars F := mem_adjoin_simple_self E x
  exact (mem_separableClosure_iff F _).2 <| separable_of_mem_isSeparable F _ h

/-- If `K / E / F` is a field extension tower, then `E` adjoin `separableClosure F K` is contained
in `separableClosure E K`. -/
theorem separableClosure.adjoin_le [Algebra E K] [IsScalarTower F E K] :
    adjoin E (separableClosure F K) ≤ separableClosure E K :=
  adjoin_le_iff.2 <| le_restrictScalars F E K

/-- A compositum of two separable extensions is separable. -/
instance IntermediateField.isSeparable_sup (L1 L2 : IntermediateField F E)
    [h1 : IsSeparable F L1] [h2 : IsSeparable F L2] :
    IsSeparable F (L1 ⊔ L2 : IntermediateField F E) := by
  rw [← le_separableClosure_iff] at h1 h2 ⊢
  exact sup_le h1 h2

/-- A compositum of separable extensions is separable. -/
instance IntermediateField.isSeparable_iSup {ι : Type*} {t : ι → IntermediateField F E}
    [h : ∀ i, IsSeparable F (t i)] : IsSeparable F (⨆ i, t i : IntermediateField F E) := by
  simp_rw [← le_separableClosure_iff] at h ⊢
  exact iSup_le h

end separableClosure

namespace Field

/-- The (infinite) separable degree for a general field extension `E / F` is defined
to be the degree of `separableClosure F E / F`. -/
def sepDegree := Module.rank F (separableClosure F E)

/-- The (infinite) inseparable degree for a general field extension `E / F` is defined
to be the degree of `E / separableClosure F E`. -/
def insepDegree := Module.rank (separableClosure F E) E

/-- The (finite) inseparable degree for a general field extension `E / F` is defined
to be the degree of `E / separableClosure F E` as a natural number. It is defined to be zero
if such field extension is infinite. -/
def finInsepDegree : ℕ := Cardinal.toNat (insepDegree F E)

instance instNeZeroSepDegree : NeZero (sepDegree F E) := ⟨rank_pos.ne'⟩

instance instNeZeroInsepDegree : NeZero (insepDegree F E) := ⟨rank_pos.ne'⟩

instance instNeZeroFinInsepDegree [FiniteDimensional F E] :
    NeZero (finInsepDegree F E) := ⟨finrank_pos.ne'⟩

/-- If `E` and `K` are isomorphic as `F`-algebras, then they have the same (infinite)
separable degree over `F`. -/
theorem sepDegree_eq_of_equiv (i : E ≃ₐ[F] K) :
    Cardinal.lift.{w} (sepDegree F E) = Cardinal.lift.{v} (sepDegree F K) :=
  (separableClosure.algEquivOfAlgEquiv F E K i).toLinearEquiv.lift_rank_eq

/-- The (infinite) separable degree multiply by the (infinite) inseparable degree is equal
to the (infinite) field extension degree. -/
theorem sepDegree_mul_insepDegree : sepDegree F E * insepDegree F E = Module.rank F E :=
  rank_mul_rank F (separableClosure F E) E

/-- If `E` and `K` are isomorphic as `F`-algebras, then they have the same (infinite)
inseparable degree over `F`. -/
theorem insepDegree_eq_of_equiv (i : E ≃ₐ[F] K) :
    Cardinal.lift.{w} (insepDegree F E) = Cardinal.lift.{v} (insepDegree F K) :=
  Algebra.lift_rank_eq_of_equiv_equiv (separableClosure.algEquivOfAlgEquiv F E K i) i rfl

/-- If `E` and `K` are isomorphic as `F`-algebras, then they have the same (finite)
inseparable degree over `F`. -/
theorem finInsepDegree_eq_of_equiv (i : E ≃ₐ[F] K) :
    finInsepDegree F E = finInsepDegree F K := by
  simpa only [Cardinal.toNat_lift] using congr_arg Cardinal.toNat
    (insepDegree_eq_of_equiv F E K i)

@[simp]
theorem sepDegree_self : sepDegree F F = 1 := by
  rw [sepDegree, Subsingleton.elim (separableClosure F F) ⊥, IntermediateField.rank_bot]

@[simp]
theorem insepDegree_self : insepDegree F F = 1 := by
  rw [insepDegree, Subsingleton.elim (separableClosure F F) ⊤, IntermediateField.rank_top]

@[simp]
theorem finInsepDegree_self : finInsepDegree F F = 1 := by
  simp only [finInsepDegree, insepDegree_self, Cardinal.one_toNat]

end Field

namespace IntermediateField

@[simp]
theorem sepDegree_bot : sepDegree F (⊥ : IntermediateField F E) = 1 := by
  have := sepDegree_eq_of_equiv _ _ _ (botEquiv F E)
  rwa [sepDegree_self, Cardinal.lift_one, ← Cardinal.lift_one.{u, v}, Cardinal.lift_inj] at this

@[simp]
theorem insepDegree_bot : insepDegree F (⊥ : IntermediateField F E) = 1 := by
  have := insepDegree_eq_of_equiv _ _ _ (botEquiv F E)
  rwa [insepDegree_self, Cardinal.lift_one, ← Cardinal.lift_one.{u, v}, Cardinal.lift_inj] at this

@[simp]
theorem finInsepDegree_bot : finInsepDegree F (⊥ : IntermediateField F E) = 1 := by
  rw [finInsepDegree_eq_of_equiv _ _ _ (botEquiv F E), finInsepDegree_self]

section Tower

variable [Algebra E K] [IsScalarTower F E K]

theorem lift_sepDegree_bot' : Cardinal.lift.{v} (sepDegree F (⊥ : IntermediateField E K)) =
    Cardinal.lift.{w} (sepDegree F E) :=
  sepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

theorem lift_insepDegree_bot' : Cardinal.lift.{v} (insepDegree F (⊥ : IntermediateField E K)) =
    Cardinal.lift.{w} (insepDegree F E) :=
  insepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

variable {F}

@[simp]
theorem finInsepDegree_bot' :
    finInsepDegree F (⊥ : IntermediateField E K) = finInsepDegree F E := by
  simpa only [Cardinal.toNat_lift] using congr_arg Cardinal.toNat (lift_insepDegree_bot' F E K)

@[simp]
theorem sepDegree_top : sepDegree F (⊤ : IntermediateField E K) = sepDegree F K := by
  simpa only [Cardinal.lift_id] using sepDegree_eq_of_equiv _ _ _
    ((topEquiv (F := E) (E := K)).restrictScalars F)

@[simp]
theorem insepDegree_top : insepDegree F (⊤ : IntermediateField E K) = insepDegree F K := by
  simpa only [Cardinal.lift_id] using insepDegree_eq_of_equiv _ _ _
    ((topEquiv (F := E) (E := K)).restrictScalars F)

@[simp]
theorem finInsepDegree_top : finInsepDegree F (⊤ : IntermediateField E K) = finInsepDegree F K := by
  simp only [finInsepDegree, insepDegree_top]

variable (K : Type v) [Field K] [Algebra F K] [Algebra E K] [IsScalarTower F E K]

@[simp]
theorem sepDegree_bot' : sepDegree F (⊥ : IntermediateField E K) = sepDegree F E := by
  simpa only [Cardinal.lift_id] using lift_sepDegree_bot' F E K

@[simp]
theorem insepDegree_bot' : insepDegree F (⊥ : IntermediateField E K) = insepDegree F E := by
  simpa only [Cardinal.lift_id] using lift_insepDegree_bot' F E K

end Tower

end IntermediateField
