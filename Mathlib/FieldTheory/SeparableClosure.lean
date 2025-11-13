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

- `separableClosure`: the relative separable closure of `F` in `E`, or called maximal separable
  subextension of `E / F`, is defined to be the intermediate field of `E / F` consisting of all
  separable elements.

- `SeparableClosure`: the absolute separable closure, defined to be the relative separable
  closure inside the algebraic closure.

- `Field.sepDegree F E`: the (infinite) separable degree $[E:F]_s$ of an algebraic extension
  `E / F` of fields, defined to be the degree of `separableClosure F E / F`. Later we will show
  that (`Field.finSepDegree_eq`, not in this file), if `Field.Emb F E` is finite, then this
  coincides with `Field.finSepDegree F E`.

- `Field.insepDegree F E`: the (infinite) inseparable degree $[E:F]_i$ of an algebraic extension
  `E / F` of fields, defined to be the degree of `E / separableClosure F E`.

- `Field.finInsepDegree F E`: the finite inseparable degree $[E:F]_i$ of an algebraic extension
  `E / F` of fields, defined to be the degree of `E / separableClosure F E` as a natural number.
  It is zero if such field extension is not finite.

## Main results

- `le_separableClosure_iff`: an intermediate field of `E / F` is contained in the
  separable closure of `F` in `E` if and only if it is separable over `F`.

- `separableClosure.normalClosure_eq_self`: the normal closure of the separable
  closure of `F` in `E` is equal to itself.

- `separableClosure.isGalois`: the separable closure in a normal extension is Galois
  (namely, normal and separable).

- `separableClosure.isSepClosure`: the separable closure in a separably closed extension
  is a separable closure of the base field.

- `IntermediateField.isSeparable_adjoin_iff_isSeparable`: `F(S) / F` is a separable extension if and
  only if all elements of `S` are separable elements.

- `separableClosure.eq_top_iff`: the separable closure of `F` in `E` is equal to `E`
  if and only if `E / F` is separable.

## Tags

separable degree, degree, separable closure

-/

open Module Polynomial IntermediateField Field

noncomputable section

universe u v w

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
variable (K : Type w) [Field K] [Algebra F K]

section separableClosure

/-- The (relative) separable closure of `F` in `E`, or called maximal separable subextension
of `E / F`, is defined to be the intermediate field of `E / F` consisting of all separable
elements. The previous results prove that these elements are closed under field operations. -/
@[stacks 09HC]
def separableClosure : IntermediateField F E where
  carrier := {x | IsSeparable F x}
  mul_mem' := isSeparable_mul
  add_mem' := isSeparable_add
  algebraMap_mem' := isSeparable_algebraMap E
  inv_mem' _ := isSeparable_inv

variable {F E K}

/-- An element is contained in the separable closure of `F` in `E` if and only if
it is a separable element. -/
theorem mem_separableClosure_iff {x : E} :
    x ∈ separableClosure F E ↔ IsSeparable F x := Iff.rfl

/-- If `i` is an `F`-algebra homomorphism from `E` to `K`, then `i x` is contained in
`separableClosure F K` if and only if `x` is contained in `separableClosure F E`. -/
theorem map_mem_separableClosure_iff (i : E →ₐ[F] K) {x : E} :
    i x ∈ separableClosure F K ↔ x ∈ separableClosure F E := by
  simp_rw [mem_separableClosure_iff, IsSeparable, minpoly.algHom_eq i i.injective]

/-- If `i` is an `F`-algebra homomorphism from `E` to `K`, then the preimage of
`separableClosure F K` under the map `i` is equal to `separableClosure F E`. -/
theorem separableClosure.comap_eq_of_algHom (i : E →ₐ[F] K) :
    (separableClosure F K).comap i = separableClosure F E := by
  ext x
  exact map_mem_separableClosure_iff i

/-- If `i` is an `F`-algebra homomorphism from `E` to `K`, then the image of `separableClosure F E`
under the map `i` is contained in `separableClosure F K`. -/
theorem separableClosure.map_le_of_algHom (i : E →ₐ[F] K) :
    (separableClosure F E).map i ≤ separableClosure F K :=
  map_le_iff_le_comap.2 (comap_eq_of_algHom i).ge

variable (F) in
/-- If `K / E / F` is a field extension tower, such that `K / E` has no non-trivial separable
subextensions (when `K / E` is algebraic, this means that it is purely inseparable),
then the image of `separableClosure F E` in `K` is equal to `separableClosure F K`. -/
theorem separableClosure.map_eq_of_separableClosure_eq_bot [Algebra E K] [IsScalarTower F E K]
    (h : separableClosure E K = ⊥) :
    (separableClosure F E).map (IsScalarTower.toAlgHom F E K) = separableClosure F K := by
  refine le_antisymm (map_le_of_algHom _) (fun x hx ↦ ?_)
  obtain ⟨y, rfl⟩ := mem_bot.1 <| h ▸ mem_separableClosure_iff.2
    (IsSeparable.tower_top E <| mem_separableClosure_iff.1 hx)
  exact ⟨y, (map_mem_separableClosure_iff <| IsScalarTower.toAlgHom F E K).mp hx, rfl⟩

/-- If `i` is an `F`-algebra isomorphism of `E` and `K`, then the image of `separableClosure F E`
under the map `i` is equal to `separableClosure F K`. -/
theorem separableClosure.map_eq_of_algEquiv (i : E ≃ₐ[F] K) :
    (separableClosure F E).map i = separableClosure F K :=
  (map_le_of_algHom i.toAlgHom).antisymm
    (fun x h ↦ ⟨_, (map_mem_separableClosure_iff i.symm).2 h, by simp⟩)

/-- If `E` and `K` are isomorphic as `F`-algebras, then `separableClosure F E` and
`separableClosure F K` are also isomorphic as `F`-algebras. -/
def separableClosure.algEquivOfAlgEquiv (i : E ≃ₐ[F] K) :
    separableClosure F E ≃ₐ[F] separableClosure F K :=
  (intermediateFieldMap i _).trans (equivOfEq (map_eq_of_algEquiv i))

alias AlgEquiv.separableClosure := separableClosure.algEquivOfAlgEquiv

variable (F E K)

/-- The separable closure of `F` in `E` is algebraic over `F`. -/
instance separableClosure.isAlgebraic : Algebra.IsAlgebraic F (separableClosure F E) :=
  ⟨fun x ↦ isAlgebraic_iff.2 (IsSeparable.isIntegral x.2).isAlgebraic⟩

/-- The separable closure of `F` in `E` is separable over `F`. -/
@[stacks 030K "$E_{sep}/F$ is separable"]
instance separableClosure.isSeparable : Algebra.IsSeparable F (separableClosure F E) :=
  ⟨fun x ↦ by simpa only [IsSeparable, minpoly_eq] using x.2⟩

/-- An intermediate field of `E / F` is contained in the separable closure of `F` in `E`
if all of its elements are separable over `F`. -/
theorem le_separableClosure' {L : IntermediateField F E} (hs : ∀ x : L, IsSeparable F x) :
    L ≤ separableClosure F E := fun x h ↦ by simpa only [IsSeparable, minpoly_eq] using hs ⟨x, h⟩

/-- An intermediate field of `E / F` is contained in the separable closure of `F` in `E`
if it is separable over `F`. -/
theorem le_separableClosure (L : IntermediateField F E) [Algebra.IsSeparable F L] :
    L ≤ separableClosure F E := le_separableClosure' F E (Algebra.IsSeparable.isSeparable F)

/-- An intermediate field of `E / F` is contained in the separable closure of `F` in `E`
if and only if it is separable over `F`. -/
theorem le_separableClosure_iff (L : IntermediateField F E) :
    L ≤ separableClosure F E ↔ Algebra.IsSeparable F L :=
  ⟨fun h ↦ ⟨fun x ↦ by simpa only [IsSeparable, minpoly_eq] using h x.2⟩,
    fun _ ↦ le_separableClosure _ _ _⟩

/-- The separable closure in `E` of the separable closure of `F` in `E` is equal to itself. -/
theorem separableClosure.separableClosure_eq_bot :
    separableClosure (separableClosure F E) E = ⊥ :=
  bot_unique fun x hx ↦ mem_bot.2
    ⟨⟨x, IsSeparable.of_algebra_isSeparable_of_isSeparable F (mem_separableClosure_iff.1 hx)⟩, rfl⟩

/-- The normal closure in `E/F` of the separable closure of `F` in `E` is equal to itself. -/
theorem separableClosure.normalClosure_eq_self :
    normalClosure F (separableClosure F E) E = separableClosure F E :=
  le_antisymm (normalClosure_le_iff.2 fun i ↦
    have : Algebra.IsSeparable F i.fieldRange :=
      (AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField i))
    le_separableClosure F E _) (le_normalClosure _)

/-- If `E` is normal over `F`, then the separable closure of `F` in `E` is Galois (i.e.
normal and separable) over `F`. -/
@[stacks 0EXK]
instance separableClosure.isGalois [Normal F E] : IsGalois F (separableClosure F E) where
  to_isSeparable := separableClosure.isSeparable F E
  to_normal := by
    rw [← separableClosure.normalClosure_eq_self]
    exact normalClosure.normal F _ E

/-- If `E / F` is a field extension and `E` is separably closed, then the separable closure
of `F` in `E` is equal to `F` if and only if `F` is separably closed. -/
theorem IsSepClosed.separableClosure_eq_bot_iff [IsSepClosed E] :
    separableClosure F E = ⊥ ↔ IsSepClosed F := by
  refine ⟨fun h ↦ IsSepClosed.of_exists_root _ fun p _ hirr hsep ↦ ?_,
    fun _ ↦ IntermediateField.eq_bot_of_isSepClosed_of_isSeparable _⟩
  obtain ⟨x, hx⟩ := IsSepClosed.exists_aeval_eq_zero E p (degree_pos_of_irreducible hirr).ne' hsep
  obtain ⟨x, rfl⟩ := h ▸ mem_separableClosure_iff.2 (hsep.of_dvd <| minpoly.dvd _ x hx)
  exact ⟨x, by simpa [Algebra.ofId_apply] using hx⟩

/-- If `E` is separably closed, then the separable closure of `F` in `E` is an absolute
separable closure of `F`. -/
instance separableClosure.isSepClosure [IsSepClosed E] : IsSepClosure F (separableClosure F E) :=
  ⟨(IsSepClosed.separableClosure_eq_bot_iff _ E).mp (separableClosure.separableClosure_eq_bot F E),
    isSeparable F E⟩

/-- The absolute separable closure is defined to be the relative separable closure inside the
algebraic closure. It is indeed a separable closure (`IsSepClosure`) by
`separableClosure.isSepClosure`, and it is Galois (`IsGalois`) by `separableClosure.isGalois`
or `IsSepClosure.isGalois`, and every separable extension embeds into it (`IsSepClosed.lift`). -/
abbrev SeparableClosure : Type _ := separableClosure F (AlgebraicClosure F)

instance SeparableClosure.isSepClosed : IsSepClosed (SeparableClosure F) :=
  (inferInstanceAs (IsSepClosure F (SeparableClosure F))).sep_closed

/-- `F(S) / F` is a separable extension if and only if all elements of `S` are
separable elements. -/
theorem IntermediateField.isSeparable_adjoin_iff_isSeparable {S : Set E} :
    Algebra.IsSeparable F (adjoin F S) ↔ ∀ x ∈ S, IsSeparable F x :=
  (le_separableClosure_iff F E _).symm.trans adjoin_le_iff

/-- The separable closure of `F` in `E` is equal to `E` if and only if `E / F` is
separable. -/
theorem separableClosure.eq_top_iff : separableClosure F E = ⊤ ↔ Algebra.IsSeparable F E :=
  ⟨fun h ↦ ⟨fun _ ↦ mem_separableClosure_iff.1 (h ▸ mem_top)⟩,
    fun _ ↦ top_unique fun x _ ↦ mem_separableClosure_iff.2 (Algebra.IsSeparable.isSeparable _ x)⟩

/-- If `K / E / F` is a field extension tower, then `separableClosure F K` is contained in
`separableClosure E K`. -/
theorem separableClosure.le_restrictScalars [Algebra E K] [IsScalarTower F E K] :
    separableClosure F K ≤ (separableClosure E K).restrictScalars F :=
  fun _ ↦ IsSeparable.tower_top E

/-- If `K / E / F` is a field extension tower, such that `E / F` is separable, then
`separableClosure F K` is equal to `separableClosure E K`. -/
theorem separableClosure.eq_restrictScalars_of_isSeparable [Algebra E K] [IsScalarTower F E K]
    [Algebra.IsSeparable F E] : separableClosure F K = (separableClosure E K).restrictScalars F :=
  (separableClosure.le_restrictScalars F E K).antisymm fun _ h ↦
    IsSeparable.of_algebra_isSeparable_of_isSeparable F h

/-- If `K / E / F` is a field extension tower, then `E` adjoin `separableClosure F K` is contained
in `separableClosure E K`. -/
theorem separableClosure.adjoin_le [Algebra E K] [IsScalarTower F E K] :
    adjoin E (separableClosure F K) ≤ separableClosure E K :=
  adjoin_le_iff.2 <| le_restrictScalars F E K

/-- A compositum of two separable extensions is separable. -/
instance IntermediateField.isSeparable_sup (L1 L2 : IntermediateField F E)
    [h1 : Algebra.IsSeparable F L1] [h2 : Algebra.IsSeparable F L2] :
    Algebra.IsSeparable F (L1 ⊔ L2 : IntermediateField F E) := by
  rw [← le_separableClosure_iff] at h1 h2 ⊢
  exact sup_le h1 h2

/-- A compositum of separable extensions is separable. -/
instance IntermediateField.isSeparable_iSup {ι : Type*} {t : ι → IntermediateField F E}
    [h : ∀ i, Algebra.IsSeparable F (t i)] :
    Algebra.IsSeparable F (⨆ i, t i : IntermediateField F E) := by
  simp_rw [← le_separableClosure_iff] at h ⊢
  exact iSup_le h

end separableClosure

namespace Field

/-- The (infinite) separable degree for a general field extension `E / F` is defined
to be the degree of `separableClosure F E / F`. -/
@[stacks 030L "Part 1"]
def sepDegree := Module.rank F (separableClosure F E)

/-- The (infinite) inseparable degree for a general field extension `E / F` is defined
to be the degree of `E / separableClosure F E`. -/
@[stacks 030L "Part 2"]
def insepDegree := Module.rank (separableClosure F E) E

/-- The finite inseparable degree for a general field extension `E / F` is defined
to be the degree of `E / separableClosure F E` as a natural number. It is defined to be zero
if such field extension is infinite. -/
def finInsepDegree : ℕ := finrank (separableClosure F E) E

theorem finInsepDegree_def' : finInsepDegree F E = Cardinal.toNat (insepDegree F E) := rfl

instance instNeZeroSepDegree : NeZero (sepDegree F E) := ⟨rank_pos.ne'⟩

instance instNeZeroInsepDegree : NeZero (insepDegree F E) := ⟨rank_pos.ne'⟩

instance instNeZeroFinInsepDegree [FiniteDimensional F E] :
    NeZero (finInsepDegree F E) := ⟨finrank_pos.ne'⟩

/-- If `E` and `K` are isomorphic as `F`-algebras, then they have the same
separable degree over `F`. -/
theorem lift_sepDegree_eq_of_equiv (i : E ≃ₐ[F] K) :
    Cardinal.lift.{w} (sepDegree F E) = Cardinal.lift.{v} (sepDegree F K) :=
  i.separableClosure.toLinearEquiv.lift_rank_eq

/-- The same-universe version of `Field.lift_sepDegree_eq_of_equiv`. -/
theorem sepDegree_eq_of_equiv (K : Type v) [Field K] [Algebra F K] (i : E ≃ₐ[F] K) :
    sepDegree F E = sepDegree F K :=
  i.separableClosure.toLinearEquiv.rank_eq

/-- The separable degree multiplied by the inseparable degree is equal
to the (infinite) field extension degree. -/
theorem sepDegree_mul_insepDegree : sepDegree F E * insepDegree F E = Module.rank F E :=
  rank_mul_rank F (separableClosure F E) E

theorem sepDegree_le_rank : sepDegree F E ≤ Module.rank F E :=
  Module.rank_bot_le_rank_of_isScalarTower _ _ _

theorem insepDegree_le_rank : insepDegree F E ≤ Module.rank F E :=
  Module.rank_top_le_rank_of_isScalarTower _ _ _

/-- If `E` and `K` are isomorphic as `F`-algebras, then they have the same
inseparable degree over `F`. -/
theorem lift_insepDegree_eq_of_equiv (i : E ≃ₐ[F] K) :
    Cardinal.lift.{w} (insepDegree F E) = Cardinal.lift.{v} (insepDegree F K) :=
  Algebra.lift_rank_eq_of_equiv_equiv i.separableClosure i rfl

/-- The same-universe version of `Field.lift_insepDegree_eq_of_equiv`. -/
theorem insepDegree_eq_of_equiv (K : Type v) [Field K] [Algebra F K] (i : E ≃ₐ[F] K) :
    insepDegree F E = insepDegree F K :=
  Algebra.rank_eq_of_equiv_equiv i.separableClosure i rfl

/-- If `E` and `K` are isomorphic as `F`-algebras, then they have the same finite
inseparable degree over `F`. -/
theorem finInsepDegree_eq_of_equiv (i : E ≃ₐ[F] K) :
    finInsepDegree F E = finInsepDegree F K := by
  simpa only [Cardinal.toNat_lift] using congr_arg Cardinal.toNat
    (lift_insepDegree_eq_of_equiv F E K i)

@[simp]
theorem sepDegree_self : sepDegree F F = 1 := by
  rw [sepDegree, Subsingleton.elim (separableClosure F F) ⊥, IntermediateField.rank_bot]

@[simp]
theorem insepDegree_self : insepDegree F F = 1 := by
  rw [insepDegree, Subsingleton.elim (separableClosure F F) ⊤, IntermediateField.rank_top]

@[simp]
theorem finInsepDegree_self : finInsepDegree F F = 1 := by
  rw [finInsepDegree_def', insepDegree_self, Cardinal.one_toNat]

end Field

namespace IntermediateField

@[simp]
theorem sepDegree_bot : sepDegree F (⊥ : IntermediateField F E) = 1 := by
  have := lift_sepDegree_eq_of_equiv _ _ _ (botEquiv F E)
  rwa [sepDegree_self, Cardinal.lift_one, ← Cardinal.lift_one.{v, u}, Cardinal.lift_inj] at this

@[simp]
theorem insepDegree_bot : insepDegree F (⊥ : IntermediateField F E) = 1 := by
  have := lift_insepDegree_eq_of_equiv _ _ _ (botEquiv F E)
  rwa [insepDegree_self, Cardinal.lift_one, ← Cardinal.lift_one.{v, u}, Cardinal.lift_inj] at this

@[simp]
theorem finInsepDegree_bot : finInsepDegree F (⊥ : IntermediateField F E) = 1 := by
  rw [finInsepDegree_eq_of_equiv _ _ _ (botEquiv F E), finInsepDegree_self]

section Tower

variable [Algebra E K] [IsScalarTower F E K]

theorem lift_sepDegree_bot' : Cardinal.lift.{v} (sepDegree F (⊥ : IntermediateField E K)) =
    Cardinal.lift.{w} (sepDegree F E) :=
  lift_sepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

theorem lift_insepDegree_bot' : Cardinal.lift.{v} (insepDegree F (⊥ : IntermediateField E K)) =
    Cardinal.lift.{w} (insepDegree F E) :=
  lift_insepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

variable {F}

@[simp]
theorem finInsepDegree_bot' :
    finInsepDegree F (⊥ : IntermediateField E K) = finInsepDegree F E := by
  simpa only [Cardinal.toNat_lift] using congr_arg Cardinal.toNat (lift_insepDegree_bot' F E K)

@[simp]
theorem sepDegree_top : sepDegree F (⊤ : IntermediateField E K) = sepDegree F K :=
  sepDegree_eq_of_equiv _ _ _ ((topEquiv (F := E) (E := K)).restrictScalars F)

@[simp]
theorem insepDegree_top : insepDegree F (⊤ : IntermediateField E K) = insepDegree F K :=
  insepDegree_eq_of_equiv _ _ _ ((topEquiv (F := E) (E := K)).restrictScalars F)

@[simp]
theorem finInsepDegree_top : finInsepDegree F (⊤ : IntermediateField E K) = finInsepDegree F K := by
  rw [finInsepDegree_def', insepDegree_top, ← finInsepDegree_def']

variable (K : Type v) [Field K] [Algebra F K] [Algebra E K] [IsScalarTower F E K]

@[simp]
theorem sepDegree_bot' : sepDegree F (⊥ : IntermediateField E K) = sepDegree F E :=
  sepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

@[simp]
theorem insepDegree_bot' : insepDegree F (⊥ : IntermediateField E K) = insepDegree F E :=
  insepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

variable (F) in
lemma _root_.Field.insepDegree_top_le_insepDegree_of_isScalarTower :
    insepDegree E K ≤ insepDegree F K := by
  letI := (IntermediateField.inclusion (separableClosure.le_restrictScalars F E K)).toAlgebra
  have : IsScalarTower (separableClosure F K) ((separableClosure E K).restrictScalars F) K :=
    .of_algebraMap_eq' rfl
  exact Module.rank_top_le_rank_of_isScalarTower
    (separableClosure F K) ((separableClosure E K).restrictScalars F) K

variable {K} in
lemma _root_.Field.insepDegree_le_of_left_le {E₁ E₂ : IntermediateField F K} (H : E₁ ≤ E₂) :
    insepDegree E₂ K ≤ insepDegree E₁ K := by
  letI := (IntermediateField.inclusion H).toAlgebra
  have : IsScalarTower E₁ E₂ K := .of_algebraMap_eq' rfl
  exact insepDegree_top_le_insepDegree_of_isScalarTower _ _ _

variable (F) in
lemma _root_.Field.finInsepDegree_top_le_finInsepDegree_of_isScalarTower [Module.Finite F K] :
    finInsepDegree E K ≤ finInsepDegree F K := by
  letI := (IntermediateField.inclusion (separableClosure.le_restrictScalars F E K)).toAlgebra
  have : IsScalarTower (separableClosure F K) ((separableClosure E K).restrictScalars F) K :=
    .of_algebraMap_eq' rfl
  exact Module.finrank_top_le_finrank_of_isScalarTower
    (separableClosure F K) ((separableClosure E K).restrictScalars F) K

variable {K} in
lemma finInsepDegree_le_of_left_le {E₁ E₂ : IntermediateField F K} (H : E₁ ≤ E₂)
    [Module.Finite E₁ K] : finInsepDegree E₂ K ≤ finInsepDegree E₁ K := by
  letI := (IntermediateField.inclusion H).toAlgebra
  have : IsScalarTower E₁ E₂ K := .of_algebraMap_eq' rfl
  exact finInsepDegree_top_le_finInsepDegree_of_isScalarTower _ _ _

end Tower

end IntermediateField

/-- A separable extension has separable degree equal to degree. -/
theorem Algebra.IsSeparable.sepDegree_eq [Algebra.IsSeparable F E] :
    sepDegree F E = Module.rank F E := by
  rw [sepDegree, (separableClosure.eq_top_iff F E).2 ‹_›, IntermediateField.rank_top']

/-- A separable extension has inseparable degree one. -/
theorem Algebra.IsSeparable.insepDegree_eq [Algebra.IsSeparable F E] : insepDegree F E = 1 := by
  rw [insepDegree, (separableClosure.eq_top_iff F E).2 ‹_›, IntermediateField.rank_top]

/-- A separable extension has finite inseparable degree one. -/
theorem Algebra.IsSeparable.finInsepDegree_eq [Algebra.IsSeparable F E] : finInsepDegree F E = 1 :=
  Cardinal.one_toNat ▸ congr(Cardinal.toNat $(insepDegree_eq F E))
