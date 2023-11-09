/-
Copyright (c) 2023 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.NormalClosure
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.Polynomial.SeparableDegree

/-!

# Separable degree

This file contains basics about the separable degree of a field extension.

## Main definitions

- `Emb F E`: the type of `F`-algebra homomorphisms from `E` to the algebraic closure of `E`.

- `sepDegree F E`: the separable degree of an algebraic extension `E / F` of fields, defined to be
  the cardinal of `F`-algebra homomorphisms from `E` to the algebraic closure of `E`.
  (Mathematically, it should be the algebraic closure of `F`, but in order to make the type
  compatible with `Module.rank F E`, we use the algebraic closure of `E`.)
  Note that if `E / F` is not algebraic, then this definition makes no mathematical sense.

- `finSepDegree F E`: the separable degree of `E / F` as a natural number, which is zero if
  `sepDegree F E` is not finite.

## Main results

- `embEquivOfEquiv`: a random isomorphism between `Emb F E` and `Emb F E'` when `E` and `E'` are
  isomorphic as `F`-algebras.

- `sepDegree_eq_of_equiv`, `finSepDegree_eq_of_equiv`: if `E` and `E'` are isomorphic as
  `F`-algebras, then they have the same separable degree over `F`.

- `embEquivOfIsAlgClosed`: a random isomorphism between `Emb F E` and `E →ₐ[F] K` when `E / F`
  is algebraic and `K / F` is algebraically closed.

- `sepDegree_eq_of_isAlgClosed`, `finSepDegree_eq_of_isAlgClosed`: the separable degree of `E / F`
  is equal to the cardinality of `E →ₐ[F] K` when `E / F` is algebraic and `K / F` is
  algebraically closed.

## Tags

separable degree, degree, polynomial

## TODO

- ...

-/

open scoped Classical Polynomial

open FiniteDimensional Polynomial IntermediateField

noncomputable section

universe u v v' w

variable (F : Type u) (E : Type v) [Field F] [Field E]

variable [Algebra F E]

namespace Field

/-- `Emb F E` is the type of `F`-algebra homomorphisms from `E` to the algebraic closure of `E`.
-/
def Emb := E →ₐ[F] (AlgebraicClosure E)

/-- If `E / F` is an algebraic extension, then the separable degree of `E / F`
is the number of `F`-algebra homomorphisms from `E` to the algebraic closure of `E`.
Note that if `E / F` is not algebraic, then this definition makes no mathematical sense.
-/
def sepDegree := Cardinal.mk (Emb F E)

/-- The separable degree of `E / F` as a natural number. -/
def finSepDegree : ℕ := Cardinal.toNat (sepDegree F E)

lemma emb_nonempty : Nonempty (Emb F E) :=
  Nonempty.intro <| IsScalarTower.toAlgHom F E (AlgebraicClosure E)

lemma sepDegree_nezero : NeZero (sepDegree F E) :=
  NeZero.mk <| haveI := emb_nonempty F E; Cardinal.mk_ne_zero _

lemma finSepDegree_nezero_of_finiteDimensional [FiniteDimensional F E] :
    NeZero (finSepDegree F E) := NeZero.mk <| by
  haveI : Fintype (Emb F E) := minpoly.AlgHom.fintype _ _ _
  haveI := emb_nonempty F E
  simp only [finSepDegree, sepDegree, Cardinal.mk_toNat_eq_card]
  exact Fintype.card_ne_zero

/-- A random isomorphism between `Emb F E` and `Emb F E'` when `E` and `E'` are isomorphic
as `F`-algebras. -/
def embEquivOfEquiv (E' : Type v') [Field E'] [Algebra F E'] (i : E ≃ₐ[F] E') :
    Emb F E ≃ Emb F E' := AlgEquiv.arrowCongr i <| AlgEquiv.symm <| by
  letI : Algebra E E' := i.toAlgHom.toRingHom.toAlgebra
  apply AlgEquiv.restrictScalars (R := F) (S := E)
  apply IsAlgClosure.equivOfAlgebraic E E' (AlgebraicClosure E') (AlgebraicClosure E)
  intro x
  have h := isAlgebraic_algebraMap (R := E) (A := E') (i.symm.toAlgHom x)
  rw [show ∀ y : E, (algebraMap E E') y = i.toAlgHom y from fun y ↦ rfl] at h
  simpa only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, AlgEquiv.apply_symm_apply] using h

/-- If `E` and `E'` are isomorphic as `F`-algebras, then they have the same separable degree
over `F`. -/
theorem sepDegree_eq_of_equiv (E' : Type v') [Field E'] [Algebra F E'] (i : E ≃ₐ[F] E') :
    Cardinal.lift.{v'} (sepDegree F E) = Cardinal.lift.{v} (sepDegree F E') := by
  have := ((Equiv.ulift.{v'} (α := E →ₐ[F] (AlgebraicClosure E))).trans
    (embEquivOfEquiv F E E' i)).trans
      (Equiv.ulift.{v} (α := E' →ₐ[F] (AlgebraicClosure E'))).symm
  simpa only [Cardinal.mk_uLift] using this.cardinal_eq

/-- If `E` and `E'` are isomorphic as `F`-algebras, then they have the same `finSepDegree`
over `F`. -/
theorem finSepDegree_eq_of_equiv (E' : Type v') [Field E'] [Algebra F E'] (i : E ≃ₐ[F] E') :
    finSepDegree F E = finSepDegree F E' := by
  simpa only [Cardinal.toNat_lift] using congr_arg Cardinal.toNat
    (sepDegree_eq_of_equiv F E E' i)

@[simp]
theorem sepDegree_self : sepDegree F F = 1 :=
  le_antisymm
    (show sepDegree F F ≤ 1 from Cardinal.le_one_iff_subsingleton.2 AlgHom.subsingleton)
      (Cardinal.one_le_iff_ne_zero.2 (sepDegree_nezero F F).out)

@[simp]
theorem finSepDegree_self : finSepDegree F F = 1 := by
  simp only [finSepDegree, sepDegree_self, Cardinal.one_toNat]

@[simp]
theorem sepDegree_bot : sepDegree F (⊥ : IntermediateField F E) = 1 := by
  have := sepDegree_eq_of_equiv _ _ _ (IntermediateField.botEquiv F E)
  rwa [sepDegree_self, Cardinal.lift_one, ← Cardinal.lift_one.{u, v}, Cardinal.lift_inj] at this

@[simp]
theorem finSepDegree_bot : finSepDegree F (⊥ : IntermediateField F E) = 1 := by
  simp only [finSepDegree, sepDegree_bot, Cardinal.one_toNat]

@[simp]
theorem sepDegree_top : sepDegree F (⊤ : IntermediateField F E) = sepDegree F E := by
  simpa only [Cardinal.lift_id] using sepDegree_eq_of_equiv F _ E IntermediateField.topEquiv

@[simp]
theorem finSepDegree_top : finSepDegree F (⊤ : IntermediateField F E) = finSepDegree F E := by
  simp only [finSepDegree, sepDegree_top]

theorem sepDegree_bot' (K : Type w) [Field K] [Algebra F K] [Algebra E K]
    [IsScalarTower F E K] : Cardinal.lift.{v} (sepDegree F (⊥ : IntermediateField E K)) =
      Cardinal.lift.{w} (sepDegree F E) := by
  exact sepDegree_eq_of_equiv _ _ _ ((IntermediateField.botEquiv E K).restrictScalars F)

@[simp]
theorem sepDegree_bot'' (K : Type v) [Field K] [Algebra F K] [Algebra E K]
    [IsScalarTower F E K] : sepDegree F (⊥ : IntermediateField E K) = sepDegree F E := by
  simpa only [Cardinal.lift_id] using sepDegree_bot' F E K

@[simp]
theorem finSepDegree_bot' (K : Type w) [Field K] [Algebra F K] [Algebra E K]
    [IsScalarTower F E K] : finSepDegree F (⊥ : IntermediateField E K) = finSepDegree F E := by
  simpa only [Cardinal.toNat_lift] using congr_arg Cardinal.toNat (sepDegree_bot' F E K)

@[simp]
theorem sepDegree_top' (K : Type w) [Field K] [Algebra F K] [Algebra E K]
    [IsScalarTower F E K] : sepDegree F (⊤ : IntermediateField E K) = sepDegree F K := by
  simpa only [Cardinal.lift_id] using sepDegree_eq_of_equiv _ _ _
    ((IntermediateField.topEquiv (F := E) (E := K)).restrictScalars F)

@[simp]
theorem finSepDegree_top' (K : Type w) [Field K] [Algebra F K] [Algebra E K]
    [IsScalarTower F E K] : finSepDegree F (⊤ : IntermediateField E K) = finSepDegree F K := by
  simp only [finSepDegree, sepDegree_top']

-- TODO: simplify and remove the following things

section Adhoc

variable {F E}

private lemma test1 {K : Type w} [Field K] [Algebra F K] (i : E →ₐ[F] K) :
    i.comp (AlgEquiv.ofInjectiveField i).symm.toAlgHom = i.fieldRange.val := by
  ext x
  rw [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, AlgHom.coe_coe, Function.comp_apply,
    show i ((AlgEquiv.ofInjectiveField i).symm x) =
        (AlgEquiv.ofInjectiveField i) ((AlgEquiv.ofInjectiveField i).symm x) by
      rw [← AlgEquiv.ofInjective_apply i i.toRingHom.injective]; rfl,
    AlgEquiv.apply_symm_apply]
  rfl

private lemma test3 {K : Type w} [Field K] [Algebra F K] (i : E →ₐ[F] K) [IsAlgClosed E] :
    IsAlgClosed i.fieldRange := by
  constructor
  intro g
  have g_lifts : g ∈ lifts (AlgEquiv.ofInjectiveField i).toAlgHom.toRingHom := by
    refine g.lifts_iff_coeff_lifts.mpr fun n ↦ ?_
    exact AlgEquiv.surjective (AlgEquiv.ofInjectiveField i) (coeff g n)
  obtain ⟨p, hp⟩ := g_lifts
  simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.toRingHom_eq_coe, coe_mapRingHom] at hp
  rw [← hp, splits_map_iff]
  exact IsAlgClosed.splits_domain p

private lemma test4b (L L' : IntermediateField F E) :
    let L'' : IntermediateField L' E := adjoin L' (L : Set E)
    letI : Algebra L' L'' := Subalgebra.algebra L''.toSubalgebra
    (L ⊔ L' : IntermediateField F E) = restrictScalars F L'' := by
  simp only
  -- TODO: use `IntermediateField.adjoin_self` after it's merged
  have h_adjoin_self : ∀ K : IntermediateField F E, adjoin F {x | x ∈ K} = K :=
    fun K ↦ le_antisymm (adjoin_le_iff.2 fun _ ↦ id) (subset_adjoin F _)
  -- TODO: use `IntermediateField.restrictScalars_adjoin` after it's merged
  have h_restrictScalars_adjoin : ∀ (K : IntermediateField F E) (S : Set E),
      restrictScalars (K := F) (adjoin K S) = adjoin F ({x | x ∈ K} ∪ S) :=
    fun K S ↦ by rw [← h_adjoin_self K, adjoin_adjoin_left, h_adjoin_self K]
  have : L' ⊔ L = (adjoin F {x | x ∈ L'}) ⊔ (adjoin F {x | x ∈ L}) := by
    simp only [h_adjoin_self]
  rw [h_restrictScalars_adjoin L', sup_comm, this, ← gc.l_sup]
  rfl

private lemma test4a (L L' : IntermediateField F E) (halg : Algebra.IsAlgebraic F L) :
    let L'' : IntermediateField L' E := adjoin L' (L : Set E)
    letI : Algebra L' L'' := Subalgebra.algebra L''.toSubalgebra
    Algebra.IsAlgebraic L' L'' := by
  have h : ∀ x : L,
      letI : Algebra L' (adjoin L' {x.1}) := Subalgebra.algebra (adjoin L' {x.1}).toSubalgebra
      Algebra.IsAlgebraic L' (adjoin L' {x.1}) := fun x ↦ by
    letI : Algebra L' (adjoin L' {x.1}) := Subalgebra.algebra (adjoin L' {x.1}).toSubalgebra
    haveI := adjoin.finiteDimensional <| isAlgebraic_iff_isIntegral.mp <|
      isAlgebraic_of_larger_base L' <| isAlgebraic_iff.mp <| halg x
    exact Algebra.isAlgebraic_of_finite L' _
  have halg' := isAlgebraic_iSup h
  have := (gc (F := L') (E := E)).l_iSup (f := fun (x : L) ↦ {x.1})
  simp only [Set.iSup_eq_iUnion, Set.iUnion_singleton_eq_range, Subtype.range_coe_subtype] at this
  rwa [← this] at halg'

private lemma test4d (L : IntermediateField F E) (hsurj : Function.Surjective (algebraMap F L)) :
    L = ⊥ := eq_bot_iff.2 fun x hx ↦ mem_bot.2 <| by
  obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
  use y
  rw [IsScalarTower.algebraMap_apply F L E, congr_arg (algebraMap L E) hy]
  rfl

private lemma test4c (L L' : IntermediateField F E) (halg : Algebra.IsAlgebraic F L)
    [IsAlgClosed L'] :
    let L'' : IntermediateField L' E := adjoin L' (L : Set E)
    letI : Algebra L' L'' := Subalgebra.algebra L''.toSubalgebra
    L'' = ⊥ := by
  let L'' : IntermediateField L' E := adjoin L' (L : Set E)
  letI : Algebra L' L'' := Subalgebra.algebra L''.toSubalgebra
  exact test4d L'' <| IsAlgClosed.algebraMap_surjective_of_isAlgebraic <| test4a L L' halg

private lemma test40 (L L' : IntermediateField F E) (halg : Algebra.IsAlgebraic F L)
    [IsAlgClosed L'] : L ≤ L' := by
  apply le_of_sup_eq
  have := congr_arg (restrictScalars F) (test4c L L' halg)
  rwa [← test4b, restrictScalars_bot_eq_self] at this

private lemma test4 (halg : Algebra.IsAlgebraic F E)
    {K : Type w} [Field K] [Algebra F K] (i : E →ₐ[F] K)
    (E' : IntermediateField F K) [IsAlgClosed E'] : i.fieldRange ≤ E' := by
  apply test40 i.fieldRange E'
  rintro ⟨_, ⟨y, rfl⟩⟩
  exact isAlgebraic_algHom_of_isAlgebraic (AlgEquiv.ofInjectiveField i).toAlgHom (halg y)

private lemma test5 (halg : Algebra.IsAlgebraic F E)
    {E' : Type v'} [Field E'] [Algebra F E'] [IsAlgClosed E']
    {K : Type w} [Field K] [Algebra F K] (i : E →ₐ[F] K) (i' : E' →ₐ[F] K) :
    i.fieldRange ≤ i'.fieldRange := by
  haveI : IsAlgClosed i'.fieldRange := test3 i'
  exact test4 halg i i'.fieldRange

end Adhoc

/-- A random isomorphism between `Emb F E` and `E →ₐ[F] K` when `E / F` is algebraic
and `K / F` is algebraically closed. -/
-- TODO: use `AlgEquiv.arrowCongr` instead
-- TODO: `IsAlgClosed K` should be replaced by `∀ α : E, Splits (algebraMap F K) (minpoly F α)`
def embEquivOfIsAlgClosed (halg : Algebra.IsAlgebraic F E)
    (K : Type w) [Field K] [Algebra F K] [IsAlgClosed K] :
    Emb F E ≃ (E →ₐ[F] K) := by
  have hac := IsAlgClosure.ofAlgebraic F E (AlgebraicClosure E) halg
  let i := IsAlgClosed.lift (M := K) hac.algebraic
  have h2 : Function.Injective (i.comp (A := E)) := fun j j' h ↦ by
    apply_fun fun x ↦ (x : E → K) at h
    simp only [AlgHom.coe_comp] at h
    exact AlgHom.ext (congrFun (Function.Injective.comp_left i.injective h))
  let i' := AlgEquiv.ofInjectiveField i
  let toFun : (E →ₐ[F] (AlgebraicClosure E)) → (E →ₐ[F] K) :=
    fun f ↦ i.comp f
  let invFun : (E →ₐ[F] K) → (E →ₐ[F] (AlgebraicClosure E)) :=
    fun f ↦ i'.symm.toAlgHom.comp (IntermediateField.inclusion <|
      test5 halg f i) |>.comp f.rangeRestrict
  have right_inv : Function.RightInverse invFun toFun := fun f ↦ by
    simp only
    rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc, test1]
    rfl
  exact ⟨toFun, invFun, fun f ↦ h2 <| right_inv <| toFun f, right_inv⟩

/-- The separable degree of `E / F` is equal to the cardinality of `E →ₐ[F] K` when `E / F`
is algebraic and `K / F` is algebraically closed. -/
theorem sepDegree_eq_of_isAlgClosed (halg : Algebra.IsAlgebraic F E)
    (K : Type w) [Field K] [Algebra F K] [IsAlgClosed K] :
    Cardinal.lift.{w} (sepDegree F E) = Cardinal.mk (E →ₐ[F] K) := by
  simpa only [Cardinal.mk_uLift] using ((Equiv.ulift.{w} (α := Emb F E)).trans
    (embEquivOfIsAlgClosed F E halg K)).cardinal_eq

/-- The `finSepDegree F E` is equal to the cardinality of `E →ₐ[F] K` as a natural number,
when `E / F` is algebraic and `K / F` is algebraically closed. -/
theorem finSepDegree_eq_of_isAlgClosed (halg : Algebra.IsAlgebraic F E)
    (K : Type w) [Field K] [Algebra F K] [IsAlgClosed K] :
    finSepDegree F E = Cardinal.toNat (Cardinal.mk (E →ₐ[F] K)) := by
  simpa only [Cardinal.toNat_lift] using congr_arg Cardinal.toNat
    (sepDegree_eq_of_isAlgClosed F E halg K)

def algHomEquivNormalClosure (K : Type w) [Field K] [Algebra F K] :
    (E →ₐ[F] K) ≃ (E →ₐ[F] (normalClosure F E K)) :=
  ⟨fun f ↦ (IntermediateField.inclusion f.fieldRange_le_normalClosure) |>.comp
    (AlgEquiv.ofInjectiveField f).toAlgHom, normalClosure F E K |>.val.comp,
      fun _ ↦ rfl, fun _ ↦ rfl⟩

lemma test101 (K : Type w) [Field K] [Algebra F K]
    {S : Set E} (hS : adjoin F S = ⊤) :
    adjoin F (⨆ f : E →ₐ[F] K, f '' S) = normalClosure F E K := by
  simp only [normalClosure, gc.l_iSup]
  congr
  funext f
  rw [← adjoin_map, hS, AlgHom.fieldRange_eq_map]

lemma test102 (K : Type w) [Field K] [Algebra F K] {S : Set E} (hS : adjoin F S = ⊤)
    (hK : ∀ s ∈ S, IsIntegral F s ∧ Polynomial.Splits (algebraMap F K) (minpoly F s)) :
    ∀ s ∈ S, Polynomial.Splits (algebraMap F (normalClosure F E K)) (minpoly F s) := by
  intro s hs
  sorry

lemma normalClosure_isAlgebraic_of_adjoin_isIntegral' (K : Type w) [Field K] [Algebra F K]
    {S : Set E} (hS : adjoin F S = ⊤)
    (hK : ∀ s ∈ S, IsIntegral F s) :
    Algebra.IsAlgebraic F (normalClosure F E K) := by
  rw [← test101 F E K hS, gc.l_iSup]
  refine isAlgebraic_iSup (fun f ↦ ?_)
  have : f '' S = ⨆ x : { x // x ∈ f '' S }, {x.1} := by simp only [Set.iSup_eq_iUnion,
    Set.iUnion_singleton_eq_range, Subtype.range_coe_subtype, Set.setOf_mem_eq]
  rw [this, gc.l_iSup]
  refine isAlgebraic_iSup (fun y ↦ ?_)
  obtain ⟨x, hx, hy⟩ := (Set.mem_image f S _).1 y.2
  haveI := adjoin.finiteDimensional <| hy ▸ map_isIntegral f (hK x hx)
  exact Algebra.isAlgebraic_of_finite _ _

def normalClosureHomOfAdjoinSplits' (K : Type w) [Field K] [Algebra F K]
    (K' : Type v') [Field K'] [Algebra F K']
    {S : Set E} (hS : adjoin F S = ⊤)
    (hK : ∀ s ∈ S, IsIntegral F s ∧ Polynomial.Splits (algebraMap F K') (minpoly F s)) :
    (normalClosure F E K) →ₐ[F] (normalClosure F E K') := by
  refine (test101 F E K hS).symm ▸ Classical.choice (algHom_mk_adjoin_splits <| fun s hs ↦ ?_)
  simp only [Set.iSup_eq_iUnion, Set.mem_iUnion, Set.mem_image] at hs
  obtain ⟨f, x, hx, rfl⟩ := hs
  rw [minpoly.algHom_eq f f.injective x]
  exact ⟨map_isIntegral f (hK x hx).1, test102 F E K' hS hK x hx⟩

def normalClosureEquivOfAdjoinSplits' (K : Type w) [Field K] [Algebra F K]
    (K' : Type v') [Field K'] [Algebra F K']
    {S : Set E} (hS : adjoin F S = ⊤)
    (hK : ∀ s ∈ S, IsIntegral F s ∧ Polynomial.Splits (algebraMap F K) (minpoly F s) ∧
      Polynomial.Splits (algebraMap F K') (minpoly F s)) :
    (normalClosure F E K) ≃ₐ[F] (normalClosure F E K') := by
  refine AlgEquiv.ofBijective _ (Algebra.IsAlgebraic.algHom_bijective₂ ?_ ?_ ?_).1
  · exact normalClosure_isAlgebraic_of_adjoin_isIntegral' F E K hS <| fun s hs ↦ (hK s hs).1
  · exact normalClosureHomOfAdjoinSplits' F E K K' hS <| fun s hs ↦ ⟨(hK s hs).1, (hK s hs).2.2⟩
  · exact normalClosureHomOfAdjoinSplits' F E K' K hS <| fun s hs ↦ ⟨(hK s hs).1, (hK s hs).2.1⟩

def embEquivOfAdjoinSplits' (K : Type w) [Field K] [Algebra F K] {S : Set E}
    (hS : adjoin F S = ⊤)
    (hK : ∀ s ∈ S, IsIntegral F s ∧ Polynomial.Splits (algebraMap F K) (minpoly F s)) :
    Emb F E ≃ (E →ₐ[F] K) :=
  algHomEquivNormalClosure F E (AlgebraicClosure E) |>.trans
    (AlgEquiv.arrowCongr (@AlgEquiv.refl F E _ _ _) <|
      normalClosureEquivOfAdjoinSplits' F E (AlgebraicClosure E) K hS <|
        fun s hs ↦ ⟨(hK s hs).1, IsAlgClosed.splits_codomain _, (hK s hs).2⟩) |>.trans
          (algHomEquivNormalClosure F E K).symm
  -- let L := normalClosure F E (AlgebraicClosure E)
  -- let S' : Set (AlgebraicClosure E) := ⨆ f : E →ₐ[F] (AlgebraicClosure E), f '' S
  -- have hK : ∀ s ∈ S', IsIntegral F s ∧ Polynomial.Splits (algebraMap F K) (minpoly F s) := by
  --   intro s hs
  --   simp only [Set.iSup_eq_iUnion, Set.mem_iUnion, Set.mem_image] at hs
  --   obtain ⟨f, x, hx, rfl⟩ := hs
  --   exact ⟨map_isIntegral f (hK x hx).1,  (minpoly.algHom_eq f f.injective x).symm ▸ (hK x hx).2⟩
  -- have hL : adjoin F S' = L := by
  --   simp only [normalClosure, gc.l_iSup]
  --   congr
  --   funext f
  --   rw [← adjoin_map, hS, AlgHom.fieldRange_eq_map]
  -- have i : L →ₐ[F] K := hL ▸ Classical.choice (algHom_mk_adjoin_splits hK)
  -- let L' := normalClosure F E K
  -- let i : L ≃ₐ[F] L' := normalClosureEquivOfAdjoinSplits' F E (AlgebraicClosure E) K hS <|
  --  fun s hs ↦ ⟨(hK s hs).1, IsAlgClosed.splits_codomain _, (hK s hs).2⟩
  -- have h2 : Function.Injective (i.comp (A := E)) := fun j j' h ↦ by
  --   apply_fun fun x ↦ (x : E → K) at h
  --   simp only [AlgHom.coe_comp] at h
  --   exact AlgHom.ext (congrFun (Function.Injective.comp_left i.injective h))

end Field
