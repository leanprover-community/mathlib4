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
  Usually denoted by $\operatorname{Emb}_F(E)$ in textbooks.

- `sepDegree F E`: the separable degree $[E:F]_s$ of an algebraic extension `E / F` of fields,
  defined to be the cardinal of `F`-algebra homomorphisms from `E` to the algebraic closure of `E`.
  (Mathematically, it should be the algebraic closure of `F`, but in order to make the type
  compatible with `Module.rank F E`, we use the algebraic closure of `E`.)
  Note that if `E / F` is not algebraic, then this definition makes no mathematical sense.

- `finSepDegree F E`: the separable degree $[E:F]_s$ of `E / F` as a natural number, which is zero
  if `sepDegree F E` is not finite.

## Main results

- `embEquivOfEquiv`, `sepDegree_eq_of_equiv`, `finSepDegree_eq_of_equiv`: a random isomorphism
  between `Emb F E` and `Emb F E'` when `E` and `E'` are isomorphic as `F`-algebras.
  In particular, they have the same cardinality (so `sepDegree` and `finSepDegree` are equal).

- `embEquivOfAdjoinSplits'`, `sepDegree_eq_of_adjoin_splits'`, `finSepDegree_eq_of_adjoin_splits'`:
  a random isomorphism between `Emb F E` and `E →ₐ[F] K` if `E = F(S)` such that every element
  `s` of `S` is integral (= algebraic) over `F` and whose minimal polynomial splits in `K`.
  In particular, they have the same cardinality.

- `embEquivOfIsAlgClosed`, `sepDegree_eq_of_isAlgClosed`, `finSepDegree_eq_of_isAlgClosed`:
  a random isomorphism between `Emb F E` and `E →ₐ[F] K` when `E / F`
  is algebraic and `K / F` is algebraically closed.
  In particular, they have the same cardinality.

- `embMulEmbOfIsAlgebraic`, `lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`,
  `sepDegree_mul_sepDegree_of_isAlgebraic`, `finSepDegree_mul_finSepDegree_of_isAlgebraic`:
  if `K / E / F` is a field extension tower, such that `K / E` is algebraic,
  then there is a non-canonical isomorphism `(Emb F E) × (Emb E K) ≃ (Emb F K)`.
  In particular, the separable degree satisfies the tower law: $[E:F]_s [K:E]_s = [K:F]_s$
  (see `lift_rank_mul_lift_rank`).

## Tags

separable degree, degree, polynomial

## TODO

- If `E / F` is a finite extension, then $[E:F]_s \mid [E:F]$. Thus we can define the inseparable
  degree $[E:F]_i$ to be $[E:F]$ divided by $[E:F]_s$.

- Define the separable degree of a polynomial over a field to be the number of distinct roots
  in algebraic closure, and prove that it's equal to `Polynomial.HasSeparableContraction.degree`.

- If `a` is an element algebraic over `F`, then $[F(a):F]_s$ is equal to the separable degree of
  the minimal polynomial of `a` over `F`. In particular, `a` is separable over `F` if and only if
  $[F(a):F]_s = [F(a):F]$.

- If `E / F` is a finite extension, then $[E:F]_s = [E:F]$ if and only if every element of `E` is
  separable over `F`, namely, `E / F` is a separable extension.

- As a corollary, if `S` is a subset of `E` consisting of separable elements, then `F(S) / F` is a
  separable extension.

- Define maximal separable subextension (or called relative separable closure)
  `separableClosure F E : IntermediateField F E` of `E / F`, and prove that its degree over `F`
  is $[E:F]_s$ if `E / F` is finite.

- Prove that `separableClosure F (AlgebraicClosure F)` is a separable closure of `F`.

- Prove that `[E:F]_s = 1` if and only if `E / F` is purely inseparable.

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
  have := (Equiv.ulift.{v'} (α := Emb F E)).trans
    (embEquivOfEquiv F E E' i) |>.trans
      (Equiv.ulift.{v} (α := Emb F E')).symm |>.cardinal_eq
  simpa only [Cardinal.mk_uLift] using this

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

/-- If `E = F(S)`, then the normal closure of `E / F` in `K` is generated by the images of `S`
under all `F`-algebra maps from `E` to `K`. -/
lemma normalClosure_eq_adjoin' (K : Type w) [Field K] [Algebra F K]
    {S : Set E} (hS : adjoin F S = ⊤) :
    normalClosure F E K = adjoin F (⨆ f : E →ₐ[F] K, f '' S) := by
  simp only [normalClosure, gc.l_iSup]
  congr
  funext f
  rw [← adjoin_map, hS, AlgHom.fieldRange_eq_map]

/-- If `E = F(S)` such that every element `s` of `S` is integral (= algebraic) over `F` and whose
minimal polynomial splits in `K`, then it also splits in the normal closure of `E / F` in `K`,
which is a field smaller than `K`. -/
lemma splits_in_normalClosure_of_adjoin_splits'
    (K : Type w) [Field K] [Algebra F K] {S : Set E} (hS : adjoin F S = ⊤)
    (hK : ∀ s ∈ S, IsIntegral F s ∧ Polynomial.Splits (algebraMap F K) (minpoly F s)) :
    ∀ s ∈ S, Polynomial.Splits (algebraMap F (normalClosure F E K)) (minpoly F s) := by
  intro s hs
  have hcomp : algebraMap F K = (algebraMap (normalClosure F E K) K).comp
    (algebraMap F (normalClosure F E K)) := rfl
  refine splits_of_comp _ _ (hcomp ▸ (hK s hs).2) <| fun a ha ↦ ?_
  rw [← hcomp] at ha
  let a' : { x // x ∈ (minpoly F s).aroots K } := ⟨a, ha⟩
  let f : F⟮s⟯ →ₐ[F] K := (algHomAdjoinIntegralEquiv F (hK s hs).1).symm a'
  have hf : f (AdjoinSimple.gen F s) = a :=
    algHomAdjoinIntegralEquiv_symm_apply_gen F (hK s hs).1 a'
  obtain ⟨φ, hφ⟩ := exists_algHom_of_adjoin_splits hK f hS
  have : a ∈ φ.fieldRange := by
    use s
    rw [← hf, ← hφ]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AdjoinSimple.gen, AlgHom.coe_comp,
      coe_val, Function.comp_apply]
  exact RingHom.mem_range.2 ⟨⟨a, φ.fieldRange_le_normalClosure this⟩, rfl⟩

/-- If `E = F(S)` such that every element `s` of `S` is integral (= algebraic) over `F`
(namely, if `E / F` is algebraic), then the normal closure of `E / F` in any field `K`
is also algebraic over `F`. -/
lemma normalClosure_isAlgebraic_of_adjoin_isIntegral' (K : Type w) [Field K] [Algebra F K]
    {S : Set E} (hS : adjoin F S = ⊤)
    (hK : ∀ s ∈ S, IsIntegral F s) :
    Algebra.IsAlgebraic F (normalClosure F E K) := by
  rw [normalClosure_eq_adjoin' F E K hS, gc.l_iSup]
  refine isAlgebraic_iSup (fun f ↦ ?_)
  have : f '' S = ⨆ x : { x // x ∈ f '' S }, {x.1} := by simp only [Set.iSup_eq_iUnion,
    Set.iUnion_singleton_eq_range, Subtype.range_coe_subtype, Set.setOf_mem_eq]
  rw [this, gc.l_iSup]
  refine isAlgebraic_iSup (fun y ↦ ?_)
  obtain ⟨x, hx, hy⟩ := (Set.mem_image f S _).1 y.2
  haveI := adjoin.finiteDimensional <| hy ▸ map_isIntegral f (hK x hx)
  exact Algebra.isAlgebraic_of_finite _ _

/-- The standard isomorphism between `E →ₐ[F] K` and `E →ₐ[F] (normalClosure F E K)`. -/
def algHomEquivNormalClosure (K : Type w) [Field K] [Algebra F K] :
    (E →ₐ[F] K) ≃ (E →ₐ[F] (normalClosure F E K)) :=
  ⟨fun f ↦ (IntermediateField.inclusion f.fieldRange_le_normalClosure) |>.comp
    (AlgEquiv.ofInjectiveField f).toAlgHom, normalClosure F E K |>.val.comp,
      fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- A random `F`-algebra map between the normal closure of `E / F` in `K` and in `K'`
if `E = F(S)` such that every element `s` of `S` is integral (= algebraic) over `F` and whose
minimal polynomial splits in `K'`. -/
def normalClosureHomOfAdjoinSplits' (K : Type w) [Field K] [Algebra F K]
    (K' : Type v') [Field K'] [Algebra F K']
    {S : Set E} (hS : adjoin F S = ⊤)
    (hK : ∀ s ∈ S, IsIntegral F s ∧ Polynomial.Splits (algebraMap F K') (minpoly F s)) :
    (normalClosure F E K) →ₐ[F] (normalClosure F E K') := by
  refine (normalClosure_eq_adjoin' F E K hS) ▸
    Classical.choice (nonempty_algHom_adjoin_of_splits <| fun s hs ↦ ?_)
  simp only [Set.iSup_eq_iUnion, Set.mem_iUnion, Set.mem_image] at hs
  obtain ⟨f, x, hx, rfl⟩ := hs
  rw [minpoly.algHom_eq f f.injective x]
  exact ⟨map_isIntegral f (hK x hx).1, splits_in_normalClosure_of_adjoin_splits' F E K' hS hK x hx⟩

/-- A random isomorphism between the normal closure of `E / F` in `K` and in `K'`
if `E = F(S)` such that every element `s` of `S` is integral (= algebraic) over `F` and whose
minimal polynomial splits in `K` and in `K'`. -/
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

/-- A random isomorphism between `Emb F E` and `E →ₐ[F] K` if `E = F(S)` such that every element
`s` of `S` is integral (= algebraic) over `F` and whose minimal polynomial splits in `K`.
Combined with `emb_nonempty`, it can be viewed as a stronger version of
`IntermediateField.algHom_mk_adjoin_splits'`. -/
def embEquivOfAdjoinSplits' (K : Type w) [Field K] [Algebra F K] {S : Set E}
    (hS : adjoin F S = ⊤)
    (hK : ∀ s ∈ S, IsIntegral F s ∧ Polynomial.Splits (algebraMap F K) (minpoly F s)) :
    Emb F E ≃ (E →ₐ[F] K) :=
  algHomEquivNormalClosure F E (AlgebraicClosure E) |>.trans
    (AlgEquiv.arrowCongr (@AlgEquiv.refl F E _ _ _) <|
      normalClosureEquivOfAdjoinSplits' F E (AlgebraicClosure E) K hS <|
        fun s hs ↦ ⟨(hK s hs).1, IsAlgClosed.splits_codomain _, (hK s hs).2⟩) |>.trans
          (algHomEquivNormalClosure F E K).symm

/-- The separable degree of `E / F` is equal to the cardinality of `E →ₐ[F] K`
if `E = F(S)` such that every element
`s` of `S` is integral (= algebraic) over `F` and whose minimal polynomial splits in `K`. -/
theorem sepDegree_eq_of_adjoin_splits'  (K : Type w) [Field K] [Algebra F K] {S : Set E}
    (hS : adjoin F S = ⊤)
    (hK : ∀ s ∈ S, IsIntegral F s ∧ Polynomial.Splits (algebraMap F K) (minpoly F s)) :
    Cardinal.lift.{w} (sepDegree F E) = Cardinal.mk (E →ₐ[F] K) := by
  simpa only [Cardinal.mk_uLift] using (Equiv.ulift.{w} (α := Emb F E)).trans
    (embEquivOfAdjoinSplits' F E K hS hK) |>.cardinal_eq

/-- The `finSepDegree F E` is equal to the cardinality of `E →ₐ[F] K`
if `E = F(S)` such that every element
`s` of `S` is integral (= algebraic) over `F` and whose minimal polynomial splits in `K`. -/
theorem finSepDegree_eq_of_adjoin_splits'  (K : Type w) [Field K] [Algebra F K] {S : Set E}
    (hS : adjoin F S = ⊤)
    (hK : ∀ s ∈ S, IsIntegral F s ∧ Polynomial.Splits (algebraMap F K) (minpoly F s)) :
    finSepDegree F E = Cardinal.toNat (Cardinal.mk (E →ₐ[F] K)) := by
  simpa only [Cardinal.toNat_lift] using congr_arg Cardinal.toNat
    (sepDegree_eq_of_adjoin_splits' F E K hS hK)

/-- A random isomorphism between `Emb F E` and `E →ₐ[F] K` when `E / F` is algebraic
and `K / F` is algebraically closed. -/
def embEquivOfIsAlgClosed (halg : Algebra.IsAlgebraic F E)
    (K : Type w) [Field K] [Algebra F K] [IsAlgClosed K] :
    Emb F E ≃ (E →ₐ[F] K) :=
  embEquivOfAdjoinSplits' F E K (adjoin_univ F E) <| fun s _ ↦
    ⟨isAlgebraic_iff_isIntegral.1 (halg s), IsAlgClosed.splits_codomain _⟩

/-- The separable degree of `E / F` is equal to the cardinality of `E →ₐ[F] K` when `E / F`
is algebraic and `K / F` is algebraically closed. -/
theorem sepDegree_eq_of_isAlgClosed (halg : Algebra.IsAlgebraic F E)
    (K : Type w) [Field K] [Algebra F K] [IsAlgClosed K] :
    Cardinal.lift.{w} (sepDegree F E) = Cardinal.mk (E →ₐ[F] K) := by
  simpa only [Cardinal.mk_uLift] using (Equiv.ulift.{w} (α := Emb F E)).trans
    (embEquivOfIsAlgClosed F E halg K) |>.cardinal_eq

/-- The `finSepDegree F E` is equal to the cardinality of `E →ₐ[F] K` as a natural number,
when `E / F` is algebraic and `K / F` is algebraically closed. -/
theorem finSepDegree_eq_of_isAlgClosed (halg : Algebra.IsAlgebraic F E)
    (K : Type w) [Field K] [Algebra F K] [IsAlgClosed K] :
    finSepDegree F E = Cardinal.toNat (Cardinal.mk (E →ₐ[F] K)) := by
  simpa only [Cardinal.toNat_lift] using congr_arg Cardinal.toNat
    (sepDegree_eq_of_isAlgClosed F E halg K)

/-- If `K / E / F` is a field extension tower, such that `K / E` is algebraic,
then there is a non-canonical isomorphism
`(Emb F E) × (Emb E K) ≃ (Emb F K)`. A corollary of `algHomEquivSigma`. -/
def embMulEmbOfIsAlgebraic
    (K : Type w) [Field K] [Algebra F K] [Algebra E K]
    [IsScalarTower F E K] (halg : Algebra.IsAlgebraic E K) :
    (Emb F E) × (Emb E K) ≃ (Emb F K) :=
  let e : ∀ f : E →ₐ[F] (AlgebraicClosure K), (@AlgHom E K (AlgebraicClosure K) _ _ _ _
      f.toRingHom.toAlgebra) ≃ (Emb E K) := fun f ↦
    (@embEquivOfIsAlgClosed E K _ _ _ halg (AlgebraicClosure K) _ f.toRingHom.toAlgebra _).symm
  (algHomEquivSigma (A := F) (B := E) (C := K) (D := AlgebraicClosure K) |>.trans
    (Equiv.sigmaEquivProdOfEquiv e) |>.trans <| Equiv.prodCongrLeft <|
      fun _ : Emb E K ↦ AlgEquiv.arrowCongr (@AlgEquiv.refl F E _ _ _) <|
        (IsAlgClosure.equivOfAlgebraic E K (AlgebraicClosure K) (AlgebraicClosure E)
          halg).restrictScalars F).symm

/-- If `K / E / F` is a field extension tower, such that `K / E` is algebraic, then
$[E:F]_s [K:E]_s = [K:F]_s$. See also `lift_rank_mul_lift_rank`. -/
theorem lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic
    (K : Type w) [Field K] [Algebra F K] [Algebra E K]
    [IsScalarTower F E K] (halg : Algebra.IsAlgebraic E K) :
    Cardinal.lift.{w} (sepDegree F E) * Cardinal.lift.{v} (sepDegree E K) =
      Cardinal.lift.{v} (sepDegree F K) := by
  have := (embMulEmbOfIsAlgebraic F E K halg).trans
    (Equiv.ulift.{v} (α := Emb F K)).symm |>.cardinal_eq
  simpa only [Cardinal.mk_prod, Cardinal.mk_uLift] using this

/-- The same-universe version of `lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`.
See also `rank_mul_rank`. -/
theorem sepDegree_mul_sepDegree_of_isAlgebraic
    (A : Type u) (B : Type u) [Field A] [Field B] [Algebra A B]
    (C : Type u) [Field C] [Algebra A C] [Algebra B C]
    [IsScalarTower A B C] (halg : Algebra.IsAlgebraic B C) :
    (sepDegree A B) * (sepDegree B C) = (sepDegree A C) := by
  simpa only [Cardinal.lift_id] using lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic A B C halg

/-- The `finSepDegree` version of `lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`.
See also `FiniteDimensional.finrank_mul_finrank'`. -/
theorem finSepDegree_mul_finSepDegree_of_isAlgebraic
    (K : Type w) [Field K] [Algebra F K] [Algebra E K]
    [IsScalarTower F E K] (halg : Algebra.IsAlgebraic E K) :
    finSepDegree F E * finSepDegree E K = finSepDegree F K := by
  simpa only [Cardinal.toNat_mul, Cardinal.toNat_lift] using congr_arg Cardinal.toNat
    (lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic F E K halg)

end Field
