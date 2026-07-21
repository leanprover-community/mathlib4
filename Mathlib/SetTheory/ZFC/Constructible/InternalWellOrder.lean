/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Delta0Godel
public import Mathlib.SetTheory.ZFC.Constructible.Choice

/-!
# Internal well-orders and Choice in the constructible universe

An external Lean relation is not enough to prove Choice inside `L`: its graph
must itself be represented by a constructible set.  This file isolates that
requirement.  A constructible set `r` represents the relation
`x <_r y` when the Kuratowski pair `⟨x,y⟩` belongs to `r`.

We prove that if every constructible set is well-orderable by such a
constructible graph, then `L` satisfies the disjoint-family form of Choice and
hence Mathlib's canonical first-order theory ZFC. The proposition
`ModelsInternalWellOrdering` is the interface used to derive these results.
-/

@[expose] public section

open Set

universe u

namespace Constructible

namespace Delta0Formula

/-! ## Bounded absoluteness for the proper class `L` -/

/--
Bounded formulas are absolute between the transitive class `L` and the
ambient `ZFSet` universe.  The left side uses subtype-valued assignments; the
right side forgets the constructibility proofs.
-/
theorem satisfies_lCarrier_absolute {n : Nat} (phi : Delta0Formula n)
    (s : Tuple Model.LCarrier.{u} n) :
    Satisfies
        (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1) phi s ↔
      Satisfies ZFMem phi (fun i => (s i).1) := by
  induction phi with
  | mem i j => rfl
  | eq i j =>
      change s i = s j ↔ (s i).1 = (s j).1
      exact Subtype.coe_injective.eq_iff.symm
  | neg phi ih => simp only [Satisfies, ih]
  | conj phi psi ihPhi ihPsi =>
      simp only [Satisfies, ihPhi, ihPsi]
  | boundedEx i phi ih =>
      constructor
      · rintro ⟨x, hx, hphi⟩
        refine ⟨x.1, hx, ?_⟩
        have habs := (ih (snoc s x)).mp hphi
        simpa only [Model.subtypeVal_snoc] using habs
      · rintro ⟨x, hx, hphi⟩
        let xL : Model.LCarrier.{u} :=
          ⟨x, mem_L_of_mem hx (s i).2⟩
        refine ⟨xL, hx, ?_⟩
        apply (ih (snoc s xL)).mpr
        simpa only [Model.subtypeVal_snoc, xL] using hphi

/-- The same absoluteness statement after translation to `FOFormula`. -/
theorem satisfies_toFO_lCarrier_absolute {n : Nat}
    (phi : Delta0Formula n) (s : Tuple Model.LCarrier.{u} n) :
    FOFormula.Satisfies
        (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1) phi.toFO s ↔
      FOFormula.Satisfies ZFMem phi.toFO (fun i => (s i).1) := by
  rw [satisfies_toFO, satisfies_toFO, satisfies_lCarrier_absolute]

end Delta0Formula

namespace Model

/-! ## Relations represented by constructible graphs -/

/-- The relation represented by a constructible set of Kuratowski pairs. -/
def GraphRel (r x y : LCarrier.{u}) : Prop :=
  ZFSet.pair x.1 y.1 ∈ r.1

/-- The carrier of an internal set, still retaining constructibility proofs. -/
abbrev InternalCarrier (a : LCarrier.{u}) :=
  {x : LCarrier.{u} // x.1 ∈ a.1}

/-- The graph relation restricted to the elements of `a`. -/
def graphRelOn (r a : LCarrier.{u}) :
    InternalCarrier a -> InternalCarrier a -> Prop :=
  fun x y => GraphRel r x.1 y.1

/-- `r ∈ L` represents a genuine well-order of the elements of `a`. -/
def InternallyWellOrders (r a : LCarrier.{u}) : Prop :=
  IsWellOrder (InternalCarrier a) (graphRelOn r a)

/-- Every internal set has a well-order whose relation graph also belongs to `L`. -/
def ModelsInternalWellOrdering : Prop :=
  forall a : LCarrier.{u}, exists r : LCarrier.{u},
    InternallyWellOrders r a

/-! ## The object-language graph predicate -/

/--
With assignment `![r,x,y]`, this bounded formula says that the Kuratowski pair
`⟨x,y⟩` belongs to `r`.
-/
def graphRelDelta0 : Delta0Formula 3 :=
  .boundedEx (0 : Fin 3)
    (Delta0Formula.kuratowskiPairEqAt
      (Fin.last 3) (1 : Fin 3).castSucc (2 : Fin 3).castSucc)

/-- The graph predicate in the unrestricted syntax used by Separation. -/
def graphRelFormula : FOFormula 3 :=
  graphRelDelta0.toFO

@[simp]
theorem satisfies_graphRelFormula (s : Tuple LCarrier.{u} 3) :
    FOFormula.Satisfies
        (fun x y : LCarrier.{u} => x.1 ∈ y.1)
        graphRelFormula s ↔
      GraphRel (s 0) (s 1) (s 2) := by
  rw [graphRelFormula,
    Delta0Formula.satisfies_toFO_lCarrier_absolute]
  simp only [Delta0Formula.satisfies_toFO, graphRelDelta0,
    Delta0Formula.Satisfies,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc, GraphRel]
  constructor
  · rintro ⟨q, hqr, hq⟩
    simpa [hq] using hqr
  · intro hpair
    exact ⟨ZFSet.pair (s 1).1 (s 2).1, hpair, rfl⟩

/-- Select `[r,z,y]` from the context `[a,r,y,x,z]`. -/
def graphMinimumRename : Fin 3 -> Fin 5 :=
  ![(1 : Fin 3).castSucc.castSucc,
    Fin.last 4,
    (2 : Fin 3).castSucc.castSucc]

theorem comp_graphMinimumRename {A : Type u}
    (s : Tuple A 3) (x z : A) :
    (fun i => snoc (snoc s x) z (graphMinimumRename i)) =
      ![s 1, z, s 2] := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change snoc (snoc s x) z ((1 : Fin 3).castSucc.castSucc) = s 1
    simp only [snoc_castSucc]
  · refine Fin.cases ?_ (fun k => ?_) j
    · change snoc (snoc s x) z (Fin.last 4) = z
      exact snoc_last _ _
    · refine Fin.cases ?_ (fun l => Fin.elim0 l) k
      change snoc (snoc s x) z ((2 : Fin 3).castSucc.castSucc) = s 2
      simp only [snoc_castSucc]

/--
With assignment `![a,r,y]`, this says that `y` is an `r`-least member of
some member of the family `a`.
-/
def graphLeastMemberPredicate : FOFormula 3 :=
  .ex
    (.conj
      (.mem (Fin.last 3) (0 : Fin 3).castSucc)
      (.conj
        (.mem (2 : Fin 3).castSucc (Fin.last 3))
        (.all
          (FOFormula.imp
            (.mem (Fin.last 4) (Fin.last 3).castSucc)
            (.neg
              (FOFormula.rename graphMinimumRename graphRelFormula))))))

@[simp]
theorem satisfies_graphLeastMemberPredicate (s : Tuple LCarrier.{u} 3) :
    FOFormula.Satisfies
        (fun x y : LCarrier.{u} => x.1 ∈ y.1)
        graphLeastMemberPredicate s ↔
      exists x : LCarrier.{u},
        x.1 ∈ (s 0).1 /\ (s 2).1 ∈ x.1 /\
          forall z : LCarrier.{u}, z.1 ∈ x.1 ->
            Not (GraphRel (s 1) z (s 2)) := by
  simp only [graphLeastMemberPredicate, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    FOFormula.satisfies_rename, snoc_last, snoc_castSucc,
    comp_graphMinimumRename, satisfies_graphRelFormula]
  simp

/-! ## Unique minima from an internal well-order -/

/-- Every nonempty subset of an internally well-ordered set has a unique minimum. -/
theorem exists_unique_graph_minimum {a r x : LCarrier.{u}}
    (hwo : InternallyWellOrders r a)
    (hxsub : forall z : LCarrier.{u}, z.1 ∈ x.1 -> z.1 ∈ a.1)
    (hxne : exists z : LCarrier.{u}, z.1 ∈ x.1) :
    exists y : LCarrier.{u},
      (y.1 ∈ x.1 /\
        forall z : LCarrier.{u}, z.1 ∈ x.1 -> Not (GraphRel r z y)) /\
      forall y' : LCarrier.{u},
        (y'.1 ∈ x.1 /\
          forall z : LCarrier.{u}, z.1 ∈ x.1 ->
            Not (GraphRel r z y')) ->
        y' = y := by
  let candidates : Set (InternalCarrier a) :=
    {z | z.1.1 ∈ x.1}
  have hcandidates : candidates.Nonempty := by
    rcases hxne with ⟨z, hzx⟩
    exact ⟨⟨z, hxsub z hzx⟩, hzx⟩
  letI : IsWellOrder (InternalCarrier a) (graphRelOn r a) := hwo
  let minimum : InternalCarrier a :=
    (IsWellFounded.wf : WellFounded (graphRelOn r a)).min
      candidates hcandidates
  have hminimumMem : minimum ∈ candidates :=
    (IsWellFounded.wf : WellFounded (graphRelOn r a)).min_mem
      candidates hcandidates
  have hminimum : forall z : LCarrier.{u}, z.1 ∈ x.1 ->
      Not (GraphRel r z minimum.1) := by
    intro z hzx hzlt
    let za : InternalCarrier a := ⟨z, hxsub z hzx⟩
    exact
      (IsWellFounded.wf : WellFounded (graphRelOn r a)).not_lt_min
        candidates (show za ∈ candidates from hzx) hzlt
  refine ⟨minimum.1, ⟨hminimumMem, hminimum⟩, ?_⟩
  · intro y' hy'
    let y'a : InternalCarrier a := ⟨y', hxsub y' hy'.1⟩
    rcases trichotomous_of (graphRelOn r a) y'a minimum with
      hy'lt | heq | hminlt
    · exact False.elim (hminimum y' hy'.1 hy'lt)
    · exact congrArg (fun z : InternalCarrier a => z.1) heq
    · exact False.elim (hy'.2 minimum.1 hminimumMem hminlt)

/-! ## Choice and ZFC -/

/-- Internal well-ordering of every constructible set implies Choice in `L`. -/
theorem lCarrier_modelsChoice_of_internalWellOrdering
    (hwo : ModelsInternalWellOrdering.{u}) :
    FirstOrder.SetTheory.ModelsChoice LCarrier.{u} := by
  intro family hnonempty hdisjoint
  let unionFamily : LCarrier.{u} := sUnionLCarrier family
  rcases hwo unionFamily with ⟨r, hr⟩
  have hmin : forall x : LCarrier.{u}, x.1 ∈ family.1 ->
      (exists y : LCarrier.{u}, y.1 ∈ x.1) ->
      exists y : LCarrier.{u},
        (y.1 ∈ x.1 /\
          forall z : LCarrier.{u}, z.1 ∈ x.1 ->
            Not (GraphRel r z y)) /\
        forall y' : LCarrier.{u},
          (y'.1 ∈ x.1 /\
            forall z : LCarrier.{u}, z.1 ∈ x.1 ->
              Not (GraphRel r z y')) ->
          y' = y := by
    intro x hxfamily hxne
    apply exists_unique_graph_minimum hr
    · intro z hzx
      exact (mem_sUnionLCarrier_iff family z).mpr
        ⟨x, hxfamily, hzx⟩
    · exact hxne
  let params : Tuple LCarrier.{u} 2 := ![family, r]
  rcases exists_separationLCarrier graphLeastMemberPredicate
      params unionFamily with
    ⟨choiceSet, hchoiceSet⟩
  refine ⟨choiceSet, ?_⟩
  intro x hxfamily
  rcases hmin x hxfamily (hnonempty x hxfamily) with
    ⟨y, ⟨hyx, hymin⟩, hyunique⟩
  refine ⟨y, hyx, ?_, ?_⟩
  · apply (hchoiceSet y).mpr
    refine ⟨?_, ?_⟩
    · exact (mem_sUnionLCarrier_iff family y).mpr
        ⟨x, hxfamily, hyx⟩
    · apply (satisfies_graphLeastMemberPredicate
        (snoc params y)).mpr
      refine ⟨x, ?_, hyx, ?_⟩
      · simpa [params, snoc_eq_finSnoc] using hxfamily
      · simpa [params, snoc_eq_finSnoc] using hymin
  · intro z hzx hzchoice
    have hzSelected := (hchoiceSet z).mp hzchoice
    rcases (satisfies_graphLeastMemberPredicate
        (snoc params z)).mp hzSelected.2 with
      ⟨x', hx'family, hzx', hzmin⟩
    have hxx' : x = x' := by
      by_contra hne
      exact hdisjoint x hxfamily x'
        (by simpa [params, snoc_eq_finSnoc] using hx'family) hne z hzx hzx'
    subst x'
    apply hyunique z
    refine ⟨hzx, ?_⟩
    simpa [params, snoc_eq_finSnoc] using hzmin

/-- The exact internal well-ordering obligation sufficient for the ZFC theorem. -/
theorem lCarrier_models_ZFC_of_internalWellOrdering
    (hwo : ModelsInternalWellOrdering.{u}) :
    LCarrier.{u} ⊨ FirstOrder.Language.Theory.ZFC := by
  rw [FirstOrder.Language.Theory.model_ZFC_iff]
  exact ⟨lCarrier_models_ZF,
    lCarrier_modelsChoice_of_internalWellOrdering hwo⟩

end Model

end Constructible
