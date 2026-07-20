/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.InternalWellOrder

/-!
# Constructible graphs of definable relations

A binary relation given by one fixed first-order formula is not merely an
external Lean predicate.  On a constructible domain, Full Separation produces
an actual Kuratowski-pair graph which belongs to `L`.

The separating set is taken from a sufficiently large constructible stage.
This avoids assuming in advance that the ambient product `d x d` itself is
constructible.
-/

@[expose] public section

universe u

namespace Constructible

namespace Model

/-- A Kuratowski ordered pair, packaged as an element of `L`. -/
def orderedPairLCarrier (x y : LCarrier.{u}) : LCarrier.{u} :=
  ⟨ZFSet.pair x.1 y.1, orderedPair_mem_L x.2 y.2⟩

@[simp]
theorem orderedPairLCarrier_val (x y : LCarrier.{u}) :
    (orderedPairLCarrier x y).1 = ZFSet.pair x.1 y.1 :=
  rfl

end Model

namespace DefinableRelationGraph

/-!
The input formula has layout `(params, x, y)`.  Under the two witnesses in
`graphFormula`, the larger layout is `(params, domain, pair, x, y)`.
-/

/-- Embed `(params, x, y)` into `(params, domain, pair, x, y)`. -/
def predicateRename {n : Nat} : Fin (n + 2) → Fin (n + 4) :=
  Fin.lastCases
    (Fin.last (n + 3))
    (fun j => Fin.lastCases
      (Fin.castSucc (Fin.last (n + 2)))
      (fun i => i.castSucc.castSucc.castSucc.castSucc)
      j)

theorem comp_predicateRename {A : Type u} {n : Nat}
    (params : Tuple A n) (domain pair x y : A) :
    (fun i => snoc (snoc (snoc (snoc params domain) pair) x) y
      (predicateRename i)) =
      snoc (snoc params x) y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [predicateRename]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [predicateRename]
    · simp [predicateRename]

/-- The index of `domain` in `(params, domain, pair, x, y)`. -/
def domainIndex (n : Nat) : Fin (n + 4) :=
  (Fin.last n).castSucc.castSucc.castSucc

/-- The index of `pair` in `(params, domain, pair, x, y)`. -/
def pairIndex (n : Nat) : Fin (n + 4) :=
  (Fin.last (n + 1)).castSucc.castSucc

/-- The index of `x` in `(params, domain, pair, x, y)`. -/
def leftIndex (n : Nat) : Fin (n + 4) :=
  (Fin.last (n + 2)).castSucc

/-- The index of `y` in `(params, domain, pair, x, y)`. -/
def rightIndex (n : Nat) : Fin (n + 4) :=
  Fin.last (n + 3)

/--
`graphFormula phi(params, domain, pair)` says that `pair = <x,y>` for
some `x,y ∈ domain` satisfying `phi(params,x,y)`.
-/
def graphFormula {n : Nat} (phi : FOFormula (n + 2)) :
    FOFormula (n + 2) :=
  .ex (.ex
    (.conj
      (.mem (leftIndex n) (domainIndex n))
      (.conj
        (.mem (rightIndex n) (domainIndex n))
        (.conj
          (Delta0Formula.kuratowskiPairEqAt
            (pairIndex n) (leftIndex n) (rightIndex n)).toFO
          (FOFormula.rename predicateRename phi)))))

theorem satisfies_pairEq_lCarrier {n : Nat}
    (pair x y : Fin n) (s : Tuple Model.LCarrier.{u} n) :
    FOFormula.Satisfies
        (fun z w : Model.LCarrier.{u} => z.1 ∈ w.1)
        (Delta0Formula.kuratowskiPairEqAt pair x y).toFO s ↔
      (s pair).1 = ZFSet.pair (s x).1 (s y).1 := by
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_kuratowskiPairEqAt]

theorem satisfies_graphFormula {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple Model.LCarrier.{u} n)
    (domain pair : Model.LCarrier.{u}) :
    FOFormula.Satisfies
        (fun z w : Model.LCarrier.{u} => z.1 ∈ w.1)
        (graphFormula phi) (snoc (snoc params domain) pair) ↔
      ∃ x y : Model.LCarrier.{u},
        x.1 ∈ domain.1 ∧ y.1 ∈ domain.1 ∧
          pair.1 = ZFSet.pair x.1 y.1 ∧
          FOFormula.Satisfies
            (fun z w : Model.LCarrier.{u} => z.1 ∈ w.1)
            phi (snoc (snoc params x) y) := by
  simp only [graphFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename, satisfies_pairEq_lCarrier,
    domainIndex, pairIndex, leftIndex, rightIndex,
    snoc_last, snoc_castSucc, comp_predicateRename]

end DefinableRelationGraph

namespace Model

/--
Every fixed first-order relation on a constructible domain has a graph which
is itself a constructible set.
-/
theorem exists_definableRelationGraph {n : Nat}
    (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n) (domain : LCarrier.{u}) :
    ∃ relation : LCarrier.{u}, ∀ x y : LCarrier.{u},
      GraphRel relation x y ↔
        x.1 ∈ domain.1 ∧ y.1 ∈ domain.1 ∧
          FOFormula.Satisfies
            (fun z w : LCarrier.{u} => z.1 ∈ w.1)
            phi (snoc (snoc params x) y) := by
  have hpairs : ∀ q ∈ ZFSet.prod domain.1 domain.1, q ∈ L := by
    intro q hq
    rcases ZFSet.mem_prod.mp hq with ⟨x, hx, y, hy, rfl⟩
    exact orderedPair_mem_L
      (mem_L_of_mem hx domain.2) (mem_L_of_mem hy domain.2)
  rcases exists_LStage_for_members hpairs with ⟨alpha, halpha⟩
  let container : LCarrier.{u} :=
    ⟨LStageZF alpha, LStageZF_mem_L alpha⟩
  let extendedParams : Tuple LCarrier.{u} (n + 1) :=
    snoc params domain
  rcases exists_separationLCarrier
      (DefinableRelationGraph.graphFormula phi)
      extendedParams container with ⟨relation, hrelation⟩
  refine ⟨relation, ?_⟩
  intro x y
  let pair : LCarrier.{u} := orderedPairLCarrier x y
  rw [GraphRel, ← orderedPairLCarrier_val x y]
  rw [hrelation pair]
  constructor
  · rintro ⟨_hpairContainer, hformula⟩
    rcases (DefinableRelationGraph.satisfies_graphFormula
        phi params domain pair).mp
        (by simpa only [extendedParams] using hformula) with
      ⟨x', y', hx', hy', hpair, hphi⟩
    have hpairRaw :
        ZFSet.pair x.1 y.1 = ZFSet.pair x'.1 y'.1 := by
      simpa only [pair, orderedPairLCarrier_val] using hpair
    have hxyRaw : x.1 = x'.1 ∧ y.1 = y'.1 :=
      ZFSet.pair_inj.mp hpairRaw
    have hxy : x = x' ∧ y = y' :=
      ⟨Subtype.ext hxyRaw.1, Subtype.ext hxyRaw.2⟩
    rcases hxy with ⟨rfl, rfl⟩
    exact ⟨hx', hy', hphi⟩
  · rintro ⟨hx, hy, hphi⟩
    have hpairProd : pair.1 ∈ ZFSet.prod domain.1 domain.1 := by
      change ZFSet.pair x.1 y.1 ∈ ZFSet.prod domain.1 domain.1
      rw [ZFSet.pair_mem_prod]
      exact ⟨hx, hy⟩
    have hpairContainer : pair.1 ∈ container.1 := by
      exact halpha pair.1 hpairProd
    refine ⟨hpairContainer, ?_⟩
    apply (DefinableRelationGraph.satisfies_graphFormula
      phi params domain pair).mpr
    exact ⟨x, y, hx, hy, rfl, hphi⟩

/-- The relation on a set carrier interpreted by a fixed formula. -/
def formulaRelOn {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n) (domain : LCarrier.{u}) :
    InternalCarrier domain → InternalCarrier domain → Prop :=
  fun x y =>
    FOFormula.Satisfies
      (fun z w : LCarrier.{u} => z.1 ∈ w.1)
      phi (snoc (snoc params x.1) y.1)

/--
A formula-defined well-order has an actual constructible Kuratowski graph.
This is the reusable bridge from object-language definability to the internal
well-ordering obligation used by the Choice proof.
-/
theorem exists_internalWellOrder_of_formula {n : Nat}
    (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n) (domain : LCarrier.{u})
    (hwell : IsWellOrder (InternalCarrier domain)
      (formulaRelOn phi params domain)) :
    ∃ relation : LCarrier.{u}, InternallyWellOrders relation domain := by
  rcases exists_definableRelationGraph phi params domain with
    ⟨relation, hrelation⟩
  refine ⟨relation, ?_⟩
  have heq : graphRelOn relation domain = formulaRelOn phi params domain := by
    funext x y
    apply propext
    have h := hrelation x.1 y.1
    simpa only [graphRelOn, GraphRel, formulaRelOn, x.2, y.2,
      true_and] using h
  rw [InternallyWellOrders, heq]
  exact hwell

end Model

end Constructible
