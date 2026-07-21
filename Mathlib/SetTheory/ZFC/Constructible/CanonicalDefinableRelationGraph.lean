/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.DefinableRelationGraph
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryConstructible

/-!
# Canonical graphs of formula-defined relations

The existential graph construction is sufficient for Separation, but a
transfinite recursion needs a graph uniquely determined by its inputs.  This
file separates directly inside the constructible Cartesian square and keeps
the resulting exact membership specification.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

/-! ## An object-language formula specifying the exact output graph -/

/--
Embed the layout `(params, domain, pair)` into
`(params, domain, relation, pair)`, skipping the candidate relation.
-/
def canonicalGraphOutputRename {n : Nat} : Fin (n + 2) → Fin (n + 3) :=
  Fin.lastCases
    (Fin.last (n + 2))
    (fun j => Fin.lastCases
      (Fin.castSucc (Fin.castSucc (Fin.last n)))
      (fun i => i.castSucc.castSucc.castSucc)
      j)

theorem comp_canonicalGraphOutputRename {A : Type u} {n : Nat}
    (params : Tuple A n) (domain relation pair : A) :
    (fun i => snoc (snoc (snoc params domain) relation) pair
      (canonicalGraphOutputRename i)) =
      snoc (snoc params domain) pair := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [canonicalGraphOutputRename]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [canonicalGraphOutputRename]
    · simp [canonicalGraphOutputRename]

/--
`canonicalGraphOutputFormula phi(params, domain, relation)` says that
`relation` consists exactly of the ordered pairs selected by `phi` on
`domain`.  Extensionality therefore makes its output unique.
-/
def canonicalGraphOutputFormula {n : Nat}
    (phi : FOFormula (n + 2)) : FOFormula (n + 2) :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (Fin.last (n + 2)) (Fin.castSucc (Fin.last (n + 1))))
      (FOFormula.rename canonicalGraphOutputRename
        (DefinableRelationGraph.graphFormula phi)))

@[simp]
theorem satisfies_canonicalGraphOutputFormula {A : Type u}
    (E : A → A → Prop) {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple A n) (domain relation : A) :
    FOFormula.Satisfies E (canonicalGraphOutputFormula phi)
        (snoc (snoc params domain) relation) ↔
      ∀ pair : A, E pair relation ↔
        FOFormula.Satisfies E
          (DefinableRelationGraph.graphFormula phi)
          (snoc (snoc params domain) pair) := by
  simp only [canonicalGraphOutputFormula, FOFormula.satisfies_all,
    FOFormula.satisfies_biimp, FOFormula.Satisfies,
    FOFormula.satisfies_rename, snoc_last, snoc_castSucc,
    comp_canonicalGraphOutputRename]

/-- The Cartesian product of two constructible sets is constructible. -/
def prodLCarrier (x y : LCarrier.{u}) : LCarrier.{u} :=
  ⟨ZFSet.prod x.1 y.1, by
    simpa [Godel.op, Godel.F2] using
      (Godel.op_mem_L (i := (2 : Fin 9)) x.2 y.2)⟩

@[simp]
theorem prodLCarrier_val (x y : LCarrier.{u}) :
    (prodLCarrier x y).1 = ZFSet.prod x.1 y.1 := rfl

/-- The canonical Separation witness for a formula-defined binary relation. -/
def canonicalDefinableRelationGraph {n : Nat}
    (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n) (domain : LCarrier.{u}) :
    LCarrier.{u} :=
  Classical.choose
    (exists_separationLCarrier
      (DefinableRelationGraph.graphFormula phi)
      (snoc params domain) (prodLCarrier domain domain))

@[simp]
theorem mem_canonicalDefinableRelationGraph_iff {n : Nat}
    (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n) (domain q : LCarrier.{u}) :
    q.1 ∈ (canonicalDefinableRelationGraph phi params domain).1 ↔
      ∃ x y : LCarrier.{u},
        x.1 ∈ domain.1 ∧ y.1 ∈ domain.1 ∧
          q.1 = ZFSet.pair x.1 y.1 ∧
          FOFormula.Satisfies
            (fun z w : LCarrier.{u} => z.1 ∈ w.1)
            phi (snoc (snoc params x) y) := by
  have hsep := Classical.choose_spec
    (exists_separationLCarrier
      (DefinableRelationGraph.graphFormula phi)
      (snoc params domain) (prodLCarrier domain domain)) q
  constructor
  · intro hq
    rcases hsep.mp hq with ⟨_hqProd, hformula⟩
    exact (DefinableRelationGraph.satisfies_graphFormula
      phi params domain q).mp hformula
  · rintro ⟨x, y, hx, hy, hq, hphi⟩
    apply hsep.mpr
    constructor
    · change q.1 ∈ ZFSet.prod domain.1 domain.1
      rw [hq, ZFSet.pair_mem_prod]
      exact ⟨hx, hy⟩
    · apply (DefinableRelationGraph.satisfies_graphFormula
        phi params domain q).mpr
      exact ⟨x, y, hx, hy, hq, hphi⟩

/-- The canonical graph represents exactly the intended relation on the
specified domain. -/
@[simp]
theorem graphRel_canonicalDefinableRelationGraph_iff {n : Nat}
    (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n) (domain x y : LCarrier.{u}) :
    GraphRel (canonicalDefinableRelationGraph phi params domain) x y ↔
      x.1 ∈ domain.1 ∧ y.1 ∈ domain.1 ∧
        FOFormula.Satisfies
          (fun z w : LCarrier.{u} => z.1 ∈ w.1)
          phi (snoc (snoc params x) y) := by
  change (orderedPairLCarrier x y).1 ∈
    (canonicalDefinableRelationGraph phi params domain).1 ↔ _
  rw [mem_canonicalDefinableRelationGraph_iff]
  constructor
  · rintro ⟨x', y', hx', hy', hpair, hphi⟩
    have hraw :
        ZFSet.pair x.1 y.1 = ZFSet.pair x'.1 y'.1 := by
      simpa only [orderedPairLCarrier_val] using hpair
    rcases ZFSet.pair_inj.mp hraw with ⟨hxEq, hyEq⟩
    have hxCarrier : x = x' := Subtype.ext hxEq
    have hyCarrier : y = y' := Subtype.ext hyEq
    subst x'
    subst y'
    exact ⟨hx', hy', hphi⟩
  · rintro ⟨hx, hy, hphi⟩
    exact ⟨x, y, hx, hy, rfl, hphi⟩

/-- Exact graph membership determines the canonical graph uniquely. -/
theorem eq_canonicalDefinableRelationGraph_of_mem_iff {n : Nat}
    (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n) (domain relation : LCarrier.{u})
    (hexact : ∀ q : LCarrier.{u}, q.1 ∈ relation.1 ↔
      ∃ x y : LCarrier.{u},
        x.1 ∈ domain.1 ∧ y.1 ∈ domain.1 ∧
          q.1 = ZFSet.pair x.1 y.1 ∧
          FOFormula.Satisfies
            (fun z w : LCarrier.{u} => z.1 ∈ w.1)
            phi (snoc (snoc params x) y)) :
    relation = canonicalDefinableRelationGraph phi params domain := by
  apply lCarrier_extensionality
  intro q
  exact (hexact q).trans
    (mem_canonicalDefinableRelationGraph_iff phi params domain q).symm

/-- The object-language output specification identifies exactly the
canonical Separation graph. -/
theorem satisfies_canonicalGraphOutputFormula_iff_eq {n : Nat}
    (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n) (domain relation : LCarrier.{u}) :
    FOFormula.Satisfies
        (fun z w : LCarrier.{u} => z.1 ∈ w.1)
        (canonicalGraphOutputFormula phi)
        (snoc (snoc params domain) relation) ↔
      relation = canonicalDefinableRelationGraph phi params domain := by
  rw [satisfies_canonicalGraphOutputFormula]
  constructor
  · intro hexact
    apply eq_canonicalDefinableRelationGraph_of_mem_iff
    intro pair
    exact (hexact pair).trans
      (DefinableRelationGraph.satisfies_graphFormula
        phi params domain pair)
  · intro hrelation
    subst relation
    intro pair
    exact (mem_canonicalDefinableRelationGraph_iff
      phi params domain pair).trans
        (DefinableRelationGraph.satisfies_graphFormula
          phi params domain pair).symm

/-- The exact graph formula has a unique constructible output.  This is the
shape consumed by function-form Replacement. -/
theorem existsUnique_canonicalGraphOutputFormula {n : Nat}
    (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n) (domain : LCarrier.{u}) :
    ∃! relation : LCarrier.{u},
      FOFormula.Satisfies
        (fun z w : LCarrier.{u} => z.1 ∈ w.1)
        (canonicalGraphOutputFormula phi)
        (snoc (snoc params domain) relation) := by
  refine ⟨canonicalDefinableRelationGraph phi params domain, ?_, ?_⟩
  · exact (satisfies_canonicalGraphOutputFormula_iff_eq
      phi params domain
      (canonicalDefinableRelationGraph phi params domain)).mpr rfl
  · intro relation hrelation
    exact (satisfies_canonicalGraphOutputFormula_iff_eq
      phi params domain relation).mp hrelation

end

end Constructible.Model
