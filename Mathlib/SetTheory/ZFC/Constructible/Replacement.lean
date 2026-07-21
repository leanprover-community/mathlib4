/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Collection

/-!
# Replacement in the constructible universe

Collection first gives a constructible set containing a value for every
input.  Full Separation then cuts out the exact range.  The formula
`replacementRangeFormula phi` expresses that its last variable is related by
`phi` to some member of the set parameter immediately preceding it.
-/

@[expose] public section

universe u

namespace Constructible

section ZFC

namespace Model

/-- Renaming raw-domain formulas composes their assignments. -/
@[simp]
theorem satisfiesIn_rename (M : Set ZFSet.{u}) {n m : Nat}
    (phi : FOFormula n) (rho : Fin n -> Fin m) (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (FOFormula.rename rho phi) s <->
      SatisfiesIn M phi (fun i => s (rho i)) := by
  induction phi generalizing m with
  | mem i j => rfl
  | eq i j => rfl
  | neg phi ih => exact not_congr (ih rho s)
  | conj phi psi ihPhi ihPsi =>
      exact and_congr (ihPhi rho s) (ihPsi rho s)
  | ex phi ih =>
      simp only [FOFormula.rename, SatisfiesIn, ih]
      constructor
      · rintro ⟨x, hxM, hphi⟩
        refine ⟨x, hxM, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hphi
      · rintro ⟨x, hxM, hphi⟩
        refine ⟨x, hxM, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hphi

end Model

/--
Variable permutation used under the existential in
`replacementRangeFormula`.  The old layout is `(params, x, y)` and the new
body layout is `(params, a, y, x)`.
-/
def replacementRangeRename {n : Nat} : Fin (n + 2) -> Fin (n + 3) :=
  Fin.lastCases
    (Fin.castSucc (Fin.last (n + 1)))
    (fun j => Fin.lastCases
      (Fin.last (n + 2))
      (fun i => i.castSucc.castSucc.castSucc)
      j)

/-- The variable permutation has the intended effect on appended tuples. -/
theorem comp_replacementRangeRename {A : Type u} {n : Nat}
    (params : Tuple A n) (a y x : A) :
    (fun i => snoc (snoc (snoc params a) y) x
      (replacementRangeRename i)) =
      snoc (snoc params x) y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [replacementRangeRename]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [replacementRangeRename]
    · simp [replacementRangeRename]

/--
`replacementRangeFormula phi(params,a,y)` says that some `x ∈ a` satisfies
`phi(params,x,y)`.
-/
def replacementRangeFormula {n : Nat}
    (phi : FOFormula (n + 2)) : FOFormula (n + 2) :=
  .ex (.conj
    (.mem (Fin.last (n + 2)) (Fin.last n).castSucc.castSucc)
    (FOFormula.rename replacementRangeRename phi))

@[simp]
theorem satisfiesIn_replacementRangeFormula (M : Set ZFSet.{u})
    {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n) (a y : ZFSet.{u}) :
    Model.SatisfiesIn M (replacementRangeFormula phi)
        (snoc (snoc params a) y) <->
      exists x : ZFSet.{u}, x ∈ M /\ x ∈ a /\
        Model.SatisfiesIn M phi (snoc (snoc params x) y) := by
  simp only [replacementRangeFormula, Model.SatisfiesIn,
    Model.satisfiesIn_rename]
  apply exists_congr
  intro x
  apply and_congr_right
  intro _hxM
  change
    (snoc (snoc (snoc params a) y) x (Fin.last (n + 2)) ∈
        snoc (snoc (snoc params a) y) x
          (Fin.last n).castSucc.castSucc /\
      Model.SatisfiesIn M phi
        (fun i => snoc (snoc (snoc params a) y) x
          (replacementRangeRename i))) <-> _
  simp only [snoc_last, snoc_castSucc, comp_replacementRangeRename]

/--
Function-form Replacement for the raw-domain semantics of `L`.

The predicate is required to have a unique constructible output for every
member of `a`.  The resulting set consists of exactly those outputs.
-/
theorem exists_replacement {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n) (hparams : forall i, params i ∈ L)
    {a : ZFSet.{u}} (ha : a ∈ L)
    (hfun : forall x : ZFSet.{u}, x ∈ a ->
      ∃! y : ZFSet.{u}, y ∈ L /\
        Model.SatisfiesIn L phi (snoc (snoc params x) y)) :
    exists b : ZFSet.{u}, b ∈ L /\
      forall y : ZFSet.{u}, y ∈ b <->
        y ∈ L /\ exists x : ZFSet.{u}, x ∈ a /\
          Model.SatisfiesIn L phi (snoc (snoc params x) y) := by
  have hexists : forall x : ZFSet.{u}, x ∈ a ->
      exists y : ZFSet.{u}, y ∈ L /\
        Model.SatisfiesIn L phi (snoc (snoc params x) y) :=
    fun x hx => (hfun x hx).exists
  rcases exists_collection phi params ha hexists with ⟨c, hcL, hcollect⟩
  let extendedParams : Tuple ZFSet.{u} (n + 1) := snoc params a
  have hextended : forall i, extendedParams i ∈ L := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [extendedParams] using ha
    · simpa [extendedParams] using hparams j
  rcases exists_separation (replacementRangeFormula phi)
      extendedParams hextended hcL with ⟨b, hbL, hb⟩
  refine ⟨b, hbL, ?_⟩
  intro y
  constructor
  · intro hyb
    rcases (hb y).mp hyb with ⟨hyc, hyrange⟩
    have hyL : y ∈ L := mem_L_of_mem hyc hcL
    rcases (satisfiesIn_replacementRangeFormula L phi params a y).mp
        (by simpa only [extendedParams] using hyrange) with
      ⟨x, _hxL, hxa, hphi⟩
    exact ⟨hyL, x, hxa, hphi⟩
  · rintro ⟨hyL, x, hxa, hphi⟩
    rcases hcollect x hxa with ⟨z, hzc, hzphi⟩
    have hzL : z ∈ L := mem_L_of_mem hzc hcL
    rcases hfun x hxa with ⟨w, hw, hunique⟩
    have hzw : z = w := hunique z ⟨hzL, hzphi⟩
    have hyw : y = w := hunique y ⟨hyL, hphi⟩
    have hyz : y = z := hyw.trans hzw.symm
    have hyc : y ∈ c := by simpa only [hyz] using hzc
    apply (hb y).mpr
    refine ⟨hyc, ?_⟩
    have hxL : x ∈ L := mem_L_of_mem hxa ha
    have hrange :=
      (satisfiesIn_replacementRangeFormula L phi params a y).mpr
        ⟨x, hxL, hxa, hphi⟩
    simpa only [extendedParams] using hrange

/-- Function-form Replacement packaged on `LCarrier`. -/
theorem Model.exists_replacementLCarrier {n : Nat}
    (phi : FOFormula (n + 2)) (params : Tuple Model.LCarrier.{u} n)
    (a : Model.LCarrier.{u})
    (hfun : forall x : Model.LCarrier.{u}, x.1 ∈ a.1 ->
      ∃! y : Model.LCarrier.{u},
        FOFormula.Satisfies
          (fun z w : Model.LCarrier.{u} => z.1 ∈ w.1)
          phi (snoc (snoc params x) y)) :
    exists b : Model.LCarrier.{u}, forall y : Model.LCarrier.{u},
      y.1 ∈ b.1 <-> exists x : Model.LCarrier.{u}, x.1 ∈ a.1 /\
        FOFormula.Satisfies
          (fun z w : Model.LCarrier.{u} => z.1 ∈ w.1)
          phi (snoc (snoc params x) y) := by
  let rawParams : Tuple ZFSet.{u} n := fun i => (params i).1
  have hrawParams : forall i, rawParams i ∈ L := fun i => (params i).2
  have hrawFun : forall x : ZFSet.{u}, x ∈ a.1 ->
      ∃! y : ZFSet.{u}, y ∈ L /\
        Model.SatisfiesIn L phi (snoc (snoc rawParams x) y) := by
    intro x hx
    let xL : Model.LCarrier.{u} := ⟨x, mem_L_of_mem hx a.2⟩
    rcases hfun xL hx with ⟨y, hy, hunique⟩
    refine ⟨y.1, ?_, ?_⟩
    · refine ⟨y.2, ?_⟩
      have hbridge := Model.satisfies_lCarrier_iff_satisfiesIn_L
        phi (snoc (snoc params xL) y)
      simpa only [Model.subtypeVal_snoc, rawParams] using hbridge.mp hy
    · intro z hz
      let zL : Model.LCarrier.{u} := ⟨z, hz.1⟩
      have hzSat :
          FOFormula.Satisfies
            (fun p q : Model.LCarrier.{u} => p.1 ∈ q.1)
            phi (snoc (snoc params xL) zL) := by
        have hbridge := Model.satisfies_lCarrier_iff_satisfiesIn_L
          phi (snoc (snoc params xL) zL)
        apply hbridge.mpr
        simpa only [Model.subtypeVal_snoc, rawParams] using hz.2
      exact congrArg Subtype.val (hunique zL hzSat)
  rcases exists_replacement phi rawParams hrawParams a.2 hrawFun with
    ⟨b, hbL, hb⟩
  refine ⟨⟨b, hbL⟩, ?_⟩
  intro y
  constructor
  · intro hyb
    rcases (hb y.1).mp hyb with ⟨_hyL, x, hxa, hphi⟩
    let xL : Model.LCarrier.{u} := ⟨x, mem_L_of_mem hxa a.2⟩
    refine ⟨xL, hxa, ?_⟩
    have hbridge := Model.satisfies_lCarrier_iff_satisfiesIn_L
      phi (snoc (snoc params xL) y)
    apply hbridge.mpr
    simpa only [Model.subtypeVal_snoc, rawParams] using hphi
  · rintro ⟨x, hxa, hphi⟩
    apply (hb y.1).mpr
    refine ⟨y.2, x.1, hxa, ?_⟩
    have hbridge := Model.satisfies_lCarrier_iff_satisfiesIn_L
      phi (snoc (snoc params x) y)
    simpa only [Model.subtypeVal_snoc, rawParams] using hbridge.mp hphi

/--
Function-form Replacement stated directly with Mathlib's
membership-language formulas.
-/
theorem Model.exists_replacementBoundedFormula {n : Nat}
    (phi : FirstOrder.Language.setTheory.BoundedFormula Empty (n + 2))
    (params : Tuple Model.LCarrier.{u} n) (a : Model.LCarrier.{u})
    (hfun : forall x : Model.LCarrier.{u}, x.1 ∈ a.1 ->
      ExistsUnique fun y : Model.LCarrier.{u} =>
        phi.Realize Empty.elim (snoc (snoc params x) y)) :
    exists b : Model.LCarrier.{u}, forall y : Model.LCarrier.{u},
      y.1 ∈ b.1 <-> exists x : Model.LCarrier.{u}, x.1 ∈ a.1 /\
        phi.Realize Empty.elim (snoc (snoc params x) y) := by
  let E := fun z w : Model.LCarrier.{u} => z.1 ∈ w.1
  have hcompat : forall x : Model.LCarrier.{u}, x.1 ∈ a.1 ->
      ExistsUnique fun y : Model.LCarrier.{u} =>
        FOFormula.Satisfies E (Model.fromBoundedFormula phi)
          (snoc (snoc params x) y) := by
    intro x hx
    rcases hfun x hx with ⟨y, hy, hunique⟩
    refine ⟨y, ?_, ?_⟩
    · exact (Model.realize_fromBoundedFormula E phi
        (snoc (snoc params x) y)).mp hy
    · intro z hz
      apply hunique z
      exact (Model.realize_fromBoundedFormula E phi
        (snoc (snoc params x) z)).mpr hz
  rcases Model.exists_replacementLCarrier
      (Model.fromBoundedFormula phi) params a hcompat with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  intro y
  constructor
  · intro hyb
    rcases (hb y).mp hyb with ⟨x, hxa, hphi⟩
    refine ⟨x, hxa, ?_⟩
    exact (Model.realize_fromBoundedFormula E phi
      (snoc (snoc params x) y)).mpr hphi
  · rintro ⟨x, hxa, hphi⟩
    apply (hb y).mpr
    refine ⟨x, hxa, ?_⟩
    exact (Model.realize_fromBoundedFormula E phi
      (snoc (snoc params x) y)).mp hphi

/--
Functional Replacement stated with Mathlib formulas whose variables are
free.  The final two coordinates are respectively the input and output of
the functional relation.
-/
theorem Model.exists_replacementFormula {n : Nat}
    (phi : FirstOrder.Language.setTheory.Formula (Fin (n + 2)))
    (params : Tuple Model.LCarrier.{u} n) (a : Model.LCarrier.{u})
    (hfun : forall x : Model.LCarrier.{u}, x.1 ∈ a.1 ->
      ExistsUnique fun y : Model.LCarrier.{u} =>
        phi.Realize (Fin.snoc (Fin.snoc params x) y)) :
    exists b : Model.LCarrier.{u}, forall y : Model.LCarrier.{u},
      y.1 ∈ b.1 <-> exists x : Model.LCarrier.{u}, x.1 ∈ a.1 /\
        phi.Realize (Fin.snoc (Fin.snoc params x) y) := by
  simpa only [FirstOrder.Language.Formula.realize_relabel_sumInr,
    Model.snoc_eq_finSnoc] using
    (Model.exists_replacementBoundedFormula
      (FirstOrder.Language.BoundedFormula.relabel
        (β := Empty) (n := n + 2) (k := 0)
        (fun i : Fin (n + 2) => (Sum.inr i : Empty ⊕ Fin (n + 2)))
        phi) params a (by
          simpa only [FirstOrder.Language.Formula.realize_relabel_sumInr,
            Model.snoc_eq_finSnoc] using hfun))

end ZFC

end Constructible
