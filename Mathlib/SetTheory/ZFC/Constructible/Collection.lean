/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Separation

/-!
# Collection in the constructible universe

Ambient choice selects one constructible witness for each member of the
given internal set.  Since that index type is small, the occurrence levels of
all selected witnesses have a supremum.  The corresponding constructible
stage is itself an element of `L` and collects every selected witness.
-/

@[expose] public section

universe u

namespace Constructible

section ZFC

/-- Full first-order Collection for the raw-domain semantics of `L`. -/
theorem exists_collection {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n) {a : ZFSet.{u}} (_ha : a ∈ L)
    (h : forall x : ZFSet.{u}, x ∈ a ->
      exists y : ZFSet.{u}, y ∈ L /\
        Model.SatisfiesIn L phi (snoc (snoc params x) y)) :
    exists b : ZFSet.{u}, b ∈ L /\
      forall x : ZFSet.{u}, x ∈ a ->
        exists y : ZFSet.{u}, y ∈ b /\
          Model.SatisfiesIn L phi (snoc (snoc params x) y) := by
  classical
  let witness : a -> ZFSet.{u} := fun x => Classical.choose (h x.1 x.2)
  have hwitnessL (x : a) : witness x ∈ L :=
    (Classical.choose_spec (h x.1 x.2)).1
  have hwitnessSat (x : a) :
      Model.SatisfiesIn L phi (snoc (snoc params x.1) (witness x)) :=
    (Classical.choose_spec (h x.1 x.2)).2
  let level : a -> Ordinal.{u} := fun x => stageOf (witness x) (hwitnessL x)
  let beta : Ordinal.{u} := iSup level
  refine ⟨LStageZF beta, LStageZF_mem_L beta, ?_⟩
  intro x hx
  let xa : a := ⟨x, hx⟩
  refine ⟨witness xa, ?_, hwitnessSat xa⟩
  exact LStageZF_mono (Ordinal.le_iSup level xa)
    (mem_LStageZF_stageOf (witness xa) (hwitnessL xa))

/-- Collection packaged on the subtype model `LCarrier`. -/
theorem Model.exists_collectionLCarrier {n : Nat}
    (phi : FOFormula (n + 2)) (params : Tuple Model.LCarrier.{u} n)
    (a : Model.LCarrier.{u})
    (h : forall x : Model.LCarrier.{u}, x.1 ∈ a.1 ->
      exists y : Model.LCarrier.{u},
        FOFormula.Satisfies
          (fun z w : Model.LCarrier.{u} => z.1 ∈ w.1)
          phi (snoc (snoc params x) y)) :
    exists b : Model.LCarrier.{u},
      forall x : Model.LCarrier.{u}, x.1 ∈ a.1 ->
        exists y : Model.LCarrier.{u}, y.1 ∈ b.1 /\
          FOFormula.Satisfies
            (fun z w : Model.LCarrier.{u} => z.1 ∈ w.1)
            phi (snoc (snoc params x) y) := by
  let rawParams : Tuple ZFSet.{u} n := fun i => (params i).1
  have hraw : forall x : ZFSet.{u}, x ∈ a.1 ->
      exists y : ZFSet.{u}, y ∈ L /\
        Model.SatisfiesIn L phi (snoc (snoc rawParams x) y) := by
    intro x hx
    let xL : Model.LCarrier.{u} := ⟨x, mem_L_of_mem hx a.2⟩
    rcases h xL hx with ⟨y, hy⟩
    refine ⟨y.1, y.2, ?_⟩
    have hbridge := Model.satisfies_lCarrier_iff_satisfiesIn_L
      phi (snoc (snoc params xL) y)
    simpa only [Model.subtypeVal_snoc] using hbridge.mp hy
  rcases exists_collection phi rawParams a.2 hraw with ⟨b, hbL, hb⟩
  refine ⟨⟨b, hbL⟩, ?_⟩
  intro x hx
  rcases hb x.1 hx with ⟨y, hyb, hy⟩
  have hyL : y ∈ L := mem_L_of_mem hyb hbL
  let yL : Model.LCarrier.{u} := ⟨y, hyL⟩
  refine ⟨yL, hyb, ?_⟩
  have hbridge := Model.satisfies_lCarrier_iff_satisfiesIn_L
    phi (snoc (snoc params x) yL)
  apply hbridge.mpr
  simpa only [Model.subtypeVal_snoc, rawParams] using hy

/-- Collection stated directly with Mathlib's membership-language formulas. -/
theorem Model.exists_collectionBoundedFormula {n : Nat}
    (phi : FirstOrder.Language.setTheory.BoundedFormula Empty (n + 2))
    (params : Tuple Model.LCarrier.{u} n) (a : Model.LCarrier.{u})
    (h : forall x : Model.LCarrier.{u}, x.1 ∈ a.1 ->
      exists y : Model.LCarrier.{u},
        phi.Realize Empty.elim (snoc (snoc params x) y)) :
    exists b : Model.LCarrier.{u},
      forall x : Model.LCarrier.{u}, x.1 ∈ a.1 ->
        exists y : Model.LCarrier.{u}, y.1 ∈ b.1 /\
          phi.Realize Empty.elim (snoc (snoc params x) y) := by
  let E := fun z w : Model.LCarrier.{u} => z.1 ∈ w.1
  have hcompat : forall x : Model.LCarrier.{u}, x.1 ∈ a.1 ->
      exists y : Model.LCarrier.{u},
        FOFormula.Satisfies E (Model.fromBoundedFormula phi)
          (snoc (snoc params x) y) := by
    intro x hx
    rcases h x hx with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    exact (Model.realize_fromBoundedFormula E phi
      (snoc (snoc params x) y)).mp hy
  rcases Model.exists_collectionLCarrier
      (Model.fromBoundedFormula phi) params a hcompat with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  intro x hx
  rcases hb x hx with ⟨y, hyb, hy⟩
  refine ⟨y, hyb, ?_⟩
  exact (Model.realize_fromBoundedFormula E phi
    (snoc (snoc params x) y)).mpr hy

end ZFC

end Constructible
