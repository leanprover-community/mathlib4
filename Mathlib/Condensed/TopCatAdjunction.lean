import Mathlib.Condensed.TopComparison

universe u

open Condensed CondensedSet CategoryTheory

attribute [local instance] ConcreteCategory.instFunLike

variable (X : CondensedSet.{u})

namespace CondensedSet

private def _root_.CompHaus.const (S : CompHaus.{u}) (s : S) : CompHaus.of PUnit ⟶ S :=
  ContinuousMap.const _ s

private def coinducingCoprod :
    (Σ (i : (S : CompHaus.{u}) × X.val.obj ⟨S⟩), i.fst) → X.val.obj ⟨CompHaus.of PUnit⟩ :=
  fun ⟨⟨S, i⟩, s⟩ ↦ X.val.map (S.const s).op i

instance : TopologicalSpace (X.val.obj ⟨CompHaus.of PUnit⟩) :=
  TopologicalSpace.coinduced (coinducingCoprod X) inferInstance

def toTopCat : TopCat.{u+1} := TopCat.of (X.val.obj ⟨CompHaus.of PUnit⟩)

variable {X} {Y : CondensedSet} (f : X ⟶ Y)

def toTopCatMap : X.toTopCat ⟶ Y.toTopCat where
  toFun := f.val.app ⟨CompHaus.of PUnit⟩
  continuous_toFun := by
    rw [continuous_coinduced_dom]
    apply continuous_sigma
    intro ⟨S, x⟩
    simp only [Function.comp_apply, coinducingCoprod]
    have : (fun (a : S) ↦ f.val.app ⟨CompHaus.of PUnit⟩ (X.val.map (S.const a).op x)) =
        (fun (a : S) ↦ Y.val.map (S.const a).op (f.val.app ⟨S⟩ x)) :=
      funext fun a ↦ NatTrans.naturality_apply f.val (S.const a).op x
    rw [this]
    suffices ∀ (i : (T : CompHaus.{u}) × Y.val.obj ⟨T⟩),
        Continuous (fun (a : i.fst) ↦ Y.coinducingCoprod ⟨i, a⟩) from this ⟨_, _⟩
    rw [← continuous_sigma_iff]
    apply continuous_coinduced_rng

end CondensedSet

def condensedSetToTopCat : CondensedSet.{u} ⥤ TopCat.{u+1} where
  obj X := X.toTopCat
  map f := toTopCatMap f

namespace CondensedSet

def topCatAdjunction : condensedSetToTopCat ⊣ topCatToCondensedSet := sorry

end CondensedSet
