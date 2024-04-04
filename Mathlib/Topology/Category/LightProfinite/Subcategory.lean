import Mathlib.Topology.Category.LightProfinite.Maps

universe u

open CategoryTheory Limits

namespace LightProfinite

def hasSurjectiveTransitionMaps (X : LightProfinite) : Prop :=
  ∀ n, Function.Surjective (X.transitionMap n)

def surj := FullSubcategory hasSurjectiveTransitionMaps

instance : Category surj := FullSubcategory.category _

@[simps]
def surj_isoMk {X Y : surj} (i : X.1 ≅ Y.1) : X ≅ Y where
  hom := i.hom
  inv := i.inv
  hom_inv_id := i.hom_inv_id
  inv_hom_id := i.inv_hom_id

@[simps]
noncomputable def equivSurj : surj ≌ LightProfinite where
  functor := fullSubcategoryInclusion _
  inverse := {
    obj := fun X ↦ ⟨ofIsLight X.toProfinite, transitionMap_surjective _⟩
    map := fun f ↦ ((iso _).inv ≫ f ≫ (iso _).hom : _) }
  unitIso := NatIso.ofComponents (fun X ↦ surj_isoMk (iso X.1))
  counitIso := NatIso.ofComponents (fun X ↦ (iso X).symm)

instance (X : surj) (n : ℕ) :
    Epi (X.obj.transitionMap n) := by
  rw [FintypeCat.epi_iff_surjective]
  exact X.property n

instance (X : surj) {n m : ℕ} (h : n ≤ m) : Epi (X.obj.transitionMapLE h) := by
  induction h with
  | refl =>
    change Epi (X.obj.diagram.map (𝟙 _))
    simp only [CategoryTheory.Functor.map_id]
    infer_instance
  | @step k h ih =>
    have : Epi ((transitionMap X.obj k ≫
      (transitionMapLE X.obj h))) := epi_comp _ _
    convert this
    simp only [transitionMapLE, transitionMap, ← Functor.map_comp]
    congr
