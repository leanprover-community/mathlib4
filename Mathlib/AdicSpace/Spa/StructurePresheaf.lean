import Mathlib.AdicSpace.Spa.RationalOpenData
import Mathlib.Topology.Category.TopCommRingCat
import Mathlib.Topology.Sheaves.Presheaf

universe u

open Topology CategoryTheory TopologicalSpace UniformSpace

namespace spa

-- Wedhorn Proposition 8.2(1)
noncomputable def rationalOpenData.uniqueOfLE
    {A : HuberPair} (r s : rationalOpenData A) (h : r ≤ s) :
    Unique (Completion s.Localization →A[A] Completion r.Localization) :=
  sorry

attribute [-instance] UniformSpace.Completion.ring

noncomputable def rationalOpenData.topAlgHomOfLE
    {A : HuberPair} (r s : rationalOpenData A) (h : r ≤ s) :
    Completion s.Localization →A[A] Completion r.Localization :=
  letI := uniqueOfLE r s h
  default

lemma rationalOpenData.topAlgHom_eq {A : HuberPair} (r s : rationalOpenData A) (h : r ≤ s)
    (f : Completion s.Localization →A[A] Completion r.Localization) :
    rationalOpenData.topAlgHomOfLE r s h = f := by
  letI := uniqueOfLE r s h
  exact Subsingleton.elim _ _

end spa

noncomputable def spa.presheafOnRationalOpenDataAlg (A : HuberPair) :
    (rationalOpenData A)ᵒᵖ ⥤  TopAlgCat A where
  obj r := TopAlgCat.of A (Completion r.unop.Localization)
  map h := TopAlgCat.ofHom A (rationalOpenData.topAlgHomOfLE _ _ h.unop.1.1)
  map_id _ := by
    apply ConcreteCategory.ext
    apply rationalOpenData.topAlgHom_eq
  map_comp _ _ := by
    apply ConcreteCategory.ext
    apply rationalOpenData.topAlgHom_eq

noncomputable def spa.presheafOnRationalOpenData (A : HuberPair) :
    (rationalOpenData A)ᵒᵖ ⥤  TopCommRingCat :=
  presheafOnRationalOpenDataAlg A ⋙ forget₂ _ _

def spa.rationalOpenDataToOpens (A : HuberPair) : rationalOpenData A ⥤ Opens (spa A) where
  obj r := ⟨r.openSet, r.openSet_isOpen⟩
  map h := h

open TopCat

noncomputable def spa.presheaf (A : HuberPair.{u}) : Presheaf TopCommRingCat.{u} (of (spa A)) :=
  (rationalOpenDataToOpens A).op.pointwiseRightKanExtension (spa.presheafOnRationalOpenData A)
