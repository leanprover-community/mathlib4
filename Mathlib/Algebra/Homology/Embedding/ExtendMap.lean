import Mathlib.Algebra.Homology.Embedding.Extend

open CategoryTheory Category Limits ZeroObject

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
variable {C D : Type*} [Category C] [HasZeroObject C] [HasZeroMorphisms C]
  [Category D] [HasZeroObject D] [HasZeroMorphisms D]

namespace HomologicalComplex

variable (K L : HomologicalComplex C c) (φ : K ⟶ L) (e : c.Embedding c') (F : C ⥤ D)
  [F.PreservesZeroMorphisms]

noncomputable def mapExtendX :
    ∀ (i : Option ι), F.obj (extend.X K i) ≅ extend.X ((F.mapHomologicalComplex c).obj K) i
  | none => F.mapZeroObject
  | some _ => Iso.refl _

lemma mapExtendX_hom_eq {i : Option ι} {j : ι} (hj : i = some j) :
    mapExtendX K F i = eqToIso (by
      subst hj
      rfl) := by
  subst hj
  rfl

@[pp_dot]
noncomputable def mapExtendIso :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e :=
  Hom.isoOfComponents (fun _ => mapExtendX _ _ _) (fun i' j' h => by
    by_cases hi' : ∃ i, e.f i = i'
    · by_cases hj' : ∃ j, e.f j = j'
      · obtain ⟨i, rfl⟩ := hi'
        obtain ⟨j, rfl⟩ := hj'
        dsimp
        simp [mapExtendX_hom_eq _ _ (e.r_f _), extend_d_eq _ e rfl rfl, extendXIso,
          extend.XIso, eqToHom_map]
      · apply IsZero.eq_of_tgt
        apply isZero_extend_X
        simpa using hj'
    · apply IsZero.eq_of_src
      apply Functor.map_isZero
      apply isZero_extend_X
      simpa using hi')

variable {K L}

@[reassoc (attr := simp)]
lemma mapExtensIso_hom_f_naturality (i' : ι') :
    F.map ((extendMap φ e).f i') ≫ (L.mapExtendIso e F).hom.f i' =
    (K.mapExtendIso e F).hom.f i' ≫ (extendMap ((F.mapHomologicalComplex c).map φ) e).f i' := by
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    simp [extendMap_f _ _ rfl, extendXIso, mapExtendIso, extend.XIso, eqToHom_map,
      mapExtendX_hom_eq _ _ (e.r_f i)]
  · apply IsZero.eq_of_tgt
    apply isZero_extend_X
    simpa using hi'

end HomologicalComplex

namespace ComplexShape

namespace Embedding

variable (e : c.Embedding c') (F : C ⥤ D) [F.PreservesZeroMorphisms]

noncomputable def mapExtendFunctorNatIso :
    e.extendFunctor C ⋙ F.mapHomologicalComplex c' ≅
      F.mapHomologicalComplex c ⋙ e.extendFunctor D :=
  NatIso.ofComponents (fun K => K.mapExtendIso e F)


end Embedding

end ComplexShape
