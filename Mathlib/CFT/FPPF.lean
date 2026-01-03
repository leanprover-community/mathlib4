import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {X Y S : Scheme.{u}} (f : X ⟶ Y)

/-- Being an isomorphism satisfies fppf descent. -/
@[stacks 02L4]
instance descendsAlong_isomorphisms_surjective_inf_flat_inf_locallyOfFinitePresentation :
    (MorphismProperty.isomorphisms Scheme.{u}).DescendsAlong
        (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) := by
  apply IsZariskiLocalAtTarget.descendsAlong
  rintro R X Y f g ⟨⟨h₁, h₂⟩, h₃⟩ H
  obtain ⟨V : X.Opens, hV, e⟩ := f.isOpenMap.exists_opens_image_eq_of_prespectralSpace
    f.continuous (by simp) isOpen_univ isCompact_univ
  refine MorphismProperty.of_isPullback_of_descendsAlong (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (.paste_vert (.of_hasPullback V.ι _) (.of_hasPullback f g)) ⟨⟨?_, inferInstance⟩,
      (quasiCompact_iff_compactSpace _).mpr (isCompact_iff_compactSpace.mp hV)⟩ ?_
  · exact ⟨fun x ↦ have ⟨y, hyV, e⟩ := e.ge (Set.mem_univ x); ⟨⟨y, hyV⟩, e⟩⟩
  dsimp [MorphismProperty.isomorphisms] at H ⊢
  infer_instance

end AlgebraicGeometry
