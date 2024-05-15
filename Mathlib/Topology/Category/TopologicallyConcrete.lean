import Mathlib.Topology.Category.LightProfinite.Limits

-- variable (C : Type*) [Category C] [ConcreteCategory C]

-- class TopologicallyConcrete where
--   topologicalSpace (X : C) : TopologicalSpace ((forget C).obj X)
--   continuousMaps (X Y : C) : ContinuousMapClass (X ⟶ Y) ((forget C).obj X) ((forget C).obj Y)

-- attribute [instance] TopologicallyConcrete.topologicalSpace
-- attribute [instance] TopologicallyConcrete.continuousMaps

-- example : TopologicallyConcrete LightProfinite where
--   topologicalSpace _ := inferInstance
--   continuousMaps _ _ := ⟨fun f ↦ f.continuous⟩

-- class CompHausLike extends TopologicallyConcrete C where
--   compactSpace (X : C) : CompactSpace ((forget C).obj X)
--   t2Space (X : C) : T2Space ((forget C).obj X)

-- example : CompHausLike LightProfinite where
--   topologicalSpace _ := inferInstance
--   continuousMaps _ _ := ⟨fun f ↦ f.continuous⟩
--   compactSpace _ := inferInstance
--   t2Space _ := inferInstance

-- attribute [instance] CompHausLike.compactSpace
-- attribute [instance] CompHausLike.t2Space

-- def CompHausLike.toCompHaus [CompHausLike C] : C ⥤ CompHaus where
--   obj X := CompHaus.of ((forget C).obj X)
--   map f := ⟨(forget C).map f, ContinuousMapClass.map_continuous f⟩

-- instance [CompHausLike C] : (CompHausLike.toCompHaus C).Faithful where
--   map_injective h := by
--     ext x
--     rw [DFunLike.ext_iff] at h
--     exact h x

-- class CompHausLikeFull extends CompHausLike C where
--   full : (CompHausLike.toCompHaus C).Full

-- variable {C} in
-- noncomputable def CompHausLike.of [CompHausLikeFull C] (X : CompHaus)
--     (hX : X ∈ (CompHausLike.toCompHaus C).essImage) : C := Functor.essImage.witness hX

-- -- class CompHausLikeWithFiniteCoproducts extends CompHausLikeFull C where
-- --   preservesFiniteCoproducts : Limits.PreservesFiniteCoproducts (CompHausLike.toCompHaus C)
