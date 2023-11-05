import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Types

universe v u

open CategoryTheory Limits

noncomputable
instance : CreatesLimitsOfSize.{u, u} uliftFunctor.{v, u} where
  CreatesLimitsOfShape {J} _ := {
    CreatesLimit := fun {K} => by
      refine @createsLimitOfFullyFaithfulOfIso _ _ _ _ _ _ K uliftFunctor _ _ _ (limit K) ?_
      sorry
      -- refine IsLimit.conePointUniqueUpToIso ?_ (limit.isLimit (K ⋙ uliftFunctor.{v, u}))
  }

instance : PreservesLimitsOfSize.{u, u} uliftFunctor where
  preservesLimitsOfShape {J} 𝒥 :=
    { preservesLimit := fun {K} =>
        { preserves := fun {c} t =>
            { lift := fun s x => sorry
              fac := fun s j => sorry
              uniq := fun s m w => sorry
              } } }
