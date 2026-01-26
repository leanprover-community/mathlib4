
/-!
# AB axioms in the category of ind-objects

We show that `Ind C` satisfies Grothendieck's axiom AB5 if `C` has finite limits and deduce that
`Ind C` is Grothendieck abelian if `C` is small and abelian.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

section

variable {C : Type u} [Category.{v} C]

instance {J : Type v} [SmallCategory J] [IsFiltered J] [HasFiniteLimits C] :
    HasExactColimitsOfShape J (Ind C) :=
  HasExactColimitsOfShape.domain_of_functor J (Ind.inclusion C)

instance [HasFiniteLimits C] : AB5 (Ind C) where
  ofShape _ _ _ := inferInstance

end

section

variable {C : Type u} [SmallCategory C] [Abelian C]

instance isGrothendieckAbelian_ind : IsGrothendieckAbelian.{u} (Ind C) where
  hasSeparator := ⟨⟨_, Ind.isSeparator_range_yoneda⟩⟩

end

end CategoryTheory.Limits
