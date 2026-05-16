import Mathlib
import Mathlib.RingTheory.GradedAlgebra.Map.DecompositionMap_SetLike
import Mathlib.RingTheory.GradedAlgebra.Map.AddSubmonoidSSup

universe u
variable {ι₁ ι₂ : Type u} [DecidableEq ι₁] [DecidableEq ι₂]

section AddCommMonoids
variable (f : ι₁ → ι₂)
variable {M : Type*}
variable [AddCommMonoid M] (ℳ : ι₁ → AddSubmonoid M)
variable [DirectSum.Decomposition ℳ]
#check (inferInstance : AddSubmonoidSSup (AddSubmonoid M) M)
instance : (DirectSum.Decomposition (DirectSum.Decomposition.map f ℳ)) :=
  DirectSum.Decomposition.map.decomposition f ℳ
#check (inferInstance : (DirectSum.Decomposition (DirectSum.Decomposition.map f ℳ)))
end AddCommMonoids

section AddCommGroups
variable (f : ι₁ → ι₂)
variable {M : Type*}
variable [AddCommGroup M] (ℳ : ι₁ → AddSubgroup M)
variable [DirectSum.Decomposition ℳ]
#check (inferInstance : AddSubmonoidSSup (AddSubgroup M) M)
instance : (DirectSum.Decomposition (DirectSum.Decomposition.map f ℳ)) :=
  DirectSum.Decomposition.map.decomposition f ℳ
#check (inferInstance : (DirectSum.Decomposition (DirectSum.Decomposition.map f ℳ)))
end AddCommGroups

section Modules
variable (f : ι₁ → ι₂)
variable {R M : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] (ℳ : ι₁ → Submodule R M)
variable [DirectSum.Decomposition ℳ]
#check (inferInstance : AddSubmonoidSSup (Submodule R M) M)
instance : (DirectSum.Decomposition (DirectSum.Decomposition.map f ℳ)) :=
  DirectSum.Decomposition.map.decomposition f ℳ
#check (inferInstance : (DirectSum.Decomposition (DirectSum.Decomposition.map f ℳ)))
end Modules

section Algebras
variable [AddCommMonoid ι₁] [AddCommMonoid ι₂]
variable (f : ι₁ →+ ι₂)
variable {R A : Type*}
variable [CommRing R] [Semiring A] [Algebra R A]
variable (𝒜 : ι₁ → Submodule R A) [GradedAlgebra 𝒜]

instance : (GradedAlgebra (DirectSum.Decomposition.map f 𝒜)) :=
  DirectSum.Decomposition.map.gradedRing f 𝒜
#check (inferInstance : (GradedAlgebra (DirectSum.Decomposition.map f 𝒜)))

end Algebras
