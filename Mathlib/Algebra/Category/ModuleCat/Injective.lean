import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.Projective
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.LinearAlgebra.FinsuppVectorSpace
import Mathlib.Data.Finsupp.Basic
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.Algebra.Category.GroupCat.Abelian

/-!
# The category of `R`-modules has enough injectives.
-/

universe v u

open CategoryTheory

open CategoryTheory.Limits

open LinearMap

open ModuleCat

open scoped Module

set_option maxHeartbeats 0

/-- The categorical notion of injective object agrees with the explicit module-theoretic notion. -/
theorem IsInjective.iff_injective {R : Type _} [Ring R] {P : Type _} [AddCommGroup P]
    [Module R P] : Module.Injective R P ↔ Injective (ModuleCat.of R P) := by
    refine' ⟨fun h => ⟨_⟩, fun h => ⟨_⟩⟩
    . intros X Y g f hf
      have Hf : Function.Injective f := Iff.mp (ModuleCat.mono_iff_injective f) hf
      rcases h.out X Y f Hf g with ⟨w, hw⟩
      use w; ext x; exact hw x
    . intros X Y _ _ _ _ f hf g
      sorry
  -- refine' ⟨fun h => _, fun h => _⟩
  -- · letI : Module.Projective R (ModuleCat.of R P) := h
  --   exact ⟨fun E X epi => Module.projective_lifting_property _ _
  --     ((ModuleCat.epi_iff_surjective _).mp epi)⟩
  -- · refine' Module.Projective.of_lifting_property.{u,v} _
  --   intro E X mE mX sE sX f g s
  --   haveI : Epi (↟f) := (ModuleCat.epi_iff_surjective (↟f)).mpr s
  --   letI : Projective (ModuleCat.of R P) := h
  --   exact ⟨Projective.factorThru (↟g) (↟f), Projective.factorThru_comp (↟g) (↟f)⟩

namespace ModuleCat

variable {R : Type u} [Ring R] {M : ModuleCat.{max u v} R}


/-
Want to show R-mod has enough injectives. Let M be an R-Module
Let I(M) be a product of I₀ := Hom_Ab(M, ℚ ⧸ ℤ), indexed by Hom_R(M, I₀).
Then I is injective
There is a map e_M : M → I(M) which is injective
-/

-- ℚ ⧸ ℤ, in Ab:
#check Ab
#check (⟨ℚ,_⟩ : Ab)


example : DivisibleBy ℚ ℤ := by infer_instance


-- ℚ ⧸ ℤ injective


-- Hom_Ab(M, ℚ / ℤ), in R-Mod


--Proof that I₀ is injective


--Proof that Π I₀ is injective:
#check Injective.instInjectivePiObj


--definition of the map M → I(M)


--injectivity of the map


--#check (ℚ ⧸ ℤ) : AddCommGroupCat

instance moduleCat_enoughInjectives : EnoughInjectives (ModuleCat.{max u v} R) where
presentation M :=
    ⟨{  J := ModuleCat.of R (M →₀ R)
        injective := sorry
        f := sorry
        mono := sorry }⟩

end ModuleCat
