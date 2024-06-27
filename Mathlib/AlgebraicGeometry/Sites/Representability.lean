import Mathlib.CategoryTheory.MorphismProperty.Presheaf
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-
## Representability

https://stacks.math.columbia.edu/tag/01JF
-/

namespace AlgebraicGeometry

open CategoryTheory

universe u

variable (X : Scheme.{u})

abbrev openImmersion : MorphismProperty (Scheme.{u}) := @IsOpenImmersion

#check Presheaf.IsLocallySurjective

variable (F : Sheaf (Scheme.zariskiTopology.{u}) (Type u)) {ι : Type u}
  {X : ι → Scheme.{u}} (f : (i : ι) → yoneda.obj (X i) ⟶ F.1)
  (hf : ∀ i, openImmersion.presheaf (f i))
  [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Limits.Sigma.desc f)]

-- IsLocal
namespace Scheme

namespace Representability

noncomputable def glueData : GlueData where
  J := ι
  U := X
  V := fun (i, j) ↦ (hf i).representable.pullback (f j)
  f i j := (hf i).representable.fst (f j)
  f_mono := sorry
  f_id := sorry
  t i j := (hf i).representable.symmetry (hf j).representable
  t_id := sorry
  t' i j k := by
    dsimp
    fapply Limits.pullback.lift
    · fapply (hf _).representable.lift'
      · refine Limits.pullback.fst ≫ ?_
        refine (hf _).representable.snd _
      · refine Limits.pullback.snd ≫ ?_
        refine (hf _).representable.snd _
      · sorry
      -- apply condition
    · fapply (hf _).representable.lift'
      · refine Limits.pullback.fst ≫ ?_
        refine (hf _).representable.snd _
      · refine Limits.pullback.snd ≫ ?_
        refine (hf _).representable.fst _
      · sorry
      -- apply condition
    · sorry
  t_fac := sorry
  cocycle := sorry
  f_open := sorry

end Representability

open Representability

theorem representability_is_local : F.1.Representable where
  has_representation := by
    use (glueData F f hf).gluedScheme
    constructor
    sorry


end Scheme


example : True := by
  let a := ∐ (fun i => yoneda.obj (X i))
  let b := Limits.Sigma.desc f
  trivial

--

end AlgebraicGeometry
