import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.Order.JordanHolder

open CategoryTheory Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

open Subobject Abelian.Subobject in
/-- The lattice of subobjects of an object in an abelian category is modular. -/
instance (A : C) : IsModularLattice (Subobject A) where
  sup_inf_le_assoc_of_le := by
    intro X Y Z hXZ
    suffices (⟨(X ⊔ Y) ⊓ Z, le_inf le_sup_left hXZ⟩ : Set.Ici X) =
      ⟨X ⊔ Y ⊓ Z, (le_sup_left : X ≤ X ⊔ (Y ⊓ Z))⟩ from (congrArg Subtype.val this).le
    apply (cokernelOrderIso X).symm.injective
    change («exists» _).obj ((X ⊔ Y) ⊓ Z) = («exists» _).obj (X ⊔ Y ⊓ Z)
    have hZ : (Subobject.pullback _).obj ((«exists» _).obj Z) = Z :=
      congrArg Subtype.val ((cokernelOrderIso X).apply_symm_apply ⟨Z, hXZ⟩)
    have hqX : («exists» _).obj X = ⊥ := (cokernelOrderIso X).symm.map_bot
    slice_lhs 0 1 =>
      rw [← hZ, Regular.exists_inf_pullback_eq_exists_inf,
      (existsPullbackAdj (cokernel.π X.arrow)).gc.l_sup, hqX, bot_sup_eq,
      ← Regular.exists_inf_pullback_eq_exists_inf, hZ,
      ← bot_sup_eq ((«exists» (cokernel.π X.arrow)).obj (Y ⊓ Z)),
      ← (cokernelOrderIso X).symm.map_bot]
    exact (existsPullbackAdj _).gc.l_sup.symm

namespace Abelian.Subobject

open CategoryTheory.Subobject

/-- The second isomorphism theorem: `(X ⊔ Y)/X ≅ Y/(X ⊓ Y)`. -/
noncomputable def supQuotientIsoQuotientInf {A : C} (X Y : Subobject A) :
    cokernel (X.ofLE (X ⊔ Y) le_sup_left) ≅
      cokernel ((X ⊓ Y).ofLE Y inf_le_right) := by
  let i := X.ofLE (X ⊔ Y) le_sup_left
  let j := Y.ofLE (X ⊔ Y) le_sup_right
  let e := (supMonoFactorisation X Y).e
  let f := j ≫ cokernel.π i
  haveI : StrongEpi e := by
    dsimp only [e]
    exact strongEpi_of_strongEpiMonoFactorisation
      (Abelian.imageStrongEpiMonoFactorisation (coprod.desc X.arrow Y.arrow))
      (supIsImage X Y)
  haveI : Epi (e ≫ cokernel.π i) := epi_comp' StrongEpi.epi (by
    dsimp only [i]
    change Epi (coequalizer.π _ 0)
    infer_instance)
  haveI : Epi f := by
    apply epi_of_epi_fac (f := coprod.desc 0 (𝟙 _))
      (h := e ≫ cokernel.π i)
    simp [e, f, i, j, supMonoFactorisation]
  let a := (X ⊓ Y).ofLE X inf_le_left
  let b := (X ⊓ Y).ofLE Y inf_le_right
  have hpb : IsPullback a b i j := by
    exact IsPullback.of_isLimit (PullbackCone.isLimitOfFactors
      X.arrow Y.arrow (X ⊔ Y).arrow i j
      (by simp [i]) (by simp [j]) (inf_isPullback X Y).cone
      (inf_isPullback X Y).isLimit)
  exact Abelian.isoCokernelKernel f ≪≫
    cokernel.mapIso _ _ (Abelian.isoKernelOfIsPullback hpb).symm (Iso.refl _) (by simp [b, f])

end Abelian.Subobject

end CategoryTheory
