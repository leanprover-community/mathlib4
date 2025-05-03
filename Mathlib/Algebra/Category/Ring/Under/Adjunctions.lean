import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Category.Ring.Adjunctions

open TensorProduct CategoryTheory
universe u
variable {R S : CommRingCat.{u}}
variable [Algebra R S]

namespace CommRingCat

variable (R S) in
/-- The forgetful base change functor. -/
@[simps! map_right]
def forgetRelative : Under S ⥤ Under R := Under.map <| CommRingCat.ofHom Algebra.algebraMap

/-- The adjunction between `tensorProd R S` and `forgetRelative R S`. -/
@[simps! unit_app counit_app]
noncomputable def adjTensorForget : tensorProd R S ⊣ forgetRelative R S :=
  (Under.mapPushoutAdj (ofHom <| algebraMap R S)).ofNatIsoLeft ((R.tensorProdIsoPushout S).symm)

variable (R) in
/-- The free functor given by polynomials. -/
@[simps! map_right]
noncomputable def freeAbs : Type u ⥤ Under R where
  obj σ := R.mkUnder <| MvPolynomial σ R
  map f := (MvPolynomial.rename f).toUnder
  map_id σ := congr_arg (fun x => x.toUnder) <| MvPolynomial.rename_id (σ := σ) (R := R)
  map_comp f g := congr_arg (fun x => x.toUnder) (MvPolynomial.rename_comp_rename (R := R) f g).symm

noncomputable def tensorProd_freeAbs : freeAbs R ⋙ R.tensorProd S ≅ freeAbs S := by
  let pointwise (σ : Type u) : (freeAbs R ⋙ R.tensorProd S).obj σ ≅ (freeAbs S).obj σ := by
    unfold freeAbs tensorProd
    simp only [Functor.comp_obj]
    rw [algebra_eq]
    exact (MvPolynomial.algebraTensorAlgEquiv (σ := σ) R S).toUnder
  exact NatIso.ofComponents pointwise (fun {σ τ} f => by
    unfold freeAbs tensorProd pointwise
    simp only [Functor.comp_obj, Functor.comp_map, eq_mpr_eq_cast, id_eq]
    -- The algebra_eq leads to some difficulties
    -- rw [algebra_eq]

    sorry
  )


/-- The freeAbs is given by `R ⊗[ℤ] ℤ [σ]`. -/

def forget : Under R ⥤ Type u := Under.forget R ⋙ HasForget.forget


-- -- The free-forget adjunction given by polynomials.
-- #check MvPolynomial.rTensor
-- #check MvPolynomial.algebraTensorAlgEquiv
-- def foo {σ : Type u} : S ⊗[R] (MvPolynomial σ R) ≃ₐ[S] MvPolynomial σ S := by
--   exact MvPolynomial.algebraTensorAlgEquiv R S
end CommRingCat
