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

def forget : Under R ⥤ Type u := Under.forget R ⋙ HasForget.forget

-- noncomputable def tensorProd_freeAbs : freeAbs R ⋙ R.tensorProd S ≅ freeAbs S := by
--   let left : Type u ⥤ Under S := {
--     obj σ := S.mkUnder <| S ⊗[R] (MvPolynomial σ R)
--     map f := (Algebra.TensorProduct.map (AlgHom.id S S) (MvPolynomial.rename f)).toUnder
--     map_id σ := by
--       simp only
--       have : MvPolynomial.rename (𝟙 σ) = AlgHom.id R (MvPolynomial σ R) :=
--         MvPolynomial.rename_id (R := R) (σ := σ)
--       rw [this, Algebra.TensorProduct.map_id]
--       rfl
--     map_comp f g := by
--       simp only
--       have : MvPolynomial.rename (R := R) (f ≫ g) =
--         (MvPolynomial.rename g).comp (MvPolynomial.rename f) :=
--         (MvPolynomial.rename_comp_rename f g).symm
--       rw [this, Algebra.TensorProduct.map_id_comp, AlgHom.toUnder_comp]
--   }
--   have : freeAbs R ⋙ R.tensorProd S = left := by
--     have obj (σ : Type u) : (freeAbs R ⋙ R.tensorProd S).obj σ = left.obj σ := by
--       unfold freeAbs left tensorProd
--       simp only [Functor.comp_obj]
--       rw [algebra_eq]
--       rfl
--     #check eqToHom
--     have map (σ τ : Type u) (f : σ ⟶ τ) : (freeAbs R ⋙ R.tensorProd S).map f
--       = eqToHom (obj σ) ≫ left.map f ≫ eqToHom (obj τ).symm := by
--       unfold freeAbs left tensorProd
--       simp only [Functor.comp_obj, Functor.comp_map, id_eq, eq_mpr_eq_cast, AlgHom.toUnder_comp,
--         cast_eq]
--       sorry
--     exact CategoryTheory.Functor.ext obj map
--   rw [this]
--   -- let pointwise (σ : Type u) : left.obj σ ≅ (freeAbs S).obj σ := (MvPolynomial.algebraTensorAlgEquiv (σ := σ) R S).toUnder
--   -- unfold left
--   exact NatIso.ofComponents (fun σ => (MvPolynomial.algebraTensorAlgEquiv (σ := σ) R S).toUnder) (fun {σ τ} f => by
--     unfold freeAbs left
--     simp only
--     -- exact?
--     sorry
--   )



  -- let pointwise (σ : Type u) : (freeAbs R ⋙ R.tensorProd S).obj σ ≅ (freeAbs S).obj σ := by
  --   unfold freeAbs tensorProd
  --   simp only [Functor.comp_obj]
  --   rw [algebra_eq]
  --   exact (MvPolynomial.algebraTensorAlgEquiv (σ := σ) R S).toUnder
  -- exact NatIso.ofComponents pointwise (fun {σ τ} f => by
  --   unfold freeAbs tensorProd pointwise
  --   simp only [Functor.comp_obj, Functor.comp_map, eq_mpr_eq_cast, id_eq]
  --   #check MvPolynomial.aeval_one_tmul
  --   -- S ⊗[R] (MvPolynomial σ R) ≃ₐ[S] MvPolynomial σ S
  --   -- S ⊗[R] (MvPolynomial τ R) ≃ₐ[S] MvPolynomial τ S
  --   have : MvPolynomial σ R →ₐ[R] MvPolynomial τ R := MvPolynomial.rename f
  --   -- have : MvPolynomial σ R ⟶ MvPolynomial τ R := (MvPolynomial.rename f).toUnder

  --   have : S ⊗[R] (MvPolynomial σ R) ⟶ S ⊗[R] (MvPolynomial τ R) := by sorry
  --   -- The algebra_eq leads to some difficulties
  --   -- rw [algebra_eq]

  --   sorry
  -- )


-- /-- The freeAbs is given by `R ⊗[ℤ] ℤ [σ]`. -/


-- -- The free-forget adjunction given by polynomials.
-- #check MvPolynomial.rTensor
-- #check MvPolynomial.algebraTensorAlgEquiv
-- def foo {σ : Type u} : S ⊗[R] (MvPolynomial σ R) ≃ₐ[S] MvPolynomial σ S := by
--   exact MvPolynomial.algebraTensorAlgEquiv R S
end CommRingCat
