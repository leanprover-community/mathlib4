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
def forgetRelative : Under S ⥤ Under R := Under.map <| ofHom Algebra.algebraMap

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

@[simp]
lemma freeAbs_obj (σ : Type u) : algebra ((freeAbs R).obj σ) = MvPolynomial.algebra :=
  mkUnder_eq <| MvPolynomial σ R

@[simp]
lemma freeAbs_map {σ τ : Type u} (f : σ ⟶ τ) :
    toAlgHom ((freeAbs R).map f) =
    (cast <| congr_arg₂
    (fun instA instB => @AlgHom R (MvPolynomial σ R) (MvPolynomial τ R) _ _ _ instA instB)
    (mkUnder_eq (MvPolynomial σ R)).symm
    (mkUnder_eq (MvPolynomial τ R)).symm) (MvPolynomial.rename f)
  := AlgHom.toUnder_eq (MvPolynomial.rename f)

def forget : Under R ⥤ Type u := Under.forget R ⋙ HasForget.forget

lemma tensorProd_freeAbs_tauto : freeAbs R ⋙ R.tensorProd S = {
    obj σ := S.mkUnder <| S ⊗[R] (MvPolynomial σ R)
    map f := (Algebra.TensorProduct.map (AlgHom.id S S) (MvPolynomial.rename f)).toUnder
    map_id σ := by
      simp only
      have : MvPolynomial.rename (𝟙 σ) = AlgHom.id R (MvPolynomial σ R) :=
        MvPolynomial.rename_id (R := R) (σ := σ)
      rw [this, Algebra.TensorProduct.map_id]
      rfl
    map_comp f g := by
      simp only
      have : MvPolynomial.rename (R := R) (f ≫ g) =
        (MvPolynomial.rename g).comp (MvPolynomial.rename f) :=
        (MvPolynomial.rename_comp_rename f g).symm
      rw [this, Algebra.TensorProduct.map_id_comp, AlgHom.toUnder_comp]
    } := by
  apply CategoryTheory.Functor.ext
  · intro σ τ f
    unfold freeAbs tensorProd
    dsimp
    rw [AlgHom.toUnder_eq]
    -- find out the path induction
    have (ninstσ : Algebra R (MvPolynomial σ R)) (ninstτ : Algebra R (MvPolynomial τ R))
        (eqσ : ninstσ = MvPolynomial.algebra) (eqτ : ninstτ = MvPolynomial.algebra) :
        (@Algebra.TensorProduct.map _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (ninstσ) _ _ _ _ _
        (ninstτ) (AlgHom.id S S)
        ((cast <| congr_arg₂ (fun instσ instτ => @AlgHom R (MvPolynomial σ R)
            (MvPolynomial τ R) _ _ _ instσ instτ)
        eqσ.symm eqτ.symm) (MvPolynomial.rename f))).toUnder =
        eqToHom (congr_arg
          (fun inst => S.mkUnder <| @TensorProduct R _ S (MvPolynomial σ R) _ _ _
          (@Algebra.toModule _ _ _ _ inst)) <| eqσ) ≫
        (@Algebra.TensorProduct.map _ _ _ _ _ _ _ _ _ _ _ _ _ _ MvPolynomial.algebra _ _ _ _ _
          MvPolynomial.algebra (AlgHom.id S S) (MvPolynomial.rename f)).toUnder ≫
        eqToHom (congr_arg
          (fun inst => S.mkUnder <| @TensorProduct R _ S (MvPolynomial τ R) _ _ _
          (@Algebra.toModule _ _ _ _ inst)) <| eqτ).symm := by
      subst eqσ eqτ
      rfl
    exact this (algebra (R.mkUnder (MvPolynomial σ R))) (algebra (R.mkUnder (MvPolynomial τ R)))
      (mkUnder_eq (MvPolynomial σ R)) (mkUnder_eq (MvPolynomial τ R))


-- noncomputable def tensorProd_freeAbs : freeAbs R ⋙ R.tensorProd S ≅ freeAbs S := by
--   -- To get rid of algebra_eq
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
--       ext x
--       -- simp only [AlgHom.toUnder_right,
--       --   Under.comp_right, Under.eqToHom_right, hom_comp, RingHom.coe_comp, Function.comp_apply]

--       #check AlgHom.toUnder_eq_core
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

  --   -- have : S ⊗[R] (MvPolynomial σ R) ⟶ S ⊗[R] (MvPolynomial τ R) := by sorry
  --   -- The algebra_eq leads to some difficulties
  --   -- rw [algebra_eq]
  --   ext x
  --   simp only [AlgHom.toUnder_eq, eq_mpr_eq_cast, cast_cast, Under.comp_right, hom_comp,
  --     RingHom.coe_comp, Function.comp_apply, AlgHom.toUnder_right]

  --   -- erw [← AlgHom.toUnder_eq]

  --   sorry
  -- )


-- /-- The freeAbs is given by `R ⊗[ℤ] ℤ [σ]`. -/


-- -- The free-forget adjunction given by polynomials.
-- #check MvPolynomial.rTensor
-- #check MvPolynomial.algebraTensorAlgEquiv
-- def foo {σ : Type u} : S ⊗[R] (MvPolynomial σ R) ≃ₐ[S] MvPolynomial σ S := by
--   exact MvPolynomial.algebraTensorAlgEquiv R S
end CommRingCat
