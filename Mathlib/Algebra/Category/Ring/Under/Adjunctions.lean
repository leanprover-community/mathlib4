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

@[simp]
lemma freeAbs_obj (σ : Type u) : algebra ((freeAbs R).obj σ) = MvPolynomial.algebra :=
  mkUnder_eq <| MvPolynomial σ R

@[simp]
lemma freeAbs_map {σ τ : Type u} (f : σ ⟶ τ) :
    toAlgHom ((freeAbs R).map f) = (by
      rw [freeAbs_obj, freeAbs_obj]
      exact MvPolynomial.rename f
    ) := AlgHom.toUnder_eq (MvPolynomial.rename f)

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
    let obj := fun σ => congr_arg
            (fun inst => S.mkUnder <| @TensorProduct R _ S (MvPolynomial σ R) _ _ _
            (@Algebra.toModule _ _ _ _ inst)) <| freeAbs_obj σ
    apply CategoryTheory.Functor.ext
    #check eq_mpr_eq_cast
    -- have obj (σ : Type u) : (freeAbs R ⋙ R.tensorProd S).obj σ = _.obj σ := by
    --   unfold freeAbs left tensorProd
    --   simp only [Functor.comp_obj]
    --   rw [algebra_eq]
    --   rfl
    · intro σ τ f
      unfold freeAbs tensorProd
      dsimp
      -- #check AlgHom.toUnder_eq
      -- #check Algebra.TensorProduct.map
      -- #check MvPolynomial.algebra
      -- #check @Algebra.TensorProduct.map _ _ _ _ _ _ _ _ _ _ _ _ _ _
      --   MvPolynomial.algebra _ _ _ _ _  MvPolynomial.algebra (AlgHom.id S S)
      --   (MvPolynomial.rename f)
      #check (@Algebra.TensorProduct.map _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (algebra ((freeAbs R).obj σ)) _ _ _ _ _  (algebra ((freeAbs R).obj τ)) (AlgHom.id S S)
        (toAlgHom (MvPolynomial.rename f).toUnder)).toUnder
      -- rw [AlgHom.toUnder_eq]
      -- simp only [eq_mpr_eq_cast, cast_cast]
      -- #check proof_irrel_heq
      -- subst (freeAbs_obj σ)
      have : (@Algebra.TensorProduct.map _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (algebra ((freeAbs R).obj σ)) _ _ _ _ _  (algebra ((freeAbs R).obj τ)) (AlgHom.id S S)
        (toAlgHom (MvPolynomial.rename f).toUnder)).toUnder = eqToHom (congr_arg
            (fun inst => S.mkUnder <| @TensorProduct R _ S (MvPolynomial σ R) _ _ _
            (@Algebra.toModule _ _ _ _ inst)) <| mkUnder_eq <| MvPolynomial σ R) ≫
        (@Algebra.TensorProduct.map _ _ _ _ _ _ _ _ _ _ _ _ _ _ MvPolynomial.algebra _ _ _ _ _
          MvPolynomial.algebra (AlgHom.id S S) (MvPolynomial.rename f)).toUnder
        ≫ eqToHom (congr_arg
            (fun inst => S.mkUnder <| @TensorProduct R _ S (MvPolynomial τ R) _ _ _
            (@Algebra.toModule _ _ _ _ inst)) <| mkUnder_eq <| MvPolynomial τ R).symm := by
        rw [AlgHom.toUnder_eq]
        #check fun (instσ : Algebra R <| MvPolynomial σ R) (instτ : Algebra R <| MvPolynomial τ R)
          (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) => eqToHom (congr_arg
          (fun inst => S.mkUnder <| @TensorProduct R _ S (MvPolynomial σ R) _ _ _
          (@Algebra.toModule _ _ _ _ inst)) <| mkUnder_eq <| MvPolynomial σ R) ≫
          (@Algebra.TensorProduct.map _ _ _ _ _ _ _ _ _ _ _ _ _ _ instσ _ _ _ _ _
          instτ (AlgHom.id S S) φ).toUnder
          ≫ eqToHom (congr_arg
          (fun inst => S.mkUnder <| @TensorProduct R _ S (MvPolynomial τ R) _ _ _
          (@Algebra.toModule _ _ _ _ inst)) <| mkUnder_eq <| MvPolynomial τ R).symm
        have : (Algebra R <| MvPolynomial σ R) = (Algebra R <| R.mkUnder <| MvPolynomial σ R) := rfl
        #check Σ' (instσ : Algebra R (MvPolynomial σ R)), (instσ = MvPolynomial.algebra)
        let s1 : Σ' (instσ : Algebra R (MvPolynomial σ R)), (instσ = MvPolynomial.algebra) :=
          ⟨MvPolynomial.algebra,rfl⟩
        let s2 : Σ' (instσ : Algebra R (MvPolynomial σ R)), (instσ = MvPolynomial.algebra) :=
          ⟨algebra (R.mkUnder (MvPolynomial σ R)), mkUnder_eq (MvPolynomial σ R)⟩
        have : s1 = s2 := by
          -- rw [mkUnder_eq] -- (MvPolynomial σ R)]
          sorry
        -- let ccf :=
        --   fun (instσ : Algebra R <| MvPolynomial σ R) =>
        --   fun (instτ : Algebra R <| MvPolynomial τ R) =>
        --   fun (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) =>
        --   -- eqToHom (congr_arg
        --   -- (fun inst => S.mkUnder <| @TensorProduct R _ S (MvPolynomial σ R) _ _ _
        --   -- (@Algebra.toModule _ _ _ _ inst)) <| mkUnder_eq <| MvPolynomial σ R) ≫
        --   (@Algebra.TensorProduct.map _ _ _ _ _ _ _ _ _ _ _ _ _ _ instσ _ _ _ _ _
        --   instτ (AlgHom.id S S) φ).toUnder
          -- ≫ eqToHom (congr_arg
          -- (fun inst => S.mkUnder <| @TensorProduct R _ S (MvPolynomial τ R) _ _ _
          -- (@Algebra.toModule _ _ _ _ inst)) <| mkUnder_eq <| MvPolynomial τ R).symm
        -- have : R.mkUnder (MvPolynomial τ R) = MvPolynomial σ R := rfl
        -- have : Algebra R (R.mkUnder (MvPolynomial τ R)) = (Algebra R <| MvPolynomial σ R) := rfl
        -- have : (algebra (R.mkUnder (MvPolynomial τ R)) : Algebra R <| MvPolynomial τ R)
        --   = MvPolynomial.algebra := mkUnder_eq (R := R) (MvPolynomial τ R) (inst := MvPolynomial.algebra)
        #check congr_arg
        -- #check →
        -- #check Σ
        -- let ccf :=
          -- fun (⟨instσ, eqσ⟩ : Σ (instσ : Algebra R <| MvPolynomial σ R) → instσ = MvPolynomial.algebra) => sorry
        -- #check congr_arg (α := Algebra R <| MvPolynomial σ R) ccf (mkUnder_eq (R := R) (MvPolynomial σ R) (inst := MvPolynomial.algebra))
        -- let v := congr_arg ccf (mkUnder_eq (R := R) (MvPolynomial τ R) (inst := MvPolynomial.algebra))

        #check (mkUnder_eq (R := R) (MvPolynomial τ R) (inst := MvPolynomial.algebra))
        sorry
      -- subst AlgHom.toUnder_eq
      -- rw [AlgHom.toUnder_eq]
      -- aesop_cat
      sorry
    ·
      exact obj
        -- fun σ => congr_arg (fun inst => S.mkUnder <| @TensorProduct R _ S (MvPolynomial σ R) _ _ _
        --     (@Algebra.toModule _ _ _ _ inst)) <| freeAbs_obj σ
      -- unfold freeAbs tensorProd
      -- dsimp
      -- -- #check algebra
      -- suffices algebra (R.mkUnder (MvPolynomial σ R)) = MvPolynomial.algebra from by
      --   -- #check @S.mkUnder S _
      --   #check TensorProduct

      --   #check @Algebra.toModule _ _ _ _ MvPolynomial.algebra
      --   #check @Algebra.toModule _ _ _ _ (algebra (R.mkUnder (MvPolynomial σ R)))
      --   #check NonUnitalNonAssocSemiring.toAddCommMonoid
      --   #check @TensorProduct R _ S (MvPolynomial σ R) _ _ _ (@Algebra.toModule _ _ _ _ MvPolynomial.algebra)
      --   #check @TensorProduct R _ S (MvPolynomial σ R) _ _ _ (@Algebra.toModule _ _ _ _ (algebra (R.mkUnder (MvPolynomial σ R))))
      --   exact congr_arg (fun inst => S.mkUnder <| @TensorProduct R _ S (MvPolynomial σ R) _ _ _ (@Algebra.toModule _ _ _ _ inst)) <| freeAbs_obj σ
      -- exact freeAbs_obj σ
      -- have : S ⊗[R] (R.mkUnder (MvPolynomial σ ↑R)).right = sorry := sorry
      -- -- apply congr_arg S.mkUnder
      -- sorry

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
