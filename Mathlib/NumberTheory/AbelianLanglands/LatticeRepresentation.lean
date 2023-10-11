import Mathlib.RepresentationTheory.Rep
import Mathlib.LinearAlgebra.FreeModule.Finite.Rank
import Mathlib.FieldTheory.Galois
import Mathlib.NumberTheory.AbelianLanglands.AlgebraicTorus

-- will have to restrict this when using `Rep` I guess?
universe v u
set_option autoImplicit false

def LatticeRepresentation (G : Type u) [Group G] (M : Type v) [AddCommGroup M]
    [Module ℤ M] [Module.Finite ℤ M] [Module.Free ℤ M] :=
  Representation ℤ G M

variable {F K : Type u} [Field F] [Field K] [Algebra F K] [IsGalois F K]

instance : Fact (Algebra.IsAlgebraic F K) :=
⟨fun x => IsIntegral.isAlgebraic F (IsSeparable.isIntegral F x)⟩

def LatticeRepresentation.toAffineGroupScheme {M : Type v} [AddCommGroup M] [Module ℤ M]
    [Module.Finite ℤ M] [Module.Free ℤ M]
    (ρ : LatticeRepresentation (K ≃ₐ[F] K) M) :
  AffineGroupScheme F := sorry

instance LatticeRepresentation.isAlgebraicTorus {M : Type v} [AddCommGroup M] [Module ℤ M]
    [Module.Finite ℤ M] [Module.Free ℤ M] (ρ : LatticeRepresentation (K ≃ₐ[F] K) M) :
  IsAlgebraicTorus F (Fin (FiniteDimensional.finrank ℤ M)) ρ.toAffineGroupScheme := sorry

variable (K) (σ : Type) [Fintype σ] (X : AffineGroupScheme F)

def IsAlgebraicTorus.toLatticeRep (σ : Type) [Fintype σ] (X : AffineGroupScheme F)
    [IsAlgebraicTorus F σ X] :
  LatticeRepresentation (K ≃ₐ[F] K) (Additive (CharGroup X)) := sorry

instance (M : Type v) [AddCommGroup M] [Module ℤ M] :
  AddCommGroup (M →+ (Additive Kˣ)) := by infer_instance

open Classical -- ????
open BigOperators

variable (σ : Type) [Fintype σ] (n : σ → ℤ) (i : σ)

open CategoryTheory

lemma splitTorusZPow_zpow {σ : Type} [Fintype σ] (n : σ → ℤ) (i : ℤ) :
  (splitTorusZPow F n) ^ i = splitTorusZPow F (i • n) := by
  refine' NatTrans.ext _ _ _
  ext A x
  dsimp
  simp only [charGroup_zpow_app, 𝔾ₘ_obj, 𝔾ₘObj_obj, splitTorusZPow_app, GroupCat.ofHom, MonoidHom.finset_prod_apply,
    MonoidHom.coe_comp, Function.comp_apply, zpowGroupHom_apply]
  dsimp
  ext
  dsimp
  simp only [Units.coe_prod, MonoidHom.coe_finset_prod]
  --edging towards a quarter life crisis I think
  sorry

lemma splitTorusZPow_prod_single {σ : Type} [Fintype σ] (n : σ → ℤ) :
    ∏ i in @Fintype.elems σ _, splitTorusZPow F (Pi.single i (n i)) = splitTorusZPow F n := by
  refine' NatTrans.ext _ _ _
  ext A x
  dsimp
  simp only [charGroup_prod_app, splitTorusZPow_app, GroupCat.ofHom]
  rw [MonoidHom.finset_prod_apply]
  simp only [MonoidHom.finset_prod_apply, MonoidHom.coe_comp, Function.comp_apply,
    zpowGroupHom_apply]
  congr 1
  ext j
  rw [Finset.prod_eq_single (β := Aˣ) j (fun b _ hb => by
    rw [Pi.single_eq_of_ne hb _, zpow_zero]) (fun h => False.elim (h (Fintype.complete j))),
    Pi.single_eq_same]

variable (F)

@[simps] noncomputable def toPointsSplit (σ : Type) [Fintype σ] :
  (CharGroup (splitTorus F σ) →* Fˣ) ≃* (σ → Fˣ) where
    toFun := fun f i => f (splitTorusZPow F (Pi.single i 1))
    invFun := fun x =>
      { toFun := fun y => y.app (CommAlg.of F F) x
        map_one' := by simp only [charGroup_one_app]; rfl
        map_mul' := fun y z => by simp only [charGroup_mul_app]; rfl }
    left_inv := fun x => by
      ext y
      dsimp
      simp only
      rcases splitTorusZPow_surjective F σ y with ⟨n, rfl⟩
      dsimp
      simp only [GroupCat.ofHom, MonoidHom.finset_prod_apply, MonoidHom.coe_comp,
        Function.comp_apply, zpowGroupHom_apply, Units.coe_prod, Units.val_zpow_eq_zpow_val]
      dsimp
      conv_rhs =>
        rw [←splitTorusZPow_prod_single]
      rw [map_prod]
      dsimp
      simp only [Units.coe_prod]
      rcongr j
      dsimp
      rw [Pi.evalMonoidHom_apply]
      rw [←Units.val_zpow_eq_zpow_val]
      rw [←map_zpow]
      rw [splitTorusZPow_zpow]
      rcongr a
      simp only [zsmul_eq_mul, Pi.coe_int, Int.cast_id]
      sorry
    right_inv := fun x => by
      dsimp
      funext j
      simp only [GroupCat.ofHom, ne_eq, MonoidHom.finset_prod_apply, MonoidHom.coe_comp,
        Function.comp_apply, zpowGroupHom_apply]
      rw [Finset.prod_eq_single (β := Fˣ) j (fun b _ hb => by
        rw [Pi.single_eq_of_ne hb _, zpow_zero]) (fun h => False.elim (h (Fintype.complete j))),
        Pi.single_eq_same]
      exact zpow_one _
    map_mul' := fun x y => rfl

variable {F}

noncomputable def toPoints (σ : Type) [Fintype σ] (X : AffineGroupScheme F) [IsAlgebraicTorus K σ X] :
  (CharGroup ((baseChange F K).obj X) →* Kˣ) ≃* (σ → Kˣ) :=
((mulEquivCharGroupOfIso (SplitsOver.iso K σ X)).monoidHomCongr
  (MulEquiv.refl _)).trans (toPointsSplit K σ)

@[simp] lemma toPoints_apply (σ : Type) [Fintype σ] (X : AffineGroupScheme F)
    [IsAlgebraicTorus K σ X] (f : CharGroup ((baseChange F K).obj X) →* Kˣ) (i : σ) :
    toPoints K σ X f i = f ((SplitsOver.iso K σ X).hom ≫ splitTorusZPow K (Pi.single i 1)) := by
  simp [toPoints, MulEquiv.trans_apply, MulEquiv.monoidHomCongr_apply,
    toPointsSplit_apply, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, MulEquiv.coe_refl,
    Function.comp_apply, id_eq, mulEquivCharGroupOfIso_apply]

variable (σ : Type) [Fintype σ] (X : AffineGroupScheme F) [IsAlgebraicTorus K σ X]
variable (F)

instance galOnUnits : MulDistribMulAction (K ≃ₐ[F] K) Kˣ where
  smul := fun f x => Units.map f x
  one_smul := fun b => by rfl -- haha just rfl doesn't work
  mul_smul := fun x y b => by rfl
  smul_mul := fun r x y => by exact map_mul _ _ _
  smul_one := fun r => by exact map_one _

@[simp] lemma galOnUnits_apply (g : K ≃ₐ[F] K) (x : Kˣ) :
    g • x = Units.map g x := rfl

instance galOnUnitsPi (σ : Type) : MulDistribMulAction (K ≃ₐ[F] K) (σ → Kˣ) :=
Pi.mulDistribMulAction _

@[simp] lemma galOnUnitsPi_apply {σ : Type} (g : K ≃ₐ[F] K) (x : σ → Kˣ) :
    g • x = fun i => Units.map g (x i) := rfl

variable {F}

noncomputable def charGroupApp (A : Type u) [CommRing A] [Algebra F A] [Algebra K A]
    [IsScalarTower F K A] (f : CharGroup ((baseChange F K).obj X)) : (σ → Aˣ) →* Aˣ :=
(f.app (CommAlg.of K A)).comp (SplitsOver.appIso K σ X A).symm

instance idk : MulDistribMulAction (K ≃ₐ[F] K)ᵐᵒᵖ ((σ → Kˣ) →* Kˣ) where
  smul := fun g f => {
    toFun := fun x => g.unop⁻¹ • f (g.unop • x)
    map_one' := by
      ext
      dsimp -- why does dsimp use galOnUnits_apply etc when they exist?
      simp only [map_one, MulEquivClass.map_eq_one_iff, Units.val_eq_one]
      exact map_one _
    map_mul' := fun x y => sorry
  }
  one_smul := sorry
  mul_smul := sorry
  smul_mul := sorry
  smul_one := sorry

def nsclif : CharGroup ((baseChange F K).obj X) := sorry

lemma nsclif_spec (g : (K ≃ₐ[F] K)ᵐᵒᵖ) (f : CharGroup ((baseChange F K).obj X)) :
    charGroupApp K σ X K (nsclif K X) = g • charGroupApp K σ X K f := sorry
#exit
def ummmmmmmm : MulDistribMulAction (K ≃ₐ[F] K)ᵐᵒᵖ (CharGroup ((baseChange F K).obj X)) where
  smul := fun g f => _
  one_smul := _
  mul_smul := _
  smul_mul := _
  smul_one := _
