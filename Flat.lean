import Mathlib.RingTheory.Flat
import Mathlib.Algebra.Algebra.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.RightExactness


/-
* TODO:
  Flatness/faithful in terms of functor
  Finish Faithful flatness TFAE

-/

universe u v w

open TensorProduct

open LinearMap

open CategoryTheory

--open Functor

namespace ModuleCat

variable {R : Type u} [CommRing R] (M : ModuleCat.{v} R)

-- need to look over a good chunk of this section
namespace HomFunctor

variable (N : ModuleCat.{v} R)

-- mostly just modeling code, idk if I should remove this or not as it is a single line
def obj' : ModuleCat R where
  carrier := M ⟶ N

def map' {N L : ModuleCat.{v} R} (g : N ⟶ L) : obj' M N ⟶ obj' M L where
  toFun := g.comp
  map_add' f f' := LinearMap.comp_add f f' g
  map_smul' := comp_smul g

end HomFunctor


section homFunctor

-- may need to generalize further (MonCat?)
def homFunctor : ModuleCat.{v} R ⥤ ModuleCat.{v} R where
  obj :=  HomFunctor.obj' M
  map := HomFunctor.map' M


variable (N : ModuleCat.{v} R)

-- @[simp]
-- lemma homFunctor.obj_eqHom : (homFunctor M).obj N = (M ⟶ N) := rfl

def homFunctor.obj_to_hom : (homFunctor M).obj N →ₗ[R] M ⟶ N where
  toFun f := f --𝟙 (M ⟶ N)
  map_add' := by simp only [forall_const]
  map_smul' := by simp only [RingHom.id_apply, forall_const]

def homFunctor.hom_to_obj : (M ⟶ N) →ₗ[R] (homFunctor M).obj N where
  toFun f := f
  map_add' := by simp only [forall_const]
  map_smul' := by simp only [RingHom.id_apply, forall_const]

@[simp]
lemma homFunctor.obj_to_hom_to_obj_eq_id :
  (obj_to_hom M N) ∘ (hom_to_obj M N) = 𝟙 (homFunctor M).obj N := rfl

@[simp]
lemma homFunctor.hom_to_obj_to_hom_eq_id :
  (hom_to_obj M N) ∘ (obj_to_hom M N) = 𝟙 (M ⟶ N) := rfl

@[simp]
lemma homFunctor.obj_to_hom_eq (f : M ⟶ N) : obj_to_hom M N f = f := rfl

@[simp]
lemma homFunctor.hom_to_obj_eq (f : (homFunctor M).obj N) : hom_to_obj M N f = f := rfl

def homFunctor.obj_hom_equiv : (homFunctor M).obj N ≃ₗ[R] M ⟶ N where
  toFun := obj_to_hom M N
  map_add' := (obj_to_hom M N).map_add'
  map_smul' := (obj_to_hom M N).map_smul'
  invFun := hom_to_obj M N
  left_inv := by
    dsimp [Function.LeftInverse]
    simp only [forall_const]
  right_inv := by
    dsimp [Function.RightInverse, Function.LeftInverse]
    simp only [forall_const]

end homFunctor

-- @[simp]
-- lemma homFunctor.obj_to_hom_apply (f : M ⟶ N) (m : M) : obj_to_hom f m = f m := by
--   unfold obj_to_hom
--   rfl

@[ext]
lemma homFunctor.ext {f g : (homFunctor M).obj N} (h : ∀ m, f.toFun m = g.toFun m) : f = g :=
  LinearMap.ext h



-- lemma homFunctor.ForgetOfHomIs : Functor.hom (ModuleCat.{v} R) := sorry



-- namespace TensorProduct

-- noncomputable def robj (N : ModuleCat.{v} R) : ModuleCat R where
--   carrier := N ⊗[R] M

-- noncomputable def lobj (N : ModuleCat.{v} R) : ModuleCat R where
--   carrier := M ⊗[R] N

-- -- noncomputable def rmap' {N L : ModuleCat.{v} R} (f : N ⟶ L) : robj' M N ⟶ robj' M L where
-- --   toFun := f.rTensor M
-- --   map_add' := map_add <| f.rTensor M
-- --   map_smul' := map_smul <| f.rTensor M

-- noncomputable def rmap {N L : ModuleCat.{v} R} (f : N ⟶ L) : robj M N ⟶ robj M L :=
--   ofHom <| rTensor M f

-- noncomputable def lmap {N L : ModuleCat.{v} R} (f : N ⟶ L) : lobj M N ⟶ lobj M L :=
--   ofHom <| lTensor M f

-- end TensorProduct

suppress_compilation

def rTensorFunctor : ModuleCat.{v} R ⥤ ModuleCat.{v} R where
  obj N := of R (N ⊗[R] M)
  map f := ofHom <| rTensor M f
  map_id N := rTensor_id M N
  map_comp f g := rTensor_comp M g f

def lTensorFunctor : ModuleCat.{v} R ⥤ ModuleCat.{v} R where
  obj N := of R (M ⊗[R] N)
  map f := ofHom <| lTensor M f
  map_id N := lTensor_id M N
  map_comp f g := lTensor_comp M g f

--used MonoidalCat tensor stuff here, idea was for compatibility reasons, but it seems
-- lean is smart enough that it just made dsimp work worse
-- noncomputable def rTensorFunctor : ModuleCat.{v} R ⥤ ModuleCat.{v} R where
--   obj N := MonoidalCategory.tensorObj N M
--   map f := MonoidalCategory.tensorHom f <| 𝟙 M
--   map_id N := rTensor_id M N
--   map_comp f g := rTensor_comp M g f

-- noncomputable def lTensorFunctor : ModuleCat.{v} R ⥤ ModuleCat.{v} R where
--   obj N :=  MonoidalCategory.tensorObj M N
--   map f :=  MonoidalCategory.tensorHom (𝟙 M) f
--   map_id N := lTensor_id M N
--   map_comp f g := lTensor_comp M g f
@[simp]
lemma rTensorFunctor.map_apply {N L : ModuleCat.{v} R} (f : N ⟶ L) (m : M) (n : N) :
  (rTensorFunctor M).map f (n ⊗ₜ m) = f n ⊗ₜ m := rfl

@[simp]
lemma lTensorFunctor.map_apply {N L : ModuleCat.{v} R} (f : N ⟶ L) (m : M) (n : N) :
  (lTensorFunctor M).map f (m ⊗ₜ n) =  m ⊗ₜ (f n) := rfl


def TensorFunctorsNatIso : rTensorFunctor M ≅ lTensorFunctor M where
  hom := {
    app := fun _ => (TensorProduct.comm R _ M).toLinearMap
    naturality := fun _ _ _ => by
      apply TensorProduct.ext'
      intro n m
      rfl
  }
  inv := {
    app := fun _ => (TensorProduct.comm R _ M).symm.toLinearMap
    naturality := fun _ _ _ => by
      apply TensorProduct.ext'
      intro n m
      rfl
  }
  hom_inv_id := by
    ext N x
    apply Equiv.leftInverse_symm <| (TensorProduct.comm R N M).toEquiv
  inv_hom_id := by
    ext N x
    apply Equiv.rightInverse_symm <| (TensorProduct.comm R N M).toEquiv

instance rTensorFunctorPreservesZeroMorphisms : Functor.PreservesZeroMorphisms (rTensorFunctor M) where
  map_zero := fun _ _ => rTensor_zero M

instance lTensorFunctorPreservesZeroMorphisms : Functor.PreservesZeroMorphisms (lTensorFunctor M) where
  map_zero := fun _ _ => lTensor_zero M


namespace TensorHomFunctorsAdj

def HomEquiv (N L : ModuleCat.{v} R) :
  ((rTensorFunctor M).obj N ⟶ L) ≃ (N ⟶ (homFunctor M).obj L) where
    toFun := curry
    invFun := uncurry R N M L --fix namespace bloat****
    left_inv := (lift.equiv R N M L).right_inv
    right_inv := (lift.equiv R N M L).left_inv

def UnitApp (N : ModuleCat.{v} R) :
  (𝟭 (ModuleCat R)).obj N ⟶ (rTensorFunctor M ⋙ homFunctor M).obj N where
    toFun n := {
      toFun := tmul R n
      map_add' := tmul_add n
      map_smul' := by simp only [tmul_smul, RingHom.id_apply, forall_const]
    }
    map_add' n₁ n₂ := by
      simp only [Functor.comp_obj, Functor.id_obj]
      ext m
      simp [add_tmul]
      rfl
    map_smul' _ _ := rfl


def CounitApp (N : ModuleCat.{v} R) :
  (homFunctor M ⋙ rTensorFunctor M).obj N ⟶ (𝟭 (ModuleCat R)).obj N :=
    uncurry R (M ⟶ N) M N <| ofHom (homFunctor.obj_to_hom M N)
    -- toFun := by
    --   simp at *
    --   sorry
    -- map_add' := sorry
    -- map_smul' := sorry

@[simp]
def CounitApp_apply (N : ModuleCat.{v} R) (f : (M ⟶ N)) (m : M) :
  CounitApp M N (f ⊗ₜ m) = f m := by erw [uncurry_apply]


def CounitNat {N L : ModuleCat.{v} R} (f : N ⟶ L) :
  (rTensorFunctor M).map ((homFunctor M).map f) ≫ CounitApp M L = CounitApp M N ≫ f := by
    apply TensorProduct.ext'
    intro f m
    erw [CounitApp_apply]

end TensorHomFunctorsAdj


def rTensorFunctorHomFunctorAdj : rTensorFunctor M ⊣ homFunctor M where
  homEquiv := TensorHomFunctorsAdj.HomEquiv M
  unit := {app := TensorHomFunctorsAdj.UnitApp M }
  counit := {
      app := TensorHomFunctorsAdj.CounitApp M
      naturality := fun _ _ f => TensorHomFunctorsAdj.CounitNat M f
      }
  homEquiv_counit := by
    intro N L g
    apply TensorProduct.ext'
    intro n m
    simp only [Functor.id_obj, Function.comp_apply, rTensorFunctor.map_apply]
    rfl


def lTensorFunctorHomFunctorAdj : lTensorFunctor M ⊣ homFunctor M :=
  Adjunction.ofNatIsoLeft (rTensorFunctorHomFunctorAdj M) (TensorFunctorsNatIso M)

instance rTensorFunctorPreservesColimits : Limits.PreservesColimits (rTensorFunctor M) :=
  Adjunction.leftAdjointPreservesColimits <| rTensorFunctorHomFunctorAdj M

instance lTensorFunctorPreservesColimits : Limits.PreservesColimits (lTensorFunctor M) :=
  Limits.preservesColimitsOfNatIso <| TensorFunctorsNatIso M

def rTensorFunctorRightExact : ModuleCat.{v} R ⥤ᵣ ModuleCat.{v} R :=
  RightExactFunctor.of (rTensorFunctor M)

def lTensorFunctorRightExact : ModuleCat.{v} R ⥤ᵣ ModuleCat.{v} R :=
  RightExactFunctor.of (lTensorFunctor M)

end ModuleCat




variable {R : Type u} {S : Type v} [CommRing R] [Ring S]

def RingHom.Flat (f : R →+* S) : Prop :=
  @Module.Flat R S _ _ f.toModule




namespace Module

namespace Flat

variable (R : Type u) (S : Type v) (M : Type w)
[CommRing R] [CommRing S]
[Algebra R S] [AddCommGroup M]
[Module R M] [Module S M] [IsScalarTower R S M]


lemma of_flat_hom [hM : Flat S M] [hS : Flat R S] : Flat R M := by
    rw [iff_rTensor_injective' R M]
    rw [iff_rTensor_injective' R S] at hS
    rw [iff_rTensor_injective' S M] at hM
    intro I
    let hS := hS I
    -- let L := LinearMap.range (TensorProduct.lift ((lsmul R S).comp I.subtype))
    let J := Submodule.baseChange S I
    -- letI := (TensorProduct.rid R S).symm
    let e := AlgebraTensorModule.rid R S S
    --letI :=  @Equiv.module S J S _  e.symm
    -- --let J := @Ideal.span S _ <| LinearMap.range (TensorProduct.lift ((lsmul R S).comp I.subtype))
    -- --let hM := hM J
    -- -- have h : (TensorProduct.lift ((lsmul R S).comp I.subtype)).comp <|
    -- --   TensorProduct.lift ((lsmul S M).comp J.subtype) = TensorProduct.lift ((lsmul R M).comp I.subtype)
    --let e₁ := (AlgebraTensorModule.assoc R S S M S I).restrictScalars R
    -- --letI := k S R R I S M
    --letI := AlgebraTensorModule.leftComm
    -- let e₂ := (TensorProduct.rid S M).restrictScalars R
    -- --let σ₃ := (TensorProduct.lid S M).toLinearMap
    -- let e₃ := TensorProduct.congr e₂ (LinearEquiv.refl R I)
    -- let e := e₃.symm ≪≫ₗ e₁
    let f := TensorProduct.lift ((lsmul R S).comp I.subtype)
    --let f' := AlgebraTensorModule.lift ((lsmul S R).comp I.subtype)
    -- have eq : f = f' := sorry
    --have hf : ∀ x ∈ I, f x ∈ J := sorry
    --let f := f.restrict (sorry)
    --let g := TensorProduct.lift ((lsmul S M).comp J.subtype)
    let h :=  TensorProduct.lift ((lsmul R M).comp I.subtype)
      --let g :=  TensorProduct.lift ((lsmul S M).comp J.subtype)


    sorry


-- lemma iff_rTensorFunctorPreservesFiniteLimits :  Flat R M ↔
--   Nonempty (PreservesFiniteLimits (ModuleCat.rTensorFunctor M)) := by
--   sorry

end Flat

end Module



namespace RingHom

namespace Flat

variable {R : Type u} {S : Type v} [CommRing R] [Ring S] (f : R →+* S)

--idk where to put
-- lemma of_preserves_flatness (M : Type w) [CommRing S] [AddCommGroup M]
--   [Module S M] [Module.Flat S M] (h : f.Flat) : @Module.Flat R M _ _ <| Module.compHom M f :=
--   sorry

def PreservesInjectiveness : Prop :=
    @Module.Flat.rTensor_preserves_injectiveness R S _ _ f.toModule

variable (R : Type u) (S : Type v) [CommRing R] [Ring S]

lemma id : Flat (RingHom.id R) := Module.Flat.self R

variable {R : Type u} {S : Type v} [CommRing R] [Ring S] (f : R →+* S)


-- it seems some stuff may have been defined in the wrong way
lemma iff_PreservesInjectiveness [UnivLE.{u, v}] :
  f.Flat ↔ PreservesInjectiveness f :=
    @Module.Flat.iff_rTensor_preserves_injectiveness R _ S _ f.toModule _

variable {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [Ring T]

lemma comp {g : S →+* T} {f : R →+* S} (hg : g.Flat) (hf : f.Flat) :
  --[UnivLE.{u, v}] [UnivLE.{v, w}] [UnivLE.{u, w}]
  Flat (RingHom.comp g f) := sorry
   -- @Module.Flat.of_flat_hom R S T _ _ f.toAlgebra _ (g.comp f).toModule g.toModule (sorry) hg hf

end Flat

end RingHom





namespace Module

open Localization

--namespace Flat

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] [Flat R M]

--class or def?
class FaithfullyFlat extends Flat R M where
  faithful : ∀ ⦃m : Ideal R⦄ (_ : m.IsMaximal), Nontrivial <| M ⊗[R] (R ⧸ m)
  --faithful := ∀ ⦃m : Ideal R⦄ (_ : m.IsMaximal), Nontrivial <| M ⧸ (m • ⊤ : Submodule R M)

namespace FaithfullyFlat

instance self : FaithfullyFlat R R where
  faithful m _ := Equiv.nontrivial (TensorProduct.lid R (R ⧸ m)).toEquiv


--def ReflectsExact : Prop := sorry

--Faithfully flat iff tensor with any R-module is nonzero
def TensorNonzero [Flat R M] : Prop :=
  ∀ {N : Type u} [AddCommGroup N] [Module R N], Nontrivial N → Nontrivial (M ⊗[R] N)

-- Faithfully flat iff tensor with all prime residues is nonzero
def PrimeResidues [Flat R M] : Prop :=
  ∀ ⦃p : Ideal R⦄ (_ : p.IsPrime), Nontrivial <| M ⊗[R] FractionRing (R ⧸ p)


-- Faithfully flat iff tensor with all maximal residues is nonzero
-- def MaximalResidues : Prop :=
--   ∀ ⦃m : Ideal R⦄ (_ : m.IsMaximal), Nontrivial <| M ⊗[R] (R ⧸ m)
  -- @TensorProduct R _ M (LocalRing.ResidueField (Localization.AtPrime m)) _ _ _ <|
  -- ((LocalRing.residue (Localization.AtPrime m)).comp
  -- (algebraMap R <| Localization.AtPrime m)).toModule

-- having to condition on universes like this maes me feel my definition is "wrong"
-- it is however in line with the definition given for flat preserving injections (in this branch)
lemma PrimeResiduesIfTensorNonzero [UnivLE.{u, v}] : TensorNonzero R M → PrimeResidues R M := by
  intro h p hp
  let h' := IsFractionRing.nontrivial (R ⧸ p) (FractionRing (R ⧸ p))
  exact h h'

lemma ToFaithfullyFlatIfPrimeResidues : PrimeResidues R M → FaithfullyFlat R M := fun h => by
  refine mk ?faithful
  intro m hm
  letI := ((Ideal.Quotient.maximal_ideal_iff_isField_quotient m).1 hm).toField
  let e := (FractionRing.algEquiv (R ⧸ m) (R ⧸ m)).restrictScalars R
  letI := h <| Ideal.IsMaximal.isPrime hm
  let e := TensorProduct.congr (LinearEquiv.refl R M) e.toLinearEquiv
  apply Equiv.nontrivial e.toEquiv.symm


variable (R : Type u) (S : Type v) (M : Type w)
[CommRing R] [CommRing S]
[Algebra R S] [AddCommGroup M]
[Module R M] [Module S M] [IsScalarTower R S M]


#check LinearMap
def of_faithfully_flat_hom [hM : FaithfullyFlat S M] [hS : FaithfullyFlat R S] :
  FaithfullyFlat R M where
    out := (Flat.of_flat_hom R S M).out
    faithful m hm := by
      -- let e₁ :=  (TensorProduct.rid S M).restrictScalars R
      -- let e₂ := TensorProduct.congr e₁ <| LinearEquiv.refl R (R ⧸ m)
      -- let e₃ := (AlgebraTensorModule.assoc R S S M S (R ⧸ m)).restrictScalars R
      -- let e := e₃.symm ≪≫ₗ e₂
      let h : Nontrivial <| S ⊗[R] (R ⧸ m) := hS.faithful hm
      let I := Ideal.map (algebraMap R S) m
      let f : S ⧸ I →ₐ[S] S ⊗[R] (R ⧸ m) := by
        let g :  S →ₐ[S] S ⊗[R] (R ⧸ m) := Algebra.TensorProduct.includeLeft
        have hg : ∀ s : S, s ∈ I → g s = 0 := fun s hs => by
          sorry
        exact Ideal.Quotient.liftₐ I g hg
      have hI : (I ≠ ⊤) := by
        by_contra hI
        letI := @RingHom.domain_nontrivial (S ⧸ I) (S ⊗[R] (R ⧸ m)) _ _ f _
        letI := Ideal.Quotient.subsingleton_iff.2 hI
        apply not_nontrivial (S ⧸ I)
        assumption
      let hm' := Ideal.exists_le_maximal I hI
      obtain ⟨m', hm', _⟩ := hm'
      letI := hM.faithful hm'
      --rTensor.surjective
      --apply Nontrivial
      let f : S ⊗[R] (R ⧸ m) →ₐ[S] S ⧸ I := by
        -- letI := AlgHom.id S
        -- letI := Algebra.ofId R S
        --letI := TensorProduct.map (AlgHom.id R S) (Algebra.ofId R S)
        have hm : ∀ r ∈ m, (Algebra.ofId R S) r = 0 := by
          sorry
        -- let g := Ideal.Quotient.liftₐ m (Algebra.ofId R S) hm
        -- letI := (Algebra.ofId S (S ⧸ I)).comp (AlgHom.id S S)

        apply Algebra.TensorProduct.productLeftAlgHom
      have hf : Function.Surjective f := by
        sorry
      --letI := Function.Surjective.nontrivial (lTensor.surjective M hf)

      sorry

end FaithfullyFlat

--end Flat

end Module

namespace RingHom

--namespace Flat

variable {R : Type u} {S : Type v} [CommRing R] [Ring S] (f : R →+* S)

def FaithfullyFlat :=
  @Module.FaithfullyFlat R S _ _ f.toModule

namespace FaithfullyFlat

lemma id (R : Type u) [CommRing R] : FaithfullyFlat (RingHom.id R) := Module.FaithfullyFlat.self R

variable  {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [Ring T] (f : R →+* S)

lemma comp {g : S →+* T} {f : R →+* S} (hg : g.FaithfullyFlat) (hf : f.FaithfullyFlat) :
  FaithfullyFlat (g.comp f) :=
    @Module.FaithfullyFlat.of_faithfully_flat_hom
      R S T _ _ f.toAlgebra _ (g.comp f).toModule g.toModule (sorry) hg hf

end FaithfullyFlat

--end Flat

end RingHom
