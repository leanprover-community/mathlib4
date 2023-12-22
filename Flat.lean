--import Mathlib.Tactic
--import Mathlib.
import Mathlib.RingTheory.Flat
import Mathlib.Algebra.Algebra.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

-- import Mathlib.Algebra.DirectSum.Module
-- import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
-- import Mathlib.LinearAlgebra.FreeModule.Basic
-- import Mathlib.Algebra.Module.Projective

/-
* Define flat ring homomorphisms
  - Show that the identity is flat
  - Show that composition of flat morphisms is flat
-/

universe u v w

-- #check Ideal
-- theorem iff_Ideal : Flat R M ↔ ∀ {I : Ideal R}, Injective (TensorProduct.lift ((lsmul R M).comp I.subtype)) := by
--   constructor
--   · intro h₁ I
--     by_contra h₂
--     have h₃ : ∃ (a b : I ⊗[R] M), (a ≠ b) ∧ (TensorProduct.lift ((lsmul R M).comp I.subtype) a
--       = TensorProduct.lift ((lsmul R M).comp I.subtype) b) := by sorry
--     obtain ⟨a, b, h₂, h₃⟩ := h₃
--     have S : Set R := sorry
--     --have J := Ideal.span S
--     sorry
--   · intro h₁
--     constructor
--     intro _ _
--     simp [h₁]

open TensorProduct

open LinearMap

open CategoryTheory

open CategoryTheory.Limits

open Functor --(PreservesZeroMorphisms) why won't this work?

namespace ModuleCat

variable {R : Type u} [CommRing R] (M : ModuleCat.{v} R) (N : ModuleCat.{v} R)


-- need to look over a good chunk of this section
namespace HomFunctor

-- mostly just modeling code, idk if I should remove this or not as it is a single line
def obj' : ModuleCat R where
  carrier := M ⟶ N

def map' {N L : ModuleCat.{v} R} (g : N ⟶ L) : obj' M N ⟶ obj' M L where
  toFun := g.comp
  map_add' f f' := LinearMap.comp_add f f' g
  map_smul' := comp_smul g

end HomFunctor

def homFunctor : ModuleCat.{v} R ⥤ ModuleCat.{v} R where
  obj :=  HomFunctor.obj' M
  map := HomFunctor.map' M

@[simp]
lemma homFunctor.obj_eqHom : ((homFunctor M).obj N) = (M ⟶ N) := rfl

lemma homFunctor.obj_toHom : ((homFunctor M).obj N) ⟶ of R (M ⟶ N) where
  toFun := 𝟙 (M ⟶ N)
  map_add' := by simp only [obj_eqHom, types_id_apply, forall_const]
  map_smul' := by simp only [obj_eqHom, types_id_apply, RingHom.id_apply, forall_const]


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

variable {R : Type u} [CommRing R] (M : ModuleCat.{v} R)

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


instance rTensorFunctorPreservesZeroMorphisms : PreservesZeroMorphisms (rTensorFunctor M) where
  map_zero := fun _ _ => rTensor_zero M

instance lTensorFunctorPreservesZeroMorphisms : PreservesZeroMorphisms (lTensorFunctor M) where
  map_zero := fun _ _ => lTensor_zero M


namespace TensorHomFunctorsAdj

def HomEquiv (N L : ModuleCat.{v} R) :
  ((rTensorFunctor M).obj N ⟶ L) ≃ (N ⟶ (homFunctor M).obj L) where
    toFun := curry
    invFun := uncurry R N M L --fix namespace bloat****
    left_inv := (lift.equiv R N M L).right_inv
    right_inv := (lift.equiv R N M L).left_inv

-- noncomputable def lhomEquiv (N L : ModuleCat.{v} R) :
--   ((rTensorFunctor M).obj N ⟶ L) ≃ (N ⟶ (homFunctor M).obj L) where
--     toFun := curry
--     invFun := uncurry R N M L --fix namespace bloat****
--     left_inv := (lift.equiv R N M L).right_inv
--     right_inv := (lift.equiv R N M L).left_inv


def UnitApp (N : ModuleCat.{v} R) :
  (𝟭 (ModuleCat R)).obj N ⟶ (rTensorFunctor M ⋙ homFunctor M).obj N where
    toFun n := {
      toFun := tmul R n
      map_add' := tmul_add n
      map_smul' := by simp only [tmul_smul, RingHom.id_apply, forall_const]
    }
    map_add' n₁ n₂ := by
      simp only [comp_obj, id_obj]
      ext m
      simp [add_tmul]
      rfl
    map_smul' _ _ := rfl


def CounitApp (N : ModuleCat.{v} R) :
  (homFunctor M ⋙ rTensorFunctor M).obj N ⟶ (𝟭 (ModuleCat R)).obj N :=
    uncurry R (M ⟶ N) M N <| homFunctor.obj_toHom M N
    -- toFun := by
    --   simp at *
    --   sorry
    -- map_add' := sorry
    -- map_smul' := sorry



end TensorHomFunctorsAdj


def rTensorHomAdj : rTensorFunctor M ⊣ homFunctor M := sorry --where
  -- homEquiv := TensorHomFunctorsAdj.HomEquiv M
  -- unit := {app := TensorHomFunctorsAdj.UnitApp M }
  -- counit := {app := uncurry R (M ⟶ N) M N <| homFunctor.obj_toHom M N}


instance rTensorFunctorPreservesFiniteColimits : PreservesFiniteColimits (rTensorFunctor M) where
  preservesFiniteColimits J := sorry

instance lTensorFunctorPreservesFiniteColimits : PreservesFiniteColimits (lTensorFunctor M) where
  preservesFiniteColimits J := sorry

def rTensorFunctorRightExact : ModuleCat.{v} R ⥤ᵣ ModuleCat.{v} R :=
  RightExactFunctor.of (rTensorFunctor M)

def lTensorFunctorRightExact : ModuleCat.{v} R ⥤ᵣ ModuleCat.{v} R :=
  RightExactFunctor.of (lTensorFunctor M)


end ModuleCat





namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [Ring S] (f : R →+* S)

def Flat : Prop :=
  @Module.Flat R S _ _ f.toModule

end RingHom

namespace Module

namespace Flat

-- def injective (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
--    ∀ ⦃N N' : Type v⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
--     (L : N →ₗ[R] N'), Function.Injective L → Function.Injective (L.rTensor M)

-- lemma iff_injective

-- variable (T : Type w)

-- better name?

variable (R : Type u) (S : Type v) (M : Type w)
[CommRing R] [CommRing S]
[Algebra R S] [AddCommGroup M]
[Module R M] [Module S M] [IsScalarTower R S M]

#check Equiv.comp_injective
#check Submodule
#check range
--LinearAlgebra.TensorProduct.Tower.assoc
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

--Faithfully flat iff relfects exact sequences (maybe put in cat file)
def ReflectsExact : Prop := sorry

--Faithfully flat iff tensor with any R-module is nonzero
def TensorNonzero [Flat R M] : Prop :=
  ∀ {N : Type v} [AddCommGroup N] [Module R N], Nontrivial N → Nontrivial (M ⊗[R] N)

-- Faithfully flat iff tensor with all prime residues is nonzero
def PrimeResidues [Flat R M] : Prop :=
  ∀ ⦃p : Ideal R⦄ (_ : p.IsPrime), Nontrivial <| M ⊗[R] FractionRing (R ⧸ p)
  -- @TensorProduct R _ M (LocalRing.ResidueField (Localization.AtPrime p)) _ _ _ <|
  -- ((LocalRing.residue (Localization.AtPrime p)).comp
  -- (algebraMap R <| Localization.AtPrime p)).toModule

-- Faithfully flat iff tensor with all maximal residues is nonzero
-- def MaximalResidues : Prop :=
--   ∀ ⦃m : Ideal R⦄ (_ : m.IsMaximal), Nontrivial <| M ⊗[R] (R ⧸ m)
  -- @TensorProduct R _ M (LocalRing.ResidueField (Localization.AtPrime m)) _ _ _ <|
  -- ((LocalRing.residue (Localization.AtPrime m)).comp
  -- (algebraMap R <| Localization.AtPrime m)).toModule


lemma TensorNonzero_to_PrimeResidues : TensorNonzero R M → PrimeResidues R M := by
  intro h p hp
  let h' := IsFractionRing.nontrivial (R ⧸ p) (FractionRing (R ⧸ p))
  sorry

lemma PrimeResidues_to_FaithfullyFlat : PrimeResidues R M → FaithfullyFlat R M := by
  intro h
  refine mk ?faithful
  intro m hm
  letI := ((Ideal.Quotient.maximal_ideal_iff_isField_quotient m).1 hm).toField
  let e := FractionRing.algEquiv (R ⧸ m) (R ⧸ m)
  --letI := TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M)
  -- let k : (R ⧸ m) = FractionRing (R ⧸ m) := sorry
  -- letI := h <| Ideal.IsMaximal.isPrime hm
  -- let l : IsFractionRing (R ⧸ m) (R ⧸ m) := by
  --   let s := (Ideal.Quotient.maximal_ideal_iff_isField_quotient m).1 hm
  --   apply?
  --rw [← k] at this
  sorry


variable (R : Type u) (S : Type v) (M : Type w)
[CommRing R] [CommRing S]
[Algebra R S] [AddCommGroup M]
[Module R M] [Module S M] [IsScalarTower R S M]

#check Equiv.nontrivial
def of_faithfully_flat_hom [hM : FaithfullyFlat S M] [hS : FaithfullyFlat R S] :
  FaithfullyFlat R M where
    out := (Flat.of_flat_hom R S M).out
    faithful m hm := by
      let e₁ :=  (TensorProduct.rid S M).restrictScalars R
      --let e₁ := TensorProduct.lid R (S ⊗[S] M)
      --let e3 := e₂ ≪≫ₗ e₁
      let e₂ := TensorProduct.congr e₁ <| LinearEquiv.refl R (R ⧸ m)
      let e₃ := (AlgebraTensorModule.assoc R S S M S (R ⧸ m)).restrictScalars R
      let e := e₃.symm ≪≫ₗ e₂

      let J := S ⊗[R] (R ⧸ m)
      let h : Nontrivial J := hS.faithful hm

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
