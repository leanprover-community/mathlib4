/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.PerfectPairing
import Mathlib.RingTheory.Flat.Basic

/-!
# Flat base change and duality

If `R` is a commutative ring and two `R`-modules are dual to each other, then their base changes
along any flat `R`-algebra `S` are also dual to each other.  In particular, reflexivity is preserved
by flat base change.  This does not hold for base change by general `R`-algebras, because
reflexivity can be badly behaved in codimension at least 2.

## Main definitions

-/

suppress_compilation

open Function Module

variable (R S M N : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
[CommRing S] [Algebra R S] [Flat R S]

section FlatBaseChange
/-!
The outline of our argument is the following:
1. We define
`flatDualEquiv : S ⊗ Dual R M ≃ Dual S (S ⊗ M)`
using `TensorProduct.AlgebraTensorModule.dualDistrib` to get `S`-linearity,
then show that as a map it is the usual base change of a linear map `s ⊗ f ↦ (s' ⊗ m ↦ ss' ⊗ f m)`.
This will let us show that it is bijective (injectivity follows from flatness?).
2. Apply the equivalence twice to show that `Dual.eval R M : M →ₗ[R] Dual R (Dual R M)` base changes
to `Dual.eval S (S ⊗ M) : (S ⊗ M) →ₗ[S] Dual S (Dual S (S ⊗ M))`
Take base change `S ⊗ M → S ⊗ Dual R (Dual R M)`,
compose with equiv: `S ⊗ Dual R (Dual R M) ≃ Dual S (S ⊗ Dual R M)`
and with dual of equiv: `Dual S (S ⊗ Dual R M) ≃ Dual S (Dual S (S ⊗ M))`

Note that Dual.eval is id.flip - this doesn't help with bijectivity.

* Boubaki Alg. I ch II sec. 4 prop 4: The canonical hom (Hom A, B ⊗ Hom C, D) → Hom (A ⊗ C, B ⊗ D)
  is an isom if at least one of the pairs A,B, A,C, C,D is made up of finite projective modules.
* Also, Section 5.3 prop 7: R commring, S an R-algebra, then the canonical B-module map
  S ⊗[R] Hom_R(E,F) → Hom_S (E_S, F_S) is an isom if either E or B are finitely generated
  projective.
* CommAlg. Ch 1 sec 2.10 Prop 11: If S is R-flat and M is finitely presented, then the map
  S ⊗ Hom_R (M, X) → Hom_S (M_S, X_S) is bijective.  Also, injective if M is just finitely
  generated.  Proof: take a presentation of M, and push it through the functors to get a commutative
  diagram. The bottom row is exact automatically, and the top row is exact by flatness.  The middle
  vertical arrow is an isom when M is finitely generated, and the right arrow is an isom when M is
  fin pres. This yields an isom or inj for the left arrow.
* CommAlg. Ch 7 sec 2 Prop 8: R a Noetherian commring, S an R-flat comm alg, M fin gen reflexive
  R-mod. Then S ⊗ M is a reflexive S-mod.  Proof: Uses the fact that fin gen. modules for a Noeth
  ring are fin pres, and sec.2.10 prop 11.

* Theorem of Specker (1950): countably infinite sum of integers is reflexive: dual is product,
  double dual is original sum and canonical map is isom.

Conclusion: Reflexivity is only preserved by flat base change when combined with fin. pres.
Reason: ⊕ℤ is reflexive, but ⊕ℚ is not, when the sums are over a countably infinite index set.

--(S →ₗ[S] S) ⊗[R] (R →ₗ[R] N) →ₗ[S] S ⊗[R] R →ₗ[S] S ⊗[R] N
Want f : S ⊗[R] R →ₗ[S] S ⊗[R] N ≃ S ⊗[R] N

Add these when working!!!
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LinearMap.Basic

-/
open TensorProduct

--#check AlgebraTensorModule.homTensorHomMap R S S S R S N
--#check TensorProduct.AlgebraTensorModule.congr (LinearMap.ringLmapEquivSelf S S S)
--  (LinearEquiv.refl R (R →ₗ[R] N))
--lemma xxx : AlgebraTensorModule.homTensorHomMap R S S S R S N = fancy id (S ⊗[R] N)

-- Try setup of CommAlg. Ch 1 sec 2.10 Prop 11: S ⊗ Hom_R (M, N) → Hom_S (M_S, N_S)
/-- Base change of an `R`-linear map. -/
def BaseChangeHom : S ⊗[R] (M →ₗ[R] N) →ₗ[S] (S ⊗[R] M →ₗ[S] S ⊗[R] N) :=
  (AlgebraTensorModule.homTensorHomMap R S S S M S N) ∘ₗ
  TensorProduct.AlgebraTensorModule.congr (LinearMap.ringLmapEquivSelf S S S).symm
  (LinearEquiv.refl R (M →ₗ[R] N))

instance : SMul S (S →ₗ[R] N) where
  smul s f :=
    { toFun := fun s' => f (s * s')
      map_add' := by
        intro s t
        simp [mul_add]
      map_smul' := by
        intro r s
        simp }

instance : Module S (S →ₗ[R] N) where
  smul s f := s • f
  one_smul f := by
    ext s
    dsimp [HSMul.hSMul, SMul.smul]
    rw [one_mul]
  mul_smul s t f := by
    ext s'
    dsimp [HSMul.hSMul, SMul.smul]
    rw [mul_assoc, mul_left_comm]
  smul_zero s := by
    ext _
    dsimp [HSMul.hSMul, SMul.smul]
  smul_add s f g := by
    ext s'
    dsimp [HSMul.hSMul, SMul.smul]
  add_smul s t f := by
    ext s'
    dsimp [HSMul.hSMul, SMul.smul]
    rw [add_mul, map_add]
  zero_smul f := by
    ext s
    dsimp [HSMul.hSMul, SMul.smul]
    rw [zero_mul, map_zero]
/-!
def BaseChangeHom_equiv_of_base : (S ⊗[R] (R →ₗ[R] N)) ≃ₗ[S] (S ⊗[R] R →ₗ[S] (S ⊗[R] N)) := by
  refine LinearEquiv.ofLinear (BaseChangeHom R S R N) ?_ ?_ ?_
  · sorry
  · sorry
  · sorry

lemma BaseChangeHom_bijective_of_base : Bijective (BaseChangeHom R S R N) := by
  dsimp [BaseChangeHom]
  refine (EquivLike.bijective_comp _ _).mpr ?_
  --let f : (S ⊗[R] R →ₗ[S] (S ⊗[R] N)) ≃ₗ[S] (S →ₗ[S] (S ⊗[R] N)) := by
    --exact?

  --let f : (S ⊗[R] R) ≃ₗ[S] S := by exact AlgebraTensorModule.rid R S S
  --let f := AlgebraTensorModule.congr (AlgebraTensorModule.rid R S S)
    (LinearEquiv.refl S (S →ₗ[R] N))
  --refine (Bijective.of_comp_iff' _ ⇑(AlgebraTensorModule.homTensorHomMap R S S S R S N)).mp ?_
  sorry



universe u in
lemma BaseChangeHom_bijective {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [CommRing S] [Algebra R S] [Flat R S] [FinitePresentation R M] :
    Bijective (BaseChangeHom R S M N) := by
  obtain ⟨L, _, _, K, f, hL, hfL, hK⟩ := Module.FinitePresentation.equiv_quotient R M
  let fL := BaseChangeHom R S L N

  sorry

--last : S ⊗[R] R ≃ₗ[S] S := AlgebraTensorModule.rid R S S

-- uses different imports
-- last2 : S ⊗[R] R ≃ₗ[S] S := (Algebra.TensorProduct.rid R S S).toLinearEquiv

-- first : (M →ₗ[R] R) →ₗ[R] S ⊗[R] M →ₗ[R] S ⊗[R] R :=
  LinearMap.lTensorHom S (R := R) (N := M) (P := R)

--To make this an equiv, I need equiv for
--`TensorProduct.AlgebraTensorModule.homTensorHomMap R S S S M S R`
-- another := TensorProduct.AlgebraTensorModule.dualDistrib R S S M
--For homobasic finite free modules, we have TensorProduct.dualDistribEquiv, but this uses a basis.

theorem homTensorHomMap_bijective_of_flat [FinitePresentation R M] :
    Bijective (TensorProduct.AlgebraTensorModule.homTensorHomMap R S S S M S R) := by

  sorry

-- anoth : S ≃ₗ[S] Dual S S := (LinearMap.ringLmapEquivSelf S S S).symm

-- anot : S ⊗[R] Dual R M ≃ₗ[S] (Dual S S) ⊗[R] Dual R M :=
  TensorProduct.AlgebraTensorModule.congr (LinearMap.ringLmapEquivSelf S S S).symm
  (LinearEquiv.refl R (Dual R M))

-- DualBaseChange : S ⊗[R] Dual R M →ₗ[S] Dual S (S ⊗[R] M) :=
  (another R S M) ∘ₗ (anot R S M)


theorem DualBaseChange_bijective_of_flat : Bijective (DualBaseChange R S M) := by
  dsimp [DualBaseChange, another]
  refine (EquivLike.bijective_comp (anot R S M) (AlgebraTensorModule.dualDistrib R S S M)).mpr ?_
  dsimp [AlgebraTensorModule.dualDistrib]
  refine Bijective.comp ?_ ?_
  · rw [← AlgEquiv.toLinearEquiv_toLinearMap, Algebra.TensorProduct.rid_toLinearEquiv]

    sorry
  · sorry

-- flatDualEquiv : S ⊗[R] Dual R M ≃ₗ[S] Dual S (S ⊗[R] M) :=
  LinearEquiv.ofBijective (DualBaseChange R S M) (DualBaseChange_bijective_of_flat R S M)


--LinearMap.llcomp R (AlgebraTensorModule.rid R S S) (LinearMap.lTensorHom S (N := M) (P := R))
-/
-- Just a copy to remove import complaints.  Orig. starts with Module.Flat.
theorem lTensor_preserves_injective_linearMap {N' : Type*} [AddCommGroup N'] [Module R N']
    [Flat R M] (L : N →ₗ[R] N') (hL : Function.Injective L) :
    Function.Injective (L.lTensor M) :=
  (L.lTensor_inj_iff_rTensor_inj M).2 (Module.Flat.rTensor_preserves_injective_linearMap L hL)

--theorem LinearMap.lTensor_surjective (hg : Function.Surjective g) :
--    Function.Surjective (lTensor Q g) := by

variable {S : Type*} [CommRing S] [Algebra R S]
/-!

/-- Linear map `Dual R M →ₗ[R] Dual S (S ⊗[R] M)` - I am having a problem getting `S`-linearity -/
def dual_lTensor : Dual R M →ₗ[R] Dual S (S ⊗[R] M) :=
  LinearMap.llcomp R (Dual R M) _ (Dual S (S ⊗[R] M))
    (LinearMap.lcomp R (Dual S (S ⊗[R] M)) _ (TensorProduct.rid R S))
    (LinearMap.lTensorHom S (N := M) (P := R))

/-- `S`-module isom between `Dual S (S ⊗[R] M))` and `S ⊗[R] Dual R M` - needs flat?-/
def dual_base_change : S ⊗[R] Dual R M ≃ₗ[S] Dual S (S ⊗[R] M) where
  toFun x := sorry
  map_add' := sorry
  map_smul' := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

theorem base_change_of_id_dual :
    LinearMap.id (R := S) (M := Dual S (S ⊗[R] M)) =
      dual_base_change ∘ₗ LinearMap.lTensor (LinearMap.id) (Dual R M) ∘ₗ
      (dual_base_change (R := R) (S := S) (M := M)).symm := by
  sorry

 Plan: base change of `id : Dual R M → Dual R M` "is" `id : Dual S (S ⊗[R] M) → Dual S (S ⊗[R] M)`
Need isom from `S ⊗[R] Dual R M` to `Dual S (S ⊗[R] M)`
That is, `S ⊗[R] (M →ₗ[R] R) ≃ₗ[S] (S ⊗[R] M) →ₗ[S] S`.
`s ⊗ₜ f → ()
base change of flip "is" flip
conclude that Dual.eval S (S ⊗[R] M) "is" base change of Dual.eval R M
base change takes surjections to surjections : LinearMap.lTensor_surjective

lemma BaseChange_isReflexive_of_flat [IsReflexive R M] (hRS : Module.Flat R S) :
    IsReflexive S (S ⊗[R] M) where
  bijective_dual_eval' := by
    --have h : Dual.eval S (S ⊗[R] M) =
      --TensorProduct.AlgebraTensorModule.map (LinearEquiv.refl S S) (Dual.eval R M) := by
      --sorry

    constructor
    · simp only [Dual.eval]



      sorry
    · simp only [Dual.eval]
      sorry
-/


namespace PerfectPairing

variable (p : PerfectPairing R M N)

/-- The first step in a base change. -/
noncomputable def baseChange1 : S ⊗[R] M ≃ₗ[S] (S ⊗[R] (N →ₗ[R] R)) :=
  TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl S S) p.toDualLeft
/-!
/-- The second step in a base change. -/
noncomputable def self_module_hom : (S →ₗ[S] S) ≃ₗ[S] S :=
  LinearMap.ringLmapEquivSelf S S S
  --((Module.moduleEndSelf S).toLinearEquiv xxx).symm ≪≫ₗ (MulOpposite.opLinearEquiv S).symm


/-- The third step in a base change. -/
noncomputable def baseChange3 : (S →ₗ[S] S) ⊗[R] (N →ₗ[R] R) →ₗ[S] (S ⊗[R] N →ₗ[S] S ⊗[R] R) :=
  TensorProduct.AlgebraTensorModule.homTensorHomMap R S S S N S R

  TensorProduct.AlgebraTensorModule.map (LinearEquiv.refl S S)

(S ⊗[R] (N →ₗ[R] R)) ≃ₗ[S] ((S ⊗[R] N) →ₗ[S] (S ⊗[R] R))

noncomputable def LinearEquiv.rTensor (e : M ≃ₗ[R] N)   :
    M ⊗[R] P ≃ₗ[R] N ⊗[R] P := TensorProduct.congr e (refl R P)
LinearEquiv.refl
noncomputable def baseChange : PerfectPairing S (S ⊗[R] M) (S ⊗[R] N)
    where
  toLin := TensorProduct.AlgebraTensorModule.homTensorHomMap R S S S N S R
    ∘ₗ (TensorProduct.AlgebraTensorModule.map
      (Module.moduleEndSelf S ∘ₗ MulOpposite.opLinearEquiv S) (LinearEquiv.refl R (N →ₗ[R] R)))
    ∘ₗ (TensorProduct.AlgebraTensorModule.map (LinearEquiv.refl S S) p.toLin)
  bijectiveLeft := sorry
  bijectiveRight := sorry

LinearEquiv.smulOfUnit : inverse to (S →ₗ[S] S) ≃ₗ[S] S

revision: I think this may fail for non-flat base change!
also, it might be better to skip curry/uncurry - just base change via
TensorProduct.AlgebraTensorModule.map (LinearEquiv.refl S S) p.toLin to
  S ⊗[R] M →ₗ[S] (S ⊗[R] (N →ₗ[R] R))
and compose with the equiv ???
  (S ⊗[R] (N →ₗ[R] R)) ≃ₗ[S] (S ⊗[R] N →ₗ[S] S ⊗[R] R) ≃ₗ[S] (S ⊗[R] N →ₗ[S] S)
We may even have base change of duals already!
Hm. I don't have the left map, but I do have TensorProduct.AlgebraTensorModule.homTensorHomMap
  (S →ₗ[S] S) ⊗[R] (N →ₗ[R] R)) →ₗ[S] (S ⊗[R] N →ₗ[S] S ⊗[R] R)
so I left-compose with
TensorProduct.AlgebraTensorModule.map ??? (LinearEquiv.refl R (N →ₗ[R] R))
  (S ⊗[R] (N →ₗ[R] R)) ≃ₗ[S] (S →ₗ[S] S) ⊗[R] (N →ₗ[R] R))


TensorProduct.AlgebraTensorModule.map (LinearEquiv.refl S S)

/-- The base chage of a perfect pairing`. -/
noncomputable def baseChange : PerfectPairing S (S ⊗[R] M) (S ⊗[R] N)
    where
  toLin := TensorProduct.curry (TensorProduct.AlgebraTensorModule.rid R S S
    ∘ₗ TensorProduct.AlgebraTensorModule.map (LinearEquiv.refl S S)
      ((TensorProduct.uncurry R M N R) P.toLin)
    ∘ₗ ((TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R S S M S N)
    ≪≫ₗ (TensorProduct.AlgebraTensorModule.congr
      (TensorProduct.rid S S) (LinearEquiv.refl R (M ⊗[R] N)))))
  bijectiveLeft := sorry
  bijectiveRight := sorry


TensorProduct.AlgebraTensorModule.map (RingHom.id S) ((TensorProduct.uncurry R M N R) P.toLin) :
  S ⊗[R] M ⊗[R] N →ₗ[S] S ⊗[R] R
so compose on left with TensorProduct.AlgebraTensorModule.rid R S S :
  S ⊗[R] R ≃ₗ[A] S,
on the right with
  (S ⊗[R] M) ⊗[S] (S ⊗[R] N) →ₗ[S] S) ≃ S ⊗[R] M ⊗[R] N
which is TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R S S M S N :
  (S ⊗[R] M) ⊗[S] (S ⊗[R] N) ≃ₗ[S] (S ⊗[S] S) ⊗[R] (M ⊗[R] N)
followed by
  TensorProduct.AlgebraTensorModule.congr TensorProduct.lid (LinearEquiv.refl R (M ⊗[R] N)) :
  (S ⊗[S] S) ⊗[R] (M ⊗[R] N) → S ⊗[R] M ⊗[R] N
then curry

/-- just copied -/
def tensorDistrib : BilinForm A M₁ ⊗[R] BilinForm R M₂ →ₗ[A] BilinForm A (M₁ ⊗[R] M₂) :=
  ((TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R A M₁ M₂ M₁ M₂).dualMap
    ≪≫ₗ (TensorProduct.lift.equiv A (M₁ ⊗[R] M₂) (M₁ ⊗[R] M₂) A).symm).toLinearMap
  ∘ₗ TensorProduct.AlgebraTensorModule.dualDistrib R _ _ _
  ∘ₗ (TensorProduct.AlgebraTensorModule.congr
    (TensorProduct.lift.equiv A M₁ M₁ A)
    (TensorProduct.lift.equiv R _ _ _)).toLinearMap

/-- just copied -/
protected def tmul (B₁ : BilinForm A M₁) (B₂ : BilinForm R M₂) : BilinForm A (M₁ ⊗[R] M₂) :=
  tensorDistrib R A (B₁ ⊗ₜ[R] B₂)

/-- just copied -/
protected def baseChange (B : BilinForm R M₂) : BilinForm A (A ⊗[R] M₂) :=
  BilinForm.tmul (R := R) (A := A) (M₁ := A) (M₂ := M₂) (LinearMap.mul A A) B


-/

end PerfectPairing

end FlatBaseChange
