/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst

/-!
# Singular homology in degree 0


-/

@[expose] public section

universe w v v' u u'

open CategoryTheory Limits AlgebraicTopology Simplicial

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

namespace SSet

variable (X : SSet) (R : C)


noncomputable def π₀.fromChainComplexXZero :
    (X.chainComplex R).X 0 ⟶ ∐ (fun (_ : π₀ X) ↦ R) :=
  (sigmaConst.obj _).map π₀.mk

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma π₀.comp_fromChainComplexXZero (x : X _⦋0⦌) :
  X.ιChainComplex x ≫ π₀.fromChainComplexXZero X R =
    Sigma.ι (fun (_ : π₀ X) ↦ R) (π₀.mk x) := by
  simp [π₀.fromChainComplexXZero, ιChainComplex]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma π₀.d_fromChainComplexXZero (n : ℕ) :
    (X.chainComplex R).d n 0 ≫ π₀.fromChainComplexXZero X R = 0 := by
  by_cases! hn : n ≠ 1
  · rw [HomologicalComplex.shape _ _ _ (by simp; lia), zero_comp]
  · subst hn
    ext x
    simp [π₀.sound (Edge.mk' x)]

set_option backward.isDefEq.respectTransparency false in
noncomputable def isColimitCokernelCoforkChainComplexDOneZero :
    IsColimit (CokernelCofork.ofπ _ (π₀.d_fromChainComplexXZero X R 1)) := by
  refine (IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_).1
    (Preadditive.isColimitCokernelCoforkOfCofork
      ((isColimitMapCoconeCoforkEquiv _ _).1
        (isColimitOfPreserves (sigmaConst.obj R) X.isColimitCoforkπ₀)))
  · refine parallelPair.ext (-Iso.refl _) (Iso.refl _) ?_ (by simp)
    simp [chainComplex, SSet.chainComplexFunctor, sub_eq_neg_add]
  · refine Cofork.ext (Iso.refl _) ?_
    ext
    simp [chainComplex, SSet.chainComplexFunctor, π₀.fromChainComplexXZero]

noncomputable def homologyData₀ :
    ((X.chainComplex R).sc' 1 0 0).HomologyData :=
  ShortComplex.HomologyData.ofIsColimitCokernelCofork _ (by cat_disch) _
    (isColimitCokernelCoforkChainComplexDOneZero X R)

variable [CategoryWithHomology C]

noncomputable def homology₀Iso :
    X.homology R 0 ≅ ∐ (fun (_ : π₀ X) ↦ R) :=
  ShortComplex.homologyMapIso (HomologicalComplex.isoSc' _ 1 0 0 (by simp) (by simp)) ≪≫
    (X.homologyData₀ R).left.homologyIso

noncomputable def homology₀ε : X.homology R 0 ⟶ R :=
  (X.homology₀Iso R).hom ≫ Sigma.desc (fun _ ↦ 𝟙 R)

set_option backward.isDefEq.respectTransparency false in
instance [X.IsConnected] : IsIso (X.homology₀ε R) := by
  dsimp [homology₀ε]
  simp only [isIso_comp_left_iff]
  let x : π₀ X := Classical.arbitrary _
  refine ⟨Sigma.ι (fun _ ↦ R) x, ?_, by simp⟩
  ext y
  obtain rfl : x = y := by subsingleton
  simp

end SSet

namespace ZerothHomotopy

variable {X : Type w} [TopologicalSpace X]

def mk (x : X) : ZerothHomotopy X := Quotient.mk _ x

lemma mk_surjective : Function.Surjective (mk (X := X)) := by
  rintro ⟨x⟩
  exact ⟨x, rfl⟩

@[elab_as_elim, induction_eliminator, cases_eliminator]
lemma rec {motive : ZerothHomotopy X → Prop}
    (mk : ∀ (x : X), motive (.mk x)) (x : ZerothHomotopy X) :
    motive x := by
  obtain ⟨x, rfl⟩ := mk_surjective x
  exact mk x

lemma sound {x y : X} (p : Path x y) : mk x = mk y :=
  Quotient.sound ⟨p⟩

section

variable {T : Type*} (f : X → T) (hf : ∀ ⦃x y : X⦄ (_ : Path x y), f x = f y)

def lift : ZerothHomotopy X → T :=
  Quotient.lift f (by rintro _ _ ⟨p⟩; exact hf p)

@[simp]
lemma lift_mk (x : X) : lift f hf (.mk x) = f x := rfl

end

end ZerothHomotopy

section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)

abbrev Homeomorph.continousMap : C(X, Y) := e

end

namespace TopCat

variable (X : TopCat.{w})

@[ext]
protected structure Path (x y : X) where
  hom : I ⟶ X
  hom₀ : hom 0 = x := by cat_disch
  hom₁ : hom 1 = y := by cat_disch

attribute [simp] Path.hom₀ Path.hom₁

variable {X} in
@[simps!]
def pathEquiv {x y : X} : X.Path x y ≃ _root_.Path x y where
  toFun p :=
    { toContinuousMap := p.hom.hom.comp TopCat.I.homeomorph.symm.continousMap
      source' := p.hom₀
      target' := p.hom₁ }
  invFun p :=
    { hom := ofHom (p.toContinuousMap.comp TopCat.I.homeomorph.continousMap)
      hom₀ := p.source'
      hom₁ := p.target' }
  left_inv _ := rfl
  right_inv _ := rfl

variable [CategoryWithHomology C] (R : C)

instance : Unique (stdSimplex ℝ (Fin (⦋0⦌.len + 1))) :=
  inferInstanceAs (Unique (stdSimplex ℝ (Fin 1)))

section

variable {X}

set_option backward.isDefEq.respectTransparency false in
noncomputable def toSSetObj₁Equiv :
    toSSet.obj X _⦋1⦌ ≃ (I ⟶ X) :=
  (toSSetObjEquiv _ _).trans
    { toFun f := ofHom (f.comp TopCat.stdSimplexHomeomorphI.symm.continousMap)
      invFun f := f.hom.comp TopCat.stdSimplexHomeomorphI.continousMap
      left_inv _ := by aesop
      right_inv _ := by aesop }

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma toSSetObj₁Equiv_apply_zero (s : toSSet.obj X _⦋1⦌) :
    X.toSSetObj₁Equiv s 0 = toSSetObj₀Equiv ((toSSet.obj X).δ 1 s) := by
  dsimp [toSSetObj₀Equiv, toSSetObj₁Equiv]
  congr 1
  rw [Subsingleton.elim default (stdSimplex.vertex 0)]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma toSSetObj₁Equiv_apply_one (s : toSSet.obj X _⦋1⦌) :
    X.toSSetObj₁Equiv s 1 = toSSetObj₀Equiv ((toSSet.obj X).δ 0 s) := by
  dsimp [toSSetObj₀Equiv, toSSetObj₁Equiv]
  congr 1
  rw [Subsingleton.elim default (stdSimplex.vertex 0)]
  simp

@[simp]
lemma δ_one_toSSetObj₁Equiv.symm (f : I ⟶ X) :
    (toSSet.obj X).δ 1 (toSSetObj₁Equiv.symm f) =
      toSSetObj₀Equiv.symm (f 0) :=
  toSSetObj₀Equiv.injective (by simp [← toSSetObj₁Equiv_apply_zero])

@[simp]
lemma δ_zero_toSSetObj₁Equiv.symm (f : I ⟶ X) :
    (toSSet.obj X).δ 0 (toSSetObj₁Equiv.symm f) =
      toSSetObj₀Equiv.symm (f 1) :=
  toSSetObj₀Equiv.injective (by simp [← toSSetObj₁Equiv_apply_one])

noncomputable def toSSetObjEdgeEquiv {x y : X} :
    SSet.Edge (toSSetObj₀Equiv.symm x) (toSSetObj₀Equiv.symm y) ≃ X.Path x y where
  toFun e := { hom := toSSetObj₁Equiv e.edge }
  invFun p := SSet.Edge.mk (toSSetObj₁Equiv.symm p.hom)
  left_inv _ := by aesop
  right_inv _ := by aesop

noncomputable def toSSetObjEdgeEquiv' {x y : X} :
    SSet.Edge (toSSetObj₀Equiv.symm x) (toSSetObj₀Equiv.symm y) ≃ _root_.Path x y :=
  toSSetObjEdgeEquiv.trans pathEquiv

end

noncomputable def zerothHomotopyEquiv : ZerothHomotopy X ≃ (toSSet.obj X).π₀ where
  toFun :=
    ZerothHomotopy.lift (SSet.π₀.mk ∘ toSSetObj₀Equiv.symm)
      (fun _ _ p ↦ SSet.π₀.sound (toSSetObjEdgeEquiv'.symm p))
  invFun := SSet.π₀.lift (ZerothHomotopy.mk ∘ toSSetObj₀Equiv) (fun x y e ↦ by
    obtain ⟨x, rfl⟩ := toSSetObj₀Equiv.symm.surjective x
    obtain ⟨y, rfl⟩ := toSSetObj₀Equiv.symm.surjective y
    exact ZerothHomotopy.sound (toSSetObjEdgeEquiv' e))
  left_inv x := by induction x; simp
  right_inv x := by induction x; simp

noncomputable def singularHomology₀Iso :
    ((singularHomologyFunctor C 0).obj R).obj X ≅ ∐ (fun (_ : ZerothHomotopy X) ↦ R) :=
  SSet.homology₀Iso _ _ ≪≫
    (sigmaConst.obj R).mapIso (zerothHomotopyEquiv X).toIso.symm

noncomputable def singularHomology₀ε :
    ((singularHomologyFunctor C 0).obj R).obj X ⟶ R :=
  SSet.homology₀ε _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma singularHomology₀Iso_sigma_desc_id :
    (singularHomology₀Iso X R).hom ≫ Sigma.desc (fun _ ↦ 𝟙 R) = singularHomology₀ε X R := by
  dsimp only [singularHomology₀Iso, singularHomology₀ε, SSet.homology₀ε]
  cat_disch

instance [PathConnectedSpace X] : Subsingleton (ZerothHomotopy X) :=
  (pathConnectedSpace_iff_zerothHomotopy.1 inferInstance).2

instance [PathConnectedSpace X] : Nonempty (ZerothHomotopy X) :=
  (pathConnectedSpace_iff_zerothHomotopy.1 inferInstance).1

instance [PathConnectedSpace X] : (toSSet.obj X).IsConnected := by
  letI : Unique (ZerothHomotopy X) := Nonempty.some (by
    rw [unique_iff_subsingleton_and_nonempty]
    constructor <;> infer_instance)
  rw [SSet.isConnected_iff_nonempty_unique]
  exact ⟨(zerothHomotopyEquiv X).symm.unique⟩

instance [PathConnectedSpace X] : IsIso (X.singularHomology₀ε R) :=
  inferInstanceAs (IsIso ((toSSet.obj X).homology₀ε R))

end TopCat
