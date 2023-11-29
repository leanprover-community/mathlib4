/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Homology.QuasiIso

#align_import category_theory.preadditive.projective_resolution from "leanprover-community/mathlib"@"324a7502510e835cdbd3de1519b6c66b51fb2467"

/-!
# Projective resolutions

A projective resolution `P : ProjectiveResolution Z` of an object `Z : C` consists of
an `ℕ`-indexed chain complex `P.complex` of projective objects,
along with a quasi-isomorphism `P.π` from `C` to the chain complex consisting just
of `Z` in degree zero.

In order to show `HasProjectiveResolutions C` one will assume `EnoughProjectives C`
and `Abelian C`. This construction appears in `CategoryTheory.Abelian.Projective`.)

We show that given `P : ProjectiveResolution X` and `Q : ProjectiveResolution Y`,
any morphism `X ⟶ Y` admits a lift to a chain map `P.complex ⟶ Q.complex`.
(It is a lift in the sense that
the projection maps `P.π` and `Q.π` intertwine the lift and the original morphism.)

Moreover, we show that any two such lifts are homotopic.

As a consequence, if every object admits a projective resolution,
we can construct a functor
`projectiveResolutions C : C ⥤ HomotopyCategory C (ComplexShape.down ℕ)`.

-/


noncomputable section

universe v u

namespace CategoryTheory

open Category Limits ChainComplex HomologicalComplex

variable {C : Type u} [Category.{v} C]

open Projective

section

variable [HasZeroObject C] [HasZeroMorphisms C]

-- porting note: removed @[nolint has_nonempty_instance]
/--
A `ProjectiveResolution Z` consists of a bundled `ℕ`-indexed chain complex of projective objects,
along with a quasi-isomorphism to the complex consisting of just `Z` supported in degree `0`.
-/
structure ProjectiveResolution (Z : C) where
  /-- the chain complex involved in the resolution -/
  complex : ChainComplex C ℕ
  /-- the chain complex must be degreewise projective -/
  projective : ∀ n, Projective (complex.X n) := by infer_instance
  /-- the chain complex must have homology -/
  [hasHomology : ∀ i, complex.HasHomology i]
  /-- the morphism to the single chain complex with `Z` in degree `0` -/
  π : complex ⟶ (ChainComplex.single₀ C).obj Z
  /-- the morphism to the single chain complex with `Z` in degree `0` is a quasi-isomorphism -/
  quasiIso : QuasiIso π := by infer_instance
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution CategoryTheory.ProjectiveResolution

open ProjectiveResolution in
attribute [instance] projective quasiIso hasHomology

/-- An object admits a projective resolution.
-/
class HasProjectiveResolution (Z : C) : Prop where
  out : Nonempty (ProjectiveResolution Z)
#align category_theory.has_projective_resolution CategoryTheory.HasProjectiveResolution

section

variable (C)

/-- You will rarely use this typeclass directly: it is implied by the combination
`[EnoughProjectives C]` and `[Abelian C]`.
By itself it's enough to set up the basic theory of derived functors.
-/
class HasProjectiveResolutions : Prop where
  out : ∀ Z : C, HasProjectiveResolution Z
#align category_theory.has_projective_resolutions CategoryTheory.HasProjectiveResolutions

attribute [instance 100] HasProjectiveResolutions.out

end

namespace ProjectiveResolution

variable {Z : C} (P : ProjectiveResolution Z)

lemma complex_exactAt_succ (n : ℕ) :
    P.complex.ExactAt (n + 1) := by
  rw [← quasiIsoAt_iff_exactAt' P.π (n + 1) (exactAt_succ_single_obj _ _)]
  · infer_instance

lemma exact_succ (n : ℕ):
    (ShortComplex.mk _ _ (P.complex.d_comp_d (n + 2) (n + 1) n)).Exact :=
  ((HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n) (by simp only [prev]; rfl)
    (by simp)).1 (P.complex_exactAt_succ n)

@[simp]
theorem π_f_succ (n : ℕ) : P.π.f (n + 1) = 0 :=
  (isZero_single_obj_X _ _ _ _ (by simp)).eq_of_tgt _ _
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.π_f_succ CategoryTheory.ProjectiveResolution.π_f_succ

@[simp]
theorem complex_d_comp_π_f_zero :
    P.complex.d 1 0 ≫ P.π.f 0 = 0 := by
  rw [← P.π.comm 1 0, single_obj_d, comp_zero]
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.complex_d_comp_π_f_zero CategoryTheory.ProjectiveResolution.complex_d_comp_π_f_zero

-- Porting note: removed @[simp] simp can prove this
theorem complex_d_succ_comp (n : ℕ) :
    P.complex.d n (n + 1) ≫ P.complex.d (n + 1) (n + 2) = 0 := by
  simp
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.complex_d_succ_comp CategoryTheory.ProjectiveResolution.complex_d_succ_comp

/-- The (limit) cokernel cofork given by the composition
`P.complex.X 1 ⟶ P.complex.X 0 ⟶ Z` when `P : ProjectiveResolution Z`. -/
@[simp]
def cokernelCofork : CokernelCofork (P.complex.d 1 0) :=
  CokernelCofork.ofπ _ P.complex_d_comp_π_f_zero

/-- `Z` is the cokernel of `P.complex.X 1 ⟶ P.complex.X 0` when `P : ProjectiveResolution Z`. -/
def isColimitCokernelCofork : IsColimit (P.cokernelCofork) := by
  refine IsColimit.ofIsoColimit (P.complex.opcyclesIsCokernel 1 0 (by simp)) ?_
  refine Cofork.ext (P.complex.isoHomologyι₀.symm ≪≫ isoOfQuasiIsoAt P.π 0 ≪≫
    singleObjHomologySelfIso _ _ _) ?_
  rw [← cancel_mono (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 _).inv,
    ← cancel_mono (isoHomologyι₀ _).hom]
  dsimp
  simp only [isoHomologyι₀_inv_naturality_assoc, p_opcyclesMap_assoc, single₀_obj_zero, assoc,
    Iso.hom_inv_id, comp_id, isoHomologyι_inv_hom_id, singleObjHomologySelfIso_inv_homologyι,
    singleObjOpcyclesSelfIso_hom, single₀ObjXSelf, Iso.refl_inv, id_comp]

instance (n : ℕ) : Epi (P.π.f n) := by
  cases n
  · exact epi_of_isColimit_cofork P.isColimitCokernelCofork
  · rw [π_f_succ]; infer_instance

variable (Z)

/-- A projective object admits a trivial projective resolution: itself in degree 0. -/
@[simps]
def self [Projective Z] : ProjectiveResolution Z where
  complex := (ChainComplex.single₀ C).obj Z
  π := 𝟙 ((ChainComplex.single₀ C).obj Z)
  projective n := by
    cases n
    · simpa
    · apply IsZero.projective
      apply HomologicalComplex.isZero_single_obj_X
      simp
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.self CategoryTheory.ProjectiveResolution.self

-- to be moved to `CategoryTheory.Abelian.ProjectiveResolution

/-- Auxiliary construction for `lift`. -/
def liftZero {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    P.complex.X 0 ⟶ Q.complex.X 0 :=
  factorThru (P.π.f 0 ≫ f) (Q.π.f 0)
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift_f_zero CategoryTheory.ProjectiveResolution.liftZero

/-- Auxiliary construction for `lift`. -/
def liftOne {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    P.complex.X 1 ⟶ Q.complex.X 1 :=
  Exact.lift (P.complex.d 1 0 ≫ liftZero f P Q) (Q.complex.d 1 0) (Q.π.f 0) Q.exact₀
    (by simp [liftZero, P.exact₀.w_assoc])
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift_f_one CategoryTheory.ProjectiveResolution.liftOne

/-- Auxiliary lemma for `lift`. -/
@[simp]
theorem liftOne_zero_comm {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y)
    (Q : ProjectiveResolution Z) :
    liftOne f P Q ≫ Q.complex.d 1 0 = P.complex.d 1 0 ≫ liftZero f P Q := by
  dsimp [liftZero, liftOne]
  simp
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift_f_one_zero_comm CategoryTheory.ProjectiveResolution.liftOne_zero_comm

/-- Auxiliary construction for `lift`. -/
def liftSucc {Y Z : C} (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) (n : ℕ)
    (g : P.complex.X n ⟶ Q.complex.X n) (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 1))
    (w : g' ≫ Q.complex.d (n + 1) n = P.complex.d (n + 1) n ≫ g) :
    Σ' g'' : P.complex.X (n + 2) ⟶ Q.complex.X (n + 2),
      g'' ≫ Q.complex.d (n + 2) (n + 1) = P.complex.d (n + 2) (n + 1) ≫ g' :=
  ⟨Exact.lift (P.complex.d (n + 2) (n + 1) ≫ g') (Q.complex.d (n + 2) (n + 1))
      (Q.complex.d (n + 1) n) (Q.exact _) (by simp [w]), by simp⟩
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift_f_succ CategoryTheory.ProjectiveResolution.liftSucc

/-- A morphism in `C` lifts to a chain map between projective resolutions. -/
def lift {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    P.complex ⟶ Q.complex :=
  ChainComplex.mkHom _ _ (liftZero f _ _) (liftOne f _ _) (liftOne_zero_comm f _ _)
    fun n ⟨g, g', w⟩ => liftSucc P Q n g g' w
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift CategoryTheory.ProjectiveResolution.lift

/-- The resolution maps intertwine the lift of a morphism and that morphism. -/
@[reassoc (attr := simp)]
theorem lift_commutes {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y)
    (Q : ProjectiveResolution Z) : lift f P Q ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f := by
  ext; simp [lift, liftZero]
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift_commutes CategoryTheory.ProjectiveResolution.lift_commutes

@[reassoc (attr := simp)]
theorem lift_commutes_zero {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y)
    (Q : ProjectiveResolution Z) :
    (lift f P Q).f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f :=
  (HomologicalComplex.congr_hom (lift_commutes f P Q) 0).trans (by simp)

-- Now that we've checked this property of the lift,
-- we can seal away the actual definition.
end ProjectiveResolution

end

namespace ProjectiveResolution

variable [HasZeroObject C] [Preadditive C] [HasEqualizers C] [HasImages C]

/-- An auxiliary definition for `liftHomotopyZero`. -/
def liftHomotopyZeroZero {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) : P.complex.X 0 ⟶ Q.complex.X 1 :=
  Exact.lift (f.f 0) (Q.complex.d 1 0) (Q.π.f 0) Q.exact₀
    (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift_homotopy_zero_zero CategoryTheory.ProjectiveResolution.liftHomotopyZeroZero

/-- An auxiliary definition for `liftHomotopyZero`. -/
def liftHomotopyZeroOne {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) : P.complex.X 1 ⟶ Q.complex.X 2 :=
  Exact.lift (f.f 1 - P.complex.d 1 0 ≫ liftHomotopyZeroZero f comm) (Q.complex.d 2 1)
    (Q.complex.d 1 0) (Q.exact _) (by simp [liftHomotopyZeroZero])
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift_homotopy_zero_one CategoryTheory.ProjectiveResolution.liftHomotopyZeroOne

/-- An auxiliary definition for `liftHomotopyZero`. -/
def liftHomotopyZeroSucc {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (n : ℕ) (g : P.complex.X n ⟶ Q.complex.X (n + 1))
    (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 2))
    (w : f.f (n + 1) = P.complex.d (n + 1) n ≫ g + g' ≫ Q.complex.d (n + 2) (n + 1)) :
    P.complex.X (n + 2) ⟶ Q.complex.X (n + 3) :=
  Exact.lift (f.f (n + 2) - P.complex.d (n + 2) (n + 1) ≫ g') (Q.complex.d (n + 3) (n + 2))
    (Q.complex.d (n + 2) (n + 1)) (Q.exact _) (by simp [w])
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift_homotopy_zero_succ CategoryTheory.ProjectiveResolution.liftHomotopyZeroSucc

/-- Any lift of the zero morphism is homotopic to zero. -/
def liftHomotopyZero {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) : Homotopy f 0 :=
  Homotopy.mkInductive _ (liftHomotopyZeroZero f comm) (by simp [liftHomotopyZeroZero])
    (liftHomotopyZeroOne f comm) (by simp [liftHomotopyZeroOne]) fun n ⟨g, g', w⟩ =>
    ⟨liftHomotopyZeroSucc f n g g' w, by simp [liftHomotopyZeroSucc, w]⟩
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift_homotopy_zero CategoryTheory.ProjectiveResolution.liftHomotopyZero

/-- Two lifts of the same morphism are homotopic. -/
def liftHomotopy {Y Z : C} (f : Y ⟶ Z) {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (g h : P.complex ⟶ Q.complex) (g_comm : g ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f)
    (h_comm : h ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f) : Homotopy g h :=
  Homotopy.equivSubZero.invFun (liftHomotopyZero _ (by simp [g_comm, h_comm]))
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift_homotopy CategoryTheory.ProjectiveResolution.liftHomotopy

/-- The lift of the identity morphism is homotopic to the identity chain map. -/
def liftIdHomotopy (X : C) (P : ProjectiveResolution X) : Homotopy (lift (𝟙 X) P P) (𝟙 P.complex) :=
  by apply liftHomotopy (𝟙 X) <;> simp
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift_id_homotopy CategoryTheory.ProjectiveResolution.liftIdHomotopy

/-- The lift of a composition is homotopic to the composition of the lifts. -/
def liftCompHomotopy {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (P : ProjectiveResolution X)
    (Q : ProjectiveResolution Y) (R : ProjectiveResolution Z) :
    Homotopy (lift (f ≫ g) P R) (lift f P Q ≫ lift g Q R) := by
  apply liftHomotopy (f ≫ g) <;> simp
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift_comp_homotopy CategoryTheory.ProjectiveResolution.liftCompHomotopy

-- We don't care about the actual definitions of these homotopies.
/-- Any two projective resolutions are homotopy equivalent. -/
def homotopyEquiv {X : C} (P Q : ProjectiveResolution X) : HomotopyEquiv P.complex Q.complex where
  hom := lift (𝟙 X) P Q
  inv := lift (𝟙 X) Q P
  homotopyHomInvId := by
    refine' (liftCompHomotopy (𝟙 X) (𝟙 X) P Q P).symm.trans _
    simp only [Category.id_comp]
    apply liftIdHomotopy
  homotopyInvHomId := by
    refine' (liftCompHomotopy (𝟙 X) (𝟙 X) Q P Q).symm.trans _
    simp only [Category.id_comp]
    apply liftIdHomotopy
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.homotopy_equiv CategoryTheory.ProjectiveResolution.homotopyEquiv

@[reassoc (attr := simp)]
theorem homotopyEquiv_hom_π {X : C} (P Q : ProjectiveResolution X) :
    (homotopyEquiv P Q).hom ≫ Q.π = P.π := by simp [homotopyEquiv]
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.homotopy_equiv_hom_π CategoryTheory.ProjectiveResolution.homotopyEquiv_hom_π

@[reassoc (attr := simp)]
theorem homotopyEquiv_inv_π {X : C} (P Q : ProjectiveResolution X) :
    (homotopyEquiv P Q).inv ≫ P.π = Q.π := by simp [homotopyEquiv]
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.homotopy_equiv_inv_π CategoryTheory.ProjectiveResolution.homotopyEquiv_inv_π

end ProjectiveResolution

section

variable [HasZeroMorphisms C] [HasZeroObject C] [HasEqualizers C] [HasImages C]

def projectiveResolution (Z : C) [HasProjectiveResolution Z] : ProjectiveResolution Z :=
  HasProjectiveResolution.out.some

-- porting note: this was named `projective_resolution` in mathlib 3. As there was also a need
-- for a definition of `ProjectiveResolution Z` given `(Z : projectiveResolution Z)`, it
-- seemed more consistent to have `projectiveResolution Z : ProjectiveResolution Z`
-- and `projectiveResolution.complex Z : ChainComplex C ℕ`
/-- An arbitrarily chosen projective resolution of an object. -/
abbrev projectiveResolution.complex (Z : C) [HasProjectiveResolution Z] : ChainComplex C ℕ :=
  (projectiveResolution Z).complex
#align category_theory.projective_resolution CategoryTheory.projectiveResolution.complex

/-- The chain map from the arbitrarily chosen projective resolution
`projectiveResolution.complex Z` back to the chain complex consisting
of `Z` supported in degree `0`. -/
abbrev projectiveResolution.π (Z : C) [HasProjectiveResolution Z] :
    projectiveResolution.complex Z ⟶ (ChainComplex.single₀ C).obj Z :=
  (projectiveResolution Z).π
#align category_theory.projective_resolution.π CategoryTheory.projectiveResolution.π

/-- The lift of a morphism to a chain map between the arbitrarily chosen projective resolutions. -/
abbrev projectiveResolution.lift {X Y : C} (f : X ⟶ Y) [HasProjectiveResolution X]
    [HasProjectiveResolution Y] :
    projectiveResolution.complex X ⟶ projectiveResolution.complex Y :=
  ProjectiveResolution.lift f _ _
#align category_theory.projective_resolution.lift CategoryTheory.projectiveResolution.lift

end

variable (C)
variable [Preadditive C] [HasZeroObject C] [HasEqualizers C] [HasImages C]
  [HasProjectiveResolutions C]

/-- Taking projective resolutions is functorial,
if considered with target the homotopy category
(`ℕ`-indexed chain complexes and chain maps up to homotopy).
-/
def projectiveResolutions : C ⥤ HomotopyCategory C (ComplexShape.down ℕ) where
  obj X := (HomotopyCategory.quotient _ _).obj (projectiveResolution.complex X)
  map f := (HomotopyCategory.quotient _ _).map (projectiveResolution.lift f)
  map_id X := by
    rw [← (HomotopyCategory.quotient _ _).map_id]
    apply HomotopyCategory.eq_of_homotopy
    apply ProjectiveResolution.liftIdHomotopy
  map_comp f g := by
    rw [← (HomotopyCategory.quotient _ _).map_comp]
    apply HomotopyCategory.eq_of_homotopy
    apply ProjectiveResolution.liftCompHomotopy
#align category_theory.projective_resolutions CategoryTheory.projectiveResolutions

end CategoryTheory
