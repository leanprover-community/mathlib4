import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.AlgebraicGeometry.OpenImmersion

open AlgebraicGeometry Scheme FiniteDimensional CategoryTheory

noncomputable section

universe u v w

instance basic_open_isOpenImmersion' {R : Type*} [CommRing R] (f : R) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) := by
  sorry

variable (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V] [Module.Free K V]
variable (r : ℕ) (hr : r < finrank K V)
variable {A : Type*} [CommRing A] [Algebra K A]

def Grassmannian.chart :=
  Spec (CommRingCat.of (MvPolynomial ((Fin (finrank K V - r)) × Fin r) K))

def Grassmannian.matrix_chart (i j : Basis (Fin (finrank K V)) K V) :
    (((Fin (finrank K V - r)) × Fin r) → A) →
    Matrix (Fin r) (Fin r) A := by
  intro φ
  set φ' : Matrix (Fin (finrank K V)) (Fin r) A := Matrix.of
    (fun x y ↦
      if x < r then if x.1 = y.1 then 1 else 0
      else φ (⟨x.1 - r, by have := x.2; omega⟩, y)) -- φ ⟨x - r, y⟩
  set M := (Basis.toMatrix i j).map (algebraMap K A) * φ'
  exact Matrix.submatrix M (Fin.castLE hr.le) id

def Grassmannian.element (i j : Basis (Fin (finrank K V)) K V) :
    (MvPolynomial ((Fin (finrank K V - r)) × Fin r) K) := by
  exact (Grassmannian.matrix_chart (hr := hr) i j MvPolynomial.X
    (A := MvPolynomial ((Fin (finrank K V - r)) × Fin r) K)).det

def Grassmannian.open_immersion (i j : Basis (Fin (finrank K V)) K V) :=
  Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial ((Fin (finrank K V - r)) × Fin r) K)
    (Localization.Away (Grassmannian.element K V r hr i j))))

local instance (i j : Basis (Fin (finrank K V)) K V) : IsOpenImmersion
    (Grassmannian.open_immersion K V r hr i j) :=
  @basic_open_isOpenImmersion (CommRingCat.of (MvPolynomial
    ((Fin (finrank K V - r)) × Fin r) K)) (Grassmannian.element (hr := hr) i j)

def Grassmannian.glueData : GlueData where
  J := Basis (Fin (finrank K V)) K V
  U _ := Grassmannian.chart K V r
  V ij := Spec (CommRingCat.of (Localization.Away (Grassmannian.element K V r hr ij.1 ij.2)))
  f i j := Grassmannian.open_immersion K V r hr i j
  f_mono _ _ := inferInstance
  f_hasPullback := sorry
  f_id := sorry
  t := sorry
  t_id := sorry
  t' := sorry
  t_fac := sorry
  cocycle := sorry
  f_open _ _ := inferInstance
