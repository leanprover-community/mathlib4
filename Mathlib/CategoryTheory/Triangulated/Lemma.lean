import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

universe u v

noncomputable section

open CategoryTheory Category Limits

variable {C : Type u} [Category.{v} C] [Abelian C] {A : ChainComplex C ℤ}
  (F : ℤ ⥤ ChainComplex C ℤ) {ι : ∀ n, F.obj n ⟶ A} [∀ n, Mono (ι n)]
  (fil₁ : ∀ n (B : C) (f : A.X n ⟶ B), (∀ p, (ι p).f n ≫ f = 0) → f = 0)
  (fil₂ : ∀ n, ∃ p, IsZero ((F.obj p).X n))

def Gr (p : ℤ) : ChainComplex C ℤ :=
  cokernel (F.map (homOfLE (le_of_lt (Int.pred_self_lt p))))

variable {F} in
def FToGr (p : ℤ) : F.obj p ⟶ Gr F p := cokernel.π _

variable (fil₂ : ∀ p q, p ≠ q → IsZero ((Gr F p).homology q))

abbrev map_for_P (n : ℤ) : (F.obj n).X n ⟶ (Gr F n).X (n - 1) :=
  (F.obj n).d n (n - 1) ≫ (FToGr n).f (n - 1)

def P (n : ℤ) : C := kernel (map_for_P F n)

abbrev map_for_Q (n : ℤ) :
    (F.obj n).X (n + 1) ⊞ (F.obj (n - 1)).X n ⟶ (F.obj n).X n :=
  biprod.desc ((F.obj n).d (n + 1) n) ((F.map (homOfLE (le_of_lt (Int.pred_self_lt n)))).f n)

def Q (n : ℤ) : C := Abelian.image (map_for_Q F n)

/-
First statement: `Q n ⊆ P n` for every `n` (i.e. the obvious map from `Q n` to `(F.obj n).n`
factors through `P n`), and the `Q n` and `P n` extend to complexes (using the differentials of
`A`).
-/

lemma Q_incl_P (n : ℤ) : Abelian.image.ι (map_for_Q F n) ≫ map_for_P F n = 0 := sorry

def QtoP (n : ℤ) : Q F n ⟶ P F n := kernel.lift (map_for_P F n) (Abelian.image.ι (map_for_Q F n))
  (Q_incl_P F n)



--lemma P_subcomplex
