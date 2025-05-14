import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

universe u v

noncomputable section

open CategoryTheory Category Limits HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {A : ChainComplex C ℤ}
  (F : ℤ ⥤ ChainComplex C ℤ) {ι : ∀ n, F.obj n ⟶ A}
  (compat : ∀ (n m) (u : n ⟶ m), F.map u ≫ ι m = ι n)
  [∀ n, Mono (ι n)]
  (fil₁ : ∀ n (B : C) (f : A.X n ⟶ B), (∀ p, (ι p).f n ≫ f = 0) → f = 0)
  (fil₂ : ∀ n, ∃ p, IsZero ((F.obj p).X n))

lemma mono_F_map (compat : ∀ (n m) (u : n ⟶ m), F.map u ≫ ι m = ι n)
 {n m : ℤ} (u : n ⟶ m) : Mono (F.map u) :=
  mono_of_mono_fac (compat n m u)

def Gr (p : ℤ) : ChainComplex C ℤ :=
  cokernel (F.map (homOfLE (le_of_lt (Int.pred_self_lt p))))

variable {F} in
abbrev FToGr (p : ℤ) : F.obj p ⟶ Gr F p := cokernel.π _

/-!
`F.obj (n - 1)` is the kernel of the morphism `FToGr n : F.obj n ⟶ Gr F n`.
-/
def F_vs_Gr (n : ℤ) : IsLimit (KernelFork.ofι (f := FToGr n)
    (F.map (homOfLE (le_of_lt (Int.pred_self_lt n)))) (cokernel.condition _)) := by
  have : Mono ((F.map (homOfLE (le_of_lt (Int.pred_self_lt n))))) := mono_F_map F compat _
  exact Abelian.monoIsKernelOfCokernel ((Cofork.ofπ (cokernel.π (F.map (homOfLE
  (le_of_lt (Int.pred_self_lt n))))) ((cokernel.condition (F.map (homOfLE (le_of_lt
  (Int.pred_self_lt n))))).trans zero_comp.symm))) (cokernelIsCokernel _)

abbrev FToGr_deg (n p : ℤ) : (F.obj n).X p ⟶ (Gr F n).X p :=
  (HomologicalComplex.eval _ _ p).map (FToGr n)

example (n p : ℤ) : (F.obj (n - 1)).X p ⟶ (F.obj n).X p :=
  (HomologicalComplex.eval _ _ p).map (F.map (homOfLE (le_of_lt (Int.pred_self_lt n))))

lemma FToGr_deg_condition (n p : ℤ) : (eval _ _ p).map (F.map (homOfLE (le_of_lt
    (Int.pred_self_lt n)))) ≫ FToGr_deg F n p = 0 := by
  unfold FToGr_deg
  rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]

def F_vs_Gr_deg (n p : ℤ) : IsLimit (KernelFork.ofι (f := (eval _ _ p).map (FToGr n))
    (((eval _ _ p).map (F.map (homOfLE (le_of_lt (Int.pred_self_lt n))))))
    (FToGr_deg_condition F n p)) :=
  KernelFork.mapIsLimit _ (F_vs_Gr F compat n) (eval C (ComplexShape.down ℤ) p)

variable (fil₂ : ∀ p q, p ≠ q → IsZero ((Gr F p).homology q))

abbrev map_for_P (n : ℤ) : (F.obj n).X n ⟶ (Gr F n).X (n - 1) :=
  (F.obj n).d n (n - 1) ≫ (FToGr n).f (n - 1)

def P (n : ℤ) : C := kernel (map_for_P F n)

/-!
The kernel fork for `(eval C (ComplexShape.down ℤ) (n - 1)).map (FToGr n)` given by
`kernel.ι (map_for_P F n) ≫ (F.obj n).d n (n - 1) : P n ⟶ (F.obj n).X (n - 1)`.
-/
abbrev P_fork (n : ℤ) : Fork ((eval C (ComplexShape.down ℤ) (n - 1)).map (FToGr (F := F) n)) 0 := by
  refine Fork.ofι (kernel.ι (map_for_P F n) ≫ (F.obj n).d n (n - 1)) ?_
  rw [assoc, comp_zero]
  exact kernel.condition _

/-!
The morphism from `P n` to `(F.obj n).X (n - 1)` (induced by `(F.obj n).d n (n - 1)`)
factors through `(F.obj (n - 1)).X (n - 1)`.
-/
def P_to_F_pred (n : ℤ) : P F n ⟶ (F.obj (n - 1)).X (n - 1) :=
  (F_vs_Gr_deg F compat n (n - 1)).lift (P_fork F n)

example (n : ℤ) :
    P_to_F_pred F compat n ≫ (F.map (homOfLE (le_of_lt (Int.pred_self_lt n)))).f (n - 1) =
    kernel.ι _ ≫ (F.obj n).d n (n - 1) :=
  (F_vs_Gr_deg F compat n (n - 1)).fac (P_fork F n) WalkingParallelPair.zero


/-! The morphism from `P n` to `(F.obj (n - 1)).X (n - 1)` lands in `P (n - 1)`.-/
lemma P_to_P_aux (n : ℤ) : P_to_F_pred F compat n ≫ map_for_P F (n - 1) = 0 := by
  suffices h : P_to_F_pred F compat n ≫ (F.obj (n - 1)).d (n - 1) (n - 1 -1) = 0 by
    unfold map_for_P
    rw [← assoc, h, zero_comp]
  have : Mono ((F.map (homOfLE (le_of_lt (Int.pred_self_lt n)))).f (n - 1 - 1)) := sorry
  rw [← cancel_mono (f := ((F.map (homOfLE (le_of_lt (Int.pred_self_lt n)))).f (n - 1 - 1))),
    zero_comp]
  have := Hom.comm (F.map (homOfLE (le_of_lt (Int.pred_self_lt n)))) (n - 1) (n - 1 - 1)
  rw [assoc]; erw [← this]; rw [← assoc]
  erw [(F_vs_Gr_deg F compat n (n - 1)).fac (P_fork F n) WalkingParallelPair.zero]
  dsimp
  simp only [assoc, d_comp_d, comp_zero]

/-!
The morphism from `P n` to `P (n - 1)`.
-/
def P_to_P (n : ℤ) : P F n ⟶ P F (n - 1) :=
  kernel.lift (P_to_F_pred F compat n) (f := map_for_P F (n - 1)) (P_to_P_aux F compat n)

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
