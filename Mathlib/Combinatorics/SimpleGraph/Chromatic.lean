import Mathlib.Combinatorics.SimpleGraph.Coloring

/-
If G is a graph with finite chromatic number r then any r-coloring of G
is surjective and has edges joining any two distinct color classes.

Definitions:

`Coloring.not_surj_toColoring` given an (r + 1)-coloring of G that does not use
color `i` we define the obvious r-coloring of G.

`Coloring.not_colorClasses_adj_toColoring` given an (r + 1)-coloring of G and a pair of
colors `i ≠ j` such that there is no edge between the color classes of i and j
produce an r-coloring of G.

-/

universe u v
namespace SimpleGraph

variable {V : Type u}
variable  {G : SimpleGraph V}


section Fin

variable {r : ℕ}
/-- If r < χ(G) then G is not r-colorable -/
lemma not_col_lt_chrom (hr : r < G.chromaticNumber) : ¬ G.Colorable r := by
  contrapose! hr
  exact Colorable.chromaticNumber_le hr


/-- In particular, if χ(G) = r + 1 then G is not r-colorable -/
lemma not_col_chrom_succ (hcrom: G.chromaticNumber = r + 1) : ¬ G.Colorable r := by
  apply not_col_lt_chrom
  rw [hcrom]
  exact_mod_cast Nat.lt_succ_self _



/-- If C is an (r + 1)-coloring of G that never uses color i then we can define
an r-coloring of G -/
def Coloring.not_surj_toColoring {i : Fin (r + 1)} (C : G.Coloring (Fin (r + 1)))
    (hc: ∀ a, C a ≠ i) : G.Coloring (Fin r) :=
  ⟨fun v ↦ if hcv : C v = Fin.last r then ⟨i, Fin.val_lt_last (hcv ▸ (hc v)).symm⟩
       else ⟨C v, Fin.val_lt_last hcv⟩, by
    intro _ b had
    dsimp
    split_ifs with h1 h2 h3
    · exfalso; exact C.valid had (h2 ▸ h1)
    all_goals intro hne; simp only [Fin.mk.injEq,Fin.val_eq_val, hc] at hne
    · exact hc b hne.symm
    · exact C.valid had hne⟩


/-- If r ≤ χ(G) and C is an r-coloring then C is surjective  -/
lemma Coloring.le_chromatic_surj (C : G.Coloring (Fin r)) (hcrom: r ≤ G.chromaticNumber) :
    Function.Surjective C := by
  intro i
  cases r with
  | zero => exact i.elim0
  | succ r =>
    contrapose! hcrom
    apply lt_of_le_of_lt (Colorable.chromaticNumber_le ⟨_,(C.not_surj_toColoring  hcrom).valid⟩)
    exact_mod_cast Nat.lt_succ_self _


/-- If G has an (r + 1)-coloring in which no vertex of color i is adjacent to a vertex of color j
and i ≠ j then we can define an r - coloring of G -/
def Coloring.not_colorClasses_adj_toColoring {i j: Fin (r + 1)} (C : G.Coloring (Fin (r + 1)))
    (hc: ∀ v w, C v = i → C w = j → ¬G.Adj v w) (hij : i ≠ j) : G.Coloring (Fin r) := by
  let C': G.Coloring (Fin (r + 1)) := ⟨fun v ↦ ite (C v = j) i (C v), by
    intro a b had heq;
    dsimp at heq
    split_ifs at heq with h1 h2 h3
    · exfalso; exact C.valid had (h2 ▸ h1)
    · exact hc b a heq.symm h1 had.symm
    · exact hc a b heq h3 had
    · exact C.valid had heq⟩
  apply C'.not_surj_toColoring  (_ : ∀ v , (C'.toFun v ≠ j))
  intro v hvj; simp only at hvj
  split_ifs at hvj with h1
  · apply hij  hvj
  . exact h1 hvj


/-- If χ(G) = r then any r-coloring has edges between any pair of distinct color classes -/
lemma Coloring.colorClasses_adj  {i j : Fin r} (C : G.Coloring (Fin r))
    (hcrom: G.chromaticNumber = r) (hij: i ≠ j) :  ∃ v w, C v = i ∧ C w = j ∧ G.Adj v w := by
  cases r with
  | zero => exact i.elim0
  | succ r =>
    by_contra! hc
    exact not_col_chrom_succ hcrom ⟨_,(C.not_colorClasses_adj_toColoring hc hij).valid⟩

end Fin

variable {β : Type v}
/-- If G has a β-Coloring then χ(G) = ‖β‖ ↔ every β-Coloring of G is surjective -/
theorem chromaticNumber_eq_card_iff_forall_surj [Fintype β] (C : G.Coloring β) :
    G.chromaticNumber = Fintype.card β  ↔ (∀ C': G.Coloring β, Function.Surjective C') := by
  refine ⟨fun h C'↦ ?_,fun h ↦ chromaticNumber_eq_card_of_forall_surj C h⟩
  let e := Fintype.equivFin β
  let D := G.recolorOfEquiv e C'
  convert (e.symm.comp_surjective D).2 <| D.le_chromatic_surj h.symm.le
  ext
  apply_fun e
  rw [Function.comp_apply, Equiv.apply_symm_apply]
  rfl



end SimpleGraph
