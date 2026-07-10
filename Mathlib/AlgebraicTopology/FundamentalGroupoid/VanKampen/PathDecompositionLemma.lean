module

public import Mathlib
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.ComposeMorphisms

@[expose] public section

open TopologicalSpace CategoryTheory

open scoped unitInterval

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Helper: the homotopy class of the concat of paths equals the comp_list of their
    homotopy classes in the fundamental groupoid. -/
lemma concat_eq_comp_list {n : ℕ} (p : Fin (n + 1) → X)
    (F : (k : Fin n) → Path (p (Fin.castSucc k)) (p (Fin.succ k))) :
    FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (Path.concat p F)) =
    comp_list n
      (fun i : Fin (n + 1) => FundamentalGroupoid.mk (p i))
      (fun i : Fin n => FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (F i))) := by
  induction n with
  | zero =>
    -- Base case: n = 0
    simp [comp_list_zero, Path.concat_zero]
    <;> rfl
  | succ n ih =>
    -- Inductive step: n → n + 1
    let p₁ : Fin (n + 1) → X := fun i : Fin (n + 1) => p (Fin.castSucc i)
    let F₁ : (k : Fin n) → Path (p₁ (Fin.castSucc k)) (p₁ (Fin.succ k)) :=
      fun k : Fin n => F (Fin.castSucc k)
    let p_last : X := p (Fin.last (n + 1))
    have h_concat : Path.concat p F =
        (Path.concat p₁ F₁).trans (F (Fin.last n)) := by
      exact Path.concat_succ p F
    have h1 : FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (Path.concat p F)) =
        FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk ((Path.concat p₁ F₁).trans (F (Fin.last n)))) := by
      congr
      <;> exact h_concat
    rw [h1]
    have h_mk : Path.Homotopic.Quotient.mk ((Path.concat p₁ F₁).trans (F (Fin.last n))) =
        Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.mk (Path.concat p₁ F₁))
          (Path.Homotopic.Quotient.mk (F (Fin.last n))) :=
      Path.Homotopic.Quotient.mk_trans (Path.concat p₁ F₁) (F (Fin.last n))
    let a : FundamentalGroupoid X := FundamentalGroupoid.mk (p₁ 0)
    let b : FundamentalGroupoid X := FundamentalGroupoid.mk (p₁ (Fin.last n))
    let c : FundamentalGroupoid X := FundamentalGroupoid.mk (p (Fin.last (n + 1)))
    let p' : a ⟶ b := FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (Path.concat p₁ F₁))
    let q' : b ⟶ c := FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (F (Fin.last n)))
    have h_comp : p' ≫ q' = Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.mk (Path.concat p₁ F₁))
        (Path.Homotopic.Quotient.mk (F (Fin.last n))) :=
      FundamentalGroupoid.comp_eq a b c p' q'
    have h2 : FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk ((Path.concat p₁ F₁).trans (F (Fin.last n)))) =
        p' ≫ q' := by
      simpa [h_comp, h_mk] using rfl


    rw [h2]
    have h_succ : comp_list (n + 1)
        (fun i : Fin (n + 2) => FundamentalGroupoid.mk (p i))
        (fun i : Fin (n + 1) => FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (F i))) =
        comp_list n
          (fun i : Fin (n + 1) => FundamentalGroupoid.mk (p₁ i))
          (fun i : Fin n => FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (F₁ i))) ≫
        FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (F (Fin.last n))) :=
      comp_list_succ n
        (fun i : Fin (n + 2) => FundamentalGroupoid.mk (p i))
        (fun i : Fin (n + 1) => FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (F i)))
    rw [h_succ]
    have h_ih' : comp_list n
        (fun i : Fin (n + 1) => FundamentalGroupoid.mk (p₁ i))
        (fun i : Fin n => FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (F₁ i))) =
        FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (Path.concat p₁ F₁)) :=
      (ih p₁ F₁).symm
    rw [h_ih']
    <;> rfl

/-- Given a path γ and a strictly monotone sequence of points ts : Fin (n + 1) → I,
    the homotopy class of the subpath from ts 0 to ts (Fin.last n) equals the
    composition of the homotopy classes of its subpaths in the fundamental groupoid. -/
theorem subpath_decomposition_comp_list {x y : X} (γ : Path x y) {n : ℕ}
    (ts : Fin (n + 1) → I)
    (h_ts_strict : StrictMono ts) :
    FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (γ.subpath (ts 0) (ts (Fin.last n)))) =
    comp_list n
      (fun i : Fin (n + 1) => FundamentalGroupoid.mk (γ (ts i)))
      (fun i : Fin n => FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (γ.subpath (ts (Fin.castSucc i)) (ts (Fin.succ i))))) := by
  let p : Fin (n + 1) → X := fun i => γ (ts i)
  let F : (k : Fin n) → Path (p (Fin.castSucc k)) (p (Fin.succ k)) :=
    fun k => γ.subpath (ts (Fin.castSucc k)) (ts (Fin.succ k))
  have h_homotopic : Path.Homotopic (Path.concat p F) (γ.subpath (ts 0) (ts (Fin.last n))) :=
    Path.Homotopic.concat_subpath γ ts
  have h_eq : Path.Homotopic.Quotient.mk (Path.concat p F) =
      Path.Homotopic.Quotient.mk (γ.subpath (ts 0) (ts (Fin.last n))) :=
    Path.Homotopic.Quotient.eq.mpr h_homotopic
  have h_main : FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (Path.concat p F)) =
      comp_list n
        (fun i : Fin (n + 1) => FundamentalGroupoid.mk (p i))
        (fun i : Fin n => FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (F i))) :=
    concat_eq_comp_list p F
  rw [←h_main]
  rw [h_eq]

end

end
