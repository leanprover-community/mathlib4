module

public import Mathlib
public import Mathlib.CategoryTheory.Groupoid.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.ComposeMorphisms

@[expose] public section

open CategoryTheory

variable {C : Type*} [Groupoid C]

/-- Given two sequences of objects connected by morphisms, and vertical morphisms
    between corresponding objects, such that each square commutes:

    p₀ --f₀--> p₁ --f₁--> ... --f_{n-1}--> pₙ
    |          |                        |
    v₀         v₁                       vₙ
    |          |                        |
    v          v                        v
    q₀ --g₀--> q₁ --g₁--> ... --g_{n-1}--> qₙ

    Then the total composition along the bottom followed by the last vertical morphism
    equals the first vertical morphism followed by the total composition along the top. -/
lemma comp_list_chain_commute {n : ℕ}
    (p_objs : Fin (n + 1) → C)
    (q_objs : Fin (n + 1) → C)
    (f_bottom : ∀ i : Fin n, p_objs (Fin.castSucc i) ⟶ p_objs (Fin.succ i))
    (f_top : ∀ i : Fin n, q_objs (Fin.castSucc i) ⟶ q_objs (Fin.succ i))
    (f_vert : ∀ i : Fin (n + 1), p_objs i ⟶ q_objs i)
    (h_square : ∀ i : Fin n,
      f_bottom i ≫ f_vert (Fin.succ i) = f_vert (Fin.castSucc i) ≫ f_top i) :
    comp_list n p_objs f_bottom ≫ f_vert (Fin.last n) =
    f_vert 0 ≫ comp_list n q_objs f_top := by
  induction n with
  | zero =>
    have h1 : comp_list 0 p_objs f_bottom = 𝟙 (p_objs 0) := comp_list_zero p_objs
    have h2 : comp_list 0 q_objs f_top = 𝟙 (q_objs 0) := comp_list_zero q_objs
    rw [h1, h2]
    <;> simp [Category.id_comp, Category.comp_id]
    <;> rfl
  | succ n ih =>
    -- For n + 1, we decompose into n + 1 = n + 1
    -- The first n morphisms plus the last one
    let p_objs' : Fin (n + 1) → C := fun i : Fin (n + 1) => p_objs (Fin.castSucc i)
    let q_objs' : Fin (n + 1) → C := fun i : Fin (n + 1) => q_objs (Fin.castSucc i)
    let f_bottom' : ∀ i : Fin n, p_objs' (Fin.castSucc i) ⟶ p_objs' (Fin.succ i) :=
      fun i : Fin n => f_bottom (Fin.castSucc i)
    let f_top' : ∀ i : Fin n, q_objs' (Fin.castSucc i) ⟶ q_objs' (Fin.succ i) :=
      fun i : Fin n => f_top (Fin.castSucc i)
    let f_vert' : ∀ i : Fin (n + 1), p_objs' i ⟶ q_objs' i :=
      fun i : Fin (n + 1) => f_vert (Fin.castSucc i)

    have h_square' : ∀ i : Fin n,
        f_bottom' i ≫ f_vert' (Fin.succ i) = f_vert' (Fin.castSucc i) ≫ f_top' i := by
      intro i
      exact h_square (Fin.castSucc i)

    have h_ih := ih p_objs' q_objs' f_bottom' f_top' f_vert' h_square'

    -- Now we have:
    -- comp_list n p_objs' f_bottom' ≫ f_vert' (Fin.last n) = f_vert' 0 ≫ comp_list n q_objs' f_top'
    -- That is:
    -- comp_list of first n bottoms ≫ f_vert n = f_vert 0 ≫ comp_list of first n tops

    -- And we also have the last square:
    -- f_bottom (Fin.last n) ≫ f_vert (Fin.succ (Fin.last n))
    --   = f_vert (Fin.castSucc (Fin.last n)) ≫ f_top (Fin.last n)
    -- That is:
    -- f_bottom n ≫ f_vert (n+1) = f_vert n ≫ f_top n

    have h_last_square := h_square (Fin.last n)

    -- Note: Fin.last (n + 1) = Fin.succ (Fin.last n)
    -- And Fin.castSucc (Fin.last n) = Fin.last n (in the context of f_vert')
    have h_vert_last_eq : f_vert (Fin.last (n + 1)) = f_vert (Fin.succ (Fin.last n)) := by
      congr <;> simp [Fin.last] <;> omega

    have h_vert'_last_eq : f_vert' (Fin.last n) = f_vert (Fin.castSucc (Fin.last n)) := by
      rfl

    have h_vert'_0_eq : f_vert' 0 = f_vert 0 := by
      rfl

    -- Now we can put it all together using whiskering
    -- Let A = comp_list n p_objs' f_bottom'
    -- Let B = f_bottom (Fin.last n)
    -- Let C = f_vert (Fin.succ (Fin.last n))
    -- Let D = f_vert (Fin.castSucc (Fin.last n))
    -- Let E = f_top (Fin.last n)
    -- We have: B ≫ C = D ≫ E
    -- We want: (A ≫ B) ≫ C' = f_vert 0 ≫ (comp_list n q_objs' f_top' ≫ E)
    --   where C' = f_vert (Fin.last (n + 1)) = C
    -- And we have: A ≫ D = A ≫ f_vert' (Fin.last n)
    -- And: f_vert' 0 ≫ comp_list n q_objs' f_top' = f_vert 0 ≫ comp_list n q_objs' f_top'

    -- First, show that we can replace C' with C
    have h_whisker_right : ∀ {X Y Z : C} (f : X ⟶ Y) {g h : Y ⟶ Z}, g = h → f ≫ g = f ≫ h := by
      intro X Y Z f g h eq
      rw [eq]
    have h_whisker_left : ∀ {X Y Z : C} {f g : X ⟶ Y} (h : Y ⟶ Z), f = g → f ≫ h = g ≫ h := by
      intro X Y Z f g h eq
      rw [eq]

    let A := comp_list n p_objs' f_bottom'
    let B := f_bottom (Fin.last n)
    let C := f_vert (Fin.succ (Fin.last n))
    let D := f_vert (Fin.castSucc (Fin.last n))
    let E := f_top (Fin.last n)
    let F := comp_list n q_objs' f_top'

    have h_BC_eq_DE : B ≫ C = D ≫ E := h_last_square
    have h_AD_eq_Avert' : A ≫ D = A ≫ f_vert' (Fin.last n) := by
      exact h_whisker_right A h_vert'_last_eq.symm
    have h_ih' : A ≫ f_vert' (Fin.last n) = f_vert' 0 ≫ F := h_ih
    have h_vert0_eq : f_vert' 0 ≫ F = f_vert 0 ≫ F := by
      exact h_whisker_left F h_vert'_0_eq

    have h_main1 : (A ≫ B) ≫ f_vert (Fin.last (n + 1)) = (A ≫ B) ≫ C := by
      exact h_whisker_right (A ≫ B) h_vert_last_eq

    have h_main2 : (A ≫ B) ≫ C = A ≫ (B ≫ C) := Category.assoc A B C
    have h_main3 : A ≫ (B ≫ C) = A ≫ (D ≫ E) := by rw [h_BC_eq_DE]
    have h_main4 : A ≫ (D ≫ E) = (A ≫ D) ≫ E := (Category.assoc A D E).symm
    have h_main5 : (A ≫ D) ≫ E = (A ≫ f_vert' (Fin.last n)) ≫ E := by rw [h_AD_eq_Avert']
    have h_main6 : (A ≫ f_vert' (Fin.last n)) ≫ E = (f_vert' 0 ≫ F) ≫ E := by rw [h_ih']
    have h_main7 : (f_vert' 0 ≫ F) ≫ E = (f_vert 0 ≫ F) ≫ E := by
      exact h_whisker_left E h_vert0_eq
    have h_main8 : (f_vert 0 ≫ F) ≫ E = f_vert 0 ≫ (F ≫ E) := Category.assoc (f_vert 0) F E

    have h_final : (A ≫ B) ≫ f_vert (Fin.last (n + 1)) = f_vert 0 ≫ (F ≫ E) := by
      have h : (A ≫ B) ≫ f_vert (Fin.last (n + 1)) = (A ≫ B) ≫ C := h_main1
      rw [h]
      have h2 : (A ≫ B) ≫ C = A ≫ B ≫ C := h_main2
      rw [h2]
      have h3 : A ≫ B ≫ C = A ≫ D ≫ E := h_main3
      rw [h3]
      have h4 : A ≫ D ≫ E = (A ≫ D) ≫ E := h_main4
      rw [h4]
      have h5 : (A ≫ D) ≫ E = (A ≫ f_vert' (Fin.last n)) ≫ E := h_main5
      rw [h5]
      have h6 : (A ≫ f_vert' (Fin.last n)) ≫ E = (f_vert' 0 ≫ F) ≫ E := h_main6
      rw [h6]
      have h7 : (f_vert' 0 ≫ F) ≫ E = (f_vert 0 ≫ F) ≫ E := h_main7
      rw [h7]
      have h8 : (f_vert 0 ≫ F) ≫ E = f_vert 0 ≫ (F ≫ E) := h_main8
      rw [h8]

    have h1 : comp_list (n + 1) p_objs f_bottom =
        comp_list n p_objs' f_bottom' ≫ f_bottom (Fin.last n) := by
      rw [comp_list_succ] <;> rfl

    have h2 : comp_list (n + 1) q_objs f_top =
        comp_list n q_objs' f_top' ≫ f_top (Fin.last n) := by
      rw [comp_list_succ] <;> rfl

    rw [h1, h2]
    exact h_final

end
