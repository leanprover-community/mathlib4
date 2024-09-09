import Mathlib.AlgebraicTopology.SimplexCatEpis

universe v u

open CategoryTheory

inductive σδ where
| σ : σδ
| δ : σδ

open σδ in
structure SimplexCod where
  (X : Type u)
  (F : List (ℕ × σδ) → ℕ → X)
  (δ_cond : ∀ (i j : ℕ) (_ : i ≤ j), F [(i, δ), (j + 1, δ)] = F [(j, δ), (i, δ)])
  (σ_cond : ∀ (i j : ℕ) (_ : i ≤ j), F [(i, σ), (j, σ)] = F [(j + 1, σ), (i, σ)])
  (δ_σ_le : ∀ (i j : ℕ) (_ : i ≤ j), F [(i, δ), (j + 1, σ)] = F [(j, σ), (i, δ)])
  (δ_σ_eq : ∀ (i n : ℕ) (_ : i < n + 1), F [(i, δ), (i, σ)] n = F [] n)
  (δ_σ_succ : ∀ (i n : ℕ) (_ : i < n + 1), F [(i + 1, δ), (i, σ)] n = F [] n)
  (δ_σ_gt : ∀ (i j : ℕ) (_ : j < i), F [(i + 1, δ), (j, σ)] = F [(j, σ), (i, δ)])

notation "Δ🐟" => SimplexCod

namespace SimplexCategory

def simplexCodF : List (ℕ × σδ) → ℕ → Option (Arrow SimplexCategory)
| [], n => Option.some ⟨mk n, mk n, 𝟙 _⟩
| (_, σδ.σ) :: _, 0 => none
| (a, σδ.σ) :: l, n + 1 => Option.recOn (simplexCodF l n) none fun l =>
  if ha : a < n + 1 ∧ mk n = l.1 then
  some ⟨mk (n + 1), l.2, σ ⟨a, ha.1⟩ ≫ eqToHom ha.2 ≫ l.hom⟩ else none
| (a, σδ.δ) :: l, n => Option.recOn (simplexCodF l (n + 1)) none fun l =>
  if ha : a < n + 2 ∧ mk (n + 1) = l.1 then
  some ⟨mk n, l.2, δ ⟨a, ha.1⟩ ≫ eqToHom ha.2 ≫ l.hom⟩ else none

@[simp]
theorem δ_none_cons {l : List (ℕ × σδ)} {a n : ℕ} (hl : simplexCodF l (n + 1) = none) :
    simplexCodF ((a, σδ.δ) :: l) n = none := by
  simp_all only [simplexCodF, Functor.id_obj]

@[simp]
theorem σ_none_cons {l : List (ℕ × σδ)} {a n : ℕ} (hl : simplexCodF l n = none) :
    simplexCodF ((a, σδ.σ) :: l) (n + 1) = none := by
  simp_all only [simplexCodF, Functor.id_obj]

@[simp]
theorem δ_of_some_cons {l : List (ℕ × σδ)} {a n : ℕ}
    (hl : (simplexCodF ((a, σδ.δ) :: l) n).isSome) :
    (simplexCodF l (n + 1)).isSome := by
  contrapose! hl
  simp_all only [ne_eq, Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none,
    δ_none_cons, Option.isSome_none, Bool.false_eq_true, not_false_eq_true]

@[simp]
theorem σ_of_some_cons {l : List (ℕ × σδ)} {a n : ℕ}
    (hl : (simplexCodF ((a, σδ.σ) :: l) (n + 1)).isSome) :
    (simplexCodF l n).isSome := by
  contrapose! hl
  simp_all only [ne_eq, Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none,
    σ_none_cons, Option.isSome_none, Bool.false_eq_true, not_false_eq_true]

theorem δ_none_of_not {l : List (ℕ × σδ)} {a n : ℕ}
    {f : Arrow SimplexCategory}
    (hl : (simplexCodF l (n + 1)) = some f)
    (hcond : ¬(a < n + 2 ∧ mk (n + 1) = f.left)) :
    simplexCodF ((a, σδ.δ) :: l) n = none := by
  rw [simplexCodF]
  simp_all only [not_and, Functor.id_obj, dite_eq_right_iff, imp_false, not_false_eq_true,
    implies_true]

theorem σ_none_of_not {l : List (ℕ × σδ)} {a n : ℕ}
    {f : Arrow SimplexCategory}
    (hl : (simplexCodF l n) = some f)
    (hcond : ¬(a < n + 1 ∧ mk n = f.left)) :
    simplexCodF ((a, σδ.σ) :: l) (n + 1) = none := by
  rw [simplexCodF]
  simp_all only [not_and, Functor.id_obj, dite_eq_right_iff, imp_false, not_false_eq_true,
    implies_true]

theorem δ_some_cond' {l : List (ℕ × σδ)} {a n : ℕ} {f : Arrow SimplexCategory}
    (hl : (simplexCodF l (n + 1)) = some f)
    (hal : (simplexCodF ((a, σδ.δ) :: l) n).isSome) :
    a < n + 2 ∧ mk (n + 1) = f.left := by
  contrapose hal
  simp_all only [Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none]
  exact δ_none_of_not hl hal

theorem σ_some_cond' {l : List (ℕ × σδ)} {a n : ℕ} {f : Arrow SimplexCategory}
    (hl : (simplexCodF l n) = some f)
    (hal : (simplexCodF ((a, σδ.σ) :: l) (n + 1)).isSome) :
    a < n + 1 ∧ mk n = f.left := by
  contrapose hal
  simp_all only [Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none]
  exact σ_none_of_not hl hal

def get {l : List (ℕ × σδ)} {n : ℕ} (H : (simplexCodF l n).isSome) :
  Arrow SimplexCategory := Option.get _ H

def getδTail {l : List (ℕ × σδ)} {n : ℕ} {a : ℕ} (H : (simplexCodF ((a, σδ.δ) :: l) n).isSome) :
    Arrow SimplexCategory := get (δ_of_some_cons H)

def getσTail {l : List (ℕ × σδ)} {n : ℕ} {a : ℕ}
    (H : (simplexCodF ((a, σδ.σ) :: l) (n + 1)).isSome) :
    Arrow SimplexCategory := get (σ_of_some_cons H)

theorem δ_some_cond {l : List (ℕ × σδ)} {a n : ℕ}
    (hal : (simplexCodF ((a, σδ.δ) :: l) n).isSome) :
    a < n + 2 ∧ mk (n + 1) = (getδTail hal).left := by
  apply δ_some_cond' (l := l)
  rw [getδTail, get]
  simp only [Option.some_get]
  exact hal

theorem σ_some_cond {l : List (ℕ × σδ)} {a n : ℕ}
    (hal : (simplexCodF ((a, σδ.σ) :: l) (n + 1)).isSome) :
    a < n + 1 ∧ mk n = (getσTail hal).left := by
  apply σ_some_cond' (l := l)
  rw [getσTail, get]
  simp only [Option.some_get]
  exact hal
/-
theorem get_δ_cons {l : List (ℕ × σδ)} {a n : ℕ} {f : Arrow SimplexCategory}
    (hl : (simplexCodF l (n + 1)) = some f)
    (hal : (simplexCodF ((a, σδ.δ) :: l) n).isSome) :
    toArrow ((a, σδ.δ) :: l) n hal = ⟨M.obj n, f.2,
      M.map ⟨a, (δ_some_cond hl hal).1⟩ ≫ eqToHom (δ_some_cond hl hal).2
      ≫ f.hom⟩ := by
  simp_all only [toArrow, δ, Functor.id_obj]
  simp_rw [dif_pos (δ_some_cond hl hal)]
  simp only [Option.get_some]

theorem toArrowTail_eq {l : List (ℕ × σδ)} {a n : ℕ}
    (hal : (simplexCodF ((a, σδ.δ) :: l) n).isSome) :
    simplexCodF l (n + 1) = some (toArrowTail hal) := by
  simp_all only [toArrowTail, toArrow, Option.some_get]

theorem toArrow_cons' {l : List (ℕ × σδ)} {a n : ℕ} (hal : (simplexCodF ((a, σδ.δ) :: l) n).isSome) :
    toArrow ((a, σδ.δ) :: l) n hal = ⟨M.obj n, (toArrowTail hal).2,
      M.map ⟨a, (δ_some_cond (toArrowTail_eq hal) hal).1⟩
      ≫ eqToHom (δ_some_cond (toArrowTail_eq hal) hal).2
      ≫ (toArrowTail hal).hom⟩ :=
  toArrow_cons (toArrowTail_eq hal) _

theorem toArrow_left {l : List (ℕ × σδ)} {n : ℕ}
    (hl : (simplexCodF l n).isSome) :
    (toArrow l n hl).left = M.obj n := by
  induction' l with a l _
  · simp_all only [toArrow, δ, Functor.id_obj]
    rfl
  · rw [toArrow_cons']
-/
@[simp]
theorem simplexCodF_nil (n : ℕ) : simplexCodF [] n = some ⟨mk n, mk n, 𝟙 _⟩ := by
  simp only [simplexCodF, Functor.id_obj]

@[simp]
lemma simplexCodF_δ (i n : ℕ) (h : i < n + 2) :
    simplexCodF [(i, σδ.δ)] n = some ⟨mk n, mk (n + 1), δ ⟨i, h⟩⟩ := by
  simp_all only [simplexCodF, true_and, Functor.id_obj, eqToHom_refl, Category.comp_id, dite_true]

@[simp]
lemma simplexCodF_σ (i n : ℕ) (h : i < n + 1) :
    simplexCodF [(i, σδ.σ)] (n + 1) = some ⟨mk (n + 1), mk n, σ ⟨i, h⟩⟩ := by
  simp_all only [simplexCodF, true_and, Functor.id_obj, eqToHom_refl, Category.comp_id, dite_true]

lemma simplexCod_δ_cond (i j : ℕ) (h : i ≤ j) :
    simplexCodF [(i, σδ.δ), (j + 1, σδ.δ)] = simplexCodF [(j, σδ.δ), (i, σδ.δ)] := by
  ext n : 1
  by_cases hn : j < n + 2
  · have hi1 : i < n + 2 := by omega
    have hi2 : i < n + 3 := by omega
    simp_all only [simplexCodF, true_and, Functor.id_obj, add_lt_add_iff_right, eqToHom_refl,
      Category.comp_id, dite_true, Category.id_comp, Option.some.injEq]
    congr 1
    convert δ_comp_δ _
    · rfl
    · assumption
  · simp_all only [simplexCodF, Functor.id_obj, add_lt_add_iff_right, false_and, dite_false,
    and_true, eqToHom_refl, Category.comp_id]
    split_ifs
    · simp
    · simp

lemma simplexCod_σ_cond (i j : ℕ) (h : i ≤ j) :
    simplexCodF [(i, σδ.σ), (j, σδ.σ)] = simplexCodF [(j + 1, σδ.σ), (i, σδ.σ)] := by
  ext n : 1
  induction' n with n ih
  · simp_all only [simplexCodF]
  · induction' n with n ih
    · simp_all only [simplexCodF, zero_add, Nat.lt_one_iff, Functor.id_obj, Fin.zero_eta,
      add_lt_iff_neg_right, not_lt_zero', false_and, dite_false]
    · by_cases hn : j < n + 1
      · have hi1 : i < n + 1 := by omega
        have hi2 : i < n + 2 := by omega
        simp_all only [simplexCodF, true_and, Functor.id_obj, add_lt_add_iff_right, eqToHom_refl,
          Category.comp_id, dite_true, Category.id_comp, Option.some.injEq, implies_true]
        congr 1
        convert σ_comp_σ _
        · rfl
        · assumption
      · simp_all only [simplexCodF, Functor.id_obj, add_lt_add_iff_right, false_and, dite_false,
        and_true, eqToHom_refl, Category.comp_id]
        split_ifs
        · simp
        · simp

lemma simplexCod_δ_σ_le (i j : ℕ) (h : i ≤ j) :
    simplexCodF [(i, σδ.δ), (j + 1, σδ.σ)] = simplexCodF [(j, σδ.σ), (i, σδ.δ)] := by
  ext n : 1
  induction' n with n ih
  · simp_all only [simplexCodF, zero_add, Functor.id_obj, add_lt_iff_neg_right, not_lt_zero',
    false_and, dite_false]
  · by_cases hn : j < n + 1
    · have hi1 : i < n + 2 := by omega
      have hi2 : i < n + 3 := by omega
      simp_all only [simplexCodF, true_and, Functor.id_obj, add_lt_add_iff_right, and_true,
        eqToHom_refl, Category.comp_id, dite_true, Category.id_comp, Option.some.injEq]
      congr 1
      convert δ_comp_σ_of_le _
      · rfl
      · simp_all only [Functor.id_obj, Nat.succ_eq_add_one, Fin.succ_mk]
      · simp_all only [Fin.castSucc_mk, Fin.mk_le_mk]
    · simp_all only [simplexCodF, Functor.id_obj, add_lt_add_iff_right, false_and, dite_false,
      and_true, eqToHom_refl, Category.comp_id]
      split_ifs
      · simp
      · simp

lemma simplexCod_δ_σ_eq (i n : ℕ) (h : i < n + 1) :
    simplexCodF [(i, σδ.δ), (i, σδ.σ)] n = simplexCodF [] n := by
  have : i < n + 1 := by omega
  have : i < n + 2 := by omega
  simp_all only [simplexCodF, true_and, Functor.id_obj, eqToHom_refl, Category.comp_id, dite_true,
    Category.id_comp, Option.some.injEq]
  congr 1
  convert δ_comp_σ_self
  · rfl

lemma simplexCod_δ_σ_succ (i n : ℕ) (h : i < n + 1) :
    simplexCodF [(i + 1, σδ.δ), (i, σδ.σ)] n = simplexCodF [] n := by
  have : i < n + 1 := by omega
  simp_all only [simplexCodF, add_lt_add_iff_right, true_and, Functor.id_obj, eqToHom_refl,
    Category.comp_id, dite_true, Category.id_comp, Option.some.injEq]
  congr 1
  convert δ_comp_σ_succ
  · rfl

lemma simplexCod_δ_σ_gt (i j : ℕ) (h : j < i) :
    simplexCodF [(i + 1, σδ.δ), (j, σδ.σ)] = simplexCodF [(j, σδ.σ), (i, σδ.δ)] := by
  ext n : 1
  induction' n with n ih
  · simp_all only [simplexCodF, zero_add, Functor.id_obj, Nat.lt_one_iff, Fin.zero_eta, and_true,
    eqToHom_refl, Category.comp_id, dite_eq_ite]
    split_ifs
    · simp_all only [zero_add, and_true, eqToHom_refl, Category.id_comp, dite_eq_right_iff,
      imp_false, not_lt]
      omega
    · simp_all only
  by_cases hn : i < n + 2
  · have : j < n + 1 := by omega
    have : j < n + 2 := by omega
    simp_all only [simplexCodF, add_lt_add_iff_right, Functor.id_obj, true_and, eqToHom_refl,
      Category.comp_id, dite_true, and_true, Category.id_comp, Option.some.injEq]
    congr 1
    convert δ_comp_σ_of_gt _
    · rfl
    · simp only [Fin.castSucc_mk]
    · simp_all only [Fin.castSucc_mk, Fin.mk_lt_mk]
  · simp_all only [simplexCodF, add_lt_add_iff_right, Functor.id_obj, and_true, eqToHom_refl,
    Category.comp_id, false_and, dite_false]
    split_ifs
    · simp
    · simp

@[simps]
def simplexCod : Δ🐟 where
  X := Option (Arrow SimplexCategory)
  F := simplexCodF
  δ_cond := simplexCod_δ_cond
  σ_cond := simplexCod_σ_cond
  δ_σ_le := simplexCod_δ_σ_le
  δ_σ_eq := simplexCod_δ_σ_eq
  δ_σ_succ := simplexCod_δ_σ_succ
  δ_σ_gt := simplexCod_δ_σ_gt

abbrev inσ : List ℕ → List (ℕ × σδ) := List.map (fun i => (i, σδ.σ))
abbrev inδ : List ℕ → List (ℕ × σδ) := List.map (fun i => (i, σδ.δ))

def toList {m n : SimplexCategory} (f : m ⟶ n) {k : ℕ} (F : Fin k ≃o Im f) : List (ℕ × σδ) :=
  inσ (toListGen f F) ++ inδ (monos.order2 f)

theorem toList_some {m n : SimplexCategory} (f : m ⟶ n) {k : ℕ} (F : Fin k ≃o Im f) :
    (simplexCodF (toList f F) m.len).isSome := sorry

theorem simplexCodF_toList {m n : SimplexCategory} (f : m ⟶ n) {k : ℕ} (F : Fin k ≃o Im f) :
    simplexCodF (toList f F) m.len = some f := sorry

def δSwap (a : ℕ) : ∀ _ : List ℕ, List ℕ × List ℕ
| [] => ([], [a])
| b :: l =>
  if a < b then ((b - 1) :: (δSwap a l).1, (δSwap a l).2) else
  if b + 1 < a then (b :: (δSwap (a - 1) l).1, (δSwap (a - 1) l).2)
  else (l, [])

def swapAux : ∀ (_ _ : List ℕ), List ℕ × List ℕ
| [], le => (le, [])
| a :: lm, le => ((swapAux lm (δSwap a le).1).1,
  (swapAux lm (δSwap a le).1).2 ++ (δSwap a le).2)

def swap (lm le : List ℕ) : List ℕ × List ℕ := ((swapAux lm.reverse le).1,
  (swapAux lm.reverse le).2)

@[simp]
def σInsert (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: σInsert (a - 1) l

@[simp]
def σSort : List ℕ → List ℕ
  | [] => []
  | b :: l => σInsert b (σSort l)

@[simp]
def δInsert (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: l => if a < b then a :: b :: l else b :: δInsert (a + 1) l

@[simp]
def δSort : List ℕ → List ℕ
  | [] => []
  | b :: l => δInsert b (δSort l)

def sort : List (ℕ × σδ) → List ℕ × List ℕ
| [] => ([], [])
| [(a, σδ.σ)] => ([a], [])
| [(a, σδ.δ)] => ([], [a])
| (a, σδ.σ) :: l => (σInsert a (sort l).1, (sort l).2)
| (a, σδ.δ) :: l => ((δSwap a (sort l).1).1, _)

end SimplexCategory
