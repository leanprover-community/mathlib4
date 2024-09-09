import Mathlib.AlgebraicTopology.SimplexCatEpis

universe v u

open CategoryTheory

def optionArrowComp {C : Type u} [Category C] [DecidableEq C]
    (f g : Option (Arrow C)) : Option (Arrow C) :=
  match f, g with
  | none, _ => none
  | _, none => none
  | some f, some g =>
    if H : f.right = g.left then some ⟨f.left, g.right, f.hom ≫ eqToHom H ≫ g.hom⟩ else none

inductive σδ where
| σ : σδ
| δ : σδ

open σδ in
structure SimplexCod where
  (X : Type u)
  (F : List (ℕ × σδ) → ℕ → X)
  (comp : X → X → X)
  (δ_cond : ∀ (i j : ℕ) (_ : i ≤ j), F [(i, δ), (j + 1, δ)] = F [(j, δ), (i, δ)])
  (σ_cond : ∀ (i j : ℕ) (_ : i ≤ j), F [(i, σ), (j, σ)] = F [(j + 1, σ), (i, σ)])
  (δ_σ_le : ∀ (i j : ℕ) (_ : i ≤ j), F [(i, δ), (j + 1, σ)] = F [(j, σ), (i, δ)])
  (δ_σ_eq : ∀ (i n : ℕ) (_ : i < n + 1), F [(i, δ), (i, σ)] n = F [] n)
  (δ_σ_succ : ∀ (i n : ℕ) (_ : i < n + 1), F [(i + 1, δ), (i, σ)] n = F [] n)
  (δ_σ_gt : ∀ (i j : ℕ) (_ : j < i), F [(i + 1, δ), (j, σ)] = F [(j, σ), (i, δ)])
  (F_comp : ∀ l₁ l₂ m n k, comp (F l₁ m) (F l₂ n) = F (l₁ ++ l₂) k)

notation "Δ🐟" => SimplexCod

structure SimplexCodCat where
  (C : Type u)
  [instCategory : Category C]
  [instDecidableEq : DecidableEq C]
  (obj : ℕ → C)
  (δ : ∀ {n : ℕ} (_ : Fin (n + 2)), obj n ⟶ obj (n + 1))
  (σ : ∀ {n : ℕ} (_ : Fin (n + 1)), obj (n + 1) ⟶ obj n)
  (δ_comp_δ : ∀ {n : ℕ} {i j : Fin (n + 2)} (_ : i ≤ j),
    δ i ≫ δ j.succ = δ j ≫ δ i.castSucc)
  (σ_comp_σ : ∀ {n : ℕ} {i j : Fin (n + 1)} (_ : i ≤ j),
    σ i.castSucc ≫ σ j = σ j.succ ≫ σ i)
  (δ_comp_σ_of_le : ∀ {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ Fin.castSucc j),
    δ (Fin.castSucc i) ≫ σ j.succ = σ j ≫ δ i)
  (δ_comp_σ_self : ∀ {n} {i : Fin (n + 1)}, δ (Fin.castSucc i) ≫ σ i = 𝟙 (obj n))
  (δ_comp_σ_succ : ∀ {n} {i : Fin (n + 1)}, δ i.succ ≫ σ i = 𝟙 (obj n))
  (δ_comp_σ_of_gt : ∀ {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i),
    δ i.succ ≫ σ (Fin.castSucc j) = σ j ≫ δ i)

attribute [instance] SimplexCodCat.instCategory SimplexCodCat.instDecidableEq

notation "Δ🐟🐈" => SimplexCodCat

namespace SimplexCategory

@[simps]
def simplexCodCat : Δ🐟🐈 where
  C := SimplexCategory
  instCategory := inferInstance
  obj := mk
  δ := δ
  σ := σ
  δ_comp_δ := δ_comp_δ
  σ_comp_σ := σ_comp_σ
  δ_comp_σ_of_le := δ_comp_σ_of_le
  δ_comp_σ_self := δ_comp_σ_self
  δ_comp_σ_succ := δ_comp_σ_succ
  δ_comp_σ_of_gt := δ_comp_σ_of_gt

end SimplexCategory
namespace SimplexCodCat
variable (C : Δ🐟🐈)

def simplexCodF : List (ℕ × σδ) → ℕ → Option (Arrow C.C)
| [], n => Option.some ⟨C.obj n, C.obj n, 𝟙 _⟩
| (_, σδ.σ) :: _, 0 => none
| (a, σδ.σ) :: l, n + 1 => Option.recOn (simplexCodF l n) none fun l =>
  if ha : a < n + 1 ∧ C.obj n = l.1 then
  some ⟨C.obj (n + 1), l.2, C.σ ⟨a, ha.1⟩ ≫ eqToHom ha.2 ≫ l.hom⟩ else none
| (a, σδ.δ) :: l, n => Option.recOn (simplexCodF l (n + 1)) none fun l =>
  if ha : a < n + 2 ∧ C.obj (n + 1) = l.1 then
  some ⟨C.obj n, l.2, C.δ  ⟨a, ha.1⟩ ≫ eqToHom ha.2 ≫ l.hom⟩ else none

variable {C}

@[simp]
theorem δ_none_cons {l : List (ℕ × σδ)} {a n : ℕ} (hl : simplexCodF C l (n + 1) = none) :
    simplexCodF C ((a, σδ.δ) :: l) n = none := by
  simp_all only [simplexCodF, Functor.id_obj]

@[simp]
theorem σ_none_cons {l : List (ℕ × σδ)} {a n : ℕ} (hl : simplexCodF C l n = none) :
    simplexCodF C ((a, σδ.σ) :: l) (n + 1) = none := by
  simp_all only [simplexCodF, Functor.id_obj]

@[simp]
theorem δ_of_some_cons {l : List (ℕ × σδ)} {a n : ℕ}
    (hl : (simplexCodF C ((a, σδ.δ) :: l) n).isSome) :
    (simplexCodF C l (n + 1)).isSome := by
  contrapose! hl
  simp_all only [ne_eq, Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none,
    δ_none_cons, Option.isSome_none, Bool.false_eq_true, not_false_eq_true]

@[simp]
theorem σ_of_some_cons {l : List (ℕ × σδ)} {a n : ℕ}
    (hl : (simplexCodF C ((a, σδ.σ) :: l) (n + 1)).isSome) :
    (simplexCodF C l n).isSome := by
  contrapose! hl
  simp_all only [ne_eq, Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none,
    σ_none_cons, Option.isSome_none, Bool.false_eq_true, not_false_eq_true]

theorem δ_none_of_not {l : List (ℕ × σδ)} {a n : ℕ}
    {f : Arrow C.C}
    (hl : (simplexCodF C l (n + 1)) = some f)
    (hcond : ¬(a < n + 2 ∧ C.obj (n + 1) = f.left)) :
    simplexCodF C ((a, σδ.δ) :: l) n = none := by
  rw [simplexCodF]
  simp_all only [not_and, Functor.id_obj, dite_eq_right_iff, imp_false, not_false_eq_true,
    implies_true]

theorem σ_none_of_not {l : List (ℕ × σδ)} {a n : ℕ}
    {f : Arrow C.C}
    (hl : (simplexCodF C l n) = some f)
    (hcond : ¬(a < n + 1 ∧ C.obj n = f.left)) :
    simplexCodF C ((a, σδ.σ) :: l) (n + 1) = none := by
  rw [simplexCodF]
  simp_all only [not_and, Functor.id_obj, dite_eq_right_iff, imp_false, not_false_eq_true,
    implies_true]

theorem δ_some_cond' {l : List (ℕ × σδ)} {a n : ℕ} {f : Arrow C.C}
    (hl : (simplexCodF C l (n + 1)) = some f)
    (hal : (simplexCodF C ((a, σδ.δ) :: l) n).isSome) :
    a < n + 2 ∧ C.obj (n + 1) = f.left := by
  contrapose hal
  simp_all only [Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none]
  exact δ_none_of_not hl hal

theorem σ_some_cond' {l : List (ℕ × σδ)} {a n : ℕ} {f : Arrow C.C}
    (hl : (simplexCodF C l n) = some f)
    (hal : (simplexCodF C ((a, σδ.σ) :: l) (n + 1)).isSome) :
    a < n + 1 ∧ C.obj n = f.left := by
  contrapose hal
  simp_all only [Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none]
  exact σ_none_of_not hl hal

def get {l : List (ℕ × σδ)} {n : ℕ} (H : (simplexCodF C l n).isSome) :
  Arrow C.C := Option.get _ H

def getδTail {l : List (ℕ × σδ)} {n : ℕ} {a : ℕ} (H : (simplexCodF C ((a, σδ.δ) :: l) n).isSome) :
    Arrow C.C := get (δ_of_some_cons H)

def getσTail {l : List (ℕ × σδ)} {n : ℕ} {a : ℕ}
    (H : (simplexCodF C ((a, σδ.σ) :: l) (n + 1)).isSome) :
    Arrow C.C := get (σ_of_some_cons H)

theorem δ_some_cond {l : List (ℕ × σδ)} {a n : ℕ}
    (hal : (simplexCodF C ((a, σδ.δ) :: l) n).isSome) :
    a < n + 2 ∧ C.obj (n + 1) = (getδTail hal).left := by
  apply δ_some_cond' (l := l)
  unfold getδTail get
  simp only [Option.some_get]
  exact hal

theorem σ_some_cond {l : List (ℕ × σδ)} {a n : ℕ}
    (hal : (simplexCodF C ((a, σδ.σ) :: l) (n + 1)).isSome) :
    a < n + 1 ∧ C.obj n = (getσTail hal).left := by
  apply σ_some_cond' (l := l)
  rw [getσTail, get]
  simp only [Option.some_get]
  exact hal

theorem get_δ_cons' {l : List (ℕ × σδ)} {a n : ℕ} {f : Arrow C.C}
    (hl : (simplexCodF C l (n + 1)) = some f)
    (hal : (simplexCodF C ((a, σδ.δ) :: l) n).isSome) :
    get hal = ⟨C.obj n, f.2,
      C.δ ⟨a, (δ_some_cond hal).1⟩ ≫ eqToHom (δ_some_cond' hl hal).2 ≫ f.hom⟩ := by
  simp_all only [get, simplexCodF, Functor.id_obj]
  simp_rw [dif_pos (δ_some_cond' hl hal)]
  simp only [Option.get_some]

theorem get_σ_cons' {l : List (ℕ × σδ)} {a n : ℕ} {f : Arrow C.C}
    (hl : (simplexCodF C l n) = some f)
    (hal : (simplexCodF C ((a, σδ.σ) :: l) (n + 1)).isSome) :
    get hal = ⟨C.obj (n + 1), f.2,
      C.σ ⟨a, (σ_some_cond hal).1⟩ ≫ eqToHom (σ_some_cond' hl hal).2 ≫ f.hom⟩ := by
  simp_all only [get, simplexCodF, Functor.id_obj]
  simp_rw [dif_pos (σ_some_cond' hl hal)]
  simp only [Option.get_some]

theorem getδTail_eq {l : List (ℕ × σδ)} {a n : ℕ}
    (hal : (simplexCodF C ((a, σδ.δ) :: l) n).isSome) :
    simplexCodF C l (n + 1) = some (getδTail hal) := by
  simp only [simplexCodF, getδTail, get, Option.some_get]

theorem getσTail_eq {l : List (ℕ × σδ)} {a n : ℕ}
    (hal : (simplexCodF C ((a, σδ.σ) :: l) (n + 1)).isSome) :
    simplexCodF C l n = some (getσTail hal) := by
  simp only [simplexCodF, getσTail, get, Option.some_get]

theorem get_δ_cons {l : List (ℕ × σδ)} {a n : ℕ} (hal : (simplexCodF C ((a, σδ.δ) :: l) n).isSome) :
    get hal = ⟨C.obj n, (getδTail hal).2,
      C.δ ⟨a, (δ_some_cond' (getδTail_eq hal) hal).1⟩
      ≫ eqToHom (δ_some_cond' (getδTail_eq hal) hal).2
      ≫ (getδTail hal).hom⟩ :=
  get_δ_cons' (getδTail_eq hal) _

theorem get_σ_cons {l : List (ℕ × σδ)} {a n : ℕ} (hal : (simplexCodF C ((a, σδ.σ) :: l) (n + 1)).isSome) :
    get hal = ⟨C.obj (n + 1), (getσTail hal).2,
      C.σ ⟨a, (σ_some_cond' (getσTail_eq hal) hal).1⟩
      ≫ eqToHom (σ_some_cond' (getσTail_eq hal) hal).2
      ≫ (getσTail hal).hom⟩ :=
  get_σ_cons' (getσTail_eq hal) _

theorem get_left {l : List (ℕ × σδ)} {n : ℕ}
    (hl : (simplexCodF C l n).isSome) :
    (get hl).left = C.obj n := by
  induction' l with a l _
  · simp_all only [get, Functor.id_obj]
    rfl
  · obtain ⟨q, a⟩ := a
    cases a
    · induction' n with n hn
      · exfalso
        simp_all only [simplexCodF, Option.isSome_none, Bool.false_eq_true]
      · rw [get_σ_cons]
    · rw [get_δ_cons]

theorem δ_some_cons {l : List (ℕ × σδ)} {a n : ℕ} (h : a < n + 2)
    (hl : (simplexCodF C l (n + 1)).isSome) : (simplexCodF C ((a, σδ.δ) :: l) n).isSome := by
  rw [simplexCodF, ← Option.some_get hl]
  simp only [Functor.id_obj]
  rw [dif_pos]
  simp only [Option.isSome_some]
  constructor
  · assumption
  · erw [get_left]

theorem σ_some_cons {l : List (ℕ × σδ)} {a n : ℕ} (h : a < n + 1)
    (hl : (simplexCodF C l n).isSome) : (simplexCodF C ((a, σδ.σ) :: l) (n + 1)).isSome := by
  rw [simplexCodF, ← Option.some_get hl]
  simp only [Functor.id_obj]
  rw [dif_pos]
  simp only [Option.isSome_some]
  constructor
  · assumption
  · erw [get_left]

abbrev right (n : ℕ) : List (ℕ × σδ) → ℕ
| [] => n
| (a, σδ.σ) :: l => right (n - 1) l
| (a, σδ.δ) :: l => right (n + 1) l

lemma right_nil (n : ℕ) : right n [] = n := rfl

lemma right_σ (n : ℕ) {a : ℕ} {l : List (ℕ × σδ)} :
    right n ((a, σδ.σ) :: l) = right (n - 1) l := rfl

lemma right_δ (n : ℕ) {a : ℕ} {l : List (ℕ × σδ)} :
    right n ((a, σδ.δ) :: l) = right (n + 1) l := rfl

theorem get_right {l : List (ℕ × σδ)} {n : ℕ} (hl : (simplexCodF C l n).isSome) :
    (get hl).right = C.obj (right n l) := by
  induction' l with a l ih generalizing n
  · simp_all only [get, simplexCodF, Functor.id_obj, Option.get_some]
  · obtain ⟨q, a⟩ := a
    cases a
    · induction' n with n hn
      · exfalso
        simp_all only [simplexCodF, Option.isSome_none, Bool.false_eq_true]
      · specialize @ih n (σ_of_some_cons hl)
        rw [right_σ, get_σ_cons, add_tsub_cancel_right]
        exact ih
    · specialize @ih (n + 1) (δ_of_some_cons hl)
      rw [right_δ, get_δ_cons]
      exact ih

@[simp]
theorem simplexCodF_nil (n : ℕ) : simplexCodF C [] n = some ⟨C.obj n, C.obj n, 𝟙 _⟩ := by
  simp only [simplexCodF, Functor.id_obj]

@[simp]
lemma simplexCodF_δ (i n : ℕ) (h : i < n + 2) :
    simplexCodF C [(i, σδ.δ)] n = some ⟨C.obj n, C.obj (n + 1), C.δ  ⟨i, h⟩⟩ := by
  simp_all only [simplexCodF, true_and, Functor.id_obj, eqToHom_refl, Category.comp_id, dite_true]

@[simp]
lemma simplexCodF_σ (i n : ℕ) (h : i < n + 1) :
    simplexCodF C [(i, σδ.σ)] (n + 1) = some ⟨C.obj (n + 1), C.obj n, C.σ ⟨i, h⟩⟩ := by
  simp_all only [simplexCodF, true_and, Functor.id_obj, eqToHom_refl, Category.comp_id, dite_true]

lemma simplexCod_δ_cond (i j : ℕ) (h : i ≤ j) :
    simplexCodF C [(i, σδ.δ), (j + 1, σδ.δ)] = simplexCodF C [(j, σδ.δ), (i, σδ.δ)] := by
  ext n : 1
  by_cases hn : j < n + 2
  · have hi1 : i < n + 2 := by omega
    have hi2 : i < n + 3 := by omega
    simp_all only [simplexCodF, true_and, Functor.id_obj, add_lt_add_iff_right, eqToHom_refl,
      Category.comp_id, dite_true, Category.id_comp, Option.some.injEq]
    congr 1
    convert C.δ_comp_δ _
    · rfl
    · assumption
  · simp_all only [simplexCodF, Functor.id_obj, add_lt_add_iff_right, false_and, dite_false,
    and_true, eqToHom_refl, Category.comp_id]
    split_ifs
    · simp
    · simp

lemma simplexCod_σ_cond (i j : ℕ) (h : i ≤ j) :
    simplexCodF C [(i, σδ.σ), (j, σδ.σ)] = simplexCodF C [(j + 1, σδ.σ), (i, σδ.σ)] := by
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
        convert C.σ_comp_σ _
        · rfl
        · assumption
      · simp_all only [simplexCodF, Functor.id_obj, add_lt_add_iff_right, false_and, dite_false,
        and_true, eqToHom_refl, Category.comp_id]
        split_ifs
        · simp
        · simp

lemma simplexCod_δ_σ_le (i j : ℕ) (h : i ≤ j) :
    simplexCodF C [(i, σδ.δ), (j + 1, σδ.σ)] = simplexCodF C [(j, σδ.σ), (i, σδ.δ)] := by
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
      convert C.δ_comp_σ_of_le _
      · rfl
      · simp_all only [Functor.id_obj, Nat.succ_eq_add_one, Fin.succ_mk]
      · simp_all only [Fin.castSucc_mk, Fin.mk_le_mk]
    · simp_all only [simplexCodF, Functor.id_obj, add_lt_add_iff_right, false_and, dite_false,
      and_true, eqToHom_refl, Category.comp_id]
      split_ifs
      · simp
      · simp

lemma simplexCod_δ_σ_eq (i n : ℕ) (h : i < n + 1) :
    simplexCodF C [(i, σδ.δ), (i, σδ.σ)] n = simplexCodF C [] n := by
  have : i < n + 1 := by omega
  have : i < n + 2 := by omega
  simp_all only [simplexCodF, true_and, Functor.id_obj, eqToHom_refl, Category.comp_id, dite_true,
    Category.id_comp, Option.some.injEq]
  congr 1
  convert C.δ_comp_σ_self
  · rfl

lemma simplexCod_δ_σ_succ (i n : ℕ) (h : i < n + 1) :
    simplexCodF C [(i + 1, σδ.δ), (i, σδ.σ)] n = simplexCodF C [] n := by
  have : i < n + 1 := by omega
  simp_all only [simplexCodF, add_lt_add_iff_right, true_and, Functor.id_obj, eqToHom_refl,
    Category.comp_id, dite_true, Category.id_comp, Option.some.injEq]
  congr 1
  convert C.δ_comp_σ_succ
  · rfl

lemma simplexCod_δ_σ_gt (i j : ℕ) (h : j < i) :
    simplexCodF C [(i + 1, σδ.δ), (j, σδ.σ)] = simplexCodF C [(j, σδ.σ), (i, σδ.δ)] := by
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
    convert C.δ_comp_σ_of_gt _
    · rfl
    · simp only [Fin.castSucc_mk]
    · simp_all only [Fin.castSucc_mk, Fin.mk_lt_mk]
  · simp_all only [simplexCodF, add_lt_add_iff_right, Functor.id_obj, and_true, eqToHom_refl,
    Category.comp_id, false_and, dite_false]
    split_ifs
    · simp
    · simp

section Comp

theorem simplexCodF_some_append {x y : List (ℕ × σδ)} {m n : ℕ}
    (hx : (simplexCodF C x m).isSome)
    (hy : (simplexCodF C y n).isSome) (h : right m x = n) :
    (simplexCodF C (x ++ y) m).isSome := by
  induction' x with a l hal generalizing m
  · simp_all only [simplexCodF_nil, Functor.id_obj, Option.isSome_some, List.nil_append]
  · obtain ⟨q, a⟩ := a
    cases a
    · induction' m with m hm
      · exfalso
        simp_all only [simplexCodF, Option.isSome_none, Bool.false_eq_true]
      · simp_all only [List.length_cons, List.cons_append, add_right_eq_self, one_ne_zero,
        false_implies, implies_true]
        apply σ_some_cons (σ_some_cond hx).1
        specialize @hal m (σ_of_some_cons hx) ?_
        rw [← h, right_σ, add_tsub_cancel_right]
        · assumption
    · simp_all only [List.length_cons, List.cons_append]
      rw [simplexCodF]
      specialize @hal (m + 1) (δ_of_some_cons hx) ?_
      · rw [← h, right_δ]
      · rw [← Option.some_get hal]
        simp only [Functor.id_obj]
        rw [dif_pos]
        simp only [Option.isSome_some]
        constructor
        · exact (δ_some_cond hx).1
        · exact (get_left hal).symm

#exit
end Comp
variable (C) in
@[simps]
def simplexCod : Δ🐟 where
  X := Option (Arrow C.C)
  F := simplexCodF C
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
