/-
Copyright (c) 2025 Rudy Peterson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rudy Peterson
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Computability.Language

/-!
# Weigted Languages

TODO: explain
-/

open List Computability

-- section Lists

-- universe a b

-- variable {α : Type a} {β : Type b} (f g : α → β)

-- -- Is this not already a lemma?
-- lemma List.Disjoint_self (l : List α) :
--     (∃ a, a ∈ l) → ¬ l.Disjoint l := by simp [Disjoint]

-- def List.splits (x : List α) : List (List α × List α) :=
--   List.map x.splitAt (range (x.length + 1))

-- @[simp]
-- lemma List.splits_nil : (List.nil (α:=α)).splits= [([], [])] := by rfl

-- @[simp]
-- lemma List.splits_cons (x : α) (xs : List α) :
--     List.splits (x :: xs) =
--     ([], x :: xs) :: List.map (fun td ↦ (x :: td.1, td.2)) (List.splits xs) := by
--   simp [List.splits]
--   rw [List.range_succ_eq_map]
--   simp

-- lemma List.splits_Nodup (l : List α) : l.splits.Nodup := by
--   simp [List.splits]
--   apply List.Nodup.map_on
--   · simp
--     intro n1 hn1 n2 hn2 hmin hdrop
--     omega
--   · apply List.nodup_range

-- lemma List.splits_spec (x y l : List α) :
--     (x, y) ∈ l.splits ↔ l = x ++ y := by
--   simp [List.splits]
--   constructor
--   · rintro ⟨n, hn, htake, hdrop⟩
--     rw [←htake, ←hdrop, List.take_append_drop]
--   · rintro rfl
--     exists x.length
--     constructor
--     · simp; omega
--     · constructor
--       · rw [List.take_left]
--       · rw [List.drop_left]

-- lemma List.splits_non_empty (l : List α) : ∃ td, td ∈ l.splits := by
--   exists ([], l)
--   simp [List.splits_spec]

-- lemma List.splits_exists_Perm (l : List α) : ∃ l', l.splits ~ l' := by
--  exists l.splits

-- lemma List.map_get? (n : Nat) (l : List α) :
--   (List.map f l).get? n = Option.map f (l.get? n) := by
--   revert n
--   induction l <;> intros n <;> simp only [List.map]
--   case nil =>
--     simp
--   case cons h t ih =>
--     cases n <;> simp

-- /-- Left-associative triple splits of a list. -/
-- def List.splits3_l : List α → List (List α × List α × List α) :=
--   List.flatMap
--   (fun td ↦
--     td.1
--     |> List.splits
--     |> List.map (fun t ↦ (t.1, t.2, td.2)))
--   ∘ List.splits

-- lemma List.splits3_l_Nodup (l : List α) : l.splits3_l.Nodup := by
--   simp [List.splits3_l, List.nodup_flatMap]
--   constructor
--   · intros t d htd_splits
--     apply List.Nodup.map_on
--     · rintro ⟨ta1, ta2⟩ hta_splits ⟨tb1, tb2⟩ htb_splits
--       simp
--     · apply List.splits_Nodup
--   · induction l
--     case nil =>
--       simp
--     case cons a l ihl =>
--       simp
--       constructor
--       · clear ihl
--         rintro b c x1 x2 hx1x2_l_splits rfl rfl
--         simp [Function.onFun]
--       · refine (List.Pairwise.map ?_ ?_ ihl); clear ihl
--         rintro ⟨x1, x2⟩ ⟨y1, y2⟩
--         simp [Function.onFun]
--         intro hdisj_map
--         constructor
--         · rintro rfl rfl
--           apply List.Disjoint.of_map at hdisj_map
--           apply List.Disjoint_self _ (List.splits_non_empty _) at hdisj_map
--           assumption
--         · rintro ⟨xx1, xx2, x2'⟩ hx1_splits hy1_splits
--           simp [List.mem_map] at hx1_splits hy1_splits
--           rcases hx1_splits with ⟨xx1', xx2', hx1_splits, rfl, rfl, rfl⟩
--           rcases hy1_splits with ⟨yy1', yy2', hy1_splits, ⟨_, rfl⟩, rfl, rfl⟩
--           simp [Disjoint] at hdisj_map
--           specialize hdisj_map _ _ _ _ _ hx1_splits rfl rfl rfl _ _ hy1_splits rfl rfl
--           contradiction

-- lemma List.splits3_l_spec (x y z l : List α) :
--     (x, y, z) ∈ l.splits3_l ↔ l = x ++ y ++ z := by
--   simp [List.splits3_l, List.splits_spec]
--   constructor
--   · rintro ⟨a, b, rfl, a', b', rfl, rfl, rfl, rfl⟩
--     simp [List.append_assoc]
--   · rintro rfl
--     exists (x ++ y), z
--     simp [List.append_assoc]

-- /-- Right-associative triple splits of a list. -/
-- def List.splits3_r : List α → List (List α × List α × List α) :=
--   List.flatMap
--   (fun td ↦
--     td.2
--     |> List.splits
--     |> List.map (fun d ↦ (td.1, d.1, d.2)))
--   ∘ List.splits

-- lemma List.splits3_r_Nodup (l : List α) : l.splits3_r.Nodup := by
--   simp [List.splits3_r, List.nodup_flatMap]
--   constructor
--   · intros t d htd_l_splits
--     apply List.Nodup.map_on
--     · rintro ⟨d1, d2⟩ hd_splits ⟨d1', d2'⟩ hd'_splits ⟨_, rfl, rfl⟩
--       rfl
--     · apply List.splits_Nodup
--   · induction l
--     case nil =>
--       simp
--     case cons a l ihl =>
--       simp
--       constructor
--       · clear ihl
--         rintro b c l1 l2 hl_splits rfl rfl
--         simp [Function.onFun, Function.comp, List.Disjoint]
--         rintro y1 y2 b y1' y2' hy' rfl rfl rfl z1 z2 hz ⟨⟩
--       · refine (List.Pairwise.map ?_ ?_ ihl); clear ihl
--         rintro ⟨x1, x2⟩ ⟨y1, y2⟩
--         simp [Function.onFun]
--         intro hdisj_map
--         rintro ⟨t, d1, d2⟩ hx2_splits hy2_splits
--         simp [List.mem_map] at hx2_splits hy2_splits
--         rcases hx2_splits with ⟨hx2_splits, rfl⟩
--         rcases hy2_splits with ⟨hy2_splits, ⟨_, rfl⟩⟩
--         apply List.Disjoint.of_map at hdisj_map
--         specialize hdisj_map hx2_splits hy2_splits
--         contradiction

-- lemma List.splits3_r_spec (x y z l : List α) :
--     (x, y, z) ∈ l.splits3_r ↔ l = x ++ y ++ z := by
--   simp [List.splits3_r, List.splits_spec]
--   constructor
--   · rintro ⟨a, b, rfl, rfl, rfl⟩
--     rfl
--   · rintro rfl
--     exists x, (y ++ z)

-- lemma List.splits3_l_r_Perm (l : List α) : l.splits3_l ~ l.splits3_r := by
--   rw [List.perm_ext_iff_of_nodup]
--   · rintro ⟨x, y, z⟩
--     simp only [List.splits3_l_spec, List.splits3_r_spec]
--   · apply List.splits3_l_Nodup
--   · apply List.splits3_r_Nodup

-- end Lists

section SemiOps

universe k

variable {κ : Type k} [W : Semiring κ]

lemma sum_left_distrib (w : κ) (l : List κ) :
  l.sum * w = (List.map (· * w) l).sum := by
  induction l <;> simp
  case cons h t ih =>
    rw [←ih, W.right_distrib]

lemma sum_right_distrib (l : List κ) (w : κ) :
  w * l.sum = (List.map (w * ·) l).sum := by
  induction l <;> simp
  case cons h t ih =>
    rw [←ih, W.left_distrib]

end SemiOps

universe u k

/--
A weighted language is a map from strings over an alphabet to
elements of a semiring.
-/
def WeightedLanguage (α : Type u) (κ : Type k) : Type (max u k) :=
  List α → κ

namespace WeightedLanguage

variable {α : Type u} {κ : Type k} [W : Semiring κ]

instance instInhabited : Inhabited (WeightedLanguage α κ) := ⟨fun _ ↦ 0⟩

instance instZero : Zero (WeightedLanguage α κ) := ⟨fun _ ↦ 0⟩

lemma zero_def_eq : (0 : WeightedLanguage α κ) = fun (_ : List α) ↦ (0 : κ) := by
  rfl

def onlyNil : List α → κ
  | [] => 1
  | _  => 0

lemma onlyNil_gives_zero (x : List α) :
  0 < x.length → onlyNil x = (0 : κ) := by
  intros hx
  cases x <;> simp [onlyNil] at *

instance instOne : One (WeightedLanguage α κ) := ⟨onlyNil⟩

lemma one_def_eq :
  (1 : WeightedLanguage α κ) = onlyNil := by
  rfl

lemma one_gives_zero (x : List α) :
  0 < x.length → (1 : WeightedLanguage α κ) x = 0 := by
  intros hx
  simp [one_def_eq]
  cases x <;> simp [onlyNil] at *

def add_def (f g : WeightedLanguage α κ) : WeightedLanguage α κ :=
  fun x ↦ f x + g x

instance instAdd : Add (WeightedLanguage α κ) where
  add := add_def

lemma add_def_eq (f g : WeightedLanguage α κ) :
  f + g = add_def f g := by
  rfl

lemma add_def_comm (f g : WeightedLanguage α κ) :
  f + g = g + f := by
  simp [add_def_eq]
  funext x
  apply W.add_comm

lemma add_def_assoc (f g h : WeightedLanguage α κ) :
  (f + g) + h = f + (g + h) := by
  funext x
  simp [add_def_eq, add_def]
  apply W.add_assoc

lemma zero_add_def (f : WeightedLanguage α κ) :
  0 + f = f := by
  funext x
  simp [add_def_eq, add_def, zero_def_eq]

lemma add_def_zero (f : WeightedLanguage α κ) :
  f + 0 = f := by
  funext x
  simp [add_def_eq, add_def, zero_def_eq]

def cauchy_prod (f g : WeightedLanguage α κ) : WeightedLanguage α κ :=
  List.sum ∘ (List.map (fun x ↦ f x.1 * g x.2)) ∘ splits

lemma zero_cauchy_prod (f : WeightedLanguage α κ) :
  (0 : WeightedLanguage α κ).cauchy_prod f = 0 := by
  funext x
  simp only [zero_def_eq, Function.comp, cauchy_prod]
  simp only [splits, List.map_map, List.splitAt_eq]
  conv_lhs => {
    arg 1
    arg 1
    ext n
    simp
  }
  simp [List.map_const']

lemma cauchy_prod_zero (f : WeightedLanguage α κ) :
  f.cauchy_prod 0 = 0 := by
  funext x
  simp only [zero_def_eq, Function.comp, cauchy_prod]
  simp only [splits, List.map_map, List.splitAt_eq]
  conv_lhs => {
    arg 1
    arg 1
    ext n
    simp
  }
  simp [List.map_const']

lemma one_cauchy_prod (f : WeightedLanguage α κ) :
  (1 : WeightedLanguage α κ).cauchy_prod f = f := by
  funext x
  simp only [one_def_eq, cauchy_prod, Function.comp]
  simp only [splits, List.map_map, List.splitAt_eq]
  conv_lhs => {
    arg 1
    arg 1
    ext n
    simp
  }
  simp [List.range_succ_eq_map]
  conv_lhs => {
    congr
    · simp [onlyNil]
    · arg 1
      arg 1
      ext n
      simp
  }
  rw (occs := [2]) [←W.add_zero (f x)]
  congr
  cases x <;> simp
  case cons a x =>
    simp [onlyNil]

lemma cauchy_prod_one (f : WeightedLanguage α κ) :
  f.cauchy_prod 1 = f := by
  funext x
  simp only [one_def_eq, cauchy_prod, Function.comp]
  simp only [splits, List.map_map, List.splitAt_eq]
  conv_lhs => {
    arg 1
    arg 1
    ext n
    simp
  }
  simp [List.range_add]
  simp [List.range_succ_eq_map]
  conv_lhs => {
    congr
    · arg 1
      arg 1
      ext n
      simp
    · simp [onlyNil]
  }
  rw (occs := [2]) [←W.add_zero (f x)]
  rw [W.add_comm (f x) 0]
  congr
  have hsilly : (0 : κ) = (List.replicate x.length 0).sum := by simp
  rw [hsilly]; clear hsilly
  congr
  simp [←List.map_const']
  have hsilly : map (fun _ : α ↦ (0 : κ)) x =
    map (fun _ : Nat ↦ (0 : κ)) (range x.length) := by simp
  rw [hsilly]; clear hsilly
  rw [←List.forall₂_eq_eq_eq]
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  rw [List.forall₂_same]
  intros n hn
  rw [List.mem_range] at hn
  have hdrop : 0 < (drop n x).length := by {
    apply List.lt_length_drop
    revert hn
    simp
  }
  simp [onlyNil_gives_zero _ hdrop]

lemma cauchy_prod_left_distrib (f g h : WeightedLanguage α κ) :
  f.cauchy_prod (g + h) = f.cauchy_prod g + f.cauchy_prod h := by
  funext x
  simp only [cauchy_prod, add_def_eq, add_def, Function.comp]
  simp only [splits, List.map_map, List.splitAt_eq]
  rw [List.sum_add_sum_eq_sum_zipWith_of_length_eq]
  · congr
    simp only [List.zipWith_map, List.zipWith_self]
    rw [←List.forall₂_eq_eq_eq]
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    rw [List.forall₂_same]
    intros n hn
    simp [W.left_distrib]
  · simp only [List.length_map]

lemma cauchy_prod_right_distrib (f g h : WeightedLanguage α κ) :
  (g + h).cauchy_prod f = g.cauchy_prod f + h.cauchy_prod f := by
  funext x
  simp only [cauchy_prod, add_def_eq, add_def, Function.comp]
  simp only [splits, List.map_map, List.splitAt_eq]
  rw [List.sum_add_sum_eq_sum_zipWith_of_length_eq]
  · congr
    simp only [List.zipWith_map, List.zipWith_self]
    rw [←List.forall₂_eq_eq_eq]
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    rw [List.forall₂_same]
    intros n hn
    simp [W.right_distrib]
  · simp only [List.length_map]

-- Left-associative cauchy product between three languages.
def cauchy_triple_l (f g h : WeightedLanguage α κ) : WeightedLanguage α κ :=
  List.sum ∘ (List.map (fun x ↦ (f x.1 * g x.2.1) * h x.2.2)) ∘ List.splits3_l

lemma cauchy_prod_triple_l (f g h : WeightedLanguage α κ) :
    (f.cauchy_prod g).cauchy_prod h = cauchy_triple_l f g h := by
  funext l
  simp only [cauchy_prod, cauchy_triple_l, Function.comp, sum_left_distrib]
  simp only [List.map_map, List.splits3_l, Function.comp]
  simp only [List.map_flatMap, List.flatMap_def]
  simp [List.map_map]
  unfold Function.comp; simp
  unfold Function.comp; simp

-- Right-associative cauchy product between three languages.
def cauchy_triple_r (f g h : WeightedLanguage α κ) : WeightedLanguage α κ :=
  List.sum ∘ (List.map (fun x ↦ f x.1 * (g x.2.1 * h x.2.2))) ∘ List.splits3_r

lemma cauchy_prod_triple_r (f g h : WeightedLanguage α κ) :
    f.cauchy_prod (g.cauchy_prod h) = cauchy_triple_r f g h := by
  funext l
  simp only [cauchy_prod, cauchy_triple_r, Function.comp, sum_right_distrib]
  simp only [List.map_map, List.splits3_r, Function.comp]
  simp only [List.map_flatMap, List.flatMap_def]
  simp [List.map_map]
  unfold Function.comp; simp
  unfold Function.comp; simp

lemma cauchy_triple_l_r (f g h : WeightedLanguage α κ) :
    cauchy_triple_l f g h = cauchy_triple_r f g h := by
  funext l
  simp [cauchy_triple_l, cauchy_triple_r, Function.comp, W.mul_assoc]
  apply_rules [List.Perm.sum_eq, List.Perm.map, List.splits3_l_r_Perm]

lemma cauchy_prod_assoc (f g h : WeightedLanguage α κ) :
  (f.cauchy_prod g).cauchy_prod h = f.cauchy_prod (g.cauchy_prod h) := by
  rw [cauchy_prod_triple_l, cauchy_triple_l_r, ←cauchy_prod_triple_r]

instance instMul : Mul (WeightedLanguage α κ) where
  mul := cauchy_prod

lemma mul_def_eq (f g : WeightedLanguage α κ) :
  f * g = cauchy_prod f g := by rfl

lemma mul_def_left_distrib (f g h : WeightedLanguage α κ) :
    f * (g + h) = f * g + f * h := by
  simp [mul_def_eq, cauchy_prod_left_distrib]

lemma mul_def_right_distrib (f g h : WeightedLanguage α κ) :
    (g + h) * f = g * f + h * f := by
  simp [mul_def_eq, cauchy_prod_right_distrib]

lemma mul_def_assoc (f g h : WeightedLanguage α κ) :
  (f * g) * h = f * (g * h) := by
  simp [mul_def_eq, cauchy_prod_assoc]

def pointwise_prod (f g : WeightedLanguage α κ) : WeightedLanguage α κ :=
  fun x ↦ f x * g x

def mem_def (f : WeightedLanguage α κ) (xw : List α × κ) : Prop :=
  f xw.1 = xw.2

instance instMem : Membership (List α × κ) (WeightedLanguage α κ) where
  mem := mem_def

def scalar_prodl (w : κ) (f : WeightedLanguage α κ) : WeightedLanguage α κ :=
  fun x ↦ w * f x

def scalar_prodr (f : WeightedLanguage α κ) (w : κ) : WeightedLanguage α κ :=
  fun x ↦ f x * w

def natCast_def : ℕ → WeightedLanguage α κ
  | 0 => 0
  | n + 1 => natCast_def n + 1

instance instNatCast : NatCast (WeightedLanguage α κ) where
  natCast := natCast_def

lemma natCast_def_eq (n : ℕ) :
    (↑ n : WeightedLanguage α κ) = natCast_def n := by rfl

lemma natCast_def_zero : ↑ 0 = (0 : WeightedLanguage α κ) := by simp

lemma natCast_def_succ (n : ℕ) : ↑ ((n + 1) : ℕ) = (((↑ n) + 1) : WeightedLanguage α κ) := by
  simp [natCast_def_eq, add_def_eq, one_def_eq]
  dsimp [natCast_def, add_def_eq, add_def, one_def_eq]

def npow_def (n : ℕ) (f : WeightedLanguage α κ) : WeightedLanguage α κ :=
  match n with
  | 0 => 1
  | n + 1 => npow_def n f * f

lemma npow_def_zero (f : WeightedLanguage α κ) : npow_def 0 f = 1 := by simp [npow_def]

lemma npow_def_succ (n : ℕ) (f : WeightedLanguage α κ) :
    npow_def (n + 1) f = npow_def n f * f := by
  rw (occs := [1]) [npow_def]

def nsmul_def (n : ℕ) (f : WeightedLanguage α κ) :=
  match n with
  | 0 => 0
  | n + 1 => nsmul_def n f + f

lemma nsmul_def_zero (f : WeightedLanguage α κ) : nsmul_def 0 f = 0 := by simp [nsmul_def]

lemma nsmul_def_succ (n : ℕ) (f : WeightedLanguage α κ) :
    nsmul_def (n + 1) f = nsmul_def n f + f := by
  rw (occs := [1]) [nsmul_def]

instance instSemiring : Semiring (WeightedLanguage α κ) where
  add_assoc := add_def_assoc
  zero_add := zero_add_def
  add_zero := add_def_zero
  add_comm := add_def_comm
  left_distrib := mul_def_left_distrib
  right_distrib f g h := by simp [mul_def_right_distrib]
  zero_mul := zero_cauchy_prod
  mul_zero := cauchy_prod_zero
  mul_assoc := mul_def_assoc
  one_mul := one_cauchy_prod
  mul_one := cauchy_prod_one
  nsmul := nsmul_def

end WeightedLanguage
