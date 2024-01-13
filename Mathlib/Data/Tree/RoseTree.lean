/-
Copyright (c) 2019 mathlib community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/

import Mathlib.Data.DList.Defs
import Mathlib.Util.CompileInductive
import Mathlib.Data.FinEnum
import Mathlib.Control.Bitraversable.Instances
import Mathlib.Control.Fold
import Mathlib.Data.Finmap
import Mathlib.Data.Array.Basic
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.List.Indexes
import Mathlib.GroupTheory.GroupAction.Opposite

section ShouldBeMoved

@[reducible, always_inline, inline]
def ReaderM.run {ρ α} (x : ReaderM ρ α) (r : ρ) : α := ReaderT.run x r

@[reducible]
protected def ReaderM.mk {ρ α} (f : ρ → α) : ReaderM ρ α := ReaderT.mk f

example {γ : Type*} : γ → γ × γ := ReaderM.run $ joinM Prod.mk

lemma eq_ite_iff' {α} {P} [Decidable P] {a b c : α} :
    a = (if P then b else c) ↔ (P → a = b) ∧ (¬P → a = c) := by
  refine Iff.trans eq_comm (Iff.trans ite_eq_iff' (Iff.and ?_ ?_))
  <;> exact Iff.imp Iff.rfl eq_comm

theorem SatisfiesM.bind_congr {m α β} [Monad m] [LawfulMonad m] {p : α → Prop}
    {x : m α} (h1 : SatisfiesM p x) {f : α → m β} {g : α → m β}
    (h2 : ∀ (a : α), p a → f a = g a) :
    x >>= f = x >>= g := by
  obtain ⟨y, ⟨⟩⟩ := h1
  rw [seq_bind_eq, seq_bind_eq]
  exact _root_.bind_congr (Subtype.forall.mpr h2)

theorem SatisfiesM.map_congr {m α β} [Monad m] [LawfulMonad m] {p : α → Prop}
    {x : m α} (h1 : SatisfiesM p x) {f : α → β} {g : α → β}
    (h2 : ∀ (a : α), p a → f a = g a) : f <$> x = g <$> x := by
    simp only [map_eq_bind_pure_comp]
    exact h1.bind_congr (congrArg _ $ h2 . .)

lemma fish_eq_backfish' {m α β γ} [Monad m] :
    (fun (p : α → m β) (q : β → m γ) => p >=> q) = (fun p q => q <=< p) := rfl

lemma fish_eq_backfish {m α β γ} [Monad m] (p : α → m β) (q : β → m γ) :
    p >=> q = q <=< p := congrFun (congrFun fish_eq_backfish' p) q

lemma kleisliRight_assoc {m α β γ δ} [Monad m] [LawfulMonad m] (p : α → m β)
    (q : β → m γ) (r : γ → m δ) : p >=> q >=> r = (p >=> q) >=> r :=
  funext $ fun x => Eq.symm (bind_assoc (p x) q r)

-- lemma StateT.SatisfiesM.conjunction.{u}
--     {σ : Type u} {α : Type u} {p q : α → Prop}
--     {x : StateM σ α} :
--     SatisfiesM p x → SatisfiesM q x → SatisfiesM (fun t => p t ∧ q t) x := by
--   simp_rw [SatisfiesM_StateT_eq, SatisfiesM_Id_eq, forall_and,
--            ← and_imp, ← imp_and, imp_self]

-- lemma Part.SatisfiesM.conjunction.{u}
--     {α : Type u} {p q : α → Prop} {x : Part α} :
--     SatisfiesM p x → SatisfiesM q x → SatisfiesM (fun t => p t ∧ q t) x := by
--   rintro ⟨x1, h1⟩ ⟨x2, h2⟩
--   have H  : x.Dom = x1.Dom := (congrArg _ h1).symm
--   have H' : x.Dom = x2.Dom := (congrArg _ h2).symm
--   dsimp only [SatisfiesM]
--   refine ⟨⟨x.Dom, (fun h => ⟨x.get h, ?_, ?_⟩)⟩, rfl⟩
--   . refine Eq.subst ?_ (x1.get (H.mp h)).property; subst h1; rfl
--   . refine Eq.subst ?_ (x2.get (H'.mp h)).property; subst h2; rfl

-- lemma SatisfiesM.conjunction {m α} [Monad m] [LawfulMonad m] {p q : α → Prop}
--     {x : m α} (h1 : SatisfiesM p x) (h2 : SatisfiesM q x) :
--     SatisfiesM (fun t => p t ∧ q t) x := by
--   -- let σ : Type := sorry
--   -- have : ∃ σ, m = StateM σ

--   -- suffices : SatisfiesM (fun y => y.1 = y.2 ∧ p y.1 ∧ q y.2)
--   --                       ((fun (t : α) => (t, t)) <$> x)
--   -- . rw [← show @Prod.fst α α <$> ((fun (t : α) => (t, t)) <$> x) = x from _]
--   --   . refine this.map_post.imp ?_; simp
--   --   . exact Eq.trans (comp_map _ _ _).symm (id_map _)

--   -- obtain ⟨x1, h1⟩ := h1
--   -- obtain ⟨x2, h2⟩ := h2
--   admit

namespace Option

lemma mem_bind {α β} {f : α → Option β} {y : β} {o : Option α} :
    y ∈ Option.bind o f ↔ ∃ x ∈ o, f x = some y := by
  cases o
  <;> simp only [none_bind, some_bind, Option.not_mem_none, false_and,
                 exists_false, Option.mem_some_iff, exists_eq_left']
  exact mem_def

lemma isSome_bind {α β} {f : α → Option β} {o : Option α} :
    (o.bind f).isSome ↔ ∃ x ∈ o, (f x).isSome :=
  Iff.trans isSome_iff_exists
  $ Iff.trans (exists_congr (fun _ => mem_bind))
  $ Iff.trans exists_comm
  $ exists_congr (fun _ =>
      Iff.trans exists_and_left $ and_congr_right' isSome_iff_exists.symm)

def assert {α} (o : Option α) (b : Bool) := o.bind (guard (fun _ => b))
@[simp] lemma assert_true {α} {o : Option α} : o.assert true = o :=
  by cases o <;> rfl
@[simp] lemma assert_false {α} {o : Option α} : o.assert false = none :=
  by cases o <;> rfl

lemma eq_assert_iff {α} {o₁ o₂ : Option α} {b : Bool} :
    o₁ = o₂.assert b ↔ (b = true → o₁ = o₂) ∧ (b = false → o₁ = none) := by
  cases b <;> simp only [assert_true, assert_false,
                         true_implies, false_implies, true_and, and_true]

lemma isSome_guard {α} {p : α → Prop} [DecidablePred p] {a : α} :
    isSome (guard p a) = decide (p a) :=
  Eq.trans (apply_ite _ _ _ _) (congrArg₂ (ite _) isSome_some isSome_none)

lemma guard_bind {α β} (x : α) (f : α → Option β) (p) [DecidablePred p] :
    guard p x >>= f = (f x).assert (p x) := by
  simp only [eq_assert_iff, decide_eq_true_iff, decide_eq_false_iff_not,
             ← ite_prop_iff_and, guard, apply_ite₂ Function.app, Function.app,
             ← ite_apply _ (. >>= f = f x) (. >>= f = none)]
  simp only [bind_eq_bind, Option.bind, ite_self]

lemma guard_const_eq_some_assert {α} (p : Prop) [Decidable p] (a : α) :
    guard (fun _ => p) a = (some a).assert p :=
  Eq.trans (Eq.symm (bind_pure _)) (guard_bind _ _ (fun _ => p))

lemma map'_guard_const {α β} (f : α → β) (p : Prop) [Decidable p] (x : α) :
    Option.map f (guard (fun _ => p) x) = guard (fun _ => p) (f x) :=
  by rename Decidable p => i; dsimp only [guard, ite]; cases i <;> rfl

lemma map_guard_const {α β} (f : α → β) (p : Prop) [Decidable p] (x : α) :
    f <$> guard (fun _ => p) x = guard (fun _ => p) (f x) := map'_guard_const f p x

lemma SatisfiesM_iff_forall_mem {α} {p : α → Prop} {o : Option α} :
    SatisfiesM p o ↔ (∀ x ∈ o, p x) := SatisfiesM_Option_eq

lemma exists_mem_iff_isSome_and_forall_mem {α} {p : α → Prop} {o : Option α} :
    (∃ x ∈ o, p x) ↔ o.isSome ∧ (∀ x ∈ o, p x) :=
  Iff.trans ⟨fun ⟨x, h1, h2⟩ => ⟨⟨x, h1⟩,
                fun _ hy => Eq.subst (Option.mem_unique h1 hy) h2⟩,
             fun ⟨⟨x, h1⟩, h2⟩ => ⟨x, h1, h2 x h1⟩⟩
            (and_congr_left' isSome_iff_exists.symm)

-- this is like Part.ext'
lemma ext' {α} {o₁ o₂ : Option α} (H : o₁.isSome = o₂.isSome)
           (H' : ∀ h₁ h₂, o₁.get h₁ = o₂.get h₂) : o₁ = o₂ :=
  match o₁, o₂, H, H' with
  | some _, some _, .refl true, H' => congrArg _ (H' isSome_some isSome_some)
  | none, none, _, _ => rfl

lemma isSome_of_mem {α} {a} {o : Option α} (h : a ∈ o) : o.isSome :=
  Option.isSome_iff_exists.mpr ⟨a, Option.mem_def.mp h⟩

lemma pmap_guard_eq_dite {α β} {p : α → Prop} {q} [DecidablePred p]
    (f : (a : α) → q → β) (a : α) (H : p a → q) :
    .pmap f (guard p a) (fun _ => H ∘ And.right ∘ Option.guard_eq_some.mp)
    = (if h : p a then some (f a (H h)) else none) :=
  by dsimp only [guard]; split_ifs <;> rfl

lemma isSome_pmap {α β} {p : α → Prop} (f : (a : α) → p a → β) (x : Option α)
    (H : ∀ a ∈ x, p a) : isSome (pmap f x H) = isSome x :=
  match x with | some _ => rfl | none => rfl

end Option

namespace Part

lemma ofOption_pure_hom {α} (x : α) : ofOption (pure x) = pure x := coe_some x
lemma pure_comp_ofOption {α} : ofOption ∘ (@pure _ _ α) = pure :=
  funext ofOption_pure_hom

lemma ofOption_bind_hom {α β} (x : Option α) (f : α → Option β) :
    ofOption (x >>= f) = ofOption x >>= ofOption ∘ f :=
  Part.ext $ fun _ => by
    simp only [Part.mem_ofOption, Option.bind_eq_bind, Option.mem_bind,
               Part.bind_eq_bind, Part.mem_bind_iff, Function.comp_apply]; rfl

lemma ofOption_naturality {α β} (x : Option α) (f : α → β) :
    ofOption (f <$> x) = f <$> ofOption x := by
  simp only [map_eq_bind_pure_comp, ofOption_bind_hom, pure_comp_ofOption,
             ← Function.comp.assoc]

end Part

namespace List
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

lemma take_one (xs : List α) : xs.take 1 = xs.head?.toList :=
  Eq.trans take_succ $ Eq.trans (congrArg (. ++ _) (take_zero _))
  $ Eq.trans (nil_append _) $ congrArg Option.toList (get?_zero _)

lemma mem_zip_iff {xs : List α} {ys : List β} {x y} :
    (x, y) ∈ zip xs ys ↔ (∃ (i : ℕ) (h1 : i < xs.length) (h2 : i < ys.length),
                          xs[i] = x ∧ ys[i] = y) := by
  refine Iff.trans mem_iff_get $ Iff.trans (Fin.exists_iff _) $ exists_congr ?_
  intro i
  simp_rw [length_zip, lt_min_iff, And.exists, List.get_zip, Prod.mk.injEq]
  rfl

lemma isSome_head? : ∀ (xs : List α), xs.head?.isSome ↔ xs ≠ []
  | [] => iff_of_false Bool.false_ne_true (not_not_intro rfl)
  | _::_ => iff_of_true rfl (cons_ne_nil _ _)

theorem head_mem_head? : ∀ {l : List α} (h : l ≠ []), head l h ∈ head? l
  | _ :: _, _ => rfl

lemma ofOption_head?_eq_head (xs : List α) :
    Part.ofOption xs.head? = Part.mk _ xs.head :=
  Eq.trans (Part.ofOption_eq_get _) $ Part.ext' (isSome_head? xs)
  $ fun _ _ => Option.get_of_mem _ (head_mem_head? _)

lemma get_zero' {xs : List α} (h : xs ≠ []) :
    get xs ⟨0, length_pos.mpr h⟩ = head xs h :=
  Option.mem_unique (get_zero _).symm (head_mem_head? h)

lemma getLast_reverse' {xs : List α} (h : xs ≠ []) :
    getLast (reverse xs) (reverse_eq_nil.not.mpr h) = head xs h :=
  Eq.trans (getLast_reverse _) (get_zero' h)

lemma head_reverse {xs : List α} (h : xs ≠ []) :
    head (reverse xs) (reverse_eq_nil.not.mpr h) = getLast xs h :=
  Eq.trans (getLast_reverse' _).symm $ by congr; exact reverse_reverse xs

lemma pmap_reverse {p : α → Prop} (f : (a : α) → p a → β) (l : List α)
    (H : ∀ a ∈ l, p a) :
    pmap f (reverse l) (H . $ mem_reverse.mp .) = reverse (pmap f l H) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [reverse_cons, pmap, pmap_append, reverse_append]
    exact congrArg (. ++ _) (ih (H . ∘ mem_cons_of_mem _))

lemma head?_SatisfiesM_eq_cons_tail (xs : List α) :
    SatisfiesM (xs = . :: xs.tail) xs.head? :=
  Option.SatisfiesM_iff_forall_mem.mpr (fun _ h => eq_cons_of_mem_head? h)

def uncons? (xs : List α) := xs.head?.map (., xs.tail)
@[simp] lemma uncons?_cons (x : α) (xs : List α) :
    uncons? (x :: xs) = some (x, xs) := rfl
@[simp] lemma uncons?_nil : uncons? ([] : List α) = none := rfl
lemma mem_uncons?_iff (p : α × List α) (xs : List α) :
    p ∈ xs.uncons? ↔ p.fst :: p.snd = xs := by
  cases xs <;> simp only [uncons?_nil, uncons?_cons,
                          Option.not_mem_none, Option.mem_some_iff]
  refine Iff.trans eq_comm $ Iff.trans Prod.ext_iff $ Iff.symm $ iff_of_eq ?_
  apply cons.injEq
lemma cons_uncons? (xs : List α) :
    Function.uncurry cons <$> xs.uncons?
    = Option.guard (List.isEmpty . = false) xs :=
  by cases xs <;> rfl

lemma cons_uncons?_SatisfiesM (xs : List α) :
    SatisfiesM (Function.uncurry cons . = xs) xs.uncons? :=
  ((head?_SatisfiesM_eq_cons_tail xs).imp Eq.symm).map_pre

lemma pair_foldr_eq_foldr_zip {α₁ α₂ β₁ β₂} {l₁ l₂} (H : l₁.length = l₂.length)
    (op₁ : α₁ → β₁ → β₁) (op₂ : α₂ → β₂ → β₂) (b₁ : β₁) (b₂ : β₂) :
    (foldr op₁ b₁ l₁, foldr op₂ b₂ l₂)
    = foldr (fun p q => (op₁ p.1 q.1, op₂ p.2 q.2)) (b₁, b₂) (zip l₁ l₂) :=
  match l₁, l₂ with
  | [], [] => rfl
  | x::_, y::_ =>
    -- `fun p q => (op₁ p.1 q.1, op₂ p.2 q.2)`
    -- `= Function.uncurry Prod.map ∘ Prod.map op₁ op₂`
    show (Function.uncurry Prod.map ∘ Prod.map op₁ op₂) (x, y) (_, _) = _
    from congrArg _ (pair_foldr_eq_foldr_zip (Nat.succ.inj H) op₁ op₂ b₁ b₂)

lemma pair_foldl_eq_foldl_zip {α₁ α₂ β₁ β₂} {l₁ l₂} (H : l₁.length = l₂.length)
    (op₁ : β₁ → α₁ → β₁) (op₂ : β₂ → α₂ → β₂) (b₁ : β₁) (b₂ : β₂) :
    (foldl op₁ b₁ l₁, foldl op₂ b₂ l₂)
    = foldl (fun p q => (op₁ p.1 q.1, op₂ p.2 q.2)) (b₁, b₂) (zip l₁ l₂) := by
  repeat rw [← foldr_reverse]
  simp only [pair_foldr_eq_foldr_zip, zip, zipWith_distrib_reverse, H, length_reverse]

lemma zip_self_eq_map_dup (xs : List α) : zip xs xs = map (fun t => (t, t)) xs :=
  Eq.trans (congrArg₂ zip (map_id _).symm (map_id _).symm) (zip_map' id id _)

lemma prod_mk_foldr (f : α → β → β) (g : α → γ → γ) (b0 : β) (c0 : γ) (as : List α) :
    (as.foldr f b0, as.foldr g c0)
    = as.foldr (fun a => Prod.map (f a) (g a)) (b0, c0) :=
  Eq.trans (pair_foldr_eq_foldr_zip rfl _ _ _ _)
  $ Eq.trans (congrArg _ (zip_self_eq_map_dup _)) (foldr_map _ _ _ _)

lemma prod_mk_foldl (f : β → α → β) (g : γ → α → γ) (b0 : β) (c0 : γ) (as : List α) :
    (as.foldl f b0, as.foldl g c0)
    = as.foldl (fun p a => Prod.map (f . a) (g . a) p) (b0, c0) :=
  by rw [← foldr_reverse, ← foldr_reverse, prod_mk_foldr, foldr_reverse]

def foldrRecOn₂ {α₁ α₂ β₁ β₂} {C : β₁ → β₂ → Sort*} {l₁ l₂}
    (H : l₁.length = l₂.length) (op₁ : α₁ → β₁ → β₁) (op₂ : α₂ → β₂ → β₂)
    (b₁ : β₁) (b₂ : β₂) (hb : C b₁ b₂)
    (hl : ∀ b₁ b₂, C b₁ b₂ → ∀ a₁ a₂, (a₁, a₂) ∈ zip l₁ l₂
                           → C (op₁ a₁ b₁) (op₂ a₂ b₂)) :
    C (foldr op₁ b₁ l₁) (foldr op₂ b₂ l₂) :=
  (congrArg (Function.uncurry C) (pair_foldr_eq_foldr_zip H op₁ op₂ b₁ b₂)).mpr
  $ foldrRecOn _ _ _ hb $ fun b₁₂ hb a₁₂ ha => hl b₁₂.1 b₁₂.2 hb a₁₂.1 a₁₂.2 ha

def foldlRecOn₂ {α₁ α₂ β₁ β₂} {C : β₁ → β₂ → Sort*} {l₁ l₂}
    (H : l₁.length = l₂.length) (op₁ : β₁ → α₁ → β₁) (op₂ : β₂ → α₂ → β₂)
    (b₁ : β₁) (b₂ : β₂) (hb : C b₁ b₂)
    (hl : ∀ b₁ b₂, C b₁ b₂ → ∀ a₁ a₂, (a₁, a₂) ∈ zip l₁ l₂
                           → C (op₁ b₁ a₁) (op₂ b₂ a₂)) :
    C (foldl op₁ b₁ l₁) (foldl op₂ b₂ l₂) :=
  (congrArg (Function.uncurry C) (pair_foldl_eq_foldl_zip H op₁ op₂ b₁ b₂)).mpr
  $ foldlRecOn _ _ _ hb $ fun b₁₂ hb a₁₂ ha => hl b₁₂.1 b₁₂.2 hb a₁₂.1 a₁₂.2 ha

def foldrRecDiag {α β₁ β₂} {C : β₁ → β₂ → Sort*} {xs}
    (op₁ : α → β₁ → β₁) (op₂ : α → β₂ → β₂) (b₁ : β₁) (b₂ : β₂) (hb : C b₁ b₂)
    (hl : ∀ b₁ b₂, C b₁ b₂ → ∀ a, a ∈ xs → C (op₁ a b₁) (op₂ a b₂)) :
    C (foldr op₁ b₁ xs) (foldr op₂ b₂ xs) := by
  refine foldrRecOn₂ rfl op₁ op₂ b₁ b₂ hb $ fun y₁ y₂ h1 x₁ x₂ h2 => ?_
  refine cast ?_ (hl y₁ y₂ h1 x₁ ?_) <;>
  have h3 := (exists_congr (fun _ => and_congr_right' Prod.ext_iff)).mp
             $ mem_map.mp ((congrArg (_ ∈ .) (zip_self_eq_map_dup xs)).mp h2)
  . refine congrArg (C (op₁ x₁ y₁) $ op₂ . y₂) ?_
    have h4 := exists_eq_left.mp $ h3.imp $ fun _ => And.right; exact h4
  . exact (exists_eq_left (p := (. ∈ xs))).mp $ h3.imp $ fun _ =>
            and_comm.mp ∘ And.imp_right And.left

def foldlRecDiag {α β₁ β₂} {C : β₁ → β₂ → Sort*} {xs}
    (op₁ : β₁ → α → β₁) (op₂ : β₂ → α → β₂) (b₁ : β₁) (b₂ : β₂) (hb : C b₁ b₂)
    (hl : ∀ b₁ b₂, C b₁ b₂ → ∀ a ∈ xs, C (op₁ b₁ a) (op₂ b₂ a)) :
    C (foldl op₁ b₁ xs) (foldl op₂ b₂ xs) := by
  refine foldlRecOn₂ rfl op₁ op₂ b₁ b₂ hb $ fun y₁ y₂ h1 x₁ x₂ h2 => ?_
  refine cast ?_ (hl y₁ y₂ h1 x₁ ?_) <;>
  have h3 := (exists_congr (fun _ => and_congr_right' Prod.ext_iff)).mp
             $ mem_map.mp ((congrArg (_ ∈ .) (zip_self_eq_map_dup xs)).mp h2)
  . refine congrArg (C (op₁ y₁ x₁) $ op₂ y₂ .) ?_
    have h4 := exists_eq_left.mp $ h3.imp $ fun _ => And.right; exact h4
  . exact (exists_eq_left (p := (. ∈ xs))).mp $ h3.imp $ fun _ =>
            and_comm.mp ∘ And.imp_right And.left

lemma foldr_mul_act [Monoid α] [MulAction α β] (b : β) (xs : List α) :
    foldr (. * .) 1 xs • b = foldr (. • .) b xs :=
  Eq.trans (Eq.symm $ foldr_hom (. • b) _ _ _ _ (Eq.symm $ mul_smul . . b))
  $ congrArg (foldr _ . _) (one_smul α b)

section
open scoped RightActions

lemma foldl_mul_act [Monoid α] [MulAction αᵐᵒᵖ β] (b : β) (xs : List α) :
    foldr (. * .) 1 xs • b = foldr (. • .) b xs :=
  Eq.trans (Eq.symm $ foldr_hom (. • b) _ _ _ _ (Eq.symm $ mul_smul . . b))
  $ congrArg (foldr _ . _) (one_smul α b)

end

lemma foldr_eq_foldr_comp_map (f : α → β → β) (b : β) (xs : List α) :
    foldr f b xs = foldr (fun s t => s ∘ t) id (map f xs) b :=
  let app (g : β → β) := g b
  Eq.trans (foldr_hom app _ _ _ id (fun _ _ => rfl))
  $ congrArg app (foldr_map _ _ _ _).symm

lemma foldl_eq_foldl_comp_map (f : β → α → β) (b : β) (xs : List α) :
    foldl f b xs = foldl (fun s t => t ∘ s) id (map (fun x y => f y x) xs) b :=
  by rw [← foldr_reverse, ← foldr_reverse, reverse_map, foldr_eq_foldr_comp_map]

/-
(β → β) → (β → α) → (β → α)

foldr (. ∘ .) i [a, b, c]
= a ∘ (b ∘ (c ∘ i))

i : α → β
a, b, c : β → β
-/

lemma foldr_comp_apply (xs : List (β → β)) (f : α → β) (a : α) :
    foldr (fun s t => s ∘ t) f xs a = foldr id (f a) xs := by

  admit
  -- sorry

lemma foldrM_eq_foldr_kleisli_comp_map {m} [Monad m] [LawfulMonad m]
    (f : α → β → m β) (b : β) (xs : List α) :
    xs.foldrM f b = foldr (. <=< .) pure (map f xs) b := by
  rw [foldrM_eq_foldr, foldr_eq_foldr_comp_map]
  refine Eq.trans (congrArg (foldr _ id . _) (map_map (. =<< .) f xs).symm) ?_
  refine Eq.trans (congrFun (foldr_map _ _ _ _) _) (Eq.symm ?_)
  exact congrFun (foldr_hom (. ∘ pure) _ _ _ id (fun _ _ => rfl)) b

lemma foldlM_eq_foldl_kleisli_comp_map {m} [Monad m] [LawfulMonad m]
    (f : β → α → m β) (b : β) (xs : List α) :
    xs.foldlM f b = foldl (. >=> .) pure (map (fun x y => f y x) xs) b := by
  rw [foldlM_eq_foldl, ← foldr_reverse, ← foldr_reverse, reverse_map,
      ← foldrM_eq_foldr, foldrM_eq_foldr_kleisli_comp_map]; rfl

lemma foldrM_homM {m n} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    (f : ∀ {a}, m a → n a) (g₁ : α → β → m β) (g₂ : α → β → n β) (l : List α)
    (init : β) (h1 : ∀ {a} (x : a), f (pure x) = pure x)
    (h2 : ∀ {a b} (x : m a) (y : a → m b), f (x >>= y) = f x >>= (f ∘ y))
    -- equivalent to `f y >>= g₂ x = f (y >>= g₁ x)` under h2
    -- which makes it look more like the condition in foldr_hom
    (H : ∀ x y, f y >>= g₂ x = f y >>= (f ∘ g₁ x)) :
    l.foldrM g₂ init = f (l.foldrM g₁ init) := by
  rw [foldrM_eq_foldr, foldrM_eq_foldr]; conv_lhs => left; exact (h1 init).symm
  exact foldr_hom _ _ _ _ _ (fun _ _ => Eq.trans (H _ _) (Eq.symm (h2 _ _)))

lemma foldlM_homM {m n} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    (f : ∀ {a}, m a → n a) (g₁ : β → α → m β) (g₂ : β → α → n β) (l : List α)
    (init : β) (h1 : ∀ {a} (x : a), f (pure x) = pure x)
    (h2 : ∀ {a b} (x : m a) (y : a → m b), f (x >>= y) = f x >>= (f ∘ y))
    -- equivalent to `f y >>= g₂ x = f (y >>= g₁ x)` under h2
    -- which makes it look more like the condition in foldr_hom
    (H : ∀ x y, f y >>= (g₂ . x) = f y >>= (f ∘ (g₁ . x))) :
    l.foldlM g₂ init = f (l.foldlM g₁ init) := by
  rw [foldlM_eq_foldl, foldlM_eq_foldl]; conv_lhs => left; exact (h1 init).symm
  exact foldl_hom _ _ _ _ _ (fun _ _ => Eq.trans (H _ _) (Eq.symm (h2 _ _)))

lemma foldr_pmap_eq_foldr_attach {α β γ} {p : α → Prop} (f : (a : α) → p a → β)
    (xs : List α) (H : ∀ a ∈ xs, p a) (g : β → γ → γ) (init : γ) :
    (xs.pmap f H).foldr g init
    = xs.attach.foldr (fun x c => g (f x.val (H _ x.property)) c) init :=
  by rw [List.pmap_eq_map_attach _ _ H, foldr_map]

lemma foldl_pmap_eq_foldl_attach {α β γ} {p : α → Prop} (f : (a : α) → p a → β)
    (xs : List α) (H : ∀ a ∈ xs, p a) (g : γ → β → γ) (init : γ) :
    (xs.pmap f H).foldl g init
    = xs.attach.foldl (fun c x => g c (f x.val (H _ x.property))) init :=
  by rw [List.pmap_eq_map_attach _ _ H, foldl_map]

lemma foldr_pmap_mem_foldrM_Part {α β γ} {p : α → Prop} (f : (a : α) → p a → β)
    (xs : List α) (H : ∀ a ∈ xs, p a) (g : β → γ → γ) (init : γ) :
    (xs.pmap f H).foldr g init
    ∈ xs.foldrM (fun a c => Part.mk (p a) (fun h => g (f a h) c)) init := by
  conv_rhs => rw [← attach_map_val xs]
  rw [foldr_pmap_eq_foldr_attach, foldrM_eq_foldr, foldr_map]
  apply foldrRecOn₂
  . rfl
  . exact Part.mem_some _
  . intro b p hb a1 a2 ha
    refine Part.mem_bind_iff.mpr ⟨b, hb, H _ a2.property, ?_⟩
    obtain ⟨i, _, _, ⟨⟩, ⟨⟩⟩ := mem_zip_iff.mp ha; rfl

lemma foldl_pmap_mem_foldlM_Part {α β γ} {p : α → Prop} (f : (a : α) → p a → β)
    (xs : List α) (H : ∀ a ∈ xs, p a) (g : γ → β → γ) (init : γ) :
    (xs.pmap f H).foldl g init
    ∈ xs.foldlM (fun c a => Part.mk (p a) (fun h => g c (f a h))) init := by
  rw [← foldr_reverse, ← foldrM_reverse, ← pmap_reverse]
  exact foldr_pmap_mem_foldrM_Part f _ _ (fun x y => g y x) init

lemma foldr_pmap_mem_foldrM_Option {α β γ} {p : α → Prop} [DecidablePred p]
    (f : (a : α) → p a → β) (xs : List α) (H : ∀ a ∈ xs, p a) (g : β → γ → γ)
    (init : γ) :
    (xs.pmap f H).foldr g init
    ∈ xs.foldrM (fun a c => (Option.guard p a).pmap (fun _ h => g (f a h) c)
                              (fun _ => And.right ∘ Option.guard_eq_some.mp))
                init := by
  refine Part.mem_ofOption.mp ?_
  refine Eq.subst ?_ (foldr_pmap_mem_foldrM_Part f xs H g init)
  apply foldrM_homM
  . exact Part.ofOption_pure_hom
  . exact Part.ofOption_bind_hom
  . intro x _
    refine _root_.bind_congr ?_
    intro
    dsimp only [Function.comp_apply]
    refine Part.ext' ?_ ?_
    . simp only [Part.ofOption_dom, Option.isSome_pmap, Option.isSome_guard]
      exact (decide_eq_true_iff _).symm
    . intro (h1 : p x) _
      simp only [Option.pmap_guard_eq_dite _ _ id, h1, dite_true,
                 Part.coe_some, Part.get_some]

lemma foldl_pmap_mem_foldlM_Option {α β γ} {p : α → Prop} [DecidablePred p]
    (f : (a : α) → p a → β) (xs : List α) (H : ∀ a ∈ xs, p a) (g : γ → β → γ)
    (init : γ) :
    (xs.pmap f H).foldl g init
    ∈ xs.foldlM (fun c a => (Option.guard p a).pmap (fun _ h => g c (f a h))
                              (fun _ => And.right ∘ Option.guard_eq_some.mp))
                init := by
  rw [← foldr_reverse, ← foldrM_reverse, ← pmap_reverse]
  exact foldr_pmap_mem_foldrM_Option f _ _ (fun x y => g y x) init

lemma foldr_telescope {α β γ δ ε ζ} (p : α → γ) (q : α → δ) (r : α → ε)
    (g₁ : γ → ζ → β) (g₂ : δ → ζ → ζ) (g₃ : ε → β → ζ) (b : β) (xs : List α)
    (h1 : Pairwise (fun w z => ∀ t, g₃ (r w) (g₁ (p z) t) = t) xs) (h2 : xs ≠ [])
    : xs.foldr (fun x y => g₁ (p x) (g₂ (q x) (g₃ (r x) y))) b
      = g₁ (p (xs.head h2)) (xs.foldr (g₂ ∘ q) (g₃ (r (xs.getLast h2)) b)) :=
  match xs, h1 with
  | [_], _ => rfl
  | _ :: x :: xs, .cons H₁ H₂ =>
    have H₃ := foldr_telescope p q r g₁ g₂ g₃ b _ H₂ (cons_ne_nil x xs)
    congrArg (g₁ (p _) ∘ g₂ (q _))
    $ Eq.trans (congrArg (g₃ (r _)) H₃) (H₁ _ (head_mem _) _)

lemma foldl_telescope {α β γ δ ε ζ} (p : α → γ) (q : α → δ) (r : α → ε)
    (g₁ : β → γ → ζ) (g₂ : ζ → δ → ζ) (g₃ : ζ → ε → β) (b : β) (xs : List α)
    (h1 : Pairwise (fun w z => ∀ t, g₁ (g₃ t (r w)) (p z) = t) xs) (h2 : xs ≠ [])
    : xs.foldl (fun x y => g₃ (g₂ (g₁ x (p y)) (q y)) (r y)) b
      = g₃ (xs.foldl (g₂ . $ q .) (g₁ b (p (xs.head h2)))) (r (xs.getLast h2)) := by
  rw [← foldr_reverse, ← foldr_reverse, ← head_reverse, ← getLast_reverse' h2]
  exact foldr_telescope r q p (flip g₃) (flip g₂) (flip g₁) b _
                        (pairwise_reverse.mpr h1) (reverse_eq_nil.not.mpr h2)

lemma foldr_telescope' {α β γ δ ε ζ} (p : γ) (q : α → δ) (r : ε)
    (g₁ : γ → ζ → β) (g₂ : δ → ζ → ζ) (g₃ : ε → β → ζ) (b : β) (xs : List α)
    (h1 : ∀ t, g₃ r (g₁ p t) = t) (h2 : xs ≠ [])
    : xs.foldr (fun x y => g₁ p (g₂ (q x) (g₃ r y))) b
      = g₁ p (xs.foldr (g₂ ∘ q) (g₃ r b)) :=
  have h3 := pairwise_of_forall_mem_list $ fun _ _ _ _ => h1
  foldr_telescope (fun _ => p) q (fun _ => r) g₁ g₂ g₃ b xs h3 h2

lemma foldl_telescope' {α β γ δ ε ζ} (p : γ) (q : α → δ) (r : ε)
    (g₁ : β → γ → ζ) (g₂ : ζ → δ → ζ) (g₃ : ζ → ε → β) (b : β) (xs : List α)
    (h1 : ∀ t, g₁ (g₃ t r) p = t) (h2 : xs ≠ [])
    : xs.foldl (fun x y => g₃ (g₂ (g₁ x p) (q y)) r) b
      = g₃ (xs.foldl (g₂ . $ q .) (g₁ b p)) r :=
  have h3 := pairwise_of_forall_mem_list $ fun _ _ _ _ => h1
  foldl_telescope (fun _ => p) q (fun _ => r) g₁ g₂ g₃ b xs h3 h2

-- `Function.uncurry cons : α × List α → List α`
-- `uncons? : List α →. α × List α`
lemma scanr_mem_foldrM {α β} (f : α → β → β) (b : β) (xs : List α) :
    scanr f b xs ∈ foldrM (fun x ys => ys.head?.map (f x . :: ys)) [b] xs := by
  let F : β × List β → List β := Function.uncurry cons
  let G := (fun a (x : _ × _) => (f a x.1, x.1 :: x.2))
  have H₁ {x ys} a (h : F a = ys) := congrArg (F $ Prod.mk (f x a.1) .) h.symm
  conv =>
    enter [2, 1, x, ys]
    rw [← Eq.trans (ys.head?.map_map Prod.fst (., _)) ys.head?.map_id'', Option.map_map]
    refine Eq.trans (ys.cons_uncons?_SatisfiesM.map_congr H₁) ?_
    refine Eq.trans (ys.uncons?.map_map F (G x)).symm ?_
    simp only [← Option.map_eq_map, ← pure_bind ys uncons?,
               map_eq_bind_pure_comp]
  rw [foldrM_eq_foldr_kleisli_comp_map, foldr_map]
  conv in _ <=< _ =>
    change y >=> (((pure >=> uncons?) >=> pure ∘ G x) >=> pure ∘ F)
    rw [fish_pipe, ← fish_assoc, ← fish_assoc]
    change pure ∘ F <=< pure ∘ G x <=< uncons? <=< y
  by_cases h' : xs = []
  . subst h'; rfl
  . rw [foldr_telescope _ _ _ (. <=< .) (. <=< .) (. <=< .)]
    . rw [← fish_eq_backfish pure, fish_pipe, ← fish_pure uncons?, fish_eq_backfish]
      conv_rhs => exact bind_pure_comp F (foldr (pure ∘ G . <=< .) _ xs [b])
      rw [← foldr_map]


      -- conv in (_ <=< _) => intro; exact bind_pure_comp (G _) _
      -- refine Eq.mp (congrArg (_ ∈ F <$> . [b])
      --               $ (foldr_map (G . <$> .) (fun x y => x ∘ y) xs uncons?)) ?_

      -- rw [← foldr_eq_foldr_comp_map]

      -- rw [← foldr_map G (fun x (y : _ → Option _) => (x <$> .) ∘ y) xs uncons?]

        -- exact funext
        -- rfl
      admit
    . refine pairwise_of_forall_mem_list ?_; intros
      rw [← fish_eq_backfish, ← fish_eq_backfish, fish_assoc]
      refine Eq.trans (congrArg (_ >=> .) ?_) (fish_pure _)
      funext (a, _); exact Eq.trans (pure_bind _ _) (uncons?_cons a _)
    . assumption
    -- change List.foldlM id pure
                  -- [Sigma.mk (List β, List β) uncons?, pure ∘ G x, pure ∘ F] y

    -- rw [fish_assoc, ← fish_assoc]



  -- fish_eq_backfish'

  -- change _ ∈ foldr (fun x y => (pure ∘ Function.uncurry cons <=< (pure ∘ G x
  --                     <=< (uncons? <=< pure))) <=< y) pure xs [b]

  -- this is actually a defeq and we could include it in the above but that would be sneaky
  -- rw []

    -- exact Eq.trans (kleisliLeft_assoc _ uncons? y).symm
    --                (kleisliLeft_assoc (pure ∘ F) (pure ∘ G x) _).symm


  -- change _ ∈ Function.app (foldr (fun a g => ((pure ∘ F <=< pure ∘ G a) <=< _) <=< g) _ _) _

  -- rw [← Function.app.eq (foldr _ _ _) (F (b, []))]
  -- change _ ∈ Function.app (foldr _ pure _) (F (b, []))
  -- conv_rhs =>


  --   rfl
  -- rw [← fun x y => kleisliLeft_assoc (pure ∘ F) (pure ∘ G x) _]

  have H₂ x (y : List β → Option _) :=
    Eq.trans (kleisliLeft_assoc (pure ∘ F) (pure ∘ G x) _)
             (kleisliLeft_assoc _ uncons? y)
  have H₃ := funext (funext $ H₂ .)
  refine Eq.mp (congrArg (_ ∈ foldr . pure xs _) H₃) ?_

        -- congrFun (congrFun (congrFun ?_ _) _) _
  -- conv_rhs =>
  --   rfl

    -- change Function.app (foldr _ _ _) _


  -- change foldr (. <=< .) id (map ((pure ∘ F <=< pure ∘ . <=< U) ∘ G) _) _ = _
  -- rw [← map_map, foldr_map]




  -- refine Eq.trans (congrFun (congrArg _ (map_map _ G _).symm) _) ?_

  -- conv => enter [1, 1, a]; change Bind.bindLeft (U >=> (pure ∘ G a) >=> (pure ∘ F))


    -- tactic =>
    -- refine (?_ : _ = (mb >>= U) >>= pure ∘ G a >>= pure ∘ F)
    -- refine Eq.trans (Eq.symm (_root_.map_bind _)) ?_



  -- simp_rw [← Option.map_eq_map]


  -- refine Eq.trans ?_ (Eq.trans (uncons?_cons _ _) (congrArg _ (Prod.eta _)))

    -- refine Option.ext ?_
    -- intro ys'
    -- simp_rw [Option.map_eq_map, Option.mem_map, mem_uncons?_iff, Option.mem_def,
    --          Option.guard_eq_some, Prod.exists, Function.uncurry_apply_pair]

    -- -- simp only [Function.uncurry_apply_pair, ne_eq]
    -- admit

  -- refine @Eq.trans _ _ (foldrM (fun x ys => Option.map (fun p => f x p.1 :: p.1 :: p.2) (uncons? ys)) [b] xs) _ ?_ ?_
  -- . simp only [uncons?, Option.map_map]
  --   congr; funext x ys; cases ys <;> dsimp
  -- . admit
  -- change foldrM (fun x ys => Option.map (_ ∘ _) (head? ys)) [b] xs = _
  -- rw [← Part.mem_coe,
  --     ← foldrM_homM @Part.ofOption _ (fun x ys => ⟨_, (. :: ys) ∘ f x ∘ ys.head⟩)]
  -- . dsimp only [scanr]

  --   admit
  -- . exact Part.ofOption_pure_hom
  -- . exact Part.ofOption_bind_hom
  -- . refine fun _ _ => _root_.bind_congr (fun _ => Eq.symm ?_)
  --   exact Eq.trans (Part.ofOption_naturality _ _)
  --         $ congrArg (_ <$> .) (ofOption_head?_eq_head _)

lemma scanr_eq_foldr {α β} (f : α → β → β) (b : β) (xs : List α) :
    scanr f b xs = foldr (fun x ys => f x (ys.headD b) :: ys) [b] xs := by
  conv =>
    enter [2, 1, x, ys]; rw [headD_eq_head?, ← Option.getD_map (f x . :: ys)]
  refine Option.mem_unique (scanr_mem_foldrM _ _ _) ?_



  -- change _ = foldr (fun x ys => Option.getD (Option.map (fun x_1 ↦ f x x_1 :: ys) (head? ys)) (f x b :: ys)) [b] xs


  -- simp only [headD_eq_head?, ← Option.getD_map (f _ . :: _)]

  admit
  -- let o := foldrM (fun a bs => Part.mk _ ((. :: bs) ∘ f a ∘ bs.head)) [b] xs
  -- <;> dsimp only [scanr, o]
  -- .
  --   change Function.uncurry cons _ ∈ _

  --   admit
  -- .

  --   admit
  -- refine Eq.trans ?_ (foldr_eq_foldr_with_loop_inv (. ≠ []) _ _ _ ?_ ?_).symm
  -- any_goals intros; exact cons_ne_nil _ _

  -- let F : β × List β → { l : List β // l ≠ [] } :=
  --   Subtype.coind (Function.uncurry cons) (fun _ => cons_ne_nil _ _)
  -- refine congrArg Subtype.val (?_ : F _ = _)


  -- lhs is producing `β × List β`, rhs is producing `List β`
  -- have function `Function.uncurry cons : β × List β → List β`

lemma scanr_eq_foldr' {α β} (f : α → β → β) (b : β) (xs : List α) :
    scanr f b xs = foldr (fun x ys => f x (ys.headD b) :: ys) [b] xs := by
  refine Option.some.inj $ Eq.symm $ Eq.trans ?_ $ scanr_mem_foldrM f b xs
  rw [foldrM_eq_foldr, ← foldr_hom some _ (fun x ys? => ys? >>= (fun ys =>
          f x (headD ys b) :: ys)) _ _ (fun _ _ => Option.some_bind _ _)]
  let C (x : Option (List β) × Option (List β)) :=
    SatisfiesM (. ≠ []) x.snd ∧ x.fst = x.snd
  refine And.right $ @Eq.substr _ C _ _ (prod_mk_foldr _ _ _ _ _) ?_
  apply foldrRecOn
  . refine ⟨?_, rfl⟩
    refine Option.SatisfiesM_iff_forall_mem.mpr (fun _ h => ?_)
    exact ne_of_eq_of_ne (Option.mem_some_iff.mp h).symm (cons_ne_nil b _)
  . rintro ⟨o, _⟩ ⟨h, ⟨⟩⟩ a _
    refine ⟨?_, Eq.symm ?_⟩
    . exact .bind h (fun _ _ => .map_pre (.of_true (fun _ => cons_ne_nil _ _)))
    . refine SatisfiesM.bind_congr (SatisfiesM.imp h ?_)
               (fun _ H => Eq.trans (congrArg _ H).symm (Option.map_some' _ _))
      intro _ H
      rw [headD_eq_head?, head?_eq_head _ H, Option.getD_of_ne_none]
      exact Option.some_ne_none _

-- lemma scanl_as_range_forM {α β} (f : α → β → α) (a : α) (xs : List β) :
--     scanl f a xs = StateT.run

-- lemma get?_scanl {α β} (f : α → β → α) (a : α) (xs : List β) (i : ℕ) :
--     get? (scanl f a xs) i = .guard (fun _ => i < xs.length + 1)
--       (Prod.snd $ Id.run $ StateT.run ([1:2].forM _) a)
--       -- ().assert (i < xs.length + 1)
--       := sorry

lemma scanl_succ_eq_range'_length {α} (s : ℕ) (xs : List α) :
    scanl (fun k _ => k + 1) s xs = range' s (xs.length + 1) := by
  refine ext_get (Eq.trans (length_scanl _ _) (length_range' _ _ _).symm) ?_
  intro i h1 h2
  rw [get_range', Nat.one_mul]; clear h2
  induction' i with i ih
  . simp only [Nat.zero_eq, get_zero_scanl, add_zero]
  . simp only [get_succ_scanl, Nat.succ_eq_add_one, ← Nat.add_assoc]
    exact congrArg (. + 1) (ih (lt_trans (Nat.lt_succ_self _) h1))

end List

namespace Array
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w} {m : Type v → Type w}
         [Monad m] [LawfulMonad m]

lemma getElem?_map (f : α → β) (a : Array α) (i : ℕ) :
    (a.map f)[i]? = a[i]?.map f := by
  have H := congrArg (i < .) (size_map f a)
  refine Eq.trans ?_ (apply_dite _ _ _ _).symm
  exact dite_congr H (congrArg some ∘' a.getElem_map f i ∘' H.mpr) (fun _ => rfl)

theorem mapIdx_eq_ofFn (a : Array α) (f : Fin a.size → α → β) :
    a.mapIdx f = Array.ofFn (fun i => f i a[i]) :=
  Array.ext _ _ (Eq.trans (Array.size_mapIdx _ _) (Array.size_ofFn _).symm)
  $ fun i h1 h2 =>
    Eq.trans (Array.getElem_mapIdx _ _ i h1) (Array.getElem_ofFn _ i h2).symm

theorem map_eq_mapIdx (a : Array α) (f : α → β) :
    a.map f = a.mapIdx (fun _ x => f x) :=
  Array.ext _ _ (Eq.trans (Array.size_map _ _) (Array.size_mapIdx _ _).symm)
  $ fun i h1 h2 =>
    Eq.trans (Array.getElem_map _ _ i h1) (Array.getElem_mapIdx _ _ i h2).symm

lemma map_eq_ofFn (a : Array α) (f : α → β) :
    a.map f = Array.ofFn (fun (i : Fin a.size) => f a[i]) :=
  Eq.trans (map_eq_mapIdx _ _) (mapIdx_eq_ofFn a _)

lemma isEmpty_iff {a : Array α} : a.isEmpty ↔ a = Array.empty where
  mp h := Array.ext _ _ ((decide_eq_true_iff _).mp h)
                        (fun _ _ h' => absurd h' (Nat.not_lt_zero _))
  mpr h := h ▸ decide_eq_true List.length_nil

lemma push_eq_append_singleton (a : Array α) (x : α) :
    Array.push a x = a ++ Array.singleton x :=
  Array.ext' $ Eq.trans (Array.push_data a x) $ Eq.symm (Array.append_data _ _)

lemma isSome_getElem? (a : Array α) (i : ℕ) : a[i]?.isSome ↔ i < a.size :=
  Iff.trans (Bool.eq_iff_iff.mp (apply_dite _ _ _ _)) (decide_eq_true_iff _)

-- def extractAlt (as : Array α) (start stop : ℕ) :=
--   (StateT.run ([start:stop].forM (m := StateT (Array α) Option)
--               $ fun i => do _root_.modify (Array.push . (← as[i]?)))
--               (mkEmpty (min stop as.size - start))).map Prod.snd

lemma extract_data (as : Array α) (start stop : ℕ) :
    (as.extract start stop).data = (as.data.drop start).take (stop - start) := by
  dsimp only [extract, Nat.sub_eq, mkEmpty_eq]
  generalize H : min stop (size as) - start = len
  refine @Eq.trans _ _ (#[].data ++ (as.data.drop start).take len) _ ?_ ?_
  . clear H; generalize #[] = acc
    induction' len with l ih generalizing start acc
    . rw [extract.loop, dite_eq_ite, ite_self, List.take_zero, List.append_nil]
    . refine Eq.trans (apply_dite Array.data _ _ _) ?_
      conv_lhs => congr
                  . intro; rw [ih, push_data, List.append_assoc]
                  . intro; exact (List.append_nil _).symm
      refine Eq.trans (apply_dite (acc.data ++ .) _ _ _).symm ?_
      refine congrArg (acc.data ++ .) (dite_eq_iff'.mpr ⟨?_, ?_⟩)
        <;> intro h <;> refine Eq.symm ?_
      . rw [Nat.succ_eq_one_add, List.take_add, List.take_one,
            ← List.drop_add, Nat.add_comm 1, List.drop_eq_get_cons h]
        rfl
      . exact List.take_eq_nil_of_eq_nil $ List.drop_eq_nil_of_le (not_lt.mp h)
  . refine Eq.trans (List.nil_append _) (List.take_eq_take.mpr ?_)
    simp only [List.length_drop, ← H, Nat.sub_min_sub_right, min_assoc, min_self]

lemma size_extract (as : Array α) (start stop : ℕ) :
    Array.size (as.extract start stop) = min stop as.size - start := by
  rw [size, extract_data, List.length_take, List.length_drop, Nat.sub_min_sub_right]

lemma extract_isEmpty_of_stop_le_start (as : Array α) (start stop : ℕ)
    (H : stop ≤ start) : (as.extract start stop).isEmpty :=
  decide_eq_true $ Eq.trans (size_extract _ _ _)
  $ Nat.sub_eq_zero_of_le $ min_le_of_left_le H

lemma extract_eq_extract_upto_min (as : Array α) (start stop : ℕ) :
    as.extract start stop = as.extract start (min stop as.size) :=
  congrArg (extract.loop as . start #[]) $ congrArg (. - start)
  $ Eq.symm $ Eq.trans (min_assoc _ _ _) $ congrArg (min stop) $ Nat.min_self _

lemma extract_isEmpty_of_size_le_start (as : Array α) (start stop : ℕ)
    (H : as.size ≤ start) : (as.extract start stop).isEmpty :=
  Eq.trans (congrArg _ (extract_eq_extract_upto_min _ _ _))
  $ extract_isEmpty_of_stop_le_start _ _ _ $ min_le_of_right_le H

lemma extract_getElem? (as : Array α) (start stop i : ℕ) :
    (as.extract start stop)[i]? = as[start + i]?.assert (start + i < stop) := by
  refine Eq.trans ?_ (congrArg _ (Bool.decide_congr lt_tsub_iff_left))
  simp only [Array.getElem?_eq_data_get?, extract_data, Option.eq_assert_iff,
             decide_eq_true_iff, decide_eq_false_iff_not, not_lt]
  exact ⟨(Eq.trans . (List.get?_drop _ _ _)) ∘ List.get?_take,
        List.get?_eq_none.mpr ∘ le_of_eq_of_le (List.length_take _ _)
                              ∘ min_le_of_left_le⟩

lemma extract_get? (as : Array α) (start stop i : ℕ) :
    (as.extract start stop).get? i
    = (as.get? (start + i)).assert (start + i < stop) :=
  extract_getElem? as start stop i

lemma extract_get (as : Array α) (start stop i : ℕ)
    (h1 : i < (extract as start stop).size)
    (h2 : start + i < as.size := lt_of_lt_of_le
            (lt_tsub_iff_left.mp $ lt_of_lt_of_eq h1 $ size_extract _ _ _)
            (min_le_right _ _)) :
    (as.extract start stop).get ⟨i, h1⟩ = as.get ⟨start + i, h2⟩ := by
  refine Option.some.inj (Eq.symm ?_)
  simp only [Array.get_eq_getElem, ← Array.getElem?_eq_getElem,
             extract_getElem?, Option.eq_assert_iff, implies_true, true_and,
             decide_eq_false_iff_not, ← lt_tsub_iff_left]
  refine absurd $ lt_of_lt_of_le h1 $ le_of_eq_of_le (size_extract _ _ _) ?_
  exact Nat.sub_le_sub_right (min_le_left _ _) _

lemma extract_getElem (as : Array α) (start stop i : ℕ)
    (h1 : i < (extract as start stop).size)
    (h2 : start + i < as.size := lt_of_lt_of_le
            (lt_tsub_iff_left.mp $ lt_of_lt_of_eq h1 $ size_extract _ _ _)
            (min_le_right _ _)) :
    (as.extract start stop)[i] = as[start + i] := extract_get _ _ _ _ _

lemma foldlM_eq_foldlM_upto_min (f : β → α → m β) (init : β) (as : Array α)
    (start stop : ℕ) :
    as.foldlM f init start stop  = as.foldlM f init start (min stop as.size) := by
  simp only [foldlM, min_le_right, dite_true, dite_eq_iff']
  refine ⟨?_, ?_ ∘ le_of_not_le⟩ <;> intro h <;> congr <;> refine Eq.symm ?_
  <;> simp only [min_eq_left_iff, min_eq_right_iff, h]

lemma foldl_eq_foldl_upto_min (f : β → α → β) (init : β) (as : Array α)
    (start stop : ℕ) :
    as.foldl f init start stop  = as.foldl f init start (min stop as.size) :=
  foldlM_eq_foldlM_upto_min (m:=Id) f init as start stop

lemma foldlM_eq_pure_init_of_stop_le_start (f : β → α → m β) (init : β)
    (as : Array α) (start stop : ℕ) (H : stop ≤ start) :
    as.foldlM f init start stop = pure init := by
  dsimp only [foldlM]; simp (config:={singlePass:=true}) only [foldlM.loop]
  simp only [not_lt.mpr H, dite_false, apply_dite (. = pure init),
             dite_prop_iff_and, implies_true, true_and, and_true]
  intro h h'; exfalso; exact h (le_trans H (le_of_lt h'))

lemma foldl_eq_init_of_stop_le_start (f : β → α → β) (init : β)
    (as : Array α) (start stop : ℕ) (H : stop ≤ start) :
    as.foldl f init start stop = init :=
  foldlM_eq_pure_init_of_stop_le_start (m:=Id) f init as start stop H

lemma foldlM_eq_foldlM_extract (f : β → α → m β) (init : β) (as : Array α)
    (start stop : ℕ) :
    as.foldlM f init start stop = (as.extract start stop).foldlM f init := by
  rw [foldlM_eq_foldlM_data, extract_data, foldlM_eq_foldlM_upto_min]
  generalize h1 : min stop (size as) = stop'
  suffices : foldlM f init as start stop'
           = List.foldlM f init ((as.data.drop start).take (stop' - start))
  . refine Eq.trans this $ congrArg _ $ List.take_eq_take.mpr ?_
    simp only [List.length_drop, ← h1, Nat.sub_min_sub_right, min_assoc, min_self]
  replace h1 := le_of_eq_of_le h1.symm (min_le_right _ _); clear stop
  cases' Nat.le_total start stop' with h2 h2
  . generalize H : stop' - start = w
    replace H := Nat.eq_add_of_sub_eq h2 H; clear h2; subst H
    simp only [foldlM, h1, le_refl, dite_true, Nat.sub_zero, Nat.add_sub_cancel]
    induction' w with w ih generalizing start init
    . rw [List.take_zero, List.foldlM_nil, foldlM.loop]
      simp only [Nat.zero_add, lt_irrefl, dite_false]
    . have := lt_of_lt_of_le (Nat.lt_succ_self start) (Nat.le_add_left _ w)
      rw [foldlM.loop]
      simp only [Nat.succ_add_eq_succ_add] at h1 ⊢
      replace ih b := ih b (Nat.succ start) h1
      simp only [ih, this, dite_true, List.take_succ_cons, List.foldlM_cons,
                 List.drop_eq_get_cons (lt_of_lt_of_le this h1)]
      rfl
  . rw [Nat.sub_eq_zero_of_le h2, List.take_zero, List.foldlM_nil]
    exact foldlM_eq_pure_init_of_stop_le_start _ _ _ _ _ h2

lemma foldl_eq_foldl_extract (f : β → α → β) (init : β) (as : Array α)
    (start stop : ℕ) :
    as.foldl f init start stop = (as.extract start stop).foldl f init :=
  foldlM_eq_foldlM_extract (m:=Id) f init as start stop

/-
theorem foldl_induction'
    {as : Array α} (motive : Nat → β → Prop) {init : β} (start stop : ℕ)
    (h0 : motive start init)
    (h0' : min stop (size as) < start → motive (min stop (size as)) init)
    {f : β → α → β}
    (hf : ∀ i : Fin as.size, ∀ b, motive i.1 b → motive (i.1 + 1) (f b as[i])) :
    motive (min stop (size as)) (as.foldl f init start (min stop (size as))) := by
  generalize H : min stop (size as) = stop' at h0 h0' ⊢
  replace H := le_of_eq_of_le H.symm (min_le_right _ _); clear stop
  by_cases H' : stop' < start
  . rw [foldl_eq_init_of_stop_le_start _ _ _ _ _ (le_of_lt H')]
    exact h0' H'
  . rw [not_lt] at H'
    rw [foldl_eq_foldl_extract]
    conv => left; exact Eq.symm (Nat.add_sub_cancel' H')
    have := Eq.symm (Eq.trans (size_extract _ _ _)
                              (congrArg (. - start) (min_eq_left H)))
    convert @foldl_induction α β (as.extract start stop') (motive $ start + .) _ h0 f ?_
    intro ⟨i, hi⟩ b h
    rw [← Nat.add_assoc, getElem_fin, extract_getElem]
    refine hf ⟨_, ?_⟩ b h
    exact lt_of_lt_of_le (lt_tsub_iff_left.mp $ lt_of_lt_of_eq hi this.symm) H
-/

theorem foldl_induction'
    {as : Array α} (motive : Nat → β → Prop) {init : β} (start stop : ℕ)
    (h0 : motive start init) (h0' : stop < start → motive stop init)
    (h1 : stop ≤ as.size) {f : β → α → β}
    -- (h1 : as.size < stop → motive as.size (foldl f init as start)
    --                      → motive stop (foldl f init as start))
    (hf : ∀ i : Fin as.size, ∀ b, start ≤ i → i < stop
                                  → motive i.1 b → motive (i.1 + 1) (f b as[i])) :
    motive stop (as.foldl f init start stop) := by
  by_cases H : stop < start
  . exact (foldl_eq_init_of_stop_le_start _ _ _ _ _ (le_of_lt H)).substr (h0' H)
  rw [not_lt] at H
  rw [foldl_eq_foldl_extract]
  conv => left; exact Eq.symm (Nat.add_sub_cancel' H)
  have := Eq.symm (Eq.trans (size_extract _ _ _)
                            (congrArg (. - start) (min_eq_left h1)))

  convert @foldl_induction α β (as.extract start stop) (motive $ start + .) _ h0 f ?_
  intro ⟨i, hi⟩ b h
  rw [← Nat.add_assoc, getElem_fin, extract_getElem]
  have H := lt_tsub_iff_left.mp $ lt_of_lt_of_eq hi this.symm
  exact hf ⟨_, lt_of_lt_of_le H h1⟩ b (Nat.le_add_right _ _) H h

lemma foldlM_eq_foldl (f : β → α → m β) (init : β) (as : Array α)
    (start : ℕ := 0) (stop : ℕ := as.size) :
    as.foldlM f init start stop
    = as.foldl (fun mb a => do f (← mb) a) (pure init) start stop := by
  simp (config:={singlePass:=true}) only [foldl, foldlM_eq_foldlM_extract]
  simp only [foldlM_eq_foldlM_data, List.foldlM_eq_foldl]
  rfl

lemma prod_mk_foldl (f : β → α → β) (g : γ → α → γ) (b0 : β) (c0 : γ)
    (as : Array α) (start stop : ℕ) :
    (as.foldl f b0 start stop, as.foldl g c0 start stop)
    = as.foldl (fun p a => Prod.map (f . a) (g . a) p) (b0, c0) start stop := by
  simp (config:={singlePass:=true}) only [foldl_eq_foldl_extract]
  simp only [foldl_eq_foldl_data, List.prod_mk_foldl]

lemma foldrM_reverse (as : Array α) (f : α → β → m β) (b : β) :
    as.reverse.foldrM f b = as.foldlM (fun x y => f y x) b :=
  Eq.trans (foldrM_eq_reverse_foldlM_data _ _ _)
  $ Eq.trans (congrArg _ (List.reverse_eq_iff.mpr (reverse_data _)))
  $ (foldlM_eq_foldlM_data _ _ _).symm

lemma foldr_reverse (as : Array α) (f : α → β → β) (b : β) :
    as.reverse.foldr f b = as.foldl (fun x y => f y x) b :=
  foldrM_reverse (m := Id) as f b

@[inline]
unsafe def foldlIdxMUnsafe (f : ℕ → β → α → m β) (init : β) (as : Array α)
    (start := 0) (stop := as.size) : m β :=
  let rec @[specialize] fold (i : USize) (stop : USize) (b : β) : m β := do
    if i == stop then
      pure b
    else
      fold (i+1) stop (← f (USize.toNat i) b (as.uget i lcProof))
  if start < stop then
    if stop ≤ as.size then
      fold (USize.ofNat start) (USize.ofNat stop) init
    else
      pure init
  else
    pure init

@[implemented_by foldlIdxMUnsafe]
def foldlIdxM (f : ℕ → β → α → m β) (init : β) (as : Array α)
    (start := 0) (stop := as.size) : m β :=
  let fold (stop : Nat) (h : stop ≤ as.size) :=
    let rec loop (i : Nat) (j : Nat) (b : β) : m β := do
      if hlt : j < stop then
        match i with
        | 0    => pure b
        | i'+1 =>
          have : j < as.size := Nat.lt_of_lt_of_le hlt h
          loop i' (j+1) (← f j b as[j])
      else
        pure b
    loop (stop - start) start init
  if h : stop ≤ as.size then
    fold stop h
  else
    fold as.size (Nat.le_refl _)

@[reducible] def foldlIdx (f : ℕ → β → α → β) (init : β) (as : Array α)
    (start := 0) (stop := as.size) := Id.run $ foldlIdxM f init as start stop

lemma foldlIdxM_eq_foldlIdxM_upto_min (f : ℕ → β → α → m β) (b : β)
    (as : Array α) (i0 i1 : ℕ) :
    as.foldlIdxM f b i0 i1  = as.foldlIdxM f b i0 (min i1 as.size) := by
  simp only [foldlIdxM, min_le_right, dite_true, dite_eq_iff']
  refine ⟨?_, ?_ ∘ le_of_not_le⟩ <;> intro h <;> congr <;> refine Eq.symm ?_
  <;> simp only [min_eq_left_iff, min_eq_right_iff, h]

lemma foldlIdxM_eq_foldlM (f : ℕ → β → α → m β) (init : β) (as : Array α)
    (start stop : ℕ) :
    as.foldlIdxM f init start stop
    = Prod.snd <$>
      as.foldlM (fun p a => Prod.mk (p.fst + 1) <$> Function.uncurry f p a)
                (start, init) start stop := by
  rw [foldlM_eq_foldlM_upto_min, foldlIdxM_eq_foldlIdxM_upto_min]
  generalize h1 : min stop (size as) = stop'
  replace h1 := le_of_eq_of_le h1.symm (min_le_right _ _); clear stop
  -- simp only [foldlIdxM, min_le_right, dite_true]
  simp only [foldlIdxM, foldlM, Id.run, h1, le_refl, dite_true]
  cases' Nat.le_total start stop' with h2 h2
  . generalize H : stop' - start = w
    replace H := Nat.eq_add_of_sub_eq h2 H; clear h2; subst H
    induction' w with w ih generalizing start init
    . simp only [Nat.zero_add, foldlM.loop, foldlIdxM.loop, lt_irrefl,
                 dite_false, map_pure, Id.pure_eq]
    . have H := lt_of_lt_of_le (Nat.lt_succ_self start) (Nat.le_add_left _ w)
      rw [foldlM.loop, foldlIdxM.loop]
      simp only [Nat.succ_add_eq_succ_add] at h1 ⊢
      simp only [H, dite_true, ih, h1, map_bind, seq_bind_eq,
                 Function.uncurry_apply_pair, Function.comp_apply]
  . rw [Nat.sub_eq_zero_of_le h2, foldlIdxM.loop, foldlM.loop]
    simp only [not_lt.mpr h2, dite_false, map_pure]

lemma foldlIdx_eq_foldl (f : ℕ → β → α → β) (init : β) (as : Array α)
    (start stop : ℕ) :
    as.foldlIdx f init start stop
    = (as.foldl (fun p a => (p.fst + 1, f p.fst p.snd a))
                (start, init) start stop).snd :=
  foldlIdxM_eq_foldlM (m := Id) f init as start stop

lemma foldlIdxM_eq_foldl (f : ℕ → β → α → m β) (init : β) (as : Array α)
    (start stop : ℕ) :
    as.foldlIdxM f init start stop
    = (as.foldl (fun p a => (p.fst + 1, p.snd >>= (f p.fst . a)))
                (start, pure init) start stop).snd := by
  refine Eq.trans (foldlIdxM_eq_foldlM f init as start stop) ?_
  -- morally Function.uncurry (Functor.map ∘ Prod.mk) is sequence
  have (x : ℕ × m β) :=
    Eq.trans (congrArg (Prod.snd <$> .)
            $ congrFun (Function.uncurry_def (Functor.map ∘ Prod.mk)) x)
    $ Eq.trans (comp_map _ _ _).symm (id_map _)
  refine Eq.trans (congrArg (Prod.snd <$> .) ?_) (this _); clear this
  rw [foldlM_eq_foldlM_extract, foldlM_eq_foldl, ← foldl_eq_foldl_extract, ← map_pure]
  let C (x : m (ℕ × β) × (ℕ × m β)) :=
    x.fst = Function.uncurry (Functor.map ∘ Prod.mk) x.snd
  refine @Eq.substr _ C _ _ (Array.prod_mk_foldl _ _ _ _ _ _ _) ?_
  rw [foldl_eq_foldl_upto_min]
  apply foldl_induction' (fun _ => C)
  . rfl
  . intro; rfl
  . exact min_le_right _ _
  . intro i ⟨x, y, z⟩ _ _ H
    dsimp only [C, Function.uncurry_apply_pair, Prod.map_mk, Function.comp_apply] at H ⊢
    rw [H, map_bind, seq_bind_eq]
    rfl

lemma foldlIdx_eq_foldlIdx_data (f : ℕ → β → α → β) (init : β)
    (as : Array α) (start stop : ℕ) :
    as.foldlIdx f init start stop
    = ((as.data.take stop).drop start).foldlIdx f init start := by
  rw [List.foldlIdx_eq_foldlIdxSpec, List.foldlIdxSpec, foldlIdx_eq_foldl]
  cases' le_total stop start with h h
  . rw [foldl_eq_init_of_stop_le_start _ _ _ _ _ h,
        List.drop_eq_nil_of_le, List.enumFrom_nil, List.foldl_nil]
    exact le_of_eq_of_le (List.length_take _ _) (min_le_of_left_le h)
  . rw [foldl_eq_foldl_extract, foldl_eq_foldl_data, extract_data,
        ← as.data.drop_take, Nat.add_sub_cancel', List.enumFrom_eq_zip_range',
        -- ← List.zipWith_foldl_eq_zip_foldl init (f := Prod.mk) (g := fun a p => f p.fst a p.snd)

        ]

    -- . change (List.foldl (fun b p => f p.fst b p.snd) init _).snd = _

    -- f p.1 p.2 a on lhs
    -- f p.1 a p.2 on rhs


-- lemma foldlIdxM_eq_foldlIdxM_extract (f : ℕ → β → α → m β) (init : β)
--     (as : Array α) (start stop : ℕ) :
--     as.foldlIdxM f init start stop
--     = (as.extract start stop).foldlIdxM (f $ start + .) init := by
--   simp_rw [foldlIdxM_eq_foldl]
--   rw [foldl_eq_foldl_extract, foldl_eq_foldl_data, foldl_eq_foldl_data]


  -- conv => congr <;> enter [1,1,p,a]
  --         . change p.map (. + 1) _

  --           rfl
  --         .

  --           rfl

  -- rw [← foldl_eq_foldl_extract]
  -- generalize @pure m _ _ init = init'

  -- ℕ × m β
  -- have := @List.foldl_hom (ℕ × m β) ℕ α Prod.s

  -- rw [List.foldl_hom, eq_comm, List.foldl_hom]

  -- conv => enter [1, 1, 2, 1]; exact (Nat.add_zero start).symm
  -- generalize 0 = i

  admit

end Array

namespace Sum

lemma exists_isLeft {α β} {P : α ⊕ β → Prop} :
    (∃ x, x.isLeft ∧ P x) ↔ (∃ a, P (Sum.inl a)) :=
  Iff.trans (exists_congr $ fun _ =>
    Iff.trans (and_congr_left' isLeft_iff) exists_and_right.symm)
  $ Iff.trans exists_swap $ exists_congr $ fun _ => exists_eq_left

lemma exists_isRight {α β} {P : α ⊕ β → Prop} :
    (∃ x, x.isRight ∧ P x) ↔ (∃ a, P (Sum.inr a)) :=
  Iff.trans (exists_congr $ fun _ =>
    Iff.trans (and_congr_left' isRight_iff) exists_and_right.symm)
  $ Iff.trans exists_swap (exists_congr (fun _ => exists_eq_left))

end Sum

end ShouldBeMoved

/-!
# Rose tree

A tree with an arbitrary (finite) number of children at each node,
storing (potentially) different types of data at the nodes and leaves.
-/

inductive RoseTree.{u, v} (N : Type u) (L : Type v) : Type (max u v)
  | leaf : L → RoseTree N L
  | branch : N → Array (RoseTree N L) → RoseTree N L
  deriving Repr

compile_inductive% RoseTree

namespace RoseTree

universe u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃
variable {N : Type u₁} {N' : Type u₂} {N'' : Type u₃}
         {L : Type v₁} {L' : Type v₂} {L'' : Type v₃}
         {ω : Type w₁}

def children : RoseTree N L → Array (RoseTree N L)
  | leaf _ => Array.empty
  | branch _ ts => ts

lemma leaf_inj_iff {x y : L} : @leaf N L x = @leaf N L y ↔ x = y :=
  iff_of_eq (leaf.injEq x y)

lemma branch_inj_iff {x} {ts : Array (RoseTree N L)} {y ts'} :
    branch x ts = branch y ts' ↔ x = y ∧ ts = ts' :=
  iff_of_eq (branch.injEq _ _ _ _)

lemma leaf_ne_branch {x : L} {y : N} {ts} : leaf x ≠ branch y ts :=
  RoseTree.noConfusion (P:=False)

lemma branch_ne_leaf {y : N} {ts} {x : L} : branch y ts ≠ leaf x :=
  Ne.symm leaf_ne_branch

section getElim
variable {motive : RoseTree N L → Sort w₁}
         (leaf : (x : L) → motive (leaf x))
         (branch : (y : N) → (ts : Array (RoseTree N L))
                 → ((i : Fin ts.size) → motive ts[i]) → motive (branch y ts))

@[eliminator]
def getElim : (t : RoseTree N L) → motive t
  | RoseTree.leaf x => leaf x
  | RoseTree.branch y ts => branch y ts (fun i => getElim ts[i])

lemma getElim_leaf {x} : getElim leaf branch (RoseTree.leaf x) = leaf x := rfl
lemma getElim_branch {y ts} :
    getElim leaf branch (RoseTree.branch y ts)
    = branch y ts (fun i => getElim leaf branch ts[i]) :=
  by rw [getElim]

end getElim

instance [DecidableEq N] [DecidableEq L] : DecidableEq (RoseTree N L) := by
  intro t₁ t₂
  induction t₁ generalizing t₂ with
  | leaf x =>
    match t₂ with
    | leaf x' => exact decidable_of_iff (x = x') leaf_inj_iff.symm
    | branch _ _ => exact Decidable.isFalse leaf_ne_branch
  | branch y ts ih =>
    match t₂ with
    | leaf _ => exact Decidable.isFalse branch_ne_leaf
    | branch y' ts' =>
      -- putting the y = y' inside the ∃ h means we check ts.size = ts'.size,
      -- which is roughly O(1), before y = y' (arbitrarily expensive)
      refine decidable_of_iff (∃ h, y = y' ∧ ∀ i, ts.get i = ts'.get (i.cast h))
                              (Iff.trans ?_ branch_inj_iff.symm)
      refine Iff.trans exists_and_left (and_congr_right' ?_)
      refine ⟨?_, (. ▸ ⟨rfl, fun _ => rfl⟩)⟩
      rintro ⟨h, h'⟩
      exact Array.ext _ _ h (fun i hi _ => h' ⟨i, hi⟩)

-- it might make more sense to use `Subarray`,
-- but because `Subarray.forIn` is opaque we can't prove anything about it
abbrev Addr := Array ℕ

def bimap (f : N → N') (g : L → L') (t : RoseTree N L) : RoseTree N' L' := by
  induction t with
  | leaf x => exact leaf (g x)
  | branch y ts self => exact branch (f y) (Array.ofFn self)

@[simp] lemma bimap_leaf {f : N → N'} {g : L → L'} {x} :
    bimap f g (leaf x) = leaf (g x) := getElim_leaf _ _

@[simp] lemma bimap_branch {f : N → N'} {g : L → L'} {y ts} :
    bimap f g (branch y ts) = branch (f y) (ts.map (bimap f g)) :=
  Eq.trans (getElim_branch _ _) $ congrArg (branch (f y)) $ ts.map_eq_ofFn _

section getNodeAt?

def getNodeData : RoseTree N L → N ⊕ L
  | leaf x => Sum.inr x
  | branch y _ => Sum.inl y

def getSubtreeAt? (t : RoseTree N L) (a : Addr) : Option (RoseTree N L) :=
  a.foldlM (fun t i => t.children[i]?) t

@[reducible] def applyAt (f : RoseTree N L → ω) (p : Addr) (t : RoseTree N L) : Option ω :=
  Option.map f (getSubtreeAt? t p)

@[reducible] def getNodeAt? (t : RoseTree N L) (p : Addr) :=
  applyAt getNodeData p t

@[reducible] def getLeafAt? (t : RoseTree N L) (p : Addr) :=
  Option.bind (getNodeAt? t p) Sum.getRight?

@[reducible] def getInnerNodeAt? (t : RoseTree N L) (p : Addr) :=
  Option.bind (getNodeAt? t p) Sum.getLeft?

@[simp] lemma getSubtreeAt?_empty {t : RoseTree N L} :
    t.getSubtreeAt? Array.empty = some t :=
  Eq.trans (Array.foldlM_eq_foldlM_data _ _ _) (List.foldlM_nil _ _)

-- i would like this to be lower priority than getSubtreeAt?_empty
@[simp] lemma getSubtreeAt?_leaf {x a} :
    getSubtreeAt? (@leaf N L x) a = (Option.guard (fun _ => a.isEmpty) (leaf x)) :=
  eq_ite_iff'.mpr
    ⟨fun h => Eq.trans (congrArg _ (Array.isEmpty_iff.mp h)) getSubtreeAt?_empty,
    fun h => have h' := List.ne_nil_of_length_pos $ Nat.pos_of_ne_zero
                        $ of_decide_eq_false ((Bool.not_eq_true _).mp h)
             Eq.trans (Array.foldlM_eq_foldlM_data _ _ _)
             $ Eq.trans (congrArg _ (List.cons_head!_tail h').symm)
             $ Eq.trans (List.foldlM_cons _ _ _ _) (Option.none_bind _)⟩

@[simp] lemma getSubtreeAt?_singleton {t : RoseTree N L} {i : ℕ} :
    getSubtreeAt? t (Array.singleton i) = t.children[i]? :=
  Eq.trans (Array.foldlM_eq_foldlM_data _ _ _)
  $ Eq.trans (congrArg (List.foldlM _ _ $ Array.data .) (Array.singleton_def i))
  $ Eq.trans (congrArg _ (List.toArray_data _))
  $ Eq.trans (List.foldlM_cons _ _ _ _)
  $ Eq.trans (congrArg _ (funext (List.foldlM_nil _))) $ Eq.trans (bind_pure _)
  $ match t with | leaf _ => rfl | branch _ _ => rfl

lemma getSubtreeAt?_append {t : RoseTree N L} {a₁ a₂ : Addr} :
    t.getSubtreeAt? (a₁ ++ a₂) = (getSubtreeAt? t a₁).bind (getSubtreeAt? . a₂) := by
  simp only [getSubtreeAt?, Array.foldlM_eq_foldlM_data, Array.append_data]
  exact List.foldlM_append _ _ _ _

lemma getSubtreeAt?_cons {t : RoseTree N L} {i : ℕ} {a : Addr} :
    getSubtreeAt? t (Array.singleton i ++ a)
    = t.children[i]?.bind (getSubtreeAt? . a) :=
  Eq.trans getSubtreeAt?_append (congrArg (Option.bind . _) getSubtreeAt?_singleton)

@[simp] lemma getNodeAt?_empty {t : RoseTree N L} :
    t.getNodeAt? Array.empty = getNodeData t :=
  Eq.trans (congrArg (Option.map _) getSubtreeAt?_empty) (Option.map_some' _ _)

@[simp] lemma getNodeAt?_leaf {x a} :
    getNodeAt? (@leaf N L x) a = (Option.guard (fun _ => a.isEmpty) $ Sum.inr x) :=
  Eq.trans (congrArg (Option.map _) getSubtreeAt?_leaf)
           (Option.map'_guard_const _ _ _)

@[simp] lemma getNodeAt?_singleton {t : RoseTree N L} {i : ℕ} :
    getNodeAt? t (Array.singleton i) = t.children[i]?.map getNodeData :=
  congrArg (Option.map _) getSubtreeAt?_singleton

lemma getNodeAt?_getSubtreeAt? (t : RoseTree N L) (p q : Addr) :
    (t.getSubtreeAt? p).bind (getNodeAt? . q) = t.getNodeAt? (p ++ q) :=
  Eq.symm $ Eq.trans (congrArg (Option.map _) getSubtreeAt?_append)
                     (Option.map_bind' _ _ _)

lemma getNodeAt?_cons {t : RoseTree N L} {i : ℕ} {a : Addr} :
    getNodeAt? t (Array.singleton i ++ a)
    = t.children[i]?.bind (getNodeAt? . a) :=
  Eq.trans (congrArg (Option.map _) getSubtreeAt?_cons) (Option.map_bind' _ _ _)

section predicates

variable (t : RoseTree N L) (p : Addr)

def hasNodeAt := ∃ n, n ∈ getNodeAt? t p
def hasLeafAt := ∃ b, Sum.inr b ∈ getNodeAt? t p
def hasInnerNodeAt := ∃ a, Sum.inl a ∈ getNodeAt? t p

lemma hasNodeAt_of_hasLeafAt : hasLeafAt t p → hasNodeAt t p
  | ⟨x, h⟩ => ⟨Sum.inr x, h⟩

lemma hasNodeAt_of_hasInnerNodeAt : hasInnerNodeAt t p → hasNodeAt t p
  | ⟨x, h⟩ => ⟨Sum.inl x, h⟩

lemma hasNodeAt_iff_getNodeAt?_isSome : hasNodeAt t p ↔ (getNodeAt? t p).isSome :=
  Option.isSome_iff_exists.symm

lemma hasNodeAt_iff_getSubtreeAt?_isSome : hasNodeAt t p ↔ (getSubtreeAt? t p).isSome :=
  Iff.trans (hasNodeAt_iff_getNodeAt?_isSome _ _) (Bool.eq_iff_iff.mp Option.isSome_map)

lemma hasLeafAt_iff_getLeafNodeAt?_isSome :
    hasLeafAt t p ↔ (getLeafAt? t p).isSome :=
  Iff.symm
  $ Iff.trans Option.isSome_bind
  $ Iff.trans (exists_congr (fun _ =>
      Iff.trans (and_congr_right' Sum.isSome_getRight?_iff_isRight) and_comm))
    Sum.exists_isRight

lemma hasInnerNodeAt_iff_getInnerNodeAt?_isSome :
    hasInnerNodeAt t p ↔ (getInnerNodeAt? t p).isSome :=
  Iff.symm
  $ Iff.trans Option.isSome_bind
  $ Iff.trans (exists_congr (fun _ =>
      Iff.trans (and_congr_right' Sum.isSome_getLeft?_iff_isLeft) and_comm))
    Sum.exists_isLeft

def getSubtreeAt {t : RoseTree N L} {p} (h : hasNodeAt t p) : RoseTree N L :=
  Option.get (getSubtreeAt? t p)
  $ Iff.mp (hasNodeAt_iff_getSubtreeAt?_isSome _ _) h

def getNodeAt {t : RoseTree N L} {p} (h : hasNodeAt t p) : N ⊕ L :=
  Option.get (getNodeAt? t p)
  $ Iff.mp (hasNodeAt_iff_getNodeAt?_isSome _ _) h

def getLeafAt {t : RoseTree N L} {p} (h : hasLeafAt t p) : L :=
  Option.get (getLeafAt? t p)
  $ Iff.mp (hasLeafAt_iff_getLeafNodeAt?_isSome _ _) h

def getInnerNodeAt {t : RoseTree N L} {p} (h : hasInnerNodeAt t p) : N :=
  Option.get (getInnerNodeAt? t p)
  $ Iff.mp (hasInnerNodeAt_iff_getInnerNodeAt?_isSome _ _) h

instance : Decidable (hasNodeAt t p) :=
  decidable_of_bool _ (hasNodeAt_iff_getNodeAt?_isSome t p).symm
instance : Decidable (hasLeafAt t p) :=
  decidable_of_bool _ (hasLeafAt_iff_getLeafNodeAt?_isSome t p).symm
instance : Decidable (hasInnerNodeAt t p) :=
  decidable_of_bool _ (hasInnerNodeAt_iff_getInnerNodeAt?_isSome t p).symm

lemma hasNodeAt_empty {t : RoseTree N L} : hasNodeAt t Array.empty :=
  (hasNodeAt_iff_getSubtreeAt?_isSome _ _).mpr
  $ Eq.trans (congrArg _ getSubtreeAt?_empty) Option.isSome_some

lemma hasNodeAt_leaf {x p} : hasNodeAt (@leaf N L x) p ↔ p.isEmpty :=
  by rw [hasNodeAt_iff_getSubtreeAt?_isSome, getSubtreeAt?_leaf,
         Option.isSome_guard, decide_eq_true_iff]

lemma hasNodeAt_push {t : RoseTree N L} {p i} :
    hasNodeAt t (p.push i)
    ↔ hasInnerNodeAt t p ∧ SatisfiesM (fun t => i < t.children.size)
                                      (getSubtreeAt? t p) := by
  simp only [hasNodeAt_iff_getSubtreeAt?_isSome, Array.push_eq_append_singleton,
             getSubtreeAt?_append, Option.isSome_bind, getSubtreeAt?_singleton,
             Array.isSome_getElem?, hasInnerNodeAt_iff_getInnerNodeAt?_isSome,
             Option.mem_map, exists_exists_and_eq_and]
  conv_rhs =>
    simp only [Option.SatisfiesM_iff_forall_mem, ← forall_and,
               Option.exists_mem_iff_isSome_and_forall_mem, and_assoc]
    rw [← Option.exists_mem_iff_isSome_and_forall_mem]
  refine exists_congr (fun t => and_congr_right (fun ht => ?_))
  rw [Sum.isSome_getLeft?_iff_isLeft, iff_and_self]
  match t with
  | leaf _ => exact Not.elim (Nat.not_lt_zero _)
  | branch _ ts => intro; rfl

end predicates

-- there's probably a clever way to do this if we inductively prove
-- equality of Option (RoseTree N L), but Lean can't automatically prove that
-- `t.bind (fun x => x.children[i]?)` is below `t`
lemma getNodeAt?_faithful ⦃t₁ t₂ : RoseTree N L⦄
    (h : ∀ p, t₁.getNodeAt? p = t₂.getNodeAt? p) : t₁ = t₂ :=
  have h1 := Option.some.inj (h Array.empty)
  have h2 : t₁.children.size = t₂.children.size := by
    have h' i := Bool.eq_iff_iff.mp $ congrArg Option.isSome (h (Array.singleton i))
    simp only [getNodeAt?_singleton, Option.isSome_map, Array.isSome_getElem?] at h'
    exact eq_of_forall_lt_iff h'
  match t₁, t₂ with
  | leaf _, leaf _ => congrArg leaf (Sum.inr.inj h1)
  | branch _ ts₁, branch _ ts₂ =>
    congrArg₂ branch (Sum.inl.inj h1)
    $ Array.ext _ _ h2 $ fun i hi₁ hi₂ => getNodeAt?_faithful $ fun a =>
      have h' := Eq.trans getNodeAt?_cons.symm
                $ Eq.trans (h (Array.singleton i ++ a)) getNodeAt?_cons
      by simp only [children, Array.getElem?_eq_getElem, hi₁, hi₂,
                    Option.some_bind] at h'; exact h'

lemma children_bimap {f : N → N'} {g : L → L'} :
    ∀ (t : RoseTree N L), (t.bimap f g).children = t.children.map (.bimap f g)
  | leaf _ => congrArg children bimap_leaf
  | branch _ _ => congrArg children bimap_branch

lemma getSubtreeAt?_bimap {f : N → N'} {g : L → L'} (t : RoseTree N L) (p : Addr) :
    (t.bimap f g).getSubtreeAt? p = (t.getSubtreeAt? p).map (.bimap f g) := by
  simp only [getSubtreeAt?, Array.foldlM_eq_foldlM_data, List.foldlM_eq_foldl]
  let C := fun x => Prod.fst x = Option.map (RoseTree.bimap f g) (Prod.snd x)
  refine @Eq.substr _ C _ _ (p.data.prod_mk_foldl _ _ _ _) $
         p.data.foldlRecOn _ _ (Option.map_some' _ _).symm $
    fun
    | (none, none), _, _, _ => (Option.map_none' _).symm
    | (some t₁, some t₂), H, i, _ =>
      Eq.trans (congrArg₂ (. >>= .) H rfl) (?_ : (t₂.bimap f g).children[i]? = _)
  exact Eq.trans (congrArg (.[i]?) (children_bimap t₂)) (Array.getElem?_map _ _ _)

-- `getNodeAt?` is a natural transformation `RoseTree → Function.bicompr Option Sum`
lemma getNodeAt?_bimap {f : N → N'} {g : L → L'} (t : RoseTree N L) (p : Addr) :
    (t.bimap f g).getNodeAt? p = (t.getNodeAt? p).map (Sum.map f g) := by
  simp only [getNodeAt?, applyAt, getSubtreeAt?_bimap, Option.map_map]
  match getSubtreeAt? t p with
  | none => exact Eq.trans (Option.map_none' _) (Option.map_none' _).symm
  | some (leaf _) => simp only [Option.map_some', Function.comp_apply,
                                bimap_leaf, getNodeData, Sum.map_inr]
  | some (branch _ _) => simp only [Option.map_some', Function.comp_apply,
                                    bimap_branch, getNodeData, Sum.map_inl]

end getNodeAt?

section setSubtreeAt?

private def modifyMSubtreeAt.impl {m} [Monad m]
    (f : RoseTree N L → m (RoseTree N L)) (p : Addr)
    (i j : ℕ) (h : j ≤ p.size) (t : RoseTree N L) : m (RoseTree N L) :=
  if h' : i < j
  then match t with
       | leaf x => pure (leaf x)
       | branch y ts =>
          branch y <$> ts.modifyM (p.get ⟨i, lt_of_lt_of_le h' h⟩)
                                  (modifyMSubtreeAt.impl f p (i + 1) j h)
  else f t
termination_by impl _ _ i j _ _ => j - i

def modifyMSubtreeAt {m} [Monad m] (f : RoseTree N L → m (RoseTree N L))
    (p : Addr) (t : RoseTree N L) : m (RoseTree N L) :=
  modifyMSubtreeAt.impl f p 0 p.size (le_refl _) t

private lemma modifyMSubtreeAt.impl_eq_modifyMSubtreeAt_extract
    (f : RoseTree N L → Option (RoseTree N L)) (p : Addr)
    (i j : ℕ) (h : j ≤ p.size) (t : RoseTree N L) :
    modifyMSubtreeAt.impl f p i j h t = modifyMSubtreeAt f (p.extract i j) t := by
  simp only [modifyMSubtreeAt, Array.size_extract, min_eq_left h]
  conv_lhs => rw [← Nat.add_zero i]
  generalize 0 = ℓ
  induction' t with x y ts ih generalizing ℓ
    <;> simp_rw [modifyMSubtreeAt.impl, lt_tsub_iff_left]
  refine dite_congr rfl (fun h' => congrArg _ ?_) (fun _ => rfl)
  rw [Array.extract_get]
  simp only [Array.modifyM, Array.get_eq_getElem, Nat.add_assoc]
  refine dite_congr rfl (fun h'' => congrArg (. >>= _) ?_) (fun _ => rfl)
  exact ih ⟨_, h''⟩ (ℓ + 1)

def maxValidPrefixLen (t : RoseTree N L) (p : Addr) :=
  (p.foldlIdxM (fun i t j => t.children[j]?.getDM (Sum.inl i)) t).getLeft?.getD p.size

lemma maxValidPrefixLen_spec (t : RoseTree N L) (p : Addr) :
    maxValidPrefixLen t p
    = (p.findIdx? (fun i => ¬ t.hasNodeAt (p.extract 0 i))).getD p.size := by
  refine congrArg (Option.getD . p.size) ?_

  admit

-- lemma modifyMSubtreeAt_def {m} [Monad m] (f : RoseTree N L → m (RoseTree N L))
--     (p : Addr) (t : RoseTree N L) :
--     modifyMSubtreeAt f p t
--     = let cont := p.foldrM
--       cont.getD id  := _

-- def setSubtreeAt? (t : RoseTree N L) (p : Addr) (t' : RoseTree N L) := sorry

-- def transformAt? (f : RoseTree N L → Option (RoseTree N L)) (p : Addr)
--     (t : RoseTree N L) : Option (RoseTree N L) :=
--   transformAt?.impl f p 0 p.size (le_refl _) t

-- private lemma transformAt?.impl_getSubtreeAt?
--     (f : RoseTree N L → Option (RoseTree N L)) (p q : Addr)
--     (i j : ℕ) (h : j ≤ p.size) (t : RoseTree N L) :
--     (transformAt?.impl f p i j h t).bind (getSubtreeAt? . q)
--     = if p.data <+: q.data
--       then ((t.getSubtreeAt? p).bind f).bind (getSubtreeAt? . $ ⟨q.data.drop p.size⟩)
--       else t.getSubtreeAt? q := by

--   admit

def contractEdge (t : RoseTree N L) (p : Addr)
    (f : N → L → N) (g : N → N → N) : Option (RoseTree N L) := by
  induction t with
  | leaf x => admit
  | branch y ts => admit

end setSubtreeAt?

end RoseTree

@[reducible] def AryTree.{u, v} (k : ℕ) (N : Type u) (L : Type v) :=
  { t : RoseTree N L // ∀ p (h : t.hasInnerNodeAt p),
    (t.getSubtreeAt (t.hasNodeAt_of_hasInnerNodeAt p h)).children.size = k }

def BinTree := AryTree 2
