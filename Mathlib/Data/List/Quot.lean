/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Quot

/-!
# Quotients indexed by a `List`

In this file, we define lifting and recursion principle for quotients indexed by a `List`.

## Main definitions

* `List.quotientLift`: Given `l : List ι`. A function on `∀ i ∈ l, α i` which respects setoid `S i`
  for each `i` in `l` can be lifted to a function on `∀ i ∈ l, Quotient (S i)`.
* `List.quotientRec`: Recursion principle for quotients indexed by a `List`. It is the dependent
  version of `List.quotientLift`.
-/

namespace List
variable {ι : Type _} [DecidableEq ι] {α : ι → Sort _} [S : ∀ i, Setoid (α i)] {β : Sort _}

namespace PiMemCons

/-- A constructor for `∀ j ∈ (i :: l), α j`, by giving the value at `i` and a function on `l`.

The inverse functions are `PiMemCons.head` and `PiMemCons.tail`.
-/
def cons {i : ι} {l : List ι} (h : α i) (t : ∀ j ∈ l, α j) :
    ∀ j ∈ (i :: l), α j :=
  fun j hj ↦ if H : j = i then (congr_arg α H).mpr h else t j ((mem_cons.mp hj).resolve_left H)
#align list.pi_mem_cons.cons List.PiMemCons.cons

/-- `PiMemCons.head f` gives the value of `f : ∀ j ∈ (i :: l), α j` at `i`. -/
def head {i : ι} {l : List ι} (f : ∀ j ∈ (i :: l), α j) :
    α i :=
  f i (mem_cons_self _ _)
#align list.pi_mem_cons.head List.PiMemCons.head

/-- `PiMemCons.tail f` restricts `f : ∀ j ∈ (i :: l), α j` to `l`. -/
def tail {i : ι} {l : List ι} (f : ∀ j ∈ (i :: l), α j) :
    ∀ j ∈ l, α j :=
  fun j hj ↦ f j (mem_cons_of_mem _ hj)
#align list.pi_mem_cons.tail List.PiMemCons.tail

@[simp] lemma eta {i : ι} {l : List ι} (f : ∀ j ∈ (i :: l), α j) :
    cons (head f) (tail f) = f := by
  ext j hj; dsimp [cons]
  split_ifs with H
  · cases H; rfl
  · rfl
#align list.pi_mem_cons.eta List.PiMemCons.eta

@[simp] lemma head_cons {i : ι} {l : List ι} (h : α i) (t : ∀ j ∈ l, α j) :
    head (cons h t) = h :=
  by simp [head, cons]
#align list.pi_mem_cons.head_cons List.PiMemCons.head_cons

lemma tail_cons {i : ι} {l : List ι} (hl : (i :: l).Nodup) (h : α i) (t : ∀ j ∈ l, α j) :
    tail (cons h t) = t := by
  ext j hj
  obtain ⟨hl, _⟩ := pairwise_cons.mp hl
  simp [tail, cons, (hl j hj).symm]
#align list.pi_mem_cons.tail_cons List.PiMemCons.tail_cons

lemma cons_apply {i : ι} {l : List ι} (h : α i) (t : ∀ j ∈ l, α j)
    {α' : ι → Sort _} (f : ∀ ⦃j⦄, α j → α' j) :
    cons (f h) (fun j hj ↦ f (t j hj)) = fun j hj ↦ f ((cons h t) j hj) := by
  ext j hj; dsimp [cons]
  split_ifs with H
  · cases H; rfl
  · rfl
#align list.pi_mem_cons.cons_apply List.PiMemCons.cons_apply

lemma setoid_congr {i : ι} {l : List ι} {h₁ h₂ : α i} {t₁ t₂ : ∀ j ∈ l, α j}
    (hh : h₁ ≈ h₂) (ht : ∀ (i : ι) (hi : i ∈ l), t₁ i hi ≈ t₂ i hi) :
    ∀ j hj, cons h₁ t₁ j hj ≈ cons h₂ t₂ j hj := by
  intro j hj; dsimp [cons]
  split_ifs with H
  · cases H; exact hh
  · exact ht _ _
#align list.pi_mem_cons.setoid_congr List.PiMemCons.setoid_congr

end PiMemCons

/-- Given a collection of setoids indexed by a type `ι`, a list `l` of indices, and a function that
  for each `i ∈ l` gives a term of the corresponding quotient type, then there is a corresponding
  term in the quotient of the product of the setoids indexed by `l`. -/
def quotientChoice : ∀ {l : List ι},
    (∀ i ∈ l, Quotient (S i)) → @Quotient (∀ i ∈ l, α i) piSetoid
  | []      , _ => ⟦fun.⟧
  | (i :: _), q => Quotient.liftOn₂ (PiMemCons.head (i := i) q)
      (quotientChoice (PiMemCons.tail q))
      (fun a l ↦ ⟦PiMemCons.cons a l⟧)
      (fun _ _ _ _ ha hl ↦ Quotient.sound (PiMemCons.setoid_congr ha hl))
#align list.quotient_choice List.quotientChoice

theorem quotientChoice_mk : ∀ {l : List ι}
    (a : ∀ i ∈ l, α i), quotientChoice (fun i h ↦ ⟦a i h⟧) = ⟦a⟧
  | []      , f => Quotient.sound fun.
  | (i :: l), f => by
    simp_rw [quotientChoice, PiMemCons.tail, quotientChoice_mk]
    exact congr_arg (Quotient.mk _) (PiMemCons.eta f)
#align list.quotient_choice_mk List.quotientChoice_mk

/-- Lift a function on `∀ i ∈ l, α i` to a function on `∀ i ∈ l, Quotient (S i)`. -/
def quotientLift {l : List ι} (f : (∀ i ∈ l, α i) → β)
    (h : ∀ (a b : ∀ i ∈ l, α i), (∀ i (hi : i ∈ l), a i hi ≈ b i hi) → f a = f b)
    (q : ∀ i ∈ l, Quotient (S i)) : β :=
  Quotient.lift f h (quotientChoice q)
#align list.quotient_lift List.quotientLift

/-- Lift a function on `∀ i ∈ l, α i` to a function on `∀ i ∈ l, Quotient (S i)`. -/
def quotientLiftOn {l : List ι} (q : ∀ i ∈ l, Quotient (S i)) (f : (∀ i ∈ l, α i) → β)
    (h : ∀ (a b : ∀ i ∈ l, α i), (∀ i (hi : i ∈ l), a i hi ≈ b i hi) → f a = f b) : β :=
  quotientLift f h q
#align list.quotient_lift_on List.quotientLiftOn

@[simp] lemma quotientLift_nil (f : (∀ i ∈ ([] : List ι), α i) → β) (h) :
    quotientLift f h = fun _ => f fun. :=
  rfl
#align list.quotient_lift_nil List.quotientLift_nil

@[simp] lemma quotientLift_mk {l : List ι} (f : (∀ i ∈ l, α i) → β)
    (h : ∀ (a b : ∀ i ∈ l, α i), (∀ i (hi : i ∈ l), a i hi ≈ b i hi) → f a = f b)
    (a : ∀ i ∈ l, α i) : quotientLift f h (fun i hi ↦ ⟦a i hi⟧) = f a := by
  dsimp [quotientLift]
  rw [quotientChoice_mk]
  rfl
#align list.quotient_lift_mk List.quotientLift_mk

@[simp] lemma quotientLiftOn_nil (q : ∀ i ∈ ([] : List ι), Quotient (S i)) :
    quotientLiftOn (β := β) q = fun f _ ↦ f fun. :=
  rfl
#align list.quotient_lift_on_nil List.quotientLiftOn_nil

@[simp] lemma quotientLiftOn_mk {l : List ι} (a : ∀ i ∈ l, α i) :
    quotientLiftOn (β := β) (fun i hi ↦ ⟦a i hi⟧) = fun f _ ↦ f a := by
  ext f h
  exact quotientLift_mk f h a
#align list.quotient_lift_on_mk List.quotientLiftOn_nil

-- Porting note: no `decidable_classical` linter
-- `@[nolint decidable_classical]`
/-- Choice-free induction principle for quotients indexed by a `List`. -/
@[elab_as_elim]
lemma quotient_ind : ∀ {l : List ι} {C : (∀ i ∈ l, Quotient (S i)) → Prop},
    (∀ a : ∀ i ∈ l, α i, C (fun i hi ↦ ⟦a i hi⟧)) → ∀ (q : ∀ i ∈ l, Quotient (S i)), C q
  | []    , C, f, q => cast (congr_arg _ (funext₂ fun.)) (f fun.)
  | (i::l), C, f, q => by
    rw [← PiMemCons.eta q]
    induction' (PiMemCons.head q) using Quotient.ind with a
    refine' @quotient_ind _ (fun q ↦ C (PiMemCons.cons ⟦a⟧ q)) _ (PiMemCons.tail q)
    intro as
    rw [PiMemCons.cons_apply a as (fun j ↦ Quotient.mk _)]
    exact f _
#align list.quotient_ind List.quotient_ind

-- Porting note: no `decidable_classical` linter
-- `@[nolint decidable_classical]`
/-- Choice-free induction principle for quotients indexed by a `List`. -/
@[elab_as_elim]
lemma quotient_induction_on {l : List ι}
    {C : (∀ i ∈ l, Quotient (S i)) → Prop}
    (q : ∀ i ∈ l, Quotient (S i)) (f : ∀ a : ∀ i ∈ l, α i, C (fun i hi ↦ ⟦a i hi⟧)) :
    C q :=
  quotient_ind f q
#align list.quotient_induction_on List.quotient_induction_on

/-- `quotientChoice` as an equivalence. -/
def quotientChoiceEquiv {l : List ι} :
    (∀ i ∈ l, Quotient (S i)) ≃ @Quotient (∀ i ∈ l, α i) piSetoid where
  toFun := quotientChoice
  invFun := fun q ↦ Quotient.liftOn q (fun a i hi ↦ ⟦a i hi⟧)
    (fun a₁ a₂ ha ↦ funext₂ (fun i hi ↦ Quotient.sound (ha i hi)))
  left_inv := fun q ↦ by
    refine' quotient_induction_on q (fun a ↦ _)
    ext i hi; dsimp
    rw [quotientChoice_mk]; rfl
  right_inv := fun q ↦ by induction' q using Quotient.ind; exact quotientChoice_mk _
#align list.quotient_choice_equiv List.quotientChoiceEquiv

section quotientRec
variable {l : List ι} {C : (∀ i ∈ l, Quotient (S i)) → Sort _}
  (f : ∀ a : ∀ i ∈ l, α i, C (fun i hi ↦ ⟦a i hi⟧))

@[reducible]
private def quotientRec.indep
    (a : ∀ i ∈ l, α i) : PSigma C :=
  ⟨fun i hi ↦ ⟦a i hi⟧, f a⟩

variable (h : ∀ (a b : ∀ i ∈ l, α i) (h : ∀ i hi, a i hi ≈ b i hi),
  Eq.ndrec (f a) (funext₂ fun i hi ↦ Quotient.sound (h i hi)) = f b)

private lemma quotientRec.indepCoherent :
    ∀ a b : ∀ i ∈ l, α i, (∀ i hi, a i hi ≈ b i hi) →
      quotientRec.indep f a = quotientRec.indep f b :=
  fun a b e ↦ PSigma.eq (funext₂ fun i hi ↦ Quotient.sound (e i hi)) (h a b e)

private lemma quotientRec.liftIndepPr1 (q : ∀ i ∈ l, Quotient (S i)) :
    (quotientLift (quotientRec.indep f) (quotientRec.indepCoherent f h) q).1 = q :=
  quotient_ind (fun a ↦ funext₂ fun i hi ↦ by rw [quotientLift_mk]) q

end quotientRec

/-- Recursion principle for quotients indexed by a `List`. -/
@[elab_as_elim] def quotientRec {l : List ι} {C : (∀ i ∈ l, Quotient (S i)) → Sort _}
    (f : ∀ a : ∀ i ∈ l, α i, C (fun i hi ↦ ⟦a i hi⟧))
    (h : ∀ (a b : ∀ i ∈ l, α i) (h : ∀ i hi, a i hi ≈ b i hi),
      Eq.ndrec (f a) (funext₂ fun i hi ↦ Quotient.sound (h i hi)) = f b)
    (q : ∀ i ∈ l, Quotient (S i)) :
    C q :=
  Eq.ndrecOn (quotientRec.liftIndepPr1 f h q)
    ((quotientLift (quotientRec.indep f) (quotientRec.indepCoherent f h) q).2)
#align list.quotient_rec List.quotientRec

/-- Recursion principle for quotients indexed by a `List`. -/
@[elab_as_elim] def quotientRecOn {l : List ι} {C : (∀ i ∈ l, Quotient (S i)) → Sort _}
    (q : ∀ i ∈ l, Quotient (S i))
    (f : ∀ a : ∀ i ∈ l, α i, C (fun i hi ↦ ⟦a i hi⟧))
    (h : ∀ (a b : ∀ i ∈ l, α i) (h : ∀ i hi, a i hi ≈ b i hi),
      Eq.ndrec (f a) (funext₂ fun i hi ↦ Quotient.sound (h i hi)) = f b) :
    C q :=
  quotientRec f h q
#align list.quotient_rec_on List.quotientRecOn

/-- Recursion principle for quotients indexed by a `List`. -/
@[elab_as_elim] def quotientHRecOn {l : List ι} {C : (∀ i ∈ l, Quotient (S i)) → Sort _}
    (q : ∀ i ∈ l, Quotient (S i))
    (f : ∀ a : ∀ i ∈ l, α i, C (fun i hi ↦ ⟦a i hi⟧))
    (h : ∀ (a b : ∀ i ∈ l, α i), (∀ i hi, a i hi ≈ b i hi) → HEq (f a) (f b)) :
    C q :=
  quotientRecOn q f (fun a b p ↦ eq_of_heq ((eq_rec_heq _ (f a)).trans (h a b p)))
#align list.quotient_hrec_on List.quotientHRecOn

@[simp] lemma quotientRec_mk {l : List ι} {C : (∀ i ∈ l, Quotient (S i)) → Sort _}
    (f : ∀ a : ∀ i ∈ l, α i, C (fun i hi ↦ ⟦a i hi⟧))
    (h) (a : ∀ i ∈ l, α i) :
    @quotientRec _ _ _ _ _ C f h (fun i hi ↦ ⟦a i hi⟧) = f a := by
  dsimp [quotientRec]; refine' eq_of_heq ((eq_rec_heq _ _).trans _)
  rw [quotientLift_mk (quotientRec.indep f) (quotientRec.indepCoherent f h) a]
#align list.quotient_rec_mk List.quotientRec_mk

@[simp] lemma quotientRecOn_mk {l : List ι} {C : (∀ i ∈ l, Quotient (S i)) → Sort _}
    (a : ∀ i ∈ l, α i) :
    @quotientRecOn _ _ _ _ _ C (fun i hi ↦ ⟦a i hi⟧) = fun f _ ↦ f a := by
  ext f h; exact quotientRec_mk _ _ _
#align list.quotient_rec_on_mk List.quotientRecOn_mk

lemma quotientLift_inj {l : List ι} (f₁ f₂ : (∀ i ∈ l, α i) → β) (h₁ h₂) :
    quotientLift f₁ h₁ = quotientLift f₂ h₂ → f₁ = f₂ :=
  fun h ↦ funext $ fun _ ↦ by rw [← quotientLift_mk f₁ h₁, ← quotientLift_mk f₂ h₂, h]
#align list.quotient_lift_inj List.quotientLift_inj

lemma quotientLift_inj_iff {l : List ι} (f₁ f₂ : (∀ i ∈ l, α i) → β) (h₁ h₂) :
    quotientLift f₁ h₁ = quotientLift f₂ h₂ ↔ f₁ = f₂ :=
  ⟨quotientLift_inj _ _ h₁ h₂, fun h ↦ by cases h; rfl⟩
#align list.quotient_lift_inj_iff List.quotientLift_inj_iff

section helper_lemmas

lemma pi_mem_eq {l₁ l₂ : List ι} (hl : ∀ i, i ∈ l₁ ↔ i ∈ l₂) :
    (∀ i ∈ l₁, α i) = (∀ i ∈ l₂, α i) :=
  pi_congr (fun _ ↦ by rw [hl])
#align list.pi_mem_eq List.pi_mem_eq

lemma fun_pi_mem_eq {l₁ l₂ : List ι} (hl : ∀ i, i ∈ l₁ ↔ i ∈ l₂) :
    ((∀ i ∈ l₁, α i) → β) = ((∀ i ∈ l₂, α i) → β) := by
  rw [pi_mem_eq hl]
#align list.fun_pi_mem_eq List.fun_pi_mem_eq

/-- A helper function to tell lean the motive. -/
-- @[elab_as_eliminator]
def mem_rec (C : (ι → Prop) → Sort _)
    {l₁ l₂ : List ι} (hl : ∀ i, i ∈ l₁ ↔ i ∈ l₂)
    (h : C (· ∈ l₁)) : C (· ∈ l₂) := by
  convert h; simp_rw [hl]
#align list.mem_rec List.mem_rec

end helper_lemmas

-- TODO: `simp_rw [hl]` fails in these 3 lemmas.
-- Can lean compute the motive? Or maybe a tactic (extension) is needed?
-- Or there are some better proofs?
-- (This may because of the order of arguments of `Membership.mem`?)

-- Porting note: `ext` can apply `Function.hfunext` in lean3

lemma quotientChoice_heq {l₁ l₂ : List ι} (hl : ∀ i, i ∈ l₁ ↔ i ∈ l₂) :
    HEq (@quotientChoice _ _ α _ l₁) (@quotientChoice _ _ α _ l₂) := by
  apply Function.hfunext (pi_mem_eq hl); intro q₁ q₂
  refine' List.quotient_induction_on q₂ _
  refine' List.quotient_induction_on q₁ _
  simp_rw [quotientChoice_mk]
  apply mem_rec (fun meml₂ ↦
    ∀ (a₁ : ∀ i ∈ l₁, α i) (a₂ : ∀ i, meml₂ i → α i),
        HEq (fun i hi ↦ ⟦a₁ i hi⟧) (fun i hi ↦ ⟦a₂ i hi⟧) → HEq ⟦a₁⟧ ⟦a₂⟧) hl
  intro a₁ a₂ ha; rw [heq_iff_eq] at *
  simp_rw [← quotientChoice_mk, ha]
#align list.quotient_choice_heq List.quotientChoice_heq

lemma quotientLiftOn_heq {l₁ l₂ : List ι} (hl : ∀ i, i ∈ l₁ ↔ i ∈ l₂) :
    HEq (@quotientLiftOn _ _ α _ β l₁) (@quotientLiftOn _ _ α _ β l₂) := by
  apply Function.hfunext (pi_mem_eq hl); intro q₁ q₂
  refine' List.quotient_induction_on q₂ _
  refine' List.quotient_induction_on q₁ _
  simp_rw [quotientLiftOn_mk]
  apply mem_rec (fun meml₂ ↦
    ∀ (a₁ : ∀ i ∈ l₁, α i) (a₂ : ∀ i, meml₂ i → α i),
        HEq (fun i hi ↦ ⟦a₁ i hi⟧) (fun i hi ↦ ⟦a₂ i hi⟧) →
      HEq (fun (f : (∀ i ∈ l₁, α i) → β)
          (_ : ∀ (a b : ∀ i ∈ l₁, α i), (∀ i hi, a i hi ≈ b i hi) → f a = f b) ↦ f a₁)
        (fun (f : (∀ i, meml₂ i → α i) → β)
          (_ : ∀ (a b : ∀ i, meml₂ i → α i), (∀ i hi, a i hi ≈ b i hi) → f a = f b) ↦ f a₂)) hl
  intro a₁ a₂ ha; rw [heq_iff_eq] at *
  ext f h; apply h; exact fun i hi ↦ Quotient.exact (congr_fun₂ ha i hi)
#align list.quotient_lift_on_heq List.quotientLiftOn_heq

lemma quotientRecOn_heq {l₁ l₂ : List ι} (hl : ∀ i, i ∈ l₁ ↔ i ∈ l₂) :
    HEq (@quotientRecOn.{_, _, uC} _ _ α _ l₁) (@quotientRecOn.{_, _, uC} _ _ α _ l₂) := by
  apply Function.hfunext (fun_pi_mem_eq hl); intros C₁ C₂ hC
  apply Function.hfunext (pi_mem_eq hl); intros q₁ q₂
  refine' List.quotient_induction_on q₂ _
  refine' List.quotient_induction_on q₁ _
  simp_rw [quotientRecOn_mk]
  revert C₁ C₂ hC
  apply mem_rec (fun meml₂ ↦
    ∀ (C₁ : (∀ i ∈ l₁, Quotient (S i)) → Sort _)
      (C₂ : (∀ i, meml₂ i → Quotient (S i)) → Sort _),
      HEq C₁ C₂ →
    ∀ (a₁ : ∀ i ∈ l₁, α i) (a₂ : ∀ i, meml₂ i → α i),
      HEq (fun i hi ↦ ⟦a₁ i hi⟧) (fun i hi ↦ ⟦a₂ i hi⟧) →
      HEq (fun (f : ∀ (a : ∀ i ∈ l₁, α i), C₁ (fun i hi ↦ ⟦a i hi⟧))
          (_ : ∀ (a b : ∀ i ∈ l₁, α i) (h : ∀ i hi, a i hi ≈ b i hi),
            Eq.ndrec (f a) (funext₂ (fun i hi ↦ Quotient.sound (h i hi))) = f b) ↦ f a₁)
        (fun (f : ∀ (a : ∀ i, meml₂ i → α i), C₂ (fun i hi ↦ ⟦a i hi⟧))
          (_ : ∀ (a b : ∀ i, meml₂ i → α i) (h : ∀ i hi, a i hi ≈ b i hi),
            Eq.ndrec (f a) (funext₂ (fun i hi ↦ Quotient.sound (h i hi))) = f b) ↦ f a₂)) hl
  intros C₁ C₂ hC; cases hC
  intros a₁ a₂ ha; rw [heq_iff_eq] at *
  apply Function.hfunext rfl; intros f _ hf; cases hf
  apply Function.hfunext rfl; intros h _ _
  exact heq_of_eq_rec_left _ (h a₁ a₂ $ fun i hi ↦ Quotient.exact (congr_fun₂ ha i hi))
#align list.quotient_rec_on_heq List.quotientRecOn_heq

end List
