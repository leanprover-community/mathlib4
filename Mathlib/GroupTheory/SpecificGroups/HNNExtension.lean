/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.GroupTheory.SpecificGroups.Coprod
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup
import Mathlib.GroupTheory.Complement

open Monoid Coprod Multiplicative Subgroup Function

local notation "C∞ " => Multiplicative ℤ

def HNNExtension.con (G : Type*) [Group G] (A B : Subgroup G) (φ : A ≃* B) : Con (G ∗ C∞) :=
  conGen (fun x y => ∃ (a : A),
    x = inr (ofAdd 1) * inl (a : G) ∧
    y = inl (φ a : G) * inr (ofAdd 1))

def HNNExtension  (G : Type*) [Group G] (A B : Subgroup G) (φ : A ≃* B) : Type _ :=
  (HNNExtension.con G A B φ).Quotient

variable {G : Type*} [Group G] {A B : Subgroup G} {φ : A ≃* B} {H : Type*} [Group H]

instance : Group (HNNExtension G A B φ) := by
  delta HNNExtension; infer_instance

namespace HNNExtension

def of : G →* HNNExtension G A B φ :=
  (HNNExtension.con G A B φ).mk'.comp inl

def t : HNNExtension G A B φ :=
  (HNNExtension.con G A B φ).mk'.comp inr (ofAdd 1)

theorem t_mul_of (a : A) :
    t * (of (a : G) : HNNExtension G A B φ) = of (φ a : G) * t :=
  (Con.eq _).2 <| ConGen.Rel.of _ _ <| ⟨a, by simp⟩

theorem of_mul_t (b : B) :
    (of (b : G) : HNNExtension G A B φ) * t = t * of (φ.symm b : G) := by
  rw [t_mul_of]; simp

theorem equiv_eq_conj (a : A) :
    (of (φ a : G) : HNNExtension G A B φ) = t * of (a : G) * t⁻¹ := by
  rw [t_mul_of]; simp

theorem equiv_symm_eq_conj (b : B) :
    (of (φ.symm b : G) : HNNExtension G A B φ) = t⁻¹ * of (b : G) * t := by
  rw [mul_assoc, of_mul_t]; simp

theorem inv_t_mul_of (b : B) :
    t⁻¹ * (of (b : G) : HNNExtension G A B φ) = of (φ.symm b : G) * t⁻¹ := by
  rw [equiv_symm_eq_conj]; simp

theorem of_mul_inv_t (a : A) :
    (of (a : G) : HNNExtension G A B φ) * t⁻¹ = t⁻¹ * of (φ a : G) := by
  rw [equiv_eq_conj]; simp [mul_assoc]

def lift (f : G →* H) (x : H) (hx : ∀ a : A, x * f ↑a = f (φ a : G) * x) :
    HNNExtension G A B φ →* H :=
  Con.lift _ (Coprod.lift f (zpowersHom H x)) (Con.conGen_le <| by
    rintro _ _ ⟨a, rfl, rfl⟩
    simp [hx])

@[simp]
theorem lift_t (f : G →* H) (x : H) (hx : ∀ a : A, x * f ↑a = f (φ a : G) * x) :
    lift f x hx t = x := by
  delta HNNExtension; simp [lift, t]

@[simp]
theorem lift_of (f : G →* H) (x : H) (hx : ∀ a : A, x * f ↑a = f (φ a : G) * x) (g : G) :
    lift f x hx (of g) = f g := by
  delta HNNExtension; simp [lift, of]

@[ext]
theorem hom_ext {f g : HNNExtension G A B φ →* H}
    (hg : f.comp of  = g.comp of) (ht : f t = g t) : f = g :=
  (MonoidHom.cancel_right Con.mk'_surjective).mp <|
    Coprod.ext_hom _ _ hg (MonoidHom.ext_mint ht)

namespace NormalWord

@[reducible]
def BoolFamily (G : Type*) [Group G] : Bool → Type _
  | true => ULift C∞
  | false => G

instance (b : Bool) : Group (BoolFamily G b) := by
  cases b <;> dsimp [BoolFamily] <;> infer_instance

variable (A B φ)

def toSubgroup (u : Units ℤ) : Subgroup G :=
  if u = 1 then A else B

@[simp]
theorem toSubgroup_one : toSubgroup A B 1 = A := rfl

@[simp]
theorem toSubgroup_neg_one : toSubgroup A B (-1) = B := rfl


variable {A B}

def toSubgroupEquiv (u : Units ℤ) : toSubgroup A B u ≃* toSubgroup A B (-u) :=
  if hu : u = 1 then hu ▸ φ else by
    convert φ.symm <;>
    cases Int.units_eq_one_or u <;> simp_all

@[simp]
theorem toSubgroupEquiv_one : toSubgroupEquiv φ 1 = φ := rfl

@[simp]
theorem toSubgroupEquiv_neg_one : toSubgroupEquiv φ (-1) = φ.symm := rfl

@[simp]
theorem toSubgroupEquiv_neg_apply (u : Units ℤ) (a : toSubgroup A B u):
    (toSubgroupEquiv φ (-u) (toSubgroupEquiv φ u a) : G) = a := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · simp only [toSubgroup_neg_one, toSubgroupEquiv_neg_one, SetLike.coe_eq_coe]
    exact φ.apply_symm_apply a

variable (G A B)
structure TransversalPair : Type _ :=
  /-- The transversal of each subgroup -/
  ( set : Units ℤ → Set G )
  /-- The chosen element of the subgroup itself is the identity -/
  ( one_mem : ∀u, 1 ∈ set u )
  /-- We have exactly one element of each coset of the subgroup -/
  ( compl : ∀ u, IsComplement (toSubgroup A B u : Subgroup G) (set u) )

variable {G A B}

structure _root_.HNNExtension.NormalWord (d : TransversalPair G A B) : Type _ :=
  ( left : G )
  ( toList : List (Units ℤ × G) )
  ( mem_set : ∀ (u : Units ℤ) (g : G), (u, g) ∈ toList → g ∈ d.set u )
  ( chain : toList.Chain' (fun a b => a.2 = 1 → a.1 = b.1) )

variable {d : TransversalPair G A B}



@[ext]
theorem NormalWord.ext {w w' : NormalWord d}
    (h1 : w.left = w'.left) (h2 : w.toList = w'.toList): w = w' := by
  cases w; cases w'; simp_all

@[simps]
def empty : NormalWord d :=
  { left := 1
    toList := []
    mem_set := by simp
    chain := List.chain'_nil }

@[simps]
def ofGroup (g : G) : NormalWord d :=
  { left := g
    toList := []
    mem_set := by simp
    chain := List.chain'_nil }

instance : Inhabited (NormalWord d) := ⟨empty⟩

instance : MulAction G (NormalWord d) :=
  { smul := fun g w => { w with left := g * w.left }
    one_smul := by simp [instHSMul]
    mul_smul := by simp [instHSMul, mul_assoc] }

theorem smul_def (g : G) (w : NormalWord d) :
    g • w = { w with left := g * w.left } := rfl

@[simp]
theorem smul_left (g : G) (w : NormalWord d) : (g • w).left = g * w.left := rfl

@[simp]
theorem smul_toList (g : G) (w : NormalWord d) : (g • w).toList = w.toList := rfl

instance : FaithfulSMul G (NormalWord d) := ⟨by simp [smul_def]⟩

@[simps]
def cons (g : G) (u : Units ℤ) (w : NormalWord d) (h1 : w.left ∈ d.set u)
    (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?, w.left = 1 → u = u') :
    NormalWord d :=
  { left := g,
    toList := (u, w.left) :: w.toList,
    mem_set := by
      intro u' g' h'
      simp only [List.mem_cons, Prod.mk.injEq] at h'
      rcases h' with ⟨rfl, rfl⟩ | h'
      · exact h1
      · exact w.mem_set _ _ h'
    chain := by
      refine List.chain'_cons'.2 ⟨?_, w.chain⟩
      rintro ⟨ u', g'⟩ hu' hw1
      exact h2 _ (by simp_all) hw1 }

@[elab_as_elim]
def consRecOn {motive : NormalWord d → Sort*} (w : NormalWord d)
    (ofGroup : ∀g, motive (ofGroup g))
    (cons : ∀ (g : G) (u : Units ℤ) (w : NormalWord d) (h1 : w.left ∈ d.set u)
      (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?, w.left = 1 → u = u'),
      motive w → motive (cons g u w h1 h2)) : motive w := by
  rcases w with ⟨g, l,  mem_set, chain⟩
  induction l generalizing g with
  | nil => exact ofGroup _
  | cons a l ih =>
    exact cons g a.1 ⟨a.2, l,
      fun _ _ h => mem_set _ _ (List.mem_cons_of_mem _ h),
      (List.chain'_cons'.1 chain).2⟩
      (mem_set a.1 a.2 (List.mem_cons_self _ _))
      (by simpa using (List.chain'_cons'.1 chain).1)
      (ih _ _ _)

@[simp]
theorem consRecOn_ofGroup {motive : NormalWord d → Sort*}
    (g : G) (ofGroup : ∀g, motive (ofGroup g))
    (cons : ∀ (g : G) (u : Units ℤ) (w : NormalWord d) (h1 : w.left ∈ d.set u)
      (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?, w.left = 1 → u = u'),
      motive w → motive (cons g u w h1 h2)) :
    consRecOn (.ofGroup g) ofGroup cons = ofGroup g := rfl

@[simp]
theorem consRecOn_cons {motive : NormalWord d → Sort*}
    (g : G) (u : Units ℤ) (w : NormalWord d) (h1 : w.left ∈ d.set u)
    (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?, w.left = 1 → u = u')
    (ofGroup : ∀g, motive (ofGroup g))
    (cons : ∀ (g : G) (u : Units ℤ) (w : NormalWord d) (h1 : w.left ∈ d.set u)
      (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?, w.left = 1 → u = u'),
      motive w → motive (cons g u w h1 h2)) :
    consRecOn (.cons g u w h1 h2) ofGroup cons = cons g u w h1 h2
      (consRecOn w ofGroup cons) := rfl

@[simp]
theorem smul_cons (g₁ g₂ : G) (u : Units ℤ) (w : NormalWord d) (h1 : w.left ∈ d.set u)
    (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?, w.left = 1 → u = u') :
    g₁ • cons g₂ u w h1 h2 = cons (g₁ * g₂) u w h1 h2 :=
  rfl

theorem smul_ofGroup (g₁ g₂ : G) :
    g₁ • (ofGroup g₂ : NormalWord d) = ofGroup (g₁ * g₂) := rfl


variable (d)
noncomputable def unitSMulGroup (u : Units ℤ) (g : G) :
    (toSubgroup A B (-u)) × d.set u :=
  let g' := (d.compl u).equiv g
  (toSubgroupEquiv φ u g'.1, g'.2)

theorem unitSMulGroup_snd (u : Units ℤ) (g : G) :
    (unitSMulGroup φ d u g).2 = ((d.compl u).equiv g).2 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rfl

variable {d} [DecidableEq G]

def Cancels (u : Units ℤ) (w : NormalWord d) : Prop :=
  (w.left ∈ (toSubgroup A B u : Subgroup G)) ∧ w.toList.head?.map Prod.fst = some (-u)

def unitSMulWithCancel (u : Units ℤ) (w : NormalWord d) : Cancels u w → NormalWord d :=
  consRecOn w
    (by simp [Cancels, ofGroup]; tauto)
    (fun g u' w h1 h2 _ can =>
      (toSubgroupEquiv φ u ⟨g, can.1⟩ : G) • w)

noncomputable def unitSMul
    (u : Units ℤ) (w : NormalWord d) : NormalWord d :=
  letI := Classical.dec
  if h : Cancels u w
  then unitSMulWithCancel φ u w h
  else let g' := unitSMulGroup φ d u w.left
    cons g'.1 u ((g'.2 * w.left⁻¹ : G) • w)
      (by simp [smul_def])
      (by
        simp [smul_def]
        simp only [Cancels, Option.map_eq_some', Prod.exists, exists_and_right, exists_eq_right,
          not_and, not_exists] at h
        simp only [unitSMulGroup_snd, IsComplement.equiv_snd_eq_one_iff_mem _ (d.one_mem _)]
        intro u' x hx hw
        by_contra huu'
        rcases Int.units_eq_one_or u' with (rfl | rfl) <;>
        rcases Int.units_eq_one_or u with (rfl | rfl) <;>
        simp_all)

set_option pp.proofs.withType false

theorem unitSMul_cancels_iff (u : Units ℤ) (w : NormalWord d) :
    Cancels (-u) (unitSMul φ u w) ↔ ¬ Cancels u w := by
  by_cases h : Cancels u w
  · simp only [unitSMul, dif_pos trivial, h, iff_false]
    induction w using consRecOn with
    | ofGroup => simp [Cancels, unitSMulWithCancel]
    | cons g u' w h1 h2 _ =>
      intro hc
      simp [Cancels, unitSMulWithCancel,
        Subgroup.mul_mem_cancel_left] at h hc
      rcases hc.2 with ⟨x, hx⟩
      rw [hx] at h2
      cases h.2
      have hw : w.left = 1 := by
        simpa using congr_arg Prod.fst
          (((d.compl (-u)).existsUnique w.left).unique
          (y₁ := (⟨w.left, hc.1⟩, ⟨1, d.one_mem (-u)⟩))
          (y₂ := (1, ⟨w.left, h1⟩)) (by simp) (by simp))
      have := h2 _ rfl hw
      simp [Units.ext_iff, neg_eq_iff_add_eq_zero] at this
  · simp only [unitSMul, dif_neg h]
    simpa [Cancels] using h

theorem unitSMul_neg [DecidableEq G] (u : Units ℤ) (w : NormalWord d) :
    unitSMul φ (-u) (unitSMul φ u w) = w := by
  rw [unitSMul]
  split_ifs with hcan
  · have hncan : ¬ Cancels u w := (unitSMul_cancels_iff _ _ _).1 hcan
    unfold unitSMul
    simp only [dif_neg hncan]
    simp [unitSMulWithCancel, unitSMulGroup, (d.compl u).equiv_snd_eq_inv_mul]
  · have hcan2 : Cancels u w := not_not.1 (mt (unitSMul_cancels_iff _ _ _).2 hcan)
    unfold unitSMul at hcan ⊢
    simp only [dif_pos hcan2] at hcan ⊢
    cases w using consRecOn with
    | ofGroup => simp [Cancels] at hcan2
    | cons g u' w h1 h2 ih =>
      clear ih
      simp [unitSMulWithCancel, unitSMulGroup]
      cases hcan2.2
      have : ((d.compl (-u)).equiv w.left).1 = 1 :=
        (d.compl (-u)).equiv_fst_eq_one_of_mem_of_one_mem _ h1
      apply NormalWord.ext
      · simp [this]
      · simp [mul_assoc, Units.ext_iff, (d.compl (-u)).equiv_snd_eq_inv_mul, this]

end NormalWord

end HNNExtension
