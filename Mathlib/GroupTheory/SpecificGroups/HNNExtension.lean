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

variable (G A B φ)

structure TransversalPair : Type _ :=
  /-- The transversal of each subgroup -/
  ( set : Units ℤ → Set G )
  /-- The chosen element of the subgroup itself is the identity -/
  ( one_mem : ∀u, 1 ∈ set u )
  /-- We have exactly one element of each coset of the subgroup -/
  ( compl : ∀ u, IsComplement (if u = 1 then A else B) (set u) )

variable {G A B}

structure _root_.HNNExtension.NormalWord (d : TransversalPair G A B) : Type _ :=
  ( left : G )
  ( toList : List (Units ℤ × G) )
  ( mem_set : ∀ (u : Units ℤ) (g : G), (u, g) ∈ toList → g ∈ d.set u )
  ( chain : toList.Chain' (fun a b => a.2 = 1 → a.1 = b.1) )

variable {d : TransversalPair G A B}

@[simps]
def empty : NormalWord d :=
  { left := 1
    toList := []
    mem_set := by simp
    chain := List.chain'_nil }

def ofGroup (g : G) : NormalWord d :=
  { left := g
    toList := []
    mem_set := by simp
    chain := List.chain'_nil }

instance : Inhabited (NormalWord d) := ⟨empty⟩

structure Pair (d : TransversalPair G A B) : Type _ :=
  ( head : G )
  ( int : Units ℤ )
  ( tail : NormalWord d )

instance : MulAction G (NormalWord d) :=
  { smul := fun g w => { w with left := g * w.left }
    one_smul := by simp [instHSMul]
    mul_smul := by simp [instHSMul, mul_assoc] }

theorem smul_def (g : G) (w : NormalWord d) :
    g • w = { w with left := g * w.left } := rfl

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

variable (d)
noncomputable def powUnitsIntSMulGroup (u : Units ℤ) (g : G) : G × d.set u :=
  if hu : u = 1
  then
    have : IsComplement (A : Set G) (d.set u) := hu ▸ d.compl 1
    let g' := this.equiv g
    (φ g'.1, g'.2)
  else
    have : IsComplement (B : Set G) (d.set u) := by simpa [hu] using d.compl u
    let g' := this.equiv g
    (φ.symm g'.1, g'.2)

variable {d}
#print Units
noncomputable def powUnitsIntSMul [DecidableEq G]
    (u : Units ℤ) (w : NormalWord d) : NormalWord d :=
  consRecOn w
    (fun g =>
      let g' := powUnitsIntSMulGroup φ d u g
      cons g'.1 u (ofGroup g'.2) (Subtype.prop _)
        (by simp [powUnitsIntSMulGroup, ofGroup]))
    (fun g u' w h1 h2 _ =>
      let g' := powUnitsIntSMulGroup φ d u g
      if hg' : (g'.2 : G) = 1 ∧ u ≠ u'
      then g'.1 • w
      else cons g'.1 u (cons g'.2 u' w h1 h2)
        (Subtype.property _)
        (by simpa using hg'))
set_option pp.proofs.withType false
theorem powUnitsIntSMulGroup_neg (u : Units ℤ) (g : G) :
    powUnitsIntSMulGroup φ d (-u) (powUnitsIntSMulGroup φ d u⁻¹ g).1 = sorry := by
  simp [powUnitsIntSMulGroup]
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
    ext
    dsimp
    rw [IsComplement.equiv_fst_eq_self_of_mem_of_one_mem]




theorem powUnitsIntSMul_neg [DecidableEq G] (u : Units ℤ) (w : NormalWord d) :
    powUnitsIntSMul φ (-u) (powUnitsIntSMul φ u w) = w :=
  consRecOn w
    (fun g => by
      rw [powUnitsIntSMul, powUnitsIntSMul]
      simp
      rw [dif_pos]
      admit
      simp [Units.ext_iff, neg_eq_iff_add_eq_zero]

      )
    _

end NormalWord

end HNNExtension
