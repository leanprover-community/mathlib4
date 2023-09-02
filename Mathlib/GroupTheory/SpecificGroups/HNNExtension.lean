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

variable {G : Type*} [Group G] {A B : Subgroup G} {φ : A ≃* B} {H : Type*}
  [Group H] {M : Type*} [Monoid M]

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
theorem hom_ext {f g : HNNExtension G A B φ →* M}
    (hg : f.comp of  = g.comp of) (ht : f t = g t) : f = g :=
  (MonoidHom.cancel_right Con.mk'_surjective).mp <|
    Coprod.ext_hom _ _ hg (MonoidHom.ext_mint ht)

@[elab_as_elim]
theorem induction_on {motive : HNNExtension G A B φ → Prop}
    (x : HNNExtension G A B φ) (of : ∀ g, motive (of g))
    (t : motive t) (mul : ∀ x y, motive x → motive y → motive (x * y))
    (inv : ∀ x, motive x → motive x⁻¹) : motive x := by
  let S : Subgroup (HNNExtension G A B φ) :=
    { carrier := setOf motive
      one_mem' := by simpa using of 1
      mul_mem' := mul _ _
      inv_mem' := inv _ }
  let f : HNNExtension G A B φ →* S :=
    lift (HNNExtension.of.codRestrict S of)
      ⟨HNNExtension.t, t⟩ (by intro a; ext; simp [equiv_eq_conj, mul_assoc])
  have hf : S.subtype.comp f = MonoidHom.id _ :=
    hom_ext (by ext; simp) (by simp)
  show motive (MonoidHom.id _ x)
  rw [← hf]
  exact (f x).2

variable (A B φ)

def toSubgroup (u : ℤˣ) : Subgroup G :=
  if u = 1 then A else B

@[simp]
theorem toSubgroup_one : toSubgroup A B 1 = A := rfl

@[simp]
theorem toSubgroup_neg_one : toSubgroup A B (-1) = B := rfl

variable {A B}

def toSubgroupEquiv (u : ℤˣ) : toSubgroup A B u ≃* toSubgroup A B (-u) :=
  if hu : u = 1 then hu ▸ φ else by
    convert φ.symm <;>
    cases Int.units_eq_one_or u <;> simp_all

@[simp]
theorem toSubgroupEquiv_one : toSubgroupEquiv φ 1 = φ := rfl

@[simp]
theorem toSubgroupEquiv_neg_one : toSubgroupEquiv φ (-1) = φ.symm := rfl

@[simp]
theorem toSubgroupEquiv_neg_apply (u : ℤˣ) (a : toSubgroup A B u):
    (toSubgroupEquiv φ (-u) (toSubgroupEquiv φ u a) : G) = a := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · simp only [toSubgroup_neg_one, toSubgroupEquiv_neg_one, SetLike.coe_eq_coe]
    exact φ.apply_symm_apply a

namespace NormalWord

variable (G A B)
structure TransversalPair : Type _ :=
  /-- The transversal of each subgroup -/
  ( set : ℤˣ → Set G )
  /-- The chosen element of the subgroup itself is the identity -/
  ( one_mem : ∀u, 1 ∈ set u )
  /-- We have exactly one element of each coset of the subgroup -/
  ( compl : ∀ u, IsComplement (toSubgroup A B u : Subgroup G) (set u) )

instance TransversalPair.nonempty : Nonempty (TransversalPair G A B) := by
  have := fun u => exists_right_transversal (H := toSubgroup A B u) (1 : G)
  simp only [Classical.skolem] at this
  rcases this with ⟨t, ht⟩
  apply Nonempty.intro
  exact
    { set := t
      one_mem := fun i => (ht i).2
      compl := fun i => (ht i).1 }

variable {G A B}

structure _root_.HNNExtension.NormalWord (d : TransversalPair G A B) : Type _ :=
  ( left : G )
  ( toList : List (ℤˣ × G) )
  ( mem_set : ∀ (u : ℤˣ) (g : G), (u, g) ∈ toList → g ∈ d.set u )
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
def cons (g : G) (u : ℤˣ) (w : NormalWord d) (h1 : w.left ∈ d.set u)
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
    (cons : ∀ (g : G) (u : ℤˣ) (w : NormalWord d) (h1 : w.left ∈ d.set u)
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
    (cons : ∀ (g : G) (u : ℤˣ) (w : NormalWord d) (h1 : w.left ∈ d.set u)
      (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?, w.left = 1 → u = u'),
      motive w → motive (cons g u w h1 h2)) :
    consRecOn (.ofGroup g) ofGroup cons = ofGroup g := rfl

@[simp]
theorem consRecOn_cons {motive : NormalWord d → Sort*}
    (g : G) (u : ℤˣ) (w : NormalWord d) (h1 : w.left ∈ d.set u)
    (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?, w.left = 1 → u = u')
    (ofGroup : ∀g, motive (ofGroup g))
    (cons : ∀ (g : G) (u : ℤˣ) (w : NormalWord d) (h1 : w.left ∈ d.set u)
      (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?, w.left = 1 → u = u'),
      motive w → motive (cons g u w h1 h2)) :
    consRecOn (.cons g u w h1 h2) ofGroup cons = cons g u w h1 h2
      (consRecOn w ofGroup cons) := rfl

@[simp]
theorem smul_cons (g₁ g₂ : G) (u : ℤˣ) (w : NormalWord d) (h1 : w.left ∈ d.set u)
    (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?, w.left = 1 → u = u') :
    g₁ • cons g₂ u w h1 h2 = cons (g₁ * g₂) u w h1 h2 :=
  rfl

@[simp]
theorem smul_ofGroup (g₁ g₂ : G) :
    g₁ • (ofGroup g₂ : NormalWord d) = ofGroup (g₁ * g₂) := rfl

variable (d)
noncomputable def unitSMulGroup (u : ℤˣ) (g : G) :
    (toSubgroup A B (-u)) × d.set u :=
  let g' := (d.compl u).equiv g
  (toSubgroupEquiv φ u g'.1, g'.2)

theorem unitSMulGroup_snd (u : ℤˣ) (g : G) :
    (unitSMulGroup φ d u g).2 = ((d.compl u).equiv g).2 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rfl

variable {d} [DecidableEq G]

def Cancels (u : ℤˣ) (w : NormalWord d) : Prop :=
  (w.left ∈ (toSubgroup A B u : Subgroup G)) ∧ w.toList.head?.map Prod.fst = some (-u)

def unitSMulWithCancel (u : ℤˣ) (w : NormalWord d) : Cancels u w → NormalWord d :=
  consRecOn w
    (by simp [Cancels, ofGroup]; tauto)
    (fun g u' w h1 h2 _ can =>
      (toSubgroupEquiv φ u ⟨g, can.1⟩ : G) • w)

noncomputable def unitSMul
    (u : ℤˣ) (w : NormalWord d) : NormalWord d :=
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

theorem not_cancels_of_cons_hyps (u : ℤˣ) (w : NormalWord d)
    (h1 : w.left ∈ d.set u)
    (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?, w.left = 1 → u = u') :
    ¬ Cancels u w := by
  simp only [Cancels, Option.map_eq_some', Prod.exists,
    exists_and_right, exists_eq_right, not_and, not_exists]
  intro hw x hx
  rw [hx] at h2
  have hw : w.left = 1 := by
    simpa using congr_arg Prod.fst
      (((d.compl u).existsUnique w.left).unique
      (y₁ := (⟨w.left, hw⟩, ⟨1, d.one_mem u⟩))
      (y₂ := (1, ⟨w.left, h1⟩)) (by simp) (by simp))
  simpa [Units.ext_iff, eq_neg_iff_add_eq_zero] using h2 (-u) rfl hw

theorem unitSMul_cancels_iff (u : ℤˣ) (w : NormalWord d) :
    Cancels (-u) (unitSMul φ u w) ↔ ¬ Cancels u w := by
  by_cases h : Cancels u w
  · simp only [unitSMul, dif_pos trivial, h, iff_false]
    induction w using consRecOn with
    | ofGroup => simp [Cancels, unitSMulWithCancel]
    | cons g u' w h1 h2 _ =>
      intro hc
      apply not_cancels_of_cons_hyps _ _ h1 h2
      simp only [Cancels, cons_left, cons_toList, List.head?_cons,
        Option.map_some', Option.some.injEq] at h
      cases h.2
      simpa [Cancels, unitSMulWithCancel,
        Subgroup.mul_mem_cancel_left] using hc
  · simp only [unitSMul, dif_neg h]
    simpa [Cancels] using h

theorem unitSMul_neg (u : ℤˣ) (w : NormalWord d) :
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

@[simps]
noncomputable def unitSMulEquiv : NormalWord d ≃ NormalWord d :=
{ toFun := unitSMul φ 1
  invFun := unitSMul φ (-1),
  left_inv := fun _ => by rw [unitSMul_neg]
  right_inv := fun w => by convert unitSMul_neg _ _ w; simp }

theorem unitSMul_one_group_smul (g : A) (w : NormalWord d) :
    unitSMul φ 1 ((g : G) • w) = (φ g : G) • (unitSMul φ 1 w) := by
  unfold unitSMul
  have : Cancels 1 ((g : G) • w) ↔ Cancels 1 w := by
    simp [Cancels, Subgroup.mul_mem_cancel_left]
  by_cases hcan : Cancels 1 w
  · simp [unitSMulWithCancel, dif_pos (this.2 hcan), dif_pos hcan]
    cases w using consRecOn
    · simp [Cancels] at hcan
    · simp only [smul_cons, consRecOn_cons, mul_smul]
      rw [← mul_smul, ← Subgroup.coe_mul, ← map_mul φ]
      rfl
  · rw [dif_neg (mt this.1 hcan), dif_neg hcan]
    simp [← mul_smul, mul_assoc, unitSMulGroup]

noncomputable instance : MulAction (HNNExtension G A B φ) (NormalWord d) :=
  MulAction.ofEndHom <| (MulAction.toEndHom (M := Equiv.Perm (NormalWord d))).comp
    (HNNExtension.lift (MulAction.toPermHom _ _) (unitSMulEquiv φ) <| by
      intro a
      ext : 1
      simp [unitSMul_one_group_smul])

def prod (w : NormalWord d) : HNNExtension G A B φ :=
  of w.left * (w.toList.map (fun x => t ^ (x.1 : ℤ) * of x.2)).prod

@[simp]
theorem prod_group_smul (g : G) (w : NormalWord d) :
    (g • w).prod φ = of g * (w.prod φ) := by
  simp [prod, smul_def, mul_assoc]

theorem of_smul_eq_smul (g : G) (w : NormalWord d) :
    (of g : HNNExtension G A B φ) • w = g • w := by
  simp [instHSMul, SMul.smul, MulAction.toEndHom]

theorem t_smul_eq_unitsSMul (w : NormalWord d) :
    (t : HNNExtension G A B φ) • w = unitSMul φ 1 w := by
  simp [instHSMul, SMul.smul, MulAction.toEndHom]

theorem t_pow_smul_eq_unitsSMul (u : ℤˣ) (w : NormalWord d) :
    (t ^ (u : ℤ) : HNNExtension G A B φ) • w = unitSMul φ u w := by
  simp [instHSMul, SMul.smul, MulAction.toEndHom]
  rcases Int.units_eq_one_or u with (rfl | rfl) <;> simp [Equiv.Perm.inv_def]

@[simp]
theorem prod_cons (g : G) (u : ℤˣ) (w : NormalWord d) (h1 : w.left ∈ d.set u)
    (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?, w.left = 1 → u = u') :
    (cons g u w h1 h2).prod φ = of g * (t ^ (u : ℤ) * w.prod φ) := by
  simp [prod, cons, smul_def, mul_assoc]

theorem prod_unitsSMul (u : ℤˣ) (w : NormalWord d) :
    (unitSMul φ u w).prod φ = (t^(u : ℤ) * w.prod φ : HNNExtension G A B φ) := by
  rw [unitSMul]
  split_ifs with hcan
  · cases w using consRecOn
    · simp [Cancels] at hcan
    · cases hcan.2
      simp [unitSMulWithCancel]
      rcases Int.units_eq_one_or u with (rfl | rfl)
      · simp [equiv_eq_conj, mul_assoc]
      · simp [equiv_symm_eq_conj, mul_assoc]
  · simp [unitSMulGroup]
    rcases Int.units_eq_one_or u with (rfl | rfl)
    · simp [equiv_eq_conj, mul_assoc, (d.compl _).equiv_snd_eq_inv_mul]
    · simp [equiv_symm_eq_conj, mul_assoc, (d.compl _).equiv_snd_eq_inv_mul]

@[simp]
theorem prod_empty : (empty : NormalWord d).prod φ = 1 := by
  simp [prod]

@[simp]
theorem prod_smul (g : HNNExtension G A B φ) (w : NormalWord d) :
    (g • w).prod φ = g * w.prod φ := by
  induction g using induction_on generalizing w with
  | of => simp [of_smul_eq_smul]
  | t => simp [t_smul_eq_unitsSMul, prod_unitsSMul, mul_assoc]
  | mul => simp_all [mul_smul, mul_assoc]
  | inv x ih =>
    apply (mul_right_inj x).1
    rw [← ih]
    simp

@[simp]
theorem prod_smul_empty (w : NormalWord d) :
    (w.prod φ) • empty = w := by
  induction w using consRecOn with
  | ofGroup => simp [ofGroup, prod, of_smul_eq_smul, smul_def]
  | cons g u w h1 h2 ih =>
    rw [prod_cons, ← mul_assoc, mul_smul, ih, mul_smul, t_pow_smul_eq_unitsSMul,
      of_smul_eq_smul, unitSMul]
    rw [dif_neg (not_cancels_of_cons_hyps u w h1 h2)]
    have := not_cancels_of_cons_hyps u w h1 h2
    simp [unitSMulGroup, (d.compl u).equiv_snd_eq_inv_mul, mul_assoc,
      (d.compl _).equiv_fst_eq_one_of_mem_of_one_mem (one_mem _) h1]
    ext <;> simp

variable (d)
noncomputable def equiv : HNNExtension G A B φ ≃ NormalWord d :=
  { toFun := fun g => g • empty,
    invFun := fun w => w.prod φ,
    left_inv := fun g => by simp [prod_smul]
    right_inv := fun w => by simp }

theorem prod_injective : Injective
    (prod φ : NormalWord d → HNNExtension G A B φ) :=
  (equiv φ d).symm.injective

instance : FaithfulSMul (HNNExtension G A B φ) (NormalWord d) :=
  ⟨fun h => by simpa using congr_arg (prod φ) (h empty)⟩

end NormalWord

open NormalWord

theorem of_injective : Function.Injective (of : G → HNNExtension G A B φ) := by
  rcases TransversalPair.nonempty G A B with ⟨d⟩
  refine Function.Injective.of_comp
    (f := ((. • .) : HNNExtension G A B φ → NormalWord d → NormalWord d)) ?_
  intros _ _ h
  exact eq_of_smul_eq_smul (fun w : NormalWord d =>
    by simp_all [Function.funext_iff, of_smul_eq_smul])

variable (G A B)
structure ReducedWord : Type _ :=
  ( left : G )
  ( toList : List (ℤˣ × G) )
  ( eq_one_of_mem : ∀ (u : ℤˣ) (g : G), (u, g) ∈ toList → g ∈ toSubgroup A B u → g = 1 )
  ( chain : toList.Chain' (fun a b => a.2 = 1 → a.1 = b.1) )

namespace ReducedWord

@[simps]
def empty : ReducedWord G A B :=
  { left := 1
    toList := []
    eq_one_of_mem := by simp
    chain := List.chain'_nil }

variable {G A B}
def prod : ReducedWord G A B → HNNExtension G A B φ :=
  fun w => of w.left * (w.toList.map (fun x => t ^ (x.1 : ℤ) * of x.2)).prod

set_option pp.proofs.withType false
theorem exists_normalWord_prod_eq
    (d : TransversalPair G A B) (w : ReducedWord G A B) :
    ∃ w' : NormalWord d, w'.prod φ = w.prod φ ∧
      w'.toList.map Prod.fst = w.toList.map Prod.fst ∧
      ∀ u ∈ w.toList.head?.map Prod.fst,
      w'.left⁻¹ * w.left ∈ toSubgroup A B (-u) := by
  suffices : ∀ w : ReducedWord G A B,
      w.left = 1 → ∃ w' : NormalWord d, w'.prod φ = w.prod φ ∧
      w'.toList.map Prod.fst = w.toList.map Prod.fst ∧
      ∀ u ∈ w.toList.head?.map Prod.fst,
      w'.left ∈ toSubgroup A B (-u)
  · by_cases hw1 : w.left = 1
    · simp only [hw1, inv_mem_iff, mul_one]
      exact this w hw1
    · rcases  this ⟨1, w.toList, w.eq_one_of_mem, w.chain⟩ rfl with ⟨w', hw'⟩
      exact ⟨w.left • w', by
        simpa [prod, NormalWord.prod, mul_assoc] using hw'⟩
  intro w hw1
  rcases w with ⟨g, l, eq_one_of_mem, chain⟩
  dsimp at hw1; subst hw1
  induction l with
  | nil =>
    exact
      ⟨{ left := 1
         toList := []
         mem_set := by simp
         chain := List.chain'_nil }, by simp [prod, NormalWord.prod]⟩
  | cons a l ih =>
    rcases ih (fun _ _ h => eq_one_of_mem _ _ (List.mem_cons_of_mem _ h))
       (List.chain'_cons'.1 chain).2 with ⟨w', hw'1, hw'2, hw'3⟩
    clear ih
    refine ⟨(t^(a.1 : ℤ) * of a.2 : HNNExtension G A B φ) • w', ?_, ?_⟩
    · rw [prod_smul, hw'1]
      simp [ReducedWord.prod]
    · have : ¬ Cancels a.1 (a.2 • w') := by
        simp only [Cancels, smul_left, smul_toList, Option.map_eq_some',
          Prod.exists, exists_and_right, exists_eq_right, not_and, not_exists]
        intro hS x hx
        have hx' := congr_arg (Option.map Prod.fst) hx
        rw [← List.head?_map, hw'2, List.head?_map, Option.map_some'] at hx'
        have : w'.left ∈ toSubgroup A B a.fst := by
          simpa using hw'3 _ hx'
        rw [mul_mem_cancel_right this] at hS
        have : a.2 = 1 := eq_one_of_mem a.1 a.2 (List.mem_cons_self _ _) hS
        have : a.fst = -a.fst := by
          have hl : l ≠ [] := by rintro rfl; simp_all
          have : a.fst = (l.head hl).fst := (List.chain'_cons'.1 chain).1 (l.head hl)
            (List.head?_eq_head _ _) this
          rwa [List.head?_eq_head _ hl, Option.map_some', ← this, Option.some_inj] at hx'
        simp [Units.ext_iff, eq_neg_iff_add_eq_zero] at this
      erw [List.map_cons, mul_smul, of_smul_eq_smul, NormalWord.smul_def,
        t_pow_smul_eq_unitsSMul, unitSMul, dif_neg this, ← hw'2]
      simp [mul_assoc, unitSMulGroup, (d.compl _).equiv_snd_eq_one_iff_mem]

theorem map_fst_eq_and_of_prod_eq {w₁ w₂ : ReducedWord G A B}
    (hprod : w₁.prod φ = w₂.prod φ) :
    w₁.toList.map Prod.fst = w₂.toList.map Prod.fst ∧
     ∀ u ∈ w₁.toList.head?.map Prod.fst,
      w₁.left⁻¹ * w₂.left ∈ toSubgroup A B (-u) := by
  rcases TransversalPair.nonempty G A B with ⟨d⟩
  rcases exists_normalWord_prod_eq φ d w₁ with ⟨w₁', hw₁'1, hw₁'2, hw₁'3⟩
  rcases exists_normalWord_prod_eq φ d w₂ with ⟨w₂', hw₂'1, hw₂'2, hw₂'3⟩
  have : w₁' = w₂' :=
    NormalWord.prod_injective φ d (by rw [hw₁'1, hw₂'1, hprod])
  subst this
  refine ⟨by rw [← hw₁'2, hw₂'2], ?_⟩
  simp only [← leftCoset_eq_iff] at *
  intro u hu
  rw [← hw₁'3 _ hu, ← hw₂'3 _]
  rwa [← List.head?_map, ← hw₂'2, hw₁'2, List.head?_map]

theorem toList_eq_nil_of_mem_of_range (w : ReducedWord G A B)
    (hw : w.prod φ ∈ (of.range : Subgroup (HNNExtension G A B φ))) :
    w.toList = [] := by
  rcases hw with ⟨g, hg⟩
  let w' : ReducedWord G A B := { empty G A B with left := g }
  have : w.prod φ = w'.prod φ := by simp [prod, hg]
  simpa using (map_fst_eq_and_of_prod_eq φ this).1

end ReducedWord

end HNNExtension
