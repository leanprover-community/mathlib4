/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.GroupTheory.SpecificGroups.CoprodI
import Mathlib.GroupTheory.SpecificGroups.Coprod
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.GroupTheory.Complement

open Monoid CoprodI Subgroup Coprod Function

variable {ι : Type*} {G : ι → Type*} {H : Type*} {K : Type*} [Monoid K]

def PushoutI.con [∀ i, Monoid (G i)] [Monoid H] (φ : ∀ i, H →* G i) :
    Con (Coprod (CoprodI G) H) :=
  conGen (fun x y : Coprod (CoprodI G) H =>
    ∃ i x', x = inl (of (φ i x')) ∧ y = inr x')

def PushoutI [∀ i, Monoid (G i)] [Monoid H] (φ : ∀ i, H →* G i) : Type _ :=
  (PushoutI.con φ).Quotient

namespace PushoutI

section Monoid

variable [∀ i, Monoid (G i)] [Monoid H] {φ : ∀ i, H →* G i}

instance monoid : Monoid (PushoutI φ) := by
  delta PushoutI; infer_instance

def of (i : ι) : G i →* PushoutI φ :=
  (Con.mk' _).comp <| inl.comp CoprodI.of

def base : H →* PushoutI φ :=
  (Con.mk' _).comp inr

theorem of_comp_eq_base (i : ι) : (of i).comp (φ i) = (base (φ := φ)) := by
  ext x
  apply (Con.eq _).2
  refine ConGen.Rel.of _ _ ?_
  simp only [MonoidHom.comp_apply, Set.mem_iUnion, Set.mem_range]
  exact ⟨_, _, rfl, rfl⟩

theorem of_apply_eq_base (i : ι) (x : H) : of i (φ i x) = base (φ := φ) x := by
  rw [← MonoidHom.comp_apply, of_comp_eq_base]

def lift (f : ∀ i, G i →* K) (k : H →* K)
    (hf : ∀ i, (f i).comp (φ i) = k) :
    PushoutI φ →* K :=
  Con.lift _ (Coprod.lift (CoprodI.lift f) k) <| by
    apply Con.conGen_le <| fun x y => ?_
    rintro ⟨i, x', rfl, rfl⟩
    simp only [FunLike.ext_iff, MonoidHom.coe_comp, comp_apply] at hf
    simp [hf]

@[simp]
theorem lift_of (f : ∀ i, G i →* K) (k : H →* K)
    (hf : ∀ i, (f i).comp (φ i) = k)
    {i : ι} (g : G i) : (lift f k hf) (of i g : PushoutI φ) = f i g := by
  delta PushoutI lift of
  simp only [MonoidHom.coe_comp, Con.coe_mk', comp_apply, Con.lift_coe, lift_inl, CoprodI.lift_of]

@[simp]
theorem lift_base (f : ∀ i, G i →* K) (k : H →* K)
    (hf : ∀ i, (f i).comp (φ i) = k)
    (g : H) : (lift f k hf) (base g : PushoutI φ) = k g := by
  delta PushoutI lift base
  simp only [MonoidHom.coe_comp, Con.coe_mk', comp_apply, Con.lift_coe, lift_inr]

@[ext 1199]
theorem hom_ext {f g : PushoutI φ →* K}
    (h : ∀ i, f.comp (of i : G i →* _) = g.comp (of i : G i →* _))
    (hbase : f.comp base = g.comp base) : f = g :=
  (MonoidHom.cancel_right Con.mk'_surjective).mp <|
    Coprod.ext_hom _ _
      (CoprodI.ext_hom _ _ h)
      hbase

@[ext high]
theorem hom_ext_nonempty [hn : Nonempty ι]
    {f g : PushoutI φ →* K}
    (h : ∀ i, f.comp (of i : G i →* _) = g.comp (of i : G i →* _)) : f = g :=
  hom_ext h <| by
    cases hn with
    | intro i =>
      ext
      rw [← of_comp_eq_base i, ← MonoidHom.comp_assoc, h, MonoidHom.comp_assoc]

def ofCoprodI : CoprodI G →* PushoutI φ :=
  CoprodI.lift of

@[simp]
theorem ofCoprodI_of (i : ι) (g : G i) :
    (ofCoprodI (CoprodI.of g) : PushoutI φ) = of i g := by
  simp [ofCoprodI]

theorem induction_on {motive : PushoutI φ → Prop}
    (x : PushoutI φ)
    (of  : ∀ (i : ι) (g : G i), motive (of i g))
    (base : ∀ h, motive (base h))
    (mul : ∀ x y, motive x → motive y → motive (x * y)) : motive x := by
  delta PushoutI PushoutI.of PushoutI.base at *
  induction x using Con.induction_on with
  | H x =>
    induction x using Coprod.induction_on with
    | h_inl g =>
      induction g using CoprodI.induction_on with
      | h_of i g => exact of i g
      | h_mul x y ihx ihy =>
        rw [map_mul]
        exact mul _ _ ihx ihy
      | h_one => simpa using base 1
    | h_inr h => exact base h
    | h_mul x y ihx ihy => exact mul _ _ ihx ihy

end Monoid

variable [∀ i, Group (G i)] [Group H] {φ : ∀ i, H →* G i}

instance : Group (PushoutI φ) :=
  { Con.group (PushoutI.con φ) with
    toMonoid := PushoutI.monoid }

namespace NormalWord

-- open Coset

-- variable (φ)

-- noncomputable def normalizeSingle {i : ι} (g : G i) : H × G i :=
--   letI := Classical.propDecidable (g ∈ (φ i).range)
--   if hg : g ∈ (φ i).range
--   then ⟨Classical.choose hg, 1⟩
--   else
--     let s : Set (G i) := rightCoset (φ i).range g
--     have hs : s.Nonempty := ⟨g, mem_own_rightCoset _ _⟩
--     let g' := Classical.choose hs
--     let h' := Classical.choose (Classical.choose_spec (Classical.choose_spec hs)).1
--     ⟨h'⁻¹, g'⟩

-- theorem normalizeSingle_fst_mul_normalizeSingle_snd {i : ι} (g : G i) :
--     φ i (normalizeSingle φ g).1 * (normalizeSingle φ g).2 = g := by
--   let s : Set (G i) := rightCoset (φ i).range g
--   have hs : s.Nonempty := ⟨g, mem_own_rightCoset _ _⟩
--   dsimp [normalizeSingle]
--   split_ifs with hg
--   · simp [Classical.choose_spec hg]
--   · simp only [normalizeSingle, MonoidHom.coe_range, Set.mem_range, map_inv,
--       Eq.ndrec, id_eq]
--     rw [Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hs)).1,
--       inv_mul_eq_iff_eq_mul]
--     have := Classical.choose_spec (Classical.choose_spec hs)
--     dsimp at this
--     rw [this.2]

-- theorem normalizeSingle_fst_eq {i : ι} (g : G i) :
--     φ i (normalizeSingle φ g).1 = g * (normalizeSingle φ g).2⁻¹ :=
--   eq_mul_inv_iff_mul_eq.2 (normalizeSingle_fst_mul_normalizeSingle_snd _ _)

-- theorem normalizeSingle_snd_eq_of_rightCosetEquivalence {i : ι} {g₁ g₂ : G i}
--     (h : RightCosetEquivalence (φ i).range g₁ g₂) :
--     (normalizeSingle φ g₁).2 = (normalizeSingle φ g₂).2 := by
--   simp [normalizeSingle]
--   by_cases hg₁ : g₁ ∈ (φ i).range
--   · have hg₂ : g₂ ∈ (φ i).range := by
--       rwa [RightCosetEquivalence, rightCoset_eq_iff, mul_mem_cancel_right
--         (inv_mem hg₁)] at h
--     rw [dif_pos hg₁, dif_pos hg₂]
--   · have hg₂ : g₂ ∉ (φ i).range := by
--       intro hg₂
--       rw [RightCosetEquivalence, rightCoset_eq_iff, mul_mem_cancel_left hg₂,
--         inv_mem_iff (x := g₁)] at h
--       exact hg₁ h
--     rw [dif_neg hg₁, dif_neg hg₂]
--     dsimp
--     congr

-- theorem rightCosetEquivalence_normalizeSingle_snd {i : ι} (g : G i) :
--     RightCosetEquivalence (φ i).range g (normalizeSingle φ g).2 := by
--   dsimp only [normalizeSingle]
--   split_ifs with hg
--   · rwa [RightCosetEquivalence, rightCoset_eq_iff, _root_.one_mul,
--       inv_mem_iff (x := g)]
--   · let s : Set (G i) := rightCoset (φ i).range g
--     have hs : s.Nonempty := ⟨g, mem_own_rightCoset _ _⟩
--     erw [RightCosetEquivalence, rightCoset_eq_iff,
--       ← mem_rightCoset_iff (s := (φ i).range) g]
--     exact Classical.choose_spec hs

-- @[simp]
-- theorem normalizeSingle_snd_normalize_single_snd {i : ι} {g : G i} :
--     (normalizeSingle φ (normalizeSingle φ g).2).2 = (normalizeSingle φ g).2 :=
--   normalizeSingle_snd_eq_of_rightCosetEquivalence _
--     (rightCosetEquivalence_normalizeSingle_snd _ _).symm

-- variable {φ} (hφ : ∀ _i, Function.Injective (φ _i))

-- theorem normalizeSingle_mul {i : ι} (h : H) (g : G i) :
--     normalizeSingle φ (φ i h * g) = ⟨h * (normalizeSingle φ g).1,
--       (normalizeSingle φ g).2⟩ := by
--   have : (normalizeSingle φ (φ i h * g)).2 = (normalizeSingle φ g).2 :=
--     normalizeSingle_snd_eq_of_rightCosetEquivalence _
--       ((rightCoset_eq_iff _).2 (by simp))
--   ext
--   · apply hφ _
--     erw [← mul_left_inj ((normalizeSingle φ (φ i h * g)).2),
--       normalizeSingle_fst_mul_normalizeSingle_snd, this,
--       map_mul, mul_assoc, normalizeSingle_fst_mul_normalizeSingle_snd]
--   · exact this

-- theorem normalizeSingle_app {i : ι} (h : H) :
--     (normalizeSingle φ (φ i h)) = (h, 1)  := by
--   rw [normalizeSingle, dif_pos (MonoidHom.mem_range.2 ⟨_, rfl⟩)]
--   simp only [Prod.mk.injEq, and_true]
--   apply hφ i
--   rw [Classical.choose_spec (MonoidHom.mem_range.2 ⟨_, rfl⟩)]

-- @[simp]
-- theorem normalizeSingle_one {i : ι} :
--     (normalizeSingle (i := i) φ 1) = (1, 1)  := by
--   have h1 : 1 ∈ (φ i).range := one_mem  _
--   rw [normalizeSingle, dif_pos (one_mem _)]
--   simp only [Prod.mk.injEq, and_true]
--   apply hφ i
--   rw [Classical.choose_spec h1, map_one]

-- theorem mem_range_iff_normalizeSingle_snd_eq_one {i : ι} (g : G i) :
--     (normalizeSingle φ g).snd = 1 ↔ g ∈ (φ i).range := by
--   rw [← mul_right_inj (φ i (normalizeSingle φ g).fst),
--     normalizeSingle_fst_mul_normalizeSingle_snd, mul_one]
--   constructor
--   · intro h; rw [h]; simp
--   · rintro ⟨_, rfl⟩; simp [normalizeSingle_app hφ]

open List

variable (φ)

structure Data : Type _ where
  ( injective : ∀i, Injective (φ i) )
  ( set : ∀ i, Set (G i) )
  ( one_mem : ∀ i, 1 ∈ set i )
  ( compl : ∀ i, IsComplement (φ i).range (set i) )

theorem data_nonempty (hφ : ∀ i, Injective (φ i)) : Nonempty (Data φ) := by
  have := fun i => exists_right_transversal (H := (φ i).range) 1
  simp only [Classical.skolem] at this
  rcases this with ⟨t, ht⟩
  apply Nonempty.intro
  exact
    { injective := hφ
      set := t
      one_mem := fun i => (ht i).2
      compl := fun i => (ht i).1 }

variable {φ}

structure _root_.PushoutI.NormalWord (d : Data φ) extends CoprodI.Word G where
  left : H
  normalized : ∀ i g, ⟨i, g⟩ ∈ toList → g ∈ d.set i

/- Inspired by a similar structure in `CoprodI` -/
structure Pair (d : Data φ) (i : ι) extends CoprodI.Word.Pair G i where
  normalized : ∀ i g, ⟨i, g⟩ ∈ tail.toList → g ∈ d.set i

variable {d : Data φ}

def Pair.toNormalWord {i : ι} (p : Pair d i) : NormalWord d :=
  { toWord := p.tail,
    left := 1,
    normalized := p.normalized }

@[simps!]
def empty : NormalWord d := ⟨CoprodI.Word.empty, 1, fun i g => by simp [CoprodI.Word.empty]⟩

instance : Inhabited (NormalWord d) := ⟨NormalWord.empty⟩

instance (i : ι) : Inhabited (Pair d i) :=
  ⟨{ (empty : NormalWord d) with
      head := 1,
      fstIdx_ne := fun h => by cases h }⟩

variable [DecidableEq ι] [∀ i, DecidableEq (G i)]

@[ext]
theorem ext {w₁ w₂ : NormalWord d} (hleft : w₁.left = w₂.left)
    (hlist : w₁.toList = w₂.toList) : w₁ = w₂ := by
  rcases w₁ with ⟨⟨_, _, _⟩, _, _⟩
  rcases w₂ with ⟨⟨_, _, _⟩, _, _⟩
  simp_all

theorem ext_iff {w₁ w₂ : NormalWord d} : w₁ = w₂ ↔ w₁.left = w₂.left ∧ w₁.toList = w₂.toList :=
  ⟨fun h => by simp [h], fun ⟨h₁, h₂⟩ => ext h₁ h₂⟩

open Subgroup.IsComplement
set_option pp.proofs.withType false

theorem eq_one_of_smul_normalized (w : CoprodI.Word G) {i : ι} (h : H)
    (hw : ∀ i g, ⟨i, g⟩ ∈ w.toList → g ∈ d.set i)
    (hφw : ∀ j g, ⟨j, g⟩ ∈ (CoprodI.of (φ i h) • w).toList → g ∈ d.set j) :
    h = 1 := by
  simp only [← (d.compl _).equiv_snd_eq_self_iff_mem (one_mem _)] at hw hφw
  have hhead : ((d.compl i).equiv (Word.equivPair i w).head).2 =
      (Word.equivPair i w).head := by
    rw [Word.equivPair_head]
    dsimp only
    split_ifs with h
    · rcases h with ⟨_, rfl⟩
      exact hw _ _ (List.head_mem _)
    · rw [equiv_one (d.compl i) (one_mem _) (d.one_mem _)]
  by_contra hh1
  have := hφw i (φ i h * (Word.equivPair i w).head) ?_
  · apply hh1
    simpa [equiv_mul_left_of_mem (d.compl i) ⟨_, rfl⟩ , hhead,
      ((injective_iff_map_eq_one' _).1 (d.injective i))] using this
  . simp only [Word.mem_smul_iff, not_true, false_and, ne_eq, Option.mem_def, mul_right_inj,
      exists_eq_right', mul_right_eq_self, exists_prop, true_and, false_or]
    constructor
    · intro h
      apply_fun (d.compl i).equiv at h
      simp only [Prod.ext_iff, equiv_one (d.compl i) (one_mem _) (d.one_mem _),
        equiv_mul_left_of_mem (d.compl i) ⟨_, rfl⟩ , hhead, Subtype.ext_iff,
        Prod.ext_iff, Subgroup.coe_mul] at h
      rcases h with ⟨h₁, h₂⟩
      dsimp at h₁ h₂
      rw [h₂, equiv_one (d.compl i) (one_mem _) (d.one_mem _), mul_one,
        ((injective_iff_map_eq_one' _).1 (d.injective i))] at h₁
      contradiction
    · rw [Word.equivPair_head]
      dsimp
      split_ifs with hep
      · rcases hep with ⟨hnil, rfl⟩
        rw [head?_eq_head _ hnil]
        simp_all
      · push_neg at hep
        by_cases hw : w.toList = []
        · simp [hw, Word.fstIdx]
        · simp [head?_eq_head _ hw, Word.fstIdx, hep hw]

theorem ext_smul {w₁ w₂ : NormalWord d} (i : ι)
    (h : CoprodI.of (φ i w₁.left) • w₁.toWord =
         CoprodI.of (φ i w₂.left) • w₂.toWord) :
    w₁ = w₂ := by
  rcases w₁ with ⟨w₁, h₁, hw₁⟩
  rcases w₂ with ⟨w₂, h₂, hw₂⟩
  dsimp at *
  rw [smul_eq_iff_eq_inv_smul, ← mul_smul] at h
  subst h
  simp only [← map_inv, ← map_mul] at hw₁
  have : h₁⁻¹ * h₂ = 1 := eq_one_of_smul_normalized w₂ (h₁⁻¹ * h₂) hw₂ hw₁
  rw [inv_mul_eq_one] at this; subst this
  simp

@[simps!]
noncomputable def cons {i} (g : G i) (w : NormalWord d) (hmw : w.fstIdx ≠ some i)
    (hgr : g ∉ (φ i).range) : NormalWord d :=
  letI n := (d.compl i).equiv (g * (φ i w.left))
  letI w' := Word.cons (n.2 : G i) w.toWord hmw
    (mt (equiv_snd_eq_one_iff_mem _ (d.one_mem _)).1
      (mt (mul_mem_cancel_right (by simp)).1 hgr))
  { toWord := w'
    left := Function.surjInv (MonoidHom.rangeRestrict_surjective _) n.1
    normalized := fun i g hg => by
      simp only [Word.cons, mem_cons, Sigma.mk.inj_iff] at hg
      rcases hg with ⟨rfl, hg | hg⟩
      · simp
      · exact w.normalized _ _ (by assumption) }

noncomputable def rcons (i : ι) (p : Pair d i) : NormalWord d :=
  letI n := (d.compl i).equiv p.head
  let w := (Word.equivPair i).symm { p.toPair with head := n.2 }
  { toWord := w
    left := Function.surjInv (MonoidHom.rangeRestrict_surjective _) n.1
    normalized := fun i g hg => by
        dsimp at hg
        rw [Word.equivPair_symm, Word.mem_rcons_iff] at hg
        rcases hg with hg | ⟨_, rfl, rfl⟩
        · exact p.normalized _ _ hg
        · simp }

theorem rcons_injective {i : ι} : Function.Injective (rcons (d := d) i) := by
  rintro ⟨⟨head₁, tail₁⟩, _⟩ ⟨⟨head₂, tail₂⟩, _⟩
  simp only [rcons, NormalWord.mk.injEq, EmbeddingLike.apply_eq_iff_eq,
    Word.Pair.mk.injEq, Pair.mk.injEq, and_imp]
  intro h₁ h₂ h₃
  subst h₂
  rw [(injective_surjInv _).eq_iff] at h₃
  rw [← equiv_fst_mul_equiv_snd (d.compl i) head₁,
      ← equiv_fst_mul_equiv_snd (d.compl i) head₂,
    h₁, h₃]
  simp

@[simp]
theorem app_surjInv_rangeRestrict {M N : Type*} [Group M] [Group N] (f : M →* N)
    (x : MonoidHom.range f) :
    f (surjInv (MonoidHom.rangeRestrict_surjective f) x) = x := by
  show Subtype.val (MonoidHom.rangeRestrict f _) = x
  rw [surjInv_eq (MonoidHom.rangeRestrict_surjective f)]


noncomputable def equivPair (i) : NormalWord d ≃ Pair d i :=
  letI toFun : NormalWord d → Pair d i :=
    fun w =>
      letI p := Word.equivPair i (CoprodI.of (φ i w.left) • w.toWord)
      { toPair := p
        normalized := fun j g hg => by
          dsimp only at hg
          rw [Word.of_smul_def, ← Word.equivPair_symm, Equiv.apply_symm_apply] at hg
          dsimp at hg
          exact w.normalized _ _ (Word.mem_of_mem_equivPair_tail _ hg) }
  haveI leftInv : Function.LeftInverse (rcons i) toFun :=
    fun w => ext_smul i <| by
      simp only [rcons, Word.equivPair_symm, Word.equivPair_smul_same, app_surjInv_rangeRestrict,
        Word.equivPair_tail_eq_inv_smul, Word.rcons_eq_smul, equiv_fst_eq_mul_inv, mul_assoc,
        map_mul, map_inv, mul_smul, inv_smul_smul, smul_inv_smul]
  { toFun := toFun
    invFun := rcons i
    left_inv := leftInv
    right_inv := fun _ => rcons_injective (leftInv _) }

noncomputable instance summandAction (i : ι) : MulAction (G i) (NormalWord d) :=
  { smul := fun g w => (equivPair i).symm
      { equivPair i w with
        head := g * (equivPair i w).head }
    one_smul := fun _ => by
      dsimp [instHSMul]
      rw [one_mul]
      exact (equivPair i).symm_apply_apply _
    mul_smul := fun _ _ _ => by
      dsimp [instHSMul]
      simp [mul_assoc, Equiv.apply_symm_apply, Function.End.mul_def] }

instance baseAction : MulAction H (NormalWord d) :=
  { smul := fun h w => { w with left := h * w.left },
    one_smul := by simp [instHSMul]
    mul_smul := by simp [instHSMul, mul_assoc] }

theorem base_smul_def' (h : H) (w : NormalWord d) :
    h • w = { w with left := h * w.left } := rfl

theorem summand_smul_def' {i : ι} (g : G i) (w : NormalWord d) :
    g • w = (equivPair i).symm
      { equivPair i w with
        head := g * (equivPair i w).head } := rfl

noncomputable instance mulAction [DecidableEq ι] [∀ i, DecidableEq (G i)] :
    MulAction (PushoutI φ) (NormalWord d) :=
  MulAction.ofEndHom <|
    lift
      (fun i => MulAction.toEndHom)
      MulAction.toEndHom <| by
    intro i
    simp only [MulAction.toEndHom, FunLike.ext_iff, MonoidHom.coe_comp, MonoidHom.coe_mk,
      OneHom.coe_mk, comp_apply]
    intro h
    funext w
    apply NormalWord.ext_smul i
    simp only [summand_smul_def', equivPair, rcons, Word.equivPair_symm, Equiv.coe_fn_mk,
      Equiv.coe_fn_symm_mk, Word.equivPair_smul_same, Word.equivPair_tail_eq_inv_smul,
      Word.rcons_eq_smul, equiv_fst_eq_mul_inv, map_mul, map_inv, mul_smul, inv_smul_smul,
      smul_inv_smul, base_smul_def', app_surjInv_rangeRestrict]

theorem base_smul_def (h : H) (w : NormalWord d) :
    base (φ := φ) h • w = { w with left := h * w.left } := by
  dsimp [NormalWord.mulAction, instHSMul, SMul.smul]
  rw [lift_base]
  rfl

theorem summand_smul_def {i : ι} (g : G i) (w : NormalWord d) :
    of (φ := φ) i g • w = (equivPair i).symm
      { equivPair i w with
        head := g * (equivPair i w).head } := by
  dsimp [NormalWord.mulAction, instHSMul, SMul.smul]
  rw [lift_of]
  rfl

theorem of_smul_eq_smul {i : ι} (g : G i) (w : NormalWord d) :
    of (φ := φ) i g • w = g • w := by
  rw [summand_smul_def, summand_smul_def']

theorem base_smul_eq_smul (h : H) (w : NormalWord d) :
    base (φ := φ) h • w = h • w := by
  rw [base_smul_def, base_smul_def']

@[elab_as_elim]
noncomputable def consRecOn {motive : NormalWord d → Sort _} (w : NormalWord d)
    (h_empty : motive empty)
    (h_cons : ∀ (i : ι) (g : G i) (w : NormalWord d) (hmw : w.fstIdx ≠ some i)
      (_hgn : g ∈ d.set i) (hgr : g ∉ (φ i).range) (_hw1 : w.left = 1),
      motive w →  motive (cons g w hmw hgr))
    (h_base : ∀ (h : H) (w : NormalWord d), w.left = 1 → motive w → motive
      (base (φ := φ) h • w)) : motive w := by
  rcases w with ⟨w, left, h3⟩
  convert h_base left ⟨w, 1, h3⟩ rfl ?_
  · simp [base_smul_def]
  · induction w using Word.consRecOn with
    | h_empty => exact h_empty
    | h_cons i g w h1 hg1 ih =>
      convert h_cons i g ⟨w, 1, fun _ _ h => h3 _ _ (List.mem_cons_of_mem _ h)⟩
        h1 (h3 _ _ (List.mem_cons_self _ _)) ?_ rfl
        (ih ?_)
      · ext; simp [Word.cons, cons,
          (equiv_snd_eq_self_iff_mem (d.compl i) (one_mem _)).2
          (h3 _ _ (List.mem_cons_self _ _))]
      · apply d.injective i
        simp [cons, equiv_fst_eq_mul_inv,
          (equiv_snd_eq_self_iff_mem (d.compl i) (one_mem _)).2
          (h3 _ _ (List.mem_cons_self _ _))]
      · rwa [← SetLike.mem_coe,
          ← equiv_snd_eq_one_iff_mem (d.compl i) (d.one_mem _),
          (equiv_snd_eq_self_iff_mem (d.compl i) (one_mem _)).2
          (h3 _ _ (List.mem_cons_self _ _))]

def prod (w : NormalWord d) : PushoutI φ :=
  base w.left * ofCoprodI (w.toWord).prod

theorem cons_eq_smul {i : ι} (g : G i)
    (w : NormalWord d) (hmw : w.fstIdx ≠ some i)
    (hgr : g ∉ (φ i).range) : cons g w hmw hgr = of (φ := φ) i g  • w := by
  apply ext_smul i
  simp only [cons, ne_eq, MonoidHom.coe_range, Word.cons_eq_smul, app_surjInv_rangeRestrict,
    equiv_fst_eq_mul_inv, mul_assoc, map_mul, map_inv, mul_smul, inv_smul_smul, summand_smul_def,
    equivPair, rcons, Word.equivPair_symm, Word.rcons_eq_smul, Equiv.coe_fn_mk,
    Word.equivPair_tail_eq_inv_smul, Equiv.coe_fn_symm_mk, smul_inv_smul]

@[simp]
theorem prod_summand_smul {i : ι} (g : G i) (w : NormalWord d) :
    (g • w).prod = of i g * w.prod := by
  simp only [prod, summand_smul_def', equivPair, rcons, MonoidHom.coe_range, Word.equivPair_symm,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Word.equivPair_smul_same,
    Word.equivPair_tail_eq_inv_smul, Word.rcons_eq_smul, ← of_apply_eq_base i,
    app_surjInv_rangeRestrict, equiv_fst_eq_mul_inv, mul_assoc, map_mul, map_inv, Word.prod_smul,
    ofCoprodI_of, inv_mul_cancel_left, mul_inv_cancel_left]

@[simp]
theorem prod_base_smul (h : H) (w : NormalWord d) :
    (h • w).prod = base h * w.prod := by
  simp only [base_smul_def', prod, map_mul, mul_assoc]

@[simp]
theorem prod_smul (g : PushoutI φ) (w : NormalWord d) :
    (g • w).prod = g * w.prod := by
  induction g using PushoutI.induction_on generalizing w with
  | of i g => rw [of_smul_eq_smul, prod_summand_smul]
  | base h => rw [base_smul_eq_smul, prod_base_smul]
  | mul x y ihx ihy => rw [mul_smul, ihx, ihy, mul_assoc]

@[simp]
theorem prod_empty : (empty : NormalWord d).prod = 1 := by
  simp [prod, empty]

@[simp]
theorem prod_cons {i} (g : G i) (w : NormalWord d) (hmw : w.fstIdx ≠ some i)
    (hgr : g ∉ (φ i).range) : (cons g w hmw hgr).prod = of i g * w.prod := by
  simp [prod, cons, Word.prod, List.map, ← of_apply_eq_base i, equiv_fst_eq_mul_inv, mul_assoc]

theorem prod_smul_empty (w : NormalWord d) : w.prod • empty = w := by
  induction w using consRecOn with
  | h_empty => simp
  | h_cons i g w _ _ _ _ ih =>
    rw [prod_cons, mul_smul, ih, cons_eq_smul]
  | h_base h w _ ih =>
    rw [prod_smul, mul_smul, ih]

noncomputable def equiv : PushoutI φ ≃ NormalWord d :=
  { toFun := fun g => g • .empty
    invFun := fun w => w.prod
    left_inv := fun g => by
      simp only [prod_smul, prod_empty, mul_one]
    right_inv := fun w => prod_smul_empty w }

theorem prod_injective : Function.Injective (prod : NormalWord d → PushoutI φ) := by
  letI := Classical.decEq ι
  letI := fun i => Classical.decEq (G i)
  classical exact equiv.symm.injective

instance : FaithfulSMul (PushoutI φ) (NormalWord d) :=
  ⟨fun h => by simpa using congr_arg prod (h empty)⟩

instance (i : ι) : FaithfulSMul (G i) (NormalWord d) :=
  ⟨by simp [summand_smul_def']⟩

instance : FaithfulSMul H (NormalWord d) :=
  ⟨by simp [base_smul_def']⟩

end NormalWord

open NormalWord

theorem of_injective (hφ : ∀ i, Function.Injective (φ i)) (i : ι) :
    Function.Injective (of (φ := φ) (i := i)) := by
  rcases data_nonempty φ hφ with ⟨d⟩
  let _ := Classical.decEq ι
  let _ := fun i => Classical.decEq (G i)
  refine Function.Injective.of_comp
    (f := ((. • .) : PushoutI φ → NormalWord d → NormalWord d)) ?_
  intros _ _ h
  exact eq_of_smul_eq_smul (fun w : NormalWord d =>
    by simp_all [Function.funext_iff, of_smul_eq_smul])

theorem base_injective (hφ : ∀ i, Function.Injective (φ i)) :
    Function.Injective (base (φ := φ)) := by
  rcases data_nonempty φ hφ with ⟨d⟩
  let _ := Classical.decEq ι
  let _ := fun i => Classical.decEq (G i)
  refine Function.Injective.of_comp
    (f := ((. • .) : PushoutI φ → NormalWord d → NormalWord d)) ?_
  intros _ _ h
  exact eq_of_smul_eq_smul (fun w : NormalWord d =>
    by simp_all [Function.funext_iff, base_smul_eq_smul])

section Reduced

open NormalWord

variable (φ)

def Reduced (w : Word G) : Prop :=
  ∀ g, g ∈ w.toList → g.2 ∉ (φ g.1).range

variable {φ}

theorem Reduced.exists_normalWord_prod_eq (d : Data φ) {w : Word G} (hw : Reduced φ w) :
    ∃ w' : NormalWord d, w'.prod = ofCoprodI w.prod ∧
      w'.toList.map Sigma.fst = w.toList.map Sigma.fst := by
  letI := Classical.decEq ι
  letI := fun i => Classical.decEq (G i)
  induction w using Word.consRecOn with
  | h_empty => exact ⟨empty, by simp, rfl⟩
  | h_cons i g w hIdx hg1 ih =>
    rcases ih (fun _ hg => hw _ (List.mem_cons_of_mem _ hg)) with
      ⟨w', hw'prod, hw'map⟩
    refine ⟨cons g w' ?_ ?_, ?_⟩
    · rwa [Word.fstIdx, ← List.head?_map, hw'map, List.head?_map]
    · exact hw _ (List.mem_cons_self _ _)
    · simp [hw'prod, hw'map]

theorem Reduced.eq_empty_of_mem_range (hφ : ∀ i, Injective (φ i))
    {w : Word G} (hw : Reduced φ w) :
    ofCoprodI w.prod ∈ (base (φ := φ)).range → w = .empty := by
  rcases data_nonempty φ hφ with ⟨d⟩
  rcases hw.exists_normalWord_prod_eq d with ⟨w', hw'prod, hw'map⟩
  rintro ⟨h, heq⟩
  have : (NormalWord.prod (d := d) ⟨.empty, h, by simp⟩) = base h := by
    simp [NormalWord.prod]
  rw [← hw'prod, ← this] at heq
  suffices : w'.toWord = .empty
  · simp [this, @eq_comm _ []] at hw'map
    ext
    simp [hw'map]
  · rw [← prod_injective heq]

end Reduced

theorem inf_of_range_eq_base_range (hφ : ∀ i, Injective (φ i)) {i j : ι} (hij : i ≠ j) :
    (of i).range ⊓ (of j).range = (base (φ := φ)).range :=
  le_antisymm
    (by
      intro x hx
      rcases hx with ⟨⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩
      by_contra hx
      have hx1 : x ≠ 1 := by rintro rfl; simp_all only [map_one, one_mem]
      have hg₁1 : g₁ ≠ 1 :=
        ne_of_apply_ne (of (φ := φ) i) (by simp_all)
      have hg₂1 : g₂ ≠ 1 :=
        ne_of_apply_ne (of (φ := φ) j) (by simp_all)
      have hg₁r : g₁ ∉ (φ i).range := by
        rintro ⟨y, rfl⟩
        subst hg₁
        exact hx (of_apply_eq_base (G:=G) i y ▸ MonoidHom.mem_range.2 ⟨y, rfl⟩)
      have hg₂r : g₂ ∉ (φ j).range := by
        rintro ⟨y, rfl⟩
        subst hg₂
        exact hx (of_apply_eq_base (G:=G) j y ▸ MonoidHom.mem_range.2 ⟨y, rfl⟩)
      let w : Word G := ⟨[⟨_, g₁⟩, ⟨_, g₂⁻¹⟩], by simp_all, by simp_all⟩
      have hw : Reduced φ w := by
        simp only [not_exists, ne_eq, Reduced, List.find?, List.mem_cons, List.mem_singleton,
          forall_eq_or_imp, not_false_eq_true, forall_const, forall_eq, true_and, hg₁r, hg₂r,
          List.mem_nil_iff, false_imp_iff, imp_true_iff, and_true, inv_mem_iff]
      have := hw.eq_empty_of_mem_range hφ (by
        simp only [Word.prod, List.map_cons, List.prod_cons, List.prod_nil,
          List.map_nil, map_mul, ofCoprodI_of, hg₁, hg₂, map_inv, map_one, mul_one,
          mul_inv_self, one_mem])
      simp [Word.empty] at this)
    (le_inf
      (by rw [← of_comp_eq_base i]
          rintro _ ⟨h, rfl⟩
          exact MonoidHom.mem_range.2 ⟨φ i h, rfl⟩)
      (by rw [← of_comp_eq_base j]
          rintro _ ⟨h, rfl⟩
          exact MonoidHom.mem_range.2 ⟨φ j h, rfl⟩))

end PushoutI
