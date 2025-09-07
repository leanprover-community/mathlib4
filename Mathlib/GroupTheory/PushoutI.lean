/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.Complement

/-!

## Pushouts of Monoids and Groups

This file defines wide pushouts of monoids and groups and proves some properties
of the amalgamated product of groups (i.e. the special case where all the maps
in the diagram are injective).

## Main definitions

- `Monoid.PushoutI`: the pushout of a diagram of monoids indexed by a type `ι`
- `Monoid.PushoutI.base`: the map from the amalgamating monoid to the pushout
- `Monoid.PushoutI.of`: the map from each Monoid in the family to the pushout
- `Monoid.PushoutI.lift`: the universal property used to define homomorphisms out of the pushout.

- `Monoid.PushoutI.NormalWord`: a normal form for words in the pushout
- `Monoid.PushoutI.of_injective`: if all the maps in the diagram are injective in a pushout of
groups then so is `of`
- `Monoid.PushoutI.Reduced.eq_empty_of_mem_range`: For any word `w` in the coproduct,
if `w` is reduced (i.e none its letters are in the image of the base monoid), and nonempty, then
`w` itself is not in the image of the base monoid.

## References

* The normal form theorem follows these [notes](https://webspace.maths.qmul.ac.uk/i.m.chiswell/ggt/lecture_notes/lecture2.pdf)
  from Queen Mary University

## Tags

amalgamated product, pushout, group

-/

namespace Monoid

open CoprodI Subgroup Coprod Function List

variable {ι : Type*} {G : ι → Type*} {H : Type*} {K : Type*} [Monoid K]

/-- The relation we quotient by to form the pushout -/
def PushoutI.con [∀ i, Monoid (G i)] [Monoid H] (φ : ∀ i, H →* G i) :
    Con (Coprod (CoprodI G) H) :=
  conGen (fun x y : Coprod (CoprodI G) H =>
    ∃ i x', x = inl (of (φ i x')) ∧ y = inr x')

/-- The indexed pushout of monoids, which is the pushout in the category of monoids,
or the category of groups. -/
def PushoutI [∀ i, Monoid (G i)] [Monoid H] (φ : ∀ i, H →* G i) : Type _ :=
  (PushoutI.con φ).Quotient

namespace PushoutI

section Monoid

variable [∀ i, Monoid (G i)] [Monoid H] {φ : ∀ i, H →* G i}

protected instance mul : Mul (PushoutI φ) := by
  delta PushoutI; infer_instance

protected instance one : One (PushoutI φ) := by
  delta PushoutI; infer_instance

instance monoid : Monoid (PushoutI φ) :=
  { Con.monoid _ with
    toMul := PushoutI.mul
    toOne := PushoutI.one }

/-- The map from each indexing group into the pushout -/
def of (i : ι) : G i →* PushoutI φ :=
  (Con.mk' _).comp <| inl.comp CoprodI.of

variable (φ) in
/-- The map from the base monoid into the pushout -/
def base : H →* PushoutI φ :=
  (Con.mk' _).comp inr

theorem of_comp_eq_base (i : ι) : (of i).comp (φ i) = (base φ) := by
  ext x
  apply (Con.eq _).2
  refine ConGen.Rel.of _ _ ?_
  simp only [MonoidHom.comp_apply]
  exact ⟨_, _, rfl, rfl⟩

variable (φ) in
theorem of_apply_eq_base (i : ι) (x : H) : of i (φ i x) = base φ x := by
  rw [← MonoidHom.comp_apply, of_comp_eq_base]

/-- Define a homomorphism out of the pushout of monoids be defining it on each object in the
diagram -/
def lift (f : ∀ i, G i →* K) (k : H →* K)
    (hf : ∀ i, (f i).comp (φ i) = k) :
    PushoutI φ →* K :=
  Con.lift _ (Coprod.lift (CoprodI.lift f) k) <| by
    apply Con.conGen_le fun x y => ?_
    rintro ⟨i, x', rfl, rfl⟩
    simp only [DFunLike.ext_iff, MonoidHom.coe_comp, comp_apply] at hf
    simp [hf]

@[simp]
theorem lift_of (f : ∀ i, G i →* K) (k : H →* K)
    (hf : ∀ i, (f i).comp (φ i) = k)
    {i : ι} (g : G i) : (lift f k hf) (of i g : PushoutI φ) = f i g := by
  delta PushoutI lift of
  simp only [MonoidHom.coe_comp, Con.coe_mk', comp_apply, Con.lift_coe,
    lift_apply_inl, CoprodI.lift_of]

@[simp]
theorem lift_base (f : ∀ i, G i →* K) (k : H →* K)
    (hf : ∀ i, (f i).comp (φ i) = k)
    (g : H) : (lift f k hf) (base φ g : PushoutI φ) = k g := by
  delta PushoutI lift base
  simp only [MonoidHom.coe_comp, Con.coe_mk', comp_apply, Con.lift_coe, lift_apply_inr]

-- `ext` attribute should be lower priority then `hom_ext_nonempty`
@[ext 1199]
theorem hom_ext {f g : PushoutI φ →* K}
    (h : ∀ i, f.comp (of i : G i →* _) = g.comp (of i : G i →* _))
    (hbase : f.comp (base φ) = g.comp (base φ)) : f = g :=
  (MonoidHom.cancel_right Con.mk'_surjective).mp <|
    Coprod.hom_ext
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

/-- The equivalence that is part of the universal property of the pushout. A hom out of
the pushout is just a morphism out of all groups in the pushout that satisfies a commutativity
condition. -/
@[simps]
def homEquiv :
    (PushoutI φ →* K) ≃ { f : (Π i, G i →* K) × (H →* K) // ∀ i, (f.1 i).comp (φ i) = f.2 } :=
  { toFun := fun f => ⟨(fun i => f.comp (of i), f.comp (base φ)),
      fun i => by rw [MonoidHom.comp_assoc, of_comp_eq_base]⟩
    invFun := fun f => lift f.1.1 f.1.2 f.2,
    left_inv := fun _ => hom_ext (by simp [DFunLike.ext_iff])
      (by simp [DFunLike.ext_iff])
    right_inv := fun ⟨⟨_, _⟩, _⟩ => by simp [DFunLike.ext_iff, funext_iff] }

/-- The map from the coproduct into the pushout -/
def ofCoprodI : CoprodI G →* PushoutI φ :=
  CoprodI.lift of

@[simp]
theorem ofCoprodI_of (i : ι) (g : G i) :
    (ofCoprodI (CoprodI.of g) : PushoutI φ) = of i g := by
  simp [ofCoprodI]

theorem induction_on {motive : PushoutI φ → Prop}
    (x : PushoutI φ)
    (of : ∀ (i : ι) (g : G i), motive (of i g))
    (base : ∀ h, motive (base φ h))
    (mul : ∀ x y, motive x → motive y → motive (x * y)) : motive x := by
  delta PushoutI PushoutI.of PushoutI.base at *
  induction x using Con.induction_on with
  | H x =>
    induction x using Coprod.induction_on with
    | inl g =>
      induction g using CoprodI.induction_on with
      | of i g => exact of i g
      | mul x y ihx ihy =>
        rw [map_mul]
        exact mul _ _ ihx ihy
      | one => simpa using base 1
    | inr h => exact base h
    | mul x y ihx ihy => exact mul _ _ ihx ihy

end Monoid

variable [∀ i, Group (G i)] [Group H] {φ : ∀ i, H →* G i}

instance : Group (PushoutI φ) :=
  { Con.group (PushoutI.con φ) with
    toMonoid := PushoutI.monoid }

namespace NormalWord

/-
In this section we show that there is a normal form for words in the amalgamated product. To have a
normal form, we need to pick canonical choice of element of each right coset of the base group. The
choice of element in the base group itself is `1`. Given a choice of element of each right coset,
given by the type `Transversal φ` we can find a normal form. The normal form for an element is an
element of the base group, multiplied by a word in the coproduct, where each letter in the word is
the canonical choice of element of its coset. We then show that all groups in the diagram act
faithfully on the normal form. This implies that the maps into the coproduct are injective.

We demonstrate the action is faithful using the equivalence `equivPair`. We show that `G i` acts
faithfully on `Pair d i` and that `Pair d i` is isomorphic to `NormalWord d`. Here, `d` is a
`Transversal`. A `Pair d i` is a word in the coproduct, `Coprod G`, the `tail`, and an element
of the group `G i`, the `head`. The first letter of the `tail` must not be an element of `G i`.
Note that the `head` may be `1` Every letter in the `tail` must be in the transversal given by `d`.

We then show that the equivalence between `NormalWord` and `PushoutI`, between the set of normal
words and the elements of the amalgamated product. The key to this is the theorem `prod_smul_empty`,
which says that going from `NormalWord` to `PushoutI` and back is the identity. This is proven
by induction on the word using `consRecOn`.
-/

variable (φ)

/-- The data we need to pick a normal form for words in the pushout. We need to pick a
canonical element of each coset. We also need all the maps in the diagram to be injective -/
structure Transversal : Type _ where
  /-- All maps in the diagram are injective -/
  injective : ∀ i, Injective (φ i)
  /-- The underlying set, containing exactly one element of each coset of the base group -/
  set : ∀ i, Set (G i)
  /-- The chosen element of the base group itself is the identity -/
  one_mem : ∀ i, 1 ∈ set i
  /-- We have exactly one element of each coset of the base group -/
  compl : ∀ i, IsComplement (φ i).range (set i)

theorem transversal_nonempty (hφ : ∀ i, Injective (φ i)) : Nonempty (Transversal φ) := by
  choose t ht using fun i => (φ i).range.exists_isComplement_right 1
  apply Nonempty.intro
  exact
    { injective := hφ
      set := t
      one_mem := fun i => (ht i).2
      compl := fun i => (ht i).1 }

variable {φ}

/-- The normal form for words in the pushout. Every element of the pushout is the product of an
element of the base group and a word made up of letters each of which is in the transversal. -/
structure _root_.Monoid.PushoutI.NormalWord (d : Transversal φ) extends CoprodI.Word G where
  /-- Every `NormalWord` is the product of an element of the base group and a word made up
  of letters each of which is in the transversal. `head` is that element of the base group. -/
  head : H
  /-- All letter in the word are in the transversal. -/
  normalized : ∀ i g, ⟨i, g⟩ ∈ toList → g ∈ d.set i

/--
A `Pair d i` is a word in the coproduct, `Coprod G`, the `tail`, and an element of the group `G i`,
the `head`. The first letter of the `tail` must not be an element of `G i`.
Note that the `head` may be `1` Every letter in the `tail` must be in the transversal given by `d`.
Similar to `Monoid.CoprodI.Pair` except every letter must be in the transversal
(not including the head letter). -/
structure Pair (d : Transversal φ) (i : ι) extends CoprodI.Word.Pair G i where
  /-- All letters in the word are in the transversal. -/
  normalized : ∀ i g, ⟨i, g⟩ ∈ tail.toList → g ∈ d.set i

variable {d : Transversal φ}

/-- The empty normalized word, representing the identity element of the group. -/
@[simps!]
def empty : NormalWord d := ⟨CoprodI.Word.empty, 1, fun i g => by simp [CoprodI.Word.empty]⟩

instance : Inhabited (NormalWord d) := ⟨NormalWord.empty⟩

instance (i : ι) : Inhabited (Pair d i) :=
  ⟨{ (empty : NormalWord d) with
      head := 1, tail := _,
      fstIdx_ne := fun h => by cases h }⟩

@[ext]
theorem ext {w₁ w₂ : NormalWord d} (hhead : w₁.head = w₂.head)
    (hlist : w₁.toList = w₂.toList) : w₁ = w₂ := by
  rcases w₁ with ⟨⟨_, _, _⟩, _, _⟩
  rcases w₂ with ⟨⟨_, _, _⟩, _, _⟩
  simp_all

open Subgroup.IsComplement

instance baseAction : MulAction H (NormalWord d) :=
  { smul := fun h w => { w with head := h * w.head },
    one_smul := by simp [instHSMul]
    mul_smul := by simp [instHSMul, mul_assoc] }

theorem base_smul_def' (h : H) (w : NormalWord d) :
    h • w = { w with head := h * w.head } := rfl
/-- Take the product of a normal word as an element of the `PushoutI`. We show that this is
bijective, in `NormalWord.equiv`. -/
def prod (w : NormalWord d) : PushoutI φ :=
  base φ w.head * ofCoprodI (w.toWord).prod

@[simp]
theorem prod_base_smul (h : H) (w : NormalWord d) :
    (h • w).prod = base φ h * w.prod := by
  simp only [base_smul_def', prod, map_mul, mul_assoc]

@[simp]
theorem prod_empty : (empty : NormalWord d).prod = 1 := by
  simp [prod, empty]

/-- A constructor that multiplies a `NormalWord` by an element, with condition to make
sure the underlying list does get longer. -/
@[simps!]
noncomputable def cons {i} (g : G i) (w : NormalWord d) (hmw : w.fstIdx ≠ some i)
    (hgr : g ∉ (φ i).range) : NormalWord d :=
  letI n := (d.compl i).equiv (g * (φ i w.head))
  letI w' := Word.cons (n.2 : G i) w.toWord hmw
    (mt (coe_equiv_snd_eq_one_iff_mem _ (d.one_mem _)).1
      (mt (mul_mem_cancel_right (by simp)).1 hgr))
  { toWord := w'
    head := (MonoidHom.ofInjective (d.injective i)).symm n.1
    normalized := fun i g hg => by
      simp only [w', Word.cons, mem_cons, Sigma.mk.inj_iff] at hg
      rcases hg with ⟨rfl, hg | hg⟩
      · simp
      · exact w.normalized _ _ (by assumption) }

@[simp]
theorem prod_cons {i} (g : G i) (w : NormalWord d) (hmw : w.fstIdx ≠ some i)
    (hgr : g ∉ (φ i).range) : (cons g w hmw hgr).prod = of i g * w.prod := by
  simp [prod, cons, ← of_apply_eq_base φ i, equiv_fst_eq_mul_inv, mul_assoc]

variable [DecidableEq ι] [∀ i, DecidableEq (G i)]

/-- Given a word in `CoprodI`, if every letter is in the transversal and when
we multiply by an element of the base group it still has this property,
then the element of the base group we multiplied by was one. -/
theorem eq_one_of_smul_normalized (w : CoprodI.Word G) {i : ι} (h : H)
    (hw : ∀ i g, ⟨i, g⟩ ∈ w.toList → g ∈ d.set i)
    (hφw : ∀ j g, ⟨j, g⟩ ∈ (CoprodI.of (φ i h) • w).toList → g ∈ d.set j) :
    h = 1 := by
  simp only [← (d.compl _).equiv_snd_eq_self_iff_mem (one_mem _)] at hw hφw
  have hhead : ((d.compl i).equiv (Word.equivPair i w).head).2 =
      (Word.equivPair i w).head := by
    rw [Word.equivPair_head]
    split_ifs with h
    · rcases h with ⟨_, rfl⟩
      exact hw _ _ (List.head_mem _)
    · rw [equiv_one (d.compl i) (one_mem _) (d.one_mem _)]
  by_contra hh1
  have := hφw i (φ i h * (Word.equivPair i w).head) ?_
  · apply hh1
    rw [equiv_mul_left_of_mem (d.compl i) ⟨_, rfl⟩, hhead] at this
    simpa [((injective_iff_map_eq_one' _).1 (d.injective i))] using this
  · simp only [Word.mem_smul_iff, not_true, false_and, ne_eq, Option.mem_def, mul_right_inj,
      exists_eq_right', mul_eq_left, exists_prop, true_and, false_or]
    constructor
    · intro h
      apply_fun (d.compl i).equiv at h
      simp only [Prod.ext_iff, equiv_one (d.compl i) (one_mem _) (d.one_mem _),
        equiv_mul_left_of_mem (d.compl i) ⟨_, rfl⟩ , hhead, Subtype.ext_iff,
        Prod.ext_iff] at h
      rcases h with ⟨h₁, h₂⟩
      rw [h₂, equiv_one (d.compl i) (one_mem _) (d.one_mem _)] at h₁
      erw [mul_one] at h₁
      simp only [((injective_iff_map_eq_one' _).1 (d.injective i))] at h₁
      contradiction
    · rw [Word.equivPair_head]
      dsimp
      split_ifs with hep
      · rcases hep with ⟨hnil, rfl⟩
        rw [head?_eq_head hnil]
        simp_all
      · push_neg at hep
        by_cases hw : w.toList = []
        · simp [hw, Word.fstIdx]
        · simp [head?_eq_head hw, Word.fstIdx, hep hw]

theorem ext_smul {w₁ w₂ : NormalWord d} (i : ι)
    (h : CoprodI.of (φ i w₁.head) • w₁.toWord =
         CoprodI.of (φ i w₂.head) • w₂.toWord) :
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

/-- Given a pair `(head, tail)`, we can form a word by prepending `head` to `tail`, but
putting head into normal form first, by making sure it is expressed as an element
of the base group multiplied by an element of the transversal. -/
noncomputable def rcons (i : ι) (p : Pair d i) : NormalWord d :=
  letI n := (d.compl i).equiv p.head
  let w := (Word.equivPair i).symm { p.toPair with head := n.2 }
  { toWord := w
    head := (MonoidHom.ofInjective (d.injective i)).symm n.1
    normalized := fun i g hg => by
        dsimp [w] at hg
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
  rw [← equiv_fst_mul_equiv_snd (d.compl i) head₁,
      ← equiv_fst_mul_equiv_snd (d.compl i) head₂,
    h₁, h₃]
  simp

/-- The equivalence between `NormalWord`s and pairs. We can turn a `NormalWord` into a
pair by taking the head of the `List` if it is in `G i` and multiplying it by the element of the
base group. -/
noncomputable def equivPair (i) : NormalWord d ≃ Pair d i :=
  letI toFun : NormalWord d → Pair d i :=
    fun w =>
      letI p := Word.equivPair i (CoprodI.of (φ i w.head) • w.toWord)
      { toPair := p
        normalized := fun j g hg => by
          dsimp only [p] at hg
          rw [Word.of_smul_def, ← Word.equivPair_symm, Equiv.apply_symm_apply] at hg
          dsimp at hg
          exact w.normalized _ _ (Word.mem_of_mem_equivPair_tail _ hg) }
  haveI leftInv : Function.LeftInverse (rcons i) toFun :=
    fun w => ext_smul i <| by
      simp only [toFun, rcons, Word.equivPair_symm,
        Word.equivPair_smul_same, Word.equivPair_tail_eq_inv_smul, Word.rcons_eq_smul,
        MonoidHom.apply_ofInjective_symm, equiv_fst_eq_mul_inv, mul_assoc, map_mul, map_inv,
        mul_smul, inv_smul_smul, smul_inv_smul]
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
      simp [mul_assoc, Equiv.apply_symm_apply] }

theorem summand_smul_def' {i : ι} (g : G i) (w : NormalWord d) :
    g • w = (equivPair i).symm
      { equivPair i w with
        head := g * (equivPair i w).head } := rfl

noncomputable instance mulAction : MulAction (PushoutI φ) (NormalWord d) :=
  MulAction.ofEndHom <|
    lift
      (fun _ => MulAction.toEndHom)
      MulAction.toEndHom <| by
    intro i
    simp only [MulAction.toEndHom, DFunLike.ext_iff, MonoidHom.coe_comp, MonoidHom.coe_mk,
      OneHom.coe_mk, comp_apply]
    intro h
    funext w
    apply NormalWord.ext_smul i
    simp only [summand_smul_def', equivPair, rcons, Word.equivPair_symm, Equiv.coe_fn_mk,
      Equiv.coe_fn_symm_mk, Word.equivPair_smul_same, Word.equivPair_tail_eq_inv_smul,
      Word.rcons_eq_smul, equiv_fst_eq_mul_inv, map_mul, map_inv, mul_smul, inv_smul_smul,
      smul_inv_smul, base_smul_def', MonoidHom.apply_ofInjective_symm]

theorem base_smul_def (h : H) (w : NormalWord d) :
    base φ h • w = { w with head := h * w.head } := by
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
    base φ h • w = h • w := by
  rw [base_smul_def, base_smul_def']

/-- Induction principle for `NormalWord`, that corresponds closely to inducting on
the underlying list. -/
@[elab_as_elim]
noncomputable def consRecOn {motive : NormalWord d → Sort _} (w : NormalWord d)
    (empty : motive empty)
    (cons : ∀ (i : ι) (g : G i) (w : NormalWord d) (hmw : w.fstIdx ≠ some i)
      (_hgn : g ∈ d.set i) (hgr : g ∉ (φ i).range) (_hw1 : w.head = 1),
      motive w → motive (cons g w hmw hgr))
    (base : ∀ (h : H) (w : NormalWord d), w.head = 1 → motive w → motive
      (base φ h • w)) : motive w := by
  rcases w with ⟨w, head, h3⟩
  convert base head ⟨w, 1, h3⟩ rfl ?_
  · simp [base_smul_def]
  · induction w using Word.consRecOn with
    | empty => exact empty
    | cons i g w h1 hg1 ih =>
      convert cons i g ⟨w, 1, fun _ _ h => h3 _ _ (List.mem_cons_of_mem _ h)⟩
        h1 (h3 _ _ List.mem_cons_self) ?_ rfl
        (ih ?_)
      · ext
        simp only [Word.cons, NormalWord.cons, map_one, mul_one,
          (equiv_snd_eq_self_iff_mem (d.compl i) (one_mem _)).2
          (h3 _ _ List.mem_cons_self)]
      · apply d.injective i
        simp only [NormalWord.cons, equiv_fst_eq_mul_inv, MonoidHom.apply_ofInjective_symm,
          map_one, mul_one, mul_inv_cancel, (equiv_snd_eq_self_iff_mem (d.compl i) (one_mem _)).2
          (h3 _ _ List.mem_cons_self)]
      · rwa [← SetLike.mem_coe,
          ← coe_equiv_snd_eq_one_iff_mem (d.compl i) (d.one_mem _),
          (equiv_snd_eq_self_iff_mem (d.compl i) (one_mem _)).2
          (h3 _ _ List.mem_cons_self)]


theorem cons_eq_smul {i : ι} (g : G i)
    (w : NormalWord d) (hmw : w.fstIdx ≠ some i)
    (hgr : g ∉ (φ i).range) : cons g w hmw hgr = of (φ := φ) i g  • w := by
  apply ext_smul i
  simp only [cons, Word.cons_eq_smul, MonoidHom.apply_ofInjective_symm,
    equiv_fst_eq_mul_inv, mul_assoc, map_mul, map_inv, mul_smul, inv_smul_smul, summand_smul_def,
    equivPair, rcons, Word.equivPair_symm, Word.rcons_eq_smul, Equiv.coe_fn_mk,
    Word.equivPair_tail_eq_inv_smul, Equiv.coe_fn_symm_mk, smul_inv_smul]

@[simp]
theorem prod_summand_smul {i : ι} (g : G i) (w : NormalWord d) :
    (g • w).prod = of i g * w.prod := by
  simp only [prod, summand_smul_def', equivPair, rcons, Word.equivPair_symm,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Word.equivPair_smul_same,
    Word.equivPair_tail_eq_inv_smul, Word.rcons_eq_smul, ← of_apply_eq_base φ i,
    MonoidHom.apply_ofInjective_symm, equiv_fst_eq_mul_inv, mul_assoc, map_mul, map_inv,
    Word.prod_smul, ofCoprodI_of, inv_mul_cancel_left, mul_inv_cancel_left]

@[simp]
theorem prod_smul (g : PushoutI φ) (w : NormalWord d) :
    (g • w).prod = g * w.prod := by
  induction g using PushoutI.induction_on generalizing w with
  | of i g => rw [of_smul_eq_smul, prod_summand_smul]
  | base h => rw [base_smul_eq_smul, prod_base_smul]
  | mul x y ihx ihy => rw [mul_smul, ihx, ihy, mul_assoc]

theorem prod_smul_empty (w : NormalWord d) : w.prod • empty = w := by
  induction w using consRecOn with
  | empty => simp
  | cons i g w _ _ _ _ ih =>
    rw [prod_cons, mul_smul, ih, cons_eq_smul]
  | base h w _ ih =>
    rw [prod_smul, mul_smul, ih]

/-- The equivalence between normal forms and elements of the pushout -/
noncomputable def equiv : PushoutI φ ≃ NormalWord d :=
  { toFun := fun g => g • .empty
    invFun := fun w => w.prod
    left_inv := fun g => by
      simp only [prod_smul, prod_empty, mul_one]
    right_inv := fun w => prod_smul_empty w }

theorem prod_injective {ι : Type*} {G : ι → Type*} [(i : ι) → Group (G i)] {φ : (i : ι) → H →* G i}
    {d : Transversal φ} : Function.Injective (prod : NormalWord d → PushoutI φ) := by
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

/-- All maps into the `PushoutI`, or amalgamated product of groups are injective,
provided all maps in the diagram are injective.

See also `base_injective` -/
theorem of_injective (hφ : ∀ i, Function.Injective (φ i)) (i : ι) :
    Function.Injective (of (φ := φ) i) := by
  rcases transversal_nonempty φ hφ with ⟨d⟩
  let _ := Classical.decEq ι
  let _ := fun i => Classical.decEq (G i)
  refine Function.Injective.of_comp
    (f := ((· • ·) : PushoutI φ → NormalWord d → NormalWord d)) ?_
  intros _ _ h
  exact eq_of_smul_eq_smul (fun w : NormalWord d =>
    by simp_all [funext_iff, of_smul_eq_smul])

theorem base_injective (hφ : ∀ i, Function.Injective (φ i)) :
    Function.Injective (base φ) := by
  rcases transversal_nonempty φ hφ with ⟨d⟩
  let _ := Classical.decEq ι
  let _ := fun i => Classical.decEq (G i)
  refine Function.Injective.of_comp
    (f := ((· • ·) : PushoutI φ → NormalWord d → NormalWord d)) ?_
  intros _ _ h
  exact eq_of_smul_eq_smul (fun w : NormalWord d =>
    by simp_all [funext_iff, base_smul_eq_smul])

section Reduced

variable (φ) in
/-- A word in `CoprodI` is reduced if none of its letters are in the base group. -/
def Reduced (w : Word G) : Prop :=
  ∀ g, g ∈ w.toList → g.2 ∉ (φ g.1).range

theorem Reduced.exists_normalWord_prod_eq (d : Transversal φ) {w : Word G} (hw : Reduced φ w) :
    ∃ w' : NormalWord d, w'.prod = ofCoprodI w.prod ∧
      w'.toList.map Sigma.fst = w.toList.map Sigma.fst := by
  classical
  induction w using Word.consRecOn with
  | empty => exact ⟨empty, by simp, rfl⟩
  | cons i g w hIdx hg1 ih =>
    rcases ih (fun _ hg => hw _ (List.mem_cons_of_mem _ hg)) with
      ⟨w', hw'prod, hw'map⟩
    refine ⟨cons g w' ?_ ?_, ?_⟩
    · rwa [Word.fstIdx, ← List.head?_map, hw'map, List.head?_map]
    · exact hw _ List.mem_cons_self
    · simp [hw'prod, hw'map]

/-- For any word `w` in the coproduct,
if `w` is reduced (i.e none its letters are in the image of the base monoid), and nonempty, then
`w` itself is not in the image of the base group. -/
theorem Reduced.eq_empty_of_mem_range
    (hφ : ∀ i, Injective (φ i)) {w : Word G} (hw : Reduced φ w)
    (h : ofCoprodI w.prod ∈ (base φ).range) : w = .empty := by
  rcases transversal_nonempty φ hφ with ⟨d⟩
  rcases hw.exists_normalWord_prod_eq d with ⟨w', hw'prod, hw'map⟩
  rcases h with ⟨h, heq⟩
  have : (NormalWord.prod (d := d) ⟨.empty, h, by simp⟩) = base φ h := by
    simp [NormalWord.prod]
  rw [← hw'prod, ← this] at heq
  suffices w'.toWord = .empty by
    simp [this, @eq_comm _ []] at hw'map
    ext
    simp [hw'map]
  rw [← prod_injective heq]

end Reduced

/-- The intersection of the images of the maps from any two distinct groups in the diagram
into the amalgamated product is the image of the map from the base group in the diagram. -/
theorem inf_of_range_eq_base_range
    (hφ : ∀ i, Injective (φ i)) {i j : ι} (hij : i ≠ j) :
    (of i).range ⊓ (of j).range = (base φ).range :=
  le_antisymm
    (by
      intro x ⟨⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩
      by_contra hx
      have hx1 : x ≠ 1 := by rintro rfl; simp_all only [ne_eq, one_mem, not_true_eq_false]
      have hg₁1 : g₁ ≠ 1 :=
        ne_of_apply_ne (of (φ := φ) i) (by simp_all)
      have hg₂1 : g₂ ≠ 1 :=
        ne_of_apply_ne (of (φ := φ) j) (by simp_all)
      have hg₁r : g₁ ∉ (φ i).range := by
        rintro ⟨y, rfl⟩
        subst hg₁
        exact hx (of_apply_eq_base φ i y ▸ MonoidHom.mem_range.2 ⟨y, rfl⟩)
      have hg₂r : g₂ ∉ (φ j).range := by
        rintro ⟨y, rfl⟩
        subst hg₂
        exact hx (of_apply_eq_base φ j y ▸ MonoidHom.mem_range.2 ⟨y, rfl⟩)
      let w : Word G := ⟨[⟨_, g₁⟩, ⟨_, g₂⁻¹⟩], by simp_all, by simp_all⟩
      have hw : Reduced φ w := by
        simp only [w, Reduced, List.mem_cons,
          forall_eq_or_imp, not_false_eq_true,
          hg₁r, hg₂r, List.mem_nil_iff, false_imp_iff, imp_true_iff, and_true,
          inv_mem_iff]
      have := hw.eq_empty_of_mem_range hφ (by
        simp only [w, Word.prod, List.map_cons, List.prod_cons, List.prod_nil,
          List.map_nil, map_mul, ofCoprodI_of, hg₁, hg₂, map_inv, mul_one,
          mul_inv_cancel, one_mem])
      simp [w, Word.empty] at this)
    (le_inf
      (by rw [← of_comp_eq_base i]
          rintro _ ⟨h, rfl⟩
          exact MonoidHom.mem_range.2 ⟨φ i h, rfl⟩)
      (by rw [← of_comp_eq_base j]
          rintro _ ⟨h, rfl⟩
          exact MonoidHom.mem_range.2 ⟨φ j h, rfl⟩))

end PushoutI

end Monoid
