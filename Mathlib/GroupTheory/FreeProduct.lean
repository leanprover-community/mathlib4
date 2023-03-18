/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Joachim Breitner

! This file was ported from Lean 3 source module group_theory.free_product
! leanprover-community/mathlib commit 9114ddffa023340c9ec86965e00cdd6fe26fcdf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.FreeMonoid.Basic
import Mathbin.GroupTheory.Congruence
import Mathbin.GroupTheory.IsFreeGroup
import Mathbin.Data.List.Chain
import Mathbin.SetTheory.Cardinal.Ordinal
import Mathbin.Data.Set.Pointwise.Smul

/-!
# The free product of groups or monoids

Given an `ι`-indexed family `M` of monoids, we define their free product (categorical coproduct)
`free_product M`. When `ι` and all `M i` have decidable equality, the free product bijects with the
type `word M` of reduced words. This bijection is constructed by defining an action of
`free_product M` on `word M`.

When `M i` are all groups, `free_product M` is also a group (and the coproduct in the category of
groups).

## Main definitions

- `free_product M`: the free product, defined as a quotient of a free monoid.
- `free_product.of {i} : M i →* free_product M`.
- `free_product.lift : (Π {i}, M i →* N) ≃ (free_product M →* N)`: the universal property.
- `free_product.word M`: the type of reduced words.
- `free_product.word.equiv M : free_product M ≃ word M`.
- `free_product.neword M i j`: an inductive description of non-empty words with first letter from
  `M i` and last letter from `M j`, together with an API (`singleton`, `append`, `head`, `tail`,
  `to_word`, `prod`, `inv`). Used in the proof of the Ping-Pong-lemma.
- `free_product.lift_injective_of_ping_pong`: The Ping-Pong-lemma, proving injectivity of the
  `lift`. See the documentation of that theorem for more information.

## Remarks

There are many answers to the question "what is the free product of a family `M` of monoids?", and
they are all equivalent but not obviously equivalent. We provide two answers. The first, almost
tautological answer is given by `free_product M`, which is a quotient of the type of words in the
alphabet `Σ i, M i`. It's straightforward to define and easy to prove its universal property. But
this answer is not completely satisfactory, because it's difficult to tell when two elements
`x y : free_product M` are distinct since `free_product M` is defined as a quotient.

The second, maximally efficient answer is given by `word M`. An element of `word M` is a word in the
alphabet `Σ i, M i`, where the letter `⟨i, 1⟩` doesn't occur and no adjacent letters share an index
`i`. Since we only work with reduced words, there is no need for quotienting, and it is easy to tell
when two elements are distinct. However it's not obvious that this is even a monoid!

We prove that every element of `free_product M` can be represented by a unique reduced word, i.e.
`free_product M` and `word M` are equivalent types. This means that `word M` can be given a monoid
structure, and it lets us tell when two elements of `free_product M` are distinct.

There is also a completely tautological, maximally inefficient answer given by
`algebra.category.Mon.colimits`. Whereas `free_product M` at least ensures that (any instance of)
associativity holds by reflexivity, in this answer associativity holds because of quotienting. Yet
another answer, which is constructively more satisfying, could be obtained by showing that
`free_product.rel` is confluent.

## References

[van der Waerden, *Free products of groups*][MR25465]

-/


open Set

variable {ι : Type _} (M : ∀ i : ι, Type _) [∀ i, Monoid (M i)]

/-- A relation on the free monoid on alphabet `Σ i, M i`, relating `⟨i, 1⟩` with `1` and
`⟨i, x⟩ * ⟨i, y⟩` with `⟨i, x * y⟩`. -/
inductive FreeProduct.Rel : FreeMonoid (Σi, M i) → FreeMonoid (Σi, M i) → Prop
  | of_one (i : ι) : FreeProduct.Rel (FreeMonoid.of ⟨i, 1⟩) 1
  |
  of_mul {i : ι} (x y : M i) :
    FreeProduct.Rel (FreeMonoid.of ⟨i, x⟩ * FreeMonoid.of ⟨i, y⟩) (FreeMonoid.of ⟨i, x * y⟩)
#align free_product.rel FreeProduct.Rel

/-- The free product (categorical coproduct) of an indexed family of monoids. -/
def FreeProduct : Type _ :=
  (conGen (FreeProduct.Rel M)).Quotient deriving Monoid, Inhabited
#align free_product FreeProduct

namespace FreeProduct

/-- The type of reduced words. A reduced word cannot contain a letter `1`, and no two adjacent
letters can come from the same summand. -/
@[ext]
structure Word where
  toList : List (Σi, M i)
  ne_one : ∀ l ∈ to_list, Sigma.snd l ≠ 1
  chain_ne : to_list.Chain' fun l l' => Sigma.fst l ≠ Sigma.fst l'
#align free_product.word FreeProduct.Word

variable {M}

/-- The inclusion of a summand into the free product. -/
def of {i : ι} : M i →* FreeProduct M
    where
  toFun x := Con.mk' _ (FreeMonoid.of <| Sigma.mk i x)
  map_one' := (Con.eq _).mpr (ConGen.Rel.of _ _ (FreeProduct.Rel.of_one i))
  map_mul' x y := Eq.symm <| (Con.eq _).mpr (ConGen.Rel.of _ _ (FreeProduct.Rel.of_mul x y))
#align free_product.of FreeProduct.of

theorem of_apply {i} (m : M i) : of m = Con.mk' _ (FreeMonoid.of <| Sigma.mk i m) :=
  rfl
#align free_product.of_apply FreeProduct.of_apply

variable {N : Type _} [Monoid N]

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem ext_hom (f g : FreeProduct M →* N) (h : ∀ i, f.comp (of : M i →* _) = g.comp of) : f = g :=
  (MonoidHom.cancel_right Con.mk'_surjective).mp <|
    FreeMonoid.hom_eq fun ⟨i, x⟩ => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← of_apply, ← MonoidHom.comp_apply, ←
        MonoidHom.comp_apply, h]
#align free_product.ext_hom FreeProduct.ext_hom

/-- A map out of the free product corresponds to a family of maps out of the summands. This is the
universal property of the free product, charaterizing it as a categorical coproduct. -/
@[simps symm_apply]
def lift : (∀ i, M i →* N) ≃ (FreeProduct M →* N)
    where
  toFun fi :=
    Con.lift _ (FreeMonoid.lift fun p : Σi, M i => fi p.fst p.snd) <|
      Con.conGen_le
        (by
          simp_rw [Con.rel_eq_coe, Con.ker_rel]
          rintro _ _ (i | ⟨x, y⟩)
          · change FreeMonoid.lift _ (FreeMonoid.of _) = FreeMonoid.lift _ 1
            simp only [MonoidHom.map_one, FreeMonoid.lift_eval_of]
          · change
              FreeMonoid.lift _ (FreeMonoid.of _ * FreeMonoid.of _) =
                FreeMonoid.lift _ (FreeMonoid.of _)
            simp only [MonoidHom.map_mul, FreeMonoid.lift_eval_of])
  invFun f i := f.comp of
  left_inv := by
    intro fi
    ext (i x)
    rw [MonoidHom.comp_apply, of_apply, Con.lift_mk', FreeMonoid.lift_eval_of]
  right_inv := by
    intro f
    ext (i x)
    simp only [MonoidHom.comp_apply, of_apply, Con.lift_mk', FreeMonoid.lift_eval_of]
#align free_product.lift FreeProduct.lift

@[simp]
theorem lift_of {N} [Monoid N] (fi : ∀ i, M i →* N) {i} (m : M i) : lift fi (of m) = fi i m := by
  conv_rhs => rw [← lift.symm_apply_apply fi, lift_symm_apply, MonoidHom.comp_apply]
#align free_product.lift_of FreeProduct.lift_of

@[elab_as_elim]
theorem induction_on {C : FreeProduct M → Prop} (m : FreeProduct M) (h_one : C 1)
    (h_of : ∀ (i) (m : M i), C (of m)) (h_mul : ∀ x y, C x → C y → C (x * y)) : C m :=
  by
  let S : Submonoid (FreeProduct M) := Submonoid.mk (setOf C) h_mul h_one
  convert Subtype.prop (lift (fun i => of.cod_restrict S (h_of i)) m)
  change MonoidHom.id _ m = S.subtype.comp _ m
  congr
  ext
  simp [MonoidHom.codRestrict]
#align free_product.induction_on FreeProduct.induction_on

theorem of_leftInverse [DecidableEq ι] (i : ι) :
    Function.LeftInverse (lift <| Pi.mulSingle i (MonoidHom.id (M i))) of := fun x => by
  simp only [lift_of, Pi.mulSingle_eq_same, MonoidHom.id_apply]
#align free_product.of_left_inverse FreeProduct.of_leftInverse

theorem of_injective (i : ι) : Function.Injective ⇑(of : M i →* _) := by
  classical exact (of_left_inverse i).Injective
#align free_product.of_injective FreeProduct.of_injective

theorem lift_mrange_le {N} [Monoid N] (f : ∀ i, M i →* N) {s : Submonoid N}
    (h : ∀ i, (f i).mrange ≤ s) : (lift f).mrange ≤ s :=
  by
  rintro _ ⟨x, rfl⟩
  induction' x using FreeProduct.induction_on with i x x y hx hy
  · exact s.one_mem
  · simp only [lift_of, SetLike.mem_coe]
    exact h i (Set.mem_range_self x)
  · simp only [map_mul, SetLike.mem_coe]
    exact s.mul_mem hx hy
#align free_product.lift_mrange_le FreeProduct.lift_mrange_le

theorem mrange_eq_supᵢ {N} [Monoid N] (f : ∀ i, M i →* N) : (lift f).mrange = ⨆ i, (f i).mrange :=
  by
  apply le_antisymm (lift_mrange_le f fun i => le_supᵢ _ i)
  apply supᵢ_le _
  rintro i _ ⟨x, rfl⟩
  exact ⟨of x, by simp only [lift_of]⟩
#align free_product.mrange_eq_supr FreeProduct.mrange_eq_supᵢ

section Group

variable (G : ι → Type _) [∀ i, Group (G i)]

instance : Inv (FreeProduct G)
    where inv :=
    MulOpposite.unop ∘ lift fun i => (of : G i →* _).op.comp (MulEquiv.inv' (G i)).toMonoidHom

theorem inv_def (x : FreeProduct G) :
    x⁻¹ =
      MulOpposite.unop
        (lift (fun i => (of : G i →* _).op.comp (MulEquiv.inv' (G i)).toMonoidHom) x) :=
  rfl
#align free_product.inv_def FreeProduct.inv_def

instance : Group (FreeProduct G) :=
  { FreeProduct.hasInv G, FreeProduct.monoid G with
    mul_left_inv := by
      intro m
      rw [inv_def]
      apply m.induction_on
      · rw [MonoidHom.map_one, MulOpposite.unop_one, one_mul]
      · intro i m
        change of m⁻¹ * of m = 1
        rw [← of.map_mul, mul_left_inv, of.map_one]
      · intro x y hx hy
        rw [MonoidHom.map_mul, MulOpposite.unop_mul, mul_assoc, ← mul_assoc _ x y, hx, one_mul,
          hy] }

theorem lift_range_le {N} [Group N] (f : ∀ i, G i →* N) {s : Subgroup N}
    (h : ∀ i, (f i).range ≤ s) : (lift f).range ≤ s :=
  by
  rintro _ ⟨x, rfl⟩
  induction' x using FreeProduct.induction_on with i x x y hx hy
  · exact s.one_mem
  · simp only [lift_of, SetLike.mem_coe]
    exact h i (Set.mem_range_self x)
  · simp only [map_mul, SetLike.mem_coe]
    exact s.mul_mem hx hy
#align free_product.lift_range_le FreeProduct.lift_range_le

theorem range_eq_supᵢ {N} [Group N] (f : ∀ i, G i →* N) : (lift f).range = ⨆ i, (f i).range :=
  by
  apply le_antisymm (lift_range_le _ f fun i => le_supᵢ _ i)
  apply supᵢ_le _
  rintro i _ ⟨x, rfl⟩
  exact ⟨of x, by simp only [lift_of]⟩
#align free_product.range_eq_supr FreeProduct.range_eq_supᵢ

end Group

namespace Word

/-- The empty reduced word. -/
def empty : Word M where
  toList := []
  ne_one _ := False.elim
  chain_ne := List.chain'_nil
#align free_product.word.empty FreeProduct.Word.empty

instance : Inhabited (Word M) :=
  ⟨empty⟩

/-- A reduced word determines an element of the free product, given by multiplication. -/
def prod (w : Word M) : FreeProduct M :=
  List.prod (w.toList.map fun l => of l.snd)
#align free_product.word.prod FreeProduct.Word.prod

@[simp]
theorem prod_empty : prod (empty : Word M) = 1 :=
  rfl
#align free_product.word.prod_empty FreeProduct.Word.prod_empty

/-- `fst_idx w` is `some i` if the first letter of `w` is `⟨i, m⟩` with `m : M i`. If `w` is empty
then it's `none`. -/
def fstIdx (w : Word M) : Option ι :=
  w.toList.head?.map Sigma.fst
#align free_product.word.fst_idx FreeProduct.Word.fstIdx

theorem fstIdx_ne_iff {w : Word M} {i} :
    fstIdx w ≠ some i ↔ ∀ l ∈ w.toList.head?, i ≠ Sigma.fst l :=
  not_iff_not.mp <| by simp [fst_idx]
#align free_product.word.fst_idx_ne_iff FreeProduct.Word.fstIdx_ne_iff

variable (M)

/-- Given an index `i : ι`, `pair M i` is the type of pairs `(head, tail)` where `head : M i` and
`tail : word M`, subject to the constraint that first letter of `tail` can't be `⟨i, m⟩`.
By prepending `head` to `tail`, one obtains a new word. We'll show that any word can be uniquely
obtained in this way. -/
@[ext]
structure Pair (i : ι) where
  headI : M i
  tail : Word M
  fstIdx_ne : fstIdx tail ≠ some i
#align free_product.word.pair FreeProduct.Word.Pair

instance (i : ι) : Inhabited (Pair M i) :=
  ⟨⟨1, empty, by tauto⟩⟩

variable {M}

variable [∀ i, DecidableEq (M i)]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Given a pair `(head, tail)`, we can form a word by prepending `head` to `tail`, except if `head`
is `1 : M i` then we have to just return `word` since we need the result to be reduced. -/
def rcons {i} (p : Pair M i) : Word M :=
  if h : p.headI = 1 then p.tail
  else
    { toList := ⟨i, p.headI⟩::p.tail.toList
      ne_one := by
        rintro l (rfl | hl)
        exact h
        exact p.tail.ne_one l hl
      chain_ne := p.tail.chain_ne.cons' (fstIdx_ne_iff.mp p.fstIdx_ne) }
#align free_product.word.rcons FreeProduct.Word.rcons

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Given a word of the form `⟨l :: ls, h1, h2⟩`, we can form a word of the form `⟨ls, _, _⟩`,
dropping the first letter. -/
private def mk_aux {l} (ls : List (Σi, M i)) (h1 : ∀ l' ∈ l::ls, Sigma.snd l' ≠ 1)
    (h2 : (l::ls).Chain' _) : Word M :=
  ⟨ls, fun l' hl => h1 _ (List.mem_cons_of_mem _ hl), h2.tail⟩
#align free_product.word.mk_aux free_product.word.mk_aux

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem cons_eq_rcons {i} {m : M i} {ls h1 h2} :
    Word.mk (⟨i, m⟩::ls) h1 h2 = rcons ⟨m, mkAux ls h1 h2, fstIdx_ne_iff.mpr h2.rel_head?⟩ :=
  by
  rw [rcons, dif_neg]
  rfl
  exact h1 ⟨i, m⟩ (ls.mem_cons_self _)
#align free_product.word.cons_eq_rcons FreeProduct.Word.cons_eq_rcons

@[simp]
theorem prod_rcons {i} (p : Pair M i) : prod (rcons p) = of p.headI * prod p.tail :=
  if hm : p.headI = 1 then by rw [rcons, dif_pos hm, hm, MonoidHom.map_one, one_mul]
  else by rw [rcons, dif_neg hm, Prod, List.map_cons, List.prod_cons, Prod]
#align free_product.word.prod_rcons FreeProduct.Word.prod_rcons

theorem rcons_inj {i} : Function.Injective (rcons : Pair M i → Word M) :=
  by
  rintro ⟨m, w, h⟩ ⟨m', w', h'⟩ he
  by_cases hm : m = 1 <;> by_cases hm' : m' = 1
  · simp only [rcons, dif_pos hm, dif_pos hm'] at he
    cc
  · exfalso
    simp only [rcons, dif_pos hm, dif_neg hm'] at he
    rw [he] at h
    exact h rfl
  · exfalso
    simp only [rcons, dif_pos hm', dif_neg hm] at he
    rw [← he] at h'
    exact h' rfl
  · have : m = m' ∧ w.to_list = w'.to_list := by
      simpa only [rcons, dif_neg hm, dif_neg hm', true_and_iff, eq_self_iff_true, Subtype.mk_eq_mk,
        heq_iff_eq, ← Subtype.ext_iff_val] using he
    rcases this with ⟨rfl, h⟩
    congr
    exact word.ext _ _ h
#align free_product.word.rcons_inj FreeProduct.Word.rcons_inj

variable [DecidableEq ι]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- This definition is computable but not very nice to look at. Thankfully we don't have to inspect
-- it, since `rcons` is known to be injective.
/-- Given `i : ι`, any reduced word can be decomposed into a pair `p` such that `w = rcons p`. -/
private def equiv_pair_aux (i) : ∀ w : Word M, { p : Pair M i // rcons p = w }
  | w@⟨[], _, _⟩ => ⟨⟨1, w, by rintro ⟨⟩⟩, dif_pos rfl⟩
  | w@⟨⟨j, m⟩::ls, h1, h2⟩ =>
    if ij : i = j then
      { val :=
          { headI := ij.symm.rec m
            tail := mkAux ls h1 h2
            fstIdx_ne := by cases ij <;> exact fst_idx_ne_iff.mpr h2.rel_head' }
        property := by cases ij <;> exact cons_eq_rcons.symm }
    else ⟨⟨1, w, (Option.some_injective _).Ne (Ne.symm ij)⟩, dif_pos rfl⟩
#align free_product.word.equiv_pair_aux free_product.word.equiv_pair_aux

/-- The equivalence between words and pairs. Given a word, it decomposes it as a pair by removing
the first letter if it comes from `M i`. Given a pair, it prepends the head to the tail. -/
def equivPair (i) : Word M ≃ Pair M i
    where
  toFun w := (equivPairAux i w).val
  invFun := rcons
  left_inv w := (equivPairAux i w).property
  right_inv p := rcons_inj (equivPairAux i _).property
#align free_product.word.equiv_pair FreeProduct.Word.equivPair

theorem equivPair_symm (i) (p : Pair M i) : (equivPair i).symm p = rcons p :=
  rfl
#align free_product.word.equiv_pair_symm FreeProduct.Word.equivPair_symm

theorem equivPair_eq_of_fstIdx_ne {i} {w : Word M} (h : fstIdx w ≠ some i) :
    equivPair i w = ⟨1, w, h⟩ :=
  (equivPair i).apply_eq_iff_eq_symm_apply.mpr <| Eq.symm (dif_pos rfl)
#align free_product.word.equiv_pair_eq_of_fst_idx_ne FreeProduct.Word.equivPair_eq_of_fstIdx_ne

instance summandAction (i) : MulAction (M i) (Word M)
    where
  smul m w := rcons { equivPair i w with headI := m * (equivPair i w).headI }
  one_smul w := by
    simp_rw [one_mul]
    apply (equiv_pair i).symm_apply_eq.mpr
    ext <;> rfl
  mul_smul m m' w := by simp only [mul_assoc, ← equiv_pair_symm, Equiv.apply_symm_apply]
#align free_product.word.summand_action FreeProduct.Word.summandAction

instance : MulAction (FreeProduct M) (Word M) :=
  MulAction.ofEndHom (lift fun i => MulAction.toEndHom)

theorem of_smul_def (i) (w : Word M) (m : M i) :
    of m • w = rcons { equivPair i w with headI := m * (equivPair i w).headI } :=
  rfl
#align free_product.word.of_smul_def FreeProduct.Word.of_smul_def

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem cons_eq_smul {i} {m : M i} {ls h1 h2} :
    Word.mk (⟨i, m⟩::ls) h1 h2 = of m • mkAux ls h1 h2 := by
  rw [cons_eq_rcons, of_smul_def, equiv_pair_eq_of_fst_idx_ne _] <;> simp only [mul_one]
#align free_product.word.cons_eq_smul FreeProduct.Word.cons_eq_smul

theorem smul_induction {C : Word M → Prop} (h_empty : C empty)
    (h_smul : ∀ (i) (m : M i) (w), C w → C (of m • w)) (w : Word M) : C w :=
  by
  cases' w with ls h1 h2
  induction' ls with l ls ih
  · exact h_empty
  cases' l with i m
  rw [cons_eq_smul]
  exact h_smul _ _ _ (ih _ _)
#align free_product.word.smul_induction FreeProduct.Word.smul_induction

@[simp]
theorem prod_smul (m) : ∀ w : Word M, prod (m • w) = m * prod w :=
  by
  apply m.induction_on
  · intro
    rw [one_smul, one_mul]
  · intros
    rw [of_smul_def, prod_rcons, of.map_mul, mul_assoc, ← prod_rcons, ← equiv_pair_symm,
      Equiv.symm_apply_apply]
  · intro x y hx hy w
    rw [mul_smul, hx, hy, mul_assoc]
#align free_product.word.prod_smul FreeProduct.Word.prod_smul

/-- Each element of the free product corresponds to a unique reduced word. -/
def equiv : FreeProduct M ≃ Word M where
  toFun m := m • empty
  invFun w := prod w
  left_inv m := by dsimp only <;> rw [prod_smul, prod_empty, mul_one]
  right_inv := by
    apply smul_induction
    · dsimp only
      rw [prod_empty, one_smul]
    · dsimp only
      intro i m w ih
      rw [prod_smul, mul_smul, ih]
#align free_product.word.equiv FreeProduct.Word.equiv

instance : DecidableEq (Word M) :=
  Function.Injective.decidableEq Word.ext

instance : DecidableEq (FreeProduct M) :=
  Word.equiv.DecidableEq

end Word

variable (M)

/-- A `neword M i j` is a representation of a non-empty reduced words where the first letter comes
from `M i` and the last letter comes from `M j`. It can be constructed from singletons and via
concatentation, and thus provides a useful induction principle. -/
@[nolint has_nonempty_instance]
inductive Neword : ι → ι → Type max u_1 u_2
  | singleton : ∀ {i} (x : M i) (hne1 : x ≠ 1), neword i i
  | append : ∀ {i j k l} (w₁ : neword i j) (hne : j ≠ k) (w₂ : neword k l), neword i l
#align free_product.neword FreeProduct.Neword

variable {M}

namespace Neword

open Word

/-- The list represented by a given `neword` -/
@[simp]
def toList : ∀ {i j} (w : Neword M i j), List (Σi, M i)
  | i, _, singleton x hne1 => [⟨i, x⟩]
  | _, _, append w₁ hne w₂ => w₁.toList ++ w₂.toList
#align free_product.neword.to_list FreeProduct.Neword.toList

theorem toList_ne_nil {i j} (w : Neword M i j) : w.toList ≠ List.nil :=
  by
  induction w
  · rintro ⟨rfl⟩
  · apply List.append_ne_nil_of_ne_nil_left
    assumption
#align free_product.neword.to_list_ne_nil FreeProduct.Neword.toList_ne_nil

/-- The first letter of a `neword` -/
@[simp]
def head : ∀ {i j} (w : Neword M i j), M i
  | i, _, singleton x hne1 => x
  | _, _, append w₁ hne w₂ => w₁.headI
#align free_product.neword.head FreeProduct.Neword.head

/-- The last letter of a `neword` -/
@[simp]
def last : ∀ {i j} (w : Neword M i j), M j
  | i, _, singleton x hne1 => x
  | _, _, append w₁ hne w₂ => w₂.getLast
#align free_product.neword.last FreeProduct.Neword.last

@[simp]
theorem toList_head? {i j} (w : Neword M i j) : w.toList.head? = Option.some ⟨i, w.headI⟩ :=
  by
  rw [← Option.mem_def]
  induction w
  · rw [Option.mem_def]
    rfl
  · exact List.head?_append w_ih_w₁
#align free_product.neword.to_list_head' FreeProduct.Neword.toList_head?

@[simp]
theorem toList_getLast? {i j} (w : Neword M i j) : w.toList.getLast? = Option.some ⟨j, w.getLast⟩ :=
  by
  rw [← Option.mem_def]
  induction w
  · rw [Option.mem_def]
    rfl
  · exact List.getLast?_append w_ih_w₂
#align free_product.neword.to_list_last' FreeProduct.Neword.toList_getLast?

/-- The `word M` represented by a `neword M i j` -/
def toWord {i j} (w : Neword M i j) : Word M
    where
  toList := w.toList
  ne_one := by
    induction w
    · rintro ⟨k, x⟩ ⟨rfl, rfl⟩
      exact w_hne1
      exfalso
      apply H
    · intro l h
      simp only [to_list, List.mem_append] at h
      cases h
      · exact w_ih_w₁ _ h
      · exact w_ih_w₂ _ h
  chain_ne := by
    induction w
    · exact List.chain'_singleton _
    · apply List.Chain'.append w_ih_w₁ w_ih_w₂
      intro x hx y hy
      rw [w_w₁.to_list_last', Option.mem_some_iff] at hx
      rw [w_w₂.to_list_head', Option.mem_some_iff] at hy
      subst hx
      subst hy
      exact w_hne
#align free_product.neword.to_word FreeProduct.Neword.toWord

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Every nonempty `word M` can be constructed as a `neword M i j` -/
theorem of_word (w : Word M) (h : w ≠ Empty) : ∃ (i j : _)(w' : Neword M i j), w'.toWord = w :=
  by
  rsuffices ⟨i, j, w, h⟩ : ∃ (i j : _)(w' : neword M i j), w'.to_word.to_list = w.to_list
  · refine' ⟨i, j, w, _⟩
    ext
    rw [h]
  cases' w with l hnot1 hchain
  induction' l with x l hi
  · contradiction
  · rw [List.forall_mem_cons] at hnot1
    cases' l with y l
    · refine' ⟨x.1, x.1, singleton x.2 hnot1.1, _⟩
      simp [to_word]
    · rw [List.chain'_cons] at hchain
      specialize hi hnot1.2 hchain.2 (by rintro ⟨rfl⟩)
      obtain ⟨i, j, w', hw' : w'.to_list = y::l⟩ := hi
      obtain rfl : y = ⟨i, w'.head⟩ := by simpa [hw'] using w'.to_list_head'
      refine' ⟨x.1, j, append (singleton x.2 hnot1.1) hchain.1 w', _⟩
      · simpa [to_word] using hw'
#align free_product.neword.of_word FreeProduct.Neword.of_word

/-- A non-empty reduced word determines an element of the free product, given by multiplication. -/
def prod {i j} (w : Neword M i j) :=
  w.toWord.Prod
#align free_product.neword.prod FreeProduct.Neword.prod

@[simp]
theorem singleton_head {i} (x : M i) (hne_one : x ≠ 1) : (singleton x hne_one).headI = x :=
  rfl
#align free_product.neword.singleton_head FreeProduct.Neword.singleton_head

@[simp]
theorem singleton_last {i} (x : M i) (hne_one : x ≠ 1) : (singleton x hne_one).getLast = x :=
  rfl
#align free_product.neword.singleton_last FreeProduct.Neword.singleton_last

@[simp]
theorem prod_singleton {i} (x : M i) (hne_one : x ≠ 1) : (singleton x hne_one).Prod = of x := by
  simp [to_word, Prod, word.prod]
#align free_product.neword.prod_singleton FreeProduct.Neword.prod_singleton

@[simp]
theorem append_head {i j k l} {w₁ : Neword M i j} {hne : j ≠ k} {w₂ : Neword M k l} :
    (append w₁ hne w₂).headI = w₁.headI :=
  rfl
#align free_product.neword.append_head FreeProduct.Neword.append_head

@[simp]
theorem append_last {i j k l} {w₁ : Neword M i j} {hne : j ≠ k} {w₂ : Neword M k l} :
    (append w₁ hne w₂).getLast = w₂.getLast :=
  rfl
#align free_product.neword.append_last FreeProduct.Neword.append_last

@[simp]
theorem append_prod {i j k l} {w₁ : Neword M i j} {hne : j ≠ k} {w₂ : Neword M k l} :
    (append w₁ hne w₂).Prod = w₁.Prod * w₂.Prod := by simp [to_word, Prod, word.prod]
#align free_product.neword.append_prod FreeProduct.Neword.append_prod

/-- One can replace the first letter in a non-empty reduced word by an element of the same
group -/
def replaceHead : ∀ {i j : ι} (x : M i) (hnotone : x ≠ 1) (w : Neword M i j), Neword M i j
  | _, _, x, h, singleton _ _ => singleton x h
  | _, _, x, h, append w₁ hne w₂ => append (replace_head x h w₁) hne w₂
#align free_product.neword.replace_head FreeProduct.Neword.replaceHead

@[simp]
theorem replaceHead_head {i j : ι} (x : M i) (hnotone : x ≠ 1) (w : Neword M i j) :
    (replaceHead x hnotone w).headI = x := by
  induction w
  rfl
  exact w_ih_w₁ _ _
#align free_product.neword.replace_head_head FreeProduct.Neword.replaceHead_head

/-- One can multiply an element from the left to a non-empty reduced word if it does not cancel
with the first element in the word. -/
def mulHead {i j : ι} (w : Neword M i j) (x : M i) (hnotone : x * w.headI ≠ 1) : Neword M i j :=
  replaceHead (x * w.headI) hnotone w
#align free_product.neword.mul_head FreeProduct.Neword.mulHead

@[simp]
theorem mulHead_head {i j : ι} (w : Neword M i j) (x : M i) (hnotone : x * w.headI ≠ 1) :
    (mulHead w x hnotone).headI = x * w.headI :=
  by
  induction w
  rfl
  exact w_ih_w₁ _ _
#align free_product.neword.mul_head_head FreeProduct.Neword.mulHead_head

@[simp]
theorem mulHead_prod {i j : ι} (w : Neword M i j) (x : M i) (hnotone : x * w.headI ≠ 1) :
    (mulHead w x hnotone).Prod = of x * w.Prod :=
  by
  unfold mul_head
  induction w
  · simp [mul_head, replace_head]
  · specialize w_ih_w₁ _ hnotone
    clear w_ih_w₂
    simp [replace_head, ← mul_assoc] at *
    congr 1
#align free_product.neword.mul_head_prod FreeProduct.Neword.mulHead_prod

section Group

variable {G : ι → Type _} [∀ i, Group (G i)]

/-- The inverse of a non-empty reduced word -/
def inv : ∀ {i j} (w : Neword G i j), Neword G j i
  | _, _, singleton x h => singleton x⁻¹ (mt inv_eq_one.mp h)
  | _, _, append w₁ h w₂ => append w₂.inv h.symm w₁.inv
#align free_product.neword.inv FreeProduct.Neword.inv

@[simp]
theorem inv_prod {i j} (w : Neword G i j) : w.inv.Prod = w.Prod⁻¹ := by
  induction w <;> simp [inv, *]
#align free_product.neword.inv_prod FreeProduct.Neword.inv_prod

@[simp]
theorem inv_head {i j} (w : Neword G i j) : w.inv.headI = w.getLast⁻¹ := by
  induction w <;> simp [inv, *]
#align free_product.neword.inv_head FreeProduct.Neword.inv_head

@[simp]
theorem inv_last {i j} (w : Neword G i j) : w.inv.getLast = w.headI⁻¹ := by
  induction w <;> simp [inv, *]
#align free_product.neword.inv_last FreeProduct.Neword.inv_last

end Group

end Neword

section PingPongLemma

open Pointwise

open Cardinal

variable [hnontriv : Nontrivial ι]

variable {G : Type _} [Group G]

variable {H : ι → Type _} [∀ i, Group (H i)]

variable (f : ∀ i, H i →* G)

-- We need many groups or one group with many elements
variable (hcard : 3 ≤ (#ι) ∨ ∃ i, 3 ≤ (#H i))

-- A group action on α, and the ping-pong sets
variable {α : Type _} [MulAction G α]

variable (X : ι → Set α)

variable (hXnonempty : ∀ i, (X i).Nonempty)

variable (hXdisj : Pairwise fun i j => Disjoint (X i) (X j))

variable (hpp : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • X j ⊆ X i)

include hpp

theorem lift_word_ping_pong {i j k} (w : Neword H i j) (hk : j ≠ k) : lift f w.Prod • X k ⊆ X i :=
  by
  rename' i => i', j => j', k => m, hk => hm
  induction' w with i x hne_one i j k l w₁ hne w₂ hIw₁ hIw₂ generalizing m <;> clear i' j'
  · simpa using hpp hm _ hne_one
  ·
    calc
      lift f (neword.append w₁ hne w₂).Prod • X m = lift f w₁.prod • lift f w₂.prod • X m := by
        simp [MulAction.mul_smul]
      _ ⊆ lift f w₁.prod • X k := (set_smul_subset_set_smul_iff.mpr (hIw₂ hm))
      _ ⊆ X i := hIw₁ hne
      
#align free_product.lift_word_ping_pong FreeProduct.lift_word_ping_pong

include X hXnonempty hXdisj

theorem lift_word_prod_nontrivial_of_other_i {i j k} (w : Neword H i j) (hhead : k ≠ i)
    (hlast : k ≠ j) : lift f w.Prod ≠ 1 := by
  intro heq1
  have : X k ⊆ X i := by simpa [heq1] using lift_word_ping_pong f X hpp w hlast.symm
  obtain ⟨x, hx⟩ := hXnonempty k
  exact (hXdisj hhead).le_bot ⟨hx, this hx⟩
#align free_product.lift_word_prod_nontrivial_of_other_i FreeProduct.lift_word_prod_nontrivial_of_other_i

include hnontriv

theorem lift_word_prod_nontrivial_of_head_eq_last {i} (w : Neword H i i) : lift f w.Prod ≠ 1 :=
  by
  obtain ⟨k, hk⟩ := exists_ne i
  exact lift_word_prod_nontrivial_of_other_i f X hXnonempty hXdisj hpp w hk hk
#align free_product.lift_word_prod_nontrivial_of_head_eq_last FreeProduct.lift_word_prod_nontrivial_of_head_eq_last

theorem lift_word_prod_nontrivial_of_head_card {i j} (w : Neword H i j) (hcard : 3 ≤ (#H i))
    (hheadtail : i ≠ j) : lift f w.Prod ≠ 1 :=
  by
  obtain ⟨h, hn1, hnh⟩ := Cardinal.three_le hcard 1 w.head⁻¹
  have hnot1 : h * w.head ≠ 1 := by
    rw [← div_inv_eq_mul]
    exact div_ne_one_of_ne hnh
  let w' : neword H i i :=
    neword.append (neword.mul_head w h hnot1) hheadtail.symm
      (neword.singleton h⁻¹ (inv_ne_one.mpr hn1))
  have hw' : lift f w'.prod ≠ 1 :=
    lift_word_prod_nontrivial_of_head_eq_last f X hXnonempty hXdisj hpp w'
  intro heq1
  apply hw'
  simp [w', heq1]
#align free_product.lift_word_prod_nontrivial_of_head_card FreeProduct.lift_word_prod_nontrivial_of_head_card

include hcard

theorem lift_word_prod_nontrivial_of_not_empty {i j} (w : Neword H i j) : lift f w.Prod ≠ 1 := by
  classical
    cases hcard
    · obtain ⟨i, h1, h2⟩ := Cardinal.three_le hcard i j
      exact lift_word_prod_nontrivial_of_other_i f X hXnonempty hXdisj hpp w h1 h2
    · cases' hcard with k hcard
      by_cases hh : i = k <;> by_cases hl : j = k
      · subst hh
        subst hl
        exact lift_word_prod_nontrivial_of_head_eq_last f X hXnonempty hXdisj hpp w
      · subst hh
        change j ≠ i at hl
        exact lift_word_prod_nontrivial_of_head_card f X hXnonempty hXdisj hpp w hcard hl.symm
      · subst hl
        change i ≠ j at hh
        have : lift f w.inv.prod ≠ 1 :=
          lift_word_prod_nontrivial_of_head_card f X hXnonempty hXdisj hpp w.inv hcard hh.symm
        intro heq
        apply this
        simpa using HEq
      · change i ≠ k at hh
        change j ≠ k at hl
        obtain ⟨h, hn1, -⟩ := Cardinal.three_le hcard 1 1
        let w' : neword H k k :=
          neword.append (neword.append (neword.singleton h hn1) hh.symm w) hl
            (neword.singleton h⁻¹ (inv_ne_one.mpr hn1))
        have hw' : lift f w'.prod ≠ 1 :=
          lift_word_prod_nontrivial_of_head_eq_last f X hXnonempty hXdisj hpp w'
        intro heq1
        apply hw'
        simp [w', heq1]
#align free_product.lift_word_prod_nontrivial_of_not_empty FreeProduct.lift_word_prod_nontrivial_of_not_empty

theorem empty_of_word_prod_eq_one {w : Word H} (h : lift f w.Prod = 1) : w = Word.empty :=
  by
  by_contra hnotempty
  obtain ⟨i, j, w, rfl⟩ := neword.of_word w hnotempty
  exact lift_word_prod_nontrivial_of_not_empty f hcard X hXnonempty hXdisj hpp w h
#align free_product.empty_of_word_prod_eq_one FreeProduct.empty_of_word_prod_eq_one

/-- The Ping-Pong-Lemma.

Given a group action of `G` on `X` so that the `H i` acts in a specific way on disjoint subsets
`X i` we can prove that `lift f` is injective, and thus the image of `lift f` is isomorphic to the
free product of the `H i`.

Often the Ping-Pong-Lemma is stated with regard to subgroups `H i` that generate the whole group;
we generalize to arbitrary group homomorphisms `f i : H i →* G` and do not require the group to be
generated by the images.

Usually the Ping-Pong-Lemma requires that one group `H i` has at least three elements. This
condition is only needed if `# ι = 2`, and we accept `3 ≤ # ι` as an alternative.
-/
theorem lift_injective_of_ping_pong : Function.Injective (lift f) := by
  classical
    apply (injective_iff_map_eq_one (lift f)).mpr
    rw [(FreeProduct.Word.equiv : _ ≃ word H).forall_congr_left']
    · intro w Heq
      dsimp [word.equiv] at *
      · rw [empty_of_word_prod_eq_one f hcard X hXnonempty hXdisj hpp Heq]
        rfl
#align free_product.lift_injective_of_ping_pong FreeProduct.lift_injective_of_ping_pong

end PingPongLemma

/-- The free product of free groups is itself a free group -/
@[simps]
instance {ι : Type _} (G : ι → Type _) [∀ i, Group (G i)] [hG : ∀ i, IsFreeGroup (G i)] :
    IsFreeGroup (FreeProduct G)
    where
  Generators := Σi, IsFreeGroup.Generators (G i)
  MulEquiv :=
    MonoidHom.toMulEquiv
      (FreeGroup.lift fun x : Σi, IsFreeGroup.Generators (G i) =>
        FreeProduct.of (IsFreeGroup.of x.2 : G x.1))
      (FreeProduct.lift fun i : ι =>
        (IsFreeGroup.lift fun x : IsFreeGroup.Generators (G i) =>
            FreeGroup.of (⟨i, x⟩ : Σi, IsFreeGroup.Generators (G i)) :
          G i →* FreeGroup (Σi, IsFreeGroup.Generators (G i))))
      (by
        ext
        simp)
      (by
        ext
        simp)

-- NB: One might expect this theorem to be phrased with ℤ, but ℤ is an additive group,
-- and using `multiplicative ℤ` runs into diamond issues.
/-- A free group is a free product of copies of the free_group over one generator. -/
@[simps]
def freeGroupEquivFreeProduct {ι : Type u_1} :
    FreeGroup ι ≃* FreeProduct fun _ : ι => FreeGroup Unit :=
  by
  refine' MonoidHom.toMulEquiv _ _ _ _
  exact FreeGroup.lift fun i => @FreeProduct.of ι _ _ i (FreeGroup.of Unit.unit)
  exact FreeProduct.lift fun i => FreeGroup.lift fun pstar => FreeGroup.of i
  · ext i
    rfl
  · ext (i a)
    cases a
    rfl
#align free_group_equiv_free_product freeGroupEquivFreeProduct

section PingPongLemma

open Pointwise Cardinal

variable [Nontrivial ι]

variable {G : Type u_1} [Group G] (a : ι → G)

-- A group action on α, and the ping-pong sets
variable {α : Type _} [MulAction G α]

variable (X Y : ι → Set α)

variable (hXnonempty : ∀ i, (X i).Nonempty)

variable (hXdisj : Pairwise fun i j => Disjoint (X i) (X j))

variable (hYdisj : Pairwise fun i j => Disjoint (Y i) (Y j))

variable (hXYdisj : ∀ i j, Disjoint (X i) (Y j))

variable (hX : ∀ i, a i • Y iᶜ ⊆ X i)

variable (hY : ∀ i, a⁻¹ i • X iᶜ ⊆ Y i)

include hXnonempty hXdisj hYdisj hXYdisj hX hY

/-- The Ping-Pong-Lemma.

Given a group action of `G` on `X` so that the generators of the free groups act in specific
ways on disjoint subsets `X i` and `Y i` we can prove that `lift f` is injective, and thus the image
of `lift f` is isomorphic to the free group.

Often the Ping-Pong-Lemma is stated with regard to group elements that generate the whole group;
we generalize to arbitrary group homomorphisms from the free group to `G`  and do not require the
group to be generated by the elements.
-/
theorem FreeGroup.injective_lift_of_ping_pong : Function.Injective (FreeGroup.lift a) :=
  by
  -- Step one: express the free group lift via the free product lift
  have :
    FreeGroup.lift a =
      (FreeProduct.lift fun i => FreeGroup.lift fun _ => a i).comp
        (@freeGroupEquivFreeProduct ι).toMonoidHom :=
    by
    ext i
    simp
  rw [this]
  clear this
  refine' Function.Injective.comp _ (MulEquiv.injective _)
  -- Step two: Invoke the ping-pong lemma for free products
  show Function.Injective (lift fun i : ι => FreeGroup.lift fun _ => a i)
  -- Prepare to instantiate lift_injective_of_ping_pong
  let H : ι → Type _ := fun i => FreeGroup Unit
  let f : ∀ i, H i →* G := fun i => FreeGroup.lift fun _ => a i
  let X' : ι → Set α := fun i => X i ∪ Y i
  apply lift_injective_of_ping_pong f _ X'
  show _ ∨ ∃ i, 3 ≤ (#H i)
  · inhabit ι
    right
    use Inhabited.default ι
    simp only [H]
    rw [free_group.free_group_unit_equiv_int.cardinal_eq, Cardinal.mk_denumerable]
    apply le_of_lt
    simp
  show ∀ i, (X' i).Nonempty
  · exact fun i => Set.Nonempty.inl (hXnonempty i)
  show Pairwise fun i j => Disjoint (X' i) (X' j)
  · intro i j hij
    simp only [X']
    apply Disjoint.union_left <;> apply Disjoint.union_right
    · exact hXdisj hij
    · exact hXYdisj i j
    · exact (hXYdisj j i).symm
    · exact hYdisj hij
  show Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • X' j ⊆ X' i
  · rintro i j hij
    -- use free_group unit ≃ ℤ
    refine' free_group.free_group_unit_equiv_int.forall_congr_left'.mpr _
    intro n hne1
    change FreeGroup.lift (fun _ => a i) (FreeGroup.of () ^ n) • X' j ⊆ X' i
    simp only [map_zpow, FreeGroup.lift.of]
    change a i ^ n • X' j ⊆ X' i
    have hnne0 : n ≠ 0 := by
      rintro rfl
      apply hne1
      simpa
    clear hne1
    simp only [X']
    -- Positive and negative powers separately
    cases' (lt_or_gt_of_ne hnne0).symm with hlt hgt
    · have h1n : 1 ≤ n := hlt
      calc
        a i ^ n • X' j ⊆ a i ^ n • Y iᶜ :=
          smul_set_mono ((hXYdisj j i).union_left <| hYdisj hij.symm).subset_compl_right
        _ ⊆ X i := by
          refine' Int.le_induction _ _ _ h1n
          · rw [zpow_one]
            exact hX i
          · intro n hle hi
            calc
              a i ^ (n + 1) • Y iᶜ = (a i ^ n * a i) • Y iᶜ := by rw [zpow_add, zpow_one]
              _ = a i ^ n • a i • Y iᶜ := (MulAction.mul_smul _ _ _)
              _ ⊆ a i ^ n • X i := (smul_set_mono <| hX i)
              _ ⊆ a i ^ n • Y iᶜ := (smul_set_mono (hXYdisj i i).subset_compl_right)
              _ ⊆ X i := hi
              
        _ ⊆ X' i := Set.subset_union_left _ _
        
    · have h1n : n ≤ -1 := by
        apply Int.le_of_lt_add_one
        simpa using hgt
      calc
        a i ^ n • X' j ⊆ a i ^ n • X iᶜ :=
          smul_set_mono ((hXdisj hij.symm).union_left (hXYdisj i j).symm).subset_compl_right
        _ ⊆ Y i := by
          refine' Int.le_induction_down _ _ _ h1n
          · rw [zpow_neg, zpow_one]
            exact hY i
          · intro n hle hi
            calc
              a i ^ (n - 1) • X iᶜ = (a i ^ n * (a i)⁻¹) • X iᶜ := by rw [zpow_sub, zpow_one]
              _ = a i ^ n • (a i)⁻¹ • X iᶜ := (MulAction.mul_smul _ _ _)
              _ ⊆ a i ^ n • Y i := (smul_set_mono <| hY i)
              _ ⊆ a i ^ n • X iᶜ := (smul_set_mono (hXYdisj i i).symm.subset_compl_right)
              _ ⊆ Y i := hi
              
        _ ⊆ X' i := Set.subset_union_right _ _
        
#align free_group.injective_lift_of_ping_pong FreeGroup.injective_lift_of_ping_pong

end PingPongLemma

end FreeProduct

