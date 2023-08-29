/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Joachim Breitner
-/
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.GroupTheory.Congruence
import Mathlib.GroupTheory.IsFreeGroup
import Mathlib.Data.List.Chain
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Data.Set.Pointwise.SMul

#align_import group_theory.free_product from "leanprover-community/mathlib"@"9114ddffa023340c9ec86965e00cdd6fe26fcdf6"

/-!
# The coproduct (a.k.a. the free product) of groups or monoids

Given an `ι`-indexed family `M` of monoids,
we define their coproduct (a.k.a. free product) `Monoid.CoprodI M`.
As usual, we use the suffix `I` for an indexed (co)product,
leaving `Coprod` for the coproduct of two monoids.

When `ι` and all `M i` have decidable equality,
the free product bijects with the type `Monoid.CoprodI.Word M` of reduced words.
This bijection is constructed
by defining an action of `Monoid.CoprodI M` on `Monoid.CoprodI.Word M`.

When `M i` are all groups, `Monoid.CoprodI M` is also a group
(and the coproduct in the category of groups).

## Main definitions

- `Monoid.CoprodI M`: the free product, defined as a quotient of a free monoid.
- `Monoid.CoprodI.of {i} : M i →* Monoid.CoprodI M`.
- `Monoid.CoprodI.lift : (∀ {i}, M i →* N) ≃ (Monoid.CoprodI M →* N)`: the universal property.
- `Monoid.CoprodI.Word M`: the type of reduced words.
- `Monoid.CoprodI.Word.equiv M : Monoid.CoprodI M ≃ word M`.
- `Monoid.CoprodI.NeWord M i j`: an inductive description of non-empty words
  with first letter from `M i` and last letter from `M j`,
  together with an API (`singleton`, `append`, `head`, `tail`, `to_word`, `Prod`, `inv`).
  Used in the proof of the Ping-Pong-lemma.
- `Monoid.CoprodI.lift_injective_of_ping_pong`: The Ping-Pong-lemma,
  proving injectivity of the `lift`. See the documentation of that theorem for more information.

## Remarks

There are many answers to the question "what is the coproduct of a family `M` of monoids?",
and they are all equivalent but not obviously equivalent.
We provide two answers.
The first, almost tautological answer is given by `Monoid.CoprodI M`,
which is a quotient of the type of words in the alphabet `Σ i, M i`.
It's straightforward to define and easy to prove its universal property.
But this answer is not completely satisfactory,
because it's difficult to tell when two elements `x y : Monoid.CoprodI M` are distinct
since `Monoid.CoprodI M` is defined as a quotient.

The second, maximally efficient answer is given by `Monoid.CoprodI.Word M`.
An element of `Monoid.CoprodI.Word M` is a word in the alphabet `Σ i, M i`,
where the letter `⟨i, 1⟩` doesn't occur and no adjacent letters share an index `i`.
Since we only work with reduced words, there is no need for quotienting,
and it is easy to tell when two elements are distinct.
However it's not obvious that this is even a monoid!

We prove that every element of `Monoid.CoprodI M` can be represented by a unique reduced word,
i.e. `Monoid.CoprodI M` and `Monoid.CoprodI.Word M` are equivalent types.
This means that `Monoid.CoprodI.Word M` can be given a monoid structure,
and it lets us tell when two elements of `Monoid.CoprodI M` are distinct.

There is also a completely tautological, maximally inefficient answer
given by `MonCat.Colimits.ColimitType`.
Whereas `Monoid.CoprodI M` at least ensures that
(any instance of) associativity holds by reflexivity,
in this answer associativity holds because of quotienting.
Yet another answer, which is constructively more satisfying,
could be obtained by showing that `Monoid.CoprodI.Rel` is confluent.

## References

[van der Waerden, *Free products of groups*][MR25465]

-/


open Set

variable {ι : Type*} (M : ι → Type*) [∀ i, Monoid (M i)]

/-- A relation on the free monoid on alphabet `Σ i, M i`,
relating `⟨i, 1⟩` with `1` and `⟨i, x⟩ * ⟨i, y⟩` with `⟨i, x * y⟩`. -/
inductive Monoid.CoprodI.Rel : FreeMonoid (Σi, M i) → FreeMonoid (Σi, M i) → Prop
  | of_one (i : ι) : Monoid.CoprodI.Rel (FreeMonoid.of ⟨i, 1⟩) 1
  | of_mul {i : ι} (x y : M i) :
    Monoid.CoprodI.Rel (FreeMonoid.of ⟨i, x⟩ * FreeMonoid.of ⟨i, y⟩) (FreeMonoid.of ⟨i, x * y⟩)
#align free_product.rel Monoid.CoprodI.Rel

/-- The free product (categorical coproduct) of an indexed family of monoids. -/
def Monoid.CoprodI : Type _ := (conGen (Monoid.CoprodI.Rel M)).Quotient
#align free_product Monoid.CoprodI

--Porting note: could not de derived
instance : Monoid (Monoid.CoprodI M) :=
  by delta Monoid.CoprodI; infer_instance
     -- ⊢ Monoid (Con.Quotient (conGen (Monoid.CoprodI.Rel M)))
                           -- 🎉 no goals

instance : Inhabited (Monoid.CoprodI M) :=
  ⟨1⟩

namespace Monoid.CoprodI

/-- The type of reduced words. A reduced word cannot contain a letter `1`, and no two adjacent
letters can come from the same summand. -/
@[ext]
structure Word where
  /-- A `Word` is a `List (Σ i, M i)`, such that `1` is not in the list, and no
  two adjacent letters are from the same summand -/
  toList : List (Σi, M i)
  /-- A reduced word does not contain `1` -/
  ne_one : ∀ l ∈ toList, Sigma.snd l ≠ 1
  /-- Adjacent letters are not from the same summand. -/
  chain_ne : toList.Chain' fun l l' => Sigma.fst l ≠ Sigma.fst l'
#align free_product.word Monoid.CoprodI.Word

variable {M}

/-- The inclusion of a summand into the free product. -/
def of {i : ι} : M i →* CoprodI M where
  toFun x := Con.mk' _ (FreeMonoid.of <| Sigma.mk i x)
  map_one' := (Con.eq _).mpr (ConGen.Rel.of _ _ (CoprodI.Rel.of_one i))
  map_mul' x y := Eq.symm <| (Con.eq _).mpr (ConGen.Rel.of _ _ (CoprodI.Rel.of_mul x y))
#align free_product.of Monoid.CoprodI.of

theorem of_apply {i} (m : M i) : of m = Con.mk' _ (FreeMonoid.of <| Sigma.mk i m) :=
  rfl
#align free_product.of_apply Monoid.CoprodI.of_apply

variable {N : Type*} [Monoid N]

/-- See note [partially-applied ext lemmas]. -/
--Porting note: higher `ext` priority
@[ext 1100]
theorem ext_hom (f g : CoprodI M →* N) (h : ∀ i, f.comp (of : M i →* _) = g.comp of) : f = g :=
  (MonoidHom.cancel_right Con.mk'_surjective).mp <|
    FreeMonoid.hom_eq fun ⟨i, x⟩ => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← of_apply, ← MonoidHom.comp_apply, ←
        MonoidHom.comp_apply, h]
#align free_product.ext_hom Monoid.CoprodI.ext_hom

/-- A map out of the free product corresponds to a family of maps out of the summands. This is the
universal property of the free product, characterizing it as a categorical coproduct. -/
@[simps symm_apply]
def lift : (∀ i, M i →* N) ≃ (CoprodI M →* N) where
  toFun fi :=
    Con.lift _ (FreeMonoid.lift fun p : Σi, M i => fi p.fst p.snd) <|
      Con.conGen_le <| by
        simp_rw [Con.rel_eq_coe, Con.ker_rel]
        -- ⊢ ∀ (x y : FreeMonoid ((i : ι) × M i)), Rel M x y → ↑(↑FreeMonoid.lift fun p = …
        rintro _ _ (i | ⟨x, y⟩)
        -- ⊢ ↑(↑FreeMonoid.lift fun p => ↑(fi p.fst) p.snd) (FreeMonoid.of { fst := i, sn …
        · change FreeMonoid.lift _ (FreeMonoid.of _) = FreeMonoid.lift _ 1
          -- ⊢ ↑(↑FreeMonoid.lift fun p => ↑(fi p.fst) p.snd) (FreeMonoid.of { fst := i, sn …
          simp only [MonoidHom.map_one, FreeMonoid.lift_eval_of]
          -- 🎉 no goals
        · change
            FreeMonoid.lift _ (FreeMonoid.of _ * FreeMonoid.of _) =
              FreeMonoid.lift _ (FreeMonoid.of _)
          simp only [MonoidHom.map_mul, FreeMonoid.lift_eval_of]
          -- 🎉 no goals
  invFun f i := f.comp of
  left_inv := by
    intro fi
    -- ⊢ (fun f i => MonoidHom.comp f of) ((fun fi => Con.lift (conGen (Rel M)) (↑Fre …
    ext i x
    -- ⊢ ↑((fun f i => MonoidHom.comp f of) ((fun fi => Con.lift (conGen (Rel M)) (↑F …
    rw [MonoidHom.comp_apply, of_apply, Con.lift_mk', FreeMonoid.lift_eval_of]
    -- 🎉 no goals
  right_inv := by
    intro f
    -- ⊢ (fun fi => Con.lift (conGen (Rel M)) (↑FreeMonoid.lift fun p => ↑(fi p.fst)  …
    ext i x
    -- ⊢ ↑(MonoidHom.comp ((fun fi => Con.lift (conGen (Rel M)) (↑FreeMonoid.lift fun …
    rfl
    -- 🎉 no goals
#align free_product.lift Monoid.CoprodI.lift

@[simp]
theorem lift_of {N} [Monoid N] (fi : ∀ i, M i →* N) {i} (m : M i) : lift fi (of m) = fi i m := by
  conv_rhs => rw [← lift.symm_apply_apply fi, lift_symm_apply, MonoidHom.comp_apply]
  -- 🎉 no goals
#align free_product.lift_of Monoid.CoprodI.lift_of

@[elab_as_elim]
theorem induction_on {C : CoprodI M → Prop} (m : CoprodI M) (h_one : C 1)
    (h_of : ∀ (i) (m : M i), C (of m)) (h_mul : ∀ x y, C x → C y → C (x * y)) : C m := by
  let S : Submonoid (CoprodI M) :=
    { carrier := setOf C
      mul_mem' := h_mul _ _
      one_mem' := h_one }
  have : C _ := Subtype.prop (lift (fun i => of.codRestrict S (h_of i)) m)
  -- ⊢ C m
  convert this
  -- ⊢ m = ↑(↑(↑lift fun i => MonoidHom.codRestrict of S (_ : ∀ (m : M i), C (↑of m …
  change MonoidHom.id _ m = S.subtype.comp _ m
  -- ⊢ ↑(MonoidHom.id (CoprodI M)) m = ↑(MonoidHom.comp (Submonoid.subtype S) (↑lif …
  congr
  -- ⊢ MonoidHom.id (CoprodI M) = MonoidHom.comp (Submonoid.subtype S) (↑lift fun i …
  ext i
  -- ⊢ ↑(MonoidHom.comp (MonoidHom.id (CoprodI M)) of) x✝ = ↑(MonoidHom.comp (Monoi …
  rfl
  -- 🎉 no goals
#align free_product.induction_on Monoid.CoprodI.induction_on

theorem of_leftInverse [DecidableEq ι] (i : ι) :
    Function.LeftInverse (lift <| Pi.mulSingle i (MonoidHom.id (M i))) of := fun x => by
  simp only [lift_of, Pi.mulSingle_eq_same, MonoidHom.id_apply]
  -- 🎉 no goals
#align free_product.of_left_inverse Monoid.CoprodI.of_leftInverse

theorem of_injective (i : ι) : Function.Injective (of : M i →* _) := by
  classical exact (of_leftInverse i).injective
  -- 🎉 no goals
#align free_product.of_injective Monoid.CoprodI.of_injective

theorem lift_mrange_le {N} [Monoid N] (f : ∀ i, M i →* N) {s : Submonoid N}
    (h : ∀ i, MonoidHom.mrange (f i) ≤ s) : MonoidHom.mrange (lift f) ≤ s := by
  rintro _ ⟨x, rfl⟩
  -- ⊢ ↑(↑lift f) x ∈ s
  induction' x using CoprodI.induction_on with i x x y hx hy
  · exact s.one_mem
    -- 🎉 no goals
  · simp only [lift_of, SetLike.mem_coe]
    -- ⊢ ↑(f i) x ∈ s
    exact h i (Set.mem_range_self x)
    -- 🎉 no goals
  · simp only [map_mul, SetLike.mem_coe]
    -- ⊢ ↑(↑lift f) x * ↑(↑lift f) y ∈ s
    exact s.mul_mem hx hy
    -- 🎉 no goals
#align free_product.lift_mrange_le Monoid.CoprodI.lift_mrange_le

theorem mrange_eq_iSup {N} [Monoid N] (f : ∀ i, M i →* N) :
    MonoidHom.mrange (lift f) = ⨆ i, MonoidHom.mrange (f i) := by
  apply le_antisymm (lift_mrange_le f fun i => le_iSup (fun i => MonoidHom.mrange (f i)) i)
  -- ⊢ ⨆ (i : ι), MonoidHom.mrange (f i) ≤ MonoidHom.mrange (↑lift f)
  apply iSup_le _
  -- ⊢ ∀ (i : ι), MonoidHom.mrange (f i) ≤ MonoidHom.mrange (↑lift f)
  rintro i _ ⟨x, rfl⟩
  -- ⊢ ↑(f i) x ∈ MonoidHom.mrange (↑lift f)
  exact ⟨of x, by simp only [lift_of]⟩
  -- 🎉 no goals
#align free_product.mrange_eq_supr Monoid.CoprodI.mrange_eq_iSup

section Group

variable (G : ι → Type*) [∀ i, Group (G i)]

instance : Inv (CoprodI G)
    where inv :=
    MulOpposite.unop ∘ lift fun i => (of : G i →* _).op.comp (MulEquiv.inv' (G i)).toMonoidHom

theorem inv_def (x : CoprodI G) :
    x⁻¹ =
      MulOpposite.unop
        (lift (fun i => (of : G i →* _).op.comp (MulEquiv.inv' (G i)).toMonoidHom) x) :=
  rfl
#align free_product.inv_def Monoid.CoprodI.inv_def

instance : Group (CoprodI G) :=
  { inferInstanceAs (Inv (CoprodI G)), inferInstanceAs (Monoid (CoprodI G)) with
    mul_left_inv := by
      intro m
      -- ⊢ m⁻¹ * m = 1
      rw [inv_def]
      -- ⊢ MulOpposite.unop (↑(↑lift fun i => MonoidHom.comp (↑MonoidHom.op of) (MulEqu …
      induction m using CoprodI.induction_on with
      | h_one => rw [MonoidHom.map_one, MulOpposite.unop_one, one_mul]
      | h_of m ih =>
        change of _⁻¹ * of _ = 1
        rw [← of.map_mul, mul_left_inv, of.map_one]
      | h_mul x y ihx ihy =>
        rw [MonoidHom.map_mul, MulOpposite.unop_mul, mul_assoc, ← mul_assoc _ x y, ihx, one_mul,
          ihy] }

theorem lift_range_le {N} [Group N] (f : ∀ i, G i →* N) {s : Subgroup N}
    (h : ∀ i, (f i).range ≤ s) : (lift f).range ≤ s := by
  rintro _ ⟨x, rfl⟩
  -- ⊢ ↑(↑lift f) x ∈ s
  induction' x using CoprodI.induction_on with i x x y hx hy
  · exact s.one_mem
    -- 🎉 no goals
  · simp only [lift_of, SetLike.mem_coe]
    -- ⊢ ↑(f i) x ∈ s
    exact h i (Set.mem_range_self x)
    -- 🎉 no goals
  · simp only [map_mul, SetLike.mem_coe]
    -- ⊢ ↑(↑lift f) x * ↑(↑lift f) y ∈ s
    exact s.mul_mem hx hy
    -- 🎉 no goals
#align free_product.lift_range_le Monoid.CoprodI.lift_range_le

theorem range_eq_iSup {N} [Group N] (f : ∀ i, G i →* N) : (lift f).range = ⨆ i, (f i).range := by
  apply le_antisymm (lift_range_le _ f fun i => le_iSup (fun i => MonoidHom.range (f i)) i)
  -- ⊢ ⨆ (i : ι), MonoidHom.range (f i) ≤ MonoidHom.range (↑lift f)
  apply iSup_le _
  -- ⊢ ∀ (i : ι), MonoidHom.range (f i) ≤ MonoidHom.range (↑lift f)
  rintro i _ ⟨x, rfl⟩
  -- ⊢ ↑(f i) x ∈ MonoidHom.range (↑lift f)
  exact ⟨of x, by simp only [lift_of]⟩
  -- 🎉 no goals
#align free_product.range_eq_supr Monoid.CoprodI.range_eq_iSup

end Group

namespace Word

/-- The empty reduced word. -/
def empty : Word M where
  toList := []
  ne_one := by simp
               -- 🎉 no goals
  chain_ne := List.chain'_nil
#align free_product.word.empty Monoid.CoprodI.Word.empty

instance : Inhabited (Word M) :=
  ⟨empty⟩

/-- A reduced word determines an element of the free product, given by multiplication. -/
def prod (w : Word M) : CoprodI M :=
  List.prod (w.toList.map fun l => of l.snd)
#align free_product.word.prod Monoid.CoprodI.Word.prod

@[simp]
theorem prod_empty : prod (empty : Word M) = 1 :=
  rfl
#align free_product.word.prod_empty Monoid.CoprodI.Word.prod_empty

/-- `fstIdx w` is `some i` if the first letter of `w` is `⟨i, m⟩` with `m : M i`. If `w` is empty
then it's `none`. -/
def fstIdx (w : Word M) : Option ι :=
  w.toList.head?.map Sigma.fst
#align free_product.word.fst_idx Monoid.CoprodI.Word.fstIdx

theorem fstIdx_ne_iff {w : Word M} {i} :
    fstIdx w ≠ some i ↔ ∀ l ∈ w.toList.head?, i ≠ Sigma.fst l :=
  not_iff_not.mp <| by simp [fstIdx]
                       -- 🎉 no goals
#align free_product.word.fst_idx_ne_iff Monoid.CoprodI.Word.fstIdx_ne_iff

variable (M)

/-- Given an index `i : ι`, `Pair M i` is the type of pairs `(head, tail)` where `head : M i` and
`tail : Word M`, subject to the constraint that first letter of `tail` can't be `⟨i, m⟩`.
By prepending `head` to `tail`, one obtains a new word. We'll show that any word can be uniquely
obtained in this way. -/
@[ext]
structure Pair (i : ι) where
  /-- An element of `M i`, the first letter of the word. -/
  head : M i
  /-- The remaining letters of the word, excluding the first letter -/
  tail : Word M
  /-- The index first letter of tail of a `Pair M i` is not equal to `i` -/
  fstIdx_ne : fstIdx tail ≠ some i
#align free_product.word.pair Monoid.CoprodI.Word.Pair

instance (i : ι) : Inhabited (Pair M i) :=
  ⟨⟨1, empty, by tauto⟩⟩
                 -- 🎉 no goals

variable {M}

variable [∀ i, DecidableEq (M i)]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Given a pair `(head, tail)`, we can form a word by prepending `head` to `tail`, except if `head`
is `1 : M i` then we have to just return `Word` since we need the result to be reduced. -/
def rcons {i} (p : Pair M i) : Word M :=
  if h : p.head = 1 then p.tail
  else
    { toList := ⟨i, p.head⟩::p.tail.toList
      ne_one := by
        simp only [List.mem_cons]
        -- ⊢ ∀ (l : (i : ι) × M i), l = { fst := i, snd := p.head } ∨ l ∈ p.tail.toList → …
        rintro l (rfl | hl)
        -- ⊢ { fst := i, snd := p.head }.snd ≠ 1
        exact h
        -- ⊢ l.snd ≠ 1
        exact p.tail.ne_one l hl
        -- 🎉 no goals
      chain_ne := p.tail.chain_ne.cons' (fstIdx_ne_iff.mp p.fstIdx_ne) }
#align free_product.word.rcons Monoid.CoprodI.Word.rcons

/-- Given a word of the form `⟨l :: ls, h1, h2⟩`, we can form a word of the form `⟨ls, _, _⟩`,
dropping the first letter. -/
private def mkAux {l} (ls : List (Σi, M i)) (h1 : ∀ l' ∈ l::ls, Sigma.snd l' ≠ 1)
    (h2 : (l::ls).Chain' (fun l l' => Sigma.fst l ≠ Sigma.fst l')) : Word M :=
  ⟨ls, fun _ hl => h1 _ (List.mem_cons_of_mem _ hl), h2.tail⟩

theorem cons_eq_rcons {i} {m : M i} {ls h1 h2} :
    Word.mk (⟨i, m⟩::ls) h1 h2 = rcons ⟨m, mkAux ls h1 h2, fstIdx_ne_iff.mpr h2.rel_head?⟩ := by
  rw [rcons, dif_neg]
  -- ⊢ { toList := { fst := i, snd := m } :: ls, ne_one := h1, chain_ne := h2 } = { …
  rfl
  -- ⊢ ¬{ head := m, tail := Monoid.CoprodI.Word.mkAux ls h1 h2, fstIdx_ne := (_ :  …
  exact h1 ⟨i, m⟩ (ls.mem_cons_self _)
  -- 🎉 no goals
#align free_product.word.cons_eq_rcons Monoid.CoprodI.Word.cons_eq_rcons

@[simp]
theorem prod_rcons {i} (p : Pair M i) : prod (rcons p) = of p.head * prod p.tail :=
  if hm : p.head = 1 then by rw [rcons, dif_pos hm, hm, MonoidHom.map_one, one_mul]
                             -- 🎉 no goals
  else by rw [rcons, dif_neg hm, prod, List.map_cons, List.prod_cons, prod]
          -- 🎉 no goals
#align free_product.word.prod_rcons Monoid.CoprodI.Word.prod_rcons

theorem rcons_inj {i} : Function.Injective (rcons : Pair M i → Word M) := by
  rintro ⟨m, w, h⟩ ⟨m', w', h'⟩ he
  -- ⊢ { head := m, tail := w, fstIdx_ne := h } = { head := m', tail := w', fstIdx_ …
  by_cases hm : m = 1 <;> by_cases hm' : m' = 1
  -- ⊢ { head := m, tail := w, fstIdx_ne := h } = { head := m', tail := w', fstIdx_ …
                          -- ⊢ { head := m, tail := w, fstIdx_ne := h } = { head := m', tail := w', fstIdx_ …
                          -- ⊢ { head := m, tail := w, fstIdx_ne := h } = { head := m', tail := w', fstIdx_ …
  · simp only [rcons, dif_pos hm, dif_pos hm'] at he
    -- ⊢ { head := m, tail := w, fstIdx_ne := h } = { head := m', tail := w', fstIdx_ …
    aesop
    -- 🎉 no goals
  · exfalso
    -- ⊢ False
    simp only [rcons, dif_pos hm, dif_neg hm'] at he
    -- ⊢ False
    rw [he] at h
    -- ⊢ False
    exact h rfl
    -- 🎉 no goals
  · exfalso
    -- ⊢ False
    simp only [rcons, dif_pos hm', dif_neg hm] at he
    -- ⊢ False
    rw [← he] at h'
    -- ⊢ False
    exact h' rfl
    -- 🎉 no goals
  · have : m = m' ∧ w.toList = w'.toList := by
      simpa [rcons, dif_neg hm, dif_neg hm', true_and_iff, eq_self_iff_true, Subtype.mk_eq_mk,
        heq_iff_eq, ← Subtype.ext_iff_val] using he
    rcases this with ⟨rfl, h⟩
    -- ⊢ { head := m, tail := w, fstIdx_ne := h✝ } = { head := m, tail := w', fstIdx_ …
    congr
    -- ⊢ w = w'
    exact Word.ext _ _ h
    -- 🎉 no goals
#align free_product.word.rcons_inj Monoid.CoprodI.Word.rcons_inj

variable [DecidableEq ι]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- This definition is computable but not very nice to look at. Thankfully we don't have to inspect
-- it, since `rcons` is known to be injective.
/-- Given `i : ι`, any reduced word can be decomposed into a pair `p` such that `w = rcons p`. -/
private def equivPairAux (i) : ∀ w : Word M, { p : Pair M i // rcons p = w }
  | w@⟨[], _, _⟩ => ⟨⟨1, w, by subst w; simp [fstIdx]⟩, by subst w; simp [rcons]⟩
                               -- ⊢ fstIdx { toList := [], ne_one := ne_one✝, chain_ne := chain_ne✝ } ≠ some i
                                        -- 🎉 no goals
                                                           -- ⊢ rcons { head := 1, tail := { toList := [], ne_one := ne_one✝, chain_ne := ch …
                                                                    -- 🎉 no goals
  | w@⟨⟨j, m⟩::ls, h1, h2⟩ =>
    if ij : i = j then
      { val :=
          { head := ij.symm.rec m
            tail := mkAux ls h1 h2
            fstIdx_ne := by cases ij; exact fstIdx_ne_iff.mpr h2.rel_head? }
                            -- ⊢ fstIdx (Monoid.CoprodI.Word.mkAux ls h1 h2) ≠ some i
                                      -- 🎉 no goals
        property := by cases ij; exact cons_eq_rcons.symm }
                       -- ⊢ rcons { head := (_ : i = i) ▸ m, tail := Monoid.CoprodI.Word.mkAux ls h1 h2, …
                                 -- 🎉 no goals
    else ⟨⟨1, w, by subst w; exact (Option.some_injective _).ne (Ne.symm ij)⟩,
                    -- ⊢ fstIdx { toList := { fst := j, snd := m } :: ls, ne_one := h1, chain_ne := h …
                             -- 🎉 no goals
      by subst w; simp [rcons]⟩
         -- ⊢ rcons { head := 1, tail := { toList := { fst := j, snd := m } :: ls, ne_one  …
                  -- 🎉 no goals

/-- The equivalence between words and pairs. Given a word, it decomposes it as a pair by removing
the first letter if it comes from `M i`. Given a pair, it prepends the head to the tail. -/
def equivPair (i) : Word M ≃ Pair M i where
  toFun w := (equivPairAux i w).val
  invFun := rcons
  left_inv w := (equivPairAux i w).property
  right_inv _ := rcons_inj (equivPairAux i _).property
#align free_product.word.equiv_pair Monoid.CoprodI.Word.equivPair

theorem equivPair_symm (i) (p : Pair M i) : (equivPair i).symm p = rcons p :=
  rfl
#align free_product.word.equiv_pair_symm Monoid.CoprodI.Word.equivPair_symm

theorem equivPair_eq_of_fstIdx_ne {i} {w : Word M} (h : fstIdx w ≠ some i) :
    equivPair i w = ⟨1, w, h⟩ :=
  (equivPair i).apply_eq_iff_eq_symm_apply.mpr <| Eq.symm (dif_pos rfl)
#align free_product.word.equiv_pair_eq_of_fst_idx_ne Monoid.CoprodI.Word.equivPair_eq_of_fstIdx_ne

instance summandAction (i) : MulAction (M i) (Word M) where
  smul m w := rcons { equivPair i w with head := m * (equivPair i w).head }
  one_smul w := by
    apply (equivPair i).symm_apply_eq.mpr
    -- ⊢ (let src := ↑(equivPair i) w;
    simp [equivPair]
    -- 🎉 no goals
  mul_smul m m' w := by
    dsimp [instHSMul]
    -- ⊢ rcons { head := m * m' * (↑(equivPair i) w).head, tail := (↑(equivPair i) w) …
    simp [mul_assoc, ← equivPair_symm, Equiv.apply_symm_apply]
    -- 🎉 no goals
#align free_product.word.summand_action Monoid.CoprodI.Word.summandAction

instance : MulAction (CoprodI M) (Word M) :=
  MulAction.ofEndHom (lift fun _ => MulAction.toEndHom)

theorem of_smul_def (i) (w : Word M) (m : M i) :
    of m • w = rcons { equivPair i w with head := m * (equivPair i w).head } :=
  rfl
#align free_product.word.of_smul_def Monoid.CoprodI.Word.of_smul_def

theorem cons_eq_smul {i} {m : M i} {ls h1 h2} :
    Word.mk (⟨i, m⟩::ls) h1 h2 = of m • mkAux ls h1 h2 := by
  rw [cons_eq_rcons, of_smul_def, equivPair_eq_of_fstIdx_ne _]
  -- ⊢ rcons { head := m, tail := Monoid.CoprodI.Word.mkAux ls h1 h2, fstIdx_ne :=  …
  · simp
    -- 🎉 no goals
  · rw [fstIdx_ne_iff]
    -- ⊢ ∀ (l : (i : ι) × M i), l ∈ List.head? (Monoid.CoprodI.Word.mkAux ls h1 h2).t …
    exact (List.chain'_cons'.1 h2).1
    -- 🎉 no goals
#align free_product.word.cons_eq_smul Monoid.CoprodI.Word.cons_eq_smul

theorem smul_induction {C : Word M → Prop} (h_empty : C empty)
    (h_smul : ∀ (i) (m : M i) (w), C w → C (of m • w)) (w : Word M) : C w := by
  cases' w with ls h1 h2
  -- ⊢ C { toList := ls, ne_one := h1, chain_ne := h2 }
  induction' ls with l ls ih
  -- ⊢ C { toList := [], ne_one := h1, chain_ne := h2 }
  · exact h_empty
    -- 🎉 no goals
  cases' l with i m
  -- ⊢ C { toList := { fst := i, snd := m } :: ls, ne_one := h1, chain_ne := h2 }
  rw [cons_eq_smul]
  -- ⊢ C (↑of m • Monoid.CoprodI.Word.mkAux ls h1 h2)
  exact h_smul _ _ _ (ih _ _)
  -- 🎉 no goals
#align free_product.word.smul_induction Monoid.CoprodI.Word.smul_induction

@[simp]
theorem prod_smul (m) : ∀ w : Word M, prod (m • w) = m * prod w := by
  induction m using CoprodI.induction_on with
  | h_one =>
    intro
    rw [one_smul, one_mul]
  | h_of _ =>
    intros
    rw [of_smul_def, prod_rcons, of.map_mul, mul_assoc, ← prod_rcons, ← equivPair_symm,
      Equiv.symm_apply_apply]
  | h_mul x y hx hy =>
    intro w
    rw [mul_smul, hx, hy, mul_assoc]
#align free_product.word.prod_smul Monoid.CoprodI.Word.prod_smul

/-- Each element of the free product corresponds to a unique reduced word. -/
def equiv : CoprodI M ≃ Word M where
  toFun m := m • empty
  invFun w := prod w
  left_inv m := by dsimp only; rw [prod_smul, prod_empty, mul_one]
                   -- ⊢ prod (m • empty) = m
                               -- 🎉 no goals
  right_inv := by
    apply smul_induction
    -- ⊢ (fun m => m • empty) ((fun w => prod w) empty) = empty
    · dsimp only
      -- ⊢ prod empty • empty = empty
      rw [prod_empty, one_smul]
      -- 🎉 no goals
    · dsimp only
      -- ⊢ ∀ (i : ι) (m : M i) (w : Word M), prod w • empty = w → prod (↑of m • w) • em …
      intro i m w ih
      -- ⊢ prod (↑of m • w) • empty = ↑of m • w
      rw [prod_smul, mul_smul, ih]
      -- 🎉 no goals
#align free_product.word.equiv Monoid.CoprodI.Word.equiv

instance : DecidableEq (Word M) :=
  Function.Injective.decidableEq Word.ext

instance : DecidableEq (CoprodI M) :=
  Equiv.decidableEq Word.equiv

end Word

variable (M)

/-- A `NeWord M i j` is a representation of a non-empty reduced words where the first letter comes
from `M i` and the last letter comes from `M j`. It can be constructed from singletons and via
concatenation, and thus provides a useful induction principle. -/
--@[nolint has_nonempty_instance] Porting note: commented out
inductive NeWord : ι → ι → Type _
  | singleton : ∀ {i : ι} (x : M i), x ≠ 1 → NeWord i i
  | append : ∀ {i j k l} (_w₁ : NeWord i j) (_hne : j ≠ k) (_w₂ : NeWord k l), NeWord i l
#align free_product.neword Monoid.CoprodI.NeWord

variable {M}

namespace NeWord

open Word

/-- The list represented by a given `NeWord` -/
@[simp]
def toList : ∀ {i j} (_w : NeWord M i j), List (Σi, M i)
  | i, _, singleton x _ => [⟨i, x⟩]
  | _, _, append w₁ _ w₂ => w₁.toList ++ w₂.toList
#align free_product.neword.to_list Monoid.CoprodI.NeWord.toList

theorem toList_ne_nil {i j} (w : NeWord M i j) : w.toList ≠ List.nil := by
  induction w
  -- ⊢ toList (singleton x✝ a✝) ≠ []
  · rintro ⟨rfl⟩
    -- 🎉 no goals
  · apply List.append_ne_nil_of_ne_nil_left
    -- ⊢ toList _w₁✝ ≠ []
    assumption
    -- 🎉 no goals
#align free_product.neword.to_list_ne_nil Monoid.CoprodI.NeWord.toList_ne_nil

/-- The first letter of a `NeWord` -/
@[simp]
def head : ∀ {i j} (_w : NeWord M i j), M i
  | _, _, singleton x _ => x
  | _, _, append w₁ _ _ => w₁.head
#align free_product.neword.head Monoid.CoprodI.NeWord.head

/-- The last letter of a `NeWord` -/
@[simp]
def last : ∀ {i j} (_w : NeWord M i j), M j
  | _, _, singleton x _hne1 => x
  | _, _, append _w₁ _hne w₂ => w₂.last
#align free_product.neword.last Monoid.CoprodI.NeWord.last

@[simp]
theorem toList_head? {i j} (w : NeWord M i j) : w.toList.head? = Option.some ⟨i, w.head⟩ := by
  rw [← Option.mem_def]
  -- ⊢ { fst := i, snd := head w } ∈ List.head? (toList w)
  induction w
  -- ⊢ { fst := i✝, snd := head (singleton x✝ a✝) } ∈ List.head? (toList (singleton …
  · rw [Option.mem_def]
    -- ⊢ List.head? (toList (singleton x✝ a✝)) = some { fst := i✝, snd := head (singl …
    rfl
    -- 🎉 no goals
  · exact List.head?_append (by assumption)
    -- 🎉 no goals
#align free_product.neword.to_list_head' Monoid.CoprodI.NeWord.toList_head?

@[simp]
theorem toList_getLast? {i j} (w : NeWord M i j) : w.toList.getLast? = Option.some ⟨j, w.last⟩ := by
  rw [← Option.mem_def]
  -- ⊢ { fst := j, snd := last w } ∈ List.getLast? (toList w)
  induction w
  -- ⊢ { fst := i✝, snd := last (singleton x✝ a✝) } ∈ List.getLast? (toList (single …
  · rw [Option.mem_def]
    -- ⊢ List.getLast? (toList (singleton x✝ a✝)) = some { fst := i✝, snd := last (si …
    rfl
    -- 🎉 no goals
  · exact List.getLast?_append (by assumption)
    -- 🎉 no goals
#align free_product.neword.to_list_last' Monoid.CoprodI.NeWord.toList_getLast?

/-- The `Word M` represented by a `NeWord M i j` -/
def toWord {i j} (w : NeWord M i j) : Word M
    where
  toList := w.toList
  ne_one := by
    induction w
    -- ⊢ ∀ (l : (i : ι) × M i), l ∈ toList (singleton x✝ a✝) → l.snd ≠ 1
    · simpa only [toList, List.mem_singleton, ne_eq, forall_eq]
      -- 🎉 no goals
    · intro l h
      -- ⊢ l.snd ≠ 1
      simp only [toList, List.mem_append] at h
      -- ⊢ l.snd ≠ 1
      cases h <;> aesop
      -- ⊢ l.snd ≠ 1
                  -- 🎉 no goals
                  -- 🎉 no goals
  chain_ne := by
    induction w
    -- ⊢ List.Chain' (fun l l' => l.fst ≠ l'.fst) (toList (singleton x✝ a✝))
    · exact List.chain'_singleton _
      -- 🎉 no goals
    · refine List.Chain'.append (by assumption) (by assumption) ?_
      -- ⊢ ∀ (x : (i : ι) × M i), x ∈ List.getLast? (toList _w₁✝) → ∀ (y : (i : ι) × M  …
      intro x hx y hy
      -- ⊢ x.fst ≠ y.fst
      rw [toList_getLast?, Option.mem_some_iff] at hx
      -- ⊢ x.fst ≠ y.fst
      rw [toList_head?, Option.mem_some_iff] at hy
      -- ⊢ x.fst ≠ y.fst
      subst hx
      -- ⊢ { fst := j✝, snd := last _w₁✝ }.fst ≠ y.fst
      subst hy
      -- ⊢ { fst := j✝, snd := last _w₁✝ }.fst ≠ { fst := k✝, snd := head _w₂✝ }.fst
      assumption
      -- 🎉 no goals
#align free_product.neword.to_word Monoid.CoprodI.NeWord.toWord

/-- Every nonempty `Word M` can be constructed as a `NeWord M i j` -/
theorem of_word (w : Word M) (h : w ≠ empty) : ∃ (i j : _) (w' : NeWord M i j), w'.toWord = w := by
  suffices : ∃ (i j : _) (w' : NeWord M i j), w'.toWord.toList = w.toList
  -- ⊢ ∃ i j w', toWord w' = w
  · rcases this with ⟨i, j, w, h⟩
    -- ⊢ ∃ i j w', toWord w' = w✝
    refine' ⟨i, j, w, _⟩
    -- ⊢ toWord w = w✝
    ext
    -- ⊢ a✝ ∈ List.get? (toWord w).toList n✝ ↔ a✝ ∈ List.get? w✝.toList n✝
    rw [h]
    -- 🎉 no goals
  cases' w with l hnot1 hchain
  -- ⊢ ∃ i j w', (toWord w').toList = { toList := l, ne_one := hnot1, chain_ne := h …
  induction' l with x l hi
  -- ⊢ ∃ i j w', (toWord w').toList = { toList := [], ne_one := hnot1, chain_ne :=  …
  · contradiction
    -- 🎉 no goals
  · rw [List.forall_mem_cons] at hnot1
    -- ⊢ ∃ i j w', (toWord w').toList = { toList := x :: l, ne_one := hnot1✝, chain_n …
    cases' l with y l
    -- ⊢ ∃ i j w', (toWord w').toList = { toList := [x], ne_one := hnot1✝, chain_ne : …
    · refine' ⟨x.1, x.1, singleton x.2 hnot1.1, _⟩
      -- ⊢ (toWord (singleton x.snd (_ : x.snd ≠ 1))).toList = { toList := [x], ne_one  …
      simp [toWord]
      -- 🎉 no goals
    · rw [List.chain'_cons] at hchain
      -- ⊢ ∃ i j w', (toWord w').toList = { toList := x :: y :: l, ne_one := hnot1✝, ch …
      specialize hi hnot1.2 hchain.2 (by rintro ⟨rfl⟩)
      -- ⊢ ∃ i j w', (toWord w').toList = { toList := x :: y :: l, ne_one := hnot1✝, ch …
      obtain ⟨i, j, w', hw' : w'.toList = y::l⟩ := hi
      -- ⊢ ∃ i j w', (toWord w').toList = { toList := x :: y :: l, ne_one := hnot1✝, ch …
      obtain rfl : y = ⟨i, w'.head⟩ := by simpa [hw'] using w'.toList_head?
      -- ⊢ ∃ i_1 j_1 w'_1, (toWord w'_1).toList = { toList := x :: { fst := i, snd := h …
      refine' ⟨x.1, j, append (singleton x.2 hnot1.1) hchain.1 w', _⟩
      -- ⊢ (toWord (append (singleton x.snd (_ : x.snd ≠ 1)) (_ : x.fst ≠ { fst := i, s …
      · simpa [toWord] using hw'
        -- 🎉 no goals
#align free_product.neword.of_word Monoid.CoprodI.NeWord.of_word

/-- A non-empty reduced word determines an element of the free product, given by multiplication. -/
def prod {i j} (w : NeWord M i j) :=
  w.toWord.prod
#align free_product.neword.prod Monoid.CoprodI.NeWord.prod

@[simp]
theorem singleton_head {i} (x : M i) (hne_one : x ≠ 1) : (singleton x hne_one).head = x :=
  rfl
#align free_product.neword.singleton_head Monoid.CoprodI.NeWord.singleton_head

@[simp]
theorem singleton_last {i} (x : M i) (hne_one : x ≠ 1) : (singleton x hne_one).last = x :=
  rfl
#align free_product.neword.singleton_last Monoid.CoprodI.NeWord.singleton_last

@[simp]
theorem prod_singleton {i} (x : M i) (hne_one : x ≠ 1) : (singleton x hne_one).prod = of x := by
  simp [toWord, prod, Word.prod]
  -- 🎉 no goals
#align free_product.neword.prod_singleton Monoid.CoprodI.NeWord.prod_singleton

@[simp]
theorem append_head {i j k l} {w₁ : NeWord M i j} {hne : j ≠ k} {w₂ : NeWord M k l} :
    (append w₁ hne w₂).head = w₁.head :=
  rfl
#align free_product.neword.append_head Monoid.CoprodI.NeWord.append_head

@[simp]
theorem append_last {i j k l} {w₁ : NeWord M i j} {hne : j ≠ k} {w₂ : NeWord M k l} :
    (append w₁ hne w₂).last = w₂.last :=
  rfl
#align free_product.neword.append_last Monoid.CoprodI.NeWord.append_last

@[simp]
theorem append_prod {i j k l} {w₁ : NeWord M i j} {hne : j ≠ k} {w₂ : NeWord M k l} :
    (append w₁ hne w₂).prod = w₁.prod * w₂.prod := by simp [toWord, prod, Word.prod]
                                                      -- 🎉 no goals
#align free_product.neword.append_prod Monoid.CoprodI.NeWord.append_prod

/-- One can replace the first letter in a non-empty reduced word by an element of the same
group -/
def replaceHead : ∀ {i j : ι} (x : M i) (_hnotone : x ≠ 1) (_w : NeWord M i j), NeWord M i j
  | _, _, x, h, singleton _ _ => singleton x h
  | _, _, x, h, append w₁ hne w₂ => append (replaceHead x h w₁) hne w₂
#align free_product.neword.replace_head Monoid.CoprodI.NeWord.replaceHead

@[simp]
theorem replaceHead_head {i j : ι} (x : M i) (hnotone : x ≠ 1) (w : NeWord M i j) :
    (replaceHead x hnotone w).head = x := by
  induction w
  -- ⊢ head (replaceHead x hnotone (singleton x✝ a✝)) = x
  rfl
  -- ⊢ head (replaceHead x hnotone (append _w₁✝ _hne✝ _w₂✝)) = x
  simp [*]
  -- 🎉 no goals
#align free_product.neword.replace_head_head Monoid.CoprodI.NeWord.replaceHead_head

/-- One can multiply an element from the left to a non-empty reduced word if it does not cancel
with the first element in the word. -/
def mulHead {i j : ι} (w : NeWord M i j) (x : M i) (hnotone : x * w.head ≠ 1) : NeWord M i j :=
  replaceHead (x * w.head) hnotone w
#align free_product.neword.mul_head Monoid.CoprodI.NeWord.mulHead

@[simp]
theorem mulHead_head {i j : ι} (w : NeWord M i j) (x : M i) (hnotone : x * w.head ≠ 1) :
    (mulHead w x hnotone).head = x * w.head := by
  induction w
  -- ⊢ head (mulHead (singleton x✝ a✝) x hnotone) = x * head (singleton x✝ a✝)
  rfl
  -- ⊢ head (mulHead (append _w₁✝ _hne✝ _w₂✝) x hnotone) = x * head (append _w₁✝ _h …
  simp [*]
  -- 🎉 no goals
#align free_product.neword.mul_head_head Monoid.CoprodI.NeWord.mulHead_head

@[simp]
theorem mulHead_prod {i j : ι} (w : NeWord M i j) (x : M i) (hnotone : x * w.head ≠ 1) :
    (mulHead w x hnotone).prod = of x * w.prod := by
  unfold mulHead
  -- ⊢ prod (replaceHead (x * head w) hnotone w) = ↑of x * prod w
  induction' w with _ _ _ _ _ _ _ _ _ _ w_ih_w₁ w_ih_w₂
  -- ⊢ prod (replaceHead (x * head (singleton x✝ a✝)) hnotone (singleton x✝ a✝)) =  …
  · simp [mulHead, replaceHead]
    -- 🎉 no goals
  · specialize w_ih_w₁ _ hnotone
    -- ⊢ prod (replaceHead (x * head (append _w₁✝ _hne✝ _w₂✝)) hnotone (append _w₁✝ _ …
    clear w_ih_w₂
    -- ⊢ prod (replaceHead (x * head (append _w₁✝ _hne✝ _w₂✝)) hnotone (append _w₁✝ _ …
    simp [replaceHead, ← mul_assoc] at *
    -- ⊢ prod (replaceHead (x * head _w₁✝) (_ : x * head _w₁✝ ≠ 1) _w₁✝) * prod _w₂✝  …
    congr 1
    -- 🎉 no goals
#align free_product.neword.mul_head_prod Monoid.CoprodI.NeWord.mulHead_prod

section Group

variable {G : ι → Type*} [∀ i, Group (G i)]

/-- The inverse of a non-empty reduced word -/
def inv : ∀ {i j} (_w : NeWord G i j), NeWord G j i
  | _, _, singleton x h => singleton x⁻¹ (mt inv_eq_one.mp h)
  | _, _, append w₁ h w₂ => append w₂.inv h.symm w₁.inv
#align free_product.neword.inv Monoid.CoprodI.NeWord.inv

@[simp]
theorem inv_prod {i j} (w : NeWord G i j) : w.inv.prod = w.prod⁻¹ := by
  induction w <;> simp [inv, *]
  -- ⊢ prod (inv (singleton x✝ a✝)) = (prod (singleton x✝ a✝))⁻¹
                  -- 🎉 no goals
                  -- 🎉 no goals
#align free_product.neword.inv_prod Monoid.CoprodI.NeWord.inv_prod

@[simp]
theorem inv_head {i j} (w : NeWord G i j) : w.inv.head = w.last⁻¹ := by
  induction w <;> simp [inv, *]
  -- ⊢ head (inv (singleton x✝ a✝)) = (last (singleton x✝ a✝))⁻¹
                  -- 🎉 no goals
                  -- 🎉 no goals
#align free_product.neword.inv_head Monoid.CoprodI.NeWord.inv_head

@[simp]
theorem inv_last {i j} (w : NeWord G i j) : w.inv.last = w.head⁻¹ := by
  induction w <;> simp [inv, *]
  -- ⊢ last (inv (singleton x✝ a✝)) = (head (singleton x✝ a✝))⁻¹
                  -- 🎉 no goals
                  -- 🎉 no goals
#align free_product.neword.inv_last Monoid.CoprodI.NeWord.inv_last

end Group

end NeWord

section PingPongLemma

open Pointwise

open Cardinal

variable [hnontriv : Nontrivial ι]

variable {G : Type*} [Group G]

variable {H : ι → Type*} [∀ i, Group (H i)]

variable (f : ∀ i, H i →* G)

-- We need many groups or one group with many elements
variable (hcard : 3 ≤ #ι ∨ ∃ i, 3 ≤ #(H i))

-- A group action on α, and the ping-pong sets
variable {α : Type*} [MulAction G α]

variable (X : ι → Set α)

variable (hXnonempty : ∀ i, (X i).Nonempty)

variable (hXdisj : Pairwise fun i j => Disjoint (X i) (X j))

variable (hpp : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • X j ⊆ X i)

--include hpp Porting note: commented out

theorem lift_word_ping_pong {i j k} (w : NeWord H i j) (hk : j ≠ k) :
    lift f w.prod • X k ⊆ X i := by
  induction' w with i x hne_one i j k l w₁ hne w₂ hIw₁ hIw₂ generalizing k
  -- ⊢ ↑(↑lift f) (NeWord.prod (NeWord.singleton x hne_one)) • X k ⊆ X i
  · simpa using hpp hk _ hne_one
    -- 🎉 no goals
  · calc
      lift f (NeWord.append w₁ hne w₂).prod • X k = lift f w₁.prod • lift f w₂.prod • X k := by
        simp [MulAction.mul_smul]
      _ ⊆ lift f w₁.prod • X _ := (set_smul_subset_set_smul_iff.mpr (hIw₂ hk))
      _ ⊆ X i := hIw₁ hne
#align free_product.lift_word_ping_pong Monoid.CoprodI.lift_word_ping_pong

--include X hXnonempty hXdisj Porting note: commented out

theorem lift_word_prod_nontrivial_of_other_i {i j k} (w : NeWord H i j) (hhead : k ≠ i)
    (hlast : k ≠ j) : lift f w.prod ≠ 1 := by
  intro heq1
  -- ⊢ False
  have : X k ⊆ X i := by simpa [heq1] using lift_word_ping_pong f X hpp w hlast.symm
  -- ⊢ False
  obtain ⟨x, hx⟩ := hXnonempty k
  -- ⊢ False
  exact (hXdisj hhead).le_bot ⟨hx, this hx⟩
  -- 🎉 no goals
#align free_product.lift_word_prod_nontrivial_of_other_i Monoid.CoprodI.lift_word_prod_nontrivial_of_other_i

--include hnontriv Porting note: commented out

theorem lift_word_prod_nontrivial_of_head_eq_last {i} (w : NeWord H i i) : lift f w.prod ≠ 1 := by
  obtain ⟨k, hk⟩ := exists_ne i
  -- ⊢ ↑(↑lift f) (NeWord.prod w) ≠ 1
  exact lift_word_prod_nontrivial_of_other_i f X hXnonempty hXdisj hpp w hk hk
  -- 🎉 no goals
#align free_product.lift_word_prod_nontrivial_of_head_eq_last Monoid.CoprodI.lift_word_prod_nontrivial_of_head_eq_last

theorem lift_word_prod_nontrivial_of_head_card {i j} (w : NeWord H i j) (hcard : 3 ≤ #(H i))
    (hheadtail : i ≠ j) : lift f w.prod ≠ 1 := by
  obtain ⟨h, hn1, hnh⟩ := Cardinal.three_le hcard 1 w.head⁻¹
  -- ⊢ ↑(↑lift f) (NeWord.prod w) ≠ 1
  have hnot1 : h * w.head ≠ 1 := by
    rw [← div_inv_eq_mul]
    exact div_ne_one_of_ne hnh
  let w' : NeWord H i i :=
    NeWord.append (NeWord.mulHead w h hnot1) hheadtail.symm
      (NeWord.singleton h⁻¹ (inv_ne_one.mpr hn1))
  have hw' : lift f w'.prod ≠ 1 :=
    lift_word_prod_nontrivial_of_head_eq_last f X hXnonempty hXdisj hpp w'
  intro heq1
  -- ⊢ False
  apply hw'
  -- ⊢ ↑(↑lift f) (NeWord.prod w') = 1
  simp [heq1]
  -- 🎉 no goals
#align free_product.lift_word_prod_nontrivial_of_head_card Monoid.CoprodI.lift_word_prod_nontrivial_of_head_card

--include hcard Porting note: commented out

theorem lift_word_prod_nontrivial_of_not_empty {i j} (w : NeWord H i j) : lift f w.prod ≠ 1 := by
  classical
    cases' hcard with hcard hcard
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
        simpa using heq
      · change i ≠ k at hh
        change j ≠ k at hl
        obtain ⟨h, hn1, -⟩ := Cardinal.three_le hcard 1 1
        let w' : NeWord H k k :=
          NeWord.append (NeWord.append (NeWord.singleton h hn1) hh.symm w) hl
            (NeWord.singleton h⁻¹ (inv_ne_one.mpr hn1))
        have hw' : lift f w'.prod ≠ 1 :=
          lift_word_prod_nontrivial_of_head_eq_last f X hXnonempty hXdisj hpp w'
        intro heq1
        apply hw'
        simp [heq1]
#align free_product.lift_word_prod_nontrivial_of_not_empty Monoid.CoprodI.lift_word_prod_nontrivial_of_not_empty

theorem empty_of_word_prod_eq_one {w : Word H} (h : lift f w.prod = 1) : w = Word.empty := by
  by_contra hnotempty
  -- ⊢ False
  obtain ⟨i, j, w, rfl⟩ := NeWord.of_word w hnotempty
  -- ⊢ False
  exact lift_word_prod_nontrivial_of_not_empty f hcard X hXnonempty hXdisj hpp w h
  -- 🎉 no goals
#align free_product.empty_of_word_prod_eq_one Monoid.CoprodI.empty_of_word_prod_eq_one

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
    rw [(CoprodI.Word.equiv).forall_congr_left']
    · intro w Heq
      dsimp [Word.equiv] at *
      · rw [empty_of_word_prod_eq_one f hcard X hXnonempty hXdisj hpp Heq]
        rfl
#align free_product.lift_injective_of_ping_pong Monoid.CoprodI.lift_injective_of_ping_pong

end PingPongLemma

/-- The free product of free groups is itself a free group -/
@[simps!]  --Porting note: added `!`
instance {ι : Type*} (G : ι → Type*) [∀ i, Group (G i)] [hG : ∀ i, IsFreeGroup (G i)] :
    IsFreeGroup (CoprodI G) where
  Generators := Σi, IsFreeGroup.Generators (G i)
  MulEquiv' :=
    MonoidHom.toMulEquiv
      (FreeGroup.lift fun x : Σi, IsFreeGroup.Generators (G i) =>
        CoprodI.of (IsFreeGroup.of x.2 : G x.1))
      (CoprodI.lift fun i : ι =>
        (IsFreeGroup.lift fun x : IsFreeGroup.Generators (G i) =>
            FreeGroup.of (⟨i, x⟩ : Σi, IsFreeGroup.Generators (G i)) :
          G i →* FreeGroup (Σi, IsFreeGroup.Generators (G i))))
      (by ext; simp)
          -- ⊢ ↑(MonoidHom.comp (↑lift fun i => ↑IsFreeGroup.lift fun x => FreeGroup.of { f …
               -- 🎉 no goals
      (by ext; simp)
          -- ⊢ ↑(MonoidHom.comp (MonoidHom.comp (↑FreeGroup.lift fun x => ↑of (IsFreeGroup. …
               -- 🎉 no goals

-- NB: One might expect this theorem to be phrased with ℤ, but ℤ is an additive group,
-- and using `Multiplicative ℤ` runs into diamond issues.
/-- A free group is a free product of copies of the free_group over one generator. -/
@[simps!]
def _root_.freeGroupEquivCoprodI {ι : Type u_1} :
    FreeGroup ι ≃* CoprodI fun _ : ι => FreeGroup Unit := by
  refine' MonoidHom.toMulEquiv _ _ _ _
  exact FreeGroup.lift fun i => @CoprodI.of ι _ _ i (FreeGroup.of Unit.unit)
  exact CoprodI.lift fun i => FreeGroup.lift fun _ => FreeGroup.of i
  -- ⊢ MonoidHom.comp (↑lift fun i => ↑FreeGroup.lift fun x => FreeGroup.of i) (↑Fr …
  · ext; simp
    -- ⊢ ↑(MonoidHom.comp (↑lift fun i => ↑FreeGroup.lift fun x => FreeGroup.of i) (↑ …
         -- 🎉 no goals
  · ext i a; cases a; simp
    -- ⊢ ↑(MonoidHom.comp (MonoidHom.comp (↑FreeGroup.lift fun i => ↑of (FreeGroup.of …
             -- ⊢ ↑(MonoidHom.comp (MonoidHom.comp (↑FreeGroup.lift fun i => ↑of (FreeGroup.of …
                      -- 🎉 no goals
#align free_group_equiv_free_product freeGroupEquivCoprodI

section PingPongLemma

open Pointwise Cardinal

variable [Nontrivial ι]

variable {G : Type u_1} [Group G] (a : ι → G)

-- A group action on α, and the ping-pong sets
variable {α : Type*} [MulAction G α]

variable (X Y : ι → Set α)

variable (hXnonempty : ∀ i, (X i).Nonempty)

variable (hXdisj : Pairwise fun i j => Disjoint (X i) (X j))

variable (hYdisj : Pairwise fun i j => Disjoint (Y i) (Y j))

variable (hXYdisj : ∀ i j, Disjoint (X i) (Y j))

variable (hX : ∀ i, a i • (Y i)ᶜ ⊆ X i)

variable (hY : ∀ i, a⁻¹ i • (X i)ᶜ ⊆ Y i)

--include hXnonempty hXdisj hYdisj hXYdisj hX hY Porting note: commented out

/-- The Ping-Pong-Lemma.

Given a group action of `G` on `X` so that the generators of the free groups act in specific
ways on disjoint subsets `X i` and `Y i` we can prove that `lift f` is injective, and thus the image
of `lift f` is isomorphic to the free group.

Often the Ping-Pong-Lemma is stated with regard to group elements that generate the whole group;
we generalize to arbitrary group homomorphisms from the free group to `G` and do not require the
group to be generated by the elements.
-/
theorem _root_.FreeGroup.injective_lift_of_ping_pong : Function.Injective (FreeGroup.lift a) := by
  -- Step one: express the free group lift via the free product lift
  have : FreeGroup.lift a =
      (CoprodI.lift fun i => FreeGroup.lift fun _ => a i).comp
        (@freeGroupEquivCoprodI ι).toMonoidHom := by
    ext i
    simp
  rw [this, MonoidHom.coe_comp]
  -- ⊢ Function.Injective (↑(↑lift fun i => ↑FreeGroup.lift fun x => a i) ∘ ↑(MulEq …
  clear this
  -- ⊢ Function.Injective (↑(↑lift fun i => ↑FreeGroup.lift fun x => a i) ∘ ↑(MulEq …
  refine' Function.Injective.comp _ (MulEquiv.injective freeGroupEquivCoprodI)
  -- ⊢ Function.Injective ↑(↑lift fun i => ↑FreeGroup.lift fun x => a i)
  -- Step two: Invoke the ping-pong lemma for free products
  show Function.Injective (lift fun i : ι => FreeGroup.lift fun _ => a i)
  -- ⊢ Function.Injective ↑(↑lift fun i => ↑FreeGroup.lift fun x => a i)
  -- Prepare to instantiate lift_injective_of_ping_pong
  let H : ι → Type _ := fun _i => FreeGroup Unit
  -- ⊢ Function.Injective ↑(↑lift fun i => ↑FreeGroup.lift fun x => a i)
  let f : ∀ i, H i →* G := fun i => FreeGroup.lift fun _ => a i
  -- ⊢ Function.Injective ↑(↑lift fun i => ↑FreeGroup.lift fun x => a i)
  let X' : ι → Set α := fun i => X i ∪ Y i
  -- ⊢ Function.Injective ↑(↑lift fun i => ↑FreeGroup.lift fun x => a i)
  apply lift_injective_of_ping_pong f _ X'
  show ∀ i, (X' i).Nonempty
  · exact fun i => Set.Nonempty.inl (hXnonempty i)
    -- 🎉 no goals
  show Pairwise fun i j => Disjoint (X' i) (X' j)
  · intro i j hij
    -- ⊢ Disjoint (X' i) (X' j)
    simp only
    -- ⊢ Disjoint (X i ∪ Y i) (X j ∪ Y j)
    apply Disjoint.union_left <;> apply Disjoint.union_right
    -- ⊢ Disjoint (X i) (X j ∪ Y j)
                                  -- ⊢ Disjoint (X i) (X j)
                                  -- ⊢ Disjoint (Y i) (X j)
    · exact hXdisj hij
      -- 🎉 no goals
    · exact hXYdisj i j
      -- 🎉 no goals
    · exact (hXYdisj j i).symm
      -- 🎉 no goals
    · exact hYdisj hij
      -- 🎉 no goals
  show Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • X' j ⊆ X' i
  -- ⊢ Pairwise fun i j => ∀ (h : H i), h ≠ 1 → ↑(f i) h • X' j ⊆ X' i
  · rintro i j hij
    -- ⊢ ∀ (h : H i), h ≠ 1 → ↑(f i) h • X' j ⊆ X' i
    -- use free_group unit ≃ ℤ
    refine' FreeGroup.freeGroupUnitEquivInt.forall_congr_left'.mpr _
    -- ⊢ ∀ (y : ℤ), ↑FreeGroup.freeGroupUnitEquivInt.symm y ≠ 1 → ↑(f i) (↑FreeGroup. …
    intro n hne1
    -- ⊢ ↑(f i) (↑FreeGroup.freeGroupUnitEquivInt.symm n) • X' j ⊆ X' i
    change FreeGroup.lift (fun _ => a i) (FreeGroup.of () ^ n) • X' j ⊆ X' i
    -- ⊢ ↑(↑FreeGroup.lift fun x => a i) (FreeGroup.of () ^ n) • X' j ⊆ X' i
    simp only [map_zpow, FreeGroup.lift.of]
    -- ⊢ a i ^ n • (X j ∪ Y j) ⊆ X i ∪ Y i
    change a i ^ n • X' j ⊆ X' i
    -- ⊢ a i ^ n • X' j ⊆ X' i
    have hnne0 : n ≠ 0 := by
      rintro rfl
      apply hne1
      simp; rfl
    clear hne1
    -- ⊢ a i ^ n • X' j ⊆ X' i
    simp only
    -- ⊢ a i ^ n • (X j ∪ Y j) ⊆ X i ∪ Y i
    -- Positive and negative powers separately
    cases' (lt_or_gt_of_ne hnne0).symm with hlt hgt
    -- ⊢ a i ^ n • (X j ∪ Y j) ⊆ X i ∪ Y i
    · have h1n : 1 ≤ n := hlt
      -- ⊢ a i ^ n • (X j ∪ Y j) ⊆ X i ∪ Y i
      calc
        a i ^ n • X' j ⊆ a i ^ n • (Y i)ᶜ :=
          smul_set_mono ((hXYdisj j i).union_left <| hYdisj hij.symm).subset_compl_right
        _ ⊆ X i := by
          clear hnne0 hlt
          refine Int.le_induction (P := fun n => a i ^ n • (Y i)ᶜ ⊆ X i) ?_ ?_ n h1n
          · dsimp
            rw [zpow_one]
            exact hX i
          · dsimp
            intro n _hle hi
            calc
              a i ^ (n + 1) • (Y i)ᶜ = (a i ^ n * a i) • (Y i)ᶜ := by rw [zpow_add, zpow_one]
              _ = a i ^ n • a i • (Y i)ᶜ := (MulAction.mul_smul _ _ _)
              _ ⊆ a i ^ n • X i := (smul_set_mono <| hX i)
              _ ⊆ a i ^ n • (Y i)ᶜ := (smul_set_mono (hXYdisj i i).subset_compl_right)
              _ ⊆ X i := hi
        _ ⊆ X' i := Set.subset_union_left _ _
    · have h1n : n ≤ -1 := by
        apply Int.le_of_lt_add_one
        simpa using hgt
      calc
        a i ^ n • X' j ⊆ a i ^ n • (X i)ᶜ :=
          smul_set_mono ((hXdisj hij.symm).union_left (hXYdisj i j).symm).subset_compl_right
        _ ⊆ Y i := by
          refine' Int.le_induction_down (P := fun n => a i ^ n • (X i)ᶜ ⊆ Y i) _ _ _ h1n
          · dsimp
            rw [zpow_neg, zpow_one]
            exact hY i
          · dsimp
            intro n _ hi
            calc
              a i ^ (n - 1) • (X i)ᶜ = (a i ^ n * (a i)⁻¹) • (X i)ᶜ := by rw [zpow_sub, zpow_one]
              _ = a i ^ n • (a i)⁻¹ • (X i)ᶜ := (MulAction.mul_smul _ _ _)
              _ ⊆ a i ^ n • Y i := (smul_set_mono <| hY i)
              _ ⊆ a i ^ n • (X i)ᶜ := (smul_set_mono (hXYdisj i i).symm.subset_compl_right)
              _ ⊆ Y i := hi
        _ ⊆ X' i := Set.subset_union_right _ _
  show _ ∨ ∃ i, 3 ≤ #(H i)
  -- ⊢ 3 ≤ #ι ∨ ∃ i, 3 ≤ #(H i)
  · inhabit ι
    -- ⊢ 3 ≤ #ι ∨ ∃ i, 3 ≤ #(H i)
    right
    -- ⊢ ∃ i, 3 ≤ #(H i)
    use Inhabited.default
    -- ⊢ 3 ≤ #(H default)
    simp only
    -- ⊢ 3 ≤ #(FreeGroup Unit)
    rw [FreeGroup.freeGroupUnitEquivInt.cardinal_eq, Cardinal.mk_denumerable]
    -- ⊢ 3 ≤ ℵ₀
    apply le_of_lt
    -- ⊢ 3 < ℵ₀
    exact nat_lt_aleph0 3
    -- 🎉 no goals
#align free_group.injective_lift_of_ping_pong FreeGroup.injective_lift_of_ping_pong

end PingPongLemma

end Monoid.CoprodI
