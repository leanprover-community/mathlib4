import Mathlib.GroupTheory.Coprod.Basic

open Function List

/-- An alternative implementation of `FreeSum` that uses fully cancelled words as the data type. -/
structure AddMonoid.Coprod.Word (M N : Type _) [AddMonoid M] [AddMonoid N] where
  toList : List (M ⊕ N)
  inl_zero_nmem : Sum.inl 0 ∉ toList
  inr_zero_nmem : Sum.inr 0 ∉ toList
  chain'_ne_on : toList.Chain' (Sum.isLeft · ≠ Sum.isLeft ·)

namespace Monoid.Coprod

/-- An alternative implementation of `FreeProd` that uses fully cancelled words as the data type. -/
@[to_additive (attr := ext)]
structure Word (M N : Type _) [Monoid M] [Monoid N] where
  toList : List (M ⊕ N)
  inl_one_nmem : Sum.inl 1 ∉ toList
  inr_one_nmem : Sum.inr 1 ∉ toList
  chain'_ne_on : toList.Chain' (Sum.isLeft · ≠ Sum.isLeft ·)

@[inherit_doc]
local infix:70 " ∗ʷ " => FreeProd.Word

namespace Word

variable {M N : Type _} [Monoid M] [Monoid N]

attribute [simp] inl_one_nmem inr_one_nmem

instance : One (M ∗ʷ N) := ⟨⟨[], not_mem_nil _, not_mem_nil _, chain'_nil⟩⟩

lemma chain'_ne_map (w : M ∗ʷ N) : (w.1.map Sum.isLeft).Chain' (· ≠ ·) :=
(List.chain'_map _).2 w.4

@[simp] lemma toList_one : (1 : M ∗ʷ N).toList = [] := rfl
@[simp] lemma mk_nil (h₁ h₂ h₃) : (mk [] h₁ h₂ h₃ : M ∗ʷ N) = 1 := rfl

@[simp] lemma mk_toList (w : M ∗ʷ N) (h₁ := w.2) (h₂ := w.3) (h₃ := w.4) :
    mk w.1 h₁ h₂ h₃ = w :=
  rfl

@[simps] def tail (w : M ∗ʷ N) : M ∗ʷ N :=
⟨w.toList.tail, mt mem_of_mem_tail w.2, mt mem_of_mem_tail w.3, w.4.tail⟩

@[simp] lemma tail_one : (1 : M ∗ʷ N).tail = 1 := rfl

variable [DecidableEq M] [DecidableEq N]

instance : DecidableEq (M ∗ʷ N) := fun _ _ => decidable_of_iff' _ (Word.ext_iff _ _)

def cons' (x : M ⊕ N) (w : M ∗ʷ N) (h : (x :: w.toList).Chain' (Sum.isLeft · ≠ Sum.isLeft ·)) :
  M ∗ʷ N :=
if hx : x ≠ .inl 1 ∧ x ≠ .inr 1
then ⟨x :: w.toList, mem_cons.not.2 <| not_or.2 ⟨hx.1.symm, w.2⟩,
  mem_cons.not.2 <| not_or.2 ⟨hx.2.symm, w.3⟩, h⟩
else w

lemma mk_cons {x : M ⊕ N} {l : List (M ⊕ N)} (h₁ h₂ h₃) :
  mk (x :: l) h₁ h₂ h₃ =
    cons' x ⟨l, mt (mem_cons_of_mem _) h₁, mt (mem_cons_of_mem _) h₂, h₃.tail⟩ h₃ :=
Eq.symm $ dif_pos ⟨Ne.symm (not_or.1 <| mem_cons.not.1 h₁).1,
  Ne.symm (not_or.1 <| mem_cons.not.1 h₂).1⟩

@[simp] lemma cons'_inl_one {w : M ∗ʷ N} (hw) : cons' (.inl 1) w hw = w := dif_neg $ by simp
@[simp] lemma cons'_inr_one {w : M ∗ʷ N} (hw) : cons' (.inr 1) w hw = w := dif_neg $ by simp

def of (x : M ⊕ N) : M ∗ʷ N := cons' x 1 (chain'_singleton _)

@[simp] lemma cons'_one (x : M ⊕ N) (h := chain'_singleton _) : cons' x 1 h = of x := rfl
@[simp] lemma of_inl_one : of (.inl 1 : M ⊕ N) = 1 := cons'_inl_one _
@[simp] lemma of_inr_one : of (.inr 1 : M ⊕ N) = 1 := cons'_inr_one _
@[simp] lemma tail_of (x : M ⊕ N) : tail (of x) = 1 := by rw [of, cons']; split_ifs <;> rfl

def cons : M ⊕ N → M ∗ʷ N → M ∗ʷ N
| x, ⟨[], _, _, _⟩ => of x
| (.inl x), w@⟨.inl y :: l, hl, hr, h⟩ => cons' (.inl (x * y)) w.tail $ h.imp_head $ fun _ => id
| (.inl x), w@⟨.inr y :: l, hl, hr, h⟩ => cons' (.inl x) w (h.cons $ by simp)
| (.inr x), w@⟨.inl y :: l, hl, hr, h⟩ => cons' (.inr x) w (h.cons $ by simp)
| (.inr x), w@⟨.inr y :: l, hl, hr, h⟩ => cons' (.inr (x * y)) w.tail $ h.imp_head $ fun _ => id

@[simp] lemma cons_one (x : M ⊕ N) : cons x 1 = of x := by cases x; refl

@[simp] lemma cons_inl_one (w : M ∗ʷ N) : cons (.inl 1) w = w :=
begin
  rcases w with ⟨(_|⟨(x|x), l⟩), hl, hr, hc⟩,
  { simp },
  { simp_rw [cons, one_mul, tail, mk_cons], refl },
  { simp_rw [cons, cons'_inl_one, eq_self_iff_true, true_and] }
end

@[simp] lemma cons_inr_one (w : M ∗ʷ N) : cons (.inr 1) w = w :=
begin
  rcases w with ⟨(_|⟨(x|x), l⟩), hl, hr, hc⟩,
  { simp },
  { simp_rw [cons, cons'_inr_one, eq_self_iff_true, true_and] },
  { simp_rw [cons, one_mul, tail, mk_cons], refl }
end

lemma cons'_eq_cons {x : M ⊕ N} {w : M ∗ʷ N} (h : (x :: w.toList).chain' ((≠) on .is_left)) :
  cons' x w h = cons x w :=
by cases x; rcases w with ⟨(_|⟨(_|_), _⟩), _, _, _⟩; try { refl }; apply absurd h.rel_head; simp

instance : mul_action (FreeMonoid (M ⊕ N)) (M ∗ʷ N) := FreeMonoid.mk_mul_action cons

instance : has_mul (M ∗ʷ N) := ⟨λ w₁ w₂, FreeMonoid.of_list w₁.toList • w₂⟩

lemma toList_smul (w₁ w₂ : M ∗ʷ N) : FreeMonoid.of_list w₁.toList • w₂ = w₁ * w₂ := rfl

lemma mk_mul (l : list (M ⊕ N)) (h₁ h₂ h₃ w)  : mk l h₁ h₂ h₃ * w = l.foldr cons w := rfl

instance : mul_one_class (M ∗ʷ N) :=
{ one_mul := λ w, rfl,
  mul_one := λ ⟨w, hl, hr, hc⟩,
    begin
      induction w with x w ihw, { refl },
      simp only [mk_mul, foldr_cons, mem_cons_iff, not_or_distrib] at hl hr ⊢ ihw,
      specialize ihw hl.2 hr.2 hc.tail,
      rw [ihw, ← cons'_eq_cons, cons', dif_pos (and.intro (ne.symm hl.1) (ne.symm hr.1))], refl
    end,
  .. word.has_one, .. word.has_mul }

lemma cons'_inl_mul {x y : M} {w : M ∗ʷ N} (h) :
  cons' (.inl (x * y)) w h = cons (.inl x) (cons' (.inl y) w (h.imp_head $ λ _, id)) :=
begin
  rcases eq_or_ne x 1 with rfl|hx, { simp only [one_mul, cons_inl_one] },
  rcases eq_or_ne y 1 with rfl|hy, { simp only [cons'_eq_cons, cons_inl_one, mul_one] },
  simp only [cons', dif_neg, dif_pos, hy, ne.def, not_false_iff, and_true, cons, mk_toList, tail,
    list.tail],
end

lemma cons'_inr_mul {x y : N} {w : M ∗ʷ N} (h) :
  cons' (.inr (x * y)) w h = cons (.inr x) (cons' (.inr y) w (h.imp_head $ λ _, id)) :=
begin
  rcases eq_or_ne x 1 with rfl|hx, { simp only [one_mul, cons_inr_one] },
  rcases eq_or_ne y 1 with rfl|hy, { simp only [cons'_eq_cons, cons_inr_one, mul_one] },
  simp only [cons', dif_neg, dif_pos, hy, ne.def, not_false_iff, true_and, cons, mk_toList, tail,
    list.tail]
end

lemma of_mul (x : M ⊕ N) (w : M ∗ʷ N) : of x * w = cons x w :=
begin
  rcases eq_or_ne x (.inl 1) with rfl|hxl, { simp },
  rcases eq_or_ne x (.inr 1) with rfl|hxr, { simp },
  simp only [of, cons', dif_pos (and.intro hxl hxr), mk_mul, toList_one, foldr]
end

@[simp] lemma of_smul (x : M ⊕ N) (w : M ∗ʷ N) : FreeMonoid.of x • w = of x * w :=
(of_mul _ _).symm

def inl : M →* M ∗ʷ N :=
⟨λ x, of (.inl x), of_inl_one, λ x y, by rw [of, cons'_inl_mul, ← of_mul, cons'_one]⟩

def inr : N →* M ∗ʷ N :=
⟨λ x, of (.inr x), of_inr_one, λ x y, by rw [of, cons'_inr_mul, ← of_mul, cons'_one]⟩

@[simp] lemma of_inl (x : M) : of (.inl x) = (inl x : M ∗ʷ N) := rfl
@[simp] lemma of_inr (x : N) : of (.inr x) = (inr x : M ∗ʷ N) := rfl

lemma toList_inl {x : M} (hx : x ≠ 1) : (inl x : M ∗ʷ N).toList = [.inl x] :=
by rw [← of_inl, of, cons', dif_pos]; [refl, exact ⟨mt .inl.inj hx, .inl_ne_inr⟩]

@[simp] lemma mk_inl (x : M) (h₁ h₂ h₃) : (mk [.inl x] h₁ h₂ h₃ : M ∗ʷ N) = inl x :=
ext _ _ $ eq.symm $ toList_inl $ by simpa [eq_comm] using h₁

lemma toList_inr {x : N} (hx : x ≠ 1) : (inr x : M ∗ʷ N).toList = [.inr x] :=
by rw [← of_inr, of, cons', dif_pos]; [refl, exact ⟨.inr_ne_inl, mt .inr.inj hx⟩]

@[simp] lemma mk_inr (x : N) (h₁ h₂ h₃) : (mk [.inr x] h₁ h₂ h₃ : M ∗ʷ N) = inr x :=
ext _ _ $ eq.symm $ toList_inr $ by simpa [eq_comm] using h₂

lemma cons'_mul (x : M ⊕ N) (w₁ w₂ : M ∗ʷ N) (h) : cons' x w₁ h * w₂ = cons x (w₁ * w₂) :=
begin
  rw [cons'],
  split_ifs with hx,
  { simp only [← toList_smul, of_list_smul, foldr] },
  { simp only [not_and_distrib, ne.def, not_not] at hx,
    rcases hx with (rfl|rfl); simp only [cons_inl_one, cons_inr_one] }
end

lemma cons_inl_mul (x y : M) (w : M ∗ʷ N) :
  cons (.inl (x * y)) w = cons (.inl x) (cons (.inl y) w) :=
begin
  rcases w with ⟨(_|⟨(z|z), l⟩), hl, hr, hc⟩,
  { simp only [mk_nil, mul_one, ← of_mul, of_inl, map_mul] },
  { simp only [cons, mul_assoc, cons'_inl_mul] },
  { simp only [cons, cons'_inl_mul] }
end

lemma cons_inr_mul (x y : N) (w : M ∗ʷ N) :
  cons (.inr (x * y)) w = cons (.inr x) (cons (.inr y) w) :=
begin
  rcases w with ⟨(_|⟨(z|z), l⟩), hl, hr, hc⟩,
  { simp only [mk_nil, mul_one, ← of_mul, of_inr, map_mul] },
  { simp only [cons, cons'_inr_mul] },
  { simp only [cons, mul_assoc, cons'_inr_mul] }
end

lemma cons_mul (x : M ⊕ N) (w₁ w₂ : M ∗ʷ N) : cons x (w₁ * w₂) = cons x w₁ * w₂ :=
begin
  rcases w₁ with ⟨(_|⟨y, l⟩), hl, hr, hc⟩,
  { simp only [mk_nil, cons_one, one_mul, of_mul] },
  rw [mk_mul, foldr_cons],
  cases x; cases y,
  { simp_rw [cons, cons'_mul, cons_inl_mul], refl },
  { simp_rw [cons, cons'_mul], refl },
  { simp_rw [cons, cons'_mul], refl },
  { simp_rw [cons, cons'_mul, cons_inr_mul], refl }
end

instance : is_scalar_tower (FreeMonoid (M ⊕ N)) (M ∗ʷ N) (M ∗ʷ N) :=
is_scalar_tower.of_mclosure_eq_top FreeMonoid.closure_range_of $ forall_range_iff.2 $ λ x w₁ w₂,
  by simp only [FreeMonoid.of_smul, smul_eq_mul, cons_mul]

instance : monoid (M ∗ʷ N) :=
{ mul_assoc := λ a b c, smul_assoc (of_list a.toList) b c,
  .. word.mul_one_class }

@[simp] lemma mrange_smul_one_hom : (smul_one_hom : FreeMonoid (M ⊕ N) →* M ∗ʷ N).mrange = ⊤ :=
top_unique $ λ w hw, ⟨of_list w.toList, by rw [smul_one_hom_apply, toList_smul, mul_one]⟩

@[simp] lemma mclosure_range_of : submonoid.closure (range of : set (M ∗ʷ N)) = ⊤ :=
by simp_rw [← mrange_smul_one_hom, monoid_hom.mrange_eq_map, ← FreeMonoid.closure_range_of,
  monoid_hom.map_mclosure, ← range_comp, (∘), smul_one_hom_apply, FreeMonoid.of_smul, cons_one]

@[simp] lemma mclosure_range_inl_union_inr :
  submonoid.closure (range inl ∪ range inr : set (M ∗ʷ N)) = ⊤ :=
by { rw [← mclosure_range_of, .range_eq], refl }

@[simp] lemma mclosure_image_inl_union_inr :
  submonoid.closure (inl '' {1}ᶜ ∪ inr '' {1}ᶜ : set (M ∗ʷ N)) = ⊤ :=
by simp_rw [← mclosure_range_inl_union_inr, ← image_univ, ← union_compl_self ({1} : set M),
  ← union_compl_self ({1} : set N), image_union, image_singleton, map_one, submonoid.closure_union,
  submonoid.closure_singleton_one, bot_sup_eq]

lemma mk_append {l₁ l₂ : list (M ⊕ N)} (h₁ h₂ h₃) :
  mk (l₁++ l₂) h₁ h₂ h₃ =
    mk l₁ (mt (mem_append_left _) h₁) (mt (mem_append_left _) h₂) h₃.left_of_append *
      mk l₂ (mt (mem_append_right _) h₁) (mt (mem_append_right _) h₂) h₃.right_of_append :=
begin
  induction l₁ with a l₁ ihl, { refl },
  specialize ihl (mt (mem_cons_of_mem _) h₁) (mt (mem_cons_of_mem _) h₂) h₃.tail,
  simp only [list.cons_append, mk_cons, cons'_eq_cons, ← of_mul, mul_assoc],
  congr, exact ihl
end

lemma prod_eq (l : list (M ∗ʷ N)) (hl : (l.map toList).join.chain' ((≠) on .is_left)) :
  l.prod = ⟨(l.map toList).join, by simp [mem_join], by simp [mem_join], hl⟩ :=
begin
  induction l with w l ihl, { refl },
  specialize ihl hl.right_of_append,
  simp only [list.map, join, prod_cons, mk_append, ihl, mk_toList]
end

lemma prod_eq_of_join_eq {l : list (M ∗ʷ N)} {w : M ∗ʷ N} (h : (l.map toList).join = w.1) :
  l.prod = w :=
begin
  simp only [prod_eq l (h.symm ▸ w.4), h, mk_toList],
end

instance : has_inv (word G H) :=
⟨λ w, ⟨(w.toList.map (.map has_inv.inv has_inv.inv)).reverse,
    by simpa only [mem_reverse, mem_map, .exists, .map_inl, .map_inr, inv_eq_one,
      false_and, exists_false, or_false, @and.comm _ (_ = _), exists_eq_left] using w.2,
    by simpa only [mem_reverse, mem_map, .exists, .map_inl, .map_inr, inv_eq_one,
      false_and, exists_false, false_or, @and.comm _ (_ = _), exists_eq_left] using w.3,
    by simpa only [chain'_reverse, chain'_map, flip, on_fun, .is_left_map, ne_comm] using w.4⟩⟩

lemma toList_inv (w : word G H) :
  (w⁻¹).toList = (w.toList.map (.map has_inv.inv has_inv.inv)).reverse :=
rfl

instance : group (word G H) :=
{ mul_left_inv := λ ⟨l, hl, hr, hc⟩,
    begin
      induction l with x l ihl, { refl },
      specialize ihl (mt (mem_cons_of_mem _) hl) (mt (mem_cons_of_mem _) hr) hc.tail,
      simp only [toList_inv, map_cons, ← toList_smul, reverse_cons, of_list_smul, foldr_append,
        foldr] at ihl ⊢,
      cases x;
        simpa only [.map_inl, .map_inr, cons, inv_mul_self, cons'_inl_one, cons'_inr_one]
    end,
  .. word.monoid, .. word.has_inv }

end word

section dec_eq

variable [DecidableEq M] [DecidableEq N]

lemma mk_word_cons' {x : M ⊕ N} {w : M ∗ʷ N} (hxw) :
  mk (of_list (w.cons' x hxw).toList) = mk (of x) * mk (of_list w.toList) :=
begin
  rw [word.cons'],
  split_ifs with hx,
  { refl },
  { rw [not_and_distrib, ne.def, ne.def, not_not, not_not] at hx,
    rcases hx with (rfl|rfl); simp only [mk_of_inl, mk_of_inr, map_one, one_mul] }
end

lemma mk_word_of (x : M ⊕ N) : mk (of_list (word.of x).toList) = mk (of x) :=
mk_word_cons' _

lemma mk_word_inl (x : M) : mk (of_list (word.inl x : M ∗ʷ N).toList) = inl x :=
mk_word_of _

lemma mk_word_inr (x : N) : mk (of_list (word.inr x : M ∗ʷ N).toList) = inr x :=
mk_word_of _

lemma mk_word_cons (x : M ⊕ N) (w : M ∗ʷ N) :
  mk (of_list (w.cons x).toList) = mk (of x) * mk (of_list w.toList) :=
by cases x; rcases w with ⟨(_|⟨(y|y), w⟩), hl, hr, hc⟩; simp only [word.cons, mk_word_of,
  of_list_nil, map_one, mul_one, mk_word_cons', of_list_cons, map_mul, mk_of_inl, mk_of_inr,
  mul_assoc, word.tail, list.tail]

lemma mk_smul_word (w₁ : FreeMonoid (M ⊕ N)) (w₂ : M ∗ʷ N) :
  mk (of_list (w₁ • w₂).toList) = mk w₁ * mk (of_list w₂.toList) :=
begin
  induction w₁ using FreeMonoid.rec_on with x w₁ ihw,
  { rw [one_smul, map_one, one_mul] },
  { rw [mul_smul, of_smul, mk_word_cons, ihw, map_mul, mul_assoc] }
end

lemma mk_word_mul (w₁ w₂ : M ∗ʷ N) :
  mk (of_list (w₁ * w₂).toList) = mk (of_list w₁.toList) * mk (of_list w₂.toList) :=
mk_smul_word _ _

@[simps symm_apply] def toWord : M ∗ N ≃* M ∗ʷ N :=
{ to_fun := clift
    (@smul_one_hom (FreeMonoid (M ⊕ N)) (M ∗ʷ N) _ _ _ _)
    (by rw [smul_one_hom_apply, of_smul, word.cons_inl_one])
    (by rw [smul_one_hom_apply, of_smul, word.cons_inr_one])
    (λ x y, by simp only [smul_one_hom_apply, word.of_smul, word.of_inl, map_mul, mul_one])
    (λ x y, by simp only [smul_one_hom_apply, word.of_smul, word.of_inr, map_mul, mul_one]),
  inv_fun := λ w, mk (of_list w.toList),
  left_inv := mk_surjective.forall.2 $ λ w, by rw [clift_apply_mk, smul_one_hom_apply, mk_smul_word,
    word.toList_one, of_list_nil, map_one, mul_one],
  right_inv := mul_one,
  map_mul' := map_mul _ }

@[simp] lemma toWord_mk (w : FreeMonoid (M ⊕ N)) : toWord (mk w) = w • 1 := rfl
@[simp] lemma toWord_inl (x : M) : toWord (inl x : M ∗ N) = word.inl x := rfl
@[simp] lemma toWord_inr (x : N) : toWord (inr x : M ∗ N) = word.inr x := rfl

@[simp] lemma of_word_smul (w₁ : FreeMonoid (M ⊕ N)) (w₂ : M ∗ʷ N) :
  toWord.symm (w₁ • w₂) = mk w₁ * toWord.symm w₂ :=
mk_smul_word _ _

@[simp] lemma of_word_cons (x : M ⊕ N) (w : M ∗ʷ N) :
  toWord.symm (w.cons x) = mk (of x) * toWord.symm w :=
mk_word_cons _ _

@[simp] lemma of_word_cons' {x : M ⊕ N} {w : M ∗ʷ N} (h) :
  toWord.symm (w.cons' x h) = mk (of x) * toWord.symm w :=
mk_word_cons' _

@[simp] lemma of_word_of (x : M ⊕ N) : toWord.symm (word.of x) = mk (of x) := mk_word_of _
@[simp] lemma of_word_inl (x : M) : toWord.symm (word.inl x : M ∗ʷ N) = inl x := of_word_of _
@[simp] lemma of_word_inr (x : N) : toWord.symm (word.inr x : M ∗ʷ N) = inr x := of_word_of _

namespace word

def lift (f : M →* P) (g : N →* P) : M ∗ʷ N →* P :=
(lift f g).comp (toWord : M ∗ N ≃* M ∗ʷ N).symm.to_monoid_hom

def fst : M ∗ʷ N →* M := lift (monoid_hom.id _) 1
def snd : M ∗ʷ N →* N := lift 1 (monoid_hom.id _)
def toProd : M ∗ʷ N →* M × N := lift (monoid_hom.inl _ _) (monoid_hom.inr _ _)

@[simp] lemma lift_apply_mk (f : M →* P) (g : N →* P) (l : list (M ⊕ N)) (hl hr hc) :
  lift f g (mk l hl hr hc) = (l.map (.elim f g)).prod :=
rfl

@[simp] lemma lift_apply_inl (f : M →* P) (g : N →* P) (x : M) :
  lift f g (inl x) = f x :=
by rw [lift, monoid_hom.comp_apply, mul_equiv.coe_to_monoid_hom, of_word_inl, lift_apply_inl]

@[simp] lemma lift_comp_inl (f : M →* P) (g : N →* P) : (lift f g).comp inl = f :=
FunLike.ext _ _ $ lift_apply_inl f g

@[simp] lemma lift_apply_inr (f : M →* P) (g : N →* P) (x : N) :
  lift f g (inr x) = g x :=
by rw [lift, monoid_hom.comp_apply, mul_equiv.coe_to_monoid_hom, of_word_inr, lift_apply_inr]

@[simp] lemma lift_comp_inr (f : M →* P) (g : N →* P) : (lift f g).comp inr = g :=
FunLike.ext _ _ $ lift_apply_inr f g

@[ext]
lemma hom_ext {f g : M ∗ʷ N →* P} (h₁ : f.comp inl = g.comp inl) (h₂ : f.comp inr = g.comp inr) :
  f = g :=
begin
  refine FunLike.ext _ _ (toWord.surjective.forall.2 $ λ x, _),
  simp only [← mul_equiv.coe_to_monoid_hom, ← monoid_hom.comp_apply],
  exact FunLike.ext_iff.1 (hom_ext h₁ h₂) x
end

@[simp] lemma fst_comp_inl : (fst : M ∗ʷ N →* M).comp inl = monoid_hom.id _ := lift_comp_inl _ _
@[simp] lemma fst_apply_inl (x : M) : fst (inl x : M ∗ʷ N) = x := lift_apply_inl _ _ _
@[simp] lemma fst_comp_inr : (fst : M ∗ʷ N →* M).comp inr = 1 := lift_comp_inr _ _
@[simp] lemma fst_apply_inr (x : N) : fst (inr x : M ∗ʷ N) = 1 := lift_apply_inr _ _ _
@[simp] lemma snd_comp_inl : (snd : M ∗ʷ N →* N).comp inl = 1 := lift_comp_inl _ _
@[simp] lemma snd_apply_inl (x : M) : snd (inl x : M ∗ʷ N) = 1 := lift_apply_inl _ _ _
@[simp] lemma snd_comp_inr : (snd : M ∗ʷ N →* N).comp inr = monoid_hom.id _ := lift_comp_inr _ _
@[simp] lemma snd_apply_inr (x : N) : snd (inr x : M ∗ʷ N) = x := lift_apply_inr _ _ _

lemma fst_surjective : surjective (fst : M ∗ʷ N → M) := left_inverse.surjective fst_apply_inl
lemma snd_surjective : surjective (snd : M ∗ʷ N → N) := left_inverse.surjective snd_apply_inr

@[simp] lemma range_fst : set.range (fst : M ∗ʷ N → M) = univ := fst_surjective.range_eq
@[simp] lemma range_snd : set.range (snd : M ∗ʷ N → N) = univ := snd_surjective.range_eq

@[simp] lemma toProd_comp_inl : (toProd : M ∗ʷ N →* M × N).comp inl = monoid_hom.inl _ _ :=
lift_comp_inl _ _

@[simp] lemma toProd_comp_inr : (toProd : M ∗ʷ N →* M × N).comp inr = monoid_hom.inr _ _ :=
lift_comp_inr _ _

@[simp] lemma toProd_apply_inl (x : M) : toProd (inl x : M ∗ʷ N) = (x, 1) :=
lift_apply_inl _ _ _

@[simp] lemma toProd_apply_inr (x : N) : toProd (inr x : M ∗ʷ N) = (1, x) :=
lift_apply_inr _ _ _

@[simp] lemma fst_prod_snd : (fst : M ∗ʷ N →* M).prod snd = toProd :=
by ext1; ext1; simp only [monoid_hom.comp_apply, monoid_hom.prod_apply, fst_apply_inl,
  fst_apply_inr, snd_apply_inl, snd_apply_inr, toProd_apply_inl, toProd_apply_inr]

@[simp] lemma prod_mk_fst_snd (x : M ∗ʷ N) : (fst x, snd x) = toProd x :=
by rw [← fst_prod_snd, monoid_hom.prod_apply]

@[simp] lemma fst_comp_toProd : (monoid_hom.fst M N).comp toProd = fst :=
by rw [← fst_prod_snd, monoid_hom.fst_comp_prod]

@[simp] lemma fst_toProd (x : M ∗ʷ N) : (toProd x).1 = fst x :=
by { rw [← fst_comp_toProd], refl }

@[simp] lemma snd_comp_toProd : (monoid_hom.snd M N).comp toProd = snd :=
by rw [← fst_prod_snd, monoid_hom.snd_comp_prod]

@[simp] lemma snd_toProd (x : M ∗ʷ N) : (toProd x).2 = snd x :=
by { rw [← snd_comp_toProd], refl }

@[simps apply_toList] def swap_hom : M ∗ʷ N →* word N M :=
monoid_hom.copy (lift inr inl)
  (λ w, ⟨w.1.map .swap, by simp [w.3], by simp [w.2], by
  { refine chain'_map_of_chain' .swap (λ a b, _) w.4,
    simp [on_fun, ← .bnot_is_right, bool.eq_bnot_iff] }⟩) $ funext $ λ w,
  begin
    rcases w with ⟨l, hl, hr, hc⟩,
    simp only [lift_apply_mk],
    refine (prod_eq_of_join_eq _).symm, simp only,
    clear hc, induction l with a l ihl, { refl },
    specialize ihl (mt (mem_cons_of_mem _) hl) (mt (mem_cons_of_mem _) hr),
    cases a,
    { have ha : a ≠ 1, by { rintro rfl, simp * at * },
      simpa only [map_cons, .elim_inl, ha, toList_inr, join, ne.def, not_false_iff,
        singleton_append, .swap_inl, eq_self_iff_true, true_and] },
    { have ha : a ≠ 1, by { rintro rfl, simp * at * },
      simpa only [map_cons, .elim_inr, ha, toList_inl, join, ne.def, not_false_iff,
        singleton_append, .swap_inr, eq_self_iff_true, true_and] },
  end

@[simps apply_toList] def swap : M ∗ʷ N ≃* word N M :=
{ to_fun := swap_hom,
  inv_fun := swap_hom,
  left_inv := λ w, ext _ _ $
    by simp only [swap_hom_apply_toList, map_map, .swap_swap_eq, list.map_id],
  right_inv := λ w, ext _ _ $
    by simp only [swap_hom_apply_toList, map_map, .swap_swap_eq, list.map_id],
  map_mul' := map_mul swap_hom }

@[simp] lemma swap_apply_inl (x : M) : swap (inl x : M ∗ʷ N) = inr x :=
by simp only [swap, mul_equiv.coe_mk, swap_hom, monoid_hom.copy_eq_self, lift_apply_inl]

@[simp] lemma swap_apply_inr (x : N) : swap (inr x : M ∗ʷ N) = inl x :=
by simp only [swap, mul_equiv.coe_mk, swap_hom, monoid_hom.copy_eq_self, lift_apply_inr]

@[simp] lemma swap_symm : (swap : M ∗ʷ N ≃* word N M).symm = swap := rfl

end word

end dec_eq


end free_prod
