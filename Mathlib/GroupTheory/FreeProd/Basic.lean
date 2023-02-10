/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Congruence
import Mathlib.GroupTheory.Submonoid.Membership

/-!
-/

open FreeMonoid Function List Set

def freeProdCon (M N : Type _) [MulOneClass M] [MulOneClass N] : Con (FreeMonoid (M ⊕ N)) :=
infₛ {c |
  (∀ x y : M, c (of (Sum.inl (x * y))) (of (Sum.inl x) * of (Sum.inl y)))
  ∧ (∀ x y : N, c (of (Sum.inr (x * y))) (of (Sum.inr x) * of (Sum.inr y)))
  ∧ c (of $ Sum.inl 1) 1 ∧ c (of $ Sum.inr 1) 1}

def FreeProd (M N : Type _) [MulOneClass M] [MulOneClass N] := (freeProdCon M N).Quotient

local infix:70 " ⋆ " => FreeProd

namespace free_prod

section MulOneClass

variable {M N P : Type _} [MulOneClass M] [MulOneClass N] [MulOneClass P]

instance : MulOneClass (M ⋆ N) := Con.mulOneClass _

def mk : FreeMonoid (M ⊕ N) →* M ⋆ N := Con.mk' _

@[simp] lemma con_ker_mk : Con.ker mk = freeProdCon M N := Con.mk'_ker _

lemma mk_surjective : Surjective (@mk M N _ _) := surjective_quot_mk _

@[simp] lemma mrange_mk : MonoidHom.mrange (@mk M N _ _) = ⊤ := Con.mrange_mk'

lemma mk_eq_mk {w₁ w₂ : FreeMonoid (M ⊕ N)} :
  mk w₁ = mk w₂ ↔ freeProdCon M N w₁ w₂ :=
Con.eq _

def inl : M →* M ⋆ N where
  toFun := fun x => mk (of (.inl x))
  map_one' := mk_eq_mk.2 $ fun _c hc => hc.2.2.1
  map_mul' := fun x y => mk_eq_mk.2 $ fun _c hc => hc.1 x y


def inr : N →* M ⋆ N where
  toFun := fun x => mk (of (.inr x))
  map_one' := mk_eq_mk.2 $ fun _c hc => hc.2.2.2
  map_mul' := fun x y => mk_eq_mk.2 $ fun _c hc => hc.2.1 x y

@[simp] lemma mk_of_inl (x : M) : (mk (of (.inl x)) : M ⋆ N) = inl x := rfl
@[simp] lemma mk_of_inr (x : N) : (mk (of (.inr x)) : M ⋆ N) = inr x := rfl

def clift (f : FreeMonoid (M ⊕ N) →* P)
    (hM₁ : f (of (.inl 1)) = 1) (hN₁ : f (of (.inr 1)) = 1)
    (hM : ∀ x y, f (of (.inl (x * y))) = f (of (.inl x) * of (.inl y)))
    (hN : ∀ x y, f (of (.inr (x * y))) = f (of (.inr x) * of (.inr y))) :
    M ⋆ N →* P :=
  Con.lift _ f $ infₛ_le ⟨hM, hN, hM₁.trans (map_one f).symm, hN₁.trans (map_one f).symm⟩

@[simp] lemma clift_apply_inl (f : FreeMonoid (M ⊕ N) →* P) (hM₁ hN₁ hM hN) (x : M) :
    clift f hM₁ hN₁ hM hN (inl x) = f (of (.inl x)) :=
  rfl

@[simp] lemma clift_apply_inr (f : FreeMonoid (M ⊕ N) →* P) (hM₁ hN₁ hM hN) (x : N) :
    clift f hM₁ hN₁ hM hN (inr x) = f (of (.inr x)) :=
rfl

@[simp] lemma clift_apply_mk (f : FreeMonoid (M ⊕ N) →* P) (hM₁ hN₁ hM hN w) :
    clift f hM₁ hN₁ hM hN (mk w) = f w :=
rfl

@[simp] lemma clift_comp_mk (f : FreeMonoid (M ⊕ N) →* P) (hM₁ hN₁ hM hN) :
    (clift f hM₁ hN₁ hM hN).comp mk = f :=
FunLike.ext' rfl

end MulOneClass

variable {α β M N G H P P' : Type _} [Monoid M] [Monoid N] [Monoid P] [Monoid P']
  [Group G] [Group H]

instance : Monoid (M ⋆ N) := Con.monoid _

def lift (f : M →* P) (g : N →* P) : (M ⋆ N) →* P :=
clift (FreeMonoid.lift $ Sum.elim f g) (map_one f) (map_one g) (map_mul f) (map_mul g)

@[simp] lemma lift_apply_mk (f : M →* P) (g : N →* P) (x : FreeMonoid (M ⊕ N)) :
  lift f g (mk x) = FreeMonoid.lift (Sum.elim f g) x :=
rfl

@[simp] lemma lift_apply_inl (f : M →* P) (g : N →* P) (x : M) :
  lift f g (inl x) = f x :=
rfl

@[simp] lemma lift_comp_inl (f : M →* P) (g : N →* P) : (lift f g).comp inl = f := rfl

@[simp] lemma lift_apply_inr (f : M →* P) (g : N →* P) (x : N) :
  lift f g (inr x) = g x :=
rfl

@[simp] lemma lift_comp_inr (f : M →* P) (g : N →* P) : (lift f g).comp inr = g := rfl

@[simp] lemma mclosure_range_inl_union_inr :
    Submonoid.closure (range (inl : M →* M ⋆ N) ∪ range (inr : N →* M ⋆ N)) = ⊤ := by
  rw [← mrange_mk, MonoidHom.mrange_eq_map, ← closure_range_of, MonoidHom.map_mclosure,
    ← range_comp, Sum.range_eq]; rfl

@[simp] lemma mrange_inl_sup_mrange_inr :
    MonoidHom.mrange (inl : M →* M ⋆ N) ⊔ MonoidHom.mrange (inr : N →* M ⋆ N) = ⊤ := by
  rw [← mclosure_range_inl_union_inr, Submonoid.closure_union, ← MonoidHom.coe_mrange,
    ← MonoidHom.coe_mrange, Submonoid.closure_eq, Submonoid.closure_eq]

@[ext 1100]
lemma hom_ext {f g : M ⋆ N →* P} (h₁ : f.comp inl = g.comp inl) (h₂ : f.comp inr = g.comp inr) :
    f = g :=
  MonoidHom.eq_of_eqOn_denseM mclosure_range_inl_union_inr $ eqOn_union.2
    ⟨eqOn_range.2 $ FunLike.ext'_iff.1 h₁, eqOn_range.2 $ FunLike.ext'_iff.1 h₂⟩

def lift_equiv : (M →* P) × (N →* P) ≃ (M ⋆ N →* P) where
  toFun fg := lift fg.1 fg.2
  invFun f := (f.comp inl, f.comp inr)
  left_inv _ := rfl
  right_inv _ := hom_ext (lift_comp_inl _ _) (lift_comp_inr _ _)

def fst : M ⋆ N →* M := lift (.id M) 1

def snd : M ⋆ N →* N := lift 1 (.id N)

def toProd : M ⋆ N →* M × N := lift (.inl _ _) (.inr _ _)

lemma comp_lift (f : P →* P') (g₁ : M →* P) (g₂ : N →* P) :
  f.comp (lift g₁ g₂) = lift (f.comp g₁) (f.comp g₂) :=
hom_ext (by rw [MonoidHom.comp_assoc, lift_comp_inl, lift_comp_inl])
  (by rw [MonoidHom.comp_assoc, lift_comp_inr, lift_comp_inr])

@[simp] lemma fst_comp_inl : (fst : M ⋆ N →* M).comp inl = .id _ := rfl
@[simp] lemma fst_apply_inl (x : M) : fst (inl x : M ⋆ N) = x := rfl
@[simp] lemma fst_comp_inr : (fst : M ⋆ N →* M).comp inr = 1 := rfl
@[simp] lemma fst_apply_inr (x : N) : fst (inr x : M ⋆ N) = 1 := rfl
@[simp] lemma snd_comp_inl : (snd : M ⋆ N →* N).comp inl = 1 := rfl
@[simp] lemma snd_apply_inl (x : M) : snd (inl x : M ⋆ N) = 1 := rfl
@[simp] lemma snd_comp_inr : (snd : M ⋆ N →* N).comp inr = .id _ := rfl
@[simp] lemma snd_apply_inr (x : N) : snd (inr x : M ⋆ N) = x := rfl

@[simp] lemma toProd_comp_inl : (toProd : M ⋆ N →* M × N).comp inl = .inl _ _ := rfl

@[simp] lemma toProd_comp_inr : (toProd : M ⋆ N →* M × N).comp inr = .inr _ _ :=
lift_comp_inr _ _

@[simp] lemma toProd_apply_inl (x : M) : toProd (inl x : M ⋆ N) = (x, 1) := lift_apply_inl _ _ _
@[simp] lemma toProd_apply_inr (x : N) : toProd (inr x : M ⋆ N) = (1, x) := lift_apply_inr _ _ _

@[simp] lemma fst_prod_snd : (fst : M ⋆ N →* M).prod snd = toProd :=
by ext1 <;> rfl

@[simp] lemma prod_mk_fst_snd (x : M ⋆ N) : (fst x, snd x) = toProd x :=
by rw [← fst_prod_snd, MonoidHom.prod_apply]

@[simp] lemma fst_comp_toProd : (MonoidHom.fst M N).comp toProd = fst :=
by rw [← fst_prod_snd, MonoidHom.fst_comp_prod]

@[simp] lemma fst_toProd (x : M ⋆ N) : (toProd x).1 = fst x := by
  rw [← fst_comp_toProd]; rfl

@[simp] lemma snd_comp_toProd : (MonoidHom.snd M N).comp toProd = snd :=
by rw [← fst_prod_snd, MonoidHom.snd_comp_prod]

@[simp] lemma snd_toProd (x : M ⋆ N) : (toProd x).2 = snd x := by
  rw [← snd_comp_toProd]; rfl

instance : Inv (G ⋆ H) where
  inv := fun x => Con.liftOn x
    (fun w => mk $ ofList (w.toList.map (Sum.map Inv.inv Inv.inv)).reverse) $ by
      change freeProdCon G H ≤ ⟨Setoid.ker _, fun hab hcd => ?_⟩
      · refine infₛ_le ⟨fun x y => ?_, fun x y => ?_, ?_, ?_⟩ <;> refine Setoid.ker_def.2 ?_ <;> dsimp only
        · simp only [List.map, toList_of, toList_of_mul, Sum.map_inl, mul_inv_rev, ofList_append,
            ofList_singleton, mul_one, mk_of_inl, map_mul, reverse_cons, reverse_singleton]
        · simp only [List.map, toList_of, toList_of_mul, Sum.map_inr, mul_inv_rev, ofList_append,
            ofList_singleton, mul_one, mk_of_inr, map_mul, reverse_cons, reverse_singleton]
        · simp only [List.map, toList_of, Sum.map_inl, inv_one, reverse_singleton, ofList_cons,
            ofList_nil, mul_one, mk_of_inl, map_one, toList_one, reverse_nil]
        · simp only [List.map, toList_of, Sum.map_inr, inv_one, reverse_singleton, ofList_cons,
            ofList_nil, mul_one, mk_of_inr, map_one, to_list_one, reverse_nil]
      · rw [← Setoid.rel, Setoid.ker_def] at hab hcd ⊢
        simp only [toList_mul, map_append, ofList_append, reverse_append, map_mul]
        exact congr_arg₂ (· * ·) hcd hab

lemma inv_def (w : FreeMonoid (G ⊕ H)) :
  (mk w)⁻¹ = mk (of_list (w.to_list.map (.map has_inv.inv has_inv.inv)).reverse) :=
rfl

instance : group (G ⋆ H) :=
{ mul_left_inv := λ x,
    begin
      refine submonoid.induction_of_closure_eq_top_left mclosure_range_inl_union_inr x rfl _,
      clear x, rintro _ (⟨x, rfl⟩|⟨x, rfl⟩); refine mk_surjective.forall.2 (λ y hy, _),
      { simp_rw [← mk_of_inl, ← map_mul, inv_def, ← map_reverse, to_list_of_mul, reverse_cons,
          map_append, map_singleton, .map_inl, of_list_append, map_mul, of_list_singleton,
          mk_of_inl, map_reverse],
        rwa [mul_assoc, ← mul_assoc (inl _) (inl _), ← map_mul, mul_left_inv, map_one, one_mul] },
      { simp_rw [← mk_of_inr, ← map_mul, inv_def, ← map_reverse, to_list_of_mul, reverse_cons,
          map_append, map_singleton, .map_inr, of_list_append, map_mul, of_list_singleton,
          mk_of_inr, map_reverse],
        rwa [mul_assoc, ← mul_assoc (inr _) (inr _), ← map_mul, mul_left_inv, map_one, one_mul] }
    end,
  .. free_prod.monoid G H, .. free_prod.has_inv }

@[ext] structure word (M N : Type*) [monoid M] [monoid N] :=
(to_list : list (M ⊕ N))
(inl_one_nmem : .inl 1 ∉ to_list)
(inr_one_nmem : .inr (1 : N) ∉ to_list)
(chain'_ne_on : to_list.chain' ((≠) on .is_left))

attribute [simp] word.inl_one_nmem word.inr_one_nmem

namespace word

instance : has_one (word M N) := ⟨⟨[], not_mem_nil _, not_mem_nil _, chain'_nil⟩⟩

lemma chain'_ne_map (w : word M N) : (w.1.map .is_left).chain' (≠) :=
(list.chain'_map _).2 w.4

@[simp] lemma to_list_one : (1 : word M N).to_list = [] := rfl
@[simp] lemma mk_nil (h₁ h₂ h₃) : (mk [] h₁ h₂ h₃ : word M N) = 1 := rfl

@[simp] lemma mk_to_list (w : word M N) (h₁ := w.2) (h₂ := w.3) (h₃ := w.4) :
  mk w.1 h₁ h₂ h₃ = w :=
ext _ _ rfl

@[simps] def tail (w : word M N) : word M N :=
⟨w.to_list.tail, mt mem_of_mem_tail w.2, mt mem_of_mem_tail w.3, w.4.tail⟩

@[simp] lemma tail_one : (1 : word M N).tail = 1 := rfl

variables [decidable_eq M] [decidable_eq N] [decidable_eq G] [decidable_eq H]

instance : decidable_eq (word M N) := λ x y, decidable_of_iff' _ (ext_iff _ _)

def cons' (x : M ⊕ N) (w : word M N) (h : (x :: w.to_list).chain' ((≠) on .is_left)) :
  word M N :=
if hx : x ≠ .inl 1 ∧ x ≠ .inr 1
then ⟨x :: w.to_list, not_or_distrib.2 ⟨hx.1.symm, w.2⟩, not_or_distrib.2 ⟨hx.2.symm, w.3⟩, h⟩
else w

lemma mk_cons {x : M ⊕ N} {l : list (M ⊕ N)} (h₁ h₂ h₃) :
  mk (x :: l) h₁ h₂ h₃ =
    cons' x ⟨l, (not_or_distrib.1 h₁).2, (not_or_distrib.1 h₂).2, h₃.tail⟩ h₃ :=
eq.symm $ dif_pos ⟨ne.symm (not_or_distrib.1 h₁).1, ne.symm (not_or_distrib.1 h₂).1⟩

@[simp] lemma cons'_inl_one {w : word M N} (hw) : cons' (.inl 1) w hw = w := dif_neg $ by simp
@[simp] lemma cons'_inr_one {w : word M N} (hw) : cons' (.inr 1) w hw = w := dif_neg $ by simp

def of (x : M ⊕ N) : word M N := cons' x 1 (chain'_singleton _)

@[simp] lemma cons'_one (x : M ⊕ N) (h := chain'_singleton _) : cons' x 1 h = of x := rfl
@[simp] lemma of_inl_one : of (.inl 1 : M ⊕ N) = 1 := cons'_inl_one _
@[simp] lemma of_inr_one : of (.inr 1 : M ⊕ N) = 1 := cons'_inr_one _
@[simp] lemma tail_of (x : M ⊕ N) : tail (of x) = 1 := by { rw [of, cons'], split_ifs; refl }

def cons : M ⊕ N → word M N → word M N
| x ⟨[], _, _, _⟩ := of x
| (.inl x) w@⟨.inl y :: l, hl, hr, h⟩ := cons' (.inl (x * y)) w.tail $ h.imp_head $ λ z, id
| (.inl x) w@⟨.inr y :: l, hl, hr, h⟩ := cons' (.inl x) w (h.cons $ by simp [on_fun])
| (.inr x) w@⟨.inl y :: l, hl, hr, h⟩ := cons' (.inr x) w (h.cons $ by simp [on_fun])
| (.inr x) w@⟨.inr y :: l, hl, hr, h⟩ := cons' (.inr (x * y)) w.tail $ h.imp_head $ λ z, id

@[simp] lemma cons_one (x : M ⊕ N) : cons x 1 = of x := by cases x; refl

@[simp] lemma cons_inl_one (w : word M N) : cons (.inl 1) w = w :=
begin
  rcases w with ⟨(_|⟨(x|x), l⟩), hl, hr, hc⟩,
  { simp },
  { simp_rw [cons, one_mul, tail, mk_cons], refl },
  { simp_rw [cons, cons'_inl_one, eq_self_iff_true, true_and] }
end

@[simp] lemma cons_inr_one (w : word M N) : cons (.inr 1) w = w :=
begin
  rcases w with ⟨(_|⟨(x|x), l⟩), hl, hr, hc⟩,
  { simp },
  { simp_rw [cons, cons'_inr_one, eq_self_iff_true, true_and] },
  { simp_rw [cons, one_mul, tail, mk_cons], refl }
end

lemma cons'_eq_cons {x : M ⊕ N} {w : word M N} (h : (x :: w.to_list).chain' ((≠) on .is_left)) :
  cons' x w h = cons x w :=
by cases x; rcases w with ⟨(_|⟨(_|_), _⟩), _, _, _⟩; try { refl }; apply absurd h.rel_head; simp

instance : mul_action (FreeMonoid (M ⊕ N)) (word M N) := FreeMonoid.mk_mul_action cons

instance : has_mul (word M N) := ⟨λ w₁ w₂, FreeMonoid.of_list w₁.to_list • w₂⟩

lemma to_list_smul (w₁ w₂ : word M N) : FreeMonoid.of_list w₁.to_list • w₂ = w₁ * w₂ := rfl

lemma mk_mul (l : list (M ⊕ N)) (h₁ h₂ h₃ w)  : mk l h₁ h₂ h₃ * w = l.foldr cons w := rfl

instance : mul_one_class (word M N) :=
{ one_mul := λ w, rfl,
  mul_one := λ ⟨w, hl, hr, hc⟩,
    begin
      induction w with x w ihw, { refl },
      simp only [mk_mul, foldr_cons, mem_cons_iff, not_or_distrib] at hl hr ⊢ ihw,
      specialize ihw hl.2 hr.2 hc.tail,
      rw [ihw, ← cons'_eq_cons, cons', dif_pos (and.intro (ne.symm hl.1) (ne.symm hr.1))], refl
    end,
  .. word.has_one, .. word.has_mul }

lemma cons'_inl_mul {x y : M} {w : word M N} (h) :
  cons' (.inl (x * y)) w h = cons (.inl x) (cons' (.inl y) w (h.imp_head $ λ _, id)) :=
begin
  rcases eq_or_ne x 1 with rfl|hx, { simp only [one_mul, cons_inl_one] },
  rcases eq_or_ne y 1 with rfl|hy, { simp only [cons'_eq_cons, cons_inl_one, mul_one] },
  simp only [cons', dif_neg, dif_pos, hy, ne.def, not_false_iff, and_true, cons, mk_to_list, tail,
    list.tail],
end

lemma cons'_inr_mul {x y : N} {w : word M N} (h) :
  cons' (.inr (x * y)) w h = cons (.inr x) (cons' (.inr y) w (h.imp_head $ λ _, id)) :=
begin
  rcases eq_or_ne x 1 with rfl|hx, { simp only [one_mul, cons_inr_one] },
  rcases eq_or_ne y 1 with rfl|hy, { simp only [cons'_eq_cons, cons_inr_one, mul_one] },
  simp only [cons', dif_neg, dif_pos, hy, ne.def, not_false_iff, true_and, cons, mk_to_list, tail,
    list.tail]
end

lemma of_mul (x : M ⊕ N) (w : word M N) : of x * w = cons x w :=
begin
  rcases eq_or_ne x (.inl 1) with rfl|hxl, { simp },
  rcases eq_or_ne x (.inr 1) with rfl|hxr, { simp },
  simp only [of, cons', dif_pos (and.intro hxl hxr), mk_mul, to_list_one, foldr]
end

@[simp] lemma of_smul (x : M ⊕ N) (w : word M N) : FreeMonoid.of x • w = of x * w :=
(of_mul _ _).symm

def inl : M →* word M N :=
⟨λ x, of (.inl x), of_inl_one, λ x y, by rw [of, cons'_inl_mul, ← of_mul, cons'_one]⟩

def inr : N →* word M N :=
⟨λ x, of (.inr x), of_inr_one, λ x y, by rw [of, cons'_inr_mul, ← of_mul, cons'_one]⟩

@[simp] lemma of_inl (x : M) : of (.inl x) = (inl x : word M N) := rfl
@[simp] lemma of_inr (x : N) : of (.inr x) = (inr x : word M N) := rfl

lemma to_list_inl {x : M} (hx : x ≠ 1) : (inl x : word M N).to_list = [.inl x] :=
by rw [← of_inl, of, cons', dif_pos]; [refl, exact ⟨mt .inl.inj hx, .inl_ne_inr⟩]

@[simp] lemma mk_inl (x : M) (h₁ h₂ h₃) : (mk [.inl x] h₁ h₂ h₃ : word M N) = inl x :=
ext _ _ $ eq.symm $ to_list_inl $ by simpa [eq_comm] using h₁

lemma to_list_inr {x : N} (hx : x ≠ 1) : (inr x : word M N).to_list = [.inr x] :=
by rw [← of_inr, of, cons', dif_pos]; [refl, exact ⟨.inr_ne_inl, mt .inr.inj hx⟩]

@[simp] lemma mk_inr (x : N) (h₁ h₂ h₃) : (mk [.inr x] h₁ h₂ h₃ : word M N) = inr x :=
ext _ _ $ eq.symm $ to_list_inr $ by simpa [eq_comm] using h₂

lemma cons'_mul (x : M ⊕ N) (w₁ w₂ : word M N) (h) : cons' x w₁ h * w₂ = cons x (w₁ * w₂) :=
begin
  rw [cons'],
  split_ifs with hx,
  { simp only [← to_list_smul, of_list_smul, foldr] },
  { simp only [not_and_distrib, ne.def, not_not] at hx,
    rcases hx with (rfl|rfl); simp only [cons_inl_one, cons_inr_one] }
end

lemma cons_inl_mul (x y : M) (w : word M N) :
  cons (.inl (x * y)) w = cons (.inl x) (cons (.inl y) w) :=
begin
  rcases w with ⟨(_|⟨(z|z), l⟩), hl, hr, hc⟩,
  { simp only [mk_nil, mul_one, ← of_mul, of_inl, map_mul] },
  { simp only [cons, mul_assoc, cons'_inl_mul] },
  { simp only [cons, cons'_inl_mul] }
end

lemma cons_inr_mul (x y : N) (w : word M N) :
  cons (.inr (x * y)) w = cons (.inr x) (cons (.inr y) w) :=
begin
  rcases w with ⟨(_|⟨(z|z), l⟩), hl, hr, hc⟩,
  { simp only [mk_nil, mul_one, ← of_mul, of_inr, map_mul] },
  { simp only [cons, cons'_inr_mul] },
  { simp only [cons, mul_assoc, cons'_inr_mul] }
end

lemma cons_mul (x : M ⊕ N) (w₁ w₂ : word M N) : cons x (w₁ * w₂) = cons x w₁ * w₂ :=
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

instance : is_scalar_tower (FreeMonoid (M ⊕ N)) (word M N) (word M N) :=
is_scalar_tower.of_mclosure_eq_top FreeMonoid.closure_range_of $ forall_range_iff.2 $ λ x w₁ w₂,
  by simp only [FreeMonoid.of_smul, smul_eq_mul, cons_mul]

instance : monoid (word M N) :=
{ mul_assoc := λ a b c, smul_assoc (of_list a.to_list) b c,
  .. word.mul_one_class }

@[simp] lemma mrange_smul_one_hom : (smul_one_hom : FreeMonoid (M ⊕ N) →* word M N).mrange = ⊤ :=
top_unique $ λ w hw, ⟨of_list w.to_list, by rw [smul_one_hom_apply, to_list_smul, mul_one]⟩

@[simp] lemma mclosure_range_of : submonoid.closure (range of : set (word M N)) = ⊤ :=
by simp_rw [← mrange_smul_one_hom, monoid_hom.mrange_eq_map, ← FreeMonoid.closure_range_of,
  monoid_hom.map_mclosure, ← range_comp, (∘), smul_one_hom_apply, FreeMonoid.of_smul, cons_one]

@[simp] lemma mclosure_range_inl_union_inr :
  submonoid.closure (range inl ∪ range inr : set (word M N)) = ⊤ :=
by { rw [← mclosure_range_of, .range_eq], refl }

@[simp] lemma mclosure_image_inl_union_inr :
  submonoid.closure (inl '' {1}ᶜ ∪ inr '' {1}ᶜ : set (word M N)) = ⊤ :=
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

lemma prod_eq (l : list (word M N)) (hl : (l.map to_list).join.chain' ((≠) on .is_left)) :
  l.prod = ⟨(l.map to_list).join, by simp [mem_join], by simp [mem_join], hl⟩ :=
begin
  induction l with w l ihl, { refl },
  specialize ihl hl.right_of_append,
  simp only [list.map, join, prod_cons, mk_append, ihl, mk_to_list]
end

lemma prod_eq_of_join_eq {l : list (word M N)} {w : word M N} (h : (l.map to_list).join = w.1) :
  l.prod = w :=
begin
  simp only [prod_eq l (h.symm ▸ w.4), h, mk_to_list],
end

instance : has_inv (word G H) :=
⟨λ w, ⟨(w.to_list.map (.map has_inv.inv has_inv.inv)).reverse,
    by simpa only [mem_reverse, mem_map, .exists, .map_inl, .map_inr, inv_eq_one,
      false_and, exists_false, or_false, @and.comm _ (_ = _), exists_eq_left] using w.2,
    by simpa only [mem_reverse, mem_map, .exists, .map_inl, .map_inr, inv_eq_one,
      false_and, exists_false, false_or, @and.comm _ (_ = _), exists_eq_left] using w.3,
    by simpa only [chain'_reverse, chain'_map, flip, on_fun, .is_left_map, ne_comm] using w.4⟩⟩

lemma to_list_inv (w : word G H) :
  (w⁻¹).to_list = (w.to_list.map (.map has_inv.inv has_inv.inv)).reverse :=
rfl

instance : group (word G H) :=
{ mul_left_inv := λ ⟨l, hl, hr, hc⟩,
    begin
      induction l with x l ihl, { refl },
      specialize ihl (mt (mem_cons_of_mem _) hl) (mt (mem_cons_of_mem _) hr) hc.tail,
      simp only [to_list_inv, map_cons, ← to_list_smul, reverse_cons, of_list_smul, foldr_append,
        foldr] at ihl ⊢,
      cases x;
        simpa only [.map_inl, .map_inr, cons, inv_mul_self, cons'_inl_one, cons'_inr_one]
    end,
  .. word.monoid, .. word.has_inv }

end word

section dec_eq

variables [decidable_eq M] [decidable_eq N]

lemma mk_word_cons' {x : M ⊕ N} {w : word M N} (hxw) :
  mk (of_list (w.cons' x hxw).to_list) = mk (of x) * mk (of_list w.to_list) :=
begin
  rw [word.cons'],
  split_ifs with hx,
  { refl },
  { rw [not_and_distrib, ne.def, ne.def, not_not, not_not] at hx,
    rcases hx with (rfl|rfl); simp only [mk_of_inl, mk_of_inr, map_one, one_mul] }
end

lemma mk_word_of (x : M ⊕ N) : mk (of_list (word.of x).to_list) = mk (of x) :=
mk_word_cons' _

lemma mk_word_inl (x : M) : mk (of_list (word.inl x : word M N).to_list) = inl x :=
mk_word_of _

lemma mk_word_inr (x : N) : mk (of_list (word.inr x : word M N).to_list) = inr x :=
mk_word_of _

lemma mk_word_cons (x : M ⊕ N) (w : word M N) :
  mk (of_list (w.cons x).to_list) = mk (of x) * mk (of_list w.to_list) :=
by cases x; rcases w with ⟨(_|⟨(y|y), w⟩), hl, hr, hc⟩; simp only [word.cons, mk_word_of,
  of_list_nil, map_one, mul_one, mk_word_cons', of_list_cons, map_mul, mk_of_inl, mk_of_inr,
  mul_assoc, word.tail, list.tail]

lemma mk_smul_word (w₁ : FreeMonoid (M ⊕ N)) (w₂ : word M N) :
  mk (of_list (w₁ • w₂).to_list) = mk w₁ * mk (of_list w₂.to_list) :=
begin
  induction w₁ using FreeMonoid.rec_on with x w₁ ihw,
  { rw [one_smul, map_one, one_mul] },
  { rw [mul_smul, of_smul, mk_word_cons, ihw, map_mul, mul_assoc] }
end

lemma mk_word_mul (w₁ w₂ : word M N) :
  mk (of_list (w₁ * w₂).to_list) = mk (of_list w₁.to_list) * mk (of_list w₂.to_list) :=
mk_smul_word _ _

@[simps symm_apply] def to_word : M ⋆ N ≃* word M N :=
{ to_fun := clift
    (@smul_one_hom (FreeMonoid (M ⊕ N)) (word M N) _ _ _ _)
    (by rw [smul_one_hom_apply, of_smul, word.cons_inl_one])
    (by rw [smul_one_hom_apply, of_smul, word.cons_inr_one])
    (λ x y, by simp only [smul_one_hom_apply, word.of_smul, word.of_inl, map_mul, mul_one])
    (λ x y, by simp only [smul_one_hom_apply, word.of_smul, word.of_inr, map_mul, mul_one]),
  inv_fun := λ w, mk (of_list w.to_list),
  left_inv := mk_surjective.forall.2 $ λ w, by rw [clift_apply_mk, smul_one_hom_apply, mk_smul_word,
    word.to_list_one, of_list_nil, map_one, mul_one],
  right_inv := mul_one,
  map_mul' := map_mul _ }

@[simp] lemma to_word_mk (w : FreeMonoid (M ⊕ N)) : to_word (mk w) = w • 1 := rfl
@[simp] lemma to_word_inl (x : M) : to_word (inl x : M ⋆ N) = word.inl x := rfl
@[simp] lemma to_word_inr (x : N) : to_word (inr x : M ⋆ N) = word.inr x := rfl

@[simp] lemma of_word_smul (w₁ : FreeMonoid (M ⊕ N)) (w₂ : word M N) :
  to_word.symm (w₁ • w₂) = mk w₁ * to_word.symm w₂ :=
mk_smul_word _ _

@[simp] lemma of_word_cons (x : M ⊕ N) (w : word M N) :
  to_word.symm (w.cons x) = mk (of x) * to_word.symm w :=
mk_word_cons _ _

@[simp] lemma of_word_cons' {x : M ⊕ N} {w : word M N} (h) :
  to_word.symm (w.cons' x h) = mk (of x) * to_word.symm w :=
mk_word_cons' _

@[simp] lemma of_word_of (x : M ⊕ N) : to_word.symm (word.of x) = mk (of x) := mk_word_of _
@[simp] lemma of_word_inl (x : M) : to_word.symm (word.inl x : word M N) = inl x := of_word_of _
@[simp] lemma of_word_inr (x : N) : to_word.symm (word.inr x : word M N) = inr x := of_word_of _

namespace word

def lift (f : M →* P) (g : N →* P) : word M N →* P :=
(lift f g).comp (to_word : M ⋆ N ≃* word M N).symm.to_monoid_hom

def fst : word M N →* M := lift (monoid_hom.id _) 1
def snd : word M N →* N := lift 1 (monoid_hom.id _)
def toProd : word M N →* M × N := lift (monoid_hom.inl _ _) (monoid_hom.inr _ _)

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
lemma hom_ext {f g : word M N →* P} (h₁ : f.comp inl = g.comp inl) (h₂ : f.comp inr = g.comp inr) :
  f = g :=
begin
  refine FunLike.ext _ _ (to_word.surjective.forall.2 $ λ x, _),
  simp only [← mul_equiv.coe_to_monoid_hom, ← monoid_hom.comp_apply],
  exact FunLike.ext_iff.1 (hom_ext h₁ h₂) x
end

@[simp] lemma fst_comp_inl : (fst : word M N →* M).comp inl = monoid_hom.id _ := lift_comp_inl _ _
@[simp] lemma fst_apply_inl (x : M) : fst (inl x : word M N) = x := lift_apply_inl _ _ _
@[simp] lemma fst_comp_inr : (fst : word M N →* M).comp inr = 1 := lift_comp_inr _ _
@[simp] lemma fst_apply_inr (x : N) : fst (inr x : word M N) = 1 := lift_apply_inr _ _ _
@[simp] lemma snd_comp_inl : (snd : word M N →* N).comp inl = 1 := lift_comp_inl _ _
@[simp] lemma snd_apply_inl (x : M) : snd (inl x : word M N) = 1 := lift_apply_inl _ _ _
@[simp] lemma snd_comp_inr : (snd : word M N →* N).comp inr = monoid_hom.id _ := lift_comp_inr _ _
@[simp] lemma snd_apply_inr (x : N) : snd (inr x : word M N) = x := lift_apply_inr _ _ _

lemma fst_surjective : surjective (fst : word M N → M) := left_inverse.surjective fst_apply_inl
lemma snd_surjective : surjective (snd : word M N → N) := left_inverse.surjective snd_apply_inr

@[simp] lemma range_fst : set.range (fst : word M N → M) = univ := fst_surjective.range_eq
@[simp] lemma range_snd : set.range (snd : word M N → N) = univ := snd_surjective.range_eq

@[simp] lemma toProd_comp_inl : (toProd : word M N →* M × N).comp inl = monoid_hom.inl _ _ :=
lift_comp_inl _ _

@[simp] lemma toProd_comp_inr : (toProd : word M N →* M × N).comp inr = monoid_hom.inr _ _ :=
lift_comp_inr _ _

@[simp] lemma toProd_apply_inl (x : M) : toProd (inl x : word M N) = (x, 1) :=
lift_apply_inl _ _ _

@[simp] lemma toProd_apply_inr (x : N) : toProd (inr x : word M N) = (1, x) :=
lift_apply_inr _ _ _

@[simp] lemma fst_prod_snd : (fst : word M N →* M).prod snd = toProd :=
by ext1; ext1; simp only [monoid_hom.comp_apply, monoid_hom.prod_apply, fst_apply_inl,
  fst_apply_inr, snd_apply_inl, snd_apply_inr, toProd_apply_inl, toProd_apply_inr]

@[simp] lemma prod_mk_fst_snd (x : word M N) : (fst x, snd x) = toProd x :=
by rw [← fst_prod_snd, monoid_hom.prod_apply]

@[simp] lemma fst_comp_toProd : (monoid_hom.fst M N).comp toProd = fst :=
by rw [← fst_prod_snd, monoid_hom.fst_comp_prod]

@[simp] lemma fst_toProd (x : word M N) : (toProd x).1 = fst x :=
by { rw [← fst_comp_toProd], refl }

@[simp] lemma snd_comp_toProd : (monoid_hom.snd M N).comp toProd = snd :=
by rw [← fst_prod_snd, monoid_hom.snd_comp_prod]

@[simp] lemma snd_toProd (x : word M N) : (toProd x).2 = snd x :=
by { rw [← snd_comp_toProd], refl }

@[simps apply_to_list] def swap_hom : word M N →* word N M :=
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
      simpa only [map_cons, .elim_inl, ha, to_list_inr, join, ne.def, not_false_iff,
        singleton_append, .swap_inl, eq_self_iff_true, true_and] },
    { have ha : a ≠ 1, by { rintro rfl, simp * at * },
      simpa only [map_cons, .elim_inr, ha, to_list_inl, join, ne.def, not_false_iff,
        singleton_append, .swap_inr, eq_self_iff_true, true_and] },
  end

@[simps apply_to_list] def swap : word M N ≃* word N M :=
{ to_fun := swap_hom,
  inv_fun := swap_hom,
  left_inv := λ w, ext _ _ $
    by simp only [swap_hom_apply_to_list, map_map, .swap_swap_eq, list.map_id],
  right_inv := λ w, ext _ _ $
    by simp only [swap_hom_apply_to_list, map_map, .swap_swap_eq, list.map_id],
  map_mul' := map_mul swap_hom }

@[simp] lemma swap_apply_inl (x : M) : swap (inl x : word M N) = inr x :=
by simp only [swap, mul_equiv.coe_mk, swap_hom, monoid_hom.copy_eq_self, lift_apply_inl]

@[simp] lemma swap_apply_inr (x : N) : swap (inr x : word M N) = inl x :=
by simp only [swap, mul_equiv.coe_mk, swap_hom, monoid_hom.copy_eq_self, lift_apply_inr]

@[simp] lemma swap_symm : (swap : word M N ≃* word N M).symm = swap := rfl

end word

end dec_eq

namespace word

local notation `ℤ₂` := mul_z2
local notation `σ` := mul_z2.a

def z2_prod_mker_fst_aux₁ : list (ℤ₂ ⊕ α) → bool → list (α ⊕ α)
| [] _ := []
| (.inl _::l) b := z2_prod_mker_fst_aux₁ l (!b)
| (.inr x::l) b := cond b (.inl x) (.inr x) :: z2_prod_mker_fst_aux₁ l b

lemma one_nmem_z2_prod_mker_fst_aux₁ [has_one α] : ∀ (b : bool) {l : list (ℤ₂ ⊕ α)},
  (.inl 1 ∉ z2_prod_mker_fst_aux₁ l b ∧ .inr 1 ∉ z2_prod_mker_fst_aux₁ l b) ↔
    .inr (1 : α) ∉ l
| _ [] := and_self _
| b (.inl x::l) := by simp only [one_nmem_z2_prod_mker_fst_aux₁, z2_prod_mker_fst_aux₁,
  mem_cons_iff, false_or]
| b (.inr x::l) := by cases b; simp only [one_nmem_z2_prod_mker_fst_aux₁, z2_prod_mker_fst_aux₁,
  cond, mem_cons_iff, false_or, not_or_distrib, and.left_comm, and_assoc]

def z2_prod_mker_fst_aux₂ : list (α ⊕ α) → list (ℤ₂ ⊕ α)
| [] := []
| (.inl x :: l) := .inl σ :: .inr x :: .inl σ :: z2_prod_mker_fst_aux₂ l
| (.inr x :: l) := .inr x :: z2_prod_mker_fst_aux₂ l

lemma z2_prod_mker_fst_inv₁ :
  ∀ l : list (α ⊕ α), z2_prod_mker_fst_aux₁ (z2_prod_mker_fst_aux₂ l) ff = l
| [] := rfl
| (.inl x :: l) := by { simp only [z2_prod_mker_fst_aux₁, z2_prod_mker_fst_aux₂, bnot, cond,
  z2_prod_mker_fst_inv₁ l], exact ⟨rfl, rfl⟩ }
| (.inr x :: l) := by rw [z2_prod_mker_fst_aux₂, z2_prod_mker_fst_aux₁, z2_prod_mker_fst_inv₁,
  cond]

lemma inr_one_nmem_z2_prod_mker_fst_aux₂ [has_one α] {l : list (α ⊕ α)} :
  .inr (1 : α) ∉ z2_prod_mker_fst_aux₂ l ↔ .inl (1 : α) ∉ l ∧ .inr (1 : α) ∉ l :=
by rw [← one_nmem_z2_prod_mker_fst_aux₁ ff, z2_prod_mker_fst_inv₁]

lemma chain'_z2_prod_mker_fst_aux₂ : ∀ l : list (α ⊕ α),
  (z2_prod_mker_fst_aux₂ l).chain' ((≠) on .is_left) ↔ l.chain' ((≠) on .is_left)
| [] := iff.rfl
| [x] := by cases x; simp only [z2_prod_mker_fst_aux₂, on_fun, .is_left, ne.def, chain'_cons,
  not_false_iff, chain'_singleton, and_self]
| (.inl x :: .inl y :: l) := by simp only [z2_prod_mker_fst_aux₂, on_fun, .is_left, ne.def,
  chain'_cons, eq_self_iff_true, not_true, false_and, and_false]
| (.inr x :: .inr y :: l) := by simp only [z2_prod_mker_fst_aux₂, on_fun, .is_left, ne.def,
  chain'_cons, eq_self_iff_true, not_true, false_and]
| (.inl x :: .inr y :: l) :=
  by simpa only [z2_prod_mker_fst_aux₂, on_fun, .is_left, ne.def, chain'_cons, not_false_iff,
    true_and] using chain'_z2_prod_mker_fst_aux₂ (.inr y :: l)
| (.inr x :: .inl y :: l) :=
  by simpa only [z2_prod_mker_fst_aux₂, on_fun, .is_left, ne.def, chain'_cons, not_false_iff,
    true_and] using chain'_z2_prod_mker_fst_aux₂ (.inl y :: l)

lemma z2_prod_mker_fst_inv₂ :
  ∀ l : list (ℤ₂ ⊕ α), .inl (1 : ℤ₂) ∉ l →
    (l.map (.elim id (λ _, (1 : ℤ₂)))).prod = 1 →
    l.chain' ((≠) on .is_left) →
    z2_prod_mker_fst_aux₂ (z2_prod_mker_fst_aux₁ l ff) = l
| [] _ _ _ := rfl
| (.inr x :: l) h₁ h₂ h₃ := congr_arg2 list.cons rfl $ z2_prod_mker_fst_inv₂ l
  (mt (mem_cons_of_mem _) h₁) (by rwa [map_cons, .elim_inr, prod_cons, one_mul] at h₂) h₃.tail
| [.inl x] h₁ h _ := absurd h $ by simpa [eq_comm] using h₁
| (.inl x :: .inl y :: l) _ _ h := (h.rel_head rfl).elim
| [.inl x, .inr y] h₁ h _ := absurd h $ by simpa [eq_comm] using h₁
| (.inl x :: .inr y :: .inl z :: l) h₁ h₂ h₃ :=
  begin
    simp only [mem_cons_iff, not_or_distrib, ← ne.def, mul_z2.one_ne_iff] at h₁,
    rcases h₁ with ⟨rfl, -, rfl, h₁⟩,
    have h₂' : (l.map (.elim id (λ _, (1 : ℤ₂)))).prod = 1,
      by simpa [← mul_assoc, mul_z2.mul_self] using h₂,
    simp only [z2_prod_mker_fst_aux₁, z2_prod_mker_fst_aux₂, bnot, cond, eq_self_iff_true, true_and],
    exact z2_prod_mker_fst_inv₂ l h₁ h₂' h₃.tail.tail.tail
  end
| (.inl x :: .inr y :: .inr z :: l) _ _ h := (h.tail.rel_head rfl).elim

lemma z2_prod_mker_fst_aux₂_eq_join : ∀ l : list (M ⊕ M),
  z2_prod_mker_fst_aux₂ l =
    (l.map (.elim (λ x, [.inl σ, .inr x, .inl σ]) (λ x, [.inr x]))).join
| [] := rfl
| (.inl x::l) := congr_arg2 list.cons rfl $ congr_arg2 list.cons rfl $ congr_arg2 list.cons rfl $
    z2_prod_mker_fst_aux₂_eq_join l
| (.inr x::l) := congr_arg2 list.cons rfl $ z2_prod_mker_fst_aux₂_eq_join l

variables [decidable_eq M]

def z2_prod_mker_fst_fun (w : word M M) : (fst : word ℤ₂ M →* ℤ₂).mker :=
⟨⟨z2_prod_mker_fst_aux₂ w.to_list,
  begin
    induction w.to_list with x w ihw, { exact not_false },
    cases x; simp [z2_prod_mker_fst_aux₂, ihw, mul_z2.one_ne_a]
  end,
  inr_one_nmem_z2_prod_mker_fst_aux₂.2 ⟨w.2, w.3⟩,
  (chain'_z2_prod_mker_fst_aux₂ _).2 w.4⟩,
  begin
    simp_rw [monoid_hom.mem_mker, fst, lift_apply_mk, z2_prod_mker_fst_aux₂_eq_join],
    induction w.to_list with x l ihl, { refl },
    cases x; simp only [map_cons, .elim_inl, .elim_inr, join, map_append,
      monoid_hom.one_apply, monoid_hom.id_apply, prod_append, prod_cons, one_mul, ihl, map_nil,
      prod_nil, mul_one, mul_z2.mul_self]
  end⟩

lemma z2_prod_mker_fst_fun_cons' {x : (M ⊕ M)} {w : word M M} (h) :
  z2_prod_mker_fst_fun (w.cons' x h) = z2_prod_mker_fst_fun (of x) * z2_prod_mker_fst_fun w :=
begin
  rw [of, cons', cons'],
  split_ifs with hx; cases x; simp only [z2_prod_mker_fst_fun, z2_prod_mker_fst_aux₂, to_list_one,
    submonoid.mk_mul_mk, mk_mul, foldr]; simp only [mk_cons, cons'_eq_cons]; refl
end

def z2_prod_mker_fst : word M M ≃* (fst : word ℤ₂ M →* ℤ₂).mker :=
{ to_fun := monoid_hom.of_mclosure_eq_top_left (@z2_prod_mker_fst_fun M _ _) mclosure_range_of rfl $
  forall_range_iff.2 $
    begin
      have h1 : z2_prod_mker_fst_fun (1 : word M M) = 1 := rfl,
      intros x w,
      rw [of_mul],
      rcases w with ⟨(_|⟨y, l⟩), hl, hr, hc⟩, { simp only [mk_nil, mul_one, h1, cons_one] },
      cases x; rcases eq_or_ne x 1 with rfl|hx;
        try { simp only [cons_inl_one, cons_inr_one, of_inl_one, of_inr_one, h1, one_mul] };
        cases y; simp only [cons, z2_prod_mker_fst_fun_cons', tail, list.tail];
        simp only [mk_cons, z2_prod_mker_fst_fun_cons', ← mul_assoc]; congr' 1;
        simp only [mem_cons_iff, not_or_distrib] at hl hr;
        simp only [z2_prod_mker_fst_fun, submonoid.mk_mul_mk, mk_mul, of_inl, of_inr];
        ext : 2; simp only [subtype.coe_mk],
      { simp only [to_list_inl hx, to_list_inl (ne.symm hl.1), z2_prod_mker_fst_aux₂, foldr,
          cons, mul_z2.mul_self, cons'_inl_one, tail, list.tail],
        by_cases hxy : x * y = 1,
        { simp only [hxy, cons'_inr_one, cons, mul_z2.mul_self, map_one, cons'_inl_one], refl },
        { simp only [to_list_inl hxy, z2_prod_mker_fst_aux₂, cons'],
          rw [dif_pos]; [skip, simpa],
          rw [cons, cons', dif_pos], simp [mul_z2.a_ne_one] } },
      { simp only [to_list_inr hx, to_list_inr (ne.symm hr.1), z2_prod_mker_fst_aux₂, foldr,
          cons, tail, list.tail, mk_nil, cons'_one, of_inr],
        by_cases hxy : x * y = 1,
        { rw [hxy, map_one, map_one], refl },
        { rw [to_list_inr hxy, to_list_inr hxy], refl } }
    end,
  inv_fun := λ w, ⟨z2_prod_mker_fst_aux₁ w.1.1 ff, ((one_nmem_z2_prod_mker_fst_aux₁ ff).2 w.1.3).1,
    ((one_nmem_z2_prod_mker_fst_aux₁ ff).2 w.1.3).2,
    begin
      rw [← chain'_z2_prod_mker_fst_aux₂, z2_prod_mker_fst_inv₂ w.1.1 w.1.2 w.2 w.1.4],
      exact w.1.4
    end⟩,
  left_inv := λ w, ext _ _ $ z2_prod_mker_fst_inv₁ _,
  right_inv := λ w, subtype.ext $ ext _ _ $ z2_prod_mker_fst_inv₂ w.1.1 w.1.2 w.2 w.1.4,
  map_mul' := map_mul _ }

lemma to_list_coe_z2_prod_mker_fst (w : word M M) :
  (w.z2_prod_mker_fst : word ℤ₂ M).to_list =
    (w.to_list.map (.elim (λ x, [.inl σ, .inr x, .inl σ]) (λ x, [.inr x]))).join :=
z2_prod_mker_fst_aux₂_eq_join _

@[simp] lemma z2_prod_mker_fst_inl (x : M) :
  (z2_prod_mker_fst (inl x) : word ℤ₂ M) = inl σ * inr x * inl σ :=
begin
  rcases eq_or_ne x 1 with rfl | hx, { simp [← map_mul] },
  rw [← mk_to_list (z2_prod_mker_fst (inl x) : word ℤ₂ M)],
  simp only [to_list_coe_z2_prod_mker_fst, to_list_inl hx, list.map, join_singleton, .elim_inl,
    mk_cons, cons'_eq_cons, mk_nil, ← of_mul, of_inl, of_inr, mul_one, mul_assoc]
end

@[simp] lemma z2_prod_mker_fst_inr (x : M) : (z2_prod_mker_fst (inr x) : word ℤ₂ M) = inr x :=
begin
  rcases eq_or_ne x 1 with rfl | hx, { simp [← map_mul] },
  rw [← mk_to_list (z2_prod_mker_fst (inr x) : word ℤ₂ M)],
  simp only [to_list_coe_z2_prod_mker_fst, to_list_inr hx, list.map, .elim_inr, join_singleton,
    mk_cons, mk_nil, cons'_one, of_inr]
end

def conj_a_mker_fst_z2 : (fst : word ℤ₂ M →* ℤ₂).mker ≃* (fst : word ℤ₂ M →* ℤ₂).mker :=
{ map_mul' := λ w₁ w₂, subtype.ext $
    begin
      simp_rw [involutive.to_perm, coe_mul, set_like.coe_mk, mul_assoc],
      rw [← mul_assoc (inl σ) (inl σ), ← map_mul, mul_z2.mul_self, map_one, one_mul]
    end,
  .. involutive.to_perm (λ w, ⟨inl σ * (w : word ℤ₂ M) * inl σ,
    by simpa only [monoid_hom.mem_mker, map_mul fst, fst_apply_inl, mul_right_comm _ _ σ]
      using w.2⟩ : (fst : word ℤ₂ M →* ℤ₂).mker → (fst : word ℤ₂ M →* ℤ₂).mker)
    (λ w, subtype.ext $ by simp_rw [subtype.coe_mk, mul_assoc, ← map_mul, mul_z2.mul_self, map_one,
      mul_one, ← mul_assoc, ← map_mul, mul_z2.mul_self, map_one, one_mul]), }

@[simp] lemma coe_conj_a_mker_fst_z2 (w : (fst : word ℤ₂ M →* ℤ₂).mker) :
  (conj_a_mker_fst_z2 w : word ℤ₂ M) = inl σ * w * inl σ :=
rfl

@[simp] lemma conj_a_mker_fst_z2_symm : (@conj_a_mker_fst_z2 M _ _).symm = conj_a_mker_fst_z2 :=
rfl

lemma z2_prod_mker_fst_trans_conj_a_mker_fst_z2 :
  (@z2_prod_mker_fst M _ _).trans conj_a_mker_fst_z2 = swap.trans z2_prod_mker_fst :=
begin
  refine mul_equiv.to_monoid_hom_injective
    (monoid_hom.eq_of_eq_on_mdense mclosure_image_inl_union_inr _),
  rintro _ (⟨x, hx : x ≠ 1, rfl⟩ | ⟨x, hx : x ≠ 1, rfl⟩); ext1; simp [mul_assoc, ← map_mul],
  simp [← mul_assoc, ← map_mul]
end

lemma z2_prod_mker_fst_symm_conj_a (w : (fst : word ℤ₂ M →* ℤ₂).mker) :
  (z2_prod_mker_fst.symm (conj_a_mker_fst_z2 w)) = swap (z2_prod_mker_fst.symm w) :=
by rw [← conj_a_mker_fst_z2_symm, ← mul_equiv.symm_trans_apply,
  z2_prod_mker_fst_trans_conj_a_mker_fst_z2, mul_equiv.symm_trans_apply, swap_symm]

end word

end free_prod
