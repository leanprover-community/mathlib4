/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Congruence
import Mathlib.GroupTheory.Submonoid.Membership

/-!
# Free product of two monoids or groups
-/

open FreeMonoid Function List Set

def freeProdCon (M N : Type _) [MulOneClass M] [MulOneClass N] : Con (FreeMonoid (M ⊕ N)) :=
infₛ {c |
  (∀ x y : M, c (of (Sum.inl (x * y))) (of (Sum.inl x) * of (Sum.inl y)))
  ∧ (∀ x y : N, c (of (Sum.inr (x * y))) (of (Sum.inr x) * of (Sum.inr y)))
  ∧ c (of $ Sum.inl 1) 1 ∧ c (of $ Sum.inr 1) 1}

def FreeProd (M N : Type _) [MulOneClass M] [MulOneClass N] := (freeProdCon M N).Quotient

local infix:70 " ⋆ " => FreeProd

namespace FreeProd

section MulOneClass

variable {M N M' N' P : Type _} [MulOneClass M] [MulOneClass N] [MulOneClass M'] [MulOneClass N']
  [MulOneClass P]

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

def map (f : M →* M') (g : N →* N') : M ⋆ N →* M' ⋆ N' :=
  clift (mk.comp <| FreeMonoid.map <| Sum.map f g)
    (by simp only [MonoidHom.comp_apply, map_of, Sum.map_inl, map_one, mk_of_inl])
    (by simp only [MonoidHom.comp_apply, map_of, Sum.map_inr, map_one, mk_of_inr])
    (fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.map_inl, map_mul, mk_of_inl])
    fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.map_inr, map_mul, mk_of_inr]

@[simp] lemma map_mk_ofList (f : M →* M') (g : N →* N') (l : List (M ⊕ N)) :
    map f g (mk (ofList l)) = mk (ofList (l.map (Sum.map f g))) :=
  rfl

@[simp] lemma map_inl (f : M →* M') (g : N →* N') (x : M) :
    map f g (inl x) = inl (f x) :=
  rfl

@[simp] lemma map_inr (f : M →* M') (g : N →* N') (x : N) :
    map f g (inr x) = inr (g x) :=
  rfl

@[simp] lemma map_comp_inl (f : M →* M') (g : N →* N') :
    (map f g).comp inl = inl.comp f :=
  rfl

@[simp] lemma map_comp_inr (f : M →* M') (g : N →* N') :
    (map f g).comp inr = inr.comp g :=
  rfl

@[simp] lemma map_id_id : map (.id M) (.id N) = .id (M ⋆ N) := hom_ext rfl rfl

lemma map_comp_map {M'' N''} [MulOneClass M''] [MulOneClass N''] (f' : M' →* M'') (g' : N' →* N'')
    (f : M →* M') (g : N →* N') : (map f' g').comp (map f g) = map (f'.comp f) (g'.comp g) :=
  hom_ext rfl rfl

lemma map_map {M'' N''} [MulOneClass M''] [MulOneClass N''] (f' : M' →* M'') (g' : N' →* N'')
    (f : M →* M') (g : N →* N') (x : M ⋆ N) :
    map f' g' (map f g x) = map (f'.comp f) (g'.comp g) x :=
  FunLike.congr_fun (map_comp_map f' g' f g) x

variable (M N)

def swap : M ⋆ N →* N ⋆ M :=
  clift (mk.comp <| FreeMonoid.map Sum.swap)
    (by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inl, mk_of_inr, map_one])
    (by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inr, mk_of_inl, map_one])
    (fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inl, mk_of_inr, map_mul])
    (fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inr, mk_of_inl, map_mul])

@[simp] lemma swap_comp_swap : (swap M N).comp (swap N M) = .id _ := hom_ext rfl rfl

variable {M N}

@[simp] lemma swap_swap (x : M ⋆ N) : swap N M (swap M N x) = x :=
  FunLike.congr_fun (swap_comp_swap _ _) x

lemma swap_comp_map (f : M →* M') (g : N →* N') :
    (swap M' N').comp (map f g) = (map g f).comp (swap M N) :=
  hom_ext rfl rfl

lemma swap_map (f : M →* M') (g : N →* N') (x : M ⋆ N) :
    swap M' N' (map f g x) = map g f (swap M N x) :=
  FunLike.congr_fun (swap_comp_map f g) x

@[simp] lemma swap_comp_inl : (swap M N).comp inl = inr := rfl
@[simp] lemma swap_inl (x : M) : swap M N (inl x) = inr x := rfl
@[simp] lemma swap_comp_inr : (swap M N).comp inr = inl := rfl
@[simp] lemma swap_inr (x : N) : swap M N (inr x) = inl x := rfl

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

@[simp] lemma lift_comp_swap (f : M →* P) (g : N →* P) :
    (lift f g).comp (swap N M) = lift g f :=
  hom_ext rfl rfl

@[simp] lemma lift_swap (f : M →* P) (g : N →* P) (x : N ⋆ M) :
    lift f g (swap N M x) = lift g f x :=
  FunLike.congr_fun (lift_comp_swap f g) x

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

@[simp] lemma fst_comp_swap : fst.comp (swap M N) = snd := lift_comp_swap _ _
@[simp] lemma fst_swap (x : M ⋆ N) : fst (swap M N x) = snd x := lift_swap _ _ _
@[simp] lemma snd_comp_swap : snd.comp (swap M N) = fst := lift_comp_swap _ _
@[simp] lemma snd_swap (x : M ⋆ N) : snd (swap M N x) = fst x := lift_swap _ _ _

@[simp] lemma lift_inr_inl : lift (inr : M →* N ⋆ M) inl = swap M N := hom_ext rfl rfl
@[simp] lemma lift_inl_inr : lift (inl : M →* M ⋆ N) inr = .id _ := hom_ext rfl rfl

lemma mk_of_inv_mul : ∀ x : G ⊕ H, mk (of (x.map Inv.inv Inv.inv)) * mk (of x) = 1
| Sum.inl _ => map_mul_eq_one inl (mul_left_inv _)
| Sum.inr _ => map_mul_eq_one inr (mul_left_inv _)

lemma con_mul_left_inv (x : FreeMonoid (G ⊕ H)) :
    freeProdCon G H (ofList (x.toList.map (Sum.map Inv.inv Inv.inv)).reverse * x) 1 := by
  rw [← mk_eq_mk, map_mul, map_one]
  induction x using FreeMonoid.recOn
  case h0 => simp [Con.refl]
  case ih x xs ihx =>
    simp only [toList_of_mul, map_cons, reverse_cons, ofList_append, map_mul, ihx, ofList_singleton]
    rwa [mul_assoc, ← mul_assoc (mk (of _)), mk_of_inv_mul, one_mul]

instance : Inv (G ⋆ H) where
  inv := Quotient.map' (fun w => ofList (w.toList.map (Sum.map Inv.inv Inv.inv)).reverse)
    ((freeProdCon G H).map_of_mul_left_rel_one _ con_mul_left_inv)

lemma inv_def (w : FreeMonoid (G ⊕ H)) :
  (mk w)⁻¹ = mk (ofList (w.toList.map (Sum.map Inv.inv Inv.inv)).reverse) :=
rfl

instance : Group (G ⋆ H) where
  mul_left_inv := mk_surjective.forall.2 <| fun x => mk_eq_mk.2 (con_mul_left_inv x)

end FreeProd

open FreeProd

namespace MulEquiv

section MulOneClass

variable {M N M' N' : Type _} [MulOneClass M] [MulOneClass N] [MulOneClass M']
    [MulOneClass N']

@[simps! (config := { fullyApplied := false })]
def freeProdCongr (e : M ≃* N) (e' : M' ≃* N') : (M ⋆ M') ≃* (N ⋆ N') :=
  (FreeProd.map (e : M →* N) (e' : M' →* N')).toMulEquiv (FreeProd.map e.symm e'.symm)
    (by ext <;> simp) (by ext <;> simp)

variable (M N)

@[simps! (config := { fullyApplied := false })]
def freeProdComm : M ⋆ N ≃* N ⋆ M :=
  (FreeProd.swap _ _).toMulEquiv (FreeProd.swap _ _) (FreeProd.swap_comp_swap _ _)
    (FreeProd.swap_comp_swap _ _)

end MulOneClass

variable (M N P : Type _) [Monoid M] [Monoid N] [Monoid P]

def freeProdAssoc : (M ⋆ N) ⋆ P ≃* M ⋆ (N ⋆ P) :=
  MonoidHom.toMulEquiv
    (FreeProd.lift (FreeProd.map (.id M) inl) (inr.comp inr))
    (FreeProd.lift (inl.comp inl) (FreeProd.map inr (.id P)))
    (by ext <;> rfl) (by ext <;> rfl)

variable {M N P}

@[simp] lemma freeProdAssoc_apply_inl_inl (x : M) :
    freeProdAssoc M N P (inl (inl x)) = inl x :=
  rfl

@[simp] lemma freeProdAssoc_apply_inl_inr (x : N) :
    freeProdAssoc M N P (inl (inr x)) = inr (inl x) :=
  rfl

@[simp] lemma freeProdAssoc_apply_inr (x : P) :
    freeProdAssoc M N P (inr x) = inr (inr x) :=
  rfl

@[simp] lemma freeProdAssoc_symm_apply_inl (x : M) :
    (freeProdAssoc M N P).symm (inl x) = inl (inl x) :=
  rfl

@[simp] lemma freeProdAssoc_symm_apply_inr_inl (x : N) :
    (freeProdAssoc M N P).symm (inr (inl x)) = inl (inr x) :=
  rfl

@[simp] lemma freeProdAssoc_symm_apply_inr_inr (x : P) :
    (freeProdAssoc M N P).symm (inr (inr x)) = inr x :=
  rfl

end MulEquiv
