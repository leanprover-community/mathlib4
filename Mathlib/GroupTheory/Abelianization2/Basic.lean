import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs

import Mathlib.GroupTheory.Abelianization2.Defs
import Mathlib.GroupTheory.Commutator

variable {M N : Type*}
namespace Abelianization2

instance [Mul M] [Fintype M] [DecidableRel (conGen (Rel M))] : Fintype (Abelianization2 M) :=
  Quotient.fintype _

instance [Mul M] [Finite M] : Finite (Abelianization2 M) :=
  Quotient.finite _

section Semigroup
variable [Semigroup M]

instance : CommSemigroup (Abelianization2 M) where
  __ := inferInstanceAs (Semigroup (conGen (Rel M)).Quotient)
  mul_comm := Abelianization2.mul_comm

/-- `of'` is the canonical projection from M to its abelianization, as a `MulHom` -/
def of' : M →ₙ* Abelianization2 M where
  toFun m := Quotient.mk _ m
  map_mul' _ _ := rfl

@[simp]
theorem mk_eq_of' (a : M) : Quot.mk _ a = of' a := rfl

def lift' {N : Type*} [CommSemigroup N] : (M →ₙ* N) ≃ (Abelianization2 M →ₙ* N) where
  toFun f := {
    toFun m := (Con.liftOn m f (by
      intro a b h
      induction h with
      | of _ _ h' =>
        cases h'
        rw [map_mul,map_mul,_root_.mul_comm]
      | refl => rfl
      | symm _ h2=> rw [h2]
      | trans _ _ h1 h2 => rw [h1,h2]
      | mul _ _ h1 h2 => rw [map_mul,map_mul,h1,h2])),
    map_mul' x y := by
      induction x, y using Con.induction_on₂
      rw [← Con.coe_mul, Con.liftOn_coe,Con.liftOn_coe,Con.liftOn_coe,map_mul] }
  invFun f := f.comp of'
  left_inv f := rfl
  right_inv f := by ext x; cases x using Con.induction_on; rfl

lemma lift'_of' {N : Type*} [CommSemigroup N] {f : M →ₙ* N} :
  ∀ m, lift' f (of' m) = f m := fun _ => rfl
end Semigroup

section Monoid
variable [Monoid M]

instance : CommMonoid (Abelianization2 M) where
  __ := inferInstanceAs (Monoid (conGen (Rel M)).Quotient)
  __ := instCommSemigroup

/-- `of` is the canonical projection from M to its abelianization, as a `MonoidHom` -/
def of : M →* Abelianization2 M where
  __ := of'
  map_one' := rfl

@[simp]
theorem of'_eq_of (a : M) : of' a = of a := rfl

-- not clear if these simp lemmas ever fire...
-- theoretically this should already be solved by simp via `mk_eq_of'` and `of'_eq_of`.
@[simp]
theorem mk_eq_of (a : M) : Quot.mk _ a = of a := rfl


def lift {N : Type*} [Monoid M] [CommMonoid N] : (M →* N) ≃ (Abelianization2 M →* N) where
  toFun f := {
  __ := lift' f.toMulHom
  map_one' := by rw [← f.map_one]; rfl
  }
  invFun f := f.comp of
  left_inv f := rfl
  right_inv f:= by ext x; cases x using Con.induction_on; rfl

lemma lift_of {N : Type*} [CommMonoid N] {f : M →* N} : ∀ m, lift f (of m) = f m :=
  fun _ => rfl

end Monoid

section Group
variable [Group M]

instance : CommGroup (Abelianization2 M) where
  __ := inferInstanceAs (Group (conGen (Rel M)).Quotient)
  __ := instCommSemigroup

-- def equivQuot : Abelianization2 M ≃* M ⧸ commutator M:= sorry
@[simp]
theorem ker_of : of.ker = commutator M := by
  rw [commutator_def, Subgroup.commutator_def]
  simp only [Subgroup.mem_top, true_and]
  ext m
  constructor
  · simp only [MonoidHom.mem_ker]
    intro hm
    have : (conGen (Abelianization2.Rel M)) m 1 := by
      rw [← Con.eq]
      exact hm
    
    cases this with
    | of x y _ => sorry
    | refl x => sorry
    | symm _ => sorry
    | trans _ _ => sorry
    | mul _ _ => sorry
  · intro hm
    induction hm using Subgroup.closure_induction with
    | mem m hm =>
      obtain ⟨g₁,g₂,rfl⟩ := hm
      simp only [MonoidHom.mem_ker,commutatorElement_def]
      rw [mul_assoc, ← mul_inv_rev, map_mul, map_inv, mul_eq_one_iff_eq_inv, inv_inv, map_mul,
        map_mul, mul_comm]
    | one => rfl
    | mul m₁ m₂ _ _ hm₁ hm₂ =>
      exact mul_mem hm₁ hm₂
    | inv m _ hm =>
      exact inv_mem hm





section lift

-- So far we have built Gᵃᵇ and proved it's an abelian group.
-- Furthermore we defined the canonical projection `of : G → Gᵃᵇ`
-- Let `A` be an abelian group and let `f` be a group homomorphism from `G` to `A`.
-- variable {A : Type v} [CommGroup A] (f : G →* A)

-- theorem commutator_subset_ker : commutator G ≤ f.ker := by
--   rw [commutator_eq_closure, Subgroup.closure_le]
--   rintro x ⟨p, q, rfl⟩
--   simp [MonoidHom.mem_ker, mul_right_comm (f p) (f q), commutatorElement_def]

-- /-- If `f : G → A` is a group homomorphism to an abelian group, then `lift f` is the unique map
--   from the abelianization of a `G` to `A` that factors through `f`. -/
-- def lift : (G →* A) ≃ (Abelianization G →* A) where
--   toFun f := QuotientGroup.lift _ f fun _ h => MonoidHom.mem_ker.2 <| commutator_subset_ker _ h
--   invFun F := F.comp of
--   left_inv _ := MonoidHom.ext fun _ => rfl
--   right_inv _ := MonoidHom.ext fun x => QuotientGroup.induction_on x fun _ => rfl

-- @[simp]
-- theorem lift.of (x : G) : lift f (of x) = f x :=
--   rfl

-- theorem lift.unique (φ : Abelianization G →* A)
--     -- hφ : φ agrees with f on the image of G in Gᵃᵇ
--     (hφ : ∀ x : G, φ (Abelianization.of x) = f x)
--     {x : Abelianization G} : φ x = lift f x :=
--   QuotientGroup.induction_on x hφ

-- @[simp]
-- theorem lift_of : lift of = MonoidHom.id (Abelianization G) :=
--   lift.apply_symm_apply <| MonoidHom.id _

end lift

end Group



end Abelianization2
