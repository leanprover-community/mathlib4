/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Module.NatInt
import Mathlib.GroupTheory.Abelianization
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Free abelian groups

The free abelian group on a type `α`, defined as the abelianisation of
the free group on `α`.

The free abelian group on `α` can be abstractly defined as the left adjoint of the
forgetful functor from abelian groups to types. Alternatively, one could define
it as the functions `α → ℤ` which send all but finitely many `(a : α)` to `0`,
under pointwise addition. In this file, it is defined as the abelianisation
of the free group on `α`. All the constructions and theorems required to show
the adjointness of the construction and the forgetful functor are proved in this
file, but the category-theoretic adjunction statement is in
`Algebra.Category.Group.Adjunctions`.

## Main definitions

Here we use the following variables: `(α β : Type*) (A : Type*) [AddCommGroup A]`

* `FreeAbelianGroup α` : the free abelian group on a type `α`. As an abelian
group it is `α →₀ ℤ`, the functions from `α` to `ℤ` such that all but finitely
many elements get mapped to zero, however this is not how it is implemented.

* `lift f : FreeAbelianGroup α →+ A` : the group homomorphism induced
  by the map `f : α → A`.

* `map (f : α → β) : FreeAbelianGroup α →+ FreeAbelianGroup β` : functoriality
    of `FreeAbelianGroup`.

* `instance [Monoid α] : Semigroup (FreeAbelianGroup α)`

* `instance [CommMonoid α] : CommRing (FreeAbelianGroup α)`

It has been suggested that we would be better off refactoring this file
and using `Finsupp` instead.

## Implementation issues

The definition is `def FreeAbelianGroup : Type u := Additive <| Abelianization <| FreeGroup α`.

Chris Hughes has suggested that this all be rewritten in terms of `Finsupp`.
Johan Commelin has written all the API relating the definition to `Finsupp`
in the lean-liquid repo.

The lemmas `map_pure`, `map_of`, `map_zero`, `map_add`, `map_neg` and `map_sub`
are proved about the `Functor.map` `<$>` construction, and need `α` and `β` to
be in the same universe. But
`FreeAbelianGroup.map (f : α → β)` is defined to be the `AddGroup`
homomorphism `FreeAbelianGroup α →+ FreeAbelianGroup β` (with `α` and `β` now
allowed to be in different universes), so `(map f).map_add`
etc can be used to prove that `FreeAbelianGroup.map` preserves addition. The
functions `map_id`, `map_id_apply`, `map_comp`, `map_comp_apply` and `map_of_apply`
are about `FreeAbelianGroup.map`.

-/


universe u v

variable (α : Type u)

/-- The free abelian group on a type. -/
def FreeAbelianGroup : Type u :=
  Additive <| Abelianization <| FreeGroup α

-- FIXME: this is super broken, because the functions have type `Additive .. → ..`
-- instead of `FreeAbelianGroup α → ..` and those are not defeq!
instance FreeAbelianGroup.addCommGroup : AddCommGroup (FreeAbelianGroup α) :=
  @Additive.addCommGroup _ <| Abelianization.commGroup _

instance : Inhabited (FreeAbelianGroup α) :=
  ⟨0⟩

instance [IsEmpty α] : Unique (FreeAbelianGroup α) := by unfold FreeAbelianGroup; infer_instance

variable {α}

namespace FreeAbelianGroup

/-- The canonical map from `α` to `FreeAbelianGroup α`. -/
def of (x : α) : FreeAbelianGroup α :=
  Additive.ofMul <| Abelianization.of <| FreeGroup.of x

/-- The map `FreeAbelianGroup α →+ A` induced by a map of types `α → A`. -/
def lift {β : Type v} [AddCommGroup β] : (α → β) ≃ (FreeAbelianGroup α →+ β) :=
  (@FreeGroup.lift _ (Multiplicative β) _).trans <|
    (@Abelianization.lift _ _ (Multiplicative β) _).trans MonoidHom.toAdditive

namespace lift

variable {β : Type v} [AddCommGroup β] (f : α → β)

open FreeAbelianGroup

-- Porting note: needed to add `(β := Multiplicative β)` and `using 1`.
@[simp]
protected theorem of (x : α) : lift f (of x) = f x := by
  convert Abelianization.lift.of
     (FreeGroup.lift f (β := Multiplicative β)) (FreeGroup.of x) using 1
  exact (FreeGroup.lift.of (β := Multiplicative β)).symm

protected theorem unique (g : FreeAbelianGroup α →+ β) (hg : ∀ x, g (of x) = f x) {x} :
    g x = lift f x :=
  DFunLike.congr_fun (lift.symm_apply_eq.mp (funext hg : g ∘ of = f)) _

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
protected theorem ext (g h : FreeAbelianGroup α →+ β) (H : ∀ x, g (of x) = h (of x)) : g = h :=
  lift.symm.injective <| funext H

theorem map_hom {α β γ} [AddCommGroup β] [AddCommGroup γ] (a : FreeAbelianGroup α) (f : α → β)
    (g : β →+ γ) : g (lift f a) = lift (g ∘ f) a := by
  show (g.comp (lift f)) a = lift (g ∘ f) a
  apply lift.unique
  intro a
  show g ((lift f) (of a)) = g (f a)
  simp only [(· ∘ ·), lift.of]

end lift

section

open scoped Classical

theorem of_injective : Function.Injective (of : α → FreeAbelianGroup α) :=
  fun x y hoxy ↦ Classical.by_contradiction fun hxy : x ≠ y ↦
    let f : FreeAbelianGroup α →+ ℤ := lift fun z ↦ if x = z then (1 : ℤ) else 0
    have hfx1 : f (of x) = 1 := (lift.of _ _).trans <| if_pos rfl
    have hfy1 : f (of y) = 1 := hoxy ▸ hfx1
    have hfy0 : f (of y) = 0 := (lift.of _ _).trans <| if_neg hxy
    one_ne_zero <| hfy1.symm.trans hfy0

@[simp]
theorem of_ne_zero (x : α) : of x ≠ 0 := by
  intro h
  let f : FreeAbelianGroup α →+ ℤ := lift 1
  have hfx : f (of x) = 1 := lift.of _ _
  have hf0 : f (of x) = 0 := by rw [h, map_zero]
  exact one_ne_zero <| hfx.symm.trans hf0

@[simp]
theorem zero_ne_of (x : α) : 0 ≠ of x := of_ne_zero _ |>.symm

instance [Nonempty α] : Nontrivial (FreeAbelianGroup α) where
  exists_pair_ne := let ⟨x⟩ := ‹Nonempty α›; ⟨0, of x, zero_ne_of _⟩

end

attribute [local instance] QuotientGroup.leftRel

@[elab_as_elim]
protected theorem induction_on {C : FreeAbelianGroup α → Prop} (z : FreeAbelianGroup α) (C0 : C 0)
    (C1 : ∀ x, C <| of x) (Cn : ∀ x, C (of x) → C (-of x)) (Cp : ∀ x y, C x → C y → C (x + y)) :
    C z :=
  Quotient.inductionOn' z fun x ↦
    Quot.inductionOn x fun L ↦
      List.recOn L C0 fun ⟨x, b⟩ _ ih ↦ Bool.recOn b (Cp _ _ (Cn _ (C1 x)) ih) (Cp _ _ (C1 x) ih)

theorem lift.add' {α β} [AddCommGroup β] (a : FreeAbelianGroup α) (f g : α → β) :
    lift (f + g) a = lift f a + lift g a := by
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp only [(lift _).map_zero, zero_add]
  · intro x
    simp only [lift.of, Pi.add_apply]
  · intro x _
    simp only [map_neg, lift.of, Pi.add_apply, neg_add]
  · intro x y hx hy
    simp only [(lift _).map_add, hx, hy, add_add_add_comm]

/-- If `g : FreeAbelianGroup X` and `A` is an abelian group then `liftAddGroupHom g`
is the additive group homomorphism sending a function `X → A` to the term of type `A`
corresponding to the evaluation of the induced map `FreeAbelianGroup X → A` at `g`. -/
@[simps!]  -- Porting note: Changed `simps` to `simps!`.
def liftAddGroupHom {α} (β) [AddCommGroup β] (a : FreeAbelianGroup α) : (α → β) →+ β :=
  AddMonoidHom.mk' (fun f ↦ lift f a) (lift.add' a)

theorem lift_neg' {β} [AddCommGroup β] (f : α → β) : lift (-f) = -lift f :=
  AddMonoidHom.ext fun _ ↦ (liftAddGroupHom _ _ : (α → β) →+ β).map_neg _

section Monad

variable {β : Type u}

instance : Monad FreeAbelianGroup.{u} where
  pure α := of α
  bind x f := lift f x

@[elab_as_elim]
protected theorem induction_on' {C : FreeAbelianGroup α → Prop} (z : FreeAbelianGroup α) (C0 : C 0)
    (C1 : ∀ x, C <| pure x) (Cn : ∀ x, C (pure x) → C (-pure x))
    (Cp : ∀ x y, C x → C y → C (x + y)) : C z :=
  FreeAbelianGroup.induction_on z C0 C1 Cn Cp

@[simp]
theorem map_pure (f : α → β) (x : α) : f <$> (pure x : FreeAbelianGroup α) = pure (f x) :=
  rfl

@[simp]
protected theorem map_zero (f : α → β) : f <$> (0 : FreeAbelianGroup α) = 0 :=
  (lift (of ∘ f)).map_zero

@[simp]
protected theorem map_add (f : α → β) (x y : FreeAbelianGroup α) :
    f <$> (x + y) = f <$> x + f <$> y :=
  (lift _).map_add _ _

@[simp]
protected theorem map_neg (f : α → β) (x : FreeAbelianGroup α) : f <$> (-x) = -f <$> x :=
  map_neg (lift <| of ∘ f) _

@[simp]
protected theorem map_sub (f : α → β) (x y : FreeAbelianGroup α) :
    f <$> (x - y) = f <$> x - f <$> y :=
  map_sub (lift <| of ∘ f) _ _

@[simp]
theorem map_of (f : α → β) (y : α) : f <$> of y = of (f y) :=
  rfl

theorem pure_bind (f : α → FreeAbelianGroup β) (x) : pure x >>= f = f x :=
  lift.of _ _

@[simp]
theorem zero_bind (f : α → FreeAbelianGroup β) : 0 >>= f = 0 :=
  (lift f).map_zero

@[simp]
theorem add_bind (f : α → FreeAbelianGroup β) (x y : FreeAbelianGroup α) :
    x + y >>= f = (x >>= f) + (y >>= f) :=
  (lift _).map_add _ _

@[simp]
theorem neg_bind (f : α → FreeAbelianGroup β) (x : FreeAbelianGroup α) : -x >>= f = -(x >>= f) :=
  map_neg (lift f) _

@[simp]
theorem sub_bind (f : α → FreeAbelianGroup β) (x y : FreeAbelianGroup α) :
    x - y >>= f = (x >>= f) - (y >>= f) :=
  map_sub (lift f) _ _

@[simp]
theorem pure_seq (f : α → β) (x : FreeAbelianGroup α) : pure f <*> x = f <$> x :=
  pure_bind _ _

@[simp]
theorem zero_seq (x : FreeAbelianGroup α) : (0 : FreeAbelianGroup (α → β)) <*> x = 0 :=
  zero_bind _

@[simp]
theorem add_seq (f g : FreeAbelianGroup (α → β)) (x : FreeAbelianGroup α) :
    f + g <*> x = (f <*> x) + (g <*> x) :=
  add_bind _ _ _

@[simp]
theorem neg_seq (f : FreeAbelianGroup (α → β)) (x : FreeAbelianGroup α) : -f <*> x = -(f <*> x) :=
  neg_bind _ _

@[simp]
theorem sub_seq (f g : FreeAbelianGroup (α → β)) (x : FreeAbelianGroup α) :
    f - g <*> x = (f <*> x) - (g <*> x) :=
  sub_bind _ _ _

/-- If `f : FreeAbelianGroup (α → β)`, then `f <*>` is an additive morphism
`FreeAbelianGroup α →+ FreeAbelianGroup β`. -/
def seqAddGroupHom (f : FreeAbelianGroup (α → β)) : FreeAbelianGroup α →+ FreeAbelianGroup β :=
  AddMonoidHom.mk' (f <*> ·) fun x y ↦
    show lift (· <$> (x + y)) _ = _ by
      simp only [FreeAbelianGroup.map_add]
      exact lift.add' f _ _

@[simp]
theorem seq_zero (f : FreeAbelianGroup (α → β)) : f <*> 0 = 0 :=
  (seqAddGroupHom f).map_zero

@[simp]
theorem seq_add (f : FreeAbelianGroup (α → β)) (x y : FreeAbelianGroup α) :
    f <*> x + y = (f <*> x) + (f <*> y) :=
  (seqAddGroupHom f).map_add x y

@[simp]
theorem seq_neg (f : FreeAbelianGroup (α → β)) (x : FreeAbelianGroup α) : f <*> -x = -(f <*> x) :=
  (seqAddGroupHom f).map_neg x

@[simp]
theorem seq_sub (f : FreeAbelianGroup (α → β)) (x y : FreeAbelianGroup α) :
    f <*> x - y = (f <*> x) - (f <*> y) :=
  (seqAddGroupHom f).map_sub x y

instance : LawfulMonad FreeAbelianGroup.{u} := LawfulMonad.mk'
  (id_map := fun x ↦ FreeAbelianGroup.induction_on' x (FreeAbelianGroup.map_zero id) (map_pure id)
    (fun x ih ↦ by rw [FreeAbelianGroup.map_neg, ih])
    fun x y ihx ihy ↦ by rw [FreeAbelianGroup.map_add, ihx, ihy])
  (pure_bind := fun x f ↦ pure_bind f x)
  (bind_assoc := fun x f g ↦ FreeAbelianGroup.induction_on' x (by iterate 3 rw [zero_bind])
    (fun x ↦ by iterate 2 rw [pure_bind]) (fun x ih ↦ by iterate 3 rw [neg_bind] <;> try rw [ih])
    fun x y ihx ihy ↦ by iterate 3 rw [add_bind] <;> try rw [ihx, ihy])

instance : CommApplicative FreeAbelianGroup.{u} where
  commutative_prod x y := by
    refine FreeAbelianGroup.induction_on' x ?_ ?_ ?_ ?_
    · rw [FreeAbelianGroup.map_zero, zero_seq, seq_zero]
    · intro p
      rw [map_pure, pure_seq]
      exact FreeAbelianGroup.induction_on' y
        (by rw [FreeAbelianGroup.map_zero, FreeAbelianGroup.map_zero, zero_seq])
        (fun q ↦ by rw [map_pure, map_pure, pure_seq, map_pure])
        (fun q ih ↦ by rw [FreeAbelianGroup.map_neg, FreeAbelianGroup.map_neg, neg_seq, ih])
        fun y₁ y₂ ih1 ih2 ↦ by
          rw [FreeAbelianGroup.map_add, FreeAbelianGroup.map_add, add_seq, ih1, ih2]
    · intro p ih
      rw [FreeAbelianGroup.map_neg, neg_seq, seq_neg, ih]
    · intro x₁ x₂ ih1 ih2
      rw [FreeAbelianGroup.map_add, add_seq, seq_add, ih1, ih2]

end Monad

universe w

variable {β : Type v} {γ : Type w}

/-- The additive group homomorphism `FreeAbelianGroup α →+ FreeAbelianGroup β` induced from a
  map `α → β`. -/
def map (f : α → β) : FreeAbelianGroup α →+ FreeAbelianGroup β :=
  lift (of ∘ f)

theorem lift_comp {α} {β} {γ} [AddCommGroup γ] (f : α → β) (g : β → γ) (x : FreeAbelianGroup α) :
    lift (g ∘ f) x = lift g (map f x) := by
  -- Porting note: Added motive.
  apply FreeAbelianGroup.induction_on (C := fun x ↦ lift (g ∘ f) x = lift g (map f x)) x
  · simp only [map_zero]
  · intro _
    simp only [lift.of, map, Function.comp]
  · intro _ h
    simp only [h, AddMonoidHom.map_neg]
  · intro _ _ h₁ h₂
    simp only [h₁, h₂, AddMonoidHom.map_add]

theorem map_id : map id = AddMonoidHom.id (FreeAbelianGroup α) :=
  Eq.symm <|
    lift.ext _ _ fun _ ↦ lift.unique of (AddMonoidHom.id _) fun _ ↦ AddMonoidHom.id_apply _ _

theorem map_id_apply (x : FreeAbelianGroup α) : map id x = x := by
  rw [map_id]
  rfl

theorem map_comp {f : α → β} {g : β → γ} : map (g ∘ f) = (map g).comp (map f) :=
  Eq.symm <| lift.ext _ _ fun _ ↦ by simp [map]

theorem map_comp_apply {f : α → β} {g : β → γ} (x : FreeAbelianGroup α) :
    map (g ∘ f) x = (map g) ((map f) x) := by
  rw [map_comp]
  rfl

-- version of map_of which uses `map`
@[simp]
theorem map_of_apply {f : α → β} (a : α) : map f (of a) = of (f a) :=
  rfl

variable (α)

section Mul

variable [Mul α]

instance mul : Mul (FreeAbelianGroup α) :=
  ⟨fun x ↦ lift fun x₂ ↦ lift (fun x₁ ↦ of (x₁ * x₂)) x⟩

variable {α}

theorem mul_def (x y : FreeAbelianGroup α) :
    x * y = lift (fun x₂ ↦ lift (fun x₁ ↦ of (x₁ * x₂)) x) y :=
  rfl

@[simp]
theorem of_mul_of (x y : α) : of x * of y = of (x * y) := by
  rw [mul_def, lift.of, lift.of]

theorem of_mul (x y : α) : of (x * y) = of x * of y :=
  Eq.symm <| of_mul_of x y

instance distrib : Distrib (FreeAbelianGroup α) :=
  { FreeAbelianGroup.mul α, FreeAbelianGroup.addCommGroup α with
    left_distrib := fun _ _ _ ↦ (lift _).map_add _ _
    right_distrib := fun x y z ↦ by simp only [(· * ·), Mul.mul, map_add, ← Pi.add_def, lift.add'] }

instance nonUnitalNonAssocRing : NonUnitalNonAssocRing (FreeAbelianGroup α) :=
  { FreeAbelianGroup.distrib,
    FreeAbelianGroup.addCommGroup _ with
    zero_mul := fun a ↦ by
      have h : 0 * a + 0 * a = 0 * a := by simp [← add_mul]
      simpa using h
    mul_zero := fun _ ↦ rfl }

end Mul

instance one [One α] : One (FreeAbelianGroup α) :=
  ⟨of 1⟩

instance nonUnitalRing [Semigroup α] : NonUnitalRing (FreeAbelianGroup α) :=
  { FreeAbelianGroup.nonUnitalNonAssocRing with
    mul_assoc := fun x y z ↦ by
      refine FreeAbelianGroup.induction_on z (by simp only [mul_zero])
          (fun L3 ↦ ?_) (fun L3 ih ↦ ?_) fun z₁ z₂ ih₁ ih₂ ↦ ?_
      · refine FreeAbelianGroup.induction_on y (by simp only [mul_zero, zero_mul])
            (fun L2 ↦ ?_) (fun L2 ih ↦ ?_) fun y₁ y₂ ih₁ ih₂ ↦ ?_
        · refine FreeAbelianGroup.induction_on x (by simp only [zero_mul])
              (fun L1 ↦ ?_) (fun L1 ih ↦ ?_) fun x₁ x₂ ih₁ ih₂ ↦ ?_
          · rw [of_mul_of, of_mul_of, of_mul_of, of_mul_of, mul_assoc]
          · rw [neg_mul, neg_mul, neg_mul, ih]
          · rw [add_mul, add_mul, add_mul, ih₁, ih₂]
        · rw [neg_mul, mul_neg, mul_neg, neg_mul, ih]
        · rw [add_mul, mul_add, mul_add, add_mul, ih₁, ih₂]
      · rw [mul_neg, mul_neg, mul_neg, ih]
      · rw [mul_add, mul_add, mul_add, ih₁, ih₂] }

section Monoid

variable {R : Type*} [Monoid α] [Ring R]

instance ring : Ring (FreeAbelianGroup α) :=
  { FreeAbelianGroup.nonUnitalRing _,
    FreeAbelianGroup.one _ with
    mul_one := fun x ↦ by
      dsimp only [(· * ·), Mul.mul, OfNat.ofNat, One.one]
      rw [lift.of]
      refine FreeAbelianGroup.induction_on x rfl (fun L ↦ ?_) (fun L ih ↦ ?_) fun x1 x2 ih1 ih2 ↦ ?_
      · rw [lift.of]
        congr 1
        exact mul_one L
      · rw [map_neg, ih]
      · rw [map_add, ih1, ih2]
    one_mul := fun x ↦ by
      dsimp only [(· * ·), Mul.mul, OfNat.ofNat, One.one]
      refine FreeAbelianGroup.induction_on x rfl ?_ ?_ ?_
      · intro L
        rw [lift.of, lift.of]
        congr 1
        exact one_mul L
      · intro L ih
        rw [map_neg, ih]
      · intro x1 x2 ih1 ih2
        rw [map_add, ih1, ih2] }

variable {α}

/-- `FreeAbelianGroup.of` is a `MonoidHom` when `α` is a `Monoid`. -/
def ofMulHom : α →* FreeAbelianGroup α where
  toFun := of
  map_one' := rfl
  map_mul' := of_mul

@[simp]
theorem ofMulHom_coe : (ofMulHom : α → FreeAbelianGroup α) = of :=
  rfl

/-- If `f` preserves multiplication, then so does `lift f`. -/
def liftMonoid : (α →* R) ≃ (FreeAbelianGroup α →+* R) where
  toFun f := { lift f with
    toFun := lift f
    map_one' := (lift.of f _).trans f.map_one
    map_mul' := fun x y ↦ by
      simp only
      refine FreeAbelianGroup.induction_on y
          (by simp only [mul_zero, map_zero]) (fun L2 ↦ ?_) (fun L2 ih ↦ ?_) ?_
      · refine FreeAbelianGroup.induction_on x
            (by simp only [zero_mul, map_zero]) (fun L1 ↦ ?_) (fun L1 ih ↦ ?_) ?_
        · simp_rw [of_mul_of, lift.of]
          exact f.map_mul _ _
        · simp_rw [neg_mul, map_neg, neg_mul]
          exact congr_arg Neg.neg ih
        · intro x1 x2 ih1 ih2
          simp only [add_mul, map_add, ih1, ih2]
      · rw [mul_neg, map_neg, map_neg, mul_neg, ih]
      · intro y1 y2 ih1 ih2
        rw [mul_add, map_add, map_add, mul_add, ih1, ih2] }
  invFun F := MonoidHom.comp (↑F) ofMulHom
  left_inv f := MonoidHom.ext <| by
    simp only [RingHom.coe_monoidHom_mk, MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk,
      ofMulHom_coe, Function.comp_apply, lift.of, forall_const]
  right_inv F := RingHom.coe_addMonoidHom_injective <| by
    simp only
    rw [← lift.apply_symm_apply (↑F : FreeAbelianGroup α →+ R)]
    rfl

@[simp]
theorem liftMonoid_coe_addMonoidHom (f : α →* R) : ↑(liftMonoid f) = lift f :=
  rfl

@[simp]
theorem liftMonoid_coe (f : α →* R) : ⇑(liftMonoid f) = lift f :=
  rfl

@[simp]
-- Porting note: Added a type to `↑f`.
theorem liftMonoid_symm_coe (f : FreeAbelianGroup α →+* R) :
    ⇑(liftMonoid.symm f) = lift.symm (↑f : FreeAbelianGroup α →+ R) :=
  rfl

theorem one_def : (1 : FreeAbelianGroup α) = of 1 :=
  rfl

theorem of_one : (of 1 : FreeAbelianGroup α) = 1 :=
  rfl

end Monoid

instance [CommMonoid α] : CommRing (FreeAbelianGroup α) :=
  { FreeAbelianGroup.ring α with
    mul_comm := fun x y ↦ by
      refine FreeAbelianGroup.induction_on x (zero_mul y) ?_ ?_ ?_
      · intro s
        refine FreeAbelianGroup.induction_on y (zero_mul _).symm ?_ ?_ ?_
        · intro t
          dsimp only [(· * ·), Mul.mul]
          iterate 4 rw [lift.of]
          congr 1
          exact mul_comm _ _
        · intro t ih
          rw [mul_neg, ih, neg_mul_eq_neg_mul]
        · intro y1 y2 ih1 ih2
          rw [mul_add, add_mul, ih1, ih2]
      · intro s ih
        rw [neg_mul, ih, neg_mul_eq_mul_neg]
      · intro x1 x2 ih1 ih2
        rw [add_mul, mul_add, ih1, ih2] }

instance pemptyUnique : Unique (FreeAbelianGroup PEmpty) where
  default := 0
  uniq x := FreeAbelianGroup.induction_on x rfl (PEmpty.elim ·) (PEmpty.elim ·) (by
    rintro - - rfl rfl
    rfl)

/-- The free abelian group on a type with one term is isomorphic to `ℤ`. -/
def punitEquiv (T : Type*) [Unique T] : FreeAbelianGroup T ≃+ ℤ where
  toFun := FreeAbelianGroup.lift fun _ ↦ (1 : ℤ)
  invFun n := n • of Inhabited.default
  left_inv z := FreeAbelianGroup.induction_on z
    (by simp only [zero_smul, AddMonoidHom.map_zero])
    (Unique.forall_iff.2 <| by simp only [one_smul, lift.of]) (Unique.forall_iff.2 <| by simp)
    fun x y hx hy ↦ by
      simp only [AddMonoidHom.map_add, add_smul] at *
      rw [hx, hy]
  right_inv n := by
    rw [AddMonoidHom.map_zsmul, lift.of]
    exact zsmul_int_one n
  map_add' := AddMonoidHom.map_add _

/-- Isomorphic types have isomorphic free abelian groups. -/
def equivOfEquiv {α β : Type*} (f : α ≃ β) : FreeAbelianGroup α ≃+ FreeAbelianGroup β where
  toFun := map f
  invFun := map f.symm
  left_inv := by
    intro x
    rw [← map_comp_apply, Equiv.symm_comp_self, map_id]
    rfl
  right_inv := by
    intro x
    rw [← map_comp_apply, Equiv.self_comp_symm, map_id]
    rfl
  map_add' := AddMonoidHom.map_add _

end FreeAbelianGroup
