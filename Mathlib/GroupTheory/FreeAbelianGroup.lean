/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Group.Pi
import Mathlib.GroupTheory.FreeGroup
import Mathlib.GroupTheory.Abelianization
import Mathlib.Algebra.Module.Basic

#align_import group_theory.free_abelian_group from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

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
#align free_abelian_group FreeAbelianGroup

-- FIXME: this is super broken, because the functions have type `Additive .. → ..`
-- instead of `FreeAbelianGroup α → ..` and those are not defeq!
instance FreeAbelianGroup.addCommGroup : AddCommGroup (FreeAbelianGroup α) :=
  @Additive.addCommGroup _ <| Abelianization.commGroup _

instance : Inhabited (FreeAbelianGroup α) :=
  ⟨0⟩

variable {α}

namespace FreeAbelianGroup

/-- The canonical map from `α` to `FreeAbelianGroup α`. -/
def of (x : α) : FreeAbelianGroup α :=
  Abelianization.of <| FreeGroup.of x
#align free_abelian_group.of FreeAbelianGroup.of

/-- The map `FreeAbelianGroup α →+ A` induced by a map of types `α → A`. -/
def lift {β : Type v} [AddCommGroup β] : (α → β) ≃ (FreeAbelianGroup α →+ β) :=
  (@FreeGroup.lift _ (Multiplicative β) _).trans <|
    (@Abelianization.lift _ _ (Multiplicative β) _).trans MonoidHom.toAdditive
#align free_abelian_group.lift FreeAbelianGroup.lift

namespace lift

variable {β : Type v} [AddCommGroup β] (f : α → β)

open FreeAbelianGroup

-- Porting note: needed to add `(β := Multiplicative β)` and `using 1`.
@[simp]
protected theorem of (x : α) : lift f (of x) = f x := by
  convert Abelianization.lift.of
     (FreeGroup.lift f (β := Multiplicative β)) (FreeGroup.of x) using 1
  exact (FreeGroup.lift.of (β := Multiplicative β)).symm
  -- 🎉 no goals
#align free_abelian_group.lift.of FreeAbelianGroup.lift.of

protected theorem unique (g : FreeAbelianGroup α →+ β) (hg : ∀ x, g (of x) = f x) {x} :
    g x = lift f x :=
  FunLike.congr_fun (lift.symm_apply_eq.mp (funext hg : g ∘ of = f)) _
#align free_abelian_group.lift.unique FreeAbelianGroup.lift.unique

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
protected theorem ext (g h : FreeAbelianGroup α →+ β) (H : ∀ x, g (of x) = h (of x)) : g = h :=
  lift.symm.injective <| funext H
#align free_abelian_group.lift.ext FreeAbelianGroup.lift.ext

theorem map_hom {α β γ} [AddCommGroup β] [AddCommGroup γ] (a : FreeAbelianGroup α) (f : α → β)
    (g : β →+ γ) : g (lift f a) = lift (g ∘ f) a := by
  show (g.comp (lift f)) a = lift (g ∘ f) a
  -- ⊢ ↑(AddMonoidHom.comp g (↑lift f)) a = ↑(↑lift (↑g ∘ f)) a
  apply lift.unique
  -- ⊢ ∀ (x : α), ↑(AddMonoidHom.comp g (↑lift f)) (of x) = (↑g ∘ f) x
  intro a
  -- ⊢ ↑(AddMonoidHom.comp g (↑lift f)) (of a) = (↑g ∘ f) a
  show g ((lift f) (of a)) = g (f a)
  -- ⊢ ↑g (↑(↑lift f) (of a)) = ↑g (f a)
  simp only [(· ∘ ·), lift.of]
  -- 🎉 no goals
#align free_abelian_group.lift.map_hom FreeAbelianGroup.lift.map_hom

end lift

section

open Classical

theorem of_injective : Function.Injective (of : α → FreeAbelianGroup α) :=
  fun x y hoxy ↦ Classical.by_contradiction fun hxy : x ≠ y ↦
    let f : FreeAbelianGroup α →+ ℤ := lift fun z ↦ if x = z then (1 : ℤ) else 0
    have hfx1 : f (of x) = 1 := (lift.of _ _).trans <| if_pos rfl
    have hfy1 : f (of y) = 1 := hoxy ▸ hfx1
    have hfy0 : f (of y) = 0 := (lift.of _ _).trans <| if_neg hxy
    one_ne_zero <| hfy1.symm.trans hfy0
#align free_abelian_group.of_injective FreeAbelianGroup.of_injective

end

attribute [local instance] QuotientGroup.leftRel

@[elab_as_elim]
protected theorem induction_on {C : FreeAbelianGroup α → Prop} (z : FreeAbelianGroup α) (C0 : C 0)
    (C1 : ∀ x, C <| of x) (Cn : ∀ x, C (of x) → C (-of x)) (Cp : ∀ x y, C x → C y → C (x + y)) :
    C z :=
  Quotient.inductionOn' z fun x ↦
    Quot.inductionOn x fun L ↦
      List.recOn L C0 fun ⟨x, b⟩ _ ih ↦ Bool.recOn b (Cp _ _ (Cn _ (C1 x)) ih) (Cp _ _ (C1 x) ih)
#align free_abelian_group.induction_on FreeAbelianGroup.induction_on

theorem lift.add' {α β} [AddCommGroup β] (a : FreeAbelianGroup α) (f g : α → β) :
    lift (f + g) a = lift f a + lift g a := by
  refine' FreeAbelianGroup.induction_on a _ _ _ _
  · simp only [(lift _).map_zero, zero_add]
    -- 🎉 no goals
  · intro x
    -- ⊢ ↑(↑lift (f + g)) (of x) = ↑(↑lift f) (of x) + ↑(↑lift g) (of x)
    simp only [lift.of, Pi.add_apply]
    -- 🎉 no goals
  · intro x _
    -- ⊢ ↑(↑lift (f + g)) (-of x) = ↑(↑lift f) (-of x) + ↑(↑lift g) (-of x)
    simp only [map_neg, lift.of, Pi.add_apply, neg_add]
    -- 🎉 no goals
  · intro x y hx hy
    -- ⊢ ↑(↑lift (f + g)) (x + y) = ↑(↑lift f) (x + y) + ↑(↑lift g) (x + y)
    simp only [(lift _).map_add, hx, hy, add_add_add_comm]
    -- 🎉 no goals
#align free_abelian_group.lift.add' FreeAbelianGroup.lift.add'

/-- If `g : FreeAbelianGroup X` and `A` is an abelian group then `liftAddGroupHom g`
is the additive group homomorphism sending a function `X → A` to the term of type `A`
corresponding to the evaluation of the induced map `FreeAbelianGroup X → A` at `g`. -/
@[simps!]  -- Porting note: Changed `simps` to `simps!`.
def liftAddGroupHom {α} (β) [AddCommGroup β] (a : FreeAbelianGroup α) : (α → β) →+ β :=
  AddMonoidHom.mk' (fun f ↦ lift f a) (lift.add' a)
#align free_abelian_group.lift_add_group_hom FreeAbelianGroup.liftAddGroupHom

theorem lift_neg' {β} [AddCommGroup β] (f : α → β) : lift (-f) = -lift f :=
  AddMonoidHom.ext fun _ ↦ (liftAddGroupHom _ _ : (α → β) →+ β).map_neg _
#align free_abelian_group.lift_neg' FreeAbelianGroup.lift_neg'

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
#align free_abelian_group.induction_on' FreeAbelianGroup.induction_on'

@[simp, nolint simpNF] -- Porting note: dsimp can not prove this
theorem map_pure (f : α → β) (x : α) : f <$> (pure x : FreeAbelianGroup α) = pure (f x) :=
  rfl
#align free_abelian_group.map_pure FreeAbelianGroup.map_pure

@[simp]
protected theorem map_zero (f : α → β) : f <$> (0 : FreeAbelianGroup α) = 0 :=
  (lift (of ∘ f)).map_zero
#align free_abelian_group.map_zero FreeAbelianGroup.map_zero

@[simp]
protected theorem map_add (f : α → β) (x y : FreeAbelianGroup α) :
    f <$> (x + y) = f <$> x + f <$> y :=
  (lift _).map_add _ _
#align free_abelian_group.map_add FreeAbelianGroup.map_add

@[simp]
protected theorem map_neg (f : α → β) (x : FreeAbelianGroup α) : f <$> (-x) = -f <$> x :=
  map_neg (lift <| of ∘ f) _
#align free_abelian_group.map_neg FreeAbelianGroup.map_neg

@[simp]
protected theorem map_sub (f : α → β) (x y : FreeAbelianGroup α) :
    f <$> (x - y) = f <$> x - f <$> y :=
  map_sub (lift <| of ∘ f) _ _
#align free_abelian_group.map_sub FreeAbelianGroup.map_sub

@[simp]
theorem map_of (f : α → β) (y : α) : f <$> of y = of (f y) :=
  rfl
#align free_abelian_group.map_of FreeAbelianGroup.map_of

-- @[simp] -- Porting note: simp can prove this
theorem pure_bind (f : α → FreeAbelianGroup β) (x) : pure x >>= f = f x :=
  lift.of _ _
#align free_abelian_group.pure_bind FreeAbelianGroup.pure_bind

@[simp]
theorem zero_bind (f : α → FreeAbelianGroup β) : 0 >>= f = 0 :=
  (lift f).map_zero
#align free_abelian_group.zero_bind FreeAbelianGroup.zero_bind

@[simp]
theorem add_bind (f : α → FreeAbelianGroup β) (x y : FreeAbelianGroup α) :
    x + y >>= f = (x >>= f) + (y >>= f) :=
  (lift _).map_add _ _
#align free_abelian_group.add_bind FreeAbelianGroup.add_bind

@[simp]
theorem neg_bind (f : α → FreeAbelianGroup β) (x : FreeAbelianGroup α) : -x >>= f = -(x >>= f) :=
  map_neg (lift f) _
#align free_abelian_group.neg_bind FreeAbelianGroup.neg_bind

@[simp]
theorem sub_bind (f : α → FreeAbelianGroup β) (x y : FreeAbelianGroup α) :
    x - y >>= f = (x >>= f) - (y >>= f) :=
  map_sub (lift f) _ _
#align free_abelian_group.sub_bind FreeAbelianGroup.sub_bind

@[simp]
theorem pure_seq (f : α → β) (x : FreeAbelianGroup α) : pure f <*> x = f <$> x :=
  pure_bind _ _
#align free_abelian_group.pure_seq FreeAbelianGroup.pure_seq

@[simp]
theorem zero_seq (x : FreeAbelianGroup α) : (0 : FreeAbelianGroup (α → β)) <*> x = 0 :=
  zero_bind _
#align free_abelian_group.zero_seq FreeAbelianGroup.zero_seq

@[simp]
theorem add_seq (f g : FreeAbelianGroup (α → β)) (x : FreeAbelianGroup α) :
    f + g <*> x = (f <*> x) + (g <*> x) :=
  add_bind _ _ _
#align free_abelian_group.add_seq FreeAbelianGroup.add_seq

@[simp]
theorem neg_seq (f : FreeAbelianGroup (α → β)) (x : FreeAbelianGroup α) : -f <*> x = -(f <*> x) :=
  neg_bind _ _
#align free_abelian_group.neg_seq FreeAbelianGroup.neg_seq

@[simp]
theorem sub_seq (f g : FreeAbelianGroup (α → β)) (x : FreeAbelianGroup α) :
    f - g <*> x = (f <*> x) - (g <*> x) :=
  sub_bind _ _ _
#align free_abelian_group.sub_seq FreeAbelianGroup.sub_seq

/-- If `f : FreeAbelianGroup (α → β)`, then `f <*>` is an additive morphism
`FreeAbelianGroup α →+ FreeAbelianGroup β`. -/
def seqAddGroupHom (f : FreeAbelianGroup (α → β)) : FreeAbelianGroup α →+ FreeAbelianGroup β :=
  AddMonoidHom.mk' ((· <*> ·) f) fun x y ↦
    show lift (· <$> (x + y)) _ = _ by
      simp only [FreeAbelianGroup.map_add]
      -- ⊢ ↑(↑lift fun x_1 => x_1 <$> x + x_1 <$> y) f = (Seq.seq f fun x_1 => x) + Seq …
      exact lift.add' f _ _
      -- 🎉 no goals
#align free_abelian_group.seq_add_group_hom FreeAbelianGroup.seqAddGroupHom

@[simp]
theorem seq_zero (f : FreeAbelianGroup (α → β)) : f <*> 0 = 0 :=
  (seqAddGroupHom f).map_zero
#align free_abelian_group.seq_zero FreeAbelianGroup.seq_zero

@[simp]
theorem seq_add (f : FreeAbelianGroup (α → β)) (x y : FreeAbelianGroup α) :
    f <*> x + y = (f <*> x) + (f <*> y) :=
  (seqAddGroupHom f).map_add x y
#align free_abelian_group.seq_add FreeAbelianGroup.seq_add

@[simp]
theorem seq_neg (f : FreeAbelianGroup (α → β)) (x : FreeAbelianGroup α) : f <*> -x = -(f <*> x) :=
  (seqAddGroupHom f).map_neg x
#align free_abelian_group.seq_neg FreeAbelianGroup.seq_neg

@[simp]
theorem seq_sub (f : FreeAbelianGroup (α → β)) (x y : FreeAbelianGroup α) :
    f <*> x - y = (f <*> x) - (f <*> y) :=
  (seqAddGroupHom f).map_sub x y
#align free_abelian_group.seq_sub FreeAbelianGroup.seq_sub

instance : LawfulMonad FreeAbelianGroup.{u} := LawfulMonad.mk'
  (id_map := fun x ↦ FreeAbelianGroup.induction_on' x (FreeAbelianGroup.map_zero id) (map_pure id)
    (fun x ih ↦ by rw [FreeAbelianGroup.map_neg, ih])
                   -- 🎉 no goals
    fun x y ihx ihy ↦ by rw [FreeAbelianGroup.map_add, ihx, ihy])
                         -- 🎉 no goals
  (pure_bind := fun x f ↦ pure_bind f x)
  (bind_assoc := fun x f g ↦ FreeAbelianGroup.induction_on' x (by iterate 3 rw [zero_bind])
                                                                  -- 🎉 no goals
    (fun x ↦ by iterate 2 rw [pure_bind]) (fun x ih ↦ by iterate 3 rw [neg_bind] <;> try rw [ih])
                -- 🎉 no goals
                                                         -- 🎉 no goals
    fun x y ihx ihy ↦ by iterate 3 rw [add_bind] <;> try rw [ihx, ihy])
                         -- 🎉 no goals

instance : CommApplicative FreeAbelianGroup.{u} where
  commutative_prod x y := by
    refine' FreeAbelianGroup.induction_on' x _ _ _ _
    · rw [FreeAbelianGroup.map_zero, zero_seq, seq_zero]
      -- 🎉 no goals
    · intro p
      -- ⊢ (Seq.seq (Prod.mk <$> pure p) fun x => y) = Seq.seq ((fun b a => (a, b)) <$> …
      rw [map_pure, pure_seq]
      -- ⊢ Prod.mk p <$> y = Seq.seq ((fun b a => (a, b)) <$> y) fun x => pure p
      exact FreeAbelianGroup.induction_on' y
        (by rw [FreeAbelianGroup.map_zero, FreeAbelianGroup.map_zero, zero_seq])
        (fun q ↦ by rw [map_pure, map_pure, pure_seq, map_pure])
        (fun q ih ↦ by rw [FreeAbelianGroup.map_neg, FreeAbelianGroup.map_neg, neg_seq, ih])
        fun y₁ y₂ ih1 ih2 ↦ by
          rw [FreeAbelianGroup.map_add, FreeAbelianGroup.map_add, add_seq, ih1, ih2]
    · intro p ih
      -- ⊢ (Seq.seq (Prod.mk <$> (-pure p)) fun x => y) = Seq.seq ((fun b a => (a, b))  …
      rw [FreeAbelianGroup.map_neg, neg_seq, seq_neg, ih]
      -- 🎉 no goals
    · intro x₁ x₂ ih1 ih2
      -- ⊢ (Seq.seq (Prod.mk <$> (x₁ + x₂)) fun x => y) = Seq.seq ((fun b a => (a, b))  …
      rw [FreeAbelianGroup.map_add, add_seq, seq_add, ih1, ih2]
      -- 🎉 no goals

end Monad

universe w

variable {β : Type v} {γ : Type w}

/-- The additive group homomorphism `FreeAbelianGroup α →+ FreeAbelianGroup β` induced from a
  map `α → β`. -/
def map (f : α → β) : FreeAbelianGroup α →+ FreeAbelianGroup β :=
  lift (of ∘ f)
#align free_abelian_group.map FreeAbelianGroup.map

theorem lift_comp {α} {β} {γ} [AddCommGroup γ] (f : α → β) (g : β → γ) (x : FreeAbelianGroup α) :
    lift (g ∘ f) x = lift g (map f x) := by
  -- Porting note: Added motive.
  apply FreeAbelianGroup.induction_on (C := fun x ↦ lift (g ∘ f) x = lift g (map f x)) x
  · simp only [map_zero]
    -- 🎉 no goals
  · intro _
    -- ⊢ ↑(↑lift (g ∘ f)) (of x✝) = ↑(↑lift g) (↑(map f) (of x✝))
    simp only [lift.of, map, Function.comp]
    -- 🎉 no goals
  · intro _ h
    -- ⊢ ↑(↑lift (g ∘ f)) (-of x✝) = ↑(↑lift g) (↑(map f) (-of x✝))
    simp only [h, AddMonoidHom.map_neg]
    -- 🎉 no goals
  · intro _ _ h₁ h₂
    -- ⊢ ↑(↑lift (g ∘ f)) (x✝ + y✝) = ↑(↑lift g) (↑(map f) (x✝ + y✝))
    simp only [h₁, h₂, AddMonoidHom.map_add]
    -- 🎉 no goals
#align free_abelian_group.lift_comp FreeAbelianGroup.lift_comp

theorem map_id : map id = AddMonoidHom.id (FreeAbelianGroup α) :=
  Eq.symm <|
    lift.ext _ _ fun _ ↦ lift.unique of (AddMonoidHom.id _) fun _ ↦ AddMonoidHom.id_apply _ _
#align free_abelian_group.map_id FreeAbelianGroup.map_id

theorem map_id_apply (x : FreeAbelianGroup α) : map id x = x := by
  rw [map_id]
  -- ⊢ ↑(AddMonoidHom.id (FreeAbelianGroup α)) x = x
  rfl
  -- 🎉 no goals
#align free_abelian_group.map_id_apply FreeAbelianGroup.map_id_apply

theorem map_comp {f : α → β} {g : β → γ} : map (g ∘ f) = (map g).comp (map f) :=
  Eq.symm <| lift.ext _ _ fun _ ↦ by simp [map]
                                     -- 🎉 no goals
#align free_abelian_group.map_comp FreeAbelianGroup.map_comp

theorem map_comp_apply {f : α → β} {g : β → γ} (x : FreeAbelianGroup α) :
    map (g ∘ f) x = (map g) ((map f) x) := by
  rw [map_comp]
  -- ⊢ ↑(AddMonoidHom.comp (map g) (map f)) x = ↑(map g) (↑(map f) x)
  rfl
  -- 🎉 no goals
#align free_abelian_group.map_comp_apply FreeAbelianGroup.map_comp_apply

-- version of map_of which uses `map`
@[simp]
theorem map_of_apply {f : α → β} (a : α) : map f (of a) = of (f a) :=
  rfl
#align free_abelian_group.map_of_apply FreeAbelianGroup.map_of_apply

variable (α)

section Mul

variable [Mul α]

instance mul : Mul (FreeAbelianGroup α) :=
  ⟨fun x ↦ lift fun x₂ ↦ lift (fun x₁ ↦ of (x₁ * x₂)) x⟩

variable {α}

theorem mul_def (x y : FreeAbelianGroup α) :
    x * y = lift (fun x₂ ↦ lift (fun x₁ ↦ of (x₁ * x₂)) x) y :=
  rfl
#align free_abelian_group.mul_def FreeAbelianGroup.mul_def

@[simp]
theorem of_mul_of (x y : α) : of x * of y = of (x * y) := by
  rw [mul_def, lift.of, lift.of]
  -- 🎉 no goals
#align free_abelian_group.of_mul_of FreeAbelianGroup.of_mul_of

theorem of_mul (x y : α) : of (x * y) = of x * of y :=
  Eq.symm <| of_mul_of x y
#align free_abelian_group.of_mul FreeAbelianGroup.of_mul

instance distrib : Distrib (FreeAbelianGroup α) :=
  { FreeAbelianGroup.mul α, FreeAbelianGroup.addCommGroup α with
    left_distrib := fun x y z ↦ (lift _).map_add _ _
    right_distrib := fun x y z ↦ by simp only [(· * ·), Mul.mul, map_add, ← Pi.add_def, lift.add'] }
                                    -- 🎉 no goals

instance nonUnitalNonAssocRing : NonUnitalNonAssocRing (FreeAbelianGroup α) :=
  { FreeAbelianGroup.distrib,
    FreeAbelianGroup.addCommGroup _ with
    zero_mul := fun a ↦ by
      have h : 0 * a + 0 * a = 0 * a := by simp [← add_mul]
      -- ⊢ 0 * a = 0
      simpa using h
      -- 🎉 no goals
    mul_zero := fun _ ↦ rfl }

end Mul

instance one [One α] : One (FreeAbelianGroup α) :=
  ⟨of 1⟩

instance nonUnitalRing [Semigroup α] : NonUnitalRing (FreeAbelianGroup α) :=
  { FreeAbelianGroup.nonUnitalNonAssocRing with
    mul := (· * ·)
    mul_assoc := fun x y z ↦ by
      refine' FreeAbelianGroup.induction_on z (by simp only [mul_zero])
          (fun L3 ↦ _) (fun L3 ih ↦ _) fun z₁ z₂ ih₁ ih₂ ↦ _
      · refine' FreeAbelianGroup.induction_on y (by simp only [mul_zero, zero_mul])
            (fun L2 ↦ _) (fun L2 ih ↦ _) fun y₁ y₂ ih₁ ih₂ ↦ _
        · refine' FreeAbelianGroup.induction_on x (by simp only [zero_mul])
              (fun L1 ↦ _) (fun L1 ih ↦ _) fun x₁ x₂ ih₁ ih₂ ↦ _
          · rw [of_mul_of, of_mul_of, of_mul_of, of_mul_of, mul_assoc]
            -- 🎉 no goals
          · rw [neg_mul, neg_mul, neg_mul, ih]
            -- 🎉 no goals
          · rw [add_mul, add_mul, add_mul, ih₁, ih₂]
            -- 🎉 no goals
        · rw [neg_mul, mul_neg, mul_neg, neg_mul, ih]
          -- 🎉 no goals
        · rw [add_mul, mul_add, mul_add, add_mul, ih₁, ih₂]
          -- 🎉 no goals
      · rw [mul_neg, mul_neg, mul_neg, ih]
        -- 🎉 no goals
      · rw [mul_add, mul_add, mul_add, ih₁, ih₂] }
        -- 🎉 no goals

section Monoid

variable {R : Type*} [Monoid α] [Ring R]

instance ring : Ring (FreeAbelianGroup α) :=
  { FreeAbelianGroup.nonUnitalRing _,
    FreeAbelianGroup.one _ with
    mul := (· * ·)
    mul_one := fun x ↦ by
      dsimp only [(· * ·), Mul.mul, OfNat.ofNat, One.one]
      -- ⊢ ↑(↑lift fun x₂ => ↑(↑lift fun x₁ => of (Mul.mul x₁ x₂)) x) (of One.one) = x
      rw [lift.of]
      -- ⊢ ↑(↑lift fun x₁ => of (Mul.mul x₁ One.one)) x = x
      refine' FreeAbelianGroup.induction_on x rfl (fun L ↦ _) (fun L ih ↦ _) fun x1 x2 ih1 ih2 ↦ _
      · erw [lift.of]
        -- ⊢ of (Mul.mul L One.one) = of L
        congr 1
        -- ⊢ Mul.mul L One.one = L
        exact mul_one L
      -- ⊢ ↑(↑lift fun x₂ => ↑(↑lift fun x₁ => of (Mul.mul x₁ x₂)) (of One.one)) x = x
        -- 🎉 no goals
      · rw [map_neg, ih]
        -- ⊢ ↑(↑lift fun x₂ => ↑(↑lift fun x₁ => of (Mul.mul x₁ x₂)) (of One.one)) (of L) …
        -- 🎉 no goals
        -- ⊢ of (Mul.mul One.one L) = of L
      · rw [map_add, ih1, ih2]
        -- ⊢ Mul.mul One.one L = L
        -- 🎉 no goals
        -- 🎉 no goals
    one_mul := fun x ↦ by
        -- ⊢ ↑(↑lift fun x₂ => ↑(↑lift fun x₁ => of (Mul.mul x₁ x₂)) (of One.one)) (-of L …
      dsimp only [(· * ·), Mul.mul, OfNat.ofNat, One.one]
        -- 🎉 no goals
      refine' FreeAbelianGroup.induction_on x rfl _ _ _
        -- ⊢ ↑(↑lift fun x₂ => ↑(↑lift fun x₁ => of (Mul.mul x₁ x₂)) (of One.one)) (x1 +  …
      · intro L
        -- 🎉 no goals
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
#align free_abelian_group.of_mul_hom FreeAbelianGroup.ofMulHom

@[simp]
theorem ofMulHom_coe : (ofMulHom : α → FreeAbelianGroup α) = of :=
  rfl
#align free_abelian_group.of_mul_hom_coe FreeAbelianGroup.ofMulHom_coe

/-- If `f` preserves multiplication, then so does `lift f`. -/
def liftMonoid : (α →* R) ≃ (FreeAbelianGroup α →+* R) where
  toFun f := { lift f with
    toFun := lift f
    map_one' := (lift.of f _).trans f.map_one
    map_mul' := fun x y ↦ by
      simp only
      -- ⊢ ↑(↑lift ↑f) (x * y) = ↑(↑lift ↑f) x * ↑(↑lift ↑f) y
      refine' FreeAbelianGroup.induction_on y
          (by simp only [mul_zero, map_zero]) (fun L2 ↦ _) (fun L2 ih ↦ _) _
      · refine' FreeAbelianGroup.induction_on x
            (by simp only [zero_mul, map_zero]) (fun L1 ↦ _) (fun L1 ih ↦ _) _
        · simp_rw [of_mul_of, lift.of]
          -- ⊢ ↑f (L1 * L2) = ↑f L1 * ↑f L2
          exact f.map_mul _ _
          -- 🎉 no goals
        · simp_rw [neg_mul, map_neg, neg_mul]
          -- ⊢ -↑(↑lift ↑f) (of L1 * of L2) = -(↑(↑lift ↑f) (of L1) * ↑(↑lift ↑f) (of L2))
          exact congr_arg Neg.neg ih
          -- 🎉 no goals
        · intro x1 x2 ih1 ih2
          -- ⊢ ↑(↑lift ↑f) ((x1 + x2) * of L2) = ↑(↑lift ↑f) (x1 + x2) * ↑(↑lift ↑f) (of L2)
          simp only [add_mul, map_add, ih1, ih2]
          -- 🎉 no goals
      · rw [mul_neg, map_neg, map_neg, mul_neg, ih]
        -- 🎉 no goals
      · intro y1 y2 ih1 ih2
        -- ⊢ ↑(↑lift ↑f) (x * (y1 + y2)) = ↑(↑lift ↑f) x * ↑(↑lift ↑f) (y1 + y2)
        rw [mul_add, map_add, map_add, mul_add, ih1, ih2] }
        -- 🎉 no goals
  invFun F := MonoidHom.comp (↑F) ofMulHom
  left_inv f := MonoidHom.ext <| by
    simp only [RingHom.coe_monoidHom_mk, MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk,
      ofMulHom_coe, Function.comp_apply, lift.of, forall_const]
  right_inv F := RingHom.coe_addMonoidHom_injective <| by
    simp only
    -- ⊢ ↑{ toMonoidHom := { toOneHom := { toFun := ↑(↑lift ↑(MonoidHom.comp (↑F) ofM …
    rw [← lift.apply_symm_apply (↑F : FreeAbelianGroup α →+ R)]
    -- ⊢ ↑{ toMonoidHom := { toOneHom := { toFun := ↑(↑lift ↑(MonoidHom.comp (↑F) ofM …
    rfl
    -- 🎉 no goals
#align free_abelian_group.lift_monoid FreeAbelianGroup.liftMonoid

@[simp]
theorem liftMonoid_coe_addMonoidHom (f : α →* R) : ↑(liftMonoid f) = lift f :=
  rfl
#align free_abelian_group.lift_monoid_coe_add_monoid_hom FreeAbelianGroup.liftMonoid_coe_addMonoidHom

@[simp]
theorem liftMonoid_coe (f : α →* R) : ⇑(liftMonoid f) = lift f :=
  rfl
#align free_abelian_group.lift_monoid_coe FreeAbelianGroup.liftMonoid_coe

@[simp]
-- Porting note: Added a type to `↑f`.
theorem liftMonoid_symm_coe (f : FreeAbelianGroup α →+* R) :
    ⇑(liftMonoid.symm f) = lift.symm (↑f : FreeAbelianGroup α →+ R) :=
  rfl
#align free_abelian_group.lift_monoid_symm_coe FreeAbelianGroup.liftMonoid_symm_coe

theorem one_def : (1 : FreeAbelianGroup α) = of 1 :=
  rfl
#align free_abelian_group.one_def FreeAbelianGroup.one_def

theorem of_one : (of 1 : FreeAbelianGroup α) = 1 :=
  rfl
#align free_abelian_group.of_one FreeAbelianGroup.of_one

end Monoid

instance [CommMonoid α] : CommRing (FreeAbelianGroup α) :=
  { FreeAbelianGroup.ring α with
    mul_comm := fun x y ↦ by
      refine' FreeAbelianGroup.induction_on x (zero_mul y) _ _ _
      · intro s
        -- ⊢ of s * y = y * of s
        refine' FreeAbelianGroup.induction_on y (zero_mul _).symm _ _ _
        · intro t
          -- ⊢ of s * of t = of t * of s
          dsimp only [(· * ·), Mul.mul]
          -- ⊢ ↑(↑lift fun x₂ => ↑(↑lift fun x₁ => of (Mul.mul x₁ x₂)) (of s)) (of t) = ↑(↑ …
          iterate 4 rw [lift.of]
          -- ⊢ of (Mul.mul s t) = of (Mul.mul t s)
          congr 1
          -- ⊢ Mul.mul s t = Mul.mul t s
          exact mul_comm _ _
          -- 🎉 no goals
        · intro t ih
          -- ⊢ of s * -of t = -of t * of s
          rw [mul_neg, ih, neg_mul_eq_neg_mul]
          -- 🎉 no goals
        · intro y1 y2 ih1 ih2
          -- ⊢ of s * (y1 + y2) = (y1 + y2) * of s
          rw [mul_add, add_mul, ih1, ih2]
          -- 🎉 no goals
      · intro s ih
        -- ⊢ -of s * y = y * -of s
        rw [neg_mul, ih, neg_mul_eq_mul_neg]
        -- 🎉 no goals
      · intro x1 x2 ih1 ih2
        -- ⊢ (x1 + x2) * y = y * (x1 + x2)
        rw [add_mul, mul_add, ih1, ih2] }
        -- 🎉 no goals

instance pemptyUnique : Unique (FreeAbelianGroup PEmpty) where
  default := 0
  uniq x := FreeAbelianGroup.induction_on x rfl (PEmpty.elim ·) (PEmpty.elim ·) (by
    rintro - - rfl rfl
    -- ⊢ default + default = default
    rfl)
    -- 🎉 no goals
#align free_abelian_group.pempty_unique FreeAbelianGroup.pemptyUnique

/-- The free abelian group on a type with one term is isomorphic to `ℤ`. -/
def punitEquiv (T : Type*) [Unique T] : FreeAbelianGroup T ≃+ ℤ where
  toFun := FreeAbelianGroup.lift fun _ ↦ (1 : ℤ)
  invFun n := n • of Inhabited.default
  left_inv z := FreeAbelianGroup.induction_on z
    (by simp only [zero_smul, AddMonoidHom.map_zero])
        -- 🎉 no goals
    (Unique.forall_iff.2 <| by simp only [one_smul, lift.of]) (Unique.forall_iff.2 <| by simp)
                               -- 🎉 no goals
                                                                                         -- 🎉 no goals
    fun x y hx hy ↦ by
      simp only [AddMonoidHom.map_add, add_smul] at *
      -- ⊢ ↑(↑lift fun x => 1) x • of default + ↑(↑lift fun x => 1) y • of default = x  …
      rw [hx, hy]
      -- 🎉 no goals
  right_inv n := by
    rw [AddMonoidHom.map_zsmul, lift.of]
    -- ⊢ n • 1 = n
    exact zsmul_int_one n
    -- 🎉 no goals
  map_add' := AddMonoidHom.map_add _
#align free_abelian_group.punit_equiv FreeAbelianGroup.punitEquiv

/-- Isomorphic types have isomorphic free abelian groups. -/
def equivOfEquiv {α β : Type*} (f : α ≃ β) : FreeAbelianGroup α ≃+ FreeAbelianGroup β where
  toFun := map f
  invFun := map f.symm
  left_inv := by
    intro x
    -- ⊢ ↑(map ↑f.symm) (↑(map ↑f) x) = x
    rw [← map_comp_apply, Equiv.symm_comp_self, map_id]
    -- ⊢ ↑(AddMonoidHom.id (FreeAbelianGroup α)) x = x
    rfl
    -- 🎉 no goals
  right_inv := by
    intro x
    -- ⊢ ↑(map ↑f) (↑(map ↑f.symm) x) = x
    rw [← map_comp_apply, Equiv.self_comp_symm, map_id]
    -- ⊢ ↑(AddMonoidHom.id (FreeAbelianGroup β)) x = x
    rfl
    -- 🎉 no goals
  map_add' := AddMonoidHom.map_add _
#align free_abelian_group.equiv_of_equiv FreeAbelianGroup.equivOfEquiv

end FreeAbelianGroup
