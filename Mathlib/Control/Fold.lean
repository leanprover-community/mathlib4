/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Sean Leather
-/
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Control.Traversable.Instances
import Mathlib.Control.Traversable.Lemmas
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Category.KleisliCat

#align_import control.fold from "leanprover-community/mathlib"@"740acc0e6f9adf4423f92a485d0456fc271482da"

/-!

# List folds generalized to `Traversable`

Informally, we can think of `foldl` as a special case of `traverse` where we do not care about the
reconstructed data structure and, in a state monad, we care about the final state.

The obvious way to define `foldl` would be to use the state monad but it
is nicer to reason about a more abstract interface with `foldMap` as a
primitive and `foldMap_hom` as a defining property.

```
def foldMap {α ω} [One ω] [Mul ω] (f : α → ω) : t α → ω := ...

lemma foldMap_hom (α β)
  [Monoid α] [Monoid β] (f : α →* β)
  (g : γ → α) (x : t γ) :
  f (foldMap g x) = foldMap (f ∘ g) x :=
...
```

`foldMap` uses a monoid ω to accumulate a value for every element of
a data structure and `foldMap_hom` uses a monoid homomorphism to
substitute the monoid used by `foldMap`. The two are sufficient to
define `foldl`, `foldr` and `toList`. `toList` permits the
formulation of specifications in terms of operations on lists.

Each fold function can be defined using a specialized
monoid. `toList` uses a free monoid represented as a list with
concatenation while `foldl` uses endofunctions together with function
composition.

The definition through monoids uses `traverse` together with the
applicative functor `const m` (where `m` is the monoid). As an
implementation, `const` guarantees that no resource is spent on
reconstructing the structure during traversal.

A special class could be defined for `foldable`, similarly to Haskell,
but the author cannot think of instances of `foldable` that are not also
`Traversable`.
-/


universe u v

open ULift CategoryTheory MulOpposite

namespace Monoid

variable {m : Type u → Type u} [Monad m]

variable {α β : Type u}

/-- For a list, foldl f x [y₀,y₁] reduces as follows:

```
calc  foldl f x [y₀,y₁]
    = foldl f (f x y₀) [y₁]      : rfl
... = foldl f (f (f x y₀) y₁) [] : rfl
... = f (f x y₀) y₁              : rfl
```
with
```
f : α → β → α
x : α
[y₀,y₁] : List β
```

We can view the above as a composition of functions:
```
... = f (f x y₀) y₁              : rfl
... = flip f y₁ (flip f y₀ x)    : rfl
... = (flip f y₁ ∘ flip f y₀) x  : rfl
```

We can use traverse and const to construct this composition:
```
calc   const.run (traverse (λ y, const.mk' (flip f y)) [y₀,y₁]) x
     = const.run ((::) <$> const.mk' (flip f y₀) <*> traverse (λ y, const.mk' (flip f y)) [y₁]) x
...  = const.run ((::) <$> const.mk' (flip f y₀) <*>
         ( (::) <$> const.mk' (flip f y₁) <*> traverse (λ y, const.mk' (flip f y)) [] )) x
...  = const.run ((::) <$> const.mk' (flip f y₀) <*>
         ( (::) <$> const.mk' (flip f y₁) <*> pure [] )) x
...  = const.run ( ((::) <$> const.mk' (flip f y₁) <*> pure []) ∘
         ((::) <$> const.mk' (flip f y₀)) ) x
...  = const.run ( const.mk' (flip f y₁) ∘ const.mk' (flip f y₀) ) x
...  = const.run ( flip f y₁ ∘ flip f y₀ ) x
...  = f (f x y₀) y₁
```

And this is how `const` turns a monoid into an applicative functor and
how the monoid of endofunctions define `Foldl`.
-/
@[reducible]
def Foldl (α : Type u) : Type u :=
  (End α)ᵐᵒᵖ
#align monoid.foldl Monoid.Foldl

def Foldl.mk (f : α → α) : Foldl α :=
  op f
#align monoid.foldl.mk Monoid.Foldl.mk

def Foldl.get (x : Foldl α) : α → α :=
  unop x
#align monoid.foldl.get Monoid.Foldl.get

@[simps]
def Foldl.ofFreeMonoid (f : β → α → β) : FreeMonoid α →* Monoid.Foldl β
    where
  toFun xs := op <| flip (List.foldl f) (FreeMonoid.toList xs)
  map_one' := rfl
  map_mul' := by
    intros; simp only [FreeMonoid.toList_mul, flip, unop_op, List.foldl_append, op_inj]; rfl
    -- ⊢ OneHom.toFun { toFun := fun xs => op (flip (List.foldl f) (↑FreeMonoid.toLis …
            -- ⊢ (op fun a => List.foldl f (List.foldl f a (↑FreeMonoid.toList x✝)) (↑FreeMon …
                                                                                         -- 🎉 no goals
#align monoid.foldl.of_free_monoid Monoid.Foldl.ofFreeMonoid

@[reducible]
def Foldr (α : Type u) : Type u :=
  End α
#align monoid.foldr Monoid.Foldr

def Foldr.mk (f : α → α) : Foldr α :=
  f
#align monoid.foldr.mk Monoid.Foldr.mk

def Foldr.get (x : Foldr α) : α → α :=
  x
#align monoid.foldr.get Monoid.Foldr.get

@[simps]
def Foldr.ofFreeMonoid (f : α → β → β) : FreeMonoid α →* Monoid.Foldr β
    where
  toFun xs := flip (List.foldr f) (FreeMonoid.toList xs)
  map_one' := rfl
  map_mul' _ _ := funext fun _ => List.foldr_append _ _ _ _
#align monoid.foldr.of_free_monoid Monoid.Foldr.ofFreeMonoid

@[reducible]
def foldlM (m : Type u → Type u) [Monad m] (α : Type u) : Type u :=
  MulOpposite <| End <| KleisliCat.mk m α
#align monoid.mfoldl Monoid.foldlM

def foldlM.mk (f : α → m α) : foldlM m α :=
  op f
#align monoid.mfoldl.mk Monoid.foldlM.mk

def foldlM.get (x : foldlM m α) : α → m α :=
  unop x
#align monoid.mfoldl.get Monoid.foldlM.get

@[simps]
def foldlM.ofFreeMonoid [LawfulMonad m] (f : β → α → m β) : FreeMonoid α →* Monoid.foldlM m β
    where
  toFun xs := op <| flip (List.foldlM f) (FreeMonoid.toList xs)
  map_one' := rfl
  map_mul' := by intros; apply unop_injective; funext; apply List.foldlM_append
                 -- ⊢ OneHom.toFun { toFun := fun xs => op (flip (List.foldlM f) (↑FreeMonoid.toLi …
                         -- ⊢ unop (OneHom.toFun { toFun := fun xs => op (flip (List.foldlM f) (↑FreeMonoi …
                                               -- ⊢ unop (OneHom.toFun { toFun := fun xs => op (flip (List.foldlM f) (↑FreeMonoi …
                                                       -- 🎉 no goals
#align monoid.mfoldl.of_free_monoid Monoid.foldlM.ofFreeMonoid

@[reducible]
def foldrM (m : Type u → Type u) [Monad m] (α : Type u) : Type u :=
  End <| KleisliCat.mk m α
#align monoid.mfoldr Monoid.foldrM

def foldrM.mk (f : α → m α) : foldrM m α :=
  f
#align monoid.mfoldr.mk Monoid.foldrM.mk

def foldrM.get (x : foldrM m α) : α → m α :=
  x
#align monoid.mfoldr.get Monoid.foldrM.get

@[simps]
def foldrM.ofFreeMonoid [LawfulMonad m] (f : α → β → m β) : FreeMonoid α →* Monoid.foldrM m β
    where
  toFun xs := flip (List.foldrM f) (FreeMonoid.toList xs)
  map_one' := rfl
  map_mul' := by intros; funext; apply List.foldrM_append
                 -- ⊢ OneHom.toFun { toFun := fun xs => flip (List.foldrM f) (↑FreeMonoid.toList x …
                         -- ⊢ OneHom.toFun { toFun := fun xs => flip (List.foldrM f) (↑FreeMonoid.toList x …
                                 -- 🎉 no goals
#align monoid.mfoldr.of_free_monoid Monoid.foldrM.ofFreeMonoid

end Monoid

namespace Traversable

open Monoid Functor

section Defs

variable {α β : Type u} {t : Type u → Type u} [Traversable t]

def foldMap {α ω} [One ω] [Mul ω] (f : α → ω) : t α → ω :=
  traverse (Const.mk' ∘ f)
#align traversable.fold_map Traversable.foldMap

def foldl (f : α → β → α) (x : α) (xs : t β) : α :=
  (foldMap (Foldl.mk ∘ flip f) xs).get x
#align traversable.foldl Traversable.foldl

def foldr (f : α → β → β) (x : β) (xs : t α) : β :=
  (foldMap (Foldr.mk ∘ f) xs).get x
#align traversable.foldr Traversable.foldr

/-- Conceptually, `toList` collects all the elements of a collection
in a list. This idea is formalized by

  `lemma toList_spec (x : t α) : toList x = foldMap FreeMonoid.mk x`.

The definition of `toList` is based on `foldl` and `List.cons` for
speed. It is faster than using `foldMap FreeMonoid.mk` because, by
using `foldl` and `List.cons`, each insertion is done in constant
time. As a consequence, `toList` performs in linear.

On the other hand, `foldMap FreeMonoid.mk` creates a singleton list
around each element and concatenates all the resulting lists. In
`xs ++ ys`, concatenation takes a time proportional to `length xs`. Since
the order in which concatenation is evaluated is unspecified, nothing
prevents each element of the traversable to be appended at the end
`xs ++ [x]` which would yield a `O(n²)` run time. -/
def toList : t α → List α :=
  List.reverse ∘ foldl (flip List.cons) []
#align traversable.to_list Traversable.toList

def length (xs : t α) : ℕ :=
  down <| foldl (fun l _ => up <| l.down + 1) (up 0) xs
#align traversable.length Traversable.length

variable {m : Type u → Type u} [Monad m]

def foldlm (f : α → β → m α) (x : α) (xs : t β) : m α :=
  (foldMap (foldlM.mk ∘ flip f) xs).get x
#align traversable.mfoldl Traversable.foldlm

def foldrm (f : α → β → m β) (x : β) (xs : t α) : m β :=
  (foldMap (foldrM.mk ∘ f) xs).get x
#align traversable.mfoldr Traversable.foldrm

end Defs

section ApplicativeTransformation

variable {α β γ : Type u}

open Function hiding const

def mapFold [Monoid α] [Monoid β] (f : α →* β) : ApplicativeTransformation (Const α) (Const β)
    where
  app _ := f
  preserves_seq' := by intros; simp only [Seq.seq, map_mul]
                       -- ⊢ (fun x => ↑f) β✝ (Seq.seq x✝ fun x => y✝) = Seq.seq ((fun x => ↑f) (α✝ → β✝) …
                        -- ⊢ (fun x => ↑f) α✝ (pure x✝) = pure x✝
                                -- 🎉 no goals
                               -- 🎉 no goals
  preserves_pure' := by intros; simp only [map_one, pure]
#align traversable.map_fold Traversable.mapFold

theorem Free.map_eq_map (f : α → β) (xs : List α) :
    f <$> xs = (FreeMonoid.toList (FreeMonoid.map f (FreeMonoid.ofList xs))) :=
  rfl
#align traversable.free.map_eq_map Traversable.Free.map_eq_map

theorem foldl.unop_ofFreeMonoid (f : β → α → β) (xs : FreeMonoid α) (a : β) :
    unop (Foldl.ofFreeMonoid f xs) a = List.foldl f a (FreeMonoid.toList xs) :=
  rfl
#align traversable.foldl.unop_of_free_monoid Traversable.foldl.unop_ofFreeMonoid

variable (m : Type u → Type u) [Monad m] [LawfulMonad m]

variable {t : Type u → Type u} [Traversable t] [LawfulTraversable t]

open LawfulTraversable

theorem foldMap_hom [Monoid α] [Monoid β] (f : α →* β) (g : γ → α) (x : t γ) :
    f (foldMap g x) = foldMap (f ∘ g) x :=
  calc
    f (foldMap g x) = f (traverse (Const.mk' ∘ g) x) := rfl
    _ = (mapFold f).app _ (traverse (Const.mk' ∘ g) x) := rfl
    _ = traverse ((mapFold f).app _ ∘ Const.mk' ∘ g) x := naturality (mapFold f) _ _
    _ = foldMap (f ∘ g) x := rfl
#align traversable.fold_map_hom Traversable.foldMap_hom

theorem foldMap_hom_free [Monoid β] (f : FreeMonoid α →* β) (x : t α) :
    f (foldMap FreeMonoid.of x) = foldMap (f ∘ FreeMonoid.of) x :=
  foldMap_hom f _ x
#align traversable.fold_map_hom_free Traversable.foldMap_hom_free

end ApplicativeTransformation

section Equalities

open LawfulTraversable

open List (cons)

variable {α β γ : Type u}

variable {t : Type u → Type u} [Traversable t] [LawfulTraversable t]

@[simp]
theorem foldl.ofFreeMonoid_comp_of (f : α → β → α) :
    Foldl.ofFreeMonoid f ∘ FreeMonoid.of = Foldl.mk ∘ flip f :=
  rfl
#align traversable.foldl.of_free_monoid_comp_of Traversable.foldl.ofFreeMonoid_comp_of

@[simp]
theorem foldr.ofFreeMonoid_comp_of (f : β → α → α) :
    Foldr.ofFreeMonoid f ∘ FreeMonoid.of = Foldr.mk ∘ f :=
  rfl
#align traversable.foldr.of_free_monoid_comp_of Traversable.foldr.ofFreeMonoid_comp_of

@[simp]
theorem foldlm.ofFreeMonoid_comp_of {m} [Monad m] [LawfulMonad m] (f : α → β → m α) :
    foldlM.ofFreeMonoid f ∘ FreeMonoid.of = foldlM.mk ∘ flip f := by
  ext1 x
  -- ⊢ (↑(foldlM.ofFreeMonoid f) ∘ FreeMonoid.of) x = (foldlM.mk ∘ flip f) x
  simp [(· ∘ ·), foldlM.ofFreeMonoid, foldlM.mk, flip]
  -- 🎉 no goals
#align traversable.mfoldl.of_free_monoid_comp_of Traversable.foldlm.ofFreeMonoid_comp_of

@[simp]
theorem foldrm.ofFreeMonoid_comp_of {m} [Monad m] [LawfulMonad m] (f : β → α → m α) :
    foldrM.ofFreeMonoid f ∘ FreeMonoid.of = foldrM.mk ∘ f := by
  ext
  -- ⊢ (↑(foldrM.ofFreeMonoid f) ∘ FreeMonoid.of) x✝ = (foldrM.mk ∘ f) x✝
  simp [(· ∘ ·), foldrM.ofFreeMonoid, foldrM.mk, flip]
  -- 🎉 no goals
#align traversable.mfoldr.of_free_monoid_comp_of Traversable.foldrm.ofFreeMonoid_comp_of

theorem toList_spec (xs : t α) : toList xs = FreeMonoid.toList (foldMap FreeMonoid.of xs) :=
  Eq.symm <|
    calc
      FreeMonoid.toList (foldMap FreeMonoid.of xs) =
          FreeMonoid.toList (foldMap FreeMonoid.of xs).reverse.reverse :=
          by simp only [List.reverse_reverse]
             -- 🎉 no goals
      _ = FreeMonoid.toList (List.foldr cons [] (foldMap FreeMonoid.of xs).reverse).reverse :=
          by simp only [List.foldr_eta]
             -- 🎉 no goals
      _ = (unop (Foldl.ofFreeMonoid (flip cons) (foldMap FreeMonoid.of xs)) []).reverse :=
          by simp [flip, List.foldr_reverse, Foldl.ofFreeMonoid, unop_op]
             -- 🎉 no goals
      _ = toList xs :=
          by rw [foldMap_hom_free (Foldl.ofFreeMonoid (flip <| @cons α))]
             -- ⊢ List.reverse (unop (foldMap (↑(Foldl.ofFreeMonoid (flip cons)) ∘ FreeMonoid. …
             simp only [toList, foldl, List.reverse_inj, Foldl.get, foldl.ofFreeMonoid_comp_of,
               Function.comp_apply]
#align traversable.to_list_spec Traversable.toList_spec

theorem foldMap_map [Monoid γ] (f : α → β) (g : β → γ) (xs : t α) :
    foldMap g (f <$> xs) = foldMap (g ∘ f) xs := by simp only [foldMap, traverse_map, Function.comp]
                                                    -- 🎉 no goals
#align traversable.fold_map_map Traversable.foldMap_map

theorem foldl_toList (f : α → β → α) (xs : t β) (x : α) :
    foldl f x xs = List.foldl f x (toList xs) := by
  rw [← FreeMonoid.toList_ofList (toList xs), ← foldl.unop_ofFreeMonoid]
  -- ⊢ foldl f x xs = unop (↑(Foldl.ofFreeMonoid f) (↑FreeMonoid.ofList (toList xs) …
  simp only [foldl, toList_spec, foldMap_hom_free, foldl.ofFreeMonoid_comp_of, Foldl.get,
    FreeMonoid.ofList_toList]
#align traversable.foldl_to_list Traversable.foldl_toList

theorem foldr_toList (f : α → β → β) (xs : t α) (x : β) :
    foldr f x xs = List.foldr f x (toList xs) := by
  change _ = Foldr.ofFreeMonoid _ (FreeMonoid.ofList <| toList xs) _
  -- ⊢ foldr f x xs = ↑(Foldr.ofFreeMonoid f) (↑FreeMonoid.ofList (toList xs)) x
  rw [toList_spec, foldr, Foldr.get, FreeMonoid.ofList_toList, foldMap_hom_free,
    foldr.ofFreeMonoid_comp_of]
#align traversable.foldr_to_list Traversable.foldr_toList

theorem toList_map (f : α → β) (xs : t α) : toList (f <$> xs) = f <$> toList xs := by
  simp only [toList_spec, Free.map_eq_map, foldMap_hom, foldMap_map, FreeMonoid.ofList_toList,
    FreeMonoid.map_of, (· ∘ ·)]
#align traversable.to_list_map Traversable.toList_map

@[simp]
theorem foldl_map (g : β → γ) (f : α → γ → α) (a : α) (l : t β) :
    foldl f a (g <$> l) = foldl (fun x y => f x (g y)) a l := by
  simp only [foldl, foldMap_map, (· ∘ ·), flip]
  -- 🎉 no goals
#align traversable.foldl_map Traversable.foldl_map

@[simp]
theorem foldr_map (g : β → γ) (f : γ → α → α) (a : α) (l : t β) :
    foldr f a (g <$> l) = foldr (f ∘ g) a l := by simp only [foldr, foldMap_map, (· ∘ ·), flip]
                                                  -- 🎉 no goals
#align traversable.foldr_map Traversable.foldr_map

@[simp]
theorem toList_eq_self {xs : List α} : toList xs = xs := by
  simp only [toList_spec, foldMap, traverse]
  -- ⊢ ↑FreeMonoid.toList (List.traverse (Const.mk' ∘ FreeMonoid.of) xs) = xs
  induction xs
  -- ⊢ ↑FreeMonoid.toList (List.traverse (Const.mk' ∘ FreeMonoid.of) []) = []
  case nil => rfl
  -- ⊢ ↑FreeMonoid.toList (List.traverse (Const.mk' ∘ FreeMonoid.of) (head✝ :: tail …
  -- 🎉 no goals
  case cons _ _ ih => conv_rhs => rw [← ih]; rfl
  -- 🎉 no goals
  -- 🎉 no goals
#align traversable.to_list_eq_self Traversable.toList_eq_self

theorem length_toList {xs : t α} : length xs = List.length (toList xs) := by
  unfold length
  -- ⊢ (foldl (fun l x => { down := l.down + 1 }) { down := 0 } xs).down = List.len …
  rw [foldl_toList]
  -- ⊢ (List.foldl (fun l x => { down := l.down + 1 }) { down := 0 } (toList xs)).d …
  generalize toList xs = ys
  -- ⊢ (List.foldl (fun l x => { down := l.down + 1 }) { down := 0 } ys).down = Lis …
  rw [← Nat.add_zero ys.length]
  -- ⊢ (List.foldl (fun l x => { down := l.down + 1 }) { down := 0 } ys).down = Lis …
  generalize 0 = n
  -- ⊢ (List.foldl (fun l x => { down := l.down + 1 }) { down := n } ys).down = Lis …
  induction' ys with _ _ ih generalizing n
  -- ⊢ (List.foldl (fun l x => { down := l.down + 1 }) { down := n } []).down = Lis …
  · simp
    -- 🎉 no goals
  · simp_arith [ih]
    -- 🎉 no goals
#align traversable.length_to_list Traversable.length_toList

variable {m : Type u → Type u} [Monad m] [LawfulMonad m]

theorem foldlm_toList {f : α → β → m α} {x : α} {xs : t β} :
    foldlm f x xs = List.foldlM f x (toList xs) :=
  calc
    foldlm f x xs = unop (foldlM.ofFreeMonoid f (FreeMonoid.ofList <| toList xs)) x :=
    by simp only [foldlm, toList_spec, foldMap_hom_free (foldlM.ofFreeMonoid f),
        foldlm.ofFreeMonoid_comp_of, foldlM.get, FreeMonoid.ofList_toList]
    _ = List.foldlM f x (toList xs) := by simp [foldlM.ofFreeMonoid, unop_op, flip]
                                          -- 🎉 no goals
#align traversable.mfoldl_to_list Traversable.foldlm_toList

theorem foldrm_toList (f : α → β → m β) (x : β) (xs : t α) :
    foldrm f x xs = List.foldrM f x (toList xs) := by
  change _ = foldrM.ofFreeMonoid f (FreeMonoid.ofList <| toList xs) x
  -- ⊢ foldrm f x xs = ↑(foldrM.ofFreeMonoid f) (↑FreeMonoid.ofList (toList xs)) x
  simp only [foldrm, toList_spec, foldMap_hom_free (foldrM.ofFreeMonoid f),
    foldrm.ofFreeMonoid_comp_of, foldrM.get, FreeMonoid.ofList_toList]
#align traversable.mfoldr_to_list Traversable.foldrm_toList

@[simp]
theorem foldlm_map (g : β → γ) (f : α → γ → m α) (a : α) (l : t β) :
    foldlm f a (g <$> l) = foldlm (fun x y => f x (g y)) a l := by
  simp only [foldlm, foldMap_map, (· ∘ ·), flip]
  -- 🎉 no goals
#align traversable.mfoldl_map Traversable.foldlm_map

@[simp]
theorem foldrm_map (g : β → γ) (f : γ → α → m α) (a : α) (l : t β) :
    foldrm f a (g <$> l) = foldrm (f ∘ g) a l := by simp only [foldrm, foldMap_map, (· ∘ ·), flip]
                                                    -- 🎉 no goals
#align traversable.mfoldr_map Traversable.foldrm_map

end Equalities

end Traversable
