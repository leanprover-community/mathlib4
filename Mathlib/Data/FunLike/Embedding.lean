/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Data.FunLike.Basic

/-!
# Typeclass for a type `F` with an injective map to `A ↪ B`

This typeclass is primarily for use by embeddings such as `rel_embedding`.

## Basic usage of `embedding_like`

A typical type of embedding should be declared as:
```
structure my_embedding (A B : Type*) [my_class A] [my_class B] :=
(to_fun : A → B)
(injective' : function.injective to_fun)
(map_op' : ∀ {x y : A}, to_fun (my_class.op x y) = my_class.op (to_fun x) (to_fun y))

namespace my_embedding

variables (A B : Type*) [my_class A] [my_class B]

-- This instance is optional if you follow the "Embedding class" design below:
instance : embedding_like (my_embedding A B) A B :=
{ coe := my_embedding.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  injective' := my_embedding.injective' }

/-- Helper instance for when there's too many metavariables to directly
apply `fun_like.to_coe_fn`. -/
instance : has_coe_to_fun (my_embedding A B) (λ _, A → B) := ⟨my_embedding.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : my_embedding A B} : f.to_fun = (f : A → B) := rfl

@[ext] theorem ext {f g : my_embedding A B} (h : ∀ x, f x = g x) : f = g := fun_like.ext f g h

/-- Copy of a `my_embedding` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : my_embedding A B) (f' : A → B) (h : f' = ⇑f) : my_embedding A B :=
{ to_fun := f',
  injective' := h.symm ▸ f.injective',
  map_op' := h.symm ▸ f.map_op' }

end my_embedding
```

This file will then provide a `has_coe_to_fun` instance and various
extensionality and simp lemmas.

## Embedding classes extending `embedding_like`

The `embedding_like` design provides further benefits if you put in a bit more work.
The first step is to extend `embedding_like` to create a class of those types satisfying
the axioms of your new type of morphisms.
Continuing the example above:

```
section
set_option old_structure_cmd true

/-- `my_embedding_class F A B` states that `F` is a type of `my_class.op`-preserving embeddings.
You should extend this class when you extend `my_embedding`. -/
class my_embedding_class (F : Type*) (A B : out_param $ Type*) [my_class A] [my_class B]
  extends embedding_like F A B :=
(map_op : ∀ (f : F) (x y : A), f (my_class.op x y) = my_class.op (f x) (f y))

end

@[simp] lemma map_op {F A B : Type*} [my_class A] [my_class B] [my_embedding_class F A B]
  (f : F) (x y : A) : f (my_class.op x y) = my_class.op (f x) (f y) :=
my_embedding_class.map_op

-- You can replace `my_embedding.embedding_like` with the below instance:
instance : my_embedding_class (my_embedding A B) A B :=
{ coe := my_embedding.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  injective' := my_embedding.injective',
  map_op := my_embedding.map_op' }

-- [Insert `has_coe_to_fun`, `to_fun_eq_coe`, `ext` and `copy` here]
```

The second step is to add instances of your new `my_embedding_class` for all types extending
`my_embedding`.
Typically, you can just declare a new class analogous to `my_embedding_class`:

```
structure cooler_embedding (A B : Type*) [cool_class A] [cool_class B]
  extends my_embedding A B :=
(map_cool' : to_fun cool_class.cool = cool_class.cool)

section
set_option old_structure_cmd true

class cooler_embedding_class (F : Type*) (A B : out_param $ Type*) [cool_class A] [cool_class B]
  extends my_embedding_class F A B :=
(map_cool : ∀ (f : F), f cool_class.cool = cool_class.cool)

end

@[simp] lemma map_cool {F A B : Type*} [cool_class A] [cool_class B] [cooler_embedding_class F A B]
  (f : F) : f cool_class.cool = cool_class.cool :=
my_embedding_class.map_op

-- You can also replace `my_embedding.embedding_like` with the below instance:
instance : cool_embedding_class (cool_embedding A B) A B :=
{ coe := cool_embedding.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  injective' := my_embedding.injective',
  map_op := cool_embedding.map_op',
  map_cool := cool_embedding.map_cool' }

-- [Insert `has_coe_to_fun`, `to_fun_eq_coe`, `ext` and `copy` here]
```

Then any declaration taking a specific type of morphisms as parameter can instead take the
class you just defined:
```
-- Compare with: lemma do_something (f : my_embedding A B) : sorry := sorry
lemma do_something {F : Type*} [my_embedding_class F A B] (f : F) : sorry := sorry
```

This means anything set up for `my_embedding`s will automatically work for `cool_embedding_class`es,
and defining `cool_embedding_class` only takes a constant amount of effort,
instead of linearly increasing the work per `my_embedding`-related declaration.

-/


/-- The class `EmbeddingLike F α β` expresses that terms of type `F` have an
injective coercion to injective functions `α ↪ β`.
-/
class EmbeddingLike (F : Sort _) (α β : outParam (Sort _)) extends FunLike F α fun _ => β where
  /-- The coercion to functions must produce injective functions. -/
  injective' : ∀ f : F, @Function.Injective α β (coe f)

namespace EmbeddingLike

variable {F α β γ : Sort _} [i : EmbeddingLike F α β]

protected theorem injective (f : F) : Function.Injective f :=
  injective' f

@[simp]
theorem apply_eq_iff_eq (f : F) {x y : α} : f x = f y ↔ x = y :=
  (EmbeddingLike.injective f).eq_iff

@[simp]
theorem comp_injective {F : Sort _} [EmbeddingLike F β γ] (f : α → β) (e : F) :
    Function.Injective (e ∘ f) ↔ Function.Injective f :=
  (EmbeddingLike.injective e).of_comp_iff f

end EmbeddingLike
