/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Data.FunLike.Embedding

/-!
# Typeclass for a type `F` with an injective map to `A ≃ B`

This typeclass is primarily for use by isomorphisms like `MonoidEquiv` and `LinearEquiv`.

## Basic usage of `EquivLike`

A typical type of isomorphisms should be declared as:
```
structure MyIso (A B : Type*) [MyClass A] [MyClass B] extends Equiv A B where
  (map_op' : ∀ (x y : A), toFun (MyClass.op x y) = MyClass.op (toFun x) (toFun y))

namespace MyIso

variable (A B : Type*) [MyClass A] [MyClass B]

instance instEquivLike : EquivLike (MyIso A B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; congr; exact EquivLike.coe_injective' _ _ h₁ h₂

@[ext] theorem ext {f g : MyIso A B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

/-- Copy of a `MyIso` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : MyIso A B) (f' : A → B) (f_inv : B → A)
    (h₁ : f' = f) (h₂ : f_inv = f.invFun) : MyIso A B where
  toFun := f'
  invFun := f_inv
  left_inv := h₁.symm ▸ h₂.symm ▸ f.left_inv
  right_inv := h₁.symm ▸ h₂.symm ▸ f.right_inv
  map_op' := h₁.symm ▸ f.map_op'

end MyIso
```

This file will then provide a `CoeFun` instance and various
extensionality and simp lemmas.

## Isomorphism classes extending `EquivLike`

The `EquivLike` design provides further benefits if you put in a bit more work.
The first step is to extend `EquivLike` to create a class of those types satisfying
the axioms of your new type of isomorphisms.
Continuing the example above:

```
/-- `MyIsoClass F A B` states that `F` is a type of `MyClass.op`-preserving morphisms.
You should extend this class when you extend `MyIso`. -/
class MyIsoClass (F : Type*) (A B : outParam Type*) [MyClass A] [MyClass B]
    [EquivLike F A B]
    extends MyHomClass F A B

namespace MyIso

variable {A B : Type*} [MyClass A] [MyClass B]

-- This goes after `MyIsoClass.instEquivLike`:
instance : MyIsoClass (MyIso A B) A B where
  map_op := MyIso.map_op'

-- [Insert `ext` and `copy` here]

end MyIso
```

The second step is to add instances of your new `MyIsoClass` for all types extending `MyIso`.
Typically, you can just declare a new class analogous to `MyIsoClass`:

```
structure CoolerIso (A B : Type*) [CoolClass A] [CoolClass B] extends MyIso A B where
  (map_cool' : toFun CoolClass.cool = CoolClass.cool)

class CoolerIsoClass (F : Type*) (A B : outParam Type*) [CoolClass A] [CoolClass B]
    [EquivLike F A B]
    extends MyIsoClass F A B where
  (map_cool : ∀ (f : F), f CoolClass.cool = CoolClass.cool)

@[simp] lemma map_cool {F A B : Type*} [CoolClass A] [CoolClass B]
    [EquivLike F A B] [CoolerIsoClass F A B] (f : F) :
    f CoolClass.cool = CoolClass.cool :=
  CoolerIsoClass.map_cool _

namespace CoolerIso

variable {A B : Type*} [CoolClass A] [CoolClass B]

instance : EquivLike (CoolerIso A B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; congr; exact EquivLike.coe_injective' _ _ h₁ h₂

instance : CoolerIsoClass (CoolerIso A B) A B where
  map_op f := f.map_op'
  map_cool f := f.map_cool'

-- [Insert `ext` and `copy` here]

end CoolerIso
```

Then any declaration taking a specific type of morphisms as parameter can instead take the
class you just defined:
```
-- Compare with: lemma do_something (f : MyIso A B) : sorry := sorry
lemma do_something {F : Type*} [EquivLike F A B] [MyIsoClass F A B] (f : F) : sorry := sorry
```

This means anything set up for `MyIso`s will automatically work for `CoolerIsoClass`es,
and defining `CoolerIsoClass` only takes a constant amount of effort,
instead of linearly increasing the work per `MyIso`-related declaration.

-/


/-- The class `EquivLike E α β` expresses that terms of type `E` have an
injective coercion to bijections between `α` and `β`.

Note that this does not directly extend `FunLike`, nor take `FunLike` as a parameter,
so we can state `coe_injective'` in a nicer way.

This typeclass is used in the definition of the isomorphism (or equivalence) typeclasses,
such as `ZeroEquivClass`, `MulEquivClass`, `MonoidEquivClass`, ....
-/
class EquivLike (E : Sort*) (α β : outParam (Sort*)) where
  /-- The coercion to a function in the forward direction. -/
  coe : E → α → β
  /-- The coercion to a function in the backwards direction. -/
  inv : E → β → α
  /-- The coercions are left inverses. -/
  left_inv : ∀ e, Function.LeftInverse (inv e) (coe e)
  /-- The coercions are right inverses. -/
  right_inv : ∀ e, Function.RightInverse (inv e) (coe e)
  /-- The two coercions to functions are jointly injective. -/
  coe_injective' : ∀ e g, coe e = coe g → inv e = inv g → e = g
  -- This is mathematically equivalent to either of the coercions to functions being injective, but
  -- the `inv` hypothesis makes this easier to prove with `congr'`

namespace EquivLike

variable {E F α β γ : Sort*} [EquivLike E α β] [EquivLike F β γ]

theorem inv_injective : Function.Injective (EquivLike.inv : E → β → α) := fun e g h ↦
  coe_injective' e g ((right_inv e).eq_rightInverse (h.symm ▸ left_inv g)) h

instance (priority := 100) toFunLike : FunLike E α β where
  coe := (coe : E → α → β)
  coe_injective' e g h :=
    coe_injective' e g h ((left_inv e).eq_rightInverse (h.symm ▸ right_inv g))

@[simp] theorem coe_apply {e : E} {a : α} : coe e a = e a := rfl

theorem inv_apply_eq {e : E} {b : β} {a : α} : inv e b = a ↔ b = e a := by
  constructor <;> rintro ⟨_, rfl⟩
  exacts [(right_inv e b).symm, left_inv e a]

instance (priority := 100) toEmbeddingLike : EmbeddingLike E α β where
  injective' e := (left_inv e).injective

@[simp] theorem coe_eq_coeFn {e : E} : coe e = ⇑e := rfl

protected theorem injective (e : E) : Function.Injective e :=
  EmbeddingLike.injective e

protected theorem surjective (e : E) : Function.Surjective e :=
  (right_inv e).surjective

protected theorem bijective (e : E) : Function.Bijective (e : α → β) :=
  ⟨EquivLike.injective e, EquivLike.surjective e⟩

theorem apply_eq_iff_eq (f : E) {x y : α} : f x = f y ↔ x = y :=
  EmbeddingLike.apply_eq_iff_eq f

@[simp]
theorem injective_comp (e : E) (f : β → γ) : Function.Injective (f ∘ e) ↔ Function.Injective f :=
  Function.Injective.of_comp_iff' f (EquivLike.bijective e)

@[simp]
theorem surjective_comp (e : E) (f : β → γ) : Function.Surjective (f ∘ e) ↔ Function.Surjective f :=
  (EquivLike.surjective e).of_comp_iff f

@[simp]
theorem bijective_comp (e : E) (f : β → γ) : Function.Bijective (f ∘ e) ↔ Function.Bijective f :=
  (EquivLike.bijective e).of_comp_iff f

/-- This lemma is only supposed to be used in the generic context, when working with instances
of classes extending `EquivLike`.
For concrete isomorphism types such as `Equiv` which have a `symm` operator,
  you should use `EquivLike.Symm.symm_apply_apply`. -/
@[simp]
theorem inv_apply_apply (e : E) (a : α) : inv e (e a) = a := left_inv _ _

/-- This lemma is only supposed to be used in the generic context, when working with instances
of classes extending `EquivLike`.
For concrete isomorphism types such as `Equiv` which have a `symm` operator,
  you should use `EquivLike.Symm.apply_symm_apply`. -/

@[simp]
theorem apply_inv_apply (e : E) (b : β) : e (inv e b) = b := right_inv _ _

@[deprecated inv_apply_eq (since := "2025-06-20")]
lemma inv_apply_eq_iff_eq_apply {e : E} {b : β} {a : α} : inv e b = a ↔ b = e a := inv_apply_eq

theorem comp_injective (f : α → β) (e : F) : Function.Injective (e ∘ f) ↔ Function.Injective f :=
  EmbeddingLike.comp_injective f e

@[simp]
theorem comp_surjective (f : α → β) (e : F) : Function.Surjective (e ∘ f) ↔ Function.Surjective f :=
  Function.Surjective.of_comp_iff' (EquivLike.bijective e) f

@[simp]
theorem comp_bijective (f : α → β) (e : F) : Function.Bijective (e ∘ f) ↔ Function.Bijective f :=
  (EquivLike.bijective e).of_comp_iff' f

include β in
/-- This is not an instance to avoid slowing down every single `Subsingleton` typeclass search. -/
lemma subsingleton_dom [Subsingleton α] : Subsingleton E :=
  ⟨fun f g ↦ DFunLike.ext f g fun _ ↦ (right_inv f).injective <| Subsingleton.elim _ _⟩

section
variable {p : α → Prop} {q : β → Prop} (e : E)

lemma forall_congr_right : (∀ a, q (e a)) ↔ ∀ b, q b :=
  ⟨fun h a ↦ by simpa using h (inv e a), fun h _ ↦ h _⟩

lemma forall_congr_left : (∀ a, p a) ↔ ∀ b, p (inv e b) :=
  ⟨fun h _ ↦ h _, fun h a ↦ by simpa using h (e a)⟩

lemma forall_congr (h : ∀ a, p a ↔ q (e a)) : (∀ a, p a) ↔ ∀ b, q b :=
  (forall_congr_left e).trans (by simp [h])

lemma forall_congr' (h : ∀ b, p (inv e b) ↔ q b) : (∀ a, p a) ↔ ∀ b, q b :=
  (forall_congr_left e).trans (by simp [h])

lemma exists_congr_right : (∃ a, q (e a)) ↔ ∃ b, q b :=
  ⟨fun ⟨_, h⟩ ↦ ⟨_, h⟩, fun ⟨a, h⟩ ↦ ⟨inv e a, by simpa using h⟩⟩

lemma exists_congr_left : (∃ a, p a) ↔ ∃ b, p (inv e b) :=
  ⟨fun ⟨a, h⟩ ↦ ⟨e a, by simpa using h⟩, fun ⟨_, h⟩ ↦ ⟨_, h⟩⟩

lemma exists_congr (h : ∀ a, p a ↔ q (e a)) : (∃ a, p a) ↔ ∃ b, q b :=
  (exists_congr_left e).trans <| by simp [h]

lemma exists_congr' (h : ∀ b, p (inv e b) ↔ q b) : (∃ a, p a) ↔ ∃ b, q b :=
  (exists_congr_left e).trans <| by simp only [h]

lemma existsUnique_congr_right : (∃! a, q (e a)) ↔ ∃! b, q b :=
  exists_congr e <| by simpa using fun _ _ ↦ forall_congr e (by simp)

lemma existsUnique_congr_left : (∃! a, p a) ↔ ∃! b, p (inv e b) :=
  exists_congr e <| by simpa using fun _ _ ↦ forall_congr e (by simp)

lemma existsUnique_congr (h : ∀ a, p a ↔ q (e a)) : (∃! a, p a) ↔ ∃! b, q b :=
  (existsUnique_congr_left e).trans <| by simp [h]

lemma existsUnique_congr' (h : ∀ b, p (inv e b) ↔ q b) : (∃! a, p a) ↔ ∃! b, q b :=
  (existsUnique_congr_left e).trans <| by simp [h]

end

abbrev Refl (E : Sort*) {α : outParam Sort*} [EquivLike E α α] := FunLike.Id E

def refl [EquivLike E α α] [Refl E] : E := FunLike.id

section Refl

variable {E α : Sort*} [EquivLike E α α] [Refl E] {e : E} {a : α}

theorem coe_refl : ⇑(refl : E) = id := FunLike.coe_id
@[simp] theorem refl_apply : (refl : E) a = a := congrFun coe_refl a

end Refl

abbrev Trans (E F : Sort*) (G : outParam Sort*) {α β γ : outParam Sort*}
    [EquivLike E α β] [EquivLike F β γ] [EquivLike G α γ] := FunLike.Comp F E G

def trans {G} [EquivLike E α β] [EquivLike F β γ] [EquivLike G α γ] [Trans E F G] :
    E → F → G := flip FunLike.comp

section Trans

variable {G H K L δ : Sort*}
  [EquivLike G γ δ] [EquivLike H α γ] [EquivLike K β δ] [EquivLike L α δ]
  [Trans E F H] [Trans F G K] [Trans H G L] [Trans E K L]
  {e : E} {f : F} {g : G} {h : H} {a : α} {c : γ}

theorem coe_trans : ⇑(trans e f) = ⇑f ∘ ⇑e := FunLike.coe_comp
@[simp] theorem trans_apply : trans e f a = f (e a) := congrFun coe_trans a

theorem trans_assoc : trans (trans e f) g = trans e (trans f g) :=
  DFunLike.ext _ _ <| fun _ => by simp only [trans_apply]

@[simp] theorem refl_trans {E} [EquivLike E α β] [EquivLike F β β] [Trans E F E] [Refl F] {e : E} :
    trans e (refl : F) = e :=
  DFunLike.ext _ _ <| fun _ => by simp only [trans_apply, refl_apply]

@[simp] theorem trans_refl {E} [EquivLike E α β] [EquivLike F α α] [Trans F E E] [Refl F] {e : E} :
    trans (refl : F) e = e :=
  DFunLike.ext _ _ <| fun _ => by simp only [trans_apply, refl_apply]

instance [Trans E F H] : FunLike.Comp F E H where
  comp := flip trans
  coe_comp' := coe_trans

end Trans

/-- A class that represents `EquivLike` types equipped with a symmetry operation. -/
class Symm (E : Sort*) (F : outParam Sort*) {α β : outParam Sort*}
  [EquivLike E α β] [EquivLike F β α] where
  /-- Symmetry operation. -/
  symm : E → F
  protected coe_symm' : ∀ {e}, symm e = inv e := by exact fun {e} => rfl

/-- Symmetry operation. -/
def symm [EquivLike E α β] [EquivLike F β α] [Symm E F] : E → F := Symm.symm

section Symm

instance [EquivLike E α β] [EquivLike F β α] : Subsingleton (Symm E F) where
  allEq a b := by
    cases a with | mk symm ha; cases b with | mk symm' hb
    cases (funext (fun _ => by simp only [DFunLike.ext'_iff, ha, hb]) : symm = symm')
    rfl

variable {E F : Sort*} [EquivLike E α β] [EquivLike F β α] [Symm E F]
  {e : E} {f : F} {a : α} {b : β}

theorem coe_symm : ⇑(symm e) = inv e := Symm.coe_symm'
theorem symm_apply : symm e b = inv e b := congrFun coe_symm b

@[simp] theorem coe_inv : inv e = symm e := coe_symm.symm
@[simp] theorem inv_apply : inv e b = symm e b := symm_apply.symm

theorem symm_apply_eq : symm e b = a ↔ b = e a := by
  rw [coe_symm, inv_apply_eq_iff_eq_apply]

theorem eq_symm_apply : a = symm e b ↔ e a = b := by
  rw [eq_comm, symm_apply_eq, eq_comm]

@[simp] theorem symm_apply_apply : symm e (e a) = a := by
  simp only [symm_apply_eq]

@[simp] theorem apply_symm_apply : e (symm e b) = b := by
  rw [← eq_symm_apply (F := F)]

@[simp] theorem symm_injective : Function.Injective (symm : E → F) := fun _ _ => by
  rw [DFunLike.ext'_iff, coe_symm, coe_symm]
  exact fun h => inv_injective h

theorem symm_symm_apply [Symm F E] : symm (symm e) a = e a := by
  simp only [symm_apply_eq, symm_apply_apply]

@[simp] theorem symm_symm [Symm F E] (e : E) : symm (symm e) = e :=
  DFunLike.ext _ _ <| fun _ => symm_symm_apply

@[simp] theorem symm_bijective [Symm F E] : Function.Bijective (symm : E → F) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp] theorem symm_refl [EquivLike E α α] [Symm E E] [Refl E] :
    symm (refl : E) = (refl : E) :=
  DFunLike.ext _ _ <| fun _ => by simp only [symm_apply_eq, refl_apply]

theorem symm_trans_apply {E E' F F' G G'} [EquivLike E α β] [EquivLike E' β α]
    [EquivLike F β γ] [EquivLike F' γ β] [EquivLike G α γ]
    [EquivLike G' γ α] [Symm E E'] [Symm F F'] [Symm G G'] [Trans E F G]
    [Trans F' E' G'] {e : E} {f : F} {c : γ} :
    symm (trans e f) c = (symm e) (symm f c) := by
  simp only [trans_apply, symm_apply_eq, apply_symm_apply]

@[simp] theorem symm_trans {E E' F F' G G'} [EquivLike E α β] [EquivLike E' β α]
    [EquivLike F β γ] [EquivLike F' γ β] [EquivLike G α γ]
    [EquivLike G' γ α] [Symm E E'] [Symm F F'] [Symm G G'] [Trans E F G]
    [Trans F' E' G'] {e : E} {f : F} :
    symm (trans e f) = trans (symm f) (symm e) :=
  DFunLike.ext _ _ <| fun _ => by simp only [symm_trans_apply (F' := F') (E' := E'), trans_apply]

@[simp] theorem symm_trans_self {E E' F} [EquivLike E α β] [EquivLike E' β α]
    [EquivLike F β β] [Symm E E'] [Refl F] [Trans E' E F] {e : E} :
    trans (symm e) e = refl := DFunLike.ext _ _ <| fun _ => by
  simp only [trans_apply, apply_symm_apply, refl_apply]

@[simp] theorem self_trans_symm {E E' F} [EquivLike E α β] [EquivLike E' β α]
    [EquivLike F α α] [Symm E E'] [Refl F] [Trans E E' F] {e : E} :
    trans e (symm e) = refl := DFunLike.ext _ _ <| fun _ => by
  simp only [trans_apply, symm_apply_apply, refl_apply]

section

variable {p : α → Prop} {q : β → Prop} (e : E)

lemma forall_congr_left_symm : (∀ a, p a) ↔ ∀ b, p (symm e b) :=
  (forall_congr_left e).trans <| by simp

lemma forall_congr'_symm (h : ∀ b, p (symm e b) ↔ q b) : (∀ a, p a) ↔ ∀ b, q b :=
  forall_congr' e <| by simp [h]

lemma exists_congr_left_symm : (∃ a, p a) ↔ ∃ b, p (symm e b) :=
  (exists_congr_left e).trans <| by simp

lemma exists_congr'_symm (h : ∀ b, p (symm e b) ↔ q b) : (∃ a, p a) ↔ ∃ b, q b :=
  exists_congr' e <| by simp [h]

lemma existsUnique_congr_left_symm : (∃! a, p a) ↔ ∃! b, p (symm e b) :=
  (existsUnique_congr_left e).trans <| by simp

lemma existsUnique_congr'_symm (h : ∀ b, p (inv e b) ↔ q b) : (∃! a, p a) ↔ ∃! b, q b :=
  existsUnique_congr' e <| by simp [h]

end

end Symm

end EquivLike
