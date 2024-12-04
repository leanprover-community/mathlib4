/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Operations on elements in a concrete category

-/

universe w v u v' u'

namespace CategoryTheory

namespace Types

variable {D : Type u'} [Category.{v'} D]

@[simps]
def functorConcat (F₁ F₂ : D ⥤ Type w) : D ⥤ Type w where
  obj X := F₁.obj X × F₂.obj X
  map f a := ⟨F₁.map f a.1, F₂.map f a.2⟩

@[simps]
def functorPr₀ {F : D ⥤ Type w} : F ⟶ (Functor.const D).obj PUnit where
  app _ _ := PUnit.unit

@[simps]
def functorPr₁ {F₁ F₂ : D ⥤ Type w} : functorConcat F₁ F₂ ⟶ F₁ where
  app X a := a.1

@[simps]
def functorPr₂ {F₁ F₂ : D ⥤ Type w} : functorConcat F₁ F₂ ⟶ F₂ where
  app X a := a.2

@[simp]
def natTransConcat {F F₁ F₂ : D ⥤ Type w} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂) :
    F ⟶ functorConcat F₁ F₂ where
  app X a := ⟨τ₁.app X a, τ₂.app X a⟩
  naturality _ _ f := by
    ext x
    exact Prod.ext (congr_fun (τ₁.naturality f) x) (congr_fun (τ₂.naturality f) x)

@[simp]
def functorConcat₃ (F₁ F₂ F₃ : D ⥤ Type w) :=
  functorConcat F₁ (functorConcat F₂ F₃)

@[simps!]
def functorPr₃₁ {F₁ F₂ F₃ : D ⥤ Type w} : functorConcat₃ F₁ F₂ F₃ ⟶ F₁ := functorPr₁

@[simps!]
def functorPr₃₂ {F₁ F₂ F₃ : D ⥤ Type w} : functorConcat₃ F₁ F₂ F₃ ⟶ F₂ :=
  functorPr₂ ≫ functorPr₁

@[simps!]
def functorPr₃₃ {F₁ F₂ F₃ : D ⥤ Type w} : functorConcat₃ F₁ F₂ F₃ ⟶ F₃ :=
  functorPr₂ ≫ functorPr₂

@[simp]
def natTransConcat₃ {F F₁ F₂ F₃ : D ⥤ Type w} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂) (τ₃ : F ⟶ F₃) :
    F ⟶ functorConcat₃ F₁ F₂ F₃ :=
  natTransConcat τ₁ (natTransConcat τ₂ τ₃)

def functorOperation₀ (F : D ⥤ Type w) := (Functor.const D).obj PUnit ⟶ F
def functorOperation₁ (F : D ⥤ Type w) := F ⟶ F
def functorOperation₂ (F : D ⥤ Type w) := functorConcat F F ⟶ F
def functorOperation₃ (F : D ⥤ Type w) := functorConcat₃ F F F ⟶ F

@[simp]
def functorOperation₀.of_iso {F₁ F₂ : D ⥤ Type w} (h : functorOperation₀ F₁)
  (e : F₁ ≅ F₂) : functorOperation₀ F₂ := h ≫ e.hom

def functorOperation₀.equiv_of_iso {F₁ F₂ : D ⥤ Type w} (e : F₁ ≅ F₂) :
  functorOperation₀ F₁ ≃ functorOperation₀ F₂ where
  toFun h := h.of_iso e
  invFun h := h.of_iso e.symm
  left_inv h := by simp
  right_inv h := by simp

@[simp]
def functorOperation₁.of_iso {F₁ F₂ : D ⥤ Type w} (h : functorOperation₁ F₁)
  (e : F₁ ≅ F₂) : functorOperation₁ F₂ := e.inv ≫ h ≫ e.hom

def functorOperation₁.equiv_of_iso {F₁ F₂ : D ⥤ Type w} (e : F₁ ≅ F₂) :
  functorOperation₁ F₁ ≃ functorOperation₁ F₂ where
  toFun h := h.of_iso e
  invFun h := h.of_iso e.symm
  left_inv h := by simp
  right_inv h := by simp

@[simp]
def functorOperation₂.of_iso {F₁ F₂ : D ⥤ Type w} (h : functorOperation₂ F₁)
    (e : F₁ ≅ F₂) : functorOperation₂ F₂ :=
  natTransConcat (functorPr₁ ≫ e.inv) (functorPr₂ ≫ e.inv) ≫ h ≫ e.hom

def functorOperation₂.equiv_of_iso {F₁ F₂ : D ⥤ Type w} (e : F₁ ≅ F₂) :
  functorOperation₂ F₁ ≃ functorOperation₂ F₂ where
  toFun h := h.of_iso e
  invFun h := h.of_iso e.symm
  left_inv h := by
    apply NatTrans.ext
    ext1 X
    funext
    simp
  right_inv h := by
    apply NatTrans.ext
    ext1 X
    funext
    simp

@[simp]
def functorOperation₂.swap {F : D ⥤ Type w} (h : functorOperation₂ F) :
  functorOperation₂ F := natTransConcat functorPr₂ functorPr₁ ≫ h

@[simp]
def functorOperation₃.of_iso {F₁ F₂ : D ⥤ Type w} (h : functorOperation₃ F₁)
    (e : F₁ ≅ F₂) : functorOperation₃ F₂ :=
  natTransConcat₃ (functorPr₃₁ ≫ e.inv) (functorPr₃₂ ≫ e.inv) (functorPr₃₃ ≫ e.inv) ≫
    h ≫ e.hom

def functorOperation₃.equiv_of_iso {F₁ F₂ : D ⥤ Type w} (e : F₁ ≅ F₂) :
  functorOperation₃ F₁ ≃ functorOperation₃ F₂ where
  toFun h := h.of_iso e
  invFun h := h.of_iso e.symm
  left_inv h := by
    apply NatTrans.ext
    ext1 X
    funext
    simp
  right_inv h := by
    apply NatTrans.ext
    ext1 X
    funext
    simp

section

variable {X₁ X₂ X₃ X₁₂ X₂₃ X₁₂₃ : D ⥤ Type w}
  (φ₁₂ : functorConcat X₁ X₂ ⟶ X₁₂) (ψ₁₂ : functorConcat X₁₂ X₃ ⟶ X₁₂₃)
  (φ₂₃ : functorConcat X₂ X₃ ⟶ X₂₃) (ψ₂₃ : functorConcat X₁ X₂₃ ⟶ X₁₂₃)

/-- Associativity -/
def functorOperation_assoc' : Prop :=
  Types.natTransConcat (Types.natTransConcat Types.functorPr₃₁ Types.functorPr₃₂ ≫ φ₁₂)
    Types.functorPr₃₃ ≫ ψ₁₂ =
  Types.natTransConcat Types.functorPr₃₁
    (Types.natTransConcat Types.functorPr₃₂ Types.functorPr₃₃ ≫ φ₂₃) ≫ ψ₂₃

def functorOperation₂.assoc {F : D ⥤ Type w} (oper : functorOperation₂ F) : Prop :=
  functorOperation_assoc' oper oper oper oper

lemma functorOperation₂.assoc.of_iso {F₁ F₂ : D ⥤ Type w} {oper : functorOperation₂ F₁}
    (h : oper.assoc) (e : F₁ ≅ F₂) : (oper.of_iso e).assoc := by
  refine Eq.trans ?_ ((congr_arg (fun (o : functorOperation₃ F₁) => o.of_iso e) h).trans ?_)
  all_goals
    apply NatTrans.ext
    ext1 X
    funext ⟨a, b, c⟩
    dsimp
    simp

end

section

variable {X Y : D ⥤ Type w}
  (add : functorConcat X Y ⟶ Y)
  (zero : functorOperation₀ X)

/-- zero_add -/
def functorOperation_zero_add' : Prop :=
  (natTransConcat (Types.functorPr₀ ≫ zero) (𝟙 Y)) ≫ add = 𝟙 Y

def functorOperation₂.zero_add (add : functorOperation₂ Y) (zero : functorOperation₀ Y) : Prop :=
  functorOperation_zero_add' add zero

lemma functorOperation₂.zero_add.of_iso {F₁ F₂ : D ⥤ Type w} {add : functorOperation₂ F₁}
  {zero : functorOperation₀ F₁} (h : add.zero_add zero) (e : F₁ ≅ F₂) :
  (add.of_iso e).zero_add (zero.of_iso e) := by
  refine Eq.trans ?_ ((congr_arg (fun (o : functorOperation₁ F₁) => o.of_iso e) h).trans ?_)
  all_goals
    apply NatTrans.ext
    ext1
    funext
    dsimp
    simp

end

section

variable {X Y : D ⥤ Type w}
  (add : functorConcat Y X ⟶ Y)
  (zero : functorOperation₀ X)

/-- add_zero -/
def functorOperation_add_zero' : Prop :=
  (natTransConcat (𝟙 Y) (Types.functorPr₀ ≫ zero)) ≫ add = 𝟙 Y

def functorOperation₂.add_zero (add : functorOperation₂ Y) (zero : functorOperation₀ Y) : Prop :=
  functorOperation_add_zero' add zero

lemma functorOperation₂.add_zero.of_iso {F₁ F₂ : D ⥤ Type w} {add : functorOperation₂ F₁}
  {zero : functorOperation₀ F₁} (h : add.add_zero zero) (e : F₁ ≅ F₂) :
  (add.of_iso e).add_zero (zero.of_iso e) := by
  refine Eq.trans ?_ ((congr_arg (fun (o : functorOperation₁ F₁) => o.of_iso e) h).trans ?_)
  all_goals
    apply NatTrans.ext
    ext1
    funext
    dsimp
    simp

end

section

variable {F : D ⥤ Type w} (add : functorOperation₂ F)

def functorOperation₂.comm : Prop := add = add.swap

lemma functorOperation₂.comm.of_iso {F₁ F₂ : D ⥤ Type w} {add : functorOperation₂ F₁}
  (h : add.comm) (e : F₁ ≅ F₂) : (add.of_iso e).comm :=
  congr_arg (fun (o : functorOperation₂ F₁) => o.of_iso e) h

end

section

variable {F : D ⥤ Type w} (add : functorOperation₂ F)
  (neg : functorOperation₁ F) (zero : functorOperation₀ F)

def functorOperation₂.add_left_neg : Prop :=
  natTransConcat neg (𝟙 _) ≫ add = functorPr₀ ≫ zero

lemma functorOperation₂.add_left_neg.of_iso {F₁ F₂ : D ⥤ Type w} {add : functorOperation₂ F₁}
    {neg : functorOperation₁ F₁} {zero : functorOperation₀ F₁}
    (h : add.add_left_neg neg zero) (e : F₁ ≅ F₂) :
    (add.of_iso e).add_left_neg (neg.of_iso e) (zero.of_iso e) := by
  refine Eq.trans ?_ (congr_arg (fun (o : functorOperation₁ F₁) => o.of_iso e) h)
  apply NatTrans.ext
  ext1
  funext
  dsimp
  simp

end

end Types

variable (A : Type u) [Category.{v} A] [ConcreteCategory.{w} A]

namespace ConcreteCategory

def Operation₀ := (Functor.const A).obj PUnit ⟶ forget A
def Operation₁ := forget A ⟶ forget A
def Operation₂ := Types.functorConcat (forget A) (forget A) ⟶ forget A
def Operation₃ := Types.functorConcat (forget A)
  (Types.functorConcat (forget A) (forget A)) ⟶ forget A

namespace Operation₂

variable {A}
variable (oper : Operation₂ A)

@[simp]
def assoc : Prop := Types.functorOperation₂.assoc oper

@[simp]
def zero_add (zero : Operation₀ A) : Prop := Types.functorOperation₂.zero_add oper zero

@[simp]
def add_zero (zero : Operation₀ A) : Prop := Types.functorOperation₂.add_zero oper zero

@[simp]
def comm : Prop := Types.functorOperation₂.comm oper

@[simp]
def add_left_neg (neg : Operation₁ A) (zero : Operation₀ A) : Prop :=
  Types.functorOperation₂.add_left_neg oper neg zero

end Operation₂

-- the naturality of these operations should be made automatic...

@[simps]
def addCommGroupCat_zero : Operation₀ Ab.{u} where
  app M _ := (0 : M)

@[simps]
def addCommGroupCat_neg : Operation₁ Ab.{u} where
  app M (x : M) := -x

@[simps]
def addCommGroupCat_add : Operation₂ Ab.{u} where
  app M := fun ⟨(x : M), (y : M)⟩ => x + y

lemma addCommGroupCat_add_assoc : addCommGroupCat_add.assoc := by
  apply NatTrans.ext
  ext1 X
  funext ⟨(x : X), ⟨(y : X), (z : X)⟩⟩
  exact add_assoc x y z

lemma addCommGroupCat_add_zero : addCommGroupCat_add.add_zero addCommGroupCat_zero := by
  apply NatTrans.ext
  ext1 X
  funext (x : X)
  exact add_zero x

lemma addCommGroupCat_zero_add : addCommGroupCat_add.zero_add addCommGroupCat_zero := by
  apply NatTrans.ext
  ext1 X
  funext (x : X)
  exact zero_add x

lemma addCommGroupCat_add_comm : addCommGroupCat_add.comm := by
  apply NatTrans.ext
  ext1 X
  funext ⟨(x : X), (y : X)⟩
  exact add_comm x y

lemma addCommGroupCat_add_left_neg : addCommGroupCat_add.add_left_neg
    addCommGroupCat_neg addCommGroupCat_zero := by
  apply NatTrans.ext
  ext1 X
  funext (x : X)
  exact neg_add_cancel x

end ConcreteCategory

end CategoryTheory
