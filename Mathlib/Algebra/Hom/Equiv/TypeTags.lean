/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathbin.Algebra.Hom.Equiv.Basic
import Mathbin.Algebra.Group.TypeTags

/-!
# Additive and multiplicative equivalences associated to `multiplicative` and `additive`.
-/


variable {G H : Type _}

/-- Reinterpret `G ≃+ H` as `multiplicative G ≃* multiplicative H`. -/
def AddEquiv.toMultiplicative [AddZeroClass G] [AddZeroClass H] :
    G ≃+ H ≃
      (Multiplicative G ≃*
        Multiplicative
          H) where 
  toFun f :=
    ⟨f.toAddMonoidHom.toMultiplicative, f.symm.toAddMonoidHom.toMultiplicative, f.3, f.4, f.5⟩
  invFun f := ⟨f.toMonoidHom, f.symm.toMonoidHom, f.3, f.4, f.5⟩
  left_inv x := by 
    ext
    rfl
  right_inv x := by 
    ext
    rfl
#align add_equiv.to_multiplicative AddEquiv.toMultiplicative

/-- Reinterpret `G ≃* H` as `additive G ≃+ additive H`. -/
def MulEquiv.toAdditive [MulOneClass G] [MulOneClass H] :
    G ≃* H ≃
      (Additive G ≃+
        Additive
          H) where 
  toFun f := ⟨f.toMonoidHom.toAdditive, f.symm.toMonoidHom.toAdditive, f.3, f.4, f.5⟩
  invFun f := ⟨f.toAddMonoidHom, f.symm.toAddMonoidHom, f.3, f.4, f.5⟩
  left_inv x := by 
    ext
    rfl
  right_inv x := by 
    ext
    rfl
#align mul_equiv.to_additive MulEquiv.toAdditive

/-- Reinterpret `additive G ≃+ H` as `G ≃* multiplicative H`. -/
def AddEquiv.toMultiplicative' [MulOneClass G] [AddZeroClass H] :
    Additive G ≃+ H ≃
      (G ≃*
        Multiplicative
          H) where 
  toFun f :=
    ⟨f.toAddMonoidHom.toMultiplicative', f.symm.toAddMonoidHom.toMultiplicative'', f.3, f.4, f.5⟩
  invFun f := ⟨f.toMonoidHom, f.symm.toMonoidHom, f.3, f.4, f.5⟩
  left_inv x := by 
    ext
    rfl
  right_inv x := by 
    ext
    rfl
#align add_equiv.to_multiplicative' AddEquiv.toMultiplicative'

/-- Reinterpret `G ≃* multiplicative H` as `additive G ≃+ H` as. -/
def MulEquiv.toAdditive' [MulOneClass G] [AddZeroClass H] :
    G ≃* Multiplicative H ≃ (Additive G ≃+ H) :=
  AddEquiv.toMultiplicative'.symm
#align mul_equiv.to_additive' MulEquiv.toAdditive'

/-- Reinterpret `G ≃+ additive H` as `multiplicative G ≃* H`. -/
def AddEquiv.toMultiplicative'' [AddZeroClass G] [MulOneClass H] :
    G ≃+ Additive H ≃
      (Multiplicative G ≃*
        H) where 
  toFun f :=
    ⟨f.toAddMonoidHom.toMultiplicative'', f.symm.toAddMonoidHom.toMultiplicative', f.3, f.4, f.5⟩
  invFun f := ⟨f.toMonoidHom, f.symm.toMonoidHom, f.3, f.4, f.5⟩
  left_inv x := by 
    ext
    rfl
  right_inv x := by 
    ext
    rfl
#align add_equiv.to_multiplicative'' AddEquiv.toMultiplicative''

/-- Reinterpret `multiplicative G ≃* H` as `G ≃+ additive H` as. -/
def MulEquiv.toAdditive'' [AddZeroClass G] [MulOneClass H] :
    Multiplicative G ≃* H ≃ (G ≃+ Additive H) :=
  AddEquiv.toMultiplicative''.symm
#align mul_equiv.to_additive'' MulEquiv.toAdditive''

section

variable (G) (H)

/-- `additive (multiplicative G)` is just `G`. -/
def AddEquiv.additiveMultiplicative [AddZeroClass G] : Additive (Multiplicative G) ≃+ G :=
  MulEquiv.toAdditive'' (MulEquiv.refl (Multiplicative G))
#align add_equiv.additive_multiplicative AddEquiv.additiveMultiplicative

/-- `multiplicative (additive H)` is just `H`. -/
def MulEquiv.multiplicativeAdditive [MulOneClass H] : Multiplicative (Additive H) ≃* H :=
  AddEquiv.toMultiplicative'' (AddEquiv.refl (Additive H))
#align mul_equiv.multiplicative_additive MulEquiv.multiplicativeAdditive

end

