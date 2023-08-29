/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathlib.Algebra.Hom.Equiv.Basic
import Mathlib.Algebra.Group.TypeTags

#align_import algebra.hom.equiv.type_tags from "leanprover-community/mathlib"@"3342d1b2178381196f818146ff79bc0e7ccd9e2d"

/-!
# Additive and multiplicative equivalences associated to `Multiplicative` and `Additive`.
-/


variable {G H : Type*}

/-- Reinterpret `G ≃+ H` as `Multiplicative G ≃* Multiplicative H`. -/
def AddEquiv.toMultiplicative [AddZeroClass G] [AddZeroClass H] :
    G ≃+ H ≃ (Multiplicative G ≃* Multiplicative H) where
  toFun f :=
    ⟨⟨AddMonoidHom.toMultiplicative f.toAddMonoidHom,
     AddMonoidHom.toMultiplicative f.symm.toAddMonoidHom, f.1.3, f.1.4⟩, f.2⟩
  invFun f := ⟨⟨f.toMonoidHom, f.symm.toMonoidHom, f.1.3, f.1.4⟩, f.2⟩
  left_inv x := by ext; rfl
                   -- ⊢ ↑((fun f => { toEquiv := { toFun := ↑(MulEquiv.toMonoidHom f), invFun := ↑(M …
                        -- 🎉 no goals
  right_inv x := by ext; rfl
                    -- ⊢ ↑((fun f => { toEquiv := { toFun := ↑(↑AddMonoidHom.toMultiplicative (toAddM …
                         -- 🎉 no goals
#align add_equiv.to_multiplicative AddEquiv.toMultiplicative

/-- Reinterpret `G ≃* H` as `Additive G ≃+ Additive H`. -/
def MulEquiv.toAdditive [MulOneClass G] [MulOneClass H] :
    G ≃* H ≃ (Additive G ≃+ Additive H) where
  toFun f := ⟨⟨MonoidHom.toAdditive f.toMonoidHom,
              MonoidHom.toAdditive f.symm.toMonoidHom, f.1.3, f.1.4⟩, f.2⟩
  invFun f := ⟨⟨f.toAddMonoidHom, f.symm.toAddMonoidHom, f.1.3, f.1.4⟩, f.2⟩
  left_inv x := by ext; rfl
                   -- ⊢ ↑((fun f => { toEquiv := { toFun := ↑(AddEquiv.toAddMonoidHom f), invFun :=  …
                        -- 🎉 no goals
  right_inv x := by ext; rfl
                    -- ⊢ ↑((fun f => { toEquiv := { toFun := ↑(↑MonoidHom.toAdditive (toMonoidHom f)) …
                         -- 🎉 no goals
#align mul_equiv.to_additive MulEquiv.toAdditive

/-- Reinterpret `Additive G ≃+ H` as `G ≃* Multiplicative H`. -/
def AddEquiv.toMultiplicative' [MulOneClass G] [AddZeroClass H] :
    Additive G ≃+ H ≃ (G ≃* Multiplicative H) where
  toFun f :=
    ⟨⟨AddMonoidHom.toMultiplicative' f.toAddMonoidHom,
     AddMonoidHom.toMultiplicative'' f.symm.toAddMonoidHom, f.1.3, f.1.4⟩, f.2⟩
  invFun f := ⟨⟨f.toMonoidHom, f.symm.toMonoidHom, f.1.3, f.1.4⟩, f.2⟩
  left_inv x := by ext; rfl
                   -- ⊢ ↑((fun f => { toEquiv := { toFun := ↑(MulEquiv.toMonoidHom f), invFun := ↑(M …
                        -- 🎉 no goals
  right_inv x := by ext; rfl
                    -- ⊢ ↑((fun f => { toEquiv := { toFun := ↑(↑AddMonoidHom.toMultiplicative' (toAdd …
                         -- 🎉 no goals
#align add_equiv.to_multiplicative' AddEquiv.toMultiplicative'

/-- Reinterpret `G ≃* Multiplicative H` as `Additive G ≃+ H` as. -/
def MulEquiv.toAdditive' [MulOneClass G] [AddZeroClass H] :
    G ≃* Multiplicative H ≃ (Additive G ≃+ H) :=
  AddEquiv.toMultiplicative'.symm
#align mul_equiv.to_additive' MulEquiv.toAdditive'

/-- Reinterpret `G ≃+ Additive H` as `Multiplicative G ≃* H`. -/
def AddEquiv.toMultiplicative'' [AddZeroClass G] [MulOneClass H] :
    G ≃+ Additive H ≃ (Multiplicative G ≃* H) where
  toFun f :=
    ⟨⟨AddMonoidHom.toMultiplicative'' f.toAddMonoidHom,
     AddMonoidHom.toMultiplicative' f.symm.toAddMonoidHom, f.1.3, f.1.4⟩, f.2⟩
  invFun f := ⟨⟨f.toMonoidHom, f.symm.toMonoidHom, f.1.3, f.1.4⟩, f.2⟩
  left_inv x := by ext; rfl
                   -- ⊢ ↑((fun f => { toEquiv := { toFun := ↑(MulEquiv.toMonoidHom f), invFun := ↑(M …
                        -- 🎉 no goals
  right_inv x := by ext; rfl
                    -- ⊢ ↑((fun f => { toEquiv := { toFun := ↑(↑AddMonoidHom.toMultiplicative'' (toAd …
                         -- 🎉 no goals
#align add_equiv.to_multiplicative'' AddEquiv.toMultiplicative''

/-- Reinterpret `Multiplicative G ≃* H` as `G ≃+ Additive H` as. -/
def MulEquiv.toAdditive'' [AddZeroClass G] [MulOneClass H] :
    Multiplicative G ≃* H ≃ (G ≃+ Additive H) :=
  AddEquiv.toMultiplicative''.symm
#align mul_equiv.to_additive'' MulEquiv.toAdditive''

section

variable (G) (H)

/-- `Additive (Multiplicative G)` is just `G`. -/
def AddEquiv.additiveMultiplicative [AddZeroClass G] : Additive (Multiplicative G) ≃+ G :=
  MulEquiv.toAdditive' (MulEquiv.refl (Multiplicative G))
#align add_equiv.additive_multiplicative AddEquiv.additiveMultiplicative

/-- `Multiplicative (Additive H)` is just `H`. -/
def MulEquiv.multiplicativeAdditive [MulOneClass H] : Multiplicative (Additive H) ≃* H :=
  AddEquiv.toMultiplicative'' (AddEquiv.refl (Additive H))
#align mul_equiv.multiplicative_additive MulEquiv.multiplicativeAdditive

end
