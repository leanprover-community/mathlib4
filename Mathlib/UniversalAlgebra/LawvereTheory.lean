import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Tactic

universe v u

inductive ProdWord (S : Type u) : Type u where
  | of : S → ProdWord S
  | prod : ProdWord S → ProdWord S → ProdWord S
  | nil : ProdWord S

inductive LawvereWord {S : Type u} (op : ProdWord S → S → Type v) :
    ProdWord S → ProdWord S → Type (max v u) where
  | of {P : ProdWord S} {T : S} (f : op P T) :
      LawvereWord op P (.of T)
  | id (P : ProdWord S) :
      LawvereWord op P P
  | comp {P Q R : ProdWord S} :
      LawvereWord op P Q →
      LawvereWord op Q R →
      LawvereWord op P R
  | fst (P Q : ProdWord S) :
      LawvereWord op (P.prod Q) P
  | snd (P Q : ProdWord S) :
      LawvereWord op (P.prod Q) Q
  | lift {T P Q : ProdWord S} :
      LawvereWord op T P →
      LawvereWord op T Q →
      LawvereWord op T (P.prod Q)
  | toNil (P : ProdWord S) :
      LawvereWord op P .nil

structure LawverePresentation (S : Type u) where
  op : ProdWord S → S → Type v
  rel : {P Q : ProdWord S} → LawvereWord op P Q → LawvereWord op P Q → Prop

open CategoryTheory Limits

structure LawvereTheory (S : Type u) where
  category : Category.{v} (ProdWord S)
  cone : (P Q : ProdWord S) → (Functor.const _).obj (P.prod Q) ⟶ (pair P Q)
  isLimit : (P Q : ProdWord S) → IsLimit ⟨P.prod Q, cone P Q⟩
  isTerminal : IsTerminal (ProdWord.nil : ProdWord S)

namespace LawvereTheory

end LawvereTheory
