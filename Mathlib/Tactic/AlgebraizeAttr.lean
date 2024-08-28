import Lean.Attributes

namespace Lean.Attr

-- TODO: should be ParametricAttribute + should write a function that gets the name
initialize algebraizeAttr : TagAttribute ← registerTagAttribute `algebraize "algebraize"

def algebraizeGetParam (thm : Name) (stx : Syntax) : AttrM Name := do
  match stx with
  | `(attr| algebraize2 $name:ident) => return name.getId
  -- TODO: deal with this case! Then if name is "RingHom.FiniteType" ---> "Algebra.FiniteType.mk"
  | `(attr| algebraize2) => throwError "algebraize requires an argument"
  | _ => throwError "unexpected algebraize argument"

initialize algebraize2Attr : ParametricAttribute Name ←
  registerParametricAttribute {
    name := `algebraize2,
    descr := "TODO",
    getParam := algebraizeGetParam }
