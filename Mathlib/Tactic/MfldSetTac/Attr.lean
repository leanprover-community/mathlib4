import Lean

open Lean Meta

initialize mfldSetTacExt : SimpExtension ←
  registerSimpAttr `mfld_simps (extName := `Tactic.MfldSetTac.mfldSetTacExt) $
    "The simpset `mfld_simps` records several simp lemmas that are
especially useful in manifolds. It is a subset of the whole set of simp lemmas, but it makes it
possible to have quicker proofs (when used with `squeeze_simp` or `simp only`) while retaining
readability.
The typical use case is the following, in a file on manifolds:
If `simp [foo, bar]` is slow, replace it with `squeeze_simp [foo, bar, mfld_simps]` and paste
its output. The list of lemmas should be reasonable (contrary to the output of
`squeeze_simp [foo, bar]` which might contain tens of lemmas), and the outcome should be quick
enough.
"

namespace Attr
syntax (name := mfldSetTacAttr) "mfld_simps" : attr
end Attr

initialize registerBuiltinAttribute {
  name := `mfldSetTacAttr
  descr := "attribute for mfld_set_tac"
  add := fun decl _stx kind => MetaM.run' $
          addSimpTheorem mfldSetTacExt decl (post := true) (inv := false) kind (eval_prio default)
}
