import ProofWidgets
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.SelectionPanel
import ProofWidgets.Component.GoalTypePanel

/-!

# In-progress experimentation for rendering LaTeX

This branch is for experimentation only.

We've got two ways to render math available to us:
- MathJax
- KaTeX

We put the local copies of MathJax and KaTeX at the top level. (This is not how we'd want to actually do things! Quick access for demo purposes only.)
-/

open ProofWidgets Jsx

/- Basic props -/

structure NoProps
#mkrpcenc NoProps

structure TextProps where
  text : String
#mkrpcenc TextProps

structure TeXProps extends TextProps where
  display : Bool := false
#mkrpcenc TeXProps

