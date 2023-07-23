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


/- # MathJax

We switch between MathJax for SVG and MathJax for CHTML for demo purposes. That means you may need to "click to reload" at certain points—a misclick can get the webview stuck in an errored state if it tries to e.g. find a function that doesn't exist on the current MathJax object.

We use the whole MathJax *source* directory, in case we want to try to modify it to get fonts to work.

The `mathjax/` directory here was obtained with
```
# clone source; would otherwise use https://github.com/mathjax/MathJax.git
git clone https://github.com/mathjax/MathJax-src.git mathjax

# build
cd mathjax
npm install
npm run compile
npm run make-components
cd ..
```
See [https://docs.mathjax.org/en/latest/web/hosting.html].

-/
