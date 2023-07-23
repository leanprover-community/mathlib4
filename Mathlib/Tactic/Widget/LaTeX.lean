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

/- ## Setting up

Here, we simply run the bundled js to get the relevant MathJax object loaded.

There are two output types we try: SVG and CommonHTML. CommonHTML fails due to access issues when looking for the fonts.

We need to check if the MathJax object already exists and, since we want to easily switch between SVG MathJax and CHTML MathJax, delete it if it does—if we try to run the bundled JS when MathJax already exists, bad things (illegal setting operations) start to happen. (In the real world we could simply not do anything instead of deleting then reloading.)

We'd presumably *not* have this as a separate component in the real worls either, but it's useful for experimenting so that the javascript of subsequent components is easier to read.
-/

/- ### SVG -/
@[widget_module]
def AddMathJaxSVG : Component NoProps where
  javascript := "
    export default function (){
      if (typeof window?.MathJax !== 'undefined') {
        delete window['MathJax']
      }" ++
      (include_str ".." / ".." / ".." / "mathjax" / "es5" / "tex-svg.js") ++ "
    }"

/- ### CommonHTML -/
@[widget_module]
def AddMathJaxCHTML : Component NoProps where
  javascript := "
    export default function (){
      if (typeof window?.MathJax !== 'undefined') {
        delete window['MathJax']
      }" ++
      (include_str ".." / ".." / ".." / "mathjax" / "es5" / "tex-chtml.js") ++ "
    }"

/- ## Rendering

There are three ways to render typesetting in MathJax: with `MathJax.typeset()`, `MathJax.typesetPromise()`, and by producing HTMLElements with converters.

-/

/- ### Using converters

There are probably better ways to use an HTMLElement than via `dangerouslySetInnerHTML`, but it at least lets us see some math! I'm going to look into using a ref next.
-/

/- __SVG via dangerouslySetInnerHTML__
Hacky but works just fine in this limited context. Proof-of-concept.
-/
@[widget_module]
def DangerousMathJaxSVG : Component TeXProps where
  javascript := "
    import * as React from 'react'
    export default function(props) {
      if (typeof window?.MathJax !== 'undefined') {
        const html = window.MathJax.tex2svg(props.text, {display:props.display}).outerHTML
        return React.createElement('span', {dangerouslySetInnerHTML:{__html:html}}) }}"

#html <AddMathJaxSVG /> -- evaluate first
#html <DangerousMathJaxSVG text="\\int_0^\\infty t^{z-1}e^{-t}\\;dt" display={true} />

