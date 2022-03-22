# Unicode in Lean

## What is Unicode?

If you want to understand how text encoding works on computers you should read these:
- https://www.joelonsoftware.com/2003/10/08/the-absolute-minimum-every-software-developer-absolutely-positively-must-know-about-unicode-and-character-sets-no-excuses/
- https://deliciousbrains.com/how-unicode-works/

## I TLDR'd those links

Fine, here is the minimal amount that you need to know:

- Computers store text as a stream of bits, but your computer needs to turn this stream into patterns of pixels that you can read.
- The stream of bits is decoded into a stream of numbers. These numbers are called __code-points__. You write these numbers in hexadecimal like U+0041 which is the code-point for "A". `U+0048 U+0065 U+006C U+006C U+006F` is "Hello".
- The function from stream-of-bits to code-points is called the __character-encoding__. There are a few like `UTF-8`, `UTF-16` which can be seen in the status bar in vscode. You can usually ignore this, modern editors and libraries are good at getting the encoding right.
- There is a gigantic table of what each code-point should map to at https://unicode.org/charts. There is a code point for each emoji, for each letter and each squiggle in every conceivable alphabet and script that humans have ever used.
- A __typeface__ (aka __font__) is a map from these code points to little pictures (__glyphs__) that can be put next to each other and rendered on a screen.
- The function `font → code points → image` is implemented by a piece of software called a [__text rendering library__](https://en.wikipedia.org/wiki/Category:Text_rendering_libraries). These are extremely difficult to write.
- When you write wacky stuff like `∈` in Lean, it is just a code-point (U+2208). That includes greek letters, superscripts, subscripts, integrals, sums, emoji etc.
- There is not a general way of writing subscript for any letter in unicode, there just happen to be some subscripted code-points like `ₐₑₒₓₔₕₖₗₘₙₚₛₜ` that we can take advantage of.
- [Mathematical Alphanumeric Symbols](http://www.unicode.org/charts/PDF/U1D400.pdf) like `ℙ` are _not_ in a different font. They have their own code points in unicode.

## Warnings!

There are some caveats in allowing unicode symbols to be a valid Lean identifiers:
- There are unicode characters that don't render to anything. Null characters.
- There are many different unicode characters for whitespace. Chart [U+2000](http://www.unicode.org/charts/PDF/U2000.pdf) has a lot of them.
- Some letter-like math glyphs (what the character looks like on a ) might look the same but have different unicode code points.
  Eg `ℝ` (U+211D) and `𝕉` (U+1D549). See [here](#letter-like-mathematical-symbols-in-unicode) for more detail.
- Some glyphs are different across typefaces or confusingly close to other glyphs. Square bullets in one typeface might be round in another. For example, all of the below are different code points and so will be treated differently by Lean:
  + `· • . ․ ‧ ⋅ ⬝ ∙ ● ⚫ ⬤ 🌑`.
  + `‣ ▶ ▸ ▸ ⯈ 🢒` (which one is transport `\t`?)
  + `⁃ ∎ ╸ ╹ ╺ ╻ ━ ■ ▪ ▬ ▮ ◼ ◾ ⬛ ⯀ 🔲`
  + `⋄ ◇ ◊ ♢ ✧ ⬦ ⬨ ⬫`.
- Some of the [Mathematical Alphanumeric Symbols](http://www.unicode.org/charts/PDF/U1D400.pdf) glyphs look the same as the ASCII symbols in some programming fonts. Lean refuses to accept a `.lean` file that uses some of these codepoints. Which is good.
- Some unicode characters (eg hebrew, arabic) _change the reading direction_ from left-to-right to right-to-left. If you try selecting the below code you will see that things are a little odd.
    ```
     ן א  נ ס ע ף פ ץ צ ק ר
    ```
    This mainly bites mathematicians when they try to define aleph-one in set theory.
    Do not use the aleph `א` at U+05D0. Use the aleph `ℵ` at U+2135 which is for mathematical use and doesn't change the reading direction.


Why is this a problem? Because it means the definitions of things can be obfuscated:
```lean
def A := true -- hide this line deep in another lean file.
def Α := false -- this is actually a capital alpha.
example : A := trivial -- Lean is inconsistent!?!?!? no.
```

This is a silly example but there are more subtle ones, like `|` (U+007c) vs `∣` (U+2223) which are both used in mathlib.

## Tangentially:

I can't resist listing some real world problems arising from unicode.
- Not all JSON is javascript because of unicode issues. http://timelessrepo.com/json-isnt-a-javascript-subset
- Some elaborate phishing schemes use invisible unicode glyphs in domain name to masquerade as other websites. https://www.plixer.com/blog/network-security/unicode-domain-phishing-attacks/
- There was a bug in how iOS renders indic scripts which caused the entire OS to crash. https://manishearth.github.io/blog/2018/02/15/picking-apart-the-crashing-ios-string/
- Some funny emoji related ones:
  + On Samsung phones, the rolling eyes emoji 🙄 rendered differently to other platforms: https://emojipedia.org/samsung/touchwiz-7.1/face-with-rolling-eyes/
  + https://techcrunch.com/2016/11/15/apple-brings-back-the-peach-butt-emoji/
- https://zalgo.org


## Issues with VSCode

There are some inconsistencies in how vscode vs Lean treat unicode.

- Lean doesn't recognise the carriage return `\r`, `U+000D` as a newline. VSCode does.
- Some unicode characters such as Mathematical 𝒮𝒸𝓇𝒾𝓅𝓉 and Mathematical 𝔉𝔯𝔞𝔨𝔱𝔲𝔯 have extra-long code points, so in UTF-8 and UTF-16, they are encoded as multiple words. The problem is that Lean gives highlight positions according to Unicode code points and VSCode does it by (16-bit?) words. So error messages can be off by one when these characters are used.


## A list of symbols used in Lean.

I am using the font [PragmataPro](https://www.fsd.it/shop/fonts/pragmatapro/?attribute_weights=PragmataPro+Regular+with+PP+Mono+Regular&attribute_license-for=desktop).
In which all of the below symbols are rendered nicely and distinguishably.
I like PragmataPro because it keeps to the letter grid even with the more obscure symbols. It also gives two characters of space to arrows (`→`) so things look less cramped. The bad news is you have to pay for this font.


## Letters
You already know about letters.
```
 A B C D E F G H I J K L M N O P Q R S T U V W X Y Z
 a b c d e f g h i j k l m n o p q r s t u v w x y z
 0 1 2 3 4 5 6 7 8 9
```
### Greek
I've removed the letters which clash with latin letters.
```
 Γ Δ Θ Λ Ξ Π Σ Υ Φ Ψ Ω
 α β γ δ ε ζ η θ ι κ λ μ ν ξ π ρ ς σ τ υ φ χ ψ ω
 ∂   ϑ ϰ ϕ ϱ ϖ
```
## Letter-like mathematical symbols in unicode.
The unicode standard messes up how it codes mathematical symbols. This is because there are two charts:
- [Letterlike Symbols](http://www.unicode.org/charts/PDF/U2100.pdf) `U+2100-214F`
- [Mathematical Alphanumeric Symbols](http://www.unicode.org/charts/PDF/U1D400.pdf) `U+1D400–1D7FF`

Some characters such as what we would write as `\mathbb{R}` in LaTeX, appear in both of these charts. Both U+211D (`ℝ`) and U+1D549 (`𝕉`) look like the symbol we use for the reals but are actually distinct unicode characters and so Lean will treat them differently. The actual unicode chart says U+1D549 is blank but many fonts render it to look like the U+211D. I think the convention is to use the U+2100-214F chart unless it doesn't have your character, and then use the U+1D400–1D7FF chart.
### The 'letterlike symbols`
```
U+2100  ℀ ℁ ℂ ℃ ℄ ℅ ℆ ℇ ℈ ℉ ℊ ℋ ℌ ℍ ℎ ℏ
U+2110  ℐ ℑ ℒ ℓ ℔ ℕ № ℗ ℘ ℙ ℚ ℛ ℜ ℝ ℞ ℟
U+2120  ℠ ℡ ™ ℣ ℤ ℥ Ω ℧ ℨ ℩ K Å ℬ ℭ ℮ ℯ
U+2130  ℰ ℱ Ⅎ ℳ ℴ ℵ ℶ ℷ ℸ ℹ ℺ ℻ ℼ ℽ ℾ ℿ
U+2140  ⅀ ⅁ ⅂ ⅃ ⅄ ⅅ ⅆ ⅇ ⅈ ⅉ ⅊ ⅋ ⅌ ⅍ ⅎ ⅏
```
## Chart __1D400–1D7FF__
All of the following characters are exclusively in the `U+1D400–1D7FF` chart. I have omitted the characters that are not allowed in Lean or which are already present on the letterlike symbols chart.
I have also omitted characters that clash with the `letterlike symbols` chart.
<!--
### Mathematical Bold
[WARNING] These are not in Lean yet.
```
 𝐀 𝐁 𝐂 𝐃 𝐄 𝐅 𝐆 𝐇 𝐈 𝐉 𝐊 𝐋 𝐌 𝐍 𝐎 𝐏 𝐐 𝐑 𝐒 𝐓 𝐔 𝐕 𝐖 𝐗 𝐘 𝐙
 𝐚 𝐛 𝐜 𝐝 𝐞 𝐟 𝐠 𝐡 𝐢 𝐣 𝐤 𝐥 𝐦 𝐧 𝐨 𝐩 𝐪 𝐫 𝐬 𝐭 𝐮 𝐯 𝐰 𝐱 𝐲 𝐳
 𝟎 𝟏 𝟐 𝟑 𝟒 𝟓 𝟔 𝟕 𝟖 𝟗
```
### Mathematical Italic
[WARNING] These are not in Lean yet.
```
 𝐴 𝐵 𝐶 𝐷 𝐸 𝐹 𝐺 𝐻 𝐼 𝐽 𝐾 𝐿 𝑀 𝑁 𝑂 𝑃 𝑄 𝑅 𝑆 𝑇 𝑈 𝑉 𝑊 𝑋 𝑌 𝑍
 𝑎 𝑏 𝑐 𝑑 𝑒 𝑓 𝑔 𝑕 𝑖 𝑗 𝑘 𝑙 𝑚 𝑛 𝑜 𝑝 𝑞 𝑟 𝑠 𝑡 𝑢 𝑣 𝑤 𝑥 𝑦 𝑧
 𝛤 𝛥 𝛩 𝛬 𝛯 𝛱 𝛳 𝛴 𝛶 𝛷 𝛸 𝛹 𝛺 𝛻
 𝛼 𝛽 𝛾 𝛿 𝜀 𝜁 𝜂 𝜃 𝜄 𝜅 𝜆 𝜇 𝜈 𝜉 𝜋 𝜌 𝜍 𝜎 𝜏 𝜐 𝜑 𝜒 𝜓 𝜔
 𝜕 𝜖 𝜗 𝜘 𝜙 𝜚 𝜛
```
-->
### Mathematical Script
Type with `\McX`.
```
 𝒜   𝒞 𝒟     𝒢     𝒥 𝒦     𝒩 𝒪 𝒫 𝒬   𝒮 𝒯 𝒰 𝒱 𝒲 𝒳 𝒴 𝒵
 𝒶 𝒷 𝒸 𝒹   𝒻   𝒽 𝒾 𝒿 𝓀 𝓁 𝓂 𝓃   𝓅 𝓆 𝓇 𝓈 𝓉 𝓊 𝓋 𝓌 𝓍 𝓎 𝓏
```
I am omitting _Mathematical Bold Script_ because it looks too similar.
### Mathematical Fraktur
Type with `\MfX`.
```
 𝔄 𝔅   𝔇 𝔈 𝔉 𝔊     𝔍 𝔎 𝔏 𝔐 𝔑 𝔒 𝔓 𝔔   𝔖 𝔗 𝔘 𝔙 𝔚 𝔛 𝔜
 𝔞 𝔟 𝔠 𝔡 𝔢 𝔣 𝔤 𝔥 𝔦 𝔧 𝔨 𝔩 𝔪 𝔫 𝔬 𝔭 𝔮 𝔯 𝔰 𝔱 𝔲 𝔳 𝔴 𝔵 𝔶 𝔷
```
I am omitting _Mathematical Bold Fraktur_ because it looks too similar.
### Mathematical Double-Struck
Type with `\bbX`.
```
 𝔸 𝔹   𝔻 𝔼 𝔽 𝔾   𝕀 𝕁 𝕂 𝕃 𝕄   𝕆       𝕊 𝕋 𝕌 𝕍 𝕎 𝕏 𝕐
 𝕒 𝕓 𝕔 𝕕 𝕖 𝕗 𝕘 𝕙 𝕚 𝕛 𝕜 𝕝 𝕞 𝕟 𝕠 𝕡 𝕢 𝕣 𝕤 𝕥 𝕦 𝕧 𝕨 𝕩 𝕪 𝕫
 𝟘 𝟙 𝟚 𝟛 𝟜 𝟝 𝟞 𝟟 𝟠 𝟡
```

## Accents and so on.

I am mostly against decorating letters with accents so I am not in a rush to fill out this section. There are also many Unicode caveats. For example:

- `ë` is `U+00EB` (Latin)
- `ё` is `U+0450` (Cyrillic)
- `e̎` is `U+0065 U+0308` and uses a [combining diaeresis](https://www.unicode.org/charts/PDF/U0300.pdf). Sometimes the combining marks look nice and sometimes the font butchers them.

It's an absolute minefield.

## Subscripts and superscripts
Note that these are just unicode characters

```
¹ ² ³
U+2070  ⁰ ⁱ   ⁴ ⁵ ⁶ ⁷ ⁸ ⁹ ⁺ ⁻ ⁼ ⁽ ⁾ ⁿ
U+2080  ₀ ₁ ₂ ₃ ₄ ₅ ₆ ₇ ₈ ₉ ₊ ₋ ₌ ₍ ₎
U+2090  ₐ ₑ ₒ ₓ ₔ ₕ ₖ ₗ ₘ ₙ ₚ ₛ ₜ
```

There are also some superscripts in "Phoenetic Extensions". These are used to make the `ᵒᵖ` superscript.

```
 U+1D20  ᴠ ᴡ ᴢ ᴣ ᴤ ᴥ ᴦ ᴧ ᴨ ᴩ ᴪ ᴫ ᴬ ᴭ ᴮ ᴯ
 U+1D30  ᴰ ᴱ ᴲ ᴳ ᴴ ᴵ ᴶ ᴷ ᴸ ᴹ ᴺ ᴻ ᴼ ᴽ ᴾ ᴿ
 U+1D40  ᵀ ᵁ ᵂ ᵃ ᵄ ᵅ ᵆ ᵇ ᵈ ᵉ ᵊ ᵋ ᵌ ᵍ ᵎ ᵏ
 U+1D50  ᵐ ᵑ ᵒ ᵓ ᵔ ᵕ ᵖ ᵗ ᵘ ᵙ ᵚ ᵛ ᵜ ᵝ ᵞ ᵟ
 U+1D60  ᵠ ᵡ ᵢ ᵣ ᵤ ᵥ ᵦ ᵧ ᵨ ᵩ ᵪ ᵫ ᵬ ᵭ ᵮ ᵯ
 U+1D70  ᵰ ᵱ ᵲ ᵳ ᵴ ᵵ ᵶ ᵷ ᵸ ᵹ ᵺ ᵻ ᵼ ᵽ ᵾ ᵿ
```


## Brackets
```
( ) [ ] { }
⦃ ⦄ ⟦ ⟧ ⟨ ⟩ ⟪ ⟫
‹ › « »
⁅ ⁆ ⌈ ⌉ ⌊ ⌋ ⌜ ⌝ ⌞ ⌟
```
These don't have completions but I like them:
```
⟮ ⟯ ⟬ ⟭
⦋ ⦌ ⦍ ⦎ ⦏ ⦐
⦉ ⦊ ⦅ ⦆ ⦇ ⦈ ⨴ ⨵
```

## Symbols
```
∀ ∂ ∃ ∄ ∅ ∝ ∞ √ ∛ ∜ ∫ ∮ ∱ ∲ ∳ ∓ ± ∆ ∇
```
### big ops
```
⋀ ⋁ ⋂ ⋃ ⨅ ⨆ ∏ ∐ ∑ ⨁ ⨂ ⨀
```
### products
```
∗ ∘ ∙ ⋄ ⋅ ⋆ ⋇ ⋈ ※
⊍ ⊎
⊕ ⊖ ⊗ ⊘ ⊙ ⊚ ⊛ ⊜ ⊝
⊞ ⊟ ⊠ ⊡
∴ ∵ ⁖ ⋮ ⋯ ⁘ ⁙
```


### relations
```
< > ≤ ≥ ≮ ≯ ≰ ≱ ∧ ∨
≺ ≻ ≼ ≽ ⊀ ⊁     ⋏ ⋎
⊂ ⊃ ⊆ ⊇ ⊄ ⊅ ⊈ ⊉ ∩ ∪
∈ ∋     ∉ ∌
⊲ ⊳ ⊴ ⊵
⊏ ⊐ ⊑ ⊒         ⊓ ⊔
⋐⋑            ⋒⋓

≃ ≄ ≅ ≇ ≈ ≉ ≊ ≋ ≍ ≎ ≏ ≐ ≑ ≒ ≓
≖ ≗ ≘ ≙ ≚ ≛ ≜ ≝ ≞ ≟ ≠ ≡ ≢ ≣
≪ ≫ ⋘ ⋙
⊢ ⊣ ⊤ ⊥ ⊦ ⊧ ⊨ ⊩ ⊪ ⊫
```
## arrows
```
← ↑ → ↓ ↔ ↕ ⟵ ⟶ ⟷
⇐ ⇑ ⇒ ⇓ ⇔ ⇕ ⟸ ⟹ ⟺
↤ ↥ ↦ ↧      ⟻ ⟼
⇜   ⇝   ↭   ⬳ ⟿
↞ ↟ ↠ ↡
↜   ↝
↢   ↣
⇇ ⇈ ⇉ ⇊
⇚ ⟰ ⇛ ⟱

↫ ↬ ↩ ↪ ↯ ↺ ↻ ⇶
```
### arrows with evil twins
I stipulate using these:
```
↼ ↾ ⇀ ⇂
⇄ ⇅
⇋ ⥮
```
And avoiding these:
```
↽ ↿ ⇁ ⇃
⇆ ⇵
⇌ ⥯
```
### arrows with no completions
```
⤆   ⤇        ⟽ ⟾
⇠ ⇡ ⇢ ⇣
⇦ ⇧ ⇨ ⇩ ⬄ ⇳
⬅ ⬆ ⮕ ⬇ ⬌ ⬍
⇤ ⤒ ⇥ ⤓
⇷ ⤉ ⇸ ⤈ ⇹
⇺ ⇞ ⇻ ⇟ ⇼
⤺   ⤻ ⤸
⇴ ⟴
```

## Emoji

Emoji are not allowed as identifiers. Maybe one day we will be able to finish off a lemma with `show 🤯, by 💩 💥`. But today is not that day.
