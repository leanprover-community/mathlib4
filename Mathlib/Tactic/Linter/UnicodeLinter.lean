/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka, Jon Eugster
-/

import Mathlib.Init

/-!

# Tools for Unicode Linter

The actual linter is defined in `TextBased.lean`.

This file provides all white-lists and other tools used by the linter.

## Main declarations

* `emojis`, `nonEmojis`: characters in these lists should always be followed by
  the correct variant-selector `UnicodeVariant.emoji` or `UnicodeVariant.text`.
  These variant-selector should not appear anywhere else.
* `withVSCodeAbbrev`: unicode characters for which the Lean extension provides a shortcut
* `othersInMathlib`: unicode characters in Mathlib without an abbreviation.
  Ideally, this list will slowly be reduced by providing shortcuts for the characters.


-/

namespace Mathlib.Linter.TextBased.UnicodeLinter

/-- Following any unicode character, this indicates that the emoji-variant should be displayed -/
def UnicodeVariant.emoji := '\uFE0F'

/-- Following any unicode character, this indicates that the text-variant should be displayed -/
def UnicodeVariant.text := '\uFE0E'

/-- Prints a unicode character's codepoint in hexadecimal with prefix 'U+'.
E.g., 'a' is "U+0061".-/
def printCodepointHex (c : Char) : String :=
  let digits := Nat.toDigits 16 c.val.toNat
  match digits.length with  -- print at least 4 (could be more) hex characters using leading zeros
  | 1 => "U+000".append <| String.mk digits
  | 2 => "U+00".append <| String.mk digits
  | 3 => "U+0".append <| String.mk digits
  | _ => "U+".append <| String.mk digits

/-- Allowed (by the linter) whitespace characters -/
def ASCII.allowedWhitespace (c : Char) := #[' ', '\n'].contains c

/-- Printable ASCII characters, not including whitespace. -/
def ASCII.printable (c : Char) := 0x21 ≤ c.toNat && c.toNat ≤ 0x7e

/-- Allowed (by the linter) ASCII characters -/
def ASCII.allowed (c : Char) := ASCII.allowedWhitespace c || ASCII.printable c

/--
Symbols with VSCode extension abbreviation as of Aug. 28, 2024

Taken from abbreviations.json in
github.com/leanprover/vscode-lean4/blob/97d7d8c382d1549c18b66cd99ab4df0b6634c8f1

Obtained using Julia code:
```julia
filter(!isascii, unique( <all text in JSON file> )) |> repr
```
And manually **excluding** \quad (U+2001) and Rial (U+FDFC).
-/
def withVSCodeAbbrev := #[
'⦃', '⦄', '⟦', '⟧', '⟨', '⟩', '⟮', '⟯', '‹', '›', '«',
'»', '⁅', '⁆', '‖', '₊', '⌊', '⌋', '⌈', '⌉', 'α', 'β',
'χ', '↓', 'ε', 'γ', '∩', 'μ', '¬', '∘', 'Π', '▸', '→',
'↑', '∨', '×', '⁻', '¹', '∼', '·', '⋆', '¿', '₁', '₂',
'₃', '₄', '₅', '₆', '₇', '₈', '₉', '₀', '←', 'Ø', '⅋',
'𝔸', 'ℂ', 'Δ', '𝔽', 'Γ', 'ℍ', '⋂', '𝕂', 'Λ', 'ℕ', 'ℚ',
'ℝ', 'Σ', '⋃', 'ℤ', '♯', '∶', '∣', '¡', 'δ', 'ζ', 'η',
'θ', 'ι', 'κ', 'λ', 'ν', 'ξ', 'π', 'ρ', 'ς', 'σ', 'τ',
'φ', 'ψ', 'ω', 'À', 'Á', 'Â', 'Ã', 'Ä', 'Ç', 'È', 'É',
'Ê', 'Ë', 'Ì', 'Í', 'Î', 'Ï', 'Ñ', 'Ò', 'Ó', 'Ô', 'Õ',
'Ö', 'Ù', 'Ú', 'Û', 'Ü', 'Ý', 'à', 'á', 'â', 'ã', 'ä',
'ç', 'è', 'é', 'ê', 'ë', 'ì', 'í', 'î', 'ï', 'ñ', 'ò',
'ó', 'ô', 'õ', 'ö', 'ø', 'ù', 'ú', 'û', 'ü', 'ý', 'ÿ',
'Ł', '∉', '♩', '𐆎', '∌', '∋', '⟹', '♮', '₦', '∇', '≉',
'№', '⇍', '⇎', '⇏', '⊯', '⊮', '≇', '↗', '≢', '≠', '∄',
'≱', '≯', '↚', '↮', '≰', '≮', '∤', '∦', '⋠', '⊀', '↛',
'≄', '≁', '⊈', '⊄', '⋡', '⊁', '⊉', '⊅', '⋬', '⋪', '⋭',
'⋫', '⊭', '⊬', '↖', '≃', '≖', '≕', '⋝', '⋜', '⊢', '–',
'∃', '∅', '—', '€', 'ℓ', '≅', '∈', '⊺', '∫', '⨍', '∆',
'⊓', '⨅', '∞', '↔', 'ı', '≣', '≡', '≗', '⇒', '≋', '≊',
'≈', '⟶', 'ϩ', '↩', '↪', '₴', 'ͱ', '♥', 'ℏ', '∻', '≔',
'∺', '∷', '≂', '⊣', '²', '³', '∹', '─', '═', '━', '╌',
'⊸', '≑', '≐', '∔', '∸', '⋯', '≘', '⟅', '≙', '∧', '∠',
'∟', 'Å', '∀', 'ᶠ', 'ᵐ', 'ℵ', '⁎', '∗', '≍', '⌶', 'å',
'æ', '₳', '؋', '∐', '≚', 'ª', 'º', '⊕', 'ᵒ', 'ᵈ', 'ᵃ',
'ᵖ', '⊖', '⊝', '⊗', '⊘', '⊙', '⊚', '⊜', 'œ', '🛑', 'Ω',
'℥', 'ο', '∮', '∯', '⨂', '∂', '≛', '≜', '▹', '▿', '⊴',
'◃', '⊵', '▵', '⬝', '◂', '↞', '↠', '⁀', '∴', '℡', '₸',
'♪', 'µ', '⁄', '฿', '✝', '⁒', '₡', '℗', '₩', '₱', '‱',
'₤', '℞', '※', '‽', '℮', '◦', '₮', '⊤', 'ₛ', 'ₐ', 'ᵇ',
'ₗ', 'ₘ', 'ₚ', '⇨', '￢', '⋖', '⩿', '≝', '°', 'ϯ', '⊡',
'₫', '⇊', '⇃', '⇂', '↘', '⇘', '₯', '↙', '⇙', '⇵', '↧',
'⟱', '⇓', '↡', '‡', '⋱', '↯', '◆', '◇', '◈', '⚀', '÷',
'⋇', '⌀', '♢', '⋄', 'ϝ', '†', 'ℸ', 'ð', '≞', '∡', '↦',
'♂', '✠', '₼', 'ℐ', '−', '₥', '℧', '⊧', '∓', '≟', '⁇',
'🛇', '∏', '∝', '≾', '≼', '⋨', '≺', '′', '↣', '𝒫', '£',
'▰', '▱', '㉐', '¶', '∥', '±', '⟂', 'ᗮ', '‰', '⅌', '₧',
'⋔', '✂', '≦', '≤', '↝', '↢', '↽', '↼', '⇇', '⇆', '⇋',
'↭', '⋋', '≲', '⋚', '≶', '⊔', '⟷', '⇔', '⌟', '⟵', '↤',
'⇚', '⇐', '↜', '⌞', '〚', '≪', '₾', '…', '“', '《', '⧏',
'◁', '⋦', '≨', '↫', '↬', '✧', '‘', '⋉', '≧', '≥', '„',
'‚', '₲', 'ϫ', '⋙', '≫', 'ℷ', '⋧', '≩', '≳', '⋗', '⋛',
'≷', '≴', '⟪', '≵', '⟫', '√', '⊂', '⊃', '⊏', '⊐', '⊆',
'⊊', '⊇', '⊋', '⨆', '∛', '∜', '≿', '≽', '⋩', '≻', '∑',
'⤳', '⋢', '⊑', '⋣', '⊒', '□', '⇝', '■', '▣', '▢', '◾',
'✦', '✶', '✴', '✹', 'ϛ', '₷', '∙', '♠', '∢', '§', 'ϻ',
'ϡ', 'ϸ', 'ϭ', 'ϣ', '﹨', '∖', '⌣', '•', '◀', 'Τ', 'Θ',
'Þ', '∪', '‿', '⯑', '⊎', '⊍', '↨', '↕', '⇕', '⇖', '⌜',
'⇗', '⌝', '⇈', '⇅', '↥', '⟰', '⇑', '↟', 'υ', '↿', '↾',
'⋀', 'Å', 'Æ', 'Α', '⋁', '⨁', '⨀', '⍟', 'Œ', 'Ω', 'Ο',
'Ι', 'ℑ', '⨄', '⨃', 'Υ', 'ƛ', 'Ϫ', 'Β', 'Ε', 'Ζ', 'Κ',
'Μ', 'Ν', 'Ξ', 'Ρ', 'Φ', 'Χ', 'Ψ', '✉', '⋘', '↰', '⊨',
'⇰', '⊩', '⊫', '⊪', '⋒', '⋓', '¤', '⋞', '⋟', '⋎', '⋏',
'↶', '↷', '♣', '🚧', 'ᶜ', '∁', '©', '●', '◌', '○', '◯',
'◎', '↺', '®', '↻', '⊛', 'Ⓢ', '¢', '℃', '₵', '✓', 'ȩ',
'₢', '☡', '∎', '⧸', '⊹', '⊟', '⊞', '⊠', '¦', '𝔹', 'ℙ',
'𝟘', '⅀', '𝟚', '𝟙', '𝟜', '𝟛', '𝟞', '𝟝', '𝟠', '𝟟', '𝟬',
'𝟡', '𝟮', '𝟭', '𝟰', '𝟯', '𝟲', '𝟱', '𝟴', '𝟳', '𝟵', '‣',
'≏', '☣', '★', '▽', '△', '≬', 'ℶ', '≌', '∵', '‵', '∍',
'∽', '⋍', '⊼', '☻', '▪', '▾', '▴', '⊥', '⋈', '◫', '⇉',
'⇄', '⇶', '⇛', '▬', '▭', '⟆', '〛', '☢', '’', '⇁',
'⇀', '⇌', '≓', '⋌', '₨', '₽', '▷', '”', '⋊', '⥤', '》',
'½', '¼', '⅓', '⅙', '⅕', '⅟', '⅛', '⅖', '⅔', '⅗', '¾',
'⅘', '⅜', '⅝', '⅚', '⅞', '⌢', '♀', '℻', 'ϥ', '♭', '≒',
'ℜ', 'Ϥ', '↱', 'Ϩ', '☹', 'Ϧ', 'Ͱ', 'Ϟ', 'ᵉ', 'ʰ', 'ᵍ',
'ʲ', 'ⁱ', 'ˡ', 'ᵏ', 'ⁿ', 'ˢ', 'ʳ', 'ᵘ', 'ᵗ', 'ʷ', 'ᵛ',
'ʸ', 'ˣ', 'ᴬ', 'ᶻ', 'ᴰ', 'ᴮ', 'ᴳ', 'ᴱ', 'ᴵ', 'ᴴ', 'ᴷ',
'ᴶ', 'ᴹ', 'ᴸ', 'ᴼ', 'ᴺ', 'ᴿ', 'ᴾ', 'ᵁ', 'ᵀ', 'ᵂ', 'ⱽ',
'⁰', '⁵', '⁴', '⁷', '⁶', '⁹', '⁸', '⁽', '⁾', '⁺', '⁼',
'ꭟ', 'ᶷ', 'ᶶ', 'ꭝ', 'ꭞ', 'ᶩ', 'ᶪ', 'ꭜ', 'ꟹ', 'ʱ', 'ᶿ',
'ꟸ', 'ᶭ', 'ᶺ', 'ᶣ', 'ᵚ', 'ᵆ', 'ᶛ', 'ᵎ', 'ᵄ', 'ʵ', 'ᵌ',
'ʴ', 'ᵔ', 'ᶵ', 'ᶴ', 'ᶾ', 'ᵑ', 'ᶞ', 'ᶼ', 'ᶽ', 'ᶦ', 'ᶹ',
'ᶰ', 'ᶫ', 'ᶧ', 'ᶸ', 'ᶝ', 'ʶ', 'ᶳ', 'ᵡ', 'ᵊ', 'ᶢ', 'ᶲ',
'ᵙ', 'ᵝ', 'ᶱ', 'ᶯ', 'ᵕ', 'ᶬ', 'ᶮ', 'ᶥ', 'ᶨ', 'ᶟ', 'ᶤ',
'ᵠ', 'ˤ', 'ˠ', 'ᵞ', 'ᵅ', 'ᵜ', 'ᵋ', 'ᵓ', 'ᴻ', 'ᴽ', 'ᴯ',
'ᴲ', '℠', 'ᴭ', '™', 'ₑ', 'ᵢ', 'ₕ', 'ₖ', 'ⱼ', 'ₒ', 'ₙ',
'ᵣ', 'ₜ', 'ᵥ', 'ᵤ', 'ₓ', '₎', '₌', '₍', '̲', '‼', '₋',
'Ϻ', '⁉', 'Ϸ', 'Ϡ', 'Ϣ', 'Ϭ', 'Ϛ', '⋑', '⋐', '☺', '𝐁',
'𝐀', '𝐃', '𝐂', '𝐅', '𝐄', '𝐇', '𝐆', '𝐉', '𝐈', '𝐋', '𝐊',
'𝐍', '𝐌', '𝐏', '𝐎', '𝐑', '𝐐', '𝐓', '𝐒', '𝐕', '𝐔', '𝐗',
'𝐖', '𝐘', '𝐙', '𝐛', '𝐚', '𝐝', '𝐜', '𝐟', '𝐞', '𝐡', '𝐠',
'𝐣', '𝐢', '𝐥', '𝐤', '𝐧', '𝐦', '𝐩', '𝐨', '𝐫', '𝐪', '𝐭',
'𝐬', '𝐯', '𝐮', '𝐱', '𝐰', '𝐲', '𝐳', '𝐴', '𝐶', '𝐵', '𝐸',
'𝐷', '𝐺', '𝐹', '𝐼', '𝐻', '𝐾', '𝐽', '𝑀', '𝐿', '𝑂', '𝑁',
'𝑄', '𝑃', '𝑆', '𝑅', '𝑈', '𝑇', '𝑊', '𝑉', '𝑌', '�', '𝑎',
'𝑍', '𝑐', '𝑏', '𝑒', '𝑑', '𝑔', '𝑓', '𝑗', '𝑖', '𝑙', '𝑘',
'𝑛', '𝑚', '𝑝', '𝑜', '𝑟', '𝑞', '𝑡', '𝑠', '𝑣', '𝑢', '𝑥',
'𝑤', '𝑧', '𝑦', '𝑩', '𝑨', '𝑫', '𝑪', '𝑭', '𝑬', '𝑯', '𝑮',
'𝑱', '𝑰', '𝑳', '𝑲', '𝑵', '𝑴', '𝑷', '𝑶', '𝑹', '𝑸', '𝑻',
'𝑺', '𝑽', '𝑼', '𝑿', '𝒁', '𝒀', '𝒃', '𝒂', '𝒅', '𝒄', '𝒇',
'𝒆', '𝒉', '𝒈', '𝒋', '𝒊', '𝒍', '𝒌', '𝒏', '𝒎', '𝒑', '𝒐',
'𝒓', '𝒒', '𝒕', '𝒔', '𝒗', '𝒖', '𝒙', '𝒘', '𝒛', '𝒚', 'ℬ',
'𝒜', '𝒟', '𝒞', 'ℱ', 'ℰ', 'ℋ', '𝒢', '𝒥', 'ℒ', '𝒦', '𝒩',
'ℳ', '𝒪', 'ℛ', '𝒬', '𝒯', '𝒮', '𝒱', '𝒰', '𝒳', '𝒲', '𝒵',
'𝒴', '𝒷', '𝒶', '𝒹', '𝒸', '𝒻', 'ℯ', '𝒽', 'ℊ', '𝒿', '𝒾',
'𝓁', '𝓀', '𝓃', '𝓂', '𝓅', 'ℴ', '𝓇', '𝓆', '𝓉', '𝓈', '𝓋',
'𝓊', '𝓍', '𝓌', '𝓏', '𝓎', '𝓑', '𝓐', '𝓓', '𝓒', '𝓕', '𝓔',
'𝓗', '𝓖', '𝓙', '𝓘', '𝓛', '𝓚', '𝓝', '𝓜', '𝓟', '𝓞', '𝓠',
'𝓣', '𝓢', '𝓥', '𝓤', '𝓧', '𝓦', '𝓩', '𝓨', '𝓫', '𝓪', '𝓭',
'𝓬', '𝓯', '𝓮', '𝓱', '𝓰', '𝓳', '𝓲', '𝓵', '𝓴', '𝓷', '𝓶',
'𝓹', '𝓸', '𝓻', '𝓺', '𝓽', '𝓼', '𝓿', '𝓾', '𝔁', '𝔀', '𝔃',
'𝔂', '𝔅', '𝔄', '𝔇', 'ℭ', '𝔉', '𝔈', 'ℌ', '𝔊', '𝔍', '𝔏',
'𝔎', '𝔑', '𝔐', '𝔓', '𝔒', '𝔔', '𝔗', '𝔖', '𝔙', '𝔘', '𝔚',
'ℨ', '𝔜', '𝔟', '𝔞', '𝔡', '𝔠', '𝔣', '𝔢', '𝔥', '𝔤', '𝔧',
'𝔦', '𝔩', '𝔨', '𝔫', '𝔪', '𝔭', '𝔬', '𝔯', '𝔮', '𝔱', '𝔰',
'𝔳', '𝔲', '𝔵', '𝔶', '𝔷', '¥', 'ϰ', 'ϱ', 'ϗ', 'ϕ', 'ϖ',
'⊲', 'ϑ', 'ϐ', '⊳', '⊻', 'ě', 'Ě', 'ď', '⋮', 'Ď', 'Č',
'č', '₭', 'ϟ', 'Į', 'į', 'K', '⚠', 'ϧ', '≀', '℘', 'Ϯ',
'Ϝ', 'Ð', 'Η', '≎', '𝔻', '𝔼', '𝔾', '𝕁', '𝕀', '𝕃', '𝕄',
'𝕆', '𝕋', '𝕊', '𝕍', '𝕌', '𝕏', '𝕎', '𝕐', '𝕓', '𝕒', '𝕕',
'𝕔', '𝕗', '𝕖', '𝕙', '𝕘', '𝕛', '𝕚', '𝕜', '𝕟', '𝕞', '𝕡',
'𝕠', '𝕣', '𝕢', '𝕥', '𝕤', '𝕧', '𝕦', '𝕩', '𝕨', '𝕪', '𝕫',
'⨯', '⨿', 'Ϳ' ]

/-- Unicode symbols in mathilb that should always be followed by the emoji-variant selector. -/
def emojis := #[
'\u2705',        -- ✅️
'\u274C',        -- ❌️
 -- TODO "missing end of character literal" if written as '\u1F4A5'
 -- see https://github.com/leanprover/lean4/blob/4eea57841d1012d6c2edab0f270e433d43f92520/src/Lean/Parser/Basic.lean#L709
.ofNat 0x1F4A5,  -- 💥️
.ofNat 0x1F7E1,  -- 🟡️
.ofNat 0x1F4A1,  -- 💡️
.ofNat 0x1F419,  -- 🐙️
.ofNat 0x1F50D,  -- 🔍️
.ofNat 0x1F389,  -- 🎉️
'\u23F3',        -- ⏳️
.ofNat 0x1F3C1 ] -- 🏁️

/-- Unicode symbols in mathilb that should always be followed by the text-variant selector. -/
def nonEmojis : Array Char := #[]

/--
Other unicode characters present in Mathlib (as of Aug. 28, 2024)
not present in any of the above lists.
-/
def othersInMathlib := #[
'▼', 'ō', '⏩', '❓',
'🆕', 'š', 'ř', '⚬', '│', '├', '┌', 'ő',
'⟍', '̂', 'ᘁ', 'ń', 'ć', '⟋', 'ỳ', 'ầ', '⥥',
'ł', '◿', '◹', '－', '＼', '◥', '／', '◢', 'Ž', 'ă',
'И', 'в', 'а', 'н', 'о', 'и', 'ч', 'Š', 'ᴜ', 'ᵧ', '´',
'ᴄ', 'ꜰ', 'ß', 'ᴢ', 'ᴏ', 'ᴀ', 'ꜱ', 'ɴ', 'ꞯ', 'ʟ',
'ʜ', 'ᵟ', 'ʙ', 'ᵪ', 'ᵩ', 'ᵦ', 'ᴊ', 'ᴛ', 'ᴡ', 'ᴠ',
'ɪ', '̀', 'ᴇ', 'ᴍ', 'ʀ', 'ᴅ', 'ɢ', 'ʏ', 'ᴘ', 'ĝ', 'ᵨ',
'ᴋ', 'ś', '꙳', '𝓡', '𝕝', '𝖣', '⨳',
-- superscript small/capital "Q" are used by `Mathlib.Util.Superscript`:
'𐞥', 'ꟴ' ]

/-
TODO there are more symbols we could use that aren't in this list yet. E.g, see
https://en.wikipedia.org/wiki/Mathematical_operators_and_symbols_in_Unicode
-/

/-- If `false` the character is not allowed in Mathlib.
Consider adding it to one of the whitelists.
Note: if `true`, character might still not be allowed in some contexts
(e.g. misplaced variant selectors) -/
def isAllowedCharacter (c : Char) : Bool :=
  ASCII.allowed c
  || withVSCodeAbbrev.contains c
  || emojis.contains c
  || nonEmojis.contains c
  || c == UnicodeVariant.emoji
  || c == UnicodeVariant.text
  || othersInMathlib.contains c

end Mathlib.Linter.TextBased.UnicodeLinter
