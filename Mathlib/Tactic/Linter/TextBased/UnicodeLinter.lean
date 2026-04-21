/-
Copyright (c) 2024 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka, Jon Eugster, Michael Rothgang
-/
module

import Mathlib.Init


/-!

# Tools for the unicode Linter

The actual linter is defined in `TextBased.lean`.

This file defines the allowlist and other tools used by the linter.

**When changing, make sure to stay in sync with [style guide](https://github.com/leanprover-community/leanprover-community.github.io/blob/lean4/templates/contribute/style.md#unicode-usage)**

-/
set_option backward.defeqAttrib.useBackward true

namespace Mathlib.Linter.TextBased.UnicodeLinter

/-- Following any unicode character, this indicates that the emoji variant should be displayed -/
public def UnicodeVariant.emoji := '\uFE0F'

/-- Following any unicode character, this indicates that the text variant should be displayed -/
public def UnicodeVariant.text := '\uFE0E'

/-- Prints a unicode character's codepoint in hexadecimal with prefix 'U+'.
E.g., 'a' is "U+0061". -/
public def Char.printCodepointHex (c : Char) : String :=
  let digits := Nat.toDigits 16 c.val.toNat
  -- print at least 4 (could be more) hex characters using leading zeros
  ("U+".append <| "0000".drop digits.length |>.toString).append <| String.ofList digits

/-- Prints all characters in a string in hexadecimal with prefix 'U+'.
E.g., "ab" is "U+0061;U+0062". -/
public def String.printCodepointHex (s : String) : String :=
  -- note: must not contain spaces because of the error message parsing below!
  ";".intercalate <| s.toList.map Char.printCodepointHex

/-- Allowed (by the linter) whitespace characters -/
def ASCII.allowedWhitespace (c : Char) : Bool := #[' ', '\n'].contains c

/-- Printable ASCII characters, not including whitespace. -/
def ASCII.printable (c : Char) : Bool := 0x21 ≤ c.toNat && c.toNat ≤ 0x7e

/-- Allowed (by the linter) ASCII characters -/
def ASCII.allowed (c : Char) : Bool := ASCII.allowedWhitespace c || ASCII.printable c

/--
Symbols with VSCode extension abbreviation, as of March 17, 2026.
Obtained using `scripts/extract-unique-nonascii.lean` from
https://github.com/leanprover/vscode-lean4/blob/132d329aa8afa3e8508ef77cfdcff112d3b35c88
-/
def withVSCodeAbbrev : Array Char := #[
  '⦃', '⦄', '⟦', '⟧', '⟨', '⟩', '⟮', '⟯', '⸨', '⸩', '‹', '›', '«', '»', '⁅', '⁆',
  '‖', '₊', '⌊', '⌋', '⌈', '⌉', '⦋', '⦌', 'α', 'β', 'χ', '↓', 'ε', 'γ', '∩', 'μ',
  '∘', 'Π', '▸', '→', '↑', '∨', '×', '⁻', '¹', '∼', '·', '⋆', '¬', '¿', '₁', '₂',
  '₃', '₄', '₅', '₆', '₇', '₈', '₉', '₀', '←', 'Ø', '⅋', '𝔸', 'ℂ', 'Δ', '𝔽', 'Γ',
  'ℍ', '⋂', '𝕂', 'Λ', 'ℕ', 'ℚ', 'ℝ', 'Σ', '⋃', 'ℤ', '♯', '∶', '∣', 'δ', 'ζ', 'η',
  'θ', 'ι', 'κ', 'λ', 'ν', 'ξ', 'π', 'ρ', 'ς', 'σ', 'τ', 'φ', 'ψ', 'ω', 'À', 'Á',
  'Â', 'Ã', 'Ä', 'Ā', 'Ç', 'È', 'É', 'Ê', 'Ë', 'Ē', 'Ì', 'Í', 'Î', 'Ï', 'Ī', 'Ñ',
  'Ò', 'Ó', 'Ô', 'Õ', 'Ö', 'Ō', 'Ù', 'Ú', 'Û', 'Ü', 'Ū', 'Ý', 'à', 'á', 'â', 'ã',
  'ä', 'ā', 'ç', 'è', 'é', 'ê', 'ë', 'ē', 'ì', 'í', 'î', 'ï', 'ī', 'ñ', 'ò', 'ó',
  'ô', 'õ', 'ö', 'ø', 'ō', 'ù', 'ú', 'û', 'ü', 'ū', 'ý', 'ÿ', 'Ł', '♩', '∉', '≮',
  '𐆎', '∌', '∋', '⟹', '♮', '₦', '∇', '≉', '№', '⇍', '⇎', '⇏', '⊯', '⊮', '≇', '↗',
  '≢', '≠', '∄', '≱', '≯', '↚', '↮', '≰', '∤', '∦', '⋠', '⊀', '↛', '≄', '≁', '⊈',
  '⊄', '⋡', '⊁', '⊉', '⊅', '⋬', '⋪', '⋭', '⋫', '⊭', '⊬', '↖', '≃', '≖', '≕', '⋝',
  '⋜', '⊢', '–', '∃', '∅', '—', '€', 'ℓ', '≅', '∈', '⊺', '∫', '⨍', '∆', '⊓', '⨅',
  '∞', '↔', 'ı', '≣', '≡', '≗', '⇒', '≋', '≊', '≈', '⟶', 'ϩ', '↩', '↪', '₴', 'ͱ',
  '♥', 'ℏ', '∻', '≔', '∺', '∷', '≂', '⊣', '²', '³', '∹', '─', '═', '━', '╌', '⊸',
  '≑', '≐', '∔', '∸', '⋯', '≘', '⟅', '≙', '∧', '∠', '∟', 'Å', '∀', 'ᶠ', 'ᵐ', 'ℵ',
  '⁎', '∗', '≍', '⌶', 'å', 'æ', '₳', '∐', '≚', 'ª', 'º', '⊕', 'ᵒ', 'ᵈ', 'ᵃ', 'ᵖ',
  '⊖', '⊝', '⊗', '⊘', '⊙', '⊚', '⊜', 'œ', '🛑', 'Ω', '℥', 'ο', '∮', '∯', '⨂', '∂',
  '≛', '≜', '▹', '▿', '⊴', '◃', '⊵', '▵', '⬝', '◂', '↞', '↠', '⁀', '∴', '℡', '₸',
  '♪', 'µ', '⁄', '฿', '✝', '⁒', '₡', '℗', '₩', '₱', '‱', '₤', '℞', '※', '‽', '℮',
  '◦', '₮', '⊤', 'ₛ', 'ₐ', 'ᵇ', 'ₗ', 'ₘ', 'ₚ', '⇨', '￢', '⋖', '⩿', '≝', '°', 'ϯ',
  '⊡', '₫', '⇊', '⇃', '⇂', '↘', '⇘', '₯', '↙', '⇙', '⇵', '↧', '⟱', '⇓', '↡', '‡',
  '⋱', '↯', '◆', '◇', '◈', '⚀', '÷', '⋇', '⌀', '♢', '⋄', 'ϝ', '†', 'ℸ', 'ð', '≞',
  '∡', '↦', '♂', '✠', '₼', 'ℐ', '−', '₥', '℧', '⊧', '∓', '≟', '⁇', '🛇', '∏', '∝',
  '≾', '≼', '⋨', '≺', '′', '↣', '𝒫', '£', '▰', '▱', '㉐', '¶', '∥', '±', '⟂', 'ᗮ',
  '‰', '⅌', '₧', '⋔', '≦', '≤', '↝', '↢', '↽', '↼', '⇇', '⇆', '⇋', '↭', '⋋', '≲',
  '⋚', '≶', '⊔', '⟷', '⇔', '⌟', '⟵', '↤', '⇚', '⇐', '↜', '⌞', '〚', '≪', '₾', '…',
  '“', '《', '⧏', '◁', '⋦', '≨', '↫', '↬', '✧', '‘', '⋉', '≧', '≥', '„', '‚', '₲',
  'ϫ', '⋙', '≫', 'ℷ', '⋧', '≩', '≳', '⋗', '⋛', '≷', '≴', '⟪', '≵', '⟫', '√', '✂',
  '⊂', '⊃', '⊏', '⊐', '⊆', '⊊', '⊇', '⊋', '⨆', '∛', '∜', '≿', '≽', '⋩', '≻', '∑',
  '⤳', '⋢', '⊑', '⋣', '⊒', '□', '⇝', '■', '▣', '▢', '◾', '✦', '✶', '✴', '✹', 'ϛ',
  '₷', '∙', '♠', '∢', '§', 'ϻ', 'ϡ', 'ϸ', 'ϭ', 'ϣ', '﹨', '∖', '⌣', '•', '◀', 'Τ',
  'Θ', 'Þ', '∪', '‿', '⯑', '⊎', '⊍', '↨', '↕', '⇕', '⇖', '⌜', '⇗', '⌝', '⇈', '⇅',
  '↥', '⟰', '⇑', '↟', 'υ', '↿', '↾', '⋀', 'Å', 'Æ', 'Α', '⋁', '⨁', '⨀', '⍟', 'Œ',
  'Ω', 'Ο', 'Ι', 'ℑ', '⨄', '⨃', 'Υ', 'ƛ', 'Ϫ', 'Β', 'Ε', 'Ζ', 'Κ', 'Μ', 'Ν', 'Ξ',
  'Ρ', 'Φ', 'Χ', 'Ψ', '✉', '⋘', '↰', '⊨', '⇰', '⊩', '⊫', '⊪', '⋒', '⋓', '¤', '⋞',
  '⋟', '⋎', '⋏', '↶', '↷', '♣', '🚧', 'ᶜ', '∁', '©', '●', '○', '◌', '◎', '◯', '↺',
  '↻', '®', 'Ⓢ', '⊛', '¢', '₵', '℃', 'ȩ', '✓', '₢', '☡', '∎', '⧸', '⊹', '⊞', '⊟',
  '⊠', '¦', 'ℙ', '𝔹', '⅀', '𝟘', '𝟙', '𝟚', '𝟛', '𝟜', '𝟝', '𝟞', '𝟟', '𝟠', '𝟡', '𝟬',
  '𝟭', '𝟮', '𝟯', '𝟰', '𝟱', '𝟲', '𝟳', '𝟴', '𝟵', '‣', '≏', '☣', '★', '▽', '△', 'ℶ',
  '≬', '∵', '≌', '∍', '‵', '⋍', '∽', '⊼', '▪', '☻', '▾', '▴', '⊥', '⋈', '◫', '⇉',
  '⇶', '⇄', '⇛', '▬', '▭', '⟆', '☢', '〛', '’', '⇁', '⇀', '⇌', '⋌', '≓', '₽', '₨',
  '▷', '⋊', '”', '》', '⥤', '½', '⅓', '¼', '⅕', '⅙', '⅛', '⅟', '⅔', '⅖', '¾', '⅗',
  '⅜', '⅘', '⅚', '⅝', '⅞', '⌢', '♀', 'ϥ', '℻', '≒', '♭', 'ℜ', '↱', 'Ϥ', '☹', 'Ϩ',
  'Ͱ', 'Ϧ', 'Ϟ', 'ᵉ', 'ᵍ', 'ʰ', 'ⁱ', 'ʲ', 'ᵏ', 'ˡ', 'ⁿ', 'ʳ', 'ˢ', 'ᵗ', 'ᵘ', 'ᵛ',
  'ʷ', 'ˣ', 'ʸ', 'ᶻ', 'ᴬ', 'ᴮ', 'ᴰ', 'ᴱ', 'ᴳ', 'ᴴ', 'ᴵ', 'ᴶ', 'ᴷ', 'ᴸ', 'ᴹ', 'ᴺ',
  'ᴼ', 'ᴾ', 'ᴿ', 'ᵀ', 'ᵁ', 'ⱽ', 'ᵂ', '⁰', '⁴', '⁵', '⁶', '⁷', '⁸', '⁹', '⁾', '⁽',
  '⁼', '⁺', 'ꭟ', 'ᶶ', 'ᶷ', 'ꭞ', 'ꭝ', 'ᶪ', 'ᶩ', 'ꟹ', 'ꭜ', 'ʱ', 'ꟸ', 'ᶿ', 'ᶺ', 'ᶭ',
  'ᵚ', 'ᶣ', 'ᶛ', 'ᵆ', 'ᵄ', 'ᵎ', 'ᵌ', 'ʵ', 'ʴ', 'ᶵ', 'ᵔ', 'ᶾ', 'ᶴ', 'ᶞ', 'ᵑ', 'ᶽ',
  'ᶼ', 'ᶹ', 'ᶦ', 'ᶫ', 'ᶰ', 'ᶸ', 'ᶧ', 'ʶ', 'ᶝ', 'ᵡ', 'ᶳ', 'ᶢ', 'ᵊ', 'ᵙ', 'ᶲ', 'ᶱ',
  'ᵝ', 'ᵕ', 'ᶯ', 'ᶮ', 'ᶬ', 'ᶨ', 'ᶥ', 'ᶤ', 'ᶟ', 'ˤ', 'ᵠ', 'ᵞ', 'ˠ', 'ᵜ', 'ᵅ', 'ᵓ',
  'ᵋ', 'ᴽ', 'ᴻ', 'ᴲ', 'ᴯ', 'ᴭ', '℠', '™', 'ₑ', 'ₕ', 'ᵢ', 'ⱼ', 'ₖ', 'ₙ', 'ₒ', 'ᵣ',
  'ₜ', 'ᵤ', 'ᵥ', 'ₓ', '₎', '₍', '₌', '₋', '‼', '⁉', 'Ϻ', 'Ϡ', 'Ϸ', 'Ϭ', 'Ϣ', 'Ϛ',
  '⋐', '⋑', '☺', '𝐀', '𝐁', '𝐂', '𝐃', '𝐄', '𝐅', '𝐆', '𝐇', '𝐈', '𝐉', '𝐊', '𝐋', '𝐌',
  '𝐍', '𝐎', '𝐏', '𝐐', '𝐑', '𝐒', '𝐓', '𝐔', '𝐕', '𝐖', '𝐗', '𝐘', '𝐙', '𝐚', '𝐛', '𝐜',
  '𝐝', '𝐞', '𝐟', '𝐠', '𝐡', '𝐢', '𝐣', '𝐤', '𝐥', '𝐦', '𝐧', '𝐨', '𝐩', '𝐪', '𝐫', '𝐬',
  '𝐭', '𝐮', '𝐯', '𝐰', '𝐱', '𝐲', '𝐳', '𝐴', '𝐵', '𝐶', '𝐷', '𝐸', '𝐹', '𝐺', '𝐻', '𝐼',
  '𝐽', '𝐾', '𝐿', '𝑀', '𝑁', '𝑂', '𝑃', '𝑄', '𝑅', '𝑆', '𝑇', '𝑈', '𝑉', '𝑊', '𝑋', '𝑌',
  '𝑍', '𝑎', '𝑏', '𝑐', '𝑑', '𝑒', '𝑓', '𝑔', '𝑖', '𝑗', '𝑘', '𝑙', '𝑚', '𝑛', '𝑜', '𝑝',
  '𝑞', '𝑟', '𝑠', '𝑡', '𝑢', '𝑣', '𝑤', '𝑥', '𝑦', '𝑧', '𝑨', '𝑩', '𝑪', '𝑫', '𝑬', '𝑭',
  '𝑮', '𝑯', '𝑰', '𝑱', '𝑲', '𝑳', '𝑴', '𝑵', '𝑶', '𝑷', '𝑸', '𝑹', '𝑺', '𝑻', '𝑼', '𝑽',
  '𝑾', '𝑿', '𝒀', '𝒁', '𝒂', '𝒃', '𝒄', '𝒅', '𝒆', '𝒇', '𝒈', '𝒉', '𝒊', '𝒋', '𝒌', '𝒍',
  '𝒎', '𝒏', '𝒐', '𝒑', '𝒒', '𝒓', '𝒔', '𝒕', '𝒖', '𝒗', '𝒘', '𝒙', '𝒚', '𝒛', '𝒜', 'ℬ',
  '𝒞', '𝒟', 'ℰ', 'ℱ', '𝒢', 'ℋ', '𝒥', '𝒦', 'ℒ', 'ℳ', '𝒩', '𝒪', '𝒬', 'ℛ', '𝒮', '𝒯',
  '𝒰', '𝒱', '𝒲', '𝒳', '𝒴', '𝒵', '𝒶', '𝒷', '𝒸', '𝒹', 'ℯ', '𝒻', 'ℊ', '𝒽', '𝒾', '𝒿',
  '𝓀', '𝓁', '𝓂', '𝓃', 'ℴ', '𝓅', '𝓆', '𝓇', '𝓈', '𝓉', '𝓊', '𝓋', '𝓌', '𝓍', '𝓎', '𝓏',
  '𝓐', '𝓑', '𝓒', '𝓓', '𝓔', '𝓕', '𝓖', '𝓗', '𝓘', '𝓙', '𝓚', '𝓛', '𝓜', '𝓝', '𝓞', '𝓟',
  '𝓠', '𝓡', '𝓢', '𝓣', '𝓤', '𝓥', '𝓦', '𝓧', '𝓨', '𝓩', '𝓪', '𝓫', '𝓬', '𝓭', '𝓮', '𝓯',
  '𝓰', '𝓱', '𝓲', '𝓳', '𝓴', '𝓵', '𝓶', '𝓷', '𝓸', '𝓹', '𝓺', '𝓻', '𝓼', '𝓽', '𝓾', '𝓿',
  '𝔀', '𝔁', '𝔂', '𝔃', '𝔄', '𝔅', 'ℭ', '𝔇', '𝔈', '𝔉', '𝔊', 'ℌ', '𝔍', '𝔎', '𝔏', '𝔐',
  '𝔑', '𝔒', '𝔓', '𝔔', '𝔖', '𝔗', '𝔘', '𝔙', '𝔚', '𝔛', '𝔜', 'ℨ', '𝔞', '𝔟', '𝔠', '𝔡',
  '𝔢', '𝔣', '𝔤', '𝔥', '𝔦', '𝔧', '𝔨', '𝔩', '𝔪', '𝔫', '𝔬', '𝔭', '𝔮', '𝔯', '𝔰', '𝔱',
  '𝔲', '𝔳', '𝔴', '𝔵', '𝔶', '𝔷', '¥', 'ϱ', 'ϰ', 'ϗ', 'ϖ', 'ϕ', 'ϑ', '⊲', '⊳', 'ϐ',
  '⊻', 'ě', 'Ě', '⋮', 'ď', 'Ď', 'č', 'Č', 'ϟ', '₭', 'į', 'Į', 'K', 'ϧ', '⚠', '℘',
  '≀', 'Ϯ', 'Ϝ', 'Ð', 'Η', '≎', '𝔻', '𝔼', '𝔾', '𝕀', '𝕁', '𝕃', '𝕄', '𝕆', '𝕊', '𝕋',
  '𝕌', '𝕍', '𝕎', '𝕏', '𝕐', '𝕒', '𝕓', '𝕔', '𝕕', '𝕖', '𝕗', '𝕘', '𝕙', '𝕚', '𝕛', '𝕜',
  '𝕝', '𝕞', '𝕟', '𝕠', '𝕡', '𝕢', '𝕣', '𝕤', '𝕥', '𝕦', '𝕧', '𝕨', '𝕩', '𝕪', '𝕫', '⨯',
  '⨿', 'Ϳ', '⧾', '⧿', '¡'
]

/--
Other unicode characters present in Mathlib but not present in any of the above lists
(as of March 17, 2026).

This list may be extended by more characters for which no VSCode-extension abbreviation exists.
Some guidelines:
- No invisible characters
- No characters affecting text directionality (Mathlib uses left-to-right text).
- No [Private Use Areas](https://en.wikipedia.org/wiki/Private_Use_Areas)

The list `withVSCodeAbbrev` contains characters with abbreviations; if an abbreviation
already has been defined, you might need to update the list `withVSCodeAbbrev`.
Further, consider proposing an abbreviation to [the extension](https://github.com/leanprover/vscode-lean4) for new symbols.

Empty lines for improved readability (otherwise some characters overlap in some fonts).
-/
def othersInMathlib : Array Char := #[
  '✔', '⟍', 'ł', 'ń', '⎯', '⏐', 'ć', 'š', '̂', 'ᘁ', '𝖣', 'ß', 'ỳ', '⤏',

  '┌', '┐', '│', '├', '└', '┬', '┘', '▼', '◄', '⋅', 'ś', '－', '＼', '◥', '／', '◢',

  '◿', '◹', 'ő', '⥥', '⤞', '⥢', '╱', '⟋', 'Ž', 'ą', 'Š', 'ầ', '：', '꙳', '⎛',

  '⎞', '⎜', '⎟', '⎝', '⎠', 'ă', 'ĝ', 'ᵧ', '▶', '‑', '‾', 'ř', '⏎', '‐', '𐞥',

  'ꟴ', 'ᵟ', 'ᴀ', 'ʙ', 'ᴄ', 'ᴅ', 'ᴇ', 'ꜰ', 'ɢ', 'ʜ', 'ɪ', 'ᴊ', 'ᴋ', 'ʟ', 'ᴍ', 'ɴ',

  'ᴏ', 'ᴘ', 'ꞯ', 'ʀ', 'ꜱ', 'ᴛ', 'ᴜ', 'ᴠ', 'ᴡ', 'ʏ', 'ᴢ', 'ᵦ', 'ᵨ', 'ᵩ', 'ᵪ', 'Ś', 'ę'
]

/-- Unicode symbols in mathlib that should always be followed by the emoji variant selector. -/
public def emojis : Array Char := #[
  '\u2705',        -- ✅️
  '\u274C',        -- ❌️
  -- Note: writing e.g. '\u1F4A5' gives error: "missing end of character literal"
  -- see https://github.com/leanprover/lean4/blob/4eea57841d1012d6c2edab0f270e433d43f92520/src/Lean/Parser/Basic.lean#L709
  .ofNat 0x1F4A5,  -- 💥️
  .ofNat 0x1F7E1,  -- 🟡️
  .ofNat 0x1F4A1,  -- 💡️
  .ofNat 0x1F419,  -- 🐙️
  .ofNat 0x1F50D,  -- 🔍️
  .ofNat 0x1F389,  -- 🎉️
  '\u23F3',        -- ⏳️
  .ofNat 0x1F3C1   -- 🏁️
]

/-- Unicode symbols in mathlib that should always be followed by the text variant selector. -/
public def nonEmojis : Array Char := #[]

/-- If `false`, the character is not allowed in Mathlib.

Implemented using an allowlist consisting of:
- certain ASCII characters
- characters with abbreviations in the VSCode extension (`withVSCodeAbbrev`)
- "the rest" (`othersInMathlib`)

Note: if `true`, a character might still not be allowed depending on context
(e.g. misplaced variant selectors).
-/
public def isAllowedCharacter (c : Char) : Bool :=
  ASCII.allowed c
  || withVSCodeAbbrev.contains c
  || othersInMathlib.contains c
  || emojis.contains c
  || nonEmojis.contains c
  || c == UnicodeVariant.emoji
  || c == UnicodeVariant.text

/-- Provide default replacement (`String`) for a disallowed character, or `none` if none defined -/
public def replaceDisallowed : Char → Option String
| '\u0009' => "  "    -- "TAB" => "2 spaces"
| '\u000B' => "\n"    -- "LINE TABULATION" => "Line Feed"
| '\u000C' => "\n"    -- "FORM FEED" => "Line Feed"
| '\u000D' => "\n"    -- "CARRIAGE RETURN" => "Line Feed"
| '\u001F' => ""      -- "INFORMATION SEPARATOR ONE" => "nothing"
| '\u00A0' => " "     -- "NO-BREAK SPACE" => "1 space"
| '\u1680' => " "     -- "OGHAM SPACE MARK" => "1 space"
| '\u2000' => "  "    -- "EN QUAD" => "2 spaces"
| '\u2001' => "    "  -- "EM QUAD" => "4 spaces"
| '\u2002' => " "     -- "EN SPACE" => "1 space"
| '\u2003' => " "     -- "EM SPACE" => "1 space"
| '\u2004' => " "     -- "THREE-PER-EM SPACE" => "1 space"
| '\u2005' => " "     -- "FOUR-PER-EM SPACE" => "1 space"
| '\u2006' => " "     -- "SIX-PER-EM SPACE" => "1 space"
| '\u2007' => " "     -- "FIGURE SPACE" => "1 space"
| '\u2008' => " "     -- "PUNCTUATION SPACE" => "1 space"
| '\u2009' => " "     -- "THIN SPACE" => "1 space"
| '\u200A' => " "     -- "HAIR SPACE" => "1 space"
| '\u200B' => ""      -- "ZERO WIDTH SPACE" => "nothing"
| '\u200C' => ""      -- "ZERO WIDTH NON-JOINER" => "nothing"
| '\u200D' => ""      -- "ZERO WIDTH JOINER" => "nothing"
| '\u200E' => ""      -- "LEFT-TO-RIGHT MARK" => "nothing"
| '\u200F' => ""      -- "RIGHT-TO-LEFT MARK" => "nothing"
| '\u2028' => " "     -- "LINE SEPARATOR" => "1 space"
| '\u2029' => " "     -- "PARAGRAPH SEPARATOR" => "1 space"
| '\u202A' => ""      -- "LEFT-TO-RIGHT EMBEDDING" => "nothing"
| '\u202B' => ""      -- "RIGHT-TO-LEFT EMBEDDING" => "nothing"
| '\u202C' => ""      -- "POP DIRECTIONAL FORMATTING" => "nothing"
| '\u202D' => ""      -- "LEFT-TO-RIGHT OVERRIDE" => "nothing"
| '\u202E' => ""      -- "RIGHT-TO-LEFT OVERRIDE" => "nothing"
| '\u202F' => " "     -- "NARROW NO-BREAK SPACE" => "1 space"
| '\u205F' => " "     -- "MEDIUM MATHEMATICAL SPACE" => "1 space"
| '\u2060' => ""      -- "WORD JOINER" => "nothing"
| '\u2062' => ""      -- "INVISIBLE TIMES" => "nothing"
| '\u2063' => ""      -- "INVISIBLE SEPARATOR" => "nothing"
| '\u2064' => ""      -- "INVISIBLE PLUS" => "nothing"
| '\u2066' => ""      -- "LEFT-TO-RIGHT ISOLATE" => "nothing"
| '\u2067' => ""      -- "RIGHT-TO-LEFT ISOLATE" => "nothing"
| '\u2068' => ""      -- "FIRST STRONG ISOLATE" => "nothing"
| '\u2069' => ""      -- "POP DIRECTIONAL ISOLATE" => "nothing"
| '\u206A' => ""      -- "INHIBIT SYMMETRIC SWAPPING" => "nothing"
| '\u206B' => ""      -- "ACTIVATE SYMMETRIC SWAPPING" => "nothing"
| '\u206C' => ""      -- "INHIBIT ARABIC FORM SHAPING" => "nothing"
| '\u206D' => ""      -- "ACTIVATE ARABIC FORM SHAPING" => "nothing"
| '\u206E' => ""      -- "NATIONAL DIGIT SHAPES" => "nothing"
| '\u206F' => ""      -- "NOMINAL DIGIT SHAPES" => "nothing"
| '\u3000' => "  "    -- "IDEOGRAPHIC SPACE" =>  "2 spaces"
| _ => none

end Mathlib.Linter.TextBased.UnicodeLinter
