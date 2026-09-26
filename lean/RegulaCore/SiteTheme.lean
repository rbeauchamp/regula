/-! # Rule-reference site theme: colour tokens, their contrast and the stylesheet

Every colour of the rule-reference site is defined here, once. Each token has exactly one light
and one dark value (`Tone`), and the stylesheet's token block is generated from those values with
CSS `light-dark()`, so the two themes cannot drift apart. The rest of the theme layer refers to
colours only through the tokens.

## Main declarations

- `Rgb`, `Tone`, `Paper`, `Ink`, `Line`: the closed token kinds and their values;
  `tokenNames_nodup`: no two tokens share a CSS name.
- `belowLinear`, `channelLow`, `channel_bracket`: for every 8-bit channel value `c`,
  `channelLow c / lumScale ≤ v(c) < (channelLow c + 1) / lumScale`, where `v` is the WCAG 2.x
  linearized channel, stated exactly in integers and kernel-checked over all 256 values.
- `meets`: a sound lower-bound test of the WCAG 2.x contrast ratio from those brackets.
- `ink_on_paper`: in both themes, every text token has at least 7:1 (headings and body text) or
  4.5:1 (every other text colour) against every background token. `control_on_paper`: the
  control boundary has at least 3:1 (WCAG 1.4.11) against every background token. Both are
  kernel evaluation over the complete token enumerations, so a token change that breaks
  contrast fails the build.
- `stylesheet`: the site stylesheet, the generated token block followed by `layerCss`;
  `hasColourLiteral`: the layer is checked by evaluation to contain no hexadecimal or functional
  colour literal.

## Boundaries

The contrast theorems are exact integer statements. They imply the WCAG ratios through one argued
step that the core library cannot state: for nonnegative reals, `p ^ 5 ≤ x ^ 12` exactly when
`p ≤ x ^ (12 / 5)`. They cover pairs of the site's tokens, so a text colour drawn on a
background colour of the theme meets its minimum whichever pairing the stylesheet uses; the
stylesheet itself is reviewed to draw text and backgrounds only from tokens (named colours are
not detected by `hasColourLiteral`). Verso's own stylesheets, the browser and support for
`light-dark()` are trusted or observed; see `docs/guides/website.md`.
-/

namespace Regula.Site

/-! ## Colours -/

/-- An sRGB colour with 8-bit channels. -/
structure Rgb where
  r : Fin 256
  g : Fin 256
  b : Fin 256

private def byte (n : Nat) : Fin 256 := ⟨n % 256, Nat.mod_lt _ (by decide)⟩

/-- The colour written `#rrggbb` in CSS, given as the number `0xrrggbb`. -/
def rgb (hex : Nat) : Rgb := ⟨byte (hex / 65536), byte (hex / 256), byte hex⟩

private def hexByte (n : Fin 256) : String :=
  String.ofList [Nat.digitChar (n.val / 16), Nat.digitChar (n.val % 16)]

/-- CSS spelling `#rrggbb` (lowercase). -/
def Rgb.css (c : Rgb) : String := "#" ++ hexByte c.r ++ hexByte c.g ++ hexByte c.b

/-! ## WCAG 2.x relative luminance, bracketed exactly

The WCAG 2.x linearized value of an 8-bit channel `c` is `v(c) = c / 3294.6` for `c ≤ 10` and
`v(c) = ((c / 255 + 0.055) / 1.055) ^ 2.4 = ((1000 c + 14025) / 269025) ^ (12 / 5)` otherwise.
WCAG 2.x states the branch point as `0.03928` and sRGB as `0.04045`; both select `c ≤ 10` on
8-bit values (`branch_agrees`). -/

/-- The fixed-point scale of the luminance brackets. -/
def lumScale : Nat := 100000

/-- The exact integer test `p / lumScale ≤ v(c)`. For `c > 10` it compares fifth powers:
`(p / lumScale) ^ 5 ≤ ((1000 c + 14025) / 269025) ^ 12`. -/
def belowLinear (c p : Nat) : Bool :=
  if c ≤ 10 then decide (p * 32946 ≤ 10 * c * lumScale)
  else decide (p ^ 5 * 269025 ^ 12 ≤ (1000 * c + 14025) ^ 12 * lumScale ^ 5)

/-- The largest `p` in `[lo, hi]` with `ok p`, for `ok` true at `lo` and antitone; `fuel`
bounds the halvings. Its result is checked, not assumed (`channel_bracket`). -/
def bisect (ok : Nat → Bool) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo then lo else
    let mid := (lo + hi + 1) / 2
    if ok mid then bisect ok fuel mid hi else bisect ok fuel lo (mid - 1)

/-- Lower end of the bracket of `v(c)`, in units of `1 / lumScale`. -/
def channelLow (c : Nat) : Nat := bisect (belowLinear c) 24 0 lumScale

/-- `channelLow c / lumScale ≤ v(c) < (channelLow c + 1) / lumScale`, in integers. -/
def bracketed (c : Nat) : Bool := belowLinear c (channelLow c) && !belowLinear c (channelLow c + 1)

/-- Every 8-bit channel value is bracketed: exhaustive kernel evaluation over all 256 values. -/
theorem channel_bracket : ∀ c, c < 256 → bracketed c = true := by decide +kernel

/-- WCAG 2.x's `c / 255 ≤ 0.03928` and sRGB's `c / 255 ≤ 0.04045` select the same 8-bit
channel values, those with `c ≤ 10`. -/
theorem branch_agrees : ∀ c, c < 256 →
    (decide (c * 100000 ≤ 3928 * 255) = decide (c ≤ 10) ∧
      decide (c * 100000 ≤ 4045 * 255) = decide (c ≤ 10)) := by decide +kernel

/-- Lower bound of the relative luminance `0.2126 R + 0.7152 G + 0.0722 B`, in units of
`1 / (10000 · lumScale)`. The matching upper bound is this plus `10000`. -/
def lumLow (c : Rgb) : Nat :=
  2126 * channelLow c.r + 7152 * channelLow c.g + 722 * channelLow c.b

/-- `meets x y tenths` holds only if the WCAG 2.x contrast ratio `(L₁ + 0.05) / (L₂ + 0.05)` of
`x` and `y` (lighter over darker) is at least `tenths / 10`: the lower bound of one colour's
luminance plus `0.05` is at least `tenths / 10` times the upper bound of the other's plus `0.05`. -/
def meets (x y : Rgb) (tenths : Nat) : Bool :=
  let a := lumLow x
  let b := lumLow y
  let flare := 500 * lumScale
  decide (tenths * (b + 10000 + flare) ≤ 10 * (a + flare)) ||
    decide (tenths * (a + 10000 + flare) ≤ 10 * (b + flare))

/-! ## Tokens -/

/-- The two colour themes. The site's System setting follows the operating system's choice
between them. -/
inductive Theme where
  | light | dark

def Theme.all : List Theme := [.light, .dark]

theorem Theme.mem_all (t : Theme) : t ∈ Theme.all := by cases t <;> simp [Theme.all]

/-- A token's value: exactly one colour per theme. -/
structure Tone where
  light : Rgb
  dark : Rgb

def Tone.get (t : Tone) : Theme → Rgb
  | .light => t.light
  | .dark => t.dark

/-- Background tokens. -/
inductive Paper where
  | bg | subtle | surface | accentBg | badBg | goodBg | delBg | insBg

/-- Text tokens. -/
inductive Ink where
  | text | heading | muted | accent | accentHover | bad | good

/-- Border tokens. `control` bounds inputs and the theme control; the others are decorative. -/
inductive Line where
  | border | control | badLine | goodLine

def Paper.all : List Paper := [.bg, .subtle, .surface, .accentBg, .badBg, .goodBg, .delBg, .insBg]
def Ink.all : List Ink := [.text, .heading, .muted, .accent, .accentHover, .bad, .good]
def Line.all : List Line := [.border, .control, .badLine, .goodLine]

theorem Paper.mem_all (p : Paper) : p ∈ Paper.all := by cases p <;> simp [Paper.all]
theorem Ink.mem_all (i : Ink) : i ∈ Ink.all := by cases i <;> simp [Ink.all]
theorem Line.mem_all (l : Line) : l ∈ Line.all := by cases l <;> simp [Line.all]

/-- CSS name of a token: `--rg-` followed by this. -/
def Paper.name : Paper → String
  | .bg => "bg" | .subtle => "bg-subtle" | .surface => "surface" | .accentBg => "accent-bg"
  | .badBg => "bad-bg" | .goodBg => "good-bg" | .delBg => "del-bg" | .insBg => "ins-bg"

def Ink.name : Ink → String
  | .text => "text" | .heading => "heading" | .muted => "muted" | .accent => "accent"
  | .accentHover => "accent-hover" | .bad => "bad" | .good => "good"

def Line.name : Line → String
  | .border => "border" | .control => "control" | .badLine => "bad-line" | .goodLine => "good-line"

/-- Every CSS token name. -/
def tokenNames : List String := Paper.all.map Paper.name ++ Ink.all.map Ink.name ++ Line.all.map Line.name

/-- No two tokens share a CSS name, so each custom property is defined exactly once. -/
theorem tokenNames_nodup : tokenNames.Nodup := by decide

/-- Page and header, sidebar, code and tags, "What to do", finding card, passing file, diff lines. -/
def Paper.tone : Paper → Tone
  | .bg => ⟨rgb 0xffffff, rgb 0x0e1014⟩
  | .subtle => ⟨rgb 0xf7f7f9, rgb 0x13161b⟩
  | .surface => ⟨rgb 0xf3f4f7, rgb 0x181c23⟩
  | .accentBg => ⟨rgb 0xf1f0fd, rgb 0x1d1b38⟩
  | .badBg => ⟨rgb 0xfff5f3, rgb 0x2a1615⟩
  | .goodBg => ⟨rgb 0xf0fbf5, rgb 0x10251b⟩
  | .delBg => ⟨rgb 0xffebe9, rgb 0x3b1e20⟩
  | .insBg => ⟨rgb 0xe2f8e8, rgb 0x173220⟩

/-- Body text, headings, meta text, links and focus, link hover, rejected, passing. -/
def Ink.tone : Ink → Tone
  | .text => ⟨rgb 0x1c1e24, rgb 0xe3e5ea⟩
  | .heading => ⟨rgb 0x0f1116, rgb 0xf5f6f8⟩
  | .muted => ⟨rgb 0x585e6c, rgb 0xa0a7b4⟩
  | .accent => ⟨rgb 0x4a3fc2, rgb 0xb0aaff⟩
  | .accentHover => ⟨rgb 0x33289e, rgb 0xd2ceff⟩
  | .bad => ⟨rgb 0xb42318, rgb 0xff9186⟩
  | .good => ⟨rgb 0x0a7447, rgb 0x64d69e⟩

def Line.tone : Line → Tone
  | .border => ⟨rgb 0xe3e5ea, rgb 0x272c36⟩
  | .control => ⟨rgb 0x80869a, rgb 0x737b8c⟩
  | .badLine => ⟨rgb 0xf2c4bd, rgb 0x5e2723⟩
  | .goodLine => ⟨rgb 0xb4e5c9, rgb 0x215c3f⟩

/-- Minimum contrast in tenths: 7:1 (WCAG 1.4.6) for body text and headings, 4.5:1 (WCAG 1.4.3)
for every other text colour. -/
def Ink.minimum : Ink → Nat
  | .text | .heading => 70
  | .muted | .accent | .accentHover | .bad | .good => 45

/-- In both themes, every text token meets its minimum contrast against every background token. -/
theorem ink_on_paper (t : Theme) (i : Ink) (p : Paper) :
    meets (i.tone.get t) (p.tone.get t) i.minimum = true := by
  have h : (Theme.all.all fun t => Ink.all.all fun i => Paper.all.all fun p =>
      meets (i.tone.get t) (p.tone.get t) i.minimum) = true := by decide +kernel
  simp only [List.all_eq_true] at h
  exact h t (Theme.mem_all t) i (Ink.mem_all i) p (Paper.mem_all p)

/-- In both themes, the control boundary has at least 3:1 against every background token. -/
theorem control_on_paper (t : Theme) (p : Paper) :
    meets (Line.control.tone.get t) (p.tone.get t) 30 = true := by
  have h : (Theme.all.all fun t => Paper.all.all fun p =>
      meets (Line.control.tone.get t) (p.tone.get t) 30) = true := by decide +kernel
  simp only [List.all_eq_true] at h
  exact h t (Theme.mem_all t) p (Paper.mem_all p)

/-! ## Stylesheet -/

private def tokenLine (name : String) (t : Tone) : String :=
  "  --rg-" ++ name ++ ": light-dark(" ++ t.light.css ++ ", " ++ t.dark.css ++ ");\n"

/-- The token block: every colour of the site, once, with its light and dark value. With no
`data-theme` the page follows the operating system; the theme control pins one side. -/
def tokenCss : String :=
  ":root {\n  color-scheme: light dark;\n" ++
  String.join (Paper.all.map fun p => tokenLine p.name p.tone) ++
  String.join (Ink.all.map fun i => tokenLine i.name i.tone) ++
  String.join (Line.all.map fun l => tokenLine l.name l.tone) ++ "}\n" ++
  ":root[data-theme=\"light\"] { color-scheme: light; }\n" ++
  ":root[data-theme=\"dark\"] { color-scheme: dark; }\n"

private def hexDigit (c : Char) : Bool := c.isDigit || ('a' ≤ c.toLower && c.toLower ≤ 'f')

private def identChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_'

private def colourFunctions : List String :=
  ["rgb(", "rgba(", "hsl(", "hsla(", "hwb(", "lab(", "lch(", "oklab(", "oklch(", "color("]

/-- Whether CSS text contains a hexadecimal colour literal (`#` followed by 3, 4, 6 or 8
hexadecimal digits that end the token, so `#cb1-input` is an identifier) or a colour function.
Named colours are not detected. -/
def hasColourLiteral (css : String) : Bool :=
  let rec go : List Char → Bool
    | [] => false
    | '#' :: rest =>
      let digits := rest.takeWhile hexDigit
      let next := rest.drop digits.length
      ([3, 4, 6, 8].contains digits.length && !(next.head?.any identChar)) || go rest
    | _ :: rest => go rest
  go css.toList || colourFunctions.any fun f => (css.toLower.splitOn f).length > 1

/-- The theme layer over Verso's stylesheets. Colours come only from the tokens; status is
always carried by a word or a `+`/`-`/✗/✓ marker as well as colour. -/
def layerCss : String := r##"
:root {
  --rg-font: -apple-system, BlinkMacSystemFont, "Segoe UI Variable Text", "Segoe UI", system-ui, Roboto, "Helvetica Neue", Arial, sans-serif;
  --rg-mono: ui-monospace, "JuliaMono", "SF Mono", "Cascadia Mono", "JetBrains Mono", Menlo, Consolas, "DejaVu Sans Mono", monospace;
  --rg-radius: 8px;
  /* A rounded square with ruler ticks cut out (even-odd), drawn as a mask in the accent colour. */
  --rg-mark: url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 24 24'%3E%3Cpath fill-rule='evenodd' d='M6 0h12a6 6 0 0 1 6 6v12a6 6 0 0 1-6 6H6a6 6 0 0 1-6-6V6a6 6 0 0 1 6-6ZM4 15h16v2H4ZM6 9h2v6H6Zm4 3h2v3h-2Zm4-3h2v6h-2Zm4 3h2v3h-2Z'/%3E%3C/svg%3E");
  --rg-search-icon: url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 24 24' fill='none' stroke='black' stroke-width='2' stroke-linecap='round'%3E%3Ccircle cx='11' cy='11' r='7'/%3E%3Cpath d='m20 20-3.5-3.5'/%3E%3C/svg%3E");
  --search-bar-width: 17rem;

  /* Verso's own variables, mapped onto the tokens */
  --verso-structure-font-family: var(--rg-font);
  --verso-text-font-family: var(--rg-font);
  --verso-code-font-family: var(--rg-mono);
  --verso-text-color: var(--rg-text);
  --verso-code-color: var(--rg-text);
  --verso-structure-color: var(--rg-heading);
  --verso-background-color: var(--rg-bg);
  --verso-surface-color: var(--rg-surface);
  --verso-border-color: var(--rg-border);
  --verso-link-color: var(--rg-accent);
  --verso-muted-color: var(--rg-muted);
  --verso-selected-color: var(--rg-accent-bg);
  --verso-tooltip-color: var(--rg-text);
  --verso-tooltip-bg-color: var(--rg-surface);
  --verso-tooltip-border-color: var(--rg-border);
  --verso-toc-background-color: var(--rg-bg-subtle);
  --verso-toc-text-color: var(--rg-text);
  --verso-toc-border-color: var(--rg-border);
  --verso-toc-resize-handle-color: var(--rg-control);
  --verso-burger-toc-hidden-color: var(--rg-text);
  --verso-burger-toc-visible-color: var(--rg-text);
  --verso-burger-toc-hidden-shadow-color: transparent;
  --verso-burger-toc-visible-shadow-color: transparent;
  --verso-content-max-width: 46rem;
  --verso-toc-width: 16rem;
  --verso-header-height: 3.25rem;
}
@media (max-width: 700px) { :root { --search-bar-width: 8.5rem; } }
@media (prefers-reduced-motion: reduce) {
  :root { --verso-toc-transition-time: 0s; }
  *, *::before, *::after { transition: none !important; animation: none !important; scroll-behavior: auto !important; }
}

/* Base */
html, body { background: var(--rg-bg); color: var(--rg-text); }
body { font-family: var(--rg-font); -webkit-font-smoothing: antialiased; }
p, dt, dd, li { line-height: 1.65; }
::selection { background: var(--rg-accent-bg); color: var(--rg-text); }
main a { color: var(--rg-accent); text-decoration: underline; text-decoration-thickness: 1px;
  text-underline-offset: 0.18em; text-decoration-color: color-mix(in srgb, currentColor 40%, transparent); }
main a:hover { color: var(--rg-accent-hover); text-decoration-color: currentColor; }
:focus-visible { outline: 2px solid var(--rg-accent); outline-offset: 2px; border-radius: 3px; }
pre, code { font-family: var(--rg-mono); font-variant-ligatures: none; }
main :not(pre) > code { font-size: 0.875em; background: var(--rg-surface); border: 1px solid var(--rg-border);
  border-radius: 5px; padding: 0.05em 0.3em; overflow-wrap: anywhere; }
main :is(p, li, dd, a) { overflow-wrap: break-word; }

/* Header: title, search, theme control */
header { background: var(--rg-bg); box-shadow: none; border-bottom: 1px solid var(--rg-border); gap: 0.75rem; padding-right: 1rem; }
.header-title { color: var(--rg-heading); font-size: 1.05rem; font-weight: 650; letter-spacing: -0.01em; }
.header-title h1 { white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
.header-title h1::before { content: ""; display: inline-block; vertical-align: -0.3em; margin-right: 0.55rem;
  width: 1.4rem; height: 1.4rem; background: var(--rg-accent);
  -webkit-mask: var(--rg-mark) center / contain no-repeat; mask: var(--rg-mark) center / contain no-repeat; }
#search-wrapper { position: static; flex: none; padding: 0; background: none; }
#search-wrapper .combobox .group { position: relative; }
#search-wrapper .combobox .group::before { content: ""; position: absolute; left: 0.6rem; top: 50%; width: 1rem; height: 1rem;
  transform: translateY(-50%); background: var(--rg-muted); pointer-events: none; z-index: 1;
  -webkit-mask: var(--rg-search-icon) center / contain no-repeat; mask: var(--rg-search-icon) center / contain no-repeat; }
#search-wrapper .combobox .cb_edit { border: 1px solid var(--rg-control); border-radius: var(--rg-radius);
  background: var(--rg-bg); color: var(--rg-text); padding: 0.4rem 0.7rem 0.4rem 2rem; font: 0.9rem var(--rg-font);
  white-space: nowrap; overflow: hidden; }
#search-wrapper .combobox .group.focus .cb_edit, #search-wrapper .combobox .group .cb_edit:hover { background: var(--rg-bg); outline: none; border-color: var(--rg-accent); }
#search-wrapper .cb_edit:empty::before { color: var(--rg-muted); font-family: var(--rg-font); }
#search-wrapper .more-results { color: var(--rg-muted); }
.rg-theme { display: inline-flex; flex: none; border: 1px solid var(--rg-control); border-radius: 999px; padding: 2px; gap: 2px; background: var(--rg-bg); }
.rg-theme button { all: unset; box-sizing: border-box; width: 1.9rem; height: 1.6rem; display: grid; place-items: center;
  border-radius: 999px; color: var(--rg-muted); cursor: pointer; }
.rg-theme button:hover { color: var(--rg-text); }
.rg-theme button[aria-pressed="true"] { background: var(--rg-accent-bg); color: var(--rg-accent); }
.rg-theme button:focus-visible { outline: 2px solid var(--rg-accent); outline-offset: 1px; }
.rg-theme svg { width: 1rem; height: 1rem; }
#toc .rg-theme { display: none; }

/* Sidebar */
#toc { border-right: none; }
#toc a { color: var(--rg-text); }
#toc a:hover { color: var(--rg-accent); text-decoration: none; }
#toc .split-tocs { margin-top: 1.25rem; padding: 0 0.75rem 0 0.25rem; }
#toc .split-toc { font-size: 0.9rem; margin-bottom: 1.25rem; }
#toc .split-toc .title { font-size: 0.75rem; font-weight: 650; letter-spacing: 0.06em; text-transform: uppercase; color: var(--rg-muted); }
#toc .split-toc .title a { color: inherit; }
#toc .split-toc label.toggle-split-toc::before { background-color: var(--rg-muted); }
#toc .split-toc table { border-left: 1px solid var(--rg-border); padding-left: 0; border-spacing: 0; margin-top: 0.35rem; }
#toc .split-toc td a { display: block; padding: 0.2rem 0.75rem; border-left: 2px solid transparent; margin-left: -1px; }
#toc .split-toc .current td:not(.num), #toc .split-toc .title .current { text-decoration: none; }
#toc .split-toc tr.current td a { color: var(--rg-accent); border-left-color: var(--rg-accent); font-weight: 600; }
#toc .split-toc a[href*="/RG"] { font-family: var(--rg-mono); font-size: 0.85rem; }
#toc .split-toc a[href*="/RG"][href*="-"] { font-family: var(--rg-font); font-size: 0.9rem; }
#meta-links { font-size: 0.85rem; padding: 0.75rem 1rem; border-top: 1px solid var(--rg-border); margin: 0; }
#meta-links a { color: var(--rg-muted); }
body:has(#toggle-toc:checked) .toc-backdrop { background-color: color-mix(in srgb, var(--rg-heading) 35%, transparent); }

/* Content */
.content-wrapper { padding: 1.75rem 2rem 4rem; }
main h1, main h2, main h3 { color: var(--rg-heading); font-family: var(--rg-font); letter-spacing: -0.015em; }
main h1 { font-size: 1.95rem; line-height: 1.25; font-weight: 700; margin: 0.25rem 0 0.75rem; text-wrap: balance; }
main .titlepage h1 { text-align: left; }
main h2 { font-size: 1.3rem; line-height: 1.35; font-weight: 650; margin: 2.75rem 0 0.75rem; }
main h3 { font-size: 1.02rem; line-height: 1.4; font-weight: 650; margin: 1.5rem 0 0.5rem; }
section > p, section > ul, section > ol { margin: 0.85rem 0; }
.permalink-widget > a { text-shadow: 0 0 0 var(--rg-muted); }
.content-wrapper > .prev-next-buttons:first-child { display: none; }
.prev-next-buttons { gap: 0.75rem; margin-top: 3.5rem; font-weight: 500; }
.prev-next-buttons > * { flex: 1 1 14rem; color: var(--rg-text); border: 1px solid var(--rg-border); border-radius: var(--rg-radius);
  padding: 0.7rem 0.9rem; font-size: 0.92rem; text-decoration: none; }
.prev-next-buttons > *:hover { border-color: var(--rg-accent); color: var(--rg-accent); }
.prev-next-buttons .arrow { font-size: 1rem; color: var(--rg-muted); }

/* Edition line */
.regula-edition { margin: 0 0 1.25rem; font-size: 0.8rem; line-height: 1.6; color: var(--rg-muted); }
.regula-edition p { margin: 0; }
.regula-edition a { color: var(--rg-muted); }
.regula-edition code { font-size: 0.95em; }
.regula-pill { font-weight: 600; color: var(--rg-accent); background: var(--rg-accent-bg); border-radius: 999px; padding: 0.05rem 0.55rem; }

/* Rule header: chips, then the problem as the lead and "What to do" (styled by adjacency) */
main section .regula-chips > li { margin: 0; }
.regula-chips { display: flex; flex-wrap: wrap; gap: 0.4rem; margin: 0 0 1.1rem; padding: 0; list-style: none; }
.regula-chip { font-size: 0.78rem; line-height: 1.5; border: 1px solid var(--rg-border); border-radius: 999px; padding: 0.05rem 0.6rem; color: var(--rg-muted); background: var(--rg-bg); }
.regula-chip strong { color: var(--rg-text); font-weight: 600; }
.regula-chip code { font-size: 0.95em; }
.regula-chip.is-error { color: var(--rg-bad); border-color: var(--rg-bad-line); background: var(--rg-bad-bg); font-weight: 600; }
.regula-chip.is-error strong { color: var(--rg-bad); }
.regula-chips + p { font-size: 1.1rem; line-height: 1.6; margin: 0 0 1rem; }
.regula-chips + p + p { border: 1px solid var(--rg-border); border-left: 3px solid var(--rg-accent); background: var(--rg-accent-bg);
  border-radius: var(--rg-radius); padding: 0.75rem 1rem; margin: 0 0 1.25rem; }
.regula-chips + p + p > strong:first-child { display: block; font-size: 0.72rem; letter-spacing: 0.07em; text-transform: uppercase; color: var(--rg-accent); }
.regula-facts { display: grid; grid-template-columns: fit-content(12rem) minmax(0, 1fr); gap: 0.35rem 1.25rem; margin: 1rem 0; font-size: 0.92rem; }
.regula-facts dt { color: var(--rg-muted); font-weight: 500; }
.regula-facts dd { margin: 0; overflow-wrap: anywhere; }
.regula-tags { display: inline-flex; flex-wrap: wrap; gap: 0.25rem; }
.regula-tag { font-size: 0.72rem; border-radius: 4px; padding: 0.02rem 0.4rem; background: var(--rg-surface); border: 1px solid var(--rg-border); color: var(--rg-text); white-space: nowrap; }

/* Checked example */
.regula-example h3 { font-size: 0.95rem; margin: 1.4rem 0 0.4rem; }
.regula-file, .regula-diff-panel { margin: 0.75rem 0 1rem; border: 1px solid var(--rg-border); border-radius: var(--rg-radius); overflow: hidden; background: var(--rg-surface); }
.regula-file > figcaption, .regula-diff-panel > figcaption { display: flex; flex-wrap: wrap; align-items: center; gap: 0.35rem 0.6rem; padding: 0.45rem 0.85rem;
  font-size: 0.8rem; color: var(--rg-muted); border-bottom: 1px solid var(--rg-border); background: var(--rg-bg); overflow-wrap: anywhere; }
.regula-file > figcaption code, .regula-diff-panel > figcaption code { background: none; border: 0; padding: 0; color: var(--rg-text); }
.regula-file > figcaption .regula-src { margin-left: auto; }
.regula-file.is-bad { border-left: 3px solid var(--rg-bad); }
.regula-file.is-good { border-left: 3px solid var(--rg-good); }
.regula-verdict { font-weight: 700; font-size: 0.72rem; letter-spacing: 0.06em; text-transform: uppercase; border-radius: 999px; padding: 0.05rem 0.55rem; }
.regula-verdict.is-bad { color: var(--rg-bad); background: var(--rg-bad-bg); border: 1px solid var(--rg-bad-line); }
.regula-verdict.is-good { color: var(--rg-good); background: var(--rg-good-bg); border: 1px solid var(--rg-good-line); }
pre.regula-code, pre.regula-diff { margin: 0; padding: 0.8rem 1rem; background: var(--rg-surface); color: var(--rg-text); border: 0; border-radius: 0;
  font-size: 0.85rem; line-height: 1.6; overflow-x: auto; white-space: pre; tab-size: 2; }
.regula-diff del, .regula-diff ins, .regula-diff .regula-keep { display: inline-block; box-sizing: border-box; min-width: calc(100% + 2rem);
  margin: 0 -1rem; padding: 0 1rem; text-decoration: none; color: var(--rg-text); }
.regula-diff del { background: var(--rg-del-bg); }
.regula-diff ins { background: var(--rg-ins-bg); }
.regula-diff .regula-keep { color: var(--rg-muted); }
.regula-finding { border: 1px solid var(--rg-bad-line); border-radius: var(--rg-radius); background: var(--rg-bad-bg); padding: 0.7rem 0.9rem; margin: 0.75rem 0 1rem; font-size: 0.9rem; }
.regula-finding p { margin: 0 0 0.35rem; overflow-wrap: anywhere; }
.regula-finding .regula-finding-head { display: flex; flex-wrap: wrap; align-items: center; gap: 0.35rem 0.5rem; }
.regula-finding code { background: none; border: 0; padding: 0; }
.regula-finding pre.regula-code { background: var(--rg-bg); border: 1px solid var(--rg-bad-line); border-radius: 6px; margin-top: 0.5rem;
  white-space: pre-wrap; overflow-wrap: anywhere; font-size: 0.82rem; }
.regula-badge { display: inline-block; border: 1px solid var(--rg-control); border-radius: 999px; padding: 0 0.5rem; font-size: 0.75rem; line-height: 1.55; color: var(--rg-text); background: var(--rg-bg); }
.regula-badge.is-error { border-color: var(--rg-bad-line); color: var(--rg-bad); font-weight: 600; }
.regula-impact-incomplete { border-style: dashed; }
details.regula-more { margin: 0.75rem 0 1rem; border: 1px solid var(--rg-border); border-radius: var(--rg-radius); padding: 0.55rem 0.9rem; font-size: 0.9rem; }
details.regula-more > summary { cursor: pointer; color: var(--rg-muted); font-weight: 550; }
details.regula-more[open] > summary { margin-bottom: 0.4rem; }
details.regula-more p { margin: 0.4rem 0; }

/* Tables and the rule index */
.regula-scroll { overflow-x: auto; max-width: 100%; }
table.regula-rules { width: 100%; border-collapse: collapse; font-size: 0.93rem; margin: 0.5rem 0 1rem; }
table.regula-rules caption { text-align: left; font-size: 0.85rem; color: var(--rg-muted); padding: 0 0 0.5rem; }
table.regula-rules thead th { font-size: 0.72rem; text-transform: uppercase; letter-spacing: 0.06em; color: var(--rg-muted); font-weight: 650;
  text-align: left; padding: 0.5rem 0.75rem; border-bottom: 1px solid var(--rg-border); }
table.regula-rules td, table.regula-rules th[scope=row] { padding: 0.65rem 0.75rem; border-bottom: 1px solid var(--rg-border); vertical-align: top; text-align: left; }
table.regula-rules tbody tr:hover { background: var(--rg-bg-subtle); }
table.regula-rules th[scope=row] a { font-family: var(--rg-mono); font-size: 0.85rem; font-weight: 600; text-decoration: none; white-space: nowrap; }
table.regula-rules th[scope=row] a code { background: none; border: 0; padding: 0; font-size: 1em; }
.regula-title { color: var(--rg-heading); font-weight: 550; }
main a.regula-title { color: var(--rg-heading); text-decoration: none; }
main a.regula-title:hover { color: var(--rg-accent); text-decoration: underline; }
.regula-sub { display: block; font-size: 0.78rem; color: var(--rg-muted); margin-top: 0.1rem; }
main:has(.regula-index) { --verso-content-max-width: 60rem; }
.regula-filters { display: flex; flex-wrap: wrap; align-items: end; gap: 0.6rem; margin: 1.25rem 0 0.75rem; }
.regula-filters label { display: grid; gap: 0.2rem; font-size: 0.75rem; font-weight: 600; color: var(--rg-muted); letter-spacing: 0.02em; }
.regula-filters select, .regula-filters input[type=reset] { font: 0.88rem var(--rg-font); color: var(--rg-text); background: var(--rg-bg);
  border: 1px solid var(--rg-control); border-radius: var(--rg-radius); padding: 0.35rem 0.55rem; min-height: 2.1rem; }
.regula-filters input[type=reset] { cursor: pointer; background: var(--rg-surface); }
.regula-index td:nth-child(3) { white-space: nowrap; }
.regula-index td:nth-child(4) { min-width: 18rem; }
tr.regula-no-match { display: none; }
tr.regula-no-match td { font-weight: 600; }

/* Phones: the theme control moves to the table-of-contents drawer; index rows become cards */
@media (max-width: 700px) {
  header > .rg-theme { display: none; }
  #toc .last { display: flex; flex-direction: column; gap: 0.5rem; }
  #toc .rg-theme { display: inline-flex; align-self: flex-start; margin: 0.25rem 1rem 1rem; }
  .content-wrapper { padding: 1.25rem 1rem 3rem; }
  main h1 { font-size: 1.6rem; }
  .permalink-widget.inline { display: none; }
  .regula-facts { grid-template-columns: minmax(0, 1fr); gap: 0.1rem; }
  .regula-facts dd { margin-bottom: 0.5rem; }
  .regula-index table.regula-rules thead { display: none; }
  .regula-index table.regula-rules, .regula-index table.regula-rules tbody, .regula-index table.regula-rules caption { display: block; }
  .regula-index table.regula-rules tr.regula-rule { display: grid; grid-template-columns: auto minmax(0, 1fr); gap: 0.2rem 0.75rem; padding: 0.7rem 0; border-bottom: 1px solid var(--rg-border); }
  .regula-index table.regula-rules tr.regula-rule > * { border: 0; padding: 0; }
  .regula-index table.regula-rules tr.regula-rule > td:nth-child(n+3) { grid-column: 2; }
}
"##

/-- The complete site stylesheet: the token block, then the theme layer. -/
def stylesheet : String := tokenCss ++ layerCss

/-- Stylesheet of the stand-alone pages outside Verso (the not-available page). -/
def plainPageCss : String :=
  tokenCss ++ "body{font-family:system-ui,sans-serif;line-height:1.5;max-width:44rem;margin:2rem auto;padding:0 1rem;" ++
  "color:var(--rg-text);background:var(--rg-bg)}a{color:var(--rg-accent)}code{font-family:ui-monospace,monospace}\n"

/-! Evaluated at build time: the theme layer outside the token block writes no colour literal,
and the detector finds the literal forms it names (controls, not proofs). -/
#guard !hasColourLiteral layerCss
#guard !hasColourLiteral (plainPageCss.drop tokenCss.length).toString
#guard hasColourLiteral "a{color:#abc}" && hasColourLiteral "a{color:rgb(1,2,3)}" && !hasColourLiteral "#cb1-input{}"
#guard hasColourLiteral tokenCss

end Regula.Site
