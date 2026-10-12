import Regula.Checker.PolicyCodec
import Regula.JsonCanon

/-! # The parse of compact JSON text

`parse_compress` proves, for every `Json` value whose object trees are search trees
(`JsonAgreement.Regular`), that `PolicyCodec.parse` of the text `PolicyCodec.compress` writes for
it, with a final newline, is the value with each object tree as the parser builds it
(`JsonCanon.canon`), which agrees with it (`JsonCanon.Regular.canon_agree`). For a value whose
object trees are already the parser's (`JsonCanon.Canonical`) the parse is the value itself
(`parse_compress_canonical`). Both are about the logical definitions of the parser and the
printer that callers run. The compiled code of the core functions they call that has
`implemented_by`, `extern` or a runtime override is trusted, since no kernel proof evaluates it.
Among them, `Nat.repr` runs `Nat.reprFast`, `String.push`, `String.append` and
`String.Pos.next` are `extern`, and `String.Pos.get` is overridden in the runtime
(`Init/Data/Repr.lean` and `Init/Data/String/`, v4.34.1).

The proof walks the text a character at a time. `At it cs` says that the parser's position `it`
is before exactly the characters `cs`; each lemma below advances it over the text one printed
part writes: a string's characters and escapes (`strCore_text`), a number's mantissa and exponent
(`num_text`), and the elements and members of arrays and objects (`value_text`). -/
namespace Regula.Checker.JsonRoundTrip
open Lean Std.Internal.Parsec Std.Internal.Parsec.String
open PolicyCodec JsonAgreement JsonCanon

/-- The input is at a position before exactly the characters `cs`. -/
def At (it : Input) (cs : List Char) : Prop := ∃ t, it.2.Splits t (String.ofList cs)

theorem At.start (text : String) : At ⟨text, text.startPos⟩ text.toList :=
  ⟨"", by simp⟩

theorem At.notEnd {it : Input} {c : Char} {cs : List Char} (h : At it (c :: cs)) :
    it.2 ≠ it.1.endPos := by
  obtain ⟨t, h⟩ := h
  have h' : it.2.Splits t (String.singleton c ++ String.ofList cs) := by simpa using h
  exact h'.ne_endPos_of_singleton

theorem At.get {it : Input} {c : Char} {cs : List Char} (h : At it (c :: cs)) (ne) :
    it.2.get ne = c := by
  obtain ⟨t, h⟩ := h
  have h' : it.2.Splits t (String.singleton c ++ String.ofList cs) := by simpa using h
  exact (h'.next).get_eq_of_singleton

theorem At.next {it : Input} {c : Char} {cs : List Char} (h : At it (c :: cs)) (ne) :
    At ⟨it.1, it.2.next ne⟩ cs := by
  obtain ⟨t, h⟩ := h
  have h' : it.2.Splits t (String.singleton c ++ String.ofList cs) := by simpa using h
  exact ⟨_, h'.next⟩

theorem At.atEnd {it : Input} (h : At it []) : it.2 = it.1.endPos := by
  obtain ⟨t, h⟩ := h
  exact h.eq_endPos_iff.mpr (by simp)

theorem At.remaining {it : Input} {cs : List Char} (h : At it cs) :
    remaining it = (String.ofList cs).utf8ByteSize := by
  obtain ⟨t, h⟩ := h
  rw [← h.remainingBytes_eq, String.Pos.remainingBytes_eq]
  rfl

theorem size_cons (c : Char) (cs : List Char) :
    (String.ofList (c :: cs)).utf8ByteSize = c.utf8Size + (String.ofList cs).utf8ByteSize := by
  simp

theorem size_append (a b : List Char) :
    (String.ofList (a ++ b)).utf8ByteSize =
      (String.ofList a).utf8ByteSize + (String.ofList b).utf8ByteSize := by
  simp

theorem peek!_at {it : Input} {c : Char} {cs : List Char} (h : At it (c :: cs)) :
    (peek! : Parser Char) it = .success it c := by
  have ne := h.notEnd
  have notEnd : ¬ it.2.IsAtEnd := by simpa [String.Pos.isAtEnd_iff] using ne
  simp only [peek!, Input.hasNext, Input.curr', notEnd]
  rw [dite_eq_left (by decide)]
  exact congrArg _ (h.get _)

theorem any_at {it : Input} {c : Char} {cs : List Char} (h : At it (c :: cs)) :
    ∃ it', At it' cs ∧ (any : Parser Char) it = .success it' c := by
  have ne := h.notEnd
  have notEnd : ¬ it.2.IsAtEnd := by simpa [String.Pos.isAtEnd_iff] using ne
  refine ⟨_, h.next ne, ?_⟩
  simp only [any, Input.hasNext, Input.curr', Input.next', notEnd]
  rw [dite_eq_left (by decide)]
  exact congrArg _ (h.get _)

theorem skip_at {it : Input} {c : Char} {cs : List Char} (h : At it (c :: cs)) :
    ∃ it', At it' cs ∧ (skip : Parser Unit) it = .success it' () := by
  have ne := h.notEnd
  have notEnd : ¬ it.2.IsAtEnd := by simpa [String.Pos.isAtEnd_iff] using ne
  refine ⟨_, h.next ne, ?_⟩
  simp only [skip, Input.hasNext, Input.next', notEnd]
  rw [dite_eq_left (by decide)]

theorem isEof_cons {it : Input} {c : Char} {cs : List Char} (h : At it (c :: cs)) :
    (isEof : Parser Bool) it = .success it false := by
  have ne := h.notEnd
  have notEnd : ¬ it.2.IsAtEnd := by simpa [String.Pos.isAtEnd_iff] using ne
  simp [isEof, Input.hasNext, notEnd]

theorem isEof_nil {it : Input} (h : At it []) :
    (isEof : Parser Bool) it = .success it true := by
  have atEnd : it.2.IsAtEnd := by rw [String.Pos.isAtEnd_iff]; exact h.atEnd
  simp [isEof, Input.hasNext, atEnd]

theorem eof_nil {it : Input} (h : At it []) :
    (eof : Parser Unit) it = .success it () := by
  have atEnd : it.2.IsAtEnd := by rw [String.Pos.isAtEnd_iff]; exact h.atEnd
  simp [eof, Input.hasNext, atEnd]

theorem bind_success {α β : Type} {f : Parser α} {g : α → Parser β} {it it' : Input} {a : α}
    (h : f it = .success it' a) : (f >>= g) it = g a it' := by
  show Std.Internal.Parsec.bind f g it = _
  simp only [Std.Internal.Parsec.bind, h]

theorem seq_success {β : Type} {f : Parser Unit} {g : Parser β} {it it' : Input}
    (h : f it = .success it' ()) : (do f; g) it = g it' := bind_success h

theorem pure_apply {α : Type} (a : α) (it : Input) : (pure a : Parser α) it = .success it a := rfl

/-- `skipWs` skips the leading whitespace of the rest. -/
theorem skipWs_at {it : Input} {cs : List Char} (h : At it cs) :
    At ⟨it.1, skipWs it.2⟩ (cs.dropWhile isWs) := by
  obtain ⟨s, p⟩ := it
  induction cs generalizing p with
  | nil =>
    have := h.atEnd
    simp only at this
    subst this
    rw [skipWs]
    simpa using h
  | cons c cs step =>
    have ne := h.notEnd
    have get := h.get ne
    rw [skipWs, dite_eq_left ne]
    simp only at get
    rw [get]
    by_cases white : isWs c = true
    · simp only [white, ite_true, List.dropWhile_cons]
      exact step _ (h.next ne)
    · simp only [white, Bool.false_eq_true, ite_false, List.dropWhile_cons]
      exact h

theorem ws_at {it : Input} {cs : List Char} (h : At it cs) :
    ∃ it', At it' (cs.dropWhile isWs) ∧ (PolicyCodec.ws : Parser Unit) it = .success it' () :=
  ⟨_, skipWs_at h, rfl⟩

theorem descend_lt {α : Type} {start it : Input}
    {k : (it : Input) → remaining it < remaining start → Result α}
    (h : remaining it < remaining start) : descend start k it = k it h := by
  simp [descend, h]

theorem stay_le {α : Type} {start it : Input}
    {k : (it : Input) → remaining it ≤ remaining start → Result α}
    (h : remaining it ≤ remaining start) : stay start k it = k it h := by
  simp [stay, h]


/-- The characters `escapeTo` appends for `c`. -/
def escChars (c : Char) : List Char := (escapeTo "" c).toList

theorem escapeTo_eq (acc : String) (c : Char) : escapeTo acc c = acc ++ escapeTo "" c := by
  unfold escapeTo
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    simp [← String.append_singleton, String.append_assoc]

theorem strCore_nil {acc : String} {rest : List Char} {it : Input} (h : At it ('"' :: rest)) :
    ∃ it', At it' rest ∧ strCore acc it = .success it' acc := by
  obtain ⟨it1, h1, skipped⟩ := skip_at h
  refine ⟨it1, h1, ?_⟩
  rw [strCore]
  show (peek! >>= _) it = _
  rw [bind_success (peek!_at h)]
  simp only [beq_self_eq_true, ite_true]
  rw [seq_success skipped]
  rfl


/-- A character that `escapeTo` writes as itself. -/
def Plain (c : Char) : Prop := c ≠ '"' ∧ c ≠ '\\' ∧ 0x20 ≤ c.val

theorem escChars_plain {c : Char} (plain : Plain c) : escChars c = [c] := by
  obtain ⟨q, b, v⟩ := plain
  have n : c ≠ '\n' := by rintro rfl; exact absurd v (by decide)
  have r : c ≠ '\r' := by rintro rfl; exact absurd v (by decide)
  simp [escChars, escapeTo, q, b, n, r, v]

theorem strCore_plain {acc : String} {c : Char} {rest : List Char} {it : Input}
    (plain : Plain c) (h : At it (c :: rest)) :
    ∃ it', At it' rest ∧ strCore acc it = strCore (acc.push c) it' := by
  obtain ⟨it1, h1, read⟩ := any_at h
  refine ⟨it1, h1, ?_⟩
  obtain ⟨q, b, v⟩ := plain
  rw [strCore]
  show (peek! >>= _) it = _
  rw [bind_success (peek!_at h)]
  have hi : c.val ≤ 1114111 := by
    have := c.valid
    rw [UInt32.le_iff_toNat_le]
    rcases this with h | ⟨_, h⟩ <;> simp at h ⊢ <;> omega
  rw [ite_eq_right (by simp [q])]
  rw [bind_success read]
  rw [ite_eq_right (by simp [b]), ite_eq_left (by simp [v, hi])]
  have lt : remaining it1 < remaining it := by
    rw [h.remaining, h1.remaining, size_cons]
    have := Char.utf8Size_pos c
    omega
  rw [descend_lt lt]




/-- The value of a hexadecimal digit, as `Json.Parser.hexChar` reads it. -/
def hexVal (c : Char) : Option UInt16 :=
  if '0' <= c && c <= '9' then some (c.val - '0'.val).toUInt16
  else if 'a' <= c && c <= 'f' then some (c.val - 'a'.val + 10).toUInt16
  else if 'A' <= c && c <= 'F' then some (c.val - 'A'.val + 10).toUInt16
  else none

theorem hexVal_digitChar : ∀ k < 16, hexVal (Nat.digitChar k) = some k.toUInt16 := by decide

theorem hexChar_at {c : Char} {v : UInt16} (hv : hexVal c = some v) {rest : List Char}
    {it : Input} (h : At it (c :: rest)) :
    ∃ it', At it' rest ∧ Json.Parser.hexChar it = .success it' v := by
  obtain ⟨it1, h1, read⟩ := any_at h
  refine ⟨it1, h1, ?_⟩
  unfold Json.Parser.hexChar
  rw [bind_success read]
  unfold hexVal at hv
  split at hv
  · rw [ite_eq_left ‹_›]; cases hv; rfl
  · rw [ite_eq_right ‹_›]
    split at hv
    · rw [ite_eq_left ‹_›]; cases hv; rfl
    · rw [ite_eq_right ‹_›]
      split at hv
      · rw [ite_eq_left ‹_›]; cases hv; rfl
      · cases hv

theorem escapedChar_at {c e : Char} {rest : List Char} {it : Input}
    (pair : (c, e) ∈ [('\\', '\\'), ('"', '"'), ('n', '\n'), ('r', '\x0d')])
    (h : At it (c :: rest)) :
    ∃ it', At it' rest ∧ Json.Parser.escapedChar it = .success it' e := by
  obtain ⟨it1, h1, read⟩ := any_at h
  refine ⟨it1, h1, ?_⟩
  unfold Json.Parser.escapedChar
  rw [bind_success read]
  simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at pair
  rcases pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem control_arith : ∀ n < 32,
    ∀ v1 v2 v3 v4, hexVal (Nat.digitChar (n / 4096)) = some v1 →
      hexVal (Nat.digitChar ((n % 4096) / 256)) = some v2 →
      hexVal (Nat.digitChar ((n % 256) / 16)) = some v3 →
      hexVal (Nat.digitChar (n % 16)) = some v4 →
      ((v1 <<< 12) ||| (v2 <<< 8) ||| (v3 <<< 4) ||| v4) < 0xD800 ∧
        ((v1 <<< 12) ||| (v2 <<< 8) ||| (v3 <<< 4) ||| v4).toUInt32 = n.toUInt32 := by
  intro n hn v1 v2 v3 v4 h1 h2 h3 h4
  rw [hexVal_digitChar _ (by omega)] at h1 h2 h3 h4
  cases h1; cases h2; cases h3; cases h4
  revert n
  decide



theorem strCore_backslash {acc : String} {e : Char} {tail rest : List Char} {it : Input}
    (esc : ∀ it, At it (tail ++ rest) →
      ∃ it', At it' rest ∧ Json.Parser.escapedChar it = .success it' e)
    (h : At it ('\\' :: (tail ++ rest))) :
    ∃ it', At it' rest ∧ strCore acc it = strCore (acc.push e) it' := by
  obtain ⟨it1, h1, read⟩ := any_at h
  obtain ⟨it2, h2, escaped⟩ := esc it1 h1
  refine ⟨it2, h2, ?_⟩
  rw [strCore]
  show (peek! >>= _) it = _
  rw [bind_success (peek!_at h), ite_eq_right (by decide), bind_success read,
    ite_eq_left (by decide), bind_success escaped]
  have lt : remaining it2 < remaining it := by
    rw [h.remaining, h2.remaining, size_cons, size_append]
    have := Char.utf8Size_pos '\\'
    omega
  rw [descend_lt lt]

theorem escapedChar_u {c : Char} {n : Nat} (hn : n = c.toNat) (small : n < 32) {rest : List Char}
    {it : Input}
    (h : At it ('u' :: Nat.digitChar (n / 4096) :: Nat.digitChar ((n % 4096) / 256) ::
      Nat.digitChar ((n % 256) / 16) :: Nat.digitChar (n % 16) :: rest)) :
    ∃ it', At it' rest ∧ Json.Parser.escapedChar it = .success it' c := by
  obtain ⟨it1, h1, read⟩ := any_at h
  obtain ⟨it2, h2, r1⟩ := hexChar_at (hexVal_digitChar _ (by omega)) h1
  obtain ⟨it3, h3, r2⟩ := hexChar_at (hexVal_digitChar _ (by omega)) h2
  obtain ⟨it4, h4, r3⟩ := hexChar_at (hexVal_digitChar _ (by omega)) h3
  obtain ⟨it5, h5, r4⟩ := hexChar_at (hexVal_digitChar _ (by omega)) h4
  refine ⟨it5, h5, ?_⟩
  obtain ⟨below, value⟩ := control_arith n small _ _ _ _ (hexVal_digitChar _ (by omega))
    (hexVal_digitChar _ (by omega)) (hexVal_digitChar _ (by omega)) (hexVal_digitChar _ (by omega))
  unfold Json.Parser.escapedChar
  rw [bind_success read]
  simp only
  rw [bind_success r1, bind_success r2, bind_success r3, bind_success r4]
  rw [dite_eq_left below]
  show ParseResult.success it5 _ = _
  congr 1
  apply Char.ext
  show (_ : UInt16).toUInt32 = c.val
  rw [value, hn, ← Char.toNat_val]
  exact UInt32.ofNat_toNat



/-- **Each character's escape is read back as the character.** -/
theorem strCore_char {acc : String} {c : Char} {rest : List Char} {it : Input}
    (h : At it (escChars c ++ rest)) :
    ∃ it', At it' rest ∧ strCore acc it = strCore (acc.push c) it' := by
  by_cases q : c = '"'
  · subst q
    exact strCore_backslash (tail := ['"']) (fun _ h => escapedChar_at (by simp) h) h
  by_cases b : c = '\\'
  · subst b
    exact strCore_backslash (tail := ['\\']) (fun _ h => escapedChar_at (by simp) h) h
  by_cases n : c = '\n'
  · subst n
    exact strCore_backslash (tail := ['n']) (fun _ h => escapedChar_at (by simp) h) h
  by_cases r : c = '\r'
  · subst r
    exact strCore_backslash (tail := ['r']) (fun _ h => escapedChar_at (by simp) h) h
  by_cases v : 0x20 ≤ c.val
  · exact strCore_plain ⟨q, b, v⟩ (by rwa [escChars_plain ⟨q, b, v⟩] at h)
  · have small : c.toNat < 32 := by
      rw [UInt32.le_iff_toNat_le] at v
      simp at v
      omega
    have chars : escChars c = '\\' :: 'u' :: Nat.digitChar (c.toNat / 4096) ::
        Nat.digitChar ((c.toNat % 4096) / 256) :: Nat.digitChar ((c.toNat % 256) / 16) ::
        Nat.digitChar (c.toNat % 16) :: [] := by
      simp [escChars, escapeTo, q, b, n, r, v]
    rw [chars] at h
    exact strCore_backslash (tail := ['u', _, _, _, _])
      (fun _ h => escapedChar_u rfl small h) h

/-- The characters of the text of `s` inside its quotes. -/
def strChars (s : String) : List Char := s.toList.flatMap escChars

/-- **A string's text is read back as the string.** -/
theorem strCore_text (cs : List Char) {acc : String} {rest : List Char} {it : Input}
    (h : At it (cs.flatMap escChars ++ '"' :: rest)) :
    ∃ it', At it' rest ∧ strCore acc it = .success it' (cs.foldl String.push acc) := by
  induction cs generalizing acc it with
  | nil => exact strCore_nil h
  | cons c cs step =>
    simp only [List.flatMap_cons, List.append_assoc] at h
    obtain ⟨it1, h1, eq⟩ := strCore_char h
    rw [eq]
    exact step h1


theorem digit_test (c : Char) : ('0' <= c && c <= '9') = c.isDigit := by
  simp [Char.isDigit, Char.le_def]

theorem digit_value {c : Char} (d : c.isDigit = true) :
    (c.val - '0'.val).toNat = c.toNat - '0'.toNat := by
  simp [Char.isDigit] at d
  rw [UInt32.toNat_sub_of_le]
  · rfl
  · simpa [UInt32.le_iff_toNat_le] using d.1

/-- The rest does not begin with a digit. -/
def NoDigit (rest : List Char) : Prop := ∀ c, rest.head? = some c → c.isDigit = false

theorem natCore_digits (ds : List Char) {acc : Nat} {rest : List Char} {it : Input}
    (digits : ∀ d ∈ ds, d.isDigit = true) (stop : NoDigit rest) (h : At it (ds ++ rest)) :
    ∃ it', At it' rest ∧ natCore acc it = .success it' (Nat.ofDigitChars 10 ds acc) := by
  induction ds generalizing acc it with
  | nil =>
    refine ⟨it, by simpa using h, ?_⟩
    rw [natCore]
    show (isEof >>= _) it = _
    cases rest with
    | nil =>
      rw [bind_success (isEof_nil (by simpa using h))]
      rfl
    | cons c cs =>
      have stopped := stop c rfl
      rw [bind_success (isEof_cons (by simpa using h))]
      simp only [Bool.false_eq_true, ite_false]
      rw [bind_success (peek!_at (by simpa using h)), digit_test, stopped]
      rfl
  | cons d ds step =>
    have isDigit := digits d List.mem_cons_self
    have h' : At it (d :: (ds ++ rest)) := by simpa using h
    obtain ⟨it1, h1, skipped⟩ := skip_at h'
    obtain ⟨it2, h2, eq⟩ := step (acc := 10 * acc + (d.toNat - '0'.toNat))
      (fun d m => digits d (List.mem_cons_of_mem _ m)) h1
    refine ⟨it2, h2, ?_⟩
    rw [natCore]
    show (isEof >>= _) it = _
    rw [bind_success (isEof_cons h')]
    simp only [Bool.false_eq_true, ite_false]
    rw [bind_success (peek!_at h'), digit_test, isDigit]
    simp only [ite_true]
    rw [seq_success skipped]
    have lt : remaining it1 < remaining it := by
      rw [h'.remaining, h1.remaining, size_cons]
      have := Char.utf8Size_pos d
      omega
    rw [descend_lt lt, digit_value isDigit, Nat.ofDigitChars_cons, eq]

theorem lookahead_at {p : Char → Prop} [DecidablePred p] {desc : String} {c : Char}
    {rest : List Char} {it : Input} (holds : p c) (h : At it (c :: rest)) :
    Json.Parser.lookahead p desc it = .success it () := by
  unfold Json.Parser.lookahead
  rw [bind_success (peek!_at h), ite_eq_left holds]
  rfl

theorem toDigits_digits (k : Nat) : ∀ d ∈ Nat.toDigits 10 k, d.isDigit = true :=
  fun _ m => Nat.isDigit_of_mem_toDigits (by decide) (by decide) m

theorem toDigits_head (k : Nat) (pos : 0 < k) :
    ∃ d ds, Nat.toDigits 10 k = d :: ds ∧ '1' ≤ d ∧ d ≤ '9' := by
  induction k using Nat.strongRecOn with
  | ind k step =>
    rw [Nat.toDigits_eq_ite (by decide)]
    split
    · refine ⟨_, [], rfl, ?_⟩
      have : k < 10 := ‹_›
      clear step
      revert this pos
      revert k
      decide
    · obtain ⟨d, ds, eq, low, high⟩ := step (k / 10) (by omega) (by omega)
      exact ⟨d, ds ++ [Nat.digitChar (k % 10)], by rw [eq]; rfl, low, high⟩

theorem nat_repr (k : Nat) {rest : List Char} {it : Input} (stop : NoDigit rest)
    (h : At it (Nat.toDigits 10 k ++ rest)) :
    ∃ it', At it' rest ∧ nat it = .success it' k := by
  unfold nat
  by_cases zero : k = 0
  · subst zero
    rw [Nat.toDigits_zero] at h
    obtain ⟨it1, h1, skipped⟩ := skip_at h
    refine ⟨it1, h1, ?_⟩
    rw [bind_success (peek!_at h), ite_eq_left (by decide), seq_success skipped]
    rfl
  · obtain ⟨d, ds, eq, low, high⟩ := toDigits_head k (by omega)
    obtain ⟨it1, h1, read⟩ := natCore_digits (acc := 0) _ (toDigits_digits k) stop h
    refine ⟨it1, h1, ?_⟩
    rw [eq] at h
    have notZero : (d == '0') = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      rintro rfl
      exact absurd low (by decide)
    rw [bind_success (peek!_at h), notZero]
    simp only [Bool.false_eq_true, ite_false]
    unfold natNonZero
    refine (bind_success (g := fun _ => (natCore 0 : Parser Nat))
      (lookahead_at (by simp [low, high]) h)).trans ?_
    rw [read, Nat.ofDigitChars_ten_toDigits]

/-- What can follow a value in compact JSON text: nothing, a separator, a closing bracket or the
final newline. -/
def Follow (rest : List Char) : Prop :=
  ∀ c, rest.head? = some c → c = ',' ∨ c = ']' ∨ c = '}' ∨ c = '\n'

theorem Follow.noDigit {rest : List Char} (follow : Follow rest) : NoDigit rest := by
  intro c head
  rcases follow c head with rfl | rfl | rfl | rfl <;> rfl

theorem int_repr_toList (m : Int) :
    m.repr.toList = (if m < 0 then ['-'] else []) ++ Nat.toDigits 10 m.natAbs := by
  cases m with
  | ofNat k => simp [Int.repr, Nat.toList_repr]
  | negSucc k =>
    simp only [Int.repr, String.toList_append, Nat.toList_repr]
    simp [Int.negSucc_lt_zero, Int.natAbs_negSucc]

/-- The integer part: `numWithDecimals` reads `m.repr` back as `m`, when no `.` follows. -/
theorem numWithDecimals_repr (m : Int) {rest : List Char} {it : Input} (stop : NoDigit rest)
    (noDot : ∀ c, rest.head? = some c → c ≠ '.') (h : At it (m.repr.toList ++ rest)) :
    ∃ it', At it' rest ∧ numWithDecimals it = .success it' (JsonNumber.fromInt m) := by
  rw [int_repr_toList] at h
  -- The sign.
  obtain ⟨it1, h1, sign⟩ : ∃ it1, At it1 (Nat.toDigits 10 m.natAbs ++ rest) ∧
      Json.Parser.numSign it = .success it1 (if m < 0 then -1 else 1) := by
    unfold Json.Parser.numSign
    by_cases neg : m < 0
    · simp only [neg, ite_true, List.cons_append, List.nil_append] at h
      obtain ⟨it1, h1, skipped⟩ := skip_at h
      refine ⟨it1, h1, ?_⟩
      rw [bind_success (peek!_at h), ite_eq_left (by decide), seq_success skipped]
      simp [neg]; rfl
    · simp only [neg, ite_false, List.nil_append] at h
      obtain ⟨d, ds, eq, isDig⟩ : ∃ d ds, Nat.toDigits 10 m.natAbs = d :: ds ∧ d.isDigit := by
        obtain ⟨d, ds, eq⟩ :=
          List.exists_cons_of_ne_nil (Nat.toDigits_ne_nil (b := 10) (n := m.natAbs))
        exact ⟨d, ds, eq, toDigits_digits _ d (by rw [eq]; exact List.mem_cons_self)⟩
      refine ⟨it, h, ?_⟩
      rw [eq] at h
      rw [bind_success (peek!_at h)]
      have : (d == '-') = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        rintro rfl
        exact absurd isDig (by decide)
      rw [this]
      simp [neg]; rfl
  obtain ⟨it2, h2, whole⟩ := nat_repr m.natAbs stop h1
  refine ⟨it2, h2, ?_⟩
  unfold numWithDecimals
  rw [bind_success sign, bind_success whole]
  have value : (if m < 0 then (-1 : Int) else 1) * (m.natAbs : Int) = m := by
    split <;> omega
  cases rest with
  | nil =>
    rw [bind_success (isEof_nil h2)]
    simp only [ite_true, value]
    rfl
  | cons c cs =>
    rw [bind_success (isEof_cons h2)]
    simp only [Bool.false_eq_true, ite_false]
    rw [bind_success (peek!_at h2)]
    have notDot : (c == '.') = false := by simpa using noDot c rfl
    rw [notDot]
    simp only [Bool.false_eq_true, ite_false, value]
    rfl

/-- The characters of the text of a number. -/
theorem numberText_toList (n : JsonNumber) :
    (numberText n).toList = n.mantissa.repr.toList ++
      (if n.exponent = 0 then [] else 'e' :: '-' :: Nat.toDigits 10 n.exponent) := by
  unfold numberText
  split <;> simp [Nat.toList_repr, *]

/-- **A number's text is read back as the number**, mantissa and exponent, when what follows it
can follow a value. -/
theorem num_text (n : JsonNumber) {rest : List Char} {it : Input} (follow : Follow rest)
    (h : At it ((numberText n).toList ++ rest)) :
    ∃ it', At it' rest ∧ num it = .success it' n := by
  obtain ⟨m, e⟩ := n
  rw [numberText_toList] at h
  simp only at h
  unfold num
  by_cases zero : e = 0
  · subst zero
    simp only [ite_true, List.append_nil] at h
    obtain ⟨it1, h1, int⟩ := numWithDecimals_repr m follow.noDigit
      (fun c head => by rcases follow c head with rfl | rfl | rfl | rfl <;> decide) h
    refine ⟨it1, h1, ?_⟩
    rw [bind_success int]
    unfold exponent
    cases rest with
    | nil =>
      rw [bind_success (isEof_nil h1)]
      rfl
    | cons c cs =>
      rw [bind_success (isEof_cons h1)]
      simp only [Bool.false_eq_true, ite_false]
      rw [bind_success (peek!_at h1)]
      have : (c == 'e' || c == 'E') = false := by
        rcases follow c rfl with rfl | rfl | rfl | rfl <;> decide
      rw [this]
      rfl
  · simp only [zero, ite_false, List.append_assoc, List.cons_append] at h
    obtain ⟨it1, h1, int⟩ := numWithDecimals_repr m (rest := 'e' :: _)
      (fun c head => by cases head; decide) (fun c head => by cases head; decide) h
    obtain ⟨it2, h2, skipE⟩ := skip_at h1
    obtain ⟨it3, h3, skipMinus⟩ := skip_at h2
    obtain ⟨d, ds, eq, isDig⟩ : ∃ d ds, Nat.toDigits 10 e = d :: ds ∧ d.isDigit := by
      obtain ⟨d, ds, eq⟩ := List.exists_cons_of_ne_nil (Nat.toDigits_ne_nil (b := 10) (n := e))
      exact ⟨d, ds, eq, toDigits_digits _ d (by rw [eq]; exact List.mem_cons_self)⟩
    obtain ⟨it4, h4, digits⟩ := natCore_digits (acc := 0) _ (toDigits_digits e) follow.noDigit h3
    refine ⟨it4, h4, ?_⟩
    rw [bind_success int]
    unfold exponent
    rw [bind_success (isEof_cons h1)]
    simp only [Bool.false_eq_true, ite_false]
    rw [bind_success (peek!_at h1)]
    simp only [show ('e' == 'e' || 'e' == 'E') = true from rfl, ite_true]
    rw [seq_success skipE, bind_success (peek!_at h2), ite_eq_left (by decide),
      seq_success skipMinus]
    unfold natMaybeZero
    rw [eq] at h3
    have look := lookahead_at (p := fun c => (decide ('0' ≤ c) && decide (c ≤ '9')) = true)
      (desc := "0-9") (by rw [digit_test]; exact isDig) h3
    refine (bind_success (g := fun _ => (_ : Parser JsonNumber)) (bind_success
      (g := fun _ => (natCore 0 : Parser Nat)) look |>.trans digits)).trans ?_
    rw [Nat.ofDigitChars_ten_toDigits]
    simp [JsonNumber.shiftr, JsonNumber.fromInt]
    rfl


/-! ### The printed text -/

theorem stringTo_eq (acc s : String) :
    stringTo acc s = acc ++ "\"" ++ String.ofList (strChars s) ++ "\"" := by
  unfold stringTo strChars
  rw [String.foldl_eq_foldl_toList]
  suffices ∀ (cs : List Char) (acc : String),
      cs.foldl escapeTo acc = acc ++ String.ofList (cs.flatMap escChars) by
    rw [this]
    simp [String.append_assoc, ← String.append_singleton]
  intro cs
  induction cs with
  | nil => simp
  | cons c cs step =>
    intro acc
    rw [List.foldl_cons, step, escapeTo_eq]
    simp [escChars, String.append_assoc]

/-- The text of a member: its name, a colon and its value. -/
def memberText (member : String × Json) : String :=
  stringTo "" member.1 ++ ":" ++ compress member.2

/-- The text of members after `first` (whether none came before), each after a comma when one
came before it. -/
def sepText (first : Bool) : List (String × Json) → String
  | [] => ""
  | member :: rest => (if first then "" else ",") ++ memberText member ++ sepText false rest

/-- The text of array elements, separated by commas. -/
def elemsText : List Json → String
  | [] => ""
  | [j] => compress j
  | j :: rest => compress j ++ "," ++ elemsText rest

theorem sepText_append (first : Bool) (ms ns : List (String × Json)) :
    sepText first (ms ++ ns) = sepText first ms ++ sepText (first && ms.isEmpty) ns := by
  induction ms generalizing first with
  | nil => simp [sepText]
  | cons m ms step => simp [sepText, step, String.append_assoc]

mutual
theorem printTo_eq (acc : String) (j : Json) : printTo acc j = acc ++ compress j := by
  match j with
  | .null => simp [printTo, compress]
  | .bool b => simp [printTo, compress]
  | .num n => simp [printTo, compress]
  | .str s => simp [printTo, compress, stringTo_eq, String.append_assoc]
  | .arr ⟨elems⟩ =>
    simp only [compress, printTo, elemsTo_eq, ← String.append_singleton, String.append_assoc]
    simp
  | .obj ⟨⟨fields⟩⟩ =>
    simp only [compress, printTo, fieldsTo_eq, ← String.append_singleton, String.append_assoc]
    simp
theorem elemsTo_eq (acc : String) (elems : List Json) :
    elemsTo acc elems = acc ++ elemsText elems := by
  match elems with
  | [] => simp [elemsTo, elemsText]
  | [j] => simp [elemsTo, elemsText, printTo_eq]
  | j :: k :: rest =>
    simp only [elemsTo, elemsTo_eq, printTo_eq, elemsText]
    simp [← String.append_singleton, String.append_assoc]
theorem fieldsTo_eq (acc : String) (first : Bool) (fields : JsonAgreement.Fields) :
    fieldsTo acc first fields =
      (acc ++ sepText first (members fields), first && (members fields).isEmpty) := by
  match fields with
  | .leaf => simp [fieldsTo, sepText]
  | .inner size key value left right =>
    simp only [fieldsTo, fieldsTo_eq, printTo_eq, stringTo_eq, members_inner, sepText_append]
    cases first <;> cases (members left).isEmpty <;>
      simp [sepText, memberText, stringTo_eq, ← String.append_singleton, ← String.append_assoc] <;>
      simp only [String.append_assoc, show ("," ++ "\"" : String) = ",\"" from rfl]
end


theorem compress_null : compress .null = "null" := rfl

theorem compress_bool (b : Bool) : compress (.bool b) = if b then "true" else "false" := by
  simp [compress, printTo]

theorem compress_num (n : JsonNumber) : compress (.num n) = numberText n := by
  simp [compress, printTo]

theorem compress_str (s : String) :
    compress (.str s) = "\"" ++ String.ofList (strChars s) ++ "\"" := by
  simp [compress, printTo, stringTo_eq]

theorem compress_arr (elems : List Json) :
    compress (.arr ⟨elems⟩) = "[" ++ elemsText elems ++ "]" := by
  simp only [compress, printTo, elemsTo_eq, ← String.append_singleton]
  rfl

theorem compress_obj (fields : JsonAgreement.Fields) :
    compress (.obj ⟨⟨fields⟩⟩) = "{" ++ sepText true (members fields) ++ "}" := by
  simp only [compress, printTo, fieldsTo_eq, ← String.append_singleton]
  rfl

/-- A character a value's text can begin with. -/
def Start (c : Char) : Prop :=
  c = 'n' ∨ c = 't' ∨ c = 'f' ∨ c = '"' ∨ c = '[' ∨ c = '{' ∨ c = '-' ∨ c.isDigit = true

theorem Start.facts {c : Char} (start : Start c) :
    isWs c = false ∧ (c == ']') = false ∧ (c == '}') = false := by
  rcases start with rfl | rfl | rfl | rfl | rfl | rfl | rfl | digit
  all_goals try decide
  refine ⟨?_, ?_, ?_⟩
  · cases white : isWs c
    · rfl
    · simp only [isWs, Bool.or_eq_true, decide_eq_true_eq] at white
      rcases white with ((rfl | rfl) | rfl) | rfl <;> exact absurd digit (by decide)
  · cases same : (c == ']')
    · rfl
    · rw [beq_iff_eq] at same
      subst same
      exact absurd digit (by decide)
  · cases same : (c == '}')
    · rfl
    · rw [beq_iff_eq] at same
      subst same
      exact absurd digit (by decide)

theorem compress_head (j : Json) : ∃ c cs, (compress j).toList = c :: cs ∧ Start c := by
  match j with
  | .null => exact ⟨'n', _, rfl, .inl rfl⟩
  | .bool true => exact ⟨'t', ['r', 'u', 'e'], by simp [compress_bool], .inr (.inl rfl)⟩
  | .bool false =>
    exact ⟨'f', ['a', 'l', 's', 'e'], by simp [compress_bool], .inr (.inr (.inl rfl))⟩
  | .str s =>
    exact ⟨'"', strChars s ++ ['"'], by simp [compress_str], .inr (.inr (.inr (.inl rfl)))⟩
  | .arr ⟨elems⟩ =>
    exact ⟨'[', (elemsText elems).toList ++ [']'], by simp [compress_arr],
      .inr (.inr (.inr (.inr (.inl rfl))))⟩
  | .obj ⟨⟨fields⟩⟩ =>
    exact ⟨'{', (sepText true (members fields)).toList ++ ['}'], by simp [compress_obj],
      .inr (.inr (.inr (.inr (.inr (.inl rfl)))))⟩
  | .num n =>
    rw [compress_num, numberText_toList, int_repr_toList]
    by_cases negative : n.mantissa < 0
    · exact ⟨'-', _ ++ _, by simp [negative]; rfl,
        .inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))⟩
    · obtain ⟨d, ds, eq⟩ := List.exists_cons_of_ne_nil
        (Nat.toDigits_ne_nil (b := 10) (n := n.mantissa.natAbs))
      refine ⟨d, ds ++ _, by simp [negative, eq]; rfl,
        .inr (.inr (.inr (.inr (.inr (.inr (.inr ?_))))))⟩
      exact toDigits_digits _ d (by rw [eq]; exact List.mem_cons_self)

theorem dropWhile_compress (j : Json) (rest : List Char) :
    ((compress j).toList ++ rest).dropWhile isWs = (compress j).toList ++ rest := by
  obtain ⟨c, cs, eq, start⟩ := compress_head j
  rw [eq, List.cons_append, List.dropWhile_cons, start.facts.1]
  rfl

theorem chars_at (cs : List Char) {rest : List Char} {it : Input} (h : At it (cs ++ rest)) :
    ∃ it', At it' rest ∧ chars cs it = .success it' () := by
  induction cs generalizing it with
  | nil => exact ⟨it, h, rfl⟩
  | cons c cs step =>
    obtain ⟨it1, h1, read⟩ := any_at h
    obtain ⟨it2, h2, eq⟩ := step h1
    refine ⟨it2, h2, ?_⟩
    simp only [chars]
    rw [bind_success read, ite_eq_left rfl, eq]

theorem literal_at (s : String) {rest : List Char} {it : Input} (h : At it (s.toList ++ rest)) :
    ∃ it', At it' rest ∧ literal s it = .success it' () := by
  obtain ⟨it1, h1, eq⟩ := chars_at s.toList h
  exact ⟨it1, h1, by simp only [literal, eq]⟩

theorem foldl_push (s : String) : s.toList.foldl String.push "" = s := by
  suffices ∀ (cs : List Char) (acc : String), cs.foldl String.push acc = acc ++ String.ofList cs by
    rw [this, String.empty_append, String.ofList_toList]
  intro cs
  induction cs with
  | nil => simp
  | cons c cs step =>
    intro acc
    rw [List.foldl_cons, step]
    simp [← String.append_singleton, String.append_assoc]


/-! ### Arrays and objects -/

/-- `value` reads the text of `j` back as `canon j`, from any position before that text and a
rest that can follow a value, and skips the whitespace after it. -/
def ValueText (j : Json) : Prop :=
  ∀ (rest : List Char) (it : Input), Follow rest → At it ((compress j).toList ++ rest) →
    ∃ it', At it' (rest.dropWhile isWs) ∧ value it = .success it' (canon j)

theorem dropWhile_solid {c : Char} (rest : List Char) (solid : isWs c = false) :
    (c :: rest).dropWhile isWs = c :: rest := by
  rw [List.dropWhile_cons, solid]
  rfl

theorem dropWhile_sep {c : Char} (rest : List Char) (sep : c = ',' ∨ c = ']' ∨ c = '}') :
    (c :: rest).dropWhile isWs = c :: rest := by
  rcases sep with rfl | rfl | rfl <;> rfl

theorem elemsText_cons (e : Json) (es : List Json) (nonempty : es ≠ []) :
    (elemsText (e :: es)).toList = (compress e).toList ++ ',' :: (elemsText es).toList := by
  cases es with
  | nil => exact absurd rfl nonempty
  | cons e' es => simp [elemsText]

theorem elemsText_head {es : List Json} (nonempty : es ≠ []) :
    ∃ e rest, (elemsText es).toList = (compress e).toList ++ rest := by
  match es, nonempty with
  | [e], _ => exact ⟨e, [], by simp [elemsText]⟩
  | e :: e' :: es, _ => exact ⟨e, _, elemsText_cons e (e' :: es) (by simp)⟩

theorem remaining_lt {it it' : Input} {front back : List Char} (h : At it (front ++ back))
    (h' : At it' back) (consumed : front ≠ []) : remaining it' < remaining it := by
  rw [h.remaining, h'.remaining, size_append]
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil consumed
  rw [size_cons]
  have := Char.utf8Size_pos c
  omega

theorem array_text {elems : List Json} (each : ∀ e ∈ elems, ValueText e) (nonempty : elems ≠ [])
    {acc : Array Json} {rest : List Char} {it : Input}
    (h : At it ((elemsText elems).toList ++ ']' :: rest)) :
    ∃ it', At it' (rest.dropWhile isWs) ∧
      array acc it = .success it' ⟨acc.toList ++ elems.map canon⟩ := by
  induction elems generalizing acc it with
  | nil => exact absurd rfl nonempty
  | cons e es step =>
    have here := each e List.mem_cons_self
    by_cases last : es = []
    · subst last
      have h' : At it ((compress e).toList ++ ']' :: rest) := by simpa [elemsText] using h
      obtain ⟨it1, h1, parsed⟩ := here _ _ (fun c head => by cases head; simp) h'
      rw [dropWhile_sep _ (.inr (.inl rfl))] at h1
      obtain ⟨it2, h2, read⟩ := any_at h1
      obtain ⟨it3, h3, skipped⟩ := ws_at h2
      refine ⟨it3, h3, ?_⟩
      rw [array]
      show (stay it (fun it _ => value it) >>= _) it = _
      rw [bind_success ((stay_le (Nat.le_refl _)).trans parsed)]
      rw [bind_success read, ite_eq_left (by decide), bind_success skipped]
      simp [Array.push, pure_apply]
    · rw [elemsText_cons e es last, List.append_assoc, List.cons_append] at h
      obtain ⟨it1, h1, parsed⟩ := here _ _ (fun c head => by cases head; simp) h
      rw [dropWhile_sep _ (.inl rfl)] at h1
      obtain ⟨it2, h2, read⟩ := any_at h1
      obtain ⟨it3, h3, skipped⟩ := ws_at h2
      obtain ⟨e', tail, text⟩ := elemsText_head last
      rw [text, List.append_assoc, dropWhile_compress, ← List.append_assoc, ← text] at h3
      obtain ⟨it4, h4, inner⟩ := step (fun e' inside => each e' (List.mem_cons_of_mem _ inside))
        last (acc := acc.push (canon e)) h3
      refine ⟨it4, h4, ?_⟩
      rw [array]
      show (stay it (fun it _ => value it) >>= _) it = _
      rw [bind_success ((stay_le (Nat.le_refl _)).trans parsed)]
      rw [bind_success read, ite_eq_right (by decide), ite_eq_left (by decide),
        bind_success skipped,
        descend_lt (remaining_lt (front := (compress e).toList ++ [',']) (by simpa using h) h3
          (by simp)), inner]
      simp [Array.push]


theorem sepText_true (m : String × Json) (ms : List (String × Json)) :
    (sepText true (m :: ms)).toList = '"' :: (strChars m.1 ++ '"' :: ':' ::
      ((compress m.2).toList ++ (sepText false ms).toList)) := by
  simp [sepText, memberText, stringTo_eq]

theorem sepText_false {ms : List (String × Json)} (nonempty : ms ≠ []) :
    (sepText false ms).toList = ',' :: (sepText true ms).toList := by
  cases ms with
  | nil => exact absurd rfl nonempty
  | cons m ms => simp [sepText]

theorem sepText_false_follow (ms : List (String × Json)) (rest : List Char) :
    Follow ((sepText false ms).toList ++ '}' :: rest) ∧
      ((sepText false ms).toList ++ '}' :: rest).dropWhile isWs =
        (sepText false ms).toList ++ '}' :: rest := by
  by_cases empty : ms = []
  · subst empty
    exact ⟨fun c head => by cases head; simp, dropWhile_sep _ (.inr (.inr rfl))⟩
  · rw [sepText_false empty]
    exact ⟨fun c head => by cases head; simp, dropWhile_sep _ (.inl rfl)⟩

theorem object_text {ms : List (String × Json)} (each : ∀ m ∈ ms, ValueText m.2)
    (nonempty : ms ≠ []) {acc : List (String × Json)}
    (names : (acc.map (·.1) ++ ms.map (·.1)).Pairwise fun a b => compare a b = .lt)
    {rest : List Char} {it : Input} (h : At it ((sepText true ms).toList ++ '}' :: rest)) :
    ∃ it', At it' (rest.dropWhile isWs) ∧
      object (treeOf acc) it =
        .success it' (treeOf (acc ++ ms.map fun m => (m.1, canon m.2))) := by
  induction ms generalizing acc it with
  | nil => exact absurd rfl nonempty
  | cons m ms step =>
    rw [sepText_true] at h
    simp only [List.cons_append, List.append_assoc] at h
    have look := lookahead_at (p := fun c => (c == '"') = true) (desc := "object key") rfl h
    obtain ⟨it1, h1, skipped⟩ := skip_at h
    obtain ⟨it2, h2, key⟩ := strCore_text (acc := "") m.1.toList h1
    rw [foldl_push] at key
    have fresh : (treeOf acc).contains m.1 = false := by
      rw [contains_treeOf, List.any_eq_false]
      intro earlier present same
      rw [beq_iff_eq] at same
      rw [List.pairwise_append] at names
      have less := names.2.2 earlier.1 (List.mem_map_of_mem present) m.1 List.mem_cons_self
      rw [same] at less
      cases less
    obtain ⟨it3, h3, white⟩ := ws_at h2
    rw [dropWhile_solid _ (by decide)] at h3
    have look2 := lookahead_at (p := fun c => (c == ':') = true) (desc := ":") rfl h3
    obtain ⟨it4, h4, skipped2⟩ := skip_at h3
    obtain ⟨it5, h5, white2⟩ := ws_at h4
    rw [dropWhile_compress] at h5
    obtain ⟨follow, solid⟩ := sepText_false_follow ms rest
    obtain ⟨it6, h6, parsed⟩ := each m List.mem_cons_self _ _ follow h5
    rw [solid] at h6
    have lt : remaining it5 < remaining it := by
      have h' : At it (('"' :: (strChars m.1 ++ ['"', ':'])) ++
          ((compress m.2).toList ++ ((sepText false ms).toList ++ '}' :: rest))) := by
        simpa using h
      exact remaining_lt h' h5 (by simp)
    have prefix_ : ∀ (k : Result JsonAgreement.Fields),
        object (treeOf acc) it = k ↔
          (any >>= fun c =>
            if (c == '}') = true then
              (do PolicyCodec.ws; pure (treeOf (acc ++ [(m.1, canon m.2)])))
            else if (c == ',') = true then (do
              PolicyCodec.ws
              descend it fun it _ => object (treeOf (acc ++ [(m.1, canon m.2)])) it)
            else fail "unexpected character in object") it6 = k := by
      intro k
      rw [treeOf_concat, object]
      show ((Json.Parser.lookahead (· == '"') "object key") >>= _) it = k ↔ _
      have key' : str it1 = .success it2 m.1 := key
      rw [bind_success look, seq_success skipped, bind_success key']
      simp only [fresh, Bool.false_eq_true, ite_false]
      rw [seq_success white, bind_success look2,
        seq_success skipped2, seq_success white2, bind_success (descend_lt lt |>.trans parsed)]
    by_cases empty : ms = []
    · subst empty
      obtain ⟨it7, h7, read⟩ := any_at (c := '}') (by simpa [sepText] using h6)
      obtain ⟨it8, h8, skipped3⟩ := ws_at h7
      refine ⟨it8, h8, (prefix_ _).mpr ?_⟩
      rw [bind_success read, ite_eq_left (by decide), seq_success skipped3]
      simp [pure_apply]
    · rw [sepText_false empty] at h6
      obtain ⟨it7, h7, read⟩ := any_at h6
      obtain ⟨it8, h8, skipped3⟩ := ws_at h7
      obtain ⟨m', ms', rfl⟩ := List.exists_cons_of_ne_nil empty
      have h8' : At it8 ((sepText true (m' :: ms')).toList ++ '}' :: rest) := by
        rw [sepText_true] at h8 ⊢
        simpa [isWs] using h8
      have names' : ((acc ++ [(m.1, canon m.2)]).map (·.1) ++ (m' :: ms').map (·.1)).Pairwise
          fun a b => compare a b = .lt := by
        simpa using names
      obtain ⟨it9, h9, inner⟩ := step (fun m inside => each m (List.mem_cons_of_mem _ inside))
        (by simp) names' h8'
      refine ⟨it9, h9, (prefix_ _).mpr ?_⟩
      have lt2 : remaining it8 < remaining it := by
        have a := h5.remaining
        have b := h6.remaining
        have c := h8'.remaining
        rw [sepText_false (by simp)] at a
        simp only [List.cons_append, size_append, size_cons] at a b c
        have := Char.utf8Size_pos ','
        omega
      rw [bind_success read, ite_eq_right (by decide), ite_eq_left (by decide),
        seq_success skipped3, descend_lt lt2, inner]
      simp


/-! ### Values -/

theorem value_scalar {it : Input} {c : Char} {cs : List Char} (h : At it (c :: cs))
    (notArr : (c == '[') = false) (notObj : (c == '{') = false) : value it = scalar it := by
  rw [value]
  show (peek! >>= _) it = _
  rw [bind_success (peek!_at h)]
  simp only [notArr, notObj, Bool.false_eq_true, ite_false]

theorem not_beq_of_digit {c d : Char} (digit : c.isDigit = true) (other : d.isDigit = false) :
    (c == d) = false := by
  cases same : (c == d)
  · rfl
  · rw [beq_iff_eq] at same
    subst same
    rw [digit] at other
    cases other

theorem numStart {c : Char} (start : c = '-' ∨ c.isDigit = true) :
    (c == '[') = false ∧ (c == '{') = false ∧ (c == '"') = false ∧ (c == 'f') = false ∧
      (c == 't') = false ∧ (c == 'n') = false ∧ (c == '-' || ('0' <= c && c <= '9')) = true := by
  rcases start with rfl | digit
  · decide
  · refine ⟨not_beq_of_digit digit rfl, not_beq_of_digit digit rfl, not_beq_of_digit digit rfl,
      not_beq_of_digit digit rfl, not_beq_of_digit digit rfl, not_beq_of_digit digit rfl, ?_⟩
    rw [digit_test, digit, Bool.or_true]

theorem number_head (n : JsonNumber) :
    ∃ c cs, (numberText n).toList = c :: cs ∧ (c = '-' ∨ c.isDigit = true) := by
  rw [numberText_toList, int_repr_toList]
  by_cases negative : n.mantissa < 0
  · exact ⟨'-', _ ++ _, by simp [negative]; rfl, .inl rfl⟩
  · obtain ⟨d, ds, eq⟩ := List.exists_cons_of_ne_nil
      (Nat.toDigits_ne_nil (b := 10) (n := n.mantissa.natAbs))
    exact ⟨d, ds ++ _, by simp [negative, eq]; rfl,
      .inr (toDigits_digits _ d (by rw [eq]; exact List.mem_cons_self))⟩

/-- **`value` reads the text of a value whose object trees are search trees back as `canon` of
the value.** -/
theorem value_text {j : Json} (regular : Regular j) : ValueText j := by
  induction regular with
  | null =>
    intro rest it _ h
    have h' : At it ('n' :: ['u', 'l', 'l'] ++ rest) := h
    obtain ⟨it1, h1, lit⟩ := literal_at "null" h
    obtain ⟨it2, h2, white⟩ := ws_at h1
    refine ⟨it2, h2, ?_⟩
    rw [value_scalar h' rfl rfl]
    unfold scalar
    rw [bind_success (peek!_at h'), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_right (by decide), ite_eq_left (by decide), seq_success lit, seq_success white]
    rfl
  | bool b =>
    intro rest it _ h
    cases b with
    | true =>
      have h' : At it ('t' :: ['r', 'u', 'e'] ++ rest) := by simpa [compress_bool] using h
      obtain ⟨it1, h1, lit⟩ := literal_at "true" (by simpa [compress_bool] using h)
      obtain ⟨it2, h2, white⟩ := ws_at h1
      refine ⟨it2, h2, ?_⟩
      rw [value_scalar h' rfl rfl]
      unfold scalar
      rw [bind_success (peek!_at h'), ite_eq_right (by decide), ite_eq_right (by decide),
        ite_eq_left (by decide), seq_success lit, seq_success white]
      rfl
    | false =>
      have h' : At it ('f' :: ['a', 'l', 's', 'e'] ++ rest) := by simpa [compress_bool] using h
      obtain ⟨it1, h1, lit⟩ := literal_at "false" (by simpa [compress_bool] using h)
      obtain ⟨it2, h2, white⟩ := ws_at h1
      refine ⟨it2, h2, ?_⟩
      rw [value_scalar h' rfl rfl]
      unfold scalar
      rw [bind_success (peek!_at h'), ite_eq_right (by decide), ite_eq_left (by decide),
        seq_success lit, seq_success white]
      rfl
  | num n =>
    intro rest it follow h
    rw [compress_num] at h
    obtain ⟨c, cs, eq, start⟩ := number_head n
    have h' : At it (c :: (cs ++ rest)) := by rw [eq] at h; simpa using h
    obtain ⟨notArr, notObj, notStr, notF, notT, notN, isNum⟩ := numStart start
    obtain ⟨it1, h1, parsed⟩ := num_text n follow h
    obtain ⟨it2, h2, white⟩ := ws_at h1
    refine ⟨it2, h2, ?_⟩
    rw [value_scalar h' notArr notObj]
    unfold scalar
    rw [bind_success (peek!_at h')]
    simp only [notStr, notF, notT, notN, isNum, Bool.false_eq_true, ite_false, ite_true]
    rw [bind_success parsed, seq_success white]
    rfl
  | str s =>
    intro rest it _ h
    have h' : At it ('"' :: (s.toList.flatMap escChars ++ '"' :: rest)) := by
      simpa [compress_str, strChars] using h
    obtain ⟨it1, h1, skipped⟩ := skip_at h'
    obtain ⟨it2, h2, parsed⟩ := strCore_text (acc := "") s.toList h1
    rw [foldl_push] at parsed
    obtain ⟨it3, h3, white⟩ := ws_at h2
    refine ⟨it3, h3, ?_⟩
    rw [value_scalar h' rfl rfl]
    unfold scalar
    have parsed' : str it1 = .success it2 s := parsed
    rw [bind_success (peek!_at h'), ite_eq_left (by decide), seq_success skipped,
      bind_success parsed', seq_success white]
    rfl
  | @arr elements _ step =>
    obtain ⟨elems⟩ := elements
    intro rest it _ h
    rw [compress_arr] at h
    have h' : At it ('[' :: ((elemsText elems).toList ++ ']' :: rest)) := by simpa using h
    obtain ⟨it1, h1, skipped⟩ := skip_at h'
    obtain ⟨it2, h2, white⟩ := ws_at h1
    by_cases empty : elems = []
    · subst empty
      have h2' : At it2 (']' :: rest) := by simpa [elemsText, isWs] using h2
      obtain ⟨it3, h3, skipped2⟩ := skip_at h2'
      obtain ⟨it4, h4, white2⟩ := ws_at h3
      refine ⟨it4, h4, ?_⟩
      rw [value]
      show (peek! >>= _) it = _
      rw [bind_success (peek!_at h'), ite_eq_left (by decide), seq_success skipped,
        seq_success white, bind_success (peek!_at h2'), ite_eq_left (by decide),
        seq_success skipped2, seq_success white2]
      rfl
    · obtain ⟨e, tail, text⟩ := elemsText_head empty
      obtain ⟨c, cs, head, start⟩ := compress_head e
      rw [text, head, List.cons_append, List.cons_append, dropWhile_solid _ start.facts.1,
        ← List.cons_append, ← List.cons_append, ← head, ← text] at h2
      have h2' : At it2 (c :: (cs ++ tail ++ ']' :: rest)) := by
        rw [text, head] at h2; simpa using h2
      obtain ⟨it3, h3, inner⟩ := array_text (acc := #[])
        (fun e inside => step e (Array.mem_def.mpr inside)) empty h2
      refine ⟨it3, h3, ?_⟩
      have lt : remaining it2 < remaining it :=
        remaining_lt (front := ['[']) (by simpa using h') h2 (by simp)
      rw [value]
      show (peek! >>= _) it = _
      rw [bind_success (peek!_at h'), ite_eq_left (by decide), seq_success skipped,
        seq_success white, bind_success (peek!_at h2'), start.facts.2.1]
      simp only [Bool.false_eq_true, ite_false]
      rw [bind_success (descend_lt lt |>.trans inner), canon_arr]
      simp <;> rfl
  | @obj fields ordered _ step =>
    intro rest it _ h
    rw [compress_obj] at h
    have h' : At it ('{' :: ((sepText true (members fields)).toList ++ '}' :: rest)) := by
      simpa using h
    obtain ⟨it1, h1, skipped⟩ := skip_at h'
    obtain ⟨it2, h2, white⟩ := ws_at h1
    by_cases empty : members fields = []
    · rw [empty] at h2
      have h2' : At it2 ('}' :: rest) := by simpa [sepText, isWs] using h2
      obtain ⟨it3, h3, skipped2⟩ := skip_at h2'
      obtain ⟨it4, h4, white2⟩ := ws_at h3
      refine ⟨it4, h4, ?_⟩
      rw [value]
      show (peek! >>= _) it = _
      rw [bind_success (peek!_at h'), ite_eq_right (by decide), ite_eq_left (by decide),
        seq_success skipped, seq_success white, bind_success (peek!_at h2'),
        ite_eq_left (by decide), seq_success skipped2, seq_success white2, canon_obj, empty]
      rfl
    · obtain ⟨m, ms, listed⟩ := List.exists_cons_of_ne_nil empty
      have h2' : At it2 ((sepText true (members fields)).toList ++ '}' :: rest) := by
        rw [listed, sepText_true] at h2 ⊢
        simpa [isWs] using h2
      have h2'' : At it2 ('"' :: ((sepText true (members fields)).toList.tail ++ '}' :: rest)) := by
        rw [listed, sepText_true] at h2' ⊢
        simpa using h2'
      have names : (([] : List (String × Json)).map (·.1) ++ (members fields).map (·.1)).Pairwise
          fun a b => compare a b = .lt := by
        simpa [List.pairwise_map] using (ordered_iff fields).mp ordered
      obtain ⟨it3, h3, inner⟩ := object_text (acc := []) step empty names h2'
      have inner : object .leaf it2 = _ := inner
      refine ⟨it3, h3, ?_⟩
      have lt : remaining it2 < remaining it :=
        remaining_lt (front := ['{']) (by simpa using h') h2' (by simp)
      rw [value]
      show (peek! >>= _) it = _
      rw [bind_success (peek!_at h'), ite_eq_right (by decide), ite_eq_left (by decide),
        seq_success skipped, seq_success white, bind_success (peek!_at h2''),
        ite_eq_right (by decide), bind_success (descend_lt lt |>.trans inner),
        canon_obj,
        sortMembers_of_increasing (increasing_members ordered fun _ value => canon value), mkObj_eq]
      simp <;> rfl


/-! ### The document -/

/-- **The parse of the compact text of a value whose object trees are search trees, with a final
newline, is the value with each object tree as the parser builds it** (`JsonCanon.canon`), which
agrees with the value (`JsonCanon.Regular.canon_agree`). -/
theorem parse_compress {j : Json} (regular : Regular j) :
    parse (compress j ++ "\n") = .ok (canon j) := by
  have start := At.start (compress j ++ "\n")
  rw [String.toList_append, show "\n".toList = ['\n'] by simp] at start
  obtain ⟨it1, h1, white⟩ := ws_at start
  rw [dropWhile_compress] at h1
  obtain ⟨it2, h2, parsed⟩ := value_text regular _ _ (fun c head => by
    cases head; decide) h1
  have h2' : At it2 [] := by simpa [isWs] using h2
  simp only [parse, Parser.run]
  rw [seq_success white, bind_success parsed, seq_success (eof_nil h2')]
  rfl

/-- **The parse of the compact text of a value whose object trees are the parser's, with a final
newline, is the value itself.** -/
theorem parse_compress_canonical {j : Json} (canonical : Canonical j) :
    parse (compress j ++ "\n") = .ok j :=
  (parse_compress canonical.regular).trans (congrArg _ canonical.canon_eq)

end Regula.Checker.JsonRoundTrip
