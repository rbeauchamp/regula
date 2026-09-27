module

public import Lean.Data.Position
public import RegulaPolicy.Domain

/-! # Source-coordinate admission

Source-coordinate admission against exact source bytes with Lean's `FileMap`.
UTF-16 columns are a parameter: Lean computes them in `Lean.Data.Lsp.Utf16`, whose
import closure contains `Lean.Environment`, so `Regula.Diagnostic` supplies
`FileMap.leanPosToLspPos`. These definitions concern the supplied bytes and coordinates;
they do not authenticate how either was acquired. -/

@[expose] public section

namespace Regula
open Lean

/-- A source text with the URI it is reported under (`RegulaPolicy.SourceSnapshot`). -/
abbrev SourceSnapshot := RegulaPolicy.SourceSnapshot
/-- A span of UTF-8 byte offsets, start inclusive and stop exclusive (`RegulaPolicy.ByteRange`). -/
abbrev ByteRange := RegulaPolicy.ByteRange

/-- Raw coordinates are admitted only after checking character boundaries and containment. -/
structure SourceCandidate where
  /-- The source the byte offsets refer to. -/
  snapshot : SourceSnapshot
  /-- The byte range of the whole reported item. -/
  full : ByteRange
  /-- The byte range of the selected part, such as a declaration name. -/
  selection : ByteRange
  deriving Repr, BEq

namespace SourceCandidate
/-- `n` is at most the byte size of `source`, and `FileMap` maps it to a position and back to
`n` itself; this is how a character boundary is recognized. -/
def boundary (source : String) (n : Nat) : Bool :=
  n ≤ source.utf8ByteSize &&
    (source.toFileMap.ofPosition (source.toFileMap.toPosition ⟨n⟩)).byteIdx == n

/-- The URI is nonempty, the selection lies within the full range with ordered ends, and all
four offsets are character boundaries of the source. -/
def valid (c : SourceCandidate) : Bool :=
  !c.snapshot.uri.isEmpty && c.full.start ≤ c.selection.start &&
  c.selection.start ≤ c.selection.stop && c.selection.stop ≤ c.full.stop &&
  [c.full.start, c.full.stop, c.selection.start, c.selection.stop].all
    (boundary c.snapshot.source)
end SourceCandidate

/-- Invalid coordinates cannot inhabit an admitted source location. -/
abbrev SourceLocation := { c : SourceCandidate // c.valid = true }

/-- Admits a candidate as a `SourceLocation` exactly when `valid` holds, refusing it otherwise. -/
def admitSource (c : SourceCandidate) : Except String SourceLocation :=
  if h : c.valid = true then .ok ⟨c, h⟩ else .error "invalid source coordinates"

/-- The UTF-16 column of a Lean position in a file map. -/
abbrev Utf16Column := FileMap → Lean.Position → Nat

/-- Lean position of a recorded one-based line and codepoint column. -/
def leanPosition (p : RegulaPolicy.Position) : Lean.Position := ⟨p.line, p.column⟩

/-- Byte offsets `FileMap` assigns to a reported range's ends. -/
def reportedBytes (fm : FileMap) (r : RegulaPolicy.Range) : ByteRange :=
  ⟨(fm.ofPosition (leanPosition r.start)).byteIdx, (fm.ofPosition (leanPosition r.end)).byteIdx⟩

/-- A reported range has positive lines, both ends round-trip through `fm`, and its
recorded UTF-16 columns are those `column` assigns. -/
def ReportedAgrees (column : Utf16Column) (fm : FileMap) (r : RegulaPolicy.Range) : Prop :=
  r.start.line > 0 ∧ r.end.line > 0 ∧
    fm.toPosition (fm.ofPosition (leanPosition r.start)) = leanPosition r.start ∧
    fm.toPosition (fm.ofPosition (leanPosition r.end)) = leanPosition r.end ∧
    column fm (leanPosition r.start) = r.startUtf16 ∧ column fm (leanPosition r.end) = r.endUtf16

instance (column : Utf16Column) (fm : FileMap) (r : RegulaPolicy.Range) :
    Decidable (ReportedAgrees column fm r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The candidate a report's full and selection ranges name in `snapshot`. -/
def reportedCandidate (snapshot : SourceSnapshot) (ranges : RegulaPolicy.Ranges) :
    SourceCandidate :=
  ⟨snapshot, reportedBytes snapshot.source.toFileMap ranges.range,
    reportedBytes snapshot.source.toFileMap ranges.selectionRange⟩

/-- Byte range of one reported range, refusing a disagreement with the exact source. -/
def reportedRange (column : Utf16Column) (fm : FileMap) (r : RegulaPolicy.Range) :
    Except String ByteRange := do
  let a : Lean.Position := ⟨r.start.line, r.start.column⟩
  let b : Lean.Position := ⟨r.end.line, r.end.column⟩
  let start := fm.ofPosition a
  let stop := fm.ofPosition b
  unless r.start.line > 0 && r.end.line > 0 && fm.toPosition start == a &&
      fm.toPosition stop == b && column fm a == r.startUtf16 && column fm b == r.endUtf16 do
    throw "reported source coordinates disagree with the snapshot"
  return ⟨start.byteIdx, stop.byteIdx⟩

theorem reportedRange_eq (column : Utf16Column) (fm : FileMap) (r : RegulaPolicy.Range) :
    reportedRange column fm r = if ReportedAgrees column fm r then .ok (reportedBytes fm r)
      else .error "reported source coordinates disagree with the snapshot" := by
  by_cases h : ReportedAgrees column fm r
  · simp only [h, ↓reduceIte]
    simp only [ReportedAgrees, leanPosition, gt_iff_lt] at h
    simp [reportedRange, reportedBytes, leanPosition, h, pure, Except.pure]
  · simp only [h, ↓reduceIte]
    simp only [ReportedAgrees, leanPosition, gt_iff_lt] at h
    simp [reportedRange, and_assoc, h, throw, throwThe, MonadExceptOf.throw, Functor.map,
      Except.map]

/-- A report's codepoint and UTF-16 columns must both agree with the exact source. -/
def sourceFromReportWith (column : Utf16Column) (snapshot : SourceSnapshot)
    (ranges : RegulaPolicy.Ranges) : Except String SourceLocation := do
  let fm := snapshot.source.toFileMap
  admitSource ⟨snapshot, ← reportedRange column fm ranges.range,
    ← reportedRange column fm ranges.selectionRange⟩

end Regula
