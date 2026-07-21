/-!
# Raw tensor interchange (FLEANTEN v1)

Reader for the trivial on-disk tensor format produced by
`references/export_raw_tensors.py`. Checkpoints are *data, not proof-data*
(`docs/verified_checker_design.md`): this file is executable plumbing with no
proof obligations. All layout integers are little-endian.

    magic   : 8 bytes  "FLEANTEN"
    version : u32      = 1
    count   : u32
    per tensor:
      nameLen : u32
      name    : nameLen bytes UTF-8
      rows    : u32
      cols    : u32
      data    : rows*cols u32 words (float32 bit patterns, row-major)

The parser is pure (`ByteArray → Except String …`); `readRawTensorFile` is the
IO wrapper.
-/

namespace Flean.Checker

/-- One tensor from a FLEANTEN file: `data` holds `rows * cols` row-major
float32 bit patterns. -/
structure RawTensor where
  name : String
  rows : Nat
  cols : Nat
  data : Array UInt32
  deriving Repr, Inhabited

namespace RawTensor

/-- Entry at `(i, j)`; `0` out of bounds. -/
def get (t : RawTensor) (i j : Nat) : UInt32 :=
  t.data.getD (i * t.cols + j) 0

end RawTensor

private def readU32 (b : ByteArray) (off : Nat) : UInt32 :=
  (b.get! off).toUInt32
    ||| (b.get! (off + 1)).toUInt32 <<< 8
    ||| (b.get! (off + 2)).toUInt32 <<< 16
    ||| (b.get! (off + 3)).toUInt32 <<< 24

/-- Parse a FLEANTEN v1 byte stream. -/
def parseRawTensors (b : ByteArray) : Except String (Array RawTensor) := do
  let magic := "FLEANTEN".toUTF8
  if b.size < 16 then throw "file too short"
  for i in [0:8] do
    if b.get! i ≠ magic.get! i then throw "bad magic (expected FLEANTEN)"
  let version := readU32 b 8
  if version ≠ 1 then throw s!"unsupported version {version}"
  let count := (readU32 b 12).toNat
  let mut off := 16
  let mut out : Array RawTensor := #[]
  for _ in [0:count] do
    if off + 4 > b.size then throw "truncated tensor header"
    let nameLen := (readU32 b off).toNat
    off := off + 4
    if off + nameLen + 8 > b.size then throw "truncated tensor header"
    let name := String.fromUTF8! (b.extract off (off + nameLen))
    off := off + nameLen
    let rows := (readU32 b off).toNat
    let cols := (readU32 b (off + 4)).toNat
    off := off + 8
    let words := rows * cols
    if off + 4 * words > b.size then throw s!"truncated data for tensor {name}"
    let mut data : Array UInt32 := Array.mkEmpty words
    for k in [0:words] do
      data := data.push (readU32 b (off + 4 * k))
    off := off + 4 * words
    out := out.push { name, rows, cols, data }
  if off ≠ b.size then throw s!"trailing bytes: consumed {off} of {b.size}"
  return out

/-- Read and parse a FLEANTEN file. -/
def readRawTensorFile (path : System.FilePath) : IO (Array RawTensor) := do
  let bytes ← IO.FS.readBinFile path
  match parseRawTensors bytes with
  | .ok ts => return ts
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- Look up a tensor by name and check its shape. -/
def RawTensor.find? (ts : Array RawTensor) (name : String) (rows cols : Nat) :
    Option RawTensor := do
  let t ← ts.find? (·.name = name)
  guard (t.rows = rows ∧ t.cols = cols)
  return t

end Flean.Checker
