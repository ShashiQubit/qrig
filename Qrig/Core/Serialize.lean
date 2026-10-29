module

public import Qrig.Core.Gate

/-!
# Textual interchange format for circuits

Circuits are exchanged with the host language (Python) as whitespace separated
prefix-notation token streams:

| token(s)          | circuit                                     |
|-------------------|---------------------------------------------|
| `I n`             | identity on `n` wires                        |
| `X`               | the NOT gate (distinguished involution)     |
| `W`               | the swap `σ₁,₁`                               |
| `U a b c d`       | one-qubit gate `[[a, b], [c, d]]`            |
| `P z`             | scalar `z` (a `0 → 0` generator)             |
| `S f g`           | `f` followed by `g`                          |
| `T f g`           | `f + g` (`f` on the top wires)               |
| `C1 f` / `C0 f`   | `C¹(f)` / `C⁰(f)`                            |

Scalars are written `a:b:c:d` for `a + bω + cω² + dω³`, each coefficient `p` or `p/q`.
Wire 0 is the top wire, i.e. the most significant bit of a basis index.
-/

@[expose] public section

namespace Qrig

/-- A circuit together with its number of wires. -/
structure AnyCirc where
  n : Nat
  c : QCirc n

/-- Serialise a circuit. -/
def Circ.toTokens : {n : Nat} → QCirc n → List String → List String
  | _, .id n, acc => "I" :: toString n :: acc
  | _, .x, acc => "X" :: acc
  | _, .swap, acc => "W" :: acc
  | _, .gen (.u a b c d), acc => "U" :: a.toToken :: b.toToken :: c.toToken :: d.toToken :: acc
  | _, .gen (.ph z), acc => "P" :: z.toToken :: acc
  | _, .seq f g, acc => "S" :: Circ.toTokens f (Circ.toTokens g acc)
  | _, .par f g, acc => "T" :: Circ.toTokens f (Circ.toTokens g acc)
  | _, .ctrl b f, acc => (if b then "C1" else "C0") :: Circ.toTokens f acc

def Circ.serialize {n : Nat} (c : QCirc n) : String :=
  " ".intercalate (Circ.toTokens c [])

/-- Parse a circuit from a token list (with fuel bounding the recursion depth). -/
def parseTokens : Nat → List String → Except String (AnyCirc × List String)
  | 0, _ => .error "parse error: input too deeply nested"
  | _ + 1, [] => .error "parse error: unexpected end of input"
  | fuel + 1, tok :: rest =>
    match tok with
    | "I" => match rest with
      | k :: rest' => match k.toNat? with
        | some n => .ok (⟨n, .id n⟩, rest')
        | none => .error s!"parse error: bad wire count '{k}'"
      | [] => .error "parse error: 'I' needs a wire count"
    | "X" => .ok (⟨1, .x⟩, rest)
    | "W" => .ok (⟨2, .swap⟩, rest)
    | "U" => match rest with
      | a :: b :: c :: d :: rest' =>
        match QOmega.ofToken a, QOmega.ofToken b, QOmega.ofToken c, QOmega.ofToken d with
        | some a, some b, some c, some d => .ok (⟨1, Circ.gen (Gate.u a b c d)⟩, rest')
        | _, _, _, _ => .error "parse error: bad scalar in 'U'"
      | _ => .error "parse error: 'U' needs four scalars"
    | "P" => match rest with
      | z :: rest' => match QOmega.ofToken z with
        | some z => .ok (⟨0, Circ.gen (Gate.ph z)⟩, rest')
        | none => .error "parse error: bad scalar in 'P'"
      | [] => .error "parse error: 'P' needs a scalar"
    | "S" => do
      let (⟨m, f⟩, r1) ← parseTokens fuel rest
      let (⟨n, g⟩, r2) ← parseTokens fuel r1
      if h : m = n then .ok (⟨n, .seq (h ▸ f) g⟩, r2)
      else .error s!"type error: sequential composition of circuits on {m} and {n} wires"
    | "T" => do
      let (⟨m, f⟩, r1) ← parseTokens fuel rest
      let (⟨n, g⟩, r2) ← parseTokens fuel r1
      .ok (⟨m + n, .par f g⟩, r2)
    | "C1" => do
      let (⟨m, f⟩, r1) ← parseTokens fuel rest
      .ok (⟨m + 1, .ctrl true f⟩, r1)
    | "C0" => do
      let (⟨m, f⟩, r1) ← parseTokens fuel rest
      .ok (⟨m + 1, .ctrl false f⟩, r1)
    | t => .error s!"parse error: unknown token '{t}'"

/-- Split a string into whitespace separated tokens. -/
def tokenize (s : String) : List String :=
  (s.split (fun ch => ch == ' ' || ch == '\n' || ch == '\t' || ch == '\r')).toList.map
    (fun t => t.toString) |>.filter (· ≠ "")

/-- Parse a complete circuit. -/
def parseCirc (s : String) : Except String AnyCirc := do
  let toks := tokenize s
  let (c, rest) ← parseTokens (toks.length + 1) toks
  if rest.isEmpty then .ok c else .error "parse error: trailing tokens"

/-- Serialise a vector of scalars. -/
def vecToString (v : Array QOmega) : String := " ".intercalate (v.toList.map QOmega.toToken)

/-- Parse a vector of scalars. -/
def parseVec (s : String) : Except String (Array QOmega) :=
  match (tokenize s).mapM QOmega.ofToken with
  | some l => .ok l.toArray
  | none => .error "parse error: bad scalar in vector"

end Qrig

end
