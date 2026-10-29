module

/-!
# Exact scalars: the cyclotomic field `ℚ(ω)`, `ω = e^{iπ/4}`

Elements are `a + b ω + c ω² + d ω³` with rational coefficients, where `ω⁴ = -1`.
Every entry of the Clifford+T, Gaussian Clifford+T and controlled-`V` gate sets of
Section 5 of the paper (`H`, `S`, `T`, `V`, `X`, `Y`, `Z`, `ω`, ...) lies in this field,
so circuit semantics can be computed *exactly*; since `{1, ω, ω², ω³}` is a basis over
`ℚ` and `Rat` is kept in normal form, structural equality is mathematical equality.
-/

@[expose] public section

namespace Qrig

/-- `a + b ω + c ω² + d ω³` with `ω = e^{iπ/4}`. -/
structure QOmega where
  a : Rat
  b : Rat
  c : Rat
  d : Rat
  deriving DecidableEq, Inhabited, Repr

namespace QOmega

instance : Zero QOmega := ⟨⟨0, 0, 0, 0⟩⟩
instance : One QOmega := ⟨⟨1, 0, 0, 0⟩⟩

instance : Add QOmega := ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩⟩
instance : Neg QOmega := ⟨fun x => ⟨-x.a, -x.b, -x.c, -x.d⟩⟩
instance : Sub QOmega := ⟨fun x y => ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩⟩

/-- Multiplication, using `ω⁴ = -1`. -/
instance : Mul QOmega := ⟨fun x y =>
  ⟨x.a * y.a - x.b * y.d - x.c * y.c - x.d * y.b,
   x.a * y.b + x.b * y.a - x.c * y.d - x.d * y.c,
   x.a * y.c + x.b * y.b + x.c * y.a - x.d * y.d,
   x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a⟩⟩

/-- Rational scalars. -/
def ofRat (q : Rat) : QOmega := ⟨q, 0, 0, 0⟩

/-- `ω = e^{iπ/4}`. -/
def omega : QOmega := ⟨0, 1, 0, 0⟩

/-- The imaginary unit `i = ω²`. -/
def imag : QOmega := ⟨0, 0, 1, 0⟩

/-- `√2 = ω - ω³`. -/
def sqrt2 : QOmega := ⟨0, 1, 0, -1⟩

/-- `1/√2 = (ω - ω³)/2`. -/
def invSqrt2 : QOmega := ⟨0, 1/2, 0, -1/2⟩

/-- Complex conjugation: `ω ↦ ω⁻¹ = -ω³`. -/
def conj (x : QOmega) : QOmega := ⟨x.a, -x.d, -x.c, -x.b⟩

/-- `ωᵏ`. -/
def omegaPow (k : Nat) : QOmega :=
  match k % 8 with
  | 0 => ⟨1, 0, 0, 0⟩
  | 1 => ⟨0, 1, 0, 0⟩
  | 2 => ⟨0, 0, 1, 0⟩
  | 3 => ⟨0, 0, 0, 1⟩
  | 4 => ⟨-1, 0, 0, 0⟩
  | 5 => ⟨0, -1, 0, 0⟩
  | 6 => ⟨0, 0, -1, 0⟩
  | _ => ⟨0, 0, 0, -1⟩

def isZero (x : QOmega) : Bool := x == 0

/-- Print a rational as `p` or `p/q`. -/
def ratToString (q : Rat) : String :=
  if q.den == 1 then toString q.num else toString q.num ++ "/" ++ toString q.den

/-- Serialise as `a:b:c:d`. -/
def toToken (x : QOmega) : String :=
  ratToString x.a ++ ":" ++ ratToString x.b ++ ":" ++ ratToString x.c ++ ":" ++ ratToString x.d

/-- Parse a rational `p` or `p/q` (with `q ≠ 0`). -/
def parseRat (s : String) : Option Rat :=
  match s.splitOn "/" with
  | [p] => (fun (z : Int) => (z : Rat)) <$> p.toInt?
  | [p, q] => do
      let pz ← p.toInt?
      let qn ← q.toNat?
      if qn == 0 then none else some ((pz : Rat) / (qn : Rat))
  | _ => none

/-- Parse `a:b:c:d`. -/
def ofToken (s : String) : Option QOmega :=
  match s.splitOn ":" with
  | [a, b, c, d] => do
      return ⟨← parseRat a, ← parseRat b, ← parseRat c, ← parseRat d⟩
  | _ => none

end QOmega

end Qrig

end
