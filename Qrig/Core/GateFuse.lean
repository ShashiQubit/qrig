module

public import Qrig.Core.Gate
public import Qrig.Core.Simplify

/-!
# Fusion of base generators

Adjacent one-qubit gates are multiplied (`u A ; u B ⇝ u (B·A)`), adjacent scalars are
multiplied, and products equal to the identity are removed.  Soundness is proved in
`QrigProofs.GateFuse`.
-/

@[expose] public section

namespace Qrig

/-- A `2 × 2` matrix `[[a, b], [c, d]]`. -/
structure M2 where
  a : QOmega
  b : QOmega
  c : QOmega
  d : QOmega
  deriving DecidableEq

/-- Matrix product `A * B`. -/
def M2.mul (A B : M2) : M2 :=
  ⟨A.a * B.a + A.b * B.c, A.a * B.b + A.b * B.d, A.c * B.a + A.d * B.c, A.c * B.b + A.d * B.d⟩

def M2.one : M2 := ⟨1, 0, 0, 1⟩

/-- Recognise a one-qubit base gate. -/
def asU : {n : Nat} → QCirc n → Option M2
  | _, .gen (.u a b c d) => some ⟨a, b, c, d⟩
  | _, _ => none

/-- Recognise a scalar. -/
def asPh : {n : Nat} → QCirc n → Option QOmega
  | _, .gen (.ph z) => some z
  | _, _ => none

/-- The one-qubit gate with matrix `M` (or the identity if `M = 1`). -/
def ofM2 (M : M2) : QCirc 1 :=
  if M = M2.one then .id 1 else (Circ.gen (Gate.u M.a M.b M.c M.d) : QCirc 1)

/-- The scalar `z` (or the empty identity if `z = 1`). -/
def ofPh (z : QOmega) : QCirc 0 :=
  if z = 1 then .id 0 else (Circ.gen (Gate.ph z) : QCirc 0)

/-- Fusion of adjacent base generators. -/
def gateFuse : FuseRule Gate := fun {n} f g =>
  if h : n = 1 then
    match asU f, asU g with
    | some A, some B => some (castC h.symm (ofM2 (B.mul A)))
    | _, _ => none
  else if h0 : n = 0 then
    match asPh f, asPh g with
    | some z, some w => some (castC h0.symm (ofPh (w * z)))
    | _, _ => none
  else none

/-- The optimiser for the concrete gate set. -/
def simplifyQ {n : Nat} (c : QCirc n) : QCirc n := simplify gateFuse c

end Qrig

end
