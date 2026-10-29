module

public import Qrig.Core.QOmega

/-!
# DAG-level peephole optimisation with the control equations

The optimiser of `Qrig.Core.Simplify` works on circuit *terms* of the controlled prop.
Production circuits (Qiskit `DAGCircuit`s, MQT Bench benchmarks, …) are instead flat
lists of *multiply controlled one-qubit gates* placed on arbitrary wires:
`C^{b₁}_{w₁} ⋯ C^{b_k}_{w_k}(U)` acting on target wire `t`.  In the language of the paper
such a gate is `C^{b₁}(⋯ C^{b_k}(U))` conjugated by the symmetries that route the wires
into place.

This file contains an executable (Mathlib-free, compiled to C) optimiser for such gate
lists.  Every rewrite is an instance of one of the equations of Figure 1:

| rule      | equation | rewrite |
|-----------|----------|---------|
| `idRem`   | (b)      | `C…C(id) ⇝ id` |
| `fuse`    | (a)      | `C^c(f) ; C^c(g) ⇝ C^c(f ; g)` when `f ; g` is again a base gate |
| `cancel`  | (a),(b)  | `C^c(f) ; C^c(g) ⇝ id` when `f ; g = id` |
| `compl`   | (e)      | `C^c C⁰_w(f) ; C^c C¹_w(f) ⇝ C^c(f)` (complementarity) |
| `xconj`   | (d)      | `x_w ; M ; x_w ⇝ M[w: 0 ↔ 1]` (colour change) |
| commute   | (f)      | gates with contradictory controls commute, as do gates that only share wires on which both act diagonally |

The optimiser scans the list left to right, and tries to merge every new gate with an
earlier gate, moving it backwards past gates it provably commutes with (a bounded
window).  Soundness (the gate list keeps its exact semantics) is proved in
`QrigProofs.Peephole` for every interpretation of the base gates by `2 × 2` matrices over
a commutative ring for which the fusion rule is sound, and for the concrete gate set
`Op` below with its complex matrices.
-/

@[expose] public section

namespace Qrig.Flat

/-- A multiply controlled one-qubit gate: `op` on wire `tgt`, applied when every control
`(w, b)` sees the value `b` on wire `w`. -/
structure MCG (T : Type) where
  ctrls : List (Nat × Bool)
  tgt : Nat
  op : T
  deriving DecidableEq, Repr

/-- The syntactic operations on base gates that the optimiser needs. -/
class OpAlg (T : Type) where
  /-- `fuse a b = some c`: `c` implements `a` followed by `b`. -/
  fuse : T → T → Option T
  /-- the gate is the identity -/
  isId : T → Bool
  /-- the gate is diagonal in the computational basis -/
  isDiag : T → Bool
  /-- the gate is the NOT gate `x` -/
  isX : T → Bool

variable {T : Type} [DecidableEq T] [OpAlg T]

namespace MCG

/-- The control wires. -/
def wires (g : MCG T) : List Nat := g.ctrls.map (·.1)

/-- The target is not also a control wire. -/
def wf (g : MCG T) : Bool := !(g.wires.contains g.tgt)

/-- All wires the gate touches. -/
def supp (g : MCG T) : List Nat := g.tgt :: g.wires

/-- The wires on which the gate acts non-diagonally. -/
def moving (g : MCG T) : List Nat := if OpAlg.isDiag g.op then [] else [g.tgt]

end MCG

/-- Some control of `g` contradicts a control of `h`: the gates are never both active. -/
def conflict (g h : MCG T) : Bool := g.ctrls.any fun c => h.ctrls.contains (c.1, !c.2)

/-- A sufficient condition for `g ; h = h ; g` (equation (f) and diagonality). -/
def commutes (g h : MCG T) : Bool :=
  g.wf && h.wf &&
    (conflict g h ||
      (g.moving.all (fun w => !h.supp.contains w) && h.moving.all (fun w => !g.supp.contains w)))

/-- Every control of `a` is a control of `b`. -/
def ctrlSub (a b : List (Nat × Bool)) : Bool := a.all (b.contains ·)

/-- Same set of controls. -/
def ctrlSetEq (a b : List (Nat × Bool)) : Bool := ctrlSub a b && ctrlSub b a

/-- The controls other than those on wire `w`. -/
def dropWire (w : Nat) (a : List (Nat × Bool)) : List (Nat × Bool) := a.filter (·.1 != w)

/-- Every control on wire `w` has colour `p`. -/
def allOn (w : Nat) (p : Bool) (a : List (Nat × Bool)) : Bool := a.all fun c => c.1 != w || c.2 == p

/-- A wire on which the two control sets are complementary (equation (e)): `a = c ∪ {(w,p)}`
and `b = c ∪ {(w,¬p)}`. -/
def complWire (a b : List (Nat × Bool)) : Option Nat :=
  a.findSome? fun c =>
    if b.contains (c.1, !c.2) && allOn c.1 c.2 a && allOn c.1 (!c.2) b &&
        ctrlSetEq (dropWire c.1 a) (dropWire c.1 b) then some c.1 else none

/-- The rewrite rules (used for statistics). -/
inductive Rule where
  | idRem | fuse | cancel | compl | xconj
  deriving DecidableEq, Repr

/-- Try to replace `h ; g` by a shorter list of gates. -/
def combine (h g : MCG T) : Option (Rule × List (MCG T)) :=
  if h.tgt == g.tgt && h.wf && g.wf then
    if ctrlSetEq h.ctrls g.ctrls then
      match OpAlg.fuse h.op g.op with
      | some o => if OpAlg.isId o then some (.cancel, []) else some (.fuse, [{ h with op := o }])
      | none => none
    else if h.op == g.op then
      match complWire h.ctrls g.ctrls with
      | some w => some (.compl, [{ ctrls := dropWire w h.ctrls, tgt := h.tgt, op := h.op }])
      | none => none
    else none
  else none

/-- `g` is an uncontrolled NOT on wire `w`. -/
def isXon (w : Nat) (g : MCG T) : Bool := g.ctrls.isEmpty && g.tgt == w && OpAlg.isX g.op

/-- `x_w` can be pushed through `g` (flipping the colour of its controls on `w`). -/
def transparent (w : Nat) (g : MCG T) : Bool := g.tgt != w && g.wf

/-- Flip the colour of the controls on wire `w` (equation (d)). -/
def flipW (w : Nat) (g : MCG T) : MCG T :=
  { g with ctrls := g.ctrls.map fun c => if c.1 == w then (c.1, !c.2) else c }

/-- Look (backwards, in a reversed gate list) for an `x_w` that cancels a new `x_w`. -/
def xScan (w : Nat) : Nat → List (MCG T) → Option (List (MCG T))
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, h :: rest =>
    if isXon w h then some rest
    else if transparent w h then (xScan w fuel rest).map (flipW w h :: ·)
    else none

/-- Look (backwards, in a reversed gate list) for an earlier gate that the new gate `g`
can be merged with, moving `g` past gates it commutes with. -/
def insertAux (g : MCG T) : Nat → List (MCG T) → Option (List (MCG T) × Rule)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, h :: rest =>
    match combine h g with
    | some (r, rs) => some (rs.reverse ++ rest, r)
    | none =>
      if commutes h g then (insertAux g fuel rest).map fun p => (h :: p.1, p.2)
      else none

/-- Insert a gate at the end of a reversed gate list, merging it with an earlier gate if
possible; otherwise the gate is simply appended (gates are never reordered without a
merge, so the circuit depth is not increased by reordering). -/
def insert (g : MCG T) (fuel : Nat) (acc : List (MCG T)) : List (MCG T) × Option Rule :=
  match insertAux g fuel acc with
  | some (l, r) => (l, some r)
  | none => (g :: acc, none)

/-- Rule statistics. -/
structure Stats where
  idRem : Nat := 0
  fuse : Nat := 0
  cancel : Nat := 0
  compl : Nat := 0
  xconj : Nat := 0
  deriving Repr

def Stats.bump (s : Stats) : Option Rule → Stats
  | none => s
  | some .idRem => { s with idRem := s.idRem + 1 }
  | some .fuse => { s with fuse := s.fuse + 1 }
  | some .cancel => { s with cancel := s.cancel + 1 }
  | some .compl => { s with compl := s.compl + 1 }
  | some .xconj => { s with xconj := s.xconj + 1 }

def Stats.add (s t : Stats) : Stats :=
  ⟨s.idRem + t.idRem, s.fuse + t.fuse, s.cancel + t.cancel, s.compl + t.compl, s.xconj + t.xconj⟩

/-- Push one gate (reversed accumulator). -/
def pushGate (window : Nat) (acc : List (MCG T)) (g : MCG T) : List (MCG T) × Option Rule :=
  if OpAlg.isId g.op then (acc, some .idRem)
  else if g.ctrls.isEmpty && OpAlg.isX g.op then
    match xScan g.tgt window acc with
    | some acc' => (acc', some .xconj)
    | none => insert g window acc
  else insert g window acc

/-- One left-to-right pass (reversed accumulator, statistics). -/
def passAux (window : Nat) : List (MCG T) × Stats → List (MCG T) → List (MCG T) × Stats
  | st, [] => st
  | (acc, s), g :: gs =>
    let r := pushGate window acc g
    passAux window (r.1, s.bump r.2) gs

/-- One pass. -/
def pass (window : Nat) (gs : List (MCG T)) : List (MCG T) × Stats :=
  let r := passAux window ([], {}) gs
  (r.1.reverse, r.2)

/-- Iterate passes until a fixed point (at most `fuel` passes). -/
def optimize (window : Nat) : Nat → List (MCG T) → List (MCG T) × Stats
  | 0, gs => (gs, {})
  | fuel + 1, gs =>
    let r := pass window gs
    if r.1 == gs then (gs, r.2)
    else
      let r' := optimize window fuel r.1
      (r'.1, r.2.add r'.2)

/-! ## The concrete gate set -/

/-- One-qubit base gates.  Angles are rational multiples of `π`:
`p q = diag(1, e^{iπq})`, `rz q = diag(e^{-iπq/2}, e^{iπq/2})`, `rx q = e^{-iπq X/2}`,
`ry q = e^{-iπq Y/2}`.  `gen k` is an opaque gate (only merged by complementarity). -/
inductive Op where
  | x | y | h | sx | sxdg
  | p (q : Rat) | rz (q : Rat) | rx (q : Rat) | ry (q : Rat)
  | gen (k : Nat)
  deriving DecidableEq, Repr

/-- `q mod m`, in `[0, m)`. -/
def normMod (m q : Rat) : Rat := q - m * (q / m).floor

def Op.fuse : Op → Op → Option Op
  | .x, .x | .y, .y | .h, .h | .sx, .sxdg | .sxdg, .sx => some (.p 0)
  | .sx, .sx | .sxdg, .sxdg => some .x
  | .p a, .p b => some (.p (normMod 2 (a + b)))
  | .rz a, .rz b => some (.rz (normMod 4 (a + b)))
  | .rx a, .rx b => some (.rx (normMod 4 (a + b)))
  | .ry a, .ry b => some (.ry (normMod 4 (a + b)))
  | _, _ => none

def Op.isId : Op → Bool
  | .p q => normMod 2 q == 0
  | .rz q | .rx q | .ry q => normMod 4 q == 0
  | _ => false

def Op.isDiag : Op → Bool
  | .p _ | .rz _ => true
  | _ => false

def Op.isX : Op → Bool
  | .x => true
  | _ => false

instance : OpAlg Op := ⟨Op.fuse, Op.isId, Op.isDiag, Op.isX⟩

/-! ## Textual format

A gate is written `OP [angle|k] tgt c₁ c₂ …` where each control is `+w` (colour 1) or
`-w` (colour 0); gates are separated by `;`. -/

def Op.toTokens : Op → List String
  | .x => ["X"] | .y => ["Y"] | .h => ["H"] | .sx => ["SX"] | .sxdg => ["SXDG"]
  | .p q => ["P", QOmega.ratToString q] | .rz q => ["RZ", QOmega.ratToString q]
  | .rx q => ["RX", QOmega.ratToString q] | .ry q => ["RY", QOmega.ratToString q]
  | .gen k => ["G", toString k]

def MCG.toStr (g : MCG Op) : String :=
  " ".intercalate (g.op.toTokens ++ [toString g.tgt] ++
    g.ctrls.map fun c => (if c.2 then "+" else "-") ++ toString c.1)

def gatesToString (gs : List (MCG Op)) : String := ";".intercalate (gs.map MCG.toStr)

def parseCtrl (s : String) : Option (Nat × Bool) :=
  if s.startsWith "+" then ((·, true)) <$> (s.drop 1).toString.toNat?
  else if s.startsWith "-" then ((·, false)) <$> (s.drop 1).toString.toNat?
  else none

def parseOp : List String → Option (Op × List String)
  | "X" :: r => some (.x, r) | "Y" :: r => some (.y, r) | "H" :: r => some (.h, r)
  | "SX" :: r => some (.sx, r) | "SXDG" :: r => some (.sxdg, r)
  | "P" :: q :: r => (fun q => (.p q, r)) <$> QOmega.parseRat q
  | "RZ" :: q :: r => (fun q => (.rz q, r)) <$> QOmega.parseRat q
  | "RX" :: q :: r => (fun q => (.rx q, r)) <$> QOmega.parseRat q
  | "RY" :: q :: r => (fun q => (.ry q, r)) <$> QOmega.parseRat q
  | "G" :: k :: r => (fun k => (.gen k, r)) <$> k.toNat?
  | _ => none

def parseGate (s : String) : Option (MCG Op) := do
  let toks := (s.splitOn " ").filter (· ≠ "")
  let (op, rest) ← parseOp toks
  match rest with
  | t :: cs => return { ctrls := ← cs.mapM parseCtrl, tgt := ← t.toNat?, op := op }
  | [] => none

def parseGates (s : String) : Except String (List (MCG Op)) :=
  let parts := (s.splitOn ";").filter (fun p => p.trimAscii.toString ≠ "")
  parts.mapM fun p => match parseGate p with
    | some g => .ok g
    | none => .error s!"cannot parse gate '{p.trimAscii}'"

def Stats.toStr (s : Stats) : String :=
  s!"{s.idRem} {s.fuse} {s.cancel} {s.compl} {s.xconj}"

/-- The optimiser for the concrete gate set, with statistics. -/
def peephole (window fuel : Nat) (gs : List (MCG Op)) : List (MCG Op) × Stats :=
  optimize window fuel gs

end Qrig.Flat

end
