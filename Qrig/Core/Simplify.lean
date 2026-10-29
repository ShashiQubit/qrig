module

public import Qrig.Core.Circ
public import Qrig.Core.Classical

/-!
# Circuit optimisation by the control equations

A semantics-preserving rewriting pass that uses the equations of Figure 1 as
optimisation rules:

* (b) identity:        `C^b(id) ⇝ id`
* (a) composition:     `C^b(f) ; C^b(g) ⇝ C^b(f ; g)`  (fusion of controlled blocks)
* (e) complementarity: `C⁰(f) ; C¹(f) ⇝ id₁ + f`  and, using (f), `C¹(f) ; C⁰(f) ⇝ id₁ + f`
* involutions:         `x ; x ⇝ id`, `σ ; σ ⇝ id`
* units:               `id ; f ⇝ f`, `f ; id ⇝ f`, `id + id ⇝ id`
* functoriality of `+`: `(f + id) ; (f' + id) ⇝ (f ; f') + id` and
                        `(id + g) ; (id + g') ⇝ id + (g ; g')`

together with a user supplied fusion rule for base generators (`fuse`), e.g.
multiplication of one-qubit matrices.  Soundness (`den (simplify c) = den c`) is proved
in `QrigProofs.Simplify`.
-/

@[expose] public section

namespace Qrig

variable {G : Type} [GateSig G] [DecidableEq G]

/-- Is the circuit the NOT gate? -/
def Circ.isX : {k : Nat} → Circ G k → Bool
  | _, .x => true
  | _, _ => false

/-- Is the circuit the swap? -/
def Circ.isSwap : {k : Nat} → Circ G k → Bool
  | _, .swap => true
  | _, _ => false

/-- Syntactic equality of circuits (possibly on different numbers of wires). -/
def Circ.beq : {m n : Nat} → Circ G m → Circ G n → Bool
  | _, _, .id a, g => match g with
    | .id b => a == b
    | _ => false
  | _, _, .x, g => g.isX
  | _, _, .swap, g => g.isSwap
  | _, _, .gen h, g => match g with
    | .gen h' => decide (h = h')
    | _ => false
  | _, _, .seq f₁ f₂, g => match g with
    | .seq g₁ g₂ => Circ.beq f₁ g₁ && Circ.beq f₂ g₂
    | _ => false
  | _, _, .par f₁ f₂, g => match g with
    | .par g₁ g₂ => Circ.beq f₁ g₁ && Circ.beq f₂ g₂
    | _ => false
  | _, _, .ctrl b f, g => match g with
    | .ctrl b' g' => b == b' && Circ.beq f g'
    | _ => false

/-- Is the circuit syntactically an identity? -/
def Circ.isId : {n : Nat} → Circ G n → Bool
  | _, .id _ => true
  | _, _ => false

/-- Smart constructor for control, using equation (b). -/
def mkCtrl {n : Nat} (b : Bool) : Circ G n → Circ G (n + 1)
  | .id _ => .id (n + 1)
  | f => .ctrl b f

/-- Smart constructor for parallel composition. -/
def mkPar {m n : Nat} : Circ G m → Circ G n → Circ G (m + n)
  | .id _, .id _ => .id (m + n)
  | f, g => .par f g

theorem one_add_eq (n : Nat) : 1 + n = n + 1 := Nat.add_comm 1 n

/-- A fusion rule: `fuse f g = some r` should mean that `r` implements `f ; g`. -/
abbrev FuseRule (G : Type) [GateSig G] := {n : Nat} → Circ G n → Circ G n → Option (Circ G n)

/-- View a circuit as a parallel composition `a + b` with `a` on `m` wires. -/
def viewPar (m n : Nat) : {k : Nat} → Circ G k → Option (Circ G m × Circ G n)
  | _, @Circ.par _ _ m' n' a b =>
    if h : m' = m ∧ n' = n then some (h.1 ▸ a, h.2 ▸ b) else none
  | _, _ => none

/-- View a circuit as a controlled circuit `C^b(f)` with `f` on `n` wires. -/
def viewCtrl (n : Nat) : {k : Nat} → Circ G k → Option (Bool × Circ G n)
  | _, @Circ.ctrl _ _ n' b f => if h : n' = n then some (b, h ▸ f) else none
  | _, _ => none

/-- Try to replace `f ; g` by a single, simpler circuit. -/
def combine (fuse : FuseRule G) : {n : Nat} → Circ G n → Circ G n → Option (Circ G n)
  | _, .id _, g => some g
  | _, .x, g =>
    if g.isX then some (.id 1) else if g.isId then some .x else fuse .x g
  | _, .swap, g =>
    if g.isSwap then some (.id 2) else if g.isId then some .swap else fuse .swap g
  | _, .gen h, g => if g.isId then some (.gen h) else fuse (.gen h) g
  | _, .seq f₁ f₂, g => if g.isId then some (.seq f₁ f₂) else fuse (.seq f₁ f₂) g
  | _, @Circ.par _ _ m n a b, g =>
    if g.isId then some (.par a b) else
    match viewPar m n g with
    | some (a', b') =>
      if b.isId && b'.isId then
        some (mkPar ((combine fuse a a').getD (.seq a a')) (.id n))
      else if a.isId && a'.isId then
        some (mkPar (.id m) ((combine fuse b b').getD (.seq b b')))
      else fuse (.par a b) g
    | none => fuse (.par a b) g
  | _, @Circ.ctrl _ _ n b f, g =>
    if g.isId then some (.ctrl b f) else
    match viewCtrl n g with
    | some (b', g') =>
      if b == b' then
        match combine fuse f g' with
        | some r => some (mkCtrl b r)
        | none => some (.ctrl b (.seq f g'))
      else if Circ.beq f g' then some (castC (one_add_eq _) (.par (.id 1) f))
      else fuse (.ctrl b f) g
    | none => fuse (.ctrl b f) g

/-- Push a circuit onto a (reversed) list of sequentially composed circuits,
cancelling / fusing with the previous one when possible. -/
def pushSeq (fuse : FuseRule G) {n : Nat} (acc : List (Circ G n)) (c : Circ G n) :
    List (Circ G n) :=
  match acc with
  | [] => if c.isId then [] else [c]
  | t :: rest =>
    match combine fuse t c with
    | some r => if r.isId then rest else r :: rest
    | none => if c.isId then acc else c :: acc

/-- The components of a sequential composition. -/
def flattenSeq : {n : Nat} → Circ G n → List (Circ G n)
  | _, .seq f g => flattenSeq f ++ flattenSeq g
  | _, c => [c]

/-- One bottom-up simplification pass. -/
def simplifyPass (fuse : FuseRule G) : {n : Nat} → Circ G n → Circ G n
  | _, .seq f g =>
    seqList ((flattenSeq (simplifyPass fuse f) ++ flattenSeq (simplifyPass fuse g)).foldl
      (pushSeq fuse) []).reverse
  | _, .par f g => mkPar (simplifyPass fuse f) (simplifyPass fuse g)
  | _, .ctrl b f => mkCtrl b (simplifyPass fuse f)
  | _, .id n => .id n
  | _, .x => .x
  | _, .swap => .swap
  | _, .gen g => .gen g

/-- Iterate `simplifyPass` (at most `fuel` times, stopping at a fixed point). -/
def simplifyN (fuse : FuseRule G) : Nat → {n : Nat} → Circ G n → Circ G n
  | 0, _, c => c
  | k + 1, _, c =>
    let c' := simplifyPass fuse c
    if Circ.beq c' c then c else simplifyN fuse k c'

/-- The optimiser. -/
def simplify (fuse : FuseRule G) {n : Nat} (c : Circ G n) : Circ G n := simplifyN fuse 16 c

end Qrig

end
