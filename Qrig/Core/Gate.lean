module

public import Qrig.Core.Circ
public import Qrig.Core.QOmega

/-!
# The concrete base prop used by `qrig`

The base generators are
* arbitrary one-qubit gates `u m₀₀ m₀₁ m₁₀ m₁₁` with entries in `ℚ(ω)`, and
* scalars (`0 → 0` morphisms) `ph z`, such as the global phase `ω` of Section 5.5.

Together with the distinguished involution `x`, the symmetry and the two control
functors this covers the Clifford+T, Gaussian Clifford+T, NCV and multiply controlled
Toffoli gate sets discussed in the paper, with exact arithmetic.
-/

@[expose] public section

namespace Qrig

/-- Base generators of the concrete prop. -/
inductive Gate where
  /-- a one-qubit gate `[[m00, m01], [m10, m11]]` -/
  | u (m00 m01 m10 m11 : QOmega)
  /-- a scalar (a `0 → 0` morphism) -/
  | ph (z : QOmega)
  deriving DecidableEq, Inhabited, Repr

instance : GateSig Gate where
  arity
    | .u .. => 1
    | .ph _ => 0

/-- Matrix semantics of the base generators. -/
def Gate.act : (g : Gate) → Vec QOmega → Vec QOmega
  | .u m00 m01 m10 m11, v => fun i =>
      if i = 0 then m00 * v 0 + m01 * v 1 else if i = 1 then m10 * v 0 + m11 * v 1 else v i
  | .ph z, v => fun i => if i = 0 then z * v 0 else v i

/-- Conjugate transpose of a base generator. -/
def Gate.adjoint : Gate → Gate
  | .u m00 m01 m10 m11 => .u m00.conj m10.conj m01.conj m11.conj
  | .ph z => .ph z.conj

theorem Gate.arity_adjoint (g : Gate) : GateSig.arity g.adjoint = GateSig.arity g := by
  cases g <;> rfl

/-- Circuits over the concrete gate set. -/
abbrev QCirc (n : Nat) := Circ Gate n

/-- Exact simulation of a circuit on a state vector of length `2ⁿ`. -/
def simulate {n : Nat} (c : QCirc n) (psi : Array QOmega) : Array QOmega :=
  denA Gate.act c psi

/-- The `j`-th computational basis vector of dimension `N`. -/
def basisVec (N j : Nat) : Array QOmega := tab N fun i => if i = j then 1 else 0

/-- The exact unitary of a circuit: `(unitary c)[i][j]` is the amplitude of `|i⟩`
in the image of `|j⟩` (row-major). -/
def unitary {n : Nat} (c : QCirc n) : Array (Array QOmega) :=
  let cols : Array (Array QOmega) := tab (2 ^ n) fun j => simulate c (basisVec (2 ^ n) j)
  tab (2 ^ n) fun i => tab (2 ^ n) fun j => aget (aget cols j) i

/-- Conjugate transpose (adjoint / dagger) of a circuit. -/
def dagger : {n : Nat} → QCirc n → QCirc n
  | _, .id n => .id n
  | _, .x => .x
  | _, .swap => .swap
  | _, .gen g => Gate.arity_adjoint g ▸ .gen g.adjoint
  | _, .seq f g => .seq (dagger g) (dagger f)
  | _, .par f g => .par (dagger f) (dagger g)
  | _, .ctrl b f => .ctrl b (dagger f)

/-- Exact equality of the semantics of two circuits on the same number of wires. -/
def equivExact {n : Nat} (c₁ c₂ : QCirc n) : Bool :=
  unitary c₁ == unitary c₂

/-- Is `u = λ v` for some scalar `λ ≠ 0` (checked by cross-multiplication)? -/
def proportional (u v : Array QOmega) : Bool :=
  match v.findIdx? (fun z => !z.isZero) with
  | none => u.all QOmega.isZero
  | some k =>
    let uk := aget u k
    let vk := aget v k
    !uk.isZero && u.size == v.size &&
      (List.range u.size).all fun i => aget u i * vk == aget v i * uk

/-- Equality of the semantics of two circuits up to a global scalar. -/
def equivUpToPhase {n : Nat} (c₁ c₂ : QCirc n) : Bool :=
  proportional (unitary c₁).flatten (unitary c₂).flatten

end Qrig

end
