module

/-!
# Controlled props: syntax and semantics

This file contains the executable core of `qrig`: the syntax of the *controlled prop*
`cP` of the paper "One rig to control them all" (Heunen, Kaarsgaard, Lemonnier), and its
semantics in the rig completion `P₂` (the functor `A : cP → P₂` of Section 4.4).

* `Circ G n` is the type of circuits on `n` wires over a set of base generators `G`.
  Its constructors are exactly the operations of Definition 6: identities, the distinguished
  involution `x` (NOT), the symmetry `σ₁,₁` (`swap`), base generators, sequential
  composition, parallel composition `f + g`, and the two control functors `C⁰`, `C¹`.
* A vector on `n` wires is a function `Nat → R` whose meaningful entries are the
  indices `0 ≤ i < 2ⁿ` (lexicographic order, the top wire is the most significant bit).
  `den` interprets a circuit as a transformation of such vectors, following the
  definition of `A`: `C¹(f) ↦ id ⊕ A(f)`, `C⁰(f) ↦ A(f) ⊕ id`, `f + g ↦ A(f) ⊗ A(g)`.
* `denA` is an efficient array-based evaluator; it is proved equal to `den`
  in `QrigProofs.ArrayEval`.

Nothing here depends on Mathlib, so the file compiles to self-contained C.
-/

@[expose] public section

namespace Qrig

/-- A signature of base generators: each generator acts on `arity g` wires. -/
class GateSig (G : Type) where
  arity : G → Nat

/-- Circuits of the controlled prop `cP`, indexed by their number of wires. -/
inductive Circ (G : Type) [GateSig G] : Nat → Type where
  /-- identity on `n` wires -/
  | id (n : Nat) : Circ G n
  /-- the distinguished involution (NOT gate) -/
  | x : Circ G 1
  /-- the symmetry `σ₁,₁` exchanging two wires -/
  | swap : Circ G 2
  /-- a base generator -/
  | gen (g : G) : Circ G (GateSig.arity g)
  /-- sequential composition: first `f`, then `g` -/
  | seq {n : Nat} (f g : Circ G n) : Circ G n
  /-- parallel composition `f + g` (`f` on the top wires) -/
  | par {m n : Nat} (f : Circ G m) (g : Circ G n) : Circ G (m + n)
  /-- the control functors: `ctrl true f = C¹(f)`, `ctrl false f = C⁰(f)`;
  the control wire is the new top wire -/
  | ctrl {n : Nat} (b : Bool) (f : Circ G n) : Circ G (n + 1)

/-- A (state) vector: amplitudes indexed by basis states `0 ≤ i < 2ⁿ`. -/
abbrev Vec (R : Type) := Nat → R

section Den

variable {G : Type} [GateSig G] {R : Type}

/-- Offset of the controlled half for a control of colour `b` on `n` target wires. -/
def ctrlOff (b : Bool) (n : Nat) : Nat := if b then 2 ^ n else 0

/-- Is basis state `i` (on `n+1` wires) in the half selected by a control of colour `b`? -/
def inHalf (b : Bool) (n i : Nat) : Bool :=
  if b then decide (2 ^ n ≤ i ∧ i < 2 ^ (n + 1)) else decide (i < 2 ^ n)

/-- The semantics of circuits (the functor `A : cP → P₂`), given the semantics `act`
of the base generators.  Outside of the meaningful range every circuit acts as the
identity. -/
def den (act : (g : G) → Vec R → Vec R) : {n : Nat} → Circ G n → Vec R → Vec R
  | _, .id _, v => v
  | _, .x, v => fun i => if i < 2 then v (1 - i) else v i
  | _, .swap, v => fun i => if i = 1 then v 2 else if i = 2 then v 1 else v i
  | _, .gen g, v => fun i => if i < 2 ^ GateSig.arity g then act g v i else v i
  | _, .seq f g, v => den act g (den act f v)
  | _, @Circ.par _ _ m n f g, v => fun i =>
      if i < 2 ^ (m + n) then
        den act f (fun a => den act g (fun b => v (a * 2 ^ n + b)) (i % 2 ^ n)) (i / 2 ^ n)
      else v i
  | _, @Circ.ctrl _ _ n b f, v => fun i =>
      if inHalf b n i then den act f (fun j => v (ctrlOff b n + j)) (i - ctrlOff b n)
      else v i

/-- Classical (forward) semantics of a circuit on basis states.  This is meaningful for
circuits built from `x`, `swap`, identities, composition and control only (reversible
Boolean circuits, the controlled prop `cX` of Theorem 9); base generators are ignored. -/
def perm : {n : Nat} → Circ G n → Nat → Nat
  | _, .id _, i => i
  | _, .x, i => if i < 2 then 1 - i else i
  | _, .swap, i => if i = 1 then 2 else if i = 2 then 1 else i
  | _, .gen _, i => i
  | _, .seq f g, i => perm g (perm f i)
  | _, @Circ.par _ _ m n f g, i =>
      if i < 2 ^ (m + n) then perm f (i / 2 ^ n) * 2 ^ n + perm g (i % 2 ^ n) else i
  | _, @Circ.ctrl _ _ n b f, i =>
      if inHalf b n i then ctrlOff b n + perm f (i - ctrlOff b n) else i

/-- Does the circuit avoid base generators (i.e. is it a reversible Boolean circuit)? -/
def isClassical : {n : Nat} → Circ G n → Bool
  | _, .gen _ => false
  | _, .seq f g => isClassical f && isClassical g
  | _, .par f g => isClassical f && isClassical g
  | _, .ctrl _ f => isClassical f
  | _, _ => true

/-- Number of primitive gates (`x`, `swap`, generators) in a circuit. -/
def size : {n : Nat} → Circ G n → Nat
  | _, .id _ => 0
  | _, .x => 1
  | _, .swap => 1
  | _, .gen _ => 1
  | _, .seq f g => size f + size g
  | _, .par f g => size f + size g
  | _, .ctrl _ f => size f

end Den

section ArrayEval

variable {G : Type} [GateSig G] {R : Type} [Inhabited R]

/-- Read an array as a vector. -/
def aget (a : Array R) : Vec R := fun i => a[i]!

/-- Tabulate the first `N` entries of a vector. -/
def tab (N : Nat) (v : Vec R) : Array R := Array.ofFn (n := N) fun i => v i.val

/-- Efficient array-based evaluator; proved to agree with `den` (`denA_eq_tab_den`). -/
def denA (act : (g : G) → Vec R → Vec R) : {n : Nat} → Circ G n → Array R → Array R
  | _, .id _, a => a
  | _, .x, a => tab 2 (den act (Circ.x (G := G)) (aget a))
  | _, .swap, a => tab 4 (den act (Circ.swap (G := G)) (aget a))
  | _, .gen g, a => tab (2 ^ GateSig.arity g) (act g (aget a))
  | _, .seq f g, a => denA act g (denA act f a)
  | _, @Circ.par _ _ m n f g, a =>
      let blocks : Array (Array R) :=
        tab (2 ^ m) fun p => denA act g (tab (2 ^ n) fun b => aget a (p * 2 ^ n + b))
      let cols : Array (Array R) :=
        tab (2 ^ n) fun b => denA act f (tab (2 ^ m) fun p => aget (aget blocks p) b)
      tab (2 ^ (m + n)) fun i => aget (aget cols (i % 2 ^ n)) (i / 2 ^ n)
  | _, @Circ.ctrl _ _ n b f, a =>
      let s := denA act f (tab (2 ^ n) fun j => aget a (ctrlOff b n + j))
      tab (2 ^ (n + 1)) fun i => if inHalf b n i then aget s (i - ctrlOff b n) else aget a i

/-- Array version of `perm`, tabulated on all basis states. -/
def permTable {n : Nat} (c : Circ G n) : Array Nat :=
  Array.ofFn (n := 2 ^ n) fun i => perm c i.val

end ArrayEval

end Qrig

end
