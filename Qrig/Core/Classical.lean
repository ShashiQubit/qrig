module

public import Qrig.Core.Circ

/-!
# Gray codes and synthesis of reversible Boolean circuits (Section 2.3, Theorem 9)

* `grayR n` is the translation permutation `rₙ` between Gray order and lexicographic
  order: `grayR n i` is (the lexicographic index of) the `i`-th word `hₙ(i)` of the
  reflected Gray code.
* `ctrlBelowX w` is the NOT gate on the top wire, controlled by the wires below it
  according to the pattern `w` (the gate `C_{w}(x)` of the paper, built from `σ` and `C`).
* `mcx above below` is the multiply controlled NOT `C^{above}_{below}(x)`.
* `theta n i` is the image `β(θₙ,ᵢ)` of the Gray transposition `θₙ,ᵢ`, a multiply
  controlled NOT swapping the basis states `grayR n i` and `grayR n (i+1)`.
* `synthPerm n p` implements the functor `β : Perm₂ → cX`: it decomposes a permutation
  of `2ⁿ` basis states into Gray transpositions (bubble sort in Gray order) and returns
  the corresponding circuit of multiply controlled NOT gates.  The result is checked
  against the specification before being returned, and its correctness is proved in
  `QrigProofs.Classical` (`synthPerm_sound`).
-/

@[expose] public section

namespace Qrig

variable {G : Type} [GateSig G]

/-- The translation permutation `rₙ` of Section 2.3. -/
def grayR : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, i => if i < 2 ^ n then grayR n i else 2 ^ n + grayR n (2 ^ (n + 1) - 1 - i)

/-- Transport a circuit along an equality of wire counts. -/
def castC {m n : Nat} (h : m = n) (c : Circ G m) : Circ G n := h ▸ c

theorem ctrlBelowX_len (w : List Bool) : 2 + w.length = (w.length + 1) + 1 := by omega

/-- `C_{w}(x)`: NOT on the top wire, controlled by the wires below according to `w`
(`true` = positive control, `false` = negative control). -/
def ctrlBelowX : (w : List Bool) → Circ G (w.length + 1)
  | [] => .x
  | b :: w =>
    castC (ctrlBelowX_len w)
      (.seq (.par .swap (.id w.length))
        (.seq (castC (ctrlBelowX_len w).symm (.ctrl b (ctrlBelowX w)))
          (.par .swap (.id w.length))))

/-- `C^{above}_{below}(x)`: NOT gate controlled by the wires above and below it. -/
def mcx : (above below : List Bool) → Circ G (below.length + 1 + above.length)
  | [], below => ctrlBelowX below
  | b :: above, below => .ctrl b (mcx above below)

/-- NOT on wire `k` of `n` wires, controlled on all other wires by the bits of `a`
(wire `j` carries bit `n - 1 - j` of the basis index). -/
def mcxOn (n a k : Nat) : Circ G n :=
  let above := (List.range k).map fun j => a.testBit (n - 1 - j)
  let below := (List.range (n - 1 - k)).map fun j => a.testBit (n - 1 - (k + 1 + j))
  if h : below.length + 1 + above.length = n then castC h (mcx above below) else .id n

/-- The wire on which two basis states differ (meaningful if they differ in one bit). -/
def diffWire (n a b : Nat) : Nat := n - 1 - Nat.log2 (a ^^^ b)

/-- `β(θₙ,ᵢ)`: the multiply controlled NOT swapping `grayR n i` and `grayR n (i+1)`. -/
def theta (n i : Nat) : Circ G n :=
  mcxOn n (grayR n i) (diffWire n (grayR n i) (grayR n (i + 1)))

/-- Sequential composition of a list of circuits. -/
def seqList {n : Nat} : List (Circ G n) → Circ G n
  | [] => .id n
  | [c] => c
  | c :: cs => .seq c (seqList cs)

/-- One pass of bubble sort, recording the positions of the performed swaps. -/
def bubblePass : Nat → Array Nat → Nat → List Nat → Array Nat × List Nat
  | 0, q, _, acc => (q, acc)
  | fuel + 1, q, j, acc =>
    if j + 1 < q.size then
      if q[j]! > q[j + 1]! then bubblePass fuel (q.swapIfInBounds j (j + 1)) (j + 1) (j :: acc)
      else bubblePass fuel q (j + 1) acc
    else (q, acc)

/-- Bubble sort, recording the positions of the performed adjacent swaps (reversed). -/
def bubbleAux : Nat → Array Nat → List Nat → List Nat
  | 0, _, acc => acc
  | fuel + 1, q, acc =>
    let r := bubblePass q.size q 0 acc
    if r.2.length == acc.length then acc else bubbleAux fuel r.1 r.2

/-- Adjacent transpositions (in order of application) that sort `q`. -/
def bubbleSwaps (q : Array Nat) : List Nat := (bubbleAux (q.size + 1) q []).reverse

/-- Is `p` a permutation of `{0, …, N-1}`? -/
def isPermTable (N : Nat) (p : Array Nat) : Bool :=
  p.size == N && p.all (· < N) &&
    ((p.foldl (fun (seen : Array Bool) k => seen.setIfInBounds k true)
      (Array.replicate N false)).all id)

/-- Inverse of a permutation table. -/
def invTable (p : Array Nat) : Array Nat :=
  (List.range p.size).foldl (fun acc i => acc.setIfInBounds (p[i]!) i) (Array.replicate p.size 0)

/-- The unverified search part of `β`: decompose `p` into Gray transpositions. -/
def synthPermRaw (n : Nat) (p : Array Nat) : Circ G n :=
  let N := 2 ^ n
  let g : Array Nat := Array.ofFn (n := N) fun j => grayR n j.val
  let ginv := invTable g
  let q : Array Nat := Array.ofFn (n := N) fun j => ginv[p[g[j.val]!]!]!
  seqList ((bubbleSwaps q).map (theta n))

/-- Synthesise a reversible circuit (multiply controlled NOT gates only) implementing the
permutation `p` of the basis states `0 … 2ⁿ - 1`: basis state `i` is sent to `p[i]`.
The result is validated against the specification before being returned. -/
def synthPerm (n : Nat) (p : Array Nat) : Except String (Circ G n) :=
  if !isPermTable (2 ^ n) p then .error "not a permutation of the 2^n basis states"
  else
    let c : Circ G n := synthPermRaw n p
    if permTable c == p then .ok c else .error "internal error: synthesis check failed"

end Qrig

end
