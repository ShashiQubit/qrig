module

public import Qrig.Core.Serialize
public import Qrig.Core.Classical
public import Qrig.Core.GateFuse
public import Qrig.Core.Peephole

/-!
# C entry point of the `qrig` library

A single exported C function `qrig_call(command, argument)` dispatches to the verified
core.  Arguments and results are strings (see `Qrig.Core.Serialize` for the format);
errors are reported as strings starting with `ERR:`.

| command      | argument                    | result                                   |
|--------------|-----------------------------|------------------------------------------|
| `check`      | circuit                     | `n size classical`                       |
| `unitary`    | circuit                     | `2ⁿ` lines of `2ⁿ` scalars (row-major)    |
| `simulate`   | circuit `|` vector          | the output vector                         |
| `perm`       | classical circuit           | the permutation table                    |
| `synth`      | `n p₀ … p_{2ⁿ-1}`           | a circuit of multiply controlled NOTs     |
| `simplify`   | circuit                     | an equivalent, optimised circuit          |
| `dagger`     | circuit                     | the adjoint circuit                       |
| `equiv`      | circuit `|` circuit         | `1` iff the unitaries are equal           |
| `equivphase` | circuit `|` circuit         | `1` iff equal up to a global scalar       |
| `gray`       | `n`                         | `grayR n 0 … grayR n (2ⁿ-1)`              |
| `peephole`   | `window fuel` `|` gate list  | `stats` `|` optimised gate list (see `Qrig.Core.Peephole`) |
| `version`    |                             | version string                            |
-/

@[expose] public section

namespace Qrig

def version : String := "qrig 1.1.0"

def maxWires : Nat := 16

def errStr (e : String) : String := "ERR: " ++ e

def withCirc (s : String) (k : AnyCirc → String) : String :=
  match parseCirc s with
  | .ok c => if c.n > maxWires then errStr s!"too many wires ({c.n} > {maxWires})" else k c
  | .error e => errStr e

def splitBar (s : String) : Option (String × String) :=
  match s.splitOn "|" with
  | [a, b] => some (a, b)
  | _ => none

def matToString (m : Array (Array QOmega)) : String :=
  "\n".intercalate (m.toList.map vecToString)

def qrigDispatch (cmd arg : String) : String :=
  match cmd with
  | "version" => version
  | "check" => withCirc arg fun ⟨n, c⟩ => s!"{n} {size c} {if isClassical c then 1 else 0}"
  | "unitary" => withCirc arg fun ⟨_, c⟩ => matToString (unitary c)
  | "simulate" =>
    match splitBar arg with
    | none => errStr "simulate expects 'circuit | vector'"
    | some (cs, vs) => withCirc cs fun ⟨n, c⟩ =>
      match parseVec vs with
      | .error e => errStr e
      | .ok v =>
        if v.size != 2 ^ n then errStr s!"state vector must have length {2 ^ n}"
        else vecToString (simulate c v)
  | "perm" => withCirc arg fun ⟨_, c⟩ =>
      if isClassical c then " ".intercalate ((permTable c).toList.map toString)
      else errStr "circuit is not classical (it contains base generators)"
  | "synth" =>
    match (tokenize arg).mapM String.toNat? with
    | some (n :: p) =>
      if n > maxWires then errStr "too many wires"
      else match synthPerm (G := Gate) n p.toArray with
        | .ok c => (simplifyQ c).serialize
        | .error e => errStr e
    | _ => errStr "synth expects 'n p0 p1 ...'"
  | "simplify" => withCirc arg fun ⟨_, c⟩ => (simplifyQ c).serialize
  | "dagger" => withCirc arg fun ⟨_, c⟩ => (dagger c).serialize
  | "equiv" | "equivphase" =>
    match splitBar arg with
    | none => errStr "equiv expects 'circuit | circuit'"
    | some (s1, s2) => withCirc s1 fun ⟨n, c₁⟩ => withCirc s2 fun ⟨m, c₂⟩ =>
      if h : n = m then
        let b := if cmd == "equiv" then equivExact (h ▸ c₁) c₂ else equivUpToPhase (h ▸ c₁) c₂
        if b then "1" else "0"
      else "0"
  | "gray" =>
    match arg.trimAscii.toString.toNat? with
    | some n => if n > maxWires then errStr "too many wires"
      else " ".intercalate ((List.range (2 ^ n)).map fun i => toString (grayR n i))
    | none => errStr "gray expects a number"
  | "peephole" =>
    match splitBar arg with
    | none => errStr "peephole expects 'window fuel | gates'"
    | some (ps, gs) =>
      match (tokenize ps).mapM String.toNat? with
      | some [window, fuel] =>
        match Flat.parseGates gs with
        | .ok l =>
          let r := Flat.peephole window fuel l
          r.2.toStr ++ " | " ++ Flat.gatesToString r.1
        | .error e => errStr e
      | _ => errStr "peephole expects 'window fuel | gates'"
  | _ => errStr s!"unknown command '{cmd}'"

/-- The exported C entry point. -/
@[export qrig_call]
def qrigCall (cmd arg : String) : String := qrigDispatch cmd arg

end Qrig

end
