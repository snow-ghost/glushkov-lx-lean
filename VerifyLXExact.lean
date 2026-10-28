import LX.SharpDiameterAll
import Lean.Util.CollectAxioms

-- These examples check the public statements, including every hypothesis.
example (n : ℕ) [NeZero n] (hn : 5 ≤ n) :
    (LX.diameter n : ℚ)=(3*(n : ℚ)^2-8*n+12-3*((n%2 : ℕ) : ℚ))/4 :=
  LX.exact_diameter_all n hn

example (n : ℕ) [NeZero n] (hn : 5 ≤ n) (a b : LX.State n) :
    ∃ w : List LX.Letter,a*LX.eval w=b ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12-3*((n%2 : ℕ) : ℤ) :=
  LX.sharp_route_all n hn a b

#check LX.odd_diameter_conjecture
#check LX.even_diameter_conjecture
#check LX.exact_diameter_all
#check LX.exact_diameter_all_int
#check LX.diameter_eq_max_dist
#print axioms LX.sharp_word_all
#print axioms LX.sharp_route_all
#print axioms LX.odd_diameter_conjecture
#print axioms LX.even_diameter_conjecture
#print axioms LX.exact_diameter_all
#print axioms LX.exact_diameter_all_int
#print axioms LX.diameter_eq_max_dist

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let prefixes := #[`LX]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := moduleNames[idx.toNat]!
    if !(prefixes.any (fun root => root.isPrefixOf mod)) then continue
    if !info.isTheorem then continue
    count := count + 1
    for ax in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Nonstandard axiom {ax} in {name} (module {mod})"
  logInfo m!"PASS: audited {count} project theorems in the exact-diameter import closure."
