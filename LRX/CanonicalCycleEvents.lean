import LRX.EventTreePotential

namespace LRX.ZeroGap
variable {n : ℕ} [NeZero n]

/-- In a single cycle with canonical displacements, a minimal event trace
cannot wind through the finite cut: all its arcs are linearly increasing. -/
theorem canonical_cycle_events_linear {p : State n} (hp : p.IsCycle)
    (events : List (Event n)) (hprod : (events.map eventSwap).prod=p)
    (hactive : ∀ e ∈ events, e.1 ∈ p.support ∧ e.2 ∈ p.support)
    (hlen : events.length+1=p.support.card)
    (hneq : ∀ e ∈ events, e.1 ≠ e.2)
    (htravel : ∀ i, Travel events i (p.symm i) ((p.symm i : ℤ)-(i : ℤ))) :
    ∀ e ∈ events, e.1.val < e.2.val := by
  classical
  obtain ⟨root,hr⟩ := hp.nonempty_support
  have hc := cycle_event_carrier hp events hprod hactive root hr
  obtain ⟨H,hH⟩ := minimal_event_potential events root (by rwa [hc])
    (fun e => (distance e.1 e.2 : ℤ))
  let F : Fin n → ℤ := fun i => H i-(i : ℤ)
  have hinv (i : Fin n) : F (p⁻¹ i)=F i := by
    have h := (htravel i).potential H hH
    simp only [Equiv.Perm.inv_def]
    dsimp [F]
    linarith
  have hpow (k : ℕ) (i : Fin n) : F (((p⁻¹)^k) i)=F i := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ',Equiv.Perm.mul_apply,hinv]
      exact ih
  intro e he
  have ha := hactive e he
  have h0 : p⁻¹ e.1 ≠ e.1 := Equiv.Perm.mem_support.mp (by simpa using ha.1)
  have h1 : p⁻¹ e.2 ≠ e.2 := Equiv.Perm.mem_support.mp (by simpa using ha.2)
  have hsame := hp.inv.sameCycle h0 h1
  obtain ⟨k,hk⟩ := hsame.exists_nat_pow_eq
  have hF : F e.2=F e.1 := by rw [← hk]; exact hpow k e.1
  have hw := hH e he
  have hpos := distance_pos e.1 e.2 (Ne.symm (hneq e he))
  have hposZ : (0 : ℤ) < (distance e.1 e.2 : ℤ) := by exact_mod_cast hpos
  have hlt : (e.1 : ℤ) < (e.2 : ℤ) := by dsimp [F] at hF; linarith
  exact_mod_cast hlt

#print axioms canonical_cycle_events_linear
end LRX.ZeroGap
