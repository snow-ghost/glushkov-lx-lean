import LRX.Graph
import Mathlib

namespace LRX.ZeroGap
variable {n : ℕ}

/-- A transposition between two different orbits puts its endpoints in one orbit. -/
theorem swap_distinct_orbits_same_cycle (p : State n) (a b : Fin n)
    (hnot : ¬p.SameCycle a b) : (Equiv.swap a b*p).SameCycle a b := by
  classical
  have hret : ∃ k : ℕ, 0 < k ∧ (p^k) b=b :=
    ⟨orderOf p,orderOf_pos p,by simp⟩
  let k := Nat.find hret
  have hk : 0 < k ∧ (p^k) b=b := Nat.find_spec hret
  have hne (j : ℕ) (hj : 0 < j) (hjk : j < k) : (p^j) b ≠ b := by
    intro he
    have hh := Nat.find_min hret hjk
    exact hh ⟨hj,he⟩
  have hna (j : ℕ) : (p^j) b ≠ a := by
    intro he
    apply hnot
    have hs : p.SameCycle b ((p^j) b) := (Equiv.Perm.SameCycle.refl p b).pow_right
    exact (he ▸ hs).symm
  let q := Equiv.swap a b*p
  have heq : ∀ j < k, (q^j) b=(p^j) b := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hp := ih (by omega)
      rw [pow_succ',Equiv.Perm.mul_apply,hp]
      change Equiv.swap a b (p ((p^j) b)) = (p^(j+1)) b
      have he : p ((p^j) b) = (p^(j+1)) b := by rw [pow_succ',Equiv.Perm.mul_apply]
      rw [he]
      exact Equiv.swap_apply_of_ne_of_ne (hna _) (hne _ (by omega) hj)
  have hlast : (q^k) b=a := by
    have he : k=(k-1)+1 := by omega
    rw [he,pow_succ',Equiv.Perm.mul_apply,heq (k-1) (by omega)]
    change Equiv.swap a b (p ((p^(k-1)) b)) = a
    have hp : p ((p^(k-1)) b)=b := by
      rw [← Equiv.Perm.mul_apply,← pow_succ',← he]
      exact hk.2
    rw [hp,Equiv.swap_apply_right]
  have hs : q.SameCycle b ((q^k) b) := (Equiv.Perm.SameCycle.refl q b).pow_right
  exact (hlast ▸ hs).symm

/-- Joining different orbits preserves every previous cyclic connection. -/
theorem same_cycle_after_orbit_merge (p : State n) (a b : Fin n)
    (hnot : ¬p.SameCycle a b) {i j : Fin n} (hij : p.SameCycle i j) :
    (Equiv.swap a b*p).SameCycle i j := by
  let q := Equiv.swap a b*p
  have hab : q.SameCycle a b := swap_distinct_orbits_same_cycle p a b hnot
  have hstep (x : Fin n) : q.SameCycle x (p x) := by
    have hx : q.SameCycle x (q x) := (Equiv.Perm.SameCycle.refl q x).apply_right
    by_cases ha : p x=a
    · have he : q x=b := by simp [q,Equiv.Perm.mul_apply,ha]
      rw [he] at hx
      rw [ha]
      exact hx.trans hab.symm
    · by_cases hb : p x=b
      · have he : q x=a := by simp [q,Equiv.Perm.mul_apply,hb]
        rw [he] at hx
        rw [hb]
        exact hx.trans hab
      · have he : q x=p x := by simp [q,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne ha hb]
        rwa [he] at hx
  obtain ⟨k,rfl⟩ := hij.exists_nat_pow_eq
  clear hij
  induction k with
  | zero => exact Equiv.Perm.SameCycle.refl q i
  | succ k ih =>
    rw [pow_succ',Equiv.Perm.mul_apply]
    exact ih.trans (hstep ((p^k) i))

#print axioms swap_distinct_orbits_same_cycle
#print axioms same_cycle_after_orbit_merge
end LRX.ZeroGap
