import LRX.AreaWindowSplitSquare
import LRX.PrefixCoreBalancedEnergy

set_option maxHeartbeats 3000000
namespace LRX.FiniteCuts

/-- Complete scalar reduction of the f=2, epsilon=2 row before the extra
core-capacity and split-family bounds. The six rows are proved exhaustive. -/
theorem two_fixed_energy_two_rows (m parity v r U S2 : ℤ)
    (hp : parity=0 ∨ parity=1) (hv : 2 ≤ v) (hr : 6 ≤ r)
    (hU : 1 ≤ U) (hUp : U ≤ 2-parity) (hm : 2*v+2+U ≤ m)
    (hcap : S2 ≤ (m-1)*(2*m+parity-r))
    (henv : S2 ≤ (m-1)^2+(m+parity+1-r)^2)
    (harea : (2*m+parity-r)^2-2*S2+4*(2*m+parity-r-1)+4+parity ≤ 4+2*parity)
    (hdensity : 2*(m*(m+parity)-2) ≤ 4*U*(2*m+parity-v-2-U)+S2) :
    parity=0 ∧ U=2 ∧ v=2 ∧
      ((m=8 ∧ r=8) ∨ (m=8 ∧ r=9) ∨ (m=9 ∧ r=8) ∨
        (m=9 ∧ r=9) ∨ (m=9 ∧ r=10) ∨ (m=10 ∧ r=9)) := by
  have hm7 : 7 ≤ m := by omega
  have hUeq : U=2 := by
    have hcases : U=1 ∨ U=2 := by omega
    rcases hcases with h | h
    · subst U
      have hprod := mul_nonneg (show 0 ≤ m-1 by omega) (show 0 ≤ r-6 by omega)
      rcases hp with hp | hp <;> subst parity <;> nlinarith only [hprod,hcap,hdensity,hv,hr,hm7]
    · exact h
  have hpeq : parity=0 := by omega
  subst U parity
  have hm8 : 8 ≤ m := by omega
  have hr13 : r ≤ 13 := by
    by_contra hh
    have hprod := mul_nonneg (show 0 ≤ m-1 by omega) (show 0 ≤ r-14 by omega)
    nlinarith only [hprod,hcap,hdensity,hv]
  have hm22 : m ≤ 22 := by
    have hsq := mul_nonneg (show 0 ≤ 13-r by omega) (show 0 ≤ 13+r by omega)
    nlinarith only [hsq,harea,henv]
  interval_cases r <;> interval_cases m <;> omega

/-- The six rows are incompatible with the real split-family square bound,
balanced core capacity, and evenness of total energy. -/
theorem two_fixed_energy_two_scalar_impossible (m parity v r U S2 c z : ℤ)
    (hp : parity=0 ∨ parity=1) (hv : 2 ≤ v) (hr : 6 ≤ r)
    (hU : 1 ≤ U) (hUp : U ≤ 2-parity) (hm : 2*v+2+U ≤ m)
    (hcap : S2 ≤ (m-1)*(2*m+parity-r))
    (henv : S2 ≤ (m-1)^2+(m+parity+1-r)^2)
    (harea : (2*m+parity-r)^2-2*S2+4*(2*m+parity-r-1)+4+parity ≤ 4+2*parity)
    (hdensity : 2*(m*(m+parity)-2) ≤ 4*U*(2*m+parity-v-2-U)+S2)
    (hcore : 2*c ≤ r-2 ∧ r-2 ≤ 2*c+1)
    (hbalanced : 2*(m*(m+parity)-2) ≤ 2*c*(2*m+parity-c)+S2)
    (hsplit : S2 ≤ (2*m+parity-r-v)^2+v^2)
    (heven : m*(m+parity)-2=2*z) : False := by
  obtain ⟨rfl,rfl,rfl,hrows⟩ := two_fixed_energy_two_rows m parity v r U S2 hp hv hr hU hUp hm
    hcap henv harea hdensity
  rcases hrows with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals
    have hcl : 3 ≤ c := by omega
    have hcu : c ≤ 4 := by omega
    interval_cases c <;> norm_num at * <;> omega

#print axioms two_fixed_energy_two_rows
#print axioms two_fixed_energy_two_scalar_impossible
end LRX.FiniteCuts
