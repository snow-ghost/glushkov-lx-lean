import LX.AnchorPhasePrice
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- Global minimum over all balanced integer lifts and all phases. It is
stronger than minimizing the anchor height. -/
def GlobalMinimum (p : State n) (a : Fin n) : Prop :=
  ∀ c d, IsLift p.symm c d → energy (displacement p a) ≤ energy d

theorem global_minimum_majorized {p : State n} {a : Fin n} (h : GlobalMinimum p a) :
    Majorized (displacement p a) :=
  minimal_majorized (NeZero.pos n) (is_lift p a) h

theorem recover_global_minimum {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p.symm c d) (hm : ∀ c' d', IsLift p.symm c' d' → energy d ≤ energy d') :
    ∃ a : Fin n, displacement p a=d ∧ (phase p a : Fin n)=(c : Fin n) ∧ GlobalMinimum p a := by
  have hmajor := minimal_majorized (NeZero.pos n) hd hm
  obtain ⟨a,_,ha⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n)) d
    ⟨0,Finset.mem_univ _⟩
  have hh := recovers_strict_strip hd a (fun i => ha i (Finset.mem_univ _)) (by
    intro i
    have hw := range_bound hd.1 hmajor i a
    omega)
  refine ⟨a,hh.1,hh.2,?_⟩
  intro c' d' hd'
  rw [hh.1]
  exact hm c' d' hd'

/-- The finite anchor family contains a globally energy-minimal actual lift. -/
theorem exists_global_minimum (p : State n) : ∃ a : Fin n, GlobalMinimum p a := by
  obtain ⟨c,d,hd,hm⟩ := exists_minimal p.symm
  obtain ⟨a,_,_,ha⟩ := recover_global_minimum hd hm
  exact ⟨a,ha⟩

theorem global_minimum_exchanges {p : State n} {a : Fin n} (ha : GlobalMinimum p a) :
    ∀ b,inversions (displacement p a) ≤ inversions (displacement p b) :=
  (minimum_energy_iff_minimum_exchanges p a).mp (fun b => ha _ _ (is_lift p b))

/-- Tight majorization subsets move to a new actual anchor at no exchange
cost. Majorization of the new phase is derived from global minimality. -/
theorem zero_slack_phase {p : State n} {a : Fin n} (ha : GlobalMinimum p a)
    (S : Finset (Fin n))
    (htight : 2*(∑ i ∈ S,displacement p a i)=(S.card : ℤ)*((n : ℤ)-S.card)) :
    ∃ b : Fin n, GlobalMinimum p b ∧
      displacement p b=phaseShift (displacement p a) S ∧
      (phase p b : Fin n)=(phase p a : Fin n)+(S.card : Fin n) ∧
      inversions (displacement p b)=inversions (displacement p a) := by
  let d := phaseShift (displacement p a) S
  have hd := shift_lift (is_lift p a) S
  have he : energy d=energy (displacement p a) := by
    have hh := shift_energy (displacement p a) S (is_lift p a).1
    rw [htight,sub_self,mul_zero] at hh
    change (energy d : ℤ)-energy (displacement p a)=0 at hh
    omega
  have hm : ∀ c' d',IsLift p.symm c' d' → energy d ≤ energy d' := by
    intro c' d' hd'
    rw [he]
    exact ha c' d' hd'
  obtain ⟨b,hb,hc,hglobal⟩ := recover_global_minimum hd hm
  refine ⟨b,hglobal,hb,?_,?_⟩
  · simpa only [Int.cast_add,Int.cast_natCast] using hc
  · have hle := global_minimum_exchanges ha b
    have hge := global_minimum_exchanges hglobal a
    omega


#print axioms exists_global_minimum
#print axioms global_minimum_exchanges
#print axioms zero_slack_phase
end LX.AnchoredPhases
