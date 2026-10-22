import LRX.FiniteInversionDecomposition

namespace LRX.FiniteCuts
variable {n : ℕ}

/-- Delete source row a and target column p(a), independently preserving
the order on the two complements. -/
def contract (p : State (n+1)) (a : Fin (n+1)) : State n :=
  (finSuccAboveEquiv a).trans
    ((p.subtypeEquiv (p := fun i => i ≠ a) (q := fun j => j ≠ p a)
      (fun _ => not_congr p.injective.eq_iff.symm)).trans (finSuccAboveEquiv (p a)).symm)

theorem contract_entry (p : State (n+1)) (a : Fin (n+1)) (i : Fin n) :
    (p a).succAbove (contract p a i)=p (a.succAbove i) := by
  change ((finSuccAboveEquiv (p a)) (contract p a i)).val=p (a.succAbove i)
  simp [contract,Equiv.subtypeEquiv,finSuccAboveEquiv_apply]

theorem contract_inverse (p : State (n+1)) (a : Fin (n+1)) :
    (contract p a).symm=contract p.symm (p a) := by
  apply Equiv.ext
  intro i
  apply a.succAbove_right_injective
  have h := contract_entry p a ((contract p a).symm i)
  rw [(contract p a).apply_symm_apply] at h
  have h' := contract_entry p.symm (p a) i
  simp only [p.symm_apply_apply] at h'
  rw [h']
  simpa only [p.symm_apply_apply] using (congrArg p.symm h).symm

#print axioms contract_entry
#print axioms contract_inverse
end LRX.FiniteCuts
