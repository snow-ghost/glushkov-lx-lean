import LRX.ExactCycleEventFactorization

namespace LRX.ZeroGap
variable {n : ℕ}

/-- Adding one new leaf to a cycle by a transposition produces a cycle on the enlarged support. -/
theorem cycle_leaf_insertion (p : State n) (hp : p.IsCycle) (a b : Fin n)
    (ha : a ∉ p.support) (hb : b ∈ p.support) :
    (Equiv.swap a b*p).IsCycle ∧ (Equiv.swap a b*p).support = insert a p.support := by
  classical
  let xs := p.toList b
  have hlen : 2 ≤ xs.length := Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hb
  have hnodup : xs.Nodup := Equiv.Perm.nodup_toList p b
  have hprod : xs.formPerm = p := by
    rw [Equiv.Perm.formPerm_toList,hp.cycleOf_eq (Equiv.Perm.mem_support.mp hb)]
  have hs : xs.toFinset = p.support := by
    rw [← hprod]
    exact (List.support_formPerm_of_nodup xs hnodup (fun x he => by
      have hh := congrArg List.length he
      simp only [List.length_singleton] at hh
      omega)).symm
  have ha' : a ∉ xs := by
    intro h
    exact ha (hs ▸ (List.mem_toFinset.mpr h))
  have hnew : (a::xs).Nodup := List.nodup_cons.mpr ⟨ha',hnodup⟩
  have he : (a::xs).formPerm = Equiv.swap a b*p := by
    have hhead := Equiv.Perm.toList_getElem_zero (p := p) (x := b) hb
    cases hx : xs with
    | nil => simp [hx] at hlen
    | cons c rest =>
      have hcb : c = b := by
        change xs[0] = b at hhead
        simpa only [hx,List.getElem_cons_zero] using hhead
      subst c
      rw [List.formPerm_cons_cons]
      rw [hx] at hprod
      rw [hprod]
  constructor
  · rw [← he]
    exact List.isCycle_formPerm hnew (by simp only [List.length_cons]; omega)
  · rw [← he,List.support_formPerm_of_nodup _ hnew (fun x hh => by
      have hh' := congrArg List.length hh
      simp only [List.length_cons,List.length_nil] at hh'
      omega),List.toFinset_cons,hs]

#print axioms cycle_leaf_insertion
end LRX.ZeroGap
