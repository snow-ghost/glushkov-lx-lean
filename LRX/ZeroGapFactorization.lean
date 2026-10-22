import LRX.ZeroGapSorting
import LRX.ClosedReachableService

/-! Recentring in a sorting trace only conjugates its endpoint transpositions.
The original finite permutation has exactly the traced number of swap factors. -/
namespace LRX.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem conjugate_swap (r q : State n) (hq : q.IsSwap) : (MulAut.conj r q).IsSwap := by
  obtain ⟨a,b,hab,rfl⟩ := hq
  refine ⟨r a,r b,fun h => hab (r.injective h),?_⟩
  exact (Equiv.swap_apply_apply r a b).symm

theorem SortingTrace.factorization {p : State n} {d : Fin n → ℤ} {M : ℕ}
    (htrace : SortingTrace p d M) (hd : AffineLift.IsLift p 0 d) :
    ∃ factors : List (State n), factors.prod=p ∧ (∀ q ∈ factors, q.IsSwap) ∧ factors.length=M := by
  induction htrace with
  | @done p d hz =>
    have hp : p=1 := by
      apply Equiv.ext
      intro i
      have h := AffineLift.lift_residue hd (p i)
      simpa only [hz,Int.cast_zero,add_zero,p.symm_apply_apply,Equiv.Perm.one_apply] using h
    exact ⟨[],by simp [hp],by simp, rfl⟩
  | @step p d u v hv hpos hneg hgap M ht ih =>
    have hv0 : v ≠ 0 := by intro h; subst v; simp at hv
    have hlocal := RotationWords.recentered_lift (0 : Fin n) u (by simpa using hd)
    obtain ⟨factors,hprod,hswaps,hlen⟩ := ih (exchange_lift hlocal v hv0)
    let base := Equiv.swap 0 v::factors
    let r := RotationWords.rotation u
    let result := base.map (MulAut.conj r)
    have hbase : base.prod=RotationWords.localTarget p 0 u := by
      simp only [base,List.prod_cons,hprod,← mul_assoc,Equiv.swap_mul_self,one_mul]
    refine ⟨result,?_,?_,?_⟩
    · change (base.map (MulAut.conj r)).prod=p
      rw [← map_list_prod,hbase,RotationWords.local_target_zero]
      change r*(r⁻¹*p*r)*r⁻¹=p
      group
    · intro q hq
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
      apply conjugate_swap
      rcases List.mem_cons.mp hz with he | he
      · subst z
        exact ⟨0,v,Ne.symm hv0,rfl⟩
      · exact hswaps z he
    · simp only [result,List.length_map,base,List.length_cons,hlen]

theorem sorting_transpositions {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ)) :
    ∃ factors : List (State n), factors.prod=p ∧ (∀ q ∈ factors, q.IsSwap) ∧
      (factors.length : ℤ)=(∑ i : Fin n, |d i|)-
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ) := by
  obtain ⟨M,ht,hcount⟩ := exists_sorting_trace hd hshort
  obtain ⟨factors,hprod,hswaps,hlen⟩ := ht.factorization hd
  exact ⟨factors,hprod,hswaps,by rw [hlen]; omega⟩

#print axioms sorting_transpositions
end LRX.ZeroGap
