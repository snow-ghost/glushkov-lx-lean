import LRX.FiniteShallowMatching

namespace LRX.FiniteCuts
variable {n : ℕ}

/-- The only noncrossing consequence needed for the equality classification. -/
def NoncrossingPairs (p : State n) : Prop :=
  ∀ a b c d : Fin n, a.val < b.val → b.val < c.val → c.val < d.val →
    p a=c → p b ≠ d

theorem involutive_of_cycles_are_swaps (p : State n)
    (hp : ∀ q ∈ p.cycleFactorsFinset, q.IsSwap) : Function.Involutive p := by
  classical
  intro i
  by_cases hi : p i=i
  · rw [hi,hi]
  · have hm : p.cycleOf i ∈ p.cycleFactorsFinset :=
      Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Equiv.Perm.mem_support.mpr hi)
    have hswap := hp _ hm
    have hinv : Function.Involutive (p.cycleOf i) := by
      obtain ⟨a,b,_,heq⟩ := hswap
      rw [heq]
      exact Equiv.swap_apply_self a b
    have h := hinv i
    rwa [Equiv.Perm.cycleOf_apply_self,Equiv.Perm.cycleOf_apply_apply_self] at h

/-- A pair's interior is closed: an escaping partner would alternate with the pair. -/
theorem noncrossing_pair_interior (p : State n) (hinv : Function.Involutive p)
    (hnc : NoncrossingPairs p) (a b x : Fin n)
    (hax : a.val < x.val) (hxb : x.val < b.val) (hab : p a=b) :
    a.val < (p x).val ∧ (p x).val < b.val := by
  have hpa : p b=a := by rw [← hab]; exact hinv a
  have hnea : p x ≠ a := by
    intro he
    have h := hinv x
    rw [he,hab] at h
    have := congrArg Fin.val h
    omega
  have hneb : p x ≠ b := by
    intro he
    have h := p.injective (he.trans hab.symm)
    have := congrArg Fin.val h
    omega
  have hneav : (p x).val ≠ a.val := fun h => hnea (Fin.ext h)
  have hnebv : (p x).val ≠ b.val := fun h => hneb (Fin.ext h)
  constructor
  · by_contra h
    have hlt : (p x).val < a.val := by omega
    exact hnc (p x) a x b hlt hax hxb (hinv x) hab
  · by_contra h
    have hlt : b.val < (p x).val := by omega
    exact hnc a x b (p x) hax hxb hlt hab rfl

/-- Every fixed-point-free pair interval contains a pair of consecutive positions. -/
theorem noncrossing_pair_contains_adjacent (p : State n) (hinv : Function.Involutive p)
    (hnc : NoncrossingPairs p) (a b : Fin n) (hablt : a.val < b.val) (hab : p a=b)
    (hfixed : ∀ i : Fin n, a.val ≤ i.val → i.val ≤ b.val → p i ≠ i) :
    ∃ x y : Fin n, a.val ≤ x.val ∧ y.val ≤ b.val ∧ x.val+1=y.val ∧ p x=y := by
  by_cases hunit : a.val+1=b.val
  · exact ⟨a,b,le_rfl,le_rfl,hunit,hab⟩
  · let x : Fin n := ⟨a.val+1,by have := b.isLt; omega⟩
    have hax : a.val < x.val := by dsimp [x]; omega
    have hxb : x.val < b.val := by dsimp [x]; omega
    have hx := noncrossing_pair_interior p hinv hnc a b x hax hxb hab
    have hne := hfixed x (by omega) (by omega)
    have hnev : (p x).val ≠ x.val := fun h => hne (Fin.ext h)
    by_cases hp : x.val < (p x).val
    · obtain ⟨u,v,hu,hv,huv,hp⟩ := noncrossing_pair_contains_adjacent p hinv hnc x (p x) hp rfl
        (fun i hi hj => hfixed i (by omega) (by omega))
      exact ⟨u,v,by omega,by omega,huv,hp⟩
    · have hpx : (p x).val < x.val := by omega
      obtain ⟨u,v,hu,hv,huv,hp⟩ := noncrossing_pair_contains_adjacent p hinv hnc (p x) x hpx (hinv x)
        (fun i hi hj => hfixed i (by omega) (by omega))
      exact ⟨u,v,by omega,by omega,huv,hp⟩
termination_by b.val-a.val
decreasing_by all_goals dsimp [x] at *; omega

#print axioms involutive_of_cycles_are_swaps
#print axioms noncrossing_pair_interior
#print axioms noncrossing_pair_contains_adjacent
end LRX.FiniteCuts
