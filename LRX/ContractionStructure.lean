import LRX.ContractionEnergy

namespace LRX.FiniteCuts
variable {n : ℕ}

theorem adjacent_complement_swap (a b : Fin (n+1))
    (hab : |(b : ℤ)-(a : ℤ)|=1) (i : Fin n) :
    a.succAbove i=Equiv.swap a b (b.succAbove i) := by
  have hab' := hab
  simp only [abs_eq_max_neg] at hab'
  by_cases hi : b.succAbove i=a
  · rw [hi,Equiv.swap_apply_left]
    apply Fin.ext
    have hv := congrArg Fin.val hi
    simp only [succAbove_value] at hv ⊢
    split_ifs at * <;> omega
  · rw [Equiv.swap_apply_of_ne_of_ne hi (b.succAbove_ne i)]
    apply Fin.ext
    have hv : (b.succAbove i).val ≠ a.val := fun h => hi (Fin.ext h)
    simp only [succAbove_value] at hv ⊢
    split_ifs at * <;> omega

theorem contract_extension (p : State (n+1)) (a : Fin (n+1))
    (hadj : |displacement p a|=1) :
    (contract p a).extendDomain (finSuccAboveEquiv a)=Equiv.swap a (p a)*p := by
  apply Equiv.ext
  intro j
  by_cases hj : j=a
  · subst j
    rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp)]
    simp [Equiv.Perm.mul_apply]
  · obtain ⟨i,hi⟩ := Fin.exists_succAbove_eq hj
    subst j
    have he := Equiv.Perm.extendDomain_apply_image (contract p a) (finSuccAboveEquiv a) i
    change ((contract p a).extendDomain (finSuccAboveEquiv a)) (a.succAbove i)=
      a.succAbove (contract p a i) at he
    rw [he,adjacent_complement_swap a (p a) hadj,contract_entry]
    rfl

theorem cycle_of_puncture_extension (q : State n) (a : Fin (n+1))
    (h : (q.extendDomain (finSuccAboveEquiv a)).IsCycle) : q.IsCycle := by
  classical
  obtain ⟨j,hj⟩ := h.nonempty_support
  rw [Equiv.Perm.support_extend_domain] at hj
  obtain ⟨i,hi,_⟩ := Finset.mem_map.mp hj
  have hx : q i ≠ i := Equiv.Perm.mem_support.mp hi
  refine ⟨i,hx,?_⟩
  intro k hk
  apply (Equiv.Perm.sameCycle_extendDomain (f := finSuccAboveEquiv a) (g := q) (x := i) (y := k)).mp
  apply h.sameCycle
  · rw [Equiv.Perm.extendDomain_apply_image]
    intro he
    exact hx ((finSuccAboveEquiv a).injective (Subtype.ext he))
  · rw [Equiv.Perm.extendDomain_apply_image]
    intro he
    exact hk ((finSuccAboveEquiv a).injective (Subtype.ext he))

theorem long_cycle_not_two_step {p : State (n+1)} (hp : p.IsCycle)
    (hc : 3 ≤ p.support.card) (a : Fin (n+1)) (ha : p a ≠ a) : p (p a) ≠ a := by
  intro h
  have he := hp.eq_swap_of_apply_apply_eq_self ha h
  have hcard : p.support.card=2 := by rw [he]; exact Equiv.Perm.card_support_swap (Ne.symm ha)
  omega

theorem contract_cycle {p : State (n+1)} (hp : p.IsCycle) (hc : 3 ≤ p.support.card)
    (a : Fin (n+1)) (hadj : |displacement p a|=1) : (contract p a).IsCycle := by
  have ha : p a ≠ a := by intro h; simp [displacement,h] at hadj
  apply cycle_of_puncture_extension _ a
  rw [contract_extension p a hadj]
  exact hp.swap_mul ha (long_cycle_not_two_step hp hc a ha)

theorem contract_cycle_support_card {p : State (n+1)} (hp : p.IsCycle) (hc : 3 ≤ p.support.card)
    (a : Fin (n+1)) (hadj : |displacement p a|=1) :
    (contract p a).support.card+1=p.support.card := by
  classical
  have ha : p a ≠ a := by intro h; simp [displacement,h] at hadj
  have hcard := Equiv.Perm.card_support_extend_domain (finSuccAboveEquiv a) (g := contract p a)
  rw [contract_extension p a hadj,
    Equiv.Perm.support_swap_mul_eq p a (long_cycle_not_two_step hp hc a ha),
    Finset.sdiff_singleton_eq_erase] at hcard
  have he := Finset.card_erase_add_one (Equiv.Perm.mem_support.mpr ha)
  omega

#print axioms contract_cycle
#print axioms contract_cycle_support_card
end LRX.FiniteCuts
