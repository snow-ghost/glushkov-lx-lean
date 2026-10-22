import LRX.ReversalPairServiceFamily
import LRX.WindowComposition
import LRX.ReflectedExactService

namespace LRX.FiniteCuts
open scoped BigOperators Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem pair_right_exact_service (hn : 2 ≤ n) (a b : Fin n) (hab : a.val < b.val) :
    ∃ s : ExactService n, s.service.port=b-1 ∧ s.service.target=Equiv.swap a b ∧
      s.displacement=displacement (Equiv.swap a b) ∧
      (BufferProgram.rotations s.service.word : ℤ)=2*((b : ℤ)-(a : ℤ))-2 := by
  have hne : a ≠ b := by intro h; subst b; omega
  have hb0 : b ≠ 0 := by intro h; have := congrArg Fin.val h; simp only [Fin.val_zero] at this; omega
  have hd : AffineLift.IsLift (Equiv.swap a b) 0 (displacement (Equiv.swap a b)) := by
    simpa using canonical_lift (Equiv.swap a b)
  have hroot : displacement (Equiv.swap a b) b ≠ 0 := by
    simp only [displacement,Equiv.swap_apply_right]; omega
  obtain ⟨s,hport,htarget,hdisp,hrot⟩ := WordReflection.single_cycle_exact_left_service hn
    (Equiv.Perm.isCycle_swap hne) hd (displacement_short _) b hroot
  have hv : (b-1 : Fin n).val+1=b.val := by rw [Fin.val_sub_one_of_ne_zero hb0]; omega
  rw [swap_displacement_mass a b hab,port_load_eq_twice_half,hv,
    swap_half_load_between a b hab b.val hab le_rfl] at hrot
  exact ⟨s,hport,htarget,hdisp,by simpa using hrot⟩
end LRX.FiniteCuts

namespace LRX.FiniteWindow
open scoped Fin.NatCast Fin.CommRing
open FiniteCuts RotationWords
variable {n b : ℕ}

theorem permutation_swap (W : Window n b) (a c : Fin b) :
    permutation W (Equiv.swap a c)=Equiv.swap (embed W a) (embed W c) := by
  apply Equiv.ext
  intro j
  by_cases hj : Contains W j
  · obtain ⟨i,rfl⟩ := (contains_iff W j).mp hj
    rw [permutation_embed]
    by_cases hia : i=a
    · subst i; simp
    · by_cases hic : i=c
      · subst i; simp
      · have hia' : embed W i ≠ embed W a := fun h => hia (embed_injective W h)
        have hic' : embed W i ≠ embed W c := fun h => hic (embed_injective W h)
        rw [Equiv.swap_apply_of_ne_of_ne hia hic,Equiv.swap_apply_of_ne_of_ne hia' hic']
  · have ha : j ≠ embed W a := fun h => hj (h ▸ contains_embed W a)
    have hc : j ≠ embed W c := fun h => hj (h ▸ contains_embed W c)
    rw [permutation_outside W _ j hj,Equiv.swap_apply_of_ne_of_ne ha hc]

theorem window_pair_left_exact_service [NeZero n] (hn : 2 ≤ n) (W : Window n b)
    (a c : Fin b) (hac : a.val < c.val) :
    ∃ s : ExactService n, s.service.port=embed W a ∧
      s.service.target=permutation W (Equiv.swap a c) ∧
      s.displacement=displacement (permutation W (Equiv.swap a c)) ∧
      (BufferProgram.rotations s.service.word : ℤ)=2*((c : ℤ)-(a : ℤ))-2 := by
  have hlt : (embed W a).val < (embed W c).val := by dsimp [embed]; omega
  obtain ⟨s,hp,ht,hd,hr⟩ := pair_left_exact_service hn (embed W a) (embed W c) hlt
  rw [← permutation_swap] at ht hd
  refine ⟨s,hp,ht,hd,?_⟩
  simpa [embed] using hr

theorem window_pair_right_exact_service [NeZero n] (hn : 2 ≤ n) (W : Window n b)
    (a c : Fin b) (hac : a.val < c.val) :
    ∃ s : ExactService n, s.service.port=embed W c-1 ∧
      s.service.target=permutation W (Equiv.swap a c) ∧
      s.displacement=displacement (permutation W (Equiv.swap a c)) ∧
      (BufferProgram.rotations s.service.word : ℤ)=2*((c : ℤ)-(a : ℤ))-2 := by
  have hlt : (embed W a).val < (embed W c).val := by dsimp [embed]; omega
  obtain ⟨s,hp,ht,hd,hr⟩ := pair_right_exact_service hn (embed W a) (embed W c) hlt
  rw [← permutation_swap] at ht hd
  refine ⟨s,hp,ht,hd,?_⟩
  simpa [embed] using hr

#print axioms window_pair_left_exact_service
#print axioms window_pair_right_exact_service
end LRX.FiniteWindow
