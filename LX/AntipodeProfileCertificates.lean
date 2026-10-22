import LX.EvenSingleRaise
import LX.OddSingleRaise

namespace LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

def profile (e : Fin n → ℤ) : Option (Fin n) → Fin n → ℤ
  | none => e
  | some a => raiseAt e a

theorem profile_cast (e : Fin n → ℤ) (a : Option (Fin n)) (i : Fin n) :
    (profile e a i : Fin n)=(e i : Fin n) := by
  cases a with
  | none => rfl
  | some a => simp [profile,raiseAt]

theorem profile_lift {p : State n} (c : Fin n) (e : Fin n → ℤ) (a : Option (Fin n))
    (hl : ∀ i,i+(e i : Fin n)=p.symm i+c) (hb : ∑ i,profile e a i=0) :
    IsLift p (c : ℤ) (profile e a) := by
  refine ⟨hb,?_⟩
  intro i
  apply (LRX.LiftedModel.cast_eq_iff_modEq _ _).mp
  simpa only [Int.cast_add,Int.cast_natCast,Fin.cast_val_eq_self,profile_cast] using hl i

theorem perturbed_board_labels (m : ℕ) (C : ℤ) (ρ : State n) (i : Fin n) :
    i+(perturbedBoard m C ρ i : Fin n)=(C : Fin n)-ρ i := by
  unfold perturbedBoard
  rw [center_cast]
  simp only [Int.cast_sub,Int.cast_natCast,Fin.cast_val_eq_self]
  ring

/-- Exact lower-bound criterion after the height and centered-mass
reductions. Only balanced profiles require a deadline certificate. -/
theorem length_lower_iff_profile_certificates (hn : 2 ≤ n) (p : State n) (B : ℕ)
    (base : Fin n → Fin n → ℤ)
    (hl : ∀ c i,i+(base c i : Fin n)=p.symm i+c)
    (hc : ∀ (c : Fin n) (d : Fin n → ℤ) (g : List Letter),IsLift p (c : ℤ) d →
      ScanTrace d g → inversions d+paidRotations c g < B → ∃ a,d=profile (base c) a) :
    B ≤ length p ↔ ∀ (c : Fin n) (a : Option (Fin n)),
      (∑ i,profile (base c) a i)=0 → LowerDeadlineCertificate B c (profile (base c) a) := by
  constructor
  · intro hB c a hb
    by_contra hnot
    have hd := profile_lift c (base c) a (hl c) hb
    obtain ⟨w,hw,hlen⟩ := LX.failed_deadline_certificate_word hn p B c _ hd hnot
    have hle := length_le_word (n := n) w
    rw [hw] at hle
    omega
  · intro hcert
    obtain ⟨c,d,g,hd,_,hg,he,hlen⟩ := LX.exists_shortest_bounded_greedy_word hn p
    have hp := (LX.greedy_lift_price_realized hn p c.val d hd g hg).2
    simp only [Fin.cast_val_eq_self] at hp
    by_contra hnot
    have hcheap : inversions d+paidRotations c g < B := by omega
    obtain ⟨a,rfl⟩ := hc c d g hd hg hcheap
    have hbound := deadline_certificate_price hn B c _ hd.1 g hg (hcert c a hd.1)
    omega

end LX.CenteredLift

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift
variable {n : ℕ} [NeZero n]

theorem even_lower_iff_profiles (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m) :
    3*m^2-4*m+3 ≤ length (even : State n) ↔
      ∀ (c : Fin n) (a : Option (Fin n)),(∑ i,profile (evenBase m c) a i)=0 →
        LowerDeadlineCertificate (3*m^2-4*m+3) c (profile (evenBase m c) a) := by
  apply length_lower_iff_profile_certificates (by omega : 2 ≤ n) even _ (evenBase m)
  · intro c i
    have hh := perturbed_board_labels m ((c : ℤ)+1) (Equiv.swap (1 : Fin n) 2) i
    change i+(evenBase m c i : Fin n)=_
    rw [show (even : State n).symm i=1-(Equiv.swap (1 : Fin n) 2) i from rfl]
    change i+(perturbedBoard m ((c : ℤ)+1) (Equiv.swap (1 : Fin n) 2) i : Fin n)=_
    rw [hh]
    simp only [Int.cast_add,Int.cast_one,Int.cast_natCast,Fin.cast_val_eq_self]
    ring
  · intro c d g hd hg hu
    rcases even_unpaid_single_raise m hm hn hd hg hu with he | ⟨a,ha⟩
    · exact ⟨none,he⟩
    · exact ⟨some a,ha⟩

theorem odd_lower_iff_profiles (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) :
    3*m^2-m+1 ≤ length (odd m hm hn) ↔
      ∀ (c : Fin n) (a : Option (Fin n)),(∑ i,profile (oddBase m hm hn c) a i)=0 →
        LowerDeadlineCertificate (3*m^2-m+1) c (profile (oddBase m hm hn c) a) := by
  apply length_lower_iff_profile_certificates (by omega : 2 ≤ n) (odd m hm hn) _ (oddBase m hm hn)
  · intro c i
    have hh := perturbed_board_labels m ((c : ℤ)+1) (oddRank m hm hn) i
    change i+(oddBase m hm hn c i : Fin n)=_
    rw [show (odd m hm hn).symm i=1-(oddRank m hm hn) i from rfl]
    change i+(perturbedBoard m ((c : ℤ)+1) (oddRank m hm hn) i : Fin n)=_
    rw [hh]
    simp only [Int.cast_add,Int.cast_one,Int.cast_natCast,Fin.cast_val_eq_self]
    ring
  · intro c d g hd hg hu
    rcases odd_unpaid_single_raise m hm hn hd hg hu with he | ⟨a,ha⟩
    · exact ⟨none,he⟩
    · exact ⟨some a,ha⟩

#print axioms even_lower_iff_profiles
#print axioms odd_lower_iff_profiles
end LX.Antipode
