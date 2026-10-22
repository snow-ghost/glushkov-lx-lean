import LRX.PacketExchangeReserve
import LRX.ConnectedLoadWord

/-! A cursor already at a packet vertex can execute its closed service
within the sharp budget. This also covers zero-width packet gaps. -/
namespace LRX.FiniteGaps
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem base_word_budget {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) :
    (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
      (∑ i : Fin n, |d i|) ≤ (n.choose 2 : ℤ) := by
  have hr := ZeroGap.exchange_reserve_nonneg hd hm
  have he := epsilon_nonneg hd hm
  have hbudget := quarter_budget (n := n) (NeZero.pos n)
  unfold exchangeReserve at hr
  unfold epsilon at he
  omega

theorem packet_vertex_sharp_word (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d)
    (r : Fin n) (hroot : d r ≠ 0) (hcover : PrunedLift.PacketCover p d r) :
    ∃ w : List Letter, eval w=(rotation r)⁻¹*p*rotation r ∧ w.length ≤ n.choose 2 := by
  have hshort (i : Fin n) : |d i| < (n : ℤ) := by
    have := FiniteWindow.majorized_short hd hm i
    have := abs_nonneg (d i)
    omega
  obtain ⟨w,he,hlen⟩ := CycleFootprint.packet_word hn hd hshort r hroot hcover r r
  have hb := base_word_budget hd hm
  have hl := port_load_nonneg d r
  simp only [sub_self,Fin.val_zero,Nat.sub_zero,min_eq_left (Nat.zero_le _),
    Nat.cast_zero,add_zero] at hlen
  have hlen' : (w.length : ℤ) ≤ (n.choose 2 : ℤ) := by omega
  exact ⟨w,he,by exact_mod_cast hlen'⟩

#print axioms base_word_budget
#print axioms packet_vertex_sharp_word
end LRX.FiniteGaps
