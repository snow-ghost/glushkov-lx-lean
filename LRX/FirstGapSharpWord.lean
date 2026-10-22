import LRX.InternalGapPayment
import LRX.QuadraticGapWord

/-! A sharp word for the first nonempty internal packet gap. The remaining
exchange-reserve inequality is an explicit hypothesis. -/
namespace LRX.FiniteGaps
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

noncomputable def exchangeReserve (d : Fin n → ℤ) : ℤ :=
  (n : ℤ)^2/4-(n/2 : ℕ)-(LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)

theorem quarter_budget (hn : 1 ≤ n) : 2*((n : ℤ)^2/4)-(n/2 : ℕ)=(n.choose 2 : ℤ) := by
  have hf := floor_square_identity n
  have hn' : (n : ℤ)=2*(n/2 : ℕ)+(n%2 : ℕ) := by omega
  have hp : (n : ℤ)*(n-1)=4*((n : ℤ)^2/4)-2*(n/2 : ℕ) := by nlinarith
  rw [Nat.choose_two_right,Int.natCast_ediv (n*(n-1)) 2]
  simp only [Nat.cast_mul,Nat.cast_sub hn,Nat.cast_one,Nat.cast_ofNat]
  rw [hp]
  omega

theorem first_internal_gap_sharp_word (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (hinternal : Internal p d 0)
    (hreserve : (PrunedLift.coreHalfSize p d : ℤ)-1 ≤ exchangeReserve d)
    (start finish : Fin n) (hxy : start.val ≤ finish.val)
    (hy : finish.val ≤ size (PrunedLift.core p d 0) 0) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  classical
  let S := PrunedLift.core p d 0
  let W := window S 0
  have hshort : |d 0| < (n : ℤ) := by
    have := FiniteWindow.majorized_short hd hm 0
    have := abs_nonneg (d 0)
    omega
  have hmov : p⁻¹ 0 ≠ 0 := fun hf => hroot (BufferProgram.fixed_short_displacement hd 0 hshort hf)
  have hpartner : p.symm 0 ∈ S := (PrunedLift.mem_core p d 0 _).mpr
    (PrunedLift.in_core_same_cycle p d 0 ⟨Relation.ReflTransGen.refl,Relation.ReflTransGen.refl⟩
      (Equiv.Perm.SameCycle.refl _ _).apply_right)
  have hpartnerpos : 0 < (p.symm 0).val := by
    have hne : (p.symm 0).val ≠ 0 := fun h => hmov (Fin.ext h)
    omega
  have hnext : next S 0 < n := by
    have h := next_le_member S 0 (p.symm 0) hpartner (by simpa using hpartnerpos)
    have h' := (p.symm 0).isLt
    omega
  let r : Fin n := ⟨next S 0,hnext⟩
  have hr : PrunedLift.InCore p d 0 r := by
    obtain ⟨j,hj,he⟩ := next_is_member S 0 hnext
    have hjr : j=r := Fin.ext he
    exact (PrunedLift.mem_core p d 0 r).mp (hjr ▸ hj)
  have hoff : W.offset=1 := by simp [W,window]
  have hedge : W.offset+size S 0=r.val := by
    have h := lt_next S 0
    dsimp [W,window,size,r]
    simp only [Fin.val_zero] at h ⊢
    omega
  have hgap : ∀ i, FiniteWindow.Contains W i → ¬PrunedLift.InCore p d 0 i := by
    intro i hi hc
    exact gap_avoids_marks S 0 i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
      ((PrunedLift.mem_core p d 0 i).mpr hc)
  have hvisit : size S 0=0 ∨ ∃ i x : Fin n, PrunedLift.InCore p d 0 i ∧ FiniteWindow.Contains W x ∧
      BufferProgram.Touches (n : ℤ) (i : ℤ) (d i) (x : ℤ) := by
    obtain ⟨i,x,hi,hx,ht⟩ := hinternal
    exact Or.inr ⟨i,x,(PrunedLift.mem_core p d 0 i).mp hi,(Finset.mem_filter.mp hx).2,ht⟩
  obtain ⟨K,hK,w,he,hlen⟩ := FiniteWindow.internal_gap_quadratic_word hn hd hm hroot hcover W hoff r hedge hr
    hgap hvisit start finish hxy hy
  have hK' : 2*gapEnergy p d 0+(K : ℤ)^2 ≤ (size S 0 : ℤ)^2 := hK
  have ha : (0 : Fin n) ∈ internalStarts p d := Finset.mem_filter.mpr ⟨core_zero p d,hinternal⟩
  have hpay := internal_gap_payment hd hm hcover hmov 0 ha K hK' (exchangeReserve d) hreserve
  have hbudget := quarter_budget (n := n) (by omega)
  unfold exchangeReserve epsilon at hpay
  have hlen' : (w.length : ℤ) ≤ (n.choose 2 : ℤ) := by nlinarith
  exact ⟨w,he,by exact_mod_cast hlen'⟩

#print axioms first_internal_gap_sharp_word
end LRX.FiniteGaps
