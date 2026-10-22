import LRX.TwoBoundaryWindowRoute

/-! The two boundaries of an invariant finite gap have equal ambient load.
Interior finite arrows cross neither boundary; external endpoints have the
same division quotient at both cuts. -/
namespace LRX.FiniteWindow
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n b : ℕ} [NeZero n]

omit [NeZero n] in
theorem inverse_outside (W : Window n b) (p : State n) (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i)) (i : Fin n)
    (hi : ¬Contains W i) : ¬Contains W (p.symm i) := by
  intro h
  obtain ⟨j,hj⟩ := (contains_iff W (p.symm i)).mp h
  have he : p.symm (embed W (filling.symm j))=p.symm i := by
    rw [hmatch,filling.apply_symm_apply,hj]
  have he' := p.symm.injective he
  apply hi
  rw [← he']
  exact contains_embed W _

theorem outside_cut_quotient (cut : ℕ) (hc : cut < n) (j : Fin n)
    (hj : j.val=0 ∨ cut < j.val) (z : ℤ) (hz : Int.ModEq (n : ℤ) (j : ℤ) z) :
    ((cut : ℤ)-z)/(n : ℤ)=(-z)/(n : ℤ) := by
  have hbase : ((cut : ℤ)-(j : ℤ))/(n : ℤ)=(-(j : ℤ))/(n : ℤ) := by
    rcases hj with hj | hj
    · have hj' : (j : ℤ)=0 := by exact_mod_cast hj
      rw [hj']
      simp only [sub_zero,neg_zero,Int.zero_ediv]
      exact Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast hc)
    · have hjn := j.isLt
      have h1 : ((cut : ℤ)-(j : ℤ))/(n : ℤ)= -1 :=
        Int.ediv_eq_neg_one_of_neg_of_le (by omega) (by omega)
      have h2 : (-(j : ℤ))/(n : ℤ)= -1 :=
        Int.ediv_eq_neg_one_of_neg_of_le (by omega) (by omega)
      rw [h1,h2]
  obtain ⟨k,hk⟩ := Int.modEq_iff_dvd.mp hz
  have he : z=(j : ℤ)+k*(n : ℤ) := by nlinarith [hk]
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have h1 : (cut : ℤ)-z=((cut : ℤ)-(j : ℤ))+(-k)*(n : ℤ) := by rw [he]; ring
  have h2 : -z=(-(j : ℤ))+(-k)*(n : ℤ) := by rw [he]; ring
  rw [h1,h2,Int.add_mul_ediv_right _ _ hn,Int.add_mul_ediv_right _ _ hn,hbase]

theorem gap_boundary_port_load {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (W : Window n b) (hoff : W.offset=1)
    (r : Fin n) (hedge : W.offset+b=r.val) (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i))
    (hfinite : ∀ i, d (embed W i)=FiniteCuts.displacement filling i) :
    portLoad d 0=portLoad d (r-1) := by
  have hr : r ≠ 0 := by intro h; rw [h,Fin.val_zero,hoff] at hedge; omega
  have hanchor : (r-1 : Fin n).val=b := by rw [Fin.val_sub_one_of_ne_zero hr]; omega
  have hcut : b < n := by have := r.isLt; omega
  have hout (i : Fin n) (hi : ¬Contains W i) : i.val=0 ∨ b < i.val := by
    unfold Contains at hi
    rw [hoff] at hi
    omega
  rw [port_load_original,port_load_original]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Fin.val_zero,Nat.cast_zero,sub_zero]
  by_cases hm : Contains W i
  · obtain ⟨j,rfl⟩ := (contains_iff W i).mp hm
    have he : (embed W j : ℤ)+d (embed W j)=(embed W (filling j) : ℤ) := by
      rw [hfinite]
      simp [embed,FiniteCuts.displacement]
    have he' : (embed W j : ℤ)-((r-1 : Fin n) : ℤ)+d (embed W j)=
        (embed W (filling j) : ℤ)-((r-1 : Fin n) : ℤ) := by linarith
    have hj0 (k : Fin b) : embed W k ≠ 0 := by
      intro h
      have hh := congrArg Fin.val h
      simp only [embed,Fin.val_zero] at hh
      omega
    have hjr (k : Fin b) : (embed W k).val < r.val := by dsimp [embed]; have := k.isLt; omega
    rw [he,he',PrunedLift.positive_endpoint_passages _ _ (hj0 j) (hj0 (filling j)),
      PrunedLift.left_incident_no_passages r _ _ hr (hjr j) (hjr (filling j))]
  · have hs := outside_cut_quotient b hcut i (hout i hm) (i : ℤ) (Int.ModEq.refl _)
    have ht : Int.ModEq (n : ℤ) (p.symm i : ℤ) ((i : ℤ)+d i) := by simpa using (hd.2 i).symm
    have he := outside_cut_quotient b hcut (p.symm i)
      (hout _ (inverse_outside W p filling hmatch i hm)) ((i : ℤ)+d i) ht
    have ha : ((r-1 : Fin n) : ℤ)=(b : ℤ) := by exact_mod_cast hanchor
    unfold PeriodicBuffer.edgePassages
    rw [ha]
    have h1 : -((i : ℤ)-(b : ℤ))=(b : ℤ)-(i : ℤ) := by ring
    have h2 : -((i : ℤ)-(b : ℤ)+d i)=(b : ℤ)-((i : ℤ)+d i) := by ring
    rw [h1,h2,hs,he]

#print axioms gap_boundary_port_load
end LRX.FiniteWindow
