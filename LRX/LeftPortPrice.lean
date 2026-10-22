import LRX.ReflectedPortLoad

/-! Paid service at the left port of a chosen root, obtained by reflection with
all original statistics and external movement costs preserved. -/
namespace LRX.WordReflection
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem left_port_price (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (c r : Fin n) (hd : AffineLift.IsLift p (c : ℤ) d)
    (hshort : ∀ i, |d i| < (n : ℤ)) (hroot : d r ≠ 0)
    (hreach : ∀ i : Fin n, localDisplacement (reflectedDisplacement d) (reflection r) i ≠ 0 →
      Relation.ReflTransGen (BufferProgram.ServiceEdge
        (localTarget (reflectedTarget p) (-c) (reflection r))
        (localDisplacement (reflectedDisplacement d) (reflection r))) 0 i) :
    ∃ w : List Letter, eval w=p ∧
      BufferProgram.exchanges w=LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) ∧
      (w.length : ℤ)=
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d (r-1)+
        (min (r-1).val (n-(r-1).val) : ℕ)+
        (min (c-(r-1)).val (n-(c-(r-1)).val) : ℕ) := by
  have hs (i : Fin n) : |reflectedDisplacement d i| < (n : ℤ) := by
    simpa only [reflectedDisplacement, abs_neg] using hshort (reflection i)
  have hr : reflectedDisplacement d (reflection r) ≠ 0 := by
    simpa only [reflectedDisplacement, reflection_twice, neg_ne_zero] using hroot
  obtain ⟨w, he, hx, hp⟩ := paid_port_price hn (-c) (reflection r)
    (reflected_lift c hd) hs hr hreach
  rw [inversion_count_reflected c hd] at hx hp
  rw [reflected_mass, ← port_load_original, port_load_reflected] at hp
  have hport : reflection r=-(r-1) := by simp only [reflection_apply]; ring
  have hend : -c-reflection r=-(c-(r-1)) := by simp only [reflection_apply]; ring
  simp only [hend] at hp
  simp only [hport, port_distance_neg] at hp
  refine ⟨mirror w, ?_, ?_, ?_⟩
  · rw [mirror_eval, he]
    simp only [reflectedTarget, mul_assoc, ← mul_assoc (reflection : State n) reflection,
      reflection_square, one_mul, mul_one]
  · rw [mirror_exchanges]; exact hx
  · rw [mirror_length]; exact hp

#print axioms left_port_price
end LRX.WordReflection
