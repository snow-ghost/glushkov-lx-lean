import LRX.ReflectedLift

/-! Reflection sends the right port of the reflected root to the original left
port and preserves its actual load and both paid cursor distances. -/
namespace LRX.WordReflection
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem floor_reflection {N : ℤ} (hN : 0 < N) (x : ℤ) :
    (x-1)/N=-((-x)/N)-1 := by
  have hdiv := Int.ediv_mul_add_emod (-x) N
  have hr0 := Int.emod_nonneg (-x) (ne_of_gt hN)
  have hr1 := Int.emod_lt_of_pos (-x) hN
  apply PeriodicBuffer.quotient_eq_of_bounds hN <;> nlinarith

theorem edge_passages_reflection {N : ℤ} (hN : 0 < N) (a b : ℤ) :
    PeriodicBuffer.edgePassages N (1-a) (1-b)=PeriodicBuffer.edgePassages N a b := by
  simp only [PeriodicBuffer.edgePassages, show -(1-a)=a-1 by ring,
    show -(1-b)=b-1 by ring, floor_reflection hN]
  rw [show -((-b)/N)-1-(-((-a)/N)-1)=-((-b)/N-(-a)/N) by ring, abs_neg]

theorem port_load_reflected (d : Fin n → ℤ) (r : Fin n) :
    portLoad (reflectedDisplacement d) (reflection r)=portLoad d (r-1) := by
  have hn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [port_load_original, port_load_original]
  rw [← Equiv.sum_comp reflection (fun i : Fin n => PeriodicBuffer.edgePassages (n : ℤ)
    ((i : ℤ)-(reflection r : ℤ))
    ((i : ℤ)-(reflection r : ℤ)+reflectedDisplacement d i))]
  apply Finset.sum_congr rfl
  intro i _
  simp only [reflectedDisplacement, reflection_twice]
  let x : ℤ := (i : ℤ)-((r-1 : Fin n) : ℤ)
  have hm : Int.ModEq (n : ℤ) ((reflection i : ℤ)-(reflection r : ℤ)) (1-x) := by
    apply (LiftedModel.cast_eq_iff_modEq _ _).mp
    simp only [x, Int.cast_sub, Int.cast_one, Int.cast_natCast, Fin.cast_val_eq_self,
      reflection_apply]
    ring
  rw [edge_passages_modEq (ne_of_gt hn) hm (-d i)]
  change PeriodicBuffer.edgePassages (n : ℤ) (1-x) ((1-x)+(-d i))=
    PeriodicBuffer.edgePassages (n : ℤ) x (x+d i)
  rw [show (1-x)+(-d i)=1-(x+d i) by ring, edge_passages_reflection hn]

theorem port_distance_neg (a : Fin n) :
    min (-a).val (n-(-a).val)=min a.val (n-a.val) := by
  rw [Fin.val_neg]
  by_cases h : a=0
  · subst a; simp
  · rw [ite_eq_right h]
    have ha := a.isLt
    omega

#print axioms port_load_reflected
#print axioms port_distance_neg
end LRX.WordReflection
