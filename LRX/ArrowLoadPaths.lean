import LRX.LoadedFootprint

/-! Lifted arrow intervals yield paths using only positive-load edges. -/
namespace LRX.CycleFootprint
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing

theorem passage_positive_of_interval {N a b : ℤ} (hN : 0 < N) (k : ℤ)
    (hlo : min a b ≤ k*N) (hhi : k*N+1 ≤ max a b) :
    0 < PeriodicBuffer.edgePassages N a b := by
  apply abs_pos.mpr
  by_cases hab : a ≤ b
  · have h1 : -k ≤ (-a)/N := (Int.le_ediv_iff_mul_le hN).mpr (by simp only [min_eq_left hab] at hlo; nlinarith)
    have h2 : (-b)/N < -k := (Int.ediv_lt_iff_lt_mul hN).mpr (by simp only [max_eq_right hab] at hhi; nlinarith)
    omega
  · have h1 : -k ≤ (-b)/N := (Int.le_ediv_iff_mul_le hN).mpr (by simp only [min_eq_right (le_of_not_ge hab)] at hlo; nlinarith)
    have h2 : (-a)/N < -k := (Int.ediv_lt_iff_lt_mul hN).mpr (by simp only [max_eq_left (le_of_not_ge hab)] at hhi; nlinarith)
    omega

variable {n : ℕ} [NeZero n]

abbrev LoadPath (d : Fin n → ℤ) := Relation.ReflTransGen (LoadedStep d)

theorem load_path_symm (d : Fin n → ℤ) {x y : Fin n} (h : LoadPath d x y) : LoadPath d y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hp he ih =>
    have hr : LoadedStep d _ _ := he.symm
    exact (Relation.ReflTransGen.single hr).trans ih

theorem arrow_edge_positive (d : Fin n → ℤ) (i : Fin n) (z : ℤ)
    (hlo : min (i : ℤ) ((i : ℤ)+d i) ≤ z)
    (hhi : z+1 ≤ max (i : ℤ) ((i : ℤ)+d i)) :
    0 < RotationWords.portLoad d (z : Fin n) := by
  have hmod : Int.ModEq (n : ℤ) ((z : Fin n) : ℤ) z := by
    apply (LiftedModel.cast_eq_iff_modEq _ _).mp
    simp only [Int.cast_natCast,Fin.cast_val_eq_self]
  obtain ⟨k,hk⟩ := Int.modEq_iff_dvd.mp hmod
  have hz : z=((z : Fin n) : ℤ)+k*(n : ℤ) := by nlinarith
  have hp := passage_positive_of_interval (show (0 : ℤ) < n by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)) k
    (a := (i : ℤ)-((z : Fin n) : ℤ)) (b := (i : ℤ)-((z : Fin n) : ℤ)+d i)
    (by omega) (by omega)
  rw [RotationWords.port_load_original]
  apply lt_of_lt_of_le hp
  exact Finset.single_le_sum (f := fun j : Fin n => PeriodicBuffer.edgePassages (n : ℤ)
    ((j : ℤ)-((z : Fin n) : ℤ)) ((j : ℤ)-((z : Fin n) : ℤ)+d j))
    (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

theorem integer_load_path (d : Fin n → ℤ) (a b : ℤ) (hab : a ≤ b)
    (hpos : ∀ z : ℤ, a ≤ z → z < b → 0 < RotationWords.portLoad d (z : Fin n)) :
    LoadPath d (a : Fin n) (b : Fin n) := by
  have hiter : ∀ k : ℕ, a+(k : ℤ) ≤ b → LoadPath d (a : Fin n) ((a+(k : ℤ) : ℤ) : Fin n) := by
    intro k
    induction k with
    | zero => intro _; simpa using (Relation.ReflTransGen.refl : LoadPath d (a : Fin n) (a : Fin n))
    | succ k ih =>
      intro hk
      apply (ih (by omega)).tail
      refine Or.inl ⟨?_,hpos _ (by omega) (by omega)⟩
      push_cast
      ring
  have he : a+(((b-a).toNat : ℕ) : ℤ)=b := by omega
  simpa only [he] using hiter (b-a).toNat (by omega)

theorem arrow_load_path (d : Fin n → ℤ) (i : Fin n) (z : ℤ)
    (hz : min (i : ℤ) ((i : ℤ)+d i) ≤ z ∧ z ≤ max (i : ℤ) ((i : ℤ)+d i)) :
    LoadPath d i (z : Fin n) := by
  have hcast : (((i : ℤ) : ℤ) : Fin n)=i := by simp
  by_cases hi : (i : ℤ) ≤ z
  · rw [← hcast]
    exact integer_load_path d (i : ℤ) z hi (fun x hx hx' => arrow_edge_positive d i x (by omega) (by omega))
  · apply load_path_symm
    rw [← hcast]
    exact integer_load_path d z (i : ℤ) (by omega) (fun x hx hx' => arrow_edge_positive d i x (by omega) (by omega))

#print axioms arrow_edge_positive
#print axioms arrow_load_path
end LRX.CycleFootprint
