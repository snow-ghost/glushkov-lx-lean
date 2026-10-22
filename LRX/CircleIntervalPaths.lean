import LRX.CycleFootprint

/-! Integer intervals project to connected paths on the physical circle. -/
namespace LRX.CycleFootprint
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

abbrev InsidePath (E : Finset (Fin n)) := Relation.ReflTransGen (FootprintGeometry.Inside E Adjacent)

theorem inside_path_symm (E : Finset (Fin n)) {x y : Fin n} (h : InsidePath E x y) : InsidePath E y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hpath he ih =>
    have hr : FootprintGeometry.Inside E Adjacent _ _ := ⟨he.2.1,he.1,adjacent_symm he.2.2⟩
    exact (Relation.ReflTransGen.single hr).trans ih

theorem interval_forward_path (E : Finset (Fin n)) (a b : ℤ) (hab : a ≤ b)
    (hmem : ∀ z : ℤ, a ≤ z → z ≤ b → (z : Fin n) ∈ E) :
    InsidePath E (a : Fin n) (b : Fin n) := by
  have hpath : ∀ k : ℕ, a+(k : ℤ) ≤ b → InsidePath E (a : Fin n) ((a+(k : ℤ) : ℤ) : Fin n) := by
    intro k
    induction k with
    | zero => intro _; simpa using (Relation.ReflTransGen.refl : InsidePath E (a : Fin n) (a : Fin n))
    | succ k ih =>
      intro hk
      have hp := ih (by omega)
      apply hp.tail
      refine ⟨hmem _ (by omega) (by omega),hmem _ (by omega) hk,Or.inl ?_⟩
      push_cast
      ring
  have he : a+(((b-a).toNat : ℕ) : ℤ)=b := by omega
  simpa only [he] using hpath (b-a).toNat (by omega)

theorem segment_path (E : Finset (Fin n)) (a b x : ℤ)
    (hx : min a b ≤ x ∧ x ≤ max a b)
    (hmem : ∀ z : ℤ, min a b ≤ z → z ≤ max a b → (z : Fin n) ∈ E) :
    InsidePath E (a : Fin n) (x : Fin n) := by
  by_cases hab : a ≤ b
  · apply interval_forward_path E a x (by omega)
    intro z hz hz'
    exact hmem z (by omega) (by omega)
  · apply inside_path_symm E
    apply interval_forward_path E x a (by omega)
    intro z hz hz'
    exact hmem z (by omega) (by omega)

#print axioms segment_path
end LRX.CycleFootprint
