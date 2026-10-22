import LRX.ShallowSelectedPhysicalBound

namespace LRX.ContractionBlocks
variable {r : ℕ}

theorem ordered_cut_neighbor_unique (f : Fin r → ℕ) (hf : StrictMono f)
    (gap : ℕ) (a b x y : Fin r)
    (hab : a.val+1=b.val) (hxy : x.val+1=y.val)
    (ha : f a ≤ gap) (hb : gap < f b) (hx : f x ≤ gap) (hy : gap < f y) : a=x ∧ b=y := by
  have hax : a.val < x.val → f b ≤ f x := by
    intro h
    apply hf.monotone
    change b.val ≤ x.val
    omega
  have hxa : x.val < a.val → f y ≤ f a := by
    intro h
    apply hf.monotone
    change y.val ≤ a.val
    omega
  have he : a.val=x.val := by omega
  exact ⟨Fin.ext he,Fin.ext (by omega)⟩

theorem unit_cut_neighbor_unique (f : Fin r → ℕ) (hf : StrictMono f)
    (gap : ℕ) (a b x y : Fin r)
    (hab : |(b : ℤ)-(a : ℤ)|=1) (hxy : |(y : ℤ)-(x : ℤ)|=1)
    (habcut : ¬(f a ≤ gap ↔ f b ≤ gap))
    (hxycut : ¬(f x ≤ gap ↔ f y ≤ gap)) :
    (x=a ∧ y=b) ∨ (x=b ∧ y=a) := by
  have hab' : a.val+1=b.val ∨ b.val+1=a.val := by
    simp only [abs_eq_max_neg] at hab
    omega
  have hxy' : x.val+1=y.val ∨ y.val+1=x.val := by
    simp only [abs_eq_max_neg] at hxy
    omega
  rcases hab' with hab' | hab' <;> rcases hxy' with hxy' | hxy'
  · have hf1 : f a < f b := hf (by change a.val < b.val; omega)
    have hf2 : f x < f y := hf (by change x.val < y.val; omega)
    obtain ⟨h1,h2⟩ := ordered_cut_neighbor_unique f hf gap a b x y hab' hxy'
      (by omega) (by omega) (by omega) (by omega)
    exact Or.inl ⟨h1.symm,h2.symm⟩
  · have hf1 : f a < f b := hf (by change a.val < b.val; omega)
    have hf2 : f y < f x := hf (by change y.val < x.val; omega)
    obtain ⟨h1,h2⟩ := ordered_cut_neighbor_unique f hf gap a b y x hab' hxy'
      (by omega) (by omega) (by omega) (by omega)
    exact Or.inr ⟨h2.symm,h1.symm⟩
  · have hf1 : f b < f a := hf (by change b.val < a.val; omega)
    have hf2 : f x < f y := hf (by change x.val < y.val; omega)
    obtain ⟨h1,h2⟩ := ordered_cut_neighbor_unique f hf gap b a x y hab' hxy'
      (by omega) (by omega) (by omega) (by omega)
    exact Or.inr ⟨h1.symm,h2.symm⟩
  · have hf1 : f b < f a := hf (by change b.val < a.val; omega)
    have hf2 : f y < f x := hf (by change y.val < x.val; omega)
    obtain ⟨h1,h2⟩ := ordered_cut_neighbor_unique f hf gap b a y x hab' hxy'
      (by omega) (by omega) (by omega) (by omega)
    exact Or.inl ⟨h2.symm,h1.symm⟩

#print axioms unit_cut_neighbor_unique
end LRX.ContractionBlocks
