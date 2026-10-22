import Mathlib

namespace BalancedTwoBlockPorts

def lee (n x y : ℤ) : ℤ := min |x-y| (n-|x-y|)

theorem even_antipodes (H x y : ℤ) (hH : 1 ≤ H)
    (hx : 0 ≤ x) (hxn : x < 2*H) (hy : 0 ≤ y) (hyH : y < H) :
    lee (2*H) x y + lee (2*H) x (y+H) = H := by
  unfold lee
  simp only [abs_eq_max_neg]
  omega

theorem odd_one_two (H x y : ℤ) (hH : 1 ≤ H)
    (hx : 0 ≤ x) (hxn : x < 2*H+1) (hy : 0 ≤ y) (hyH : y < H) :
    lee (2*H+1) x y +
      min (lee (2*H+1) x (y+H)) (lee (2*H+1) x (y+H+1)) = H := by
  unfold lee
  simp only [abs_eq_max_neg]
  omega

theorem odd_two_one (H x y : ℤ) (hH : 1 ≤ H)
    (hx : 0 ≤ x) (hxn : x < 2*H+1) (hy : 0 ≤ y) (hyH : y < H) :
    min (lee (2*H+1) x y) (lee (2*H+1) x (y+1)) +
      lee (2*H+1) x (y+H+1) = H := by
  unfold lee
  simp only [abs_eq_max_neg]
  omega

theorem four_ports_cover (a b c f : ℤ) (ha : 2 ≤ a)
    (hb : b = a ∨ b = a+1)
    (hc : 0 ≤ c) (hcn : c < a+b) (hf : 0 ≤ f) (hfn : f < a+b) :
    let h := (a-2)/2
    let s := (b-2)/2
    lee (a+b) c h + lee (a+b) f (a+b-2-s) ≤ a ∨
    lee (a+b) c (a-2-h) + lee (a+b) f (a+s) ≤ a ∨
    lee (a+b) c (a+s) + lee (a+b) f (a-2-h) ≤ a ∨
    lee (a+b) c (a+b-2-s) + lee (a+b) f h ≤ a := by
  dsimp
  rcases hb with hb | hb
  · subst b
    have h1 := even_antipodes a c ((a-2)/2) (by omega) hc (by omega)
      (by omega) (by omega)
    have h2 := even_antipodes a f (a-2-(a-2)/2) (by omega) hf (by omega)
      (by omega) (by omega)
    have hn : a+a = 2*a := by ring
    have he : a+a-2-(a-2)/2 = (a-2-(a-2)/2)+a := by omega
    rw [he, hn]
    have hx : a+(a-2)/2 = (a-2)/2+a := by omega
    rw [hx]
    omega
  · subst b
    have heven : a % 2 = 0 ∨ a % 2 = 1 := by omega
    rcases heven with heven | hodd
    · have h1 := odd_one_two a c ((a-2)/2) (by omega) hc (by omega)
        (by omega) (by omega)
      have h2 := odd_one_two a f ((a-2)/2) (by omega) hf (by omega)
        (by omega) (by omega)
      have hn : a+(a+1) = 2*a+1 := by ring
      have hs : (a+1-2)/2 = (a-2)/2 := by omega
      have hl : a-2-(a-2)/2 = (a-2)/2 := by omega
      have hb0 : a+(a-2)/2 = (a-2)/2+a := by omega
      have hb1 : a+(a+1)-2-(a-2)/2 = (a-2)/2+a+1 := by omega
      rw [hs, hl, hb0, hb1, hn]
      omega
    · have h1 := odd_two_one a c ((a-2)/2) (by omega) hc (by omega)
        (by omega) (by omega)
      have h2 := odd_two_one a f ((a-2)/2) (by omega) hf (by omega)
        (by omega) (by omega)
      have hn : a+(a+1) = 2*a+1 := by ring
      have hl : a-2-(a-2)/2 = (a-2)/2+1 := by omega
      have hb0 : a+(a+1-2)/2 = (a-2)/2+a+1 := by omega
      have hb1 : a+(a+1)-2-(a+1-2)/2 = (a-2)/2+a+1 := by omega
      rw [hl, hb0, hb1, hn]
      omega

theorem boundary_pairs_disjoint (a b r i j : ℤ)
    (hbal : a = b ∨ a = b+1) (hr : 2 ≤ r)
    (_hi : 0 ≤ i) (hik : i ≤ a-r) (hj : 0 ≤ j) :
    r-1+i < b+r-1+j := by
  omega

theorem balanced_quadratic_identity (a b : ℤ) (hbal : a = b ∨ a = b+1) :
    2*a*(a-1)+2*b*(b-1)+2*b = (a+b)*(a+b-1) := by
  rcases hbal with h | h <;> subst a <;> ring

end BalancedTwoBlockPorts

#print axioms BalancedTwoBlockPorts.even_antipodes
#print axioms BalancedTwoBlockPorts.odd_one_two
#print axioms BalancedTwoBlockPorts.odd_two_one
#print axioms BalancedTwoBlockPorts.four_ports_cover
#print axioms BalancedTwoBlockPorts.boundary_pairs_disjoint
#print axioms BalancedTwoBlockPorts.balanced_quadratic_identity
