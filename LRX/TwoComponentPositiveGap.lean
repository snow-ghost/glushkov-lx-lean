import LRX.MaximalCutManyRouting

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- In the two-component branch C7 already pays the actual positive-gap
price sum(gamma)+2B-1; the stronger historical reserve is unnecessary. -/
theorem two_component_positive_gap_reserve (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card=1) :
    let q := localTarget p 0 (componentLeft p root)
    ∃ hc : (componentRoots q).card=1+1,
      ((positiveSourceFamily q n).map FillingWindow.deficit).sum+
        2*(bridgeBudget (componentBridges q hc) : ℤ)-1 ≤
        ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ) := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let a := (singletonSuffixComponents q L).card
  let v := ∑ C ∈ nontrivialSuffixComponents q L, C.card
  have hreserve := large_component_numeric_reserve hn p hmaj hm root hlarge
  dsimp only at hreserve
  rw [ht] at hreserve
  norm_num only [Nat.cast_one,sub_self,mul_zero,zero_mul,add_zero] at hreserve
  obtain ⟨hc0,_⟩ := component_cut_bridge_parameters p root (by omega)
  have hc : (componentRoots q).card=1+1 := by simpa only [ht] using hc0
  have hB := component_bridge_isolated_budget q hc
  have hi := component_cut_isolated_count p root (by omega)
  change (isolatedVertices q).card=a at hi
  rw [hi] at hB
  refine ⟨hc,?_⟩
  have hv : 2 ≤ v := by
    have hh := nontrivial_suffix_size_sum q L
    change 2*(nontrivialSuffixComponents q L).card ≤ v at hh
    change (nontrivialSuffixComponents q L).card=1 at ht
    rw [ht] at hh
    omega
  have hprod : 2*(a : ℤ) ≤ (a : ℤ)*(v : ℤ) := by
    have hh := mul_nonneg (show (0 : ℤ) ≤ a by positivity)
      (show (0 : ℤ) ≤ (v : ℤ)-2 by omega)
    nlinarith
  have hB' : (bridgeBudget (componentBridges q hc) : ℤ) ≤ (a : ℤ)+1 := by exact_mod_cast hB
  have hpairs : (0 : ℤ) ≤ (a.choose 2 : ℤ) := by positivity
  change ((positiveSourceFamily q n).map FillingWindow.deficit).sum+1+
    (a : ℤ)*(v : ℤ)+(a.choose 2 : ℤ) ≤ _ at hreserve
  change ((positiveSourceFamily q n).map FillingWindow.deficit).sum+
    2*(bridgeBudget (componentBridges q hc) : ℤ)-1 ≤ _
  linarith

/-- All positive source-gap cursor pairs are paid at the component cut in
the two-component branch, with no packet-defect or shallow hypothesis. -/
theorem two_component_internal_gap_sharp_word (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card=1) :
    let r := componentLeft p root
    let q := localTarget p 0 r
    ∀ (u : {u // u ∈ positiveSourceGapStarts q n}) (start finish : Fin n),
      u.val.val ≤ (start-r).val → (start-r).val < FiniteGaps.next (sourcePackets q) u.val →
      u.val.val ≤ (finish-r).val → (finish-r).val < FiniteGaps.next (sourcePackets q) u.val →
      ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  dsimp only
  intro u start finish hsu hsv hfu hfv
  let r := componentLeft p root
  let q := localTarget p 0 r
  obtain ⟨hc,hreserve⟩ := two_component_positive_gap_reserve (by omega) p hmaj hm root hlarge ht
  obtain ⟨w,he,hl⟩ := selected_source_gap_word (by omega) q hc (by omega) u
    (start-r) (finish-r) hsu hsv hfu hfv
  have hqm : AffineLift.Majorized (displacement q.symm) := by
    rw [← component_cut_canonical_displacement]
    exact majorized_recenter hmaj _
  have hmass := majorized_canonical_energy q hqm
  have hI := inversion_number_zero_recenter p (componentLeft p root-1) (component_left_port_zero p root)
  rw [sub_add_cancel] at hI
  have hchoose := choose_two_half_identity n
  have hlen : (w.length : ℤ) ≤ (n.choose 2 : ℤ) := by
    change inversionNumber q=inversionNumber p at hI
    rw [hI] at hl
    linarith
  exact ⟨w,he.trans (shifted_word_target p r start finish),by exact_mod_cast hlen⟩

#print axioms two_component_positive_gap_reserve
#print axioms two_component_internal_gap_sharp_word
end LRX.FiniteCuts
