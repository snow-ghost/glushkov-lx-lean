import GraphBridge
import Reachability
import LRX.LowerBoundNativeComplete
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Data.List.Permutation

namespace LRX.GraphBridge
open LRX.BlockExchange

instance vertex_nonempty (n : ℕ) : Nonempty (Vertex n) := ⟨root n⟩

instance vertex_finite (n : ℕ) : Finite (Vertex n) := by
  classical
  have hf := ((List.finRange n).permutations.toFinset).finite_toSet
  have heq : {xs : List (Fin n) | xs.Perm (List.finRange n)} =
      ↑((List.finRange n).permutations.toFinset) := by
    ext xs
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset, List.mem_permutations]
  change Finite {xs : List (Fin n) // xs.Perm (List.finRange n)}
  exact (heq ▸ hf : Set.Finite {xs : List (Fin n) | xs.Perm (List.finRange n)}).to_subtype

theorem connected {n : ℕ} (hn : 2 ≤ n) : (graph n).Connected := by
  refine ⟨?_⟩
  intro u v
  obtain ⟨w, hw⟩ := LRX.GraphReachability.exists_word_of_perm (u.property.trans v.property.symm)
  obtain ⟨p, _⟩ := word_walk hn w u
  have hv : runV w u = v := Subtype.ext hw
  rw [hv] at p
  exact ⟨p⟩

def target (n : ℕ) : Vertex n :=
  ⟨(List.finRange n).reverse.rotate (n-2),
    (List.rotate_perm _ _).trans (List.reverse_perm _)⟩

theorem walk_lower {n : ℕ} (hn : 4 ≤ n)
    (p : (graph n).Walk (root n) (target n)) : n*(n-1)/2 ≤ p.length := by
  obtain ⟨w, hw, hl⟩ := walk_word p
  have h := LRX.LowerBoundNativeComplete.native_lower hn w hw
  simpa only [hl] using h

theorem dist_lower {n : ℕ} (hn : 4 ≤ n) :
    n*(n-1)/2 ≤ (graph n).dist (root n) (target n) := by
  obtain ⟨p, hp⟩ := (connected (by omega : 2 ≤ n)).exists_walk_length_eq_dist (root n) (target n)
  simpa only [hp] using walk_lower hn p

theorem diam_lower {n : ℕ} (hn : 4 ≤ n) : n*(n-1)/2 ≤ (graph n).diam := by
  exact (dist_lower hn).trans ((graph n).dist_le_diam
    ((graph n).connected_iff_ediam_ne_top.mp (connected (by omega))))

#print axioms connected
#print axioms walk_lower
#print axioms dist_lower
#print axioms diam_lower
end LRX.GraphBridge
