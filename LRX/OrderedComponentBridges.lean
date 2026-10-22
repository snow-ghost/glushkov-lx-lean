import LRX.FiniteComponentRoots

namespace LRX.FiniteCuts
variable {n k : ℕ} [NeZero n]

noncomputable def componentOrder (p : State n) (hcard : (componentRoots p).card=k+1) :
    Fin (k+1) ↪o Fin n := (componentRoots p).orderEmbOfFin hcard

theorem component_order_mem (p : State n) (hcard : (componentRoots p).card=k+1) (i : Fin (k+1)) :
    componentOrder p hcard i ∈ componentRoots p := Finset.orderEmbOfFin_mem _ _ _

theorem component_order_surjective (p : State n) (hcard : (componentRoots p).card=k+1)
    (a : Fin n) (ha : a ∈ componentRoots p) : ∃ i, componentOrder p hcard i=a := by
  classical
  have he := Finset.image_orderEmbOfFin_univ (componentRoots p) hcard
  have hi : a ∈ Finset.univ.image (componentOrder p hcard) := by
    change a ∈ Finset.univ.image ((componentRoots p).orderEmbOfFin hcard)
    rw [he]
    exact ha
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hi
  exact ⟨i,hi⟩

theorem component_root_moved (p : State n) (a : Fin n) (ha : a ∈ componentRoots p) : p.symm a ≠ a := by
  classical
  exact (mem_support_inverse p a).mp (Finset.mem_filter.mp ha).1

noncomputable def bridgeEndpoints (p : State n) (hcard : (componentRoots p).card=k+1)
    (i : Fin k) : Fin n × Fin n :=
  (componentRight p (componentOrder p hcard i.castSucc),
   componentLeft p (componentOrder p hcard i.succ))

def ValidBridge (p : State n) (uv : Fin n × Fin n) : Prop :=
  uv.1.val < uv.2.val ∧ (p.symm uv.1).val < uv.1.val ∧ uv.2.val < (p.symm uv.2).val ∧
  ∀ x : Fin n, uv.1.val < x.val → x.val < uv.2.val → p x=x

theorem ordered_component_bridge_valid (p : State n) (hcard : (componentRoots p).card=k+1)
    (i : Fin k) : ValidBridge p (bridgeEndpoints p hcard i) := by
  let e := componentOrder p hcard
  have hA := component_order_mem p hcard i.castSucc
  have hB := component_order_mem p hcard i.succ
  have hAB : (e i.castSucc).val < (e i.succ).val := e.strictMono (by simp [Fin.lt_def])
  have horder := ordered_component_roots p hA hB hAB
  have hdata := component_extreme_bridge_data p
    ⟨e i.castSucc,component_root_moved p _ hA⟩ ⟨e i.succ,component_root_moved p _ hB⟩ horder
  refine ⟨horder,hdata.2.2.1,hdata.2.2.2,?_⟩
  apply consecutive_component_gap_fixed p (e i.castSucc) (e i.succ) hA hB
  intro c hc hbetween
  obtain ⟨j,hj⟩ := component_order_surjective p hcard c hc
  change e j=c at hj
  rw [← hj] at hbetween
  have hleft : i.castSucc < j := e.strictMono.lt_iff_lt.mp hbetween.1
  have hright : j < i.succ := e.strictMono.lt_iff_lt.mp hbetween.2
  change i.val < j.val at hleft
  change j.val < i.val+1 at hright
  omega

/-- Distinct consecutive-component bridges have disjoint, strictly ordered
endpoints; a nontrivial intervening component separates them. -/
theorem ordered_component_bridges_separated (p : State n) (hcard : (componentRoots p).card=k+1)
    (i j : Fin k) (hij : i.val < j.val) :
    (bridgeEndpoints p hcard i).2.val < (bridgeEndpoints p hcard j).1.val := by
  let e := componentOrder p hcard
  have hi := component_order_mem p hcard i.succ
  have hj := component_order_mem p hcard j.castSucc
  have hwidth := component_nontrivial_width p (e i.succ) (component_root_moved p _ hi)
  change (componentLeft p (e i.succ)).val < (componentRight p (e j.castSucc)).val
  by_cases he : i.succ=j.castSucc
  · simpa only [he] using hwidth
  · have hne : i.val+1 ≠ j.val := fun h => he (Fin.ext h)
    have hidx : i.succ < j.castSucc := by change i.val+1 < j.val; omega
    have horder := ordered_component_roots p hi hj (e.strictMono hidx)
    change (componentRight p (e i.succ)).val < (componentLeft p (e j.castSucc)).val at horder
    have hb := component_left_bound p (e j.castSucc) (componentRight p (e j.castSucc))
      (component_right_path p (e j.castSucc))
    omega

#print axioms ordered_component_bridge_valid
#print axioms ordered_component_bridges_separated
end LRX.FiniteCuts
