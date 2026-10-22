import LRX.JoinedPeakArcWord
import LRX.ArcCycleSelection

namespace LRX.FiniteCuts
open RotationWords
variable {n : ℕ} [NeZero n]

noncomputable def peakArcServices (start finish : Fin n) (ss : List (ExactService n))
    (forward : Bool) : List (ExactService n) :=
  ss.filter (fun a => if forward then
    decide ((arcCoordinate true start a.service.port).val ≤ (arcCoordinate true start finish).val)
    else !decide ((arcCoordinate true start a.service.port).val ≤ (arcCoordinate true start finish).val))

theorem peak_arc_services_mem (start finish : Fin n) (ss : List (ExactService n))
    (forward : Bool) {a : ExactService n} (ha : a ∈ peakArcServices start finish ss forward) : a ∈ ss :=
  (List.mem_filter.mp ha).1

theorem peak_arc_services_range (start finish : Fin n) (hne : start ≠ finish)
    (ss : List (ExactService n)) (forward : Bool) (a : ExactService n)
    (ha : a ∈ peakArcServices start finish ss forward) :
    (arcCoordinate forward start a.service.port).val ≤ (arcCoordinate forward start finish).val := by
  have hh := (List.mem_filter.mp ha).2
  cases forward
  · apply arc_not_forward_is_reverse start finish a.service.port hne
    simpa using hh
  · simpa using hh

theorem peak_arc_services_savings (start finish : Fin n) (ss : List (ExactService n))
    (saving : ExactService n → ℤ) :
    ((peakArcServices start finish ss true).map saving).sum+
      ((peakArcServices start finish ss false).map saving).sum=(ss.map saving).sum := by
  induction ss with
  | nil => simp [peakArcServices]
  | cons a rest ih =>
    by_cases h : (arcCoordinate true start a.service.port).val ≤ (arcCoordinate true start finish).val
    · simp only [peakArcServices,List.filter_cons,ite_true,Bool.false_eq_true,ite_false,
        h,decide_true,Bool.not_true,List.map_cons,List.sum_cons] at ih ⊢
      omega
    · simp only [peakArcServices,List.filter_cons,ite_true,Bool.false_eq_true,ite_false,
        h,decide_false,Bool.not_false,List.map_cons,List.sum_cons] at ih ⊢
      omega

theorem peak_arc_services_disjoint (start finish : Fin n) (ss : List (ExactService n))
    (hdis : ss.Pairwise (fun a b => a.service.target.Disjoint b.service.target)) (forward : Bool) :
    (peakArcServices start finish ss forward).Pairwise (fun a b => a.service.target.Disjoint b.service.target) :=
  hdis.filter _

theorem peak_arc_services_canonical (start finish : Fin n) (ss : List (ExactService n))
    (hc : CanonicalFamily ss) (forward : Bool) : CanonicalFamily (peakArcServices start finish ss forward) :=
  fun a ha => hc a (peak_arc_services_mem start finish ss forward ha)

#print axioms peak_arc_services_savings
#print axioms peak_arc_services_range
end LRX.FiniteCuts
