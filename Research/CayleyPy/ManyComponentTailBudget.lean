import Mathlib

/-! Phase60: general finite component bridges and short-tail certificates.
The component and permutation geometry is proved in the accompanying note. -/
namespace CayleyPy.ManyComponentTailBudget

theorem signed_tail_reserve (m p k x r b Delta epsilon : ℤ)
    (hk : k=m-x) (he : epsilon=m*(m+p)-Delta)
    (hprefix : Delta-2*b ≤ (k-r)*(2*m+p-k+r)) :
    (x+r)*(x+r+p)-2*b ≤ epsilon := by
  rw [hk] at hprefix
  rw [he]
  nlinarith

theorem tail_pays_fixed_positions (r p x f b epsilon : ℤ)
    (hr : 2 ≤ r) (hp : 0 ≤ p) (hx : 0 ≤ x) (hf : f ≤ 2*x+p)
    (he : (x+r)*(x+r+p)-2*b ≤ epsilon) : 2*f+r*r-2*b ≤ epsilon := by
  have hxx := sq_nonneg x
  have hpx := mul_nonneg hp hx
  have hrx := mul_nonneg (show 0 ≤ 2*r-4 by omega) hx
  have hrp := mul_nonneg (show 0 ≤ r-2 by omega) hp
  nlinarith

theorem tail_threshold (f r b t epsilon : ℤ)
    (he : 2*f+r*r-2*b ≤ epsilon) (ht : 2*t-3 ≤ r*r-2*b) :
    2*f+2*t-3 ≤ epsilon := by omega

theorem hull_certificate (v t b : ℤ)
    (hb : b ≤ v-t) (hv : 2*v ≤ t*t+3) : 2*t-3 ≤ t*t-2*b := by omega

theorem bounded_arrow_certificate (r s b t : ℤ)
    (hb : b ≤ r*s) (hc : 2*t-3 ≤ r*(r-2*s)) : 2*t-3 ≤ r*r-2*b := by nlinarith

theorem enough_bounded_components (s t : ℤ)
    (hs : 1 ≤ s) (ht : 2*s+2 ≤ t) : 2*t-3 ≤ t*(t-2*s) := by
  have hp := mul_nonneg (show 0 ≤ t by omega) (show 0 ≤ t-2*s-2 by omega)
  nlinarith

theorem enough_unit_components (t : ℤ) (ht : 3 ≤ t) : 2*t-3 ≤ t*(t-2) := by
  have hp := mul_nonneg (show 0 ≤ t-1 by omega) (show 0 ≤ t-3 by omega)
  nlinarith

theorem high_epsilon_activity (f p t epsilon A : ℤ)
    (hf : 0 ≤ f) (hp : 0 ≤ p) (ht : 3 ≤ t)
    (he : 2*f+2*t-3 ≤ epsilon) (hA : A=2*epsilon+p-f) :
    2*f+3*t-3 ≤ A := by omega

theorem general_forest_credit (Z Zbig Zother kbig kother U eta t : ℤ)
    (hbig : 2 ≤ Zbig-kbig+U) (hother : kother-t ≤ Zother)
    (hZ : Zbig+Zother ≤ Z) (heta : 0 ≤ eta) :
    2-t ≤ Z-kbig-kother+U+eta := by omega

theorem bridge_geometry_budget (f a t B largest : ℤ)
    (haf : a ≤ f) (hl : 1 ≤ largest) (hB : B+largest=a+t+1) :
    B ≤ f+t ∧ 2*B+largest-1 ≤ 2*f+2*t := by omega

theorem all_old_gaps_paid (f t B K w delta epsilon : ℤ)
    (hB : B ≤ f+t) (hK : K ≤ delta-1) (hw : 2 ≤ w)
    (he : 2*f+2*t-3 ≤ epsilon) : 2*B+K-w ≤ delta+epsilon := by omega

theorem fixed_gaps_paid (f t B largest delta epsilon : ℤ)
    (hB : 2*B+largest-1 ≤ 2*f+2*t) (hd : 3 ≤ delta)
    (he : 2*f+2*t-3 ≤ epsilon) : 2*B+largest-1 ≤ delta+epsilon := by omega

theorem peak_paid (D gamma credit A B t : ℤ)
    (hid : D-(2*B+gamma)=credit+A+1-2*B)
    (hc : 2-t ≤ credit) (hA : 2*B+t-3 ≤ A) : 2*B+gamma ≤ D := by omega

theorem unpaid_fixed_positions (f p t epsilon : ℤ)
    (hact : f*f ≤ 4*epsilon+p) (he : epsilon < 2*f+2*t-3) :
    (f-4)*(f-4) ≤ 8*t+p := by
  have hh : epsilon ≤ 2*f+2*t-4 := by omega
  nlinarith

theorem unpaid_component_count (t v n p : ℤ)
    (hfail : t*t+3 < 2*v) (hbig : 2*v ≤ n-p-2) : t*t ≤ n-p-6 := by omega

theorem external_cross_minimum (t v a fixedPairs M : ℤ)
    (ht : 2 ≤ t) (hv : 2*t ≤ v) (ha : 0 ≤ a) (hfixed : 0 ≤ fixedPairs)
    (hM : 2*(t-1)*(v-t)+a*v+fixedPairs ≤ M) : 2*(a+t) ≤ M := by
  have htv := mul_nonneg (show 0 ≤ t-1 by omega) (show 0 ≤ v-2*t by omega)
  have htt := mul_nonneg (show 0 ≤ t by omega) (show 0 ≤ t-2 by omega)
  have hav := mul_nonneg ha (show 0 ≤ v-2 by omega)
  nlinarith

theorem universal_old_gap_payment (delta epsilon d K w M B : ℤ)
    (hd : d+M+1 ≤ delta) (he : 0 ≤ epsilon) (hK : K ≤ d+1)
    (hw : 2 ≤ w) (hM : 2*B ≤ M) : 2*B+K-w ≤ delta+epsilon-2 := by omega

theorem universal_fixed_gap_payment (delta epsilon B largest M : ℤ)
    (hcost : 2*B+largest-1 ≤ M) (hd : M+1 ≤ delta) (he : 0 ≤ epsilon) :
    2*B+largest-1 ≤ delta+epsilon-1 := by omega

theorem refined_activity_from_mass (f p t epsilon A : ℤ)
    (hA : A=2*epsilon+p-f) (he : 3*f+3*t-3 ≤ 2*epsilon+p) :
    2*f+3*t-3 ≤ A := by omega

theorem refined_tail_peak (f p t r b epsilon A : ℤ)
    (he : 2*f+r*r-2*b ≤ epsilon) (hA : A=2*epsilon+p-f)
    (ht : 3*t-3 ≤ f+p+2*(r*r-2*b)) : 2*f+3*t-3 ≤ A := by omega

theorem refined_hull_certificate (v t b : ℤ)
    (hb : b ≤ v-t) (hv : 4*v ≤ 2*t*t+t+3) :
    3*t-3 ≤ 2*(t*t-2*b) := by nlinarith

theorem area_peak_payment (a t v fixedPairs M B m gamma delta epsilon : ℤ)
    (ha : 0 ≤ a) (hv : 2 ≤ v) (hfixed : 0 ≤ fixedPairs)
    (hM : 2*(t-1)*(v-t)+a*v+fixedPairs ≤ M) (hB : B ≤ a+t)
    (hm : m ≤ 2*(t-1)*v-2*t*t+4) (hg : gamma ≤ m-3)
    (hd : M+1 ≤ delta) (he : 0 ≤ epsilon) : 2*B+gamma ≤ delta+epsilon := by
  have hav := mul_nonneg ha (show 0 ≤ v-2 by omega)
  nlinarith

theorem unpaid_fixed_positions_refined (f p t epsilon A : ℤ)
    (hact : f*f ≤ 4*epsilon+p) (hA : A=2*epsilon+p-f)
    (hfail : A < 2*f+3*t-3) : (f-3)*(f-3) ≤ 6*t+1-p := by
  have hh : A ≤ 2*f+3*t-4 := by omega
  nlinarith

theorem unpaid_cubic_component_count (t v m : ℤ)
    (ht : 3 ≤ t) (hsmall : t*t+3 < 2*v)
    (hlarge : 2*(t-1)*v-2*t*t+4 < m) :
    t*t*t-3*t*t+4*t+1 ≤ m := by
  have hv : 0 ≤ 2*v-t*t-4 := by omega
  have hm : 2*(t-1)*v-2*t*t+5 ≤ m := by omega
  have hp := mul_nonneg (show 0 ≤ t-1 by omega) hv
  nlinarith

theorem three_component_residual (f p epsilon A : ℤ)
    (hf : 0 ≤ f) (hp0 : 0 ≤ p) (_hp1 : p ≤ 1)
    (hact : f*f ≤ 4*epsilon+p) (hA : A=2*epsilon+p-f)
    (hfail : A < 2*f+3) : f ≤ 6 ∧ epsilon ≤ 10 := by
  have hbound := unpaid_fixed_positions_refined f p 2 epsilon A hact hA (by omega)
  have hf6 : f ≤ 6 := by
    by_contra h
    have hf7 : 7 ≤ f := by omega
    nlinarith [sq_nonneg (f-7)]
  constructor
  · exact hf6
  · omega

#print axioms signed_tail_reserve
#print axioms tail_pays_fixed_positions
#print axioms tail_threshold
#print axioms hull_certificate
#print axioms bounded_arrow_certificate
#print axioms enough_bounded_components
#print axioms enough_unit_components
#print axioms high_epsilon_activity
#print axioms general_forest_credit
#print axioms bridge_geometry_budget
#print axioms all_old_gaps_paid
#print axioms fixed_gaps_paid
#print axioms peak_paid
#print axioms unpaid_fixed_positions
#print axioms unpaid_component_count
#print axioms external_cross_minimum
#print axioms universal_old_gap_payment
#print axioms universal_fixed_gap_payment
#print axioms refined_activity_from_mass
#print axioms refined_tail_peak
#print axioms refined_hull_certificate
#print axioms area_peak_payment
#print axioms unpaid_fixed_positions_refined
#print axioms unpaid_cubic_component_count
#print axioms three_component_residual

end CayleyPy.ManyComponentTailBudget
