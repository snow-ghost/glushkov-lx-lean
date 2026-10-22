import Mathlib

/-!
Phase80: the complement-of-a-gap estimate from the submitted proof.
This file proves the unbounded arithmetic implications. The finite
footrule inequality, source-packet geometry, exact service construction,
and quadratic gap-service lemma are explicit mathematical inputs.
-/
namespace CayleyPy.ConnectedComplementCap

theorem source_packet_exchange_reserve
    (delta L Z ZP A r k : ℤ)
    (hid : 2*delta = L+2*Z+A) (hL : r-2*k ≤ L)
    (hZ : ZP ≤ Z) (hA : 0 ≤ A) (hsource : k-1 ≤ ZP) :
    (r+1)/2-1 ≤ delta := by omega

theorem complement_root_deficit
    (n b l eta t Delta H : ℤ)
    (ht : t = 2*b-(n-(2*l+eta)))
    (hH : H = l*(n-l)-Delta)
    (hfinite : Delta ≤ 2*l*(n-b-l)) :
    l*(t-l-eta) ≤ H := by
  subst t
  subst H
  nlinarith

theorem localized_energy
    (Q epsilon DeltaP gapDelta otherDelta G H squares gapSquare K : ℤ)
    (hmass : Q-epsilon = DeltaP+gapDelta+otherDelta)
    (hroot : DeltaP = Q-G-H)
    (hlocal : 2*gapDelta+K^2 ≤ gapSquare)
    (hother : 2*otherDelta ≤ squares-gapSquare) :
    K^2 ≤ squares-2*G-2*H+2*epsilon := by omega

theorem dominant_square_upper
    (p eta t b c e s G H squares : ℤ)
    (heta : eta=0 ∨ eta=1) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hb : b=t+c+e) (hs : s=b+c+e)
    (hG : 4*G=(s+eta)^2-p) (hsquares : squares ≤ b^2+c^2) :
    2*(squares-2*G-2*H) ≤ (t-eta)^2+p-2*eta-4*H := by
  subst b
  subst s
  have hce := mul_nonneg hc he
  rcases heta with rfl | rfl <;> nlinarith [sq_nonneg e]

theorem complement_square_cap
    (l u p eta H T : ℤ)
    (_hl : 0 ≤ l) (hu : 0 ≤ u) (hutop : u ≤ 2*l)
    (hp : p ≤ 1) (heta : 0 ≤ eta)
    (hH : 0 ≤ H) (hcomp : l*(u-l) ≤ H)
    (hT : 2*T ≤ u^2+p-2*eta-4*H) :
    2*T ≤ l^2+1 := by
  by_cases hside : u ≤ l
  · have hs := mul_nonneg (show 0 ≤ l-u by omega)
        (show 0 ≤ l+u by omega)
    nlinarith
  · have hs := mul_nonneg (show 0 ≤ u-l by omega)
        (show 0 ≤ 3*l-u by omega)
    nlinarith

theorem nondominant_square_cap
    (s eta p G H squares : ℤ)
    (hs : 0 ≤ s) (heta : eta=0 ∨ eta=1) (hp : p ≤ 1)
    (hG : 4*G=(s+eta)^2-p) (hH : 0 ≤ H)
    (hsquares : 2*squares ≤ s^2) :
    2*(squares-2*G-2*H) ≤ 1 := by
  rcases heta with rfl | rfl <;> nlinarith

theorem all_internal_gaps_paid
    (l delta epsilon K w T : ℤ)
    (hl : 0 ≤ l) (hdelta : l-1 ≤ delta)
    (hepsilon : 0 ≤ epsilon) (hw : 2 ≤ w)
    (henergy : K^2 ≤ T+2*epsilon)
    (hcap : 2*T ≤ l^2+1) :
    K-w ≤ delta+epsilon := by
  by_contra h
  have hK : l+epsilon+2 ≤ K := by omega
  have hp := mul_nonneg (show 0 ≤ K-(l+epsilon+2) by omega)
      (show 0 ≤ K+(l+epsilon+2) by omega)
  have he := mul_nonneg hepsilon
      (show 0 ≤ epsilon+2*l+2 by omega)
  nlinarith [sq_nonneg l]

theorem complementary_arcs_paid
    (m q k Z A : ℤ) (hsource : k-1 ≤ Z) (hA : 0 ≤ A) :
    m-(q-k)-2 ≤ m-q+Z+A := by omega

theorem full_circle_cases_paid
    (l delta epsilon K w T charge D : ℤ)
    (hl : 0 ≤ l) (hd : l-1 ≤ delta) (he : 0 ≤ epsilon)
    (hw : 2 ≤ w) (henergy : K^2 ≤ T+2*epsilon)
    (hcap : 2*T ≤ l^2+1) (hD : D=delta+epsilon)
    (hcases : charge ≤ D ∨ charge ≤ K-w) : charge ≤ D := by
  have hp := all_internal_gaps_paid l delta epsilon K w T hl hd he hw henergy hcap
  rcases hcases with h | h <;> omega

#print axioms source_packet_exchange_reserve
#print axioms complement_root_deficit
#print axioms localized_energy
#print axioms dominant_square_upper
#print axioms complement_square_cap
#print axioms nondominant_square_cap
#print axioms all_internal_gaps_paid
#print axioms complementary_arcs_paid
#print axioms full_circle_cases_paid

end CayleyPy.ConnectedComplementCap
