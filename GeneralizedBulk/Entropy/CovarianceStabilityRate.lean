import GeneralizedBulk.Entropy.ConstructedCovarianceStability

/-! The constructed covariance comparison has an honest linear error rate and only a quadratic signal loss. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Entropy

def stabilityRateConstant (T L Dlog Dinv Dfactor : ℝ) : ℝ :=
  Dlog + Dinv*L*(8+2*T^2) + L^2*Dfactor*(1+T)

set_option maxHeartbeats 1000000 in
theorem mixtureStabilityCoefficient_linear_bound
    (B T0 T1 L0 L1 Dlog Dinv Dfactor e : ℝ)
    (hB : 0 ≤ B) (hT0 : 0 ≤ T0) (hT1 : 0 ≤ T1) (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1)
    (hDlog : 0 ≤ Dlog) (hDinv : 0 ≤ Dinv) (hDfactor : 0 ≤ Dfactor)
    (he : 0 ≤ e) (he1 : e ≤ 1) :
    mixtureStabilityCoefficient B (T0+T1*e) (L0+L1*e) (Dlog*e) (Dinv*e) (Dfactor*e) ≤
      stabilityRateConstant (T0+T1) (L0+L1) Dlog Dinv Dfactor * (1+B^2) * e := by
  let T := T0+T1
  let L := L0+L1
  have hT : T0+T1*e ≤ T := by dsimp [T]; nlinarith
  have hL : L0+L1*e ≤ L := by dsimp [L]; nlinarith
  have hTpos : 0 ≤ T := add_nonneg hT0 hT1
  have hLpos : 0 ≤ L := add_nonneg hL0 hL1
  have heq : mixtureStabilityCoefficient B (T0+T1*e) (L0+L1*e) (Dlog*e) (Dinv*e) (Dfactor*e) =
      (Dlog + Dinv*(L0+L1*e)*(8*B^2+2*(T0+T1*e)^2) + (L0+L1*e)^2*Dfactor*(B+(T0+T1*e)))*e := by
    unfold mixtureStabilityCoefficient
    ring
  rw [heq]
  apply mul_le_mul_of_nonneg_right _ he
  have hmono : Dlog + Dinv*(L0+L1*e)*(8*B^2+2*(T0+T1*e)^2) + (L0+L1*e)^2*Dfactor*(B+(T0+T1*e)) ≤
      Dlog + Dinv*L*(8*B^2+2*T^2) + L^2*Dfactor*(B+T) := by
    gcongr
  have hbpoly : 8*B^2+2*T^2 ≤ (8+2*T^2)*(1+B^2) := by
    nlinarith [mul_nonneg (sq_nonneg T) (sq_nonneg B)]
  have hblin : B+T ≤ (1+T)*(1+B^2) := by
    nlinarith [sq_nonneg (B-1/2), mul_nonneg hTpos (sq_nonneg B)]
  have hd := mul_le_mul_of_nonneg_left (show 1 ≤ 1+B^2 by nlinarith [sq_nonneg B]) hDlog
  simp only [mul_one] at hd
  have hp := mul_le_mul_of_nonneg_left hbpoly (mul_nonneg hDinv hLpos)
  have hl := mul_le_mul_of_nonneg_left hblin (mul_nonneg (sq_nonneg L) hDfactor)
  calc
    _ ≤ Dlog+Dinv*L*(8*B^2+2*T^2)+L^2*Dfactor*(B+T) := hmono
    _ ≤ Dlog*(1+B^2)+(Dinv*L)*((8+2*T^2)*(1+B^2))+
        (L^2*Dfactor)*((1+T)*(1+B^2)) := add_le_add (add_le_add hd hp) hl
    _ = _ := by dsimp [stabilityRateConstant,T,L]; ring

end GeneralizedBulk.Entropy
