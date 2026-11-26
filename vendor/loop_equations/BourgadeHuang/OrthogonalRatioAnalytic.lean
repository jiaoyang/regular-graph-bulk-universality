import BourgadeHuang.OrthogonalRatioLoop
import BourgadeHuang.AnchoredPowerSeriesDerivatives

/-! Common measurable power series for the genuine orthogonal ratio family.
Consequently all finite-product expectations are jointly analytic, and their
coordinate derivatives can be computed under the integral. -/
noncomputable section
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory Filter
namespace BourgadeHuang

theorem hasAnchoredPowerSeries_exp_primitive (c : ℂ) {u v : ℂ}
    (huv : SameOpenHalfPlane u v) :
    HasAnchoredPowerSeries (fun s z => Complex.exp (c*nevanlinnaPathPrimitive s z v)) u := by
  obtain ⟨R,hR,K,hK,hKoff,hSame,hPath⟩ := exists_ratioPath_compact_tube huv
  obtain ⟨C,hC,hb⟩ := exists_compact_resolvent_anchor_bound hK hKoff
  let L := ‖c‖*((‖u-v‖+R)*C)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  apply hasAnchoredPowerSeries_of_uniform_circle_bound _ u ⟨R,hR.le⟩ hR L hL
  · intro s z hz
    exact (((hasDerivAt_nevanlinnaPathPrimitive_numerator s (hSame z hz)).const_mul c).cexp).differentiableAt
  · intro z hz
    exact Complex.measurable_exp.comp
      ((measurable_nevanlinnaPathPrimitive (hSame z (Metric.sphere_subset_closedBall hz))).const_mul c)
  · intro s z hz
    apply (Complex.norm_exp_le_exp_norm _).trans
    apply Real.exp_le_exp.mpr
    rw [norm_mul]
    have hn : ‖z-v‖ ≤ ‖u-v‖+R := by
      have ht := norm_add_le (z-u) (u-v)
      rw [sub_add_sub_cancel] at ht
      have hz' : ‖z-u‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
      linarith
    have hp := norm_nevanlinnaPathPrimitive_le_of_bound s z v C (fun t => hb s _ (hPath z hz t))
    calc
      ‖c‖*‖nevanlinnaPathPrimitive s z v‖ ≤ ‖c‖*((‖z-v‖*C)*‖s.val.2‖) :=
        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ ≤ ‖c‖*(((‖u-v‖+R)*C)*‖s.val.2‖) := by gcongr
      _ = L*‖s.val.2‖ := by ring

theorem hasAnchoredPowerSeries_entireRatio_numerator (u : ℂ) {v : ℂ} (hv : v.im ≠ 0) :
    HasAnchoredPowerSeries (fun s z => entireCharacteristicRatio s z v) u := by
  obtain ⟨R,hR,L,hL,_,hb⟩ := exists_inverseEntireNumerator_bound hv
  let C := entireNumeratorGrowthConstant (‖u‖+1)
  have hC : 0 ≤ C := entireNumeratorGrowthConstant_nonneg (by positivity)
  apply hasAnchoredPowerSeries_of_uniform_circle_bound _ u 1 (by norm_num) (C+L) (add_nonneg hC hL)
  · intro s z _
    exact differentiable_entireCharacteristicRatio_numerator s v z
  · intro z _
    exact measurable_entireCharacteristicRatio z v
  · intro s z hz
    have hz' : ‖z-u‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_eq_norm,NNReal.coe_one] using hz
    have hn : ‖z‖ ≤ ‖u‖+1 := by
      have ht := norm_add_le (z-u) u
      rw [sub_add_cancel] at ht
      linarith
    rw [entireCharacteristicRatio,div_eq_mul_inv,norm_mul,add_mul,Real.exp_add]
    exact mul_le_mul (norm_anchoredEntireNumerator_le (‖u‖+1) (by positivity) s hn)
      (hb s v (Metric.mem_closedBall_self R.coe_nonneg)) (norm_nonneg _) (Real.exp_nonneg _)

/-- A common denominator base separates all three coordinates with no choice of
square-root values. -/
theorem orthogonalCharacteristicRatio_base (s : AnchoredCountingState) (u : ℂ)
    {v w b : ℂ} (hvb : SameOpenHalfPlane v b) (hwb : SameOpenHalfPlane w b) :
    orthogonalCharacteristicRatio s u v w =
      (entireCharacteristicRatio s u b * Complex.exp ((1/2:ℂ)*nevanlinnaPathPrimitive s v b))*
        Complex.exp ((1/2:ℂ)*nevanlinnaPathPrimitive s w b) := by
  rw [orthogonalCharacteristicRatio,
    ← entireCharacteristicRatio_mul_exp_primitive s u hvb,
    nevanlinnaPathPrimitive_cocycle s hwb hvb]
  simp only [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Uniform joint analyticity after any three contractive coordinate maps. -/
theorem hasAnchoredPowerSeries_orthogonalRatio_comp
    (U V W : E →L[ℂ] ℂ) (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) (hW : ‖W‖ ≤ 1)
    (x : E) (hwv : SameOpenHalfPlane (W x) (V x)) :
    HasAnchoredPowerSeries (fun s z => orthogonalCharacteristicRatio s (U z) (V z) (W z)) x := by
  have h₁ := (hasAnchoredPowerSeries_entireRatio_numerator (U x) hwv.right_offReal).pullback U hU x
  have h₂ := (hasAnchoredPowerSeries_exp_primitive (1/2:ℂ)
    (sameOpenHalfPlane_self_of_offReal hwv.right_offReal)).pullback V hV x
  have h₃ := (hasAnchoredPowerSeries_exp_primitive (1/2:ℂ) hwv).pullback W hW x
  apply ((h₁.mul h₂).mul h₃).congr_eventually
  filter_upwards [V.continuous.continuousAt.eventually
    (sameOpenHalfPlane_nhds (sameOpenHalfPlane_self_of_offReal hwv.right_offReal)),
    W.continuous.continuousAt.eventually (sameOpenHalfPlane_nhds hwv)] with z hzV hzW
  intro s
  exact (orthogonalCharacteristicRatio_base s (U z) hzV hzW).symm

/-- Three blocks of coordinates, one numerator block and two denominator blocks. -/
abbrev OrthogonalRatioPoint (q : ℕ) := (Fin q → ℂ) × ((Fin q → ℂ) × (Fin q → ℂ))

def orthogonalNumeratorProjection (q : ℕ) (j : Fin q) : OrthogonalRatioPoint q →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) j).comp (ContinuousLinearMap.fst ℂ _ _)
def orthogonalFirstDenominatorProjection (q : ℕ) (j : Fin q) : OrthogonalRatioPoint q →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) j).comp
    ((ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _))
def orthogonalSecondDenominatorProjection (q : ℕ) (j : Fin q) : OrthogonalRatioPoint q →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) j).comp
    ((ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _))

set_option maxHeartbeats 1000000 in
theorem hasAnchoredPowerSeries_orthogonalRatios_joint {q : ℕ}
    (u v w : Fin q → ℂ) (hwv : ∀ j, SameOpenHalfPlane (w j) (v j)) :
    HasAnchoredPowerSeries (fun s (p : OrthogonalRatioPoint q) =>
      orthogonalCharacteristicRatios s p.1 p.2.1 p.2.2) (u,v,w) := by
  change HasAnchoredPowerSeries (fun (s : AnchoredCountingState) (p : OrthogonalRatioPoint q) => ∏ j ∈ Finset.univ,
    orthogonalCharacteristicRatio s (p.1 j) (p.2.1 j) (p.2.2 j)) (u,v,w)
  apply HasAnchoredPowerSeries.finset_prod
  intro j _
  apply hasAnchoredPowerSeries_orthogonalRatio_comp
    (orthogonalNumeratorProjection q j) (orthogonalFirstDenominatorProjection q j)
    (orthogonalSecondDenominatorProjection q j) _ _ _ (u,v,w) (hwv j)
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro p
    change ‖p.1 j‖ ≤ 1*‖p‖
    simpa only [one_mul] using (norm_le_pi_norm p.1 j).trans (norm_fst_le p)
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro p
    change ‖p.2.1 j‖ ≤ 1*‖p‖
    simpa only [one_mul] using ((norm_le_pi_norm p.2.1 j).trans (norm_fst_le p.2)).trans (norm_snd_le p)
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro p
    change ‖p.2.2 j‖ ≤ 1*‖p‖
    simpa only [one_mul] using ((norm_le_pi_norm p.2.2 j).trans (norm_snd_le p.2)).trans (norm_snd_le p)

def expectedOrthogonalCharacteristicRatios {q : ℕ} (ν : Measure AnchoredCountingState)
    (u v w : Fin q → ℂ) : ℂ := ∫ s, orthogonalCharacteristicRatios s u v w ∂ν

theorem analyticAt_expectedOrthogonalCharacteristicRatios_joint {q : ℕ}
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v w : Fin q → ℂ) (hwv : ∀ j, SameOpenHalfPlane (w j) (v j)) :
    AnalyticAt ℂ (fun p : OrthogonalRatioPoint q =>
      expectedOrthogonalCharacteristicRatios ν p.1 p.2.1 p.2.2) (u,v,w) :=
  (hasAnchoredPowerSeries_orthogonalRatios_joint u v w hwv).analyticAt_integral ν ha he

end BourgadeHuang
