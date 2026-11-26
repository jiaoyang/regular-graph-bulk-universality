import BourgadeHuang.OrthogonalCharacteristicRatio

/-! # Exact loop equations for the genuine orthogonal ratios

Arbitrary complex weights on compact ratio paths are first handled directly by
the proved integrated-source identity. The orthogonal numerator weight is −1
and each of its two denominator weights is one half.
-/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

/-- Every finite weighted family of path primitives obeys the exact endpoint
loop equation. This includes fractional denominator powers with fixed branches. -/
theorem weightedRatioPrimitives_integrable_and_endpoint_loop {q : ℕ}
    (ν : Measure AnchoredCountingState) (β : Beta) (hh : ExactAnchoredHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (c u v : Fin q → ℂ) (huv : ∀ j, SameOpenHalfPlane (u j) (v j))
    {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (fun s => Complex.exp (∑ j, c j*nevanlinnaPathPrimitive s (u j) (v j))) ν ∧
    Integrable (fun s => (anchoredLoopHead β s z+(2/β.value)*
      ∑ j, c j*(anchoredDividedDifference s z (u j)-anchoredDividedDifference s z (v j)))*
        Complex.exp (∑ j, c j*nevanlinnaPathPrimitive s (u j) (v j))) ν ∧
    (∫ s, (anchoredLoopHead β s z+(2/β.value)*
      ∑ j, c j*(anchoredDividedDifference s z (u j)-anchoredDividedDifference s z (v j)))*
        Complex.exp (∑ j, c j*nevanlinnaPathPrimitive s (u j) (v j)) ∂ν) = 0 := by
  cases q with
  | zero =>
    have h := characteristicRatio_integrable_and_loop ν β hh ha he
      (u := Complex.I) (v := Complex.I) (Or.inl ⟨by simp,by simp⟩) hz
    simpa [anchoredCharacteristicRatio_self] using h
  | succ q =>
    let γ : Fin (q+1) × RatioInterval → ℂ := fun t => ratioPath (u t.1) (v t.1) t.2
    let ρ : Fin (q+1) × RatioInterval → ℂ := fun t => c t.1*(u t.1-v t.1)
    have hγ : Continuous γ := continuous_prod_of_discrete_left.mpr
      (fun j => (continuous_ratioPath (u j) (v j)).comp continuous_subtype_val)
    have hρ : Continuous ρ := by
      exact ((continuous_of_discreteTopology : Continuous c).comp continuous_fst).mul
        (((continuous_of_discreteTopology : Continuous u).comp continuous_fst).sub
          ((continuous_of_discreteTopology : Continuous v).comp continuous_fst))
    have hoff (t : Fin (q+1) × RatioInterval) : (γ t).im ≠ 0 :=
      ratioPath_offReal (huv t.1) t.2.property
    have hF (s : AnchoredCountingState) : Continuous (fun t => ρ t*anchoredNevanlinna s (γ t)) := by
      apply hρ.mul
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (differentiableAt_anchoredNevanlinna s (hoff t)).continuousAt.comp hγ.continuousAt
    have hG (s : AnchoredCountingState) : Continuous
        (fun t => ρ t*((2/β.value)*anchoredInteraction s z (γ t))) := by
      apply hρ.mul (continuous_const.mul _)
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (continuousAt_anchoredInteraction_right s hz (hoff t)).comp hγ.continuousAt
    have hprim (s : AnchoredCountingState) :
        (∫ t, ρ t*anchoredNevanlinna s (γ t) ∂ratioSourceMeasure (q+1)) =
          ∑ j, c j*nevanlinnaPathPrimitive s (u j) (v j) := by
      rw [integral_ratioSource _ (hF s)]
      apply Finset.sum_congr rfl
      intro j _
      simp only [ρ, γ, mul_assoc, nevanlinnaPathPrimitive, integral_const_mul]
    have hint (s : AnchoredCountingState) :
        (∫ t, ρ t*((2/β.value)*anchoredInteraction s z (γ t)) ∂ratioSourceMeasure (q+1)) =
          (2/β.value)*∑ j, c j*(anchoredDividedDifference s z (u j)-anchoredDividedDifference s z (v j)) := by
      rw [integral_ratioSource _ (hG s), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have h := integral_ratioPath_interaction s (huv j) hz
      have hpos : (∫ t : RatioInterval, (u j-v j)*
          anchoredInteraction s z (ratioPath (u j) (v j) t) ∂ratioIntervalMeasure) =
            anchoredDividedDifference s z (u j)-anchoredDividedDifference s z (v j) := by
        calc
          _ = -(∫ t : RatioInterval, -(u j-v j)*
              anchoredInteraction s z (ratioPath (u j) (v j) t) ∂ratioIntervalMeasure) := by
            rw [← integral_neg]
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun t => by ring)
          _ = _ := by rw [h, neg_sub]
      change (∫ t : RatioInterval, (c j*(u j-v j))*((2/β.value)*
        anchoredInteraction s z (ratioPath (u j) (v j) t)) ∂ratioIntervalMeasure) = _
      simp_rw [show ∀ a b d : ℂ, (c j*a)*(b*d) = b*(c j*(a*d)) by intros; ring]
      rw [integral_const_mul, integral_const_mul, hpos]
    have h := exponential_loop_identity_compact_source_and_integrable (ratioSourceMeasure (q+1))
      γ ρ hγ hρ hoff ν β hh ha he hz
    simpa only [hprim,hint] using h

/-- The actual β = 1 endpoint identity has one contribution for each denominator
and minus twice the contribution of each numerator. -/
theorem orthogonalCharacteristicRatios_integrable_and_endpoint_loop {q : ℕ}
    (ν : Measure AnchoredCountingState) (hh : ExactAnchoredHierarchy ν .one)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v w : Fin q → ℂ) (huv : ∀ j, SameOpenHalfPlane (u j) (v j))
    (hwv : ∀ j, SameOpenHalfPlane (w j) (v j)) {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (fun s => orthogonalCharacteristicRatios s u v w) ν ∧
    Integrable (fun s => (anchoredLoopHead .one s z+
      ∑ j, (anchoredDividedDifference s z (v j)+anchoredDividedDifference s z (w j)-
        2*anchoredDividedDifference s z (u j)))*orthogonalCharacteristicRatios s u v w) ν ∧
    (∫ s, (anchoredLoopHead .one s z+
      ∑ j, (anchoredDividedDifference s z (v j)+anchoredDividedDifference s z (w j)-
        2*anchoredDividedDifference s z (u j)))*orthogonalCharacteristicRatios s u v w ∂ν) = 0 := by
  let c : Fin (q+q) → ℂ := Fin.append (fun _ : Fin q => -1) (fun _ : Fin q => 1/2)
  let U : Fin (q+q) → ℂ := Fin.append u w
  let V : Fin (q+q) → ℂ := Fin.append v v
  have hUV : ∀ j, SameOpenHalfPlane (U j) (V j) := by
    intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa only [U,V,Fin.append_left] using huv j
    · simpa only [U,V,Fin.append_right] using hwv j
  have h := weightedRatioPrimitives_integrable_and_endpoint_loop ν .one hh ha he c U V hUV hz
  have hexp (s : AnchoredCountingState) :
      Complex.exp (∑ j, c j*nevanlinnaPathPrimitive s (U j) (V j)) =
        orthogonalCharacteristicRatios s u v w := by
    simp only [c,U,V,Fin.sum_univ_add,Fin.append_left,Fin.append_right]
    rw [← Finset.sum_add_distrib, Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro j _
    rw [orthogonalCharacteristicRatio_eq_exp s (huv j)]
    congr 1
    ring
  have hint (s : AnchoredCountingState) :
      (2/Beta.one.value : ℂ)*∑ j, c j*(anchoredDividedDifference s z (U j)-anchoredDividedDifference s z (V j)) =
        ∑ j, (anchoredDividedDifference s z (v j)+anchoredDividedDifference s z (w j)-
          2*anchoredDividedDifference s z (u j)) := by
    simp only [c,U,V,Fin.sum_univ_add,Fin.append_left,Fin.append_right,Beta.value]
    norm_num only [Nat.cast_one, div_one]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simpa only [hexp,hint] using h

end BourgadeHuang
