import BourgadeHuang.RationalEdge.ExponentialSources
import BourgadeHuang.OrthogonalRatioLoop

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge

/-- Every finite weighted family of path primitives obeys the exact endpoint
loop equation. This includes fractional denominator powers with fixed branches. -/
theorem weightedRatioPrimitives_integrable_and_endpoint_loop {q : ℕ}
    (ν : Measure AnchoredCountingState) (β : ℝ) (hh : ExactHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (c u v : Fin q → ℂ) (huv : ∀ j, SameOpenHalfPlane (u j) (v j))
    {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (fun s => Complex.exp (∑ j, c j*nevanlinnaPathPrimitive s (u j) (v j))) ν ∧
    Integrable (fun s => (loopHead β s z+(2/(β : ℂ))*
      ∑ j, c j*(anchoredDividedDifference s z (u j)-anchoredDividedDifference s z (v j)))*
        Complex.exp (∑ j, c j*nevanlinnaPathPrimitive s (u j) (v j))) ν ∧
    (∫ s, (loopHead β s z+(2/(β : ℂ))*
      ∑ j, c j*(anchoredDividedDifference s z (u j)-anchoredDividedDifference s z (v j)))*
        Complex.exp (∑ j, c j*nevanlinnaPathPrimitive s (u j) (v j)) ∂ν) = 0 := by
  cases q with
  | zero =>
    have h := multivariate_exponential_tilted_loop_identity ν β hh ha he hz
      (v := fun _ : Fin 0 => Complex.I) (fun i => Fin.elim0 i) (fun _ => 0)
    simpa only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Complex.exp_zero, mul_one, mul_zero] using
      And.intro (show Integrable (fun _ : AnchoredCountingState => (1 : ℂ)) ν from
        by
          have hr : Integrable (fun _ : AnchoredCountingState => (1 : ℝ)) ν := by
            simpa using integrable_anchor_polynomial_exp ν ha he (by norm_num : (0 : ℝ) ≤ 1) 0 0
          simpa using hr.ofReal)
        h
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
        (fun t => ρ t*((2/(β : ℂ))*anchoredInteraction s z (γ t))) := by
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
        (∫ t, ρ t*((2/(β : ℂ))*anchoredInteraction s z (γ t)) ∂ratioSourceMeasure (q+1)) =
          (2/(β : ℂ))*∑ j, c j*(anchoredDividedDifference s z (u j)-anchoredDividedDifference s z (v j)) := by
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
      change (∫ t : RatioInterval, (c j*(u j-v j))*((2/(β : ℂ))*
        anchoredInteraction s z (ratioPath (u j) (v j) t)) ∂ratioIntervalMeasure) = _
      simp_rw [show ∀ a b d : ℂ, (c j*a)*(b*d) = b*(c j*(a*d)) by intros; ring]
      rw [integral_const_mul, integral_const_mul, hpos]
    have h := exponential_loop_identity_compact_source_and_integrable (ratioSourceMeasure (q+1))
      γ ρ hγ hρ hoff ν β hh ha he hz
    simpa only [hprim,hint] using h


end BourgadeHuang.RationalEdge
