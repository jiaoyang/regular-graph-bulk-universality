import BourgadeHuang.NevanlinnaDividedDifference
import BourgadeHuang.CharacteristicRatioExpectation
import Mathlib.MeasureTheory.Integral.Prod

/-! All finite characteristic-ratio products satisfy the actual endpoint loop
identity. Integrability is obtained from one compact source, not inferred from
the individual factors. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

def ratioSourceMeasure (q : ℕ) : Measure (Fin q × RatioInterval) :=
  (Measure.count : Measure (Fin q)).prod ratioIntervalMeasure

instance (q : ℕ) : IsFiniteMeasure (ratioSourceMeasure q) := by
  unfold ratioSourceMeasure
  infer_instance

def anchoredCharacteristicRatios {q : ℕ} (s : AnchoredCountingState)
    (u v : Fin q → ℂ) : ℂ := ∏ j, anchoredCharacteristicRatio s (u j) (v j)

theorem integral_ratioSource {q : ℕ} (f : Fin q × RatioInterval → ℂ)
    (hf : Continuous f) :
    (∫ t, f t ∂ratioSourceMeasure q) =
      ∑ j : Fin q, ∫ t : RatioInterval, f (j,t) ∂ratioIntervalMeasure := by
  rw [ratioSourceMeasure, integral_prod _
    (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)), integral_count]

theorem characteristicRatios_integrable_and_endpoint_loop {q : ℕ}
    (ν : Measure AnchoredCountingState) (β : Beta) (hh : ExactAnchoredHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v : Fin q → ℂ) (huv : ∀ j, SameOpenHalfPlane (u j) (v j))
    {w : ℂ} (hw : w.im ≠ 0) :
    Integrable (fun s => anchoredCharacteristicRatios s u v) ν ∧
    Integrable (fun s => (anchoredLoopHead β s w+(2/β.value)*
      ∑ j, (anchoredDividedDifference s w (v j)-anchoredDividedDifference s w (u j)))*
        anchoredCharacteristicRatios s u v) ν ∧
    (∫ s, (anchoredLoopHead β s w+(2/β.value)*
      ∑ j, (anchoredDividedDifference s w (v j)-anchoredDividedDifference s w (u j)))*
        anchoredCharacteristicRatios s u v ∂ν) = 0 := by
  cases q with
  | zero =>
    have h := characteristicRatio_integrable_and_loop ν β hh ha he
      (u := Complex.I) (v := Complex.I)
      (Or.inl ⟨by simp,by simp⟩) hw
    simpa [anchoredCharacteristicRatios, anchoredCharacteristicRatio_self] using h
  | succ q =>
    let γ : Fin (q+1) × RatioInterval → ℂ := fun t => ratioPath (u t.1) (v t.1) t.2
    let ρ : Fin (q+1) × RatioInterval → ℂ := fun t => -(u t.1-v t.1)
    have hγ : Continuous γ := continuous_prod_of_discrete_left.mpr
      (fun j => (continuous_ratioPath (u j) (v j)).comp continuous_subtype_val)
    have hρ : Continuous ρ := by
      exact (((continuous_of_discreteTopology : Continuous u).comp continuous_fst).sub
        ((continuous_of_discreteTopology : Continuous v).comp continuous_fst)).neg
    have hoff (t : Fin (q+1) × RatioInterval) : (γ t).im ≠ 0 :=
      ratioPath_offReal (huv t.1) t.2.property
    have hF (s : AnchoredCountingState) : Continuous (fun t => ρ t*anchoredNevanlinna s (γ t)) := by
      apply hρ.mul
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (differentiableAt_anchoredNevanlinna s (hoff t)).continuousAt.comp hγ.continuousAt
    have hG (s : AnchoredCountingState) : Continuous
        (fun t => ρ t*((2/β.value)*anchoredInteraction s w (γ t))) := by
      apply hρ.mul (continuous_const.mul _)
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (continuousAt_anchoredInteraction_right s hw (hoff t)).comp hγ.continuousAt
    have hexp (s : AnchoredCountingState) :
        Complex.exp (∫ t, ρ t*anchoredNevanlinna s (γ t) ∂ratioSourceMeasure (q+1)) =
          anchoredCharacteristicRatios s u v := by
      rw [integral_ratioSource _ (hF s), Complex.exp_sum]
      rfl
    have hint (s : AnchoredCountingState) :
        (∫ t, ρ t*((2/β.value)*anchoredInteraction s w (γ t)) ∂ratioSourceMeasure (q+1)) =
          (2/β.value)*∑ j, (anchoredDividedDifference s w (v j)-anchoredDividedDifference s w (u j)) := by
      rw [integral_ratioSource _ (hG s), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      change (∫ t : RatioInterval, -(u j-v j)*((2/β.value)*
        anchoredInteraction s w (ratioPath (u j) (v j) t)) ∂ratioIntervalMeasure) = _
      simp_rw [mul_left_comm (-(u j-v j)) (2/β.value)]
      rw [integral_const_mul, integral_ratioPath_interaction s (huv j) hw]
    have h := exponential_loop_identity_compact_source_and_integrable (ratioSourceMeasure (q+1))
      γ ρ hγ hρ hoff ν β hh ha he hw
    simpa only [hexp,hint] using h

end BourgadeHuang
