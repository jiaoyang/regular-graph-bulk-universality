import BourgadeHuang.VanishingAnchoredLimits

/-! Literal edge loop observables for arbitrary real beta. The analytic state space is
unchanged and includes the nonnegative affine Nevanlinna coefficient. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge

/-- The actual reconstructed loop polynomial, including coincident parameters. -/
def loopIntegrand {n : ℕ} (β : ℝ) (s : AnchoredCountingState)
    (w : ℂ) (aux : Fin n → ℂ) : ℂ :=
  (((2 - (β : ℂ)) / (β : ℂ)) * anchoredDerivative s w +
      anchoredNevanlinna s w ^ 2 + (-w)) *
    (∏ a, anchoredNevanlinna s (aux a)) +
    (2 / (β : ℂ)) * ∑ a, anchoredInteraction s w (aux a) *
      excludedProduct (fun b => anchoredNevanlinna s (aux b)) a

theorem continuous_loopIntegrand {n : ℕ} (β : ℝ)
    {w : ℂ} {aux : Fin n → ℂ} (hw : w.im ≠ 0) (haux : ∀ a, (aux a).im ≠ 0) :
    Continuous (fun s : AnchoredCountingState => loopIntegrand β s w aux) := by
  unfold loopIntegrand excludedProduct
  exact ((((continuous_const.mul (continuous_anchoredDerivative hw)).add
    ((continuous_anchoredNevanlinna hw).pow 2)).add continuous_const).mul
    (continuous_finset_prod _ (fun a _ => continuous_anchoredNevanlinna (haux a)))).add
    (continuous_const.mul (continuous_finset_sum _ (fun a _ =>
      (continuous_anchoredInteraction hw (haux a)).mul
        (continuous_finset_prod _ (fun b _ => continuous_anchoredNevanlinna (haux b))))))

/-- All parameters may repeat: the bound has degree `n+2` and uses only the anchor. -/
theorem growth_loopIntegrand {n : ℕ} (β : ℝ) {w : ℂ} {aux : Fin n → ℂ}
    (hw : w.im ≠ 0) (haux : ∀ a, (aux a).im ≠ 0) :
    AnchoredGrowth (fun s => loopIntegrand β s w aux) (n + 2) := by
  have hhead : AnchoredGrowth (fun s =>
      ((2 - (β : ℂ)) / (β : ℂ)) * anchoredDerivative s w + anchoredNevanlinna s w ^ 2 + (-w)) 2 := by
    have hs := (anchoredGrowth_nevanlinna hw).mul (anchoredGrowth_nevanlinna hw)
    simp only [← pow_two] at hs
    exact (((AnchoredGrowth.const_mul _ (anchoredGrowth_derivative hw)).mono (by omega)).add hs).add
      ((AnchoredGrowth.const (-w)).mono (by omega))
  have hp : AnchoredGrowth (fun s => ∏ a, anchoredNevanlinna s (aux a)) n := by
    simpa using AnchoredGrowth.finset_prod Finset.univ (fun a s => anchoredNevanlinna s (aux a))
      (fun a _ => anchoredGrowth_nevanlinna (haux a))
  have he (a : Fin n) : AnchoredGrowth
      (fun s => excludedProduct (fun b => anchoredNevanlinna s (aux b)) a) n := by
    exact (AnchoredGrowth.finset_prod (Finset.univ.erase a) (fun b s => anchoredNevanlinna s (aux b))
      (fun b _ => anchoredGrowth_nevanlinna (haux b))).mono
        ((Finset.card_erase_le).trans (by simp))
  have hsum : AnchoredGrowth (fun s => ∑ a, anchoredInteraction s w (aux a) *
      excludedProduct (fun b => anchoredNevanlinna s (aux b)) a) (n + 2) := by
    apply AnchoredGrowth.finset_sum
    intro a _
    exact ((anchoredGrowth_interaction hw (haux a)).mul (he a)).mono (by omega)
  have hmain : AnchoredGrowth (fun s =>
      (((2 - (β : ℂ)) / (β : ℂ)) * anchoredDerivative s w + anchoredNevanlinna s w ^ 2 + (-w)) *
        ∏ a, anchoredNevanlinna s (aux a)) (n + 2) := by
    simpa only [Nat.add_comm 2] using hhead.mul hp
  exact hmain.add (AnchoredGrowth.const_mul _ hsum)

def coefficientBound (β : ℝ) : ℝ := 1 + ‖(2 - (β : ℂ)) / (β : ℂ)‖ + ‖2 / (β : ℂ)‖

theorem coefficientBound_pos (β : ℝ) : 0 < coefficientBound β := by
  unfold coefficientBound
  positivity

theorem first_coefficient_le (β : ℝ) : ‖(2 - (β : ℂ)) / (β : ℂ)‖ ≤ coefficientBound β := by
  unfold coefficientBound
  linarith [norm_nonneg (2 / (β : ℂ))]

theorem second_coefficient_le (β : ℝ) : ‖2 / (β : ℂ)‖ ≤ coefficientBound β := by
  unfold coefficientBound
  linarith [norm_nonneg ((2 - (β : ℂ)) / (β : ℂ))]

/-- Exact edge hierarchy, with every expectation required to exist. -/
def ExactHierarchy (ν : Measure AnchoredCountingState) (β : ℝ) : Prop :=
  ∀ n : ℕ, ∀ w : ℂ, w.im ≠ 0 → ∀ aux : Fin n → ℂ, (∀ a, (aux a).im ≠ 0) →
    Integrable (fun s => loopIntegrand β s w aux) ν ∧
      (∫ s, loopIntegrand β s w aux ∂ν) = 0

/-- Pointwise absolute error form, after the relative-error absorption step. -/
def VanishingHierarchy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (β : ℝ) (X : ℕ → Ω → AnchoredCountingState) : Prop :=
  ∀ n (w : ℂ), w.im ≠ 0 → ∀ aux : Fin n → ℂ, (∀ j, (aux j).im ≠ 0) →
    Tendsto (fun N => ∫ ω, loopIntegrand β (X N ω) w aux ∂μ) atTop (𝓝 0)

theorem integrable_loop_comp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → AnchoredCountingState) (hX : Measurable X)
    (hm : ∀ q : ℕ, Integrable (fun ω => ‖(X ω).val.2‖^q) μ)
    (β : ℝ) {n : ℕ} {w : ℂ} {aux : Fin n → ℂ}
    (hw : w.im ≠ 0) (haux : ∀ j, (aux j).im ≠ 0) :
    Integrable (fun ω => loopIntegrand β (X ω) w aux) μ :=
  integrable_anchoredGrowth_comp μ X hX hm
    (continuous_loopIntegrand β hw haux) (growth_loopIntegrand β hw haux)

end BourgadeHuang.RationalEdge
