import BourgadeHuang.RationalEdge.Foundation
import BourgadeHuang.MultivariateExponentialLoop

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge

/-- The quadratic head of the loop equation. -/
def loopHead (β : ℝ) (s : AnchoredCountingState) (w : ℂ) : ℂ :=
  ((2 - (β : ℂ)) / (β : ℂ)) * anchoredDerivative s w + anchoredNevanlinna s w ^ 2 + (-w)

theorem continuous_loopHead (β : ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    Continuous (fun s : AnchoredCountingState => loopHead β s w) :=
  ((continuous_const.mul (continuous_anchoredDerivative hw)).add
    ((continuous_anchoredNevanlinna hw).pow 2)).add continuous_const

theorem anchoredGrowth_loopHead (β : ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    AnchoredGrowth (fun s => loopHead β s w) 2 := by
  have hs := (anchoredGrowth_nevanlinna hw).mul (anchoredGrowth_nevanlinna hw)
  simp only [← pow_two] at hs
  exact (((AnchoredGrowth.const_mul _ (anchoredGrowth_derivative hw)).mono (by omega)).add hs).add
    ((AnchoredGrowth.const (-w)).mono (by omega))


/-- Every finite linear combination of resolvents satisfies all polynomial
integration-by-parts identities, by the original mixed-parameter hierarchy. -/
theorem exactHierarchy_linearCombination_monomial
    (ν : Measure AnchoredCountingState) (β : ℝ) (hh : ExactHierarchy ν β)
    {m : ℕ} {w : ℂ} {v : Fin m → ℂ} (hw : w.im ≠ 0) (hv : ∀ i, (v i).im ≠ 0)
    (c : Fin m → ℂ) (n : ℕ) :
    let X := fun s : AnchoredCountingState => ∑ i, c i * anchoredNevanlinna s (v i)
    let J := fun s : AnchoredCountingState => ∑ i, c i * ((2 / (β : ℂ)) * anchoredInteraction s w (v i))
    Integrable (fun s => loopHead β s w * X s ^ n + (n : ℂ) * J s * X s ^ (n - 1)) ν ∧
      (∫ s, loopHead β s w * X s ^ n + (n : ℂ) * J s * X s ^ (n - 1) ∂ν) = 0 := by
  let Q (f : Fin n → Fin m) (s : AnchoredCountingState) :=
    (∏ a, c (f a)) * loopIntegrand β s w (fun a => v (f a))
  have hQ (f : Fin n → Fin m) : Integrable (Q f) ν ∧ (∫ s, Q f s ∂ν) = 0 := by
    obtain ⟨hi, hz⟩ := hh n w hw (fun a => v (f a)) (fun a => hv (f a))
    exact ⟨hi.const_mul _, by rw [integral_const_mul, hz, mul_zero]⟩
  have heq (s : AnchoredCountingState) : (∑ f : Fin n → Fin m, Q f s) =
      loopHead β s w * (∑ i, c i * anchoredNevanlinna s (v i)) ^ n +
        (n : ℂ) * (∑ i, c i * ((2 / (β : ℂ)) * anchoredInteraction s w (v i))) *
          (∑ i, c i * anchoredNevanlinna s (v i)) ^ (n - 1) := by
    have hpoint := weighted_loop_words n m (loopHead β s w) c
      (fun i => anchoredNevanlinna s (v i)) (fun i => (2 / (β : ℂ)) * anchoredInteraction s w (v i))
    convert hpoint using 1
    apply Finset.sum_congr rfl
    intro f _
    dsimp [Q, loopIntegrand, loopHead]
    rw [Finset.mul_sum]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    ring
  constructor
  · simpa only [heq] using integrable_finset_sum Finset.univ (fun f _ => (hQ f).1)
  · calc
      _ = ∫ s, ∑ f : Fin n → Fin m, Q f s ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall (fun s => (heq s).symm))
      _ = 0 := by
        rw [integral_finset_sum _ (fun f _ => (hQ f).1)]
        simp only [(hQ _).2, Finset.sum_const_zero]


/-- The full finite-source exponential generating equation. Repetitions among
the spectral parameters and mixed upper/lower half-planes are unrestricted. -/
theorem multivariate_exponential_tilted_loop_identity
    (ν : Measure AnchoredCountingState) (β : ℝ) (hh : ExactHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    {m : ℕ} {w : ℂ} {v : Fin m → ℂ} (hw : w.im ≠ 0) (hv : ∀ i, (v i).im ≠ 0)
    (c : Fin m → ℂ) :
    let X := fun s : AnchoredCountingState => ∑ i, c i * anchoredNevanlinna s (v i)
    let J := fun s : AnchoredCountingState => ∑ i, c i * ((2 / (β : ℂ)) * anchoredInteraction s w (v i))
    Integrable (fun s => (loopHead β s w + J s) * Complex.exp (X s)) ν ∧
      (∫ s, (loopHead β s w + J s) * Complex.exp (X s) ∂ν) = 0 := by
  let H := fun s : AnchoredCountingState => loopHead β s w
  let X := fun s : AnchoredCountingState => ∑ i, c i * anchoredNevanlinna s (v i)
  let J := fun s : AnchoredCountingState => ∑ i, c i * ((2 / (β : ℂ)) * anchoredInteraction s w (v i))
  have hH : Continuous H := continuous_loopHead β hw
  have hX : Continuous X := continuous_finset_sum _ (fun i _ =>
    continuous_const.mul (continuous_anchoredNevanlinna (hv i)))
  have hJ : Continuous J := continuous_finset_sum _ (fun i _ =>
    continuous_const.mul (continuous_const.mul (continuous_anchoredInteraction hw (hv i))))
  have hXg : AnchoredGrowth X 1 := AnchoredGrowth.finset_sum _ _ (fun i _ =>
    AnchoredGrowth.const_mul _ (anchoredGrowth_nevanlinna (hv i)))
  have hJg : AnchoredGrowth J 1 := AnchoredGrowth.finset_sum _ _ (fun i _ =>
    AnchoredGrowth.const_mul _ (AnchoredGrowth.const_mul _ (anchoredGrowth_interaction hw (hv i))))
  have hdom := (integrable_growth_norm_mul_exp_norm ν ha he H X hH hX (anchoredGrowth_loopHead β hw) hXg).add
    (integrable_growth_norm_mul_exp_norm ν ha he J X hJ hX hJg hXg)
  have hres := integral_exponential_identity_of_monomials ν H X J 1 hH.aestronglyMeasurable
    hX.aestronglyMeasurable hJ.aestronglyMeasurable
    (fun n => exactHierarchy_linearCombination_monomial ν β hh hw hv c n)
    (by simpa only [norm_one, one_mul, add_mul] using hdom)
  simpa only [one_mul] using hres


end BourgadeHuang.RationalEdge
