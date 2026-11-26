import BourgadeHuang.RationalEdge.GaussianEdgeSample
import BourgadeHuang.RationalEdge.EventVanishing
import BourgadeHuang.RationalEdge.Limits
import BourgadeHuang.RationalEdge.CharacterizationReduction

/-! Existence of an actual Gaussian beta soft-edge reference law. The exact
finite density identity implies the weighted hierarchy directly, and hence
compactness and exact loop equations. No local law or Airy process is assumed. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge
open RationalBulk

theorem gaussianBetaEdge_eventWeightedHierarchy (β : ℝ) (hβ : 0<β) :
    RationalEdge.EventWeightedHierarchy (gaussianBetaProduct β hβ) β gaussianBetaEdgeState
      (fun _ => Set.univ) := by
  refine ⟨measurable_gaussianBetaEdgeState,fun _=>MeasurableSet.univ,?_,?_,?_⟩
  · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  · intro N q
    simpa using gaussianBetaEdgeState_moment β hβ N q
  · intro n K hK hoff
    obtain ⟨C,hC,hbound⟩ := hK.isBounded.exists_pos_norm_le
    refine ⟨fun N=>C/gaussianEdgeScale N,?_,(fun N=>div_nonneg hC.le (gaussianEdgeScale_pos N).le),?_⟩
    · simpa only [div_eq_mul_inv,mul_zero] using gaussianEdgeScale_inv_tendsto.const_mul C
    · intro N w hw aux haux
      simp only [Measure.restrict_univ]
      have hw0 := hoff w hw
      have ha0 (a) := hoff (aux a) (haux a)
      have hi := gaussianBetaProduct_integral β hβ N
        (fun x=>RationalEdge.loopIntegrand β (finiteEdgeState (gaussianEdgeScale N) x) w aux)
        ((RationalEdge.continuous_loopIntegrand β hw0 ha0).measurable.comp
          (measurable_finiteEdgeState (N+1) (gaussianEdgeScale N))).stronglyMeasurable
      have hm := gaussianBetaProduct_integral β hβ N
        (fun x=>resolventMonomial (finiteEdgeState (gaussianEdgeScale N) x) w aux)
        ((continuous_resolventMonomial hw0 ha0).measurable.comp
          (measurable_finiteEdgeState (N+1) (gaussianEdgeScale N))).stronglyMeasurable
      change ‖∫ ω,RationalEdge.loopIntegrand β (finiteEdgeState (gaussianEdgeScale N) (ω N)) w aux
        ∂gaussianBetaProduct β hβ‖ ≤ _
      rw [hi,gaussianBeta_finite_edge_loop β hβ N n (gaussianEdgeScale_pos N).ne'
        (gaussianEdgeScale_cube N) w hw0 aux ha0,←hm,norm_mul,norm_neg,norm_div,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos (gaussianEdgeScale_pos N)]
      exact mul_le_mul (div_le_div_of_nonneg_right (hbound w hw) (gaussianEdgeScale_pos N).le)
        (norm_integral_resolventMonomial_le (gaussianBetaProduct β hβ) (gaussianBetaEdgeState N)
          (measurable_gaussianBetaEdgeState N) (gaussianBetaEdgeState_moment β hβ N) hw0 ha0)
        (norm_nonneg _) (div_nonneg hC.le (gaussianEdgeScale_pos N).le)

theorem gaussianBetaEdge_vanishingHierarchy (β : ℝ) (hβ : 0<β) :
    RationalEdge.VanishingHierarchy (gaussianBetaProduct β hβ) β gaussianBetaEdgeState := by
  intro n w hw aux ha
  simpa only [Measure.restrict_univ] using
    (gaussianBetaEdge_eventWeightedHierarchy β hβ).restricted_loop_tendsto hw ha

theorem exists_gaussianBetaEdgeReference (β : ℝ) (hβ : 0<β) :
    ∃ (ν : ProbabilityMeasure AnchoredCountingState) (r : ℕ→ℕ), StrictMono r ∧
      WeakLawConverges (gaussianBetaProduct β hβ) (fun N=>gaussianBetaEdgeState (r N))
        (ν : Measure AnchoredCountingState) ∧
      RationalEdge.ExactHierarchy (ν : Measure AnchoredCountingState) β ∧
      ∃a : ℝ, 0<a ∧ Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2))
        (ν : Measure AnchoredCountingState) := by
  exact RationalEdge.exists_exact_anchored_subsequence_of_vanishingHierarchy
    (gaussianBetaProduct β hβ) β gaussianBetaEdgeState measurable_gaussianBetaEdgeState
    (gaussianBetaEdgeState_moment β hβ) (gaussianBetaEdge_vanishingHierarchy β hβ)

structure GaussianBetaEdgeReference (β : ℝ) (hβ : 0<β) where
  law : ProbabilityMeasure AnchoredCountingState
  subsequence : ℕ→ℕ
  strictMono : StrictMono subsequence
  converges : WeakLawConverges (gaussianBetaProduct β hβ)
    (fun N=>gaussianBetaEdgeState (subsequence N)) (law : Measure AnchoredCountingState)
  hierarchy : RationalEdge.ExactHierarchy (law : Measure AnchoredCountingState) β
  exponentialSquare : ∃a : ℝ, 0<a ∧ Integrable
    (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2))
    (law : Measure AnchoredCountingState)

theorem nonempty_gaussianBetaEdgeReference (β : ℝ) (hβ : 0<β) :
    Nonempty (GaussianBetaEdgeReference β hβ) := by
  obtain ⟨ν,r,hr,hw,hh,he⟩ := exists_gaussianBetaEdgeReference β hβ
  exact ⟨⟨ν,r,hr,hw,hh,he⟩⟩

/-- An actual Gaussian beta soft-edge subsequential law, whose existence and
loop hierarchy were proved from finite normalized particle densities. -/
def gaussianBetaEdgeReference (β : ℝ) (hβ : 0<β) : GaussianBetaEdgeReference β hβ :=
  Classical.choice (nonempty_gaussianBetaEdgeReference β hβ)

namespace GaussianBetaEdgeReference
variable {β : ℝ} {hβ : 0<β} (R : GaussianBetaEdgeReference β hβ)

def countingLaw : ProbabilityMeasure LocalCountingMeasure := anchoredCountingLaw R.law

theorem vague_subsequence : VagueLawConverges (gaussianBetaProduct β hβ)
    (fun N ω=>(gaussianBetaEdgeState (R.subsequence N) ω).val.1)
    (R.countingLaw : Measure LocalCountingMeasure) :=
  anchored_sequence_vagueLawConverges (gaussianBetaProduct β hβ)
    (fun N=>gaussianBetaEdgeState (R.subsequence N)) R.law R.converges

theorem full_convergence_of_uniqueness
    (hunique : ∀ρ : ProbabilityMeasure AnchoredCountingState,
      RationalEdge.ExactHierarchy (ρ : Measure AnchoredCountingState) β →
      (∃a : ℝ, 0<a ∧ Integrable
        (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2))
        (ρ : Measure AnchoredCountingState)) → ρ=R.law) :
    WeakLawConverges (gaussianBetaProduct β hβ) gaussianBetaEdgeState
      (R.law : Measure AnchoredCountingState) :=
  RationalEdge.weakLawConverges_of_vanishingHierarchy_and_uniqueness
    (gaussianBetaProduct β hβ) β gaussianBetaEdgeState measurable_gaussianBetaEdgeState
    (gaussianBetaEdgeState_moment β hβ) (gaussianBetaEdge_vanishingHierarchy β hβ) R.law hunique

end GaussianBetaEdgeReference
end BourgadeHuang.RationalEdge
