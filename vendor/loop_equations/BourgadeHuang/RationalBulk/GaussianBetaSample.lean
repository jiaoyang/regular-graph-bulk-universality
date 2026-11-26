import BourgadeHuang.RationalBulk.GaussianBetaDensity
import BourgadeHuang.RationalBulk.FiniteParticleLaw

/-! A single probability space carrying all finite Gaussian beta ensembles.
The coordinates are the actual labelled beta-density particles, with no
postulated spectral law or limiting process. -/
noncomputable section
open scoped BigOperators Topology ENNReal
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

def gaussianBetaFiniteLaw (β : ℝ) (hβ : 0 < β) (N : ℕ) :
    ProbabilityMeasure (Fin (N+1) → ℝ) :=
  ⟨gaussianBetaMeasure β (N+1), gaussianBetaMeasure_probability hβ (by omega)⟩

abbrev GaussianBetaSpace := ParticleProductSpace (fun N => N+1)

def gaussianBetaProduct (β : ℝ) (hβ : 0 < β) : Measure GaussianBetaSpace :=
  particleProductMeasure (gaussianBetaFiniteLaw β hβ)

instance gaussianBetaProduct_probability (β : ℝ) (hβ : 0 < β) :
    IsProbabilityMeasure (gaussianBetaProduct β hβ) := by
  unfold gaussianBetaProduct
  infer_instance

def gaussianBetaState (N : ℕ) (ω : GaussianBetaSpace) : AnchoredCountingState :=
  particleProductState 0 N ω

theorem gaussianBetaProduct_map_eval (β : ℝ) (hβ : 0 < β) (N : ℕ) :
    (gaussianBetaProduct β hβ).map (fun ω => ω N) = gaussianBetaMeasure β (N+1) :=
  particleProductMeasure_map_eval (gaussianBetaFiniteLaw β hβ) N

theorem gaussianBetaProduct_integral (β : ℝ) (hβ : 0 < β) (N : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin (N+1) → ℝ) → E) (hf : StronglyMeasurable f) :
    (∫ ω, f (ω N) ∂gaussianBetaProduct β hβ) = ∫ x, f x ∂gaussianBetaMeasure β (N+1) :=
  particleProductMeasure_integral (gaussianBetaFiniteLaw β hβ) N f hf

theorem measurable_gaussianBetaState (N : ℕ) : Measurable (gaussianBetaState N) :=
  measurable_particleProductState 0 N

theorem gaussianBetaState_moment (β : ℝ) (hβ : 0 < β) (N q : ℕ) :
    Integrable (fun ω => ‖(gaussianBetaState N ω).val.2‖^q) (gaussianBetaProduct β hβ) :=
  particleProductState_moment (gaussianBetaFiniteLaw β hβ) 0 N q

@[simp] theorem gaussianBetaState_nevanlinna (N : ℕ) (ω : GaussianBetaSpace)
    {w : ℂ} (hw : w.im ≠ 0) :
    anchoredNevanlinna (gaussianBetaState N ω) w = microscopicResolvent (ω N) 0 w :=
  finiteAnchoredState_nevanlinna (ω N) 0 hw

/-- The point measures are exactly the finite Gaussian beta particles. -/
@[simp] theorem gaussianBetaState_measure (N : ℕ) (ω : GaussianBetaSpace) :
    (gaussianBetaState N ω).val.1.measure = ∑ i, Measure.dirac (ω N i) := rfl

end BourgadeHuang.RationalBulk
