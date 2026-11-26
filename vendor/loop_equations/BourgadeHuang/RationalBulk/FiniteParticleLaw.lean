import BourgadeHuang.FiniteCountingConfiguration
import BourgadeHuang.AnchoredStateBorel
import BourgadeHuang.Integrability
import BourgadeHuang.InfiniteProductCoordinates
import Mathlib.Probability.ProductMeasure

/-! Actual finite particle laws and their simultaneous realization.  This module
does not assume a matrix representation, a loop equation, or a limiting law. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory
namespace BourgadeHuang.RationalBulk

def finiteAnchoredState {N : ℕ} (x : Fin N → ℝ) (center : ℝ) : AnchoredCountingState :=
  ⟨(finiteCountingConfiguration x, microscopicResolvent x center Complex.I),
    validAnchoredCountingState_finite x center _ rfl⟩

@[simp] theorem finiteAnchoredState_counting {N : ℕ} (x : Fin N → ℝ) (center : ℝ) :
    (finiteAnchoredState x center).val.1 = finiteCountingConfiguration x := rfl

@[simp] theorem finiteAnchoredState_anchor {N : ℕ} (x : Fin N → ℝ) (center : ℝ) :
    (finiteAnchoredState x center).val.2 = microscopicResolvent x center Complex.I := rfl

theorem measurable_finiteAnchoredState (N : ℕ) (center : ℝ) :
    Measurable (fun x : Fin N → ℝ => finiteAnchoredState x center) :=
  ((measurable_finiteCountingConfiguration N).prodMk
    (measurable_microscopicResolvent (fun i => measurable_pi_apply i) center (by simp))).subtype_mk

theorem finiteAnchoredState_anchor_bound {N : ℕ} (x : Fin N → ℝ) (center : ℝ) :
    ‖(finiteAnchoredState x center).val.2‖ ≤ N + |center| := by
  simpa using norm_microscopicResolvent_le x center (w := Complex.I) (by simp)

theorem finiteAnchoredState_nevanlinna {N : ℕ} (x : Fin N → ℝ) (center : ℝ)
    {w : ℂ} (hw : w.im ≠ 0) :
    anchoredNevanlinna (finiteAnchoredState x center) w = microscopicResolvent x center w :=
  anchoredNevanlinna_eq_finite x center _ rfl hw

theorem finiteAnchoredState_moment {N : ℕ} (ν : Measure (Fin N → ℝ)) [IsFiniteMeasure ν]
    (center : ℝ) (q : ℕ) :
    Integrable (fun x => ‖(finiteAnchoredState x center).val.2‖ ^ q) ν :=
  integrable_microscopicResolvent_norm_pow (fun i => measurable_pi_apply i) center (by simp) q

abbrev ParticleProductSpace (d : ℕ → ℕ) := (N : ℕ) → Fin (d N) → ℝ

def particleProductMeasure {d : ℕ → ℕ}
    (ν : (N : ℕ) → ProbabilityMeasure (Fin (d N) → ℝ)) : Measure (ParticleProductSpace d) :=
  Measure.infinitePi (fun N => (ν N : Measure (Fin (d N) → ℝ)))

instance particleProductMeasure_probability {d : ℕ → ℕ}
    (ν : (N : ℕ) → ProbabilityMeasure (Fin (d N) → ℝ)) :
    IsProbabilityMeasure (particleProductMeasure ν) := by
  unfold particleProductMeasure
  infer_instance

theorem particleProductMeasure_map_eval {d : ℕ → ℕ}
    (ν : (N : ℕ) → ProbabilityMeasure (Fin (d N) → ℝ)) (N : ℕ) :
    (particleProductMeasure ν).map (fun ω => ω N) = (ν N : Measure (Fin (d N) → ℝ)) :=
  infinitePi_map_eval _ N

theorem particleProductMeasure_integral {d : ℕ → ℕ}
    (ν : (N : ℕ) → ProbabilityMeasure (Fin (d N) → ℝ)) (N : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin (d N) → ℝ) → E) (hf : StronglyMeasurable f) :
    (∫ ω, f (ω N) ∂particleProductMeasure ν) = ∫ x, f x ∂(ν N : Measure (Fin (d N) → ℝ)) := by
  rw [← particleProductMeasure_map_eval ν N]
  exact (integral_map_of_stronglyMeasurable (measurable_pi_apply N) hf).symm

def particleProductState {d : ℕ → ℕ} (center : ℝ) (N : ℕ)
    (ω : ParticleProductSpace d) : AnchoredCountingState := finiteAnchoredState (ω N) center

theorem measurable_particleProductState {d : ℕ → ℕ} (center : ℝ) (N : ℕ) :
    Measurable (particleProductState (d := d) center N) :=
  (measurable_finiteAnchoredState (d N) center).comp (measurable_pi_apply N)

theorem particleProductState_moment {d : ℕ → ℕ}
    (ν : (N : ℕ) → ProbabilityMeasure (Fin (d N) → ℝ)) (center : ℝ) (N q : ℕ) :
    Integrable (fun ω => ‖(particleProductState (d := d) center N ω).val.2‖ ^ q)
      (particleProductMeasure ν) :=
  integrable_microscopicResolvent_norm_pow
    (fun i => (measurable_pi_apply i).comp (measurable_pi_apply N)) center (by simp) q

end BourgadeHuang.RationalBulk
