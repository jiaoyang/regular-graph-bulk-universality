import BourgadeHuang.OrthogonalLargeChamber
import BourgadeHuang.CMS.PhysicalSectorialBasis

/-! The actual beta-one expected characteristic ratios have a unique finite
sectorial expansion. The analytic branches, their equations, independence and
spanning are all constructed; no CMS basis or asymptotic identity is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace BourgadeHuang
namespace OrthogonalCMS

/-- A single constructed large radius works for every orthogonal sign pattern. -/
def sectorialRadius (q : ℕ) : ℝ :=
  CMS.RadialConstructionData.physicalCommonRadius (β:=1) zero_lt_one
    (charges q) (charges_physical q)

/-- The actual normalized physical branch for the orthogonal charge vector. -/
def sectorialBranch {q : ℕ} (σ : Fin (q+(q+q)) → CMS.Sign) : CMS.Point (q+(q+q)) → ℂ :=
  CMS.RadialConstructionData.physicalBranch (β:=1) zero_lt_one (charges q) σ (charges_physical q)

/-- The common large chamber with prescribed paired denominator half-planes. -/
def sectorialChamber {q : ℕ} (η : Fin q → CMS.Sign) : Set (CMS.Point (q+(q+q))) :=
  largeChamber (sectorialRadius q) η

theorem sectorialRadius_pos (q : ℕ) : 0<sectorialRadius q :=
  CMS.RadialConstructionData.physicalCommonRadius_pos (β:=1) zero_lt_one
    (charges q) (charges_physical q)

end OrthogonalCMS

/-- Actual hierarchy expectations possess a unique finite beta-one CMS
expansion on every common paired denominator chamber. -/
theorem existsUnique_expectedOrthogonalRatio_sectorial_expansion {q : ℕ}
    (ν : Measure AnchoredCountingState) (hh : ExactAnchoredHierarchy ν .one)
    {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) ν)
    (η : Fin q → CMS.Sign) :
    ∃!b : (Fin (q+(q+q)) → CMS.Sign) → ℂ,
      EqOn (expectedOrthogonalRatioFunction ν)
        (fun z=>∑σ,b σ*OrthogonalCMS.sectorialBranch σ z) (OrthogonalCMS.sectorialChamber η) := by
  have hsol := expectedOrthogonalRatioFunction_largeChamber_solution ν hh ha he
    (OrthogonalCMS.sectorialRadius_pos q).le η
  exact CMS.RadialConstructionData.existsUnique_physical_expansion (β:=1) zero_lt_one
    (OrthogonalCMS.charges q) (OrthogonalCMS.charges_physical q)
    (OrthogonalCMS.sectorialChamber η)
    (CMS.orderedGapMixedDomain_isOpen _ _ _ _)
    (CMS.orderedGapMixedDomain_isConnected _ _ _ _).isPreconnected
    (CMS.orderedGapMixedDomain_nonempty _ _ _ _)
    (fun _ hz=>hz.1) hsol.1 (by simpa only [Complex.ofReal_one] using hsol.2)

/-- Coefficients are selected from the proved unique expansion of the actual
expectation, not from an assumed comparison expression. -/
def orthogonalSectorialCoefficients {q : ℕ}
    (ν : Measure AnchoredCountingState) (hh : ExactAnchoredHierarchy ν .one)
    {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) ν)
    (η : Fin q → CMS.Sign) : (Fin (q+(q+q)) → CMS.Sign) → ℂ :=
  (existsUnique_expectedOrthogonalRatio_sectorial_expansion ν hh ha he η).choose

theorem orthogonalSectorialCoefficients_spec {q : ℕ}
    (ν : Measure AnchoredCountingState) (hh : ExactAnchoredHierarchy ν .one)
    {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) ν)
    (η : Fin q → CMS.Sign) :
    EqOn (expectedOrthogonalRatioFunction ν)
      (fun z=>∑σ,orthogonalSectorialCoefficients ν hh ha he η σ*OrthogonalCMS.sectorialBranch σ z)
      (OrthogonalCMS.sectorialChamber η) :=
  (existsUnique_expectedOrthogonalRatio_sectorial_expansion ν hh ha he η).choose_spec.1

/-- Every coefficient comparison reduces to equality of the actual analytic
expectations on the common chamber, by the proved unique expansion. -/
theorem orthogonalSectorialCoefficients_eq_iff {q : ℕ}
    (ν μ : Measure AnchoredCountingState)
    (hν : ExactAnchoredHierarchy ν .one) (hμ : ExactAnchoredHierarchy μ .one)
    {a b : ℝ} (ha : 0<a) (hb : 0<b)
    (heν : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) ν)
    (heμ : Integrable (fun s : AnchoredCountingState=>Real.exp (b*‖s.val.2‖^2)) μ)
    (η : Fin q → CMS.Sign) :
    orthogonalSectorialCoefficients ν hν ha heν η=orthogonalSectorialCoefficients μ hμ hb heμ η ↔
      EqOn (expectedOrthogonalRatioFunction ν) (expectedOrthogonalRatioFunction μ)
        (OrthogonalCMS.sectorialChamber η) := by
  constructor
  · intro he z hz
    rw [(orthogonalSectorialCoefficients_spec ν hν ha heν η) hz,
      (orthogonalSectorialCoefficients_spec μ hμ hb heμ η) hz,he]
  · intro he
    apply ((existsUnique_expectedOrthogonalRatio_sectorial_expansion ν hν ha heν η).choose_spec.2
      (orthogonalSectorialCoefficients μ hμ hb heμ η) ?_).symm
    intro z hz
    exact (he hz).trans ((orthogonalSectorialCoefficients_spec μ hμ hb heμ η) hz)

end BourgadeHuang
