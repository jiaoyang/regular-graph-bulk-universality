import BourgadeHuang.CMS.CanonicalSectorialFamily
import BourgadeHuang.CMS.BanachParameterBounds

/-! Actual radial-tail decay of parameter derivatives of the canonical
holomorphic family. The empty component has a locally analytic weighted
primitive, so its parameter derivatives decay as well as its value minus one. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
namespace RadialConstructionData
variable {d : ℕ} (P : RadialConstructionData d)

/-- A genuine locally analytic weighted primitive for the empty correction. -/
theorem exists_analytic_weightedEmptyCorrection {z : Point d}
    (hz : z∈OrderedGapDomain d P.radius) :
    ∃W : Point d → EmptyBanach P.radius,AnalyticAt ℂ W z ∧
      ∀ᶠw in 𝓝 z,P.emptyFamily w=BoundedContinuousFunction.const _ (1:EmptyVector)+
        boundedUnweight P.radius_pos (W w) := by
  let F := P.localFamily z hz
  let W : Point d → EmptyBanach P.radius := fun w=>complexPrimitiveOperator P.radius_pos
    (F.c01Op w (F.weightedSolution P.radius_pos P.gap_pos P.lam P.lam_gap w))
  have hf := P.localFamily_spec z hz
  have hZ := F.analyticAt_weightedSolution P.radius_pos P.gap_pos P.lam P.lam_gap
    hf.1 hf.2.2.self_of_nhds.2
  have h01 := analyticAt_complexBoundedCoefficientOperator hf.1.2.1
  have hW : AnalyticAt ℂ W z :=
    analyticAt_clm_apply analyticAt_const (analyticAt_clm_apply h01 hZ)
  refine ⟨W,hW,?_⟩
  filter_upwards [P.eventually_localFamily_eq hz] with w hw
  rw [←hw.2]
  rfl

/-- Every directional parameter derivative of both normalized blocks is
O(t⁻¹), with one constant for the whole radial tail and all directions. -/
theorem parameter_derivatives_reciprocal_bound {z : Point d}
    (hz : z∈OrderedGapDomain d P.radius) :
    ∃C : ℝ,0≤C ∧ ∀t : Tail P.radius,∀v : Point d,
      ‖fderiv ℂ (fun w=>P.emptyFamily w t) z v‖≤C*‖v‖/t.val ∧
      ‖fderiv ℂ (fun w=>P.nonemptyFamily w t) z v‖≤C*‖v‖/t.val := by
  obtain ⟨W,hW,he⟩ := P.exists_analytic_weightedEmptyCorrection hz
  let C := max ‖fderiv ℂ W z‖ ‖fderiv ℂ P.weightedFamily z‖
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro t v
  have ht : 0<t.val := P.radius_pos.trans_le t.property
  constructor
  · have hloc : (fun w=>P.emptyFamily w t)=ᶠ[𝓝 z]
        (fun w=>(1:EmptyVector)+boundedUnweight P.radius_pos (W w) t) := by
      filter_upwards [he] with w hw
      exact congrArg (fun f : EmptyBanach P.radius=>f t) hw
    have hd := (hasFDerivAt_unweighted_bounded_eval P.radius_pos hW.differentiableAt t).const_add (1:EmptyVector)
    have hdP := hd.congr_of_eventuallyEq hloc
    rw [hdP.fderiv]
    change ‖boundedUnweight P.radius_pos (fderiv ℂ W z v) t‖≤_
    exact (norm_unweight_le P.radius_pos _ t).trans
      (div_le_div_of_nonneg_right (((fderiv ℂ W z).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg v))) ht.le)
  · have hb := norm_fderiv_unweighted_bounded_eval_le P.radius_pos
      (P.analyticOnNhd_weightedFamily z hz).differentiableAt t v
    exact hb.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg v)) ht.le)

/-- Scalar coordinate derivatives of every actual subset component inherit
the same uniform radial-tail decay. -/
theorem coordinate_derivatives_reciprocal_bound {z : Point d}
    (hz : z∈OrderedGapDomain d P.radius) :
    ∃C : ℝ,0≤C ∧ ∀t : Tail P.radius,∀i : Fin d,
      ‖coordDeriv i (fun w=>P.emptyFamily w t ()) z‖≤C/t.val ∧
      ∀S : NonemptySubset d,‖coordDeriv i (fun w=>P.nonemptyFamily w t S) z‖≤C/t.val := by
  obtain ⟨C,hC,hbound⟩ := P.parameter_derivatives_reciprocal_bound hz
  refine ⟨C,hC,?_⟩
  intro t i
  have h0 := (hasFDerivAt_bounded_eval (P.analyticOnNhd_emptyFamily z hz).differentiableAt t).differentiableAt
  have h1 := (hasFDerivAt_bounded_eval (P.analyticOnNhd_nonemptyFamily z hz).differentiableAt t).differentiableAt
  have hb := hbound t (Pi.single i 1)
  have hn : ‖(Pi.single i 1 : Point d)‖=1 := by simp only [Pi.norm_single,norm_one]
  simp only [hn,mul_one] at hb
  constructor
  · rw [coordDeriv_component_eq_fderiv h0]
    exact (norm_le_pi_norm _ ()).trans hb.1
  · intro S
    rw [coordDeriv_component_eq_fderiv h1]
    exact (norm_le_pi_norm _ S).trans hb.2

/-- The empty correction and all parameter derivatives have a common tail
bound; the constants arise from actual Banach-valued analytic functions. -/
theorem values_and_parameter_derivatives_bound {z : Point d}
    (hz : z∈OrderedGapDomain d P.radius) :
    ∃C : ℝ,0≤C ∧ ∀t : Tail P.radius,
      ‖P.emptyFamily z t-1‖≤C/t.val ∧ ‖P.nonemptyFamily z t‖≤C/t.val ∧
      ∀v : Point d,‖fderiv ℂ (fun w=>P.emptyFamily w t) z v‖≤C*‖v‖/t.val ∧
        ‖fderiv ℂ (fun w=>P.nonemptyFamily w t) z v‖≤C*‖v‖/t.val := by
  obtain ⟨B,hB,hval⟩ := P.families_reciprocal_bound hz
  obtain ⟨C,hC,hderiv⟩ := P.parameter_derivatives_reciprocal_bound hz
  refine ⟨max B C,le_trans hB (le_max_left _ _),?_⟩
  intro t
  have ht : 0≤t.val := (P.radius_pos.trans_le t.property).le
  refine ⟨(hval t).1.trans (div_le_div_of_nonneg_right (le_max_left _ _) ht),
    (hval t).2.trans (div_le_div_of_nonneg_right (le_max_left _ _) ht),?_⟩
  intro v
  exact ⟨(hderiv t v).1.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg v)) ht),
    (hderiv t v).2.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg v)) ht)⟩

end RadialConstructionData
end BourgadeHuang.CMS
