import BourgadeHuang.CMS.PhysicalBranchIndependence
import BourgadeHuang.CMS.OrderedGapGeometry
import BourgadeHuang.CMS.DeformedBasis

/-! A genuine basis of physical general-coupling CMS solutions. Every branch
is constructed, its differential equations and independence are proved, and
finite-jet uniqueness supplies spanning on each connected open subdomain. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace BourgadeHuang.CMS
namespace RadialConstructionData
variable {d : ℕ} {β : ℝ} (hβ : 0<β) (c : Fin d → ℂ)
  (hc : ∀i,c i= -1 ∨ c i=(β:ℂ)/2)

theorem physicalCommonRadius_pos : 0<physicalCommonRadius hβ c hc := by
  unfold physicalCommonRadius
  exact add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun σ _=>(physical hβ c σ hc).radius_pos.le))

/-- Independence persists on every nonempty open part of the common chamber,
by the analytic identity principle on the connected ambient chamber. -/
theorem physicalBranch_linearIndependent_on_open (U : Set (Point d))
    (hU : IsOpen U) (hne : U.Nonempty)
    (hsub : U⊆OrderedGapDomain d (physicalCommonRadius hβ c hc)) :
    LinearIndependent ℂ (fun σ : Fin d → Sign=>fun z : U=>physicalBranch hβ c σ hc z.val) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have hrel : ∀z∈U,(∑σ,a σ*physicalBranch hβ c σ hc z)=0 := by
    intro z hz
    have hh := congrFun ha ⟨z,hz⟩
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using hh
  have hAn : AnalyticOnNhd ℂ (fun z=>∑σ,a σ*physicalBranch hβ c σ hc z)
      (OrderedGapDomain d (physicalCommonRadius hβ c hc)) := by
    intro z hz
    exact Finset.analyticAt_sum _ (fun σ _=>analyticAt_const.mul
      (physicalBranch_analytic hβ c σ hc z (physical_common_subset hβ c hc σ hz)))
  obtain ⟨z,hz⟩ := hne
  have he := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (orderedGapDomain_isConnected d (physicalCommonRadius hβ c hc)).isPreconnected
    (hsub hz) (by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact hrel w hw)
  apply (Fintype.linearIndependent_iff.mp (physicalBranch_linearIndependent_common hβ c hc)) a
  funext w
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using he w.property

/-- The actual branches satisfy every deformed equation on a common subdomain. -/
theorem physicalBranch_family (U : Set (Point d))
    (hsub : U⊆OrderedGapDomain d (physicalCommonRadius hβ c hc)) :
    ∀σ,AnalyticOnNhd ℂ (physicalBranch hβ c σ hc) U ∧
      ∀z∈U,∀i,deformedOperator (β:ℂ) c i (physicalBranch hβ c σ hc) z=0 := by
  intro σ
  exact ⟨(physicalBranch_analytic hβ c σ hc).mono (hsub.trans (physical_common_subset hβ c hc σ)),
    fun z hz=>physicalBranch_deformed hβ c σ hc z (physical_common_subset hβ c hc σ (hsub hz))⟩

/-- Unique general-coupling sectorial expansion, with no assumed branch,
asymptotic, independence, dimension, or spanning hypothesis. -/
theorem existsUnique_physical_expansion (U : Set (Point d))
    (hU : IsOpen U) (hconn : IsPreconnected U) (hne : U.Nonempty)
    (hsub : U⊆OrderedGapDomain d (physicalCommonRadius hβ c hc))
    {f : Point d → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hsolve : ∀z∈U,∀i,deformedOperator (β:ℂ) c i f z=0) :
    ∃!a : (Fin d → Sign) → ℂ,
      EqOn f (fun z=>∑σ,a σ*physicalBranch hβ c σ hc z) U := by
  apply existsUnique_deformed_expansion (β:ℂ) c U
    (fun σ=>physicalBranch hβ c σ hc) (physicalBranch_family hβ c hc U hsub)
    hU hconn hne
    (fun z hz=>orderedDomain_collisionFree
      (orderedGapDomain_subset_orderedDomain (physicalCommonRadius_pos hβ c hc).le (hsub hz)))
    (physicalBranch_linearIndependent_on_open hβ c hc U hU hne hsub)
    _ hf hsolve
  simp [Sign]

/-- The actual restricted solution space has precisely dimension 2^d. -/
theorem finrank_physicalSolutionSpace (U : Set (Point d))
    (hU : IsOpen U) (hconn : IsPreconnected U) (hne : U.Nonempty)
    (hsub : U⊆OrderedGapDomain d (physicalCommonRadius hβ c hc)) :
    Module.finrank ℂ (LinearMap.range (deformedSolutionRestriction (β:ℂ) c U))=2^d := by
  apply finrank_deformedRestrictedSolutionSpace (β:ℂ) c U
    (fun σ=>physicalBranch hβ c σ hc) (physicalBranch_family hβ c hc U hsub)
    hU hconn hne
    (fun z hz=>orderedDomain_collisionFree
      (orderedGapDomain_subset_orderedDomain (physicalCommonRadius_pos hβ c hc).le (hsub hz)))
    (physicalBranch_linearIndependent_on_open hβ c hc U hU hne hsub)
  simp [Sign]

end RadialConstructionData
end BourgadeHuang.CMS
