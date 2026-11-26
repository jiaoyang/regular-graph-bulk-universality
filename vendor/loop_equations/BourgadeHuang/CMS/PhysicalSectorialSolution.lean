import BourgadeHuang.CMS.CanonicalObstructionEquation
import BourgadeHuang.CMS.CanonicalObstructionBounds
import BourgadeHuang.CMS.WeightedRadialZero
import BourgadeHuang.CMS.ConnectionSolutions

/-! Genuine normalized sectorial solutions of the physical general-coupling
CMS system. Compatibility follows from actual curvature, analytic parameter
decay and homogeneous radial uniqueness, not an assumed jet condition. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 100000
namespace RadialConstructionData
variable {d : ℕ}

@[simp] theorem canonicalJet_empty_eq_normalizedGerm (P : RadialConstructionData d) (z : Point d) :
    P.canonicalJet z ∅=P.normalizedGerm z := by
  simp only [canonicalJet,Finset.card_empty,pow_zero,inv_one,one_mul,fullFamily_empty,normalizedGerm]
  exact congrArg (fun v : EmptyVector=>v ())
    (tailExtension_apply (P.emptyFamily z) (⟨P.radius,le_rfl⟩ : Tail P.radius))

variable {β : ℝ} (hβ : 0<β) (c : Fin d → ℂ) (σ : Fin d → Sign)
  (hc : ∀i,c i= -1 ∨ c i=(β:ℂ)/2)

/-- All actual coordinate obstructions vanish. The proof constructs their
bounded weighted representatives and applies the proved zero terminal problem. -/
theorem physical_obstruction_eq_zero {z : Point d}
    (hz : z∈OrderedGapDomain d (physical hβ c σ hc).radius)
    (i : Fin d) (S : Finset (Fin d)) :
    let P:=physical hβ c σ hc
    P.D.obstruction P.canonicalJet i S z=0 := by
  let P:=physical hβ c σ hc
  have hh := P.unscaled_radial_zero hz
    (fun r T=>P.D.obstruction P.canonicalJet i T (sectorialRay P.sign z P.radius r))
    (P.continuous_obstruction_ray hz i) (P.obstruction_scaled_bound hz i)
    (fun t ht T=>physical_hasDerivAt_scaled_obstruction hβ c σ hc hz i T t ht) S
  have hr : sectorialRay P.sign z P.radius P.radius=z := by
    funext j
    simp [sectorialRay,shiftedRay]
  rw [hr] at hh
  exact hh

/-- The constructed analytic finite vector satisfies the whole flat
connection, with every coordinate equation proved. -/
theorem physical_connectionSolution :
    let P:=physical hβ c σ hc
    P.D.ConnectionSolutionOn P.canonicalJet (OrderedGapDomain d P.radius) := by
  let P:=physical hβ c σ hc
  refine ⟨P.analyticOnNhd_canonicalJet,?_⟩
  intro z hz i S
  exact sub_eq_zero.mp (physical_obstruction_eq_zero hβ c σ hc hz i S)

/-- The canonical subset components are the genuine square-free derivatives
of the constructed scalar normalized germ. -/
theorem physical_squareFreeDerivative (S : Finset (Fin d)) :
    let P:=physical hβ c σ hc
    EqOn (squareFreeDerivative S P.normalizedGerm) (fun z=>P.canonicalJet z S)
      (OrderedGapDomain d P.radius) := by
  let P:=physical hβ c σ hc
  simpa only [canonicalJet_empty_eq_normalizedGerm] using
    P.D.connectionSolution_squareFreeDerivative (orderedGapDomain_isOpen d P.radius)
      (physical_connectionSolution hβ c σ hc) S

/-- The actual normalized scalar solves the gauged second-order equations. -/
theorem physical_normalizedGerm_operator :
    let P:=physical hβ c σ hc
    ∀z∈OrderedGapDomain d P.radius,∀i,P.D.operator i P.normalizedGerm z=0 := by
  let P:=physical hβ c σ hc
  simpa only [canonicalJet_empty_eq_normalizedGerm] using
    SectorialData.general_connectionSolution_operator (β:ℂ) c σ
      (Complex.ofReal_ne_zero.mpr hβ.ne') hc (orderedGapDomain_isOpen d P.radius)
      (orderedGapDomain_subset_orderedDomain P.radius_pos.le)
      (physical_connectionSolution hβ c σ hc)

/-- The constructed physical general-coupling sectorial branch. -/
def physicalBranch (z : Point d) : ℂ :=
  generalBranch (β:ℂ) c σ z*(physical hβ c σ hc).normalizedGerm z

/-- The constructed branch is holomorphic on its actual large chamber. -/
theorem physicalBranch_analytic :
    AnalyticOnNhd ℂ (physicalBranch hβ c σ hc)
      (OrderedGapDomain d (physical hβ c σ hc).radius) := by
  intro z hz
  exact (analyticAt_generalBranch (β:ℂ) c σ
    (orderedGapDomain_subset_orderedDomain (physical hβ c σ hc).radius_pos.le hz)).mul
      ((physical hβ c σ hc).analyticOnNhd_normalizedGerm z hz)

/-- The constructed branch solves the original deformed CMS differential
system, for every positive coupling and every physical charge assignment. -/
theorem physicalBranch_deformed :
    ∀z∈OrderedGapDomain d (physical hβ c σ hc).radius,∀i,
      deformedOperator (β:ℂ) c i (physicalBranch hβ c σ hc) z=0 := by
  let P:=physical hβ c σ hc
  simpa only [canonicalJet_empty_eq_normalizedGerm,physicalBranch] using
    SectorialData.general_connectionSolution_deformed (β:ℂ) c σ
      (Complex.ofReal_ne_zero.mpr hβ.ne') hc (orderedGapDomain_isOpen d P.radius)
      (orderedGapDomain_subset_orderedDomain P.radius_pos.le)
      (physical_connectionSolution hβ c σ hc)

/-- Scalar normalization along the complete physical ray. -/
theorem physical_normalizedGerm_ray_limit {z : Point d}
    (hz : z∈OrderedGapDomain d (physical hβ c σ hc).radius) :
    let P:=physical hβ c σ hc
    Tendsto (fun t : Tail P.radius=>P.normalizedGerm
      (sectorialRay P.sign z P.radius t)) atTop (𝓝 1) := by
  let P:=physical hβ c σ hc
  have he (t : Tail P.radius) :
      P.normalizedGerm (sectorialRay P.sign z P.radius t)=P.emptyFamily z t () := by
    rw [←P.canonicalJet_empty_eq_normalizedGerm,P.canonicalJet_sectorialRay hz t]
    simp only [Finset.card_empty,pow_zero,inv_one,one_mul,fullFamily_empty,tailExtension_apply]
  change Tendsto (fun t : Tail P.radius=>P.normalizedGerm
    (sectorialRay P.sign z P.radius t)) atTop (𝓝 1)
  simp_rw [he]
  exact (tendsto_pi_nhds.mp (P.families_limits hz).1) ()

/-- All nonempty scaled genuine jets decay on the physical ray. -/
theorem physical_scaled_squareFree_ray_limit {z : Point d}
    (hz : z∈OrderedGapDomain d (physical hβ c σ hc).radius) (S : NonemptySubset d) :
    let P:=physical hβ c σ hc
    Tendsto (fun t : Tail P.radius=>(t.val:ℂ)^S.val.card*
      squareFreeDerivative S.val P.normalizedGerm (sectorialRay P.sign z P.radius t)) atTop (𝓝 0) := by
  let P:=physical hβ c σ hc
  have he (t : Tail P.radius) :
      (t.val:ℂ)^S.val.card*squareFreeDerivative S.val P.normalizedGerm
        (sectorialRay P.sign z P.radius t)=P.nonemptyFamily z t S := by
    have hj : squareFreeDerivative S.val P.normalizedGerm (sectorialRay P.sign z P.radius t)=
        P.canonicalJet (sectorialRay P.sign z P.radius t) S.val :=
      physical_squareFreeDerivative hβ c σ hc S.val
        (shiftedRay_mem_orderedGapDomain P.sign hz (sub_nonneg.mpr t.property))
    rw [hj,P.canonicalJet_sectorialRay hz t,←mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr
        (P.radius_pos.trans_le t.property).ne')),one_mul,fullFamily_nonempty,tailExtension_apply]
  change Tendsto (fun t : Tail P.radius=>(t.val:ℂ)^S.val.card*
    squareFreeDerivative S.val P.normalizedGerm (sectorialRay P.sign z P.radius t)) atTop (𝓝 0)
  simp_rw [he]
  exact (tendsto_pi_nhds.mp (P.families_limits hz).2) S

end RadialConstructionData
end BourgadeHuang.CMS
