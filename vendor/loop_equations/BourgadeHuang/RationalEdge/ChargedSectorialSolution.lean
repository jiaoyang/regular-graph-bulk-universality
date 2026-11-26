import BourgadeHuang.EdgeCMS.PhysicalComparisonSystem
import BourgadeHuang.EdgeCMS.SectorialLinearity
import BourgadeHuang.RationalEdge.ChargedSystem
import BourgadeHuang.RationalEdge.PhysicalChargeChamber
import BourgadeHuang.RationalEdge.NormalizedObservableGerms

/-! The genuine charged expectation, normalized by the complete physical
WKB gauge and the actual Airy inverse, solves the constructed homogeneous
comparison system. Every analytic and differential hypothesis follows from
the edge hierarchy and its exponential-square anchor moment. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set
namespace BourgadeHuang.RationalEdge
open RationalBulk EdgeCMS CMS

theorem physicalNormalizedObservable_isSolution {n m : ℕ}
    (ν : Measure AnchoredCountingState) (β : ℝ) (hβ : 0<β)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) ν)
    (theta : Fin n→Bool) (eta : Fin m→Bool)
    (hn : (n:ℝ)=(m:ℝ)*β/2)
    (hbal : β*(signCount eta true:ℝ)=2*(signCount theta true:ℝ)) :
    (physicalComparisonData (β:ℂ) (charges β n m)
      (by exact_mod_cast hβ.ne') (Fin.append theta eta)).IsSolution
      (physicalNormalizedObservable ν (β:ℂ) (charges β n m) (Fin.append theta eta)) := by
  have hF : ∀y∈(physicalOpenCone (charges β n m) (Fin.append theta eta)).carrier,
      AnalyticAt ℂ (expectedChargedObservable ν (charges β n m) (blockAnchors theta eta))
        (airyInverseCoordinates y) := by
    intro y hy
    exact analyticOn_expectedChargedObservable ν ha he β theta eta _
      (chargedPhysicalChamber_inverse_denominatorDomain hy)
  have hop : ∀y∈(physicalOpenCone (charges β n m) (Fin.append theta eta)).carrier,∀i,
      edgeOperator (β:ℂ) (charges β n m) i
        (expectedChargedObservable ν (charges β n m) (blockAnchors theta eta))
        (airyInverseCoordinates y)=0 := by
    intro y hy i
    exact expectedChargedObservable_edgeOperator_eq_zero ν β hβ hh ha he theta eta hn hbal
      (chargedPhysicalChamber_inverse_denominatorDomain hy)
      (chargedPhysicalChamber_inverse_collisionFree hy) i
  have hs := physicalComparisonData_isSolution (β:ℂ) (charges β n m)
    (by exact_mod_cast hβ.ne') (Fin.append theta eta) hF hop
  simpa only [physicalAiryNormalized,physicalNormalized,physicalNormalizedObservable,
    blockAnchors_eq_reflect] using hs

end BourgadeHuang.RationalEdge
