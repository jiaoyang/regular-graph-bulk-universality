import BourgadeHuang.CMS.AnalyticNormalizedRadial
import BourgadeHuang.CMS.CoupledODERepresentation

/-! Uniqueness and independence of the local analytic lifts for the actual
normalized CMS radial solution. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
namespace RadialOperatorFamily
variable {d : ℕ} {R a : ℝ} (F G : RadialOperatorFamily d R)
  (D : SectorialData d) (ω : Point d) (σ : Fin d → Sign)
  (hR : 0<R) (ha : 0<a) (lam : NonemptySubset d → ℂ) (hlam : ∀i,a≤(lam i).re)

/-- The actual normalized ODE determines the bounded weighted solution,
without assuming its Volterra representation. -/
theorem weightedSolution_unique_of_ode {w : Point d} (hF : F.Matches D ω σ w)
    (hsmall : ‖F.effectiveOperator hR ha lam hlam w‖<1)
    (Y0 : EmptyBanach R) (Z : RadialBanach d R)
    (hlim : Tendsto Y0 atTop (𝓝 (1:EmptyVector)))
    (h0 : ∀t : Tail R,R<t.val → HasDerivAt (tailExtension Y0)
      (t.val⁻¹ • F.C01 w t (boundedUnweight hR Z t)) t.val)
    (h1 : ∀t : Tail R,R<t.val → HasDerivAt (tailExtension (boundedUnweight hR Z))
      (complexDiagonalOperator lam (boundedUnweight hR Z t)+F.N w t (boundedUnweight hR Z t)+
        t.val⁻¹ • (F.C10 w t (Y0 t)+F.C11 w t (boundedUnweight hR Z t))) t.val) :
    Z=F.weightedSolution hR ha lam hlam w ∧ Y0=F.normalizedEmpty hR ha lam hlam w := by
  have hz := coupledRadialODE_unique hR (F.N w) (F.C01 w) (F.C10 w) (F.C11 w)
    ha lam hlam 1 Y0 Z hlim h0 h1 (d+1)
    (F.principal_integral_nilpotent D ω σ hF hR ha lam hlam) hsmall
  have h0eq := emptyComponent_eq_of_ode hR (F.C01 w) 1 Y0 Z hlim h0
  exact ⟨hz,by rw [h0eq,hz]; rfl⟩

/-- Matching lifts represent exactly the same four bounded matrix fields. -/
theorem blocks_eq_of_matches {w : Point d} (hF : F.Matches D ω σ w)
    (hG : G.Matches D ω σ w) :
    F.N w=G.N w ∧ F.C01 w=G.C01 w ∧ F.C10 w=G.C10 w ∧ F.C11 w=G.C11 w := by
  constructor
  · ext t v i
    rw [hF.1,hG.1]
  constructor
  · ext t v i
    rw [hF.2.1,hG.2.1]
  constructor
  · ext t v i
    rw [hF.2.2.1,hG.2.2.1]
  · ext t v i
    rw [hF.2.2.2,hG.2.2.2]

/-- The normalized family is independent of all choices in the local
Banach-space analytic lifting construction. -/
theorem weightedSolution_eq_of_matches {w : Point d}
    (hF : F.Matches D ω σ w) (hG : G.Matches D ω σ w) :
    F.weightedSolution hR ha lam hlam w=G.weightedSolution hR ha lam hlam w ∧
      F.normalizedEmpty hR ha lam hlam w=G.normalizedEmpty hR ha lam hlam w ∧
      F.normalizedNonempty hR ha lam hlam w=G.normalizedNonempty hR ha lam hlam w := by
  obtain ⟨hn,h01,h10,h11⟩ := F.blocks_eq_of_matches G D ω σ hF hG
  have hz : F.weightedSolution hR ha lam hlam w=G.weightedSolution hR ha lam hlam w := by
    unfold weightedSolution nOp c01Op c10Op c11Op
    rw [hn,h01,h10,h11]
  exact ⟨hz,by simp only [normalizedEmpty,h01,hz],by simp only [normalizedNonempty,hz]⟩

end RadialOperatorFamily
end BourgadeHuang.CMS
