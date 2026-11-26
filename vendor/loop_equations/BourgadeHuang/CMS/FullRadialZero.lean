import BourgadeHuang.CMS.FullRadialUniqueness

/-! Vanishing of the homogeneous full radial system with zero terminal value. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
namespace RadialConstructionData
variable {d : ℕ} (P : RadialConstructionData d)

/-- The actual full radial equations and terminal normalization determine all
components; the Volterra equation need not be assumed. -/
theorem full_radial_zero {w : Point d} (hw : w∈OrderedGapDomain d P.radius)
    (Y0 : EmptyBanach P.radius) (Z : RadialBanach d P.radius)
    (hlim : Tendsto Y0 atTop (𝓝 (0:EmptyVector)))
    (hY : ∀t : Tail P.radius,P.radius<t.val → ∀S : Finset (Fin d),
      HasDerivAt (fun s => subsetVector (tailExtension Y0 s ())
        (tailExtension (boundedUnweight P.radius_pos Z) s) S)
      (P.D.scaledRadialAction (shiftedDirection P.sign)
        (sectorialRay P.sign w P.radius t) (t:ℝ)
        (subsetVector (Y0 t ()) (boundedUnweight P.radius_pos Z t)) S) t.val) :
    Z=0 ∧ Y0=0 := by
  let F := P.localFamily w hw
  have hf := (P.localFamily_spec w hw).2.2.self_of_nhds
  have h0 : ∀t : Tail P.radius,P.radius<t.val →
      HasDerivAt (tailExtension Y0)
        (t.val⁻¹ • F.C01 w t (boundedUnweight P.radius_pos Z t)) t.val := by
    intro t ht
    apply hasDerivAt_pi.mpr
    intro u
    cases u
    simpa only [F,subsetVector_empty,P.D.scaledRadialAction_empty,Pi.smul_apply,hf.1.2.1,
      Complex.real_smul,Complex.ofReal_inv] using hY t ht ∅
  have h1 : ∀t : Tail P.radius,P.radius<t.val →
      HasDerivAt (tailExtension (boundedUnweight P.radius_pos Z))
        (complexDiagonalOperator P.lam (boundedUnweight P.radius_pos Z t)+
          F.N w t (boundedUnweight P.radius_pos Z t)+
          t.val⁻¹ • (F.C10 w t (Y0 t)+F.C11 w t (boundedUnweight P.radius_pos Z t))) t.val := by
    intro t ht
    apply hasDerivAt_pi.mpr
    intro S
    have hh := hY t ht S.val
    simpa only [F,subsetVector_nonempty,P.D.scaledRadialAction_nonempty,
      Pi.add_apply,Pi.smul_apply,complexDiagonalOperator_apply,hf.1.1,hf.1.2.2.1,hf.1.2.2.2,
      Fintype.sum_unique,P.lam_eq,Complex.real_smul,Complex.ofReal_inv] using hh
  have hZ := coupledRadialODE_unique P.radius_pos (F.N w) (F.C01 w) (F.C10 w) (F.C11 w)
    P.gap_pos P.lam P.lam_gap 0 Y0 Z hlim h0 h1 (d+1)
    (F.principal_integral_nilpotent P.D (shiftedDirection P.sign) P.sign hf.1
      P.radius_pos P.gap_pos P.lam P.lam_gap) hf.2
  have hconst : BoundedContinuousFunction.const (Tail P.radius) (0:EmptyVector)=0 := by ext t u;rfl
  rw [hconst] at hZ
  have hZzero : Z=0 := by
    simpa [coupledVolterraSolution,triangularAffineFixedPoint,affineFixedPoint] using hZ
  have h0eq := emptyComponent_eq_of_ode P.radius_pos (F.C01 w) 0 Y0 Z hlim h0
  refine ⟨hZzero,?_⟩
  rw [h0eq,hZzero]
  ext t u
  simp [coupledEmptyComponent,boundedUnweight_apply]

end RadialConstructionData
end BourgadeHuang.CMS
