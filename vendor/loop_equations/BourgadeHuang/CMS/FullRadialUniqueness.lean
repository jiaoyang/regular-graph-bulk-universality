import BourgadeHuang.CMS.FullSubsetRadial

/-! Uniqueness of the normalized full finite radial system in its natural
bounded weighted class. -/
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
theorem full_radial_unique {w : Point d} (hw : w∈OrderedGapDomain d P.radius)
    (Y0 : EmptyBanach P.radius) (Z : RadialBanach d P.radius)
    (hlim : Tendsto Y0 atTop (𝓝 (1:EmptyVector)))
    (hY : ∀t : Tail P.radius,P.radius<t.val → ∀S : Finset (Fin d),
      HasDerivAt (fun s => subsetVector (tailExtension Y0 s ())
        (tailExtension (boundedUnweight P.radius_pos Z) s) S)
      (P.D.scaledRadialAction (shiftedDirection P.sign)
        (sectorialRay P.sign w P.radius t) (t:ℝ)
        (subsetVector (Y0 t ()) (boundedUnweight P.radius_pos Z t)) S) t.val) :
    Z=P.weightedFamily w ∧ Y0=P.emptyFamily w := by
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
  obtain ⟨hZ,h0eq⟩ := F.weightedSolution_unique_of_ode P.D (shiftedDirection P.sign) P.sign
    P.radius_pos P.gap_pos P.lam P.lam_gap hf.1 hf.2 Y0 Z hlim h0 h1
  exact ⟨by simpa only [weightedFamily,dif_pos hw] using hZ,
    by simpa only [emptyFamily,dif_pos hw] using h0eq⟩

end RadialConstructionData
end BourgadeHuang.CMS
