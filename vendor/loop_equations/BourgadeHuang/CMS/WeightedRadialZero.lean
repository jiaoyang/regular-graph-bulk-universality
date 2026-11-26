import BourgadeHuang.CMS.FullRadialZero

/-! A homogeneous radial solution with the proved weighted decay vanishes.
The bounded weighted Banach-space representatives are constructed explicitly. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 100000
namespace RadialConstructionData
variable {d : ℕ} (P : RadialConstructionData d)

/-- Actual reciprocal decay suffices for uniqueness; a supplied bounded
weighted representative is not an additional hypothesis. -/
theorem unscaled_radial_zero {z : Point d} (hz : z∈OrderedGapDomain d P.radius)
    (H : ℝ → Finset (Fin d) → ℂ)
    (hcont : ∀S,Continuous (fun t : Tail P.radius=>H t.val S))
    (hbound : ∃C : ℝ,0≤C ∧ ∀t : Tail P.radius,∀S,
      ‖(t.val:ℂ)^S.card*H t.val S‖≤C/t.val)
    (hODE : ∀t : Tail P.radius,P.radius<t.val → ∀S,
      HasDerivAt (fun r : ℝ=>(r:ℂ)^S.card*H r S)
        (P.D.scaledRadialAction (shiftedDirection P.sign)
          (sectorialRay P.sign z P.radius t) (t:ℝ)
          (fun T=>(t.val:ℂ)^T.card*H t.val T) S) t.val) :
    ∀S,H P.radius S=0 := by
  classical
  obtain ⟨C,hC,hB⟩ := hbound
  let W : Tail P.radius →ᵇ (Finset (Fin d) → ℂ) :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun t S=>(t.val:ℂ)^(S.card+1)*H t.val S)
      (continuous_pi (fun S=>((Complex.continuous_ofReal.comp continuous_subtype_val).pow _).mul (hcont S)))
      C (by
        intro t
        apply (pi_norm_le_iff_of_nonneg hC).mpr
        intro S
        have ht:=P.radius_pos.trans_le t.property
        calc
          ‖(t.val:ℂ)^(S.card+1)*H t.val S‖=
              t.val*‖(t.val:ℂ)^S.card*H t.val S‖ := by
            rw [pow_succ]
            rw [show (t.val:ℂ)^S.card*(t.val:ℂ)*H t.val S=
              (t.val:ℂ)*((t.val:ℂ)^S.card*H t.val S) by ring,norm_mul]
            simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
          _≤t.val*(C/t.val) := mul_le_mul_of_nonneg_left (hB t S) ht.le
          _=C := by field_simp)
  let L0 : (Finset (Fin d) → ℂ) →L[ℂ] EmptyVector :=
    ContinuousLinearMap.pi (fun _ : Unit=>(ContinuousLinearMap.proj (R:=ℂ) (∅ : Finset (Fin d)) :
      (Finset (Fin d) → ℂ) →L[ℂ] ℂ))
  let L1 : (Finset (Fin d) → ℂ) →L[ℂ] RadialVector d :=
    ContinuousLinearMap.pi (fun S : NonemptySubset d=>(ContinuousLinearMap.proj (R:=ℂ) S.val :
      (Finset (Fin d) → ℂ) →L[ℂ] ℂ))
  let Y0 : EmptyBanach P.radius := boundedUnweight P.radius_pos (L0.compLeftContinuousBounded _ W)
  let Z : RadialBanach d P.radius := L1.compLeftContinuousBounded _ W
  have hu (t : Tail P.radius) (S : Finset (Fin d)) :
      (t.val:ℂ)⁻¹*((t.val:ℂ)^(S.card+1)*H t.val S)=
        (t.val:ℂ)^S.card*H t.val S := by
    have ht : (t.val:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (P.radius_pos.trans_le t.property).ne'
    rw [pow_succ]
    field_simp
    ring
  have he (t : Tail P.radius) (S : Finset (Fin d)) :
      subsetVector (Y0 t ()) (boundedUnweight P.radius_pos Z t) S=
        (t.val:ℂ)^S.card*H t.val S := by
    by_cases hS : S.Nonempty
    · rw [subsetVector,dif_pos hS]
      change (t.val⁻¹:ℝ) • ((t.val:ℂ)^(S.card+1)*H t.val S)=_
      simpa only [Complex.real_smul,Complex.ofReal_inv] using hu t S
    · have hSe : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      rw [subsetVector_empty]
      change (t.val⁻¹:ℝ) • ((t.val:ℂ)^((∅ : Finset (Fin d)).card+1)*H t.val ∅)=_
      simpa only [Complex.real_smul,Complex.ofReal_inv] using hu t ∅
  have hlim : Tendsto Y0 atTop (𝓝 (0:EmptyVector)) :=
    tendsto_unweight_zero P.radius_pos (L0.compLeftContinuousBounded _ W)
  have hfull : ∀t : Tail P.radius,P.radius<t.val → ∀S : Finset (Fin d),
      HasDerivAt (fun s=>subsetVector (tailExtension Y0 s ())
        (tailExtension (boundedUnweight P.radius_pos Z) s) S)
        (P.D.scaledRadialAction (shiftedDirection P.sign) (sectorialRay P.sign z P.radius t) (t:ℝ)
          (subsetVector (Y0 t ()) (boundedUnweight P.radius_pos Z t)) S) t.val := by
    intro t ht S
    rw [show subsetVector (Y0 t ()) (boundedUnweight P.radius_pos Z t)=
      (fun T=>(t.val:ℂ)^T.card*H t.val T) from funext (he t)]
    apply (hODE t ht S).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds ht] with r hr
    change subsetVector (tailExtension Y0 (⟨r,hr.le⟩ : Tail P.radius).val ())
      (tailExtension (boundedUnweight P.radius_pos Z) (⟨r,hr.le⟩ : Tail P.radius).val) S=_
    rw [tailExtension_apply,tailExtension_apply]
    exact he ⟨r,hr.le⟩ S
  obtain ⟨hZ,h0⟩ := P.full_radial_zero hz Y0 Z hlim hfull
  intro S
  have hh := he (⟨P.radius,le_rfl⟩ : Tail P.radius) S
  rw [hZ,h0] at hh
  have hz0 : subsetVector ((0 : EmptyBanach P.radius) ⟨P.radius,le_rfl⟩ ())
      (boundedUnweight P.radius_pos (0 : RadialBanach d P.radius) ⟨P.radius,le_rfl⟩) S=0 := by
    unfold subsetVector
    split <;> simp
  rw [hz0] at hh
  exact (mul_eq_zero.mp hh.symm).resolve_left
    (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr P.radius_pos.ne'))

end RadialConstructionData
end BourgadeHuang.CMS
