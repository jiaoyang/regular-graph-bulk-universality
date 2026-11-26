import BourgadeHuang.CMS.FreeVolterraODE
import BourgadeHuang.CMS.ComplexPrimitiveODE

/-! Exact normalized radial ODEs for the actual coupled complex Volterra
fixed point. The differential equations and limits follow from the integrals. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option linter.unusedSectionVars false
variable {J K : Type*} [Fintype J] [DecidableEq J] [Fintype K]
  {R a : ℝ} (hR : 0<R)
  (N : Tail R →ᵇ ((J → ℂ) →L[ℂ] (J → ℂ)))
  (C01 : Tail R →ᵇ ((J → ℂ) →L[ℂ] (K → ℂ)))
  (C10 : Tail R →ᵇ ((K → ℂ) →L[ℂ] (J → ℂ)))
  (C11 : Tail R →ᵇ ((J → ℂ) →L[ℂ] (J → ℂ)))

def coupledEmptyComponent (e : K → ℂ) (Z : Tail R →ᵇ (J → ℂ)) : Tail R →ᵇ (K → ℂ) :=
  BoundedContinuousFunction.const _ e+
    boundedUnweight hR (complexPrimitiveOperator hR (complexBoundedCoefficientOperator C01 Z))

def coupledFullSource (e : K → ℂ) (Z : Tail R →ᵇ (J → ℂ)) : Tail R →ᵇ (J → ℂ) :=
  complexBoundedCoefficientOperator N (boundedUnweight hR Z)+
    boundedUnweight hR
      (complexBoundedCoefficientOperator C10 (coupledEmptyComponent hR C01 e Z)+
        complexBoundedCoefficientOperator C11 (boundedUnweight hR Z))

theorem coupledEmptyComponent_normalization (e : K → ℂ) (Z : Tail R →ᵇ (J → ℂ)) :
    Tendsto (coupledEmptyComponent hR C01 e Z) atTop (𝓝 e) := by
  simpa only [coupledEmptyComponent,BoundedContinuousFunction.coe_add,
    BoundedContinuousFunction.const_apply,Pi.add_apply,add_zero] using
    (tendsto_const_nhds.add (tendsto_unweight_zero hR
      (complexPrimitiveOperator hR (complexBoundedCoefficientOperator C01 Z))))

theorem coupledComponents_reciprocal_bound (e : K → ℂ) (Z : Tail R →ᵇ (J → ℂ)) :
    ∃B : ℝ,0≤B ∧ ∀t : Tail R,
      ‖coupledEmptyComponent hR C01 e Z t-e‖≤B/t.val ∧
      ‖boundedUnweight hR Z t‖≤B/t.val := by
  let W := complexPrimitiveOperator hR (complexBoundedCoefficientOperator C01 Z)
  refine ⟨max ‖W‖ ‖Z‖,(norm_nonneg Z).trans (le_max_right _ _),?_⟩
  intro t
  constructor
  · change ‖(e+boundedUnweight hR W t)-e‖≤_
    rw [add_sub_cancel_left]
    exact (norm_unweight_le hR W t).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (hR.trans_le t.property).le)
  · exact (norm_unweight_le hR Z t).trans
      (div_le_div_of_nonneg_right (le_max_right _ _) (hR.trans_le t.property).le)

/-- The eliminated empty component satisfies its actual first-order equation. -/
theorem hasDerivAt_coupledEmptyComponent (e : K → ℂ) (Z : Tail R →ᵇ (J → ℂ))
    (t : Tail R) (ht : R<t.val) :
    HasDerivAt (tailExtension (coupledEmptyComponent hR C01 e Z))
      (t.val⁻¹ • C01 t (boundedUnweight hR Z t)) t.val := by
  have hd := (hasDerivAt_unweight_complexPrimitive hR
    (complexBoundedCoefficientOperator C01 Z) ht).const_add e
  have he : tailExtension (boundedUnweight hR (boundedUnweight hR
      (complexBoundedCoefficientOperator C01 Z))) t.val=
      t.val⁻¹ • C01 t (boundedUnweight hR Z t) := by
    rw [tailExtension_apply,boundedUnweight_apply,boundedUnweight_apply,
      complexBoundedCoefficientOperator_apply,boundedUnweight_apply,
      ContinuousLinearMap.map_smul_of_tower]
  rw [he] at hd
  exact hd

/-- The nonempty component satisfies the exact radial ODE, with the true
matrix coefficients and the constructed empty component. -/
theorem hasDerivAt_coupledNonemptyComponent (ha : 0<a) (lam : J → ℂ)
    (hlam : ∀i,a≤(lam i).re) (e : K → ℂ) (Z : Tail R →ᵇ (J → ℂ))
    (hZ : Z=freeForcingOperator hR ha lam hlam
        (complexBoundedCoefficientOperator N Z+
          complexBoundedCoefficientOperator C10 (BoundedContinuousFunction.const _ e))+
      freeRemainderOperator hR ha lam hlam
        (complexBoundedCoefficientOperator C10
          (complexPrimitiveOperator hR (complexBoundedCoefficientOperator C01 Z))+
          complexBoundedCoefficientOperator C11 Z))
    (t : Tail R) (ht : R<t.val) :
    HasDerivAt (tailExtension (boundedUnweight hR Z))
      (complexDiagonalOperator lam (boundedUnweight hR Z t)+
        N t (boundedUnweight hR Z t)+t.val⁻¹ •
          (C10 t (coupledEmptyComponent hR C01 e Z t)+C11 t (boundedUnweight hR Z t))) t.val := by
  let f := complexBoundedCoefficientOperator N Z+
    complexBoundedCoefficientOperator C10 (BoundedContinuousFunction.const _ e)
  let g := complexBoundedCoefficientOperator C10
    (complexPrimitiveOperator hR (complexBoundedCoefficientOperator C01 Z))+
    complexBoundedCoefficientOperator C11 Z
  have he : Z=freeForcingOperator hR ha lam hlam (f+boundedUnweight hR g) := by
    change Z=freeForcingOperator hR ha lam hlam f+freeRemainderOperator hR ha lam hlam g at hZ
    rw [freeRemainder_eq_forcing_unweight,←map_add] at hZ
    exact hZ
  have hs : boundedUnweight hR (f+boundedUnweight hR g)=coupledFullSource hR N C01 C10 C11 e Z := by
    apply BoundedContinuousFunction.ext
    intro s
    simp only [f,g,coupledFullSource,coupledEmptyComponent,boundedUnweight_apply,
      complexBoundedCoefficientOperator_apply,BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.const_apply,map_add,ContinuousLinearMap.map_smul_of_tower,smul_add,add_assoc]
  have hd := hasDerivAt_unweight_freeForcing hR ha lam hlam (f+boundedUnweight hR g) ht
  rw [←he,hs,tailExtension_apply,tailExtension_apply] at hd
  convert hd using 1
  simp only [coupledFullSource,BoundedContinuousFunction.add_apply,
    complexBoundedCoefficientOperator_apply,boundedUnweight_apply,add_assoc]

end BourgadeHuang.CMS
