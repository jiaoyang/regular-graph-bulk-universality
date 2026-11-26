import BourgadeHuang.CMS.BackwardODERepresentation
import BourgadeHuang.CMS.CoupledVolterraODE
import BourgadeHuang.CMS.AnalyticCoupledVolterra

/-! Reverse passage from the true normalized radial ODE to its constructed
Volterra equation. This supplies uniqueness independently of the construction. -/
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

/-- The terminal normalization fixes the empty component as the actual
weighted primitive, for every bounded weighted nonempty component. -/
theorem emptyComponent_eq_of_ode (e : K → ℂ)
    (Y0 : Tail R →ᵇ (K → ℂ)) (Z : Tail R →ᵇ (J → ℂ))
    (hlim : Tendsto Y0 atTop (𝓝 e))
    (h0 : ∀t : Tail R,R<t.val → HasDerivAt (tailExtension Y0)
      (t.val⁻¹ • C01 t (boundedUnweight hR Z t)) t.val) :
    Y0=coupledEmptyComponent hR C01 e Z := by
  let q := complexBoundedCoefficientOperator C01 Z
  let f := boundedUnweight hR (boundedUnweight hR q)
  have hlim' : Tendsto (tailExtension Y0) atTop (𝓝 e) := by
    apply (tendsto_comp_val_Ici_atTop (a:=R)).mp
    exact hlim.congr (fun t => (tailExtension_apply Y0 t).symm)
  have hd (s : ℝ) (hs : R<s) : HasDerivAt (tailExtension Y0) (tailExtension f s) s := by
    have hh := h0 ⟨s,hs.le⟩ hs
    change HasDerivAt (tailExtension Y0) (tailExtension f (⟨s,hs.le⟩ : Tail R).val) s
    rw [tailExtension_apply]
    convert hh using 1
    simp only [f,q,boundedUnweight_apply,complexBoundedCoefficientOperator_apply,
      ContinuousLinearMap.map_smul_of_tower]
  apply BoundedContinuousFunction.ext
  intro t
  have he := solution_eq_terminal_tail (tailExtension Y0) (tailExtension f) e hd
    (integrable_doubleUnweight_tail hR q) hlim' t.property
  rw [tailExtension_apply] at he
  change Y0 t=e+boundedUnweight hR (complexPrimitiveOperator hR q) t
  rw [unweight_complexPrimitive_eq_tail]
  exact he

/-- Every normalized bounded-weight solution of the actual radial ODE
satisfies the genuine free-diagonal coupled Volterra equation. -/
theorem coupledVolterra_equation_of_ode (ha : 0<a) (lam : J → ℂ)
    (hlam : ∀i,a≤(lam i).re) (e : K → ℂ)
    (Y0 : Tail R →ᵇ (K → ℂ)) (Z : Tail R →ᵇ (J → ℂ))
    (hlim : Tendsto Y0 atTop (𝓝 e))
    (h0 : ∀t : Tail R,R<t.val → HasDerivAt (tailExtension Y0)
      (t.val⁻¹ • C01 t (boundedUnweight hR Z t)) t.val)
    (h1 : ∀t : Tail R,R<t.val → HasDerivAt (tailExtension (boundedUnweight hR Z))
      (complexDiagonalOperator lam (boundedUnweight hR Z t)+N t (boundedUnweight hR Z t)+
        t.val⁻¹ • (C10 t (Y0 t)+C11 t (boundedUnweight hR Z t))) t.val) :
    Z=freeForcingOperator hR ha lam hlam
        (complexBoundedCoefficientOperator N Z+
          complexBoundedCoefficientOperator C10 (BoundedContinuousFunction.const _ e))+
      freeRemainderOperator hR ha lam hlam
        (complexBoundedCoefficientOperator C10
          (complexPrimitiveOperator hR (complexBoundedCoefficientOperator C01 Z))+
          complexBoundedCoefficientOperator C11 Z) := by
  have hY0 := emptyComponent_eq_of_ode hR C01 e Y0 Z hlim h0
  let f := complexBoundedCoefficientOperator N Z+
    complexBoundedCoefficientOperator C10 (BoundedContinuousFunction.const _ e)
  let g := complexBoundedCoefficientOperator C10
    (complexPrimitiveOperator hR (complexBoundedCoefficientOperator C01 Z))+
    complexBoundedCoefficientOperator C11 Z
  have hs : boundedUnweight hR (f+boundedUnweight hR g)=coupledFullSource hR N C01 C10 C11 e Z := by
    apply BoundedContinuousFunction.ext
    intro s
    simp only [f,g,coupledFullSource,coupledEmptyComponent,boundedUnweight_apply,
      complexBoundedCoefficientOperator_apply,BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.const_apply,map_add,ContinuousLinearMap.map_smul_of_tower,smul_add,add_assoc]
  have hd (s : ℝ) (hst : R<s) :
      HasDerivAt (tailExtension (boundedUnweight hR Z))
        (complexDiagonalOperator lam (tailExtension (boundedUnweight hR Z) s)+
          tailExtension (coupledFullSource hR N C01 C10 C11 e Z) s) s := by
    have hh := h1 ⟨s,hst.le⟩ hst
    rw [hY0] at hh
    change HasDerivAt (tailExtension (boundedUnweight hR Z))
      (complexDiagonalOperator lam (tailExtension (boundedUnweight hR Z) (⟨s,hst.le⟩ : Tail R).val)+
        tailExtension (coupledFullSource hR N C01 C10 C11 e Z) (⟨s,hst.le⟩ : Tail R).val) s
    rw [tailExtension_apply,tailExtension_apply]
    simpa only [coupledFullSource,BoundedContinuousFunction.add_apply,
      complexBoundedCoefficientOperator_apply,boundedUnweight_apply,add_assoc] using hh
  have he : Z=freeForcingOperator hR ha lam hlam (f+boundedUnweight hR g) := by
    apply BoundedContinuousFunction.ext
    intro t
    have hy := bounded_vector_solution_eq_freeBackward ha lam hlam
      (tailExtension (boundedUnweight hR Z))
      (tailExtension (coupledFullSource hR N C01 C10 C11 e Z)) hd t.property
    rw [tailExtension_apply,←hs,←unweight_freeForcing_eq_backward hR ha lam hlam] at hy
    have hh := congrArg (fun v : J → ℂ => t.val • v) hy
    simpa only [boundedUnweight_apply,smul_smul,mul_inv_cancel₀ (hR.trans_le t.property).ne',one_smul] using hh
  calc
    Z=freeForcingOperator hR ha lam hlam (f+boundedUnweight hR g) := he
    _=freeForcingOperator hR ha lam hlam f+freeRemainderOperator hR ha lam hlam g := by
      rw [map_add,freeRemainder_eq_forcing_unweight]
    _=_ := rfl

/-- The actual normalized radial ODE has at most one bounded weighted
solution, since its true integral equation has the finite-inverse fixed point. -/
theorem coupledRadialODE_unique (ha : 0<a) (lam : J → ℂ)
    (hlam : ∀i,a≤(lam i).re) (e : K → ℂ)
    (Y0 : Tail R →ᵇ (K → ℂ)) (Z : Tail R →ᵇ (J → ℂ))
    (hlim : Tendsto Y0 atTop (𝓝 e))
    (h0 : ∀t : Tail R,R<t.val → HasDerivAt (tailExtension Y0)
      (t.val⁻¹ • C01 t (boundedUnweight hR Z t)) t.val)
    (h1 : ∀t : Tail R,R<t.val → HasDerivAt (tailExtension (boundedUnweight hR Z))
      (complexDiagonalOperator lam (boundedUnweight hR Z t)+N t (boundedUnweight hR Z t)+
        t.val⁻¹ • (C10 t (Y0 t)+C11 t (boundedUnweight hR Z t))) t.val)
    (H : ℕ)
    (hN : ((freeForcingOperator hR ha lam hlam).comp (complexBoundedCoefficientOperator N))^H=0)
    (hsmall : ‖triangularInverse ((freeForcingOperator hR ha lam hlam).comp
        (complexBoundedCoefficientOperator N)) H*
      coupledVolterraRemainder (freeRemainderOperator hR ha lam hlam)
        (complexPrimitiveOperator (E:=K → ℂ) hR) (complexBoundedCoefficientOperator C01)
        (complexBoundedCoefficientOperator C10) (complexBoundedCoefficientOperator C11)‖<1) :
    Z=coupledVolterraSolution (freeForcingOperator hR ha lam hlam)
      (freeRemainderOperator hR ha lam hlam) (complexPrimitiveOperator (E:=K → ℂ) hR)
      (complexBoundedCoefficientOperator N) (complexBoundedCoefficientOperator C01)
      (complexBoundedCoefficientOperator C10) (complexBoundedCoefficientOperator C11)
      (BoundedContinuousFunction.const _ e) H := by
  apply coupledVolterraSolution_unique _ _ _ _ _ _ _ _ _ hN hsmall Z
  exact coupledVolterra_equation_of_ode hR N C01 C10 C11 ha lam hlam e Y0 Z hlim h0 h1

end BourgadeHuang.CMS
