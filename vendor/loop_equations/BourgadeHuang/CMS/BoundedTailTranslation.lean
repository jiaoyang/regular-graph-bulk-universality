import BourgadeHuang.CMS.ComplexMatrixCoefficients
import BourgadeHuang.CMS.VolterraEquation

/-! Bounded translation and degree rescaling on the half-line. These actual
operators transport the normalized weighted radial solution to a later base point. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.CMS
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
variable {R h : ℝ}

/-- Positive translation preserves the fixed half-line. -/
def translateTail (hh : 0≤h) : C(Tail R,Tail R) where
  toFun t := ⟨t.val+h,le_add_of_nonneg_right hh |>.trans' t.property⟩
  continuous_toFun := (continuous_subtype_val.add continuous_const).subtype_mk _

@[simp] theorem translateTail_val (hh : 0≤h) (t : Tail R) :
    (translateTail hh t).val=t.val+h := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Precomposition by positive translation is a genuine contraction. -/
def translateTailOperator (hh : 0≤h) : (Tail R →ᵇ E) →L[ℂ] (Tail R →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := fun f => f.compContinuous (translateTail hh)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 (by
        intro f
        simpa only [one_mul] using (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
          (fun t => f.norm_coe_le_norm (translateTail hh t)))

@[simp] theorem translateTailOperator_apply (hh : 0≤h) (f : Tail R →ᵇ E) (t : Tail R) :
    translateTailOperator hh f t=f (translateTail hh t) := rfl

/-- The ratios used in radial degree rescaling lie in the closed unit interval. -/
theorem tail_scale_mem_Icc (hR : 0<R) (hh : 0≤h) (t : Tail R) :
    t.val/(t.val+h)∈Icc (0:ℝ) 1 := by
  have ht := hR.trans_le t.property
  exact ⟨div_nonneg ht.le (by linarith),(div_le_one (by linarith)).mpr (by linarith)⟩

/-- Exact scalar degree correction as a bounded continuous function. -/
def tailScalePower (hR : 0<R) (hh : 0≤h) (n : ℕ) : Tail R →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => ((t.val/(t.val+h):ℝ):ℂ)^n)
    (((Complex.continuous_ofReal.comp (continuous_subtype_val.div
      (continuous_subtype_val.add continuous_const) (fun t => by
        have ht := hR.trans_le t.property
        linarith))).pow n)) 1 (by
      intro t
      rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (tail_scale_mem_Icc hR hh t).1]
      exact pow_le_one₀ (tail_scale_mem_Icc hR hh t).1 (tail_scale_mem_Icc hR hh t).2)

@[simp] theorem tailScalePower_apply (hR : 0<R) (hh : 0≤h) (n : ℕ) (t : Tail R) :
    tailScalePower hR hh n t=((t.val/(t.val+h):ℝ):ℂ)^n := rfl

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Degree-corrected positive translation of the actual weighted vector. -/
def translateWeighted (hR : 0<R) (hh : 0≤h) (degree : J → ℕ)
    (Z : Tail R →ᵇ (J → ℂ)) : Tail R →ᵇ (J → ℂ) :=
  complexBoundedCoefficientOperator
    (complexBoundedMatrix (fun i j => if i=j then tailScalePower hR hh (degree i+1) else 0))
      (translateTailOperator hh Z)

@[simp] theorem translateWeighted_apply (hR : 0<R) (hh : 0≤h) (degree : J → ℕ)
    (Z : Tail R →ᵇ (J → ℂ)) (t : Tail R) (i : J) :
    translateWeighted hR hh degree Z t i=
      ((t.val/(t.val+h):ℝ):ℂ)^(degree i+1)*Z (translateTail hh t) i := by
  simp only [translateWeighted,complexBoundedCoefficientOperator_apply,complexBoundedMatrix_apply,
    translateTailOperator_apply]
  rw [Finset.sum_eq_single i]
  · simp only [if_true,tailScalePower_apply]
  · intro j hj hji
    rw [if_neg (Ne.symm hji)]
    simp
  · simp

/-- Removing one radial weight leaves exactly the degree rescaling. -/
theorem unweight_translateWeighted (hR : 0<R) (hh : 0≤h) (degree : J → ℕ)
    (Z : Tail R →ᵇ (J → ℂ)) (t : Tail R) (i : J) :
    boundedUnweight hR (translateWeighted hR hh degree Z) t i=
      ((t.val/(t.val+h):ℝ):ℂ)^degree i*
        boundedUnweight hR Z (translateTail hh t) i := by
  simp only [boundedUnweight_apply,Pi.smul_apply,translateWeighted_apply,
    translateTail_val,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_div,Complex.ofReal_add,pow_succ]
  have ht : (t.val:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hR.trans_le t.property).ne'
  have hs : ((t.val:ℂ)+(h:ℂ))≠0 := by
    rw [←Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (by have hp:=hR.trans_le t.property; linarith)
  field_simp
  ring

/-- Translation preserves the terminal normalization. -/
theorem tendsto_translateTail_atTop (hh : 0≤h) :
    Tendsto (translateTail (R:=R) hh) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with t ht
  exact ht.trans (le_add_of_nonneg_right hh)

end BourgadeHuang.CMS
