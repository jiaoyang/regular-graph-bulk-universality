import BourgadeHuang.CMS.BackwardODERepresentation
import BourgadeHuang.CMS.ComplexPrimitiveODE

/-! A bounded solution of the triangular radial system has a bounded weighted
nonempty component and a genuine terminal limit in its empty component. Neither
property is added as a normalization hypothesis. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.EdgeCMS
open CMS
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option linter.unusedSectionVars false

variable {J K : Type*} [Fintype J] [DecidableEq J] [Fintype K]
  {R a : ℝ}

/-- Pointwise strict triangularity in the finite subset-degree filtration. -/
def StrictlyLowerDegree (degree : J → ℕ)
    (N : Tail R →ᵇ ((J → ℂ) →L[ℂ] (J → ℂ))) : Prop :=
  ∀ t i v, (∀ j, degree j < degree i → v j = 0) → N t v i = 0

theorem strictlyLowerDegree_raisesDegree (degree : J → ℕ)
    (N : Tail R →ᵇ ((J → ℂ) →L[ℂ] (J → ℂ)))
    (hN : StrictlyLowerDegree degree N) :
    RaisesDegree degree (complexBoundedCoefficientOperator N) := by
  intro k f hf t i hi
  apply hN t i (f t)
  intro j hj
  exact hf t j (by omega)

theorem strictlyLowerDegree_freeForcing_nilpotent
    (hR : 0 < R) (ha : 0 < a) (lam : J → ℂ) (hlam : ∀ i, a ≤ (lam i).re)
    (degree : J → ℕ) (N : Tail R →ᵇ ((J → ℂ) →L[ℂ] (J → ℂ)))
    (hN : StrictlyLowerDegree degree N) (H : ℕ) (hH : ∀ i, degree i < H) :
    (freeForcingOperator hR ha lam hlam * complexBoundedCoefficientOperator N) ^ H = 0 := by
  apply pow_eq_zero_of_raisesDegree (degree := degree) _ hH
  intro k f hf
  exact freeForcingOperator_vanishesBelow hR ha lam hlam
    (strictlyLowerDegree_raisesDegree degree N hN k f hf)

/-- A bounded homogeneous solution with positive diagonal exponents and a
strictly triangular coupling is zero. This is finite induction, not an assumed
radial uniqueness statement. -/
theorem bounded_homogeneous_triangular_zero
    (ha : 0 < a) (lam : J → ℂ) (hlam : ∀ i, a ≤ (lam i).re)
    (degree : J → ℕ) (N : Tail R →ᵇ ((J → ℂ) →L[ℂ] (J → ℂ)))
    (hN : StrictlyLowerDegree degree N) (Y : Tail R →ᵇ (J → ℂ))
    (hY : ∀ t : Tail R, R < t.val → HasDerivAt (tailExtension Y)
      (complexDiagonalOperator lam (Y t) + N t (Y t)) t.val) : Y = 0 := by
  have hall : ∀ n : ℕ, ∀ i, degree i = n → ∀ t : Tail R, Y t i = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi t
      have hNi (u : Tail R) : N u (Y u) i = 0 := by
        apply hN u i (Y u)
        intro j hj
        exact ih (degree j) (by omega) j rfl u
      let Yi : ℝ →ᵇ ℂ :=
        (ContinuousLinearMap.proj (R := ℂ) i).compLeftContinuousBounded ℝ (tailExtension Y)
      have hd (s : ℝ) (hs : R < s) :
          HasDerivAt Yi (lam i * Yi s + (0 : ℝ →ᵇ ℂ) s) s := by
        have hh := (ContinuousLinearMap.proj (R := ℝ) i).hasFDerivAt.comp_hasDerivAt s
          (hY ⟨s, hs.le⟩ hs)
        have he : tailExtension Y s = Y ⟨s, hs.le⟩ := tailExtension_apply Y ⟨s, hs.le⟩
        convert hh using 1
        simp only [Yi, ContinuousLinearMap.compLeftContinuousBounded_apply,
          ContinuousLinearMap.proj_apply, Pi.add_apply, complexDiagonalOperator_apply,
          BoundedContinuousFunction.coe_zero, Pi.zero_apply, he, hNi, add_zero]
      have he := bounded_solution_eq_backward_integral (lam i)
        (ha.trans_le (hlam i)) Yi 0 hd t.property
      simpa only [Yi, ContinuousLinearMap.compLeftContinuousBounded_apply,
        ContinuousLinearMap.proj_apply, tailExtension_apply,
        BoundedContinuousFunction.coe_zero, Pi.zero_apply, mul_zero, integral_zero, neg_zero] using he
  apply BoundedContinuousFunction.ext
  intro t
  funext i
  exact hall (degree i) i rfl t

/-- Bounded inhomogeneous triangular solutions automatically decay as `1/t`.
The weighted particular solution is built by the finite Volterra inverse. -/
theorem bounded_triangular_solution_has_weight
    (hR : 0 < R) (ha : 0 < a) (lam : J → ℂ) (hlam : ∀ i, a ≤ (lam i).re)
    (degree : J → ℕ) (N : Tail R →ᵇ ((J → ℂ) →L[ℂ] (J → ℂ)))
    (hN : StrictlyLowerDegree degree N) (H : ℕ) (hH : ∀ i, degree i < H)
    (Y f : Tail R →ᵇ (J → ℂ))
    (hY : ∀ t : Tail R, R < t.val → HasDerivAt (tailExtension Y)
      (complexDiagonalOperator lam (Y t) + N t (Y t) + t.val⁻¹ • f t) t.val) :
    ∃ Z : Tail R →ᵇ (J → ℂ), Y = boundedUnweight hR Z := by
  let V := freeForcingOperator hR ha lam hlam
  let B := V * complexBoundedCoefficientOperator N
  have hnil : B ^ H = 0 := strictlyLowerDegree_freeForcing_nilpotent
    hR ha lam hlam degree N hN H hH
  let Z := triangularInverse B H (V f)
  have hz : Z = B Z + V f := by
    have hh := congrArg (fun L : (Tail R →ᵇ (J → ℂ)) →L[ℂ] (Tail R →ᵇ (J → ℂ)) => L (V f))
      (mul_triangularInverse hnil)
    change Z - B Z = V f at hh
    exact (eq_add_of_sub_eq hh).trans (add_comm _ _)
  have hz' : Z = V (complexBoundedCoefficientOperator N Z + f) := by
    rw [map_add]
    exact hz
  let Yhat := boundedUnweight hR Z
  have hhat (t : Tail R) (ht : R < t.val) : HasDerivAt (tailExtension Yhat)
      (complexDiagonalOperator lam (Yhat t) + N t (Yhat t) + t.val⁻¹ • f t) t.val := by
    have hh := hasDerivAt_unweight_freeForcing hR ha lam hlam
      (complexBoundedCoefficientOperator N Z + f) ht
    change HasDerivAt (tailExtension (boundedUnweight hR
      (V (complexBoundedCoefficientOperator N Z + f)))) _ _ at hh
    rw [← hz'] at hh
    simpa only [tailExtension_apply, boundedUnweight_apply,
      BoundedContinuousFunction.add_apply, complexBoundedCoefficientOperator_apply,
      ContinuousLinearMap.map_smul_of_tower, smul_add, add_assoc, Yhat] using hh
  let D := Y - Yhat
  have hD (t : Tail R) (ht : R < t.val) : HasDerivAt (tailExtension D)
      (complexDiagonalOperator lam (D t) + N t (D t)) t.val := by
    convert (hY t ht).sub (hhat t ht) using 1
    simp only [D, BoundedContinuousFunction.sub_apply, map_sub]
    abel
  have hd := bounded_homogeneous_triangular_zero ha lam hlam degree N hN D hD
  refine ⟨Z, ?_⟩
  change Y = Yhat
  exact sub_eq_zero.mp hd

/-- Once the nonempty component is `1/t` times a bounded function, the empty
component has an integrable derivative and therefore an actual terminal limit. -/
theorem bounded_empty_component_has_limit
    (hR : 0 < R) (C01 : Tail R →ᵇ ((J → ℂ) →L[ℂ] (K → ℂ)))
    (Y0 : Tail R →ᵇ (K → ℂ)) (Z : Tail R →ᵇ (J → ℂ))
    (h0 : ∀ t : Tail R, R < t.val → HasDerivAt (tailExtension Y0)
      (t.val⁻¹ • C01 t (boundedUnweight hR Z t)) t.val) :
    ∃ e : K → ℂ, Tendsto Y0 atTop (𝓝 e) := by
  let q := complexBoundedCoefficientOperator C01 Z
  let f := boundedUnweight hR (boundedUnweight hR q)
  have hd (s : ℝ) (hs : s ∈ Ioi R) :
      HasDerivAt (tailExtension Y0) (tailExtension f s) s := by
    have hh := h0 ⟨s, hs.le⟩ hs
    change HasDerivAt (tailExtension Y0) (tailExtension f (⟨s, hs.le⟩ : Tail R).val) s
    rw [tailExtension_apply]
    convert hh using 1
    simp only [f, q, boundedUnweight_apply, complexBoundedCoefficientOperator_apply,
      ContinuousLinearMap.map_smul_of_tower]
  have ht := tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi hd
    (integrable_doubleUnweight_tail hR q)
  refine ⟨limUnder atTop (tailExtension Y0), ?_⟩
  have hcomp := (tendsto_comp_val_Ici_atTop (a := R)).mpr ht
  exact hcomp.congr (fun t => tailExtension_apply Y0 t)

/-- The complete bounded-to-weighted radial reduction, valid for arbitrary
finite-dimensional empty and nonempty sectors. -/
theorem bounded_coupled_radial_has_weight_and_limit
    (hR : 0 < R) (ha : 0 < a) (lam : J → ℂ) (hlam : ∀ i, a ≤ (lam i).re)
    (degree : J → ℕ) (N : Tail R →ᵇ ((J → ℂ) →L[ℂ] (J → ℂ)))
    (hN : StrictlyLowerDegree degree N) (H : ℕ) (hH : ∀ i, degree i < H)
    (C01 : Tail R →ᵇ ((J → ℂ) →L[ℂ] (K → ℂ)))
    (C10 : Tail R →ᵇ ((K → ℂ) →L[ℂ] (J → ℂ)))
    (C11 : Tail R →ᵇ ((J → ℂ) →L[ℂ] (J → ℂ)))
    (Y0 : Tail R →ᵇ (K → ℂ)) (Y1 : Tail R →ᵇ (J → ℂ))
    (h0 : ∀ t : Tail R, R < t.val → HasDerivAt (tailExtension Y0)
      (t.val⁻¹ • C01 t (Y1 t)) t.val)
    (h1 : ∀ t : Tail R, R < t.val → HasDerivAt (tailExtension Y1)
      (complexDiagonalOperator lam (Y1 t) + N t (Y1 t) +
        t.val⁻¹ • (C10 t (Y0 t) + C11 t (Y1 t))) t.val) :
    ∃ (Z : Tail R →ᵇ (J → ℂ)) (e : K → ℂ),
      Y1 = boundedUnweight hR Z ∧ Tendsto Y0 atTop (𝓝 e) := by
  let f := complexBoundedCoefficientOperator C10 Y0 + complexBoundedCoefficientOperator C11 Y1
  obtain ⟨Z, hZ⟩ := bounded_triangular_solution_has_weight hR ha lam hlam
    degree N hN H hH Y1 f h1
  obtain ⟨e, he⟩ := bounded_empty_component_has_limit hR C01 Y0 Z (by simpa only [← hZ] using h0)
  exact ⟨Z, e, hZ, he⟩

end BourgadeHuang.EdgeCMS
