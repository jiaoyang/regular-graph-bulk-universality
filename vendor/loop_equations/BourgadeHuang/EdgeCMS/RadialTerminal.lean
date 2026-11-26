import BourgadeHuang.EdgeCMS.BoundedRadial
import BourgadeHuang.CMS.CoupledODERepresentation

/-! The terminal functional is constructed from the actual bounded radial ODE.
Its kernel is proved zero by the checked backward-integral uniqueness theorem. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.EdgeCMS
open CMS
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option linter.unusedSectionVars false

section TerminalMap
variable {V E T : Type*} [AddCommGroup V] [Module ℂ V]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace T] {l : Filter T} [NeBot l]

/-- Limits of an actual linear family form a linear map. -/
def terminalLinearMap (Y : V →ₗ[ℂ] (T →ᵇ E))
    (h : ∀ v, ∃ e, Tendsto (Y v) l (𝓝 e)) : V →ₗ[ℂ] E where
  toFun v := Classical.choose (h v)
  map_add' v w := by
    have hv := Classical.choose_spec (h v)
    have hw := Classical.choose_spec (h w)
    apply tendsto_nhds_unique (Classical.choose_spec (h (v + w)))
    simpa only [map_add, BoundedContinuousFunction.coe_add, Pi.add_apply] using hv.add hw
  map_smul' c v := by
    have hv := Classical.choose_spec (h v)
    apply tendsto_nhds_unique (Classical.choose_spec (h (c • v)))
    simpa only [map_smul, BoundedContinuousFunction.coe_smul, Pi.smul_apply] using hv.const_smul c

theorem terminalLinearMap_tendsto (Y : V →ₗ[ℂ] (T →ᵇ E))
    (h : ∀ v, ∃ e, Tendsto (Y v) l (𝓝 e)) (v : V) :
    Tendsto (Y v) l (𝓝 (terminalLinearMap Y h v)) := Classical.choose_spec (h v)
end TerminalMap

section RadialKernel
variable {J K : Type*} [Fintype J] [DecidableEq J] [Fintype K]
  {R a : ℝ} (hR : 0 < R) (ha : 0 < a)
  (lam : J → ℂ) (hlam : ∀ i, a ≤ (lam i).re)
  (degree : J → ℕ) (N : Tail R →ᵇ ((J → ℂ) →L[ℂ] (J → ℂ)))
  (hN : StrictlyLowerDegree degree N) (H : ℕ) (hH : ∀ i, degree i < H)
  (C01 : Tail R →ᵇ ((J → ℂ) →L[ℂ] (K → ℂ)))
  (C10 : Tail R →ᵇ ((K → ℂ) →L[ℂ] (J → ℂ)))
  (C11 : Tail R →ᵇ ((J → ℂ) →L[ℂ] (J → ℂ)))

include degree hN hH

/-- Zero terminal data force both actual bounded radial components to vanish. -/
theorem bounded_radial_zero_of_terminal_zero
    (Y0 : Tail R →ᵇ (K → ℂ)) (Y1 : Tail R →ᵇ (J → ℂ))
    (h0 : ∀ t : Tail R, R < t.val → HasDerivAt (tailExtension Y0)
      (t.val⁻¹ • C01 t (Y1 t)) t.val)
    (h1 : ∀ t : Tail R, R < t.val → HasDerivAt (tailExtension Y1)
      (complexDiagonalOperator lam (Y1 t) + N t (Y1 t) +
        t.val⁻¹ • (C10 t (Y0 t) + C11 t (Y1 t))) t.val)
    (hlim : Tendsto Y0 atTop (𝓝 0))
    (hsmall : ‖triangularInverse ((freeForcingOperator hR ha lam hlam).comp
        (complexBoundedCoefficientOperator N)) H *
      coupledVolterraRemainder (freeRemainderOperator hR ha lam hlam)
        (complexPrimitiveOperator (E := K → ℂ) hR) (complexBoundedCoefficientOperator C01)
        (complexBoundedCoefficientOperator C10) (complexBoundedCoefficientOperator C11)‖ < 1) :
    Y0 = 0 ∧ Y1 = 0 := by
  obtain ⟨Z, e, hZ, he⟩ := bounded_coupled_radial_has_weight_and_limit
    hR ha lam hlam degree N hN H hH C01 C10 C11 Y0 Y1 h0 h1
  have h0' : ∀ t : Tail R, R < t.val → HasDerivAt (tailExtension Y0)
      (t.val⁻¹ • C01 t (boundedUnweight hR Z t)) t.val := by
    simpa only [← hZ] using h0
  have h1' : ∀ t : Tail R, R < t.val → HasDerivAt (tailExtension (boundedUnweight hR Z))
      (complexDiagonalOperator lam (boundedUnweight hR Z t) + N t (boundedUnweight hR Z t) +
        t.val⁻¹ • (C10 t (Y0 t) + C11 t (boundedUnweight hR Z t))) t.val := by
    simpa only [← hZ] using h1
  have hnil : ((freeForcingOperator hR ha lam hlam).comp (complexBoundedCoefficientOperator N)) ^ H = 0 :=
    strictlyLowerDegree_freeForcing_nilpotent hR ha lam hlam degree N hN H hH
  have huniq := coupledRadialODE_unique hR N C01 C10 C11 ha lam hlam
    (0 : K → ℂ) Y0 Z hlim h0' h1' H hnil hsmall
  have hconst : BoundedContinuousFunction.const (Tail R) (0 : K → ℂ) = 0 := by
    ext t i
    rfl
  have hZ0 : Z = 0 := by
    simpa only [coupledVolterraSolution, triangularAffineFixedPoint, affineFixedPoint,
      hconst, map_zero] using huniq
  have hY0 := emptyComponent_eq_of_ode hR C01 (0 : K → ℂ) Y0 Z hlim h0'
  constructor
  · rw [hY0, hZ0]
    apply BoundedContinuousFunction.ext
    intro t
    simp only [coupledEmptyComponent, map_zero, boundedUnweight_apply,
      BoundedContinuousFunction.add_apply, BoundedContinuousFunction.const_apply,
      BoundedContinuousFunction.coe_zero, Pi.zero_apply, smul_zero, add_zero]
  · rw [hZ, hZ0]
    apply BoundedContinuousFunction.ext
    intro t
    simp only [boundedUnweight_apply, BoundedContinuousFunction.coe_zero, Pi.zero_apply, smul_zero]

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The actual bounded radial equations construct a linear terminal map with
proved zero kernel on radial components. The edge empty sector is `K = Unit`. -/
theorem exists_radial_terminal_linearMap
    (Y0 : V →ₗ[ℂ] (Tail R →ᵇ (K → ℂ)))
    (Y1 : V →ₗ[ℂ] (Tail R →ᵇ (J → ℂ)))
    (h0 : ∀ v, ∀ t : Tail R, R < t.val → HasDerivAt (tailExtension (Y0 v))
      (t.val⁻¹ • C01 t (Y1 v t)) t.val)
    (h1 : ∀ v, ∀ t : Tail R, R < t.val → HasDerivAt (tailExtension (Y1 v))
      (complexDiagonalOperator lam (Y1 v t) + N t (Y1 v t) +
        t.val⁻¹ • (C10 t (Y0 v t) + C11 t (Y1 v t))) t.val)
    (hsmall : ‖triangularInverse ((freeForcingOperator hR ha lam hlam).comp
        (complexBoundedCoefficientOperator N)) H *
      coupledVolterraRemainder (freeRemainderOperator hR ha lam hlam)
        (complexPrimitiveOperator (E := K → ℂ) hR) (complexBoundedCoefficientOperator C01)
        (complexBoundedCoefficientOperator C10) (complexBoundedCoefficientOperator C11)‖ < 1) :
    ∃ L : V →ₗ[ℂ] (K → ℂ),
      (∀ v, Tendsto (Y0 v) atTop (𝓝 (L v))) ∧
      ∀ v, L v = 0 → Y0 v = 0 ∧ Y1 v = 0 := by
  have hlim (v : V) : ∃ e : K → ℂ, Tendsto (Y0 v) atTop (𝓝 e) := by
    obtain ⟨Z, e, hZ, he⟩ := bounded_coupled_radial_has_weight_and_limit
      hR ha lam hlam degree N hN H hH C01 C10 C11 (Y0 v) (Y1 v) (h0 v) (h1 v)
    exact ⟨e, he⟩
  let L := terminalLinearMap Y0 hlim
  refine ⟨L, fun v => terminalLinearMap_tendsto Y0 hlim v, ?_⟩
  intro v hv
  have ht := terminalLinearMap_tendsto Y0 hlim v
  change Tendsto (Y0 v) atTop (𝓝 (L v)) at ht
  rw [hv] at ht
  exact bounded_radial_zero_of_terminal_zero hR ha lam hlam degree N hN H hH C01 C10 C11
    (Y0 v) (Y1 v) (h0 v) (h1 v) ht hsmall

end RadialKernel
end BourgadeHuang.EdgeCMS
