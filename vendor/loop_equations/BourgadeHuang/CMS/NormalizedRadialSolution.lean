import BourgadeHuang.CMS.VolterraEmptyEquation
import BourgadeHuang.CMS.TriangularVolterraODE

/-! A genuine normalized radial solution of the finite triangular system.
The solution is obtained from the constructed Volterra contraction. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace BourgadeHuang.CMS
set_option maxHeartbeats 600000
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Existence with the prescribed normalization and reciprocal decay. The
principal evolution, improper integrals, and differentiability are all
constructed from the bounded triangular coefficients and their spectral gap. -/
theorem exists_normalized_radialSolution
    {R a : ℝ} (hR : 0<R) (ha : 0<a) (lam : J → ℂ)
    (N : Tail R →ᵇ (J → J → ℂ)) (degree : J → ℕ)
    (hN : ∀ x i j, ¬ degree j<degree i → N x i j=0)
    (H : ℕ) (hH : ∀ i, degree i<H) (hlam : ∀ i, 2*a≤(lam i).re)
    (C01 : Tail R →ᵇ ((J → ℂ) →L[ℝ] ℂ))
    (C10 : Tail R →ᵇ (ℂ →L[ℝ] (J → ℂ)))
    (C11 : Tail R →ᵇ ((J → ℂ) →L[ℝ] (J → ℂ)))
    (hsmall : (triangularVolterraData ha lam N H hlam C01 C10 C11).contractionConstant<1) :
    ∃ (Y0 : Tail R →ᵇ ℂ) (Y : Tail R →ᵇ (J → ℂ)) (K : ℝ),
      0≤K ∧ Tendsto Y0 atTop (𝓝 1) ∧ Tendsto Y atTop (𝓝 0) ∧
      (∀ t : Tail R, ‖Y0 t-1‖≤K/t.val ∧ ‖Y t‖≤K/t.val) ∧
      ∀ t : Tail R, R<t.val →
        HasDerivAt (tailExtension Y0) (t.val⁻¹ • C01 t (Y t)) t.val ∧
        HasDerivAt (tailExtension Y)
          (triangularGenerator lam N t.val (Y t)+
            t.val⁻¹ • (C10 t (Y0 t)+C11 t (Y t))) t.val := by
  let D := triangularVolterraData ha lam N H hlam C01 C10 C11
  have hC := triangularDecayConstant_nonneg (J:=J) ha (norm_nonneg N) H
  obtain ⟨Z,hZ,_⟩ := D.existsUnique_fixedPoint hR ha hC hsmall
  let Y0 : Tail R →ᵇ ℂ := BoundedContinuousFunction.const _ 1+
    boundedUnweight hR (D.primitive hR Z)
  let Y : Tail R →ᵇ (J → ℂ) := boundedUnweight hR Z
  let K := max (‖C01‖*‖Z‖) ‖Z‖
  refine ⟨Y0,Y,K,(norm_nonneg Z).trans (le_max_right _ _),?_,?_,?_,?_⟩
  · exact (D.empty_normalization hR Z).1
  · exact tendsto_unweight_zero hR Z
  · intro t
    constructor
    · exact ((D.empty_normalization hR Z).2 t).trans
        (div_le_div_of_nonneg_right (le_max_left _ _) (hR.trans_le t.property).le)
    · exact (norm_unweight_le hR Z t).trans
        (div_le_div_of_nonneg_right (le_max_right _ _) (hR.trans_le t.property).le)
  · intro t ht
    constructor
    · have hd := D.hasDerivAt_emptyComponent hR Z ht
      have he : (fun s => (1:ℂ)+tailExtension (boundedUnweight hR (D.primitive hR Z)) s) =
          tailExtension Y0 := rfl
      rw [he,tailExtension_apply] at hd
      exact hd
    · have hd := hasDerivAt_triangular_fixedPoint hR ha lam N degree hN H hH hlam
        C01 C10 C11 Z hZ ht
      rw [tailExtension_apply,tailExtension_apply] at hd
      exact hd

/-- An explicit sufficiently large starting radius ensures contraction. -/
theorem exists_normalized_radialSolution_of_large_radius
    {R a M : ℝ} (hR : 0<R) (ha : 0<a) (hM : 0≤M) (lam : J → ℂ)
    (N : Tail R →ᵇ (J → J → ℂ)) (degree : J → ℕ)
    (hN : ∀ x i j, ¬ degree j<degree i → N x i j=0)
    (H : ℕ) (hH : ∀ i, degree i<H) (hlam : ∀ i, 2*a≤(lam i).re)
    (C01 : Tail R →ᵇ ((J → ℂ) →L[ℝ] ℂ))
    (C10 : Tail R →ᵇ (ℂ →L[ℝ] (J → ℂ)))
    (C11 : Tail R →ᵇ ((J → ℂ) →L[ℝ] (J → ℂ)))
    (h01 : ‖C01‖≤M) (h10 : ‖C10‖≤M) (h11 : ‖C11‖≤M)
    (hlarge : triangularDecayConstant (J:=J) a ‖N‖ H*a⁻¹*(M*M+M)<R) :
    ∃ (Y0 : Tail R →ᵇ ℂ) (Y : Tail R →ᵇ (J → ℂ)) (K : ℝ),
      0≤K ∧ Tendsto Y0 atTop (𝓝 1) ∧ Tendsto Y atTop (𝓝 0) ∧
      (∀ t : Tail R, ‖Y0 t-1‖≤K/t.val ∧ ‖Y t‖≤K/t.val) ∧
      ∀ t : Tail R, R<t.val →
        HasDerivAt (tailExtension Y0) (t.val⁻¹ • C01 t (Y t)) t.val ∧
        HasDerivAt (tailExtension Y)
          (triangularGenerator lam N t.val (Y t)+
            t.val⁻¹ • (C10 t (Y0 t)+C11 t (Y t))) t.val := by
  apply exists_normalized_radialSolution hR ha lam N degree hN H hH hlam C01 C10 C11
  exact (triangularVolterraData ha lam N H hlam C01 C10 C11).contractionConstant_lt_one_of_radius
    hR ha (triangularDecayConstant_nonneg ha (norm_nonneg N) H) hM h01 h10 h11 hlarge

end BourgadeHuang.CMS
