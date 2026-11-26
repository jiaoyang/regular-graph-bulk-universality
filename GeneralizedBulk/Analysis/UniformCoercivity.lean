import Mathlib

/-! Compact parameter families of finite-dimensional admissible quadratic forms. -/
noncomputable section
open scoped Topology

namespace GeneralizedBulk.Analysis

/-- Pointwise strictness upgrades to a uniform positive gap. Admissibility
may vary with the parameter: only its closed graph and linearity are used. -/
theorem uniform_coercivity_of_compact
    {P E : Type*} [TopologicalSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : Set P) (hK : IsCompact K) (S : P → Submodule ℝ E)
    (hclosed : IsClosed {z : P × E | z.2 ∈ S z.1})
    (q : P → E → ℝ) (hq : Continuous (fun z : P × E => q z.1 z.2))
    (hhom : ∀ p t x, q p (t • x) = t ^ 2 * q p x)
    (hnonneg : ∀ p ∈ K, ∀ x ∈ S p, 0 ≤ q p x)
    (hkernel : ∀ p ∈ K, ∀ x ∈ S p, q p x = 0 → x = 0) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ p ∈ K, ∀ x ∈ S p, kappa * ‖x‖ ^ 2 ≤ q p x := by
  letI : ProperSpace E := FiniteDimensional.proper ℝ E
  let A : Set (P × E) := {z | z.1 ∈ K ∧ z.2 ∈ S z.1 ∧ ‖z.2‖ = 1}
  have hA : IsCompact A := by
    have heq : A = (K ×ˢ Metric.sphere (0 : E) 1) ∩ {z | z.2 ∈ S z.1} := by
      ext z
      simp only [A, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod,
        Metric.mem_sphere, dist_zero_right]
      tauto
    rw [heq]
    exact (hK.prod (isCompact_sphere (0 : E) 1)).inter_right hclosed
  have hqzero (p : P) : q p 0 = 0 := by simpa using hhom p 0 (0 : E)
  have hnormalize (p : P) (hp : p ∈ K) (x : E) (hx : x ∈ S p) (hx0 : x ≠ 0) :
      (p, ‖x‖⁻¹ • x) ∈ A := by
    refine ⟨hp, (S p).smul_mem _ hx, ?_⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)]
  by_cases hne : A.Nonempty
  · obtain ⟨z, hz, hmin⟩ := hA.exists_isMinOn hne hq.continuousOn
    have hz0 : q z.1 z.2 ≠ 0 := by
      intro h
      have hv := hkernel z.1 hz.1 z.2 hz.2.1 h
      have hh := hz.2.2
      rw [hv, norm_zero] at hh
      norm_num at hh
    refine ⟨q z.1 z.2, lt_of_le_of_ne (hnonneg z.1 hz.1 z.2 hz.2.1) hz0.symm, ?_⟩
    intro p hp x hx
    by_cases hx0 : x = 0
    · subst x
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        mul_zero, hqzero, le_refl]
    · have hm := hmin (hnormalize p hp x hx hx0)
      change q z.1 z.2 ≤ q p (‖x‖⁻¹ • x) at hm
      rw [hhom] at hm
      have hmul := mul_le_mul_of_nonneg_left hm (sq_nonneg ‖x‖)
      have heq : ‖x‖ ^ 2 * (‖x‖⁻¹ ^ 2 * q p x) = q p x := by
        field_simp [norm_ne_zero_iff.mpr hx0]
      rw [heq] at hmul
      simpa only [mul_comm] using hmul
  · refine ⟨1, by norm_num, ?_⟩
    intro p hp x hx
    by_cases hx0 : x = 0
    · subst x
      simp [hqzero]
    · exact (hne ⟨(p, ‖x‖⁻¹ • x), hnormalize p hp x hx hx0⟩).elim

end GeneralizedBulk.Analysis
