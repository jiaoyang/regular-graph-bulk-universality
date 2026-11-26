import GeneralizedBulk.Entropy.HermiteGaussian

/-! Actual multivariate Gaussian Hermite functions and their L² normalization. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite
open GeneralizedBulk.Gaussian

variable (I : Type*) [Fintype I]

def standardGaussian : Measure (I → ℝ) := Measure.pi (fun _ => standardNormal)

instance : IsProbabilityMeasure (standardGaussian I) := by unfold standardGaussian; infer_instance

def multiHermite (a : I → ℕ) (x : I → ℝ) : ℝ := ∏ i, (hermite (a i)).eval (x i)
def multiFactorial (a : I → ℕ) : ℝ := ∏ i, ((a i).factorial : ℝ)

theorem continuous_multiHermite (a : I → ℕ) : Continuous (multiHermite I a) := by
  unfold multiHermite
  exact continuous_finset_prod _ (fun i _ => (hermite (a i)).continuous.comp (continuous_apply i))

theorem integrable_multiHermite (a : I → ℕ) : Integrable (multiHermite I a) (standardGaussian I) := by
  letI : MeasureSpace ℝ := ⟨standardNormal⟩
  letI : IsProbabilityMeasure (volume : Measure ℝ) := (inferInstance : IsProbabilityMeasure standardNormal)
  simpa only [multiHermite, standardGaussian, volume_pi] using
    Integrable.fintype_prod (fun i : I => integrable_polynomial (hermite (a i)))

theorem integrable_multiHermite_pair (a b : I → ℕ) :
    Integrable (fun x => multiHermite I a x * multiHermite I b x) (standardGaussian I) := by
  letI : MeasureSpace ℝ := ⟨standardNormal⟩
  letI : IsProbabilityMeasure (volume : Measure ℝ) := (inferInstance : IsProbabilityMeasure standardNormal)
  have h := Integrable.fintype_prod (fun i : I => integrable_product (hermite (a i)) (hermite (b i)))
  simpa only [multiHermite, standardGaussian, volume_pi, Finset.prod_mul_distrib] using h

/-- Gaussian orthogonality is an actual Fubini integral, rather than an assumed
inner product on formal Hermite symbols. -/
theorem integral_multiHermite_pair (a b : I → ℕ) :
    (∫ x, multiHermite I a x * multiHermite I b x ∂standardGaussian I) =
      if a = b then multiFactorial I a else 0 := by
  classical
  have hfub : (∫ x, multiHermite I a x * multiHermite I b x ∂standardGaussian I) =
      ∏ i, ∫ t : ℝ, (hermite (a i)).eval t * (hermite (b i)).eval t ∂standardNormal := by
    letI : MeasureSpace ℝ := ⟨standardNormal⟩
    letI : IsProbabilityMeasure (volume : Measure ℝ) := (inferInstance : IsProbabilityMeasure standardNormal)
    simpa only [multiHermite, standardGaussian, volume_pi, Finset.prod_mul_distrib] using
      integral_fintype_prod_eq_prod I (fun i : I => fun t : ℝ => (hermite (a i)).eval t * (hermite (b i)).eval t)
  rw [hfub]
  simp_rw [integral_hermite_pair]
  by_cases hab : a = b
  · subst b
    simp only [↓reduceIte, multiFactorial]
  · simp only [hab, ↓reduceIte]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := Function.ne_iff.mp hab
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem multiHermite_memLp_two (a : I → ℕ) : MemLp (multiHermite I a) 2 (standardGaussian I) := by
  apply (memLp_two_iff_integrable_sq (continuous_multiHermite I a).aestronglyMeasurable).2
  simpa only [pow_two] using integrable_multiHermite_pair I a a

/-- The literal L² representative of the actual multivariate Hermite polynomial. -/
def multiLp (a : I → ℕ) : Lp ℝ 2 (standardGaussian I) :=
  (multiHermite_memLp_two I a).toLp (multiHermite I a)

theorem multiLp_ae (a : I → ℕ) : (multiLp I a : (I → ℝ) → ℝ) =ᵐ[standardGaussian I] multiHermite I a :=
  MemLp.coeFn_toLp _

theorem multiLp_inner (a b : I → ℕ) :
    @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (multiLp I a) (multiLp I b) =
      if a = b then multiFactorial I a else 0 := by
  rw [L2.inner_def]
  have heq : (fun x => @inner ℝ ℝ _ (multiLp I a x) (multiLp I b x)) =ᵐ[standardGaussian I]
      (fun x => multiHermite I a x * multiHermite I b x) := by
    filter_upwards [multiLp_ae I a, multiLp_ae I b] with x ha hb
    simp only [ha, hb, RCLike.inner_apply, conj_trivial]
    ring
  rw [integral_congr_ae heq]
  exact integral_multiHermite_pair I a b

@[simp] theorem multiLp_norm_sq (a : I → ℕ) : ‖multiLp I a‖ ^ 2 = multiFactorial I a := by
  rw [← real_inner_self_eq_norm_sq, multiLp_inner]
  simp

theorem multiFactorial_pos (a : I → ℕ) : 0 < multiFactorial I a := by
  unfold multiFactorial
  apply Finset.prod_pos
  intro i hi
  exact_mod_cast Nat.factorial_pos (a i)

end GeneralizedBulk.Entropy.Hermite
