import GeneralizedBulk.Entropy.ChannelFrames

/-! Actual orthogonal endpoint reversal in the fixed whitened star space. -/
noncomputable section
namespace GeneralizedBulk.Entropy.Channel

theorem root_decomposition (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) (i : Fin d) :
    rootVector d = alpha c • directionA d hd c i + beta c • directionB d hd c i := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · change 1 = alpha c * alpha c + beta c * beta c
    nlinarith [alpha_sq_add_beta_sq c hc]
  · change (0 : Transverse d) = alpha c • (-(beta c) • simplex d hd i) +
      beta c • (alpha c • simplex d hd i)
    rw [smul_smul, smul_smul, ← add_smul]
    have hs : alpha c * -(beta c) + beta c * alpha c = 0 := by ring
    rw [hs, zero_smul]

theorem leaf_decomposition (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) (i : Fin d) :
    leafVector d hd c (rho c) i = beta c • directionA d hd c i + alpha c • directionB d hd c i := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · change c * 1 + rho c * 0 = beta c * alpha c + alpha c * beta c
    nlinarith [two_alpha_mul_beta c hc]
  · change c • (0 : Transverse d) + rho c • simplex d hd i =
      beta c • (-(beta c) • simplex d hd i) + alpha c • (alpha c • simplex d hd i)
    simp only [smul_zero, zero_add, smul_smul, ← add_smul]
    congr 1
    nlinarith [alpha_sq_sub_beta_sq c hc]

/-- Orthogonal reflection exchanging the two adapted endpoint directions. -/
def endpointReversal (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (i : Fin d) :
    WhiteStar d ≃ₗᵢ[ℝ] WhiteStar d :=
  Submodule.reflection (ℝ ∙ (directionA d hd c i - directionB d hd c i))ᗮ

theorem endpointReversal_involutive (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (i : Fin d) :
    Function.Involutive (endpointReversal d hd c i) := Submodule.reflection_involutive _

@[simp] theorem endpointReversal_directionA (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) (i : Fin d) :
    endpointReversal d hd c i (directionA d hd c i) = directionB d hd c i := by
  apply Submodule.reflection_sub
  have ha := directionA_norm_sq d hd c hc i
  have hb := directionB_norm_sq d hd c hc i
  nlinarith [norm_nonneg (directionA d hd c i), norm_nonneg (directionB d hd c i)]

@[simp] theorem endpointReversal_directionB (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) (i : Fin d) :
    endpointReversal d hd c i (directionB d hd c i) = directionA d hd c i := by
  have h := endpointReversal_involutive d hd c i (directionA d hd c i)
  rwa [endpointReversal_directionA d hd c hc i] at h

/-- The orthogonal action really exchanges physical root and leaf observables. -/
@[simp] theorem endpointReversal_root (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) (i : Fin d) :
    endpointReversal d hd c i (rootVector d) = leafVector d hd c (rho c) i := by
  rw [root_decomposition d hd c hc i]
  simp only [map_add, map_smul, endpointReversal_directionA d hd c hc i,
    endpointReversal_directionB d hd c hc i]
  rw [leaf_decomposition d hd c hc i]
  abel

@[simp] theorem endpointReversal_leaf (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) (i : Fin d) :
    endpointReversal d hd c i (leafVector d hd c (rho c) i) = rootVector d := by
  have h := endpointReversal_involutive d hd c i (rootVector d)
  rwa [endpointReversal_root d hd c hc i] at h

/-- Endpoint reversal fixes every vector perpendicular to the edge observation. -/
theorem endpointReversal_fixed_of_projection_zero (d : ℕ) (hd : 2 ≤ d) (c : ℝ)
    (i : Fin d) (y : WhiteStar d) (hy : edgeProjection d hd i y = 0) :
    endpointReversal d hd c i y = y := by
  apply Submodule.reflection_mem_subspace_eq_self
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left,
    real_inner_comm (directionA d hd c i - directionB d hd c i) y, inner_sub_left,
    directionA_inner, directionB_inner]
  have hy0 : y.fst = 0 := by simpa using congrArg (fun z : WhiteStar d => z.fst) hy
  have hys : (@inner ℝ (Transverse d) _ (simplex d hd i) y.snd) • simplex d hd i = 0 := by
    simpa using congrArg (fun z : WhiteStar d => z.snd) hy
  have hsi : @inner ℝ (Transverse d) _ (simplex d hd i) y.snd = 0 := by
    rcases smul_eq_zero.mp hys with hs | hs
    · exact hs
    · have hn := simplex_norm_sq d hd i
      rw [hs, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hn
      norm_num at hn
  simp [hy0, hsi]

end GeneralizedBulk.Entropy.Channel
