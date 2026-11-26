import GeneralizedBulk.Entropy.HermiteCompleteness

/-! Actual homogeneous projections, commutation with degree-preserving Gaussian
operators, and convergent quadratic-channel energy expansions. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite
variable (I : Type*) [Fintype I] [DecidableEq I]

def chaosProjection (n : ℕ) : Lp ℝ 2 (standardGaussian I) →L[ℝ] fullChaosSpace I n :=
  (show Lp ℝ 2 (standardGaussian I) →ₗ[ℝ] fullChaosSpace I n from
    { toFun := fun f => chaosComponent I f n
      map_add' := fun f g => congrArg (fun h : lp (fun m : ℕ => fullChaosSpace I m) 2 => h n)
        ((fullChaosRepresentation I).map_add f g)
      map_smul' := fun t f => congrArg (fun h : lp (fun m : ℕ => fullChaosSpace I m) 2 => h n)
        ((fullChaosRepresentation I).map_smul t f) }).mkContinuous 1
    (fun f => by simpa only [one_mul, (fullChaosRepresentation I).norm_map] using
      lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (fullChaosRepresentation I f) n)

def wholeChaosProjection (n : ℕ) : Lp ℝ 2 (standardGaussian I) →L[ℝ] Lp ℝ 2 (standardGaussian I) :=
  (fullChaosSpace I n).subtypeL.comp (chaosProjection I n)

@[simp] theorem wholeChaosProjection_apply (n : ℕ) (f : Lp ℝ 2 (standardGaussian I)) :
    wholeChaosProjection I n f = (chaosComponent I f n : Lp ℝ 2 (standardGaussian I)) := rfl

theorem fullChaosRepresentation_coe (n : ℕ) (f : fullChaosSpace I n) :
    fullChaosRepresentation I (f : Lp ℝ 2 (standardGaussian I)) = lp.single 2 n f := by
  apply (fullChaosRepresentation I).symm.injective
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact ((fullChaosHilbertSum I).linearIsometryEquiv_symm_apply_single f).symm

/-- The decomposition components really are the projections onto the proved
homogeneous spaces. -/
theorem wholeChaosProjection_of_mem (n m : ℕ) (f : fullChaosSpace I m) :
    wholeChaosProjection I n (f : Lp ℝ 2 (standardGaussian I)) =
      if n = m then (f : Lp ℝ 2 (standardGaussian I)) else 0 := by
  change ((fullChaosRepresentation I (f : Lp ℝ 2 (standardGaussian I)) n : fullChaosSpace I n) :
    Lp ℝ 2 (standardGaussian I)) = _
  rw [fullChaosRepresentation_coe]
  by_cases hnm : n = m
  · subst n
    simp only [lp.single_apply, Pi.single_eq_same, ↓reduceDIte, ↓reduceIte]
  · simp only [lp.single_apply, Pi.single_eq_of_ne hnm, hnm, ↓reduceDIte, ↓reduceIte]
    rfl

/-- Any actual continuous linear Gaussian operator preserving every full
homogeneous space commutes with the true infinite chaos decomposition. -/
theorem wholeChaosProjection_commute (C : Lp ℝ 2 (standardGaussian I) →L[ℝ] Lp ℝ 2 (standardGaussian I))
    (hC : ∀ n, ∀ f ∈ fullChaosSpace I n, C f ∈ fullChaosSpace I n)
    (n : ℕ) (f : Lp ℝ 2 (standardGaussian I)) :
    wholeChaosProjection I n (C f) = C (wholeChaosProjection I n f) := by
  have hsum := (wholeChaosProjection I n).hasSum (C.hasSum (hasSum_chaosComponents I f))
  have hzero (m : ℕ) (hm : m ≠ n) :
      wholeChaosProjection I n (C (chaosComponent I f m)) = 0 := by
    have h := wholeChaosProjection_of_mem I n m ⟨C (chaosComponent I f m), hC m _ (chaosComponent I f m).property⟩
    simpa only [Ne.symm hm, ↓reduceIte] using h
  have hsingle := hasSum_single n hzero
  have heq := hsum.unique hsingle
  have hfix := wholeChaosProjection_of_mem I n n ⟨C (chaosComponent I f n), hC n _ (chaosComponent I f n).property⟩
  simpa only [↓reduceIte, wholeChaosProjection_apply] using heq.trans hfix

/-- The actual degree component has the defining Hilbert projection pairing. -/
theorem chaosComponent_inner (n : ℕ) (f : Lp ℝ 2 (standardGaussian I)) (g : fullChaosSpace I n) :
    @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (chaosComponent I f n : Lp ℝ 2 (standardGaussian I)) g =
      @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ f g := by
  have h := (fullChaosRepresentation I).inner_map_map f (g : Lp ℝ 2 (standardGaussian I))
  rw [fullChaosRepresentation_coe, lp.inner_single_right] at h
  exact h

theorem chaosComponent_eq_zero_of_inner_zero (n : ℕ) (f : Lp ℝ 2 (standardGaussian I))
    (hf : ∀ g : fullChaosSpace I n, @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ f g = 0) :
    chaosComponent I f n = 0 := by
  have hh := chaosComponent_inner I n f (chaosComponent I f n)
  rw [hf, real_inner_self_eq_norm_sq] at hh
  exact norm_eq_zero.mp (pow_eq_zero hh)

theorem degreeIndexNat_zero (a : DegreeIndex I 0) : degreeIndexNat I a = 0 := by
  funext i
  have hs := degreeIndexNat_sum I a
  have hi := Finset.single_le_sum (s := Finset.univ) (f := degreeIndexNat I a)
    (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  change degreeIndexNat I a i = 0
  omega

/-- Centering removes the degree-zero component of the genuine decomposition. -/
theorem chaosComponent_zero_of_integral_zero (f : Lp ℝ 2 (standardGaussian I))
    (hf : (∫ x, f x ∂standardGaussian I) = 0) : chaosComponent I f 0 = 0 := by
  have hinner : @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ f (multiLp I 0) = 0 := by
    rw [L2.inner_def]
    calc
      _ = ∫ x, f x ∂standardGaussian I := by
        apply integral_congr_ae
        filter_upwards [multiLp_ae I 0] with x hx
        simp only [hx, multiHermite, Pi.zero_apply, hermite_zero, Polynomial.eval_one,
          Finset.prod_const_one, RCLike.inner_apply, conj_trivial, one_mul]
      _ = 0 := hf
  apply chaosComponent_eq_zero_of_inner_zero I 0 f
  intro g
  obtain ⟨coeff, hg⟩ := g.property
  change fullChaosMap I 0 coeff = (g : Lp ℝ 2 (standardGaussian I)) at hg
  rw [← hg]
  change @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ f (chaosLp (degreeIndexNat I) coeff) = 0
  simp only [chaosLp, inner_sum, inner_smul_right, degreeIndexNat_zero I, hinner,
    mul_zero, Finset.sum_const_zero]

/-- Actual channel defect for any finite family of degree-preserving operators. -/
def linearChannelDefect {J : Type*} [Fintype J]
    (C : J → Lp ℝ 2 (standardGaussian I) →L[ℝ] Lp ℝ 2 (standardGaussian I))
    (f : Lp ℝ 2 (standardGaussian I)) : ℝ :=
  ‖f‖ ^ 2 - (1 / 2 : ℝ) * ∑ j, ‖C j f‖ ^ 2

/-- The source's quadratic chaos-energy series actually converges and sums to
the full channel defect; no summability premise is required. -/
theorem hasSum_linearChannelDefect {J : Type*} [Fintype J]
    (C : J → Lp ℝ 2 (standardGaussian I) →L[ℝ] Lp ℝ 2 (standardGaussian I))
    (hC : ∀ j n, ∀ f ∈ fullChaosSpace I n, C j f ∈ fullChaosSpace I n)
    (f : Lp ℝ 2 (standardGaussian I)) :
    HasSum (fun n : ℕ => linearChannelDefect I C (chaosComponent I f n)) (linearChannelDefect I C f) := by
  have hnorm (j : J) : HasSum (fun n : ℕ => ‖C j (chaosComponent I f n)‖ ^ 2) (‖C j f‖ ^ 2) := by
    have h := hasSum_chaosComponent_norm_sq I (C j f)
    have heq (n : ℕ) : ‖C j (chaosComponent I f n)‖ = ‖chaosComponent I (C j f) n‖ := by
      have hh := wholeChaosProjection_commute I (C j) (hC j) n f
      exact congrArg norm hh.symm
    simpa only [← heq] using h
  have hfinite : HasSum (fun n : ℕ => ∑ j : J, ‖C j (chaosComponent I f n)‖ ^ 2)
      (∑ j : J, ‖C j f‖ ^ 2) := by
    exact hasSum_sum (fun j _ => hnorm j)
  exact (hasSum_chaosComponent_norm_sq I f).sub (hfinite.mul_left (1 / 2 : ℝ))

end GeneralizedBulk.Entropy.Hermite
