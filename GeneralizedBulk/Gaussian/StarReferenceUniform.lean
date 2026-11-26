import GeneralizedBulk.Gaussian.StarCovariancePositive
import GeneralizedBulk.Analysis.UniformCoercivity

/-! A uniform positive covariance floor for the actual full star reference on compact bulk sets. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Gaussian
open GeneralizedBulk.Entropy.Channel GeneralizedBulk.External.RegularSpectralData GeneralizedBulk.Analysis

def starReferenceCovariance (d : ℕ) (E : ℝ) : Matrix (Fin (d+1)) (Fin (d+1)) ℝ :=
  starWaveCovariance d E + starNormalProjection d E

theorem continuous_starReferenceCovariance (d : ℕ) (hd : 0 < d) : Continuous (starReferenceCovariance d) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hn (k : Fin (d+1)) : Continuous (fun E => normalizedStarNormal d E k) := by
    unfold normalizedStarNormal
    have hbase : Continuous (fun E : ℝ => entropyStarNormal (d := d) E k) := by
      refine Fin.cases ?_ (fun l => ?_) k <;> simp only [entropyStarNormal, Fin.cases_zero, Fin.cases_succ] <;> fun_prop
    exact hbase.div (by fun_prop) (fun E => ne_of_gt (Real.sqrt_pos.mpr
      (add_pos_of_pos_of_nonneg (Nat.cast_pos.mpr hd) (sq_nonneg E))))
  have hs : Continuous (fun E => starWaveCovariance d E i j) := by
    refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j <;>
      simp only [starWaveCovariance, Fin.cases_zero, Fin.cases_succ]
    all_goals first | fun_prop | (split_ifs <;> fun_prop)
  exact hs.add ((hn i).mul (hn j))

theorem starReference_uniform_positive_floor (d : ℕ) (hd : 2 ≤ d) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K, |E| < d) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ E ∈ K, ∀ x : Fin (d+1) → ℝ,
      kappa * (∑ i, x i ^ 2) ≤ dotProduct x ((starReferenceCovariance d E).mulVec x) := by
  let V := EuclideanSpace ℝ (Fin (d+1))
  let q := fun E (x : V) => dotProduct (fun i => x i) ((starReferenceCovariance d E).mulVec (fun i => x i))
  have hC := continuous_starReferenceCovariance d (by omega : 0 < d)
  have hCij (i j : Fin (d+1)) : Continuous (fun E => starReferenceCovariance d E i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp hC)
  have hq : Continuous (fun z : ℝ × V => q z.1 z.2) := by
    dsimp [q]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    fun_prop
  have hhom (E t : ℝ) (x : V) : q E (t • x) = t ^ 2 * q E x := by
    dsimp only [V] at x ⊢
    dsimp [q]
    simp only [PiLp.smul_apply, smul_eq_mul, dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hn (E : ℝ) (hE : E ∈ K) (x : V) : 0 ≤ q E x := by
    have hp := (starWave_add_normal_posDef d hd E (hbulk E hE)).posSemidef.2 (fun i => x i)
    simpa only [star_trivial] using hp
  have hk (E : ℝ) (hE : E ∈ K) (x : V) (hx : q E x = 0) : x = 0 := by
    by_contra hh
    have hx' : (fun i : Fin (d+1) => x i) ≠ (0 : Fin (d+1) → ℝ) := by
      intro ht
      apply hh
      exact (WithLp.equiv 2 _).injective ht
    have hp := (starWave_add_normal_posDef d hd E (hbulk E hE)).2 (fun i => x i) hx'
    change 0 < q E x at hp
    linarith
  obtain ⟨k,hkpos,hkbound⟩ := uniform_coercivity_of_compact K hK (fun _ => (⊤ : Submodule ℝ V))
    (by simpa only [Submodule.mem_top, Set.setOf_true] using isClosed_univ) q hq hhom
    (fun E hE x _ => hn E hE x) (fun E hE x _ hx => hk E hE x hx)
  refine ⟨k,hkpos,fun E hE x => ?_⟩
  have hh := hkbound E hE ((WithLp.equiv 2 _).symm x) (Submodule.mem_top)
  have hnorm : ‖(WithLp.equiv 2 (Fin (d+1) → ℝ)).symm x‖ ^ 2 = ∑ i, x i ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial, pow_two]
    rfl
  simpa only [hnorm] using hh

end GeneralizedBulk.Gaussian
