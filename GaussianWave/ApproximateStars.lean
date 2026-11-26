import GaussianWave.AlmostEigenvectors
import GaussianWave.StarComparison
import GaussianWave.StarCovariancePSD

/-!
# Normalized stars of controlled almost eigenvectors

The sampled law is the actual finite `D.starLaw q`, with arbitrary
orthonormal zero-sum signals `q`. The exact eigenvectors included in `D`
are not used as these signals. Residual contractions are estimated by finite
Cauchy--Schwarz; the covariance limit is a conclusion rather than an input.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace GaussianWave

def finitePairing {ι : Type*} [Fintype ι] (f g : ι → ℝ) : ℝ := ∑ x, f x * g x

lemma finitePairing_add_left {ι : Type*} [Fintype ι] (f g h : ι → ℝ) :
    finitePairing (f + g) h = finitePairing f h + finitePairing g h := by
  simp [finitePairing, add_mul, Finset.sum_add_distrib]

lemma finitePairing_add_right {ι : Type*} [Fintype ι] (f g h : ι → ℝ) :
    finitePairing f (g + h) = finitePairing f g + finitePairing f h := by
  simp [finitePairing, mul_add, Finset.sum_add_distrib]

lemma finitePairing_smul_left {ι : Type*} [Fintype ι] (a : ℝ) (f g : ι → ℝ) :
    finitePairing (fun x => a * f x) g = a * finitePairing f g := by
  simp [finitePairing, Finset.mul_sum, mul_assoc]

lemma finitePairing_smul_right {ι : Type*} [Fintype ι] (a : ℝ) (f g : ι → ℝ) :
    finitePairing f (fun x => a * g x) = a * finitePairing f g := by
  simp [finitePairing, Finset.mul_sum, mul_assoc, mul_left_comm]

lemma finitePairing_comm {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    finitePairing f g = finitePairing g f := by simp [finitePairing, mul_comm]

/-- Finite Cauchy--Schwarz is applied before taking any graph-size limit. -/
lemma finitePairing_sq_le {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    finitePairing f g ^ 2 ≤ squareMass f * squareMass g :=
  Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g

lemma finitePairing_tendsto_zero {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (f g : ∀ n, ι n → ℝ)
    (hh : Tendsto (fun n => squareMass (f n) * squareMass (g n)) atTop (𝓝 0)) :
    Tendsto (fun n => finitePairing (f n) (g n)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he := (tendsto_order.mp hh).2 (ε ^ 2) (sq_pos_of_pos hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero]
  have hc := finitePairing_sq_le (f n) (g n)
  have ht := hN n hn
  nlinarith [abs_nonneg (finitePairing (f n) (g n)), sq_abs (finitePairing (f n) (g n))]

end GaussianWave

namespace GaussianWave.RegularEigenData
variable {d N c k : ℕ} (D : GaussianWave.RegularEigenData d N c)

def adjacencyImage (f : Fin N → ℝ) : Fin N → ℝ :=
  fun v => ∑ w, D.adjacency v w * f w

lemma adjacencyImage_eq_residual (f : Fin N → ℝ) (lam : ℝ) :
    D.adjacencyImage f =
      (fun v => lam * f v) + eigenResidual D.adjacency lam f := by
  funext v
  simp only [adjacencyImage, eigenResidual, Pi.add_apply]
  ring

/-- The generic root--neighbor moment is an adjacency contraction. -/
theorem integral_arbitrary_star_root_neighbor (q : Fin k → Fin N → ℝ)
    (i j : Fin k) (l : Fin d) :
    (∫ x, x (i, 0) * x (j, l.succ) ∂D.starLaw q) =
      finitePairing (q i) (D.adjacencyImage (q j)) / d := by
  classical
  have hP : (Fintype.card (Equiv.Perm (Fin d)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt l.isLt)
  rw [D.integral_star_coordinate_pair]
  simp only [starVertex, Fin.cases_zero, Fin.cases_succ]
  rw [D.sum_star_root_neighbor]
  simp_rw [D.sum_neighbor]
  unfold finitePairing adjacencyImage
  field_simp

/-- The same neighbor position has exactly the root Gram matrix. -/
theorem integral_arbitrary_star_same_neighbor (q : Fin k → Fin N → ℝ)
    (i j : Fin k) (l : Fin d) :
    (∫ x, x (i, l.succ) * x (j, l.succ) ∂D.starLaw q) =
      finitePairing (q i) (q j) := by
  classical
  have hP : (Fintype.card (Equiv.Perm (Fin d)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [D.integral_star_coordinate_pair]
  simp only [starVertex, Fin.cases_succ]
  rw [D.sum_star_neighbor l (fun v => q i v * q j v)]
  unfold finitePairing
  field_simp

lemma arbitrary_neighbor_offdiagonal (q : Fin k → Fin N → ℝ) (i j : Fin k) :
    (∑ v : Fin N, ∑ a : Fin d, ∑ b : Fin d, if a = b then 0 else
      q i (D.neighbor v a) * q j (D.neighbor v b)) =
        finitePairing (D.adjacencyImage (q i)) (D.adjacencyImage (q j)) -
          d * finitePairing (q i) (q j) := by
  simp_rw [sum_offdiagonal_product]
  rw [Finset.sum_sub_distrib, D.sum_neighbor_global (fun v => q i v * q j v)]
  simp_rw [D.sum_neighbor]
  rfl

/-- Distinct leaves involve the adjacency Gram matrix, with the diagonal
neighbor terms subtracted exactly. -/
theorem integral_arbitrary_star_distinct_neighbors (hd : 2 ≤ d)
    (q : Fin k → Fin N → ℝ) (i j : Fin k) (l m : Fin d) (hlm : l ≠ m) :
    (∫ x, x (i, l.succ) * x (j, m.succ) ∂D.starLaw q) =
      (finitePairing (D.adjacencyImage (q i)) (D.adjacencyImage (q j)) -
        d * finitePairing (q i) (q j)) / ((d : ℝ) * (d - 1)) := by
  classical
  have hP : (Fintype.card (Equiv.Perm (Fin d)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  rw [D.integral_star_coordinate_pair]
  simp only [starVertex, Fin.cases_succ]
  rw [D.sum_star_distinct_neighbors hd l m hlm, D.arbitrary_neighbor_offdiagonal]
  field_simp

/-- Root-adjacency contraction expanded with the actual residual. -/
lemma arbitrary_root_adjacency_pair (q : Fin k → Fin N → ℝ)
    (horth : ∀ i j, finitePairing (q i) (q j) = if i = j then 1 else 0)
    (lam : Fin k → ℝ) (i j : Fin k) :
    finitePairing (q i) (D.adjacencyImage (q j)) =
      lam j * (if i = j then 1 else 0) +
        finitePairing (q i) (eigenResidual D.adjacency (lam j) (q j)) := by
  rw [D.adjacencyImage_eq_residual (q j) (lam j), finitePairing_add_right,
    finitePairing_smul_right, horth]

/-- The two-adjacency contraction has three residual error terms. -/
lemma arbitrary_adjacency_pair (q : Fin k → Fin N → ℝ)
    (horth : ∀ i j, finitePairing (q i) (q j) = if i = j then 1 else 0)
    (lam : Fin k → ℝ) (i j : Fin k) :
    finitePairing (D.adjacencyImage (q i)) (D.adjacencyImage (q j)) =
      lam i * lam j * (if i = j then 1 else 0) +
        lam i * finitePairing (q i) (eigenResidual D.adjacency (lam j) (q j)) +
        lam j * finitePairing (eigenResidual D.adjacency (lam i) (q i)) (q j) +
        finitePairing (eigenResidual D.adjacency (lam i) (q i))
          (eigenResidual D.adjacency (lam j) (q j)) := by
  rw [D.adjacencyImage_eq_residual (q i) (lam i),
    D.adjacencyImage_eq_residual (q j) (lam j)]
  simp only [finitePairing_add_left, finitePairing_add_right,
    finitePairing_smul_left, finitePairing_smul_right, horth]
  ring

end GaussianWave.RegularEigenData

namespace GaussianWave

lemma squareMass_of_orthonormal_signal {N k : ℕ} (q : Fin k → Fin N → ℝ)
    (horth : ∀ i j, finitePairing (q i) (q j) = if i = j then 1 else 0) (i : Fin k) :
    squareMass (q i) = 1 := by
  simpa only [squareMass, finitePairing, pow_two, ↓reduceIte] using horth i i

lemma finitePairing_tendsto_zero_of_unit {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (f g : ∀ n, ι n → ℝ) (hf : ∀ n, squareMass (f n) = 1)
    (hg : Tendsto (fun n => squareMass (g n)) atTop (𝓝 0)) :
    Tendsto (fun n => finitePairing (f n) (g n)) atTop (𝓝 0) := by
  apply finitePairing_tendsto_zero f g
  simpa only [hf, one_mul] using hg

/-- Residual size tending to zero and orthonormality imply convergence of the
root-adjacency contraction, with no covariance-limit assumption. -/
theorem almost_star_root_adjacency_tendsto
    {d k : ℕ} (N c : ℕ → ℕ) (D : ∀ n, RegularEigenData d (N n) (c n))
    (q : ∀ n, Fin k → Fin (N n) → ℝ)
    (horth : ∀ n i j, finitePairing (q n i) (q n j) = if i = j then 1 else 0)
    (lam : ℕ → Fin k → ℝ) (E : ℝ)
    (hE : ∀ a, Tendsto (fun n => lam n a) atTop (𝓝 E))
    (hres : ∀ a, Tendsto (fun n =>
      squareMass (eigenResidual (D n).adjacency (lam n a) (q n a))) atTop (𝓝 0))
    (i j : Fin k) :
    Tendsto (fun n => finitePairing (q n i) ((D n).adjacencyImage (q n j))) atTop
      (𝓝 (E * (if i = j then 1 else 0))) := by
  have herr := finitePairing_tendsto_zero_of_unit (fun n => q n i)
    (fun n => eigenResidual (D n).adjacency (lam n j) (q n j))
    (fun n => squareMass_of_orthonormal_signal (q n) (horth n) i) (hres j)
  have heq (n : ℕ) := (D n).arbitrary_root_adjacency_pair (q n) (horth n) (lam n) i j
  simp_rw [heq]
  simpa only [add_zero] using ((hE j).mul_const (if i = j then 1 else 0)).add herr

/-- The adjacency Gram contraction converges by expanding its three residual
errors and bounding each one by finite Cauchy--Schwarz. -/
theorem almost_star_adjacency_pair_tendsto
    {d k : ℕ} (N c : ℕ → ℕ) (D : ∀ n, RegularEigenData d (N n) (c n))
    (q : ∀ n, Fin k → Fin (N n) → ℝ)
    (horth : ∀ n i j, finitePairing (q n i) (q n j) = if i = j then 1 else 0)
    (lam : ℕ → Fin k → ℝ) (E : ℝ)
    (hE : ∀ a, Tendsto (fun n => lam n a) atTop (𝓝 E))
    (hres : ∀ a, Tendsto (fun n =>
      squareMass (eigenResidual (D n).adjacency (lam n a) (q n a))) atTop (𝓝 0))
    (i j : Fin k) :
    Tendsto (fun n => finitePairing ((D n).adjacencyImage (q n i))
      ((D n).adjacencyImage (q n j))) atTop (𝓝 (E ^ 2 * (if i = j then 1 else 0))) := by
  have herr (a b : Fin k) := finitePairing_tendsto_zero_of_unit (fun n => q n a)
    (fun n => eigenResidual (D n).adjacency (lam n b) (q n b))
    (fun n => squareMass_of_orthonormal_signal (q n) (horth n) a) (hres b)
  have hrev : Tendsto (fun n =>
      finitePairing (eigenResidual (D n).adjacency (lam n i) (q n i)) (q n j))
      atTop (𝓝 0) := by
    convert herr j i using 1
    funext n
    exact finitePairing_comm _ _
  have hrr := finitePairing_tendsto_zero
    (fun n => eigenResidual (D n).adjacency (lam n i) (q n i))
    (fun n => eigenResidual (D n).adjacency (lam n j) (q n j))
    (by simpa only [mul_zero] using (hres i).mul (hres j))
  have heq (n : ℕ) := (D n).arbitrary_adjacency_pair (q n) (horth n) (lam n) i j
  simp_rw [heq]
  simpa only [pow_two, mul_zero, add_zero] using
    ((((hE i).mul (hE j)).mul_const (if i = j then 1 else 0)).add
      ((hE i).mul (herr i j)) |>.add ((hE j).mul hrev) |>.add hrr)

/-- Actual finite-star second moments converge to the normalized independent
channel covariance at the common limiting energy. -/
theorem almost_star_covariance_tendsto
    {d k : ℕ} (hd : 2 ≤ d) (N c : ℕ → ℕ)
    (D : ∀ n, RegularEigenData d (N n) (c n))
    (q : ∀ n, Fin k → Fin (N n) → ℝ)
    (horth : ∀ n i j, finitePairing (q n i) (q n j) = if i = j then 1 else 0)
    (lam : ℕ → Fin k → ℝ) (E : ℝ)
    (hE : ∀ a, Tendsto (fun n => lam n a) atTop (𝓝 E))
    (hres : ∀ a, Tendsto (fun n =>
      squareMass (eigenResidual (D n).adjacency (lam n a) (q n a))) atTop (𝓝 0)) :
    ∀ aj bl, Tendsto (fun n =>
      ∫ x, x aj * x bl ∂(D n).starLaw (q n)) atTop
        (𝓝 (jointStarCovariance d k E aj bl)) := by
  have hroot := almost_star_root_adjacency_tendsto N c D q horth lam E hE hres
  have hadj := almost_star_adjacency_pair_tendsto N c D q horth lam E hE hres
  rintro ⟨i, l⟩ ⟨j, m⟩
  refine Fin.cases ?_ (fun l => ?_) l
  · refine Fin.cases ?_ (fun m => ?_) m
    · have heq (n : ℕ) : (∫ x, x (i, 0) * x (j, 0) ∂(D n).starLaw (q n)) =
          if i = j then 1 else 0 := by
        rw [(D n).integral_star_root_pair]
        exact horth n i j
      simp_rw [heq]
      simpa only [jointStarCovariance, RegularEigenData.starWaveCovariance,
        Fin.cases_zero, mul_one] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => if i = j then (1 : ℝ) else 0)
            atTop (𝓝 (if i = j then 1 else 0)))
    · have heq (n : ℕ) := (D n).integral_arbitrary_star_root_neighbor (q n) i j m
      simp_rw [heq]
      convert (hroot i j).div_const (d : ℝ) using 1 ;
        simp only [jointStarCovariance, RegularEigenData.starWaveCovariance,
          Fin.cases_zero, Fin.cases_succ] ; ring_nf
  · refine Fin.cases ?_ (fun m => ?_) m
    · have heq (n : ℕ) :
          (∫ x, x (i, l.succ) * x (j, 0) ∂(D n).starLaw (q n)) =
            finitePairing (q n j) ((D n).adjacencyImage (q n i)) / d := by
        have hcomm : (fun x : (Fin k × Fin (d + 1)) → ℝ =>
            x (i, l.succ) * x (j, 0)) = (fun x => x (j, 0) * x (i, l.succ)) := by
          funext x
          ring
        rw [hcomm, (D n).integral_arbitrary_star_root_neighbor]
      simp_rw [heq]
      convert (hroot j i).div_const (d : ℝ) using 1 ;
        simp only [jointStarCovariance, RegularEigenData.starWaveCovariance,
          Fin.cases_zero, Fin.cases_succ, eq_comm] ; ring_nf
    · by_cases hlm : l = m
      · subst m
        have heq (n : ℕ) :
            (∫ x, x (i, l.succ) * x (j, l.succ) ∂(D n).starLaw (q n)) =
              if i = j then 1 else 0 := by
          rw [(D n).integral_arbitrary_star_same_neighbor]
          exact horth n i j
        simp_rw [heq]
        simpa only [jointStarCovariance, RegularEigenData.starWaveCovariance,
          Fin.cases_succ, ↓reduceIte, mul_one] using
            (tendsto_const_nhds : Tendsto (fun _ : ℕ => if i = j then (1 : ℝ) else 0)
              atTop (𝓝 (if i = j then 1 else 0)))
      · have heq (n : ℕ) :=
          (D n).integral_arbitrary_star_distinct_neighbors hd (q n) i j l m hlm
        simp_rw [heq, horth]
        convert ((hadj i j).sub_const ((d : ℝ) * (if i = j then 1 else 0))).div_const
          ((d : ℝ) * (d - 1)) using 1 ;
            simp only [jointStarCovariance, RegularEigenData.starWaveCovariance,
              Fin.cases_succ, hlm, ↓reduceIte] ; ring_nf

end GaussianWave

namespace GaussianWave.RegularEigenData

/-- Zero sums give exact zero first moments for arbitrary approximate signals. -/
theorem integral_arbitrary_star_coordinate_zero
    {d N c k : ℕ} (D : GaussianWave.RegularEigenData d N c)
    (q : Fin k → Fin N → ℝ) (hzero : ∀ a, (∑ v, q a v) = 0)
    (a : Fin k) (j : Fin (d + 1)) :
    (∫ x, x (a, j) ∂D.starLaw q) = 0 := by
  refine Fin.cases ?_ (fun l => ?_) j
  · rw [D.integral_star_root, hzero, mul_zero]
  · rw [D.integral_star_neighbor, hzero, mul_zero]

end GaussianWave.RegularEigenData

namespace GaussianWave

/-- Residual control, root fourth moments, and the qualitative BS input imply
normalized weak Gaussian stars for actual almost-eigenvector signals. -/
theorem almostEigenvectors_normalizedStar_weakConverges
    {d k : ℕ} (hd : 2 ≤ d) (N c : ℕ → ℕ)
    (D : ∀ n, RegularEigenData d (N n) (c n))
    (q : ∀ n, Fin k → Fin (N n) → ℝ)
    (horth : ∀ n i j, finitePairing (q n i) (q n j) = if i = j then 1 else 0)
    (_hzero : ∀ n a, (∑ v, q n a v) = 0)
    (lam : ℕ → Fin k → ℝ) (E : ℝ)
    (hE : ∀ a, Tendsto (fun n => lam n a) atTop (𝓝 E))
    (hres : ∀ a, Tendsto (fun n =>
      squareMass (eigenResidual (D n).adjacency (lam n a) (q n a))) atTop (𝓝 0))
    (M : ℝ) (hM : ∀ n a, (N n : ℝ) * ∑ v, q n a v ^ 4 ≤ M)
    (BS : BSJointClassification (fun n => (D n).starLaw (q n))) :
    ∃ hC : (jointStarCovariance d k E).PosSemidef,
      WeakLawConverges (fun n => (D n).starLaw (q n))
        (gaussianCovarianceLaw (jointStarCovariance d k E) hC) := by
  classical
  let μ := fun n => (D n).starLaw (q n)
  letI : ∀ n, IsProbabilityMeasure (μ n) := fun n => (D n).starLaw_isProbability _
  apply normalizedGaussian_weakConverges μ
    (fun n aj => (D n).integrable_starLaw _ _) M ?_
    (jointStarCovariance d k E) ?_ BS
  · intro n aj
    rw [(D n).integral_star_coordinate_fourth]
    exact hM n aj.1
  · exact almost_star_covariance_tendsto hd N c D q horth lam E hE hres

/-- The variance-one Gaussian-star covariance at each channel's parameter. -/
def parameterStarCovariance (d k : ℕ) (lam : Fin k → ℝ) :
    Matrix (Fin k × Fin (d + 1)) (Fin k × Fin (d + 1)) ℝ :=
  channelBlockCovariance (fun a => RegularEigenData.starWaveCovariance d (lam a))

lemma parameterStarCovariance_diagonal (d k : ℕ) (lam : Fin k → ℝ)
    (aj : Fin k × Fin (d + 1)) : parameterStarCovariance d k lam aj aj = 1 := by
  simp only [parameterStarCovariance, channelBlockCovariance, ↓reduceIte]
  refine Fin.cases ?_ (fun j => ?_) aj.2 <;> simp [RegularEigenData.starWaveCovariance]

lemma parameterStarCovariance_posSemidef (d k : ℕ) (hd : 2 ≤ d)
    (lam : Fin k → ℝ) (hlam : ∀ a, |lam a| ≤ (d : ℝ)) :
    (parameterStarCovariance d k lam).PosSemidef :=
  channelBlockCovariance_posSemidef _
    (fun a => RegularEigenData.starWaveCovariance_posSemidef d (lam a) hd (hlam a))

/-- An actual Gaussian comparison law with independent variance-one channels,
each at its own approximate eigenvalue. -/
def parameterStarGaussian (d k : ℕ) (hd : 2 ≤ d)
    (lam : Fin k → ℝ) (hlam : ∀ a, |lam a| ≤ (d : ℝ)) :
    Measure ((Fin k × Fin (d + 1)) → ℝ) :=
  gaussianCovarianceLaw (parameterStarCovariance d k lam)
    (parameterStarCovariance_posSemidef d k hd lam hlam)

instance parameterStarGaussian_isProbability (d k : ℕ) (hd : 2 ≤ d)
    (lam : Fin k → ℝ) (hlam : ∀ a, |lam a| ≤ (d : ℝ)) :
    IsProbabilityMeasure (parameterStarGaussian d k hd lam hlam) := by
  unfold parameterStarGaussian
  infer_instance

theorem parameterStarGaussian_product (d k : ℕ) (hd : 2 ≤ d)
    (lam : Fin k → ℝ) (hlam : ∀ a, |lam a| ≤ (d : ℝ)) :
    parameterStarGaussian d k hd lam hlam =
      Measure.map flattenChannels (Measure.pi (fun a => gaussianCovarianceLaw
        (RegularEigenData.starWaveCovariance d (lam a))
        (RegularEigenData.starWaveCovariance_posSemidef d (lam a) hd (hlam a)))) :=
  gaussianCovarianceLaw_channel_product _ _

/-- Gaussian comparison laws vary weakly continuously, including singular
stars and rank changes. -/
theorem parameterStarGaussian_weakConverges
    {d k : ℕ} (hd : 2 ≤ d) (lam : ℕ → Fin k → ℝ)
    (hlam : ∀ n a, |lam n a| ≤ (d : ℝ)) (E : ℝ)
    (hE : ∀ a, Tendsto (fun n => lam n a) atTop (𝓝 E))
    (hC : (jointStarCovariance d k E).PosSemidef) :
    WeakLawConverges (fun n => parameterStarGaussian d k hd (lam n) (hlam n))
      (gaussianCovarianceLaw (jointStarCovariance d k E) hC) := by
  apply gaussianCovarianceLaw_weakConverges
  rintro ⟨a, i⟩ ⟨b, j⟩
  by_cases hab : a = b
  · simp only [parameterStarCovariance, channelBlockCovariance, jointStarCovariance,
      hab, ↓reduceIte, one_mul]
    exact ((RegularEigenData.continuous_starWaveCovariance d i j).tendsto E).comp (hE b)
  · simp only [parameterStarCovariance, channelBlockCovariance, jointStarCovariance,
      hab, ↓reduceIte, zero_mul]
    exact tendsto_const_nhds

/-- The note's almost-eigenvector star corollary, in genuine Wasserstein cost
and compared with independent waves at the individual approximate eigenvalues.
The covariance-limit condition is proved from residuals inside this theorem. -/
theorem almostEigenvectors_normalizedStar_wasserstein
    {d k : ℕ} (hd : 2 ≤ d) (N c : ℕ → ℕ)
    (D : ∀ n, RegularEigenData d (N n) (c n))
    (q : ∀ n, Fin k → Fin (N n) → ℝ)
    (horth : ∀ n i j, finitePairing (q n i) (q n j) = if i = j then 1 else 0)
    (hzero : ∀ n a, (∑ v, q n a v) = 0)
    (lam : ℕ → Fin k → ℝ) (E : ℝ)
    (hlam : ∀ n a, |lam n a| ≤ (d : ℝ))
    (hE : ∀ a, Tendsto (fun n => lam n a) atTop (𝓝 E))
    (hres : ∀ a, Tendsto (fun n =>
      squareMass (eigenResidual (D n).adjacency (lam n a) (q n a))) atTop (𝓝 0))
    (M : ℝ) (hM : ∀ n a, (N n : ℝ) * ∑ v, q n a v ^ 4 ≤ M)
    (BS : BSJointClassification (fun n => (D n).starLaw (q n))) :
    Tendsto (fun n => wassersteinTwo ((D n).starLaw (q n))
      (parameterStarGaussian d k hd (lam n) (hlam n))) atTop (𝓝 0) := by
  classical
  let μ := fun n => (D n).starLaw (q n)
  let ν := fun n => parameterStarGaussian d k hd (lam n) (hlam n)
  letI : ∀ n, IsProbabilityMeasure (μ n) := fun n => (D n).starLaw_isProbability _
  obtain ⟨hC, hw⟩ := almostEigenvectors_normalizedStar_weakConverges hd N c D q horth hzero
    lam E hE hres M hM BS
  have hg := parameterStarGaussian_weakConverges hd lam hlam E hE hC
  have hμ (n : ℕ) := integral_squareMass_sq_le (μ n)
    (fun aj => (D n).integrable_starLaw _ _) M (fun aj => by
      rw [(D n).integral_star_coordinate_fourth]
      exact hM n aj.1)
  have hν (n : ℕ) : Integrable (fun x => squareMass x ^ 2) (ν n) ∧
      (∫ x, squareMass x ^ 2 ∂ν n) ≤
        3 * (Fintype.card (Fin k × Fin (d + 1)) : ℝ) ^ 2 := by
    apply integral_squareMass_sq_le _
      (fun aj => gaussianCovarianceLaw_coordinate_integrable_pow _ _ aj 4) 3
    intro aj
    change (∫ x, x aj ^ 4 ∂parameterStarGaussian d k hd (lam n) (hlam n)) ≤ 3
    rw [parameterStarGaussian, gaussianCovarianceLaw_coordinate_fourth,
      parameterStarCovariance_diagonal]
    norm_num
  exact wassersteinTwo_tendsto_zero_of_common_weak_limit μ ν
    (gaussianCovarianceLaw (jointStarCovariance d k E) hC) hw hg
    (fun n => (hμ n).1) (fun n => (hν n).1)
    (M * (Fintype.card (Fin k × Fin (d + 1)) : ℝ) ^ 2)
    (3 * (Fintype.card (Fin k × Fin (d + 1)) : ℝ) ^ 2)
    (fun n => (hμ n).2) (fun n => (hν n).2)

end GaussianWave
