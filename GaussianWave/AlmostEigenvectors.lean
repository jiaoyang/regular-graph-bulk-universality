import GaussianWave.MomentTail

/-!
# Common-energy residuals of finite orthonormal tuples

These are finite deterministic identities. They explain why nearby
orthonormal eigenvectors are eligible for the qualitative almost-eigenvector
input. No Gaussian conclusion or probabilistic graph theorem is assumed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace GaussianWave

/-- A finite real channel combination in the physical vertex coordinates. -/
def channelCombination {κ ι : Type*} [Fintype κ]
    (u : κ → ι → ℝ) (c : κ → ℝ) : ι → ℝ :=
  fun x => ∑ a, c a * u a x

/-- The residual of the adjacency eigenvector equation at one energy. -/
def eigenResidual {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (E : ℝ) (u : ι → ℝ) : ι → ℝ :=
  fun x => (∑ y, A x y * u y) - E * u x

lemma channelCombination_eq_vecMul {κ ι : Type*} [Fintype κ]
    (u : κ → ι → ℝ) (c : κ → ℝ) :
    channelCombination u c = Matrix.vecMul c u := rfl

/-- The exact Gram identity, valid for any finite orthonormal family. -/
theorem squareMass_channelCombination {κ ι : Type*} [Fintype κ] [Fintype ι]
    [DecidableEq κ]
    (u : κ → ι → ℝ)
    (horth : ∀ a b, (∑ x, u a x * u b x) = if a = b then 1 else 0)
    (c : κ → ℝ) :
    squareMass (channelCombination u c) = ∑ a, c a ^ 2 := by
  let U : Matrix κ ι ℝ := u
  have hU : U * U.transpose = 1 := by
    ext a b
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using horth a b
  rw [channelCombination_eq_vecMul]
  change squareMass (Matrix.vecMul c U) = _
  calc
    _ = Matrix.vecMul c U ⬝ᵥ (U.transpose.mulVec c) := by
      rw [Matrix.mulVec_transpose]
      simp only [squareMass, dotProduct, pow_two]
    _ = c ⬝ᵥ U.mulVec (U.transpose.mulVec c) := (Matrix.dotProduct_mulVec ..).symm
    _ = c ⬝ᵥ (U * U.transpose).mulVec c := by rw [Matrix.mulVec_mulVec]
    _ = _ := by rw [hU, Matrix.one_mulVec]; simp only [dotProduct, pow_two]

/-- Unit coefficient vectors yield unit physical Euclidean norm. -/
theorem squareMass_channelCombination_eq_one {κ ι : Type*}
    [Fintype κ] [Fintype ι] [DecidableEq κ]
    (u : κ → ι → ℝ)
    (horth : ∀ a b, (∑ x, u a x * u b x) = if a = b then 1 else 0)
    (c : κ → ℝ) (hc : (∑ a, c a ^ 2) = 1) :
    squareMass (channelCombination u c) = 1 := by
  rw [squareMass_channelCombination u horth, hc]

/-- Zero entry sums are preserved by all channel combinations. -/
theorem sum_channelCombination_eq_zero {κ ι : Type*} [Fintype κ] [Fintype ι]
    (u : κ → ι → ℝ) (hu : ∀ a, (∑ x, u a x) = 0) (c : κ → ℝ) :
    (∑ x, channelCombination u c x) = 0 := by
  simp only [channelCombination]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hu, mul_zero]
  exact Finset.sum_const_zero

lemma eigenResidual_channelCombination {κ ι : Type*} [Fintype κ] [Fintype ι]
    (A : Matrix ι ι ℝ) (E : ℝ) (u : κ → ι → ℝ) (c : κ → ℝ) :
    eigenResidual A E (channelCombination u c) =
      channelCombination (fun a => eigenResidual A E (u a)) c := by
  funext x
  have he : (∑ y, A x y * ∑ a, c a * u a y) =
      ∑ a, c a * ∑ y, A x y * u a y := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro y _
    ring
  simp only [eigenResidual, channelCombination]
  rw [he]
  simp only [Finset.mul_sum, Finset.sum_sub_distrib, mul_sub]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Exact residual decomposition for almost eigenvectors at differing energies. -/
theorem eigenResidual_commonEnergy_decomposition {κ ι : Type*}
    [Fintype κ] [Fintype ι]
    (A : Matrix ι ι ℝ) (lam : κ → ℝ) (E : ℝ)
    (u : κ → ι → ℝ) (c : κ → ℝ) :
    eigenResidual A E (channelCombination u c) =
      channelCombination (fun a => eigenResidual A (lam a) (u a)) c +
        channelCombination u (fun a => c a * (lam a - E)) := by
  rw [eigenResidual_channelCombination]
  funext x
  simp only [channelCombination, eigenResidual, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- For exact eigenvectors, the common-energy residual is another channel
combination with the eigenvalue differences as coefficients. -/
theorem eigenResidual_exact_channelCombination {κ ι : Type*}
    [Fintype κ] [Fintype ι]
    (A : Matrix ι ι ℝ) (lam : κ → ℝ) (E : ℝ)
    (u : κ → ι → ℝ)
    (heig : ∀ a x, (∑ y, A x y * u a y) = lam a * u a x) (c : κ → ℝ) :
    eigenResidual A E (channelCombination u c) =
      channelCombination u (fun a => c a * (lam a - E)) := by
  rw [eigenResidual_commonEnergy_decomposition A lam]
  have hz : channelCombination (fun a => eigenResidual A (lam a) (u a)) c = 0 := by
    funext x
    simp [channelCombination, eigenResidual, heig]
  rw [hz, zero_add]

/-- The exact identity used to apply the common-energy qualitative theorem. -/
theorem commonEnergy_residual_square_identity {κ ι : Type*}
    [Fintype κ] [Fintype ι] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (lam : κ → ℝ) (E : ℝ)
    (u : κ → ι → ℝ)
    (horth : ∀ a b, (∑ x, u a x * u b x) = if a = b then 1 else 0)
    (heig : ∀ a x, (∑ y, A x y * u a y) = lam a * u a x) (c : κ → ℝ) :
    squareMass (eigenResidual A E (channelCombination u c)) =
      ∑ a, c a ^ 2 * (lam a - E) ^ 2 := by
  rw [eigenResidual_exact_channelCombination A lam E u heig,
    squareMass_channelCombination u horth]
  simp only [mul_pow]

/-- The orthonormal eigenvalue-shift part has squared size at most `δ²`. -/
theorem squareMass_shiftCombination_le {κ ι : Type*}
    [Fintype κ] [Fintype ι] [DecidableEq κ]
    (u : κ → ι → ℝ)
    (horth : ∀ a b, (∑ x, u a x * u b x) = if a = b then 1 else 0)
    (lam : κ → ℝ) (E δ : ℝ) (hδ : 0 ≤ δ)
    (hclose : ∀ a, |lam a - E| ≤ δ)
    (c : κ → ℝ) (hc : (∑ a, c a ^ 2) = 1) :
    squareMass (channelCombination u (fun a => c a * (lam a - E))) ≤ δ ^ 2 := by
  rw [squareMass_channelCombination u horth]
  calc
    _ = ∑ a, c a ^ 2 * (lam a - E) ^ 2 := by simp only [mul_pow]
    _ ≤ ∑ a, c a ^ 2 * δ ^ 2 := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      nlinarith [hclose a, abs_nonneg (lam a - E), sq_abs (lam a - E)]
    _ = δ ^ 2 := by rw [← Finset.sum_mul, hc, one_mul]

/-- Every normalized combination is a `δ`-almost eigenvector in squared norm. -/
theorem commonEnergy_residual_square_le {κ ι : Type*}
    [Fintype κ] [Fintype ι] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (lam : κ → ℝ) (E : ℝ)
    (u : κ → ι → ℝ)
    (horth : ∀ a b, (∑ x, u a x * u b x) = if a = b then 1 else 0)
    (heig : ∀ a x, (∑ y, A x y * u a y) = lam a * u a x)
    (δ : ℝ) (hδ : 0 ≤ δ) (hclose : ∀ a, |lam a - E| ≤ δ)
    (c : κ → ℝ) (hc : (∑ a, c a ^ 2) = 1) :
    squareMass (eigenResidual A E (channelCombination u c)) ≤ δ ^ 2 := by
  rw [eigenResidual_exact_channelCombination A lam E u heig]
  exact squareMass_shiftCombination_le u horth lam E δ hδ hclose c hc

/-- Cauchy--Schwarz controls combinations of residuals without assuming that
those residuals themselves are orthogonal. -/
theorem squareMass_channelCombination_le {κ ι : Type*} [Fintype κ] [Fintype ι]
    (u : κ → ι → ℝ) (c : κ → ℝ) :
    squareMass (channelCombination u c) ≤
      (∑ a, c a ^ 2) * ∑ a, squareMass (u a) := by
  calc
    _ ≤ ∑ x, (∑ a, c a ^ 2) * ∑ a, u a x ^ 2 := by
      apply Finset.sum_le_sum
      intro x _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c (fun a => u a x)
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      rfl

lemma squareMass_add_le {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    squareMass (x + y) ≤ 2 * squareMass x + 2 * squareMass y := by
  calc
    _ ≤ ∑ i, (2 * x i ^ 2 + 2 * y i ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      change (x i + y i) ^ 2 ≤ _
      nlinarith [sq_nonneg (x i - y i)]
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, squareMass]

/-- An approximate tuple at nearby energies has common-energy squared
residual at most `2 k ρ² + 2 δ²`. This vanishes for fixed `k` when the two
input errors vanish; exact tuples satisfy the sharper bound above. -/
theorem commonEnergy_almost_residual_square_le {κ ι : Type*}
    [Fintype κ] [Fintype ι] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (lam : κ → ℝ) (E : ℝ)
    (u : κ → ι → ℝ)
    (horth : ∀ a b, (∑ x, u a x * u b x) = if a = b then 1 else 0)
    (ρ δ : ℝ) (hδ : 0 ≤ δ)
    (hres : ∀ a, squareMass (eigenResidual A (lam a) (u a)) ≤ ρ ^ 2)
    (hclose : ∀ a, |lam a - E| ≤ δ)
    (c : κ → ℝ) (hc : (∑ a, c a ^ 2) = 1) :
    squareMass (eigenResidual A E (channelCombination u c)) ≤
      2 * (Fintype.card κ : ℝ) * ρ ^ 2 + 2 * δ ^ 2 := by
  rw [eigenResidual_commonEnergy_decomposition A lam]
  have hr : squareMass (channelCombination (fun a => eigenResidual A (lam a) (u a)) c) ≤
      (Fintype.card κ : ℝ) * ρ ^ 2 := by
    have hh := squareMass_channelCombination_le (fun a => eigenResidual A (lam a) (u a)) c
    rw [hc, one_mul] at hh
    apply hh.trans
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      (Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hres a))
  have hs := squareMass_shiftCombination_le u horth lam E δ hδ hclose c hc
  exact (squareMass_add_le _ _).trans (by nlinarith)

/-- The common-energy almost-eigenvector condition follows for a fixed number
of channels even when the vertex dimension and the coefficients vary with the
index. Both input errors are required to tend to zero. -/
theorem commonEnergy_almost_residual_tendsto_zero
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (A : ∀ n, Matrix (ι n) (ι n) ℝ) (lam : ℕ → κ → ℝ) (E : ℕ → ℝ)
    (u : ∀ n, κ → ι n → ℝ)
    (horth : ∀ n a b, (∑ x, u n a x * u n b x) = if a = b then 1 else 0)
    (ρ δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hres : ∀ n a, squareMass (eigenResidual (A n) (lam n a) (u n a)) ≤ ρ n ^ 2)
    (hclose : ∀ n a, |lam n a - E n| ≤ δ n)
    (c : ℕ → κ → ℝ) (hc : ∀ n, (∑ a, c n a ^ 2) = 1)
    (hρlim : Tendsto ρ atTop (𝓝 0)) (hδlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => squareMass (eigenResidual (A n) (E n)
      (channelCombination (u n) (c n)))) atTop (𝓝 0) := by
  have hup : Tendsto (fun n =>
      2 * (Fintype.card κ : ℝ) * ρ n ^ 2 + 2 * δ n ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero] using
      ((hρlim.pow 2).const_mul (2 * (Fintype.card κ : ℝ))).add
        ((hδlim.pow 2).const_mul 2)
  exact squeeze_zero (fun n => squareMass_nonneg _)
    (fun n => commonEnergy_almost_residual_square_le (A n) (lam n) (E n) (u n)
      (horth n) (ρ n) (δ n) (hδ n) (hres n) (hclose n) (c n) (hc n)) hup

end GaussianWave
