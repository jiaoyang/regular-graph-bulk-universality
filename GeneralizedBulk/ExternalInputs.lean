import Mathlib

/-!
# Explicit external BS and HY contracts

These are ordinary hypotheses on concrete finite spectral data, not global
axioms. No instance is constructed here. The uniform graph/proposal adapters,
Kesten--McKay quantiles, and infinite regular-tree Green function are proved
in the subsequent graph and spectral modules.

The BS contract is the star restriction of the qualitative uniform theorem:
subsequential limits of nearby almost-eigenvector tuples are centered jointly
Gaussian, with an unspecified covariance. Quantitative fourth moments and
variance-one normalization are deliberately absent.

The HY contracts below cover rigidity, delocalization, mesoscopic trace bounds,
and a separately parameterized star comparison. The fixed-radius
local-tree geometry used in the source HY citation is recorded separately in
`ExternalGeometry.HYGeometryInput`.
-/

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter

namespace GeneralizedBulk.External

/-- Measurable real adjacency matrices, ordered real eigenpairs, and an exact
ordered enumeration of every vertex's neighbors. All graph properties are
literal matrix equalities. Uniform graph sampling is adapter work. -/
structure RegularSpectralData (d : ℕ) (N : ℕ → ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  size_pos : ∀ n, 0 < N n
  size_tendsto : Tendsto N atTop atTop
  adjacency : ∀ n, Ω → Matrix (Fin (N n)) (Fin (N n)) ℝ
  eigenvalue : ∀ n, Ω → Fin (N n) → ℝ
  eigenvector : ∀ n, Ω → Fin (N n) → Fin (N n) → ℝ
  neighbor : ∀ n, Ω → Fin (N n) → Fin d → Fin (N n)
  symmetric : ∀ n ω v w, adjacency n ω v w = adjacency n ω w v
  diagonal_zero : ∀ n ω v, adjacency n ω v v = 0
  entry_zero_one : ∀ n ω v w, adjacency n ω v w = 0 ∨ adjacency n ω v w = 1
  regular : ∀ n ω v, ∑ w, adjacency n ω v w = (d : ℝ)
  neighbor_injective : ∀ n ω v, Function.Injective (neighbor n ω v)
  neighbor_exact : ∀ n ω v w, adjacency n ω v w = 1 ↔ ∃ j, neighbor n ω v j = w
  orthonormal : ∀ n ω i j,
    ∑ v, eigenvector n ω i v * eigenvector n ω j v = if i = j then 1 else 0
  eigen_equation : ∀ n ω i v,
    ∑ w, adjacency n ω v w * eigenvector n ω i w =
      eigenvalue n ω i * eigenvector n ω i v
  ordered : ∀ n ω i j, i ≤ j → eigenvalue n ω j ≤ eigenvalue n ω i
  constant_eigenvalue : ∀ n ω, eigenvalue n ω ⟨0, size_pos n⟩ = d
  constant_eigenvector : ∀ n ω v,
    eigenvector n ω ⟨0, size_pos n⟩ v = (Real.sqrt (N n))⁻¹
  measurable_adjacency : ∀ n v w, Measurable (fun ω => adjacency n ω v w)
  measurable_eigenvalue : ∀ n i, Measurable (fun ω => eigenvalue n ω i)
  measurable_eigenvector : ∀ n i v, Measurable (fun ω => eigenvector n ω i v)
  measurable_neighbor : ∀ n v j, Measurable (fun ω => neighbor n ω v j)

namespace RegularSpectralData
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The genuine finite empirical star law, sampled at a uniform root and
uniform neighbor ordering. Repeated channel and physical coordinates remain. -/
def starLaw (D : RegularSpectralData d N Ω) {k : ℕ} (n : ℕ) (ω : Ω)
    (q : Fin k → Fin (N n) → ℝ) : Measure ((Fin k × Fin (d + 1)) → ℝ) := by
  classical
  let V := Fin (N n) × Equiv.Perm (Fin d)
  let mark : V → (Fin k × Fin (d + 1)) → ℝ := fun sample aj =>
    Real.sqrt (N n) * q aj.1
      (Fin.cases sample.1 (fun j => D.neighbor n ω sample.1 (sample.2 j)) aj.2)
  exact (Fintype.card V : ENNReal)⁻¹ • ∑ sample : V, Measure.dirac (mark sample)

/-- The empirical law is normalized, independently of the selected vectors. -/
theorem starLaw_isProbability (D : RegularSpectralData d N Ω) {k : ℕ}
    (n : ℕ) (ω : Ω) (q : Fin k → Fin (N n) → ℝ) :
    IsProbabilityMeasure (D.starLaw n ω q) := by
  classical
  letI : Nonempty (Fin (N n)) := ⟨⟨0, D.size_pos n⟩⟩
  have hN : N n ≠ 0 := Nat.ne_of_gt (D.size_pos n)
  constructor
  simp [starLaw, Measure.smul_apply, Finset.sum_apply]
  apply ENNReal.inv_mul_cancel
  · simp [hN, Fintype.card_ne_zero]
  · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)

/-- Actual adjacency resolvent; nonreal invertibility is a later finite
spectral lemma, rather than a field allowing an arbitrary comparison matrix. -/
def resolvent (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω) (z : ℂ) :
    Matrix (Fin (N n)) (Fin (N n)) ℂ := by
  classical
  exact ((D.adjacency n ω).map Complex.ofReal - z • (1 : Matrix (Fin (N n)) _ ℂ))⁻¹

def scalarResolvent (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω) (z : ℂ) : ℂ :=
  (N n : ℂ)⁻¹ * Matrix.trace (D.resolvent n ω z)

/-- Total squared residual for an almost-eigenvector tuple at one energy. -/
def tupleResidual (D : RegularSpectralData d N Ω) {k : ℕ} (n : ℕ) (ω : Ω)
    (q : Fin k → Fin (N n) → ℝ) (energy : ℝ) : ℝ :=
  ∑ a, ∑ v, ((∑ w, D.adjacency n ω v w * q a w) - energy * q a v) ^ 2
end RegularSpectralData

/-- Weak convergence tested by genuine bounded continuous functions. -/
def WeakLawConverges {V : Type*} [TopologicalSpace V] [MeasurableSpace V]
    (ν : ℕ → Measure V) (limit : Measure V) : Prop :=
  ∀ f : BoundedContinuousFunction V ℝ,
    Tendsto (fun n => ∫ x, f x ∂ν n) atTop (𝓝 (∫ x, f x ∂limit))

/-- Centered joint Gaussianity via its characteristic function. The covariance
is existential and may be degenerate or smaller than the empirical covariance. -/
def CenteredGaussianLaw {I : Type*} [Fintype I] (ν : Measure (I → ℝ)) : Prop :=
  IsProbabilityMeasure ν ∧ ∃ cov : Matrix I I ℝ,
    (∀ i j, cov i j = cov j i) ∧
    (∀ t : I → ℝ, 0 ≤ ∑ i, ∑ j, t i * cov i j * t j) ∧
    ∀ t : I → ℝ,
      (∫ x, Complex.exp ((↑(∑ i, t i * x i) : ℂ) * Complex.I) ∂ν) =
        Complex.exp (↑(-(1 / 2 : ℝ) * ∑ i, ∑ j, t i * cov i j * t j) : ℂ)

/-- A source-faithful weak consequence of BS, uniform over choices on common
high-probability events. It asserts neither independent channels nor unit
variance, and it contains no fourth-moment conclusion. -/
structure BSQualitativeInput
    {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (D : RegularSpectralData d N Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Set ℝ) where
  degree_ge_three : 3 ≤ d
  compact_bulk : IsCompact K ∧ ∀ x ∈ K, |x| < 2 * Real.sqrt (d - 1 : ℝ)
  good : ℕ → ℕ → Set Ω
  measurable_good : ∀ k n, MeasurableSet (good k n)
  good_probability : ∀ k, Tendsto (fun n => P (good k n)ᶜ) atTop (𝓝 0)
  gaussian_limit : ∀ k : ℕ, 0 < k → ∀ ω : ℕ → Ω,
    (∀ᶠ n in atTop, ω n ∈ good k n) →
    ∀ q : ∀ n, Fin k → Fin (N n) → ℝ, ∀ energy : ℕ → ℝ,
    (∀ᶠ n in atTop, energy n ∈ K) →
    (∀ᶠ n in atTop, ∀ a, ∑ v, q n a v = 0) →
    (∀ᶠ n in atTop, ∀ a b, ∑ v, q n a v * q n b v = if a = b then 1 else 0) →
    Tendsto (fun n => D.tupleResidual n (ω n) (q n) (energy n)) atTop (𝓝 0) →
    ∀ energyLimit ∈ K, Tendsto energy atTop (𝓝 energyLimit) →
    ∀ φ : ℕ → ℕ, StrictMono φ →
    ∀ ν : Measure ((Fin k × Fin (d + 1)) → ℝ),
      WeakLawConverges (fun n => D.starLaw (φ n) (ω (φ n)) (q (φ n))) ν →
      CenteredGaussianLaw ν

/-- Polynomial-probability good events with a common deterministic threshold. -/
structure PolynomialGoodEvents {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (N : ℕ → ℕ) where
  good : ℕ → Set Ω
  measurable_good : ∀ n, MeasurableSet (good n)
  exponent : ℝ
  constant : ℝ
  exponent_pos : 0 < exponent
  constant_pos : 0 < constant
  threshold : ℕ
  failure_bound : ∀ n, threshold ≤ n →
    P (good n)ᶜ ≤ ENNReal.ofReal (constant * (N n : ℝ) ^ (-exponent))

/-- HY rigidity and delocalization. Quantile identification with the exact
Kesten--McKay law is required in the graph adapter. Delocalization quantifies
over every unit eigenvector, including arbitrary repeated-eigenspace choices. -/
structure HYCoarseInput
    {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (D : RegularSpectralData d N Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (quantile : ∀ n, Fin (N n) → ℝ) where
  events : PolynomialGoodEvents P N
  rigidity_exponent : ℝ
  rigidity_exponent_pos : 0 < rigidity_exponent
  logPower : ℕ
  rigidity : ∀ n, events.threshold ≤ n → ∀ ω ∈ events.good n,
    ∀ i : Fin (N n), i.val ≠ 0 →
      |D.eigenvalue n ω i - quantile n i| ≤ (N n : ℝ) ^ (-rigidity_exponent)
  delocalization : ∀ n, events.threshold ≤ n → ∀ ω ∈ events.good n,
    ∀ q : Fin (N n) → ℝ, ∀ energy : ℝ, (∑ v, q v ^ 2) = 1 →
    (∀ v, ∑ w, D.adjacency n ω v w * q w = energy * q v) →
    ∀ v, Real.sqrt (N n) * |q v| ≤
      events.constant * Real.log (N n) ^ logPower

/-- HY averaged local-law bound for one fixed positive mesoscopic exponent.
A full spectral input supplies this record separately for every alpha > 0. -/
structure HYMesoscopicInput
    {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (D : RegularSpectralData d N Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Set ℝ) (α : ℝ) where
  alpha_pos : 0 < α
  events : PolynomialGoodEvents P N
  trace_bound : ∀ n, events.threshold ≤ n → ∀ ω ∈ events.good n,
    ∀ x ∈ K, ∀ η : ℝ, 0 < η → (N n : ℝ) ^ (-1 + α) ≤ η → η ≤ 1 →
      (D.scalarResolvent n ω ((x : ℂ) + η * Complex.I)).im ≤ events.constant

/-- Explicit optional local-star approximation input. The deterministic array
must subsequently be identified with the infinite regular tree Green function.
This record alone does not encode the separate fixed-radius tree geometry. -/
structure HYLocalStarInput
    {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (D : RegularSpectralData d N Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Set ℝ) (c₀ : ℝ)
    (treeGreen : ℂ → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) where
  height_range : 0 < c₀ ∧ c₀ < 1 / 2
  events : PolynomialGoodEvents P N
  local_exponent : ℝ
  local_exponent_pos : 0 < local_exponent
  badRoots : ∀ n, Ω → Finset (Fin (N n))
  bad_count : ∀ n, events.threshold ≤ n → ∀ ω ∈ events.good n,
    ((badRoots n ω).card : ℝ) ≤ (N n : ℝ) ^ (1 / 2 : ℝ)
  approximation : ∀ n, events.threshold ≤ n → ∀ ω ∈ events.good n,
    ∀ root : Fin (N n), root ∉ badRoots n ω → ∀ energy ∈ K,
    ∀ i j : Fin (d + 1),
      let z := (energy : ℂ) + (↑((N n : ℝ) ^ (-c₀)) : ℂ) * Complex.I
      let vertex : Fin (d + 1) → Fin (N n) := Fin.cases root (D.neighbor n ω root)
      ‖D.resolvent n ω z (vertex i) (vertex j) - treeGreen z i j‖ ≤
        (N n : ℝ) ^ (-local_exponent)

end GeneralizedBulk.External
