import GaussianWave.Covariance

/-!
# Cover-sampling contracts and exact covariance on every finite tree window

This module does not construct the infinite uniform covering map. It proves
what follows from an explicit sampling adapter: uniform vertex marginals,
radial invariance of the pair law, and a genuine local covering relation.
The geometry contract is purely combinatorial. No covariance identity or
Gaussian eigenvector statistic is included among these assumptions.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ENNReal

namespace GaussianWave

/-- A radial description of the infinite d-regular tree sufficient for the
covariance recurrence. The `radial_sum` field is the count of one inward and
d-1 outward neighbors, with d outward neighbors at distance zero. -/
structure RadialTreeGeometry (d : ℕ) (T : Type*) where
  root : T
  neighbor : T → Fin d → T
  distance : T → T → ℕ
  distance_self : ∀ x, distance x x = 0
  pointAtDistance : ℕ → T
  root_distance : ∀ r, distance root (pointAtDistance r) = r
  radial_sum : ∀ (x y : T) (f : ℕ → ℝ),
    (∑ j, f (distance x (neighbor y j))) =
      if distance x y = 0 then (d : ℝ) * f 1 else
        f (distance x y - 1) + ((d : ℝ) - 1) * f (distance x y + 1)

/-- Actual uniform measure on the finite graph vertex set. -/
def uniformVertexLaw (N : ℕ) : Measure (Fin N) :=
  (N : ℝ≥0∞)⁻¹ • ∑ v : Fin N, Measure.dirac v

theorem integrable_uniformVertexLaw (N : ℕ) (hN : 0 < N) (f : Fin N → ℝ) :
    Integrable f (uniformVertexLaw N) := by
  classical
  exact (integrable_finset_sum_measure.mpr (fun _ _ => integrable_dirac)).smul_measure
    (ENNReal.inv_ne_top.mpr (by exact_mod_cast Nat.ne_of_gt hN))

theorem integral_uniformVertexLaw (N : ℕ) (f : Fin N → ℝ) :
    (∫ v, f v ∂uniformVertexLaw N) = (N : ℝ)⁻¹ * ∑ v, f v := by
  classical
  rw [uniformVertexLaw, integral_smul_measure,
    integral_finset_sum_measure (fun _ _ => integrable_dirac)]
  simp

/-- A precise adapter for the uniform-cover sampling law. The covering field
says that at each tree vertex the graph neighbors are enumerated bijectively.
The infinite sampling construction itself is a separate task. -/
structure CoverSampling {d N c : ℕ} (D : RegularEigenData d N c)
    {T Ω : Type*} (G : RadialTreeGeometry d T) [MeasurableSpace Ω] (P : Measure Ω) where
  image : Ω → T → Fin N
  measurable_eval : ∀ x, Measurable (fun ω => image ω x)
  uniform_vertex : ∀ x, Measure.map (fun ω => image ω x) P = uniformVertexLaw N
  radial_pair : ∀ x y x' y', G.distance x y = G.distance x' y' →
    Measure.map (fun ω => (image ω x, image ω y)) P =
      Measure.map (fun ω => (image ω x', image ω y')) P
  covering : ∀ x, ∀ᵐ ω ∂P, ∃ σ : Equiv.Perm (Fin d),
    ∀ j, image ω (G.neighbor x j) = D.neighbor (image ω x) (σ j)

namespace CoverSampling
variable {d N c : ℕ} {D : RegularEigenData d N c}
variable {T Ω : Type*} {G : RadialTreeGeometry d T}
variable [MeasurableSpace Ω] {P : Measure Ω}
variable (S : CoverSampling D G P)

/-- The normalized eigenvector lifted by the sampled covering map. -/
def coordinate (a : Fin c) (x : T) (ω : Ω) : ℝ :=
  Real.sqrt N * D.eigenvector a (S.image ω x)

theorem measurable_coordinate (a : Fin c) (x : T) : Measurable (S.coordinate a x) :=
  measurable_const.mul ((measurable_of_finite _).comp (S.measurable_eval x))

theorem integrable_eval (x : T) (f : Fin N → ℝ) :
    Integrable (fun ω => f (S.image ω x)) P := by
  have hf : Integrable f (Measure.map (fun ω => S.image ω x) P) := by
    rw [S.uniform_vertex x]
    exact integrable_uniformVertexLaw N D.size_pos f
  exact (integrable_map_measure hf.aestronglyMeasurable
    (S.measurable_eval x).aemeasurable).mp hf

theorem integral_eval (x : T) (f : Fin N → ℝ) :
    (∫ ω, f (S.image ω x) ∂P) = (N : ℝ)⁻¹ * ∑ v, f v := by
  have hf : AEStronglyMeasurable f (Measure.map (fun ω => S.image ω x) P) :=
    (measurable_of_finite f).aestronglyMeasurable
  calc
    _ = ∫ v, f v ∂Measure.map (fun ω => S.image ω x) P :=
      (integral_map (S.measurable_eval x).aemeasurable hf).symm
    _ = _ := by rw [S.uniform_vertex x, integral_uniformVertexLaw]

theorem integrable_coordinate_pow (a : Fin c) (x : T) (p : ℕ) :
    Integrable (fun ω => S.coordinate a x ω ^ p) P :=
  S.integrable_eval x (fun v => (Real.sqrt N * D.eigenvector a v) ^ p)

theorem integrable_coordinate_pair (a b : Fin c) (x y : T) :
    Integrable (fun ω => S.coordinate a x ω * S.coordinate b y ω) P := by
  apply ((S.integrable_coordinate_pow a x 2).add
    (S.integrable_coordinate_pow b y 2)).mono'
    ((S.measurable_coordinate a x).mul (S.measurable_coordinate b y)).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_mul]
  change |S.coordinate a x ω| * |S.coordinate b y ω| ≤
    S.coordinate a x ω ^ 2 + S.coordinate b y ω ^ 2
  nlinarith [sq_nonneg (|S.coordinate a x ω| - |S.coordinate b y ω|),
    sq_abs (S.coordinate a x ω), sq_abs (S.coordinate b y ω)]

/-- Pair expectation, before any radial or eigenvector calculation. -/
def pairMoment (a b : Fin c) (x y : T) : ℝ :=
  ∫ ω, S.coordinate a x ω * S.coordinate b y ω ∂P

theorem pairMoment_radial (a b : Fin c) (x y x' y' : T)
    (h : G.distance x y = G.distance x' y') :
    S.pairMoment a b x y = S.pairMoment a b x' y' := by
  let f : Fin N × Fin N → ℝ := fun z =>
    (Real.sqrt N * D.eigenvector a z.1) * (Real.sqrt N * D.eigenvector b z.2)
  have hm (x y : T) : Measurable (fun ω => (S.image ω x, S.image ω y)) :=
    (S.measurable_eval x).prodMk (S.measurable_eval y)
  have hf := measurable_of_finite f
  change (∫ ω, f (S.image ω x, S.image ω y) ∂P) =
    ∫ ω, f (S.image ω x', S.image ω y') ∂P
  rw [← integral_map (hm x y).aemeasurable hf.aestronglyMeasurable,
    ← integral_map (hm x' y').aemeasurable hf.aestronglyMeasurable,
    S.radial_pair x y x' y' h]

/-- A reference pair at each distance, defined using only the tree geometry. -/
def radialMoment (a b : Fin c) (r : ℕ) : ℝ :=
  S.pairMoment a b G.root (G.pointAtDistance r)

theorem pairMoment_eq_radial (a b : Fin c) (x y : T) :
    S.pairMoment a b x y = S.radialMoment a b (G.distance x y) :=
  S.pairMoment_radial a b x y G.root (G.pointAtDistance (G.distance x y))
    (G.root_distance _).symm

theorem pairMoment_self (a b : Fin c) (x : T) :
    S.pairMoment a b x x = if a = b then 1 else 0 := by
  classical
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt D.size_pos)
  have hs : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg _)
  change (∫ ω, (Real.sqrt N * D.eigenvector a (S.image ω x)) *
    (Real.sqrt N * D.eigenvector b (S.image ω x)) ∂P) = _
  rw [S.integral_eval x (fun v => (Real.sqrt N * D.eigenvector a v) *
    (Real.sqrt N * D.eigenvector b v))]
  have he (v : Fin N) : (Real.sqrt N * D.eigenvector a v) *
      (Real.sqrt N * D.eigenvector b v) = (N : ℝ) * (D.eigenvector a v * D.eigenvector b v) := by
    calc
      _ = Real.sqrt (N : ℝ) ^ 2 * (D.eigenvector a v * D.eigenvector b v) := by ring
      _ = _ := by rw [hs]
  simp_rw [he]
  rw [← Finset.mul_sum, D.orthonormal]
  field_simp

theorem radialMoment_zero (a b : Fin c) :
    S.radialMoment a b 0 = if a = b then 1 else 0 := by
  rw [radialMoment, ← S.pairMoment_radial a b G.root G.root G.root (G.pointAtDistance 0)
    (by rw [G.distance_self, G.root_distance])]
  exact S.pairMoment_self a b G.root

theorem covering_eigenrelation (a : Fin c) (x : T) :
    ∀ᵐ ω ∂P, (∑ j, S.coordinate a (G.neighbor x j) ω) =
      D.eigenvalue a * S.coordinate a x ω := by
  filter_upwards [S.covering x] with ω hω
  obtain ⟨σ, hσ⟩ := hω
  simp only [coordinate]
  rw [← Finset.mul_sum]
  simp_rw [hσ]
  rw [Equiv.sum_comp σ (fun j => D.eigenvector a (D.neighbor (S.image ω x) j)),
    D.eigenvector_neighbor_sum]
  ring

/-- Integrating the lifted eigenrelation yields the covariance equation. -/
theorem pairMoment_eigenrelation (a b : Fin c) (x y : T) :
    (∑ j, S.pairMoment a b x (G.neighbor y j)) =
      D.eigenvalue b * S.pairMoment a b x y := by
  simp only [pairMoment]
  rw [← integral_finset_sum _
    (fun j _ => S.integrable_coordinate_pair a b x (G.neighbor y j))]
  calc
    _ = ∫ ω, D.eigenvalue b *
        (S.coordinate a x ω * S.coordinate b y ω) ∂P := by
      apply integral_congr_ae
      filter_upwards [S.covering_eigenrelation b y] with ω hω
      rw [← Finset.mul_sum, hω]
      ring
    _ = _ := integral_const_mul _ _

end CoverSampling
end GaussianWave

namespace GaussianWave.CoverSampling
variable {d N c : ℕ} {D : RegularEigenData d N c}
variable {T Ω : Type*} {G : RadialTreeGeometry d T}
variable [MeasurableSpace Ω] {P : Measure Ω}
variable (S : CoverSampling D G P)

theorem radialMoment_equation (a b : Fin c) (r : ℕ) :
    (if r = 0 then (d : ℝ) * S.radialMoment a b 1 else
      S.radialMoment a b (r - 1) + ((d : ℝ) - 1) * S.radialMoment a b (r + 1)) =
      D.eigenvalue b * S.radialMoment a b r := by
  have h := S.pairMoment_eigenrelation a b G.root (G.pointAtDistance r)
  simp_rw [S.pairMoment_eq_radial] at h
  rw [G.radial_sum, G.root_distance] at h
  exact h

/-- Covariance is derived from uniform marginals, radial invariance, and the
covering eigenrelation. It is not a field of the sampling contract. -/
theorem exact_covariance (hd : 2 ≤ d) (a b : Fin c) (x y : T) :
    (∫ ω, S.coordinate a x ω * S.coordinate b y ω ∂P) =
      (if a = b then 1 else 0) *
        sphericalCovariance d (D.eigenvalue a) (G.distance x y) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  have hone : (d : ℝ) * S.radialMoment a b 1 =
      D.eigenvalue b * S.radialMoment a b 0 := by
    simpa using S.radialMoment_equation a b 0
  have hrec (n : ℕ) : S.radialMoment a b n +
      ((d : ℝ) - 1) * S.radialMoment a b (n + 2) =
        D.eigenvalue b * S.radialMoment a b (n + 1) := by
    simpa using S.radialMoment_equation a b (n + 1)
  have hrad := covariance_eq_scaled_spherical d (D.eigenvalue b)
    (if a = b then 1 else 0) hd0 hd1 (S.radialMoment a b)
    (S.radialMoment_zero a b) hone hrec (G.distance x y)
  change S.pairMoment a b x y = _
  rw [S.pairMoment_eq_radial, hrad]
  by_cases hab : a = b <;> simp [hab]

/-- All sampled sites have the same exact scalar empirical fourth moment. -/
theorem coordinate_fourth (a : Fin c) (x : T) :
    (∫ ω, S.coordinate a x ω ^ 4 ∂P) =
      (N : ℝ) * ∑ v, D.eigenvector a v ^ 4 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt D.size_pos)
  have hs : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg _)
  have hs4 : Real.sqrt (N : ℝ) ^ 4 = (N : ℝ) ^ 2 := by
    calc
      _ = (Real.sqrt (N : ℝ) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hs]
  change (∫ ω, (Real.sqrt N * D.eigenvector a (S.image ω x)) ^ 4 ∂P) = _
  rw [S.integral_eval x (fun v => (Real.sqrt N * D.eigenvector a v) ^ 4)]
  simp_rw [mul_pow, hs4]
  rw [← Finset.mul_sum]
  field_simp
  ring

theorem coordinate_mean_zero (a : Fin c) (x : T)
    (ha : D.eigenvalue a ≠ (d : ℝ)) :
    (∫ ω, S.coordinate a x ω ∂P) = 0 := by
  change (∫ ω, Real.sqrt N * D.eigenvector a (S.image ω x) ∂P) = 0
  rw [S.integral_eval x (fun v => Real.sqrt N * D.eigenvector a v),
    ← Finset.mul_sum, D.eigenvector_sum_zero a ha]
  simp

/-- Actual law of any fixed finite selection of tree sites and eigenchannels. -/
def windowLaw {k m : ℕ} (a : Fin k → Fin c) (site : Fin m → T) :
    Measure ((Fin k × Fin m) → ℝ) :=
  Measure.map (fun ω (aj : Fin k × Fin m) => S.coordinate (a aj.1) (site aj.2) ω) P

theorem measurable_window {k m : ℕ} (a : Fin k → Fin c) (site : Fin m → T) :
    Measurable (fun ω (aj : Fin k × Fin m) => S.coordinate (a aj.1) (site aj.2) ω) := by
  exact measurable_pi_lambda _ (fun aj => S.measurable_coordinate _ _)

instance windowLaw_isProbability [IsProbabilityMeasure P] {k m : ℕ}
    (a : Fin k → Fin c) (site : Fin m → T) :
    IsProbabilityMeasure (S.windowLaw a site) :=
  MeasureTheory.isProbabilityMeasure_map (S.measurable_window a site).aemeasurable

theorem windowLaw_coordinate_fourth {k m : ℕ}
    (a : Fin k → Fin c) (site : Fin m → T) (aj : Fin k × Fin m) :
    (∫ z, z aj ^ 4 ∂S.windowLaw a site) =
      (N : ℝ) * ∑ v, D.eigenvector (a aj.1) v ^ 4 := by
  rw [windowLaw, integral_map (S.measurable_window a site).aemeasurable
    (((continuous_apply aj).pow 4).measurable.aestronglyMeasurable)]
  exact S.coordinate_fourth (a aj.1) (site aj.2)

theorem windowLaw_integrable_coordinate_fourth {k m : ℕ}
    (a : Fin k → Fin c) (site : Fin m → T) (aj : Fin k × Fin m) :
    Integrable (fun z => z aj ^ 4) (S.windowLaw a site) := by
  exact (integrable_map_measure (((continuous_apply aj).pow 4).measurable.aestronglyMeasurable)
    (S.measurable_window a site).aemeasurable).mpr
      (S.integrable_coordinate_pow (a aj.1) (site aj.2) 4)

theorem windowLaw_exact_covariance (hd : 2 ≤ d) {k m : ℕ}
    (a : Fin k → Fin c) (ha : Function.Injective a) (site : Fin m → T)
    (aj bl : Fin k × Fin m) :
    (∫ z, z aj * z bl ∂S.windowLaw a site) =
      (if aj.1 = bl.1 then 1 else 0) *
        sphericalCovariance d (D.eigenvalue (a aj.1))
          (G.distance (site aj.2) (site bl.2)) := by
  rw [windowLaw, integral_map (S.measurable_window a site).aemeasurable
    (((continuous_apply aj).mul (continuous_apply bl)).measurable.aestronglyMeasurable)]
  simpa only [ha.eq_iff] using S.exact_covariance hd (a aj.1) (a bl.1) (site aj.2) (site bl.2)

end GaussianWave.CoverSampling
