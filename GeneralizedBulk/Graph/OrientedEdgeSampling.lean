import GeneralizedBulk.Graph.StarCovariance
import GeneralizedBulk.Graph.UniformSwitching

/-! Exact star-root/ordered-leaf sampling equals uniform oriented-edge sampling. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph

theorem integral_finiteUniform {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (f : α → ℝ) :
    (∫ x, f x ∂finiteUniform α) = (Fintype.card α : ℝ)⁻¹ * ∑ a, f a := by
  rw [finiteUniform, integral_smul_measure, integral_finset_sum_measure (fun _ _ => integrable_dirac)]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]

theorem finiteUniform_map_equiv {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]
    (e : α ≃ β) : Measure.map e (finiteUniform α) = finiteUniform β := by
  have hm : Measurable e := measurable_of_finite _
  rw [finiteUniform, ← Measure.mapₗ_apply_of_measurable hm, map_smul, map_sum]
  simp only [Measure.mapₗ_apply_of_measurable hm, Measure.map_dirac hm]
  rw [Fintype.card_congr e]
  congr 1
  exact Equiv.sum_comp e Measure.dirac

end GeneralizedBulk.Graph

namespace GeneralizedBulk.External.RegularSpectralData

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def starEdgeRestriction {k : ℕ} (leaf : Fin d) (y : (Fin k × Fin (d + 1)) → ℝ)
    (ai : Fin k × Fin 2) : ℝ := ![y (ai.1, 0), y (ai.1, leaf.succ)] ai.2

theorem measurable_starEdgeRestriction {k : ℕ} (leaf : Fin d) :
    Measurable (starEdgeRestriction (k := k) leaf) := by
  apply measurable_pi_lambda
  rintro ⟨a, i⟩
  fin_cases i
  · exact measurable_pi_apply (a, 0)
  · exact measurable_pi_apply (a, leaf.succ)

def orientedEdgeMark {k : ℕ} (q : Fin k → Fin (N n) → ℝ)
    (sample : Fin (N n) × Fin d) (ai : Fin k × Fin 2) : ℝ :=
  Real.sqrt (N n) * q ai.1 (![sample.1, D.neighbor n ω sample.1 sample.2] ai.2)

def orientedEdgeLaw {k : ℕ} (q : Fin k → Fin (N n) → ℝ) : Measure ((Fin k × Fin 2) → ℝ) :=
  Measure.map (D.orientedEdgeMark n ω q) (Graph.finiteUniform (Fin (N n) × Fin d))

theorem orientedEdgeLaw_isProbability {k : ℕ} (hd : 0 < d) (q : Fin k → Fin (N n) → ℝ) :
    IsProbabilityMeasure (D.orientedEdgeLaw n ω q) := by
  letI : Nonempty (Fin (N n)) := ⟨⟨0, D.size_pos n⟩⟩
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  letI := Graph.finiteUniform_isProbability (Fin (N n) × Fin d)
  exact MeasureTheory.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

theorem starEdgeRestriction_sample {k : ℕ} (q : Fin k → Fin (N n) → ℝ)
    (sample : Fin (N n) × Equiv.Perm (Fin d)) (leaf : Fin d) :
    starEdgeRestriction leaf (D.starSample n ω q sample) =
      D.orientedEdgeMark n ω q (sample.1, sample.2 leaf) := by
  ext ai
  rcases ai with ⟨a, i⟩
  fin_cases i <;> rfl

/-- Every ordered leaf of the uniformly permuted empirical star is exactly a
uniform neighbor of its uniform root. No asymptotic sampling approximation is
used to pass from stars to oriented edges. -/
theorem starLaw_edge_marginal {k : ℕ} (q : Fin k → Fin (N n) → ℝ) (leaf : Fin d) :
    Measure.map (starEdgeRestriction leaf) (D.starLaw n ω q) = D.orientedEdgeLaw n ω q := by
  letI : IsProbabilityMeasure (D.starLaw n ω q) := D.starLaw_isProbability n ω q
  letI : IsProbabilityMeasure (D.orientedEdgeLaw n ω q) :=
    D.orientedEdgeLaw_isProbability n ω (by have h := leaf.isLt; omega) q
  have hN : (N n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos n))
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt leaf.isLt)
  have hP : (Fintype.card (Equiv.Perm (Fin d)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  letI : Nonempty (Fin d) := ⟨leaf⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  rw [integral_map (measurable_starEdgeRestriction leaf).aemeasurable F.continuous.aestronglyMeasurable,
    orientedEdgeLaw, integral_map (measurable_of_finite _).aemeasurable F.continuous.aestronglyMeasurable,
    D.integral_starLaw n ω, Graph.integral_finiteUniform]
  simp_rw [starEdgeRestriction_sample]
  simp only [Fintype.sum_prod_type]
  have he (v : Fin (N n)) := Graph.sum_perm_eval
    (fun j => F (D.orientedEdgeMark n ω q (v, j))) leaf
  simp_rw [he]
  rw [← Finset.mul_sum]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  field_simp
  ring

def simpleGraph : SimpleGraph (Fin (N n)) where
  Adj v w := D.adjacency n ω v w = 1
  symm v w h := by
    change D.adjacency n ω w v = 1
    rw [← D.symmetric n ω v w]
    exact h
  loopless v h := by
    change D.adjacency n ω v v = 1 at h
    rw [D.diagonal_zero n ω v] at h
    norm_num at h

theorem simpleGraph_regular : (D.simpleGraph n ω).IsRegularOfDegree d := by
  intro v
  have heq : (D.simpleGraph n ω).neighborFinset v = Finset.univ.image (D.neighbor n ω v) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, simpleGraph, Finset.mem_image, Finset.mem_univ, true_and]
    exact D.neighbor_exact n ω v w
  rw [SimpleGraph.degree, heq, Finset.card_image_of_injective _ (D.neighbor_injective n ω v),
    Finset.card_univ, Fintype.card_fin]

def portDartEquiv : (Fin (N n) × Fin d) ≃ (D.simpleGraph n ω).Dart where
  toFun s := ⟨(s.1, D.neighbor n ω s.1 s.2), (D.neighbor_exact n ω s.1 _).mpr ⟨s.2, rfl⟩⟩
  invFun a := (a.fst, Classical.choose ((D.neighbor_exact n ω a.fst a.snd).mp a.adj))
  left_inv s := by
    apply Prod.ext
    · rfl
    · apply D.neighbor_injective n ω s.1
      exact Classical.choose_spec ((D.neighbor_exact n ω s.1 _).mp
        ((D.neighbor_exact n ω s.1 _).mpr ⟨s.2, rfl⟩))
  right_inv a := by
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · rfl
    · exact Classical.choose_spec ((D.neighbor_exact n ω a.fst a.snd).mp a.adj)

def dartEigenMark {k : ℕ} (q : Fin k → Fin (N n) → ℝ)
    (a : (D.simpleGraph n ω).Dart) (bi : Fin k × Fin 2) : ℝ :=
  Real.sqrt (N n) * q bi.1 (![a.fst, a.snd] bi.2)

/-- The ordered-neighbor sampler is exactly the uniform dart sampler of the
simple regular graph reconstructed from the literal spectral adjacency data. -/
theorem orientedEdgeLaw_eq_dartLaw {k : ℕ} (q : Fin k → Fin (N n) → ℝ) :
    D.orientedEdgeLaw n ω q = Measure.map (D.dartEigenMark n ω q)
      (Graph.finiteUniform (D.simpleGraph n ω).Dart) := by
  rw [← Graph.finiteUniform_map_equiv (D.portDartEquiv n ω),
    Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  rfl

end GeneralizedBulk.External.RegularSpectralData
