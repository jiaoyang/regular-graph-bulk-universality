import GeneralizedBulk.Gaussian.StratifiedNormalization
import GeneralizedBulk.Graph.RawCouplingLimit

/-!
Separate raw couplings at each height suffice for normalization. Their actual
countable product supplies a common probability space; no simultaneous
analytic or infinite-dimensional switched coupling is assumed.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory BourgadeHuang Filter ProbabilityTheory
open scoped Topology ENNReal
namespace GeneralizedBulk.Gaussian
open Counting Analysis Graph GeneralizedSwitching Exterior

theorem independentHeight_map_eval (Q : ℕ → Measure RawPair)
    [∀ n, IsProbabilityMeasure (Q n)] (n : ℕ) :
    Measure.map (fun z : ℕ → RawPair => z n) (Measure.infinitePi Q) = Q n := by
  classical
  ext A hA
  rw [Measure.map_apply (measurable_pi_apply n) hA]
  have heq : (fun z : ℕ → RawPair => z n) ⁻¹' A = Set.pi ({n} : Finset ℕ) (fun _ => A) := by
    ext z
    simp [Set.mem_pi]
  rw [heq,Measure.infinitePi_pi _ (fun i hi => hA)]
  simp

/-- Normalization needs only separate finite-dimensional switched couplings
at the integer heights. The common coupling is constructed as a product. -/
theorem normalization_of_height_couplings
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (parameters : Parameters)
    (C1 C2 : ℝ) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hheight1 : ∀ n : ℕ, (∫ s : AnchoredCountingState,
      ‖anchoredNevanlinna s (normalizationHeight n)‖ ∂ν) ≤ C1)
    (hiheight2 : ∀ n : ℕ, Integrable (fun s : AnchoredCountingState =>
      ‖anchoredNevanlinna s (normalizationHeight n)‖ ^ 2) ν)
    (hheight2 : ∀ n : ℕ, (∫ s : AnchoredCountingState,
      ‖anchoredNevanlinna s (normalizationHeight n)‖ ^ 2 ∂ν) ≤ C2)
    (Q : ℕ → Measure RawPair) [∀ n, IsProbabilityMeasure (Q n)]
    (hfst : ∀ n, Measure.map Prod.fst (Q n) =
      Measure.map (massRawHeight ν hm parameters n) (massMarkedLaw ν parameters))
    (hsnd : ∀ n, Measure.map Prod.snd (Q n) =
      Measure.map (massRawHeight ν hm parameters n) (massMarkedLaw ν parameters))
    (hrank : ∀ n : ℕ, ∀ᵐ x ∂Q n, ‖x.2.1 - x.1.1‖ ≤ 4 / ((n : ℝ) + 1))
    (hswitch : ∀ n, ∀ᵐ x ∂Q n, (1 + x.1.2 * switchIncrement) *
      (endpointPermutation * x.2.2 * endpointPermutation) = x.1.2) :
    Tendsto (fun n : ℕ => ∫ s : AnchoredCountingState,
      ‖anchoredNevanlinna s (normalizationHeight n) - Complex.I‖ ∂ν) atTop (𝓝 0) ∧
      (∀ᵐ a ∂ν, a.val.1.measure Set.univ = ∞) := by
  let P : Measure (ℕ → RawPair) := Measure.infinitePi Q
  have hp (n : ℕ) : MeasurePreserving (fun z : ℕ → RawPair => z n) P (Q n) :=
    ⟨measurable_pi_apply n,independentHeight_map_eval Q n⟩
  let s := fun n (z : ℕ → RawPair) => (z n).1.1
  let t := fun n (z : ℕ → RawPair) => (z n).2.1
  let M := fun n (z : ℕ → RawPair) => (z n).1.2
  let Mt := fun n (z : ℕ → RawPair) => (z n).2.2
  have hf (n : ℕ) : IdentDistrib (fun z => (s n z,M n z))
      (massRawHeight ν hm parameters n) P (massMarkedLaw ν parameters) := by
    change IdentDistrib (fun z : ℕ → RawPair => (z n).1)
      (massRawHeight ν hm parameters n) P (massMarkedLaw ν parameters)
    refine ⟨(measurable_fst.comp (measurable_pi_apply n)).aemeasurable,
      (measurable_massRawHeight ν hm parameters n).aemeasurable,?_⟩
    change Measure.map (Prod.fst ∘ (fun z : ℕ → RawPair => z n)) P = _
    rw [← Measure.map_map measurable_fst (measurable_pi_apply n),(hp n).map_eq,hfst n]
  have hr (n : ℕ) : IdentDistrib (fun z => (t n z,Mt n z))
      (massRawHeight ν hm parameters n) P (massMarkedLaw ν parameters) := by
    change IdentDistrib (fun z : ℕ → RawPair => (z n).2)
      (massRawHeight ν hm parameters n) P (massMarkedLaw ν parameters)
    refine ⟨(measurable_snd.comp (measurable_pi_apply n)).aemeasurable,
      (measurable_massRawHeight ν hm parameters n).aemeasurable,?_⟩
    change Measure.map (Prod.snd ∘ (fun z : ℕ → RawPair => z n)) P = _
    rw [← Measure.map_map measurable_snd (measurable_pi_apply n),(hp n).map_eq,hsnd n]
  have hb : Tendsto (fun n : ℕ => 4 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (4 : ℝ)
  have hRank (n) : ∀ᵐ z ∂P, ‖t n z - s n z‖ ≤ 4 / ((n : ℝ) + 1) :=
    (hp n).quasiMeasurePreserving.ae (hrank n)
  have hSwitch (n) : ∀ᵐ z ∂P, (1 + M n z * switchIncrement) *
      (endpointPermutation * Mt n z * endpointPermutation) = M n z :=
    (hp n).quasiMeasurePreserving.ae (hswitch n)
  exact ⟨mass_normalization_of_inverse_free_switched_coupling ν hm parameters C1 C2 hC1 hC2
    hheight1 hiheight2 hheight2 P s t M Mt hf hr _ hb hRank hSwitch,
    infinite_mass_of_inverse_free_switched_coupling ν hm parameters C1 C2 hC1 hC2
      hheight1 hiheight2 hheight2 P s t M Mt hf hr _ hb hRank hSwitch⟩

end GeneralizedBulk.Gaussian
