import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Entire products with locally summable deviations from one. Products are
allowed to vanish; nonvanishing and logarithmic derivatives are proved at
points where the factors do not vanish. -/
noncomputable section
open scoped Topology BigOperators
open Filter
namespace BourgadeHuang

variable {ι : Type*}

def LocallySummableProduct (f : ι → ℂ → ℂ) : Prop :=
  ∀ R : ℝ, 0 < R → ∃ b : ι → ℝ, Summable b ∧
    ∀ i z, ‖z‖ ≤ R → ‖f i z-1‖ ≤ b i

theorem LocallySummableProduct.multipliable {f : ι → ℂ → ℂ}
    (hb : LocallySummableProduct f) (z : ℂ) : Multipliable (fun i => f i z) := by
  obtain ⟨b,hb,hbound⟩ := hb (‖z‖+1) (by positivity)
  have hs : Summable (fun i => ‖f i z-1‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hbound i z (by linarith)) hb
  simpa only [add_sub_cancel] using multipliable_one_add_of_summable hs

/-- A summable bound on deviations from one controls the entire product. -/
theorem norm_tprod_le_exp_tsum {f : ι → ℂ} {b : ι → ℝ}
    (hb : Summable b) (hbound : ∀ i, ‖f i-1‖ ≤ b i) :
    ‖∏' i,f i‖ ≤ Real.exp (∑' i,b i) := by
  classical
  have hs : Summable (fun i => ‖f i-1‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hbound hb
  have hm : Multipliable f := by
    simpa only [add_sub_cancel] using multipliable_one_add_of_summable hs
  have hi (i : ι) : ‖f i‖ ≤ Real.exp (b i) := by
    calc
      ‖f i‖ = ‖(f i-1)+1‖ := by ring_nf
      _ ≤ ‖f i-1‖+1 := by simpa using norm_add_le (f i-1) (1:ℂ)
      _ ≤ b i+1 := add_le_add_right (hbound i) 1
      _ ≤ Real.exp (b i) := Real.add_one_le_exp _
  have hI (I : Finset ι) : ‖∏ i ∈ I,f i‖ ≤ Real.exp (∑ i ∈ I,b i) := by
    calc
      ‖∏ i ∈ I,f i‖ ≤ ∏ i ∈ I,‖f i‖ := Finset.norm_prod_le _ _
      _ ≤ ∏ i ∈ I,Real.exp (b i) :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hi i)
      _ = Real.exp (∑ i ∈ I,b i) := (Real.exp_sum _ _).symm
  exact le_of_tendsto_of_tendsto (Filter.Tendsto.norm hm.hasProd) (Filter.Tendsto.rexp hb.hasSum)
    (Filter.Eventually.of_forall hI)

theorem LocallySummableProduct.ne_zero {f : ι → ℂ → ℂ}
    (hb : LocallySummableProduct f) {z : ℂ} (hz : ∀ i, f i z ≠ 0) :
    (∏' i, f i z) ≠ 0 := by
  obtain ⟨b,hb,hbound⟩ := hb (‖z‖+1) (by positivity)
  have hs : Summable (fun i => f i z-1) :=
    Summable.of_norm_bounded b hb (fun i => hbound i z (by linarith))
  have hl : Summable (fun i => Complex.log (f i z)) := by
    simpa only [add_sub_cancel] using Complex.summable_log_one_add_of_summable hs
  rw [← Complex.cexp_tsum_eq_tprod hz hl]
  exact Complex.exp_ne_zero _

theorem locallySummableProduct_uniform_closedBall {f : ι → ℂ → ℂ}
    (hf : ∀ i, Continuous (f i)) (hb : LocallySummableProduct f)
    (R : ℝ) (hR : 0 < R) :
    TendstoUniformlyOn (fun I : Finset ι => fun z => ∏ i ∈ I, f i z)
      (fun z => ∏' i, f i z) atTop (Metric.closedBall (0:ℂ) R) := by
  classical
  let K := Metric.closedBall (0:ℂ) R
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall (0:ℂ) R)
  letI : Nonempty K := ⟨⟨0,Metric.mem_closedBall_self hR.le⟩⟩
  let F : ι → C(K,ℂ) := fun i => ⟨fun z => f i z,(hf i).comp continuous_subtype_val⟩
  obtain ⟨b,hbs,hbound⟩ := hb R hR
  have hb0 (i : ι) : 0 ≤ b i := (norm_nonneg _).trans (hbound i 0 (by simpa using hR.le))
  have hnorm (i : ι) : ‖F i-1‖ ≤ b i := by
    apply (ContinuousMap.norm_le _ (hb0 i)).mpr
    intro z
    exact hbound i z (by simpa only [K,Metric.mem_closedBall,dist_zero_right] using z.property)
  have hs : Summable (fun i => ‖F i-1‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hnorm hbs
  have hm : Multipliable F := by
    simpa only [add_sub_cancel] using multipliable_one_add_of_summable hs
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hm.hasProd) ε hε] with I hI
  intro z hz
  have h := ContinuousMap.norm_coe_le_norm ((∏ i ∈ I,F i)-(∏' i,F i)) (⟨z,hz⟩:K)
  have ht : (∏' i,F i) (⟨z,hz⟩:K) = ∏' i,f i z := (ContinuousMap.tprod_apply hm _).symm
  have hp : (∏ i ∈ I,F i) (⟨z,hz⟩:K) = ∏ i ∈ I,f i z := by simp [F]
  rw [ContinuousMap.sub_apply,hp,ht] at h
  rw [dist_eq_norm] at hI
  simpa only [dist_eq_norm,norm_sub_rev] using h.trans_lt hI

theorem LocallySummableProduct.tendstoLocallyUniformly {f : ι → ℂ → ℂ}
    (hb : LocallySummableProduct f) (hf : ∀ i, Continuous (f i)) :
    TendstoLocallyUniformlyOn (fun I : Finset ι => fun z => ∏ i ∈ I, f i z)
      (fun z => ∏' i, f i z) atTop Set.univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _ hK
  obtain ⟨R,hR,hKR⟩ := hK.isBounded.subset_closedBall_lt 0 (0:ℂ)
  exact (locallySummableProduct_uniform_closedBall hf hb R hR).mono hKR

theorem LocallySummableProduct.differentiable {f : ι → ℂ → ℂ}
    (hb : LocallySummableProduct f) (hf : ∀ i, Differentiable ℂ (f i)) :
    Differentiable ℂ (fun z => ∏' i, f i z) := by
  classical
  have h := (hb.tendstoLocallyUniformly (fun i => (hf i).continuous)).differentiableOn
    (Filter.Eventually.of_forall (fun I =>
      (Differentiable.finset_prod (fun i _ => hf i)).differentiableOn)) isOpen_univ
  exact differentiableOn_univ.mp h

theorem hasDerivAt_finset_prod_logarithmic (f : ι → ℂ → ℂ) (g : ι → ℂ)
    (z : ℂ) (I : Finset ι) (hf : ∀ i ∈ I, HasDerivAt (f i) (g i*f i z) z) :
    HasDerivAt (fun w => ∏ i ∈ I,f i w) ((∑ i ∈ I,g i)*(∏ i ∈ I,f i z)) z := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using hasDerivAt_const z (1:ℂ)
  | @insert i I hi ih =>
    have h := (hf i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    simp only [Finset.prod_insert hi,Finset.sum_insert hi]
    convert h using 1 <;> ring

theorem LocallySummableProduct.hasDerivAt {f : ι → ℂ → ℂ}
    (hb : LocallySummableProduct f) (hf : ∀ i, Differentiable ℂ (f i))
    (z : ℂ) (g : ι → ℂ) (hg : Summable g)
    (hd : ∀ i, HasDerivAt (f i) (g i*f i z) z) :
    HasDerivAt (fun w => ∏' i,f i w) ((∑' i,g i)*(∏' i,f i z)) z := by
  classical
  have hp := hb.tendstoLocallyUniformly (fun i => (hf i).continuous)
  have hder := (hp.deriv (Filter.Eventually.of_forall (fun I =>
    (Differentiable.finset_prod (fun i _ => hf i)).differentiableOn)) isOpen_univ).tendsto_at
      (Set.mem_univ z)
  have he (I : Finset ι) : deriv (fun w => ∏ i ∈ I,f i w) z =
      (∑ i ∈ I,g i)*(∏ i ∈ I,f i z) :=
    (hasDerivAt_finset_prod_logarithmic f g z I (fun i _ => hd i)).deriv
  simp only [Function.comp_def,he] at hder
  have hlim := Filter.Tendsto.mul hg.hasSum ((hb.multipliable z).hasProd)
  have hval := tendsto_nhds_unique hder hlim
  rw [← hval]
  exact (hb.differentiable hf z).hasDerivAt

end BourgadeHuang
