import BourgadeHuang.FactorialTopology
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Tight

/-!
# Compact families of locally finite counting measures

Compact families are constructed as images of products of finite particle lists
in closed annuli. Each annulus has finitely many available slots, and an inactive
slot contributes the zero measure. The annuli escape to infinity, so the resulting
countable sum is locally finite and every vague test sees only finitely many slots.
-/
noncomputable section
open scoped BigOperators Topology CompactlySupported ENNReal
open MeasureTheory Filter

namespace BourgadeHuang

/-- The closed annulus of radii `n` and `n + 1` on the real line. -/
def realAnnulus (n : ℕ) : Set ℝ :=
  Set.Icc (-(n : ℝ) - 1) (-(n : ℝ)) ∪ Set.Icc (n : ℝ) ((n : ℝ) + 1)

theorem isCompact_realAnnulus (n : ℕ) : IsCompact (realAnnulus n) :=
  isCompact_Icc.union isCompact_Icc

theorem le_abs_of_mem_realAnnulus {n : ℕ} {x : ℝ} (hx : x ∈ realAnnulus n) :
    (n : ℝ) ≤ |x| := by
  rcases hx with hx | hx
  · exact (by linarith [hx.2] : (n : ℝ) ≤ -x).trans (neg_le_abs x)
  · exact hx.1.trans (le_abs_self x)

theorem abs_le_of_mem_realAnnulus {n : ℕ} {x : ℝ} (hx : x ∈ realAnnulus n) :
    |x| ≤ (n : ℝ) + 1 := by
  apply abs_le.mpr
  rcases hx with hx | hx <;> constructor <;> linarith [hx.1, hx.2, Nat.cast_nonneg (α := ℝ) n]

instance (n : ℕ) : CompactSpace (realAnnulus n) :=
  isCompact_iff_compactSpace.mp (isCompact_realAnnulus n)

/-- The first component activates or deactivates an annular particle slot. -/
abbrev AnnularSlot (n : ℕ) := Bool × realAnnulus n

/-- A finite, prescribed number of slots in each annulus. -/
abbrev AnnularSlots (B : ℕ → ℕ) := ∀ n, Fin (B n) → AnnularSlot n

instance (B : ℕ → ℕ) : CompactSpace (AnnularSlots B) := inferInstance

/-- The measure contributed by one optional atom. -/
def annularSlotMeasure {n : ℕ} (s : AnnularSlot n) : Measure ℝ :=
  if s.1 then Measure.dirac s.2.val else 0

/-- The finite measure in one annulus. -/
def annularBlockMeasure {B : ℕ → ℕ} (s : AnnularSlots B) (n : ℕ) : Measure ℝ :=
  ∑ i, annularSlotMeasure (s n i)

/-- The locally finite sum of all annular blocks. -/
def annularMeasure {B : ℕ → ℕ} (s : AnnularSlots B) : Measure ℝ :=
  Measure.sum (annularBlockMeasure s)

/-- Actual integer count of active annular slots lying in a set. -/
def annularBlockCount {B : ℕ → ℕ} (s : AnnularSlots B) (n : ℕ) (K : Set ℝ) : ℕ :=
  by classical exact ∑ i, if (s n i).1 = true ∧ (s n i).2.val ∈ K then 1 else 0

theorem annularBlockMeasure_apply {B : ℕ → ℕ} (s : AnnularSlots B) (n : ℕ)
    {K : Set ℝ} (hK : MeasurableSet K) :
    annularBlockMeasure s n K = (annularBlockCount s n K : ℝ≥0∞) := by
  classical
  rw [annularBlockMeasure, Measure.finset_sum_apply]
  simp only [annularBlockCount, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hb : (s n i).1 = true
  · by_cases hx : (s n i).2.val ∈ K <;> simp [annularSlotMeasure, hb, Measure.dirac_apply, hK, hx]
  · simp [annularSlotMeasure, hb]

/-- A compact set meets only finitely many of the escaping annular blocks. -/
theorem annularBlockMeasure_eventually_zero {B : ℕ → ℕ} (s : AnnularSlots B)
    {K : Set ℝ} (hK : IsCompact K) :
    ∃ M : ℕ, ∀ n, M ≤ n → annularBlockMeasure s n K = 0 := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨M, hM⟩ := exists_nat_gt R
  refine ⟨M, ?_⟩
  intro n hn
  rw [annularBlockMeasure, Measure.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hx : (s n i).2.val ∉ K := by
    intro hx
    have hr := hKR _ hx
    have hn' : (M : ℝ) ≤ n := by exact_mod_cast hn
    have hs := le_abs_of_mem_realAnnulus (s n i).2.property
    rw [Real.norm_eq_abs] at hr
    linarith
  by_cases hb : (s n i).1 = true <;>
    simp [annularSlotMeasure, hb, Measure.dirac_apply, hK.measurableSet, hx]

/-- Compact-set masses are finite sums of actual natural-number slot counts. -/
theorem annularMeasure_compact_integer {B : ℕ → ℕ} (s : AnnularSlots B)
    {K : Set ℝ} (hK : IsCompact K) : ∃ m : ℕ, annularMeasure s K = m := by
  obtain ⟨M, hM⟩ := annularBlockMeasure_eventually_zero s hK
  refine ⟨∑ n ∈ Finset.range M, annularBlockCount s n K, ?_⟩
  rw [annularMeasure, Measure.sum_apply _ hK.measurableSet,
    tsum_eq_sum (s := Finset.range M) (fun n hn => hM n (Nat.le_of_not_gt (by simpa using hn)))]
  simp only [annularBlockMeasure_apply s _ hK.measurableSet, Nat.cast_sum]

instance {B : ℕ → ℕ} (s : AnnularSlots B) : IsLocallyFiniteMeasure (annularMeasure s) where
  finiteAtNhds x := by
    obtain ⟨m, hm⟩ := annularMeasure_compact_integer s
      (K := Set.Icc (x - 1) (x + 1)) isCompact_Icc
    refine ⟨Set.Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
    rw [hm]
    exact ENNReal.natCast_lt_top m

/-- Every annular slot configuration is a genuine locally finite integer measure. -/
def annularConfiguration {B : ℕ → ℕ} (s : AnnularSlots B) : LocalCountingMeasure where
  measure := annularMeasure s
  locallyFinite := inferInstance
  integer_compacts := fun _ hK => annularMeasure_compact_integer s hK

/-- Value of a compact test on an active slot. -/
def annularSlotTest (f : ℝ →C_c ℝ) {n : ℕ} (s : AnnularSlot n) : ℝ :=
  if s.1 then f s.2.val else 0

theorem continuous_annularSlotTest (f : ℝ →C_c ℝ) (n : ℕ) :
    Continuous (annularSlotTest f : AnnularSlot n → ℝ) := by
  have hb : Continuous (fun b : Bool => if b then (1 : ℝ) else 0) :=
    continuous_of_discreteTopology
  have hf : Continuous (fun s : AnnularSlot n => f s.2.val) :=
    f.continuous.comp (continuous_subtype_val.comp continuous_snd)
  convert (hb.comp continuous_fst).mul hf using 1
  funext s
  cases h : s.1 <;> simp [annularSlotTest, h]

theorem integral_annularBlockMeasure {B : ℕ → ℕ} (s : AnnularSlots B)
    (f : ℝ →C_c ℝ) (n : ℕ) :
    (∫ x, f x ∂annularBlockMeasure s n) = ∑ i, annularSlotTest f (s n i) := by
  classical
  rw [annularBlockMeasure, integral_finset_sum_measure]
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hb : (s n i).1 = true <;> simp [annularSlotMeasure, annularSlotTest, hb]
  · intro i _
    by_cases hb : (s n i).1 = true <;> simp [annularSlotMeasure, hb, integrable_dirac]

/-- A compactly supported test ignores every sufficiently distant annular slot,
with the same cutoff for all configurations. -/
theorem exists_annular_test_cutoff (f : ℝ →C_c ℝ) :
    ∃ M : ℕ, ∀ n, M ≤ n → ∀ s : AnnularSlot n, annularSlotTest f s = 0 := by
  obtain ⟨R, hR, hKR⟩ := f.hasCompactSupport.isBounded.exists_pos_norm_le
  obtain ⟨M, hM⟩ := exists_nat_gt R
  refine ⟨M, ?_⟩
  intro n hn s
  have hx : s.2.val ∉ tsupport f := by
    intro hx
    have hr := hKR _ hx
    have hn' : (M : ℝ) ≤ n := by exact_mod_cast hn
    have hs := le_abs_of_mem_realAnnulus s.2.property
    rw [Real.norm_eq_abs] at hr
    linarith
  have hf := image_eq_zero_of_nmem_tsupport hx
  simp [annularSlotTest, hf]

theorem integral_annularConfiguration {B : ℕ → ℕ} (s : AnnularSlots B)
    (f : ℝ →C_c ℝ) (M : ℕ)
    (hM : ∀ n, M ≤ n → ∀ a : AnnularSlot n, annularSlotTest f a = 0) :
    (∫ x, f x ∂(annularConfiguration s).measure) =
      ∑ n ∈ Finset.range M, ∑ i, annularSlotTest f (s n i) := by
  have hi : Integrable f (annularMeasure s) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  change (∫ x, f x ∂annularMeasure s) = _
  rw [annularMeasure, integral_sum_measure hi]
  rw [tsum_eq_sum (s := Finset.range M) (fun n hn => ?_)]
  · simp_rw [integral_annularBlockMeasure]
  · rw [integral_annularBlockMeasure]
    apply Finset.sum_eq_zero
    intro i _
    exact hM n (Nat.le_of_not_gt (by simpa using hn)) (s n i)

/-- The map from a compact product of annular particle slots to counting measures
is continuous for the actual initial vague topology in `Model.lean`. -/
theorem continuous_annularConfiguration (B : ℕ → ℕ) :
    Continuous (annularConfiguration : AnnularSlots B → LocalCountingMeasure) := by
  apply continuous_iInf_rng.mpr
  intro f
  apply continuous_induced_rng.mpr
  obtain ⟨M, hM⟩ := exists_annular_test_cutoff f
  have heq : (fun s : AnnularSlots B => ∫ x, f x ∂(annularConfiguration s).measure) =
      fun s => ∑ n ∈ Finset.range M, ∑ i, annularSlotTest f (s n i) := by
    funext s
    exact integral_annularConfiguration s f M hM
  rw [show (fun a : LocalCountingMeasure => ∫ x, f x ∂a.measure) ∘ annularConfiguration =
    (fun s : AnnularSlots B => ∫ x, f x ∂(annularConfiguration s).measure) from rfl, heq]
  apply continuous_finset_sum
  intro n hn
  apply continuous_finset_sum
  intro i hi
  exact (continuous_annularSlotTest f n).comp ((continuous_apply i).comp (continuous_apply n))

/-- An explicitly constructed compact family of locally finite counting measures. -/
def annularCompactFamily (B : ℕ → ℕ) : Set LocalCountingMeasure :=
  Set.range (annularConfiguration : AnnularSlots B → LocalCountingMeasure)

theorem isCompact_annularCompactFamily (B : ℕ → ℕ) : IsCompact (annularCompactFamily B) :=
  isCompact_range (continuous_annularConfiguration B)

/-- Half-open annuli partition the real line without duplicating boundary atoms. -/
def annularCell (n : ℕ) : Set ℝ :=
  {x | (n : ℝ) ≤ |x| ∧ |x| < (n : ℝ) + 1}

theorem measurableSet_annularCell (n : ℕ) : MeasurableSet (annularCell n) :=
  measurableSet_Ico.preimage continuous_abs.measurable

theorem annularCell_subset_realAnnulus (n : ℕ) : annularCell n ⊆ realAnnulus n := by
  intro x hx
  by_cases h : 0 ≤ x
  · right
    simpa [abs_of_nonneg h] using And.intro hx.1 hx.2.le
  · left
    rw [annularCell, Set.mem_setOf_eq, abs_of_neg (lt_of_not_ge h)] at hx
    constructor <;> linarith [hx.1, hx.2]

theorem pairwise_disjoint_annularCell : Pairwise (fun n m => Disjoint (annularCell n) (annularCell m)) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro x hn hm
  have hn' : ⌊|x|⌋₊ = n := (Nat.floor_eq_iff (abs_nonneg x)).mpr hn
  have hm' : ⌊|x|⌋₊ = m := (Nat.floor_eq_iff (abs_nonneg x)).mpr hm
  exact hnm (hn'.symm.trans hm')

theorem iUnion_annularCell : (⋃ n, annularCell n) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.mpr ⟨⌊|x|⌋₊, Nat.floor_le (abs_nonneg x), Nat.lt_floor_add_one |x|⟩

/-- An inactive slot, used to pad a particle list to its prescribed bound. -/
def inactiveAnnularSlot (n : ℕ) : AnnularSlot n :=
  (false, ⟨n, Or.inr ⟨le_rfl, by linarith⟩⟩)

@[simp] theorem annularSlotMeasure_inactive (n : ℕ) :
    annularSlotMeasure (inactiveAnnularSlot n) = 0 := rfl

/-- Every bounded annular restriction can be encoded by a fixed number of slots. -/
theorem exists_annular_slots_of_count_le (ξ : LocalCountingMeasure) (n B : ℕ)
    (hB : ξ.measure (realAnnulus n) ≤ B) :
    ∃ s : Fin B → AnnularSlot n,
      (∑ i, annularSlotMeasure (s i)) = ξ.measure.restrict (annularCell n) := by
  classical
  obtain ⟨N, x, hx, hμ, hN⟩ :=
    ξ.exists_compact_particle_list_with_multiplicity (isCompact_realAnnulus n)
  have hNB : N ≤ B := by exact_mod_cast hN ▸ hB
  let t : Fin N → AnnularSlot n := fun i =>
    (decide (x i ∈ annularCell n), ⟨x i, hx i⟩)
  let e : Fin N → Fin B := Fin.castLE hNB
  let s : Fin B → AnnularSlot n := Function.extend e t (fun _ => inactiveAnnularSlot n)
  have he : Function.Injective e := Fin.castLE_injective hNB
  have hs : (fun i => annularSlotMeasure (s i)) =
      Function.extend e (fun i => annularSlotMeasure (t i)) 0 := by
    funext i
    exact Function.apply_extend (g := t) annularSlotMeasure e (fun _ => inactiveAnnularSlot n) i
  refine ⟨s, ?_⟩
  rw [← Measure.sum_fintype, hs, Measure.sum_extend_zero he, Measure.sum_fintype]
  rw [← Measure.restrict_restrict_of_subset (annularCell_subset_realAnnulus n), hμ]
  ext A hA
  rw [Measure.restrict_apply hA, Measure.finset_sum_apply, Measure.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x i ∈ annularCell n <;>
    simp [t, annularSlotMeasure, hi, Measure.dirac_apply, hA,
      hA.inter (measurableSet_annularCell n), Set.indicator_apply]

/-- Prescribing one finite compact-count bound for each annulus places the whole
configuration in an explicitly constructed compact family. -/
theorem mem_annularCompactFamily_of_count_le (ξ : LocalCountingMeasure) (B : ℕ → ℕ)
    (hB : ∀ n, ξ.measure (realAnnulus n) ≤ B n) : ξ ∈ annularCompactFamily B := by
  choose s hs using fun n => exists_annular_slots_of_count_le ξ n (B n) (hB n)
  refine ⟨s, ?_⟩
  have hm : (annularConfiguration s).measure = ξ.measure := by
    change Measure.sum (annularBlockMeasure s) = ξ.measure
    have he : annularBlockMeasure s = fun n => ξ.measure.restrict (annularCell n) := by
      funext n
      exact hs n
    rw [he, ← Measure.restrict_iUnion pairwise_disjoint_annularCell measurableSet_annularCell,
      iUnion_annularCell, Measure.restrict_univ]
  cases ξ
  cases he : annularConfiguration s
  rw [he] at hm
  simpa only [LocalCountingMeasure.mk.injEq] using hm

/-- Compact continuous integrals determine a locally finite counting measure. -/
theorem LocalCountingMeasure.ext_integral {ξ ζ : LocalCountingMeasure}
    (h : ∀ f : ℝ →C_c ℝ, (∫ x, f x ∂ξ.measure) = ∫ x, f x ∂ζ.measure) : ξ = ζ := by
  have hK : ∀ K : Set ℝ, IsCompact K → ξ.measure K = ζ.measure K := by
    intro K hK
    rw [hK.measure_eq_biInf_integral_hasCompactSupport ξ.measure,
      hK.measure_eq_biInf_integral_hasCompactSupport ζ.measure]
    congr 1
    funext f
    congr 1
    funext hf
    congr 1
    funext hs
    congr 1
    funext h1
    congr 1
    funext h0
    exact congrArg ENNReal.ofReal (h ⟨⟨f, hf⟩, hs⟩)
  have hm : ξ.measure = ζ.measure := by
    apply Measure.ext
    intro A hA
    rw [hA.measure_eq_iSup_isCompact ξ.measure, hA.measure_eq_iSup_isCompact ζ.measure]
    congr 1
    funext K
    congr 1
    funext hKA
    congr 1
    funext hcomp
    exact hK K hcomp
  cases ξ
  cases ζ
  simpa only [LocalCountingMeasure.mk.injEq] using hm

/-- The initial vague topology is Hausdorff because compact tests separate measures. -/
instance : T2Space LocalCountingMeasure :=
  T2Space.of_injective_continuous
    (f := fun ξ : LocalCountingMeasure => fun f : ℝ →C_c ℝ => ∫ x, f x ∂ξ.measure)
    (fun _ _ h => LocalCountingMeasure.ext_integral (congrFun h))
    (continuous_pi fun f => continuous_linearStatistic f)

/-- A uniform first-moment bound gives arbitrarily small tails above one natural
threshold, uniformly over the family. -/
theorem exists_nat_uniform_tail_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (f : ℕ → Ω → ℝ)
    (hnonneg : ∀ N ω, 0 ≤ f N ω) (hi : ∀ N, Integrable (f N) μ)
    (C : ℝ) (hC : ∀ N, (∫ ω, f N ω ∂μ) ≤ C) {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℕ, ∀ N, μ {ω | (B : ℝ) < f N ω} ≤ ENNReal.ofReal δ := by
  obtain ⟨B, hB⟩ := exists_nat_gt (max 0 (C / δ))
  have hBpos : 0 < (B : ℝ) := (le_max_left _ _).trans_lt hB
  have hCB : C ≤ (B : ℝ) * δ :=
    ((div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hB)).le
  refine ⟨B, fun N => ?_⟩
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (Filter.Eventually.of_forall (hnonneg N)) (hi N) (B : ℝ)
  have hr : (μ {ω | (B : ℝ) ≤ f N ω}).toReal ≤ δ := by
    change (B : ℝ) * (μ {ω | (B : ℝ) ≤ f N ω}).toReal ≤ _ at hMarkov
    nlinarith [hC N]
  calc
    μ {ω | (B : ℝ) < f N ω} ≤ μ {ω | (B : ℝ) ≤ f N ω} :=
      measure_mono (by
        intro ω hω
        exact le_of_lt (show (B : ℝ) < f N ω from hω))
    _ = ENNReal.ofReal ((μ {ω | (B : ℝ) ≤ f N ω}).toReal) :=
      (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hr

/-- Annular counts are bounded by the counts in centered compact intervals. -/
theorem realAnnulus_subset_Icc (n : ℕ) :
    realAnnulus n ⊆ Set.Icc (-(n : ℝ) - 1) ((n : ℝ) + 1) := by
  intro x hx
  have h := abs_le_of_mem_realAnnulus hx
  have := abs_le.mp h
  constructor <;> linarith [this.1, this.2]

/-- Uniform compact count moments produce an actual compact set capturing all
configuration laws up to any prescribed error. Only their first moments are used. -/
theorem exists_compact_capture_of_uniformCountMoments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (ξ : ℕ → Ω → LocalCountingMeasure)
    (hc : UniformCountMoments μ ξ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set LocalCountingMeasure, IsCompact K ∧
      ∀ N, μ (ξ N ⁻¹' Kᶜ) ≤ ENNReal.ofReal ε := by
  let δ : ℕ → ℝ := fun n => ε / 2 / 2 ^ n
  have hδ : ∀ n, 0 < δ n := fun n => by dsimp [δ]; positivity
  have hb : ∀ n : ℕ, ∃ B : ℕ, ∀ N,
      μ {ω | (B : ℝ) < ((ξ N ω).measure (Set.Icc (-(n : ℝ) - 1) ((n : ℝ) + 1))).toReal}
        ≤ ENNReal.ofReal (δ n) := by
    intro n
    obtain ⟨hi, C, hC⟩ := hc (-(n : ℝ) - 1) ((n : ℝ) + 1) 1
    simp only [pow_one] at hi hC
    exact exists_nat_uniform_tail_bound _ (fun _ _ => ENNReal.toReal_nonneg) hi C hC (hδ n)
  choose B hB using hb
  refine ⟨annularCompactFamily B, isCompact_annularCompactFamily B, fun N => ?_⟩
  have hsub : ξ N ⁻¹' (annularCompactFamily B)ᶜ ⊆
      ⋃ n, {ω | (B n : ℝ) <
        ((ξ N ω).measure (Set.Icc (-(n : ℝ) - 1) ((n : ℝ) + 1))).toReal} := by
    intro ω hω
    by_contra hh
    have hcounts : ∀ n, (ξ N ω).measure (realAnnulus n) ≤ B n := by
      intro n
      have hn : ((ξ N ω).measure (Set.Icc (-(n : ℝ) - 1) ((n : ℝ) + 1))).toReal ≤ (B n : ℝ) := by
        by_contra hn
        exact hh (Set.mem_iUnion.mpr ⟨n, lt_of_not_ge hn⟩)
      calc
        (ξ N ω).measure (realAnnulus n) ≤
          (ξ N ω).measure (Set.Icc (-(n : ℝ) - 1) ((n : ℝ) + 1)) :=
          measure_mono (realAnnulus_subset_Icc n)
        _ ≤ B n := by
          apply (ENNReal.toReal_le_toReal (isCompact_Icc.measure_ne_top) (ENNReal.natCast_ne_top _)).mp
          simpa using hn
    exact hω (mem_annularCompactFamily_of_count_le _ B hcounts)
  calc
    μ (ξ N ⁻¹' (annularCompactFamily B)ᶜ) ≤
        μ (⋃ n, {ω | (B n : ℝ) <
          ((ξ N ω).measure (Set.Icc (-(n : ℝ) - 1) ((n : ℝ) + 1))).toReal}) := measure_mono hsub
    _ ≤ ∑' n, μ {ω | (B n : ℝ) <
          ((ξ N ω).measure (Set.Icc (-(n : ℝ) - 1) ((n : ℝ) + 1))).toReal} := measure_iUnion_le _
    _ ≤ ∑' n, ENNReal.ofReal (δ n) := ENNReal.tsum_le_tsum (fun n => hB n N)
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (hδ n).le)
        (summable_geometric_two' ε), tsum_geometric_two' ε]

/-- Uniform compact count moments imply tightness of the genuine vague laws.
Compactness is proved by the annular particle construction, not supplied as an assumption. -/
theorem isTightMeasureSet_of_uniformCountMoments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (ξ : ℕ → Ω → LocalCountingMeasure)
    (hm : ∀ N, Measurable (ξ N)) (hc : UniformCountMoments μ ξ) :
    IsTightMeasureSet (Set.range (fun N => Measure.map (ξ N) μ)) := by
  rw [IsTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases htop : ε = ∞
  · exact ⟨∅, isCompact_empty, fun _ _ => by simp [htop]⟩
  have hεreal : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  obtain ⟨K, hK, hcapture⟩ := exists_compact_capture_of_uniformCountMoments ξ hc hεreal
  refine ⟨K, hK, ?_⟩
  rintro _ ⟨N, rfl⟩
  rw [Measure.map_apply (hm N) hK.measurableSet.compl]
  simpa only [ENNReal.ofReal_toReal htop] using hcapture N

/-- The same explicit compact families are sequentially compact, since their
annular slot domains are countable products of compact metric spaces. -/
theorem isSeqCompact_annularCompactFamily (B : ℕ → ℕ) :
    IsSeqCompact (annularCompactFamily B) :=
  IsSeqCompact.range (continuous_annularConfiguration B).seqContinuous

/-- Deterministic relative sequential compactness under uniform local count bounds. -/
theorem exists_vaguely_convergent_subsequence_of_count_bound
    (ξ : ℕ → LocalCountingMeasure) (B : ℕ → ℕ)
    (hB : ∀ N n, (ξ N).measure (realAnnulus n) ≤ B n) :
    ∃ (ζ : LocalCountingMeasure) (r : ℕ → ℕ), StrictMono r ∧
      Tendsto (ξ ∘ r) atTop (𝓝 ζ) := by
  obtain ⟨ζ, _, r, hr, hconv⟩ := isSeqCompact_annularCompactFamily B
    (fun N => mem_annularCompactFamily_of_count_le (ξ N) B (hB N))
  exact ⟨ζ, r, hr, hconv⟩

end BourgadeHuang
