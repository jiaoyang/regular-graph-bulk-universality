import GaussianWave.BS.Lower.CommonRecoloringEvent
import GaussianWave.BS.Lower.CoverInjectivityEvent

/-! One actual uniform-simple-RRG event controls every finite palette and
all fixed cover radii. A proved slow diagonal makes the permitted radius
grow while both its exceptional-root fraction and event failure vanish. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
set_option maxHeartbeats 1200000
namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Graph GaussianWave.BS.Reused.Graph.Configuration

def LocalCoverGoodUpTo {N m : ℕ} (K : ℕ) (G : RegularGraph N (m+2)) : Prop :=
  ∀ k : Fin (K+1),badVertexCoverRootCount G k.val < (1/(K+1 : ℝ))*(N : ℝ)

theorem local_cover_good_failure_tendsto_zero (m K : ℕ) (N : ℕ → ℕ)
    (hNinf : Tendsto N atTop atTop) (hgraphs : ∀ n,Nonempty (RegularGraph (N n) (m+2))) :
    Tendsto (fun n => (regularGraphLaw (N n) (m+2)).real {G | ¬LocalCoverGoodUpTo K G}) atTop (𝓝 0) := by
  let A (n : ℕ) (k : Fin (K+1)) := {G : RegularGraph (N n) (m+2) |
    (1/(K+1 : ℝ))*(N n : ℝ) ≤ badVertexCoverRootCount G k.val}
  have he (n : ℕ) : {G : RegularGraph (N n) (m+2) | ¬LocalCoverGoodUpTo K G}=⋃ k : Fin (K+1),A n k := by
    ext G
    simp only [LocalCoverGoodUpTo,not_forall,not_lt,Set.mem_setOf_eq,Set.mem_iUnion,A]
  have hsum : Tendsto (fun n => ∑ k : Fin (K+1),(regularGraphLaw (N n) (m+2)).real (A n k)) atTop (𝓝 0) := by
    have h := tendsto_finset_sum (Finset.univ : Finset (Fin (K+1))) (fun k _ => bad_vertex_cover_fraction_tendsto_zero m k.val N hNinf hgraphs
      (1/(K+1 : ℝ)) (by positivity))
    simpa only [Finset.sum_const_zero] using h
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => measureReal_nonneg)) _ hsum
  exact Filter.Eventually.of_forall (fun n => by rw [he]; exact measureReal_iUnion_fintype_le _)

/-- A genuine slow diagonal for countably many convergences to zero. The
selected index tends to infinity, and its moving-row errors still vanish. -/
theorem exists_slow_diagonal_of_tendsto_zero (f : ℕ → ℕ → ℝ)
    (hf0 : ∀ k n,0 ≤ f k n) (hf : ∀ k,Tendsto (f k) atTop (𝓝 0)) :
    ∃ K : ℕ → ℕ,Tendsto K atTop atTop ∧ Tendsto (fun n => f (K n) n) atTop (𝓝 0) := by
  have hex (k : ℕ) : ∃ t : ℕ,∀ n,t ≤ n → f k n < 1/(k+1 : ℝ) := by
    apply eventually_atTop.mp
    exact (hf k).eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < 1/(k+1 : ℝ)))
  let t (k : ℕ) := (hex k).choose
  have ht (k n : ℕ) (hn : t k ≤ n) : f k n < 1/(k+1 : ℝ) := (hex k).choose_spec n hn
  let K (n : ℕ) := Nat.findGreatest (fun k => t k ≤ n) n
  have hK : Tendsto K atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop (max k (t k))] with n hn
    exact Nat.le_findGreatest (le_trans (le_max_left _ _) hn) (le_trans (le_max_right _ _) hn)
  have hden : Tendsto (fun n => (K n : ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith : ∀ n,(K n : ℝ) ≤ (K n : ℝ)+1)
      (tendsto_natCast_atTop_atTop.comp hK)
  have hupp := hden.const_div_atTop (1 : ℝ)
  refine ⟨K,hK,squeeze_zero' (Filter.Eventually.of_forall (fun n => hf0 _ _)) ?_ hupp⟩
  filter_upwards [eventually_ge_atTop (t 0)] with n hn
  exact (ht (K n) n (Nat.findGreatest_spec (P := fun k => t k ≤ n) (Nat.zero_le n) hn)).le

def CommonGraphGood {N m E : ℕ} (C : ℝ) (K : ℕ) (G : RegularGraph N (m+2)) : Prop :=
  AllPaletteGood (m := E) C (Real.sqrt (N : ℝ)) (8*(m+2)*(m+2+1)) G ∧ LocalCoverGoodUpTo K G

/-- No counting or local-tree premise remains: there are explicit ordinary
graph events of probability tending to one, with all palettes and a radius
cutoff tending to infinity. -/
theorem exists_common_graph_good_events (m : ℕ) (N E : ℕ → ℕ)
    (hNinf : Tendsto N atTop atTop) (hgraphs : ∀ n,Nonempty (RegularGraph (N n) (m+2)))
    (hNE : ∀ n,N n*(m+2)=2*E n) :
    ∃ (C : ℝ) (K : ℕ → ℕ),0 ≤ C ∧ Tendsto K atTop atTop ∧
      Tendsto (fun n => (regularGraphLaw (N n) (m+2)).real
        {G | ¬CommonGraphGood (E := E n) C (K n) G}) atTop (𝓝 0) := by
  obtain ⟨C,hC,hpalette⟩ := exists_all_palette_good_events (m+2) (by omega) N E hNinf hgraphs hNE
  obtain ⟨K,hK,hlocal⟩ := exists_slow_diagonal_of_tendsto_zero
    (fun k n => (regularGraphLaw (N n) (m+2)).real {G | ¬LocalCoverGoodUpTo k G})
    (fun _ _ => measureReal_nonneg) (fun k => local_cover_good_failure_tendsto_zero m k N hNinf hgraphs)
  refine ⟨C,K,hC,hK,?_⟩
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [add_zero] using hpalette.add hlocal)
  exact Filter.Eventually.of_forall (fun n => by
    have he : {G : RegularGraph (N n) (m+2) | ¬CommonGraphGood (E := E n) C (K n) G}=
        {G | ¬AllPaletteGood (m := E n) C (Real.sqrt (N n : ℝ)) (8*(m+2)*(m+2+1)) G} ∪
          {G | ¬LocalCoverGoodUpTo (K n) G} := by ext G; simp only [CommonGraphGood,not_and_or,Set.mem_setOf_eq,Set.mem_union]
    rw [he]
    exact measureReal_union_le _ _)

/-- Every deterministic graph sequence eventually in the genuine common
events has a vanishing colliding-cover root fraction at every fixed depth. -/
theorem common_graph_good_bad_fraction_tendsto_zero (m : ℕ) (N E : ℕ → ℕ)
    (hNinf : Tendsto N atTop atTop) (G : ∀ n,RegularGraph (N n) (m+2))
    (C : ℝ) (K : ℕ → ℕ) (hK : Tendsto K atTop atTop)
    (hgood : ∀ᶠ n in atTop,CommonGraphGood (E := E n) C (K n) (G n)) (k : ℕ) :
    Tendsto (fun n => (N n : ℝ)⁻¹*badVertexCoverRootCount (G n) k) atTop (𝓝 0) := by
  have hden : Tendsto (fun n => (K n : ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith : ∀ n,(K n : ℝ) ≤ (K n : ℝ)+1)
      (tendsto_natCast_atTop_atTop.comp hK)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n =>
    mul_nonneg (by positivity) (badVertexCoverRootCount_nonneg (G n) k))) _ (hden.const_div_atTop 1)
  filter_upwards [hgood,hK.eventually (eventually_ge_atTop k),hNinf.eventually (eventually_ge_atTop 1)] with n hn hk hN
  have hraw := hn.2 ⟨k,by omega⟩
  have hNr : (0 : ℝ) < N n := by exact_mod_cast (by omega : 0 < N n)
  have h := mul_le_mul_of_nonneg_left hraw.le (inv_nonneg.mpr hNr.le)
  have he : (N n : ℝ)⁻¹*((1/(K n+1 : ℝ))*(N n : ℝ))=1/(K n+1 : ℝ) := by
    field_simp
  exact h.trans_eq he

end GaussianWave.BS.Lower
