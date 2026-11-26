import GeneralizedBulk.Graph.ColoredPairings
import GeneralizedBulk.Graph.ColorProfiles
import GeneralizedBulk.Graph.TypeClassEntropy

/-! The actual configuration model and its ordered coloring profiles. -/
noncomputable section
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph.Configuration
open ColorProfiles

abbrev Stub (N d : ℕ) := Fin N × Fin d
abbrev VertexColoring (N q : ℕ) := Fin N → Fin q

def configurationWord {N d q : ℕ} (p : Pairing (Stub N d)) (c : VertexColoring N q)
    (v : Fin N) : StarWord d q :=
  Fin.cases (c v) (fun j => c (p.val (v,j)).1)

def wordSource {N d q : ℕ} (w : Fin N → StarWord d q) (h : Stub N d) : ℕ := (w h.1 0).val

def wordTarget {N d q : ℕ} (w : Fin N → StarWord d q) (h : Stub N d) : ℕ := (w h.1 h.2.succ).val

theorem configurationWord_compatible {N d q : ℕ}
    (p : Pairing (Stub N d)) (c : VertexColoring N q) :
    Compatible (wordSource (configurationWord p c)) (wordTarget (configurationWord p c)) p := by
  intro h
  simp [wordSource, wordTarget, configurationWord]

def wordRootColor {N d q : ℕ} (w : Fin N → StarWord d q) : VertexColoring N q := fun v => w v 0

theorem configurationWord_of_compatible {N d q : ℕ} (w : Fin N → StarWord d q)
    (p : ColoredPairing (wordSource w) (wordTarget w)) :
    configurationWord p.val (wordRootColor w) = w := by
  funext v i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · apply Fin.ext
    exact p.property (v,j)

def profileColorings {N d q : ℕ} (w : Fin N → StarWord d q) :=
  {z : Pairing (Stub N d) × VertexColoring N q // configurationWord z.1 z.2 ∈ typeClass w}

instance {N d q : ℕ} (w : Fin N → StarWord d q) : Fintype (profileColorings w) := by
  unfold profileColorings
  infer_instance

def ProfileConfigurationCode {N d q : ℕ} (w : Fin N → StarWord d q) :=
  Σ z : {z : Fin N → StarWord d q // z ∈ typeClass w}, ColoredPairing (wordSource z.val) (wordTarget z.val)

instance {N d q : ℕ} (w : Fin N → StarWord d q) : Fintype (ProfileConfigurationCode w) := by
  unfold ProfileConfigurationCode
  infer_instance

def profileConfigurationCode {N d q : ℕ} (w : Fin N → StarWord d q) :
    profileColorings w → ProfileConfigurationCode w :=
  fun z => ⟨⟨configurationWord z.val.1 z.val.2,z.property⟩,
    ⟨z.val.1,configurationWord_compatible z.val.1 z.val.2⟩⟩

theorem profileConfigurationCode_injective {N d q : ℕ} (w : Fin N → StarWord d q) :
    Function.Injective (profileConfigurationCode w) := by
  intro x y h
  have hp := congrArg (fun z : ProfileConfigurationCode w => z.2.val) h
  have hw := congrArg (fun z : ProfileConfigurationCode w => z.1.val) h
  apply Subtype.ext
  apply Prod.ext hp
  funext v
  exact congrFun (congrFun hw v) 0

theorem profileColorings_card_le {N d q : ℕ} (w : Fin N → StarWord d q) :
    Fintype.card (profileColorings w) ≤
      ∑ z : {z : Fin N → StarWord d q // z ∈ typeClass w},
        Fintype.card (ColoredPairing (wordSource z.val) (wordTarget z.val)) := by
  exact (Fintype.card_le_of_injective _ (profileConfigurationCode_injective w)).trans_eq
    Fintype.card_sigma

def wordEdgeCount {N d q : ℕ} (w : Fin N → StarWord d q) (a b : Fin q) : ℕ :=
  Fintype.card (ColorBlock (wordSource w) (wordTarget w) a b)

def wordPortCount {d q : ℕ} (s : StarWord d q) (a b : Fin q) : ℕ :=
  (Finset.univ.filter (fun j : Fin d => s 0 = a ∧ s j.succ = b)).card

theorem wordEdgeCount_eq_vertex_sum {N d q : ℕ} (w : Fin N → StarWord d q) (a b : Fin q) :
    wordEdgeCount w a b = ∑ v, wordPortCount (w v) a b := by
  simp only [wordEdgeCount, Fintype.card_subtype, wordSource, wordTarget, wordPortCount,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Fin.ext_iff]

theorem wordEdgeCount_eq_count_sum {N d q : ℕ} (w : Fin N → StarWord d q) (a b : Fin q) :
    wordEdgeCount w a b = ∑ s, wordCount w s * wordPortCount s a b := by
  rw [wordEdgeCount_eq_vertex_sum,
    ← Finset.sum_fiberwise' (Finset.univ : Finset (Fin N)) w (fun s => wordPortCount s a b)]
  simp only [Finset.sum_const, nsmul_eq_mul, wordCount, Nat.cast_id]

theorem wordEdgeCount_of_typeClass {N d q : ℕ} {w z : Fin N → StarWord d q}
    (hz : z ∈ typeClass w) (a b : Fin q) : wordEdgeCount z a b = wordEdgeCount w a b := by
  rw [wordEdgeCount_eq_count_sum, wordEdgeCount_eq_count_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [(Finset.mem_filter.mp hz).2 s]

theorem wordEdgeCount_sum {N d q : ℕ} (w : Fin N → StarWord d q) :
    (∑ a : Fin q, ∑ b : Fin q, wordEdgeCount w a b) = N * d := by
  let F : Stub N d → Fin q × Fin q := fun h => (w h.1 0, w h.1 h.2.succ)
  have hc (a b : Fin q) : wordEdgeCount w a b =
      (Finset.univ.filter (fun h : Stub N d => F h = (a,b))).card := by
    simp only [wordEdgeCount, Fintype.card_subtype, wordSource, wordTarget]
    congr 1
    ext h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, F, Prod.mk.injEq, Fin.ext_iff]
  simp_rw [hc]
  have h := Finset.card_eq_sum_card_fiberwise (f := F)
    (s := (Finset.univ : Finset (Stub N d))) (t := (Finset.univ : Finset (Fin q × Fin q)))
    (fun h hh => Finset.mem_univ _)
  rw [Fintype.sum_prod_type] at h
  simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] using h.symm

end GeneralizedBulk.Graph.Configuration
