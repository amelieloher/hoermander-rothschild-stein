-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HolderTransfer
public import RothschildStein.P2.HolderTransferTopology
public import RothschildStein.P2.SmoothingSobolev
public import RothschildStein.P1.RestrictedErrorChart
public import RothschildStein.P1.H2CertificateCarrier
public import RothschildStein.S.ClassicalWords
public import RothschildStein.S.Locality
public import RothschildStein.S.WordDerivativeGerms
public import RothschildStein.S.HolderArithmetic
public import RothschildStein.S.TestWordHolderBounds
public import RothschildStein.S.ControlDistanceComparison
public import RothschildStein.S.IntrinsicWeakWordExport
public import RothschildStein.Definitions.memHolderX
public import RothschildStein.Definitions.memHolderXLoc
public import RothschildStein.Definitions.memSobolevXLoc

/-!
# Lift, solve and subtract: geometry of small lifted balls and smooth parts on relatively compact sets

* `exists_isSmallBallRadius_of_mem`, `isOpen_rsBall_of_isSmallBallRadius`, `closure_rsBall_subset`:
  small lifted control balls `B̃(ξ₀, r)` are open with compact closure inside larger balls;
  `memLp_comp_basePoint_of_subset` (the upper fiber bound of BB p. 584: `f ∈ L^p(Ω)` gives
  `f ∘ π ∈ L^p` on every measurable subset of the chart neighborhood);
* `memSobolevXLoc_add_smooth`: `v + h`, `v ∈ W^{k,p}(U)`, `h` smooth on `U`, is in `W^{k,p}`
  on every `V ⋐ U`;
* `exists_jets_of_memHolderX` (BB Prop 2.22): the intrinsic word derivatives of a member of
  `C^{k,α}_{X̃}` are continuous and weak derivatives; `holderENorm_wordDerivative_lt_top` (using the `(HD)`
  property of the lifted control distance): the word derivatives of a smooth function have finite `C^α_{X̃}` norm on every
  relatively compact `V` (a test cutoff and the HD3 comparison of the lifted control distance);
  `memHolderXLoc_add_smooth`: `v + h` is in `C^{k,α}_{X̃}(V)` for `V ⋐ U`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators Distributions
open RothschildStein.P1
namespace RothschildStein.P2

section Geometry

variable {n k s m : ℕ} {w : Fin k → ℕ+} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : P1.LiftedChart w s Ω hΩ X x₀ m)

/-- Every point of the chart neighborhood has an admissible small-ball radius (for a compact
Euclidean ball around it inside `U`). -/
theorem exists_isSmallBallRadius_of_mem {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U) :
    ∃ (K₀ : Set (Fin (n + m) → ℝ)) (rstar : ℝ), IsCompact K₀ ∧ K₀ ⊆ C.U ∧
      C.IsSmallBallRadius K₀ ξ₀ rstar := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp C.isOpen_U ξ₀ hξ₀
  have hsub : Metric.closedBall ξ₀ (ε / 2) ⊆ C.U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hint : ξ₀ ∈ interior (Metric.closedBall ξ₀ (ε / 2)) :=
    Metric.ball_subset_interior_closedBall (Metric.mem_ball_self (by linarith))
  obtain ⟨rstar, hr⟩ := P1.LiftedChart.exists_isSmallBallRadius (C := C)
    (isCompact_closedBall ξ₀ (ε / 2)) hsub hint
  exact ⟨_, rstar, isCompact_closedBall ξ₀ (ε / 2), hsub, hr⟩

/-- Small lifted control balls are Euclidean open. -/
theorem isOpen_rsBall_of_isSmallBallRadius {K₀ : Set (Fin (n + m) → ℝ)} {ξ₀ : Fin (n + m) → ℝ}
    {rstar : ℝ} (hr : C.IsSmallBallRadius K₀ ξ₀ rstar) {r : ℝ} (hr0 : 0 < r) (hrr : r < rstar) :
    IsOpen (rsBall C.O w C.Xl ξ₀ r) :=
  isOpen_rsBall_lifted C (fun _ hy => hr.subset_U (hr.ball_subset r hr0 hrr hy))

/-- The closure of a small lifted control ball is compact and lies in every larger ball
(closure `⊆ {d̃ ≤ r}` by the Euclidean continuity of `d̃` on `U`). -/
theorem closure_rsBall_subset {K₀ : Set (Fin (n + m) → ℝ)} {ξ₀ : Fin (n + m) → ℝ} {rstar : ℝ}
    (hK₀ : IsCompact K₀) (hr : C.IsSmallBallRadius K₀ ξ₀ rstar) {r R : ℝ} (hr0 : 0 < r)
    (hrR : r < R) (hrr : r < rstar) :
    IsCompact (closure (rsBall C.O w C.Xl ξ₀ r)) ∧
      closure (rsBall C.O w C.Xl ξ₀ r) ⊆ rsBall C.O w C.Xl ξ₀ R := by
  have hsub : rsBall C.O w C.Xl ξ₀ r ⊆ K₀ := hr.ball_subset r hr0 hrr
  have hcl : closure (rsBall C.O w C.Xl ξ₀ r) ⊆ K₀ := closure_minimal hsub hK₀.isClosed
  refine ⟨hK₀.of_isClosed_subset isClosed_closure hcl, fun ξ hξ => ?_⟩
  have hξK : ξ ∈ C.U := hr.subset_U (hcl hξ)
  have hε : 0 < R - r := by linarith
  obtain ⟨δ', hδ', hclose⟩ := exists_dl_lt_of_euclid_close C hξK hε
  obtain ⟨ζ, hζ, hdist⟩ := Metric.mem_closure_iff.mp hξ δ' hδ'
  have hζn : ‖ζ - ξ‖ < δ' := by rw [← dist_eq_norm, dist_comm]; exact hdist
  obtain ⟨-, hdl⟩ := hclose ζ hζn
  refine ⟨holderTransfer_U_subset_O C hξK, ?_⟩
  calc C.dl ξ₀ ξ ≤ C.dl ξ₀ ζ + C.dl ζ ξ := G1.controlDistance_triangle C.O w C.Xl ξ₀ ζ ξ
    _ < ENNReal.ofReal r + ENNReal.ofReal (R - r) := by
        refine ENNReal.add_lt_add hζ.2 ?_
        rw [show C.dl ζ ξ = C.dl ξ ζ from G1.controlDistance_symm C.O w C.Xl ζ ξ]
        exact hdl
    _ = ENNReal.ofReal R := by
        rw [← ENNReal.ofReal_add hr0.le hε.le]
        congr 1
        ring

/-- Membership of the centre in a control ball. -/
theorem mem_rsBall_self {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.O) {R : ℝ} (hR : 0 < R) :
    ξ₀ ∈ rsBall C.O w C.Xl ξ₀ R :=
  ⟨hξ₀, by rw [G1.controlDistance_self _ C.Xl hξ₀]; exact ENNReal.ofReal_pos.2 hR⟩

/-- A function of the base in `L^p(Ω)` composes with `π` to an `L^p` function on every measurable
subset of the chart neighborhood (the upper fiber bound, BB p. 584). -/
theorem memLp_comp_basePoint_of_subset {A : Set (Fin (n + m) → ℝ)} (hA : MeasurableSet A)
    (hAU : A ⊆ C.U) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) {f : (Fin n → ℝ) → ℝ}
    (hf : MemLp f p (volume.restrict Ω)) :
    MemLp (fun ξ => f (basePoint ξ)) p (volume.restrict A) := by
  obtain ⟨c, hc0, hc⟩ := liftedChart_fiberVolume_bounded C
  have hFB : FiberBounds A Ω ∅ c 0 :=
    { cup_nonneg := hc0
      clow_nonneg := le_rfl
      measurableSet_A := hA
      measurableSet_V := hΩ.measurableSet
      measurableSet_W := MeasurableSet.empty
      subset := empty_subset _
      proj := fun ξ hξ => liftedChart_basePoint_mem C (hAU hξ)
      upper := fun z => le_trans (measure_mono fun t ht => hAU ht) (hc z)
      lower := fun z hz => absurd hz (notMem_empty z) }
  exact lt_of_le_of_lt (hFB.eLpNorm_comp_le hp hpt hf.aestronglyMeasurable)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf)

end Geometry

section AddSmooth

variable {N k₀ : ℕ}

/-- A function continuous on a compact set `K` is in every `L^p(V)`, `V ⊆ K` measurable. -/
theorem memLp_of_continuousOn_compact {K V : Set (Fin N → ℝ)} (hK : IsCompact K)
    (hV : MeasurableSet V) (hVK : V ⊆ K) {g : (Fin N → ℝ) → ℝ} (hg : ContinuousOn g K)
    (p : ℝ≥0∞) : MemLp g p (volume.restrict V) := by
  have : IsFiniteMeasure (volume.restrict V) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_lt (measure_mono hVK) hK.measure_lt_top⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hg
  exact MemLp.of_bound ((hg.mono hVK).aestronglyMeasurable hV) M
    (ae_restrict_of_forall_mem hV fun x hx => hM x (hVK hx))

/-- A smooth function on `U` is a classical weak solution of its word derivatives, and
`v + h` with `v ∈ W^{k,p}(U)` and `h` smooth on `U` lies in `W^{k,p}(V)` for every `V` with compact
closure in `U`, with weak word derivatives `g_I + X_I h` (BB p. 68, Def 2.1, 2.2). -/
theorem memSobolevXLoc_add_smooth (wt : Fin k₀ → ℕ+)
    (Xa : Fin k₀ → (Fin N → ℝ) → (Fin N → ℝ)) (U : Opens (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xa i) (U : Set (Fin N → ℝ))) {kk : ℕ} {p : ℝ≥0∞}
    {v h : (Fin N → ℝ) → ℝ} (hv : memSobolevX wt Xa U kk p v)
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h (U : Set (Fin N → ℝ))) :
    memSobolevXLoc wt Xa U kk p (fun x => v x + h x) := by
  intro V hVc hVU
  have hVU' : (V : Set (Fin N → ℝ)) ⊆ U := subset_closure.trans hVU
  have hmeas : MeasurableSet (V : Set (Fin N → ℝ)) := V.isOpen.measurableSet
  have hμ : volume.restrict (V : Set (Fin N → ℝ)) ≤ volume.restrict (U : Set (Fin N → ℝ)) :=
    Measure.restrict_mono hVU' le_rfl
  refine ⟨(hv.1.mono_measure hμ).add (memLp_of_continuousOn_compact hVc hmeas subset_closure
    (hh.continuousOn.mono hVU) p), fun I hI => ?_⟩
  obtain ⟨g, hg, hgL⟩ := hv.2 I hI
  have hgV := RothschildStein.S.hasWeakWordDeriv_restrict Xa U V hVU' hg
  have hcl := RothschildStein.S.hasWeakWordDeriv_classical V Xa (fun i => (hX i).mono hVU') I h
    (hh.mono hVU')
  refine ⟨fun x => g x + wordDerivative Xa I h x,
    RothschildStein.S.hasWeakWordDeriv_add Xa V (fun i => (hX i).mono hVU') hgV hcl,
    (hgL.mono_measure hμ).add (memLp_of_continuousOn_compact hVc hmeas subset_closure
      ((RothschildStein.S.contDiffOn_wordDerivative U Xa hX I h hh).continuousOn.mono hVU) p)⟩

end AddSmooth

section HolderAddSmooth

variable {n k s m : ℕ} {w : Fin k → ℕ+} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : P1.LiftedChart w s Ω hΩ X x₀ m)

theorem holderSeminorm_ne_top_of_holderENorm_lt_top {d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞} {α : ℝ}
    {V : Set (Fin n → ℝ)} {g : (Fin n → ℝ) → ℝ} (hg : holderENorm d α V g < ⊤) :
    holderSeminorm d α V g ≠ ⊤ :=
  ne_top_of_le_ne_top hg.ne le_add_self

/-- Members of `C^α_{X̃}` on an open subset of the chart are continuous. -/
theorem continuousOn_of_holderENorm_lt_top_chart {α : ℝ} (hα : 0 < α) {U : Opens (Fin (n + m) → ℝ)}
    (hUC : (U : Set (Fin (n + m) → ℝ)) ⊆ C.U) {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : holderENorm C.dl α (U : Set (Fin (n + m) → ℝ)) g < ⊤) :
    ContinuousOn g (U : Set (Fin (n + m) → ℝ)) :=
  continuousOn_of_holderSeminorm_ne_top C U.isOpen hUC hα
    (holderSeminorm_ne_top_of_holderENorm_lt_top hg)

/-- The lifted control distance separates points of the lifted domain. -/
theorem dl_eq_zero_imp_eq {x y : Fin (n + m) → ℝ} (hx : x ∈ C.O) (h : C.dl x y = 0) : x = y :=
  ((G1.controlDistance_eq_zero_iff C.isOpen_O_of_chart w C.Xl
    (fun i => (C.lift_smooth i).continuousOn) hx).mp h)

/-- The jets of a member of `C^{kk,α}_{X̃}(U)`: choose, for every admissible word, the
intrinsic word derivative with finite Hölder norm; it is continuous, and (BB Prop 2.22) also the weak word
derivative. -/
theorem exists_jets_of_memHolderX {α : ℝ} (hα : 0 < α) {U : Opens (Fin (n + m) → ℝ)}
    (hUC : (U : Set (Fin (n + m) → ℝ)) ⊆ C.U) {kk : ℕ} {v : (Fin (n + m) → ℝ) → ℝ}
    (hv : memHolderX w C.Xl C.dl U kk α v) :
    ∃ jet : List (Fin k) → (Fin (n + m) → ℝ) → ℝ, jet [] = v ∧
      ∀ J ∈ wordFamily w kk, hasIntrinsicWordDeriv C.Xl U J v (jet J) ∧
        hasWeakWordDeriv C.Xl U J v (jet J) ∧ ContinuousOn (jet J) (U : Set (Fin (n + m) → ℝ)) ∧
        holderENorm C.dl α (U : Set (Fin (n + m) → ℝ)) (jet J) < ⊤ := by
  classical
  have hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (U : Set (Fin (n + m) → ℝ)) :=
    fun i => (C.lift_smooth i).mono (hUC.trans (holderTransfer_U_subset_O C))
  let jet : List (Fin k) → (Fin (n + m) → ℝ) → ℝ := fun J =>
    if hJ : J ∈ wordFamily w kk then
      (if J = [] then v else Classical.choose (hv.2 J hJ)) else 0
  have hjet0 : jet [] = v := by
    simp [jet, RothschildStein.S.nil_mem_wordFamily]
  have hint : ∀ J ∈ wordFamily w kk, hasIntrinsicWordDeriv C.Xl U J v (jet J) ∧
      ContinuousOn (jet J) (U : Set (Fin (n + m) → ℝ)) ∧
      holderENorm C.dl α (U : Set (Fin (n + m) → ℝ)) (jet J) < ⊤ := by
    intro J hJ
    by_cases hJ0 : J = []
    · subst hJ0
      obtain ⟨g₀, hg₀, hg₀n⟩ := hv.2 [] (RothschildStein.S.nil_mem_wordFamily w kk)
      have heq : EqOn v g₀ (U : Set (Fin (n + m) → ℝ)) := fun x hx => (hg₀ hx).symm
      rw [hjet0]
      refine ⟨fun _ _ => rfl, ?_, ?_⟩
      · exact (continuousOn_of_holderENorm_lt_top_chart C hα hUC hg₀n).congr heq
      · rw [holderENorm_congr heq]
        exact hg₀n
    · have hspec := Classical.choose_spec (hv.2 J hJ)
      have hj : jet J = Classical.choose (hv.2 J hJ) := by
        simp [jet, hJ, hJ0]
      rw [hj]
      exact ⟨hspec.1, continuousOn_of_holderENorm_lt_top_chart C hα hUC hspec.2, hspec.2⟩
  refine ⟨jet, hjet0, fun J hJ => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hint J hJ
  refine ⟨h1, ?_, h2, h3⟩
  exact RothschildStein.S.hasWeakWordDeriv_of_continuous_intrinsic_words U C.Xl hX J v jet hjet0
    (fun J' hJ' => (hint J' (RothschildStein.S.sublist_mem_wordFamily w kk hJ' hJ)).1)
    (fun J' hJ' => (hint J' (RothschildStein.S.sublist_mem_wordFamily w kk hJ' hJ)).2.1)

/-- The classical word derivatives of a smooth function have finite `C^α_{X̃}`
norm on every open `V` with compact closure inside the open set where it is smooth: a test cutoff
equal to one near `closure V` gives a test with the same derivatives on `V`, and the HD3 comparison
of `d̃` on the compact patch gives the Hölder bound (`holderENorm_word_test_lt_top`). -/
theorem holderENorm_wordDerivative_lt_top (hw : ∀ i, (w i : ℕ) ≤ 2) {α : ℝ} (hα : 0 < α)
    (hα1 : α ≤ 1) {U V : Opens (Fin (n + m) → ℝ)}
    (hUC : (U : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (hVc : IsCompact (closure (V : Set (Fin (n + m) → ℝ))))
    (hVU : closure (V : Set (Fin (n + m) → ℝ)) ⊆ U) {h : (Fin (n + m) → ℝ) → ℝ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h (U : Set (Fin (n + m) → ℝ))) (I : List (Fin k)) :
    holderENorm C.dl α (V : Set (Fin (n + m) → ℝ)) (wordDerivative C.Xl I h) < ⊤ := by
  have hUO : (U : Set (Fin (n + m) → ℝ)) ⊆ C.O := hUC.trans (holderTransfer_U_subset_O C)
  let O' : Opens (Fin (n + m) → ℝ) := ⟨C.O, C.isOpen_O_of_chart⟩
  obtain ⟨κ, hκ⟩ := RothschildStein.S.exists_controlDistance_comparison_on_compact_patch O' w C.Xl hw
    (fun i => (C.lift_smooth i).continuousOn) hVc (fun x hx => hUO (hVU hx))
  obtain ⟨χ, U', hU'o, hKU', hU'U, hχ⟩ := RothschildStein.S.exists_test_plateau U
    ⟨closure (V : Set (Fin (n + m) → ℝ)), hVc⟩ hVU
  let φ : TestFunction U ℝ (⊤ : ℕ∞) := testMultiplierOn U h hh χ
  have hφ : ∀ y ∈ U', φ y = h y := by
    intro y hy
    change χ y * h y = h y
    rw [hχ hy]
    simp
  have hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (U : Set (Fin (n + m) → ℝ)) :=
    fun i => (C.lift_smooth i).mono hUO
  have hfin := RothschildStein.S.holderENorm_word_test_lt_top U C.Xl hX
    (controlDistance (O' : Set (Fin (n + m) → ℝ)) w C.Xl) (V : Set (Fin (n + m) → ℝ)) hκ hα hα1 I φ
  have heq : EqOn (wordDerivative C.Xl I φ) (wordDerivative C.Xl I h) (V : Set (Fin (n + m) → ℝ)) := by
    intro x hx
    have hev : (φ : (Fin (n + m) → ℝ) → ℝ) =ᶠ[nhds x] h :=
      Filter.eventuallyEq_of_mem (hU'o.mem_nhds (hKU' (subset_closure hx))) hφ
    exact (RothschildStein.S.wordDerivative_eventuallyEq C.Xl I hev).eq_of_nhds
  rw [← holderENorm_congr heq]
  exact hfin

/-- `v + h`, with `v ∈ C^{kk,α}_{X̃}(U)` and `h` smooth on `U`, lies in
`C^{kk,α}_{X̃}(V)` for every `V` with compact closure in `U` (the finiteness of the intrinsic
derivatives and Hölder norms of the smooth part on a relatively compact ball, BB pp. 609-610). -/
theorem memHolderXLoc_add_smooth (hw : ∀ i, (w i : ℕ) ≤ 2) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {U : Opens (Fin (n + m) → ℝ)} (hUC : (U : Set (Fin (n + m) → ℝ)) ⊆ C.U) {kk : ℕ}
    {v h : (Fin (n + m) → ℝ) → ℝ} (hv : memHolderX w C.Xl C.dl U kk α v)
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h (U : Set (Fin (n + m) → ℝ))) :
    memHolderXLoc w C.Xl C.dl U kk α (fun x => v x + h x) := by
  intro V hVc hVU
  have hVU' : (V : Set (Fin (n + m) → ℝ)) ⊆ U := subset_closure.trans hVU
  have hUO : (U : Set (Fin (n + m) → ℝ)) ⊆ C.O := hUC.trans (holderTransfer_U_subset_O C)
  obtain ⟨jet, hj0, hjet⟩ := exists_jets_of_memHolderX C hα hUC hv
  have hXU : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (U : Set (Fin (n + m) → ℝ)) :=
    fun i => (C.lift_smooth i).mono hUO
  have hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (V : Set (Fin (n + m) → ℝ)) :=
    fun i => (hXU i).mono hVU'
  have hsep : ∀ x ∈ (V : Set (Fin (n + m) → ℝ)), ∀ y ∈ (V : Set (Fin (n + m) → ℝ)),
      C.dl x y = 0 → x = y := fun x hx _ _ h => dl_eq_zero_imp_eq C (hUO (hVU' hx)) h
  let jw : List (Fin k) → (Fin (n + m) → ℝ) → ℝ := fun J x => jet J x + wordDerivative C.Xl J h x
  have hmain : ∀ J ∈ wordFamily w kk,
      hasWeakWordDeriv C.Xl V J (fun x => v x + h x) (jw J) ∧
      ContinuousOn (jw J) (V : Set (Fin (n + m) → ℝ)) ∧
      holderENorm C.dl α (V : Set (Fin (n + m) → ℝ)) (jw J) < ⊤ := by
    intro J hJ
    obtain ⟨-, hweak, hcont, hfin⟩ := hjet J hJ
    have hcl := RothschildStein.S.hasWeakWordDeriv_classical V C.Xl hXV J h (hh.mono hVU')
    refine ⟨RothschildStein.S.hasWeakWordDeriv_add C.Xl V hXV
      (RothschildStein.S.hasWeakWordDeriv_restrict C.Xl U V hVU' hweak) hcl, ?_, ?_⟩
    · exact (hcont.mono hVU').add
        ((RothschildStein.S.contDiffOn_wordDerivative U C.Xl hXU J h hh).continuousOn.mono hVU')
    · have h1 : holderENorm C.dl α (V : Set (Fin (n + m) → ℝ)) (jet J) < ⊤ :=
        lt_of_le_of_lt (RothschildStein.S.holderENorm_mono C.dl α (U : Set (Fin (n + m) → ℝ))
          (jet J) hVU') hfin
      have h2 := holderENorm_wordDerivative_lt_top C hw hα hα1 hUC hVc hVU hh J
      exact lt_of_le_of_lt (RothschildStein.S.holderENorm_add_le C.dl α _ hα hsep (jet J) _ h1 h2)
        (ENNReal.add_lt_top.2 ⟨h1, h2⟩)
  have hjw0 : jw [] = fun x => v x + h x := by
    funext x
    simp [jw, hj0, wordDerivative]
  refine ⟨?_, fun I hI => ⟨jw I, ?_, (hmain I hI).2.2⟩⟩
  · have := (hmain [] (RothschildStein.S.nil_mem_wordFamily w kk)).2.2
    rwa [hjw0] at this
  · refine hasIntrinsicWordDeriv_of_continuous_weak_words V C.Xl hXV I _ jw hjw0 ?_ ?_
    · intro J hJ
      exact (hmain J (RothschildStein.S.sublist_mem_wordFamily w kk hJ hI)).1
    · intro J hJ
      exact (hmain J (RothschildStein.S.sublist_mem_wordFamily w kk hJ hI)).2.1

end HolderAddSmooth

end RothschildStein.P2
