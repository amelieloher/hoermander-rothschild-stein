-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.F.Coordinates
public import Hormander.F.DifferentialTransport
public import Hormander.F.SchwartzTransport
public import Hormander.F.AdjointTest
public import Hormander.F.WordLocality
public import Hormander.F.Defs
public import Hormander.C.Words
public import Hormander.C.FrameAlgebra
public import Hormander.D.Cutoffs
public import Hormander.Interface.LieAlgebraSpansOn
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.MetricSpace.ProperSpace

@[expose] public section

noncomputable section

open Filter Function Set Topology
open scoped BigOperators

namespace Hormander.F

/-- Convert a standard right-nested word into the binary Lie-word syntax `Hormander.Interface.LieWord`. -/
def nestedToLieWord {k : ℕ} : Hormander.C.NestedWord k → Hormander.Interface.LieWord k
  | .generator i => .generator i
  | .bracket i w => .bracket (.generator i) (nestedToLieWord w)

@[simp] theorem lieWordEval_nestedToLieWord {k N : ℕ}
    (X : Fin (k + 1) → E₂ N → E₂ N) (w : Hormander.C.NestedWord k) :
    Hormander.lieWordEval X (nestedToLieWord w) = Hormander.C.nestedEval X w := by
  induction w with
  | generator i => rfl
  | bracket i w ih => simp [nestedToLieWord, Hormander.lieWordEval, Hormander.C.nestedEval, ih]

@[simp] theorem lieWordLength_nestedToLieWord {k : ℕ}
    (w : Hormander.C.NestedWord k) :
    Hormander.lieWordLength (nestedToLieWord w) = Hormander.C.nestedLength w := by
  induction w with
  | generator i => rfl
  | bracket i w ih =>
      simp [nestedToLieWord, Hormander.lieWordLength, Hormander.C.nestedLength, ih]
      omega

private theorem combinationEval_mem_nestedSpan {k N : ℕ}
    (X : Fin (k + 1) → E₂ N → E₂ N) (c : Hormander.C.WordCombination k)
    (x : E₂ N) :
    Hormander.C.combinationEval X c x ∈
      Submodule.span ℝ (Set.range (fun w : Hormander.C.NestedWord k =>
        Hormander.C.nestedEval X w x)) := by
  induction c with
  | nil => simp [Hormander.C.combinationEval]
  | cons head tail ih =>
      rcases head with ⟨n, w⟩
      simp only [Hormander.C.combinationEval]
      apply add_mem
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, rfl⟩)
      · exact ih

private theorem exists_nested_frame_at_point {k N : ℕ} {Ω : Set (E₂ N)}
    (hΩ : IsOpen Ω) (X : Fin (k + 1) → E₂ N → E₂ N)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (x : E₂ N) (hx : x ∈ Ω)
    (hspan : Submodule.span ℝ
      (Set.range (fun w : Hormander.Interface.LieWord k => Hormander.lieWordEval X w x)) = ⊤) :
    ∃ words : Fin N → Hormander.C.NestedWord k,
      LinearIndependent ℝ (fun a => Hormander.C.nestedEval X (words a) x) := by
  let standardValues : Hormander.C.NestedWord k → E₂ N :=
    fun w => Hormander.C.nestedEval X w x
  have hstandardSpan : Submodule.span ℝ (Set.range standardValues) = ⊤ := by
    apply top_unique
    have hle : Submodule.span ℝ
        (Set.range (fun w : Hormander.Interface.LieWord k => Hormander.lieWordEval X w x)) ≤
          Submodule.span ℝ (Set.range standardValues) := by
      apply Submodule.span_le.2
      rintro _ ⟨w, rfl⟩
      have hnormalized := Hormander.C.binaryExpansion_eqOn hΩ X hX w
      change Hormander.lieWordEval X w x ∈ _
      rw [← hnormalized hx]
      exact combinationEval_mem_nestedSpan X (Hormander.C.binaryExpansion w) x
    rw [hspan] at hle
    exact hle
  obtain ⟨κ, chooseWord, hchooseInjective, hchooseSpan, hchooseIndependent⟩ :=
    exists_linearIndependent' (K := ℝ) standardValues
  have hselectedSpan : Submodule.span ℝ
      (Set.range (standardValues ∘ chooseWord)) = ⊤ := hchooseSpan.trans hstandardSpan
  let : Finite κ := hchooseIndependent.finite
  let : Fintype κ := Fintype.ofFinite κ
  have hdim : Module.finrank ℝ (Submodule.span ℝ
      (Set.range (standardValues ∘ chooseWord))) = Fintype.card κ :=
    finrank_span_eq_card hchooseIndependent
  have hcard : Fintype.card κ = N := by
    calc
      Fintype.card κ = Module.finrank ℝ
          (Submodule.span ℝ (Set.range (standardValues ∘ chooseWord))) := hdim.symm
      _ = Module.finrank ℝ (⊤ : Submodule ℝ (E₂ N)) := by rw [hselectedSpan]
      _ = N := by simp [E₂]
  let reindex : Fin N ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun a => chooseWord (reindex a), ?_⟩
  exact hchooseIndependent.comp reindex reindex.injective

/-- A spanning family of smooth Lie words gives one local ball, one
cutoff extension of the coefficients, and one standard-word frame with its fixed gain. -/
theorem exists_local_frame_patch {k N : ℕ} (hN : 0 < N)
    {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (c : (Fin N → ℝ) → ℝ) (x₀ : Fin N → ℝ) (hx₀ : x₀ ∈ Ω)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hspan : Hormander.Interface.LieAlgebraSpansOn Ω X)
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c Ω) :
    Nonempty (LocalPatch hN (coordinateEquiv N '' Ω) (pushVectorFields X)
      (fun y => c ((coordinateEquiv N).symm y)) (coordinateEquiv N x₀)) := by
  let e := coordinateEquiv N
  let Ω₂ : Set (E₂ N) := e '' Ω
  let X₂ : Fin (k + 1) → E₂ N → E₂ N := pushVectorFields X
  let c₂ : E₂ N → ℝ := fun y => c (e.symm y)
  have hΩ₂ : IsOpen Ω₂ := by
    exact e.toHomeomorph.isOpenMap Ω hΩ
  have hpreimage : e.symm ⁻¹' Ω = Ω₂ := by
    ext y
    constructor
    · intro hy
      exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
    · rintro ⟨x, hx, rfl⟩
      exact e.symm_apply_apply x ▸ hx
  have hX₂ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X₂ i) Ω₂ := by
    intro i
    have hpost : ContDiffOn ℝ (⊤ : ℕ∞) (e ∘ X i) Ω :=
      (e : (Fin N → ℝ) →L[ℝ] E₂ N).contDiff.comp_contDiffOn (hX i)
    have hpre := hpost.comp_continuousLinearMap (e.symm : E₂ N →L[ℝ] (Fin N → ℝ))
    change ContDiffOn ℝ (⊤ : ℕ∞) (fun y => e (X i (e.symm y))) Ω₂
    simpa [Ω₂, hpreimage, Function.comp_def, e] using hpre
  have hc₂ : ContDiffOn ℝ (⊤ : ℕ∞) c₂ Ω₂ := by
    have hpre := hc.comp_continuousLinearMap (e.symm : E₂ N →L[ℝ] (Fin N → ℝ))
    simpa [c₂, Ω₂, hpreimage, Function.comp_def, e] using hpre
  have hspan₂ : ∀ y ∈ Ω₂, Submodule.span ℝ
      (Set.range (fun w : Hormander.Interface.LieWord k => Hormander.lieWordEval X₂ w y)) = ⊤ := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    let L := (e : (Fin N → ℝ) →L[ℝ] E₂ N).toLinearMap
    have hset : e '' Set.range (fun w : Hormander.Interface.LieWord k =>
        Hormander.Interface.LieWord.eval X w x) =
        Set.range (fun w : Hormander.Interface.LieWord k =>
          Hormander.lieWordEval X₂ w (e x)) := by
      calc
        e '' Set.range (fun w : Hormander.Interface.LieWord k =>
            Hormander.Interface.LieWord.eval X w x) =
            Set.range (fun w : Hormander.Interface.LieWord k =>
              e (Hormander.Interface.LieWord.eval X w x)) := by
                rw [← Set.range_comp]
                rfl
        _ = Set.range (fun w : Hormander.Interface.LieWord k =>
            Hormander.lieWordEval X₂ w (e x)) := by
              congr 1
              funext w
              simpa [X₂, e] using (congrFun (lieWordEval_coordinateConjugate X w) (e x)).symm
    have hmap : Submodule.map L (Submodule.span ℝ (Set.range (fun w :
        Hormander.Interface.LieWord k => Hormander.Interface.LieWord.eval X w x))) =
        Submodule.span ℝ (Set.range (fun w : Hormander.Interface.LieWord k =>
          Hormander.lieWordEval X₂ w (e x))) := by
      have hsetL : L '' Set.range (fun w : Hormander.Interface.LieWord k =>
          Hormander.Interface.LieWord.eval X w x) =
          Set.range (fun w : Hormander.Interface.LieWord k =>
            Hormander.lieWordEval X₂ w (e x)) := by
        change e '' Set.range (fun w : Hormander.Interface.LieWord k =>
          Hormander.Interface.LieWord.eval X w x) = _
        exact hset
      rw [Submodule.map_span, hsetL]
    have htop : Submodule.map L (Submodule.span ℝ (Set.range (fun w :
        Hormander.Interface.LieWord k => Hormander.Interface.LieWord.eval X w x))) = ⊤ := by
      rw [hspan x hx, Submodule.map_top]
      exact LinearMap.range_eq_top.mpr e.surjective
    calc
      Submodule.span ℝ (Set.range (fun w : Hormander.Interface.LieWord k =>
          Hormander.lieWordEval X₂ w (e x))) =
          Submodule.map L (Submodule.span ℝ (Set.range (fun w :
            Hormander.Interface.LieWord k => Hormander.Interface.LieWord.eval X w x))) := hmap.symm
      _ = ⊤ := htop
  obtain ⟨nestedWords, hframeAt⟩ := exists_nested_frame_at_point hΩ₂ X₂ hX₂
    (e x₀) ⟨x₀, hx₀, rfl⟩ (hspan₂ (e x₀) ⟨x₀, hx₀, rfl⟩)
  let words : Fin N → Hormander.Interface.LieWord k := fun a => nestedToLieWord (nestedWords a)
  let frameFields : Fin N → E₂ N → E₂ N := fun a y => Hormander.lieWordEval X₂ (words a) y
  have hframeAt' : LinearIndependent ℝ (fun a => frameFields a (e x₀)) := by
    simpa [frameFields, words] using hframeAt
  have hframeSmooth : ∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (frameFields a) Ω₂ := by
    intro a
    exact lieWordEval_contDiffOn hΩ₂ X₂ hX₂ (words a)
  have hdetSmooth : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => (Hormander.C.frameMatrixAt frameFields y).det) Ω₂ := by
    simp_rw [Matrix.det_apply', Hormander.C.frameMatrixAt, Hormander.C.frameMatrix]
    fun_prop
  have hdetAt : (Hormander.C.frameMatrixAt frameFields (e x₀)).det ≠ 0 :=
    (Hormander.C.frameMatrix_det_ne_zero_iff (fun a => frameFields a (e x₀))).2 hframeAt'
  have hy₀ : e x₀ ∈ Ω₂ := ⟨x₀, hx₀, rfl⟩
  have hdetContinuousAt : ContinuousAt
      (fun y => (Hormander.C.frameMatrixAt frameFields y).det) (e x₀) :=
    hdetSmooth.continuousOn.continuousAt (hΩ₂.mem_nhds hy₀)
  have hdetEventually : ∀ᶠ y in 𝓝 (e x₀),
      (Hormander.C.frameMatrixAt frameFields y).det ≠ 0 :=
    hdetContinuousAt.eventually_ne hdetAt
  have hΩEventually : ∀ᶠ y in 𝓝 (e x₀), y ∈ Ω₂ := hΩ₂.mem_nhds hy₀
  have hnear : ∀ᶠ y in 𝓝 (e x₀),
      y ∈ Ω₂ ∧ (Hormander.C.frameMatrixAt frameFields y).det ≠ 0 :=
    hΩEventually.and hdetEventually
  obtain ⟨R, hRpos, hRball⟩ := Metric.mem_nhds_iff.mp hnear
  let radius : ℝ := R / 2
  have hradius : 0 < radius := by dsimp [radius]; linarith
  have hclosure : closure (Metric.ball (e x₀) radius) ⊆ Ω₂ := by
    calc
      closure (Metric.ball (e x₀) radius) ⊆ Metric.closedBall (e x₀) radius :=
        Metric.closure_ball_subset_closedBall
      _ ⊆ Metric.ball (e x₀) R := Metric.closedBall_subset_ball (by dsimp [radius]; linarith)
      _ ⊆ Ω₂ := fun y hy => (hRball hy).1
  have hBcompact : IsCompact (closure (Metric.ball (e x₀) radius)) := by
    apply (isCompact_closedBall (e x₀) radius).of_isClosed_subset isClosed_closure
    exact Metric.closure_ball_subset_closedBall
  obtain ⟨cutoff, hcutoffSmooth, hcutoffCompact, -, hcutoffSupport, hcutoffOne⟩ :=
    Hormander.D.exists_smooth_cutoff hBcompact hΩ₂ hclosure
  have hcutoffOn : ∀ y ∈ closure (Metric.ball (e x₀) radius), cutoff y = 1 := by
    intro y hy
    have heventually : ∀ᶠ z in 𝓝 y, cutoff z = 1 :=
      hcutoffOne.filter_mono (nhds_le_nhdsSet hy)
    exact heventually.self_of_nhds
  let extendedX : Fin (k + 1) → E₂ N → E₂ N := fun i y => cutoff y • X₂ i y
  let extendedC : E₂ N → ℝ := fun y => cutoff y * c₂ y
  have hextendedXSmooth : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (extendedX i) := by
    intro i
    exact Hormander.C.localized_smul_smooth hΩ₂ cutoff hcutoffSmooth hcutoffSupport
      (X₂ i) (hX₂ i)
  have hextendedXCompact : ∀ i, HasCompactSupport (extendedX i) := by
    intro i
    apply HasCompactSupport.of_support_subset_isCompact hcutoffCompact
    exact (support_smul_subset_left _ _).trans (subset_tsupport cutoff)
  have hextendedC : ContDiff ℝ (⊤ : ℕ∞) extendedC := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun y => cutoff y * c₂ y)
    simpa only [smul_eq_mul] using
      (Hormander.C.localized_smul_smooth hΩ₂ cutoff hcutoffSmooth hcutoffSupport c₂ hc₂)
  have hextendedCCompact : HasCompactSupport extendedC := by
    apply HasCompactSupport.of_support_subset_isCompact hcutoffCompact
    exact (support_mul_subset_left _ _).trans (subset_tsupport cutoff)
  have hextendedXEq : ∀ i,
      ∀ᶠ y in 𝓝ˢ (closure (Metric.ball (e x₀) radius)), extendedX i y = X₂ i y := by
    intro i
    filter_upwards [hcutoffOne] with y hy
    simp [extendedX, hy]
  have hextendedCEq :
      ∀ᶠ y in 𝓝ˢ (closure (Metric.ball (e x₀) radius)), extendedC y = c₂ y := by
    filter_upwards [hcutoffOne] with y hy
    simp [extendedC, hy]
  have hfieldsEq : ∀ i, EqOn (X₂ i) (extendedX i) (Metric.ball (e x₀) radius) := by
    intro i y hy
    simp [extendedX, hcutoffOn y (subset_closure hy)]
  have hframeOnBall : ∀ y ∈ Metric.ball (e x₀) radius,
      LinearIndependent ℝ (fun a => Hormander.lieWordEval extendedX (words a) y) := by
    intro y hy
    have hyR : y ∈ Metric.ball (e x₀) R :=
      Metric.ball_subset_ball (by dsimp [radius]; linarith) hy
    have hdetY := (hRball hyR).2
    have hLIOriginal : LinearIndependent ℝ (fun a => frameFields a y) := by
      apply (Hormander.C.frameMatrix_det_ne_zero_iff (fun a => frameFields a y)).1
      simpa [Hormander.C.frameMatrixAt] using hdetY
    have hwordEq := lieWordEval_eqOn_of_eqOn (Metric.isOpen_ball) X₂ extendedX hfieldsEq
    have hmatrixEq : Hormander.C.frameMatrix
        (fun a => Hormander.lieWordEval extendedX (words a) y) =
        Hormander.C.frameMatrix (fun a => frameFields a y) := by
      ext i a
      simp [Hormander.C.frameMatrix, frameFields, hwordEq (words a) hy]
    apply (Hormander.C.frameMatrix_det_ne_zero_iff
      (fun a => Hormander.lieWordEval extendedX (words a) y)).1
    rw [hmatrixEq]
    exact (Hormander.C.frameMatrix_det_ne_zero_iff (fun a => frameFields a y)).2 hLIOriginal
  let step : ℕ := Finset.univ.sup (fun a : Fin N => Hormander.lieWordLength (words a))
  have hwordLength : ∀ a, Hormander.lieWordLength (words a) ≤ step := by
    intro a
    exact Finset.le_sup (f := fun a : Fin N => Hormander.lieWordLength (words a))
      (Finset.mem_univ a)
  have hstepPos : 0 < step := by
    obtain ⟨a⟩ := (Fin.pos_iff_nonempty.mp hN)
    have hlenNested : 0 < Hormander.C.nestedLength (nestedWords a) := by
      induction nestedWords a with
      | generator i => simp [Hormander.C.nestedLength]
      | bracket i w ih => simp [Hormander.C.nestedLength]
    have hlen : 0 < Hormander.lieWordLength (words a) := by
      simpa [words] using hlenNested
    exact lt_of_lt_of_le hlen (hwordLength a)
  refine ⟨{
    radius := radius
    radius_pos := hradius
    ball_closure_subset := hclosure
    cutoff := cutoff
    cutoff_smooth := hcutoffSmooth
    cutoff_compact := hcutoffCompact
    cutoff_tsupport := hcutoffSupport
    cutoff_one_near_ball := hcutoffOne
    extendedX := extendedX
    extendedX_smooth := hextendedXSmooth
    extendedX_compact := hextendedXCompact
    extendedX_eq_near_ball := hextendedXEq
    extendedC := extendedC
    extendedC_smooth := hextendedC
    extendedC_compact := hextendedCCompact
    extendedC_eq_near_ball := hextendedCEq
    words := words
    frame_on_ball := hframeOnBall
    step := step
    step_eq := rfl
    word_length_le_step := hwordLength
    gain := 2 / (4 : ℝ) ^ step
    gain_eq := rfl
  }⟩

end Hormander.F
