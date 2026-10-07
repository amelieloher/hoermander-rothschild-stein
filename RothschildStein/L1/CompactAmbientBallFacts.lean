-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.CompactDomainBallEquality
public import RothschildStein.L1.FreeOrdinaryBallVolumeProvider
public import RothschildStein.G1.ActualControlComparison
public import RothschildStein.G1.ControlBallOpenness

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.L1

/-- Small ambient balls from every
center of a compact patch stay in the patch, are open and measurable,
and have positive finite volume. Rank is required only on the patch
(BB pp. 519–522; the compact-center domain repair). -/
theorem exists_compact_ambient_ball_facts {a n s : ℕ}
    {U K : Set (Fin n → ℝ)} (hU : IsOpen U)
    (hclosure : IsCompact (closure U)) (hK : IsCompact K) (hKU : K ⊆ U)
    (w : Fin a → ℕ+) (hs : 1 ≤ s) (hw : ∀ i, (w i : ℕ) ≤ s)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) U)
    (hstep : bracketStepOn U w X s) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ Ω : Set (Fin n → ℝ), U ⊆ Ω →
      ∀ x ∈ K, ∀ r : ℝ, 0 < r → r ≤ r₀ →
        rsBall Ω w X x r ⊆ U ∧ IsOpen (rsBall Ω w X x r) ∧
        MeasurableSet (rsBall Ω w X x r) ∧
        volume (rsBall Ω w X x r) ≠ ⊤ ∧
        0 < (volume (rsBall Ω w X x r)).toReal := by
  have hcomp := G1.localControlComparison_of_smooth_bracketStep hU w X hX hs hw hstep
  obtain ⟨r₀,hr₀,_,hd⟩ := exists_compact_controlBall_domain_equality hU hK hKU X hX w
  refine ⟨r₀,hr₀,?_⟩
  intro Ω hUΩ x hx r hr hrr
  have he : rsBall Ω w X x r = rsBall U w X x r := by
    simpa only [rsBall,ordinary_ball_inter_domain_eq] using hd Ω hUΩ x hx r hr hrr
  have hsub : rsBall Ω w X x r ⊆ U := by
    rw [he]
    exact fun _ hy => hy.1
  have hopen : IsOpen (rsBall Ω w X x r) := by
    rw [he]
    exact G1.isOpen_rsBall_of_local_comparison hU w X
      (fun i => (hX i).continuousOn) (by omega) hcomp (hKU hx) r
  have hfin : volume (rsBall Ω w X x r) ≠ ⊤ :=
    ne_top_of_le_ne_top hclosure.measure_lt_top.ne (measure_mono (hsub.trans subset_closure))
  have hself : x ∈ rsBall Ω w X x r := by
    refine ⟨hUΩ (hKU hx),?_⟩
    rw [G1.controlDistance_self w X (hUΩ (hKU hx))]
    exact ENNReal.ofReal_pos.mpr hr
  exact ⟨hsub,hopen,hopen.measurableSet,hfin,
    ENNReal.toReal_pos (hopen.measure_pos volume ⟨x,hself⟩).ne' hfin⟩

end RothschildStein.L1
