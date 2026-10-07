-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SmoothPotentialSecondHolderBound
public import RothschildStein.H3.SmoothPotentialFirstFrozenBound
public import RothschildStein.H3.SmoothPotentialLocalJets
public import RothschildStein.H3.SecondHolderNormFormula
public import RothschildStein.H3.LocalHolderSupNorm
public import RothschildStein.H3.ControlDistanceGeometry
public import RothschildStein.G2.NormConstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- The smooth-source Holder estimate (⋆) for the fundamental potential.
The first-kernel and principal-value bounds control every weighted word
under the global control-norm hypotheses. -/
theorem smooth_potential_full_holder_bound_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    {a : ℝ≥0} (ha : 0 < a) (ha1 : (a : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ A : ℝ, 0 < A ∧ ∀ f : (Fin N → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      tsupport f ⊆ {x | C.norm x < ρ} →
      holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields)
        (quasiballDomain G C.norm 0 ρ) 2 a (G2.groupConvolution G f K) ≤
      ENNReal.ofReal A * holderENorm (controlDistance univ driftWeight H.fields) a univ f := by
  classical
  let U := quasiballDomain G C.norm 0 ρ
  let d := controlDistance univ driftWeight H.fields
  let D := controlDistanceGeometry_of_controlNorm G driftWeight H.fields C
  obtain ⟨A₁, hA₁, hfirst⟩ := smooth_potential_first_holderX_bound_of_controlNorm G H K C hQ
    (G2.smoothNorm G) (G2.smoothNorm_smooth G) ha ha1 hρ
  have hUR : ∀ x ∈ U, C.norm x < ρ := by
    intro x hx
    change C.norm (G.mul (G.inv 0) x) < ρ at hx
    rwa [G2.inv_zero, G2.zero_mul] at hx
  obtain ⟨L, hL, hsecond⟩ := smooth_potential_second_holder_bound_of_controlNorm
    G H K hQ C ha ha1 U hρ hUR
  let P : ℝ := (q : ℝ)^2 + (1 + (q : ℝ))
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  refine ⟨A₁ + P * L, add_pos_of_pos_of_nonneg hA₁ (mul_nonneg hP hL0), ?_⟩
  intro f hf hc hs
  have hsU : tsupport f ⊆ (U : Set (Fin N → ℝ)) := by
    intro x hx
    change C.norm (G.mul (G.inv 0) x) < ρ
    rw [G2.inv_zero, G2.zero_mul]
    exact hs hx
  have hfN := smooth_source_global_holder_finite_of_controlNorm G H.fields C a ha1.le ρ f hf hc hs
  have hp := hfirst 0 f hf hc hsU
  have hlp : eLpNorm f ⊤ volume ≤ holderENorm d a univ f := by
    have hh := eLpNorm_top_le_local_holderNorm ⊤ ⊤ D (subset_univ _) ha hfN
    change eLpNorm f ⊤ (volume.restrict (univ : Set (Fin N → ℝ))) ≤
      holderENorm d a univ f at hh
    simpa only [Measure.restrict_univ] using hh
  have hlpR : lpNorm f ⊤ volume ≤ (holderENorm d a univ f).toReal :=
    ENNReal.toReal_mono hfN.ne hlp
  have hp' : holderXENorm driftWeight H.fields d U 1 a (G2.groupConvolution G f K) ≤
      ENNReal.ofReal A₁ * holderENorm d a univ f := by
    apply hp.trans
    calc
      _ ≤ ENNReal.ofReal (A₁ * (holderENorm d a univ f).toReal) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hlpR hA₁.le)
      _ = _ := by
        rw [ENNReal.ofReal_mul hA₁.le,
          ENNReal.ofReal_toReal (show holderENorm d a univ f ≠ ⊤ from hfN.ne)]
  have hq : ENNReal.ofReal P = (q : ℝ≥0∞)^2 + (1 + (q : ℝ≥0∞)) := by
    dsimp [P]
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by norm_num) (by positivity),
      ENNReal.ofReal_pow (Nat.cast_nonneg q)]
    simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  have hcoef : ENNReal.ofReal (A₁ + P * L) =
      ENNReal.ofReal A₁ + ((q : ℝ≥0∞)^2 + (1 + (q : ℝ≥0∞))) * ENNReal.ofReal L := by
    rw [ENNReal.ofReal_add hA₁.le (mul_nonneg hP hL0), ENNReal.ofReal_mul hP, hq]
  have he : holderXENorm driftWeight H.fields d U 2 a (G2.groupConvolution G f K) =
      holderXENorm driftWeight H.fields d U 1 a (G2.groupConvolution G f K) +
      ((∑ i : Fin q, ∑ j : Fin q, holderENorm d a (U : Set (Fin N → ℝ))
        (wordDerivative H.fields [i.succ, j.succ] (G2.groupConvolution G f K))) +
        holderENorm d a (U : Set (Fin N → ℝ))
          (wordDerivative H.fields [0] (G2.groupConvolution G f K))) := by
    rw [holderXENorm_drift_two_split]
    simp_rw [smooth_fundamental_potential_intrinsic_norm G H K hQ f hf hc]
    ac_rfl
  rw [he, hcoef, add_mul]
  exact add_le_add hp' (hsecond f hf hc hsU)

end RothschildStein.H3
