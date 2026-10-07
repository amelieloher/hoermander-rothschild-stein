-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SolvabilityFullFrame
public import RothschildStein.P2.SolvabilityFullLp
public import RothschildStein.P2.SolvabilityFullWeak
public import RothschildStein.P2.SmoothingChart
public import RothschildStein.P1.GainHolder
public import RothschildStein.S.SobolevAE

/-!
# Local solvability, `L^p` half: `v = P_R E_R f ∈ W^{2,p}(U_R)` with `L̃ v = g` a.e.

For a lifted drift chart `C`, a centre `ξ₀ ∈ C.U`, `1 < p < ∞`, the local solvability argument gives, for
`g ∈ L^p(U_R)` and `R` small, `v ∈ W^{2,p}_{X̃}(U_R)` with `L̃ v = g` a.e. The distributional solution
`v = P_R E_R f` is `exists_lp_solution`; its membership in `W^{2,p}` is the gain theorem (under the `LeftDifferentiation` hypothesis for the standard frame of the chart patch), applied to the bounded `L^p` extension of the
type-2 operator `P_R` which, on `L^p` input, is the integral `P_R` itself (`SolvabilityFullLp`); and
`L̃ v = g` a.e. follows from the weak derivatives of `v` and the distributional equation
(`SolvabilityFullWeak`).

`LeftDifferentiationOnStandardFrames K hQ` is the hypothesis `LeftDifferentiation` (left differentiation) for every standard
frame of the chart with the kernel `Γ = K`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators Distributions
open RothschildStein.P1
namespace RothschildStein.P2

section Sobolev

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : P1.LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m}
  {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
  (K : H1.FundamentalKernel C.G (C.driftModel hq ν₀))
  (hQ : 2 < (C.G.homogeneousDimension : ℝ))

variable (C) in
/-- The hypothesis `LeftDifferentiation` (left differentiation of type-`λ` operators) for
every standard frame of the chart `C` with the kernel `Γ = K`. -/
def LeftDifferentiationOnStandardFrames : Prop :=
  ∀ F : KernelFrame (n + m), C.IsStandardFrame F (C.driftModel hq ν₀) K hQ →
    LeftDifferentiation F (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) C.Xl

/-- **Fixed frame data around a centre.** For `ξ₀ ∈ C.U` there are a patch `V ∋ ξ₀` with
closure in `C.U`, cutoffs `a, b ∈ C_c^∞(V)` with `a b = a` and `a = 1` near `ξ₀`, and a compact
`K₀ ⊆ V` with an admissible radius `r_*` for `ξ₀`. -/
theorem exists_fixed_frame {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U) :
    ∃ (V : Opens (Fin (n + m) → ℝ)) (a b : TestFunction V ℝ (⊤ : ℕ∞))
      (K₀ : Set (Fin (n + m) → ℝ)) (rstar : ℝ),
      ξ₀ ∈ (V : Set (Fin (n + m) → ℝ)) ∧ closure (V : Set (Fin (n + m) → ℝ)) ⊆ C.U ∧
        (∀ ξ, a ξ * b ξ = a ξ) ∧ (∀ᶠ ξ in 𝓝 ξ₀, a ξ = 1) ∧ IsCompact K₀ ∧
        K₀ ⊆ (V : Set (Fin (n + m) → ℝ)) ∧ C.IsSmallBallRadius K₀ ξ₀ rstar := by
  obtain ⟨V, a, b, hξV, hVcl, hab, ha1⟩ := exists_frame_cutoffs C hξ₀
  obtain ⟨K₀, rstar, hK₀, hK₀V, hr⟩ := exists_small_balls_in C (subset_closure.trans hVcl) hξV
  exact ⟨V, a, b, K₀, rstar, hξV, hVcl, hab, ha1, hK₀, hK₀V, hr⟩

/-- **The `L^p` half of local solvability, assuming `LeftDifferentiation`.** For `ξ₀ ∈ C.U` and
`1 < p < ∞` there is `R₀ > 0` such that for every `0 < R < R₀`, on `U_R = B̃(ξ₀, R)` every
`g ∈ L^p(U_R)` has a `v ∈ W^{2,p}_{X̃}(U_R)` (`memSobolevX`) with `L̃ v = g` almost
everywhere (`weakDriftEquation`). Here `v = P_R E_R f` for the fixed point `f = g + 𝓕_R f`; the
membership is the gain theorem (`LeftDifferentiation` for the standard frame of a patch `V ∋ ξ₀`), the
equation is `exists_lp_solution` and the weak derivatives. -/
theorem localSolvability_lp_of_leftDifferentiation (hsymm : ∀ u, (C.driftModel hq ν₀).norm (-u) = (C.driftModel hq ν₀).norm u)
    (hsmooth : (C.driftModel hq ν₀).norm.Smooth) (hprops : H1.FundamentalKernelProperties K)
    (hLeftDiff : LeftDifferentiationOnStandardFrames C K hQ) {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U) {p : ℝ≥0∞}
    (hp : 1 < p) (hpt : p < ⊤) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ →
      ∀ UR : Opens (Fin (n + m) → ℝ), (UR : Set (Fin (n + m) → ℝ)) = C.driftBall ξ₀ R →
        ∀ g : (Fin (n + m) → ℝ) → ℝ, MemLp g p (volume.restrict (UR : Set (Fin (n + m) → ℝ))) →
          ∃ v : (Fin (n + m) → ℝ) → ℝ, memSobolevX driftWeight C.Xl UR 2 p v ∧
            weakDriftEquation UR C.Xl v g := by
  obtain ⟨V, a, b, K₀, rstar, hξV, hVcl, hab, ha1, hK₀, hK₀V, hr⟩ := exists_fixed_frame hξ₀
  have hVU : (V : Set (Fin (n + m) → ℝ)) ⊆ C.U := subset_closure.trans hVcl
  have hF := isStandardFrame_stdFrame K hQ V hVcl hsymm hsmooth hprops
  have hLeftDiffF := hLeftDiff _ hF
  have hVle : V ≤ C.chartOpens := hVU
  let aC : TestFunction C.chartOpens ℝ (⊤ : ℕ∞) := LiftedChart.testOfLe V hVle a
  let bC : TestFunction C.chartOpens ℝ (⊤ : ℕ∞) := LiftedChart.testOfLe V hVle b
  obtain ⟨r₀, hr₀, hsolve⟩ := exists_lp_solution K aC bC hab hξ₀ ha1
  have : Fact (1 ≤ p) := ⟨hp.le⟩
  refine ⟨min r₀ rstar, lt_min hr₀ hr.pos, fun R hR0 hRR UR hUR g hg => ?_⟩
  have hRr₀ : R < r₀ := hRR.trans_le (min_le_left _ _)
  have hRrs : R < rstar := hRR.trans_le (min_le_right _ _)
  have hg' : MemLp g p (volume.restrict (C.driftBall ξ₀ R)) := by
    rw [← hUR]
    exact hg
  obtain ⟨f, hf, -, -, -, hsol⟩ := hsolve R hR0 hRr₀ p hp.le hpt.ne g hg'
  have hEV : C.driftBall ξ₀ R ⊆ (V : Set (Fin (n + m) → ℝ)) :=
    (hr.ball_subset R hR0 hRrs).trans hK₀V
  have hEm : MeasurableSet (C.driftBall ξ₀ R) := by
    rw [← hUR]
    exact UR.isOpen.measurableSet
  have hURV : (UR : Set (Fin (n + m) → ℝ)) ⊆ (V : Set (Fin (n + m) → ℝ)) := by
    rw [hUR]
    exact hEV
  have hURU : (UR : Set (Fin (n + m) → ℝ)) ⊆ C.U := hURV.trans hVU
  have hgV : MemLp ((C.driftBall ξ₀ R).indicator f) p (volume.restrict (V : Set (Fin (n + m) → ℝ))) := by
    rw [memLp_indicator_iff_restrict hEm, Measure.restrict_restrict hEm, inter_eq_left.2 hEV]
    exact hf
  -- the bounded extension of `P_R` and its gain
  have hp1 : 1 < p := hp
  obtain ⟨Λ₀, -, Tb, -, hTbt, -, -⟩ :=
    (rightOp K hQ V hVcl a b).exists_lpExtension_standard hF hp1 hpt.ne
  obtain ⟨Cg, -, hgain⟩ := (rightOp K hQ V hVcl a b).gain_lp_extension hF hLeftDiffF hp1 hpt.ne
  have hTbt' := fun f => (hTbt f).2
  have hmem := (hgain Tb hTbt' (hgV.toLp _)).1
  have hid := (rightOp K hQ V hVcl a b).lpExtension_eq_apply_of_memLp hF (by norm_num) hp1 hpt.ne
    Tb hTbt' hgV
  rw [rightOp_apply K hQ V hVcl a b] at hid
  have hmemV : memSobolevX driftWeight C.Xl V 2 p
      (C.rightParametrix K aC bC ((C.driftBall ξ₀ R).indicator f)) :=
    (RothschildStein.S.memSobolevX_congr_ae C.Xl V driftWeight 2 p hid).1 hmem
  have hmemUR : memSobolevX driftWeight C.Xl UR 2 p
      (C.rightParametrix K aC bC ((C.driftBall ξ₀ R).indicator f)) :=
    RothschildStein.S.memSobolevX_restrict driftWeight C.Xl V UR hURV hmemV
  refine ⟨_, hmemUR, ?_⟩
  -- the equation
  have hXUR : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (UR : Set (Fin (n + m) → ℝ)) :=
    fun i => (liftedChart_contDiffOn_lift C i).mono hURU
  obtain ⟨g₀, hg₀, -⟩ := hmemUR.2 [0] mem_wordFamily_drift_zero
  choose gs hgs _ using fun i : Fin q => hmemUR.2 [i.succ, i.succ] (mem_wordFamily_drift_succ_succ i)
  have hURle : UR ≤ C.chartOpens := hURU
  have hsolUR : ∀ φ : TestFunction UR ℝ (⊤ : ℕ∞),
      ∫ ξ in (UR : Set (Fin (n + m) → ℝ)),
          C.rightParametrix K aC bC ((C.driftBall ξ₀ R).indicator f) ξ *
            sumSquaresWithDriftTranspose C.Xl φ ξ =
        ∫ ξ in (UR : Set (Fin (n + m) → ℝ)), g ξ * φ ξ := by
    intro φ
    have hφt : tsupport ((LiftedChart.testOfLe UR hURle φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
        (Fin (n + m) → ℝ) → ℝ) ⊆ C.driftBall ξ₀ R := by
      rw [← hUR]
      exact φ.tsupport_subset
    have h1 := hsol (LiftedChart.testOfLe UR hURle φ) hφt
    have h2 := setIntegral_mul_sumSquaresWithDriftTranspose_eq UR C.Xl hXUR
      C.isOpen_U.measurableSet hURU
      (C.rightParametrix K aC bC ((C.driftBall ξ₀ R).indicator f)) φ
    have h3 : ∫ ξ in C.driftBall ξ₀ R, g ξ * φ ξ = ∫ ξ in (UR : Set (Fin (n + m) → ℝ)), g ξ * φ ξ := by
      rw [hUR]
    rw [← h2, ← h3]
    exact h1
  have hglocal : LocallyIntegrableOn g (UR : Set (Fin (n + m) → ℝ)) volume :=
    locallyIntegrableOn_of_memLp UR.isOpen hp.le hg
  have hae := weakDriftEquation_ae_of_solution UR C.Xl hXUR hg₀ hgs hglocal hsolUR
  exact ⟨g₀, gs, hg₀, hgs, hae⟩

end Sobolev

end RothschildStein.P2
