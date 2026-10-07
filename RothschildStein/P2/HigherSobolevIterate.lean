-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HigherSobolevCutoff

/-!
# Higher Sobolev estimate, step 2: the iteration on successively smaller balls

Part of the higher Sobolev estimate (BB pp. 589–590, Prop 11.47: a finite iteration, with no reversed
ball-containment assumption).
At a lifted no-drift chart with the frame hypotheses `HigherFrame` and the cutoff radii `GoodRadius`:

* `liftedRegularity`: if `u ∈ W^{2,p}(U_R)` and `L̃ u = f ∈ W^{k,p}(U_R)` then `u ∈ W^{k+2,p}(U_{R/2^k})`
  (`k` applications of the cutoff regularity step `cutoffRegularity`, each halving the ball);
* `liftedEstimate` (**the a priori estimate on the iterated balls**): if `u ∈ W^{k+2,p}(U_R)` and
  `L̃ u = f ∈ W^{k,p}(U_R)` then
  `‖u‖_{W^{k+2,p}(U_{R/2^{k+2}})} ≤ C (‖f‖_{W^{k,p}(U_R)} + ‖u‖_{L^p(U_R)})`, from the base estimate
  `LiftedBaseSobolevEstimate` (order `k = 0`) and the cutoff recurrence `cutoffEstimate`
  (`k → k + 1`: the cutoff recurrence on `U_ρ`, `ρ = R/2^{k+2}`, bounds the order-`k+3` norm by the order-`k+2`
  norm on `U_ρ`, which the estimate for `k` bounds by the data on `U_R`).
  In the radius normalization (outer radius `2^{k+1} r`, inner radius `r/2`) this is `R = 2^{k+1} r`
  after halving, the inner radius being `R/2^{k+2} = r/2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1 RothschildStein

section Iterate

variable {n q s m : ℕ} {w : Fin q → ℕ+} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)} {q₀ : ℕ}
  {H : H1.StandingHypotheses C.G q₀} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)} {a : TestFunction F.V ℝ (⊤ : ℕ∞)}
  {ν : G2.HomogeneousNorm C.G} {R₀ : ℝ}

/-- **Regularity on the lifted balls without presupposing it**:
`u ∈ W^{2,p}(U_R)` with `L̃ u = f ∈ W^{k,p}(U_R)` lies in `W^{k+2,p}(U_{R/2^k})`, `R < R₀`. -/
theorem liftedRegularity (hH : HigherFrame C H K hQ F a) (hg : GoodRadius C ν F a R₀) {P : ℝ≥0∞}
    (hP1 : 1 < P) (hPt : P ≠ ⊤) (k : ℕ) {R : ℝ} (hR : 0 < R) (hRR : R < R₀)
    {u f : (Fin (n + m) → ℝ) → ℝ} (hu : memSobolevX w C.Xl (rhoBallOpen C ν R) 2 P u)
    (hop : HasWeakOperatorValue C.Xl (rhoBallOpen C ν R) (noDriftOpWords q) u f)
    (hf : memSobolevX w C.Xl (rhoBallOpen C ν R) k P f) :
    memSobolevX w C.Xl (rhoBallOpen C ν (R / 2 ^ k)) (k + 2) P u := by
  induction k with
  | zero => simpa using hu
  | succ k ih =>
    have hf' : memSobolevX w C.Xl (rhoBallOpen C ν R) k P f :=
      RothschildStein.S.memSobolevX_mono_order w C.Xl _ (Nat.le_succ k) hf
    have ih' := ih hf'
    have hle : R / 2 ^ k ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
    have hR' : 0 < R / 2 ^ k := by positivity
    have hsubR : (rhoBallOpen C ν (R / 2 ^ k) : Set (Fin (n + m) → ℝ)) ⊆
        (rhoBallOpen C ν R : Set (Fin (n + m) → ℝ)) :=
      rhoBall_mono C ν (joinPoint x₀ (0 : Fin m → ℝ)) hle
    have hop' : HasWeakOperatorValue C.Xl (rhoBallOpen C ν (R / 2 ^ k)) (noDriftOpWords q) u f :=
      HasWeakOperatorValue.mono hsubR hop
    have hf'' : memSobolevX w C.Xl (rhoBallOpen C ν (R / 2 ^ k)) (k + 1) P f :=
      RothschildStein.S.memSobolevX_restrict w C.Xl _ _ hsubR hf
    have := cutoffRegularity hH hg hP1 hPt k hR' (hle.trans_lt hRR) ih' hop' hf''
    have e : R / 2 ^ k / 2 = R / 2 ^ (k + 1) := by
      rw [pow_succ, div_div]
    rw [e] at this
    exact this

/-- **The a priori estimate on the iterated balls** (BB pp. 589-590, Prop 11.47):
under `HigherFrame`, `GoodRadius` and the lifted base Sobolev estimate there are `R₁ ∈ (0, R₀]` and, for
`R < R₁`, `C > 0` with
`‖u‖_{W^{k+2,p}(U_{R/2^{k+2}})} ≤ C (‖L̃ u‖_{W^{k,p}(U_R)} + ‖u‖_{L^p(U_R)})`
for every `u ∈ W^{k+2,p}(U_R)` with `L̃ u = f ∈ W^{k,p}(U_R)`. -/
theorem liftedEstimate (hH : HigherFrame C H K hQ F a) (hg : GoodRadius C ν F a R₀) {P : ℝ≥0∞}
    (hbase : LiftedBaseSobolevEstimate C ν (noDriftOpWords q) P) (hP1 : 1 < P) (hPt : P ≠ ⊤)
    (k : ℕ) :
    ∃ R₁ : ℝ, 0 < R₁ ∧ R₁ ≤ R₀ ∧ ∀ R : ℝ, 0 < R → R < R₁ → ∃ Cst : ℝ, 0 < Cst ∧
      ∀ u f : (Fin (n + m) → ℝ) → ℝ,
        memSobolevX w C.Xl (rhoBallOpen C ν R) (k + 2) P u →
        HasWeakOperatorValue C.Xl (rhoBallOpen C ν R) (noDriftOpWords q) u f →
        memSobolevX w C.Xl (rhoBallOpen C ν R) k P f →
        sobolevXENorm w C.Xl (rhoBallOpen C ν (R / 2 ^ (k + 2))) (k + 2) P u ≤
          ENNReal.ofReal Cst * (sobolevXENorm w C.Xl (rhoBallOpen C ν R) k P f +
            eLpNorm u P (volume.restrict (rhoBallOpen C ν R : Set (Fin (n + m) → ℝ)))) := by
  have hP : (1 : ℝ≥0∞) ≤ P := hP1.le
  induction k with
  | zero =>
    obtain ⟨r₀, hr₀, hb⟩ := hbase
    refine ⟨min (2 * r₀) R₀, lt_min (by linarith) hg.1, min_le_right _ _, fun R hR hRR => ?_⟩
    have hRr : R / 2 ≤ r₀ := by
      have := hRR.trans_le (min_le_left _ _)
      linarith
    obtain ⟨Cst, hCst, hmain⟩ := hb (R / 2) (half_pos hR) hRr
    refine ⟨Cst, hCst, fun u f hu hop hf => ?_⟩
    have hsub : (rhoBallOpen C ν (R / 2) : Set (Fin (n + m) → ℝ)) ⊆
        (rhoBallOpen C ν R : Set (Fin (n + m) → ℝ)) :=
      rhoBall_mono C ν (joinPoint x₀ (0 : Fin m → ℝ)) (by linarith)
    have hu' : memSobolevX w C.Xl (rhoBallOpen C ν (R / 2)) 2 P u :=
      RothschildStein.S.memSobolevX_restrict w C.Xl _ _ hsub hu
    have hop' : HasWeakOperatorValue C.Xl (rhoBallOpen C ν (R / 2)) (noDriftOpWords q) u f :=
      HasWeakOperatorValue.mono hsub hop
    have h1 := hmain u f hu' hop'
    have e : R / 2 ^ (0 + 2) = R / 2 / 2 := by rw [div_div]; norm_num
    rw [e, sobolevXENorm_zero_eq_eLpNorm w C.Xl _ hP]
    refine h1.trans (mul_le_mul' le_rfl (add_le_add ?_ ?_))
    · exact eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)
    · exact eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)
  | succ k ih =>
    obtain ⟨R₁, hR₁, hR₁R₀, hE⟩ := ih
    refine ⟨R₁, hR₁, hR₁R₀, fun R hR hRR => ?_⟩
    have hρ : 0 < R / 2 ^ (k + 2) := by positivity
    have hρR : R / 2 ^ (k + 2) ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
    obtain ⟨C₁, hC₁, h1⟩ := cutoffEstimate hH hg hP1 hPt (k + 1) hρ
      (hρR.trans_lt (hRR.trans_le hR₁R₀))
    obtain ⟨C₂, hC₂, h2⟩ := hE R hR hRR
    refine ⟨C₁ * (1 + C₂), mul_pos hC₁ (by linarith), fun u f hu hop hf => ?_⟩
    have huk : memSobolevX w C.Xl (rhoBallOpen C ν R) (k + 2) P u :=
      RothschildStein.S.memSobolevX_mono_order w C.Xl _ (Nat.le_succ _) hu
    have hfk : memSobolevX w C.Xl (rhoBallOpen C ν R) k P f :=
      RothschildStein.S.memSobolevX_mono_order w C.Xl _ (Nat.le_succ _) hf
    have hsub : (rhoBallOpen C ν (R / 2 ^ (k + 2)) : Set (Fin (n + m) → ℝ)) ⊆
        (rhoBallOpen C ν R : Set (Fin (n + m) → ℝ)) :=
      rhoBall_mono C ν (joinPoint x₀ (0 : Fin m → ℝ)) hρR
    have hu_ρ : memSobolevX w C.Xl (rhoBallOpen C ν (R / 2 ^ (k + 2))) (k + 1 + 2) P u :=
      RothschildStein.S.memSobolevX_restrict w C.Xl _ _ hsub hu
    have hop_ρ : HasWeakOperatorValue C.Xl (rhoBallOpen C ν (R / 2 ^ (k + 2))) (noDriftOpWords q) u f :=
      HasWeakOperatorValue.mono hsub hop
    have hf_ρ : memSobolevX w C.Xl (rhoBallOpen C ν (R / 2 ^ (k + 2))) (k + 1) P f :=
      RothschildStein.S.memSobolevX_restrict w C.Xl _ _ hsub hf
    have step1 := h1 u f hu_ρ hop_ρ hf_ρ
    have step2 := h2 u f huk hop hfk
    have hfmono : sobolevXENorm w C.Xl (rhoBallOpen C ν (R / 2 ^ (k + 2))) (k + 1) P f ≤
        sobolevXENorm w C.Xl (rhoBallOpen C ν R) (k + 1) P f :=
      sobolevXENorm_mono_domain w C.Xl hsub hf
    have hfk' : sobolevXENorm w C.Xl (rhoBallOpen C ν R) k P f ≤
        sobolevXENorm w C.Xl (rhoBallOpen C ν R) (k + 1) P f :=
      sobolevXENorm_mono_order (Nat.le_succ k) f
    set a₁ := sobolevXENorm w C.Xl (rhoBallOpen C ν R) (k + 1) P f with ha₁
    set a₂ := eLpNorm u P (volume.restrict (rhoBallOpen C ν R : Set (Fin (n + m) → ℝ))) with ha₂
    have e : R / 2 ^ (k + 1 + 2) = R / 2 ^ (k + 2) / 2 := by
      rw [show k + 1 + 2 = (k + 2) + 1 from rfl, pow_succ, div_div]
    rw [e]
    calc sobolevXENorm w C.Xl (rhoBallOpen C ν (R / 2 ^ (k + 2) / 2)) (k + 1 + 2) P u
        ≤ ENNReal.ofReal C₁ * (sobolevXENorm w C.Xl (rhoBallOpen C ν (R / 2 ^ (k + 2))) (k + 1) P f +
          sobolevXENorm w C.Xl (rhoBallOpen C ν (R / 2 ^ (k + 2))) (k + 1 + 1) P u) := step1
      _ ≤ ENNReal.ofReal C₁ * (a₁ + ENNReal.ofReal C₂ * (a₁ + a₂)) := by
          refine mul_le_mul' le_rfl (add_le_add hfmono ?_)
          refine step2.trans (mul_le_mul' le_rfl (add_le_add hfk' le_rfl))
      _ ≤ ENNReal.ofReal C₁ * ((a₁ + a₂) + ENNReal.ofReal C₂ * (a₁ + a₂)) :=
          mul_le_mul' le_rfl (add_le_add le_self_add le_rfl)
      _ = ENNReal.ofReal (C₁ * (1 + C₂)) * (a₁ + a₂) := by
          rw [ENNReal.ofReal_mul hC₁.le, ENNReal.ofReal_add zero_le_one hC₂.le, ENNReal.ofReal_one]
          ring

end Iterate

end RothschildStein.P2
