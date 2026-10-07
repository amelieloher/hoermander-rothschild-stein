-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HigherSobolevIterate

/-!
# Transfer of the iterated estimate to the original domain (local step)

Part of the higher Sobolev estimate (BB p. 591: "Transfer and cover as above"; the Sobolev transfer and finite-cover argument, BB p. 587). The lifted a priori
estimate for order `kk + 2`, `LiftedHigherEstimate`

`‖u‖_{W^{kk+2,p}(U_{R/2^{kk+2}})} ≤ C (‖L̃ u‖_{W^{kk,p}(U_R)} + ‖u‖_{L^p(U_R)})` (`R < R₁`),

gives, through the lifted Sobolev norm transfer (`FiberSetting.le_sobolevXENorm_lift`,
`sobolevXENorm_lift_le`), the original estimate on a small base ball around the chart base point:
for `ε > 0` there are `0 < ρ ≤ b ≤ ε` and `K > 0` with
`‖u‖_{W^{kk+2,p}(V_ρ)} ≤ K (‖L u‖_{W^{kk,p}(V_b)} + ‖u‖_{L^p(V_b)})` for `u ∈ W^{kk+2,p}_X(V_b)`
(`higher_local_transfer`). It is the proof of `sobolev_local_transfer` (for the base Sobolev estimate) with the radii
`(R/2^{kk+2}, R)` in place of `(R/2, R)`, and the data norm of order `kk`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1 RothschildStein

section Transfer

variable {n k : ℕ} {w : Fin k → ℕ+} {st : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}

/-- The lifted higher estimate on a chart (the conclusion of
`liftedEstimate`): there is `R₁ > 0` such that for `0 < R < R₁` there is `C(R) > 0` with
`‖u‖_{W^{kk+2,p}(U_{R/2^{kk+2}})} ≤ C (‖L̃ u‖_{W^{kk,p}(U_R)} + ‖u‖_{L^p(U_R)})` for every
`u ∈ W^{kk+2,p}_{X̃}(U_R)` with `L̃ u = f ∈ W^{kk,p}_{X̃}(U_R)`. -/
def LiftedHigherEstimate {ι : Type} [Fintype ι] (C : LiftedChart w st Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) (J : ι → List (Fin k)) (p : ℝ≥0∞) (kk : ℕ) : Prop :=
  ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ R : ℝ, 0 < R → R < R₁ → ∃ Cst : ℝ, 0 < Cst ∧
    ∀ u f : (Fin (n + m) → ℝ) → ℝ,
      memSobolevX w C.Xl (rhoBallOpen C ν R) (kk + 2) p u →
      HasWeakOperatorValue C.Xl (rhoBallOpen C ν R) J u f →
      memSobolevX w C.Xl (rhoBallOpen C ν R) kk p f →
      sobolevXENorm w C.Xl (rhoBallOpen C ν (R / 2 ^ (kk + 2))) (kk + 2) p u ≤
        ENNReal.ofReal Cst * (sobolevXENorm w C.Xl (rhoBallOpen C ν R) kk p f +
          eLpNorm u p (volume.restrict (rhoBallOpen C ν R : Set (Fin (n + m) → ℝ))))

/-- From the lifted higher estimate, the original estimate on a small
base ball: for `ε > 0` there are `0 < ρ ≤ b ≤ ε` and `K > 0` with
`‖u‖_{W^{kk+2,p}(V_ρ)} ≤ K (‖f‖_{W^{kk,p}(V_b)} + ‖u‖_{L^p(V_b)})` for `u ∈ W^{kk+2,p}_X(V_b)` with
`L u = f ∈ W^{kk,p}_X(V_b)` (`V_ρ = B(x₀, ρ)`, `V_b = B(x₀, b)`), and the control balls `B(x₀, ρ')`, `ρ' ≤ b`,
are Euclidean open. -/
theorem higher_local_transfer {ι : Type} [Fintype ι] (C : LiftedChart w st Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) (J : ι → List (Fin k)) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    {kk : ℕ} (hest : LiftedHigherEstimate C ν J p kk) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ b K : ℝ, 0 < ρ ∧ ρ ≤ b ∧ b ≤ ε ∧ 0 < K ∧
      (∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ b → IsOpen (rsBall Ω w X x₀ ρ')) ∧
      ∀ (Vρ Vb : Opens (Fin n → ℝ)), (Vρ : Set (Fin n → ℝ)) = rsBall Ω w X x₀ ρ →
        (Vb : Set (Fin n → ℝ)) = rsBall Ω w X x₀ b → ∀ u f : (Fin n → ℝ) → ℝ,
        memSobolevX w X Vb (kk + 2) p u → HasWeakOperatorValue X Vb J u f →
        memSobolevX w X Vb kk p f →
        sobolevXENorm w X Vρ (kk + 2) p u ≤ ENNReal.ofReal K *
          (sobolevXENorm w X Vb kk p f +
            eLpNorm u p (volume.restrict (Vb : Set (Fin n → ℝ)))) := by
  classical
  set η₀ : Fin (n + m) → ℝ := joinPoint x₀ (0 : Fin m → ℝ) with hη₀
  have hK : IsCompact ({η₀} : Set (Fin (n + m) → ℝ)) := isCompact_singleton
  have hKU : ({η₀} : Set (Fin (n + m) → ℝ)) ⊆ C.U := singleton_subset_iff.mpr C.center_mem
  have hbase : basePoint η₀ = x₀ := basePoint_joinPoint x₀ 0
  obtain ⟨R₁, hR₁, hbound⟩ := hest
  obtain ⟨Cν, hCν1, hgc⟩ := exists_gauge_comparison C ν
  obtain ⟨ρ₀, hρ₀, hopen⟩ := exists_isOpen_base_ball C
  obtain ⟨rF, δ, cLo, cHi, hrF, hδ0, hδ1, hcLo, hcHi, hF⟩ := exists_fiberBounds' C hK hKU
  have hCν0 : 0 < Cν := lt_of_lt_of_le one_pos hCν1
  set A : ℝ := 2 * Cν ^ 2 * 2 ^ (kk + 2) with hAdef
  have hA : (1 : ℝ) ≤ A := by
    have h1 : (1 : ℝ) ≤ Cν ^ 2 := one_le_pow₀ hCν1
    have h2 : (1 : ℝ) ≤ 2 ^ (kk + 2) := one_le_pow₀ (by norm_num)
    have h3 : (1 : ℝ) ≤ Cν ^ 2 * 2 ^ (kk + 2) := one_le_mul_of_one_le_of_one_le h1 h2
    rw [hAdef, mul_assoc]
    linarith
  obtain ⟨rS, C₁, hrS, hC₁, hscale⟩ := ballRatioAt_scale_le C hK hKU hA
  obtain ⟨rB, cv, Cv, δB, cf, Cf, hrB, -, -, -, -, -, -, hall⟩ := C.ball_bounds {η₀} hK hKU
  -- the radii
  set Rr : ℝ := min (min (min rF rB) (min rS ρ₀)) ε with hRr
  have hRr0 : 0 < Rr := lt_min (lt_min (lt_min hrF hrB) (lt_min hrS hρ₀)) hε
  have hRF : Rr ≤ rF := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hRB : Rr ≤ rB := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hRS : Rr ≤ rS := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRρ : Rr ≤ ρ₀ := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hRε : Rr ≤ ε := min_le_right _ _
  set r : ℝ := min (R₁ / 2) (Rr / (4 * Cν)) with hr
  have hr0 : 0 < r := lt_min (half_pos hR₁) (by positivity)
  have hrR₁ : r < R₁ := (min_le_left _ _).trans_lt (half_lt_self hR₁)
  have hrR : r ≤ Rr / (4 * Cν) := min_le_right _ _
  obtain ⟨rin, hrin⟩ : ∃ rin : ℝ, rin = r / 2 ^ (kk + 2) := ⟨_, rfl⟩
  have hrin0 : 0 < rin := by rw [hrin]; positivity
  have hrinr : rin ≤ r := by
    rw [hrin]
    exact div_le_self hr0.le (one_le_pow₀ (by norm_num))
  obtain ⟨a₁, ha₁⟩ : ∃ a₁ : ℝ, a₁ = rin / Cν := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 2 * Cν * r := ⟨_, rfl⟩
  have ha0 : 0 < a₁ := by rw [ha₁]; positivity
  have hb0 : 0 < b := by rw [hb]; positivity
  have hAa : A * a₁ = b := by
    rw [ha₁, hb, hrin, hAdef]
    field_simp
  have hab : a₁ ≤ b := by
    calc a₁ = 1 * a₁ := (one_mul _).symm
      _ ≤ A * a₁ := mul_le_mul_of_nonneg_right hA ha0.le
      _ = b := hAa
  have hbR : b ≤ Rr / 2 := by
    rw [hb]
    have : 2 * Cν * r ≤ 2 * Cν * (Rr / (4 * Cν)) := mul_le_mul_of_nonneg_left hrR (by positivity)
    calc 2 * Cν * r ≤ 2 * Cν * (Rr / (4 * Cν)) := this
      _ = Rr / 2 := by field_simp; ring
  have hbR' : b < Rr := by linarith
  have hbrF : b < rF := lt_of_lt_of_le hbR' hRF
  have hbrB : b < rB := lt_of_lt_of_le hbR' hRB
  have hbrS : b < rS := lt_of_lt_of_le hbR' hRS
  have hbρ : b ≤ ρ₀ := (hbR'.trans_le hRρ).le
  have hbε : b ≤ ε := (hbR'.trans_le hRε).le
  have hδa : δ * a₁ ≤ b := by
    have := mul_le_mul_of_nonneg_right hδ1.le ha0.le
    linarith
  have hδa0 : 0 < δ * a₁ := mul_pos hδ0 ha0
  have hδb0 : 0 < δ * b := mul_pos hδ0 hb0
  have hδb : δ * b ≤ b := by
    have := mul_le_mul_of_nonneg_right hδ1.le hb0.le
    linarith
  -- the open sets
  have hUaU : rsBall C.O w C.Xl η₀ a₁ ⊆ C.U := by
    obtain ⟨h, -⟩ := hall η₀ (mem_singleton _) a₁ ha0 (lt_of_le_of_lt hab hbrB)
    exact h
  have hUbU : rsBall C.O w C.Xl η₀ b ⊆ C.U := by
    obtain ⟨h, -⟩ := hall η₀ (mem_singleton _) b hb0 hbrB
    exact h
  let Va : Opens (Fin n → ℝ) :=
    ⟨rsBall Ω w X (basePoint η₀) a₁, by rw [hbase]; exact hopen a₁ ha0 (hab.trans hbρ)⟩
  let Vδb : Opens (Fin n → ℝ) :=
    ⟨rsBall Ω w X (basePoint η₀) (δ * b), by rw [hbase]; exact hopen _ hδb0 (hδb.trans hbρ)⟩
  let Ua : Opens (Fin (n + m) → ℝ) := ⟨rsBall C.O w C.Xl η₀ a₁, isOpen_rsBall_lifted C hUaU⟩
  let Ub : Opens (Fin (n + m) → ℝ) := ⟨rsBall C.O w C.Xl η₀ b, isOpen_rsBall_lifted C hUbU⟩
  -- the inclusions between lifted control balls and `ρ`-balls
  have hUa_ρ : (Ua : Set (Fin (n + m) → ℝ)) ⊆ (rhoBallOpen C ν rin : Set (Fin (n + m) → ℝ)) := by
    intro ξ hξ
    have hξ' : ξ ∈ rsBall C.O w C.Xl η₀ a₁ := hξ
    have hξU : ξ ∈ C.U := hUaU hξ'
    refine ⟨hξU, ?_⟩
    obtain ⟨hl, -⟩ := hgc η₀ C.center_mem ξ hξU
    have h1 : ENNReal.ofReal (ν (C.Θ η₀ ξ) / Cν) < ENNReal.ofReal a₁ := lt_of_le_of_lt hl hξ'.2
    have h2 : ν (C.Θ η₀ ξ) / Cν < a₁ := (ENNReal.ofReal_lt_ofReal_iff ha0).1 h1
    calc ν (C.Θ η₀ ξ) < a₁ * Cν := (div_lt_iff₀ hCν0).1 h2
      _ = rin := by rw [ha₁]; field_simp
  have hWr_Ub : (rhoBallOpen C ν r : Set (Fin (n + m) → ℝ)) ⊆ (Ub : Set (Fin (n + m) → ℝ)) := by
    intro ξ hξ
    obtain ⟨hξU, hν⟩ := hξ
    refine ⟨C.closure_U_subset (subset_closure hξU), ?_⟩
    obtain ⟨-, hup⟩ := hgc η₀ C.center_mem ξ hξU
    refine lt_of_le_of_lt hup ((ENNReal.ofReal_lt_ofReal_iff hb0).2 ?_)
    rw [hb]
    nlinarith [mul_lt_mul_of_pos_left hν hCν0, mul_pos hCν0 hr0]
  -- the constant
  obtain ⟨Cst, hCst, hmain⟩ := hbound r hr0 hrR₁
  rw [← hrin] at hmain
  have hq0 : 0 < 1 / p.toReal :=
    one_div_pos.2 (ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hpt)
  have hMq0 : 0 < (cHi * C₁ / cLo) ^ (1 / p.toReal) :=
    Real.rpow_pos_of_pos (by positivity) _
  refine ⟨δ * a₁, b, Cst * (cHi * C₁ / cLo) ^ (1 / p.toReal), hδa0, hδa, hbε, mul_pos hCst hMq0,
    fun ρ' h0 h1 => hopen ρ' h0 (h1.trans hbρ), ?_⟩
  intro Vρ Vb hVρ hVb u f hu hop hf
  have hba : BallsAt C η₀ a₁ δ Va Vρ Ua := ⟨rfl, by rw [hVρ, hbase], rfl⟩
  have hbb : BallsAt C η₀ b δ Vb Vδb Ub := ⟨by rw [hVb, hbase], rfl, rfl⟩
  obtain ⟨-, hρa, hSa, hFBa⟩ := hF η₀ (mem_singleton _) a₁ ha0
    (lt_of_le_of_lt hab hbrF) Va Vρ Ua hba
  obtain ⟨-, hρb, hSb, hFBb⟩ := hF η₀ (mem_singleton _) b hb0 hbrF Vb Vδb Ub hbb
  have hVaVb : (Va : Set (Fin n → ℝ)) ⊆ (Vb : Set (Fin n → ℝ)) := by
    show rsBall Ω w X (basePoint η₀) a₁ ⊆ (Vb : Set (Fin n → ℝ))
    rw [hVb, hbase]
    exact rsBall_mono Ω w X x₀ hab
  have hVaΩ : (Va : Set (Fin n → ℝ)) ⊆ Ω := fun y hy =>
    (hy : y ∈ rsBall Ω w X (basePoint η₀) a₁).1
  have hVbΩ : (Vb : Set (Fin n → ℝ)) ⊆ Ω := by
    rw [hVb]
    exact fun y hy => hy.1
  have hX_a : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Va : Set (Fin n → ℝ)) :=
    fun i => (liftedChart_contDiffOn_base C i).mono hVaΩ
  have hX_b : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Vb : Set (Fin n → ℝ)) :=
    fun i => (liftedChart_contDiffOn_base C i).mono hVbΩ
  have hXt_a := liftedChart_hXt C Ua hUaU
  have hXt_b := liftedChart_hXt C Ub hUbU
  -- the lower transfer at the inner radius `a₁`
  have hu_a : memSobolevX w X Va (kk + 2) p u :=
    RothschildStein.S.memSobolevX_restrict w X Vb Va hVaVb hu
  have hlow := hSa.le_sobolevXENorm_lift w X C.P hXt_a hX_a (kk + 2) Vρ hFBa.subset hp
    (K := ENNReal.ofReal ((cLo * ballRatio Ua Va) ^ (1 / p.toReal)))
    (fun g hg => hFBa.le_eLpNorm_comp hp hpt hg) u hu_a.1.aestronglyMeasurable
    (fun I hI _ => by obtain ⟨g, hg, -⟩ := hu_a.2 I hI; exact ⟨g, hg⟩)
  -- the lift to the outer radius `b` and the lifted estimate
  have hut : memSobolevX w C.Xl Ub (kk + 2) p (fun ξ => u (basePoint ξ)) :=
    memSobolevX_lift hSb hFBb C.P hXt_b hX_b hp hpt hu
  have hfk : memSobolevX w C.Xl Ub kk p (fun ξ => f (basePoint ξ)) :=
    memSobolevX_lift hSb hFBb C.P hXt_b hX_b hp hpt hf
  have hft : HasWeakOperatorValue C.Xl Ub J (fun ξ => u (basePoint ξ)) (fun ξ => f (basePoint ξ)) :=
    hop.lift hSb C.P hXt_b hX_b
  have hut_r := RothschildStein.S.memSobolevX_restrict w C.Xl Ub (rhoBallOpen C ν r) hWr_Ub hut
  have hfk_r := RothschildStein.S.memSobolevX_restrict w C.Xl Ub (rhoBallOpen C ν r) hWr_Ub hfk
  have hrin_r : (rhoBallOpen C ν rin : Set (Fin (n + m) → ℝ)) ⊆
      (rhoBallOpen C ν r : Set (Fin (n + m) → ℝ)) :=
    rhoBall_mono C ν η₀ hrinr
  have hut_rin := RothschildStein.S.memSobolevX_restrict w C.Xl (rhoBallOpen C ν r)
    (rhoBallOpen C ν rin) hrin_r hut_r
  have hfr : HasWeakOperatorValue C.Xl (rhoBallOpen C ν r) J (fun ξ => u (basePoint ξ))
      (fun ξ => f (basePoint ξ)) := hft.mono hWr_Ub
  have hmono : sobolevXENorm w C.Xl Ua (kk + 2) p (fun ξ => u (basePoint ξ)) ≤
      sobolevXENorm w C.Xl (rhoBallOpen C ν rin) (kk + 2) p (fun ξ => u (basePoint ξ)) :=
    sobolevXENorm_mono_domain w C.Xl hUa_ρ hut_rin
  have hmain' := hmain _ _ hut_r hfr hfk_r
  -- the upper transfer for the data on the outer ball
  have hq0' : 0 < (cHi * ballRatio Ub Vb) ^ (1 / p.toReal) :=
    Real.rpow_pos_of_pos (mul_pos hcHi hρb) _
  have hbf := hSb.sobolevXENorm_lift_le w X C.P hXt_b hX_b kk
    (K := ENNReal.ofReal ((cHi * ballRatio Ub Vb) ^ (1 / p.toReal)))
    (ENNReal.ofReal_pos.2 hq0').ne' ENNReal.ofReal_ne_top
    (fun g hg => hFBb.eLpNorm_comp_le hp hpt hg) f
  have hbu := hFBb.eLpNorm_comp_le hp hpt hu.1.aestronglyMeasurable
  have hWf : sobolevXENorm w C.Xl (rhoBallOpen C ν r) kk p (fun ξ => f (basePoint ξ)) ≤
      sobolevXENorm w C.Xl Ub kk p (fun ξ => f (basePoint ξ)) :=
    sobolevXENorm_mono_domain w C.Xl hWr_Ub hfk
  have hWu : eLpNorm (fun ξ => u (basePoint ξ)) p
      (volume.restrict (rhoBallOpen C ν r : Set (Fin (n + m) → ℝ))) ≤
      eLpNorm (fun ξ => u (basePoint ξ)) p (volume.restrict (Ub : Set (Fin (n + m) → ℝ))) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono hWr_Ub le_rfl)
  -- the ratios of the fiber volumes
  have hrat := hscale η₀ (mem_singleton _) a₁ ha0 (by rw [hAa]; exact hbrS)
  rw [hAa] at hrat
  have hρbρa : ballRatio Ub Vb ≤ C₁ * ballRatio Ua Va := by
    rw [ballRatio_eq_ballRatioAt hba, ballRatio_eq_ballRatioAt hbb]
    exact hrat
  have hκ0 : 0 < (cLo * ballRatio Ua Va) ^ (1 / p.toReal) :=
    Real.rpow_pos_of_pos (mul_pos hcLo hρa) _
  have hcLone : cLo ≠ 0 := hcLo.ne'
  have hcb : (cHi * ballRatio Ub Vb) ^ (1 / p.toReal) ≤
      (cHi * C₁ / cLo) ^ (1 / p.toReal) * (cLo * ballRatio Ua Va) ^ (1 / p.toReal) := by
    calc (cHi * ballRatio Ub Vb) ^ (1 / p.toReal)
        ≤ (cHi * (C₁ * ballRatio Ua Va)) ^ (1 / p.toReal) :=
          Real.rpow_le_rpow (mul_nonneg hcHi.le hρb.le)
            (mul_le_mul_of_nonneg_left hρbρa hcHi.le) hq0.le
      _ = ((cHi * C₁ / cLo) * (cLo * ballRatio Ua Va)) ^ (1 / p.toReal) := by
          congr 1
          field_simp
      _ = _ := Real.mul_rpow (by positivity) (mul_nonneg hcLo.le hρa.le)
  set κ : ℝ := (cLo * ballRatio Ua Va) ^ (1 / p.toReal) with hκ
  set Mq : ℝ := (cHi * C₁ / cLo) ^ (1 / p.toReal) with hMq
  set N : ℝ≥0∞ := sobolevXENorm w X Vb kk p f +
    eLpNorm u p (volume.restrict (Vb : Set (Fin n → ℝ))) with hN
  have hchain : ENNReal.ofReal κ * sobolevXENorm w X Vρ (kk + 2) p u ≤
      ENNReal.ofReal κ * (ENNReal.ofReal (Cst * Mq) * N) := by
    calc ENNReal.ofReal κ * sobolevXENorm w X Vρ (kk + 2) p u
        ≤ sobolevXENorm w C.Xl Ua (kk + 2) p (fun ξ => u (basePoint ξ)) := hlow
      _ ≤ sobolevXENorm w C.Xl (rhoBallOpen C ν rin) (kk + 2) p (fun ξ => u (basePoint ξ)) := hmono
      _ ≤ ENNReal.ofReal Cst *
          (sobolevXENorm w C.Xl (rhoBallOpen C ν r) kk p (fun ξ => f (basePoint ξ)) +
            eLpNorm (fun ξ => u (basePoint ξ)) p
              (volume.restrict (rhoBallOpen C ν r : Set (Fin (n + m) → ℝ)))) := hmain'
      _ ≤ ENNReal.ofReal Cst *
          (ENNReal.ofReal ((cHi * ballRatio Ub Vb) ^ (1 / p.toReal)) * N) := by
          rw [hN, mul_add (ENNReal.ofReal ((cHi * ballRatio Ub Vb) ^ (1 / p.toReal)))]
          gcongr
          · exact hWf.trans hbf
          · exact hWu.trans hbu
      _ ≤ ENNReal.ofReal Cst * (ENNReal.ofReal (Mq * κ) * N) :=
          mul_le_mul' le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal hcb) le_rfl)
      _ = ENNReal.ofReal κ * (ENNReal.ofReal (Cst * Mq) * N) := by
          rw [ENNReal.ofReal_mul hMq0.le, ENNReal.ofReal_mul hCst.le]
          ring
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 hκ0).ne' ENNReal.ofReal_ne_top).1 hchain

end Transfer

end RothschildStein.P2
