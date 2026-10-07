-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HigherSobolevTransfer
public import RothschildStein.P2.SmoothingNoDriftGlue
public import RothschildStein.P2.SmoothingSobolev

/-!
# From the lifted regularity to the original domain (local step)

Part of the higher Sobolev estimate (BB p. 591: "Transfer and cover as above"; the descent of regularity as in the distributional smoothing theorem, BB p. 609). If the lifted
regularity `LiftedHigherRegularity` holds on a chart `C`
(`u ∈ W^{2,p}(U_R)`, `L̃ u = f ∈ W^{kk,p}(U_R)` imply `u ∈ W^{kk+2,p}(U_{R/2^{kk}})`), then for `u ∈ W^{2,p}_X(W)`,
`L u = f ∈ W^{kk,p}_X(W)` on a neighborhood `W` of the chart base point, `u ∈ W^{kk+2,p}_X(A)` on a neighborhood
`A ⊆ W` of the base point (`higher_local_regularity`): lift `ũ = u ∘ π` to a lifted control ball
(`memSobolevX_lift`, the lifted Sobolev norm transfer), apply the lifted regularity, restrict to a cylinder `A × B` around the lift of the
base point and descend (`memSobolevX_descent`, as in the distributional smoothing theorem).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators Distributions
namespace RothschildStein.P2

open RothschildStein.P1 RothschildStein

section LocalRegularity

variable {n k : ℕ} {w : Fin k → ℕ+} {st : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}

/-- The lifted regularity on a chart (the conclusion of `liftedRegularity`):
for `0 < R < R₀`, `u ∈ W^{2,p}(U_R)` with `L̃ u = f ∈ W^{kk,p}(U_R)` lies in `W^{kk+2,p}(U_{R/2^{kk}})`. -/
def LiftedHigherRegularity {ι : Type} [Fintype ι] (C : LiftedChart w st Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) (J : ι → List (Fin k)) (p : ℝ≥0∞) (kk : ℕ) : Prop :=
  ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ → ∀ u f : (Fin (n + m) → ℝ) → ℝ,
    memSobolevX w C.Xl (rhoBallOpen C ν R) 2 p u →
    HasWeakOperatorValue C.Xl (rhoBallOpen C ν R) J u f →
    memSobolevX w C.Xl (rhoBallOpen C ν R) kk p f →
    memSobolevX w C.Xl (rhoBallOpen C ν (R / 2 ^ kk)) (kk + 2) p u

/-- **Local regularity on the original domain** (BB p. 591; descent as in the distributional smoothing theorem
descent): from `LiftedHigherRegularity` at a chart centred at `x₀`, every `u ∈ W^{2,p}_X(W)` with
`L u = f ∈ W^{kk,p}_X(W)` (`W ∋ x₀` open, `W ⊆ Ω`) lies in `W^{kk+2,p}_X(A)` on an open `A ∋ x₀`, `A ⊆ W`. -/
theorem higher_local_regularity {ι : Type} [Fintype ι] (C : LiftedChart w st Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) (J : ι → List (Fin k)) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    {kk : ℕ} (hreg : LiftedHigherRegularity C ν J p kk) {W : Opens (Fin n → ℝ)}
    (hx₀ : x₀ ∈ (W : Set (Fin n → ℝ))) (hWΩ : (W : Set (Fin n → ℝ)) ⊆ Ω)
    {u f : (Fin n → ℝ) → ℝ} (hu : memSobolevX w X W 2 p u) (hop : HasWeakOperatorValue X W J u f)
    (hf : memSobolevX w X W kk p f) :
    ∃ A : Opens (Fin n → ℝ), x₀ ∈ (A : Set (Fin n → ℝ)) ∧ (A : Set (Fin n → ℝ)) ⊆ (W : Set (Fin n → ℝ)) ∧
      memSobolevX w X A (kk + 2) p u := by
  classical
  set η₀ : Fin (n + m) → ℝ := joinPoint x₀ (0 : Fin m → ℝ) with hη₀
  have hK : IsCompact ({η₀} : Set (Fin (n + m) → ℝ)) := isCompact_singleton
  have hKU : ({η₀} : Set (Fin (n + m) → ℝ)) ⊆ C.U := singleton_subset_iff.mpr C.center_mem
  have hbase : basePoint η₀ = x₀ := basePoint_joinPoint x₀ 0
  obtain ⟨R₀, hR₀, hbound⟩ := hreg
  obtain ⟨ε, hε, hεW⟩ := exists_rsBall_subset (w := w) hΩ
    (fun i => (liftedChart_contDiffOn_base C i).continuousOn) W.isOpen hx₀ (hWΩ hx₀)
  obtain ⟨Cν, hCν1, hgc⟩ := exists_gauge_comparison C ν
  obtain ⟨ρ₀, hρ₀, hopen⟩ := exists_isOpen_base_ball C
  obtain ⟨rF, δ, cLo, cHi, hrF, hδ0, hδ1, hcLo, hcHi, hF⟩ := exists_fiberBounds' C hK hKU
  have hCν0 : 0 < Cν := lt_of_lt_of_le one_pos hCν1
  obtain ⟨rB, cv, Cv, δB, cf, Cf, hrB, -, -, -, -, -, -, hall⟩ := C.ball_bounds {η₀} hK hKU
  set Rr : ℝ := min (min rF rB) (min ρ₀ ε) with hRr
  have hRr0 : 0 < Rr := lt_min (lt_min hrF hrB) (lt_min hρ₀ hε)
  have hRF : Rr ≤ rF := (min_le_left _ _).trans (min_le_left _ _)
  have hRB : Rr ≤ rB := (min_le_left _ _).trans (min_le_right _ _)
  have hRρ : Rr ≤ ρ₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hRε : Rr ≤ ε := (min_le_right _ _).trans (min_le_right _ _)
  set R : ℝ := min (R₀ / 2) (Rr / (4 * Cν)) with hR
  have hR0 : 0 < R := lt_min (half_pos hR₀) (by positivity)
  have hRR₀ : R < R₀ := (min_le_left _ _).trans_lt (half_lt_self hR₀)
  have hRle : R ≤ Rr / (4 * Cν) := min_le_right _ _
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 2 * Cν * R := ⟨_, rfl⟩
  have hb0 : 0 < b := by rw [hb]; positivity
  have hbR : b ≤ Rr / 2 := by
    rw [hb]
    have : 2 * Cν * R ≤ 2 * Cν * (Rr / (4 * Cν)) := mul_le_mul_of_nonneg_left hRle (by positivity)
    calc 2 * Cν * R ≤ 2 * Cν * (Rr / (4 * Cν)) := this
      _ = Rr / 2 := by field_simp; ring
  have hbR' : b < Rr := by linarith
  have hbrF : b < rF := lt_of_lt_of_le hbR' hRF
  have hbrB : b < rB := lt_of_lt_of_le hbR' hRB
  have hbρ : b ≤ ρ₀ := (hbR'.trans_le hRρ).le
  have hbε : b ≤ ε := (hbR'.trans_le hRε).le
  have hδb0 : 0 < δ * b := mul_pos hδ0 hb0
  have hδb : δ * b ≤ b := by
    have := mul_le_mul_of_nonneg_right hδ1.le hb0.le
    linarith
  have hUbU : rsBall C.O w C.Xl η₀ b ⊆ C.U := by
    obtain ⟨h, -⟩ := hall η₀ (mem_singleton _) b hb0 hbrB
    exact h
  let Vb : Opens (Fin n → ℝ) :=
    ⟨rsBall Ω w X (basePoint η₀) b, by rw [hbase]; exact hopen b hb0 hbρ⟩
  let Vδb : Opens (Fin n → ℝ) :=
    ⟨rsBall Ω w X (basePoint η₀) (δ * b), by rw [hbase]; exact hopen _ hδb0 (hδb.trans hbρ)⟩
  let Ub : Opens (Fin (n + m) → ℝ) := ⟨rsBall C.O w C.Xl η₀ b, isOpen_rsBall_lifted C hUbU⟩
  have hWr_Ub : (rhoBallOpen C ν R : Set (Fin (n + m) → ℝ)) ⊆ (Ub : Set (Fin (n + m) → ℝ)) := by
    intro ξ hξ
    obtain ⟨hξU, hν⟩ := hξ
    refine ⟨C.closure_U_subset (subset_closure hξU), ?_⟩
    obtain ⟨-, hup⟩ := hgc η₀ C.center_mem ξ hξU
    refine lt_of_le_of_lt hup ((ENNReal.ofReal_lt_ofReal_iff hb0).2 ?_)
    rw [hb]
    nlinarith [mul_lt_mul_of_pos_left hν hCν0, mul_pos hCν0 hR0]
  have hbb : BallsAt C η₀ b δ Vb Vδb Ub := ⟨rfl, rfl, rfl⟩
  obtain ⟨-, hρb, hSb, hFBb⟩ := hF η₀ (mem_singleton _) b hb0 hbrF Vb Vδb Ub hbb
  have hVbε : (Vb : Set (Fin n → ℝ)) ⊆ rsBall Ω w X x₀ ε := by
    show rsBall Ω w X (basePoint η₀) b ⊆ rsBall Ω w X x₀ ε
    rw [hbase]
    exact rsBall_mono Ω w X x₀ (hbε)
  have hVbW : (Vb : Set (Fin n → ℝ)) ⊆ (W : Set (Fin n → ℝ)) := hVbε.trans hεW
  have hVbΩ : (Vb : Set (Fin n → ℝ)) ⊆ Ω := hVbW.trans hWΩ
  have hX_b : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Vb : Set (Fin n → ℝ)) :=
    fun i => (liftedChart_contDiffOn_base C i).mono hVbΩ
  have hXt_b := liftedChart_hXt C Ub hUbU
  -- lift to the outer ball and restrict to the `ρ`-ball
  have hu_b : memSobolevX w X Vb 2 p u := RothschildStein.S.memSobolevX_restrict w X W Vb hVbW hu
  have hf_b : memSobolevX w X Vb kk p f := RothschildStein.S.memSobolevX_restrict w X W Vb hVbW hf
  have hop_b : HasWeakOperatorValue X Vb J u f := HasWeakOperatorValue.mono hVbW hop
  have hut : memSobolevX w C.Xl Ub 2 p (fun ξ => u (basePoint ξ)) :=
    memSobolevX_lift hSb hFBb C.P hXt_b hX_b hp hpt hu_b
  have hfk : memSobolevX w C.Xl Ub kk p (fun ξ => f (basePoint ξ)) :=
    memSobolevX_lift hSb hFBb C.P hXt_b hX_b hp hpt hf_b
  have hft : HasWeakOperatorValue C.Xl Ub J (fun ξ => u (basePoint ξ)) (fun ξ => f (basePoint ξ)) :=
    hop_b.lift hSb C.P hXt_b hX_b
  have hut_r := RothschildStein.S.memSobolevX_restrict w C.Xl Ub (rhoBallOpen C ν R) hWr_Ub hut
  have hfk_r := RothschildStein.S.memSobolevX_restrict w C.Xl Ub (rhoBallOpen C ν R) hWr_Ub hfk
  have hfr : HasWeakOperatorValue C.Xl (rhoBallOpen C ν R) J (fun ξ => u (basePoint ξ))
      (fun ξ => f (basePoint ξ)) := HasWeakOperatorValue.mono hWr_Ub hft
  have hreg' := hbound R hR0 hRR₀ _ _ hut_r hfr hfk_r
  -- the cylinder inside `U_{R/2^kk}` and the descent
  have hle : R / 2 ^ kk ≤ R := div_le_self hR0.le (one_le_pow₀ (by norm_num))
  have hν0 : ν 0 = 0 := (ν.gauge.2.2.1 0).2 rfl
  have hξUR : joinPoint x₀ (0 : Fin m → ℝ) ∈ (rhoBallOpen C ν (R / 2 ^ kk) : Set (Fin (n + m) → ℝ)) := by
    refine ⟨C.center_mem, ?_⟩
    have h0 : C.Θ η₀ η₀ = 0 := (C.chart η₀ C.center_mem).2.2.2.2
    show ν (C.Θ η₀ η₀) < R / 2 ^ kk
    rw [h0, hν0]
    positivity
  have hURU : (rhoBallOpen C ν (R / 2 ^ kk) : Set (Fin (n + m) → ℝ)) ⊆ C.U := fun ξ hξ => hξ.1
  obtain ⟨A, B, hxA, h0B, hcpt, hcl, hBfin, hBpos⟩ := exists_cylinder_closure_subset hξUR
  obtain ⟨η, hη⟩ := exists_test_integral_eq_one B h0B
  have hsubUR : (cylinder A B : Set (Fin (n + m) → ℝ)) ⊆
      (rhoBallOpen C ν (R / 2 ^ kk) : Set (Fin (n + m) → ℝ)) := subset_closure.trans hcl
  have hsubU : (cylinder A B : Set (Fin (n + m) → ℝ)) ⊆ C.U := hsubUR.trans hURU
  have hsubUb : (cylinder A B : Set (Fin (n + m) → ℝ)) ⊆ (Ub : Set (Fin (n + m) → ℝ)) :=
    hsubUR.trans ((rhoBall_mono C ν η₀ hle).trans hWr_Ub)
  have hAcyl : ∀ x ∈ (A : Set (Fin n → ℝ)),
      joinPoint x (0 : Fin m → ℝ) ∈ (cylinder A B : Set (Fin (n + m) → ℝ)) := fun x hx =>
    joinPoint_mem_cylinder.2 ⟨hx, h0B⟩
  have hAVb : (A : Set (Fin n → ℝ)) ⊆ (Vb : Set (Fin n → ℝ)) := by
    intro x hx
    have h2 := hSb.proj _ (hsubUb (hAcyl x hx))
    rwa [basePoint_joinPoint] at h2
  have hAΩ : A ≤ liftedChartBaseOpens C := by
    intro x hx
    have := liftedChart_basePoint_mem C (hsubU (hAcyl x hx))
    rwa [basePoint_joinPoint] at this
  have hAW : (A : Set (Fin n → ℝ)) ⊆ (W : Set (Fin n → ℝ)) := hAVb.trans hVbW
  let S := liftedChart_cylinderFiberSetting C A B hsubU hBfin
  have hS : memSobolevX w C.Xl (cylinder A B) (kk + 2) p (fun ξ => u (basePoint ξ)) :=
    RothschildStein.S.memSobolevX_restrict w C.Xl _ _ hsubUR hreg'
  have hu_loc : LocallyIntegrableOn u (A : Set (Fin n → ℝ)) volume :=
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hu.1.locallyIntegrable hp)).mono_set hAW
  have hT : ∀ ψ : TestFunction (cylinder A B) ℝ (⊤ : ℕ∞),
      Distribution.ofFun A u volume (⊤ : ℕ∞) (S.test ψ) =
        Distribution.ofFun (cylinder A B) (fun ξ => u (basePoint ξ)) volume (⊤ : ℕ∞) ψ :=
    fun ψ => S.ofFun_test hu_loc ψ
  obtain ⟨hrep, -, hmem⟩ := memSobolevX_descent w X C.P
    (fun i => (liftedChart_contDiffOn_lift C i).mono hsubU)
    (fun i => (liftedChart_contDiffOn_base C i).mono hAΩ) S hη
    (Distribution.ofFun A u volume (⊤ : ℕ∞)) hT hp hpt hBpos hBfin hS
  have hae : u =ᵐ[volume.restrict (A : Set (Fin n → ℝ))]
      fiberAvg (fun ξ => u (basePoint ξ)) η :=
    Distribution.ofFun_injective hu_loc hrep.1 hrep.2
  exact ⟨A, hxA, hAW, (RothschildStein.S.memSobolevX_congr_ae X A w (kk + 2) p hae).2 hmem⟩

end LocalRegularity

end RothschildStein.P2
