-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.TransferCoverCore

/-!
# Sobolev transfer and finite cover: from the lifted base Sobolev estimate to the original domain

The base Sobolev estimate (BB pp. 585–587, Thms 11.42-11.43, (11.69)-(11.72)). `LiftedBaseSobolevEstimate` is the
exact statement of the lifted base Sobolev estimate on a lifted chart: there is `r₀ > 0` such that for
`0 < r ≤ r₀` and every `u ∈ W^{2,p}_{X̃}(U^ρ_r)`
`‖u‖_{W^{2,p}(U^ρ_{r/2})} ≤ C(r) (‖L̃ u‖_{L^p(U^ρ_r)} + ‖u‖_{L^p(U^ρ_r)})`, with the `memSobolevX` and `sobolevXENorm` for the lifted fields `C.Xl`, the operator `L̃ = ∑ X̃_{J i}`
(drift allowed) being given by weak word derivatives (`HasWeakOperatorValue`).

`sobolev_transfer_cover_of_lifted` is the base Sobolev estimate on the original domain (BB p. 587, Thm 11.43): for
`Ω' ⋐ Ω'' ⋐ Ω` and `u ∈ W^{2,p}_X(Ω'')`,
`‖u‖_{W^{2,p}_X(Ω')} ≤ C(X, Ω', Ω'', p) (‖Lu‖_{L^p(Ω'')} + ‖u‖_{L^p(Ω'')})`.
It is proved from the lifted estimate at a lifted chart at every point of `closure Ω'` by

1. the lifted norm transfer (`exists_fiberBounds'`, the weak word lift) at the radii
   `a = r / (2 C_ρ)` (inner) and `b = 2 C_ρ r` (outer), where `C_ρ` is the comparison constant of
   the comparison between `ν ∘ Θ` and `d̃`, so that `B̃(ξ₀, a) ⊆ U^ρ_{r/2}` and `U^ρ_r ⊆ B̃(ξ₀, b)`;
2. the comparison `H(ξ₀, b) ≤ C₁ H(ξ₀, a)` of the fiber ratios `|U_ρ| / |V_ρ|` at the radii `a`
   and `b` (from lifted volume growth and monotonicity of `|V_ρ|`), which cancels the
   radius ratio of the lifted norm transfer (BB (11.68)) between the two sides;
3. a finite cover of the compact set `closure Ω'` by the inner base balls `V_{δ a}(x)` and the
   finite-cover inequality for the Sobolev norm.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators
open RothschildStein.P1
namespace RothschildStein.P2
variable {n k : ℕ} {w : Fin k → ℕ+} {st : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}

/-- The lifted base Sobolev estimate (BB pp. 585-587, (11.69)-(11.72)): on the lifted chart
`C` with the smooth homogeneous norm `ν` there is `r₀ > 0` such that for every `0 < r ≤ r₀` there is
a constant `C(r)` with
`‖u‖_{W^{2,p}_{X̃}(U^ρ_{r/2})} ≤ C(r) (‖L̃ u‖_{L^p(U^ρ_r)} + ‖u‖_{L^p(U^ρ_r)})`
for every `u ∈ W^{2,p}_{X̃}(U^ρ_r)` and every value `f = L̃ u` of the operator `L̃ = ∑ X̃_{J i}`
(`J = driftOpWords q` for the drift operator, `J = noDriftOpWords q` without drift). -/
def LiftedBaseSobolevEstimate {ι : Type} [Fintype ι] (C : LiftedChart w st Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) (J : ι → List (Fin k)) (p : ℝ≥0∞) : Prop :=
  ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → ∃ Cst : ℝ, 0 < Cst ∧
    ∀ u f : (Fin (n + m) → ℝ) → ℝ,
      memSobolevX w C.Xl (rhoBallOpen C ν r) 2 p u →
      HasWeakOperatorValue C.Xl (rhoBallOpen C ν r) J u f →
      sobolevXENorm w C.Xl (rhoBallOpen C ν (r / 2)) 2 p u ≤
        ENNReal.ofReal Cst *
          (eLpNorm f p (volume.restrict (rhoBallOpen C ν r : Set (Fin (n + m) → ℝ))) +
            eLpNorm u p (volume.restrict (rhoBallOpen C ν r : Set (Fin (n + m) → ℝ))))

/-- The Sobolev norm is monotone in the domain, given the weak derivatives on the larger
domain. -/
theorem sobolevXENorm_mono_domain {n' k' : ℕ} (w' : Fin k' → ℕ+)
    (X' : Fin k' → (Fin n' → ℝ) → (Fin n' → ℝ)) {V V' : Opens (Fin n' → ℝ)}
    (hV : (V' : Set (Fin n' → ℝ)) ⊆ (V : Set (Fin n' → ℝ))) {j : ℕ} {p : ℝ≥0∞}
    {u : (Fin n' → ℝ) → ℝ} (hu : memSobolevX w' X' V j p u) :
    sobolevXENorm w' X' V' j p u ≤ sobolevXENorm w' X' V j p u := by
  unfold sobolevXENorm
  refine Finset.sum_le_sum fun I hI => ?_
  obtain ⟨g, hg, -⟩ := hu.2 I hI
  exact RothschildStein.H3.weakWordENorm_mono_domain X' V V' hV I p u g hg

/-- At a lifted chart `C` whose lifted estimate holds,
the original estimate holds on a small base ball around `x₀` with the larger ball `V_b ⊆ V_ε`
on the right: for every `ε > 0` there are `0 < ρ ≤ b ≤ ε` and `K > 0` with
`‖u‖_{W^{2,p}(V_ρ)} ≤ K (‖Lu‖_{L^p(V_b)} + ‖u‖_{L^p(V_b)})`
for `u ∈ W^{2,p}_X(V_b)` (`V_ρ = B(x₀, ρ)`, `V_b = B(x₀, b)`), and the control balls
`B(x₀, ρ')`, `ρ' ≤ b`, are Euclidean open. Here `ρ = δ a`, `b = 2 C_ρ r` with `a = r / (2 C_ρ)`. -/
theorem sobolev_local_transfer {ι : Type} [Fintype ι] (C : LiftedChart w st Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) (J : ι → List (Fin k)) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (hest : LiftedBaseSobolevEstimate C ν J p) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ b K : ℝ, 0 < ρ ∧ ρ ≤ b ∧ b ≤ ε ∧ 0 < K ∧
      (∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ b → IsOpen (rsBall Ω w X x₀ ρ')) ∧
      ∀ (Vρ Vb : Opens (Fin n → ℝ)), (Vρ : Set (Fin n → ℝ)) = rsBall Ω w X x₀ ρ →
        (Vb : Set (Fin n → ℝ)) = rsBall Ω w X x₀ b → ∀ u f : (Fin n → ℝ) → ℝ,
        memSobolevX w X Vb 2 p u → HasWeakOperatorValue X Vb J u f →
        sobolevXENorm w X Vρ 2 p u ≤ ENNReal.ofReal K *
          (eLpNorm f p (volume.restrict (Vb : Set (Fin n → ℝ))) +
            eLpNorm u p (volume.restrict (Vb : Set (Fin n → ℝ)))) := by
  classical
  set η₀ : Fin (n + m) → ℝ := joinPoint x₀ (0 : Fin m → ℝ) with hη₀
  have hK : IsCompact ({η₀} : Set (Fin (n + m) → ℝ)) := isCompact_singleton
  have hKU : ({η₀} : Set (Fin (n + m) → ℝ)) ⊆ C.U := singleton_subset_iff.mpr C.center_mem
  have hbase : basePoint η₀ = x₀ := basePoint_joinPoint x₀ 0
  obtain ⟨r₀, hr₀, hbound⟩ := hest
  obtain ⟨Cν, hCν1, hgc⟩ := exists_gauge_comparison C ν
  obtain ⟨ρ₀, hρ₀, hopen⟩ := exists_isOpen_base_ball C
  obtain ⟨rF, δ, cLo, cHi, hrF, hδ0, hδ1, hcLo, hcHi, hF⟩ := exists_fiberBounds' C hK hKU
  have hCν0 : 0 < Cν := lt_of_lt_of_le one_pos hCν1
  have hA : (1 : ℝ) ≤ 4 * Cν ^ 2 := by nlinarith
  obtain ⟨rS, C₁, hrS, hC₁, hscale⟩ := ballRatioAt_scale_le C hK hKU hA
  obtain ⟨rB, cv, Cv, δB, cf, Cf, hrB, -, -, -, -, -, -, hall⟩ := C.ball_bounds {η₀} hK hKU
  -- the radii
  set R : ℝ := min (min (min rF rB) (min rS ρ₀)) ε with hR
  have hR0 : 0 < R := lt_min (lt_min (lt_min hrF hrB) (lt_min hrS hρ₀)) hε
  have hRF : R ≤ rF := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hRB : R ≤ rB := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hRS : R ≤ rS := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRρ : R ≤ ρ₀ := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hRε : R ≤ ε := min_le_right _ _
  set r : ℝ := min r₀ (R / (4 * Cν)) with hr
  have hr0 : 0 < r := lt_min hr₀ (by positivity)
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrR : r ≤ R / (4 * Cν) := min_le_right _ _
  set a : ℝ := r / (2 * Cν) with ha
  set b : ℝ := 2 * Cν * r with hb
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have har : a ≤ r / 2 := by
    rw [ha]
    exact div_le_div_of_nonneg_left hr0.le (by norm_num) (by linarith)
  have hab : a < b := by nlinarith
  have hbR : b ≤ R / 2 := by
    rw [hb]
    have : 2 * Cν * r ≤ 2 * Cν * (R / (4 * Cν)) := mul_le_mul_of_nonneg_left hrR (by positivity)
    calc 2 * Cν * r ≤ 2 * Cν * (R / (4 * Cν)) := this
      _ = R / 2 := by field_simp; ring
  have hbR' : b < R := by linarith
  have hbrF : b < rF := lt_of_lt_of_le hbR' hRF
  have hbrB : b < rB := lt_of_lt_of_le hbR' hRB
  have hbrS : b < rS := lt_of_lt_of_le hbR' hRS
  have hbρ : b ≤ ρ₀ := (hbR'.trans_le hRρ).le
  have hbε : b ≤ ε := (hbR'.trans_le hRε).le
  have hAa : 4 * Cν ^ 2 * a = b := by rw [ha, hb]; field_simp; ring
  have hδa : δ * a ≤ b := by nlinarith
  have hδa0 : 0 < δ * a := mul_pos hδ0 ha0
  have hδb0 : 0 < δ * b := mul_pos hδ0 hb0
  have hδb : δ * b ≤ b := by nlinarith
  -- the open sets
  have hUaU : rsBall C.O w C.Xl η₀ a ⊆ C.U := by
    obtain ⟨h, -⟩ := hall η₀ (mem_singleton _) a ha0 (lt_of_lt_of_le hab hbrB.le)
    exact h
  have hUbU : rsBall C.O w C.Xl η₀ b ⊆ C.U := by
    obtain ⟨h, -⟩ := hall η₀ (mem_singleton _) b hb0 hbrB
    exact h
  let Va : Opens (Fin n → ℝ) :=
    ⟨rsBall Ω w X (basePoint η₀) a, by rw [hbase]; exact hopen a ha0 (hab.le.trans hbρ)⟩
  let Vδb : Opens (Fin n → ℝ) :=
    ⟨rsBall Ω w X (basePoint η₀) (δ * b), by rw [hbase]; exact hopen _ hδb0 (hδb.trans hbρ)⟩
  let Ua : Opens (Fin (n + m) → ℝ) := ⟨rsBall C.O w C.Xl η₀ a, isOpen_rsBall_lifted C hUaU⟩
  let Ub : Opens (Fin (n + m) → ℝ) := ⟨rsBall C.O w C.Xl η₀ b, isOpen_rsBall_lifted C hUbU⟩
  -- the inclusions between lifted control balls and `ρ`-balls
  have hUa_ρ : (Ua : Set (Fin (n + m) → ℝ)) ⊆ (rhoBallOpen C ν (r / 2) : Set (Fin (n + m) → ℝ)) := by
    intro ξ hξ
    have hξ' : ξ ∈ rsBall C.O w C.Xl η₀ a := hξ
    have hξU : ξ ∈ C.U := hUaU hξ'
    refine ⟨hξU, ?_⟩
    obtain ⟨hl, -⟩ := hgc η₀ C.center_mem ξ hξU
    have h1 : ENNReal.ofReal (ν (C.Θ η₀ ξ) / Cν) < ENNReal.ofReal a := lt_of_le_of_lt hl hξ'.2
    have h2 : ν (C.Θ η₀ ξ) / Cν < a := (ENNReal.ofReal_lt_ofReal_iff ha0).1 h1
    calc ν (C.Θ η₀ ξ) < a * Cν := (div_lt_iff₀ hCν0).1 h2
      _ = r / 2 := by rw [ha]; field_simp
  have hWr_Ub : (rhoBallOpen C ν r : Set (Fin (n + m) → ℝ)) ⊆ (Ub : Set (Fin (n + m) → ℝ)) := by
    intro ξ hξ
    obtain ⟨hξU, hν⟩ := hξ
    refine ⟨C.closure_U_subset (subset_closure hξU), ?_⟩
    obtain ⟨-, hup⟩ := hgc η₀ C.center_mem ξ hξU
    refine lt_of_le_of_lt hup ((ENNReal.ofReal_lt_ofReal_iff hb0).2 ?_)
    nlinarith [mul_pos hCν0 hr0]
  -- the constant
  obtain ⟨Cst, hCst, hmain⟩ := hbound r hr0 hrr₀
  have hq0 : 0 < 1 / p.toReal :=
    one_div_pos.2 (ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hpt)
  have hMq0 : 0 < (cHi * C₁ / cLo) ^ (1 / p.toReal) :=
    Real.rpow_pos_of_pos (by positivity) _
  refine ⟨δ * a, b, Cst * (cHi * C₁ / cLo) ^ (1 / p.toReal), hδa0, hδa, hbε, mul_pos hCst hMq0,
    fun ρ' h0 h1 => hopen ρ' h0 (h1.trans hbρ), ?_⟩
  intro Vρ Vb hVρ hVb u f hu hf
  have hba : BallsAt C η₀ a δ Va Vρ Ua := ⟨rfl, by rw [hVρ, hbase], rfl⟩
  have hbb : BallsAt C η₀ b δ Vb Vδb Ub := ⟨by rw [hVb, hbase], rfl, rfl⟩
  obtain ⟨-, hρa, hSa, hFBa⟩ := hF η₀ (mem_singleton _) a ha0
    (lt_of_lt_of_le hab hbrF.le) Va Vρ Ua hba
  obtain ⟨-, hρb, hSb, hFBb⟩ := hF η₀ (mem_singleton _) b hb0 hbrF Vb Vδb Ub hbb
  have hVaVb : (Va : Set (Fin n → ℝ)) ⊆ (Vb : Set (Fin n → ℝ)) := by
    show rsBall Ω w X (basePoint η₀) a ⊆ (Vb : Set (Fin n → ℝ))
    rw [hVb, hbase]
    exact rsBall_mono Ω w X x₀ hab.le
  have hVaΩ : (Va : Set (Fin n → ℝ)) ⊆ Ω := fun y hy =>
    (hy : y ∈ rsBall Ω w X (basePoint η₀) a).1
  have hVbΩ : (Vb : Set (Fin n → ℝ)) ⊆ Ω := by
    rw [hVb]
    exact fun y hy => hy.1
  have hX_a : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Va : Set (Fin n → ℝ)) :=
    fun i => (liftedChart_contDiffOn_base C i).mono hVaΩ
  have hX_b : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Vb : Set (Fin n → ℝ)) :=
    fun i => (liftedChart_contDiffOn_base C i).mono hVbΩ
  have hXt_a := liftedChart_hXt C Ua hUaU
  have hXt_b := liftedChart_hXt C Ub hUbU
  -- the lower transfer at the inner radius `a`
  have hu_a : memSobolevX w X Va 2 p u := RothschildStein.S.memSobolevX_restrict w X Vb Va hVaVb hu
  have hlow := hSa.le_sobolevXENorm_lift w X C.P hXt_a hX_a 2 Vρ hFBa.subset hp
    (K := ENNReal.ofReal ((cLo * ballRatio Ua Va) ^ (1 / p.toReal)))
    (fun g hg => hFBa.le_eLpNorm_comp hp hpt hg) u hu_a.1.aestronglyMeasurable
    (fun I hI _ => by obtain ⟨g, hg, -⟩ := hu_a.2 I hI; exact ⟨g, hg⟩)
  -- the lift to the outer radius `b` and the lifted estimate
  have hut : memSobolevX w C.Xl Ub 2 p (fun ξ => u (basePoint ξ)) :=
    memSobolevX_lift hSb hFBb C.P hXt_b hX_b hp hpt hu
  have hft : HasWeakOperatorValue C.Xl Ub J (fun ξ => u (basePoint ξ)) (fun ξ => f (basePoint ξ)) :=
    hf.lift hSb C.P hXt_b hX_b
  have hWr2_Wr : (rhoBallOpen C ν (r / 2) : Set (Fin (n + m) → ℝ)) ⊆
      (rhoBallOpen C ν r : Set (Fin (n + m) → ℝ)) :=
    rhoBall_mono C ν η₀ (by linarith)
  have hut_r := RothschildStein.S.memSobolevX_restrict w C.Xl Ub (rhoBallOpen C ν r) hWr_Ub hut
  have hut_r2 := RothschildStein.S.memSobolevX_restrict w C.Xl (rhoBallOpen C ν r)
    (rhoBallOpen C ν (r / 2)) hWr2_Wr hut_r
  have hfr : HasWeakOperatorValue C.Xl (rhoBallOpen C ν r) J (fun ξ => u (basePoint ξ))
      (fun ξ => f (basePoint ξ)) := hft.mono hWr_Ub
  have hmono : sobolevXENorm w C.Xl Ua 2 p (fun ξ => u (basePoint ξ)) ≤
      sobolevXENorm w C.Xl (rhoBallOpen C ν (r / 2)) 2 p (fun ξ => u (basePoint ξ)) :=
    sobolevXENorm_mono_domain w C.Xl hUa_ρ hut_r2
  have hmain' := hmain _ _ hut_r hfr
  -- `L^p` bounds on the outer ball
  have hbf := hFBb.eLpNorm_comp_le hp hpt hf.aestronglyMeasurable
  have hbu := hFBb.eLpNorm_comp_le hp hpt hu.1.aestronglyMeasurable
  have hWf : eLpNorm (fun ξ => f (basePoint ξ)) p
      (volume.restrict (rhoBallOpen C ν r : Set (Fin (n + m) → ℝ))) ≤
      eLpNorm (fun ξ => f (basePoint ξ)) p (volume.restrict (Ub : Set (Fin (n + m) → ℝ))) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono hWr_Ub le_rfl)
  have hWu : eLpNorm (fun ξ => u (basePoint ξ)) p
      (volume.restrict (rhoBallOpen C ν r : Set (Fin (n + m) → ℝ))) ≤
      eLpNorm (fun ξ => u (basePoint ξ)) p (volume.restrict (Ub : Set (Fin (n + m) → ℝ))) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono hWr_Ub le_rfl)
  -- the ratios of the fiber volumes
  have hrat := hscale η₀ (mem_singleton _) a ha0 (by rw [hAa]; exact hbrS)
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
  set N : ℝ≥0∞ := eLpNorm f p (volume.restrict (Vb : Set (Fin n → ℝ))) +
    eLpNorm u p (volume.restrict (Vb : Set (Fin n → ℝ))) with hN
  have hchain : ENNReal.ofReal κ * sobolevXENorm w X Vρ 2 p u ≤
      ENNReal.ofReal κ * (ENNReal.ofReal (Cst * Mq) * N) := by
    calc ENNReal.ofReal κ * sobolevXENorm w X Vρ 2 p u
        ≤ sobolevXENorm w C.Xl Ua 2 p (fun ξ => u (basePoint ξ)) := hlow
      _ ≤ sobolevXENorm w C.Xl (rhoBallOpen C ν (r / 2)) 2 p (fun ξ => u (basePoint ξ)) := hmono
      _ ≤ ENNReal.ofReal Cst *
          (eLpNorm (fun ξ => f (basePoint ξ)) p
              (volume.restrict (rhoBallOpen C ν r : Set (Fin (n + m) → ℝ))) +
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

/-- The original-domain base Sobolev estimate from the lifted one
(BB p. 587, Thm 11.43). For `Ω' ⋐ Ω'' ⋐ Ω` (here: `closure Ω'` compact in `Ω''`, `Ω'' ⊆ Ω`) and
`1 ≤ p < ∞`: if the lifted base Sobolev estimate `LiftedBaseSobolevEstimate` holds on a lifted
chart at every point of `closure Ω'` (the charts given by the lifting theorem, taken as data), then
there is `C = C(X, Ω', Ω'', p)` with
`‖u‖_{W^{2,p}_X(Ω')} ≤ C (‖Lu‖_{L^p(Ω'')} + ‖u‖_{L^p(Ω'')})`
for all `u ∈ W^{2,p}_X(Ω'')` and every value `f = L u` of `L = ∑ X_{J i}` on `Ω''`
(`J = driftOpWords q`: drift allowed). -/
theorem sobolev_transfer_cover_of_lifted {ι : Type} [Fintype ι] (J : ι → List (Fin k))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) (Ω' Ω'' : Opens (Fin n → ℝ))
    (hcpt : IsCompact (closure (Ω' : Set (Fin n → ℝ))))
    (hΩ'Ω'' : closure (Ω' : Set (Fin n → ℝ)) ⊆ (Ω'' : Set (Fin n → ℝ)))
    (hΩ''Ω : (Ω'' : Set (Fin n → ℝ)) ⊆ Ω)
    (hcharts : ∀ x ∈ closure (Ω' : Set (Fin n → ℝ)), ∃ m : ℕ,
      ∃ C : LiftedChart w st Ω hΩ X x m, ∃ ν : G2.HomogeneousNorm C.G,
        LiftedBaseSobolevEstimate C ν J p) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∀ u f : (Fin n → ℝ) → ℝ,
      memSobolevX w X Ω'' 2 p u → HasWeakOperatorValue X Ω'' J u f →
      sobolevXENorm w X Ω' 2 p u ≤ ENNReal.ofReal Cst *
        (eLpNorm f p (volume.restrict (Ω'' : Set (Fin n → ℝ))) +
          eLpNorm u p (volume.restrict (Ω'' : Set (Fin n → ℝ)))) := by
  classical
  have hxΩ : ∀ x ∈ closure (Ω' : Set (Fin n → ℝ)), x ∈ Ω := fun x hx => hΩ''Ω (hΩ'Ω'' hx)
  have hloc : ∀ x ∈ closure (Ω' : Set (Fin n → ℝ)), ∃ ρ b K : ℝ, 0 < ρ ∧ ρ ≤ b ∧
      rsBall Ω w X x b ⊆ (Ω'' : Set (Fin n → ℝ)) ∧ 0 < K ∧
      (∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ b → IsOpen (rsBall Ω w X x ρ')) ∧
      ∀ (Vρ Vb : Opens (Fin n → ℝ)), (Vρ : Set (Fin n → ℝ)) = rsBall Ω w X x ρ →
        (Vb : Set (Fin n → ℝ)) = rsBall Ω w X x b → ∀ u f : (Fin n → ℝ) → ℝ,
        memSobolevX w X Vb 2 p u → HasWeakOperatorValue X Vb J u f →
        sobolevXENorm w X Vρ 2 p u ≤ ENNReal.ofReal K *
          (eLpNorm f p (volume.restrict (Vb : Set (Fin n → ℝ))) +
            eLpNorm u p (volume.restrict (Vb : Set (Fin n → ℝ)))) := by
    intro x hx
    obtain ⟨m, C, ν, hest⟩ := hcharts x hx
    obtain ⟨ε, hε0, hεV⟩ := exists_rsBall_subset hΩ
      (fun i => (liftedChart_contDiffOn_base C i).continuousOn) Ω''.isOpen (hΩ'Ω'' hx) (hxΩ x hx)
    obtain ⟨ρ, b, K, hρ, hρb, hbε, hK, hopen, hbound⟩ :=
      sobolev_local_transfer C ν J hp hpt hest hε0
    exact ⟨ρ, b, K, hρ, hρb, (rsBall_mono Ω w X x hbε).trans hεV, hK, hopen, hbound⟩
  choose ρ b K hρ0 hρb hbΩ hK0 hopen hbound using hloc
  have hnhds : ∀ x (hx : x ∈ closure (Ω' : Set (Fin n → ℝ))),
      rsBall Ω w X x (ρ x hx) ∈ 𝓝 x := fun x hx =>
    (hopen x hx _ (hρ0 x hx) (hρb x hx)).mem_nhds
      ⟨hxΩ x hx, by
        rw [G1.controlDistance_self w X (hxΩ x hx)]
        exact ENNReal.ofReal_pos.2 (hρ0 x hx)⟩
  obtain ⟨t, ht⟩ := hcpt.elim_nhds_subcover' (fun x hx => rsBall Ω w X x (ρ x hx)) hnhds
  let A : closure (Ω' : Set (Fin n → ℝ)) → Opens (Fin n → ℝ) := fun x =>
    ⟨rsBall Ω w X x.1 (ρ x.1 x.2), hopen x.1 x.2 _ (hρ0 x.1 x.2) (hρb x.1 x.2)⟩
  let B : closure (Ω' : Set (Fin n → ℝ)) → Opens (Fin n → ℝ) := fun x =>
    ⟨rsBall Ω w X x.1 (b x.1 x.2),
      hopen x.1 x.2 _ ((hρ0 x.1 x.2).trans_le (hρb x.1 x.2)) le_rfl⟩
  have hBΩ : ∀ x, (B x : Set (Fin n → ℝ)) ⊆ (Ω'' : Set (Fin n → ℝ)) := fun x => hbΩ x.1 x.2
  have hAΩ : ∀ x, (A x : Set (Fin n → ℝ)) ⊆ (Ω'' : Set (Fin n → ℝ)) := fun x =>
    (rsBall_mono Ω w X x.1 (hρb x.1 x.2)).trans (hbΩ x.1 x.2)
  have hKsum : 0 ≤ ∑ x ∈ t, K x.1 x.2 :=
    Finset.sum_nonneg fun x _ => (hK0 x.1 x.2).le
  refine ⟨1 + ∑ x ∈ t, K x.1 x.2, by linarith, fun u f hu hf => ?_⟩
  have hcov := RothschildStein.H3.sobolevXENorm_le_finite_open_cover w X Ω'' Ω' t A
    (subset_closure.trans hΩ'Ω'') (fun x _ => hAΩ x)
    (fun y hy => by
      have := ht (subset_closure hy)
      simp only [mem_iUnion] at this
      obtain ⟨x, hx, hyx⟩ := this
      exact ⟨x, hx, hyx⟩) 2 p hp u hu
  refine hcov.trans ?_
  set N : ℝ≥0∞ := eLpNorm f p (volume.restrict (Ω'' : Set (Fin n → ℝ))) +
    eLpNorm u p (volume.restrict (Ω'' : Set (Fin n → ℝ))) with hN
  calc ∑ x ∈ t, sobolevXENorm w X (A x) 2 p u
      ≤ ∑ x ∈ t, ENNReal.ofReal (K x.1 x.2) * N := by
        refine Finset.sum_le_sum fun x _ => ?_
        refine (hbound x.1 x.2 (A x) (B x) rfl rfl u f
          (RothschildStein.S.memSobolevX_restrict w X Ω'' (B x) (hBΩ x) hu)
          (hf.mono (hBΩ x))).trans ?_
        refine mul_le_mul' le_rfl (add_le_add ?_ ?_)
        · exact eLpNorm_mono_measure _ (Measure.restrict_mono (hBΩ x) le_rfl)
        · exact eLpNorm_mono_measure _ (Measure.restrict_mono (hBΩ x) le_rfl)
    _ = ENNReal.ofReal (∑ x ∈ t, K x.1 x.2) * N := by
        rw [ENNReal.ofReal_sum_of_nonneg fun x _ => (hK0 x.1 x.2).le, Finset.sum_mul]
    _ ≤ ENNReal.ofReal (1 + ∑ x ∈ t, K x.1 x.2) * N := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl

/-- drift case: `L = X_0 + ∑_{i ≥ 1} X_i²` on the alphabet
`Fin (q + 1)` with weights `driftWeight` (drift of weight two at the letter `0`). -/
theorem sobolev_transfer_cover_drift_of_lifted {q : ℕ}
    {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (Ω' Ω'' : Opens (Fin n → ℝ)) (hcpt : IsCompact (closure (Ω' : Set (Fin n → ℝ))))
    (hΩ'Ω'' : closure (Ω' : Set (Fin n → ℝ)) ⊆ (Ω'' : Set (Fin n → ℝ)))
    (hΩ''Ω : (Ω'' : Set (Fin n → ℝ)) ⊆ Ω)
    (hcharts : ∀ x ∈ closure (Ω' : Set (Fin n → ℝ)), ∃ m : ℕ,
      ∃ C : LiftedChart driftWeight st Ω hΩ X x m, ∃ ν : G2.HomogeneousNorm C.G,
        LiftedBaseSobolevEstimate C ν (driftOpWords q) p) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∀ u f : (Fin n → ℝ) → ℝ,
      memSobolevX driftWeight X Ω'' 2 p u → HasWeakOperatorValue X Ω'' (driftOpWords q) u f →
      sobolevXENorm driftWeight X Ω' 2 p u ≤ ENNReal.ofReal Cst *
        (eLpNorm f p (volume.restrict (Ω'' : Set (Fin n → ℝ))) +
          eLpNorm u p (volume.restrict (Ω'' : Set (Fin n → ℝ)))) :=
  sobolev_transfer_cover_of_lifted (driftOpWords q) hp hpt Ω' Ω'' hcpt hΩ'Ω'' hΩ''Ω hcharts

end RothschildStein.P2
