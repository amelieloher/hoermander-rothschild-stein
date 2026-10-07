-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.JointShortChartInjectivity
public import RothschildStein.L1.MixedWeightedBoxes
public import RothschildStein.G4.InjectiveChartSmoothInverse
public import RothschildStein.G4.ControlledChartPathLifting
public import RothschildStein.G4.ZeroShiftTrajectoryCost
public import RothschildStein.G4.CompactUniformChartInjectivity
public import RothschildStein.G4.SelectedChartDerivativeContinuity

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped BigOperators Topology

namespace RothschildStein.L1
open G4

/-- Primitive local smoothness, jet and rank data construct
one jointly smooth shifted family, with a fresh shift radius after each
selected horizontal radius, compact-center injectivity, factor-four
Jacobians, all ball inclusions, and a smooth inverse on its entire image
(BB Theorems 9.11/9.42, pp. 404, 438; Prop 9.52, pp. 448–449). -/
theorem exists_joint_shifted_short_ball_box (k n s h q : ℕ)
    (hn : 0 < n) (hs : 0 < s) (horder : q + 1 = n * s + s) (hq : q + 1 ≤ h)
    (w : Fin (k + 1) → ℕ+) {M Δ R t : ℝ}
    (hM : 0 ≤ M) (hΔ : 0 < Δ) (hR : 0 < R) (ht : 0 < t) (ht1 : t < 1)
    (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω)
    (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) Ω) (hstep : bracketStepOn Ω w X s)
    (x₀ : Fin n → ℝ) (hRΩ : closedBall x₀ R ⊆ Ω)
    (hjets : ∀ j, HasJetBound Ω (closedBall x₀ R) (X j)
      (max (2 * (n * s) + 2 * s) (max ((q + 1) * s) (h + 1 + s))) M)
    (hmax : ∀ y ∈ closedBall x₀ R, ∃ B : Fin n → ShortWord w s,
      Δ ≤ |frameDet (shortField w X) B y|) :
    let m := Fintype.card (ShortWord w s)
    let wf : Fin m → ℕ+ := fun j => shortWeight w (shortIndex w j)
    let Zf : Fin m → (Fin n → ℝ) → (Fin n → ℝ) := fun j => shortField w X (shortIndex w j)
    let δ := R / (64 * (1 + ((n + m : ℕ) : ℝ) * wordJetBase n 0 s M ^ s))
    ∃ a₀ r₀ D κ : ℝ, 0 < a₀ ∧ a₀ < 1 ∧ a₀ < δ ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
      0 ≤ D ∧ 0 < κ ∧ (n : ℝ) * κ ≤ 1 / 4 ∧
      ∃ Φ : (Fin n → ShortWord w s) →
        (((Fin (n + m) → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ),
      (∀ B, ContDiffOn ℝ (⊤ : ℕ∞) (Φ B)
        ((ball 0 δ ×ˢ ball x₀ (R/4)) ×ˢ Ioo (-2) 2) ∧
        ∀ p ∈ ball 0 δ, ∀ x ∈ ball x₀ (R/4), Φ B ((p,x),0) = x ∧
          ∀ τ ∈ Ioo (-2 : ℝ) 2, Φ B ((p,x),τ) ∈ ball x₀ R ∧
            HasDerivAt (fun v => Φ B ((p,x),v))
              (∑ j, p j • shortField w X (selectedAuxiliaryIndex w B j) (Φ B ((p,x),τ))) τ) ∧
      ∀ a : ℝ, 0 < a → a ≤ a₀ →
      ∃ b : ℝ, 0 < b ∧ b < a/4 ∧ 2*b ≤ 1 ∧
      ∀ x ∈ closedBall x₀ (R / 16), ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ B : Fin n → ShortWord w s,
        IsSuboptimal (shortField w X) (shortWeight w) B x t r →
      ∀ v ∈ weightedBox wf (b * r),
      let F := fun u => Φ B ((Fin.append u v, x), 1)
      let Q := weightedBox (shortWeight w ∘ B) (a * r)
      ChartAnalyticBounds Ω wf Zf ((Fintype.equivFin (ShortWord w s)) ∘ B) F Q r κ D ∧
      ChartTrajectories Ω Zf ((Fintype.equivFin (ShortWord w s)) ∘ B) F Q x v
        (fun u τ => Φ B ((Fin.append u v, x), τ)) ∧
      (v = 0 → F 0 = x) ∧ InjOn F Q ∧
      (∀ u ∈ Q, |frameDet (shortField w X) B x| / 4 ≤
        |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ∧
        |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ≤
          4 * |frameDet (shortField w X) B x|) ∧
      ({y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal (b * r)} ⊆ F '' Q) ∧
      (F '' Q ⊆ {y | constantShortDistance (s := s) Ω w X x y < ENNReal.ofReal (2 * a * r)}) ∧
      ({y | constantShortDistance (s := s) Ω w X x y < ENNReal.ofReal (2 * a * r)} ⊆
        {y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal (2 * a * r)}) ∧
      (v = 0 → F '' Q ⊆
        {y | constantShortDistance (s := s) Ω w X x y < ENNReal.ofReal (a * r)}) ∧
      IsOpen (F '' Q) ∧
      ∃ Ψ : (Fin n → ℝ) → (Fin n → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) Ψ (F '' Q) ∧
        (∀ y ∈ F '' Q, Ψ y ∈ Q ∧ F (Ψ y) = y) ∧ (∀ u ∈ Q, Ψ (F u) = u) ∧
        ∀ y ∈ F '' Q, ∀ ℓ i : Fin n,
          |(fderiv ℝ Ψ y (shortField w X (B ℓ) y)) i| ≤ (4 / 3 : ℝ) *
            r ^ (((shortWeight w (B i) : ℕ) : ℤ) - ((shortWeight w (B ℓ) : ℕ) : ℤ)) := by
  intro m wf Zf δ
  obtain ⟨a₀,r₀,D,κ,ha₀,ha₀1,ha₀δ,hr₀,hr1,hD,hκ,hsmall,Φ,hjoint,hcharts⟩ :=
    exists_actual_short_chart_injectivity_with_flow k n s h q hn hs horder hq w
      hM hΔ hR ht ht1 Ω hΩ X hX hstep x₀ hRΩ hjets hmax
  refine ⟨a₀,r₀,D,κ,ha₀,ha₀1,ha₀δ,hr₀,hr1,hD,hκ,hsmall,Φ,hjoint,?_⟩
  intro a ha haa₀
  have ha1 : a ≤ 1 := haa₀.trans ha₀1.le
  obtain ⟨b,hb,hba,hb1,hlifter⟩ :=
    exists_uniform_controlled_chart_lift_radius (m := m) (n := n) (s := s) ha ha1 hD
  have hba' : b ≤ a := by linarith
  refine ⟨b,hb,hba,hb1,?_⟩
  intro x hx r hr hrr B hB v hv F Q
  let Bf := (Fintype.equivFin (ShortWord w s)) ∘ B
  have hweights : wf ∘ Bf = shortWeight w ∘ B := by
    funext i
    simp [wf, Bf, shortIndex]
  have hvA : v ∈ weightedBox wf (a * r) := by
    intro i
    exact (hv i).trans_le (pow_le_pow_left₀ (mul_nonneg hb.le hr.le)
      (mul_le_mul_of_nonneg_right hba' hr.le) _)
  have hvA₀ : v ∈ weightedBox wf (a₀*r) :=
    weightedBox_subset_of_radius_le wf (mul_nonneg ha.le hr.le)
      (mul_le_mul_of_nonneg_right haa₀ hr.le) hvA
  obtain ⟨hAB₀,htraj₀,hzero,hinj₀,hjac₀⟩ := hcharts x hx r hr hrr B hB v hvA₀
  have hQQ₀ : Q ⊆ weightedBox (shortWeight w ∘ B) (a₀*r) :=
    weightedBox_subset_of_radius_le _ (mul_nonneg ha.le hr.le)
      (mul_le_mul_of_nonneg_right haa₀ hr.le)
  have hAB : ChartAnalyticBounds Ω wf Zf Bf F Q r κ D :=
    ⟨hAB₀.1.mono hQQ₀,fun u hu => hAB₀.2.1 (hQQ₀ hu),
      fun u hu => hAB₀.2.2.1 u (hQQ₀ hu),
      fun u hu => hAB₀.2.2.2.1 u (hQQ₀ hu),
      fun u hu => hAB₀.2.2.2.2.1 u (hQQ₀ hu),
      fun u hu => hAB₀.2.2.2.2.2 u (hQQ₀ hu)⟩
  have htraj := fun u hu => htraj₀ u (hQQ₀ hu)
  have hinj := hinj₀.mono hQQ₀
  have hjac := fun u hu => hjac₀ u (hQQ₀ hu)
  have hQ : IsOpen Q := isOpen_weightedBox (shortWeight w ∘ B) (a * r)
  have hne : Q.Nonempty := ⟨0, fun i => by
    simp only [Pi.zero_apply, abs_zero]
    exact pow_pos (mul_pos ha hr) _⟩
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F (weightedBox (wf ∘ Bf) (a * r)) := by
    simpa only [hweights] using hAB.1
  have hw : ∀ i, (wf (Bf i) : ℕ) ≤ s := by
    intro i
    have hh := ((mem_shortWordFamily_iff w (B i).val).mp (B i).property).2
    simpa [wf, Bf, shortIndex, shortWeight] using hh
  have hj : ∀ u ∈ weightedBox (wf ∘ Bf) (a * r),
      Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u)) ≠ 0 := by
    simpa only [hweights] using hAB.2.2.1
  have hd : ∀ u ∈ weightedBox (wf ∘ Bf) (a * r), frameDet Zf Bf (F u) ≠ 0 := by
    simpa only [hweights] using hAB.2.2.2.1
  have hspan : ∃ C : Fin n → ShortWord w s, frameDet (shortField w X) C x ≠ 0 := by
    obtain ⟨C, hC⟩ := hmax x (closedBall_subset_closedBall (by linarith) hx)
    exact ⟨C, abs_pos.mp (hΔ.trans_le hC)⟩
  have hBx : frameDet Zf Bf x ≠ 0 := by
    have hh := suboptimal_frame_ne_zero ht hr hspan hB
    simpa only [Zf, Bf, shortIndex, frameDet_reindex] using hh
  have hlift : ∀ γ : ℝ → (Fin n → ℝ), isControlledCurve Ω wf Zf (2 * b * r) γ →
      F 0 = γ 0 → ∃ θ, IsChartPathLift F γ θ (weightedBox (wf ∘ Bf) (a * r)) 1 := by
    intro γ hγ hstart
    obtain ⟨θ, hθ, _, _⟩ := hlifter wf Bf hw Zf F r κ hr (hrr.trans hr1)
      hκ.le hsmall hF hj hd
      (by simpa only [hweights] using hAB.2.2.2.2.1)
      (by simpa only [hweights] using hAB.2.2.2.2.2) Ω γ hγ hstart
    exact ⟨θ, hθ⟩
  have hballs := shifted_chart_ball_inclusions Ω wf Zf Bf F hBx ha hb hba' hr v hv
    (fun u τ => Φ B ((Fin.append u v, x), τ))
    (by simpa only [hweights, ChartTrajectories, F, Zf, Bf] using htraj) hlift
  have hballs' :
      ({y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal (b * r)} ⊆ F '' Q) ∧
      (F '' Q ⊆ {y | constantShortDistance (s := s) Ω w X x y < ENNReal.ofReal (2 * a * r)}) ∧
      ({y | constantShortDistance (s := s) Ω w X x y < ENNReal.ofReal (2 * a * r)} ⊆
        {y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal (2 * a * r)}) := by
    simpa only [hweights, auxiliaryDistance, constantShortDistance] using hballs
  have hzeroUpper : v = 0 → F '' Q ⊆
      {y | constantShortDistance (s := s) Ω w X x y < ENNReal.ofReal (a * r)} := by
    intro hv0
    subst v
    rintro y ⟨u, hu, rfl⟩
    obtain ⟨hac, hmap, hinit, hend, hder⟩ := htraj u hu
    have he := selectedAuxiliaryTrajectory_zero_shift_cost_lt Ω wf Zf Bf
      (frame_index_injective_of_frameDet_ne_zero Zf Bf hBx) (mul_pos ha hr) u
      (by simpa only [hweights] using hu)
      (fun τ => Φ B ((Fin.append u 0, x), τ)) hac hmap hder
    have hi' : Φ B ((Fin.append u 0, x), 0) = x := hinit
    have he' : Φ B ((Fin.append u 0, x), 1) = F u := hend
    rw [hi', he'] at he
    simpa only [constantShortDistance, Zf, wf, mem_ofPred_eq] using he
  obtain ⟨hopen, Ψ, hΨ, hright, hleft⟩ :=
    exists_smooth_inverse_of_actual_chart_injective hQ hne F hAB.1 hAB.2.2.1 hinj
  refine ⟨hAB, htraj, hzero, hinj, hjac, hballs'.1, hballs'.2.1, hballs'.2.2,
    hzeroUpper, hopen, Ψ, hΨ, hright, hleft, ?_⟩
  intro y hy ℓ i
  have hu := (hright y hy).1
  have hFy := (hright y hy).2
  have hFD := (hAB.1.contDiffAt (hQ.mem_nhds hu)).differentiableAt (by simp)
  have hΨD := (hΨ.contDiffAt (hopen.mem_nhds hy)).differentiableAt (by simp)
  have hrightGerm : (fun z => F (Ψ z)) =ᶠ[𝓝 y] (fun z => z) := by
    filter_upwards [hopen.mem_nhds hy] with z hz
    exact (hright z hz).2
  have hdetY : frameDet Zf Bf y ≠ 0 := by
    have hh : frameDet Zf Bf (F (Ψ y)) ≠ 0 := hAB.2.2.2.1 (Ψ y) hu
    rw [hFy] at hh
    exact hh
  have herrorY : ∀ j i : Fin n, |frameCoefficient Zf Bf
      (fun z => fderiv ℝ F (Ψ y) (Pi.single i 1) - Zf (Bf i) z) j y| ≤
        κ * r ^ (((wf (Bf j) : ℕ) : ℤ) - ((wf (Bf i) : ℕ) : ℤ)) := by
    have hh : ∀ j i : Fin n, |frameCoefficient Zf Bf
        (fun z => fderiv ℝ F (Ψ y) (Pi.single i 1) - Zf (Bf i) z) j (F (Ψ y))| ≤
          κ * r ^ (((wf (Bf j) : ℕ) : ℤ) - ((wf (Bf i) : ℕ) : ℤ)) :=
      hAB.2.2.2.2.1 (Ψ y) hu
    rw [hFy] at hh
    exact hh
  have he := local_inverse_frame_derivative_bound Zf wf Bf F Ψ rfl hFD hΨD
    hrightGerm hdetY hr hκ.le hsmall herrorY ℓ i
  simpa [Zf, wf, Bf, shortIndex] using he

end RothschildStein.L1
