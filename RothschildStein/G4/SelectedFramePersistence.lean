-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.InitialDeterminantFlowBounds
public import RothschildStein.G4.FrameDetJetBounds
public import RothschildStein.G4.SuboptimalLowerBounds
public import RothschildStein.G4.WeightedTaylorSmallness
public import RothschildStein.G4.TaylorPolynomialBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Selected-frame persistence along actual constant-control
flows, with a radius chosen from numerical data before the fields,
spatial sets, frame, center and controls. The Taylor order is ns−1.
The geometric construction supplies the common buffer and flow existence. -/
theorem exists_selected_frame_persistence_radius (k n s : ℕ) (hn : 0 < n) (hs : 0 < s)
    (w : Fin (k + 1) → ℕ+) (M Δ t : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ)
    (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ e ≤ t ∧
      ∀ (Ω K : Set (Fin n → ℝ)), IsOpen Ω → K ⊆ Ω →
      ∀ (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) → bracketStepOn Ω w X s →
      (∀ i, HasJetBound Ω K (X i) (n * s + 2 * s) M) →
      (∀ x ∈ K, ∃ C : Fin n → ShortWord w s, Δ ≤ |frameDet (shortField w X) C x|) →
      ∀ (B : Fin n → ShortWord w s) x, x ∈ K → ∀ r : ℝ, 0 < r → r ≤ 1 →
      IsSuboptimal (shortField w X) (shortWeight w) B x t r →
      ∀ (a : ShortWord w s → ℝ), (∀ I, |a I| ≤ (e * r) ^ (shortWeight w I : ℕ)) →
      ∀ γ : ℝ → (Fin n → ℝ), γ 0 = x → ContDiffOn ℝ (⊤ : ℕ∞) γ (Icc 0 1) →
      MapsTo γ (Icc 0 1) K →
      (∀ τ ∈ Icc 0 1, HasDerivAt γ (∑ I, a I • shortField w X I (γ τ)) τ) →
      |frameDet (shortField w X) B (γ 1) - frameDet (shortField w X) B x| ≤
        |frameDet (shortField w X) B x| / 2 := by
  classical
  let d := n * s
  let m := d - 1
  have hd : 0 < d := Nat.mul_pos hn hs
  have hmd : m + 1 = d := by dsimp [m]; omega
  obtain ⟨C₀, hC₀, hinitial⟩ := exists_initial_frameDet_flow_derivative_bound k n s m w M Δ hM hΔ
  let P := wordJetBase n d s M ^ s
  have hP : 0 ≤ P := pow_nonneg (wordJetBase_nonneg_and_le hM).1 _
  obtain ⟨C, hC, hdetjets⟩ := exists_frameDet_jet_bound n d P hP
  let A := fieldIterationBudget 0 d * C * ((Fintype.card (ShortWord w s) : ℝ) * P) ^ d /
    (m.factorial : ℝ)
  have hA : 0 ≤ A := div_nonneg (mul_nonneg (mul_nonneg (fieldIterationBudget_nonneg _ _) hC.le)
    (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hP) _)) (Nat.cast_nonneg _)
  let b := fun j => (j.factorial : ℝ)⁻¹ *
    ((Fintype.card (ShortWord w s) : ℝ) ^ j * C₀ * t⁻¹ ^ j)
  obtain ⟨e, he, he1, het, hsmall⟩ := exists_weightedTaylor_smallness m d hd b A t Δ ht hΔ
  refine ⟨e, he, he1, het, ?_⟩
  intro Ω K hΩ hKΩ X hX hstep hjets hmax B x hx r hr hr1 hB a ha γ hinit hγs hmap hγ
  let Z := shortField (s := s) w X
  let v := shortWeight (s := s) w
  have hZ : ∀ I, ContDiffOn ℝ (⊤ : ℕ∞) (Z I) Ω := shortField_contDiffOn hΩ hX
  have hZP : ∀ I : ShortWord w s, HasJetBound Ω K (Z I) d P := by
    intro I
    have hw := ((mem_shortWordFamily_iff w I.val).mp I.property).2
    exact wordBracket_jet_bound_uniform hΩ hKΩ X hX hM
      (fun i => (hjets i).mono (by dsimp [d]; omega)) I.val
      ((wordLength_le_wordWeight w I.val).trans hw)
  have hdetSmooth : ContDiffOn ℝ (⊤ : ℕ∞) (frameDet Z B) Ω := frameDet_contDiffOn hZ B
  have hdetC := hdetjets (ShortWord w s) Ω K hΩ hKΩ Z hZ hZP B
  have hden : ∀ y ∈ K, Δ ^ 2 ≤ determinantSquareSum Z y := by
    intro y hy
    obtain ⟨D, hD⟩ := hmax y hy
    have hb : (frameDet Z D y) ^ 2 ≤ determinantSquareSum Z y :=
      Finset.single_le_sum (fun D _ => sq_nonneg (frameDet Z D y)) (Finset.mem_univ D)
    nlinarith [sq_abs (frameDet Z D y)]
  let f : ℝ → ℝ := frameDet Z B ∘ γ
  let E := ∑ j ∈ Finset.range m, b (j + 1) * e ^ (j + 1)
  have hE : 0 ≤ E := Finset.sum_nonneg (fun j _ => mul_nonneg
    (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hC₀.le)
        (pow_nonneg (inv_nonneg.mpr ht.le) _))) (pow_nonneg he.le _))
  have hpoly : |taylorWithinEval f m (Icc 0 1) 0 1 - f 0| ≤ E * |frameDet Z B x| := by
    apply taylorWithinEval_one_deviation_bound f m
      (fun j => (Fintype.card (ShortWord w s) : ℝ) ^ j * C₀ * t⁻¹ ^ j)
    intro j hj
    have hjm : j + 1 ≤ m := Finset.mem_range.mp hj
    have hflow := iteratedDerivWithin_comp_flow hΩ
      (ContDiffOn.sum (fun I _ => (contDiffOn_const (c := a I)).smul (hZ I))) hdetSmooth
      (by norm_num : (0 : ℝ) < 1) (fun _ hτ => hKΩ (hmap hτ)) hγ (j + 1)
      (by constructor <;> norm_num : (0 : ℝ) ∈ Icc 0 1)
    change |iteratedDerivWithin (j + 1) (frameDet Z B ∘ γ) (Icc 0 1) 0| ≤ _
    rw [hflow]
    change |fieldIterates (fun y => ∑ I, a I • Z I y) (j + 1) (frameDet Z B) (γ 0)| ≤ _
    rw [hinit]
    have hb := hinitial Ω K hΩ hKΩ X hX hstep
      (fun i => (hjets i).mono (by dsimp [m, d]; omega)) hden B (j + 1) hjm x hx
      t r e ht ht1 hr hr1 he.le he1 hB a ha
    nlinarith [hb]
  have her1 : e * r ≤ 1 := (mul_le_mul_of_nonneg_right he1 hr.le).trans (by simpa using hr1)
  have hrem := small_control_flow_taylor_remainder_bound hΩ hKΩ hZ hdetSmooth v a hγs hmap hγ m
    hP hC.le (fun I => by simpa only [hmd] using hZP I)
    (by simpa only [hmd] using hdetC) (mul_nonneg he.le hr.le)
    her1 ha
  have hrem' : |f 1 - taylorWithinEval f m (Icc 0 1) 0 1| ≤ A * (e * r) ^ d := by
    simpa only [f, A, Function.comp_apply, hmd] using hrem
  have hlower := suboptimal_frameDet_lower_bound v s
    (fun I => ((mem_shortWordFamily_iff w I.val).mp I.property).2) B ht hr hr1 hΔ.le (hmax x hx) hB
  have heq := relative_taylor_error_bound he.le hr ht hΔ hA hE hlower hpoly hrem'
  have hhalf := mul_le_mul_of_nonneg_right hsmall.le (abs_nonneg (frameDet Z B x))
  have heq' : |f 1 - f 0| ≤ (E + A * e ^ d / (t * Δ)) * |frameDet Z B x| := heq
  have hb := heq'.trans hhalf
  simpa only [f, Function.comp_apply, hinit, div_eq_mul_inv, one_mul, mul_comm] using hb

end RothschildStein.G4
