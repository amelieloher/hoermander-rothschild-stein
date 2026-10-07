-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.InitialOtherDeterminantFlowBounds
public import RothschildStein.G4.SelectedFramePersistence
public import RothschildStein.G4.OtherFrameRemainderBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Every other determinant obeys the sharp nearby weighted
bound along actual constant-control flows. The constant is chosen before
t, the fields, frames, sets and controls. The Taylor order is 2ns−1;
only the initial n inverse-suboptimality factors occur. -/
theorem exists_other_frame_persistence_bound (k n s : ℕ) (hn : 0 < n) (hs : 0 < s)
    (w : Fin (k + 1) → ℕ+) (M Δ : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∀ (Ω K : Set (Fin n → ℝ)), IsOpen Ω → K ⊆ Ω →
      ∀ (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) → bracketStepOn Ω w X s →
      (∀ i, HasJetBound Ω K (X i) (2 * (n * s) + 2 * s) M) →
      (∀ x ∈ K, ∃ C : Fin n → ShortWord w s, Δ ≤ |frameDet (shortField w X) C x|) →
      ∀ (B C : Fin n → ShortWord w s) x, x ∈ K → ∀ r : ℝ, 0 < r → r ≤ 1 →
      IsSuboptimal (shortField w X) (shortWeight w) B x t r →
      ∀ e : ℝ, 0 ≤ e → e ≤ 1 → e ≤ t →
      ∀ a : ShortWord w s → ℝ, (∀ I, |a I| ≤ (e * r) ^ (shortWeight w I : ℕ)) →
      ∀ γ : ℝ → (Fin n → ℝ), γ 0 = x → ContDiffOn ℝ (⊤ : ℕ∞) γ (Icc 0 1) →
      MapsTo γ (Icc 0 1) K →
      (∀ τ ∈ Icc 0 1, HasDerivAt γ (∑ I, a I • shortField w X I (γ τ)) τ) →
      |frameDet (shortField w X) C (γ 1)| ≤ D * t⁻¹ ^ n *
        r ^ (frameWeight (shortWeight w) B - frameWeight (shortWeight w) C) *
          |frameDet (shortField w X) B x| := by
  classical
  let d := n * s
  let m := 2 * d - 1
  have hd : 0 < d := Nat.mul_pos hn hs
  have hmd : m + 1 = 2 * d := by dsimp [m]; omega
  obtain ⟨C₀, hC₀, hinitial⟩ := exists_initial_other_frameDet_flow_derivative_bound k n s m w M Δ hM hΔ
  let P := wordJetBase n (2 * d) s M ^ s
  have hP : 0 ≤ P := pow_nonneg (wordJetBase_nonneg_and_le hM).1 _
  obtain ⟨C₁, hC₁, hdetjets⟩ := exists_frameDet_jet_bound n (2 * d) P hP
  let A := fieldIterationBudget 0 (2 * d) * C₁ * ((Fintype.card (ShortWord w s) : ℝ) * P) ^ (2 * d) /
    (m.factorial : ℝ)
  have hA : 0 ≤ A := div_nonneg (mul_nonneg (mul_nonneg (fieldIterationBudget_nonneg _ _) hC₁.le)
    (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hP) _)) (Nat.cast_nonneg _)
  let E := ∑ j ∈ Finset.range m, ((j + 1).factorial : ℝ)⁻¹ *
    ((Fintype.card (ShortWord w s) : ℝ) ^ (j + 1) * C₀)
  have hE : 0 ≤ E := Finset.sum_nonneg (fun j _ => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hC₀.le))
  refine ⟨C₀ + E + A / Δ, by linarith [div_nonneg hA hΔ.le], ?_⟩
  intro t ht ht1 Ω K hΩ hKΩ X hX hstep hjets hmax B C x hx r hr hr1 hB e he he1 het a ha γ hinit hγs hmap hγ
  let Z := shortField (s := s) w X
  let v := shortWeight (s := s) w
  let p := frameWeight v B - frameWeight v C
  let V := r ^ p * |frameDet Z B x|
  let Q := t⁻¹ ^ n * V
  have hV : 0 ≤ V := mul_nonneg (zpow_nonneg hr.le _) (abs_nonneg _)
  have hQ : 0 ≤ Q := mul_nonneg (pow_nonneg (inv_nonneg.mpr ht.le) _) hV
  have hVQ : V ≤ Q := le_mul_of_one_le_left hV (one_le_pow₀ ((one_le_inv₀ ht).mpr ht1))
  have hZ : ∀ I, ContDiffOn ℝ (⊤ : ℕ∞) (Z I) Ω := shortField_contDiffOn hΩ hX
  have hZP : ∀ I : ShortWord w s, HasJetBound Ω K (Z I) (2 * d) P := by
    intro I
    have hw := ((mem_shortWordFamily_iff w I.val).mp I.property).2
    exact wordBracket_jet_bound_uniform hΩ hKΩ X hX hM
      (fun i => (hjets i).mono (by dsimp [d]; omega)) I.val
      ((wordLength_le_wordWeight w I.val).trans hw)
  have hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (frameDet Z C) Ω := frameDet_contDiffOn hZ C
  have hdetC := hdetjets (ShortWord w s) Ω K hΩ hKΩ Z hZ hZP C
  have hden : ∀ y ∈ K, Δ ^ 2 ≤ determinantSquareSum Z y := by
    intro y hy
    obtain ⟨D, hD⟩ := hmax y hy
    have hb : (frameDet Z D y) ^ 2 ≤ determinantSquareSum Z y :=
      Finset.single_le_sum (fun D _ => sq_nonneg (frameDet Z D y)) (Finset.mem_univ D)
    nlinarith [sq_abs (frameDet Z D y)]
  have hb := hinitial Ω K hΩ hKΩ X hX hstep
    (fun i => (hjets i).mono (by dsimp [m, d]; omega)) hden B C
  have hn : 0 ≤ e * t⁻¹ := mul_nonneg he (inv_nonneg.mpr ht.le)
  have hn1 : e * t⁻¹ ≤ 1 := (mul_inv_le_iff₀ ht).mpr (by simpa using het)
  have hb' : ∀ j ≤ m, |fieldIterates (fun y => ∑ I, a I • Z I y) j (frameDet Z C) x| ≤
      (Fintype.card (ShortWord w s) : ℝ) ^ j * C₀ * Q := by
    intro j hj
    have hjbound := hb j hj x hx t r e ht ht1 hr hr1 he he1 hB a ha
    have hpow : (e * t⁻¹) ^ j ≤ 1 := pow_le_one₀ hn hn1
    calc
      _ ≤ (Fintype.card (ShortWord w s) : ℝ) ^ j * C₀ * t⁻¹ ^ (n + j) * e ^ j *
          r ^ p * |frameDet Z B x| := hjbound
      _ = ((Fintype.card (ShortWord w s) : ℝ) ^ j * C₀ * Q) * (e * t⁻¹) ^ j := by
        dsimp [Q, V]; rw [pow_add, mul_pow]; ring
      _ ≤ _ := mul_le_of_le_one_right (mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hC₀.le) hQ) hpow
  let f : ℝ → ℝ := frameDet Z C ∘ γ
  have hpoly : |taylorWithinEval f m (Icc 0 1) 0 1 - f 0| ≤ E * Q := by
    have hbpoly := taylorWithinEval_one_deviation_bound f m
      (fun j => (Fintype.card (ShortWord w s) : ℝ) ^ j * C₀) (e := 1) (D := Q)
    simp only [one_pow, mul_one] at hbpoly
    apply hbpoly
    intro j hj
    have hflow := iteratedDerivWithin_comp_flow hΩ
      (ContDiffOn.sum (fun I _ => (contDiffOn_const (c := a I)).smul (hZ I))) hsmooth
      (by norm_num : (0 : ℝ) < 1) (fun _ hτ => hKΩ (hmap hτ)) hγ (j + 1)
      (by constructor <;> norm_num : (0 : ℝ) ∈ Icc 0 1)
    change |iteratedDerivWithin (j + 1) (frameDet Z C ∘ γ) (Icc 0 1) 0| ≤ _
    rw [hflow]
    change |fieldIterates (fun y => ∑ I, a I • Z I y) (j + 1) (frameDet Z C) (γ 0)| ≤ _
    rw [hinit]
    exact hb' (j + 1) (Finset.mem_range.mp hj)
  have her1 : e * r ≤ 1 := (mul_le_mul_of_nonneg_right he1 hr.le).trans (by simpa using hr1)
  have hrem := small_control_flow_taylor_remainder_bound hΩ hKΩ hZ hsmooth v a hγs hmap hγ m
    hP hC₁.le (fun I => by simpa only [hmd] using hZP I)
    (by simpa only [hmd] using hdetC) (mul_nonneg he hr.le) her1 ha
  have hrem' : |f 1 - taylorWithinEval f m (Icc 0 1) 0 1| ≤ A * (e * r) ^ (2 * d) := by
    simpa only [f, A, Function.comp_apply, hmd] using hrem
  have hw : ∀ I : ShortWord w s, (v I : ℕ) ≤ s := fun I =>
    ((mem_shortWordFamily_iff w I.val).mp I.property).2
  have hp : p ≤ (d : ℤ) := by
    have hBC := frameWeight_le v s hw B
    have hCw := frameWeight_nonneg v C
    dsimp [p, d]
    omega
  have hlower := suboptimal_frameDet_lower_bound v s hw B ht hr hr1 hΔ.le (hmax x hx) hB
  have hrbound := other_frame_remainder_scale_bound hd hp hA he he1 het hr hr1 ht hΔ hlower hrem'
  have hrQ : |f 1 - taylorWithinEval f m (Icc 0 1) 0 1| ≤ (A / Δ) * Q :=
    hrbound.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hVQ (div_nonneg hA hΔ.le))
  have hzero : |f 0| ≤ C₀ * Q := by
    simpa only [f, Function.comp_apply, hinit, fieldIterates, pow_zero, one_mul] using hb' 0 (Nat.zero_le _)
  have hsum : |f 1| ≤ (C₀ + E + A / Δ) * Q := by
    have heq := abs_sub_le (f 1) (taylorWithinEval f m (Icc 0 1) 0 1) (f 0)
    have hnorm := abs_add_le (f 1 - f 0) (f 0)
    have hnorm' : |f 1| ≤ |f 1 - f 0| + |f 0| := by simpa only [sub_add_cancel] using hnorm
    linarith
  simpa only [f, Function.comp_apply, Q, V, p, mul_assoc] using hsum

end RothschildStein.G4
