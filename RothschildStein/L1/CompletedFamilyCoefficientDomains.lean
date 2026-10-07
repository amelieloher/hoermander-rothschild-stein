-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.JointShortChartFamilyProperties
public import RothschildStein.L1.CompletedFrameShiftCoefficients
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.L1

/-- The two unequal coordinate boxes fit in the completed
lifted selected box without changing its application scale. -/
theorem completed_selected_parameters_mem_box {q n m s : ℕ} (w : Fin q → ℕ+)
    (B : Fin n → G4.ShortWord w s) (J : Fin m → G4.ShortWord w s)
    {a au av r : ℝ} (hau : 0 ≤ au) (hav : 0 ≤ av) (hr : 0 ≤ r)
    (haua : au ≤ a) (hava : av ≤ a)
    {u : Fin n → ℝ} {v : Fin m → ℝ}
    (hu : u ∈ G4.weightedBox (G4.shortWeight w ∘ B) (au*r))
    (hv : v ∈ G4.weightedBox (G4.shortWeight w ∘ J) (av*r)) :
    Fin.append u v ∈ G4.weightedBox (G4.shortWeight w ∘ Fin.addCases B J) (a*r) := by
  refine Fin.addCases ?_ ?_
  · intro i
    simp only [Fin.append_left,Function.comp_apply,Fin.addCases_left]
    exact (hu i).trans_le (pow_le_pow_left₀ (mul_nonneg hau hr)
      (mul_le_mul_of_nonneg_right haua hr) _)
  · intro i
    simp only [Fin.append_right,Function.comp_apply,Fin.addCases_right]
    exact (hv i).trans_le (pow_le_pow_left₀ (mul_nonneg hav hr)
      (mul_le_mul_of_nonneg_right hava hr) _)

/-- The actual completed lifted parameters and zero full shift
fit in the constructed lifted joint flow domain. -/
theorem completed_lifted_parameters_mem_flowDomain {q n m s : ℕ} {w : Fin q → ℕ+}
    {Ω : Set (Fin (n+m) → ℝ)}
    {X : Fin q → (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ)}
    {z : Fin (n+m) → ℝ} {t : ℝ}
    (F : JointShortChartFamily (n := n+m) (s := s) w Ω X z t)
    (B : Fin n → G4.ShortWord w s) (J : Fin m → G4.ShortWord w s)
    {a au av r : ℝ} (ha : 0 < a) (haa₀ : a ≤ F.a₀)
    (hau : 0 ≤ au) (hav : 0 ≤ av) (haua : au ≤ a) (hava : av ≤ a)
    (hr : 0 < r) (hrr : r ≤ F.r₀)
    {u : Fin n → ℝ} {v : Fin m → ℝ}
    (hu : u ∈ G4.weightedBox (G4.shortWeight w ∘ B) (au*r))
    (hv : v ∈ G4.weightedBox (G4.shortWeight w ∘ J) (av*r)) :
    Fin.append (Fin.append u v) (0 : Fin (Fintype.card (G4.ShortWord w s)) → ℝ) ∈
      ball 0 F.coeffRadius := by
  have hp := completed_selected_parameters_mem_box (q := q) (n := n) (m := m)
    (s := s) w B J (a := a) (au := au) (av := av) (r := r)
    (u := u) (v := v) hau hav hr.le haua hava hu hv
  have har : 0 < a*r := mul_pos ha hr
  have ha1 : a ≤ 1 := haa₀.trans F.a₀_lt_one.le
  have hr1 : r ≤ 1 := hrr.trans F.r₀_le_one
  have har1 : a*r ≤ 1 := (mul_le_mul_of_nonneg_right ha1 hr.le).trans (by simpa using hr1)
  have hnorm : ‖Fin.append u v‖ ≤ a*r :=
    G4.weighted_coefficients_norm_le (G4.shortWeight w ∘ Fin.addCases B J)
      har.le har1 (fun i => (hp i).le)
  rw [mem_ball,dist_zero_right]
  have hn : ‖Fin.append (Fin.append u v)
      (0 : Fin (Fintype.card (G4.ShortWord w s)) → ℝ)‖ ≤ a*r := by
    apply (pi_norm_le_iff_of_nonneg har.le).mpr
    refine Fin.addCases ?_ ?_
    · intro i
      simp only [Fin.append_left]
      exact (norm_le_pi_norm (Fin.append u v) i).trans hnorm
    · intro j
      simp only [Fin.append_right,Pi.zero_apply,norm_zero]
      exact har.le
  exact hn.trans_lt ((mul_le_of_le_one_right ha.le hr1).trans_lt
    (haa₀.trans_lt F.a₀_lt_coeffRadius))

/-- A nonzero completed determinant puts its inserted vertical
shift in the original joint flow domain. This uses the freshly chosen
shift radius, after the horizontal radius (BB pp. 520–521). -/
theorem completed_original_parameters_mem_flowDomain {q n m s : ℕ} {w : Fin q → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}
    {z : Fin n → ℝ} {t : ℝ} (F : JointShortChartFamily (s := s) w Ω X z t)
    (B : Fin n → G4.ShortWord w s) (J : Fin m → G4.ShortWord w s)
    (Z : G4.ShortWord w s → (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ))
    (ξ : Fin (n+m) → ℝ) (hdet : G4.frameDet Z (Fin.addCases B J) ξ ≠ 0)
    {au av b r : ℝ} (hau : 0 < au) (haua₀ : au ≤ F.a₀)
    (hav : 0 < av) (havb : av ≤ b) (hbau : b ≤ au)
    (hr : 0 < r) (hrr : r ≤ F.r₀)
    {u : Fin n → ℝ} {v : Fin m → ℝ}
    (hu : u ∈ G4.weightedBox (G4.shortWeight w ∘ B) (au*r))
    (hv : v ∈ G4.weightedBox (G4.shortWeight w ∘ J) (av*r)) :
    Fin.append u (completionShift w J v) ∈ ball 0 F.coeffRadius := by
  have hv' := completionShift_mem_weightedBox_of_frameDet_ne_zero w B J Z ξ hdet
    (mul_pos hav hr) hv
  have hvb := weightedBox_subset_of_radius_le
    (fun j => G4.shortWeight w (G4.shortIndex (s := s) w j))
    (mul_nonneg hav.le hr.le) (mul_le_mul_of_nonneg_right havb hr.le) hv'
  exact F.parameters_mem_flowDomain B (a := au) (b := b) (r := r)
    (u := u) (v := completionShift w J v) hau haua₀ (hav.le.trans havb) hbau hr.le hrr hu hvb

/-- Joined geometric coordinates are the selected completed parameters. -/
theorem joinPoint_eq_append {n m : ℕ} (u : Fin n → ℝ) (v : Fin m → ℝ) :
    joinPoint u v = Fin.append u v := by
  ext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [joinPoint]
  · intro j
    simp [joinPoint]

/-- The full completed frame weights are exactly the two weight blocks. -/
theorem completed_shortWeight_eq {q n m s : ℕ} (w : Fin q → ℕ+)
    (B : Fin n → G4.ShortWord w s) (J : Fin m → G4.ShortWord w s) :
    (G4.shortWeight w ∘ Fin.addCases B J) =
      Fin.addCases (G4.shortWeight w ∘ B) (G4.shortWeight w ∘ J) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp
  · intro j
    simp

end RothschildStein.L1
