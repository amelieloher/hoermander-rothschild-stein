-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.KernelEstimatesWeightedTaylor

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace RothschildStein.P1

variable {N : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [LocallyCompactSpace P]

omit [LocallyCompactSpace P] in
/-- Hadamard decomposition `F(η,u) - F(η,0) = ∑ⱼ uⱼ Fⱼ(η,u)` along rays. -/
theorem hadamard_decomp_generic_parameter (F : P × (Fin N → ℝ) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (η : P) (u : Fin N → ℝ) :
    F (η, u) - F (η, 0) = ∑ j, u j * ∫ θ in Icc (0 : ℝ) 1,
      fderiv ℝ F (η, θ • u) (0, Pi.single j 1) := by
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)
  have hderiv : ∀ θ ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun θ : ℝ => F (η, θ • u))
      (fderiv ℝ F (η, θ • u) (0, u)) θ := by
    intro θ _
    have h1 : HasDerivAt (fun θ : ℝ => ((η, θ • u) : P × (Fin N → ℝ))) ((0, u)) θ := by
      refine (hasDerivAt_const θ η).prodMk ?_
      simpa using (hasDerivAt_id θ).smul_const u
    exact (hFd (η, θ • u)).hasFDerivAt.comp_hasDerivAt θ h1
  have hc : Continuous (fun θ : ℝ => fderiv ℝ F (η, θ • u) (0, u)) :=
    ((hF.continuous_fderiv (by simp)).comp (continuous_const.prodMk (continuous_id.smul continuous_const))).clm_apply
      continuous_const
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hc.intervalIntegrable 0 1)
  simp only [one_smul, zero_smul] at hftc
  rw [← hftc, intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  have hsum : ∀ θ : ℝ, fderiv ℝ F (η, θ • u) (0, u) =
      ∑ j, u j * fderiv ℝ F (η, θ • u) (0, Pi.single j 1) := by
    intro θ
    have : ((0 : P), u) = ∑ j, u j • ((0 : P), (Pi.single j (1 : ℝ) : Fin N → ℝ)) := by
      apply Prod.ext
      · simp [Prod.fst_sum]
      · ext i
        simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [this, map_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [map_smul, smul_eq_mul])
  simp_rw [hsum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_const_mul]
  · intro j _
    exact (continuous_const.mul (((hF.continuous_fderiv (by simp)).comp
      (continuous_const.prodMk (continuous_id.smul continuous_const))).clm_apply
        continuous_const)).integrableOn_Icc


omit [LocallyCompactSpace P] in
/-- The coordinate partial of a parametrized function is the partial derivative. -/
theorem rsPartial_single_generic_parameter (F : P × (Fin N → ℝ) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (η : P) (y : Fin N → ℝ) (j : Fin N) :
    rsPartial [j] (fun u => F (η, u)) y = fderiv ℝ F (η, y) (0, Pi.single j 1) := by
  have h1 : HasFDerivAt (fun u : Fin N → ℝ => F (η, u))
      ((fderiv ℝ F (η, y)).comp (ContinuousLinearMap.inr ℝ P (Fin N → ℝ))) y :=
    ((hF.differentiable (by simp)) (η, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right η y)
  show fderiv ℝ (fun u : Fin N → ℝ => F (η, u)) y (Pi.single j 1) = _
  rw [h1.fderiv]
  simp

/-- The Hadamard factors of a smooth parametrized function are smooth. -/
theorem hadamardFactor_generic_parameter_contDiff (F : P × (Fin N → ℝ) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (j : Fin N) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : P × (Fin N → ℝ) =>
      ∫ θ in Icc (0 : ℝ) 1, fderiv ℝ F (p.1, θ • p.2) (0, Pi.single j 1)) := by
  apply RothschildStein.G1.compactParameterIntegral_contDiff
    (fun q : (P × (Fin N → ℝ)) × ℝ => fderiv ℝ F (q.1.1, q.2 • q.1.2) (0, Pi.single j 1))
  have hD : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ F) := (contDiff_infty_iff_fderiv.mp hF).2
  have harg : ContDiff ℝ (⊤ : ℕ∞) (fun q : (P × (Fin N → ℝ)) × ℝ =>
      (q.1.1, q.2 • q.1.2)) :=
    contDiff_fst.fst.prodMk (contDiff_snd.smul contDiff_fst.snd)
  exact (hD.comp harg).clm_apply contDiff_const

/-- Weighted Taylor bound with vanishing weighted jets: if the weighted jets of a smooth
`F(η, ·)` with arbitrary locally compact normed parameters of order `< b` vanish at `0` for `η` in a compact set, then `|F(η,u)| ≤ C ρ(u)^b` for
`ρ(u) ≤ 1` (BB p. 548, Lemma 11.16 and Remark 11.17). -/
theorem weighted_taylor_generic_parameter (G : HomogeneousGroup N) :
    ∀ (b : ℕ) (F : P × (Fin N → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) F →
    ∀ K : Set P, IsCompact K →
    (∀ η ∈ K, ∀ J : List (Fin N), (J.map G.weight).sum < b →
        rsPartial J (fun u => F (η, u)) 0 = 0) →
    ∃ C : ℝ, ∀ η ∈ K, ∀ u : Fin N → ℝ, kgauge G u ≤ 1 →
      |F (η, u)| ≤ C * kgauge G u ^ b := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro F hF K hK hjet
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · have hcomp : IsCompact (K ×ˢ {u : Fin N → ℝ | kgauge G u ≤ 1}) :=
        hK.prod (G2.isCompact_gauge_le (G2.isHomogeneousGauge_max G) 1)
      obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hF.continuous.continuousOn
      exact ⟨C, fun η hη u hu => by simpa using hC (η, u) ⟨hη, hu⟩⟩
    · set Fj : Fin N → P × (Fin N → ℝ) → ℝ := fun j p =>
        ∫ θ in Icc (0 : ℝ) 1, fderiv ℝ F (p.1, θ • p.2) (0, Pi.single j 1) with hFj
      have hjets : ∀ j : Fin N, ∀ η ∈ K, ∀ J : List (Fin N),
          (J.map G.weight).sum < b - G.weight j →
          rsPartial J (fun u => Fj j (η, u)) 0 = 0 := by
        intro j η hη J hJ
        have hg : ContDiff ℝ (⊤ : ℕ∞) (fun u : Fin N → ℝ => F (η, u)) :=
          hF.comp (contDiff_const.prodMk contDiff_id)
        have heq : (fun u => Fj j (η, u)) = fun y : Fin N → ℝ => ∫ θ in Icc (0 : ℝ) 1,
            rsPartial [j] (fun u => F (η, u)) (θ • y) := by
          funext y
          simp only [hFj]
          refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
          exact (rsPartial_single_generic_parameter F hF η _ j).symm
        rw [heq]
        apply rsPartial_scaledIntegral_eq_zero _ (rsPartial_contDiff [j] hg)
        rw [rsPartial_append_single]
        apply hjet η hη
        simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero]
        omega
      have hC := fun j : Fin N => ih (b - G.weight j)
        (by have := G.weight_pos j; omega) (Fj j) (hadamardFactor_generic_parameter_contDiff F hF j) K hK
        (hjets j)
      choose C hC using hC
      refine ⟨∑ j, |C j|, fun η hη u hu => ?_⟩
      have hF0 : F (η, 0) = 0 := by
        have := hjet η hη [] (by simpa using hb)
        simpa [rsPartial] using this
      have hdec := hadamard_decomp_generic_parameter F hF η u
      rw [hF0, sub_zero] at hdec
      have hρ0 : 0 ≤ kgauge G u := kgauge_nonneg G u
      rw [hdec, Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
      have h1 := hC j η hη u hu
      rw [abs_mul]
      have h2 : |u j| ≤ kgauge G u ^ G.weight j := abs_apply_le_kgauge_pow G u j
      have h3 : |Fj j (η, u)| ≤ |C j| * kgauge G u ^ (b - G.weight j) :=
        h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hρ0 _))
      calc |u j| * |Fj j (η, u)| ≤ kgauge G u ^ G.weight j * (|C j| * kgauge G u ^ (b - G.weight j)) :=
            mul_le_mul h2 h3 (abs_nonneg _) (pow_nonneg hρ0 _)
        _ = |C j| * kgauge G u ^ (G.weight j + (b - G.weight j)) := by rw [pow_add]; ring
        _ ≤ |C j| * kgauge G u ^ b :=
            mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ0 hu (by omega)) (abs_nonneg _)



end RothschildStein.P1
