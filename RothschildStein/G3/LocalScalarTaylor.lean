-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FlatScalarJets

@[expose] public section
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace RothschildStein.G3

theorem local_scalar_taylor_littleO {f : ℝ → ℝ} {n : ℕ}
    (hf : ContDiffAt ℝ n f 0) :
    (fun t => f t - taylorWithinEval f n Set.univ 0 t)
      =o[𝓝 0] (fun t : ℝ => t ^ n) := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn (m := (n : WithTop ℕ∞)) le_rfl (by simp)
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.mp hu
  have hzero : (0 : ℝ) ∈ Metric.ball 0 r := by simp [hr]
  have ht := taylor_isLittleO (convex_ball (0 : ℝ) r) hzero (hfu.mono hru)
  rw [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds 0 hr)] at ht
  have he : ∀ t : ℝ,
      taylorWithinEval f n (Metric.ball 0 r) 0 t =
        taylorWithinEval f n Set.univ 0 t := by
    intro t
    simp only [taylor_within_apply, iteratedDerivWithin_univ]
    apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDerivWithin_of_isOpen Metric.isOpen_ball hzero]
  simpa only [he, sub_zero] using ht

theorem iteratedDeriv_zero_of_flat_littleO_at {f : ℝ → ℝ} {n : ℕ}
    (hf : ContDiffAt ℝ n f 0)
    (hflat : (fun t => f t) =o[𝓝 0] (fun t : ℝ => t ^ n)) :
    ∀ k ≤ n, iteratedDeriv k f 0 = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    have hprev : ∀ j < k, iteratedDeriv j f 0 = 0 := by
      intro j hj
      exact ih j hj (by omega)
    have hfk : ContDiffAt ℝ k f 0 := hf.of_le (by exact_mod_cast hk)
    have hsmall : f =o[𝓝 0] (fun t : ℝ => t ^ k) := by
      rcases lt_or_eq_of_le hk with hlt | heq
      · exact hflat.trans_isBigO (isLittleO_pow_pow hlt).isBigO
      · simpa [heq] using hflat
    have ht := local_scalar_taylor_littleO hfk
    have hz : (fun t : ℝ =>
        ((k.factorial : ℝ)⁻¹ * iteratedDeriv k f 0) * t ^ k)
        =o[𝓝 0] (fun t : ℝ => t ^ k) := by
      have hd := hsmall.sub (by simpa only [sub_zero] using ht)
      convert hd using 1
      ext t
      rw [taylor_leading_term_of_lower_jets_zero f k hprev]
      ring
    have ha := scalar_coefficient_zero_of_littleO _ k hz
    exact (mul_eq_zero.mp ha).resolve_left (inv_ne_zero (by positivity))

theorem iteratedDeriv_zero_of_power_bound_at {f : ℝ → ℝ} {n : ℕ} {C : ℝ}
    (hf : ContDiffAt ℝ n f 0)
    (hbound : ∀ᶠ t : ℝ in 𝓝 0, ‖f t‖ ≤ C * |t| ^ (n + 1)) :
    ∀ k ≤ n, iteratedDeriv k f 0 = 0 := by
  have hb : f =O[𝓝 0] (fun t : ℝ => t ^ (n + 1)) := by
    apply isBigO_iff.mpr
    exact ⟨C, by simpa only [norm_pow, Real.norm_eq_abs] using hbound⟩
  exact iteratedDeriv_zero_of_flat_littleO_at hf
    (hb.trans_isLittleO (isLittleO_pow_pow (Nat.lt_succ_self n)))

theorem scalar_jets_eq_of_power_error_at {f g : ℝ → ℝ} {n : ℕ} {C : ℝ}
    (hf : ContDiffAt ℝ n f 0) (hg : ContDiffAt ℝ n g 0)
    (hbound : ∀ᶠ t : ℝ in 𝓝 0, ‖f t - g t‖ ≤ C * |t| ^ (n + 1)) :
    ∀ k ≤ n, iteratedDeriv k f 0 = iteratedDeriv k g 0 := by
  have hz := iteratedDeriv_zero_of_power_bound_at (hf.sub hg) hbound
  intro k hk
  have hfk : ContDiffAt ℝ k f 0 := hf.of_le (by exact_mod_cast hk)
  have hgk : ContDiffAt ℝ k g 0 := hg.of_le (by exact_mod_cast hk)
  have he := hz k hk
  rw [iteratedDeriv_fun_sub hfk hgk] at he
  exact sub_eq_zero.mp he

end RothschildStein.G3
