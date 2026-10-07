-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.HomogeneousIteratedDerivative
public import RothschildStein.P1.WeightedPoleSmoothExtension

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set

namespace RothschildStein.P1

/-- A homogeneous kernel of sufficiently high
weighted degree extends with every prescribed finite ordinary derivative
across its pole. Its value at zero is zero. The sufficient budget uses the
largest coordinate weight and depends on the requested regularity. -/
theorem contDiff_homogeneous_of_high_degree {N : ℕ} (G : HomogeneousGroup N)
    (W m : ℕ) (hW : ∀ i, G.weight i ≤ W)
    (g : (Fin N → ℝ) → ℝ) (d : ℤ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin N → ℝ, u ≠ 0 →
      g (G.dilate r u) = r ^ d * g u)
    (hzero : g 0 = 0) (hd : (((m + 1) * W : ℕ) : ℤ) < d) :
    ContDiff ℝ m g := by
  let L : ((Fin N → ℝ) × (Fin N → ℝ)) →L[ℝ] (Fin N → ℝ) :=
    ContinuousLinearMap.snd ℝ (Fin N → ℝ) (Fin N → ℝ)
  let H : ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ := g ∘ L
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound (by norm_num)
    intro z
    change ‖z.2‖ ≤ 1 * ‖z‖
    simpa only [one_mul] using norm_snd_le z
  have hHoff : ContDiffOn ℝ (⊤ : ℕ∞) H
      {z : (Fin N → ℝ) × (Fin N → ℝ) | z.1 ∈ univ ∧ kgauge G z.2 < 1 ∧ z.2 ≠ 0} :=
    hg.comp L.contDiff.contDiffOn (fun _ hz => hz.2.2)
  have hHbound : ∀ j : ℕ, j ≤ m → ∃ C : ℝ, 0 ≤ C ∧
      ∀ p ∈ (univ : Set (Fin N → ℝ)), ∀ u : Fin N → ℝ,
        u ≠ 0 → kgauge G u ≤ 1 →
        ‖iteratedFDeriv ℝ j H (p, u)‖ ≤ C * kgauge G u ^ (W + 1) := by
    intro j hj
    obtain ⟨C, hC, hb⟩ := exists_homogeneous_iteratedFDeriv_bound G W hW g d hg hhom j
    refine ⟨C, hC, ?_⟩
    intro p hp u hu hρ
    have hjW : j * W ≤ m * W := Nat.mul_le_mul_right W hj
    have hjWz : ((j * W : ℕ) : ℤ) ≤ ((m * W : ℕ) : ℤ) := by exact_mod_cast hjW
    have hexp : ((W + 1 : ℕ) : ℤ) ≤ d - ((j * W : ℕ) : ℤ) := by
      push_cast at hd hjWz ⊢
      nlinarith
    have hpow := zpow_le_zpow_right_of_le_one₀ (kgauge_pos G hu) hρ hexp
    have hnorm := norm_iteratedFDeriv_comp_linear_le_of_contDiffOn L hL g
      {(0 : Fin N → ℝ)}ᶜ isOpen_compl_singleton hg j (p, u) hu
    exact hnorm.trans ((hb u hu hρ).trans
      (by simpa only [zpow_natCast] using mul_le_mul_of_nonneg_left hpow hC))
  have hH := contDiffOn_of_weighted_pole_decay G W 1 m hW (by norm_num) H univ isOpen_univ
    (fun _ _ => hzero) hHoff hHbound
  have hnear : ContDiffOn ℝ m g {u : Fin N → ℝ | kgauge G u < 1} :=
    hH.comp ((contDiffOn_const (c := (0 : Fin N → ℝ))).prodMk contDiffOn_id) (fun u hu => ⟨mem_univ _, hu⟩)
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u = 0
  · subst u
    apply hnear.contDiffAt
    apply (isOpen_lt (G2.continuous_gauge G) continuous_const).mem_nhds
    change kgauge G (0 : Fin N → ℝ) < 1
    rw [(kgauge_eq_zero_iff G 0).mpr rfl]
    norm_num
  · exact (hg.contDiffAt (isOpen_compl_singleton.mem_nhds hu)).of_le (by simp)

end RothschildStein.P1
