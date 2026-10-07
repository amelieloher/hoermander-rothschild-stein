-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.KernelEstimatesHomogeneous

/-!
# Radial cutoffs

The weighted bounds `HasWeightedBounds` of a kernel family `Ψ` are stable under multiplication by
a `C¹` function `χ(u)` of the group variable alone (a smooth radial cutoff `φ(ν(u))`, with `φ`
constant near `0`, is the case of interest): the derivative of `χ` only improves the weight of the
`u`-derivative, since `ρ^d = ρ^(w_j) ρ^(d - w_j) ≤ R^(w_j) ρ^(d - w_j)` on `ρ ≤ R`
(BB pp. 569–571, Prop 11.32: "the data include radial cutoff derivatives").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RothschildStein.P1

variable {N : ℕ} {G : HomogeneousGroup N}
variable {Ψ : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) → ℝ} {d : ℤ}

/-- Product rule for `(ξ, η, u) ↦ χ(u) Ψ(ξ, η, u)` off `u = 0`. -/
theorem fderiv_cutoff_mul {χ : (Fin N → ℝ) → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hΨ : ContDiffOn ℝ 1 (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    {ξ η u : Fin N → ℝ} (hu : u ≠ 0) (v : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)) :
    fderiv ℝ (kernelUncurry (fun ξ η u => χ u * Ψ ξ η u)) (ξ, η, u) v =
      χ u * fderiv ℝ (kernelUncurry Ψ) (ξ, η, u) v +
        Ψ ξ η u * fderiv ℝ χ u v.2.2 := by
  have hs : HasFDerivAt (fun z : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ) => z.2.2)
      ((ContinuousLinearMap.snd ℝ (Fin N → ℝ) (Fin N → ℝ)).comp
        (ContinuousLinearMap.snd ℝ (Fin N → ℝ) ((Fin N → ℝ) × (Fin N → ℝ)))) (ξ, η, u) :=
    (hasFDerivAt_snd (p := (η, u))).comp (ξ, η, u) hasFDerivAt_snd
  have h1 := ((hχ.differentiable one_ne_zero u).hasFDerivAt.comp (ξ, η, u) hs)
  have h2 := (kernelUncurry_differentiableAt (ξ := ξ) (η := η) hΨ hu).hasFDerivAt
  have h3 : HasFDerivAt (kernelUncurry (fun ξ η u => χ u * Ψ ξ η u)) _ (ξ, η, u) := h1.mul h2
  rw [h3.fderiv]
  simp

/-- The weighted bounds are stable under multiplication by a `C¹` function of the group
variable (a radial cutoff; BB pp. 569–571, Prop 11.32). -/
theorem HasWeightedBounds.cutoff_mul {χ : (Fin N → ℝ) → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hΨ : ContDiffOn ℝ 1 (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (h : HasWeightedBounds G d Ψ) :
    HasWeightedBounds G d (fun ξ η u => χ u * Ψ ξ η u) := by
  intro L hL R
  set Rm : ℝ := max R 1 with hRm
  have hRm1 : 1 ≤ Rm := le_max_right _ _
  obtain ⟨M, hM0, hM⟩ := h L hL R
  have hB : IsCompact {u : Fin N → ℝ | kgauge G u ≤ R} :=
    G2.isCompact_gauge_le (G2.isHomogeneousGauge_max G) R
  obtain ⟨Mχ, hMχ⟩ := hB.exists_bound_of_continuousOn hχ.continuous.continuousOn
  obtain ⟨Dχ, hDχ⟩ := hB.exists_bound_of_continuousOn
    (hχ.continuous_fderiv one_ne_zero).continuousOn
  set S : ℝ := ∑ j : Fin N, Rm ^ G.weight j with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun j _ => by positivity)
  have hSj : ∀ j : Fin N, Rm ^ G.weight j ≤ S :=
    fun j => Finset.single_le_sum (f := fun j : Fin N => Rm ^ G.weight j)
      (fun j _ => by positivity) (Finset.mem_univ j)
  set Mχ' : ℝ := max |Mχ| 0 with hMχ'
  set Dχ' : ℝ := max |Dχ| 0 with hDχ'
  have hMχ0 : 0 ≤ Mχ' := le_max_right _ _
  have hDχ0 : 0 ≤ Dχ' := le_max_right _ _
  refine ⟨M * (Mχ' + Dχ' * S), by positivity, ?_⟩
  intro ξ hξ η hη u hu hR
  obtain ⟨hsize, hpar, hu'⟩ := hM ξ hξ η hη u hu hR
  have hρ : 0 < kgauge G u := kgauge_pos G hu
  have hχb : |χ u| ≤ Mχ' := by
    have := hMχ u hR
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_abs_self _).trans (le_max_left _ _))
  have hdχb : ‖fderiv ℝ χ u‖ ≤ Dχ' :=
    (hDχ u hR).trans ((le_abs_self _).trans (le_max_left _ _))
  have hpd : 0 < kgauge G u ^ d := zpow_pos hρ d
  have hbase : M * kgauge G u ^ d * Mχ' ≤ M * (Mχ' + Dχ' * S) * kgauge G u ^ d := by
    have : 0 ≤ M * kgauge G u ^ d * (Dχ' * S) := by positivity
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · calc |χ u * Ψ ξ η u| = |χ u| * |Ψ ξ η u| := abs_mul _ _
      _ ≤ Mχ' * (M * kgauge G u ^ d) := mul_le_mul hχb hsize (abs_nonneg _) hMχ0
      _ ≤ _ := by
        have : 0 ≤ M * kgauge G u ^ d * (Dχ' * S) := by positivity
        nlinarith
  · intro a
    have hp := hpar a
    change |fderiv ℝ (kernelUncurry (fun ξ η u => χ u * Ψ ξ η u)) (ξ, η, u) (a, 0, 0)| ≤ _
    rw [fderiv_cutoff_mul hχ hΨ hu]
    simp only [map_zero, mul_zero, add_zero]
    rw [abs_mul]
    calc |χ u| * |fderiv ℝ (kernelUncurry Ψ) (ξ, η, u) (a, 0, 0)|
        ≤ Mχ' * (M * kgauge G u ^ d * ‖a‖) := mul_le_mul hχb hp (abs_nonneg _) hMχ0
      _ ≤ M * (Mχ' + Dχ' * S) * kgauge G u ^ d * ‖a‖ := by
        have h0 : 0 ≤ ‖a‖ := norm_nonneg a
        have : 0 ≤ M * kgauge G u ^ d * (Dχ' * S) := by positivity
        nlinarith [mul_nonneg this h0]
  · intro j
    rw [fderiv_cutoff_mul hχ hΨ hu]
    set P : ℝ := kgauge G u ^ (d - (G.weight j : ℤ)) with hP
    have hPpos : 0 < P := zpow_pos hρ _
    have hρd : kgauge G u ^ d = kgauge G u ^ G.weight j * P := by
      rw [hP, ← zpow_natCast, ← zpow_add₀ hρ.ne']
      congr 1
      ring
    have hρw : kgauge G u ^ G.weight j ≤ S := (pow_le_pow_left₀ hρ.le (hR.trans (le_max_left _ _))
      _).trans (hSj j)
    have he : ‖(Pi.single j (1 : ℝ) : Fin N → ℝ)‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun i => ?_)
      by_cases hij : i = j <;> simp [hij]
    have hdχe : |fderiv ℝ χ u (Pi.single j 1)| ≤ Dχ' := by
      have := (fderiv ℝ χ u).le_opNorm (Pi.single j (1 : ℝ))
      rw [Real.norm_eq_abs] at this
      exact this.trans ((mul_le_mul hdχb he (norm_nonneg _) hDχ0).trans (by rw [mul_one]))
    have hM' : |fderiv ℝ (kernelUncurry Ψ) (ξ, η, u) (0, 0, Pi.single j 1)| ≤ M * P := hu' j
    have hΨb : |Ψ ξ η u| ≤ M * (S * P) := by
      refine hsize.trans ?_
      rw [hρd]
      have := mul_le_mul_of_nonneg_right hρw hPpos.le
      nlinarith [mul_le_mul_of_nonneg_left this hM0]
    calc |χ u * fderiv ℝ (kernelUncurry Ψ) (ξ, η, u) (0, 0, Pi.single j 1) +
          Ψ ξ η u * fderiv ℝ χ u (Pi.single j 1)|
        ≤ |χ u * fderiv ℝ (kernelUncurry Ψ) (ξ, η, u) (0, 0, Pi.single j 1)| +
          |Ψ ξ η u * fderiv ℝ χ u (Pi.single j 1)| := abs_add_le _ _
      _ ≤ Mχ' * (M * P) + (M * (S * P)) * Dχ' := by
        refine add_le_add ?_ ?_
        · rw [abs_mul]
          exact mul_le_mul hχb hM' (abs_nonneg _) hMχ0
        · rw [abs_mul]
          exact mul_le_mul hΨb hdχe (abs_nonneg _) (by positivity)
      _ = M * (Mχ' + Dχ' * S) * P := by ring

/-- A radial cutoff `φ ∘ ν`, with `ν` a smooth homogeneous norm and `φ` of class `C¹` and
constant near `0`, is `C¹` on the whole space (`ν` is smooth only off the origin, but `φ ∘ ν` is
constant near it). This is the cutoff hypothesis `hχ` of the kernel estimates. -/
theorem contDiff_radial_cutoff {G : HomogeneousGroup N} (ν : G2.HomogeneousNorm G)
    (hν : ν.Smooth) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {ε c : ℝ} (hε : 0 < ε)
    (hφc : ∀ t : ℝ, 0 ≤ t → t < ε → φ t = c) : ContDiff ℝ 1 (fun u => φ (ν u)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have hν0 : ν 0 = 0 := (ν.gauge.2.2.1 0).mpr rfl
    have hcont : ContinuousAt ν 0 := ν.gauge.1.continuousAt
    have hev : ∀ᶠ u in 𝓝 (0 : Fin N → ℝ), ν u < ε :=
      hcont.eventually (gt_mem_nhds (by rw [hν0]; exact hε))
    have : (fun u => φ (ν u)) =ᶠ[𝓝 0] fun _ => c :=
      hev.mono (fun u hu => hφc _ (ν.gauge.2.1 u) hu)
    exact contDiffAt_const.congr_of_eventuallyEq this
  · have hxn : x ∈ ({0}ᶜ : Set (Fin N → ℝ)) := hx
    have hν' : ContDiffAt ℝ 1 ν x :=
      (hν.contDiffAt (isOpen_compl_singleton.mem_nhds hxn)).of_le (by simp)
    exact hφ.contDiffAt.comp x hν'

end RothschildStein.P1
