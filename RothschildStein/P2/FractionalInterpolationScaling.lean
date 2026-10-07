-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.CutoffsHomogeneous
public import RothschildStein.G2.Gauge
public import RothschildStein.P1.KernelEstimatesHomogeneous

/-!
# Hölder interpolation: scaling bounds for homogeneous kernel families

A family `W(ξ, η, u)`, smooth off `u = 0` and homogeneous of integer degree `d` in `u` for the
model dilations, has iterated derivatives (in all of `(ξ, η, u)`) of size
`‖D^j W(ξ, η, u)‖ ≤ S ν(u)^d (1 + ‖δ_{1/ν(u)}‖)^j`, uniformly for `(ξ, η)` in a compact set
(`exists_iteratedFDeriv_scaling_bound`): scale to the unit sphere `ν(u) = 1`, where continuity on a
compact set bounds `D^j W`, and use `W ∘ Λ_t = t^d W` with `Λ_t = (id, id, δ_t)` linear. This is the
explicit-scale form of BB pp. 569-571, Prop 11.32 ("scale to the unit sphere"), needed to track the
dependence on the cutoff scale `h` of the far kernel (BB pp. 594-595, Lem 11.51).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

variable {N : ℕ} (G : HomogeneousGroup N)

/-- A bound for the operator norm of the dilation `δ_t`: `∑_j |t|^{w_j}`. -/
def dilNorm (t : ℝ) : ℝ := ∑ j, |t| ^ G.weight j

theorem dilNorm_nonneg (t : ℝ) : 0 ≤ dilNorm G t :=
  Finset.sum_nonneg fun _ _ => pow_nonneg (abs_nonneg _) _

theorem norm_dilCLM_le (t : ℝ) : ‖dilCLM G t‖ ≤ dilNorm G t := by
  refine ContinuousLinearMap.opNorm_le_bound _ (dilNorm_nonneg G t) fun u => ?_
  rw [dilCLM_apply]
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (dilNorm_nonneg G t) (norm_nonneg _))).2 fun j => ?_
  simp only [HomogeneousGroup.dilate, coordinateDilation, Real.norm_eq_abs, abs_mul, abs_pow]
  have h1 : |t| ^ G.weight j ≤ dilNorm G t :=
    Finset.single_le_sum (f := fun j => |t| ^ G.weight j) (fun _ _ => pow_nonneg (abs_nonneg _) _)
      (Finset.mem_univ j)
  have h2 : |u j| ≤ ‖u‖ := by simpa using norm_le_pi_norm u j
  exact mul_le_mul h1 h2 (abs_nonneg _) (dilNorm_nonneg G t)

/-- The space `(ξ, η, u)` of kernel families. -/
abbrev Z3 (N : ℕ) : Type := (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)

/-- The map `Λ_t(ξ, η, u) = (ξ, η, δ_t u)` as a continuous linear map. -/
def lamCLM (t : ℝ) : Z3 N →L[ℝ] Z3 N :=
  (ContinuousLinearMap.id ℝ (Fin N → ℝ)).prodMap
    ((ContinuousLinearMap.id ℝ (Fin N → ℝ)).prodMap (dilCLM G t))

theorem lamCLM_apply (t : ℝ) (z : Z3 N) : lamCLM G t z = (z.1, z.2.1, G.dilate t z.2.2) := by
  show (z.1, z.2.1, dilCLM G t z.2.2) = _
  rw [dilCLM_apply]

theorem norm_lamCLM_le (t : ℝ) : ‖lamCLM G t‖ ≤ 1 + dilNorm G t := by
  have hd := dilNorm_nonneg G t
  refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun z => ?_
  rw [lamCLM_apply, Prod.norm_def, Prod.norm_def]
  have h1 : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
  have h2 : ‖z.2.1‖ ≤ ‖z‖ := (norm_fst_le z.2).trans (norm_snd_le z)
  have h4 : ‖z.2.2‖ ≤ ‖z‖ := (norm_snd_le z.2).trans (norm_snd_le z)
  have h3 : ‖G.dilate t z.2.2‖ ≤ dilNorm G t * ‖z‖ := by
    have := (dilCLM G t).le_opNorm z.2.2
    rw [dilCLM_apply] at this
    exact this.trans (mul_le_mul (norm_dilCLM_le G t) h4 (norm_nonneg _) hd)
  have hz := norm_nonneg z
  have e1 : ‖z‖ ≤ (1 + dilNorm G t) * ‖z‖ := by nlinarith
  have e2 : dilNorm G t * ‖z‖ ≤ (1 + dilNorm G t) * ‖z‖ := by nlinarith
  exact max_le (h1.trans e1) (max_le (h2.trans e1) (h3.trans e2))

/-- **Scaling bound for the iterated derivatives of a homogeneous family**: if `W` is
smooth off `u = 0` and homogeneous of degree `d` in `u`, then uniformly for `(ξ, η)` in a compact
set `L` and `u ≠ 0`,
`‖D^j W(ξ, η, u)‖ ≤ S ν(u)^d (1 + ‖δ_{1/ν(u)}‖)^j`. -/
theorem exists_iteratedFDeriv_scaling_bound {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    {W : Z3 N → ℝ} {d : ℤ} (hW : ContDiffOn ℝ (⊤ : ℕ∞) W {z | z.2.2 ≠ 0})
    (hhom : ∀ ξ η : Fin N → ℝ, ∀ t : ℝ, 0 < t → ∀ u : Fin N → ℝ, u ≠ 0 →
      W (ξ, η, G.dilate t u) = t ^ d * W (ξ, η, u))
    {L : Set ((Fin N → ℝ) × (Fin N → ℝ))} (hL : IsCompact L) (j : ℕ) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ z : Z3 N, (z.1, z.2.1) ∈ L → z.2.2 ≠ 0 →
      ‖iteratedFDeriv ℝ j W z‖ ≤ S * ν z.2.2 ^ d * (1 + dilNorm G (ν z.2.2)⁻¹) ^ j := by
  set 𝒰 : Set (Z3 N) := {z | z.2.2 ≠ 0} with h𝒰
  have hU : IsOpen 𝒰 :=
    (isOpen_compl_singleton (x := (0 : Fin N → ℝ))).preimage (continuous_snd.comp continuous_snd)
  have hsph : IsCompact {u : Fin N → ℝ | ν u = 1} :=
    (G2.isCompact_gauge_le hν 1).of_isClosed_subset (isClosed_eq hν.1 continuous_const)
      (fun u hu => le_of_eq hu)
  set Sph : Set (Z3 N) := (Homeomorph.prodAssoc _ _ _) '' (L ×ˢ {u | ν u = 1}) with hSph
  have hSphc : IsCompact Sph := (hL.prod hsph).image (Homeomorph.prodAssoc _ _ _).continuous
  have hSph𝒰 : Sph ⊆ 𝒰 := by
    rintro _ ⟨⟨⟨ξ, η⟩, u⟩, ⟨-, hu⟩, rfl⟩ hu0
    have h0 : u = 0 := hu0
    have h1 : ν u = 1 := hu
    rw [h0, (hν.2.2.1 0).mpr rfl] at h1
    norm_num at h1
  have hcont : ContinuousOn (iteratedFDeriv ℝ j W) 𝒰 :=
    ContinuousOn.continuousOn_iteratedFDeriv hW hU (by exact_mod_cast le_top)
  obtain ⟨S₀, hS₀⟩ := hSphc.exists_bound_of_continuousOn (hcont.mono hSph𝒰)
  refine ⟨max S₀ 0, le_max_right _ _, fun z hzL hz => ?_⟩
  set ρ : ℝ := ν z.2.2 with hρ
  have hρ0 : 0 < ρ := G2.gauge_pos hν hz
  set t : ℝ := ρ⁻¹ with ht
  have ht0 : 0 < t := inv_pos.mpr hρ0
  set z₁ : Z3 N := lamCLM G t z with hz₁
  have hz₁Sph : z₁ ∈ Sph := by
    refine ⟨((z.1, z.2.1), G.dilate t z.2.2), ⟨hzL, ?_⟩, rfl⟩
    show ν (G.dilate t z.2.2) = 1
    rw [hν.2.2.2 t ht0, ← hρ, ht, inv_mul_cancel₀ hρ0.ne']
  have hz₁U : z₁ ∈ 𝒰 := hSph𝒰 hz₁Sph
  have hzU : z ∈ 𝒰 := hz
  have hlamU : IsOpen (lamCLM G t ⁻¹' 𝒰) := hU.preimage (lamCLM G t).continuous
  have hWj : ContDiffOn ℝ (j : WithTop ℕ∞) W 𝒰 := hW.of_le (by exact_mod_cast le_top)
  have hzU' : z ∈ lamCLM G t ⁻¹' 𝒰 := hz₁U
  -- the chain rule for the linear map
  have h1 : iteratedFDeriv ℝ j (fun y => W (lamCLM G t y)) z =
      (iteratedFDeriv ℝ j W z₁).compContinuousLinearMap fun _ => lamCLM G t := by
    have := ContinuousLinearMap.iteratedFDerivWithin_comp_right (lamCLM G t) hWj
      hU.uniqueDiffOn hlamU.uniqueDiffOn (x := z) hz₁U le_rfl
    rw [iteratedFDerivWithin_of_isOpen j hlamU hzU', iteratedFDerivWithin_of_isOpen j hU hz₁U]
      at this
    exact this
  -- the homogeneity
  have h2 : (fun y => W (lamCLM G t y)) =ᶠ[𝓝 z] fun y => t ^ d • W y := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    rw [lamCLM_apply]
    exact hhom y.1 y.2.1 t ht0 y.2.2 hy
  have h3 : iteratedFDeriv ℝ j (fun y => W (lamCLM G t y)) z = t ^ d • iteratedFDeriv ℝ j W z := by
    rw [(h2.iteratedFDeriv ℝ j).self_of_nhds]
    exact iteratedFDeriv_const_smul_apply' (hW.contDiffAt (hU.mem_nhds hzU) |>.of_le
      (by exact_mod_cast le_top))
  have e : ρ ^ d * t ^ d = 1 := by
    rw [ht, inv_zpow', ← zpow_add₀ hρ0.ne', add_neg_cancel, zpow_zero]
  have h4 : iteratedFDeriv ℝ j W z =
      ρ ^ d • (iteratedFDeriv ℝ j W z₁).compContinuousLinearMap fun _ => lamCLM G t := by
    calc iteratedFDeriv ℝ j W z = (ρ ^ d * t ^ d) • iteratedFDeriv ℝ j W z := by rw [e, one_smul]
      _ = ρ ^ d • (t ^ d • iteratedFDeriv ℝ j W z) := by rw [mul_smul]
      _ = _ := by rw [← h3, h1]
  have hb := ContinuousMultilinearMap.norm_compContinuousLinearMap_le (iteratedFDeriv ℝ j W z₁)
    (fun _ : Fin j => lamCLM G t)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hb
  have hD : ‖iteratedFDeriv ℝ j W z₁‖ ≤ max S₀ 0 := (hS₀ z₁ hz₁Sph).trans (le_max_left _ _)
  have hΛ : ‖lamCLM G t‖ ≤ 1 + dilNorm G t := norm_lamCLM_le G t
  have hρd : 0 < ρ ^ d := zpow_pos hρ0 d
  rw [h4, norm_smul, Real.norm_eq_abs, abs_of_pos hρd]
  calc ρ ^ d * ‖(iteratedFDeriv ℝ j W z₁).compContinuousLinearMap fun _ => lamCLM G t‖
      ≤ ρ ^ d * (‖iteratedFDeriv ℝ j W z₁‖ * ‖lamCLM G t‖ ^ j) :=
        mul_le_mul_of_nonneg_left hb hρd.le
    _ ≤ ρ ^ d * (max S₀ 0 * (1 + dilNorm G t) ^ j) := by
        refine mul_le_mul_of_nonneg_left ?_ hρd.le
        exact mul_le_mul hD (pow_le_pow_left₀ (norm_nonneg _) hΛ j) (by positivity)
          ((norm_nonneg _).trans hD)
    _ = max S₀ 0 * ρ ^ d * (1 + dilNorm G ρ⁻¹) ^ j := by rw [ht]; ring

end RothschildStein.P2
