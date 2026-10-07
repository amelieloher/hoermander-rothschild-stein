-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import RothschildStein.G2.Gauge

/-!
# Homogeneous kernel estimates: scaling to the unit sphere

For a homogeneous group `G` and a family `Ψ ξ η u`, jointly `C¹` off `u = 0` and homogeneous of
integer degree `d` in `u` for the model dilations, this file proves the weighted size bounds
`|Ψ| ≤ M ‖u‖^d`, `|∂_ξ Ψ| ≤ M ‖u‖^d`, `|∂_{u_j} Ψ| ≤ M ‖u‖^(d - w_j)` on compact parameter sets
(BB pp. 569–571, Prop 11.32: "scale to the unit sphere"). Here `‖·‖` is the coordinate max gauge.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RothschildStein.P1

section Dilation

variable {N : ℕ} (G : HomogeneousGroup N)

/-- The coordinate max gauge of a homogeneous group (BB Prop 3.10, p. 100). -/
abbrev kgauge (u : Fin N → ℝ) : ℝ := rsGauge G.weight G.weight_pos u

/-- The coordinate formula of the model dilations. -/
theorem kdilate_apply (t : ℝ) (u : Fin N → ℝ) (j : Fin N) :
    G.dilate t u j = t ^ G.weight j * u j := rfl

/-- Dilations compose multiplicatively. -/
theorem kdilate_dilate (t s : ℝ) (u : Fin N → ℝ) :
    G.dilate t (G.dilate s u) = G.dilate (t * s) u := by
  ext j
  simp [kdilate_apply, mul_pow, mul_assoc]

/-- The unit dilation is the identity. -/
theorem kdilate_one (u : Fin N → ℝ) : G.dilate 1 u = u := by
  ext j
  simp [kdilate_apply]

/-- Dilations commute with negation. -/
theorem kdilate_neg (t : ℝ) (u : Fin N → ℝ) : G.dilate t (-u) = -G.dilate t u := by
  ext j
  simp [kdilate_apply]

/-- Dilation of a coordinate vector. -/
theorem kdilate_single (t : ℝ) (j : Fin N) :
    G.dilate t (Pi.single j (1 : ℝ)) = t ^ G.weight j • Pi.single j (1 : ℝ) := by
  ext i
  by_cases h : i = j
  · subst h; simp [kdilate_apply]
  · simp [kdilate_apply, h]

/-- Positive dilations of nonzero points are nonzero. -/
theorem kdilate_ne_zero {t : ℝ} (ht : 0 < t) {u : Fin N → ℝ} (hu : u ≠ 0) :
    G.dilate t u ≠ 0 := by
  intro h
  apply hu
  have := kdilate_dilate G t⁻¹ t u
  rw [h] at this
  have h0 : G.dilate t⁻¹ (0 : Fin N → ℝ) = 0 := by ext j; simp [kdilate_apply]
  rw [h0, inv_mul_cancel₀ ht.ne', kdilate_one] at this
  exact this.symm

/-- The max gauge is homogeneous of degree one. -/
theorem kgauge_dilate {t : ℝ} (ht : 0 < t) (u : Fin N → ℝ) :
    kgauge G (G.dilate t u) = t * kgauge G u := G2.gauge_dilate G t ht u

/-- The max gauge is positive off zero. -/
theorem kgauge_pos {u : Fin N → ℝ} (hu : u ≠ 0) : 0 < kgauge G u :=
  G2.gauge_pos (G2.isHomogeneousGauge_max G) hu

/-- The max gauge is nonnegative. -/
theorem kgauge_nonneg (u : Fin N → ℝ) : 0 ≤ kgauge G u := G2.gauge_nonneg G u

/-- The max gauge is even. -/
theorem kgauge_neg (u : Fin N → ℝ) : kgauge G (-u) = kgauge G u := G2.gauge_neg G u

/-- The max gauge vanishes exactly at zero. -/
theorem kgauge_eq_zero_iff (u : Fin N → ℝ) : kgauge G u = 0 ↔ u = 0 := G2.gauge_eq_zero_iff G u

/-- Coordinates are bounded by powers of the max gauge. -/
theorem abs_apply_le_kgauge_pow (u : Fin N → ℝ) (j : Fin N) :
    |u j| ≤ kgauge G u ^ G.weight j := by
  have h := G2.coordinate_root_le_gauge G u j
  have hr : (0 : ℝ) ≤ kgauge G u := kgauge_nonneg G u
  have := (Real.rpow_inv_le_iff_of_pos (abs_nonneg (u j)) hr
    (Nat.cast_pos.mpr (G.weight_pos j))).mp (by simpa only [Real.rpow_eq_pow] using h)
  simpa only [Real.rpow_natCast] using this

/-- Every nonzero point is a dilate of a point of the unit gauge sphere. -/
theorem exists_unit_sphere {u : Fin N → ℝ} (hu : u ≠ 0) :
    ∃ u₁ : Fin N → ℝ, kgauge G u₁ = 1 ∧ u = G.dilate (kgauge G u) u₁ := by
  refine ⟨G.dilate (kgauge G u)⁻¹ u, G2.gauge_normalize (G2.isHomogeneousGauge_max G) hu, ?_⟩
  exact (G2.dilate_normalize (G2.isHomogeneousGauge_max G) hu).symm

/-- The coordinate-wise dilation as a continuous linear map. -/
def kdilateCLM (t : ℝ) : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi (fun j => (t ^ G.weight j) • ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin N => ℝ) j)

/-- The continuous linear dilation map agrees with the group dilation. -/
theorem kdilateCLM_apply (t : ℝ) (u : Fin N → ℝ) : kdilateCLM G t u = G.dilate t u := by
  ext j
  simp [kdilateCLM, kdilate_apply]

end Dilation

section Homogeneous

variable {N : ℕ} (G : HomogeneousGroup N)

/-- The jointly-uncurried form `(ξ, η, u) ↦ Ψ ξ η u` of a family of kernels. -/
def kernelUncurry (Ψ : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (z : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)) : ℝ := Ψ z.1 z.2.1 z.2.2

/-- The domain `{u ≠ 0}` of a homogeneous kernel family is open. -/
theorem isOpen_kernelDomain :
    IsOpen {z : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ) | z.2.2 ≠ 0} :=
  (isOpen_compl_singleton (x := (0 : Fin N → ℝ))).preimage (continuous_snd.comp continuous_snd)

variable {G}
variable {Ψ : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) → ℝ} {d : ℤ}

/-- A kernel family that is `C¹` off `u = 0` is differentiable there. -/
theorem kernelUncurry_differentiableAt
    (hΨ : ContDiffOn ℝ 1 (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    {ξ η u : Fin N → ℝ} (hu : u ≠ 0) : DifferentiableAt ℝ (kernelUncurry Ψ) (ξ, η, u) :=
  (hΨ.differentiableOn one_ne_zero).differentiableAt
    (isOpen_kernelDomain.mem_nhds (show (ξ, η, u).2.2 ≠ 0 from hu))

/-- Parameter derivatives of a homogeneous family are homogeneous of the same degree. -/
theorem fderiv_param_homogeneous
    (hΨ : ContDiffOn ℝ 1 (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (hhom : ∀ ξ η : Fin N → ℝ, ∀ t : ℝ, 0 < t → ∀ u : Fin N → ℝ, u ≠ 0 →
      Ψ ξ η (G.dilate t u) = t ^ d * Ψ ξ η u)
    (ξ η : Fin N → ℝ) {u : Fin N → ℝ} (hu : u ≠ 0) {t : ℝ} (ht : 0 < t) (a : Fin N → ℝ) :
    fderiv ℝ (kernelUncurry Ψ) (ξ, η, G.dilate t u) (a, 0, 0) =
      t ^ d * fderiv ℝ (kernelUncurry Ψ) (ξ, η, u) (a, 0, 0) := by
  have hA : ∀ y : Fin N → ℝ, HasFDerivAt (fun x : Fin N → ℝ => (x, η, y))
      ((ContinuousLinearMap.id ℝ (Fin N → ℝ)).prod (0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) × (Fin N → ℝ)))
      ξ := fun y => (hasFDerivAt_id ξ).prodMk (hasFDerivAt_const ((η, y) : (Fin N → ℝ) × (Fin N → ℝ)) ξ)
  have hu' : G.dilate t u ≠ 0 := kdilate_ne_zero G ht hu
  have h1 := (kernelUncurry_differentiableAt hΨ hu').hasFDerivAt.comp ξ (hA (G.dilate t u))
  have h2 := ((kernelUncurry_differentiableAt hΨ hu).hasFDerivAt.comp ξ (hA u)).const_mul (t ^ d)
  have hfun : (fun x : Fin N → ℝ => kernelUncurry Ψ (x, η, G.dilate t u)) =
      fun x => t ^ d * (kernelUncurry Ψ ∘ fun x : Fin N → ℝ => (x, η, u)) x := by
    funext x
    exact hhom x η t ht u hu
  have h1' : HasFDerivAt (fun x : Fin N → ℝ => kernelUncurry Ψ (x, η, G.dilate t u))
      ((fderiv ℝ (kernelUncurry Ψ) (ξ, η, G.dilate t u)).comp
        ((ContinuousLinearMap.id ℝ (Fin N → ℝ)).prod
          (0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) × (Fin N → ℝ)))) ξ := h1
  rw [hfun] at h1'
  have := congrArg (fun L => L a) (h1'.unique h2)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply,
    smul_apply, smul_eq_mul] at this
  exact this

/-- The `u`-derivative of a homogeneous family: dilating the point and the direction. -/
theorem fderiv_u_homogeneous
    (hΨ : ContDiffOn ℝ 1 (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (hhom : ∀ ξ η : Fin N → ℝ, ∀ t : ℝ, 0 < t → ∀ u : Fin N → ℝ, u ≠ 0 →
      Ψ ξ η (G.dilate t u) = t ^ d * Ψ ξ η u)
    (ξ η : Fin N → ℝ) {u : Fin N → ℝ} (hu : u ≠ 0) {t : ℝ} (ht : 0 < t) (v : Fin N → ℝ) :
    fderiv ℝ (kernelUncurry Ψ) (ξ, η, G.dilate t u) (0, 0, G.dilate t v) =
      t ^ d * fderiv ℝ (kernelUncurry Ψ) (ξ, η, u) (0, 0, v) := by
  have hB : HasFDerivAt (fun y : Fin N → ℝ => (ξ, η, G.dilate t y))
      ((0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)).prod
        ((0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)).prod (kdilateCLM G t))) u := by
    have hd : HasFDerivAt (G.dilate t) (kdilateCLM G t) u := by
      have := (kdilateCLM G t).hasFDerivAt (x := u)
      have hf : (⇑(kdilateCLM G t)) = G.dilate t := funext (kdilateCLM_apply G t)
      rwa [hf] at this
    exact (hasFDerivAt_const ξ u).prodMk ((hasFDerivAt_const η u).prodMk hd)
  have hB' : HasFDerivAt (fun y : Fin N → ℝ => (ξ, η, y))
      ((0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)).prod
        ((0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)).prod (ContinuousLinearMap.id ℝ (Fin N → ℝ)))) u :=
    (hasFDerivAt_const ξ u).prodMk ((hasFDerivAt_const η u).prodMk (hasFDerivAt_id u))
  have hu' : G.dilate t u ≠ 0 := kdilate_ne_zero G ht hu
  have h1 := (kernelUncurry_differentiableAt hΨ hu').hasFDerivAt.comp u hB
  have h2 := ((kernelUncurry_differentiableAt hΨ hu).hasFDerivAt.comp u hB').const_mul (t ^ d)
  have hev : (fun y : Fin N → ℝ => kernelUncurry Ψ (ξ, η, G.dilate t y)) =ᶠ[𝓝 u]
      fun y => t ^ d * (kernelUncurry Ψ ∘ fun y : Fin N → ℝ => (ξ, η, y)) y := by
    filter_upwards [(isOpen_compl_singleton (x := (0 : Fin N → ℝ))).mem_nhds hu] with y hy
    exact hhom ξ η t ht y hy
  have h2' := h2.congr_of_eventuallyEq hev
  have h1' : HasFDerivAt (fun y : Fin N → ℝ => kernelUncurry Ψ (ξ, η, G.dilate t y))
      ((fderiv ℝ (kernelUncurry Ψ) (ξ, η, G.dilate t u)).comp
        ((0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)).prod
          ((0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)).prod (kdilateCLM G t)))) u := h1
  have := congrArg (fun L => L v) (h1'.unique h2')
  simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    kdilateCLM_apply] using this

/-- Weighted size bounds, uniform on a compact parameter set `L × L` and `ρ(u) ≤ R`:
size `M ρ^d`, parameter derivative `M ρ^d`, and `∂_{u_j}` bound `M ρ^(d - w_j)`
(BB pp. 569–571, Prop 11.32). -/
def HasWeightedBounds (G : HomogeneousGroup N)
    (d : ℤ) (Ψ : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) → ℝ) : Prop :=
  ∀ L : Set (Fin N → ℝ), IsCompact L → ∀ R : ℝ, ∃ M : ℝ, 0 ≤ M ∧
    ∀ ξ ∈ L, ∀ η ∈ L, ∀ u : Fin N → ℝ, u ≠ 0 → kgauge G u ≤ R →
      |Ψ ξ η u| ≤ M * kgauge G u ^ d ∧
      (∀ a : Fin N → ℝ,
        |fderiv ℝ (kernelUncurry Ψ) (ξ, η, u) (a, 0, 0)| ≤ M * kgauge G u ^ d * ‖a‖) ∧
      (∀ j : Fin N, |fderiv ℝ (kernelUncurry Ψ) (ξ, η, u) (0, 0, Pi.single j 1)| ≤
        M * kgauge G u ^ (d - (G.weight j : ℤ)))

/-- Scaling to the unit sphere: a family that is `C¹` off `u = 0` and homogeneous of
degree `d` has the weighted bounds `HasWeightedBounds` (BB pp. 569–571, Prop 11.32). -/
theorem hasWeightedBounds_of_homogeneous
    (hΨ : ContDiffOn ℝ 1 (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (hhom : ∀ ξ η : Fin N → ℝ, ∀ t : ℝ, 0 < t → ∀ u : Fin N → ℝ, u ≠ 0 →
      Ψ ξ η (G.dilate t u) = t ^ d * Ψ ξ η u) :
    HasWeightedBounds G d Ψ := by
  intro L hL R
  have hS : IsCompact (L ×ˢ (L ×ˢ {u : Fin N → ℝ | kgauge G u = 1})) :=
    hL.prod (hL.prod (G2.isCompact_max_unit G))
  have hsub : (L ×ˢ (L ×ˢ {u : Fin N → ℝ | kgauge G u = 1})) ⊆
      {z : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ) | z.2.2 ≠ 0} := by
    rintro ⟨ξ, η, u⟩ ⟨-, -, hu⟩ h0
    have : kgauge G u = 1 := hu
    have hz : u = 0 := h0
    rw [hz, (kgauge_eq_zero_iff G 0).mpr rfl] at this
    norm_num at this
  obtain ⟨M₀, hM₀⟩ := hS.exists_bound_of_continuousOn (hΨ.continuousOn.mono hsub)
  obtain ⟨M₁, hM₁⟩ := hS.exists_bound_of_continuousOn
    ((hΨ.continuousOn_fderiv_of_isOpen isOpen_kernelDomain le_rfl).mono hsub)
  set M : ℝ := max M₀ M₁ ⊔ 0 with hMdef
  refine ⟨M, le_max_right _ _, ?_⟩
  intro ξ hξ η hη u hu hR
  have key : ∀ ρ : ℝ, 0 < ρ → ∀ u₁ : Fin N → ℝ, kgauge G u₁ = 1 →
      |Ψ ξ η (G.dilate ρ u₁)| ≤ M * ρ ^ d ∧
      (∀ a : Fin N → ℝ, |fderiv ℝ (kernelUncurry Ψ) (ξ, η, G.dilate ρ u₁) (a, 0, 0)| ≤
        M * ρ ^ d * ‖a‖) ∧
      (∀ j : Fin N, |fderiv ℝ (kernelUncurry Ψ) (ξ, η, G.dilate ρ u₁) (0, 0, Pi.single j 1)| ≤
        M * ρ ^ (d - (G.weight j : ℤ))) := by
    intro ρ hρ u₁ hu₁
    have hu₁ne : u₁ ≠ 0 := by
      intro h0
      rw [h0, (kgauge_eq_zero_iff G 0).mpr rfl] at hu₁
      norm_num at hu₁
    have hmem : (ξ, η, u₁) ∈ L ×ˢ (L ×ˢ {u : Fin N → ℝ | kgauge G u = 1}) := ⟨hξ, hη, hu₁⟩
    have hMa : |Ψ ξ η u₁| ≤ M := by
      have := hM₀ _ hmem
      simp only [Real.norm_eq_abs, kernelUncurry] at this
      exact this.trans ((le_max_left _ _).trans (le_max_left _ _))
    have hMb : ‖fderiv ℝ (kernelUncurry Ψ) (ξ, η, u₁)‖ ≤ M :=
      (hM₁ _ hmem).trans ((le_max_right _ _).trans (le_max_left _ _))
    have hpos : 0 < ρ ^ d := zpow_pos hρ d
    refine ⟨?_, ?_, ?_⟩
    · rw [hhom ξ η ρ hρ u₁ hu₁ne, abs_mul, abs_of_pos hpos, mul_comm]
      exact mul_le_mul_of_nonneg_right hMa hpos.le
    · intro a
      rw [fderiv_param_homogeneous hΨ hhom ξ η hu₁ne hρ a, abs_mul, abs_of_pos hpos]
      have h1 : |fderiv ℝ (kernelUncurry Ψ) (ξ, η, u₁) (a, 0, 0)| ≤ M * ‖a‖ := by
        have := (fderiv ℝ (kernelUncurry Ψ) (ξ, η, u₁)).le_opNorm (a, 0, 0)
        have hn : ‖((a, 0, 0) : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ))‖ ≤ ‖a‖ := by
          simp [Prod.norm_def]
        rw [Real.norm_eq_abs] at this
        exact this.trans (mul_le_mul hMb hn (norm_nonneg _) (norm_nonneg _ |>.trans hMb |> fun h => h))
      calc ρ ^ d * |fderiv ℝ (kernelUncurry Ψ) (ξ, η, u₁) (a, 0, 0)|
          ≤ ρ ^ d * (M * ‖a‖) := mul_le_mul_of_nonneg_left h1 hpos.le
        _ = M * ρ ^ d * ‖a‖ := by ring
    · intro j
      have h := fderiv_u_homogeneous hΨ hhom ξ η hu₁ne hρ (Pi.single j (1 : ℝ))
      rw [kdilate_single] at h
      have hsm : ((0 : Fin N → ℝ), (0 : Fin N → ℝ), ρ ^ G.weight j • (Pi.single j (1 : ℝ) : Fin N → ℝ)) =
          ρ ^ G.weight j • ((0 : Fin N → ℝ), (0 : Fin N → ℝ), (Pi.single j (1 : ℝ) : Fin N → ℝ)) := by
        simp
      rw [hsm, map_smul, smul_eq_mul] at h
      have hw : 0 < ρ ^ G.weight j := pow_pos hρ _
      have hX : fderiv ℝ (kernelUncurry Ψ) (ξ, η, G.dilate ρ u₁) (0, 0, Pi.single j 1) =
          ρ ^ (d - (G.weight j : ℤ)) *
            fderiv ℝ (kernelUncurry Ψ) (ξ, η, u₁) (0, 0, Pi.single j 1) := by
        rw [zpow_sub₀ hρ.ne', zpow_natCast]
        field_simp
        linarith
      rw [hX, abs_mul, abs_of_pos (zpow_pos hρ _), mul_comm]
      have h1 : |fderiv ℝ (kernelUncurry Ψ) (ξ, η, u₁) (0, 0, Pi.single j 1)| ≤ M := by
        have := (fderiv ℝ (kernelUncurry Ψ) (ξ, η, u₁)).le_opNorm (0, 0, Pi.single j 1)
        have hn : ‖((0, 0, Pi.single j (1 : ℝ)) : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ))‖ ≤ 1 := by
          simp only [Prod.norm_def, norm_zero]
          refine max_le zero_le_one (max_le zero_le_one ?_)
          refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun i => ?_)
          by_cases hij : i = j <;> simp [hij]
        rw [Real.norm_eq_abs] at this
        calc _ ≤ ‖fderiv ℝ (kernelUncurry Ψ) (ξ, η, u₁)‖ * 1 :=
              this.trans (mul_le_mul_of_nonneg_left hn (norm_nonneg _))
          _ ≤ M := by rw [mul_one]; exact hMb
      exact mul_le_mul_of_nonneg_right h1 (zpow_pos hρ _).le
  obtain ⟨u₁, hu₁, hdec⟩ := exists_unit_sphere G hu
  have hρ : 0 < kgauge G u := kgauge_pos G hu
  have := key (kgauge G u) hρ u₁ hu₁
  rw [← hdec] at this
  exact this


/-- A continuous field homogeneous of weight `-a` in the sense of the model fields
(`Y (δ_t u) = t^(-a) δ_t (Y u)`) has coordinates bounded by `M ρ^(w_j - a)`, by scaling to the
unit sphere (BB p. 569, proof of Prop 11.32). -/
theorem exists_field_homogeneous_bound (G : HomogeneousGroup N) (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (a : ℕ) (hY : Continuous Y)
    (hhom : ∀ t : ℝ, 0 < t → ∀ u, Y (G.dilate t u) = t ^ (-(a : ℤ)) • G.dilate t (Y u)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : Fin N → ℝ, u ≠ 0 → ∀ j : Fin N,
      |Y u j| ≤ M * kgauge G u ^ ((G.weight j : ℤ) - a) := by
  obtain ⟨M₀, hM₀⟩ := (G2.isCompact_max_unit G).exists_bound_of_continuousOn hY.continuousOn
  refine ⟨max M₀ 0, le_max_right _ _, fun u hu j => ?_⟩
  have key : ∀ ρ : ℝ, 0 < ρ → ∀ u₁ : Fin N → ℝ, kgauge G u₁ = 1 →
      |Y (G.dilate ρ u₁) j| ≤ max M₀ 0 * ρ ^ ((G.weight j : ℤ) - a) := by
    intro ρ hρ u₁ hu₁
    have hb : |Y u₁ j| ≤ max M₀ 0 := by
      have h1 : ‖Y u₁‖ ≤ M₀ := hM₀ u₁ hu₁
      have h2 := norm_le_pi_norm (Y u₁) j
      rw [Real.norm_eq_abs] at h2
      exact (h2.trans h1).trans (le_max_left _ _)
    rw [hhom ρ hρ]
    simp only [Pi.smul_apply, smul_eq_mul, kdilate_apply, abs_mul]
    rw [abs_of_pos (zpow_pos hρ _), abs_of_pos (pow_pos hρ _), ← mul_assoc,
      ← zpow_natCast, ← zpow_add₀ hρ.ne']
    have : (-(a : ℤ) + (G.weight j : ℤ)) = (G.weight j : ℤ) - a := by ring
    rw [this, mul_comm (max M₀ 0)]
    exact mul_le_mul_of_nonneg_left hb (zpow_pos hρ _).le
  obtain ⟨u₁, hu₁, hdec⟩ := exists_unit_sphere G hu
  have := key (kgauge G u) (kgauge_pos G hu) u₁ hu₁
  rw [← hdec] at this
  exact this

section ZPow

/-- Integer powers are monotone in the base for nonnegative exponents. -/
theorem kzpow_le_of_nonneg {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) {p : ℤ} (hp : 0 ≤ p) :
    x ^ p ≤ y ^ p := zpow_le_zpow_left₀ hp hx.le hxy

/-- Integer powers are antitone in the base for nonpositive exponents. -/
theorem kzpow_le_of_nonpos {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) {p : ℤ} (hp : p ≤ 0) :
    y ^ p ≤ x ^ p := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = -(n : ℤ) := ⟨(-p).toNat, by omega⟩
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  exact inv_anti₀ (pow_pos hx n) (pow_le_pow_left₀ hx.le hxy n)

/-- Comparable quantities have comparable integer powers. -/
theorem kzpow_le_const_mul {c x y : ℝ} (hc : 1 ≤ c) (hx : 0 < x) (hy : 0 < y)
    (h1 : x ≤ c * y) (h2 : y ≤ c * x) (p : ℤ) : x ^ p ≤ c ^ p.natAbs * y ^ p := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  rcases le_total 0 p with hp | hp
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    simp only [zpow_natCast, Int.natAbs_natCast]
    rw [← mul_pow]
    exact pow_le_pow_left₀ hx.le h1 n
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = -(n : ℤ) := ⟨(-p).toNat, by omega⟩
    simp only [zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast]
    have h3 : y / c ≤ x := by rw [div_le_iff₀ hc0]; linarith
    have h4 : (y / c) ^ n ≤ x ^ n := pow_le_pow_left₀ (div_pos hy hc0).le h3 n
    calc (x ^ n)⁻¹ ≤ ((y / c) ^ n)⁻¹ := inv_anti₀ (pow_pos (div_pos hy hc0) n) h4
      _ = c ^ n * (y ^ n)⁻¹ := by rw [div_pow, inv_div]; field_simp

end ZPow

end Homogeneous

end RothschildStein.P1
