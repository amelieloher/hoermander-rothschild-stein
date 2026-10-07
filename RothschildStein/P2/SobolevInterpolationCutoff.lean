-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.Cutoffs
public import RothschildStein.P1.H2CertificateTruncation
public import RothschildStein.P1.KernelEstimatesChart
public import RothschildStein.S.ClassicalWords

/-!
# Sobolev interpolation: the cutoff `φ_ε(ξ, ·)` centred at the output point

The near/far splitting of the kernel of `F_l` at scale `ε` uses the radial cutoff of the radial cutoff construction
centred at the output point `ξ`: `φ_ε(ξ, η) = radialCutoff C ν ξ (ε/4) ε η` (`= 1` for
`ν(Θ(ξ, η)) < ε/4`, `= 0` for `ν(Θ(ξ, η)) ≥ 5ε/8`). Through the comparison `θ₁ d̃ ≤ ν ∘ Θ ≤ θ₂ d̃`
(the comparison `ρ ≍ d̃`, `exists_rho_comparison`) the cutoff is expressed in the control distance
`d̃ = d̃(ξ, η)`: `φ_ε = 1` near every `η` with `d̃ < c₁ ε`, `φ_ε = 0` for `d̃ > c₂ ε`, and the weighted
jets satisfy `|X̃_i φ_ε| d̃^{w_i} ≤ B`, `|X̃_i² φ_ε| d̃^{2 w_i} ≤ B` with `B` independent of
`ε, ξ` (the derivative bounds for this cutoff on the annulus `d̃ ≈ ε`, `C (r - s)^{-wt}` with
`r - s = 3ε/4`). (BB pp. 578-583.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}

/-- The open `ρ`-ball `{η ∈ U | ν(Θ(ξ, η)) < r}` is open. -/
theorem isOpen_rhoBall_of (C : LiftedChart w s Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (r : ℝ) : IsOpen (rhoBall C ν ξ r) := by
  have hc : ContinuousOn (fun η : Fin (n + m) → ℝ => ν (C.Θ ξ η)) C.U :=
    ν.gauge.1.comp_continuousOn (C.theta_contDiffOn_right hξ).continuousOn
  exact hc.isOpen_inter_preimage C.isOpen_U (isOpen_Iio (a := r))

/-- The comparison `θ₁ d̃ ≤ ν(Θ(ξ, η)) ≤ θ₂ d̃` on `U × U` (the comparison `ρ ≍ d̃` of the lifted chart). -/
theorem exists_nu_theta_comparison (C : LiftedChart w s Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) :
    ∃ θ₁ θ₂ : ℝ, 0 < θ₁ ∧ θ₁ ≤ 1 ∧ 1 ≤ θ₂ ∧ ∀ ξ ∈ C.U, ∀ η ∈ C.U,
      θ₁ * (C.dl ξ η).toReal ≤ ν (C.Θ ξ η) ∧ ν (C.Θ ξ η) ≤ θ₂ * (C.dl ξ η).toReal := by
  obtain ⟨θ₁, θ₂, h1, h2, h3, hcomp⟩ := C.exists_rho_comparison ν.gauge
  refine ⟨θ₁, θ₂, h1, h2, h3, fun ξ hξ η hη => ?_⟩
  have h := hcomp ⟨η, hη⟩ ⟨ξ, hξ⟩
  have e : (C.dl η ξ) = C.dl ξ η := C.dl_symm η ξ
  have h' : θ₁ * (C.dl η ξ).toReal ≤ ν (C.Θ ξ η) ∧ ν (C.Θ ξ η) ≤ θ₂ * (C.dl η ξ).toReal := h
  rwa [e] at h'

/-- A weighted derivative bound on an annulus: if `|y| ≤ C' (ε - ε/4)^(-n)` and
`d ≤ c ε` then `|y| d^n ≤ C' (4c/3)^n`. -/
theorem abs_mul_pow_le_of_annulus {C' ε c d y : ℝ} (hε : 0 < ε) (hd0 : 0 ≤ d) (hd : d ≤ c * ε)
    (n : ℕ) (hC' : 0 ≤ C') (hy : |y| ≤ C' * (ε - ε / 4) ^ (-(n : ℤ))) :
    |y| * d ^ n ≤ C' * (4 * c / 3) ^ n := by
  have h34 : ε - ε / 4 = 3 * ε / 4 := by ring
  have hpos : 0 < 3 * ε / 4 := by positivity
  rw [h34, zpow_neg, zpow_natCast] at hy
  have hdn : d ^ n ≤ (c * ε) ^ n := pow_le_pow_left₀ hd0 hd n
  have hP : 0 < (3 * ε / 4) ^ n := pow_pos hpos n
  calc |y| * d ^ n ≤ (C' * ((3 * ε / 4) ^ n)⁻¹) * (c * ε) ^ n :=
        mul_le_mul hy hdn (pow_nonneg hd0 n) (by positivity)
    _ = C' * (4 * c / 3) ^ n := by
        have : (4 * c / 3) = c * ε / (3 * ε / 4) := by
          field_simp
        rw [this, div_pow (c * ε) (3 * ε / 4) n, mul_assoc, inv_mul_eq_div]

/-- **The cutoff centred at the output point.** There are `ε₀ ∈ (0, 1]`, `c₁, c₂ > 0` and `B ≥ 0`
such that for every centre `ξ ∈ Kc` and `0 < ε < ε₀` the cutoff `φ = radialCutoff C ν ξ (ε/4) ε`
(the radial cutoff construction) is smooth with values in `[0, 1]`, equals `1` near every `η` with `d̃(ξ, η) < c₁ ε`, vanishes
at every `η` with `d̃(ξ, η) > c₂ ε`, and has weighted first and second jets
`|X̃_i φ(η)| d̃^{w_i} ≤ B`, `|X̃_i X̃_i φ(η)| d̃^{2 w_i} ≤ B` at every `η ∈ U`
(`d̃ = d̃(ξ, η)`). -/
theorem exists_centredCutoff (C : LiftedChart w s Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (hν : ν.Smooth) {Kc : Set (Fin (n + m) → ℝ)} (hKc : IsCompact Kc) (hKU : Kc ⊆ C.U) :
    ∃ ε₀ c₁ c₂ B : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 < c₁ ∧ 0 < c₂ ∧ 0 ≤ B ∧
      ∀ ξ ∈ Kc, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ContDiff ℝ (⊤ : ℕ∞) (radialCutoff C ν ξ (ε / 4) ε) ∧
        (∀ η, 0 ≤ radialCutoff C ν ξ (ε / 4) ε η ∧ radialCutoff C ν ξ (ε / 4) ε η ≤ 1) ∧
        (∀ η ∈ C.U, (C.dl ξ η).toReal < c₁ * ε →
          ∀ᶠ η' in 𝓝 η, radialCutoff C ν ξ (ε / 4) ε η' = 1) ∧
        (∀ η ∈ C.U, c₂ * ε < (C.dl ξ η).toReal → radialCutoff C ν ξ (ε / 4) ε η = 0) ∧
        (∀ η ∈ C.U, ∀ i : Fin k,
          |fieldDerivative (C.Xl i) (radialCutoff C ν ξ (ε / 4) ε) η| *
              (C.dl ξ η).toReal ^ (w i : ℕ) ≤ B ∧
          |fieldDerivative (C.Xl i) (fieldDerivative (C.Xl i) (radialCutoff C ν ξ (ε / 4) ε)) η| *
              (C.dl ξ η).toReal ^ (2 * (w i : ℕ)) ≤ B) := by
  obtain ⟨θ₁, θ₂, hθ₁, hθ₁1, hθ₂1, hcmp⟩ := exists_nu_theta_comparison C ν
  obtain ⟨rstar, hr0, hr1, hq, hsup⟩ := exists_radialCutoff C ν hν hKc hKU
  choose C₁ hC₁0 hC₁ using fun i : Fin k => hsup [i]
  choose C₂ hC₂0 hC₂ using fun i : Fin k => hsup [i, i]
  set c₂ : ℝ := 1 / θ₁ with hc₂
  set c₁ : ℝ := 1 / (4 * θ₂) with hc₁
  have hc₂0 : 0 < c₂ := by positivity
  have hc₁0 : 0 < c₁ := by positivity
  have hθc : θ₁ * c₂ = 1 := by rw [hc₂]; field_simp
  set B : ℝ := ∑ i, C₁ i * (4 * c₂ / 3) ^ (w i : ℕ) +
    ∑ i, C₂ i * (4 * c₂ / 3) ^ (2 * (w i : ℕ)) with hB
  have hB1 : ∀ i, C₁ i * (4 * c₂ / 3) ^ (w i : ℕ) ≤ B := by
    intro i
    have h1 : C₁ i * (4 * c₂ / 3) ^ (w i : ℕ) ≤ ∑ i, C₁ i * (4 * c₂ / 3) ^ (w i : ℕ) :=
      Finset.single_le_sum (f := fun i => C₁ i * (4 * c₂ / 3) ^ (w i : ℕ))
        (fun i _ => mul_nonneg (hC₁0 i) (by positivity)) (Finset.mem_univ i)
    have h2 : 0 ≤ ∑ i, C₂ i * (4 * c₂ / 3) ^ (2 * (w i : ℕ)) :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hC₂0 i) (by positivity))
    linarith
  have hB2 : ∀ i, C₂ i * (4 * c₂ / 3) ^ (2 * (w i : ℕ)) ≤ B := by
    intro i
    have h1 : C₂ i * (4 * c₂ / 3) ^ (2 * (w i : ℕ)) ≤
        ∑ i, C₂ i * (4 * c₂ / 3) ^ (2 * (w i : ℕ)) :=
      Finset.single_le_sum (f := fun i => C₂ i * (4 * c₂ / 3) ^ (2 * (w i : ℕ)))
        (fun i _ => mul_nonneg (hC₂0 i) (by positivity)) (Finset.mem_univ i)
    have h2 : 0 ≤ ∑ i, C₁ i * (4 * c₂ / 3) ^ (w i : ℕ) :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hC₁0 i) (by positivity))
    linarith
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact add_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hC₁0 i) (by positivity)))
      (Finset.sum_nonneg (fun i _ => mul_nonneg (hC₂0 i) (by positivity)))
  refine ⟨rstar, c₁, c₂, B, hr0, hr1, hc₁0, hc₂0, hB0, fun ξ hξ ε hε hεr => ?_⟩
  have hξU : ξ ∈ C.U := hKU hξ
  have hs : 0 < ε / 4 := by positivity
  have hsr : ε / 4 < ε := by linarith
  obtain ⟨hcd, -, hrange, heq1, hts, -⟩ := hq ξ hξ (ε / 4) ε hs hsr hεr
  have hmid : (ε / 4 + ε) / 2 = 5 * ε / 8 := by ring
  -- vanishing of the derivatives and of the cutoff for `d̃ > c₂ ε`
  have hout : ∀ η ∈ C.U, c₂ * ε < (C.dl ξ η).toReal →
      η ∉ tsupport (radialCutoff C ν ξ (ε / 4) ε) := by
    intro η hη hd hts'
    have h1 := hts hts'
    have hν1 : ν (C.Θ ξ η) ≤ (ε / 4 + ε) / 2 := h1.2
    have h2 := (hcmp ξ hξU η hη).1
    have h3 : θ₁ * (c₂ * ε) < θ₁ * (C.dl ξ η).toReal := mul_lt_mul_of_pos_left hd hθ₁
    have h4 : θ₁ * (c₂ * ε) = ε := by rw [← mul_assoc, hθc, one_mul]
    rw [hmid] at hν1
    linarith
  refine ⟨hcd, hrange, ?_, ?_, ?_⟩
  · intro η hη hd
    have h1 := (hcmp ξ hξU η hη).2
    have hlt : ν (C.Θ ξ η) < ε / 4 := by
      have : θ₂ * (C.dl ξ η).toReal < θ₂ * (c₁ * ε) := mul_lt_mul_of_pos_left hd (by linarith)
      have h5 : θ₂ * (c₁ * ε) = ε / 4 := by rw [hc₁]; field_simp
      linarith
    have hmem : η ∈ rhoBall C ν ξ (ε / 4) := ⟨hη, hlt⟩
    exact Filter.eventuallyEq_of_mem ((isOpen_rhoBall_of C ν hξU _).mem_nhds hmem)
      (fun η' hη' => radialCutoff_eq_one C ν ξ hsr hη')
  · intro η hη hd
    exact image_eq_zero_of_notMem_tsupport (hout η hη hd)
  · intro η hη i
    have hd0 : 0 ≤ (C.dl ξ η).toReal := ENNReal.toReal_nonneg
    by_cases hd : c₂ * ε < (C.dl ξ η).toReal
    · have hz : ∀ I : List (Fin k), wordDerivative C.Xl I (radialCutoff C ν ξ (ε / 4) ε) η = 0 :=
        fun I => image_eq_zero_of_notMem_tsupport (fun h =>
          hout η hη hd (S.tsupport_wordDerivative_subset C.Xl I _ h))
      have h1 : fieldDerivative (C.Xl i) (radialCutoff C ν ξ (ε / 4) ε) η = 0 := hz [i]
      have h2 : fieldDerivative (C.Xl i) (fieldDerivative (C.Xl i)
          (radialCutoff C ν ξ (ε / 4) ε)) η = 0 := hz [i, i]
      rw [h1, h2]
      simp only [abs_zero, zero_mul]
      exact ⟨hB0, hB0⟩
    · have hd' : (C.dl ξ η).toReal ≤ c₂ * ε := not_lt.mp hd
      refine ⟨?_, ?_⟩
      · have hb := hC₁ i ξ hξ (ε / 4) ε hs hsr hεr η
        rw [wordWeight_singleton] at hb
        exact (abs_mul_pow_le_of_annulus hε hd0 hd' (w i : ℕ) (hC₁0 i) hb).trans (hB1 i)
      · have hb := hC₂ i ξ hξ (ε / 4) ε hs hsr hεr η
        have hw : wordWeight w [i, i] = 2 * (w i : ℕ) := by simp [wordWeight]; ring
        rw [hw] at hb
        exact (abs_mul_pow_le_of_annulus hε hd0 hd' (2 * (w i : ℕ)) (hC₂0 i) hb).trans (hB2 i)

end RothschildStein.P2
