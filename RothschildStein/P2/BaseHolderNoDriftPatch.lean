-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.BaseHolderNoDriftStep
public import RothschildStein.P2.BaseHolderNoDriftArith
public import RothschildStein.P2.SobolevInterpolationNoDriftNhds

/-!
# No drift: the base Hölder estimate on the frame patch

Part of the base Hölder estimate (BB pp. 600-602, Thms 11.57-11.58), alphabet `Fin q`, all weights one. For a function
`u ∈ C^{2,α}_{X̃}(V)` on the whole patch `V = F.V` of a standard frame with Hölder weak jet `D`, and
`0 < t < s ≤ r₁` (so that `U_s^ρ ⊆ V` and the cutoff `a` of the representations equals `1` on `U_s^ρ`),

`‖u‖_{C^{2,α}(U_t^ρ)} ≤ K (s - t)^{-β} (‖L̃u‖_{C^α(U_s^ρ)} + ‖u‖_{∞, U_s^ρ})`, `β = γ + 4`.

The proof is the cutoff step (`cutoff_step_noDrift`: the compact Hölder estimate for
`ζ u`) with the data `∑ₗ ‖X̃ₗ u‖_{C^α(U_{t+2g}^ρ)} ≤ c_n (‖L̃u‖_{C^α(U_s^ρ)} + ‖u‖_{∞,U_s^ρ})` of the nested
Hölder interpolation (`g = (s - t)/3`, `δ = 1/4`). Without drift `L̃u` is data, so the hole-filling inequality
`ψ(t) ≤ θ ψ(s) + C (s - t)^{-β} (H + U)` holds with `θ = 0` and its iteration (BB Lemma 8.55) is not
needed: the nested Hölder interpolation inequality is itself the iterated one for the first
derivatives, and `‖L̃u‖_{L^∞} ≤ ‖L̃u‖_{C^α}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

variable {n q st m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart noDriftWeight st Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {q₀ : ℕ} {H : H1.StandingHypotheses C.G q₀} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- **The base Hölder estimate on the frame patch, no drift** (BB Thm 11.57, pp. 600-602). Conditional
exactly on the hypotheses of the derivative representations without drift (`TypeKernelIntegrable`, `LeftDifferentiation`,
`RightDifferentiation`, `DerivativeTransfer`, the `SignedParametrixNoDrift`s with the density data `c`) on a standard frame, with a cutoff
`a` equal to `1` near the centre `ξ₀`. There are `r₁ ∈ (0, 1]`, `β > 0`, `K > 0` such that for `0 < t < s ≤ r₁` and
every `u ∈ C^{2,α}_{X̃}(V)` with Hölder weak jet `D` on the patch,
`‖u‖_{C^{2,α}(U_t^ρ)} ≤ K (s - t)^{-β} (‖L̃u‖_{C^α(U_s^ρ)} + ‖u‖_{∞,U_s^ρ})`
(the left side computed on the jet, `jetENormNoDrift`). -/
theorem exists_patchHolder_noDrift_of_representation (hF : C.IsStandardFrame F H K hQ)
    (B : Fin (n + m) → List (Fin q)) (hRowInt : TypeKernelIntegrable F)
    (hLeftDiff : LeftDifferentiation F noDriftWeight C.Xl)
    (hRightDiff : RightDifferentiation F noDriftWeight C.Xl hF.lifted.contDiffOn_Xl)
    (hTransfer : DerivativeTransfer F noDriftWeight C.Xl B)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F C.Xl c a b)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth) {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U)
    (ha : ∀ᶠ x in 𝓝 ξ₀, x ∈ (F.V : Set (Fin (n + m) → ℝ)) ∧ a x = 1) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) :
    ∃ r₁ β Kc : ℝ, 0 < r₁ ∧ r₁ ≤ 1 ∧ 0 < β ∧ 0 < Kc ∧
      (∀ s : ℝ, s ≤ r₁ → rhoBall C ν ξ₀ s ⊆ (F.V : Set (Fin (n + m) → ℝ)) ∧
        ∀ x ∈ rhoBall C ν ξ₀ s, a x = 1) ∧ ∀ t s : ℝ, 0 < t → t < s → s ≤ r₁ →
      ∀ (u : (Fin (n + m) → ℝ) → ℝ) (D : List (Fin q) → (Fin (n + m) → ℝ) → ℝ),
        memHolderX noDriftWeight C.Xl C.dl F.V 2 α u →
        LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl F.V 2 α u D →
        jetENormNoDrift C.dl α (rhoBall C ν ξ₀ t) D ≤
          ENNReal.ofReal (Kc * (s - t) ^ (-β)) *
            (holderENorm C.dl α (rhoBall C ν ξ₀ s) (weakSumSquares D []) +
              supNormE (rhoBall C ν ξ₀ s) u) := by
  classical
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_compactHolder_noDrift_of_representation hF B hRowInt hLeftDiff hRightDiff hTransfer hc hc0
    a hParametrix hα0 hα1
  obtain ⟨C₃, hC₃, hS⟩ := exists_holderFromSup_noDrift_of_representation hF hLeftDiff hc hc0 a hParametrix hα0 hα1
  obtain ⟨rstar, b₁, b₂, B₀, B₁, B₂, hr0, hr1, hb₁, hb₂, hB₀, hB₁, hB₂, hcut⟩ :=
    exists_cutoffData_noDrift C ν hν hξ₀ hα0 hα1
  obtain ⟨Rstar, γ, Cn, hR0, hR1, hγ, hCn, hnest⟩ :=
    exists_nestedInterpolation_noDrift_of_representation hF hLeftDiff hc hc0 a hParametrix ν hν hξ₀ hα0 hα1
  obtain ⟨r₂, hr₂, hsub⟩ := exists_rhoBall_subset_of_mem_nhds_noDrift C ν hξ₀ ha
  set r₁ : ℝ := min (min (rstar / 2) Rstar) r₂ with hr₁
  have hr₁0 : 0 < r₁ := lt_min (lt_min (by linarith) hR0) hr₂
  have hr₁rstar : r₁ ≤ rstar / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hr₁R : r₁ ≤ Rstar := (min_le_left _ _).trans (min_le_right _ _)
  have hr₁r₂ : r₁ ≤ r₂ := min_le_right _ _
  have hr₁1 : r₁ ≤ 1 := hr₁R.trans hR1
  set κ : ℝ := 1 / 4 + Cn * (1 / 4 : ℝ) ^ (-γ) with hκ
  have hκ0 : 0 ≤ κ := by
    have : 0 ≤ Cn * (1 / 4 : ℝ) ^ (-γ) := mul_nonneg hCn.le (Real.rpow_nonneg (by norm_num) _)
    rw [hκ]
    linarith
  set K₀ : ℝ := Λ * (B₀ + 2 * B₁ * κ + C₃ * B₂ * (2 + 2 * b₁ * κ + b₂) + 1) with hK₀
  have hK₀0 : 0 ≤ K₀ := by
    rw [hK₀]
    positivity
  refine ⟨r₁, γ + 4, K₀ * 3 ^ (γ + 4) + 1, hr₁0, hr₁1, by linarith, by positivity,
    fun s hs => ⟨fun x hx => (hsub s (hs.trans hr₁r₂) hx).1,
      fun x hx => (hsub s (hs.trans hr₁r₂) hx).2⟩, ?_⟩
  intro t s ht hts hsr u D hu hD
  set g : ℝ := (s - t) / 3 with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  have hst : t + 3 * g = s := by rw [hg]; ring
  have hg1 : g ≤ 1 := by
    rw [hg]
    have : s ≤ 1 := hsr.trans hr₁1
    linarith
  have hsrstar : t + 3 * g < rstar := by
    rw [hst]
    linarith
  have hsub' := hsub s (hsr.trans hr₁r₂)
  have hBVs : rhoBall C ν ξ₀ s ⊆ (F.V : Set (Fin (n + m) → ℝ)) := fun x hx => (hsub' hx).1
  have ha1s : ∀ x ∈ rhoBall C ν ξ₀ s, a x = 1 := fun x hx => (hsub' hx).2
  have hBV : rhoBall C ν ξ₀ (t + 3 * g) ⊆ (F.V : Set (Fin (n + m) → ℝ)) := by
    rw [hst]
    exact hBVs
  have ha1 : ∀ x ∈ rhoBall C ν ξ₀ (t + 3 * g), a x = 1 := by
    rw [hst]
    exact ha1s
  -- the nested interpolation gives the data `Ψ ≤ c_n Y`
  have hnest' := hnest s (by linarith) (hsr.trans hr₁R) hBVs ha1s u D hu hD (t + 2 * g)
    (by linarith) (by rw [← hst]; linarith) (1 / 4) (by norm_num) (by norm_num)
  set Y : ℝ≥0∞ := holderENorm C.dl α (rhoBall C ν ξ₀ s) (weakSumSquares D []) +
    supNormE (rhoBall C ν ξ₀ s) u with hY
  have hY1 : holderENorm C.dl α (rhoBall C ν ξ₀ (t + 3 * g)) (weakSumSquares D []) ≤ Y := by
    rw [hst]
    exact le_self_add
  have hY2 : supNormE (rhoBall C ν ξ₀ (t + 3 * g)) u ≤ Y := by
    rw [hst]
    exact le_add_self
  set cn : ℝ := 1 / 4 + Cn * (1 / 4 : ℝ) ^ (-γ) * g ^ (-γ) with hcn
  have hcn0 : 0 ≤ cn := by
    rw [hcn]
    positivity
  have hΨ : ∑ l : Fin q, holderENorm C.dl α (rhoBall C ν ξ₀ (t + 2 * g)) (D [l]) ≤
      ENNReal.ofReal cn * Y := by
    refine hnest'.trans ?_
    have hRr : s - (t + 2 * g) = g := by rw [← hst]; ring
    rw [hRr]
    have hf : (⨆ x : rhoBall C ν ξ₀ s, ENNReal.ofReal |weakSumSquares D [] x|) ≤ Y :=
      (supNormE_le_holderENorm _ _).trans le_self_add
    have hu' : (⨆ x : rhoBall C ν ξ₀ s, ENNReal.ofReal |u x|) ≤ Y := le_add_self
    have hb : BoundedBy (ENNReal.ofReal (1 / 4) *
        (⨆ x : rhoBall C ν ξ₀ s, ENNReal.ofReal |weakSumSquares D [] x|) +
        ENNReal.ofReal (Cn * (1 / 4 : ℝ) ^ (-γ) * g ^ (-γ)) *
          ⨆ x : rhoBall C ν ξ₀ s, ENNReal.ofReal |u x|) Y cn := by
      have h1 := BoundedBy.of_const_mul_le (by norm_num : (0 : ℝ) ≤ 1 / 4) hf
      have h2 := BoundedBy.of_const_mul_le (by positivity : 0 ≤ Cn * (1 / 4 : ℝ) ^ (-γ) * g ^ (-γ)) hu'
      exact h1.add h2 (by norm_num) (by positivity)
    exact hb
  have hstep := cutoff_step_noDrift hF.lifted hξ₀ hα0 hα1 hΛ0.le hΛ hC₃.le hS hb₁ hb₂ hB₀ hB₁ hB₂ hcut
    ht hg0 hsrstar hBV ha1 (ne_top_of_lt hu.1) hD hcn0 hY1 hY2 hΨ
  refine hstep.trans (mul_le_mul' ?_ le_rfl)
  refine ENNReal.ofReal_le_ofReal ?_
  -- the real arithmetic
  set E : ℝ := g⁻¹ with hE
  have hE1 : 1 ≤ E := by
    rw [hE]
    exact one_le_inv_iff₀.2 ⟨hg0, hg1⟩
  have hcnE : cn ≤ κ * E ^ γ := by
    have hEγ : g ^ (-γ) = E ^ γ := by
      rw [hE, Real.rpow_neg hg0.le, Real.inv_rpow hg0.le]
    have hE1γ : 1 ≤ E ^ γ := Real.one_le_rpow hE1 (by linarith)
    rw [hcn, hEγ, hκ]
    have : 0 ≤ Cn * (1 / 4 : ℝ) ^ (-γ) * E ^ γ := by positivity
    nlinarith
  have hpoly := cutoffStep_poly_le (E := E) (γ := γ) (κ := κ) (cn := cn) (Λ := Λ) (B₀ := B₀)
    (B₁ := B₁) (B₂ := B₂) (b₁ := b₁) (b₂ := b₂) (C₃ := C₃) hγ hE1 hcn0 hcnE hΛ0.le hB₀ hB₁ hB₂ hb₁ hb₂
    hC₃.le
  have e1 : B₀ * g⁻¹ + 2 * (B₁ * (g ^ 2)⁻¹) * cn +
      C₃ * (2 + 2 * (b₁ * g⁻¹) * cn + b₂ * (g ^ 2)⁻¹) * (B₂ * (g ^ 3)⁻¹) + 1 =
      B₀ * E + 2 * (B₁ * E ^ 2) * cn + C₃ * (2 + 2 * (b₁ * E) * cn + b₂ * E ^ 2) * (B₂ * E ^ 3) + 1 := by
    rw [hE, inv_pow, inv_pow]
  rw [e1]
  refine hpoly.trans ?_
  have hEβ : E ^ (4 + γ) = 3 ^ (γ + 4) * (s - t) ^ (-(γ + 4)) := by
    rw [hE, hg, add_comm 4 γ]
    exact inv_div_three_rpow hts
  rw [hEβ]
  have hpos : 0 ≤ (s - t) ^ (-(γ + 4)) := Real.rpow_nonneg (by linarith) _
  have h3 : 0 ≤ (3 : ℝ) ^ (γ + 4) := Real.rpow_nonneg (by norm_num) _
  calc Λ * (B₀ + 2 * B₁ * κ + C₃ * B₂ * (2 + 2 * b₁ * κ + b₂) + 1) * (3 ^ (γ + 4) * (s - t) ^ (-(γ + 4)))
      = K₀ * 3 ^ (γ + 4) * (s - t) ^ (-(γ + 4)) := by rw [hK₀]; ring
    _ ≤ (K₀ * 3 ^ (γ + 4) + 1) * (s - t) ^ (-(γ + 4)) :=
        mul_le_mul_of_nonneg_right (by linarith) hpos

end RothschildStein.P2
