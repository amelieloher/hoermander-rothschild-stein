-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.BaseSobolevNoDriftRho
public import RothschildStein.P2.TransferCover

/-!
# The lifted base Sobolev estimate for no-drift charts

Part of the base Sobolev estimate (BB pp. 585-587, Thms 11.42-11.43, (11.69)-(11.72)), without drift. From the absorption
`Φ₂ + Φ₁ ≤ K (r² ‖L̃u‖_{L^p(U_r)} + Φ₀)` (`exists_secondAbsorption_nhds_noDrift_of_representation`) at
`σ = 1/2`, `∑_{|I| ≤ 2} ‖X̃_I u‖_{L^p(U_{r/2})} ≤ D(r) (Φ₀ + Φ₁ + Φ₂)` with `D(r) = 1 + 2/r + 4/r²`
(`sobolevXENorm_le_seminormPhi_noDrift`), and `Φ₀ ≤ ‖u‖_{L^p(U_r)}` (`seminormPhi_zero_le_noDrift`);
hence `liftedBaseSobolevEstimate_noDrift_of_representation`, the statement
`LiftedBaseSobolevEstimate C ν (noDriftOpWords q) p` of the lifted base Sobolev estimate (the input of
`sobolev_transfer_cover_of_lifted`), under the hypotheses of
`representation_secondOrder_noDrift_of`: `TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer`,
`SignedParametrixNoDrift`, a standard frame, and a cutoff `a` equal to `1` near the chart centre.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P2

open RothschildStein.P1 RothschildStein

section Assembly

variable {n q : ℕ} {w : Fin q → ℕ+} {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}

/-- `Φ₀(u) ≤ ‖u‖_{L^p(U_r)}` for `u ∈ W^{2,p}_{X̃}(U_r)` (no drift). -/
theorem seminormPhi_zero_le_noDrift {U : ℝ → Opens (Fin n → ℝ)}
    (hmono : ∀ s t : ℝ, s ≤ t → U s ≤ U t) {p : ℝ≥0∞} {r : ℝ} (hr0 : 0 < r)
    {u : (Fin n → ℝ) → ℝ} (hu : memSobolevX w X (U r) 2 p u) :
    seminormPhi w X U p r 0 u ≤ eLpNorm u p (volume.restrict (U r : Set (Fin n → ℝ))) := by
  obtain ⟨gN, hgN, -⟩ := hu.2 [] (S.nil_mem_wordFamily w 2)
  unfold seminormPhi
  refine iSup₂_le fun σ hσ => ?_
  rw [wordsOfWeight_zero, Finset.sum_singleton, pow_zero, ENNReal.ofReal_one, one_mul]
  have hσr : σ * r ≤ r := mul_le_of_le_one_left hr0.le hσ.2.le
  calc weakWordENorm X (U (σ * r)) [] p u ≤ weakWordENorm X (U r) [] p u :=
        weakWordENorm_mono_of_memSobolevX_noDrift hu (hmono _ _ hσr) (S.nil_mem_wordFamily w 2)
    _ = eLpNorm u p (volume.restrict (U r : Set (Fin n → ℝ))) :=
        S.weakWordENorm_eq X (U r) [] p u u (S.hasWeakWordDeriv_nil X (U r) hgN.1)

/-- The Sobolev norm of order two on `U_{r/2}` is bounded by the
seminorms `Φ_j` at `σ = 1/2`: `‖u‖_{W^{2,p}(U_{r/2})} ≤ (1 + 2/r + 4/r²) (Φ₀ + Φ₂ + Φ₁)` (no drift). -/
theorem sobolevXENorm_le_seminormPhi_noDrift (U : ℝ → Opens (Fin n → ℝ)) {p : ℝ≥0∞} {r : ℝ}
    (hr0 : 0 < r) (u : (Fin n → ℝ) → ℝ) :
    sobolevXENorm w X (U (r / 2)) 2 p u ≤
      ENNReal.ofReal (1 + 2 / r + 4 / r ^ 2) *
        (seminormPhi w X U p r 0 u + (seminormPhi w X U p r 2 u + seminormPhi w X U p r 1 u)) := by
  have hj : ∀ j : ℕ, ∑ I ∈ wordsOfWeight w j, weakWordENorm X (U (r / 2)) I p u ≤
      ENNReal.ofReal ((2 / r) ^ j) * seminormPhi w X U p r j u := by
    intro j
    have h := le_seminormPhi_noDrift (w := w) X U p r j u (σ := 1 / 2) ⟨le_rfl, by norm_num⟩
    have e1 : (1 - 1 / 2 : ℝ) * r = r / 2 := by ring
    have e2 : (1 / 2 : ℝ) * r = r / 2 := by ring
    rw [e1, e2] at h
    have hprod : (2 / r) ^ j * (r / 2) ^ j = 1 := by
      rw [← mul_pow]
      have : 2 / r * (r / 2) = 1 := by field_simp
      rw [this, one_pow]
    calc ∑ I ∈ wordsOfWeight w j, weakWordENorm X (U (r / 2)) I p u
        = ENNReal.ofReal ((2 / r) ^ j) * (ENNReal.ofReal ((r / 2) ^ j) *
            ∑ I ∈ wordsOfWeight w j, weakWordENorm X (U (r / 2)) I p u) := by
          rw [← mul_assoc, ofReal_mul_ofReal _ (by positivity), hprod, ENNReal.ofReal_one,
            one_mul]
      _ ≤ _ := mul_le_mul' le_rfl h
  have hD0 : (2 / r) ^ 0 ≤ 1 + 2 / r + 4 / r ^ 2 := by
    have h1 : 0 ≤ 2 / r := by positivity
    have h2 : 0 ≤ 4 / r ^ 2 := by positivity
    rw [pow_zero]
    linarith
  have hD1 : (2 / r) ^ 1 ≤ 1 + 2 / r + 4 / r ^ 2 := by
    have h2 : 0 ≤ 4 / r ^ 2 := by positivity
    rw [pow_one]
    linarith
  have hD2 : (2 / r) ^ 2 ≤ 1 + 2 / r + 4 / r ^ 2 := by
    have h1 : 0 ≤ 2 / r := by positivity
    have : (2 / r) ^ 2 = 4 / r ^ 2 := by
      rw [div_pow]
      norm_num
    rw [this]
    linarith
  unfold sobolevXENorm
  refine (sum_wordFamily_two_le_noDrift w _).trans ?_
  calc _ ≤ ENNReal.ofReal ((2 / r) ^ 0) * seminormPhi w X U p r 0 u +
        ENNReal.ofReal ((2 / r) ^ 1) * seminormPhi w X U p r 1 u +
        ENNReal.ofReal ((2 / r) ^ 2) * seminormPhi w X U p r 2 u :=
        add_le_add (add_le_add (hj 0) (hj 1)) (hj 2)
    _ ≤ ENNReal.ofReal (1 + 2 / r + 4 / r ^ 2) * seminormPhi w X U p r 0 u +
        ENNReal.ofReal (1 + 2 / r + 4 / r ^ 2) * seminormPhi w X U p r 1 u +
        ENNReal.ofReal (1 + 2 / r + 4 / r ^ 2) * seminormPhi w X U p r 2 u :=
        add_le_add (add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal hD0) le_rfl)
          (mul_le_mul' (ENNReal.ofReal_le_ofReal hD1) le_rfl))
          (mul_le_mul' (ENNReal.ofReal_le_ofReal hD2) le_rfl)
    _ = _ := by ring

end Assembly

section Lifted

variable {n q s m : ℕ} {w : Fin q → ℕ+} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- **The lifted base Sobolev estimate for no-drift charts** (BB pp. 585-587, Thms 11.42-11.43,
(11.69)-(11.72)), under the hypotheses of `representation_secondOrder_noDrift_of`. Let
`C` be a lifted no-drift chart, `F` a standard frame of it, `a ∈ C_c^∞(V)` a cutoff with `a = 1` near the
centre `(x₀, 0)` for which the derivative representations hold (`TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation`,
`DerivativeTransfer`, `SignedParametrixNoDrift`) and `ν` a smooth homogeneous norm. Then for `1 < p < ∞`
`LiftedBaseSobolevEstimate C ν (noDriftOpWords q) p`: there is `r₀ > 0` such that for `0 < r ≤ r₀` there
is `C(r)` with `‖u‖_{W^{2,p}_{X̃}(U^ρ_{r/2})} ≤ C(r) (‖L̃u‖_{L^p(U^ρ_r)} + ‖u‖_{L^p(U^ρ_r)})` for every
`u ∈ W^{2,p}_{X̃}(U^ρ_r)` with `L̃u = f` (weak word derivatives of `[i, i]`). -/
theorem liftedBaseSobolevEstimate_noDrift_of_representation
    {q₀ : ℕ} {H : H1.StandingHypotheses C.G q₀} {K : H1.FundamentalKernel C.G H}
    {hQ : 2 < (C.G.homogeneousDimension : ℝ)} (hF : C.IsStandardFrame F H K hQ)
    (hw : ∀ j, (w j : ℕ) = 1)
    (B : Fin (n + m) → List (Fin q)) (hRowInt : TypeKernelIntegrable F) (hLeftDiff : LeftDifferentiation F w C.Xl)
    (hRightDiff : RightDifferentiation F w C.Xl hF.lifted.contDiffOn_Xl) (hTransfer : DerivativeTransfer F w C.Xl B)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F C.Xl c a b)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth)
    (ha : ∀ᶠ x in 𝓝 (joinPoint x₀ (0 : Fin m → ℝ)),
      x ∈ (F.V : Set (Fin (n + m) → ℝ)) ∧ a x = 1)
    {p : ℝ≥0∞} (hp1 : 1 < p) (hpt : p ≠ ⊤) :
    LiftedBaseSobolevEstimate C ν (noDriftOpWords q) p := by
  obtain ⟨p', rfl⟩ : ∃ p' : ℝ, p = ENNReal.ofReal p' :=
    ⟨p.toReal, (ENNReal.ofReal_toReal hpt).symm⟩
  have hp' : 1 < p' := ENNReal.one_lt_ofReal.1 hp1
  obtain ⟨r₀, hr₀, hr₀1, hmain⟩ := exists_secondAbsorption_nhds_noDrift_of_representation hF hw B
    hRowInt hLeftDiff hRightDiff hTransfer hc hc0 a hParametrix ν hν C.center_mem ha
  obtain ⟨Kc, hKc0, hKc⟩ := hmain p' hp'
  refine ⟨r₀, hr₀, fun r hr0 hrr => ⟨(1 + 2 / r + 4 / r ^ 2) * (1 + Kc), by positivity,
    fun u f hu hf => ?_⟩⟩
  have hr1 : r ≤ 1 := hrr.trans hr₀1
  have hmono : ∀ s t : ℝ, s ≤ t →
      rhoOpensNoDrift C ν C.center_mem s ≤ rhoOpensNoDrift C ν C.center_mem t :=
    fun s t hst => rhoOpensNoDrift_mono C ν C.center_mem hst
  have hΦ := hKc r hr0 hrr u f hu hf
  have hsob := sobolevXENorm_le_seminormPhi_noDrift (w := w) (X := C.Xl)
    (rhoOpensNoDrift C ν C.center_mem) (p := ENNReal.ofReal p') hr0 u
  have hΦ0 := seminormPhi_zero_le_noDrift (w := w) (X := C.Xl) hmono hr0 hu
  have hF1 : ENNReal.ofReal (r ^ 2) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (pow_le_one₀ hr0.le hr1)
  have h2 : seminormPhi w C.Xl (rhoOpensNoDrift C ν C.center_mem) (ENNReal.ofReal p') r 2 u +
        seminormPhi w C.Xl (rhoOpensNoDrift C ν C.center_mem) (ENNReal.ofReal p') r 1 u ≤
      ENNReal.ofReal Kc * (eLpNorm f (ENNReal.ofReal p')
          (volume.restrict (rhoOpensNoDrift C ν C.center_mem r : Set (Fin (n + m) → ℝ))) +
        eLpNorm u (ENNReal.ofReal p')
          (volume.restrict (rhoOpensNoDrift C ν C.center_mem r : Set (Fin (n + m) → ℝ)))) := by
    refine hΦ.trans (mul_le_mul' le_rfl (add_le_add ?_ hΦ0))
    calc ENNReal.ofReal (r ^ 2) * eLpNorm f (ENNReal.ofReal p')
          (volume.restrict (rhoOpensNoDrift C ν C.center_mem r : Set (Fin (n + m) → ℝ)))
        ≤ 1 * eLpNorm f (ENNReal.ofReal p')
          (volume.restrict (rhoOpensNoDrift C ν C.center_mem r : Set (Fin (n + m) → ℝ))) :=
          mul_le_mul' hF1 le_rfl
      _ = _ := one_mul _
  have h3 : seminormPhi w C.Xl (rhoOpensNoDrift C ν C.center_mem) (ENNReal.ofReal p') r 0 u +
        (seminormPhi w C.Xl (rhoOpensNoDrift C ν C.center_mem) (ENNReal.ofReal p') r 2 u +
          seminormPhi w C.Xl (rhoOpensNoDrift C ν C.center_mem) (ENNReal.ofReal p') r 1 u) ≤
      ENNReal.ofReal (1 + Kc) * (eLpNorm f (ENNReal.ofReal p')
          (volume.restrict (rhoOpensNoDrift C ν C.center_mem r : Set (Fin (n + m) → ℝ))) +
        eLpNorm u (ENNReal.ofReal p')
          (volume.restrict (rhoOpensNoDrift C ν C.center_mem r : Set (Fin (n + m) → ℝ)))) := by
    calc _ ≤ (eLpNorm f (ENNReal.ofReal p')
            (volume.restrict (rhoOpensNoDrift C ν C.center_mem r : Set (Fin (n + m) → ℝ))) +
          eLpNorm u (ENNReal.ofReal p')
            (volume.restrict (rhoOpensNoDrift C ν C.center_mem r : Set (Fin (n + m) → ℝ)))) +
          ENNReal.ofReal Kc * (eLpNorm f (ENNReal.ofReal p')
            (volume.restrict (rhoOpensNoDrift C ν C.center_mem r : Set (Fin (n + m) → ℝ))) +
          eLpNorm u (ENNReal.ofReal p')
            (volume.restrict (rhoOpensNoDrift C ν C.center_mem r : Set (Fin (n + m) → ℝ)))) :=
          add_le_add (hΦ0.trans le_add_self) h2
      _ = _ := by
          rw [ENNReal.ofReal_add zero_le_one hKc0, ENNReal.ofReal_one]
          ring
  calc sobolevXENorm w C.Xl (rhoOpensNoDrift C ν C.center_mem (r / 2)) 2 (ENNReal.ofReal p') u
      ≤ ENNReal.ofReal (1 + 2 / r + 4 / r ^ 2) *
        (seminormPhi w C.Xl (rhoOpensNoDrift C ν C.center_mem) (ENNReal.ofReal p') r 0 u +
          (seminormPhi w C.Xl (rhoOpensNoDrift C ν C.center_mem) (ENNReal.ofReal p') r 2 u +
            seminormPhi w C.Xl (rhoOpensNoDrift C ν C.center_mem) (ENNReal.ofReal p') r 1 u)) :=
        hsob
    _ ≤ ENNReal.ofReal (1 + 2 / r + 4 / r ^ 2) * (ENNReal.ofReal (1 + Kc) *
        (eLpNorm f (ENNReal.ofReal p')
          (volume.restrict (rhoOpensNoDrift C ν C.center_mem r : Set (Fin (n + m) → ℝ))) +
        eLpNorm u (ENNReal.ofReal p')
          (volume.restrict (rhoOpensNoDrift C ν C.center_mem r : Set (Fin (n + m) → ℝ))))) :=
        mul_le_mul' le_rfl h3
    _ = _ := by
        rw [← mul_assoc, ofReal_mul_ofReal _ (by positivity)]
        rfl

end Lifted

end RothschildStein.P2
