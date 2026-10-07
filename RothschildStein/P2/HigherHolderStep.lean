-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HigherHolderStage

/-!
# The step estimate on `ρ`-balls

Part of the higher Hölder estimate (BB p. 604). `stage_step`: for a lifted no-drift chart and the radial cutoff `ζ = φ(s, r)` of the radial cutoff construction,
a Hölder weak jet `D` of order `j' + 2` of `D []` on the ball `U_r^ρ` and a Hölder weak jet `Df` of order `j' + 1`
of `Df [] = ∑ᵢ D [i, i]` there, the function `D []` has a Hölder weak jet of order `j' + 3` on `U_s^ρ`
(extending `D`) with
`‖·‖_{j'+3, C^α(U_s)} ≤ C (r - s)^{-(j'+4)} (‖Df‖_{j'+1, C^α(U_r)} + ‖D‖_{j'+2, C^α(U_r)})`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2.HigherHolder

open RothschildStein.P1

theorem mem_wordFamily_iff_length {k : ℕ} {w : Fin k → ℕ+} (hw : ∀ j, (w j : ℕ) = 1) {N : ℕ}
    {K : List (Fin k)} : K ∈ wordFamily w N ↔ K.length ≤ N := by
  rw [S.mem_wordFamily_iff, wordWeight_eq_length hw]

theorem holderJetNorm_shift_le {n' k : ℕ} {w : Fin k → ℕ+} (hw : ∀ j, (w j : ℕ) = 1)
    (d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞) (V : Set (Fin n' → ℝ)) (α : ℝ) (N : ℕ)
    (D : List (Fin k) → (Fin n' → ℝ) → ℝ) (i : Fin k) :
    holderJetNorm w d V α N (fun K' => D (K' ++ [i])) ≤ holderJetNorm w d V α (N + 1) D := by
  classical
  unfold holderJetNorm
  have hinj : Function.Injective fun K' : List (Fin k) => K' ++ [i] := fun a b h =>
    List.append_cancel_right h
  calc ∑ K' ∈ wordFamily w N, holderENorm d α V (D (K' ++ [i]))
      = ∑ K ∈ (wordFamily w N).image (fun K' => K' ++ [i]), holderENorm d α V (D K) := by
        rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset ?_
        intro K hK
        obtain ⟨K', hK', rfl⟩ := Finset.mem_image.1 hK
        rw [mem_wordFamily_iff_length hw] at hK' ⊢
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega

theorem holderJetNorm_mono_order {n' k : ℕ} {w : Fin k → ℕ+} (hw : ∀ j, (w j : ℕ) = 1)
    (d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞) (V : Set (Fin n' → ℝ)) (α : ℝ) {N N' : ℕ}
    (h : N ≤ N') (D : List (Fin k) → (Fin n' → ℝ) → ℝ) :
    holderJetNorm w d V α N D ≤ holderJetNorm w d V α N' D := by
  unfold holderJetNorm
  refine Finset.sum_le_sum_of_subset fun K hK => ?_
  rw [mem_wordFamily_iff_length hw] at hK ⊢
  omega

theorem holderJetNorm_mono_set {n' k : ℕ} {w : Fin k → ℕ+}
    (d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞) {V V' : Set (Fin n' → ℝ)} (hV : V' ⊆ V) (α : ℝ)
    (N : ℕ) (D : List (Fin k) → (Fin n' → ℝ) → ℝ) :
    holderJetNorm w d V' α N D ≤ holderJetNorm w d V α N D :=
  Finset.sum_le_sum fun _ _ => S.holderENorm_mono d α V _ hV

theorem holderJetNorm_ne_top {n' k : ℕ} {w : Fin k → ℕ+} {d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞}
    {V : Set (Fin n' → ℝ)} {α : ℝ} {N : ℕ} {D : List (Fin k) → (Fin n' → ℝ) → ℝ}
    (hD : ∀ K ∈ wordFamily w N, holderENorm d α V (D K) ≠ ⊤) : holderJetNorm w d V α N D ≠ ⊤ :=
  ENNReal.sum_ne_top.2 hD

theorem single_le_holderJetNorm {n' k : ℕ} {w : Fin k → ℕ+} {d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞}
    {V : Set (Fin n' → ℝ)} {α : ℝ} {N : ℕ} {D : List (Fin k) → (Fin n' → ℝ) → ℝ}
    {K : List (Fin k)} (hK : K ∈ wordFamily w N) :
    holderENorm d α V (D K) ≤ holderJetNorm w d V α N D :=
  Finset.single_le_sum (f := fun K => holderENorm d α V (D K)) (fun _ _ => zero_le) hK

section Cutoff

variable {n q st m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

theorem noDriftWeight_coe_eq_one (i : Fin q) : ((noDriftWeight i : ℕ+) : ℕ) = 1 := by
  simp [noDriftWeight]

/-- **The cutoff package** (the radial cutoff construction): thresholds and constants such that the radial cutoff
`φ(s, r)` at the chart centre is smooth with compact support in `U_r^ρ`, equals `1` on `U_s^ρ`, and
`‖X̃_I φ‖_{C^α(O)} ≤ c (r - s)^{-(N+1)}` for words of length at most `N`. -/
theorem exists_cutoff_package (C : LiftedChart noDriftWeight st Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (N : ℕ) :
    ∃ rstar c : ℝ, 0 < rstar ∧ rstar ≤ 1 ∧ 0 < c ∧ ∀ s r : ℝ, 0 < s → s < r → r < rstar →
      ContDiff ℝ (⊤ : ℕ∞) (radialCutoff C ν (joinPoint x₀ (0 : Fin m → ℝ)) s r) ∧
      HasCompactSupport (radialCutoff C ν (joinPoint x₀ (0 : Fin m → ℝ)) s r) ∧
      EqOn (radialCutoff C ν (joinPoint x₀ (0 : Fin m → ℝ)) s r) (fun _ => 1)
        (rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) s) ∧
      tsupport (radialCutoff C ν (joinPoint x₀ (0 : Fin m → ℝ)) s r) ⊆
        rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) r ∧
      ∀ I : List (Fin q), I.length ≤ N →
        holderENorm C.dl α C.O
          (wordDerivative C.Xl I (radialCutoff C ν (joinPoint x₀ (0 : Fin m → ℝ)) s r)) ≤
          ENNReal.ofReal (c * ((r - s)⁻¹) ^ (N + 1)) := by
  classical
  obtain ⟨rstar, hr0, hr1, hq, -, hhold⟩ := smooth_cutoffs_noDrift C ν hν
    (isCompact_singleton (x := joinPoint x₀ (0 : Fin m → ℝ))) (singleton_subset_iff.2 C.center_mem)
  choose CI hCI0 hCI using hhold
  have hsum0 : 0 ≤ ∑ I ∈ repWords q N, CI I := Finset.sum_nonneg fun I _ => hCI0 I
  refine ⟨rstar, 1 + ∑ I ∈ repWords q N, CI I, hr0, hr1, by linarith, fun s r hs hsr hrr => ?_⟩
  obtain ⟨h1, h2, -, h4, h5, h6⟩ := hq _ (mem_singleton _) s r hs hsr hrr
  refine ⟨h1, h2, h4, h5.trans h6, fun I hI => ?_⟩
  have hb := hCI I _ (mem_singleton _) s r hs hsr hrr α hα0 hα1
  refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
  have hwt : wordWeight noDriftWeight I = I.length :=
    wordWeight_eq_length (fun j => noDriftWeight_coe_eq_one j) I
  rw [hwt]
  have hΔ0 : 0 < r - s := sub_pos.2 hsr
  have hΔ1 : r - s ≤ 1 := by linarith
  have hinv1 : 1 ≤ (r - s)⁻¹ := (one_le_inv₀ hΔ0).2 hΔ1
  have hzp : (r - s) ^ (-((I.length : ℤ) + 1)) = ((r - s)⁻¹) ^ (I.length + 1) := by
    rw [show -((I.length : ℤ) + 1) = -((I.length + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
      zpow_natCast, inv_pow]
  rw [hzp]
  have hCle : CI I ≤ 1 + ∑ J ∈ repWords q N, CI J := by
    have : CI I ≤ ∑ J ∈ repWords q N, CI J :=
      Finset.single_le_sum (f := CI) (fun J _ => hCI0 J) (mem_repWords.2 hI)
    linarith
  have hpow : ((r - s)⁻¹) ^ (I.length + 1) ≤ ((r - s)⁻¹) ^ (N + 1) :=
    pow_le_pow_right₀ hinv1 (by omega)
  exact mul_le_mul hCle hpow (pow_nonneg (inv_nonneg.2 hΔ0.le) _) (by linarith)

end Cutoff

theorem holderENorm_forcingJet_le {n' q : ℕ} {X : Fin q → (Fin n' → ℝ) → (Fin n' → ℝ)}
    {d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞} {α : ℝ} (hα : 0 ≤ α) (V B : Set (Fin n' → ℝ))
    (ζ : (Fin n' → ℝ) → ℝ) (Du Df : List (Fin q) → (Fin n' → ℝ) → ℝ) (K : List (Fin q)) :
    holderENorm d α V (forcingJet X B ζ Du Df K) ≤ holderENorm d α V (leibJet X B ζ Df K) +
      ∑ i : Fin q, (holderENorm d α V
          (leibJet X B (fieldDerivative (X i) ζ) (fun K' => Du (K' ++ [i])) K) +
        holderENorm d α V (leibJet X B (fieldDerivative (X i) ζ) (fun K' => Du (K' ++ [i])) K) +
        holderENorm d α V (leibJet X B (fieldDerivative (X i) (fieldDerivative (X i) ζ)) Du K)) := by
  unfold forcingJet
  refine (holderENorm_add_le hα _ _).trans (add_le_add le_rfl
    ((holderENorm_sum_le hα _ _).trans (Finset.sum_le_sum fun i _ => ?_)))
  exact (holderENorm_add_le hα _ _).trans (add_le_add (holderENorm_add_le hα _ _) le_rfl)

/-- Arithmetic of the step: the constants combine to `Λ (A₁ (3q + 1) + A₂) c'`. -/
theorem stage_arith {Λ A1 A2 c' : ℝ} {q : ℕ} (hΛ : 0 ≤ Λ) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (_hc' : 0 ≤ c') {JF JD Jfv Jv : ℝ≥0∞}
    (hfv : Jfv ≤ ENNReal.ofReal A1 * ENNReal.ofReal c' * (JF + JD) * (1 + 3 * (q : ℝ≥0∞)))
    (hv : Jv ≤ ENNReal.ofReal A2 * ENNReal.ofReal c' * JD) :
    ENNReal.ofReal Λ * (Jfv + Jv) ≤
      ENNReal.ofReal (Λ * (A1 * (3 * q + 1) + A2) * c') * (JF + JD) := by
  have e1 : (1 + 3 * (q : ℝ≥0∞)) = ENNReal.ofReal (3 * q + 1) := by
    rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_natCast, ENNReal.ofReal_one, ENNReal.ofReal_ofNat, add_comm]
  have hJD : ENNReal.ofReal A2 * ENNReal.ofReal c' * JD ≤
      ENNReal.ofReal A2 * ENNReal.ofReal c' * (JF + JD) := mul_le_mul' le_rfl le_add_self
  calc ENNReal.ofReal Λ * (Jfv + Jv)
      ≤ ENNReal.ofReal Λ * (ENNReal.ofReal A1 * ENNReal.ofReal c' * (JF + JD) *
          ENNReal.ofReal (3 * q + 1) + ENNReal.ofReal A2 * ENNReal.ofReal c' * (JF + JD)) :=
        mul_le_mul' le_rfl (add_le_add (hfv.trans (le_of_eq (by rw [e1]))) (hv.trans hJD))
    _ = ENNReal.ofReal (Λ * (A1 * (3 * q + 1) + A2) * c') * (JF + JD) := by
        have h1 : ENNReal.ofReal (Λ * (A1 * (3 * q + 1) + A2) * c') =
            ENNReal.ofReal Λ * (ENNReal.ofReal A1 * ENNReal.ofReal (3 * q + 1) +
              ENNReal.ofReal A2) * ENNReal.ofReal c' := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_add (by positivity) hA2, ENNReal.ofReal_mul hA1]
        rw [h1]
        ring


end RothschildStein.P2.HigherHolder
