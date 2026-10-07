-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.H2DataDMeasurable
public import RothschildStein.H2.KernelClass

/-!
# Data D2: from lifted kernel bounds to H2's volume-denominator kernel classes

`HasKernelBounds L ℓ κ` states the size bound `A d̃^{ℓ-Q}` and the difference bound
`S d̃(ξ, ξ')/d̃(ξ', η)^{Q+1-ℓ}` in powers of the lifted control distance `d̃`. H2's kernel class
(BB Def 7.10, p. 299) uses the volume denominator `V(x; y) = μ(B(x, d(x, y)))` instead:
`|K(x, y)| ≤ A d^ν / V(x; y)` and
`|K(x₀, y) - K(x, y)| ≤ S (d(x₀, y)^ν / V(x₀; y)) (d(x₀, x)/d(x₀, y))^β`.
Under the uniform volume bound `μ(B(y, t)) ≤ v₊ t^Q` one has
`d^{-Q} ≤ v₊ / V`, so the exponent `ℓ` kernel bounds give the kernel class with `ν = ℓ`, `β = 1`
and the constants `(A v₊, S v₊)` (BB pp. 572–576, Prop 11.33).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Metric MeasureTheory
namespace RothschildStein.P1

/-- Power form of the upper volume bound: `d^(e-Q) ≤ v₊ d^e / V` when
`V ≤ v₊ d^Q`. -/
theorem zpow_sub_le_of_volume {d V v : ℝ} (hd : 0 < d) (hV : 0 < V) (Q e : ℕ)
    (hVup : V ≤ v * d ^ Q) : d ^ ((e : ℤ) - (Q : ℤ)) ≤ v * (d ^ e / V) := by
  rw [zpow_sub₀ hd.ne', zpow_natCast, zpow_natCast, div_le_iff₀ (pow_pos hd Q)]
  have h1 : 1 ≤ v * d ^ Q / V := (one_le_div hV).mpr hVup
  calc d ^ e = d ^ e * 1 := (mul_one _).symm
    _ ≤ d ^ e * (v * d ^ Q / V) := mul_le_mul_of_nonneg_left h1 (pow_nonneg hd.le e)
    _ = v * (d ^ e / V) * d ^ Q := by ring

/-- `1 / d^(Q+1-e) = d^(e-Q) / d`. -/
theorem one_div_zpow_succ_sub {d : ℝ} (hd : 0 < d) (Q e : ℕ) :
    1 / d ^ ((Q : ℤ) + 1 - (e : ℤ)) = d ^ ((e : ℤ) - (Q : ℤ)) / d := by
  rw [one_div, ← zpow_neg, show -((Q : ℤ) + 1 - (e : ℤ)) = ((e : ℤ) - (Q : ℤ)) - 1 by ring,
    zpow_sub₀ hd.ne', zpow_one]

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- **Data D2.** A kernel with lifted bounds of exponent `ℓ` on the compact
`val '' closure Ω₂` is, on a measurable `E ⊆ Ω₁` of `d`-diameter at most `6κ` and for a Borel
measurable `carrierKernel κ`, a kernel of H2's class `KernelClass μ E 1 ℓ A S`: the powers of the
lifted distance are converted into H2's volume denominators `V(x; y) = μ(B(x, d(x, y)))` by the
uniform upper volume bound of the metric-measure certificate, `d^{-Q} ≤ v₊/V` (BB p. 299, (7.6)-(7.7)). `ℓ = 0` is the singular
class (`ν = 0`), `ℓ = 1` the fractional class (`ν = 1`). -/
theorem kernelClass_of_hasKernelBounds {S : H2.LocDoubling C.Carrier} {vLo vHi : ℝ}
    (hS : C.IsMetricMeasureCertificate S vLo vHi) {E : Set C.Carrier}
    (hEm : MeasurableSet E) (hEΩ : E ⊆ S.Ω₁) (hEd : ∀ x ∈ E, ∀ y ∈ E, dist x y ≤ 6 * S.κ)
    {ℓ : ℕ} {e : ℝ} (he : e = (ℓ : ℝ)) {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hb : C.HasKernelBounds (Carrier.val '' closure S.Ω₂) ℓ κ)
    (hmeas : Measurable (fun p : E × E => C.carrierKernel κ p.1.1 p.2.1)) :
    ∃ A S' : ℝ, H2.KernelClass S.μ E 1 e A S' (C.carrierKernel κ) := by
  obtain ⟨A, Sc, hA, hSc, hsize, hdiff⟩ := hb
  have hvHi : 0 < vHi := lt_of_lt_of_le hS.vLo_pos hS.vLo_le_vHi
  have hmemL : ∀ x ∈ E, x.val ∈ Carrier.val '' closure S.Ω₂ := fun x hx =>
    ⟨x, subset_closure (S.sub₁₂ (hEΩ hx)), rfl⟩
  have hvol : ∀ x ∈ E, ∀ d : ℝ, 0 < d → d ≤ 6 * S.κ → 0 < (S.μ (ball x d)).toReal ∧
      (S.μ (ball x d)).toReal ≤ vHi * d ^ C.G.homogeneousDimension := by
    intro x hx d hd hd6
    obtain ⟨hpos, hfin⟩ := hS.ball_pos_lt_top x (hEΩ hx) d hd hd6
    exact ⟨ENNReal.toReal_pos hpos.ne' hfin.ne, hS.volume_upper x (hEΩ hx) d hd hd6⟩
  refine ⟨A * vHi, Sc * vHi, hEm, hmeas, one_pos, le_rfl, he ▸ Nat.cast_nonneg ℓ,
    mul_nonneg hA hvHi.le, mul_nonneg hSc hvHi.le, ?_, ?_⟩
  · intro x hx y hy hxy
    rw [C.carrierKernel_of_ne hxy]
    have hd : 0 < dist x y := dist_pos.mpr hxy
    have h1 := hsize x.val (hmemL x hx) y.val (hmemL y hy) (fun h => hxy (Carrier.val_injective h))
    obtain ⟨hVpos, hVup⟩ := hvol x hx (dist x y) hd (hEd x hx y hy)
    have hdist : (C.dl x.val y.val).toReal = dist x y := rfl
    rw [hdist] at h1
    refine h1.trans ?_
    unfold H2.kernelWeight H2.volumeAt
    rw [he, Real.rpow_natCast]
    have h2 := zpow_sub_le_of_volume hd hVpos C.G.homogeneousDimension ℓ hVup
    calc A * dist x y ^ ((ℓ : ℤ) - (C.G.homogeneousDimension : ℤ))
        ≤ A * (vHi * (dist x y ^ ℓ / (S.μ (ball x (dist x y))).toReal)) :=
          mul_le_mul_of_nonneg_left h2 hA
      _ = A * vHi * (dist x y ^ ℓ / (S.μ (ball x (dist x y))).toReal) := by ring
  · intro x₀' hx₀ x hx y hy hsep
    have hd₀ : 0 < dist x₀' y :=
      lt_of_le_of_lt (mul_nonneg zero_le_two dist_nonneg) hsep
    have hne1 : x₀' ≠ y := fun h => by
      rw [h, dist_self] at hd₀
      exact lt_irrefl _ hd₀
    have hne2 : x ≠ y := by
      rintro rfl
      linarith [dist_nonneg (x := x₀') (y := x)]
    rw [C.carrierKernel_of_ne hne1, C.carrierKernel_of_ne hne2]
    have hsep' : 2 * (C.dl x.val x₀'.val).toReal < (C.dl x₀'.val y.val).toReal := by
      have e1 : (C.dl x.val x₀'.val).toReal = dist x₀' x := by rw [dist_comm]; rfl
      rw [e1]
      exact hsep
    have h := hdiff x.val (hmemL x hx) x₀'.val (hmemL x₀' hx₀) y.val (hmemL y hy) hsep'
    have e2 : (C.dl x.val x₀'.val).toReal = dist x₀' x := by rw [dist_comm]; rfl
    have e3 : (C.dl x₀'.val y.val).toReal = dist x₀' y := rfl
    rw [e2, e3] at h
    have h' : |κ x₀'.val y.val - κ x.val y.val| ≤
        Sc * dist x₀' x / dist x₀' y ^ ((C.G.homogeneousDimension : ℤ) + 1 - (ℓ : ℤ)) :=
      le_trans (le_add_of_nonneg_right (abs_nonneg _)) h
    obtain ⟨hVpos, hVup⟩ := hvol x₀' hx₀ (dist x₀' y) hd₀ (hEd x₀' hx₀ y hy)
    have h2 := zpow_sub_le_of_volume hd₀ hVpos C.G.homogeneousDimension ℓ hVup
    have h3 : Sc * dist x₀' x / dist x₀' y ^ ((C.G.homogeneousDimension : ℤ) + 1 - (ℓ : ℤ)) =
        Sc * dist x₀' x * (dist x₀' y ^ ((ℓ : ℤ) - (C.G.homogeneousDimension : ℤ)) /
          dist x₀' y) := by
      rw [← one_div_zpow_succ_sub hd₀, mul_one_div]
    refine h'.trans ?_
    rw [h3]
    unfold H2.kernelWeight H2.volumeAt
    rw [he, Real.rpow_natCast, Real.rpow_one]
    have h4 : Sc * dist x₀' x * (dist x₀' y ^ ((ℓ : ℤ) - (C.G.homogeneousDimension : ℤ)) /
          dist x₀' y) ≤ Sc * dist x₀' x * (vHi * (dist x₀' y ^ ℓ /
            (S.μ (ball x₀' (dist x₀' y))).toReal) / dist x₀' y) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h2 hd₀.le)
        (mul_nonneg hSc dist_nonneg)
    refine h4.trans (le_of_eq ?_)
    ring

end LiftedChart
end RothschildStein.P1
