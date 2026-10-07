-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HolderInterpolationLocal
public import RothschildStein.P2.HolderInterpolationDerivative
public import RothschildStein.P2.Iteration

/-!
# Iteration and the nested interpolation inequality

The nested Hölder interpolation inequality (BB Thm 11.53, pp. 596–597, (11.87)). With
`ψ(t) = ∑_l ‖X̃_l u‖_{C^α(U_t^ρ)}` the localization step (`nested_step`) gives, for `0 < t < s ≤ R` and every
`0 < ε < 1`, `ψ(t) ≤ ε (‖L̃u‖_∞ + 2 b₁ (s-t)⁻¹ ψ(s) + b₂ (s-t)⁻² ‖u‖_∞) + Cc ε^{-γ} ‖u‖_∞`. Choosing `ε`
a small fixed multiple of `δ (s - t)` makes the coefficient of `ψ(s)` smaller than `1/3`, the data coefficient a
fixed multiple of `δ`, and the remainder `C δ^{-γ'} (s-t)^{-γ'}`, `γ' = γ + 2` (using `s - t ≤ 1`). The
iteration lemma (`exists_iteration_third`) and a rescaling of `δ` give the stated inequality
(`nested_arith`, a statement about real numbers only).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

/-- The one-step arithmetic: with `ε = κ a`, `a = s - t ≤ 1`, `0 < κ < 1`
the compact interpolation inequality gives `ψ(t) ≤ 2 b₁ κ ψ(s) + (κ b₂ + Cc₁ κ^{-γ₁}) ‖u‖ a^{-(γ₁+2)} +
κ ‖L̃u‖`. -/
theorem nested_onestep {b₁ b₂ Cc₁ γ₁ κ ML Mu a ψt ψs : ℝ} (hb₂ : 0 ≤ b₂) (hCc₁ : 0 ≤ Cc₁)
    (hγ₁ : 1 < γ₁) (hκ : 0 < κ) (ha0 : 0 < a) (ha1 : a ≤ 1) (hML : 0 ≤ ML) (hMu : 0 ≤ Mu)
    (hmain : ψt ≤ κ * a * (ML + 2 * b₁ * a⁻¹ * ψs + b₂ * (a ^ 2)⁻¹ * Mu) +
      Cc₁ * (κ * a) ^ (-γ₁) * Mu) :
    ψt ≤ 2 * b₁ * κ * ψs + (κ * b₂ + Cc₁ * κ ^ (-γ₁)) * Mu * a ^ (-(γ₁ + 2)) + κ * ML := by
  have i1 : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0.ne'
  have i2 : a * (a ^ 2)⁻¹ = a⁻¹ := by
    rw [sq, mul_inv, ← mul_assoc, mul_inv_cancel₀ ha0.ne', one_mul]
  have hεpow : (κ * a) ^ (-γ₁) = κ ^ (-γ₁) * a ^ (-γ₁) := Real.mul_rpow hκ.le ha0.le
  have hexp : κ * a * (ML + 2 * b₁ * a⁻¹ * ψs + b₂ * (a ^ 2)⁻¹ * Mu) +
      Cc₁ * (κ * a) ^ (-γ₁) * Mu =
      κ * a * ML + 2 * b₁ * κ * ψs + κ * b₂ * a⁻¹ * Mu + Cc₁ * κ ^ (-γ₁) * a ^ (-γ₁) * Mu := by
    rw [hεpow]
    linear_combination (2 * b₁ * κ * ψs) * i1 + (κ * b₂ * Mu) * i2
  have p1 : a⁻¹ ≤ a ^ (-(γ₁ + 2)) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge ha0 ha1 (by linarith)
  have p2 : a ^ (-γ₁) ≤ a ^ (-(γ₁ + 2)) :=
    Real.rpow_le_rpow_of_exponent_ge ha0 ha1 (by linarith)
  have hrpow0 : 0 ≤ κ ^ (-γ₁) := Real.rpow_nonneg hκ.le _
  have q1 : κ * a * ML ≤ κ * ML := by
    have h1 : κ * a ≤ κ * 1 := mul_le_mul_of_nonneg_left ha1 hκ.le
    calc κ * a * ML ≤ κ * 1 * ML := mul_le_mul_of_nonneg_right h1 hML
      _ = κ * ML := by ring
  have q2 : κ * b₂ * a⁻¹ * Mu ≤ κ * b₂ * a ^ (-(γ₁ + 2)) * Mu :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left p1 (mul_nonneg hκ.le hb₂)) hMu
  have q3 : Cc₁ * κ ^ (-γ₁) * a ^ (-γ₁) * Mu ≤ Cc₁ * κ ^ (-γ₁) * a ^ (-(γ₁ + 2)) * Mu :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left p2 (mul_nonneg hCc₁ hrpow0)) hMu
  linarith [hmain, hexp, q1, q2, q3]

/-- The rescaling of the data coefficient (`κ = c₁ δ'`,
`δ' = δ / (1 + Cit c₁)`): `Cit (κ b₂ + Cc₁ κ^{-γ₁}) ≤ Cn' δ^{-(γ₁+2)}`. -/
theorem nested_coef {b₂ Cc₁ γ₁ c₁ Cit δ δ' κ : ℝ} (hb₂ : 0 ≤ b₂) (hCc₁ : 0 ≤ Cc₁)
    (hγ₁ : 1 < γ₁) (hc₁ : 0 < c₁) (hCit : 0 < Cit) (hδ0 : 0 < δ) (hδ3 : δ < 1 / 3)
    (hδ' : δ' = δ / (1 + Cit * c₁)) (hκ : κ = c₁ * δ') :
    Cit * (κ * b₂ + Cc₁ * κ ^ (-γ₁)) ≤
      (Cit * (c₁ * b₂ + Cc₁ * c₁ ^ (-γ₁) * (1 + Cit * c₁) ^ γ₁) + 1) * δ ^ (-(γ₁ + 2)) := by
  have hden : 0 < 1 + Cit * c₁ := by positivity
  have hδ'0 : 0 < δ' := by rw [hδ']; positivity
  have hδ'δ : δ' ≤ δ := by
    rw [hδ', div_le_iff₀ hden]
    nlinarith [mul_pos hδ0 (mul_pos hCit hc₁)]
  have hδ'pow : δ' ^ (-γ₁) = δ ^ (-γ₁) * (1 + Cit * c₁) ^ γ₁ := by
    rw [hδ', Real.div_rpow hδ0.le hden.le, Real.rpow_neg hden.le, div_inv_eq_mul]
  have hδβ : δ ^ (-γ₁) ≤ δ ^ (-(γ₁ + 2)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ0 (by linarith) (by linarith)
  have hδ1 : δ ≤ δ ^ (-(γ₁ + 2)) := by
    have : 1 ≤ δ ^ (-(γ₁ + 2)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ0 (by linarith) (by linarith)
    linarith
  have hκpow : κ ^ (-γ₁) = c₁ ^ (-γ₁) * δ' ^ (-γ₁) := by
    rw [hκ]
    exact Real.mul_rpow hc₁.le hδ'0.le
  have e1 : κ * b₂ ≤ c₁ * b₂ * δ ^ (-(γ₁ + 2)) := by
    rw [hκ]
    calc c₁ * δ' * b₂ ≤ c₁ * δ * b₂ := by gcongr
      _ = c₁ * b₂ * δ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hδ1 (by positivity)
  have e2 : Cc₁ * κ ^ (-γ₁) ≤ Cc₁ * c₁ ^ (-γ₁) * (1 + Cit * c₁) ^ γ₁ * δ ^ (-(γ₁ + 2)) := by
    rw [hκpow, hδ'pow]
    have h0 : 0 ≤ Cc₁ * c₁ ^ (-γ₁) * (1 + Cit * c₁) ^ γ₁ := by
      have := Real.rpow_nonneg hc₁.le (-γ₁)
      have := Real.rpow_nonneg hden.le γ₁
      positivity
    calc Cc₁ * (c₁ ^ (-γ₁) * (δ ^ (-γ₁) * (1 + Cit * c₁) ^ γ₁)) =
          Cc₁ * c₁ ^ (-γ₁) * (1 + Cit * c₁) ^ γ₁ * δ ^ (-γ₁) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hδβ h0
  have hδβ0 : 0 ≤ δ ^ (-(γ₁ + 2)) := Real.rpow_nonneg hδ0.le _
  calc Cit * (κ * b₂ + Cc₁ * κ ^ (-γ₁))
      ≤ Cit * (c₁ * b₂ * δ ^ (-(γ₁ + 2)) +
          Cc₁ * c₁ ^ (-γ₁) * (1 + Cit * c₁) ^ γ₁ * δ ^ (-(γ₁ + 2))) :=
        mul_le_mul_of_nonneg_left (add_le_add e1 e2) hCit.le
    _ = Cit * (c₁ * b₂ + Cc₁ * c₁ ^ (-γ₁) * (1 + Cit * c₁) ^ γ₁) * δ ^ (-(γ₁ + 2)) := by ring
    _ ≤ _ := by linarith

/-- The data term: `Cit κ ‖L̃u‖ ≤ δ ‖L̃u‖` for `κ = c₁ δ'`,
`δ' = δ / (1 + Cit c₁)`. -/
theorem nested_data {c₁ Cit δ δ' κ ML : ℝ} (hCit : 0 < Cit) (hc₁ : 0 < c₁) (hML : 0 ≤ ML)
    (hδ' : δ' = δ / (1 + Cit * c₁)) (hκ : κ = c₁ * δ') (hδ0 : 0 < δ) :
    Cit * (κ * ML) ≤ δ * ML := by
  have hden : 0 < 1 + Cit * c₁ := by positivity
  have h1 : Cit * κ ≤ δ := by
    rw [hκ, hδ', ← mul_assoc, mul_div_assoc', div_le_iff₀ hden]
    nlinarith [hδ0]
  calc Cit * (κ * ML) = (Cit * κ) * ML := by ring
    _ ≤ δ * ML := mul_le_mul_of_nonneg_right h1 hML

/-- **The arithmetic of the nested interpolation** (choose `ε` a
sufficiently small fixed multiple of `δ (s - t)`, apply the iteration and rescale `δ`). For constants
`b₁, b₂, Cc₁ ≥ 0` and `γ₁ > 1` there is `Cn > 0` such that every function `ψ`, bounded above on `[r, R]`,
satisfying the one-step inequality for `r ≤ t < s ≤ R ≤ 1` and all `0 < ε < 1` satisfies
`ψ(r) ≤ δ ML + Cn δ^{-(γ₁+2)} (R - r)^{-(γ₁+2)} Mu` for `0 < δ < 1/3`. -/
theorem nested_arith {b₁ b₂ Cc₁ γ₁ : ℝ} (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hCc₁ : 0 ≤ Cc₁)
    (hγ₁ : 1 < γ₁) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (ψ : ℝ → ℝ) (R r ML Mu δ : ℝ), 0 ≤ ML → 0 ≤ Mu → 0 < r → r < R → R ≤ 1 →
      0 < δ → δ < 1 / 3 → (∃ K, ∀ t ∈ Icc r R, ψ t ≤ K) →
      (∀ t s : ℝ, r ≤ t → t < s → s ≤ R → ∀ ε : ℝ, 0 < ε → ε < 1 →
        ψ t ≤ ε * (ML + 2 * b₁ * (s - t)⁻¹ * ψ s + b₂ * ((s - t) ^ 2)⁻¹ * Mu) +
          Cc₁ * ε ^ (-γ₁) * Mu) →
      ψ r ≤ δ * ML + Cn * δ ^ (-(γ₁ + 2)) * (R - r) ^ (-(γ₁ + 2)) * Mu := by
  obtain ⟨Cit, hCit0, hCit⟩ := exists_iteration_third (β := γ₁ + 2) (by linarith)
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = 1 / (2 * b₁ + 1) := ⟨_, rfl⟩
  have hc₁0 : 0 < c₁ := by rw [hc₁]; positivity
  have hc₁1 : c₁ ≤ 1 := by
    rw [hc₁, div_le_one (by positivity)]
    linarith
  have h2bc : 2 * b₁ * c₁ ≤ 1 := by
    rw [hc₁, mul_one_div, div_le_one (by positivity)]
    linarith
  have hden : 0 < 1 + Cit * c₁ := by positivity
  refine ⟨Cit * (c₁ * b₂ + Cc₁ * c₁ ^ (-γ₁) * (1 + Cit * c₁) ^ γ₁) + 1, ?_, ?_⟩
  · have h1 := Real.rpow_nonneg hc₁0.le (-γ₁)
    have h2 := Real.rpow_nonneg hden.le γ₁
    positivity
  intro ψ R r ML Mu δ hML hMu hr hrR hR1 hδ0 hδ3 hK h
  obtain ⟨δ', hδ'⟩ : ∃ δ', δ' = δ / (1 + Cit * c₁) := ⟨_, rfl⟩
  have hδ'0 : 0 < δ' := by rw [hδ']; positivity
  have hδ'δ : δ' ≤ δ := by
    rw [hδ', div_le_iff₀ hden]
    nlinarith [mul_pos hδ0 (mul_pos hCit0 hc₁0)]
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = c₁ * δ' := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hκδ : κ ≤ δ' := by
    rw [hκ]
    calc c₁ * δ' ≤ 1 * δ' := mul_le_mul_of_nonneg_right hc₁1 hδ'0.le
      _ = δ' := one_mul _
  have hκ1 : κ < 1 := by linarith
  have hθ0 : 0 ≤ 2 * b₁ * κ := by positivity
  have hθ3 : 2 * b₁ * κ < 1 / 3 := by
    have : 2 * b₁ * κ ≤ δ' := by
      rw [hκ]
      calc 2 * b₁ * (c₁ * δ') = (2 * b₁ * c₁) * δ' := by ring
        _ ≤ 1 * δ' := mul_le_mul_of_nonneg_right h2bc hδ'0.le
        _ = δ' := one_mul _
    linarith
  have hrpow0 : 0 ≤ κ ^ (-γ₁) := Real.rpow_nonneg hκ0.le _
  have hA0 : 0 ≤ (κ * b₂ + Cc₁ * κ ^ (-γ₁)) * Mu :=
    mul_nonneg (add_nonneg (mul_nonneg hκ0.le hb₂) (mul_nonneg hCc₁ hrpow0)) hMu
  have hB0 : 0 ≤ κ * ML := mul_nonneg hκ0.le hML
  have hstep : ∀ t s : ℝ, r ≤ t → t < s → s ≤ R →
      ψ t ≤ 2 * b₁ * κ * ψ s + (κ * b₂ + Cc₁ * κ ^ (-γ₁)) * Mu * (s - t) ^ (-(γ₁ + 2)) + κ * ML := by
    intro t s htr hts hsR
    have ha0 : 0 < s - t := sub_pos.2 hts
    have ha1 : s - t ≤ 1 := by linarith
    have hε1 : κ * (s - t) < 1 :=
      calc κ * (s - t) ≤ κ * 1 := mul_le_mul_of_nonneg_left ha1 hκ0.le
        _ < 1 := by linarith
    exact nested_onestep hb₂ hCc₁ hγ₁ hκ0 ha0 ha1 hML hMu
      (h t s htr hts hsR (κ * (s - t)) (mul_pos hκ0 ha0) hε1)
  have hit := hCit (2 * b₁ * κ) hθ0 hθ3 ψ r R ((κ * b₂ + Cc₁ * κ ^ (-γ₁)) * Mu) (κ * ML) hA0 hB0 hK
    hstep r R le_rfl hrR le_rfl
  have hcoef := nested_coef hb₂ hCc₁ hγ₁ hc₁0 hCit0 hδ0 hδ3 hδ' hκ
  have hdata := nested_data hCit0 hc₁0 hML hδ' hκ hδ0
  have hRr : 0 ≤ (R - r) ^ (-(γ₁ + 2)) := Real.rpow_nonneg (sub_pos.2 hrR).le _
  calc ψ r ≤ Cit * ((κ * b₂ + Cc₁ * κ ^ (-γ₁)) * Mu * (R - r) ^ (-(γ₁ + 2)) + κ * ML) := hit
    _ = Cit * (κ * b₂ + Cc₁ * κ ^ (-γ₁)) * Mu * (R - r) ^ (-(γ₁ + 2)) + Cit * (κ * ML) := by ring
    _ ≤ (Cit * (c₁ * b₂ + Cc₁ * c₁ ^ (-γ₁) * (1 + Cit * c₁) ^ γ₁) + 1) * δ ^ (-(γ₁ + 2)) * Mu *
          (R - r) ^ (-(γ₁ + 2)) + δ * ML :=
        add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hMu) hRr) hdata
    _ = _ := by ring

variable {n q st m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart driftWeight st Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {q₀ : ℕ} {H : H1.StandingHypotheses C.G q₀} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- **The nested interpolation inequality** (BB Thm 11.53, pp. 596-597,
(11.87)). Conditional exactly on the hypotheses of the derivative representations
(`LeftDifferentiation`, `SignedParametrix`, the density data `c`) on a standard frame and on the `(HD)` package `G` of the
lifted control distance (`LiftedChart.distanceGeometry`). For `0 < α < 1`, a smooth gauge `ν`, and a chart centre `ξ₀` there are a
threshold `R_* ≤ 1`, `γ > 1` and `C_n` such that for `0 < R ≤ R_*` with `U_R^ρ ⊆ V` and `a = 1` on `U_R^ρ`
(`a` the cutoff of the representation), every `u ∈ C^{2,α}_{X̃}(V)` with Hölder weak jet `D`, `0 < r < R`
and `0 < δ < 1/3`:
`∑_l ‖X̃_l u‖_{C^α(U_r^ρ)} ≤ δ ‖L̃u‖_{L^∞(U_R^ρ)} + C_n δ^{-γ} (R - r)^{-γ} ‖u‖_{L^∞(U_R^ρ)}`. -/
theorem exists_nestedInterpolation_of_representation (hF : C.IsStandardFrame F H K hQ)
    (hLeftDiff : LeftDifferentiation F driftWeight C.Xl)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrix F C.Xl c a b)
    (Ω₂ : Opens (Fin (n + m) → ℝ)) (G : S.DistanceGeometry Ω₂) (hG : G.d = C.dl)
    (hV : (F.V : Set (Fin (n + m) → ℝ)) ⊆ (Ω₂ : Set (Fin (n + m) → ℝ)))
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth) {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ Rstar γ Cn : ℝ, 0 < Rstar ∧ Rstar ≤ 1 ∧ 1 < γ ∧ 0 < Cn ∧
      ∀ R : ℝ, 0 < R → R ≤ Rstar → rhoBall C ν ξ₀ R ⊆ (F.V : Set (Fin (n + m) → ℝ)) →
        (∀ x ∈ rhoBall C ν ξ₀ R, a x = 1) →
        ∀ (u : (Fin (n + m) → ℝ) → ℝ) (D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ),
          memHolderX driftWeight C.Xl C.dl F.V 2 α u →
          LiftedChart.IsHolderWeakJet driftWeight C.Xl C.dl F.V 2 α u D →
          ∀ r : ℝ, 0 < r → r < R → ∀ δ : ℝ, 0 < δ → δ < 1 / 3 →
            ∑ l : Fin q, holderENorm C.dl α (rhoBall C ν ξ₀ r) (D [l.succ]) ≤
              ENNReal.ofReal δ * (⨆ x : rhoBall C ν ξ₀ R,
                  ENNReal.ofReal |weakSumSquaresWithDrift D x|) +
                ENNReal.ofReal (Cn * δ ^ (-γ) * (R - r) ^ (-γ)) *
                  ⨆ x : rhoBall C ν ξ₀ R, ENNReal.ofReal |u x| := by
  classical
  obtain ⟨γ₁, Cc₁, hγ₁, hCc₁, hder⟩ := exists_derivativeInterpolation_of_representation hF hLeftDiff hc
    hc0 a hParametrix Ω₂ G hG hV hα0 hα1
  obtain ⟨rstar, b₁, b₂, hr0, hr1, hb₁, hb₂, hqual, hζb1, hζb2⟩ := exists_cutoff_data C ν hν hξ₀
  obtain ⟨Cn, hCn, harith⟩ := nested_arith hb₁ hb₂ hCc₁.le hγ₁
  refine ⟨rstar / 2, γ₁ + 2, Cn, by linarith, by linarith, by linarith, hCn, ?_⟩
  intro R hR0 hRstar hBV ha1 u D hu hD r hr0' hrR δ hδ0 hδ3
  have hw : ∀ j : Fin q, ((driftWeight j.succ : ℕ+) : ℕ) = 1 := fun j => by
    simp [driftWeight, Fin.succ_ne_zero]
  have hw0 : ((driftWeight (0 : Fin (q + 1)) : ℕ+) : ℕ) = 2 := by simp [driftWeight]
  have hRr : R < rstar := by linarith
  have hu' : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) u ≠ ⊤ := ne_top_of_lt hu.1
  have hLD : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (weakSumSquaresWithDrift D) ≠ ⊤ :=
    hD.weakSumSquaresWithDrift_ne_top hw0 hw hα0
  have hDfin : ∀ i : Fin q, holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (D [i.succ]) ≠ ⊤ :=
    fun i => (hD [i.succ] (LiftedChart.horizontal_mem_wordFamily (w := driftWeight) hw i)).2
  have hfinR : ∑ l : Fin q, holderENorm C.dl α (rhoBall C ν ξ₀ R) (D [l.succ]) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun l _ => holderENorm_ball_ne_top ν (hDfin l) hBV
  have hfinr : ∑ l : Fin q, holderENorm C.dl α (rhoBall C ν ξ₀ r) (D [l.succ]) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun l _ => holderENorm_ball_ne_top ν (hDfin l)
      ((rhoBall_mono C ν ξ₀ hrR.le).trans hBV)
  have hK : ∃ K, ∀ t ∈ Icc r R, psiBall C ν ξ₀ α D t ≤ K := by
    refine ⟨psiBall C ν ξ₀ α D R, fun t ht => ?_⟩
    exact ENNReal.toReal_mono hfinR (Finset.sum_le_sum fun l _ =>
      S.holderENorm_mono C.dl α _ _ (rhoBall_mono C ν ξ₀ ht.2))
  have hstep : ∀ t s : ℝ, r ≤ t → t < s → s ≤ R → ∀ ε : ℝ, 0 < ε → ε < 1 →
      psiBall C ν ξ₀ α D t ≤
        ε * (supBall C ν ξ₀ (weakSumSquaresWithDrift D) R +
            2 * b₁ * (s - t)⁻¹ * psiBall C ν ξ₀ α D s +
              b₂ * ((s - t) ^ 2)⁻¹ * supBall C ν ξ₀ u R) +
          Cc₁ * ε ^ (-γ₁) * supBall C ν ξ₀ u R :=
    fun t s htr hts hsR ε hε0 hε1 => nested_step hF.lifted Ω₂ G hG hV ν hξ₀ hα0 hα1 hder hCc₁.le hb₁
      hb₂ hqual hζb1 hζb2 hRr hBV ha1 hu' hD (lt_of_lt_of_le hr0' htr) hts hsR hε0 hε1
  have hres := harith (psiBall C ν ξ₀ α D) R r (supBall C ν ξ₀ (weakSumSquaresWithDrift D) R)
    (supBall C ν ξ₀ u R) δ (supBall_nonneg C ν ξ₀ _ R) (supBall_nonneg C ν ξ₀ _ R) hr0' hrR
    (by linarith) hδ0 hδ3 hK hstep
  have hML : ENNReal.ofReal (supBall C ν ξ₀ (weakSumSquaresWithDrift D) R) =
      ⨆ x : rhoBall C ν ξ₀ R, ENNReal.ofReal |weakSumSquaresWithDrift D x| :=
    ENNReal.ofReal_toReal (supBall_ne_top ν hLD hBV)
  have hMu : ENNReal.ofReal (supBall C ν ξ₀ u R) =
      ⨆ x : rhoBall C ν ξ₀ R, ENNReal.ofReal |u x| :=
    ENNReal.ofReal_toReal (supBall_ne_top ν hu' hBV)
  have hCδ0 : 0 ≤ Cn * δ ^ (-(γ₁ + 2)) * (R - r) ^ (-(γ₁ + 2)) :=
    mul_nonneg (mul_nonneg hCn.le (Real.rpow_nonneg hδ0.le _))
      (Real.rpow_nonneg (sub_pos.2 hrR).le _)
  calc ∑ l : Fin q, holderENorm C.dl α (rhoBall C ν ξ₀ r) (D [l.succ])
      = ENNReal.ofReal (psiBall C ν ξ₀ α D r) := (ENNReal.ofReal_toReal hfinr).symm
    _ ≤ ENNReal.ofReal (δ * supBall C ν ξ₀ (weakSumSquaresWithDrift D) R +
          Cn * δ ^ (-(γ₁ + 2)) * (R - r) ^ (-(γ₁ + 2)) * supBall C ν ξ₀ u R) :=
        ENNReal.ofReal_le_ofReal hres
    _ = ENNReal.ofReal δ * ENNReal.ofReal (supBall C ν ξ₀ (weakSumSquaresWithDrift D) R) +
          ENNReal.ofReal (Cn * δ ^ (-(γ₁ + 2)) * (R - r) ^ (-(γ₁ + 2))) *
            ENNReal.ofReal (supBall C ν ξ₀ u R) := by
        rw [ENNReal.ofReal_add (mul_nonneg hδ0.le (supBall_nonneg C ν ξ₀ _ R))
          (mul_nonneg hCδ0 (supBall_nonneg C ν ξ₀ _ R)), ENNReal.ofReal_mul hδ0.le,
          ENNReal.ofReal_mul hCδ0]
    _ = _ := by rw [hML, hMu]

end RothschildStein.P2
