-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalMonomialProduct
public import RothschildStein.P1.HighMonomialPrincipalRegular
public import RothschildStein.P1.KernelListSums
public import RothschildStein.P1.FiniteWeightedPatchExpansion

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.P1
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- Expanding only the smooth chart coefficient
produces a sharp lower-weight finite principal Taylor part and an actual
regular remainder. The operator coefficients stay inside their original
principal term (BB Lemma 11.16 and Lemma 11.18, pp. 548–549). -/
theorem LiftedChart.exists_weightedPrincipal_chart_expansion
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (t : PrincipalTerm F) (W budget b low : ℕ) (hW : ∀ j, F.G.weight j ≤ W) (hb : 0 < b)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole t.star (F.G.dilate r u) = r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole t.star u)
    (hd : ∀ α ∈ t.indices, (((budget + 1) * W : ℕ) : ℤ) < (b : ℤ) +
      (2 - (F.G.homogeneousDimension : ℤ) - ((∑ j, F.G.weight j * α j : ℕ) : ℤ)))
    (A : (((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) × (Fin (n + m) → ℝ)) → ℝ)
    (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hjet : ∀ p ∈ tsupport t.a ×ˢ tsupport t.b, ∀ I : List (Fin (n + m)),
      (I.map F.G.weight).sum < low → rsPartial I (fun u => A (p, u)) 0 = 0) :
    ∃ poly : List (List (Fin (n + m)) ×
        (((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) → ℝ)),
    ∃ r : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ,
      (∀ q ∈ poly, low ≤ (q.1.map F.G.weight).sum ∧
        (q.1.map F.G.weight).sum < b ∧ ContDiff ℝ (⊤ : ℕ∞) q.2) ∧
      IsRegularKernel F budget r ∧ ∀ ξ η,
        t.a ξ * t.b η * (A ((ξ, η), F.Θ η ξ) * t.modelKernel ξ η (F.Θ η ξ)) =
          (poly.map (fun q => q.2 (ξ, η) * taylorWordMonomial q.1 (F.Θ η ξ) *
            t.kernel ξ η)).sum + r ξ η := by
  classical
  obtain ⟨poly, rem, hp, hr, he⟩ := exists_finite_weighted_expansion_patch_lower_weight
    F.G (tsupport t.a ×ˢ tsupport t.b) b low A hA hjet
  let r := fun ξ η => (rem.map (fun q => t.a ξ * t.b η *
    (q.2 ((ξ, η), F.Θ η ξ) * taylorWordMonomial q.1 (F.Θ η ξ) *
      t.modelKernel ξ η (F.Θ η ξ)))).sum
  have hreg : IsRegularKernel F budget r := by
    apply IsRegularKernel.listSum
    intro q hq
    have hJ : q.1 ≠ [] := by
      intro hnil
      have hweight := (hr q hq).1
      rw [hnil] at hweight
      simp only [List.map_nil, List.sum_nil] at hweight
      omega
    apply C.isRegularKernel_highMonomial_principal F hΘ hVU t W budget hW q.1 hJ hΓ hhom
      (fun α hα => ?_) q.2 (hr q hq).2
    have hweight : (b : ℤ) ≤ ((q.1.map F.G.weight).sum : ℤ) := by exact_mod_cast (hr q hq).1
    have hbound := hd α hα
    omega
  refine ⟨poly, r, hp, hreg, ?_⟩
  intro ξ η
  by_cases ha : t.a ξ = 0
  · simp [ha, r, PrincipalTerm.kernel]
  by_cases hb' : t.b η = 0
  · simp [hb', r, PrincipalTerm.kernel]
  have h := he (ξ, η) ⟨subset_tsupport t.a ha, subset_tsupport t.b hb'⟩ (F.Θ η ξ)
  rw [h, add_mul, mul_add]
  have hpoly : t.a ξ * t.b η *
      ((poly.map (fun q => taylorWordMonomial q.1 (F.Θ η ξ) * q.2 (ξ, η))).sum *
        t.modelKernel ξ η (F.Θ η ξ)) =
      (poly.map (fun q => q.2 (ξ, η) * taylorWordMonomial q.1 (F.Θ η ξ) * t.kernel ξ η)).sum := by
    rw [← List.sum_map_mul_right, ← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro q _
    change t.a ξ * t.b η * ((taylorWordMonomial q.1 (F.Θ η ξ) * q.2 (ξ, η)) *
      t.modelKernel ξ η (F.Θ η ξ)) = _
    change _ = q.2 (ξ, η) * taylorWordMonomial q.1 (F.Θ η ξ) *
      (t.a ξ * t.b η * t.modelKernel ξ η (F.Θ η ξ))
    ring
  have hrem : t.a ξ * t.b η *
      ((rem.map (fun q => taylorWordMonomial q.1 (F.Θ η ξ) * q.2 ((ξ, η), F.Θ η ξ))).sum *
        t.modelKernel ξ η (F.Θ η ξ)) = r ξ η := by
    rw [← List.sum_map_mul_right, ← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro q _
    ring
  rw [hpoly, hrem]

end RothschildStein.P1
