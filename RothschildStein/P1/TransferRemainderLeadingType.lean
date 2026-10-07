-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TransferRemainderCoefficientType
public import RothschildStein.P1.PrincipalLeadingSum
public import RothschildStein.P1.CoordinateFieldHomogeneity

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

/-- The complete transfer remainder coefficient times
any actual coordinate-leading principal term has type λ+1-w_i. -/
theorem LiftedChart.isTypeKernel_transfer_remainder_coordinate_principal
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hG : F.G = C.G)
    (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (t P : PrincipalTerm F) (i : Fin k) (j : Fin (n + m)) (lam : ℕ)
    (hw : (w i : ℕ) ≤ lam) (hd : t.degree ≤ 2 - (lam : ℤ))
    (hP : P.degree ≤ t.degree + (F.G.weight j : ℤ)) (hstar : P.star = t.star)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole t.star (F.G.dilate r u) = r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole t.star u) :
    IsTypeKernel F (lam + 1 - (w i : ℕ))
      (fun ξ η => C.generatorTransferRemainder i ξ η (F.Θ η ξ) j * P.kernel ξ η) := by
  have hdegree : P.degree - (1 - ((w i : ℕ) : ℤ) + (F.G.weight j : ℤ)).toNat ≤
      2 - ((lam + 1 - (w i : ℕ) : ℕ) : ℤ) := by omega
  have h := C.isTypeKernel_transfer_remainder_coefficient F hΘ hG hVU P i j
    (lam + 1 - (w i : ℕ)) hdegree (by simpa only [hstar] using hΓ)
    (by simpa only [hstar] using hhom)
  convert h using 1
  funext ξ η
  simp only [PrincipalTerm.kernel, PrincipalTerm.modelKernel]
  ring

/-- The complete transfer remainder coefficient R_j times the
constructed full jth coordinate derivative has the sharp remainder type,
without requiring weight(j)≤λ. -/
theorem LiftedChart.isTypeKernel_transfer_remainder_times_leadingKernel
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hG : F.G = C.G)
    (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (t : PrincipalTerm F) (i : Fin k) (j : Fin (n + m)) (lam : ℕ)
    (hw : (w i : ℕ) ≤ lam) (hd : t.degree ≤ 2 - (lam : ℤ))
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole t.star (F.G.dilate r u) = r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole t.star u) :
    IsTypeKernel F (lam + 1 - (w i : ℕ)) (fun ξ η => C.generatorTransferRemainder i ξ η (F.Θ η ξ) j *
      t.leadingKernel (fun _ => Pi.single j 1) contDiff_const (F.G.weight j : ℤ)
        (coordinateField_homogeneous F.G j) ξ η) := by
  classical
  simp only [PrincipalTerm.leadingKernel, Finset.mul_sum, mul_add]
  apply IsTypeKernel.sum
  intro α _
  apply IsTypeKernel.sum
  intro l _
  apply IsTypeKernel.add
  · exact C.isTypeKernel_transfer_remainder_coordinate_principal F hΘ hG hVU t
      (t.leadingCoefficientDerivative α.val α.property l (fun _ => Pi.single j 1)
        contDiff_const (F.G.weight j : ℤ) (coordinateField_homogeneous F.G j)) i j lam hw hd
      le_rfl rfl hΓ hhom
  · exact C.isTypeKernel_transfer_remainder_coordinate_principal F hΘ hG hVU t
      (t.leadingPoleDerivative α.val α.property l (fun _ => Pi.single j 1)
        contDiff_const (F.G.weight j : ℤ) (coordinateField_homogeneous F.G j)) i j lam hw hd
      le_rfl rfl hΓ hhom

end RothschildStein.P1
