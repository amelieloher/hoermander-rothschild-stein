-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ChartRemainderLeadingType

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.P1
variable {N : ℕ} {F : KernelFrame N}

/-- Every constructed leading contribution
vanishes when either endpoint cutoff vanishes, including at the model origin. -/
theorem PrincipalTerm.leadingKernel_eq_zero_of_cutoff (t : PrincipalTerm F)
    (Y : (Fin N → ℝ) → (Fin N → ℝ)) (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    (w : ℤ) (hhY : G2.IsHomogeneousField F.G Y w) (ξ η : Fin N → ℝ)
    (hzero : t.a ξ = 0 ∨ t.b η = 0) : t.leadingKernel Y hY w hhY ξ η = 0 := by
  classical
  rcases hzero with ha | hb
  · simp [PrincipalTerm.leadingKernel, PrincipalTerm.leadingCoefficientDerivative_kernel,
      PrincipalTerm.leadingPoleDerivative_kernel, ha]
  · simp [PrincipalTerm.leadingKernel, PrincipalTerm.leadingCoefficientDerivative_kernel,
      PrincipalTerm.leadingPoleDerivative_kernel, hb]

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The fourth term is an actual kernel of type
λ+1-w_i: type λ for horizontal fields and type λ-1 for drift. The proof
constructs the local Taylor decompositions and uses the actual chart jets;
no type assertion for this remainder is an input (BB Lemma 11.18, p. 549). -/
theorem LiftedChart.isTypeKernel_chart_remainder_derivative
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hG : F.G = C.G)
    (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (t : PrincipalTerm F) (i : Fin k) (lam : ℕ)
    (hw : (w i : ℕ) ≤ lam) (hd : t.degree ≤ 2 - (lam : ℤ))
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole t.star (F.G.dilate r u) = r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole t.star u) :
    IsTypeKernel F (lam + 1 - (w i : ℕ)) (fun ξ η => t.a ξ * t.b η *
      fieldDerivative (C.R [i] η) (t.modelKernel ξ η) (F.Θ η ξ)) := by
  classical
  have hs := IsTypeKernel.sum (Finset.univ : Finset (Fin (n + m)))
    (fun j _ => C.isTypeKernel_remainder_times_leadingKernel F hΘ hG hVU t i j lam hw hd hΓ hhom)
  apply hs.congr_off_diagonal
  intro ξ η hne
  by_cases ha : t.a ξ = 0
  · have hz (j : Fin (n + m)) := t.leadingKernel_eq_zero_of_cutoff
      (fun _ => Pi.single j 1) contDiff_const (F.G.weight j : ℤ)
      (coordinateField_homogeneous F.G j) ξ η (Or.inl ha)
    simp [hz, ha]
  by_cases hb : t.b η = 0
  · have hz (j : Fin (n + m)) := t.leadingKernel_eq_zero_of_cutoff
      (fun _ => Pi.single j 1) contDiff_const (F.G.weight j : ℤ)
      (coordinateField_homogeneous F.G j) ξ η (Or.inr hb)
    simp [hz, hb]
  have hξ : ξ ∈ C.U := hVU (t.a.tsupport_subset (subset_tsupport t.a ha))
  have hη : η ∈ C.U := hVU (t.b.tsupport_subset (subset_tsupport t.b hb))
  have hu : F.Θ η ξ ≠ 0 := by
    rw [hΘ]
    exact (C.theta_eq_zero_iff hη hξ).not.mpr hne
  rw [fieldDerivative_coordinate_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [t.leadingKernel_eq (fun _ => Pi.single j 1) contDiff_const (F.G.weight j : ℤ)
    (coordinateField_homogeneous F.G j) hΓ ξ η hu]
  simp only [fieldDerivative]
  ring

end RothschildStein.P1
