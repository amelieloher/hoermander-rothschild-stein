-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.HomogeneousFiniteExtension
public import RothschildStein.P1.TaylorWordMonomial
public import RothschildStein.P1.WeightedTaylorJetLoss

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace RothschildStein.P1

variable {N : ℕ}

/-- Every nonempty coordinate monomial vanishes
at the origin, independently of the value assigned to the selected pole. -/
theorem taylorWordMonomial_zero_of_ne_nil (J : List (Fin N)) (hJ : J ≠ []) :
    taylorWordMonomial J (0 : Fin N → ℝ) = 0 := by
  cases J with
  | nil => exact (hJ rfl).elim
  | cons j J => simp only [taylorWordMonomial_cons, Pi.zero_apply, zero_mul]

/-- Multiplying a punctured homogeneous pole by a
sufficiently high-weight coordinate monomial gives a globally C^m function.
This is the actual homogeneous part of a finite Taylor remainder term. -/
theorem contDiff_taylorWordMonomial_mul_homogeneous (G : HomogeneousGroup N)
    (W m : ℕ) (hW : ∀ i, G.weight i ≤ W)
    (g : (Fin N → ℝ) → ℝ) (d : ℤ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin N → ℝ, u ≠ 0 →
      g (G.dilate r u) = r ^ d * g u)
    (J : List (Fin N)) (hJ : J ≠ [])
    (hd : (((m + 1) * W : ℕ) : ℤ) < ((J.map G.weight).sum : ℤ) + d) :
    ContDiff ℝ m (fun u => taylorWordMonomial J u * g u) := by
  apply contDiff_homogeneous_of_high_degree G W m hW _ _
    ((taylorWordMonomial_contDiff J).contDiffOn.mul hg) _ _ hd
  · intro r hr u hu
    rw [taylorWordMonomial_homogeneous, hhom r hr u hu]
    calc
      _ = (r ^ ((J.map G.weight).sum : ℤ) * r ^ d) *
          (taylorWordMonomial J u * g u) := by rw [zpow_natCast]; ring
      _ = _ := by rw [← zpow_add₀ hr.ne']
  · rw [taylorWordMonomial_zero_of_ne_nil J hJ, zero_mul]

/-- Jointly smooth Taylor remainder coefficients
preserve C^m regularity of the high-weight homogeneous factor. -/
theorem contDiff_weightedTaylor_remainder_term {P : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (G : HomogeneousGroup N) (W m : ℕ) (hW : ∀ i, G.weight i ≤ W)
    (g : (Fin N → ℝ) → ℝ) (d : ℤ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin N → ℝ, u ≠ 0 →
      g (G.dilate r u) = r ^ d * g u)
    (J : List (Fin N)) (hJ : J ≠ [])
    (hd : (((m + 1) * W : ℕ) : ℤ) < ((J.map G.weight).sum : ℤ) + d)
    (H : P × (Fin N → ℝ) → ℝ) (hH : ContDiff ℝ (⊤ : ℕ∞) H) :
    ContDiff ℝ m (fun q : P × (Fin N → ℝ) =>
      H q * (taylorWordMonomial J q.2 * g q.2)) :=
  (hH.of_le (by simp)).mul
    ((contDiff_taylorWordMonomial_mul_homogeneous G W m hW g d hg hhom J hJ hd).comp contDiff_snd)

end RothschildStein.P1
