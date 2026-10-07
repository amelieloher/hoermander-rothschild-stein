-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalModelKernel
public import RothschildStein.P1.PrincipalLeadingTerms
public import RothschildStein.P1.WeightedTaylorRegularTerm
public import RothschildStein.P1.ChartRegularKernel
public import RothschildStein.H1.FiniteCoordinateHomogeneity

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.P1
variable {N : ℕ} {F : KernelFrame N}

/-- A sufficiently high coordinate monomial
makes the whole actual finite principal model kernel jointly C^m.
The degree bound is checked for every effective pole partial (BB Lemma 11.16, pp. 548–549). -/
theorem PrincipalTerm.contDiff_highMonomial_model (t : PrincipalTerm F)
    (W budget : ℕ) (hW : ∀ j, F.G.weight j ≤ W)
    (J : List (Fin N)) (hJ : J ≠ [])
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin N → ℝ, u ≠ 0 →
      F.pole t.star (F.G.dilate r u) = r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole t.star u)
    (hd : ∀ α ∈ t.indices, (((budget + 1) * W : ℕ) : ℤ) <
      ((J.map F.G.weight).sum : ℤ) +
        (2 - (F.G.homogeneousDimension : ℤ) - ((∑ j, F.G.weight j * α j : ℕ) : ℤ)))
    (A : (((Fin N → ℝ) × (Fin N → ℝ)) × (Fin N → ℝ)) → ℝ)
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) :
    ContDiff ℝ budget (fun q : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ) =>
      A ((q.1, q.2.1), q.2.2) * taylorWordMonomial J q.2.2 * t.modelKernel q.1 q.2.1 q.2.2) := by
  classical
  have hpartial (α : Fin N → ℕ) : ContDiffOn ℝ (⊤ : ℕ∞)
      (euclideanPartial α (F.pole t.star)) {(0 : Fin N → ℝ)}ᶜ := by
    apply contDiffOn_iff_forall_nat_le.mpr
    intro m _
    exact H1.contDiffOn_euclideanPartial_finite
      ⟨{(0 : Fin N → ℝ)}ᶜ, isOpen_compl_singleton⟩ α m (F.pole t.star)
      (hΓ.of_le (by simp))
  have hterm (α : Fin N → ℕ) (hα : α ∈ t.indices) :
      ContDiff ℝ budget (fun q : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ) =>
        A ((q.1, q.2.1), q.2.2) * taylorWordMonomial J q.2.2 *
          ((t.D q.1 q.2.1).coefficient α q.2.2 * euclideanPartial α (F.pole t.star) q.2.2)) := by
    let d : ℤ := 2 - (F.G.homogeneousDimension : ℤ) - ((∑ j, F.G.weight j * α j : ℕ) : ℤ)
    have hh : ∀ r : ℝ, 0 < r → ∀ u : Fin N → ℝ, u ≠ 0 →
        euclideanPartial α (F.pole t.star) (F.G.dilate r u) =
          r ^ d * euclideanPartial α (F.pole t.star) u := by
      intro r hr u hu
      have h := H1.euclideanPartial_punctured_homogeneity_finite F.G α
        (hΓ.of_le (by simp)) hhom hr hu
      have he : (d : ℝ) = (2 : ℝ) - F.G.homogeneousDimension -
          ((∑ j, F.G.weight j * α j : ℕ) : ℝ) := by
        dsimp only [d]
        simp only [Int.cast_sub, Int.cast_natCast, Int.cast_ofNat]
      rw [← he, Real.rpow_intCast] at h
      exact h
    have hreg := contDiff_weightedTaylor_remainder_term F.G W budget hW
      (euclideanPartial α (F.pole t.star)) d (hpartial α) hh J hJ (hd α hα)
      (fun q => A q * t.coefficientLeft α q) (hA.mul (t.coefficientLeft_contDiff α hα))
    have hs := hreg.comp ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd)
    convert hs using 1
    funext q
    dsimp only [PrincipalTerm.coefficientLeft, Function.comp_def]
    ring
  have he : (fun q : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ) =>
      A ((q.1, q.2.1), q.2.2) * taylorWordMonomial J q.2.2 * t.modelKernel q.1 q.2.1 q.2.2) =
      (fun q => ∑ α ∈ t.indices, A ((q.1, q.2.1), q.2.2) * taylorWordMonomial J q.2.2 *
        ((t.D q.1 q.2.1).coefficient α q.2.2 * euclideanPartial α (F.pole t.star) q.2.2)) := by
    funext q
    simp only [PrincipalTerm.modelKernel, SmoothDifferentialOperator.apply, t.indices_eq, Finset.mul_sum]
  rw [he]
  exact ContDiff.sum hterm

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The high-monomial Taylor contribution
becomes a compact C^m regular kernel after the actual chart and endpoint cutoffs. -/
theorem LiftedChart.isRegularKernel_highMonomial_principal
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (t : PrincipalTerm F) (W budget : ℕ) (hW : ∀ j, F.G.weight j ≤ W)
    (J : List (Fin (n + m))) (hJ : J ≠ [])
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole t.star (F.G.dilate r u) = r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole t.star u)
    (hd : ∀ α ∈ t.indices, (((budget + 1) * W : ℕ) : ℤ) <
      ((J.map F.G.weight).sum : ℤ) +
        (2 - (F.G.homogeneousDimension : ℤ) - ((∑ j, F.G.weight j * α j : ℕ) : ℤ)))
    (A : (((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) × (Fin (n + m) → ℝ)) → ℝ)
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) :
    IsRegularKernel F budget (fun ξ η => t.a ξ * t.b η *
      (A ((ξ, η), F.Θ η ξ) * taylorWordMonomial J (F.Θ η ξ) * t.modelKernel ξ η (F.Θ η ξ))) :=
  C.isRegularKernel_cutoff_model F hΘ hVU budget t.a t.b _
    (t.contDiff_highMonomial_model W budget hW J hJ hΓ hhom hd A hA)

end RothschildStein.P1
