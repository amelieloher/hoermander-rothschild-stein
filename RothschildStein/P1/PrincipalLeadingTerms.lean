-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.CoefficientPartialOperator
public import RothschildStein.P1.SmoothFieldHomogeneity
public import RothschildStein.P1.WeightedTaylorParameters

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace RothschildStein.P1

variable {N : ℕ} {F : KernelFrame N}

/-- The coefficient family with the endpoint pair grouped as a parameter. -/
def PrincipalTerm.coefficientLeft (t : PrincipalTerm F) (α : Fin N → ℕ)
    (q : ((Fin N → ℝ) × (Fin N → ℝ)) × (Fin N → ℝ)) : ℝ :=
  (t.D q.1.1 q.1.2).coefficient α q.2

/-- Joint smoothness survives regrouping the endpoint parameters. -/
theorem PrincipalTerm.coefficientLeft_contDiff (t : PrincipalTerm F) (α : Fin N → ℕ)
    (hα : α ∈ t.indices) : ContDiff ℝ (⊤ : ℕ∞) (PrincipalTerm.coefficientLeft t α) :=
  (t.coefficient_smooth α hα).comp
    (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))

/-- The scalar coefficient of a coordinate contribution to Y(DΓ). -/
def PrincipalTerm.gradientFamily (t : PrincipalTerm F) (α : Fin N → ℕ) (j : Fin N)
    (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (q : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)) : ℝ :=
  Y q.2.2 j * fderiv ℝ (PrincipalTerm.coefficientLeft t α) ((q.1, q.2.1), q.2.2) (0, Pi.single j 1)

/-- Joint smoothness of the differentiated coefficient family. -/
theorem PrincipalTerm.gradientFamily_contDiff (t : PrincipalTerm F) (α : Fin N → ℕ)
    (hα : α ∈ t.indices) (j : Fin N) (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ContDiff ℝ (⊤ : ℕ∞) Y) : ContDiff ℝ (⊤ : ℕ∞) (PrincipalTerm.gradientFamily t α j Y) := by
  have hD := ((contDiff_infty_iff_fderiv.mp (PrincipalTerm.coefficientLeft_contDiff t α hα)).2).clm_apply
    (contDiff_const (c := ((0 : (Fin N → ℝ) × (Fin N → ℝ)), Pi.single j 1)))
  exact (((contDiff_apply ℝ ℝ j).comp hY).comp contDiff_snd.snd).mul
    (hD.comp ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd))

/-- The parameter derivative agrees with differentiation in the model variable. -/
theorem PrincipalTerm.gradientFamily_eval (t : PrincipalTerm F) (α : Fin N → ℕ)
    (hα : α ∈ t.indices) (j : Fin N) (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (ξ η u : Fin N → ℝ) :
    PrincipalTerm.gradientFamily t α j Y (ξ, η, u) =
      Y u j * fderiv ℝ ((t.D ξ η).coefficient α) u (Pi.single j 1) := by
  have h := rsPartial_single_generic_parameter (PrincipalTerm.coefficientLeft t α)
    (PrincipalTerm.coefficientLeft_contDiff t α hα) (ξ, η) u j
  change fderiv ℝ ((t.D ξ η).coefficient α) u (Pi.single j 1) =
    fderiv ℝ (PrincipalTerm.coefficientLeft t α) ((ξ, η), u) (0, Pi.single j 1) at h
  change Y u j * _ = _
  rw [← h]

/-- Actual operator homogeneity gives the exact coefficient weight. -/
theorem PrincipalTerm.coefficient_homogeneous (t : PrincipalTerm F) (α : Fin N → ℕ)
    (hα : α ∈ t.indices) (ξ η : Fin N → ℝ) :
    ∀ r : ℝ, 0 < r → ∀ u,
      (t.D ξ η).coefficient α (F.G.dilate r u) =
        r ^ ((∑ i, F.G.weight i * α i : ℕ) - (t.degree : ℝ)) * (t.D ξ η).coefficient α u := by
  exact (G2.operator_homogeneous_iff_coefficients F.G (t.D ξ η) t.degree).mp
    (t.homogeneous ξ η) α (by rw [t.indices_eq]; exact hα)

/-- The differentiated-coefficient part of
Y(DΓ) is an actual principal term of degree degree(D)+degree(Y), with
its original cutoffs and pole (BB Lemma 11.18, p. 549). -/
def PrincipalTerm.leadingCoefficientDerivative (t : PrincipalTerm F) (α : Fin N → ℕ)
    (hα : α ∈ t.indices) (j : Fin N) (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ContDiff ℝ (⊤ : ℕ∞) Y) (w : ℤ) (hhY : G2.IsHomogeneousField F.G Y w) :
    PrincipalTerm F :=
  PrincipalTerm.ofCoefficientPartial F t.a t.b α (PrincipalTerm.gradientFamily t α j Y)
    (PrincipalTerm.gradientFamily_contDiff t α hα j Y hY) (t.degree + w) (by
      intro ξ η r hr u
      rw [PrincipalTerm.gradientFamily_eval t α hα j Y, PrincipalTerm.gradientFamily_eval t α hα j Y]
      have hc := (t.D ξ η).smooth_coefficient α (by rw [t.indices_eq]; exact hα)
      have hd := coordinatePartial_global_homogeneous F.G j hc
        (PrincipalTerm.coefficient_homogeneous t α hα ξ η) hr u
      have hy := (G2.isHomogeneousField_iff_coefficients F.G Y w).mp hhY j r hr u
      rw [hd, hy]
      rw [mul_mul_mul_comm, ← Real.rpow_add hr]
      congr 1
      congr 1
      simp only [Int.cast_add]
      ring) t.star

/-- The constructed gradient term has the
actual scalar coefficient Y(j)∂j(coefficient(D,α)) times ∂αΓ. -/
theorem PrincipalTerm.leadingCoefficientDerivative_kernel (t : PrincipalTerm F)
    (α : Fin N → ℕ) (hα : α ∈ t.indices) (j : Fin N)
    (Y : (Fin N → ℝ) → (Fin N → ℝ)) (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    (w : ℤ) (hhY : G2.IsHomogeneousField F.G Y w) (ξ η : Fin N → ℝ) :
    (t.leadingCoefficientDerivative α hα j Y hY w hhY).kernel ξ η =
      t.a ξ * t.b η *
        ((Y (F.Θ η ξ) j * fderiv ℝ ((t.D ξ η).coefficient α) (F.Θ η ξ) (Pi.single j 1)) *
          euclideanPartial α (F.pole t.star) (F.Θ η ξ)) := by
  rw [PrincipalTerm.leadingCoefficientDerivative, PrincipalTerm.ofCoefficientPartial_kernel,
    PrincipalTerm.gradientFamily_eval t α hα j Y]

/-- Increasing one coordinate of a multi-index adds its homogeneous coordinate weight. -/
theorem weightedIndex_successor (G : HomogeneousGroup N) (α : Fin N → ℕ) (j : Fin N) :
    (∑ i, G.weight i * ((α + Pi.single j 1 : Fin N → ℕ) i)) = (∑ i, G.weight i * α i) + G.weight j := by
  simp [Pi.add_apply, mul_add, Finset.sum_add_distrib, Pi.single_apply]

/-- The differentiated-pole part of Y(DΓ)
is an actual principal term with the successor multi-index and exact
degree degree(D)+degree(Y) (BB Lemma 11.18, p. 549). -/
def PrincipalTerm.leadingPoleDerivative (t : PrincipalTerm F) (α : Fin N → ℕ)
    (hα : α ∈ t.indices) (j : Fin N) (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ContDiff ℝ (⊤ : ℕ∞) Y) (w : ℤ) (hhY : G2.IsHomogeneousField F.G Y w) :
    PrincipalTerm F :=
  PrincipalTerm.ofCoefficientPartial F t.a t.b (α + Pi.single j 1)
    (fun q => Y q.2.2 j * (t.D q.1 q.2.1).coefficient α q.2.2)
    ((((contDiff_apply ℝ ℝ j).comp hY).comp contDiff_snd.snd).mul
      (t.coefficient_smooth α hα)) (t.degree + w) (by
      intro ξ η r hr u
      have hy := (G2.isHomogeneousField_iff_coefficients F.G Y w).mp hhY j r hr u
      have hc := PrincipalTerm.coefficient_homogeneous t α hα ξ η r hr u
      change Y (F.G.dilate r u) j * (t.D ξ η).coefficient α (F.G.dilate r u) = _
      rw [hy, hc, mul_mul_mul_comm, ← Real.rpow_add hr]
      congr 1
      congr 1
      rw [weightedIndex_successor]
      simp only [Nat.cast_add, Int.cast_add]
      ring) t.star

/-- The constructed pole-derivative term
has precisely Y(j)coefficient(D,α)∂^(α+ej)Γ as its model kernel. -/
theorem PrincipalTerm.leadingPoleDerivative_kernel (t : PrincipalTerm F)
    (α : Fin N → ℕ) (hα : α ∈ t.indices) (j : Fin N)
    (Y : (Fin N → ℝ) → (Fin N → ℝ)) (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    (w : ℤ) (hhY : G2.IsHomogeneousField F.G Y w) (ξ η : Fin N → ℝ) :
    (t.leadingPoleDerivative α hα j Y hY w hhY).kernel ξ η =
      t.a ξ * t.b η *
        ((Y (F.Θ η ξ) j * (t.D ξ η).coefficient α (F.Θ η ξ)) *
          euclideanPartial (α + Pi.single j 1) (F.pole t.star) (F.Θ η ξ)) := by
  rw [PrincipalTerm.leadingPoleDerivative, PrincipalTerm.ofCoefficientPartial_kernel]

end RothschildStein.P1
