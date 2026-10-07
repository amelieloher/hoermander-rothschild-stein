-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SingularSplitEstimatesFamily
public import RothschildStein.G1.CompactParameterIntegral

/-!
# Parameter mean-value estimate: Hadamard factorization of `D^{ξ,η} - D^{ξ,ξ}`

For the parameter part `E = [k^{ξ,η} - k^{ξ,ξ}](Θ(η, ξ))` of `K₁` (BB pp. 575–576, (11.59)) the
argument uses the parameter mean value: the difference of the coefficients of the family at the
two parameter values is `∑_l (η_l - ξ_l) ĉ_{a,l}(ξ, η, u)` with *jointly smooth* Hadamard
coefficients `ĉ_{a,l}(ξ, η, u) = ∫₀¹ ∂_{η_l} c_a(ξ, ξ + θ(η - ξ), u) dθ` (differentiation under the
integral over the compact segment, `G1.compactParameterIntegral_contDiff`). Hence
`(D^{ξ,η} Γ - D^{ξ,ξ} Γ)(u) = ∑_l (η_l - ξ_l) V_l(ξ, η, u)` with the kernel families
`V_l = ∑_a ĉ_{a,l} ∂^a Γ`, which are

* jointly smooth off `u = 0` (the Hadamard coefficients are smooth and `∂^a Γ` is smooth off `0`);
* homogeneous of degree `-Q` in `u`: `V_l(ξ, η, ·)` is the average over the segment of the
  parameter derivatives `∂_{η_l}(D^{ξ,η} Γ)`, which are homogeneous of degree `-Q` because every
  `D^{ξ,η} Γ` is.

So the kernel estimates apply to each `V_l` with `ℓ = 0`, and the factor `(η - ξ)_l` (which vanishes on the
diagonal) raises the exponent to `ℓ = 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1
namespace SplitFamily

variable {N : ℕ} {G : HomogeneousGroup N}
  (D : (Fin N → ℝ) → (Fin N → ℝ) → SmoothDifferentialOperator N)

/-- The coefficient `c_a(ξ, η, u)` of `D^{ξ,η}` as a function of the triple. -/
def coefTriple (a : Fin N → ℕ) (z : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)) : ℝ :=
  (D z.1 z.2.1).coefficient a z.2.2

/-- The Hadamard coefficient
`ĉ_{a,l}(ξ, η, u) = ∫₀¹ ∂_{η_l} c_a(ξ, ξ + θ(η - ξ), u) dθ` (BB pp. 575–576, parameter mean
value). -/
def hadamardCoef (a : Fin N → ℕ) (l : Fin N)
    (z : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)) : ℝ :=
  ∫ θ in Icc (0 : ℝ) 1, fderiv ℝ (coefTriple D a)
    (z.1, z.1 + θ • (z.2.1 - z.1), z.2.2) (0, Pi.single l 1, 0)

/-- The Hadamard coefficients of smooth coefficients are jointly smooth, also across
`η = ξ` (differentiation under the integral over the compact segment). -/
theorem contDiff_hadamardCoef (a : Fin N → ℕ) (hD : ContDiff ℝ (⊤ : ℕ∞) (coefTriple D a))
    (l : Fin N) : ContDiff ℝ (⊤ : ℕ∞) (hadamardCoef D a l) := by
  have hD' : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (coefTriple D a)) :=
    (contDiff_infty_iff_fderiv.mp hD).2
  have harg : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ((Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)) × ℝ =>
        (p.1.1, p.1.1 + p.2 • (p.1.2.1 - p.1.1), p.1.2.2)) :=
    contDiff_fst.fst.prodMk ((contDiff_fst.fst).add
      (contDiff_snd.smul (contDiff_fst.snd.fst.sub contDiff_fst.fst)) |>.prodMk
        contDiff_fst.snd.snd)
  exact RothschildStein.G1.compactParameterIntegral_contDiff
    (fun p : ((Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)) × ℝ =>
      fderiv ℝ (coefTriple D a) (p.1.1, p.1.1 + p.2 • (p.1.2.1 - p.1.1), p.1.2.2)
        (0, Pi.single l 1, 0))
    ((hD'.comp harg).clm_apply contDiff_const)

/-- A parameter-direction vector is the sum of its coordinates times the coordinate
directions of the second slot. -/
theorem vec_decomp (v : Fin N → ℝ) :
    (((0 : Fin N → ℝ), v, (0 : Fin N → ℝ)) :
        (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)) =
      ∑ l, v l • (((0 : Fin N → ℝ), (Pi.single l (1 : ℝ) : Fin N → ℝ), (0 : Fin N → ℝ)) :
        (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)) := by
  ext i
  · simp [Prod.fst_sum]
  · simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  · simp [Prod.snd_sum, Finset.sum_apply]

/-- Hadamard factorization of the coefficient difference
`c_a(ξ, η, u) - c_a(ξ, ξ, u) = ∑_l (η_l - ξ_l) ĉ_{a,l}(ξ, η, u)` (fundamental theorem of calculus
along the parameter segment). -/
theorem coef_sub_eq_sum (a : Fin N → ℕ) (hD : ContDiff ℝ (⊤ : ℕ∞) (coefTriple D a))
    (ξ η u : Fin N → ℝ) :
    (D ξ η).coefficient a u - (D ξ ξ).coefficient a u =
      ∑ l, (η l - ξ l) * hadamardCoef D a l (ξ, η, u) := by
  have hdiff : Differentiable ℝ (coefTriple D a) := hD.differentiable (by simp)
  have hpath : ∀ θ : ℝ, HasDerivAt
      (fun θ : ℝ => ((ξ, ξ + θ • (η - ξ), u) : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)))
      ((0, η - ξ, 0) : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)) θ := by
    intro θ
    have ht : HasDerivAt (fun t : ℝ => ξ + t • (η - ξ)) (η - ξ) θ := by
      simpa only [id_eq, one_smul] using! ((hasDerivAt_id θ).smul_const (η - ξ)).const_add ξ
    exact (hasDerivAt_const θ ξ).prodMk (ht.prodMk (hasDerivAt_const θ u))
  have hderiv : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => coefTriple D a (ξ, ξ + θ • (η - ξ), u))
      (fderiv ℝ (coefTriple D a) (ξ, ξ + θ • (η - ξ), u) (0, η - ξ, 0)) θ :=
    fun θ => (hdiff.differentiableAt.hasFDerivAt).comp_hasDerivAt θ (hpath θ)
  have hcpath : Continuous (fun θ : ℝ =>
      ((ξ, ξ + θ • (η - ξ), u) : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ))) :=
    continuous_const.prodMk ((continuous_const.add (continuous_id.smul continuous_const)).prodMk
      continuous_const)
  have hcont : ∀ v : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ), Continuous (fun θ : ℝ =>
      fderiv ℝ (coefTriple D a) (ξ, ξ + θ • (η - ξ), u) v) := fun v =>
    ((hD.continuous_fderiv (by simp)).comp hcpath).clm_apply continuous_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hderiv θ)
    ((hcont (0, η - ξ, 0)).intervalIntegrable 0 1)
  have hdec : ∀ θ : ℝ, fderiv ℝ (coefTriple D a) (ξ, ξ + θ • (η - ξ), u) (0, η - ξ, 0) =
      ∑ l, (η l - ξ l) * fderiv ℝ (coefTriple D a) (ξ, ξ + θ • (η - ξ), u)
        (0, Pi.single l 1, 0) := by
    intro θ
    rw [vec_decomp (η - ξ), map_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [map_smul, smul_eq_mul, Pi.sub_apply]
  have hsum : (∫ θ in (0 : ℝ)..1, fderiv ℝ (coefTriple D a) (ξ, ξ + θ • (η - ξ), u)
      (0, η - ξ, 0)) = ∑ l, (η l - ξ l) * hadamardCoef D a l (ξ, η, u) := by
    simp_rw [hdec]
    rw [intervalIntegral.integral_finsetSum (fun l _ =>
      ((hcont (0, Pi.single l 1, 0)).const_mul (η l - ξ l)).intervalIntegrable 0 1)]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [intervalIntegral.integral_const_mul]
    congr 1
    simp only [hadamardCoef, intervalIntegral.integral_of_le zero_le_one,
      integral_Icc_eq_integral_Ioc]
  rw [← hsum, hFTC]
  simp [coefTriple]

variable {D}
variable (F : SplitFamily G D) (Γ : (Fin N → ℝ) → ℝ)

/-- The kernel family of the parameter mean value,
`V_l(ξ, η, u) = ∑_a ĉ_{a,l}(ξ, η, u) ∂^a Γ(u)`. -/
def hadamardKernel (l : Fin N) (ξ η u : Fin N → ℝ) : ℝ :=
  ∑ a ∈ F.indices, hadamardCoef D a l (ξ, η, u) * euclideanPartial a Γ u

/-- **Parameter mean value for the operator family**:
`(D^{ξ,η} Γ)(u) - (D^{ξ,ξ} Γ)(u) = ∑_l (η_l - ξ_l) V_l(ξ, η, u)` (BB pp. 575–576). -/
theorem apply_sub_eq_sum (ξ η u : Fin N → ℝ) :
    (D ξ η).apply Γ u - (D ξ ξ).apply Γ u =
      ∑ l, (η l - ξ l) * F.hadamardKernel Γ l ξ η u := by
  rw [F.apply_eq_sum Γ ξ η u, F.apply_eq_sum Γ ξ ξ u, ← Finset.sum_sub_distrib]
  have h1 : ∀ a ∈ F.indices, (D ξ η).coefficient a u * euclideanPartial a Γ u -
      (D ξ ξ).coefficient a u * euclideanPartial a Γ u =
      ∑ l, (η l - ξ l) * (hadamardCoef D a l (ξ, η, u) * euclideanPartial a Γ u) := by
    intro a ha
    rw [← sub_mul, coef_sub_eq_sum D a (F.coefficient_smooth a ha) ξ η u, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [hadamardKernel, Finset.mul_sum]

variable {Γ}

include F in
/-- The kernel families `V_l` of the parameter mean value are jointly smooth off `u = 0`
(`ĉ_{a,l}` is jointly smooth and `∂^a Γ` is smooth off `0`). -/
theorem contDiffOn_kernelUncurry_hadamard (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin N → ℝ)}ᶜ)
    (l : Fin N) :
    ContDiffOn ℝ (⊤ : ℕ∞) (kernelUncurry (fun ξ η u => F.hadamardKernel Γ l ξ η u))
      {z | z.2.2 ≠ 0} := by
  have hfun : kernelUncurry (fun ξ η u => F.hadamardKernel Γ l ξ η u) = fun z =>
      ∑ a ∈ F.indices, hadamardCoef D a l z * euclideanPartial a Γ z.2.2 := rfl
  rw [hfun]
  refine ContDiffOn.sum (fun a ha => ?_)
  exact (contDiff_hadamardCoef D a (F.coefficient_smooth a ha) l).contDiffOn.mul
    ((contDiffOn_euclideanPartial hΓ a).comp contDiff_snd.snd.contDiffOn (fun z hz => hz))

variable (Γ)

/-- The parameter derivative kernel
`∂_{y_l}(D^{ξ,y} Γ)(u) = ∑_a ∂_{y_l} c_a(ξ, y, u) ∂^a Γ(u)`. -/
def dirKernel (l : Fin N) (ξ y u : Fin N → ℝ) : ℝ :=
  ∑ a ∈ F.indices, fderiv ℝ (coefTriple D a) (ξ, y, u) (0, Pi.single l 1, 0) *
    euclideanPartial a Γ u

/-- `dirKernel` is the derivative of `(D^{ξ,y} Γ)(u)` along the coordinate direction
`l` of the second parameter. -/
theorem hasDerivAt_apply_param (l : Fin N) (ξ y u : Fin N → ℝ) :
    HasDerivAt (fun s : ℝ => (D ξ (y + s • Pi.single l 1)).apply Γ u)
      (F.dirKernel Γ l ξ y u) 0 := by
  have hfun : (fun s : ℝ => (D ξ (y + s • Pi.single l 1)).apply Γ u) = fun s : ℝ =>
      ∑ a ∈ F.indices, coefTriple D a (ξ, y + s • Pi.single l 1, u) *
        euclideanPartial a Γ u :=
    funext fun s => F.apply_eq_sum Γ ξ _ u
  rw [hfun]
  refine HasDerivAt.fun_sum (fun a ha => ?_)
  have hc : Differentiable ℝ (coefTriple D a) := (F.coefficient_smooth a ha).differentiable
    (by simp)
  have ht : HasDerivAt (fun t : ℝ => y + t • (Pi.single l (1 : ℝ) : Fin N → ℝ))
      (Pi.single l (1 : ℝ) : Fin N → ℝ) 0 := by
    simpa only [id_eq, one_smul] using! ((hasDerivAt_id (0 : ℝ)).smul_const
      (Pi.single l (1 : ℝ) : Fin N → ℝ)).const_add y
  have hpath : HasDerivAt
      (fun s : ℝ => ((ξ, y + s • Pi.single l 1, u) :
        (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)))
      ((0, Pi.single l 1, 0) : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)) 0 :=
    (hasDerivAt_const (0 : ℝ) ξ).prodMk (ht.prodMk (hasDerivAt_const (0 : ℝ) u))
  have h1 := ((hc.differentiableAt.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hpath).mul_const
    (euclideanPartial a Γ u)
  refine h1.congr_deriv ?_
  simp

include F in
/-- The parameter derivative kernels are homogeneous of degree `-Q` in `u` (they are
derivatives in the parameter of the homogeneous kernels `(D^{ξ,y} Γ)`). -/
theorem dirKernel_dilate (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin N → ℝ)}ᶜ)
    (hΓh : ∀ t : ℝ, 0 < t → ∀ x : Fin N → ℝ, x ≠ 0 →
      Γ (G.dilate t x) = t ^ (2 - (G.homogeneousDimension : ℝ)) * Γ x)
    (l : Fin N) (ξ y : Fin N → ℝ) {t : ℝ} (ht : 0 < t) {u : Fin N → ℝ} (hu : u ≠ 0) :
    F.dirKernel Γ l ξ y (G.dilate t u) =
      t ^ (((0 : ℕ) : ℤ) - (G.homogeneousDimension : ℤ)) * F.dirKernel Γ l ξ y u := by
  have h1 := F.hasDerivAt_apply_param Γ l ξ y (G.dilate t u)
  have h2 := (F.hasDerivAt_apply_param Γ l ξ y u).const_mul
    (t ^ (((0 : ℕ) : ℤ) - (G.homogeneousDimension : ℤ)))
  have hfun : (fun s : ℝ => (D ξ (y + s • Pi.single l 1)).apply Γ (G.dilate t u)) =
      fun s : ℝ => t ^ (((0 : ℕ) : ℤ) - (G.homogeneousDimension : ℤ)) *
        (D ξ (y + s • Pi.single l 1)).apply Γ u :=
    funext fun s => F.apply_dilate hΓ hΓh ξ _ ht hu
  rw [hfun] at h1
  exact h1.unique h2

include F in
/-- Integral representation: `V_l(ξ, η, u)` is the average over the parameter segment of
the parameter derivatives `∂_{y_l}(D^{ξ,y} Γ)(u)`. -/
theorem hadamardKernel_eq_integral (l : Fin N) (ξ η u : Fin N → ℝ) :
    F.hadamardKernel Γ l ξ η u =
      ∫ θ in Icc (0 : ℝ) 1, F.dirKernel Γ l ξ (ξ + θ • (η - ξ)) u := by
  have hcpath : Continuous (fun θ : ℝ =>
      ((ξ, ξ + θ • (η - ξ), u) : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ))) :=
    continuous_const.prodMk ((continuous_const.add (continuous_id.smul continuous_const)).prodMk
      continuous_const)
  have hint : ∀ a ∈ F.indices, IntegrableOn (fun θ : ℝ =>
      fderiv ℝ (coefTriple D a) (ξ, ξ + θ • (η - ξ), u) (0, Pi.single l 1, 0) *
        euclideanPartial a Γ u) (Icc (0 : ℝ) 1) volume := by
    intro a ha
    exact ((((F.coefficient_smooth a ha).continuous_fderiv (by simp)).comp hcpath).clm_apply
      continuous_const).mul continuous_const |>.integrableOn_Icc
  simp only [hadamardKernel, hadamardCoef, dirKernel]
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [integral_mul_const]

include F in
/-- **Homogeneity of the parameter mean value kernels**: `V_l(ξ, η, δ_t u) =
t^(-Q) V_l(ξ, η, u)` off `u = 0` (`ℓ = 0` in the kernel estimates). -/
theorem hadamardKernel_dilate (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin N → ℝ)}ᶜ)
    (hΓh : ∀ t : ℝ, 0 < t → ∀ x : Fin N → ℝ, x ≠ 0 →
      Γ (G.dilate t x) = t ^ (2 - (G.homogeneousDimension : ℝ)) * Γ x)
    (l : Fin N) (ξ η : Fin N → ℝ) {t : ℝ} (ht : 0 < t) {u : Fin N → ℝ} (hu : u ≠ 0) :
    F.hadamardKernel Γ l ξ η (G.dilate t u) =
      t ^ (((0 : ℕ) : ℤ) - (G.homogeneousDimension : ℤ)) * F.hadamardKernel Γ l ξ η u := by
  rw [F.hadamardKernel_eq_integral, F.hadamardKernel_eq_integral, ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Icc
    (fun θ _ => F.dirKernel_dilate Γ hΓ hΓh l ξ _ ht hu)

end SplitFamily

end RothschildStein.P1
