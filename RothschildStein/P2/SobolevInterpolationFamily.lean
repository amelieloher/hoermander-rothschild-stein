-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ParametrixKernelBoundsHomogeneous
public import RothschildStein.P1.ContinuityPositive

/-!
# Sobolev interpolation, kernel derivative bounds: principal terms are weighted symbols

The derivative bounds of `RothschildStein.P1.ParametrixKernelBoundsDeriv` apply to a kernel family
`A(ξ, η, Θ(η, ξ))` with `A` in the weighted symbol class `WtSym`. The kernel of a principal term
`a(ξ) b(η) (D^{ξ,η} Γ)(Θ(η, ξ))` of a type-`λ` decomposition has `A = a(ξ) b(η) E(ξ, η, u)`, where
`E(ξ, η, u) = (D^{ξ,η} Γ)(u)` is jointly smooth off `u = 0` and, for every `(ξ, η)`, homogeneous in `u`
of the integer degree `2 - deg D - Q`. This file shows that such a family is a symbol of that degree
to every depth (`wtSym_homogeneousFamily`: the parameter derivatives of a homogeneous family are
homogeneous of the same degree, the `u_j`-derivative of degree lowered by `w_j`), and applies it to
the principal terms (`principalTerm_wtSym`). (BB pp. 543, 569-571, 581-583.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

section Homogeneous

variable {N : ℕ} {G : HomogeneousGroup N}
  {Ψ : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) → ℝ} {d : ℤ}

/-- The derivative of a homogeneous family in the second parameter is homogeneous of the same
degree (the analogue of `fderiv_param_homogeneous` for the variable `η`). -/
theorem fderiv_eta_homogeneous
    (hΨ : ContDiffOn ℝ 1 (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (hhom : ∀ ξ η : Fin N → ℝ, ∀ t : ℝ, 0 < t → ∀ u : Fin N → ℝ, u ≠ 0 →
      Ψ ξ η (G.dilate t u) = t ^ d * Ψ ξ η u)
    (ξ η : Fin N → ℝ) {u : Fin N → ℝ} (hu : u ≠ 0) {t : ℝ} (ht : 0 < t) (b : Fin N → ℝ) :
    fderiv ℝ (kernelUncurry Ψ) (ξ, η, G.dilate t u) (0, b, 0) =
      t ^ d * fderiv ℝ (kernelUncurry Ψ) (ξ, η, u) (0, b, 0) := by
  have hA : ∀ y : Fin N → ℝ, HasFDerivAt (fun x : Fin N → ℝ => (ξ, x, y))
      ((0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)).prod ((ContinuousLinearMap.id ℝ (Fin N → ℝ)).prod
        (0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)))) η := fun y =>
    (hasFDerivAt_const ξ η).prodMk ((hasFDerivAt_id η).prodMk (hasFDerivAt_const y η))
  have hu' : G.dilate t u ≠ 0 := kdilate_ne_zero G ht hu
  have h1 := (kernelUncurry_differentiableAt hΨ hu').hasFDerivAt.comp η (hA (G.dilate t u))
  have h2 := ((kernelUncurry_differentiableAt hΨ hu).hasFDerivAt.comp η (hA u)).const_mul (t ^ d)
  have hfun : (fun x : Fin N → ℝ => kernelUncurry Ψ (ξ, x, G.dilate t u)) =
      fun x => t ^ d * (kernelUncurry Ψ ∘ fun x : Fin N → ℝ => (ξ, x, u)) x := by
    funext x
    exact hhom ξ x t ht u hu
  have h1' : HasFDerivAt (fun x : Fin N → ℝ => kernelUncurry Ψ (ξ, x, G.dilate t u))
      ((fderiv ℝ (kernelUncurry Ψ) (ξ, η, G.dilate t u)).comp
        ((0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)).prod ((ContinuousLinearMap.id ℝ (Fin N → ℝ)).prod
          (0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))))) η := h1
  rw [hfun] at h1'
  have := congrArg (fun L => L b) (h1'.unique h2)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply,
    smul_apply, smul_eq_mul] using this

/-- The `u_j`-derivative of a homogeneous family of degree `d` is homogeneous of degree
`d - w_j`. -/
theorem fderiv_u_single_homogeneous
    (hΨ : ContDiffOn ℝ 1 (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (hhom : ∀ ξ η : Fin N → ℝ, ∀ t : ℝ, 0 < t → ∀ u : Fin N → ℝ, u ≠ 0 →
      Ψ ξ η (G.dilate t u) = t ^ d * Ψ ξ η u)
    (ξ η : Fin N → ℝ) {u : Fin N → ℝ} (hu : u ≠ 0) {t : ℝ} (ht : 0 < t) (j : Fin N) :
    fderiv ℝ (kernelUncurry Ψ) (ξ, η, G.dilate t u) (0, 0, Pi.single j 1) =
      t ^ (d - (G.weight j : ℤ)) * fderiv ℝ (kernelUncurry Ψ) (ξ, η, u) (0, 0, Pi.single j 1) := by
  have h := fderiv_u_homogeneous hΨ hhom ξ η hu ht (Pi.single j (1 : ℝ))
  rw [kdilate_single] at h
  have hsm : ((0 : Fin N → ℝ), (0 : Fin N → ℝ), t ^ G.weight j • (Pi.single j (1 : ℝ) : Fin N → ℝ)) =
      t ^ G.weight j • ((0 : Fin N → ℝ), (0 : Fin N → ℝ), (Pi.single j (1 : ℝ) : Fin N → ℝ)) := by
    simp
  rw [hsm, map_smul, smul_eq_mul] at h
  have hw : 0 < t ^ G.weight j := pow_pos ht _
  rw [zpow_sub₀ ht.ne', zpow_natCast]
  field_simp
  linarith

/-- **Homogeneous families are symbols.** A family `Ψ(ξ, η, u)` that is jointly smooth off
`u = 0` and homogeneous of integer degree `d` in `u` for every `(ξ, η)` lies in `WtSym G (L × L) R k d`
for every compact `L`, radius `R` and depth `k` (scaling to the unit sphere; the parameter derivatives
keep the degree, the `u_j`-derivative lowers it by `w_j`). -/
theorem wtSym_homogeneousFamily (G : HomogeneousGroup N) {L : Set (Fin N → ℝ)} (hL : IsCompact L)
    (R : ℝ) :
    ∀ {k : ℕ} {d : ℤ} (Ψ : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) (kernelUncurry Ψ) {z | z.2.2 ≠ 0} →
      (∀ ξ η : Fin N → ℝ, ∀ t : ℝ, 0 < t → ∀ u : Fin N → ℝ, u ≠ 0 →
        Ψ ξ η (G.dilate t u) = t ^ d * Ψ ξ η u) →
      WtSym G (L ×ˢ L) R k d (kernelUncurry Ψ) := by
  have h0 : ∀ {d : ℤ} (Ψ : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) (kernelUncurry Ψ) {z | z.2.2 ≠ 0} →
      (∀ ξ η : Fin N → ℝ, ∀ t : ℝ, 0 < t → ∀ u : Fin N → ℝ, u ≠ 0 →
        Ψ ξ η (G.dilate t u) = t ^ d * Ψ ξ η u) →
      WtSym G (L ×ˢ L) R 0 d (kernelUncurry Ψ) := by
    intro d Ψ hΨ hhom
    refine WtSym.intro_zero hΨ ?_
    obtain ⟨M, hM0, hM⟩ := hasWeightedBounds_of_homogeneous (hΨ.of_le (by simp)) hhom L hL R
    exact ⟨M, hM0, fun z hz hz0 hρ => (hM z.1 hz.1 z.2.1 hz.2 z.2.2 hz0 hρ).1⟩
  intro k
  induction k with
  | zero => exact fun Ψ hΨ hhom => h0 Ψ hΨ hhom
  | succ k ih =>
    intro d Ψ hΨ hhom
    have hΨ1 : ContDiffOn ℝ 1 (kernelUncurry Ψ) {z | z.2.2 ≠ 0} := hΨ.of_le (by simp)
    refine WtSym.intro_succ (h0 Ψ hΨ hhom) (fun s => ?_)
    rcases s with l | l | j
    · have h1 := ih (fun ξ η u => fderiv ℝ (kernelUncurry Ψ) (ξ, η, u) (Pi.single l 1, 0, 0))
        (contDiffOn_fderiv_letter hΨ ((Pi.single l 1, 0, 0) : KZ N))
        (fun ξ η t ht u hu => fderiv_param_homogeneous hΨ1 hhom ξ η hu ht (Pi.single l 1))
      exact h1.degree_congr (by simp [symWt])
    · have h1 := ih (fun ξ η u => fderiv ℝ (kernelUncurry Ψ) (ξ, η, u) (0, Pi.single l 1, 0))
        (contDiffOn_fderiv_letter hΨ ((0, Pi.single l 1, 0) : KZ N))
        (fun ξ η t ht u hu => fderiv_eta_homogeneous hΨ1 hhom ξ η hu ht (Pi.single l 1))
      exact h1.degree_congr (by simp [symWt])
    · have h1 := ih (fun ξ η u => fderiv ℝ (kernelUncurry Ψ) (ξ, η, u) (0, 0, Pi.single j 1))
        (contDiffOn_fderiv_letter hΨ ((0, 0, Pi.single j 1) : KZ N))
        (fun ξ η t ht u hu => fderiv_u_single_homogeneous hΨ1 hhom ξ η hu ht j)
      exact h1

end Homogeneous

section Term

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- The family `(ξ, η, u) ↦ a(ξ) b(η) (D^{ξ,η} Γ)(u)` of a principal term `t` of a frame of a
lifted chart is a weighted symbol of degree `2 - deg D - Q` to every depth on every `L × L`. -/
theorem principalTerm_wtSym (hF : C.IsLiftedFrame F) (t : PrincipalTerm F)
    {L : Set (Fin (n + m) → ℝ)} (hL : IsCompact L) (R : ℝ) (kk : ℕ) :
    WtSym C.G (L ×ˢ L) R kk (2 - t.degree - (C.G.homogeneousDimension : ℤ))
      (fun z : KZ (n + m) =>
        t.a z.1 * t.b z.2.1 * (t.D z.1 z.2.1).apply (F.pole t.star) z.2.2) := by
  have hD : ∀ ξ η, (t.D ξ η).IsHomogeneous C.G t.degree := by
    intro ξ η
    have := t.homogeneous ξ η
    rwa [hF.G_eq] at this
  have hΓ := hF.pole_smooth t.star
  have hΓh := hF.pole_homogeneous t.star
  have hE := wtSym_homogeneousFamily C.G hL R (k := kk)
    (d := 2 - t.degree - (C.G.homogeneousDimension : ℤ))
    (fun ξ η u => (t.D ξ η).apply (F.pole t.star) u) (t.contDiffOn_family hΓ) (by
      intro ξ η s hs u hu
      have h := (H3.homogeneousOperator_kernel (t.D ξ η) (hD ξ η) hΓ hΓh).2 s hs u hu
      have e : (2 - (C.G.homogeneousDimension : ℝ)) - (t.degree : ℝ) =
          (((2 - t.degree - (C.G.homogeneousDimension : ℤ) : ℤ)) : ℝ) := by push_cast; ring
      rw [h, e, Real.rpow_intCast])
  have hab : WtSym C.G (L ×ˢ L) R kk 0
      (fun z : KZ (n + m) => (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
        t.a p.1 * t.b p.2) (z.1, z.2.1)) :=
    WtSym.param (G := C.G) (R := R) (hL.prod hL)
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => t.a p.1 * t.b p.2)
      ((t.a.contDiff.comp contDiff_fst).mul (t.b.contDiff.comp contDiff_snd))
  exact (WtSym.mul hab hE).degree_congr (zero_add _)

end Term

end RothschildStein.P2
