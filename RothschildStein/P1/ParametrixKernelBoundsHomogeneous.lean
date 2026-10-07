-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ParametrixKernelBoundsClass

/-!
# The elementary members of the weighted symbol classes

Two families of members of `WtSym` (`ParametrixKernelBoundsClass`):

* smooth functions `h(ξ, η)` of the parameters alone, of degree `0`, on compact parameter sets
  (`WtSym.param`): the cutoff factors `a(ξ)`, `b(η)/c(η)` and the coordinates of the extended
  lifted fields;
* functions `H(u)` of the group variable alone that are smooth off `u = 0` and homogeneous of
  integer degree `d` for the model dilations (`WtSym.homogeneous`), by scaling to the unit sphere
  (`hasWeightedBounds_of_homogeneous`) and the homogeneity of the coordinate derivatives
  (`partial_homogeneous`): the pole `Γ`, the model fields `Y_i`, and the coordinates `u_j`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RothschildStein.P1

variable {N : ℕ}

/-- The projection `(ξ, η, u) ↦ (ξ, η)` as a continuous linear map. -/
def projP (N : ℕ) : KZ N →L[ℝ] (Fin N → ℝ) × (Fin N → ℝ) :=
  ContinuousLinearMap.prod (ContinuousLinearMap.fst ℝ (Fin N → ℝ) ((Fin N → ℝ) × (Fin N → ℝ)))
    ((ContinuousLinearMap.fst ℝ (Fin N → ℝ) (Fin N → ℝ)).comp
      (ContinuousLinearMap.snd ℝ (Fin N → ℝ) ((Fin N → ℝ) × (Fin N → ℝ))))

/-- Chain rule for a function of `u` alone. -/
theorem fderiv_uslice {H : (Fin N → ℝ) → ℝ} {z : KZ N} (hH : DifferentiableAt ℝ H z.2.2)
    (v : KZ N) :
    fderiv ℝ (fun z : KZ N => H z.2.2) z v = fderiv ℝ H z.2.2 v.2.2 := by
  have hs : HasFDerivAt (fun z : KZ N => z.2.2)
      ((ContinuousLinearMap.snd ℝ (Fin N → ℝ) (Fin N → ℝ)).comp
        (ContinuousLinearMap.snd ℝ (Fin N → ℝ) ((Fin N → ℝ) × (Fin N → ℝ)))) z :=
    (hasFDerivAt_snd (p := z.2)).comp z hasFDerivAt_snd
  have h := (hH.hasFDerivAt.comp z hs).fderiv
  exact congrArg (fun L => L v) h

/-- Chain rule for a function of the parameters `(ξ, η)` alone. -/
theorem fderiv_param {h : (Fin N → ℝ) × (Fin N → ℝ) → ℝ} {z : KZ N}
    (hh : DifferentiableAt ℝ h (z.1, z.2.1)) (v : KZ N) :
    fderiv ℝ (fun z : KZ N => h (z.1, z.2.1)) z v = fderiv ℝ h (z.1, z.2.1) (v.1, v.2.1) := by
  have hp : HasFDerivAt (fun z : KZ N => ((z.1, z.2.1) : (Fin N → ℝ) × (Fin N → ℝ))) (projP N) z :=
    (projP N).hasFDerivAt
  have h' := (hh.hasFDerivAt.comp z hp).fderiv
  exact congrArg (fun L => L v) h'

/-- Chain rule for a function of `(η, u)` alone. -/
theorem fderiv_eta_u {F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ} {z : KZ N}
    (hF : DifferentiableAt ℝ F z.2) (v : KZ N) :
    fderiv ℝ (fun z : KZ N => F z.2) z v = fderiv ℝ F z.2 v.2 := by
  have hs : HasFDerivAt (fun z : KZ N => z.2)
      (ContinuousLinearMap.snd ℝ (Fin N → ℝ) ((Fin N → ℝ) × (Fin N → ℝ))) z :=
    hasFDerivAt_snd
  have h' := (hF.hasFDerivAt.comp z hs).fderiv
  exact congrArg (fun L => L v) h'

section Param

variable {G : HomogeneousGroup N} {K : Set ((Fin N → ℝ) × (Fin N → ℝ))} {R : ℝ}

/-- Smooth functions of the parameters are symbols of degree `0` on compact parameter
sets. -/
theorem WtSym.param (hK : IsCompact K) :
    ∀ {k : ℕ} (h : (Fin N → ℝ) × (Fin N → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) h →
      WtSym G K R k 0 (fun z => h (z.1, z.2.1)) := by
  have h0 : ∀ h : (Fin N → ℝ) × (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      WtSym G K R 0 0 (fun z => h (z.1, z.2.1)) := by
    intro h hh
    refine WtSym.intro_zero ?_ ?_
    · exact (hh.comp (contDiff_fst.prodMk contDiff_snd.fst)).contDiffOn
    · obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hh.continuous.continuousOn
      refine ⟨|M|, abs_nonneg _, fun z hzK _ _ => ?_⟩
      have := hM _ hzK
      rw [Real.norm_eq_abs] at this
      simpa using this.trans (le_abs_self _)
  intro k
  induction k with
  | zero => exact fun h hh => h0 h hh
  | succ k ih =>
    intro h hh
    have hdh : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ h) := (contDiff_infty_iff_fderiv.mp hh).2
    have hdiff : ∀ z : KZ N, DifferentiableAt ℝ h (z.1, z.2.1) := fun z =>
      (hh.differentiable (by simp)) _
    refine WtSym.intro_succ (h0 h hh) (fun s => ?_)
    rcases s with l | l | j
    · have h1 := ih (fun p => fderiv ℝ h p (Pi.single l 1, 0)) (hdh.clm_apply contDiff_const)
      refine (WtSym.congr (fun z _ => ?_) h1).degree_congr (by simp [symWt])
      rw [fderiv_param (hdiff z)]
      rfl
    · have h1 := ih (fun p => fderiv ℝ h p (0, Pi.single l 1)) (hdh.clm_apply contDiff_const)
      refine (WtSym.congr (fun z _ => ?_) h1).degree_congr (by simp [symWt])
      rw [fderiv_param (hdiff z)]
      rfl
    · refine WtSym.congr (fun z _ => ?_) (WtSym.zero_fun (k := k) (d := 0 - symWt G (Sum.inr (Sum.inr j))))
      rw [fderiv_param (hdiff z)]
      exact map_zero (fderiv ℝ h (z.1, z.2.1))

end Param

section Homogeneous

variable (G : HomogeneousGroup N)

/-- The coordinate derivative of a homogeneous function of degree `d` is homogeneous of
degree `d - w_j`. -/
theorem partial_homogeneous {H : (Fin N → ℝ) → ℝ} (hH : ContDiffOn ℝ (⊤ : ℕ∞) H {0}ᶜ) {d : ℤ}
    (hhom : ∀ t : ℝ, 0 < t → ∀ u : Fin N → ℝ, u ≠ 0 → H (G.dilate t u) = t ^ d * H u)
    (j : Fin N) {t : ℝ} (ht : 0 < t) {u : Fin N → ℝ} (hu : u ≠ 0) :
    fderiv ℝ H (G.dilate t u) (Pi.single j 1) =
      t ^ (d - (G.weight j : ℤ)) * fderiv ℝ H u (Pi.single j 1) := by
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : KZ N => H z.2.2) {z | z.2.2 ≠ 0} :=
    hH.comp (contDiff_snd.snd).contDiffOn (fun z hz => hz)
  have hΨ : ContDiffOn ℝ 1 (kernelUncurry (fun (_ _ u : Fin N → ℝ) => H u)) {z | z.2.2 ≠ 0} :=
    hsm.of_le (by simp)
  have hdiff : ∀ v : Fin N → ℝ, v ≠ 0 → DifferentiableAt ℝ H v := fun v hv =>
    (hH.contDiffAt (isOpen_compl_singleton.mem_nhds hv)).differentiableAt (by simp)
  have h := fderiv_u_homogeneous (G := G) hΨ (fun ξ η t ht u hu => hhom t ht u hu)
    (0 : Fin N → ℝ) (0 : Fin N → ℝ) hu ht (Pi.single j 1)
  have e1 : ∀ (v : Fin N → ℝ) (w : Fin N → ℝ), v ≠ 0 →
      fderiv ℝ (kernelUncurry (fun (_ _ u : Fin N → ℝ) => H u))
        ((0 : Fin N → ℝ), (0 : Fin N → ℝ), v) (0, 0, w) = fderiv ℝ H v w := fun v w hv =>
    fderiv_uslice (z := ((0 : Fin N → ℝ), (0 : Fin N → ℝ), v)) (hdiff v hv) _
  rw [e1 _ _ (kdilate_ne_zero G ht hu), e1 _ _ hu, kdilate_single, map_smul, smul_eq_mul] at h
  have hw : 0 < t ^ G.weight j := pow_pos ht _
  rw [zpow_sub₀ ht.ne', zpow_natCast]
  field_simp
  linarith

/-- **Homogeneous functions of `u` are symbols.** A function `H(u)`, smooth off `0` and
homogeneous of integer degree `d` for the model dilations, lies in `WtSym G K R k d` for every
parameter set, radius and depth (scaling to the unit sphere). -/
theorem WtSym.homogeneous (K : Set ((Fin N → ℝ) × (Fin N → ℝ))) (R : ℝ) :
    ∀ {k : ℕ} {d : ℤ} (H : (Fin N → ℝ) → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) H {0}ᶜ →
      (∀ t : ℝ, 0 < t → ∀ u : Fin N → ℝ, u ≠ 0 → H (G.dilate t u) = t ^ d * H u) →
      WtSym G K R k d (fun z => H z.2.2) := by
  have hsm : ∀ H : (Fin N → ℝ) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) H {0}ᶜ →
      ContDiffOn ℝ (⊤ : ℕ∞) (fun z : KZ N => H z.2.2) {z | z.2.2 ≠ 0} := fun H hH =>
    hH.comp (contDiff_snd.snd).contDiffOn (fun z hz => hz)
  have hdiff : ∀ H : (Fin N → ℝ) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) H {0}ᶜ →
      ∀ v : Fin N → ℝ, v ≠ 0 → DifferentiableAt ℝ H v := fun H hH v hv =>
    (hH.contDiffAt (isOpen_compl_singleton.mem_nhds hv)).differentiableAt (by simp)
  have h0 : ∀ {d : ℤ} (H : (Fin N → ℝ) → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) H {0}ᶜ →
      (∀ t : ℝ, 0 < t → ∀ u : Fin N → ℝ, u ≠ 0 → H (G.dilate t u) = t ^ d * H u) →
      WtSym G K R 0 d (fun z => H z.2.2) := by
    intro d H hH hhom
    refine WtSym.intro_zero (hsm H hH) ?_
    have hΨ : ContDiffOn ℝ 1 (kernelUncurry (fun (_ _ u : Fin N → ℝ) => H u)) {z | z.2.2 ≠ 0} :=
      (hsm H hH).of_le (by simp)
    have hWB := hasWeightedBounds_of_homogeneous (G := G) hΨ
      (fun ξ η t ht u hu => hhom t ht u hu)
    obtain ⟨M, hM0, hM⟩ := hWB {0} isCompact_singleton R
    exact ⟨M, hM0, fun z _ hz hρ => (hM 0 rfl 0 rfl z.2.2 hz hρ).1⟩
  intro k
  induction k with
  | zero => exact fun H hH hhom => h0 H hH hhom
  | succ k ih =>
    intro d H hH hhom
    refine WtSym.intro_succ (h0 H hH hhom) (fun s => ?_)
    rcases s with l | l | j
    · refine WtSym.congr (fun z hz => ?_)
        (WtSym.zero_fun (k := k) (d := d - symWt G (Sum.inl l)))
      rw [fderiv_uslice (hdiff H hH _ hz)]
      simp [symDir]
    · refine WtSym.congr (fun z hz => ?_)
        (WtSym.zero_fun (k := k) (d := d - symWt G (Sum.inr (Sum.inl l))))
      rw [fderiv_uslice (hdiff H hH _ hz)]
      simp [symDir]
    · have hdH : ContDiffOn ℝ (⊤ : ℕ∞) (fun u => fderiv ℝ H u (Pi.single j 1)) {0}ᶜ :=
        (hH.fderiv_of_isOpen isOpen_compl_singleton (by simp)).clm_apply contDiffOn_const
      have h1 := ih (fun u => fderiv ℝ H u (Pi.single j 1)) hdH
        (fun t ht u hu => partial_homogeneous G hH hhom j ht hu)
      refine WtSym.congr (fun z hz => ?_) h1
      rw [fderiv_uslice (hdiff H hH _ hz)]
      rfl

/-- The coordinate function `u ↦ u_j` is a symbol of degree `w_j`. -/
theorem WtSym.coord (K : Set ((Fin N → ℝ) × (Fin N → ℝ))) (R : ℝ) (k : ℕ) (j : Fin N) :
    WtSym G K R k (G.weight j : ℤ) (fun z => z.2.2 j) :=
  WtSym.homogeneous G K R (fun u => u j) (contDiff_apply ℝ ℝ j).contDiffOn
    (fun t _ u _ => by rw [kdilate_apply, zpow_natCast])

/-- **Coordinates of a homogeneous field are symbols.** If `Y(δ_t u) = t^(-a) δ_t(Y u)`
(the model fields of the lifted chart, `a = w_i`), then `u ↦ Y(u)_j` is a symbol of degree
`w_j - a`. -/
theorem WtSym.fieldCoord (K : Set ((Fin N → ℝ) × (Fin N → ℝ))) (R : ℝ) (k : ℕ)
    {Y : (Fin N → ℝ) → (Fin N → ℝ)} (a : ℕ) (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    (hhom : ∀ t : ℝ, 0 < t → ∀ u, Y (G.dilate t u) = t ^ (-(a : ℤ)) • G.dilate t (Y u))
    (j : Fin N) : WtSym G K R k ((G.weight j : ℤ) - a) (fun z => Y z.2.2 j) := by
  refine WtSym.homogeneous G K R (fun u => Y u j) (contDiff_pi.1 hY j).contDiffOn ?_
  intro t ht u _
  have h := congrFun (hhom t ht u) j
  simp only [Pi.smul_apply, smul_eq_mul] at h
  show Y (G.dilate t u) j = _
  rw [h, kdilate_apply, sub_eq_add_neg, zpow_add₀ ht.ne', zpow_natCast]
  ring

end Homogeneous

end RothschildStein.P1
