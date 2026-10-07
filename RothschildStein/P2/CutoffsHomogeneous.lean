-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.CutoffsSymbols
public import RothschildStein.H3.HomogeneousBounds
public import RothschildStein.Definitions.HomogeneousGroup.dilate

/-!
# Homogeneous symbols

A function smooth off the origin and homogeneous of degree `e` for the model dilations lies in
every symbol class `Sym c k e` (BB p. 579, the homogeneous model derivative of degree `1 - j`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.P2

variable {N : ℕ}

/-- The model dilation `δ_t` as a continuous linear map. -/
def dilCLM (G : HomogeneousGroup N) (t : ℝ) : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  LinearMap.toContinuousLinearMap (LinearMap.pi fun i => (t ^ G.weight i) • LinearMap.proj i)

theorem dilCLM_apply (G : HomogeneousGroup N) (t : ℝ) (u : Fin N → ℝ) :
    dilCLM G t u = G.dilate t u := by
  ext i
  simp [dilCLM, HomogeneousGroup.dilate, coordinateDilation]

theorem dilate_ne_zero (G : HomogeneousGroup N) {t : ℝ} (ht : 0 < t) {u : Fin N → ℝ}
    (hu : u ≠ 0) : G.dilate t u ≠ 0 := by
  intro h
  apply hu
  ext i
  have hi := congrFun h i
  simp only [HomogeneousGroup.dilate, coordinateDilation, Pi.zero_apply] at hi
  rcases mul_eq_zero.mp hi with h0 | h0
  · exact absurd h0 (pow_ne_zero _ ht.ne')
  · simpa using h0

theorem dilCLM_single (G : HomogeneousGroup N) (t : ℝ) (j : Fin N) :
    dilCLM G t (Pi.single j 1) = (t ^ G.weight j) • (Pi.single j (1 : ℝ) : Fin N → ℝ) := by
  ext i
  by_cases h : i = j
  · subst h; simp [dilCLM]
  · simp [dilCLM, h]

/-- The partial derivatives of a homogeneous function are homogeneous of degree `e - ω_j`. -/
theorem pdv_homogeneous (G : HomogeneousGroup N) {e : ℤ} {H : (Fin N → ℝ) → ℝ}
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H {0}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ u, u ≠ 0 → H (G.dilate t u) = t ^ e * H u) (j : Fin N) :
    ∀ t : ℝ, 0 < t → ∀ u, u ≠ 0 →
      pdv j H (G.dilate t u) = t ^ (e - (G.weight j : ℤ)) * pdv j H u := by
  intro t ht u hu
  have hopen : IsOpen ({0}ᶜ : Set (Fin N → ℝ)) := isOpen_compl_singleton
  have hdu : G.dilate t u ≠ 0 := dilate_ne_zero G ht hu
  have hdiffu : DifferentiableAt ℝ H u :=
    (hH.contDiffAt (hopen.mem_nhds hu)).differentiableAt (by simp)
  have hdiffdu : DifferentiableAt ℝ H (dilCLM G t u) := by
    rw [dilCLM_apply]
    exact (hH.contDiffAt (hopen.mem_nhds hdu)).differentiableAt (by simp)
  have hev : (fun v => H (dilCLM G t v)) =ᶠ[𝓝 u] fun v => t ^ e * H v := by
    filter_upwards [hopen.mem_nhds hu] with v hv
    rw [dilCLM_apply]
    exact hhom t ht v hv
  have h1 : HasFDerivAt (fun v => H (dilCLM G t v))
      ((fderiv ℝ H (dilCLM G t u)).comp (dilCLM G t)) u :=
    hdiffdu.hasFDerivAt.comp u (dilCLM G t).hasFDerivAt
  have h2 : HasFDerivAt (fun v => t ^ e * H v) (t ^ e • fderiv ℝ H u) u :=
    hdiffu.hasFDerivAt.const_mul _
  have h3 := hev.fderiv_eq (𝕜 := ℝ)
  rw [h1.fderiv, h2.fderiv] at h3
  have h4 := congrArg (fun L : (Fin N → ℝ) →L[ℝ] ℝ => L (Pi.single j 1)) h3
  simp only [ContinuousLinearMap.comp_apply, dilCLM_single, map_smul, smul_apply, smul_eq_mul]
    at h4
  have hw : (t ^ G.weight j) ≠ 0 := pow_ne_zero _ ht.ne'
  have hd : dilCLM G t u = G.dilate t u := dilCLM_apply G t u
  rw [hd] at h4
  unfold pdv
  rw [zpow_sub₀ ht.ne', zpow_natCast]
  field_simp
  linarith [h4]

/-- A homogeneous function lies in every symbol class of its degree. -/
theorem Sym.of_homogeneous (G : HomogeneousGroup N) {c : SymCtx N}
    (hω : c.ω = G.weight) (hν : G.IsHomogeneousGauge c.ν) :
    ∀ (k : ℕ) (e : ℤ) (H : (Fin N → ℝ) → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) H {0}ᶜ →
      (∀ t : ℝ, 0 < t → ∀ u, u ≠ 0 → H (G.dilate t u) = t ^ e * H u) →
        Sym c k e (fun _ => H) := by
  have hPne : ∀ u ∈ c.P, u ≠ 0 := by
    intro u hu hu0
    have h0 := hu.1
    rw [hu0, (hν.2.2.1 0).mpr rfl] at h0
    exact lt_irrefl _ h0
  intro k
  induction k with
  | zero =>
    intro e H hH hhom
    refine Sym.intro_zero c (fun η _ => hH.mono (fun u hu => hPne u hu)) ?_
    obtain ⟨M, _, _, _, hM⟩ := H3.homogeneous_function_sphere_bound hν (e : ℝ) hH.continuousOn
      (fun t ht x hx => by rw [hhom t ht x hx, Real.rpow_intCast])
    exact ⟨M, fun η _ u hu => by
      have := hM u (hPne u hu)
      rwa [Real.rpow_intCast] at this⟩
  | succ k ih =>
    intro e H hH hhom
    refine Sym.intro_succ c ((ih e H hH hhom).zero_part c) (fun j => ?_)
    have hopen : IsOpen ({0}ᶜ : Set (Fin N → ℝ)) := isOpen_compl_singleton
    have hs : ContDiffOn ℝ (⊤ : ℕ∞) (pdv j H) {0}ᶜ := by
      have h := (hH.fderiv_of_isOpen hopen (m := (⊤ : ℕ∞)) (by simp)).clm_apply
        (contDiffOn_const (c := (Pi.single j 1 : Fin N → ℝ)))
      exact h
    have hj : (c.ω j : ℤ) = (G.weight j : ℤ) := by rw [hω]
    rw [hj]
    exact ih (e - (G.weight j : ℤ)) (pdv j H) hs (pdv_homogeneous G hH hhom j)

end RothschildStein.P2
