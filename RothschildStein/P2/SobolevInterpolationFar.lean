-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SobolevInterpolationTranspose
public import RothschildStein.P2.SobolevInterpolationCutoff
public import RothschildStein.P2.SobolevInterpolationShell
public import RothschildStein.P1.ContinuityTheorem

/-!
# Sobolev interpolation, far part: the six contributions bounded by `C ε^{-1}`

For a type-1 operator `T` of a lifted drift frame, the far kernel
`κ_{ξ,ε}(η) = T.kernel ξ η · (1 - φ_ε(ξ, η))` (`φ_ε` the radial cutoff centred at the
output point `ξ`) is `C²` on `V` and satisfies, for `η ∈ V`,
`|L̃ᵀ κ_{ξ,ε}(η)| ≤ K / max(d̃(ξ, η), c₁ ε)^(Q+1)` (`exists_farKernel_bound`): `κ = 0` near `η` when
`d̃ < c₁ ε`, and otherwise the product bound `abs_sumSquaresWithDriftTranspose_mul_le` applies to the jets
of the kernel (`typeKernel_jetBounds`, sizes `d̃^(1-Q-wt)`) and of the cutoff (`exists_centredCutoff`,
`B d̃^(-wt)`): `(L̃*_η k)(1 - φ)` of size `d̃^(-Q-1)`, the terms with `X̃_i(1 - φ)` and `L̃*(1 - φ)`
supported on the annulus `d̃ ≈ ε`, and the zeroth- and first-order adjoint coefficients (the six
contributions of BB p. 581). The integral of the far part against `L̃ v` is then
`∫ (L̃ᵀ κ) v` (`integral_mul_sumSquaresWithDrift`) and the Schur bound of
`SobolevInterpolationShell` gives `C ε^{-1} ‖v‖_p`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P2

open RothschildStein.P1 RothschildStein

section Elementary

variable {N : ℕ}

/-- `X̃(1 - φ) = -X̃ φ`. -/
theorem fieldDerivative_one_sub {V : (Fin N → ℝ) → (Fin N → ℝ)} {φ : (Fin N → ℝ) → ℝ}
    {x : Fin N → ℝ} :
    fieldDerivative V (fun y => 1 - φ y) x = -fieldDerivative V φ x := by
  unfold fieldDerivative
  rw [fderiv_const_sub]
  rfl

/-- `X̃ X̃ (1 - φ) = -X̃ X̃ φ`. -/
theorem fieldDerivative_fieldDerivative_one_sub {V : (Fin N → ℝ) → (Fin N → ℝ)}
    {φ : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ} :
    fieldDerivative V (fieldDerivative V (fun y => 1 - φ y)) x =
      -fieldDerivative V (fieldDerivative V φ) x := by
  have h : fieldDerivative V (fun y => 1 - φ y) = fun y => -fieldDerivative V φ y :=
    funext fun y => fieldDerivative_one_sub
  rw [h]
  unfold fieldDerivative
  rw [fderiv_fun_neg]
  rfl

/-- A function that vanishes near `x` has vanishing transpose of `L̃` at `x`. -/
theorem sumSquaresWithDriftTranspose_eq_zero_of_eventuallyEq {q : ℕ} (Ω : Opens (Fin N → ℝ))
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ))) {φ : (Fin N → ℝ) → ℝ}
    {x : Fin N → ℝ} (hx : x ∈ (Ω : Set (Fin N → ℝ))) (h : φ =ᶠ[𝓝 x] fun _ => 0) :
    sumSquaresWithDriftTranspose X φ x = 0 := by
  have hφ2 : ContDiffAt ℝ 2 φ x := contDiffAt_const.congr_of_eventuallyEq h
  rw [sumSquaresWithDriftTranspose_apply_of_contDiffAt Ω X hX φ hx hφ2]
  have e0 : φ x = 0 := h.eq_of_nhds
  have e1 : ∀ V : (Fin N → ℝ) → (Fin N → ℝ), fieldDerivative V φ x = 0 := fun V => by
    rw [fieldDerivative_congr_eventually h]
    exact fieldDerivative_const_zero
  have e2 : ∀ V W : (Fin N → ℝ) → (Fin N → ℝ), fieldDerivative V (fieldDerivative W φ) x = 0 :=
    fun V W => by
      rw [fieldDerivative_fieldDerivative_congr_eventually h]
      have : fieldDerivative W (fun _ : Fin N → ℝ => (0 : ℝ)) = fun _ => 0 :=
        funext fun y => fieldDerivative_const_zero
      rw [this]
      exact fieldDerivative_const_zero
  simp [e0, e1, e2]

/-- The three exponent identities used to put the kernel jets in the form `M d² u`,
`M d u`, `M u` with `u = d^(1-Q-2)`. -/
theorem zpow_exponent_cases {d : ℝ} (hd : 0 < d) (Qz : ℤ) :
    d ^ ((1 : ℤ) - Qz) = d ^ 2 * d ^ ((1 : ℤ) - Qz - 2) ∧
    d ^ ((1 : ℤ) - Qz - 1) = d * d ^ ((1 : ℤ) - Qz - 2) ∧
    d ^ ((1 : ℤ) - Qz - 1 - 1) = d ^ ((1 : ℤ) - Qz - 2) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show d ^ 2 = d ^ ((2 : ℤ)) from (zpow_ofNat d 2).symm, ← zpow_add₀ hd.ne']
    congr 1
    ring
  · rw [← zpow_one_add₀ hd.ne']
    congr 1
    ring
  · congr 1
    ring

/-- The far profile at `d ≥ a` is `K d^(1-Q-2) = K d^(-(Q+1))`. -/
theorem interpFarProfile_eq {d a : ℝ} (_hd : 0 < d) (had : a ≤ d) (K : ℝ) {Q : ℕ} (hQ : 1 ≤ Q) :
    interpFarProfile K a (Q - 1) d = K * d ^ ((1 : ℤ) - (Q : ℤ) - 2) := by
  unfold interpFarProfile
  rw [max_eq_left had]
  have : (1 : ℤ) - (Q : ℤ) - 2 = -((Q - 1 + 2 : ℕ) : ℤ) := by omega
  rw [this, zpow_neg, zpow_natCast, div_eq_mul_inv]

end Elementary

section Chart

variable {n q s m : ℕ} {w : Fin (q + 1) → ℕ+} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- The divergence coefficients of `L̃ᵀ` are bounded on a compact subset of the chart domain. -/
theorem exists_divergence_bounds (C : LiftedChart w s Ω hΩ X x₀ m)
    {L : Set (Fin (n + m) → ℝ)} (hL : IsCompact L) (hLU : L ⊆ C.U) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ i : Fin (q + 1), ∀ η ∈ L,
      |Hormander.Interface.euclideanDivergence (C.Xl i) η| ≤ Cd ∧
      |fieldDerivative (C.Xl i) (Hormander.Interface.euclideanDivergence (C.Xl i)) η +
        Hormander.Interface.euclideanDivergence (C.Xl i) η ^ 2| ≤ Cd := by
  let Ωo : Opens (Fin (n + m) → ℝ) := ⟨C.U, C.isOpen_U⟩
  have hdiv : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Hormander.Interface.euclideanDivergence (C.Xl i)) C.U :=
    fun i => contDiffOn_euclideanDivergence Ωo (C.Xl i) (C.contDiffOn_Xl_U i)
  have hg : ∀ i, ContinuousOn (fun η => fieldDerivative (C.Xl i)
      (Hormander.Interface.euclideanDivergence (C.Xl i)) η +
        Hormander.Interface.euclideanDivergence (C.Xl i) η ^ 2) C.U := fun i =>
    ((S.contDiffOn_fieldDerivative Ωo (C.Xl i) _ (C.contDiffOn_Xl_U i) (hdiv i)).continuousOn).add
      ((hdiv i).continuousOn.pow 2)
  choose B₁ hB₁ using fun i => hL.exists_bound_of_continuousOn ((hdiv i).continuousOn.mono hLU)
  choose B₂ hB₂ using fun i => hL.exists_bound_of_continuousOn ((hg i).mono hLU)
  refine ⟨∑ i, (max (B₁ i) 0 + max (B₂ i) 0), Finset.sum_nonneg (fun i _ =>
    add_nonneg (le_max_right _ _) (le_max_right _ _)), fun i η hη => ?_⟩
  have hi : max (B₁ i) 0 + max (B₂ i) 0 ≤ ∑ i, (max (B₁ i) 0 + max (B₂ i) 0) :=
    Finset.single_le_sum (f := fun i => max (B₁ i) 0 + max (B₂ i) 0)
      (fun i _ => add_nonneg (le_max_right _ _) (le_max_right _ _)) (Finset.mem_univ i)
  have h1 : |Hormander.Interface.euclideanDivergence (C.Xl i) η| ≤ max (B₁ i) 0 := by
    have := hB₁ i η hη
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have h2 : |fieldDerivative (C.Xl i) (Hormander.Interface.euclideanDivergence (C.Xl i)) η +
      Hormander.Interface.euclideanDivergence (C.Xl i) η ^ 2| ≤ max (B₂ i) 0 := by
    have := hB₂ i η hη
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have p1 : 0 ≤ max (B₁ i) 0 := le_max_right _ _
  have p2 : 0 ≤ max (B₂ i) 0 := le_max_right _ _
  exact ⟨h1.trans (by linarith), h2.trans (by linarith)⟩

/-- **The far kernel and its transpose.** For a type-1 operator `T` of a lifted drift
frame there are `ε₀ ∈ (0, 1]`, `K₀ ≥ 0`, `c₁ > 0` such that for `0 < ε < ε₀` and `ξ ∈ V` the far kernel
`κ(η) = T.kernel ξ η · (1 - φ_ε(ξ, η))` is `C²` on `V` and
`|L̃ᵀκ(η)| ≤ K₀ / max(d̃(ξ, η), c₁ ε)^(Q+1)` on `V` (BB pp. 581-583: the six contributions). -/
theorem exists_farKernel_bound (hF : C.IsLiftedFrame F) (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1)
    (hw0 : (w 0 : ℕ) = 2) (T : TypeOperator F 1) (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth) :
    ∃ ε₀ K₀ c₁ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 ≤ K₀ ∧ 0 < c₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)),
        ContDiffOn ℝ 2 (fun η => T.kernel ξ η * (1 - radialCutoff C ν ξ (ε / 4) ε η))
          (F.V : Set (Fin (n + m) → ℝ)) ∧
        ∀ η ∈ (F.V : Set (Fin (n + m) → ℝ)),
          |sumSquaresWithDriftTranspose C.Xl
              (fun η => T.kernel ξ η * (1 - radialCutoff C ν ξ (ε / 4) ε η)) η| ≤
            interpFarProfile K₀ (c₁ * ε) (C.G.homogeneousDimension - 1) (C.dl ξ η).toReal := by
  have hL : IsCompact (closure (F.V : Set (Fin (n + m) → ℝ))) := hF.isCompact_closure
  have hLU : closure (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U := hF.closure_subset
  have hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U := hF.subset_U
  have hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (F.V : Set (Fin (n + m) → ℝ)) :=
    fun i => (C.contDiffOn_Xl_U i).mono hVU
  obtain ⟨M, hM⟩ := typeKernel_jetBounds hF T
  obtain ⟨ε₀, c₁, c₂, B, hε₀, hε₀1, hc₁, hc₂, hB, hcut⟩ := exists_centredCutoff C ν hν hL hLU
  obtain ⟨D₀, hD₀, hD⟩ := LiftedChart.exists_dl_bound (C := C) hL hLU
  obtain ⟨Cd, hCd, hCdb⟩ := exists_divergence_bounds C hL hLU
  have hM0 : 0 ≤ M := hM.1
  have hQ1 : 1 ≤ C.G.homogeneousDimension := G2.homogeneousDimension_pos C.G
  set K₀ : ℝ := M * (q * (1 + 2 * B + B) + (1 + B) + 2 * q * Cd * D₀ * (1 + B) +
    (q + 1) * Cd * D₀ ^ 2) with hK₀
  have hK0 : 0 ≤ K₀ := by positivity
  refine ⟨ε₀, K₀, c₁, hε₀, hε₀1, hK0, hc₁, fun ε hε hεr ξ hξ => ?_⟩
  obtain ⟨hsm, hrange, hnear1, hfar0, hjets⟩ := hcut ξ (subset_closure hξ) ε hε hεr
  set φ : (Fin (n + m) → ℝ) → ℝ := radialCutoff C ν ξ (ε / 4) ε with hφ
  have hξU : ξ ∈ C.U := hVU hξ
  have hψsm : ContDiff ℝ (⊤ : ℕ∞) (fun y => 1 - φ y) := contDiff_const.sub hsm
  have hself : C.dl ξ ξ = 0 := G1.controlDistance_self w C.Xl (C.mem_O_of_mem_U hξU)
  have hzero : ∀ η ∈ C.U, (C.dl ξ η).toReal < c₁ * ε →
      (fun η' => T.kernel ξ η' * (1 - φ η')) =ᶠ[𝓝 η] fun _ => 0 := by
    intro η hη hd
    filter_upwards [hnear1 η hη hd] with η' hη'
    simp [hη']
  refine ⟨?_, ?_⟩
  · intro η hη
    refine ContDiffAt.contDiffWithinAt ?_
    rcases eq_or_ne η ξ with rfl | hηξ
    · have hd : (C.dl η η).toReal < c₁ * ε := by
        rw [hself]
        simpa using mul_pos hc₁ hε
      exact contDiffAt_const.congr_of_eventuallyEq (hzero η hξU hd)
    · have hk := (hM.2 ξ (subset_closure hξ) η (subset_closure hη) (Ne.symm hηξ)).1
      exact hk.mul (hψsm.contDiffAt.of_le (by simp))
  · intro η hη
    have hηU : η ∈ C.U := hVU hη
    have hP0 : 0 ≤ interpFarProfile K₀ (c₁ * ε) (C.G.homogeneousDimension - 1)
        (C.dl ξ η).toReal := interpFarProfile_nonneg hK0 (mul_pos hc₁ hε) _ ENNReal.toReal_nonneg
    by_cases hd : (C.dl ξ η).toReal < c₁ * ε
    · rw [sumSquaresWithDriftTranspose_eq_zero_of_eventuallyEq F.V C.Xl hXV hη
        (hzero η hηU hd), abs_zero]
      exact hP0
    · have hd' : c₁ * ε ≤ (C.dl ξ η).toReal := not_lt.mp hd
      set d : ℝ := (C.dl ξ η).toReal with hdd
      have hdpos : 0 < d := lt_of_lt_of_le (mul_pos hc₁ hε) hd'
      have hne : ξ ≠ η := by
        rintro rfl
        rw [hself] at hdd
        simp at hdd
        linarith
      have hdD : d ≤ D₀ := hD ξ (subset_closure hξ) η (subset_closure hη)
      obtain ⟨hc2, hsz, hj1, hj2⟩ := hM.2 ξ (subset_closure hξ) η (subset_closure hη) hne
      set Qz : ℤ := (C.G.homogeneousDimension : ℤ) with hQz
      obtain ⟨e1, e2, e3⟩ := zpow_exponent_cases hdpos Qz
      set u : ℝ := d ^ ((1 : ℤ) - Qz - 2) with hu
      have hu0 : 0 ≤ u := (zpow_pos hdpos _).le
      have hf0 : |T.kernel ξ η| ≤ M * d ^ 2 * u := by
        have := hsz
        rw [e1] at this
        linarith
      have hf1 : ∀ i : Fin q, |fieldDerivative (C.Xl i.succ) (T.kernel ξ) η| ≤ M * d * u := by
        intro i
        have := hj1 i.succ
        rw [hw i, Nat.cast_one, e2] at this
        linarith
      have hf2 : ∀ i : Fin q, |fieldDerivative (C.Xl i.succ) (fieldDerivative (C.Xl i.succ)
          (T.kernel ξ)) η| ≤ M * u := by
        intro i
        have := hj2 i.succ i.succ
        rw [hw i, Nat.cast_one, e3] at this
        exact this
      have hfd : |fieldDerivative (C.Xl 0) (T.kernel ξ) η| ≤ M * u := by
        have := hj1 0
        rw [hw0, show (((2 : ℕ)) : ℤ) = 2 from rfl] at this
        exact this
      have hg0 : |(fun y => 1 - φ y) η| ≤ 1 := by
        obtain ⟨h1, h2⟩ := hrange η
        exact abs_le.2 ⟨by simp only []; linarith, by simp only []; linarith⟩
      have hg1 : ∀ i : Fin q, |fieldDerivative (C.Xl i.succ) (fun y => 1 - φ y) η| * d ≤ B := by
        intro i
        have := (hjets η hηU i.succ).1
        rw [hw i, pow_one] at this
        rw [fieldDerivative_one_sub, abs_neg]
        exact this
      have hg2 : ∀ i : Fin q, |fieldDerivative (C.Xl i.succ) (fieldDerivative (C.Xl i.succ)
          (fun y => 1 - φ y)) η| * d ^ 2 ≤ B := by
        intro i
        have := (hjets η hηU i.succ).2
        rw [hw i, show 2 * 1 = 2 from rfl] at this
        rw [fieldDerivative_fieldDerivative_one_sub, abs_neg]
        exact this
      have hgd : |fieldDerivative (C.Xl 0) (fun y => 1 - φ y) η| * d ^ 2 ≤ B := by
        have := (hjets η hηU 0).1
        rw [hw0] at this
        rw [fieldDerivative_one_sub, abs_neg]
        exact this
      have hbound := abs_sumSquaresWithDriftTranspose_mul_le F.V C.Xl hXV hη
        (f := T.kernel ξ) (g := fun y => 1 - φ y) hc2
        (hψsm.contDiffAt.of_le (by simp)) (Cd := Cd) (M := M) (B₁ := B) (B₂ := B) (u := u)
        (d := d) (D₀ := D₀)
        (fun i => (hCdb i.succ η (subset_closure hη)).1) (hCdb 0 η (subset_closure hη)).1
        (fun i => (hCdb i.succ η (subset_closure hη)).2) hCd hM0 hB hu0 hdpos hdD hf0 hf1 hf2 hfd
        hg0 hg1 hg2 hgd
      rw [interpFarProfile_eq hdpos hd' K₀ hQ1]
      exact hbound

end Chart

end RothschildStein.P2
