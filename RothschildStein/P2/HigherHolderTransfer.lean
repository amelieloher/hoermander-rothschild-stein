-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HigherHolderLadder
public import RothschildStein.P2.SmoothingGlue
public import RothschildStein.P2.SmoothingIntrinsic
public import RothschildStein.P2.SmoothingBridge
public import RothschildStein.P2.SmoothingDescent

/-!
# Transfer: from the lifted regularity to the original domain (local step)

Part of the higher Hölder estimate (BB p. 604: "Transfer and use the finite-cover argument"; the
descent of regularity as in the distributional smoothing theorem, BB pp. 609–610; the Hölder transfer). Given the lifted higher Hölder estimate `LiftedHigherHolderEstimate` at a
chart and the original local doubling, for `u ∈ C^{2,α}_X(V_b)` with `L u = f ∈ C^{k,α}_X(V_b)`
(intrinsic derivatives, no regularity beyond order two presupposed) on a small base ball:

* the lifted function `ũ = u ∘ π` is of class `C^{2,α}_{X̃}` on the lifted ball (`memHolderX_comp_basePoint`,
  lifting of derivatives); `LiftedHigherHolderEstimate` makes it of class `C^{k+2,α}_{X̃}` on `U_r^ρ`, with its estimate;
* the continuous weak lifted derivatives of `ũ` on a cylinder `A × B ⊆ U_r^ρ` descend to intrinsic derivatives of
  `u` on `A` (`hasIntrinsicWordDeriv_descent`, as in the distributional smoothing theorem);
* on a base ball `V_s ⊆ A` the reverse Hölder transfer (`holderTransfer_reverse_words`, derivatives of `u`
  on `V_s` known) bounds the original norm of order `k + 2` by the lifted one (`higher_holder_local_transfer`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2.HigherHolder

open RothschildStein.P1

section Local

variable {n q st m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- A function of finite weighted Hölder norm: the norm is finite. -/
theorem holderXENorm_lt_top_of_memHolderX {n' k' : ℕ} {w' : Fin k' → ℕ+}
    {X' : Fin k' → (Fin n' → ℝ) → (Fin n' → ℝ)} {d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞}
    {V : Opens (Fin n' → ℝ)} {j : ℕ} {α : ℝ} {f : (Fin n' → ℝ) → ℝ}
    (h : memHolderX w' X' d V j α f) : holderXENorm w' X' d V j α f < ⊤ := by
  unfold holderXENorm
  refine ENNReal.sum_lt_top.2 fun I hI => ?_
  obtain ⟨g, hg, hgf⟩ := h.2 I hI
  exact lt_of_le_of_lt (sInf_le ⟨g, hg, rfl⟩) hgf

/-- **Descent of the lifted regularity**: if the lifted function `ũ = u ∘ π` is of
class `C^{N,α}_{X̃}` on `U_r^ρ`, then on every cylinder base `A` of a cylinder `A × B ⊆ U_r^ρ` the function `u`
has the intrinsic word derivatives of weight at most `N` (BB pp. 609–610, as in the distributional smoothing theorem). -/
theorem exists_intrinsic_on_base_of_lift (C : LiftedChart noDriftWeight st Ω hΩ X x₀ m)
    {Ur : Opens (Fin (n + m) → ℝ)} (hUrU : (Ur : Set (Fin (n + m) → ℝ)) ⊆ C.U) {α : ℝ} (hα : 0 < α)
    {N : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hlift : memHolderX noDriftWeight C.Xl C.dl Ur N α (fun ξ => u (basePoint ξ)))
    {A : Opens (Fin n → ℝ)} {B : Opens (Fin m → ℝ)}
    (hsub : (cylinder A B : Set (Fin (n + m) → ℝ)) ⊆ (Ur : Set (Fin (n + m) → ℝ)))
    (hBfin : volume (B : Set (Fin m → ℝ)) < ⊤) {η : TestFunction B ℝ (⊤ : ℕ∞)}
    (hη : ∫ t : Fin m → ℝ, η t = 1) (h0B : (0 : Fin m → ℝ) ∈ (B : Set (Fin m → ℝ))) :
    ∀ I ∈ wordFamily noDriftWeight N, ∃ g : (Fin n → ℝ) → ℝ, hasIntrinsicWordDeriv X A I u g := by
  classical
  intro I hI
  have hXr : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (Ur : Set (Fin (n + m) → ℝ)) := fun i =>
    (C.lift_smooth i).mono (fun x hx => holderTransfer_U_subset_O C (hUrU hx))
  obtain ⟨D, hD0, hD⟩ := exists_selfJet_of_memHolderX hUrU hXr hα hlift
  have hsubU : (cylinder A B : Set (Fin (n + m) → ℝ)) ⊆ C.U := hsub.trans hUrU
  let Sf := liftedChart_cylinderFiberSetting C A B hsubU hBfin
  have hcontlift : ContinuousOn (fun ξ => u (basePoint ξ)) (Ur : Set (Fin (n + m) → ℝ)) :=
    LiftedChart.continuousOn_of_holderENorm_lt_top hUrU hα hlift.1
  have hjoin : ∀ x ∈ (A : Set (Fin n → ℝ)),
      joinPoint x (0 : Fin m → ℝ) ∈ (cylinder A B : Set (Fin (n + m) → ℝ)) := fun x hx =>
    joinPoint_mem_cylinder.2 ⟨hx, h0B⟩
  have hu_cont : ContinuousOn u (A : Set (Fin n → ℝ)) := by
    have h1 : ContinuousOn (fun x => u (basePoint (joinPoint x (0 : Fin m → ℝ))))
        (A : Set (Fin n → ℝ)) :=
      hcontlift.comp (continuous_joinPoint_left (0 : Fin m → ℝ)).continuousOn
        (fun x hx => hsub (hjoin x hx))
    simpa [basePoint_joinPoint] using h1
  have hu_loc : LocallyIntegrableOn u (A : Set (Fin n → ℝ)) volume :=
    hu_cont.locallyIntegrableOn A.isOpen.measurableSet
  have hT : ∀ ψ : TestFunction (cylinder A B) ℝ (⊤ : ℕ∞),
      Distribution.ofFun A u volume (⊤ : ℕ∞) (Sf.test ψ) =
        Distribution.ofFun (cylinder A B) (fun ξ => u (basePoint ξ)) volume (⊤ : ℕ∞) ψ :=
    fun ψ => Sf.ofFun_test hu_loc ψ
  have hw_loc : LocallyIntegrableOn (fun ξ => u (basePoint ξ)) (cylinder A B : Set (Fin (n + m) → ℝ))
      volume := Sf.locallyIntegrableOn_comp_basePoint hu_loc
  have hsubO : (A : Set (Fin n → ℝ)) ⊆ Ω := by
    intro x hx
    have := holderTransfer_U_subset_O C (hsubU (hjoin x hx))
    simpa [LiftedChart.O, basePoint_joinPoint] using this
  have hXA : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (A : Set (Fin n → ℝ)) := fun i =>
    (liftedChart_contDiffOn_base C i).mono hsubO
  have hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X C.P i)
      (cylinder A B : Set (Fin (n + m) → ℝ)) := fun i => (hXr i).mono hsub
  have hwk : ∀ J ∈ wordFamily noDriftWeight N,
      hasWeakWordDeriv (triangularLift X C.P) (cylinder A B) J (fun ξ => u (basePoint ξ)) (D J) :=
    fun J hJ => S.hasWeakWordDeriv_restrict (triangularLift X C.P) Ur (cylinder A B) hsub (hD J hJ).1
  refine ⟨fun x => D I (joinPoint x 0), ?_⟩
  have hsubl : ∀ J, J.Sublist I → J ∈ wordFamily noDriftWeight N := fun J hJ =>
    S.sublist_mem_wordFamily _ N hJ hI
  have := hasIntrinsicWordDeriv_descent (A := A) (B := B) X C.P hXt hXA Sf hη
    (Distribution.ofFun A u volume (⊤ : ℕ∞)) hw_loc hT I D hD0
    (fun J hJ => hwk J (hsubl J hJ))
    (fun J hJ => (LiftedChart.continuousOn_of_holderENorm_lt_top hUrU hα
      (lt_top_iff_ne_top.2 (hD J (hsubl J hJ)).2)).mono hsub) h0B
  have e : (fun x => (fun ξ => u (basePoint ξ)) (joinPoint x (0 : Fin m → ℝ))) = u := by
    funext x
    simp [basePoint_joinPoint]
  rw [e] at this
  exact this.2

/-- **Local regularity and estimate on
the original domain** (BB p. 604; Hölder transfer, descent of regularity, local doubling). Let `C` be a lifted no-drift chart centred above `x₀`
with the original local doubling `OriginalLocalDoubling` on `π(U)` and the lifted higher estimate
`LiftedHigherHolderEstimate`. For `ε > 0` there are `0 < ρ ≤ b ≤ ε` and `K > 0` such that for `u ∈ C^{2,α}_X(V_b)`
with `L u = f ∈ C^{k,α}_X(V_b)` (intrinsic derivatives): `u ∈ C^{k+2,α}_X(V_ρ)` and
`‖u‖_{C^{k+2,α}(V_ρ)} ≤ K (‖f‖_{C^{k,α}(V_b)} + ‖u‖_{L^∞(V_b)})` (`V_ρ = B(x₀, ρ)`, `V_b = B(x₀, b)`); the control balls
`B(x₀, ρ')`, `ρ' ≤ b`, are Euclidean open. -/
theorem higher_holder_local_transfer (C : LiftedChart noDriftWeight st Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {k : ℕ}
    (hdbl : OriginalLocalDoubling Ω noDriftWeight X (basePoint '' C.U))
    (hest : LiftedHigherHolderEstimate C ν α k) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ b K : ℝ, 0 < ρ ∧ ρ ≤ b ∧ b ≤ ε ∧ 0 < K ∧
      (∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ b → IsOpen (rsBall Ω noDriftWeight X x₀ ρ')) ∧
      ∀ (Vρ Vb : Opens (Fin n → ℝ)), (Vρ : Set (Fin n → ℝ)) = rsBall Ω noDriftWeight X x₀ ρ →
        (Vb : Set (Fin n → ℝ)) = rsBall Ω noDriftWeight X x₀ b → ∀ u f : (Fin n → ℝ) → ℝ,
        memHolderX noDriftWeight X (controlDistance Ω noDriftWeight X) Vb 2 α u →
        HasIntrinsicOperatorValue X Vb (noDriftOpWords q) u f →
        memHolderX noDriftWeight X (controlDistance Ω noDriftWeight X) Vb k α f →
        memHolderX noDriftWeight X (controlDistance Ω noDriftWeight X) Vρ (k + 2) α u ∧
        holderXENorm noDriftWeight X (controlDistance Ω noDriftWeight X) Vρ (k + 2) α u ≤
          ENNReal.ofReal K * (holderXENorm noDriftWeight X (controlDistance Ω noDriftWeight X) Vb k α f +
            eLpNorm u ⊤ (volume.restrict (Vb : Set (Fin n → ℝ)))) := by
  classical
  set η₀ : Fin (n + m) → ℝ := joinPoint x₀ (0 : Fin m → ℝ) with hη₀
  have hK : IsCompact ({η₀} : Set (Fin (n + m) → ℝ)) := isCompact_singleton
  have hKU : ({η₀} : Set (Fin (n + m) → ℝ)) ⊆ C.U := singleton_subset_iff.mpr C.center_mem
  have hbase : basePoint η₀ = x₀ := basePoint_joinPoint x₀ 0
  have hν0 : ν 0 = 0 := (ν.gauge.2.2.1 0).2 rfl
  obtain ⟨r₀, hr₀, βn, Kc, hKc, hhigh⟩ := hest
  obtain ⟨Cν, hCν1, hgc⟩ := exists_gauge_comparison C ν
  obtain ⟨ρ₀, hρ₀, hopen⟩ := exists_isOpen_base_ball C
  obtain ⟨-, rR, δR, hrR, hδR0, hδR1, hrev⟩ := holderTransfer_of_doubling C hα hα1 hK hKU hdbl
  obtain ⟨rB, cv, Cv, δB, cf, Cf, hrB, -, -, -, -, -, -, hall⟩ := C.ball_bounds {η₀} hK hKU
  have hCν0 : 0 < Cν := lt_of_lt_of_le one_pos hCν1
  -- the radii
  set R : ℝ := min (min rB rR) (min ρ₀ ε) with hR
  have hR0 : 0 < R := lt_min (lt_min hrB hrR) (lt_min hρ₀ hε)
  have hRB : R ≤ rB := (min_le_left _ _).trans (min_le_left _ _)
  have hRR : R ≤ rR := (min_le_left _ _).trans (min_le_right _ _)
  have hRρ : R ≤ ρ₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hRε : R ≤ ε := (min_le_right _ _).trans (min_le_right _ _)
  set r : ℝ := min (r₀ / 2) (R / (8 * Cν)) with hr
  have hr0 : 0 < r := lt_min (by positivity) (by positivity)
  have hrr₀ : r < r₀ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr₀)
  have hrR' : r ≤ R / (8 * Cν) := min_le_right _ _
  set b : ℝ := 4 * Cν * r with hb
  have hb0 : 0 < b := by positivity
  -- the cylinder inside the lifted `ρ`-ball of radius `r`
  have hξUR : η₀ ∈ (rhoBallOpen C ν r : Set (Fin (n + m) → ℝ)) := by
    refine ⟨C.center_mem, ?_⟩
    have h0 : C.Θ η₀ η₀ = 0 := (C.chart η₀ C.center_mem).2.2.2.2
    show ν (C.Θ η₀ η₀) < r
    rw [h0, hν0]
    exact hr0
  obtain ⟨A, B, hxA, h0B, hcpt, hcl', hBfin, hBpos⟩ :=
    exists_cylinder_closure_subset (UR := rhoBallOpen C ν r) hξUR
  obtain ⟨η, hη⟩ := exists_test_integral_eq_one B h0B
  have hsubUR : (cylinder A B : Set (Fin (n + m) → ℝ)) ⊆ (rhoBallOpen C ν r : Set (Fin (n + m) → ℝ)) :=
    subset_closure.trans hcl'
  obtain ⟨εA, hεA0, hεA⟩ := exists_rsBall_subset (w := noDriftWeight) hΩ
    (fun i => (liftedChart_contDiffOn_base C i).continuousOn) A.isOpen hxA (liftedChart_base_mem C)
  set s₁ : ℝ := min (r / Cν) εA with hs₁
  have hs₁0 : 0 < s₁ := lt_min (by positivity) hεA0
  have hs₁le : s₁ ≤ r / Cν := min_le_left _ _
  have hs₁A : s₁ ≤ εA := min_le_right _ _
  set a : ℝ := s₁ / 2 with ha
  have ha0 : 0 < a := by positivity
  have has : a < s₁ := by rw [ha]; linarith
  have hs₁r : s₁ ≤ r := hs₁le.trans (div_le_self hr0.le hCν1)
  have hs₁b : s₁ ≤ b := by
    rw [hb]
    nlinarith
  have hbR : b ≤ R / 2 := by
    rw [hb]
    have : 4 * Cν * r ≤ 4 * Cν * (R / (8 * Cν)) :=
      mul_le_mul_of_nonneg_left hrR' (by positivity)
    calc 4 * Cν * r ≤ 4 * Cν * (R / (8 * Cν)) := this
      _ = R / 2 := by field_simp; ring
  have hbR' : b < R := by linarith
  have hbrB : b < rB := lt_of_lt_of_le hbR' hRB
  have hs₁rR : s₁ < rR := lt_of_le_of_lt hs₁b (lt_of_lt_of_le hbR' hRR)
  have hbρ : b ≤ ρ₀ := (hbR'.trans_le hRρ).le
  have hbε : b ≤ ε := (hbR'.trans_le hRε).le
  have hδa0 : 0 < δR * a := mul_pos hδR0 ha0
  have hδa : δR * a ≤ b := by nlinarith
  -- the reverse transfer at `(a, s₁)`
  obtain ⟨CR, hCR, hCRall⟩ := hrev a s₁ ha0 has hs₁rR
  obtain ⟨-, hwords⟩ := hCRall η₀ (mem_singleton _)
  -- the lifted balls
  have hUsU : rsBall C.O noDriftWeight C.Xl η₀ s₁ ⊆ C.U := by
    obtain ⟨h, -⟩ := hall η₀ (mem_singleton _) s₁ hs₁0 (lt_of_le_of_lt hs₁b hbrB)
    exact h
  have hUbU : rsBall C.O noDriftWeight C.Xl η₀ b ⊆ C.U := by
    obtain ⟨h, -⟩ := hall η₀ (mem_singleton _) b hb0 hbrB
    exact h
  let Vs : Opens (Fin n → ℝ) :=
    ⟨rsBall Ω noDriftWeight X (basePoint η₀) s₁, by
      rw [hbase]; exact hopen s₁ hs₁0 (hs₁b.trans hbρ)⟩
  let Us : Opens (Fin (n + m) → ℝ) := ⟨rsBall C.O noDriftWeight C.Xl η₀ s₁, isOpen_rsBall_lifted C hUsU⟩
  let Ub : Opens (Fin (n + m) → ℝ) := ⟨rsBall C.O noDriftWeight C.Xl η₀ b, isOpen_rsBall_lifted C hUbU⟩
  -- inclusions of balls
  have hUs_ρ : (Us : Set (Fin (n + m) → ℝ)) ⊆ (rhoBallOpen C ν r : Set (Fin (n + m) → ℝ)) := by
    intro ξ hξ
    have hξ' : ξ ∈ rsBall C.O noDriftWeight C.Xl η₀ s₁ := hξ
    have hξU : ξ ∈ C.U := hUsU hξ'
    refine ⟨hξU, ?_⟩
    obtain ⟨hl, -⟩ := hgc η₀ C.center_mem ξ hξU
    have h1 : ENNReal.ofReal (ν (C.Θ η₀ ξ) / Cν) < ENNReal.ofReal s₁ := lt_of_le_of_lt hl hξ'.2
    have h2 : ν (C.Θ η₀ ξ) / Cν < s₁ := (ENNReal.ofReal_lt_ofReal_iff hs₁0).1 h1
    calc ν (C.Θ η₀ ξ) < s₁ * Cν := (div_lt_iff₀ hCν0).1 h2
      _ ≤ r / Cν * Cν := mul_le_mul_of_nonneg_right hs₁le hCν0.le
      _ = r := by field_simp
  have hcl : closedRhoBall C ν η₀ (2 * r) ⊆ (Ub : Set (Fin (n + m) → ℝ)) := by
    intro ξ hξ
    obtain ⟨hξU, hν⟩ := hξ
    refine ⟨C.closure_U_subset (subset_closure hξU), ?_⟩
    obtain ⟨-, hup⟩ := hgc η₀ C.center_mem ξ hξU
    refine lt_of_le_of_lt hup ((ENNReal.ofReal_lt_ofReal_iff hb0).2 ?_)
    nlinarith [mul_pos hCν0 hr0]
  have hρ2_Ub : (rhoBallOpen C ν (2 * r) : Set (Fin (n + m) → ℝ)) ⊆ (Ub : Set (Fin (n + m) → ℝ)) :=
    (rhoBall_subset_closed C ν η₀).trans hcl
  refine ⟨δR * a, b, CR * (Kc * (r⁻¹) ^ βn), hδa0, hδa, hbε, mul_pos hCR (by positivity),
    fun ρ' h0 h1 => hopen ρ' h0 (h1.trans hbρ), ?_⟩
  intro Vρ Vb hVρ hVb u f hu hf hfk
  -- the base sets
  have hVsVb : (Vs : Set (Fin n → ℝ)) ⊆ (Vb : Set (Fin n → ℝ)) := by
    show rsBall Ω noDriftWeight X (basePoint η₀) s₁ ⊆ (Vb : Set (Fin n → ℝ))
    rw [hVb, hbase]
    exact rsBall_mono Ω noDriftWeight X x₀ hs₁b
  have hVρVs : (Vρ : Set (Fin n → ℝ)) ⊆ (Vs : Set (Fin n → ℝ)) := by
    show (Vρ : Set (Fin n → ℝ)) ⊆ rsBall Ω noDriftWeight X (basePoint η₀) s₁
    rw [hVρ, hbase]
    exact rsBall_mono Ω noDriftWeight X x₀ (by nlinarith [mul_lt_mul_of_pos_right hδR1 ha0])
  have hVsA : (Vs : Set (Fin n → ℝ)) ⊆ (A : Set (Fin n → ℝ)) := by
    show rsBall Ω noDriftWeight X (basePoint η₀) s₁ ⊆ (A : Set (Fin n → ℝ))
    rw [hbase]
    exact (rsBall_mono Ω noDriftWeight X x₀ hs₁A).trans hεA
  have hproj : ∀ ξ ∈ (Ub : Set (Fin (n + m) → ℝ)), basePoint ξ ∈ (Vb : Set (Fin n → ℝ)) := by
    intro ξ hξ
    have h1 := basePoint_mem_rsBall (P := C.P) (hξ : ξ ∈ rsBall C.O noDriftWeight C.Xl η₀ b)
    rw [hbase] at h1
    rw [hVb]
    exact h1
  have hXt_b := liftedChart_hXt C Ub hUbU
  -- the lifted data
  have hut : memHolderX noDriftWeight C.Xl C.dl Ub 2 α (fun ξ => u (basePoint ξ)) :=
    memHolderX_comp_basePoint (P := C.P) Ω Ub Vb hproj hXt_b hα.le 2 hu
  have hft : HasIntrinsicOperatorValue C.Xl Ub (noDriftOpWords q) (fun ξ => u (basePoint ξ))
      (fun ξ => f (basePoint ξ)) := hf.lift Ub Vb hproj hXt_b
  have hfkt : memHolderX noDriftWeight C.Xl C.dl Ub k α (fun ξ => f (basePoint ξ)) :=
    memHolderX_comp_basePoint (P := C.P) Ω Ub Vb hproj hXt_b hα.le k hfk
  -- (1) the lifted regularity and estimate
  obtain ⟨hreg, h3⟩ := hhigh r hr0 hrr₀ Ub hcl _ _ hut hft hfkt
  -- (2) descent: intrinsic derivatives of `u` on `A`
  have hUrU : (rhoBallOpen C ν r : Set (Fin (n + m) → ℝ)) ⊆ C.U := fun ξ hξ => hξ.1
  have hderivA := exists_intrinsic_on_base_of_lift C hUrU hα hreg hsubUR hBfin hη h0B
  have hderiv : ∀ I ∈ wordFamily noDriftWeight (k + 2), ∃ g, hasIntrinsicWordDeriv X Vs I u g := by
    intro I hI
    obtain ⟨g, hg⟩ := hderivA I hI
    exact ⟨g, hasIntrinsicWordDeriv_mono hVsA I hg⟩
  -- (3) the reverse transfer
  have hrw := hwords Vρ Vs Us (by rw [hVρ, hbase]) rfl rfl (k + 2) u hderiv
  have hf0 : holderXENorm noDriftWeight C.Xl C.dl (rhoBallOpen C ν (2 * r)) k α
      (fun ξ => f (basePoint ξ)) ≤
      holderXENorm noDriftWeight X (controlDistance Ω noDriftWeight X) Vb k α f :=
    (holderXENorm_mono_domain noDriftWeight hρ2_Ub k _).trans
      (holderXENorm_comp_le (P := C.P) Ω Ub Vb hproj hXt_b hα.le k f)
  have hu_top : eLpNorm (fun ξ => u (basePoint ξ)) ⊤
      (volume.restrict (rhoBallOpen C ν (2 * r) : Set (Fin (n + m) → ℝ))) ≤
      eLpNorm u ⊤ (volume.restrict (Vb : Set (Fin n → ℝ))) :=
    (eLpNorm_mono_measure _ (Measure.restrict_mono hρ2_Ub le_rfl)).trans
      (eLpNorm_top_comp_basePoint_le Ub.isOpen.measurableSet Vb.isOpen.measurableSet hproj u)
  have hbound : holderXENorm noDriftWeight X (controlDistance Ω noDriftWeight X) Vρ (k + 2) α u ≤
      ENNReal.ofReal (CR * (Kc * (r⁻¹) ^ βn)) *
        (holderXENorm noDriftWeight X (controlDistance Ω noDriftWeight X) Vb k α f +
          eLpNorm u ⊤ (volume.restrict (Vb : Set (Fin n → ℝ)))) := by
    calc holderXENorm noDriftWeight X (controlDistance Ω noDriftWeight X) Vρ (k + 2) α u
        ≤ ENNReal.ofReal CR * holderXENorm noDriftWeight C.Xl C.dl Us (k + 2) α
            (fun ξ => u (basePoint ξ)) := hrw
      _ ≤ ENNReal.ofReal CR * holderXENorm noDriftWeight C.Xl C.dl (rhoBallOpen C ν r) (k + 2) α
            (fun ξ => u (basePoint ξ)) :=
          mul_le_mul' le_rfl (holderXENorm_mono_domain noDriftWeight hUs_ρ (k + 2) _)
      _ ≤ ENNReal.ofReal CR * (ENNReal.ofReal (Kc * (r⁻¹) ^ βn) *
            (holderXENorm noDriftWeight X (controlDistance Ω noDriftWeight X) Vb k α f +
              eLpNorm u ⊤ (volume.restrict (Vb : Set (Fin n → ℝ))))) :=
          mul_le_mul' le_rfl (h3.trans (mul_le_mul' le_rfl (add_le_add hf0 hu_top)))
      _ = _ := by
          rw [ENNReal.ofReal_mul hCR.le, mul_assoc]
  refine ⟨?_, hbound⟩
  -- membership
  have hfin : holderXENorm noDriftWeight X (controlDistance Ω noDriftWeight X) Vρ (k + 2) α u < ⊤ := by
    refine lt_of_le_of_lt (hrw.trans (mul_le_mul' le_rfl
      (holderXENorm_mono_domain noDriftWeight hUs_ρ (k + 2) _))) ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (holderXENorm_lt_top_of_memHolderX hreg)
  have hVρΩ : (Vρ : Set (Fin n → ℝ)) ⊆ (Vs : Set (Fin n → ℝ)) := hVρVs
  refine ⟨?_, fun I hI => ?_⟩
  · have h1 : intrinsicWordENorm X (controlDistance Ω noDriftWeight X) Vρ [] α u =
        holderENorm (controlDistance Ω noDriftWeight X) α (Vρ : Set (Fin n → ℝ)) u :=
      intrinsicWordENorm_eq_holderENorm (fun x _ => rfl)
    rw [← h1]
    exact lt_of_le_of_lt (intrinsicWordENorm_le_holderXENorm noDriftWeight
      (S.nil_mem_wordFamily noDriftWeight (k + 2)) u) hfin
  · obtain ⟨g, hg⟩ := hderiv I hI
    have hgρ := hasIntrinsicWordDeriv_mono hVρVs I hg
    refine ⟨g, hgρ, ?_⟩
    rw [← intrinsicWordENorm_eq_holderENorm hgρ]
    exact lt_of_le_of_lt (intrinsicWordENorm_le_holderXENorm noDriftWeight hI u) hfin

end Local

end RothschildStein.P2.HigherHolder
