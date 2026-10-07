-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SolvabilityNoDriftUnconditional
public import RothschildStein.P1.ParametrixStatementsAssembly
public import RothschildStein.P1.ParametrixKernelBoundsChart
public import RothschildStein.P1.ParametrixKernelBoundsNoDriftRight
public import RothschildStein.P1.RepresentationBasic
public import RothschildStein.P1.StandardFrame
public import RothschildStein.P1.ContinuityRegularAssembly

/-!
# Local solvability without drift: the right parametrix as a type-2 operator of a standard frame

For a lifted no-drift chart `C` with H1 fundamental kernel `Γ = K` of its no-drift model, the right
The right parametrix `P_R f(ξ) = a(ξ) ∫ Γ(Θ(η, ξ)) (b(η)/c(η)) f(η) dη` has the single principal
term `a(ξ) (b/c)(η) Γ(Θ(η, ξ))` (`D = id`) and therefore is a type-2 operator on every standard
frame with cutoff region `V ⋐ C.U` (`PrincipalTerm.ofCutoffs`, `isTypeKernelOn_of_eq_principal`).

* `exists_frame_cutoffs_noDrift`: for `ξ₀ ∈ C.U` there are a patch `V ∋ ξ₀` with compact closure in `C.U`
  and cutoffs `a, b ∈ C_c^∞(V)` with `a b = a` and `a = 1` near `ξ₀`;
* `stdFrameNoDrift`: the kernel frame `(G, Θ, V, Γ, Γ*, ν)` of the chart and `isStandardFrame_stdFrameNoDrift`;
* `rightOpNoDrift`: the type-2 operator with kernel `a(ξ)(b/c)(η) Γ(Θ(η, ξ))`, and `rightOpNoDrift_apply`:
  its action `∫ k(ξ, η) f(η) dη` is `LiftedChart.rightParametrixNoDrift`;
* `exists_small_balls_in_noDrift`: small lifted control balls `U_r ⊆ K₀ ⊆ V`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal NNReal Topology BigOperators
open RothschildStein.P1
namespace RothschildStein.P2

section Cutoffs

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : P1.LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m)

/-- **Cutoffs for the fixed right parametrix.** For `ξ₀ ∈ C.U` there is a patch `V ∋ ξ₀`
(an open ball) with closure in `C.U` and cutoffs `a, b ∈ C_c^∞(V)` with `a b = a` and `a = 1` near
`ξ₀` (the local solvability proof takes `a = 1` on a neighborhood of `ξ₀`). -/
theorem exists_frame_cutoffs_noDrift {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U) :
    ∃ (V : Opens (Fin (n + m) → ℝ)) (a b : TestFunction V ℝ (⊤ : ℕ∞)),
      ξ₀ ∈ (V : Set (Fin (n + m) → ℝ)) ∧ closure (V : Set (Fin (n + m) → ℝ)) ⊆ C.U ∧
        (∀ ξ, a ξ * b ξ = a ξ) ∧ ∀ᶠ ξ in 𝓝 ξ₀, a ξ = 1 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp C.isOpen_U ξ₀ hξ₀
  let V : Opens (Fin (n + m) → ℝ) := ⟨Metric.ball ξ₀ (ε / 2), Metric.isOpen_ball⟩
  have hcl : closure (V : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    (Metric.closure_ball_subset_closedBall.trans
      (Metric.closedBall_subset_ball (by linarith))).trans hball
  have hS : Metric.closedBall ξ₀ (ε / 4) ⊆ (V : Set (Fin (n + m) → ℝ)) :=
    Metric.closedBall_subset_ball (by linarith)
  obtain ⟨f, hf, hfT, W, hW, hSW, hf1⟩ := exists_cutoff_nhds (T := (V : Set (Fin (n + m) → ℝ)))
    V.isOpen (isCompact_closedBall ξ₀ (ε / 4)) hS
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset (isCompact_closedBall ξ₀ (ε / 2)) (isClosed_tsupport f)
      (hfT.trans Metric.ball_subset_closedBall)
  let a : TestFunction V ℝ (⊤ : ℕ∞) := ⟨f, hf, hfc, hfT⟩
  obtain ⟨b, hb⟩ := exists_cutoff_mul_eq V a
  refine ⟨V, a, b, Metric.mem_ball_self (by linarith), hcl, hb, ?_⟩
  filter_upwards [hW.mem_nhds (hSW (Metric.mem_closedBall_self (by linarith)))] with ξ hξ
  exact hf1 ξ hξ

/-- **Small lifted control balls inside a patch.** If `V ⊆ C.U` is open and `ξ₀ ∈ V`, there
are a compact `K₀ ⊆ V` and an admissible radius `r_*` (`IsSmallBallRadius K₀ ξ₀ r_*`); the lifted
control balls `B̃(ξ₀, r)`, `r < r_*`, are Euclidean open and lie in `K₀`. -/
theorem exists_small_balls_in_noDrift {V : Opens (Fin (n + m) → ℝ)} (hVU : (V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ (V : Set (Fin (n + m) → ℝ))) :
    ∃ (K₀ : Set (Fin (n + m) → ℝ)) (rstar : ℝ), IsCompact K₀ ∧
      K₀ ⊆ (V : Set (Fin (n + m) → ℝ)) ∧ C.IsSmallBallRadius K₀ ξ₀ rstar := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp V.isOpen ξ₀ hξ₀
  have hsub : Metric.closedBall ξ₀ (ε / 2) ⊆ (V : Set (Fin (n + m) → ℝ)) :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hint : ξ₀ ∈ interior (Metric.closedBall ξ₀ (ε / 2)) :=
    Metric.ball_subset_interior_closedBall (Metric.mem_ball_self (by linarith))
  obtain ⟨rstar, hr⟩ := P1.LiftedChart.exists_isSmallBallRadius (C := C)
    (isCompact_closedBall ξ₀ (ε / 2)) (hsub.trans hVU) hint
  exact ⟨_, rstar, isCompact_closedBall ξ₀ (ε / 2), hsub, hr⟩

end Cutoffs

section Frame

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : P1.LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m}
  {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
  (K : H1.FundamentalKernel C.G (C.noDriftModel hq ν₀))
  (hQ : 2 < (C.G.homogeneousDimension : ℝ))

variable (C) in
/-- The standard kernel frame on the patch `V`: model group and two-point map
of the chart, poles `Γ = K` and `Γ* = K ∘ inv`, the smooth symmetric gauge of the drift model. -/
abbrev stdFrameNoDrift (V : Opens (Fin (n + m) → ℝ)) : KernelFrame (n + m) where
  G := C.G
  Θ := C.Θ
  V := V
  Γ := K
  Γs := K.reflection hQ
  gauge := (C.noDriftModel hq ν₀).norm

/-- The frame `stdFrameNoDrift` is a standard frame, given the gauge hypotheses and
the H1 properties of the kernel. -/
theorem isStandardFrame_stdFrameNoDrift (V : Opens (Fin (n + m) → ℝ))
    (hV : closure (V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (hsymm : ∀ u, (C.noDriftModel hq ν₀).norm (-u) = (C.noDriftModel hq ν₀).norm u)
    (hsmooth : (C.noDriftModel hq ν₀).norm.Smooth) (hprops : H1.FundamentalKernelProperties K) :
    C.IsStandardFrame (stdFrameNoDrift C K hQ V) (C.noDriftModel hq ν₀) K hQ :=
  ⟨P1.LiftedChart.IsLiftedFrame.of_fundamentalKernels K (K.reflection hQ) rfl rfl hV rfl rfl,
    rfl, rfl, rfl, hsymm, hsmooth, hprops⟩

variable (C) in
/-- The right parametrix kernel `a(ξ) (b/c)(η) Γ(Θ(η, ξ))` vanishes for `η` outside the
support of `b`. -/
theorem rightParametrixKernelNoDrift_eq_zero_of_not_mem_tsupport (K' a b : (Fin (n + m) → ℝ) → ℝ)
    {ξ η : Fin (n + m) → ℝ} (hη : η ∉ tsupport b) : C.rightParametrixKernelNoDrift K' a b ξ η = 0 := by
  have : b η = 0 := image_eq_zero_of_notMem_tsupport hη
  simp [LiftedChart.rightParametrixKernelNoDrift, this]

/-- **The right parametrix is a type-2 operator** (`P_R` has type 2; a
single principal term `a(ξ) (b/c)(η) Γ(Θ(η, ξ))`, `D = id`, no regular remainder, no multiplier). -/
def rightOpNoDrift (V : Opens (Fin (n + m) → ℝ)) (hV : closure (V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (a b : TestFunction V ℝ (⊤ : ℕ∞)) : TypeOperator (stdFrameNoDrift C K hQ V) 2 where
  kernel := C.rightParametrixKernelNoDrift K a b
  isType :=
    (isTypeKernelOn_of_eq_principal (stdFrameNoDrift C K hQ V) (lam := 2) le_rfl a
      (divTest (stdFrameNoDrift C K hQ V) C.c (C.density_smooth.mono (subset_closure.trans hV))
        (fun ξ hξ => C.density_pos ξ (hV (subset_closure hξ))) b) false
      (C.rightParametrixKernelNoDrift K a b) (fun ξ η => by
        rw [divTest_apply]
        rfl)).isTypeKernel
  mult := 0
  mult_eq_zero := fun _ => by
    funext x
    simp

/-- The action of `rightOp` is `LiftedChart.rightParametrix`: at positive type the action
is the integral `∫ k(ξ, η) f(η) dη`, and the kernel vanishes off the support of `b ⊆ V ⊆ C.U`. -/
theorem rightOpNoDrift_apply (V : Opens (Fin (n + m) → ℝ)) (hV : closure (V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (a b : TestFunction V ℝ (⊤ : ℕ∞)) (f : (Fin (n + m) → ℝ) → ℝ) :
    (rightOpNoDrift K hQ V hV a b).apply f = C.rightParametrixNoDrift K a b f := by
  funext ξ
  rw [TypeOperator.apply_eq_integral (by norm_num) _ f]
  rw [LiftedChart.rightParametrix_eq_integral_noDrift]
  symm
  refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun η hη => ?_)
  have hη' : η ∉ tsupport (b : (Fin (n + m) → ℝ) → ℝ) :=
    fun h => hη (hV (subset_closure (b.tsupport_subset h)))
  have := rightParametrixKernelNoDrift_eq_zero_of_not_mem_tsupport C K a b (ξ := ξ) hη'
  simp [this]

end Frame

end RothschildStein.P2
