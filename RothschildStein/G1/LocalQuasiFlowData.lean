-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G3.UniformQuasiPointError
public import RothschildStein.G1.JetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.G1
open G3

/-- Local genuine flow data consumed by the actual bracket
chart. All point maps are finite primitive schedules of the same Φ. -/
structure LocalQuasiFlowData {a s n : ℕ} {p : Fin a → ℕ+}
    (Ω : Set (Fin n → ℝ)) (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (D : FreeModelData a s p) (z : Fin n → ℝ) where
  U : Set (Fin n → ℝ)
  V : Set (Fin n → ℝ)
  open_U : IsOpen U
  open_V : IsOpen V
  center : z ∈ U
  U_subset_V : U ⊆ V
  V_subset_Ω : V ⊆ Ω
  σ : ℝ
  κ : ℝ
  η : ℝ
  M : ℝ
  σ_pos : 0 < σ
  κ_pos : 0 < κ
  η_pos : 0 < η
  M_pos : 0 < M
  Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ)
  smooth_Φ : ContDiffOn ℝ (⊤ : ℕ∞) Φ ((ball 0 σ ×ˢ V) ×ˢ Ioo (-2 : ℝ) 2)
  ode_Φ : ∀ f : formalSpan a s p, D.basis.equivFun f ∈ ball 0 σ → ∀ x ∈ V,
    Φ ((D.basis.equivFun f, x), 0) = x ∧ ∀ t ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (fun v => Φ ((D.basis.equivFun f, x), v))
        (finiteLieField D X f (Φ ((D.basis.equivFun f, x), t))) t ∧
      Φ ((D.basis.equivFun f, x), t) ∈ Ω
  smooth_primitive : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (primitiveFlowFromLieFamily D Φ κ i)
    (V ×ˢ Ioo (-κ) κ)
  ode_primitive : ∀ i x, x ∈ V → primitiveFlowFromLieFamily D Φ κ i (x, 0) = x ∧
    ∀ t ∈ Ioo (-κ) κ,
      HasDerivAt (fun v => primitiveFlowFromLieFamily D Φ κ i (x, v))
        (X i (primitiveFlowFromLieFamily D Φ κ i (x, t))) t ∧
      primitiveFlowFromLieFamily D Φ κ i (x, t) ∈ Ω
  smooth_points : ∀ I : List (Fin a), I ≠ [] → wordWeight p I ≤ s →
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (Fin n → ℝ) × ℝ => quasiExponentialPointMap p (primitiveFlowFromLieFamily D Φ κ) I q.2 q.1)
      (U ×ˢ Ioo (-η) η) ∧
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (Fin n → ℝ) × ℝ => inverseQuasiExponentialPointMap p (primitiveFlowFromLieFamily D Φ κ) I q.2 q.1)
      (U ×ˢ Ioo (-η) η)
  admissible : ∀ I : List (Fin a), I ≠ [] → wordWeight p I ≤ s → ∀ x ∈ U,
    ∀ t ∈ Ioo (-η) η,
      FlowScheduleAdmissible (primitiveFlowFromLieFamily D Φ κ) (fun i t => t ^ (p i : ℕ))
        (fun _ => V) (fun _ => κ) t (commutatorSchedule I) x ∧
      FlowScheduleAdmissible (primitiveFlowFromLieFamily D Φ κ) (fun i t => t ^ (p i : ℕ))
        (fun _ => V) (fun _ => κ) t (inverseSchedule (commutatorSchedule I)) x
  point_error : ∀ I : List (Fin a), I ≠ [] → wordWeight p I ≤ s → ∀ x ∈ U,
    ∀ t ∈ Ioo (-η) η,
      ‖quasiExponentialPointMap p (primitiveFlowFromLieFamily D Φ κ) I t x -
        Φ ((dilatedInputCoordinates D (quasiExponentialLog I) t, x), 1)‖ ≤ M * |t| ^ (s + 1) ∧
      ‖inverseQuasiExponentialPointMap p (primitiveFlowFromLieFamily D Φ κ) I t x -
        Φ ((dilatedInputCoordinates D (-(quasiExponentialLog I : formalSpan a s p)) t, x), 1)‖ ≤
          M * |t| ^ (s + 1)

/-- Smooth coefficients give actual local quasi-flow data;
finite jet bounds are derived on a compact buffer, not assumed. -/
theorem exists_local_quasi_flow_data {a s n : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (hs : 1 ≤ s) (hw : ∀ i, (p i : ℕ) ≤ s)
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (z : Fin n → ℝ) (hz : z ∈ Ω) : Nonempty (LocalQuasiFlowData Ω X D z) := by
  obtain ⟨ε, hε, hεΩ⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hz)
  let r : ℝ := ε / 8
  have hr : 0 < r := by dsimp [r]; positivity
  let K := closedBall z r
  have hcompactΩ : closedBall z (2 * r) ⊆ Ω :=
    (closedBall_subset_ball (by dsimp [r]; linarith)).trans hεΩ
  have hbuffer : (centreBuffer K r : Set (Fin n → ℝ)) ⊆ closedBall z (2 * r) := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := mem_centreBuffer_iff.mp hy
    change dist y z ≤ 2 * r
    exact ((dist_triangle y x z).trans (add_le_add (mem_ball.mp hyx).le (mem_closedBall.mp hx))).trans
      (by ring_nf; exact le_rfl)
  obtain ⟨B, hB, hjet⟩ := exists_uniform_coefficient_jet_bound hΩ
    (isCompact_closedBall z (2 * r)) hcompactΩ X hX (3 * s + 2)
  obtain ⟨η, M, κ, σ, hη, _hη1, hM, hκ, hσ, hflow⟩ :=
    exists_uniform_quasiExponentialPoint_error (N := n) D hs hw hr hB.le
  have hbufΩ := hbuffer.trans hcompactΩ
  obtain ⟨Φ, hΦ, hODE, hΨ, hΨODE, hpoints⟩ := hflow K X
    (fun i => (hX i).mono hbufΩ) (fun x hx i j hj => by
      have hh := hjet i j hj x (hbuffer hx)
      rwa [iteratedFDerivWithin_of_isOpen j hΩ (hbufΩ hx)] at hh)
  let U := ball z r
  let V : Set (Fin n → ℝ) := centreBuffer K (r / 2)
  have hUK : U ⊆ K := ball_subset_closedBall
  have hKV : K ⊆ V := fun x hx => mem_centreBuffer_iff.mpr ⟨x, hx, mem_ball_self (by positivity)⟩
  have hVU : V ⊆ Ω := fun x hx => hbufΩ (by
    obtain ⟨y, hy, hxy⟩ := mem_centreBuffer_iff.mp hx
    exact mem_centreBuffer_iff.mpr ⟨y, hy, (ball_subset_ball (by linarith : r / 2 ≤ r)) hxy⟩)
  refine ⟨{
    U := U, V := V, open_U := isOpen_ball, open_V := (centreBuffer K (r / 2)).isOpen,
    center := mem_ball_self hr, U_subset_V := hUK.trans hKV, V_subset_Ω := hVU,
    σ := σ, κ := κ, η := η, M := M, σ_pos := hσ, κ_pos := hκ, η_pos := hη, M_pos := hM,
    Φ := Φ, smooth_Φ := hΦ,
    ode_Φ := ?_, smooth_primitive := hΨ, ode_primitive := ?_,
    smooth_points := ?_, admissible := ?_, point_error := ?_ }⟩
  · intro f hf x hx
    obtain ⟨hinit, hd⟩ := hODE f hf x hx
    exact ⟨hinit, fun t ht => ⟨(hd t ht).2, hbufΩ (hd t ht).1⟩⟩
  · intro i x hx
    obtain ⟨hinit, hd⟩ := hΨODE i x hx
    exact ⟨hinit, fun t ht => ⟨(hd t ht).2, hbufΩ (hd t ht).1⟩⟩
  · intro I hne hI
    constructor <;> intro q hq
    · have hh := (hpoints I hne hI q.1 (hUK hq.1) q.2 (abs_lt.mpr hq.2)).2.2.1
      exact (hh.comp q (contDiffAt_snd.prodMk contDiffAt_fst)).contDiffWithinAt
    · have hh := (hpoints I hne hI q.1 (hUK hq.1) q.2 (abs_lt.mpr hq.2)).2.2.2.1
      exact (hh.comp q (contDiffAt_snd.prodMk contDiffAt_fst)).contDiffWithinAt
  · intro I hne hI x hx t ht
    have hh := hpoints I hne hI x (hUK hx) t (abs_lt.mpr ht)
    exact ⟨hh.1, hh.2.1⟩
  · intro I hne hI x hx t ht
    have hh := hpoints I hne hI x (hUK hx) t (abs_lt.mpr ht)
    exact hh.2.2.2.2.2.2.2.2

end RothschildStein.G1
