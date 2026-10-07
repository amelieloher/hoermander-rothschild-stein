-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SmoothingNoDriftEquation
public import RothschildStein.P2.SmoothingSolve
public import RothschildStein.P2.SmoothingChart

/-!
# Lift, solve and subtract without drift (chart level, under a `LocalSolvabilityNoDrift` hypothesis)

For a lifted no-drift chart `C` (alphabet `Fin q`, weights one, `L = ∑ Xᵢ²`) and `T ∈ 𝒟'(Ω)` with
`L T = f` (`hasDistributionEquation`):

* `solve_subtract_sobolev_noDrift_of_localSolvability` (`f ∈ L^p(Ω)`, `1 < p < ∞`): near every
  `ξ₀ ∈ U` the lift `T̃ = T ∘ J` is represented on a small lifted ball by `w = v + H ∈ W^{2,p}_{X̃,loc}`;
* `solve_subtract_holder_noDrift_of_localSolvability` (`f ∈ C^α_X(Ω)`, `0 < α < 1`): the same
  with a continuous `w ∈ C^{2,α}_{X̃,loc}`.

`v` is the particular solution of `LocalSolvabilityNoDrift` (`f̃ = f ∘ π` lies in the lifted data space
by the fiber bound, resp. the forward Hölder transfer), `H = T̃ - v` solves `L̃ H = 0` and is smooth by the homogeneous
hypoellipticity statement (the lifted fields are free and satisfy the rank condition),
and `H` has finite `W^{2,p}` / `C^{2,α}_{X̃}` norms on relatively compact balls (smooth functions, using the `(HD)` property of the lifted control
distance). The geometry of small lifted balls and the smooth-part lemmas are the alphabet-generic
ones of `SmoothingSolveSmooth`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators Distributions
open RothschildStein.P1
namespace RothschildStein.P2

section SolveSubtractNoDrift

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : P1.LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m)

/-- The no-drift weights are at most two. -/
theorem noDriftWeight_coe_le_two : ∀ i : Fin q, ((noDriftWeight i : ℕ+) : ℕ) ≤ 2 := by
  intro i
  simp [noDriftWeight]

/-- The intrinsic no-drift equation for a member of `C^{2,α}_{X̃}(U)` is the weak no-drift equation
(BB Prop 2.22: continuous intrinsic derivatives are the weak ones). -/
theorem weakNoDriftEquation_of_intrinsic {α : ℝ} (hα : 0 < α) {U : Opens (Fin (n + m) → ℝ)}
    (hUC : (U : Set (Fin (n + m) → ℝ)) ⊆ C.U) {v g : (Fin (n + m) → ℝ) → ℝ}
    (hv : memHolderX noDriftWeight C.Xl C.dl U 2 α v)
    (heq : intrinsicNoDriftEquation U C.Xl v g) : weakNoDriftEquation U C.Xl v g := by
  obtain ⟨jet, -, hjet⟩ := exists_jets_of_memHolderX C hα hUC hv
  obtain ⟨gs, hs, hsum⟩ := heq
  have ms : ∀ i : Fin q, ([i, i] : List (Fin q)) ∈ wordFamily noDriftWeight 2 := by
    intro i
    rw [RothschildStein.S.mem_wordFamily_iff]
    simp [wordWeight, noDriftWeight]
  refine ⟨gs, fun i => ?_, ae_restrict_of_forall_mem U.isOpen.measurableSet hsum⟩
  exact hasWeakWordDeriv_congr_eqOn C.Xl U (hjet [i, i] (ms i)).2.1
    (RothschildStein.S.hasIntrinsicWordDeriv_unique U C.Xl [i, i] (hjet [i, i] (ms i)).1 (hs i))

/-- **Lift, solve, subtract (Sobolev case), no drift, under a `LocalSolvabilityNoDrift` hypothesis.** In a lifted no-drift chart `C`, let `T ∈ 𝒟'(Ω)` with `L T = f`, `L = ∑ Xᵢ²`, and
`f ∈ L^p(Ω)`, `1 < p < ∞`. For every `ξ₀ ∈ U` there is a Euclidean open ball `UR = B̃(ξ₀, R)`, `R`
small, and a function `w` with `T̃|_{UR} = w` (the lift `T̃ = T ∘ J` restricted to `UR`) such that
`w ∈ W^{2,p}_{X̃}` on every `V` with compact closure in `UR` (`memSobolevXLoc`).

Proof: `f̃ = f ∘ π ∈ L^p(UR)` (fiber bound of the lifted norm transfer); `L̃ T̃ = f̃` (adjoint intertwining); local solvability
(`LocalSolvabilityNoDrift`) gives `v ∈ W^{2,p}(UR)` with `L̃ v = f̃` a.e.; `H = T̃ - v` solves `L̃ H = 0`
so is smooth (the homogeneous hypoellipticity statement; the lifted fields are free, so they satisfy the rank condition); on compact subsets of `UR` the
smooth `H` has finite `W^{2,p}` norms and `T̃ = v + H` (BB pp. 609-610). -/
theorem solve_subtract_sobolev_noDrift_of_localSolvability (hP : LocalSolvabilityNoDrift C)
    {p : ℝ≥0∞} (hp : 1 < p) (hpt : p < ⊤)
    (T : Distribution (liftedChartBaseOpens C) ℝ (⊤ : ℕ∞))
    {f : (Fin n → ℝ) → ℝ} (hf : MemLp f p (volume.restrict Ω))
    (hT : hasDistributionEquation (liftedChartBaseOpens C) X (liftedChart_contDiffOn_base C) T f)
    {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U) :
    ∃ UR : Opens (Fin (n + m) → ℝ), ξ₀ ∈ (UR : Set (Fin (n + m) → ℝ)) ∧
      (UR : Set (Fin (n + m) → ℝ)) ⊆ C.U ∧
      ∃ w : (Fin (n + m) → ℝ) → ℝ,
        LocallyIntegrableOn w (UR : Set (Fin (n + m) → ℝ)) volume ∧
        RothschildStein.S.distributionRestrictionCLM (liftedChartOpens C) UR (liftedChartLift C T) =
          Distribution.ofFun UR w volume (⊤ : ℕ∞) ∧
        memSobolevXLoc noDriftWeight C.Xl UR 2 p w := by
  obtain ⟨K₀, rstar, hK₀, hK₀U, hr⟩ := exists_isSmallBallRadius_of_mem C hξ₀
  obtain ⟨R₀, hR₀, hsol⟩ := (hP ξ₀ hξ₀).1 p hp hpt
  have hR0 : 0 < min (R₀ / 2) (rstar / 2) := lt_min (by linarith) (by linarith [hr.pos])
  have hRR₀ : min (R₀ / 2) (rstar / 2) < R₀ := (min_le_left _ _).trans_lt (by linarith)
  have hRrs : min (R₀ / 2) (rstar / 2) < rstar :=
    (min_le_right _ _).trans_lt (by linarith [hr.pos])
  set R := min (R₀ / 2) (rstar / 2) with hRdef
  let UR : Opens (Fin (n + m) → ℝ) :=
    ⟨C.noDriftBall ξ₀ R, isOpen_rsBall_of_isSmallBallRadius C hr hR0 hRrs⟩
  have hUR_U : (UR : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    fun y hy => hr.subset_U (hr.ball_subset R hR0 hRrs hy)
  have hg : MemLp (fun ξ => f (basePoint ξ)) p (volume.restrict (UR : Set (Fin (n + m) → ℝ))) :=
    memLp_comp_basePoint_of_subset C UR.isOpen.measurableSet hUR_U hp.le hpt.ne hf
  obtain ⟨v, hv, hveq⟩ := hsol R hR0 hRR₀ UR rfl _ hg
  have hX_UR : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (UR : Set (Fin (n + m) → ℝ)) :=
    fun i => (liftedChart_contDiffOn_lift C i).mono hUR_U
  have hTR := hasDistributionEquation_restrict_noDrift (liftedChartOpens C) UR hUR_U C.Xl
    (liftedChart_contDiffOn_lift C) (liftedChart_hasDistributionEquation_lift C hT)
  have hspan : bracketSpansOn (UR : Set (Fin (n + m) → ℝ)) C.Xl :=
    bracketSpansOn_of_stepSpansAt (fun x hx => (C.lift_free x (hUR_U hx)).2)
  have hvloc : LocallyIntegrableOn v (UR : Set (Fin (n + m) → ℝ)) volume := by
    obtain ⟨g₀, hg₀, -⟩ := hv.2 [] (RothschildStein.S.nil_mem_wordFamily noDriftWeight 2)
    exact hg₀.1
  obtain ⟨h, hh, hrep⟩ := exists_smooth_add_of_hasDistributionEquation_noDrift UR C.Xl hX_UR hspan
    _ hTR hvloc hveq Filter.EventuallyEq.rfl
  refine ⟨UR, mem_rsBall_self C (holderTransfer_U_subset_O C hξ₀) hR0, hUR_U,
    fun x => v x + h x, ?_, hrep, memSobolevXLoc_add_smooth noDriftWeight C.Xl UR hX_UR hv hh⟩
  exact hvloc.add (hh.continuousOn.locallyIntegrableOn UR.isOpen.measurableSet)

/-- **Lift, solve, subtract (Hölder case), no drift, under a `LocalSolvabilityNoDrift` hypothesis.** In a lifted no-drift chart `C`, let `T ∈ 𝒟'(Ω)` with `L T = f`, `L = ∑ Xᵢ²`, and
`f ∈ C^α_X(Ω)`, `0 < α < 1`. For every `ξ₀ ∈ U` there is a Euclidean open ball
`UR' = B̃(ξ₀, R/2)`, `R` small, and a continuous function `w` with `T̃|_{UR'} = w` such that
`w ∈ C^{2,α}_{X̃}` on every `V` with compact closure in `UR'` (`memHolderXLoc`).

Proof: `f̃ = f ∘ π ∈ C^α_{X̃}(UR)` (forward Hölder transfer); `L̃ T̃ = f̃`; local solvability
(`LocalSolvabilityNoDrift`) gives `v ∈ C^{2,α}_{X̃}(UR')` with `L̃ v = f̃` there, hence weakly (BB Prop 2.22);
`H = T̃ - v` is smooth (the homogeneous hypoellipticity statement), has finite intrinsic derivatives and `C^α_{X̃}` norms on
every relatively compact `V ⋐ UR'` (with the HD3 comparison of the lifted chart)
and `T̃ = v + H` (BB pp. 609-610). -/
theorem solve_subtract_holder_noDrift_of_localSolvability (hP : LocalSolvabilityNoDrift C)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (T : Distribution (liftedChartBaseOpens C) ℝ (⊤ : ℕ∞)) {f : (Fin n → ℝ) → ℝ}
    (hf : memHolderX noDriftWeight X (controlDistance Ω noDriftWeight X) (liftedChartBaseOpens C) 0 α f)
    (hT : hasDistributionEquation (liftedChartBaseOpens C) X (liftedChart_contDiffOn_base C) T f)
    {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U) :
    ∃ UR : Opens (Fin (n + m) → ℝ), ξ₀ ∈ (UR : Set (Fin (n + m) → ℝ)) ∧
      (UR : Set (Fin (n + m) → ℝ)) ⊆ C.U ∧
      ∃ w : (Fin (n + m) → ℝ) → ℝ, ContinuousOn w (UR : Set (Fin (n + m) → ℝ)) ∧
        RothschildStein.S.distributionRestrictionCLM (liftedChartOpens C) UR (liftedChartLift C T) =
          Distribution.ofFun UR w volume (⊤ : ℕ∞) ∧
        memHolderXLoc noDriftWeight C.Xl C.dl UR 2 α w := by
  obtain ⟨K₀, rstar, hK₀, hK₀U, hr⟩ := exists_isSmallBallRadius_of_mem C hξ₀
  obtain ⟨R₀, hR₀, hsol⟩ := (hP ξ₀ hξ₀).2 α hα hα1
  have hR0 : 0 < min (R₀ / 2) (rstar / 2) := lt_min (by linarith) (by linarith [hr.pos])
  have hRR₀ : min (R₀ / 2) (rstar / 2) < R₀ := (min_le_left _ _).trans_lt (by linarith)
  have hRrs : min (R₀ / 2) (rstar / 2) < rstar :=
    (min_le_right _ _).trans_lt (by linarith [hr.pos])
  set R := min (R₀ / 2) (rstar / 2) with hRdef
  have hRh0 : 0 < R / 2 := by linarith
  have hRhrs : R / 2 < rstar := by linarith
  let UR : Opens (Fin (n + m) → ℝ) :=
    ⟨C.noDriftBall ξ₀ R, isOpen_rsBall_of_isSmallBallRadius C hr hR0 hRrs⟩
  let UR' : Opens (Fin (n + m) → ℝ) :=
    ⟨C.noDriftBall ξ₀ (R / 2), isOpen_rsBall_of_isSmallBallRadius C hr hRh0 hRhrs⟩
  have hUR_U : (UR : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    fun y hy => hr.subset_U (hr.ball_subset R hR0 hRrs hy)
  have hUR'_U : (UR' : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    fun y hy => hr.subset_U (hr.ball_subset (R / 2) hRh0 hRhrs hy)
  have hUR_O : (UR : Set (Fin (n + m) → ℝ)) ⊆ C.O := hUR_U.trans (holderTransfer_U_subset_O C)
  have hproj : ∀ ξ ∈ (UR : Set (Fin (n + m) → ℝ)),
      basePoint ξ ∈ ((liftedChartBaseOpens C : Opens (Fin n → ℝ)) : Set (Fin n → ℝ)) :=
    fun ξ hξ => liftedChart_basePoint_mem C (hUR_U hξ)
  have hg : memHolderX noDriftWeight C.Xl C.dl UR 0 α (fun ξ => f (basePoint ξ)) :=
    memHolderX_comp_basePoint (P := C.P) Ω UR (liftedChartBaseOpens C) hproj
      (fun i => (C.lift_smooth i).mono hUR_O) hα.le 0 hf
  obtain ⟨v, hv, hveq⟩ := hsol R hR0 hRR₀ UR UR' rfl rfl _ hg
  have hX_UR' : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (UR' : Set (Fin (n + m) → ℝ)) :=
    fun i => (liftedChart_contDiffOn_lift C i).mono hUR'_U
  have hweak := weakNoDriftEquation_of_intrinsic C hα hUR'_U hv hveq
  have hTR := hasDistributionEquation_restrict_noDrift (liftedChartOpens C) UR' hUR'_U C.Xl
    (liftedChart_contDiffOn_lift C) (liftedChart_hasDistributionEquation_lift C hT)
  have hspan : bracketSpansOn (UR' : Set (Fin (n + m) → ℝ)) C.Xl :=
    bracketSpansOn_of_stepSpansAt (fun x hx => (C.lift_free x (hUR'_U hx)).2)
  obtain ⟨jet, hj0, hjet⟩ := exists_jets_of_memHolderX C hα hUR'_U hv
  have hvc : ContinuousOn v (UR' : Set (Fin (n + m) → ℝ)) := by
    have := (hjet [] (RothschildStein.S.nil_mem_wordFamily noDriftWeight 2)).2.2.1
    rwa [hj0] at this
  have hvloc : LocallyIntegrableOn v (UR' : Set (Fin (n + m) → ℝ)) volume :=
    hvc.locallyIntegrableOn UR'.isOpen.measurableSet
  obtain ⟨h, hh, hrep⟩ := exists_smooth_add_of_hasDistributionEquation_noDrift UR' C.Xl hX_UR'
    hspan _ hTR hvloc hweak Filter.EventuallyEq.rfl
  refine ⟨UR', mem_rsBall_self C (holderTransfer_U_subset_O C hξ₀) hRh0, hUR'_U,
    fun x => v x + h x, hvc.add hh.continuousOn, hrep, ?_⟩
  exact memHolderXLoc_add_smooth C noDriftWeight_coe_le_two hα hα1.le hUR'_U hv hh

end SolveSubtractNoDrift

end RothschildStein.P2
