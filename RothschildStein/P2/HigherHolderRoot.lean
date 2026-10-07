-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HigherHolderCover
public import RothschildStein.P2.LocalRegularityHypotheses
public import RothschildStein.P2.LocalRegularityCharts
public import RothschildStein.P2.SolvabilityFullNoDriftFrame
public import RothschildStein.P2.SobolevInterpolationNoDriftNhds
public import RothschildStein.P1.ParametrixStatementsAssembly
public import RothschildStein.H1.CompleteAssembly

/-!
# Higher Hölder regularity, no drift (BB Thms 11.59-11.60, (11.94)-(11.96), pp. 603-604)

`higherHolderRegularityNoDrift_of_hypotheses` proves the statement `HigherHolderRegularityNoDrift` of `LocalRegularityHypotheses` (the exact content
of the higher Hölder estimate on the original domain, `Ω' ⋐ Ω'' ⋐ Ω`) from

* the lifting theorem statement (no drift) `LiftApproximationNoDriftStatement` (the lifted charts at every point);
* the P1 statements for the standard no-drift frames: `HolderTypeCalculusAllChartsNoDrift` (row integrability `TypeKernelIntegrable`,
  differentiation `LeftDifferentiation`, `RightDifferentiation`, transfer `DerivativeTransfer`) and `HolderSignedParametrixAllChartsNoDrift` (the signed parametrix
  `SignedParametrixNoDrift`);
* the lifted base Hölder estimate without drift, `LiftedBaseHolderAllChartsNoDrift` (`LiftedBaseHolderEstimate`
  at the smooth homogeneous norm of every no-drift chart);
* the original local doubling, `LocalDoublingAllChartsNoDrift`.

*Proof.* At every point `x` of `closure Ω'` a lifted chart (the lifting theorem), an H1 kernel `K`, a standard frame and the
cutoff `a` give `HolderFrame`; `liftedHigherHolder_of_base` (compact recurrence with regularity, cutoff step,
ladder of radii, base estimate) gives the lifted higher estimate; `higher_holder_local_transfer` (forward lift
of derivatives, descent of the regularity as in the distributional smoothing theorem, and the reverse
Hölder transfer under local doubling) gives the local statement on
small base balls; `higher_holder_finite_cover` (gluing of intrinsic derivatives, Lebesgue number) finishes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators
open RothschildStein.P1
namespace RothschildStein.P2

/-- The P1 type-calculus statements for every standard frame of every lifted no-drift chart
over a system with `3 ≤ n` and `0 < q`, with every H1 fundamental kernel `K` of the no-drift model of the chart at
the smooth homogeneous norm of the chart group: `TypeKernelIntegrable` (BB p. 544), `LeftDifferentiation`, `RightDifferentiation` (BB
pp. 546-551) and `DerivativeTransfer` (for the model bracket basis `C.B`; BB pp. 552-559). -/
def HolderTypeCalculusAllChartsNoDrift : Prop :=
  ∀ {n q s m : ℕ} (hn : 3 ≤ n) (hq : 0 < q) {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (C : P1.LiftedChart noDriftWeight s Ω hΩ X x₀ m)
    (K : H1.FundamentalKernel C.G (C.noDriftModel hq (G2.smoothNorm C.G)))
    (F : KernelFrame (n + m))
    (hF : C.IsStandardFrame F (C.noDriftModel hq (G2.smoothNorm C.G)) K
      (C.two_lt_homogeneousDimension hn)),
    TypeKernelIntegrable F ∧ LeftDifferentiation F noDriftWeight C.Xl ∧
      RightDifferentiation F noDriftWeight C.Xl hF.lifted.contDiffOn_Xl ∧ DerivativeTransfer F noDriftWeight C.Xl C.B

/-- The operator-level statement `SignedParametrixNoDrift` of the signed parametrix (BB pp. 561-563) for every
standard frame of every lifted no-drift chart over a system with `3 ≤ n` and `0 < q`, every H1 fundamental kernel
of the no-drift model of the chart at the smooth homogeneous norm of the chart group, and all cutoffs
`a, b ∈ C_c^∞(F.V)`, with the density `C.c` of the chart. -/
def HolderSignedParametrixAllChartsNoDrift : Prop :=
  ∀ {n q s m : ℕ} (hn : 3 ≤ n) (hq : 0 < q) {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (C : P1.LiftedChart noDriftWeight s Ω hΩ X x₀ m)
    (K : H1.FundamentalKernel C.G (C.noDriftModel hq (G2.smoothNorm C.G)))
    (F : KernelFrame (n + m))
    (_hF : C.IsStandardFrame F (C.noDriftModel hq (G2.smoothNorm C.G)) K
      (C.two_lt_homogeneousDimension hn))
    (a b : TestFunction F.V ℝ (⊤ : ℕ∞)), SignedParametrixNoDrift F C.Xl C.c a b

/-- The lifted base Hölder estimate without drift (BB pp. 600-602, Thms 11.57-11.58, (11.92)-(11.93)): for
every lifted no-drift chart over a system with `3 ≤ n`, `0 < q` and every `0 < α < 1`,
`LiftedBaseHolderEstimate` at the smooth homogeneous norm of the chart group. -/
def LiftedBaseHolderAllChartsNoDrift : Prop :=
  ∀ {n q s m : ℕ}, 3 ≤ n → 0 < q → ∀ {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (C : P1.LiftedChart noDriftWeight s Ω hΩ X x₀ m) {α : ℝ}, 0 < α → α < 1 →
    LiftedBaseHolderEstimate C (G2.smoothNorm C.G) (noDriftOpWords q) α

open RothschildStein.P2.HigherHolder

/-- **The local statement at a point** (the hypotheses of `higher_holder_finite_cover` at `x`): from the lifting theorem,
the P1 statements, the lifted base estimate and the doubling. -/
theorem higher_holder_local_at_point (liftApproximation : LiftApproximationNoDriftStatement) (hP : HolderTypeCalculusAllChartsNoDrift)
    (hParametrix : HolderSignedParametrixAllChartsNoDrift) (hbase : LiftedBaseHolderAllChartsNoDrift) (hdbl : LocalDoublingAllChartsNoDrift)
    {n q : ℕ} (hn : 3 ≤ n) (Ω : Opens (Fin n → ℝ)) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hspan : bracketSpansOn (Ω : Set (Fin n → ℝ)) X) {k : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {x : Fin n → ℝ} (hx : x ∈ (Ω : Set (Fin n → ℝ))) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ b K : ℝ, 0 < ρ ∧ ρ ≤ b ∧ b ≤ ε ∧ 0 < K ∧
      (∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ b → IsOpen (rsBall (Ω : Set (Fin n → ℝ)) noDriftWeight X x ρ')) ∧
      ∀ (Vρ Vb : Opens (Fin n → ℝ)),
        (Vρ : Set (Fin n → ℝ)) = rsBall (Ω : Set (Fin n → ℝ)) noDriftWeight X x ρ →
        (Vb : Set (Fin n → ℝ)) = rsBall (Ω : Set (Fin n → ℝ)) noDriftWeight X x b → ∀ u f : (Fin n → ℝ) → ℝ,
        memHolderX noDriftWeight X (controlDistance (Ω : Set (Fin n → ℝ)) noDriftWeight X) Vb 2 α u →
        HasIntrinsicOperatorValue X Vb (noDriftOpWords q) u f →
        memHolderX noDriftWeight X (controlDistance (Ω : Set (Fin n → ℝ)) noDriftWeight X) Vb k α f →
        memHolderX noDriftWeight X (controlDistance (Ω : Set (Fin n → ℝ)) noDriftWeight X) Vρ (k + 2) α u ∧
        holderXENorm noDriftWeight X (controlDistance (Ω : Set (Fin n → ℝ)) noDriftWeight X) Vρ (k + 2) α u ≤
          ENNReal.ofReal K * (holderXENorm noDriftWeight X
              (controlDistance (Ω : Set (Fin n → ℝ)) noDriftWeight X) Vb k α f +
            eLpNorm u ⊤ (volume.restrict (Vb : Set (Fin n → ℝ)))) := by
  classical
  -- a generator exists: the bracket span is the whole space at `x`
  have hq : 0 < q := by
    by_contra hq0
    have hq00 : q = 0 := by omega
    subst hq00
    have hx' := hspan x hx
    have hempty : {v : Fin n → ℝ | ∃ I : List (Fin 0), I ≠ [] ∧ v = wordBracket X I x} = ∅ := by
      ext v
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨I, hI, -⟩
      cases I with
      | nil => exact hI rfl
      | cons a _ => exact a.elim0
    rw [hempty, Submodule.span_empty] at hx'
    have h1 : (Pi.single (⟨0, by omega⟩ : Fin n) (1 : ℝ) : Fin n → ℝ) ∈ (⊤ : Submodule ℝ (Fin n → ℝ)) :=
      Submodule.mem_top
    rw [← hx', Submodule.mem_bot] at h1
    have := congrFun h1 ⟨0, by omega⟩
    simp at this
  obtain ⟨s, m, ⟨C⟩⟩ := hchart_noDrift liftApproximation (by omega) hq Ω X hX hspan x hx
  have hQ := C.two_lt_homogeneousDimension hn
  obtain ⟨K⟩ := (C.noDriftModel hq (G2.smoothNorm C.G)).exists_globalFundamentalKernel C.G hQ
  have hprops : H1.FundamentalKernelProperties K := H1.assemble_kernel K hQ
  have hsymm : ∀ u, (C.noDriftModel hq (G2.smoothNorm C.G)).norm (-u) =
      (C.noDriftModel hq (G2.smoothNorm C.G)).norm u := fun u => by
    have hu := C.smoothNorm_symmetric u
    rwa [show C.G.inv u = -u from C.inv_eq_neg u] at hu
  have hsmooth : (C.noDriftModel hq (G2.smoothNorm C.G)).norm.Smooth := G2.smoothNorm_smooth C.G
  obtain ⟨V, a, b₀, hξV, hVcl, hab, ha1⟩ := exists_frame_cutoffs_noDrift C C.center_mem
  have hF := isStandardFrame_stdFrameNoDrift K hQ V hVcl hsymm hsmooth hprops
  obtain ⟨hRowInt, hLeftDiff, hRightDiff, hTransfer⟩ := hP hn hq C K _ hF
  have hH : HolderFrame C (C.noDriftModel hq (G2.smoothNorm C.G)) K hQ (stdFrameNoDrift C K hQ V) a :=
    ⟨hF, fun j => noDriftWeight_coe_eq_one j, hRowInt, hLeftDiff, hRightDiff, hTransfer, fun b' => hParametrix hn hq C K _ hF a b'⟩
  have ha : ∀ᶠ ξ in 𝓝 (joinPoint x (0 : Fin m → ℝ)), ξ ∈ ((stdFrameNoDrift C K hQ V).V :
      Set (Fin (n + m) → ℝ)) ∧ a ξ = 1 := by
    filter_upwards [V.isOpen.mem_nhds hξV, ha1] with ξ h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨R, hR0, hsubR⟩ := exists_rhoBall_subset_of_mem_nhds_noDrift C (G2.smoothNorm C.G)
    C.center_mem ha
  have hRV : rhoBall C (G2.smoothNorm C.G) (joinPoint x (0 : Fin m → ℝ)) R ⊆
      ((stdFrameNoDrift C K hQ V).V : Set (Fin (n + m) → ℝ)) := fun ξ hξ => (hsubR R le_rfl hξ).1
  have hRa : ∀ ξ ∈ rhoBall C (G2.smoothNorm C.G) (joinPoint x (0 : Fin m → ℝ)) R, a ξ = 1 :=
    fun ξ hξ => (hsubR R le_rfl hξ).2
  have hest := liftedHigherHolder_of_base hH (G2.smoothNorm C.G) (G2.smoothNorm_smooth C.G) hα0 hα1 k hR0
    hRV hRa (hbase hn hq C hα0 hα1)
  exact higher_holder_local_transfer C (G2.smoothNorm C.G) hα0 hα1 (hdbl hn hX hspan C) hest hε

end RothschildStein.P2

namespace RothschildStein.P2

open RothschildStein.P2.HigherHolder

/-- **Higher Hölder regularity, no drift** (BB pp. 603-604, Thms 11.59-11.60, (11.94)-(11.96)): the exact
statement `HigherHolderRegularityNoDrift`, assuming the lifting theorem, the P1 statements for the standard frames
(`HolderTypeCalculusAllChartsNoDrift`, `HolderSignedParametrixAllChartsNoDrift`), the lifted base Hölder estimate
(`LiftedBaseHolderAllChartsNoDrift`) and the local doubling (`LocalDoublingAllChartsNoDrift`). -/
theorem higherHolderRegularityNoDrift_of_hypotheses (liftApproximation : LiftApproximationNoDriftStatement) (hP : HolderTypeCalculusAllChartsNoDrift)
    (hParametrix : HolderSignedParametrixAllChartsNoDrift) (hbase : LiftedBaseHolderAllChartsNoDrift) (hdbl : LocalDoublingAllChartsNoDrift) :
    HigherHolderRegularityNoDrift := by
  intro n q hn Ω Ω' Ω'' X hX hspan hcpt' hΩ'Ω'' hcpt'' hΩ''Ω k α hα0 hα1
  have hΩ''sub : (Ω'' : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) :=
    subset_closure.trans hΩ''Ω
  exact higher_holder_finite_cover (X := X) Ω.isOpen hX hα0 Ω' Ω'' hcpt' hΩ'Ω'' hΩ''sub
    (fun x hx ε hε => higher_holder_local_at_point liftApproximation hP hParametrix hbase hdbl hn Ω X hX hspan hα0 hα1
      (hΩ''sub (hΩ'Ω'' hx)) hε)

end RothschildStein.P2
