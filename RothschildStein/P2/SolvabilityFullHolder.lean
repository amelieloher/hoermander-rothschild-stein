-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SolvabilityFullSobolev
public import RothschildStein.P2.SolvabilityFullTail
public import RothschildStein.P2.SmoothingSolve
public import RothschildStein.P2.ProductAbsorptionExit
public import RothschildStein.P2.TransferCoverHolderCover
public import RothschildStein.P1.GainHolder
public import RothschildStein.S.HolderProducts

/-!
# Local solvability, Hölder half: `v = P_R E_R f ∈ C^{2,α}(U_{R/2})` with `L̃ v = g` there

For `g ∈ C^α_{X̃}(U_R)` the distributional solution of `exists_holder_solution` is
`v = P_R E_R f`, with `f ∈ C^α(U_R)`, and `E_R f` is only in `L^p`. As in the proof of local
solvability, split `E_R f = χ f + (1 - χ) E_R f` with `χ ∈ C_c^∞(U_R)`, `χ = 1` near the closure of
`U_{R/2}`:

* `χ f` extends by zero to a function of finite `C^α(V)` norm on the fixed patch `V` (zero extension
  with a support margin `holderENorm_cutoff_product_eq`, product estimate, BB (2.20)–(2.21)), so `P_R(χ f)` is
  in `C^{2,α}(V)` by the Hölder gain theorem (under the `LeftDifferentiation` hypothesis);
* `P_R((1 - χ) E_R f)` is smooth near `U_{R/2}` (`SolvabilityFullTail`);
* `C^{2,α}` membership of the sum on `U_{R/2}` (`memHolderXLoc_add_smooth`), and `L̃ v = g` at every
  point of `U_{R/2}`: the weak equation holds a.e. (`SolvabilityFullWeak`), and both sides are continuous.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators Distributions
open RothschildStein.P1
namespace RothschildStein.P2

section Holder

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : P1.LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m}
  {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
  (K : H1.FundamentalKernel C.G (C.driftModel hq ν₀))
  (hQ : 2 < (C.G.homogeneousDimension : ℝ))

/-- **Hölder norm of the cutoff product.** If `f` has finite
`C^α(E)` norm on an open `E ⊆ V ⊆ C.U` and `χ` is smooth with `tsupport χ ⊆ E`, then
`f χ`, extended by zero, has finite `C^α(V)` norm. -/
theorem holderENorm_cutoff_mul_ne_top {E V : Set (Fin (n + m) → ℝ)} (hE : IsOpen E)
    (hEV : E ⊆ V) (hVU : V ⊆ C.U) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f χ : (Fin (n + m) → ℝ) → ℝ} (hf : holderENorm C.dl α E f < ⊤) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχE : tsupport χ ⊆ E) :
    holderENorm C.dl α V (fun x => f x * χ x) ≠ ⊤ := by
  have hw : ∀ i : Fin (q + 1), (driftWeight i : ℕ) ≤ 2 := driftWeight_coe_le_two
  have hEU : E ⊆ C.U := hEV.trans hVU
  have heq := holderENorm_cutoff_product_eq (Ω := C.O) (w := driftWeight) (X := C.Xl) hw hα f χ
    hχc hE hχE hEV (fun z hz => image_eq_zero_of_notMem_tsupport hz)
  have hsep : ∀ x ∈ E, ∀ y ∈ E, C.dl x y = 0 → x = y := fun x hx y _ h =>
    dl_eq_zero_imp_eq C (holderTransfer_U_subset_O C (hEU hx)) h
  have hχn : holderENorm C.dl α E χ < ⊤ :=
    lt_top_iff_ne_top.mpr (LiftedChart.holderENorm_ne_top_of_contDiff_compact hEU hχ hχc
      (hχE.trans hEU) hα hα1)
  have hm := RothschildStein.S.holderENorm_mul_le C.dl hα E hsep f χ hf hχn
  have heq' : holderENorm C.dl α V (fun x => f x * χ x) =
      holderENorm C.dl α E (fun x => f x * χ x) := heq
  rw [heq']
  exact (lt_of_le_of_lt hm (ENNReal.mul_lt_top hf hχn)).ne

/-- **Interior Hölder gain of the right parametrix.** Let `V` be a patch
with closure in `C.U`, `a, b ∈ C_c^∞(V)`, `E ⊆ V` open, `E'` open with compact closure inside `E`,
and `f` of finite `C^α(E)` norm. Then `v = P_R E_E f`, `E_E f = 1_E f` (the zero extension, which is
only `L^p`), is of class `C^{2,α}_{X̃}(E')` (`memHolderX`, order `2`), assuming `LeftDifferentiation`
for the standard frame of the patch (the Hölder gain theorem for `P_R(χ f)`), with `χ ∈ C_c^∞(E)`
equal to one near `closure E'`: `P_R(χ f)` is `C^{2,α}`, and `P_R((1 - χ) E_E f)` is smooth near `E'`
(`contDiffOn_tail_integral`), by separation from the support of the input. -/
theorem rightParametrix_holder_interior_gain
    (hsymm : ∀ u, (C.driftModel hq ν₀).norm (-u) = (C.driftModel hq ν₀).norm u)
    (hsmooth : (C.driftModel hq ν₀).norm.Smooth) (hprops : H1.FundamentalKernelProperties K)
    (hLeftDiff : LeftDifferentiationOnStandardFrames C K hQ) {V : Opens (Fin (n + m) → ℝ)}
    (hVcl : closure (V : Set (Fin (n + m) → ℝ)) ⊆ C.U) (a b : TestFunction V ℝ (⊤ : ℕ∞))
    {E : Set (Fin (n + m) → ℝ)} {E' : Opens (Fin (n + m) → ℝ)} (hEopen : IsOpen E)
    (hEV : E ⊆ (V : Set (Fin (n + m) → ℝ)))
    (hE'c : IsCompact (closure (E' : Set (Fin (n + m) → ℝ))))
    (hE'E : closure (E' : Set (Fin (n + m) → ℝ)) ⊆ E) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {f : (Fin (n + m) → ℝ) → ℝ} (hfn : holderENorm C.dl α E f < ⊤) :
    memHolderX driftWeight C.Xl C.dl E' 2 α (C.rightParametrix K a b (E.indicator f)) := by
  have hVU : (V : Set (Fin (n + m) → ℝ)) ⊆ C.U := subset_closure.trans hVcl
  have hF := isStandardFrame_stdFrame K hQ V hVcl hsymm hsmooth hprops
  have hLeftDiffF := hLeftDiff _ hF
  have hVle : V ≤ C.chartOpens := hVU
  let aC : TestFunction C.chartOpens ℝ (⊤ : ℕ∞) := LiftedChart.testOfLe V hVle a
  let bC : TestFunction C.chartOpens ℝ (⊤ : ℕ∞) := LiftedChart.testOfLe V hVle b
  have hEU : E ⊆ C.U := hEV.trans hVU
  -- the cutoff
  obtain ⟨χ, hχ, hχT, N, hN, hSN, hχ1⟩ := exists_cutoff_nhds hEopen hE'c hE'E
  have hχc : HasCompactSupport χ :=
    IsCompact.of_isClosed_subset hF.lifted.isCompact_closure (isClosed_tsupport χ)
      (hχT.trans (hEV.trans subset_closure))
  have hNE : N ⊆ E := fun x hx =>
    hχT (subset_tsupport _ (by rw [Function.mem_support, hχ1 x hx]; exact one_ne_zero))
  have hχ0 : ∀ x, x ∉ E → χ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hχT h))
  -- boundedness and measurability of the input `E_E f`
  have hfcont : ContinuousOn f E := LiftedChart.continuousOn_of_holderENorm_lt_top hEU hα hfn
  set Mf : ℝ := (holderENorm C.dl α E f).toReal with hMfdef
  have hMf0 : 0 ≤ Mf := ENNReal.toReal_nonneg
  have hMf : ∀ y ∈ E, |f y| ≤ Mf := fun y hy => abs_le_toReal_holderENorm hfn.ne hy
  set g' : (Fin (n + m) → ℝ) → ℝ := E.indicator f with hg'def
  have hg'bd : ∀ y, |g' y| ≤ Mf := by
    intro y
    by_cases hy : y ∈ E
    · rw [hg'def, Set.indicator_of_mem hy]
      exact hMf y hy
    · rw [hg'def, Set.indicator_of_notMem hy, abs_zero]
      exact hMf0
  have hg'meas : AEStronglyMeasurable g' (volume : Measure (Fin (n + m) → ℝ)) :=
    (aestronglyMeasurable_indicator_iff hEopen.measurableSet).2
      (hfcont.aestronglyMeasurable hEopen.measurableSet)
  have hfinE : volume E ≠ ⊤ :=
    ne_top_of_le_ne_top hF.lifted.volume_lt_top.ne (measure_mono hEV)
  have : IsFiniteMeasure (volume.restrict E) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hfinE⟩
  have hfint : IntegrableOn f E :=
    Integrable.of_bound (hfcont.aestronglyMeasurable hEopen.measurableSet) Mf
      (ae_restrict_of_forall_mem hEopen.measurableSet fun y hy => by
        rw [Real.norm_eq_abs]
        exact hMf y hy)
  have hg'int : Integrable g' volume := (integrable_indicator_iff hEopen.measurableSet).2 hfint
  -- the splitting `E_E f = u + w`
  obtain ⟨Bχ, hBχ⟩ := hχ.continuous.bounded_above_of_compact_support hχc
  have hBχ0 : 0 ≤ Bχ := (norm_nonneg _).trans (hBχ 0)
  let u : (Fin (n + m) → ℝ) → ℝ := fun x => f x * χ x
  let w : (Fin (n + m) → ℝ) → ℝ := fun x => (1 - χ x) * g' x
  have hsplit : ∀ x, g' x = u x + w x := by
    intro x
    by_cases hx : x ∈ E
    · simp only [hg'def, Set.indicator_of_mem hx, u, w]
      try ring
    · simp only [hg'def, Set.indicator_of_notMem hx, u, w, hχ0 x hx]
      try ring
  have hu_g' : ∀ x, u x = g' x * χ x := by
    intro x
    by_cases hx : x ∈ E
    · simp only [hg'def, Set.indicator_of_mem hx, u]
    · simp only [hg'def, Set.indicator_of_notMem hx, u, hχ0 x hx]
      try ring
  -- the type-2 operator and its patch kernel
  let Pop := rightOp K hQ V hVcl a b
  have hpatch := TypeOperator.patchKernel hF.lifted (by norm_num : 1 ≤ 2) Pop
  have hint : ∀ h : (Fin (n + m) → ℝ) → ℝ, AEStronglyMeasurable h (volume.restrict (V : Set _)) →
      ∀ M : ℝ, 0 ≤ M → (∀ y ∈ (V : Set (Fin (n + m) → ℝ)), |h y| ≤ M) → ∀ ξ,
        Integrable (fun η => C.rightParametrixKernel K a b ξ η * h η) :=
    fun h hm M hM0 hM ξ => hpatch.integrable_row hm hM0 hM ξ
  have hu_int : ∀ ξ, Integrable (fun η => C.rightParametrixKernel K a b ξ η * u η) := by
    refine hint u ?_ (Bχ * Mf) (mul_nonneg hBχ0 hMf0) (fun y _ => ?_)
    · have : AEStronglyMeasurable u (volume : Measure (Fin (n + m) → ℝ)) := by
        have h2 := hg'meas.mul hχ.continuous.aestronglyMeasurable
        exact h2.congr (Filter.Eventually.of_forall fun x => (hu_g' x).symm)
      exact this.restrict
    · rw [hu_g' y, abs_mul]
      calc |g' y| * |χ y| ≤ Mf * Bχ :=
            mul_le_mul (hg'bd y) (by simpa [Real.norm_eq_abs] using hBχ y) (abs_nonneg _) hMf0
        _ = Bχ * Mf := mul_comm _ _
  have hw_int : ∀ ξ, Integrable (fun η => C.rightParametrixKernel K a b ξ η * w η) := by
    refine hint w ?_ ((1 + Bχ) * Mf) (mul_nonneg (by linarith) hMf0) (fun y _ => ?_)
    · have : AEStronglyMeasurable w (volume : Measure (Fin (n + m) → ℝ)) :=
        (aestronglyMeasurable_const.sub hχ.continuous.aestronglyMeasurable).mul hg'meas
      exact this.restrict
    · rw [abs_mul]
      have h1 : |1 - χ y| ≤ 1 + Bχ := by
        calc |1 - χ y| ≤ |(1 : ℝ)| + |χ y| := abs_sub _ _
          _ ≤ 1 + Bχ := by
            rw [abs_one]
            have := hBχ y
            rw [Real.norm_eq_abs] at this
            linarith
      exact mul_le_mul h1 (hg'bd y) (abs_nonneg _) (by linarith)
  -- `P_R E_E f = P_R u + P_R w`
  let A : (Fin (n + m) → ℝ) → ℝ := Pop.apply u
  let t : (Fin (n + m) → ℝ) → ℝ := fun ξ =>
    ∫ η, C.rightParametrixKernel K a b ξ η * ((1 - χ η) * g' η)
  have hpar : ∀ (h : (Fin (n + m) → ℝ) → ℝ) ξ,
      C.rightParametrix K a b h ξ = ∫ η, C.rightParametrixKernel K a b ξ η * h η := by
    intro h ξ
    rw [← rightOp_apply K hQ V hVcl a b h]
    exact congrFun (TypeOperator.apply_eq_integral (by norm_num) Pop h) ξ
  have hA : ∀ ξ, A ξ = ∫ η, C.rightParametrixKernel K a b ξ η * u η := fun ξ =>
    congrFun (TypeOperator.apply_eq_integral (by norm_num) Pop u) ξ
  have hv_eq : ∀ ξ, C.rightParametrix K a b g' ξ = A ξ + t ξ := by
    intro ξ
    rw [hpar, hA]
    calc ∫ η, C.rightParametrixKernel K a b ξ η * g' η
        = ∫ η, (C.rightParametrixKernel K a b ξ η * u η +
            C.rightParametrixKernel K a b ξ η * w η) :=
          integral_congr_ae (Filter.Eventually.of_forall fun η => by beta_reduce; rw [hsplit η]; ring)
      _ = _ := integral_add (hu_int ξ) (hw_int ξ)
  -- Hölder regularity of `P_R u`
  have hu : holderENorm C.dl α (V : Set (Fin (n + m) → ℝ)) u ≠ ⊤ :=
    holderENorm_cutoff_mul_ne_top hEopen hEV hVU hα hα1.le hfn hχ hχc hχT
  obtain ⟨CH, -, hmemH⟩ := Pop.gain_holder hF hLeftDiffF hα hα1
  have hAmem : memHolderX driftWeight C.Xl C.dl V 2 α A := (hmemH u hu).1
  -- smoothness of `t` on `N`
  have ht : ContDiffOn ℝ (⊤ : ℕ∞) t N :=
    contDiffOn_tail_integral K aC bC hN (hNE.trans hEU) hχ hχ1 hg'int.locallyIntegrable
  -- `C^{2,α}` on `E'`
  let Nop : Opens (Fin (n + m) → ℝ) := ⟨N, hN⟩
  have hNV : (Nop : Set (Fin (n + m) → ℝ)) ⊆ (V : Set (Fin (n + m) → ℝ)) := hNE.trans hEV
  have hANop : memHolderX driftWeight C.Xl C.dl Nop 2 α A :=
    memHolderX_mono_domain driftWeight hNV hAmem
  have hvNop : memHolderXLoc driftWeight C.Xl C.dl Nop 2 α (fun x => A x + t x) :=
    memHolderXLoc_add_smooth C (fun i => driftWeight_coe_le_two i) hα hα1.le
      (hNE.trans hEU) hANop ht
  have hvE' : memHolderX driftWeight C.Xl C.dl E' 2 α (fun x => A x + t x) :=
    hvNop E' hE'c hSN
  have hfun : C.rightParametrix K a b g' = fun x => A x + t x := funext hv_eq
  rw [hfun]
  exact hvE'

/-- **The Hölder half of local solvability, assuming `LeftDifferentiation`.** For
`ξ₀ ∈ C.U` and `0 < α < 1` there is `R₀ > 0` such that for every `0 < R < R₀`, every
`g ∈ C^α_{X̃}(U_R)` has a `v ∈ C^{2,α}_{X̃}(U_{R/2})` (`memHolderX`, order `2`) with `L̃ v = g`
at every point of `U_{R/2}` (`intrinsicDriftEquation`). Here `v = P_R E_R f` with
`f = g + 𝓕_R f ∈ C^α(U_R)` (`exists_holder_solution`), `v ∈ C^{2,α}(U_{R/2})` is the interior gain
`rightParametrix_holder_interior_gain`, and the equation holds a.e. by the distributional equation
and weak derivatives and then everywhere by continuity of both sides. -/
theorem localSolvability_holder_of_leftDifferentiation
    (hsymm : ∀ u, (C.driftModel hq ν₀).norm (-u) = (C.driftModel hq ν₀).norm u)
    (hsmooth : (C.driftModel hq ν₀).norm.Smooth) (hprops : H1.FundamentalKernelProperties K)
    (hLeftDiff : LeftDifferentiationOnStandardFrames C K hQ) {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ →
      ∀ UR UR' : Opens (Fin (n + m) → ℝ), (UR : Set (Fin (n + m) → ℝ)) = C.driftBall ξ₀ R →
        (UR' : Set (Fin (n + m) → ℝ)) = C.driftBall ξ₀ (R / 2) →
        ∀ g : (Fin (n + m) → ℝ) → ℝ, memHolderX driftWeight C.Xl C.dl UR 0 α g →
          ∃ v : (Fin (n + m) → ℝ) → ℝ, memHolderX driftWeight C.Xl C.dl UR' 2 α v ∧
            intrinsicDriftEquation UR' C.Xl v g := by
  obtain ⟨V, a, b, K₀, rstar, hξV, hVcl, hab, ha1, hK₀, hK₀V, hr⟩ := exists_fixed_frame hξ₀
  have hVU : (V : Set (Fin (n + m) → ℝ)) ⊆ C.U := subset_closure.trans hVcl
  have hVle : V ≤ C.chartOpens := hVU
  let aC : TestFunction C.chartOpens ℝ (⊤ : ℕ∞) := LiftedChart.testOfLe V hVle a
  let bC : TestFunction C.chartOpens ℝ (⊤ : ℕ∞) := LiftedChart.testOfLe V hVle b
  obtain ⟨r₀, hr₀, hsolve⟩ := exists_holder_solution K aC bC hab hξ₀ ha1 hα hα1
  refine ⟨min r₀ rstar, lt_min hr₀ hr.pos, fun R hR0 hRR UR UR' hUR hUR' g hg => ?_⟩
  have hRr₀ : R < r₀ := hRR.trans_le (min_le_left _ _)
  have hRrs : R < rstar := hRR.trans_le (min_le_right _ _)
  have hR2 : 0 < R / 2 := by linarith
  have hR2R : R / 2 < R := by linarith
  have hR2rs : R / 2 < rstar := by linarith
  have hEopen : IsOpen (C.driftBall ξ₀ R) := isOpen_rsBall_of_isSmallBallRadius C hr hR0 hRrs
  have hEK : C.driftBall ξ₀ R ⊆ K₀ := hr.ball_subset R hR0 hRrs
  have hEV : C.driftBall ξ₀ R ⊆ (V : Set (Fin (n + m) → ℝ)) := hEK.trans hK₀V
  have hEU : C.driftBall ξ₀ R ⊆ C.U := hEV.trans hVU
  obtain ⟨hcpt', hcl⟩ := closure_rsBall_subset C hK₀ hr hR2 hR2R hR2rs
  have hE'c : IsCompact (closure (UR' : Set (Fin (n + m) → ℝ))) := by
    rw [hUR']
    exact hcpt'
  have hE'E : closure (UR' : Set (Fin (n + m) → ℝ)) ⊆ C.driftBall ξ₀ R := by
    rw [hUR']
    exact hcl
  have hUR'E : (UR' : Set (Fin (n + m) → ℝ)) ⊆ C.driftBall ξ₀ R := subset_closure.trans hE'E
  have hUR'U : (UR' : Set (Fin (n + m) → ℝ)) ⊆ C.U := hUR'E.trans hEU
  have hURU : (UR : Set (Fin (n + m) → ℝ)) ⊆ C.U := by
    rw [hUR]
    exact hEU
  -- the solution
  have hgn : holderENorm C.dl α (C.driftBall ξ₀ R) g < ⊤ := by
    rw [← hUR]
    exact hg.1
  obtain ⟨f, hfn, -, -, -, hsol⟩ := hsolve R hR0 hRr₀ g hgn
  -- the interior gain
  have hvmem : memHolderX driftWeight C.Xl C.dl UR' 2 α
      (C.rightParametrix K aC bC ((C.driftBall ξ₀ R).indicator f)) :=
    rightParametrix_holder_interior_gain K hQ hsymm hsmooth hprops hLeftDiff hVcl a b hEopen hEV hE'c
      hE'E hα hα1 hfn
  -- the equation
  have hX' : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (UR' : Set (Fin (n + m) → ℝ)) :=
    fun i => (liftedChart_contDiffOn_lift C i).mono hUR'U
  obtain ⟨jet, hj0, hjet⟩ := exists_jets_of_memHolderX C hα hUR'U hvmem
  have hURle : UR' ≤ C.chartOpens := hUR'U
  have hsolUR' : ∀ φ : TestFunction UR' ℝ (⊤ : ℕ∞),
      ∫ ξ in (UR' : Set (Fin (n + m) → ℝ)),
          C.rightParametrix K aC bC ((C.driftBall ξ₀ R).indicator f) ξ *
            sumSquaresWithDriftTranspose C.Xl φ ξ =
        ∫ ξ in (UR' : Set (Fin (n + m) → ℝ)), g ξ * φ ξ := by
    intro φ
    have hφt : tsupport ((LiftedChart.testOfLe UR' hURle φ :
        TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) : (Fin (n + m) → ℝ) → ℝ) ⊆
        C.driftBall ξ₀ R := φ.tsupport_subset.trans hUR'E
    have h1 := hsol (LiftedChart.testOfLe UR' hURle φ) hφt
    have h2 := setIntegral_mul_sumSquaresWithDriftTranspose_eq UR' C.Xl hX'
      C.isOpen_U.measurableSet hUR'U
      (C.rightParametrix K aC bC ((C.driftBall ξ₀ R).indicator f)) φ
    have h3 : ∫ ξ in C.driftBall ξ₀ R, g ξ * φ ξ =
        ∫ ξ in (UR' : Set (Fin (n + m) → ℝ)), g ξ * φ ξ :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hEopen.measurableSet hUR'E (fun x hx => by
        rw [φ.zero_on_compl (show x ∈ (UR' : Set (Fin (n + m) → ℝ))ᶜ from hx.2)]
        simp)
    rw [← h2, ← h3]
    exact h1
  have hcontg : ContinuousOn g (UR' : Set (Fin (n + m) → ℝ)) := by
    have hgn' : holderENorm C.dl α (UR : Set (Fin (n + m) → ℝ)) g < ⊤ := hg.1
    exact (LiftedChart.continuousOn_of_holderENorm_lt_top hURU hα hgn').mono (by
      rw [hUR]
      exact hUR'E)
  have hglocal : LocallyIntegrableOn g (UR' : Set (Fin (n + m) → ℝ)) volume :=
    hcontg.locallyIntegrableOn UR'.isOpen.measurableSet
  have h0 := (hjet [0] mem_wordFamily_drift_zero).2.1
  have hs := fun i : Fin q => (hjet _ (mem_wordFamily_drift_succ_succ i)).2.1
  have hae := weakDriftEquation_ae_of_solution UR' C.Xl hX' h0 hs hglocal hsolUR'
  have hcontL : ContinuousOn (fun x => (∑ i : Fin q, jet [i.succ, i.succ] x) + jet [0] x)
      (UR' : Set (Fin (n + m) → ℝ)) :=
    (continuousOn_finsetSum _ fun i _ =>
      (hjet _ (mem_wordFamily_drift_succ_succ i)).2.2.1).add
      (hjet [0] mem_wordFamily_drift_zero).2.2.1
  have heq := Measure.eqOn_open_of_ae_eq hae UR'.isOpen hcontL hcontg
  exact ⟨_, hvmem, jet [0], fun i => jet [i.succ, i.succ],
    (hjet [0] mem_wordFamily_drift_zero).1,
    fun i => (hjet _ (mem_wordFamily_drift_succ_succ i)).1, fun x hx => heq hx⟩

end Holder

end RothschildStein.P2
