-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.TransferCoverCore
public import RothschildStein.P2.TransferCoverHolderCover

/-!
# Hölder transfer and finite cover: from the lifted base Hölder estimate to the original domain

The base Hölder estimate (BB pp. 600–602, Thms 11.57–11.58, (11.92)-(11.93)). `LiftedBaseHolderEstimate` is the
exact statement of the lifted base Hölder estimate on a lifted chart: there are `r₀ > 0`, `β > 0`
and `C` such that for `0 < t < s < r₀` and every `u ∈ C^{2,α}_{X̃}` on a neighborhood `W` of the
closed `ρ`-ball `{ν ∘ Θ ≤ s}`
`‖u‖_{C^{2,α}_{X̃}(U^ρ_t)} ≤ C (s - t)^{-β} (‖L̃ u‖_{C^α_{X̃}(U^ρ_s)} + ‖u‖_{L^∞(U^ρ_s)})`,
with the `memHolderX`, `holderXENorm` for the lifted fields `C.Xl` and the lifted control
distance `C.dl`; the operator `L̃ = ∑ X̃_{J i}` (drift allowed) is given by intrinsic word
derivatives (`HasIntrinsicOperatorValue`).

`holder_finite_cover_of_lifted` is the consequence of the lifted base Hölder estimate for `u ∈ C^{2,α}_X(Ω'')`, the base
Hölder estimate on the original domain: `‖u‖_{C^{2,α}_X(Ω')} ≤ C (‖Lu‖_{C^α_X(Ω'')} + ‖u‖_{L^∞(Ω'')})`. It is
proved by

1. the Hölder transfer (`holderTransfer_of_doubling`: the forward inequality and the reverse
   inequality assuming the original local doubling hypothesis `OriginalLocalDoubling`) and
   the comparison `ν ∘ Θ ≍ d̃` at the radii `a = r / (2 C_ρ)`, `s₁ = r / C_ρ`
   (inner) and `b = 4 C_ρ r` (outer) for the `ρ`-radii `t = r`, `s = 2 r`;
2. the finite cover of the compact set `closure Ω'` by the base balls `V_{ρ_x / 2}(x)` and the
   Lebesgue number argument `holderENorm_le_of_cover` (pairs at distance `< ℓ` lie in one
   `V_{ρ_x}(x)`; pairs at distance `≥ ℓ` use the sup norm).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators
open RothschildStein.P1
namespace RothschildStein.P2
variable {n k : ℕ} {w : Fin k → ℕ+} {st : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}

/-- The lifted base Hölder estimate (BB pp. 600-602, (11.92)-(11.93)): on the lifted chart
`C` with the homogeneous norm `ν` there are `r₀ > 0`, `β > 0` and `C > 0` such that for
`0 < t < s < r₀`, every open `W` containing the closed `ρ`-ball `{ν ∘ Θ ≤ s}`, every
`u ∈ C^{2,α}_{X̃}(W)` and every value `f = L̃ u` of the operator `L̃ = ∑ X̃_{J i}`,
`‖u‖_{C^{2,α}_{X̃}(U^ρ_t)} ≤ C (s - t)^{-β} (‖f‖_{C^α_{X̃}(U^ρ_s)} + ‖u‖_{L^∞(U^ρ_s)})`
(`J = driftOpWords q` for the drift operator, `J = noDriftOpWords q` without drift). -/
def LiftedBaseHolderEstimate {ι : Type} [Fintype ι] (C : LiftedChart w st Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) (J : ι → List (Fin k)) (α : ℝ) : Prop :=
  ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ β : ℝ, 0 < β ∧ ∃ Cst : ℝ, 0 < Cst ∧
    ∀ t s : ℝ, 0 < t → t < s → s < r₀ →
      ∀ W : Opens (Fin (n + m) → ℝ),
        closedRhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) s ⊆ (W : Set (Fin (n + m) → ℝ)) →
        ∀ u f : (Fin (n + m) → ℝ) → ℝ,
          memHolderX w C.Xl C.dl W 2 α u → HasIntrinsicOperatorValue C.Xl W J u f →
          holderXENorm w C.Xl C.dl (rhoBallOpen C ν t) 2 α u ≤
            ENNReal.ofReal (Cst / (s - t) ^ β) *
              (holderXENorm w C.Xl C.dl (rhoBallOpen C ν s) 0 α f +
                eLpNorm u ⊤ (volume.restrict (rhoBallOpen C ν s : Set (Fin (n + m) → ℝ))))

theorem HasIntrinsicOperatorValue.lift {ι : Type} [Fintype ι] {J : ι → List (Fin k)}
    {u f : (Fin n → ℝ) → ℝ} {P : Fin k → Fin m → MvPolynomial (Fin (n + m)) ℝ}
    (Uo : Opens (Fin (n + m) → ℝ)) (Vo : Opens (Fin n → ℝ))
    (hproj : ∀ ξ ∈ (Uo : Set (Fin (n + m) → ℝ)), basePoint ξ ∈ (Vo : Set (Fin n → ℝ)))
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) (Uo : Set (Fin (n + m) → ℝ)))
    (h : HasIntrinsicOperatorValue X Vo J u f) :
    HasIntrinsicOperatorValue (triangularLift X P) Uo J (fun ξ => u (basePoint ξ))
      (fun ξ => f (basePoint ξ)) := by
  obtain ⟨g, hg, hf⟩ := h
  exact ⟨fun i ξ => g i (basePoint ξ),
    fun i => hasIntrinsicWordDeriv_comp_basePoint Uo Vo hproj hXt (J i) (hg i),
    fun ξ hξ => hf (basePoint ξ) (hproj ξ hξ)⟩

/-- At a lifted chart `C` whose lifted Hölder estimate holds, and
with the original local doubling hypothesis on `π(U)`, the original estimate holds on a small base
ball around `x₀`: for every `ε > 0` there are `0 < ρ ≤ b ≤ ε` and `K > 0` with
`‖u‖_{C^{2,α}_X(V_ρ)} ≤ K (‖Lu‖_{C^α_X(V_b)} + ‖u‖_{L^∞(V_b)})`
for `u ∈ C^{2,α}_X(V_b)` (`V_ρ = B(x₀, ρ)`, `V_b = B(x₀, b)`), and the control balls `B(x₀, ρ')`,
`ρ' ≤ b`, are Euclidean open. Here `ρ = δ a` with `a = r / (2 C_ρ)` and `b = 4 C_ρ r`. -/
theorem holder_local_transfer {ι : Type} [Fintype ι] (C : LiftedChart w st Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) (J : ι → List (Fin k)) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hdbl : OriginalLocalDoubling Ω w X (basePoint '' C.U))
    (hest : LiftedBaseHolderEstimate C ν J α) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ b K : ℝ, 0 < ρ ∧ ρ ≤ b ∧ b ≤ ε ∧ 0 < K ∧
      (∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ b → IsOpen (rsBall Ω w X x₀ ρ')) ∧
      ∀ (Vρ Vb : Opens (Fin n → ℝ)), (Vρ : Set (Fin n → ℝ)) = rsBall Ω w X x₀ ρ →
        (Vb : Set (Fin n → ℝ)) = rsBall Ω w X x₀ b → ∀ u f : (Fin n → ℝ) → ℝ,
        memHolderX w X (controlDistance Ω w X) Vb 2 α u → HasIntrinsicOperatorValue X Vb J u f →
        holderXENorm w X (controlDistance Ω w X) Vρ 2 α u ≤ ENNReal.ofReal K *
          (holderXENorm w X (controlDistance Ω w X) Vb 0 α f +
            eLpNorm u ⊤ (volume.restrict (Vb : Set (Fin n → ℝ)))) := by
  classical
  set η₀ : Fin (n + m) → ℝ := joinPoint x₀ (0 : Fin m → ℝ) with hη₀
  have hK : IsCompact ({η₀} : Set (Fin (n + m) → ℝ)) := isCompact_singleton
  have hKU : ({η₀} : Set (Fin (n + m) → ℝ)) ⊆ C.U := singleton_subset_iff.mpr C.center_mem
  have hbase : basePoint η₀ = x₀ := basePoint_joinPoint x₀ 0
  obtain ⟨r₀, hr₀, β, hβ, C₀, hC₀, hbound⟩ := hest
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
  set r : ℝ := min (r₀ / 4) (R / (8 * Cν)) with hr
  have hr0 : 0 < r := lt_min (by positivity) (by positivity)
  have hrr₀ : r ≤ r₀ / 4 := min_le_left _ _
  have hrR : r ≤ R / (8 * Cν) := min_le_right _ _
  set b : ℝ := 4 * Cν * r with hb
  set s₁ : ℝ := r / Cν with hs₁
  set a : ℝ := s₁ / 2 with ha
  have hb0 : 0 < b := by positivity
  have hs₁0 : 0 < s₁ := by positivity
  have ha0 : 0 < a := by positivity
  have has : a < s₁ := by rw [ha]; linarith
  have hs₁r : s₁ ≤ r := by
    rw [hs₁]
    exact div_le_self hr0.le hCν1
  have hs₁b : s₁ ≤ b := by
    rw [hb]
    nlinarith
  have hbR : b ≤ R / 2 := by
    rw [hb]
    have : 4 * Cν * r ≤ 4 * Cν * (R / (8 * Cν)) :=
      mul_le_mul_of_nonneg_left hrR (by positivity)
    calc 4 * Cν * r ≤ 4 * Cν * (R / (8 * Cν)) := this
      _ = R / 2 := by field_simp; ring
  have hbR' : b < R := by linarith
  have hbrB : b < rB := lt_of_lt_of_le hbR' hRB
  have hs₁rR : s₁ < rR := lt_of_le_of_lt hs₁b (lt_of_lt_of_le hbR' hRR)
  have hbρ : b ≤ ρ₀ := (hbR'.trans_le hRρ).le
  have hbε : b ≤ ε := (hbR'.trans_le hRε).le
  have h2r : 2 * r < r₀ := by linarith
  have hδa0 : 0 < δR * a := mul_pos hδR0 ha0
  have hδa : δR * a ≤ b := by nlinarith
  -- the reverse transfer at `(a, s₁)`
  obtain ⟨CR, hCR, hCRall⟩ := hrev a s₁ ha0 has hs₁rR
  obtain ⟨-, hwords⟩ := hCRall η₀ (mem_singleton _)
  -- the lifted balls
  have hUsU : rsBall C.O w C.Xl η₀ s₁ ⊆ C.U := by
    obtain ⟨h, -⟩ := hall η₀ (mem_singleton _) s₁ hs₁0 (lt_of_le_of_lt hs₁b hbrB)
    exact h
  have hUbU : rsBall C.O w C.Xl η₀ b ⊆ C.U := by
    obtain ⟨h, -⟩ := hall η₀ (mem_singleton _) b hb0 hbrB
    exact h
  let Vs : Opens (Fin n → ℝ) :=
    ⟨rsBall Ω w X (basePoint η₀) s₁, by rw [hbase]; exact hopen s₁ hs₁0 (hs₁b.trans hbρ)⟩
  let Us : Opens (Fin (n + m) → ℝ) := ⟨rsBall C.O w C.Xl η₀ s₁, isOpen_rsBall_lifted C hUsU⟩
  let Ub : Opens (Fin (n + m) → ℝ) := ⟨rsBall C.O w C.Xl η₀ b, isOpen_rsBall_lifted C hUbU⟩
  -- inclusions of balls
  have hUs_ρ : (Us : Set (Fin (n + m) → ℝ)) ⊆ (rhoBallOpen C ν r : Set (Fin (n + m) → ℝ)) := by
    intro ξ hξ
    have hξ' : ξ ∈ rsBall C.O w C.Xl η₀ s₁ := hξ
    have hξU : ξ ∈ C.U := hUsU hξ'
    refine ⟨hξU, ?_⟩
    obtain ⟨hl, -⟩ := hgc η₀ C.center_mem ξ hξU
    have h1 : ENNReal.ofReal (ν (C.Θ η₀ ξ) / Cν) < ENNReal.ofReal s₁ := lt_of_le_of_lt hl hξ'.2
    have h2 : ν (C.Θ η₀ ξ) / Cν < s₁ := (ENNReal.ofReal_lt_ofReal_iff hs₁0).1 h1
    calc ν (C.Θ η₀ ξ) < s₁ * Cν := (div_lt_iff₀ hCν0).1 h2
      _ = r := by rw [hs₁]; field_simp
  have hcl : closedRhoBall C ν η₀ (2 * r) ⊆ (Ub : Set (Fin (n + m) → ℝ)) := by
    intro ξ hξ
    obtain ⟨hξU, hν⟩ := hξ
    refine ⟨C.closure_U_subset (subset_closure hξU), ?_⟩
    obtain ⟨-, hup⟩ := hgc η₀ C.center_mem ξ hξU
    refine lt_of_le_of_lt hup ((ENNReal.ofReal_lt_ofReal_iff hb0).2 ?_)
    nlinarith [mul_pos hCν0 hr0]
  have hρ2_Ub : (rhoBallOpen C ν (2 * r) : Set (Fin (n + m) → ℝ)) ⊆ (Ub : Set (Fin (n + m) → ℝ)) :=
    (rhoBall_subset_closed C ν η₀).trans hcl
  have hK0 : 0 < CR * (C₀ / r ^ β) := mul_pos hCR (div_pos hC₀ (Real.rpow_pos_of_pos hr0 _))
  refine ⟨δR * a, b, CR * (C₀ / r ^ β), hδa0, hδa, hbε, hK0,
    fun ρ' h0 h1 => hopen ρ' h0 (h1.trans hbρ), ?_⟩
  intro Vρ Vb hVρ hVb u f hu hf
  -- the base sets
  have hVsVb : (Vs : Set (Fin n → ℝ)) ⊆ (Vb : Set (Fin n → ℝ)) := by
    show rsBall Ω w X (basePoint η₀) s₁ ⊆ (Vb : Set (Fin n → ℝ))
    rw [hVb, hbase]
    exact rsBall_mono Ω w X x₀ hs₁b
  have hproj : ∀ ξ ∈ (Ub : Set (Fin (n + m) → ℝ)), basePoint ξ ∈ (Vb : Set (Fin n → ℝ)) := by
    intro ξ hξ
    have h1 := basePoint_mem_rsBall (P := C.P) (hξ : ξ ∈ rsBall C.O w C.Xl η₀ b)
    rw [hbase] at h1
    rw [hVb]
    exact h1
  have hXt_b := liftedChart_hXt C Ub hUbU
  -- (1) the reverse transfer
  have hderiv : ∀ I ∈ wordFamily w 2, ∃ g, hasIntrinsicWordDeriv X Vs I u g := by
    intro I hI
    obtain ⟨g, hg, -⟩ := hu.2 I hI
    exact ⟨g, hasIntrinsicWordDeriv_mono hVsVb I hg⟩
  have hrw := hwords Vρ Vs Us (by rw [hVρ, hbase]) rfl rfl 2 u hderiv
  -- (2) the lifted function on the outer ball and the lifted estimate
  have hut : memHolderX w C.Xl C.dl Ub 2 α (fun ξ => u (basePoint ξ)) :=
    memHolderX_comp_basePoint (P := C.P) Ω Ub Vb hproj hXt_b hα.le 2 hu
  have hft : HasIntrinsicOperatorValue C.Xl Ub J (fun ξ => u (basePoint ξ))
      (fun ξ => f (basePoint ξ)) := hf.lift Ub Vb hproj hXt_b
  have h3 := hbound r (2 * r) hr0 (by linarith) h2r Ub hcl _ _ hut hft
  have h2r' : 2 * r - r = r := by ring
  rw [h2r'] at h3
  -- (3) the right-hand side on the outer ball
  have hf0 : holderXENorm w C.Xl C.dl (rhoBallOpen C ν (2 * r)) 0 α (fun ξ => f (basePoint ξ)) ≤
      holderXENorm w X (controlDistance Ω w X) Vb 0 α f :=
    (holderXENorm_mono_domain w hρ2_Ub 0 _).trans
      (holderXENorm_comp_le (P := C.P) Ω Ub Vb hproj hXt_b hα.le 0 f)
  have hu_top : eLpNorm (fun ξ => u (basePoint ξ)) ⊤
      (volume.restrict (rhoBallOpen C ν (2 * r) : Set (Fin (n + m) → ℝ))) ≤
      eLpNorm u ⊤ (volume.restrict (Vb : Set (Fin n → ℝ))) :=
    (eLpNorm_mono_measure _ (Measure.restrict_mono hρ2_Ub le_rfl)).trans
      (eLpNorm_top_comp_basePoint_le Ub.isOpen.measurableSet Vb.isOpen.measurableSet hproj u)
  calc holderXENorm w X (controlDistance Ω w X) Vρ 2 α u
      ≤ ENNReal.ofReal CR * holderXENorm w C.Xl C.dl Us 2 α (fun ξ => u (basePoint ξ)) := hrw
    _ ≤ ENNReal.ofReal CR *
        holderXENorm w C.Xl C.dl (rhoBallOpen C ν r) 2 α (fun ξ => u (basePoint ξ)) :=
      mul_le_mul' le_rfl (holderXENorm_mono_domain w hUs_ρ 2 _)
    _ ≤ ENNReal.ofReal CR * (ENNReal.ofReal (C₀ / r ^ β) *
        (holderXENorm w X (controlDistance Ω w X) Vb 0 α f +
          eLpNorm u ⊤ (volume.restrict (Vb : Set (Fin n → ℝ))))) :=
      mul_le_mul' le_rfl (h3.trans (mul_le_mul' le_rfl (add_le_add hf0 hu_top)))
    _ = ENNReal.ofReal (CR * (C₀ / r ^ β)) *
        (holderXENorm w X (controlDistance Ω w X) Vb 0 α f +
          eLpNorm u ⊤ (volume.restrict (Vb : Set (Fin n → ℝ)))) := by
      rw [ENNReal.ofReal_mul hCR.le, mul_assoc]

/-- The original-domain base Hölder estimate from the lifted one (BB p. 602,
Thm 11.58). For `Ω' ⋐ Ω'' ⋐ Ω` (here: `closure Ω'` compact in `Ω''`, `Ω'' ⊆ Ω`) and
`0 < α < 1`: if the lifted base Hölder estimate `LiftedBaseHolderEstimate` holds on a lifted chart
at every point of `closure Ω'` (the charts given by the lifting theorem, taken as data) and the
original local doubling hypothesis holds on the projected neighborhood `π(U)` of every such chart
(`OriginalLocalDoubling`), then there is `C = C(X, Ω', Ω'', α)` with
`‖u‖_{C^{2,α}_X(Ω')} ≤ C (‖Lu‖_{C^α_X(Ω'')} + ‖u‖_{L^∞(Ω'')})`
for all `u ∈ C^{2,α}_X(Ω'')` and every value `f = L u` of `L = ∑ X_{J i}` on `Ω''`
(`J = driftOpWords q`: drift allowed). -/
theorem holder_finite_cover_of_lifted {ι : Type} [Fintype ι] (J : ι → List (Fin k)) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (Ω' Ω'' : Opens (Fin n → ℝ))
    (hcpt : IsCompact (closure (Ω' : Set (Fin n → ℝ))))
    (hΩ'Ω'' : closure (Ω' : Set (Fin n → ℝ)) ⊆ (Ω'' : Set (Fin n → ℝ)))
    (hΩ''Ω : (Ω'' : Set (Fin n → ℝ)) ⊆ Ω)
    (hdbl : ∀ x ∈ closure (Ω' : Set (Fin n → ℝ)), ∀ (m : ℕ) (C : LiftedChart w st Ω hΩ X x m),
      OriginalLocalDoubling Ω w X (basePoint '' C.U))
    (hcharts : ∀ x ∈ closure (Ω' : Set (Fin n → ℝ)), ∃ m : ℕ,
      ∃ C : LiftedChart w st Ω hΩ X x m, ∃ ν : G2.HomogeneousNorm C.G,
        LiftedBaseHolderEstimate C ν J α) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∀ u f : (Fin n → ℝ) → ℝ,
      memHolderX w X (controlDistance Ω w X) Ω'' 2 α u → HasIntrinsicOperatorValue X Ω'' J u f →
      holderXENorm w X (controlDistance Ω w X) Ω' 2 α u ≤ ENNReal.ofReal Cst *
        (holderXENorm w X (controlDistance Ω w X) Ω'' 0 α f +
          eLpNorm u ⊤ (volume.restrict (Ω'' : Set (Fin n → ℝ)))) := by
  classical
  have hxΩ : ∀ x ∈ closure (Ω' : Set (Fin n → ℝ)), x ∈ Ω := fun x hx => hΩ''Ω (hΩ'Ω'' hx)
  have hΩ'sub : (Ω' : Set (Fin n → ℝ)) ⊆ (Ω'' : Set (Fin n → ℝ)) := subset_closure.trans hΩ'Ω''
  have hloc : ∀ x ∈ closure (Ω' : Set (Fin n → ℝ)), ∃ ρ b K : ℝ, 0 < ρ ∧ ρ ≤ b ∧
      rsBall Ω w X x b ⊆ (Ω'' : Set (Fin n → ℝ)) ∧ 0 < K ∧
      (∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ b → IsOpen (rsBall Ω w X x ρ')) ∧
      ∀ (Vρ Vb : Opens (Fin n → ℝ)), (Vρ : Set (Fin n → ℝ)) = rsBall Ω w X x ρ →
        (Vb : Set (Fin n → ℝ)) = rsBall Ω w X x b → ∀ u f : (Fin n → ℝ) → ℝ,
        memHolderX w X (controlDistance Ω w X) Vb 2 α u → HasIntrinsicOperatorValue X Vb J u f →
        holderXENorm w X (controlDistance Ω w X) Vρ 2 α u ≤ ENNReal.ofReal K *
          (holderXENorm w X (controlDistance Ω w X) Vb 0 α f +
            eLpNorm u ⊤ (volume.restrict (Vb : Set (Fin n → ℝ)))) := by
    intro x hx
    obtain ⟨m, C, ν, hest⟩ := hcharts x hx
    obtain ⟨ε, hε0, hεV⟩ := exists_rsBall_subset hΩ
      (fun i => (liftedChart_contDiffOn_base C i).continuousOn) Ω''.isOpen (hΩ'Ω'' hx) (hxΩ x hx)
    obtain ⟨ρ, b, K, hρ, hρb, hbε, hK, hopen, hbound⟩ :=
      holder_local_transfer C ν J hα hα1 (hdbl x hx m C) hest hε0
    exact ⟨ρ, b, K, hρ, hρb, (rsBall_mono Ω w X x hbε).trans hεV, hK, hopen, hbound⟩
  choose ρ b K hρ0 hρb hbΩ hK0 hopen hbound using hloc
  have hnhds : ∀ x (hx : x ∈ closure (Ω' : Set (Fin n → ℝ))),
      rsBall Ω w X x (ρ x hx / 2) ∈ 𝓝 x := fun x hx =>
    (hopen x hx _ (half_pos (hρ0 x hx)) (by linarith [hρb x hx, hρ0 x hx])).mem_nhds
      ⟨hxΩ x hx, by
        rw [G1.controlDistance_self w X (hxΩ x hx)]
        exact ENNReal.ofReal_pos.2 (half_pos (hρ0 x hx))⟩
  obtain ⟨t, ht⟩ := hcpt.elim_nhds_subcover' (fun x hx => rsBall Ω w X x (ρ x hx / 2)) hnhds
  obtain ⟨ℓ, hℓ0, hℓ⟩ := exists_pos_le_finset t (fun x => ρ x.1 x.2 / 2)
    (fun x _ => half_pos (hρ0 x.1 x.2))
  let A : closure (Ω' : Set (Fin n → ℝ)) → Opens (Fin n → ℝ) := fun x =>
    ⟨rsBall Ω w X x.1 (ρ x.1 x.2), hopen x.1 x.2 _ (hρ0 x.1 x.2) (hρb x.1 x.2)⟩
  let B : closure (Ω' : Set (Fin n → ℝ)) → Opens (Fin n → ℝ) := fun x =>
    ⟨rsBall Ω w X x.1 (b x.1 x.2),
      hopen x.1 x.2 _ ((hρ0 x.1 x.2).trans_le (hρb x.1 x.2)) le_rfl⟩
  have hBΩ : ∀ x, (B x : Set (Fin n → ℝ)) ⊆ (Ω'' : Set (Fin n → ℝ)) := fun x => hbΩ x.1 x.2
  have hAΩ : ∀ x, (A x : Set (Fin n → ℝ)) ⊆ (Ω'' : Set (Fin n → ℝ)) := fun x =>
    (rsBall_mono Ω w X x.1 (hρb x.1 x.2)).trans (hbΩ x.1 x.2)
  -- the cover of `Ω'` and the Lebesgue number
  have hcover : ∀ y ∈ (Ω' : Set (Fin n → ℝ)), ∃ x ∈ t, y ∈ ((A x : Opens (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    intro y hy
    have h1 := ht (subset_closure hy)
    simp only [mem_iUnion] at h1
    obtain ⟨x, hxt, hyx⟩ := h1
    exact ⟨x, hxt, ⟨hyx.1, lt_of_lt_of_le hyx.2
      (ENNReal.ofReal_le_ofReal (by linarith [hρ0 x.1 x.2]))⟩⟩
  have hleb : ∀ y ∈ (Ω' : Set (Fin n → ℝ)), ∀ z ∈ (Ω' : Set (Fin n → ℝ)),
      controlDistance Ω w X y z < ENNReal.ofReal ℓ →
      ∃ x ∈ t, y ∈ ((A x : Opens (Fin n → ℝ)) : Set (Fin n → ℝ)) ∧
        z ∈ ((A x : Opens (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    intro y hy z hz hyz
    have h1 := ht (subset_closure hy)
    simp only [mem_iUnion] at h1
    obtain ⟨x, hxt, hyx⟩ := h1
    have hρx := hρ0 x.1 x.2
    refine ⟨x, hxt, ⟨hyx.1, lt_of_lt_of_le hyx.2
      (ENNReal.ofReal_le_ofReal (by linarith))⟩, ⟨hxΩ z (subset_closure hz), ?_⟩⟩
    show controlDistance Ω w X x.1 z < ENNReal.ofReal (ρ x.1 x.2)
    calc controlDistance Ω w X x.1 z
        ≤ controlDistance Ω w X x.1 y + controlDistance Ω w X y z :=
          G1.controlDistance_triangle Ω w X x.1 y z
      _ < ENNReal.ofReal (ρ x.1 x.2 / 2) + ENNReal.ofReal ℓ := ENNReal.add_lt_add hyx.2 hyz
      _ ≤ ENNReal.ofReal (ρ x.1 x.2 / 2) + ENNReal.ofReal (ρ x.1 x.2 / 2) :=
          add_le_add le_rfl (ENNReal.ofReal_le_ofReal (hℓ x hxt))
      _ = ENNReal.ofReal (ρ x.1 x.2) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  have hsep : ∀ x ∈ t, ∀ y ∈ ((A x : Opens (Fin n → ℝ)) : Set (Fin n → ℝ)),
      ∀ z ∈ ((A x : Opens (Fin n → ℝ)) : Set (Fin n → ℝ)),
      controlDistance Ω w X y z = 0 → y = z := by
    intro x _ y hy z _ h
    obtain ⟨m, C, -⟩ := hcharts x.1 x.2
    exact (G1.controlDistance_eq_zero_iff hΩ w X
      (fun i => (liftedChart_contDiffOn_base C i).continuousOn)
      (show y ∈ Ω from (hy : y ∈ rsBall Ω w X x.1 (ρ x.1 x.2)).1)).1 h
  -- the constants
  have hKsum : 0 ≤ ∑ x ∈ t, K x.1 x.2 := Finset.sum_nonneg fun x _ => (hK0 x.1 x.2).le
  set Ksum : ℝ := 1 + ∑ x ∈ t, K x.1 x.2 with hKs
  have hKs1 : 1 ≤ Ksum := by linarith
  have hℓα : 0 < ℓ ^ α := Real.rpow_pos_of_pos hℓ0 α
  set cK : ℝ := Ksum * (2 + 2 * (ℓ ^ α)⁻¹) with hcK
  have hcK0 : 0 < cK := by positivity
  set nW : ℕ := (wordFamily w 2).card with hnW
  have hCst : 0 < ((nW : ℝ) + 1) * cK := by positivity
  refine ⟨((nW : ℝ) + 1) * cK, hCst, fun u f hu hf => ?_⟩
  set N' : ℝ≥0∞ := holderXENorm w X (controlDistance Ω w X) Ω'' 0 α f +
    eLpNorm u ⊤ (volume.restrict (Ω'' : Set (Fin n → ℝ))) with hN'
  by_cases hN : N' = ⊤
  · rw [hN, ENNReal.mul_top (ENNReal.ofReal_pos.2 hCst).ne']
    exact le_top
  set M0 : ℝ := N'.toReal with hM0
  have hM00 : 0 ≤ M0 := ENNReal.toReal_nonneg
  have hN'eq : N' = ENNReal.ofReal M0 := (ENNReal.ofReal_toReal hN).symm
  -- the local bounds on the cover
  have hAbound : ∀ x ∈ t, holderXENorm w X (controlDistance Ω w X) (A x) 2 α u ≤
      ENNReal.ofReal (K x.1 x.2 * M0) := by
    intro x _
    refine (hbound x.1 x.2 (A x) (B x) rfl rfl u f
      (memHolderX_mono_domain w (hBΩ x) hu) (hf.mono (hBΩ x))).trans ?_
    calc ENNReal.ofReal (K x.1 x.2) *
          (holderXENorm w X (controlDistance Ω w X) (B x) 0 α f +
            eLpNorm u ⊤ (volume.restrict (B x : Set (Fin n → ℝ))))
        ≤ ENNReal.ofReal (K x.1 x.2) * N' := by
          refine mul_le_mul' le_rfl (add_le_add (holderXENorm_mono_domain w (hBΩ x) 0 f) ?_)
          exact eLpNorm_mono_measure _ (Measure.restrict_mono (hBΩ x) le_rfl)
      _ = ENNReal.ofReal (K x.1 x.2 * M0) := by
          rw [hN'eq, ← ENNReal.ofReal_mul (hK0 x.1 x.2).le]
  -- the estimate for each word
  have hword : ∀ I ∈ wordFamily w 2, intrinsicWordENorm X (controlDistance Ω w X) Ω' I α u ≤
      ENNReal.ofReal (cK * M0) := by
    intro I hI
    obtain ⟨g, hg, -⟩ := hu.2 I hI
    have hgΩ' : hasIntrinsicWordDeriv X Ω' I u g := hasIntrinsicWordDeriv_mono hΩ'sub I hg
    rw [intrinsicWordENorm_eq_holderENorm hgΩ']
    have hM : 0 ≤ Ksum * M0 := mul_nonneg (by linarith) hM00
    have hcov := holderENorm_le_of_cover (d := controlDistance Ω w X) hα t
      (fun x => ((A x : Opens (Fin n → ℝ)) : Set (Fin n → ℝ)))
      (U := (Ω' : Set (Fin n → ℝ))) (g := g) hM hℓ0 hcover hleb hsep (by
        intro x hx
        have hgA : hasIntrinsicWordDeriv X (A x) I u g := hasIntrinsicWordDeriv_mono (hAΩ x) I hg
        show holderENorm (controlDistance Ω w X) α ((A x : Opens (Fin n → ℝ)) : Set (Fin n → ℝ)) g ≤
          ENNReal.ofReal (Ksum * M0)
        rw [← intrinsicWordENorm_eq_holderENorm hgA]
        refine (intrinsicWordENorm_le_holderXENorm w hI u).trans ((hAbound x hx).trans ?_)
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hM00)
        have := Finset.single_le_sum (f := fun x : closure (Ω' : Set (Fin n → ℝ)) => K x.1 x.2)
          (fun x _ => (hK0 x.1 x.2).le) hx
        linarith)
    have hrw : Ksum * M0 * (2 + 2 * (ℓ ^ α)⁻¹) = cK * M0 := by rw [hcK]; ring
    rw [hrw] at hcov
    exact hcov
  have hcard : ∀ I ∈ wordFamily w 2, intrinsicWordENorm X (controlDistance Ω w X) Ω' I α u ≤
      ENNReal.ofReal (cK * M0) := hword
  calc holderXENorm w X (controlDistance Ω w X) Ω' 2 α u
      = ∑ I ∈ wordFamily w 2, intrinsicWordENorm X (controlDistance Ω w X) Ω' I α u := rfl
    _ ≤ ∑ _I ∈ wordFamily w 2, ENNReal.ofReal (cK * M0) := Finset.sum_le_sum hcard
    _ = ENNReal.ofReal ((nW : ℝ) * (cK * M0)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg nW),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (((nW : ℝ) + 1) * cK * M0) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : (nW : ℝ) * (cK * M0) ≤ ((nW : ℝ) + 1) * cK * M0 := by
          have h1 : 0 ≤ cK * M0 := mul_nonneg hcK0.le hM00
          nlinarith
        exact this
    _ = ENNReal.ofReal (((nW : ℝ) + 1) * cK) * N' := by
        rw [hN'eq, ← ENNReal.ofReal_mul hCst.le]

/-- drift case: `L = X_0 + ∑_{i ≥ 1} X_i²` on the alphabet `Fin (q + 1)`
with weights `driftWeight` (drift of weight two at the letter `0`). -/
theorem holder_finite_cover_drift_of_lifted {q : ℕ}
    {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (Ω' Ω'' : Opens (Fin n → ℝ)) (hcpt : IsCompact (closure (Ω' : Set (Fin n → ℝ))))
    (hΩ'Ω'' : closure (Ω' : Set (Fin n → ℝ)) ⊆ (Ω'' : Set (Fin n → ℝ)))
    (hΩ''Ω : (Ω'' : Set (Fin n → ℝ)) ⊆ Ω)
    (hdbl : ∀ x ∈ closure (Ω' : Set (Fin n → ℝ)), ∀ (m : ℕ)
      (C : LiftedChart driftWeight st Ω hΩ X x m), OriginalLocalDoubling Ω driftWeight X (basePoint '' C.U))
    (hcharts : ∀ x ∈ closure (Ω' : Set (Fin n → ℝ)), ∃ m : ℕ,
      ∃ C : LiftedChart driftWeight st Ω hΩ X x m, ∃ ν : G2.HomogeneousNorm C.G,
        LiftedBaseHolderEstimate C ν (driftOpWords q) α) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∀ u f : (Fin n → ℝ) → ℝ,
      memHolderX driftWeight X (controlDistance Ω driftWeight X) Ω'' 2 α u →
      HasIntrinsicOperatorValue X Ω'' (driftOpWords q) u f →
      holderXENorm driftWeight X (controlDistance Ω driftWeight X) Ω' 2 α u ≤
        ENNReal.ofReal Cst *
          (holderXENorm driftWeight X (controlDistance Ω driftWeight X) Ω'' 0 α f +
            eLpNorm u ⊤ (volume.restrict (Ω'' : Set (Fin n → ℝ)))) :=
  holder_finite_cover_of_lifted (driftOpWords q) hα hα1 Ω' Ω'' hcpt hΩ'Ω'' hΩ''Ω hdbl hcharts

end RothschildStein.P2
