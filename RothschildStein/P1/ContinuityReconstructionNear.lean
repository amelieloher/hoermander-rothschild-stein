-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuityReconstructionPV

/-!
# Reconstruction: `T_near f = a ∑_j T_j (b f)`

For a near certificate `cert` (finite localization `(t, χ_j, ψ_j)`, radial profile `φ`, truncation
`d'`) with Data D `Q_j` on each doubled ball, the near part `a(ξ) K^φ(ξ, η) b(η)` of one principal
term satisfies, for every input `f` with `b f` Hölder on the balls of the cover:

* `rhoTruncated_near_eq`: the `ρ`-truncated integrals of the near part against `f` are
  `a(ξ) ∑_j ∫_{d' > ε} (χ_j K ψ_j)(ξ, y) (b f)(y) dy`, with all pieces integrable;
* `hasRhoPV_near`: the `ρ`-principal value of the near part exists at every `ξ` and equals the
  explicit finite sum `nearOutput = a(ξ) ∑_j (T_j (b f))(ξ)` of H2's principal values, each
  `T_j` extended by zero outside its ball.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology
namespace RothschildStein.P1
namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The input of the localized operators: the product
`b f`, extended by zero to the carrier (the function on the carrier `y ↦ b(y) f(y)`). -/
def inputCarrier (b f : (Fin (n + m) → ℝ) → ℝ) : C.Carrier → ℝ := fun y => b y.val * f y.val

variable {C}
variable {ν : (Fin (n + m) → ℝ) → ℝ} {Fs : Set (Fin (n + m) → ℝ)}
  {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}
  {Γ : (Fin (n + m) → ℝ) → ℝ} {cert : C.NearCertificate ν Fs}

open Classical in
/-- **The explicit output of the near part**,
`a(ξ) ∑_j (T_j (b f))(ξ)` of the finite reconstruction formula: `T_j` is H2's principal value of the localized
operator with kernel `χ_j(x) K(x, y) ψ_j(y)`, its output extended by zero (it vanishes outside
`B(z_j, r/4)`); outside the chart domain the output is `0` (there `a = 0`). -/
def nearOutput (dd : C.NearDataD cert D Γ) (a b f : (Fin (n + m) → ℝ) → ℝ)
    (ξ : Fin (n + m) → ℝ) : ℝ :=
  if h : ξ ∈ C.U then
    a ξ * ∑ z : cert.t, (dd.Q z).principalValue (C.inputCarrier b f) (Carrier.mk ξ h)
  else 0

/-- The ball of the Data D of a centre is the ball of the cover. -/
theorem Q_ball_eq (dd : C.NearDataD cert D Γ) (z : cert.t) :
    ball (dd.Q z).z (dd.Q z).R = ball z.1 cert.r := by
  rw [(dd.split z).z_eq, (dd.split z).R_eq]

/-- The output cutoff `χ_j` of the Data D of a centre vanishes outside `B(z_j, r/4)`. -/
theorem Q_a_eq_zero_of_not_mem (dd : C.NearDataD cert D Γ) (z : cert.t) {x : C.Carrier}
    (hx : x ∉ ball (dd.Q z).z ((dd.Q z).R / 4)) : (dd.Q z).a x = 0 := by
  rw [(dd.split z).a_eq]
  show cert.χ z.1 x.val = 0
  by_contra hne
  have hxs : x.val ∈ tsupport (cert.χ z.1) := subset_tsupport _ hne
  obtain ⟨x', hx', hxx'⟩ := cert.loc.χ_support z.1 z.2 hxs
  have h : x' = x := Carrier.val_injective hxx'
  subst h
  apply hx
  rw [(dd.split z).z_eq, (dd.split z).R_eq]
  exact hx'

/-- A function that is bounded Hölder on every ball of the cover is bounded Hölder on the
ball of each Data D. -/
theorem boundedHolder_Q_ball (dd : C.NearDataD cert D Γ) {δ : ℝ≥0} {g : C.Carrier → ℝ}
    (hg : ∀ z : cert.t, H2.BoundedHolder δ (ball z.1 cert.r) g) (z : cert.t) :
    H2.BoundedHolder δ (ball (dd.Q z).z (dd.Q z).R) g := by
  rw [Q_ball_eq dd z]
  exact hg z

/-- **The finite reconstruction formula for the truncations.** Let
`x` be a point of the output support `Fs`, `ε > 0`, and `b f` bounded Hölder (extended by zero to
the carrier) on the balls of the cover. The `ρ`-truncation of the near part at `x`
is integrable and equals `a(x) ∑_j ∫_{d'(x,y) > ε} χ_j(x) K(x, y) ψ_j(y) (b f)(y) dy`, i.e. the
sum of H2's truncated integrals (`d' = ρ` wherever the near kernel is nonzero, and
`∑_j χ_j K ψ_j = K` on `Fs`). -/
theorem rhoTruncated_near_eq (dd : C.NearDataD cert D Γ) {a b f : (Fin (n + m) → ℝ) → ℝ}
    (hνg : C.G.IsHomogeneousGauge ν) (hb0 : ∀ ξ, ξ ∉ C.U → b ξ = 0) {δ : ℝ≥0} (hδ : 0 < δ)
    (hg : ∀ z : cert.t, H2.BoundedHolder δ (ball z.1 cert.r) (C.inputCarrier b f))
    {x : C.Carrier} (hx : x.val ∈ Fs) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun η => C.nearKernel ν D Γ cert.φ a b x.val η * f η)
        {η | ε < C.rhoGauge ν x.val η} volume ∧
      rhoTruncated (C.rhoGauge ν) (C.nearKernel ν D Γ cert.φ a b) f ε x.val =
        a x.val * ∑ z : cert.t, H2.truncatedIntegral (volume : Measure C.Carrier)
          (ball (dd.Q z).z (dd.Q z).R) cert.T.d' (dd.Q z).cutoffKernel ε
          (C.inputCarrier b f) x := by
  classical
  have hμ : cert.S.μ = volume := cert.hS.μ_eq
  have hν : Continuous ν := hνg.1
  have hν0 : ν 0 = 0 := (hνg.2.2.1 0).mpr rfl
  obtain ⟨g, hg_def⟩ : ∃ g : C.Carrier → ℝ, g = C.inputCarrier b f := ⟨_, rfl⟩
  obtain ⟨Kc, hKc⟩ : ∃ Kc : C.Carrier → C.Carrier → ℝ,
      Kc = C.carrierKernel (C.pairKernel ν D Γ cert.φ) := ⟨_, rfl⟩
  rw [← hg_def] at hg ⊢
  have hsum : ∀ y, ∑ z : cert.t, (dd.Q z).cutoffKernel x y = Kc x y := fun y => by
    rw [hKc]
    exact sum_cutoffKernel_eq dd x y hx
  set Bρ : Set C.Carrier := {y | ε < C.rho ν x y} with hBρ
  set Sε : Set C.Carrier := {y | ε < cert.T.d' x y} with hSε
  have hBρm : MeasurableSet Bρ :=
    measurableSet_lt measurable_const
      ((C.continuous_rho hν).measurable.comp (measurable_const.prodMk measurable_id))
  have hSεm : MeasurableSet Sε :=
    measurableSet_lt measurable_const (cert.T.meas.comp (measurable_const.prodMk measurable_id))
  have hUS : C.U ∩ {η | ε < C.rhoGauge ν x.val η} = Carrier.val '' Bρ := by
    ext η
    constructor
    · rintro ⟨hη, hεη⟩
      exact ⟨Carrier.mk η hη, hεη, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.val_mem, hy⟩
  set F : (Fin (n + m) → ℝ) → ℝ := fun η => C.nearKernel ν D Γ cert.φ a b x.val η * f η with hF
  have hF0 : ∀ η, η ∉ C.U → F η = 0 := fun η hη => by simp [hF, nearKernel, hb0 η hη]
  obtain ⟨hint, hI⟩ := Carrier.setIntegral_eq_carrier_of_inter
    {η | ε < C.rhoGauge ν x.val η} F hF0 hBρm hUS
  -- pointwise comparison of the two truncated integrands on the carrier
  have hstar : ∀ y : C.Carrier, Bρ.indicator (fun y : C.Carrier => F y.val) y =
      Sε.indicator (fun y : C.Carrier => a x.val * Kc x y * g y) y := by
    intro y
    by_cases hxy : x = y
    · subst hxy
      have h0 : x ∉ Bρ := by
        show ¬ (ε < C.rho ν x x)
        unfold rho
        rw [(C.chart x.val x.val_mem).2.2.2.2, hν0]
        exact not_lt.mpr hε.le
      rw [indicator_of_notMem h0]
      have hK0 : Kc x x = 0 := by rw [hKc]; exact carrierKernel_self x
      by_cases h : x ∈ Sε
      · rw [indicator_of_mem h]
        simp [hK0]
      · rw [indicator_of_notMem h]
    · by_cases hp : C.pairKernel ν D Γ cert.φ x.val y.val = 0
      · have hK0 : Kc x y = 0 := by rw [hKc, carrierKernel_of_ne hxy]; exact hp
        have hF0' : F y.val = 0 := by simp [hF, nearKernel, hp]
        by_cases hB : y ∈ Bρ <;> by_cases hS : y ∈ Sε <;>
          simp [Set.indicator, hB, hS, hF0', hK0]
      · have hKne : Kc x y ≠ 0 := by rw [hKc, carrierKernel_of_ne hxy]; exact hp
        obtain ⟨-, -, hdr⟩ := carrierKernel_ne_zero_imp
          (fun ξ η h => pairKernel_eq_zero_of_cutoff_eq_zero h) cert.φ_zero cert.hT cert.hR
          (hKc ▸ hKne)
        have hmem : y ∈ Bρ ↔ y ∈ Sε := by
          show ε < C.rho ν x y ↔ ε < cert.T.d' x y
          rw [hdr]
        have hval : F y.val = a x.val * Kc x y * g y := by
          simp only [hF, nearKernel, hg_def, inputCarrier]
          rw [hKc, carrierKernel_of_ne hxy]
          ring
        by_cases hB : y ∈ Bρ
        · rw [indicator_of_mem hB, indicator_of_mem (hmem.mp hB), hval]
        · rw [indicator_of_notMem hB, indicator_of_notMem (fun h => hB (hmem.mpr h))]
  -- the integral over the carrier is the sum of the localized truncations
  have hz : ∀ z : cert.t,
      IntegrableOn (fun y => (dd.Q z).cutoffKernel x y * g y) Sε volume ∧
        (∫ y in Sε, (dd.Q z).cutoffKernel x y * g y) =
          H2.truncatedIntegral (volume : Measure C.Carrier) (ball (dd.Q z).z (dd.Q z).R)
            cert.T.d' (dd.Q z).cutoffKernel ε g x := fun z => by
    have h := localKernelData_truncation (dd.Q z) hδ (boundedHolder_Q_ball dd hg z) hε x
    rw [hμ] at h
    exact h
  have hΨ : (fun y : C.Carrier => a x.val * Kc x y * g y) =
      fun y => a x.val * ∑ z : cert.t, (dd.Q z).cutoffKernel x y * g y := by
    funext y
    rw [← hsum y, mul_assoc, Finset.sum_mul]
  have hΨint : IntegrableOn (fun y : C.Carrier => a x.val * Kc x y * g y) Sε volume ∧
      (∫ y in Sε, a x.val * Kc x y * g y) =
        a x.val * ∑ z : cert.t, H2.truncatedIntegral (volume : Measure C.Carrier)
          (ball (dd.Q z).z (dd.Q z).R) cert.T.d' (dd.Q z).cutoffKernel ε g x := by
    rw [hΨ]
    refine ⟨(integrable_finsetSum _ (fun z _ => (hz z).1)).const_mul _, ?_⟩
    rw [integral_const_mul, integral_finsetSum _ (fun z _ => (hz z).1)]
    exact congrArg _ (Finset.sum_congr rfl fun z _ => (hz z).2)
  have hind : Bρ.indicator (fun y : C.Carrier => F y.val) =
      Sε.indicator (fun y : C.Carrier => a x.val * Kc x y * g y) := funext hstar
  refine ⟨?_, ?_⟩
  · refine hI.mpr ?_
    rw [← integrable_indicator_iff hBρm, hind, integrable_indicator_iff hSεm]
    exact hΨint.1
  · show (∫ η in {η | ε < C.rhoGauge ν x.val η}, F η) = _
    rw [hint, ← integral_indicator hBρm, hind, integral_indicator hSεm, hΨint.2]

/-- **The principal value of the near part exists and is
the finite sum of the local principal values** (the finite reconstruction formula): for a profile with
`ν(Θ)`-truncation, a cutoff `a` supported in `Fs` and `b` supported in `U`, every input `f` with
`b f` bounded Hölder on the balls of the cover has, at **every** `ξ`, integrable `ρ`-truncations of
`a(ξ) K^φ(ξ, η) b(η)` converging as `ε ↓ 0` to `nearOutput = a(ξ) ∑_j (T_j (b f))(ξ)`. -/
theorem hasRhoPV_near (dd : C.NearDataD cert D Γ) {a b f : (Fin (n + m) → ℝ) → ℝ}
    (hνg : C.G.IsHomogeneousGauge ν) (ha : ∀ ξ, a ξ ≠ 0 → ξ ∈ Fs)
    (hb0 : ∀ ξ, ξ ∉ C.U → b ξ = 0) {δ : ℝ≥0} (hδ : 0 < δ)
    (hg : ∀ z : cert.t, H2.BoundedHolder δ (ball z.1 cert.r) (C.inputCarrier b f))
    (ξ : Fin (n + m) → ℝ) :
    HasRhoPV (C.rhoGauge ν) (C.nearKernel ν D Γ cert.φ a b) f ξ (nearOutput dd a b f ξ) := by
  classical
  have hμ : cert.S.μ = volume := cert.hS.μ_eq
  by_cases hax : a ξ = 0
  · have hk : ∀ η, C.nearKernel ν D Γ cert.φ a b ξ η = 0 := fun η => by simp [nearKernel, hax]
    have hout : nearOutput dd a b f ξ = 0 := by
      unfold nearOutput
      split_ifs <;> simp [hax]
    refine ⟨fun ε _ => ?_, ?_⟩
    · simp [hk]
    · simp only [rhoTruncated, hk, zero_mul, integral_zero, hout]
      exact tendsto_const_nhds
  · have hξFs := ha ξ hax
    have hξU : ξ ∈ C.U := by
      obtain ⟨y, -, rfl⟩ := cert.Fs_sub hξFs
      exact y.val_mem
    set x : C.Carrier := Carrier.mk ξ hξU with hxdef
    have hxξ : x.val = ξ := rfl
    refine ⟨fun ε hε => ?_, ?_⟩
    · have h := (rhoTruncated_near_eq dd (a := a) hνg hb0 hδ hg (x := x) (by rw [hxξ]; exact hξFs) hε).1
      rw [hxξ] at h
      exact h
    · have hlim := tendsto_finsetSum (Finset.univ : Finset cert.t)
        (fun z _ => by
          have h := localKernelData_principalValue_limit (dd.Q z) hδ
            (boundedHolder_Q_ball dd hg z) x
          rw [hμ] at h
          exact h)
      have hlim' := hlim.const_mul (a ξ)
      have hval : nearOutput dd a b f ξ =
          a ξ * ∑ z : cert.t, (dd.Q z).principalValue (C.inputCarrier b f) x := by
        simp only [nearOutput, hξU, ↓reduceDIte, hxdef]
      rw [hval]
      refine hlim'.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have h := (rhoTruncated_near_eq dd (a := a) hνg hb0 hδ hg (x := x) (by rw [hxξ]; exact hξFs)
        (show 0 < ε from hε)).2
      rw [hxξ] at h
      exact h.symm

end LiftedChart
end RothschildStein.P1
