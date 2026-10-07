-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuityReconstructionHolder
public import RothschildStein.P1.TypeKernel
public import RothschildStein.H2.CompactTruncationSum

/-!
# Reconstruction: near part, far part and the finite localization

One original degree-2 principal term `a(ξ) K(ξ, η) b(η)`, `K(ξ, η) = (D^{ξ,η} Γ)(Θ(η, ξ))`, is
split along the radial profile `φ(ρ)` of the localization certificate into

* the **far part** `farKernel`, the part outside the radial profile, `a b (D Γ)(Θ) (1 - φ(ρ))`:
  a smooth, compactly supported, off-diagonal kernel (`farKernel_isRegular`: it is a regular
  kernel of every budget in the sense of the type calculus, `IsRegularKernel`);
* the **near part** `nearKernel = a(ξ) K^φ(ξ, η) b(η)`, with `K^φ = pairKernel` the kernel cut
  off by `φ(ρ)` (the kernel split into `K₀ + K₁` by the singular split).

`nearKernel_add_farKernel` is the algebraic identity `φ + (1 - φ) = 1`.

The finite reconstruction formula `T_near f = a ∑_j T_j (b f)` uses the localization
`(t, χ_j, ψ_j)` at the common localization radius. A `NearCertificate` bundles the geometric choices (the metric-measure
certificate, the symmetric truncation `d'`, the common radius `r`, the admissible support radius
`R'`, the smooth radial profile `φ`, the finite cover and cutoffs); `NearDataD` adds the Data D
(`H2.LocalKernelData`) of every doubled ball with its H2 transpose. `sum_cutoffKernel_eq` is the
kernel form of the finite reconstruction formula: for `ξ` in the output support,
`∑_j χ_j(ξ) K(ξ, η) ψ_j(η) = K(ξ, η)`, because `χ_j(ξ) K(ξ, η) ≠ 0` forces `η ∈ B(z_j, r/2)` where
`ψ_j = 1`.
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

/-- The **near part** of the principal term
`a(ξ) (D^{ξ,η} Γ)(Θ(η, ξ)) b(η)`: the kernel cut off by the radial profile `φ(ν(Θ(η, ξ)))`,
`a(ξ) K^φ(ξ, η) b(η)`, `K^φ = pairKernel` (the kernel that the singular split writes as `K₀ + K₁`). -/
def nearKernel (ν : (Fin (n + m) → ℝ) → ℝ)
    (D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m))
    (Γ : (Fin (n + m) → ℝ) → ℝ) (φ : ℝ → ℝ) (a b : (Fin (n + m) → ℝ) → ℝ)
    (ξ η : Fin (n + m) → ℝ) : ℝ :=
  a ξ * C.pairKernel ν D Γ φ ξ η * b η

/-- The **far part** of the principal term, outside the
radial profile: `a(ξ) b(η) (D^{ξ,η} Γ)(Θ(η, ξ)) (1 - φ(ν(Θ(η, ξ))))`. -/
def farKernel (ν : (Fin (n + m) → ℝ) → ℝ)
    (D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m))
    (Γ : (Fin (n + m) → ℝ) → ℝ) (φ : ℝ → ℝ) (a b : (Fin (n + m) → ℝ) → ℝ)
    (ξ η : Fin (n + m) → ℝ) : ℝ :=
  a ξ * b η * ((D ξ η).apply Γ (C.Θ η ξ) * (1 - φ (ν (C.Θ η ξ))))

variable {C}

/-- The near and far parts add up to the principal term. -/
theorem nearKernel_add_farKernel (ν : (Fin (n + m) → ℝ) → ℝ)
    (D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m))
    (Γ : (Fin (n + m) → ℝ) → ℝ) (φ : ℝ → ℝ) (a b : (Fin (n + m) → ℝ) → ℝ)
    (ξ η : Fin (n + m) → ℝ) :
    C.nearKernel ν D Γ φ a b ξ η + C.farKernel ν D Γ φ a b ξ η =
      a ξ * b η * (D ξ η).apply Γ (C.Θ η ξ) := by
  unfold nearKernel farKernel pairKernel cutoffKernel
  ring

/-- The far part vanishes unless both cutoffs do not. -/
theorem farKernel_eq_zero_of_left {ν : (Fin (n + m) → ℝ) → ℝ}
    {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}
    {Γ : (Fin (n + m) → ℝ) → ℝ} {φ : ℝ → ℝ} {a b : (Fin (n + m) → ℝ) → ℝ}
    {ξ η : Fin (n + m) → ℝ} (h : a ξ = 0) : C.farKernel ν D Γ φ a b ξ η = 0 := by
  simp [farKernel, h]

/-- The far part vanishes unless both cutoffs do not. -/
theorem farKernel_eq_zero_of_right {ν : (Fin (n + m) → ℝ) → ℝ}
    {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}
    {Γ : (Fin (n + m) → ℝ) → ℝ} {φ : ℝ → ℝ} {a b : (Fin (n + m) → ℝ) → ℝ}
    {ξ η : Fin (n + m) → ℝ} (h : b η = 0) : C.farKernel ν D Γ φ a b ξ η = 0 := by
  simp [farKernel, h]

/-- **The far part is smooth and compactly supported**
(proof of the finite reconstruction formula: "its part outside the radial profile is a smooth, compactly supported
off-diagonal kernel"): for `a, b` smooth with compact support in `U`, a profile `φ` with `φ = 1`
on `(-∞, ε]` (so `1 - φ(ρ)` vanishes near the diagonal, where `Γ` is singular), the far kernel is
jointly smooth on `ℝ^{n+m} × ℝ^{n+m}` with compact support in `supp a × supp b`. -/
theorem contDiff_farKernel {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (hνs : ContDiffOn ℝ (⊤ : ℕ∞) ν {(0 : Fin (n + m) → ℝ)}ᶜ)
    {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}
    (SF : SplitFamily C.G D) {Γ : (Fin (n + m) → ℝ) → ℝ}
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin (n + m) → ℝ)}ᶜ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {ε : ℝ} (hε : 0 < ε) (hφ1 : ∀ t, t ≤ ε → φ t = 1)
    {a b : (Fin (n + m) → ℝ) → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hac : HasCompactSupport a) (hbc : HasCompactSupport b) (haU : tsupport a ⊆ C.U)
    (hbU : tsupport b ⊆ C.U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
        C.farKernel ν D Γ φ a b z.1 z.2) ∧
      HasCompactSupport (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
        C.farKernel ν D Γ φ a b z.1 z.2) ∧
      tsupport (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
        C.farKernel ν D Γ φ a b z.1 z.2) ⊆ tsupport a ×ˢ tsupport b := by
  set Kset : Set ((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) := tsupport a ×ˢ tsupport b with hKset
  have hKc : IsCompact Kset := hac.isCompact.prod hbc.isCompact
  have hKcl : IsClosed Kset := hKc.isClosed
  have hzero : ∀ z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ), z ∉ Kset →
      C.farKernel ν D Γ φ a b z.1 z.2 = 0 := by
    intro z hz
    rw [hKset, mem_prod, not_and_or] at hz
    rcases hz with h | h
    · exact farKernel_eq_zero_of_left (image_eq_zero_of_notMem_tsupport h)
    · exact farKernel_eq_zero_of_right (image_eq_zero_of_notMem_tsupport h)
  have hopenU : IsOpen {z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) |
      z.2.2 ≠ 0} := isOpen_ne_fun (continuous_snd.comp continuous_snd) continuous_const
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      C.farKernel ν D Γ φ a b z.1 z.2) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p ∈ Kset
    · have hξ : p.1 ∈ C.U := haU hp.1
      have hη : p.2 ∈ C.U := hbU hp.2
      have hΘ : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun q : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.Θ q.2 q.1) p := by
        have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
            C.Θ z.1 z.2) (p.2, p.1) :=
          C.theta_smooth.contDiffAt ((C.isOpen_U.prod C.isOpen_U).mem_nhds ⟨hη, hξ⟩)
        exact h1.comp p (contDiffAt_snd.prodMk contDiffAt_fst)
      by_cases hnu : ν (C.Θ p.2 p.1) < ε
      · have hcont : ContinuousAt
            (fun q : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => ν (C.Θ q.2 q.1)) p :=
          hν.1.continuousAt.comp hΘ.continuousAt
        have hev : ∀ᶠ q in 𝓝 p, ν (C.Θ q.2 q.1) < ε := hcont.eventually (gt_mem_nhds hnu)
        have h0 : (fun q : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
            C.farKernel ν D Γ φ a b q.1 q.2) =ᶠ[𝓝 p] fun _ => 0 :=
          hev.mono fun q hq => by simp [farKernel, hφ1 _ hq.le]
        exact contDiffAt_const.congr_of_eventuallyEq h0
      · have hne : C.Θ p.2 p.1 ≠ 0 := by
          intro h
          exact hnu (by rw [h, (hν.2.2.1 0).mpr rfl]; exact hε)
        have hmap : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
            (q.1, q.2, C.Θ q.2 q.1)) p :=
          contDiffAt_fst.prodMk (contDiffAt_snd.prodMk hΘ)
        have hD : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
            (D q.1 q.2).apply Γ (C.Θ q.2 q.1)) p := by
          have h1 := (SF.contDiffOn_kernelUncurry hΓ).contDiffAt
            (hopenU.mem_nhds (show ((p.1, p.2, C.Θ p.2 p.1) :
              (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) ∈
                {z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) | z.2.2 ≠ 0}
                from hne))
          have h2 := h1.comp p hmap
          exact h2
        have hνat : ContDiffAt ℝ (⊤ : ℕ∞) ν (C.Θ p.2 p.1) :=
          hνs.contDiffAt (isOpen_compl_singleton.mem_nhds hne)
        have hφat : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
            1 - φ (ν (C.Θ q.2 q.1))) p :=
          contDiffAt_const.sub (hφ.contDiffAt.comp p (hνat.comp p hΘ))
        have haat : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
            a q.1) p := ha.contDiffAt.comp p contDiffAt_fst
        have hbat : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
            b q.2) p := hb.contDiffAt.comp p contDiffAt_snd
        exact (haat.mul hbat).mul (hD.mul hφat)
    · have hev : ∀ᶠ q in 𝓝 p, q ∈ Kset ᶜ := hKcl.isOpen_compl.mem_nhds hp
      have h0 : (fun q : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
          C.farKernel ν D Γ φ a b q.1 q.2) =ᶠ[𝓝 p] fun _ => 0 :=
        hev.mono fun q hq => hzero q hq
      exact contDiffAt_const.congr_of_eventuallyEq h0
  refine ⟨hsmooth, ?_, ?_⟩
  · exact HasCompactSupport.intro hKc hzero
  · refine closure_minimal (fun z hz => ?_) hKcl
    by_contra hzK
    exact hz (hzero z hzK)

/-- **The far part is a regular kernel of every budget**
(`IsRegularKernel`): jointly smooth, compactly supported in `V × V`. Here `a, b ∈ C_c^∞(V)`
are the test cutoffs of the principal term, `V ⊆ U` the cutoff region of the frame, and `φ` a
profile equal to one near zero. -/
theorem farKernel_isRegular (F : KernelFrame (n + m)) (hV : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (hνs : ContDiffOn ℝ (⊤ : ℕ∞) ν {(0 : Fin (n + m) → ℝ)}ᶜ)
    {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}
    (SF : SplitFamily C.G D) {Γ : (Fin (n + m) → ℝ) → ℝ}
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin (n + m) → ℝ)}ᶜ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {ε : ℝ} (hε : 0 < ε) (hφ1 : ∀ t, t ≤ ε → φ t = 1)
    (a b : TestFunction F.V ℝ (⊤ : ℕ∞)) (m' : ℕ) :
    IsRegularKernel F m' (C.farKernel ν D Γ φ a b) := by
  obtain ⟨h1, h2, h3⟩ := contDiff_farKernel hν hνs SF hΓ hφ hε hφ1 a.contDiff b.contDiff
    a.hasCompactSupport b.hasCompactSupport (a.tsupport_subset.trans hV)
    (b.tsupport_subset.trans hV)
  exact ⟨h1.of_le (by exact_mod_cast le_top), h2, h3.trans (prod_mono a.tsupport_subset
    b.tsupport_subset)⟩

/-- The cut-off kernel vanishes where the radial profile does. -/
theorem pairKernel_eq_zero_of_cutoff_eq_zero {ν : (Fin (n + m) → ℝ) → ℝ}
    {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}
    {Γ : (Fin (n + m) → ℝ) → ℝ} {φ : ℝ → ℝ} {ξ η : Fin (n + m) → ℝ}
    (h : φ (ν (C.Θ η ξ)) = 0) : C.pairKernel ν D Γ φ ξ η = 0 := by
  simp [pairKernel, cutoffKernel, h]

variable (C)

/-- **The geometric certificate of a near part** for an output
support `Fs` and a homogeneous gauge `ν`: the metric-measure certificate `(Ω₀ ⋐ Ω₁ ⋐ Ω₂, κ)`
(`IsMetricMeasureCertificate`), the symmetric truncation distance `d'` (`IsRhoTruncation`),
a common radius `r < κ`, an admissible radial support radius `R'` (`IsAdmissibleRadius`), a smooth radial profile `φ` (`1` on `(-∞, R'/2]`, `0` on `[R', ∞)`), and the
finite localization `(t, χ_j, ψ_j)` of `Fs` (`IsLocalization`). All choices are independent of the
function acted on. -/
structure NearCertificate (ν : (Fin (n + m) → ℝ) → ℝ) (Fs : Set (Fin (n + m) → ℝ)) where
  /-- The locally doubling structure on the carrier. -/
  S : H2.LocDoubling C.Carrier
  vLo : ℝ
  vHi : ℝ
  hS : C.IsMetricMeasureCertificate S vLo vHi
  /-- The near-diagonal radius of the truncation certificate. -/
  τ : ℝ
  τ_pos : 0 < τ
  /-- The symmetric truncation distance `d' = ρ` on `{d < τ}`. -/
  T : H2.TruncDist S
  hT : C.IsRhoTruncation S ν τ T
  /-- The common localization radius. -/
  r : ℝ
  r_pos : 0 < r
  r_lt : r < S.κ
  /-- The common radial support radius. -/
  R' : ℝ
  hR : C.IsAdmissibleRadius S T ν τ r R'
  /-- The smooth radial profile. -/
  φ : ℝ → ℝ
  φ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ
  φ_one : ∀ t, t ≤ R' / 2 → φ t = 1
  φ_zero : ∀ t, R' ≤ t → φ t = 0
  /-- The finite cover and the partition of unity. -/
  t : Finset C.Carrier
  χ : C.Carrier → (Fin (n + m) → ℝ) → ℝ
  ψ : C.Carrier → (Fin (n + m) → ℝ) → ℝ
  loc : C.IsLocalization S Fs r t χ ψ
  Fs_sub : Fs ⊆ Carrier.val '' S.Ω₀

variable {C}

/-- **Existence of the geometric certificate** for every compact output support
`Fs ⊆ U`, every homogeneous gauge `ν` with `ν(-u) = ν(u)` and every `τ > 0`
(`exists_h2Certificate`, a radial profile and the finite localization). -/
theorem exists_nearCertificate {Fs : Set (Fin (n + m) → ℝ)} (hF : IsCompact Fs) (hFU : Fs ⊆ C.U)
    {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν) (hsym : ∀ u, ν (-u) = ν u)
    {τ : ℝ} (hτ : 0 < τ) : Nonempty (C.NearCertificate ν Fs) := by
  obtain ⟨S, vLo, vHi, hcert, hKS, h⟩ := C.exists_h2Certificate hF hFU
  obtain ⟨T, hT, hrest⟩ := h ν hν hsym τ hτ
  have hr : 0 < S.κ / 2 := by linarith [S.κ_pos]
  obtain ⟨⟨R', hR⟩, hloc⟩ := hrest (S.κ / 2) hr (by linarith [S.κ_pos])
  obtain ⟨φ, hφ, hφ1, hφ0⟩ := exists_radial_profile hR.pos
  obtain ⟨t, χ, ψ, hl⟩ := hloc Fs hF hKS
  exact ⟨⟨S, vLo, vHi, hcert, τ, hτ, T, hT, S.κ / 2, hr, by linarith [S.κ_pos], R', hR, φ, hφ,
    hφ1, hφ0, t, χ, ψ, hl, hKS⟩⟩

/-- **The Data D of every doubled ball** of a near certificate, with the H2
transpose datum: for each centre `z_j` an `H2.LocalKernelData` `Q_j` on `B(z_j, 2r)` whose pieces
are `K₀, K₁` of the cut-off kernel (cutoffs `χ_j, ψ_j`), and its `H2.TransposeData` `P_j`. -/
structure NearDataD {ν : (Fin (n + m) → ℝ) → ℝ} {Fs : Set (Fin (n + m) → ℝ)}
    (cert : C.NearCertificate ν Fs)
    (D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m))
    (Γ : (Fin (n + m) → ℝ) → ℝ) where
  Q : cert.t → H2.LocalKernelData cert.S cert.T
  P : ∀ z, H2.TransposeData (Q z)
  split : ∀ z : cert.t, C.IsSplitData (Q z) z.1 cert.r cert.R'
    (fun x : C.Carrier => cert.χ z.1 x.val) (fun x : C.Carrier => cert.ψ z.1 x.val)
    (C.splitK0 ν D Γ cert.φ) (C.splitK1 ν D Γ cert.φ)
  P_exponents : ∀ z : cert.t,
    (P z).data.β₀ = 1 ∧ (P z).data.β = 1 ∧ (P z).data.ν = 1

/-- **Existence of the Data D of a near
certificate**, both for the original splitting and for the separate transposed splitting
`Kᵗ = K'₀ + K'₁` of `(transposeFamily D, Γ*)` with the exchanged cutoffs
(`exists_dataD_of_localization`). -/
theorem exists_nearDataD {q : ℕ} {H : H1.StandingHypotheses C.G q}
    (hQ : 2 < (C.G.homogeneousDimension : ℝ)) (hsym : ∀ u, H.norm (-u) = H.norm u)
    (hνs : H.norm.Smooth) (Γ : H1.FundamentalKernel C.G H) (hΓ : H1.KernelShellCancellation Γ)
    {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}
    (SF : SplitFamily C.G D) {Fs : Set (Fin (n + m) → ℝ)} (cert : C.NearCertificate H.norm Fs) :
    ∃ dd : C.NearDataD cert D Γ, ∀ z : cert.t,
      C.IsSplitData (dd.P z).data z.1 cert.r cert.R'
        (fun x : C.Carrier => cert.ψ z.1 x.val) (fun x : C.Carrier => cert.χ z.1 x.val)
        (C.splitK0 H.norm (transposeFamily D) (Γ.reflection hQ) cert.φ)
        (C.splitK1 H.norm (transposeFamily D) (Γ.reflection hQ) cert.φ) := by
  have h : ∀ z : cert.t, ∃ (Q : H2.LocalKernelData cert.S cert.T) (P : H2.TransposeData Q),
      C.IsSplitData Q z.1 cert.r cert.R' (fun x : C.Carrier => cert.χ z.1 x.val)
        (fun x : C.Carrier => cert.ψ z.1 x.val) (C.splitK0 H.norm D Γ cert.φ)
        (C.splitK1 H.norm D Γ cert.φ) ∧
      C.IsSplitData P.data z.1 cert.r cert.R' (fun x : C.Carrier => cert.ψ z.1 x.val)
        (fun x : C.Carrier => cert.χ z.1 x.val)
        (C.splitK0 H.norm (transposeFamily D) (Γ.reflection hQ) cert.φ)
        (C.splitK1 H.norm (transposeFamily D) (Γ.reflection hQ) cert.φ) := fun z =>
    C.exists_dataD_of_localization hQ hsym hνs Γ hΓ SF (cert.φ_smooth.of_le (by simp))
      (ε := cert.R' / 2) (by linarith [cert.hR.pos]) (fun t _ ht => cert.φ_one t ht.le)
      cert.φ_zero cert.hS cert.hT cert.hR cert.r_pos cert.r_lt cert.loc z.2
  choose Q P hQP using h
  exact ⟨⟨Q, P, fun z => (hQP z).1,
    fun z => ⟨(hQP z).2.β₀_eq, (hQP z).2.β_eq, (hQP z).2.ν_eq⟩⟩, fun z => (hQP z).2⟩

section KernelIdentity

variable {ν : (Fin (n + m) → ℝ) → ℝ} {Fs : Set (Fin (n + m) → ℝ)}
  {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}
  {Γ : (Fin (n + m) → ℝ) → ℝ} {cert : C.NearCertificate ν Fs}

/-- The H2 sum kernel `K₀ + K₁` of a Data D of the split is the carrier
kernel of the cut-off kernel (`K = K₀ + K₁` on `U × U`, value `0` on the diagonal). -/
theorem sumKernel_eq_carrierKernel_pair {z : C.Carrier} {r R' : ℝ} {a b : C.Carrier → ℝ}
    {Q : H2.LocalKernelData cert.S cert.T}
    (h : C.IsSplitData Q z r R' a b (C.splitK0 ν D Γ cert.φ) (C.splitK1 ν D Γ cert.φ))
    (x y : C.Carrier) :
    Q.sumKernel x y = C.carrierKernel (C.pairKernel ν D Γ cert.φ) x y := by
  unfold H2.LocalKernelData.sumKernel
  rw [h.K₀_eq, h.K₁_eq]
  by_cases hxy : x = y
  · subst hxy
    simp [carrierKernel_self]
  · rw [carrierKernel_of_ne hxy, carrierKernel_of_ne hxy, carrierKernel_of_ne hxy]
    exact (pairKernel_eq_splitK0_add_splitK1 x.val_mem y.val_mem).symm

/-- **The kernel form of the finite reconstruction formula**: for `x` in
the output support `Fs`, the localized kernels `χ_j(x) K(x, y) ψ_j(y)` of the finite cover add up
to `K(x, y)`. Indeed `χ_j(x) K(x, y) ≠ 0` forces `x ∈ B(z_j, r/4)` and `d'(x, y) < R'`, hence
`y ∈ B(z_j, r/2)` where `ψ_j = 1`; and `∑_j χ_j = 1` on `Fs`. -/
theorem sum_cutoffKernel_eq (dd : C.NearDataD cert D Γ) (x y : C.Carrier) (hx : x.val ∈ Fs) :
    ∑ z : cert.t, (dd.Q z).cutoffKernel x y =
      C.carrierKernel (C.pairKernel ν D Γ cert.φ) x y := by
  classical
  set Kc := C.carrierKernel (C.pairKernel ν D Γ cert.φ) x y with hKc
  have hterm : ∀ z : cert.t,
      (dd.Q z).cutoffKernel x y = cert.χ z.1 x.val * Kc * cert.ψ z.1 y.val := by
    intro z
    rw [H2.LocalKernelData.cutoffKernel_eq_product, (dd.split z).a_eq, (dd.split z).b_eq,
      sumKernel_eq_carrierKernel_pair (dd.split z)]
  by_cases hK : Kc = 0
  · simp [hterm, hK]
  · have hterm' : ∀ z : cert.t, (dd.Q z).cutoffKernel x y = cert.χ z.1 x.val * Kc := by
      intro z
      rw [hterm z]
      by_cases hχ : cert.χ z.1 x.val = 0
      · simp [hχ]
      · have hxs : x.val ∈ tsupport (cert.χ z.1) := subset_tsupport _ hχ
        obtain ⟨x', hx', hxx'⟩ := cert.loc.χ_support z.1 z.2 hxs
        have hx'x : x' = x := Carrier.val_injective hxx'
        subst hx'x
        obtain ⟨-, hd', -⟩ := carrierKernel_ne_zero_imp
          (fun ξ η h => pairKernel_eq_zero_of_cutoff_eq_zero h) cert.φ_zero cert.hT cert.hR hK
        have hy : y ∈ ball z.1 (cert.r / 2) := cert.hR.mem_ball_half cert.hT hx' hd'
        rw [cert.loc.ψ_eq_one z.1 z.2 y.val ⟨y, hy, rfl⟩, mul_one]
    rw [Finset.sum_congr rfl (fun z _ => hterm' z), ← Finset.sum_mul]
    obtain ⟨N, -, hFN, hN⟩ := cert.loc.sum_eq_one
    have h1 : ∑ z : cert.t, cert.χ z.1 x.val = 1 := by
      rw [Finset.sum_coe_sort cert.t (fun z => cert.χ z x.val)]
      exact hN _ (hFN hx)
    rw [h1, one_mul]

end KernelIdentity

end LiftedChart

namespace PrincipalTerm

variable {N : ℕ} {F : KernelFrame N}

/-- A principal term of degree `2` whose frame has the model group `G` is a `SplitFamily`
(the hypotheses of the singular split). -/
def toSplitFamily (t : PrincipalTerm F) {G : HomogeneousGroup N} (hG : F.G = G)
    (hdeg : t.degree = 2) : SplitFamily G t.D where
  indices := t.indices
  indices_eq := t.indices_eq
  coefficient_smooth := t.coefficient_smooth
  homogeneous ξ η := by
    subst hG
    have h := t.homogeneous ξ η
    rwa [hdeg] at h

end PrincipalTerm

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- **A principal term is near plus far**: if
the frame of the term has the chart's two-point map and the pole of the term is `Γ`, its kernel
`a(ξ) b(η) (D^{ξ,η} Γ)(Θ(η, ξ))` is the sum of the near and far parts. -/
theorem principalTerm_kernel_eq_near_add_far {F : KernelFrame (n + m)} (t : PrincipalTerm F)
    (hΘ : F.Θ = C.Θ) {Γ : (Fin (n + m) → ℝ) → ℝ} (hpole : F.pole t.star = Γ)
    (ν : (Fin (n + m) → ℝ) → ℝ) (φ : ℝ → ℝ) (ξ η : Fin (n + m) → ℝ) :
    t.kernel ξ η = C.nearKernel ν t.D Γ φ t.a t.b ξ η + C.farKernel ν t.D Γ φ t.a t.b ξ η := by
  rw [nearKernel_add_farKernel]
  simp [PrincipalTerm.kernel, hΘ, hpole]

end LiftedChart

end RothschildStein.P1
