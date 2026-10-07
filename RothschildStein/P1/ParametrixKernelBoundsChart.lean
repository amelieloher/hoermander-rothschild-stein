-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ParametrixKernelBoundsJets
public import RothschildStein.P1.KernelEstimatesChain
public import RothschildStein.G1.LocalProductFactorization

/-!
# Global smooth extensions of the chart data over a compact set

The kernel-estimate machinery consumes kernel families that are `C¹` on all of `{u ≠ 0}`, whereas the remainder
fields `R_{[i],η}(u)` of the lifted chart are smooth only on the open set `C.T`, and the lifted
fields `X̃_i` only on the lifted domain. For a compact `L ⊆ U` the structure `ChartExt C L` records
globally smooth extensions `Rt` of the remainders and `Xb` of the lifted fields that

* coincide with `R_{[i]}` on an open neighborhood `V` of `{(η, Θ(η, ξ)) : η, ξ ∈ L}` and with `X̃_i`
  on `U`;
* have the weighted symbol class of the remainders on every compact parameter set
  (`Rt_class`: the coordinates `Rt_{[i]}^j` have degree `w_j - w_i + 1`, by vanishing weighted
  jets, `WtSym.of_jets`).

The extension is `Rt = χ(η) f(η, u) R` with `f` a cutoff equal to `1` near the compact set and
supported in `T`, and `χ` a cutoff in `η` supported where `f ≡ 1` near `u = 0`: the jets of `Rt`
then vanish for all `η`, which is what makes the class available on every compact parameter set
(`HasWeightedBounds` quantifies over all compact sets).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace RothschildStein.P1

/-- A smooth cutoff, supported in an open set `T`, equal to one on a neighborhood of a
compact `S ⊆ T`. -/
theorem exists_cutoff_nhds {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {T S : Set X} (hT : IsOpen T) (hS : IsCompact S) (hST : S ⊆ T) :
    ∃ f : X → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ tsupport f ⊆ T ∧
      ∃ V : Set X, IsOpen V ∧ S ⊆ V ∧ ∀ x ∈ V, f x = 1 := by
  obtain ⟨Δ, hΔ, hΔT⟩ := hS.exists_cthickening_subset_open hT hST
  obtain ⟨f, hf, -, hf0, hf1⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed (n := (⊤ : ℕ∞))
    (s := (Metric.thickening Δ S)ᶜ) (t := Metric.cthickening (Δ / 2) S)
    Metric.isOpen_thickening.isClosed_compl Metric.isClosed_cthickening (by
      rw [Set.disjoint_compl_left_iff_subset]
      exact Metric.cthickening_subset_thickening' hΔ (by linarith) S)
  refine ⟨f, hf, ?_, Metric.thickening (Δ / 2) S, Metric.isOpen_thickening, ?_, ?_⟩
  · have h1 : Function.support f ⊆ Metric.thickening Δ S := by
      intro p hp
      by_contra hnp
      exact hp ((hf0 p).mp hnp)
    exact (closure_mono h1).trans ((Metric.closure_thickening_subset_cthickening Δ S).trans hΔT)
  · exact Metric.self_subset_thickening (by linarith) S
  · intro x hx
    exact (hf1 x).mp (Metric.thickening_subset_cthickening _ _ hx)

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The lifted domain is open. -/
theorem isOpen_liftedDomain : IsOpen C.O := by
  have hc : Continuous (basePoint : (Fin (n + m) → ℝ) → Fin n → ℝ) :=
    continuous_pi (fun j => continuous_apply _)
  exact hΩ.preimage hc

/-- **Global extensions of the chart data over a compact set `L ⊆ U`.** `Rt i` extends
the remainder field `R_{[i]}` and `Xb i` the lifted field `X̃_i` to globally smooth maps; `Rt`
agrees with `R_{[i]}` on the open set `V ⊇ {(η, Θ(η, ξ)) : η, ξ ∈ L}`, `Xb` agrees with `X̃_i` on
`U`, and the coordinates of `Rt_{[i]}` are symbols of degree `w_j - w_i + 1` on every compact
parameter set (vanishing weighted jets). -/
structure ChartExt (L : Set (Fin (n + m) → ℝ)) where
  /-- The extended remainder fields. -/
  Rt : Fin k → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ)
  /-- The extended lifted fields. -/
  Xb : Fin k → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ)
  /-- The open set where `Rt = R`. -/
  V : Set ((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ))
  isOpen_V : IsOpen V
  mem_V : ∀ η ∈ L, ∀ ξ ∈ L, (η, C.Θ η ξ) ∈ V
  Rt_eq : ∀ i, ∀ p ∈ V, Rt i p.1 p.2 = C.R [i] p.1 p.2
  Rt_smooth : ∀ i j, ContDiff ℝ (⊤ : ℕ∞)
    (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => Rt i p.1 p.2 j)
  Xb_smooth : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun ξ : Fin (n + m) → ℝ => Xb i ξ j)
  Xb_eq : ∀ i, ∀ ξ ∈ C.U, Xb i ξ = C.Xl i ξ
  Rt_class : ∀ (i : Fin k) (j : Fin (n + m))
    (K : Set ((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ))), IsCompact K → ∀ R : ℝ, 0 < R →
      ∀ dp : ℕ, WtSym C.G K R dp ((C.G.weight j : ℤ) - ((w i : ℕ) : ℤ) + 1)
        (fun z => Rt i z.2.1 z.2.2 j)

/-- The extensions exist for every compact `L ⊆ U`. -/
theorem exists_chartExt {L : Set (Fin (n + m) → ℝ)} (hL : IsCompact L) (hLU : L ⊆ C.U) :
    Nonempty (C.ChartExt L) := by
  -- the compact set of two-point values and its cutoff
  let S₁ : Set ((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) :=
    (fun p => (p.1, C.Θ p.1 p.2)) '' (L ×ˢ L)
  have hS₁ : IsCompact S₁ := (hL.prod hL).image_of_continuousOn
    (continuousOn_fst.prodMk (C.theta_continuousOn.mono (Set.prod_mono hLU hLU)))
  have hS₁T : S₁ ⊆ C.T := by
    rintro _ ⟨p, hp, rfl⟩
    exact C.mem_T_theta (hLU hp.1) (hLU hp.2)
  obtain ⟨f₁, hf₁, hf₁T, V₁, hV₁o, hS₁V₁, hV₁⟩ := exists_cutoff_nhds C.isOpen_T hS₁ hS₁T
  -- the parameters where the cutoff is one near `u = 0`
  have hOo : IsOpen {η : Fin (n + m) → ℝ | (η, (0 : Fin (n + m) → ℝ)) ∈ V₁} :=
    hV₁o.preimage (continuous_id.prodMk continuous_const)
  have hLO : L ⊆ {η : Fin (n + m) → ℝ | (η, (0 : Fin (n + m) → ℝ)) ∈ V₁} := by
    intro η hη
    refine hS₁V₁ ⟨(η, η), ⟨hη, hη⟩, ?_⟩
    exact Prod.ext rfl (C.chart η (hLU hη)).2.2.2.2
  obtain ⟨χ, hχ, hχT, W₀, hW₀o, hLW₀, hW₀⟩ := exists_cutoff_nhds hOo hL hLO
  -- the cutoff of the lifted fields
  obtain ⟨χX, hχX, hχXT, VX, hVXo, hSVX, hVX⟩ :=
    exists_cutoff_nhds C.isOpen_liftedDomain C.isCompact_closure_U C.closure_U_subset
  refine ⟨⟨fun i η u => (χ η * f₁ (η, u)) • C.R [i] η u, fun i ξ => χX ξ • C.Xl i ξ,
    V₁ ∩ Prod.fst ⁻¹' W₀, hV₁o.inter (hW₀o.preimage continuous_fst), ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro η hη ξ hξ
    exact ⟨hS₁V₁ ⟨(η, ξ), ⟨hη, hξ⟩, rfl⟩, hLW₀ hη⟩
  · intro i p hp
    show (χ p.1 * f₁ (p.1, p.2)) • C.R [i] p.1 p.2 = C.R [i] p.1 p.2
    rw [hW₀ p.1 hp.2, hV₁ (p.1, p.2) hp.1, one_mul, one_smul]
  · intro i j
    have hG : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.R [i] p.1 p.2 j) C.T :=
      (contDiffOn_pi.mp (C.remainder_smooth [i])) j
    have hφ : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => χ p.1 * f₁ p) :=
      (hχ.comp contDiff_fst).mul hf₁
    have hsupp : tsupport (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => χ p.1 * f₁ p) ⊆ C.T :=
      (tsupport_mul_subset_right (f := fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => χ p.1)
        (g := f₁)).trans hf₁T
    exact RothschildStein.G1.cutoff_smul_contDiff C.isOpen_T _ hG _ hφ hsupp
  · intro i j
    have hG : ContDiffOn ℝ (⊤ : ℕ∞) (fun ξ : Fin (n + m) → ℝ => C.Xl i ξ j) C.O :=
      (contDiffOn_pi.mp (C.lift_smooth i)) j
    exact RothschildStein.G1.cutoff_smul_contDiff C.isOpen_liftedDomain _ hG χX hχX hχXT
  · intro i ξ hξ
    show χX ξ • C.Xl i ξ = C.Xl i ξ
    rw [hVX ξ (hSVX (subset_closure hξ)), one_smul]
  · intro i j K' hK' R hR dp
    set b : ℤ := (C.G.weight j : ℤ) - ((w i : ℕ) : ℤ) + 1 with hb
    have hF₀ : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => f₁ p * C.R [i] p.1 p.2 j) := by
      have := RothschildStein.G1.cutoff_smul_contDiff C.isOpen_T
        (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.R [i] p.1 p.2 j)
        ((contDiffOn_pi.mp (C.remainder_smooth [i])) j) f₁ hf₁ hf₁T
      simpa [smul_eq_mul] using this
    have hww : wordWeight w [i] = ((w i : ℕ)) := by simp [wordWeight]
    have hjet : ∀ η ∈ {η : Fin (n + m) → ℝ | (η, (0 : Fin (n + m) → ℝ)) ∈ V₁},
        WtJetsVanish C.G b (fun u => f₁ (η, u) * C.R [i] η u j) := by
      intro η hη J hJ
      have hη0 : f₁ (η, 0) = 1 := hV₁ _ hη
      have hηT : (η, (0 : Fin (n + m) → ℝ)) ∈ C.T :=
        hf₁T (subset_tsupport f₁ (Function.mem_support.mpr (by rw [hη0]; exact one_ne_zero)))
      have hηU : η ∈ C.U := hηT.1
      have hev : (fun u => f₁ (η, u) * C.R [i] η u j) =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)]
          fun u => C.R [i] η u j := by
        have hmem : {u : Fin (n + m) → ℝ | (η, u) ∈ V₁} ∈ 𝓝 (0 : Fin (n + m) → ℝ) :=
          (hV₁o.preimage (continuous_const.prodMk continuous_id)).mem_nhds hη
        filter_upwards [hmem] with u hu
        rw [hV₁ _ hu, one_mul]
      rw [(rsPartial_eventuallyEq J hev).eq_of_nhds]
      have hwt := C.remainder_weight [i] (List.cons_ne_nil _ _) η hηU
      refine hwt j J ?_
      rw [hww]
      omega
    set K₁ : Set ((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) :=
      K' ∩ {p | p.2 ∈ tsupport χ} with hK₁def
    have hK₁ : IsCompact K₁ := hK'.inter_right ((isClosed_tsupport χ).preimage continuous_snd)
    have hmain := WtSym.of_jets (G := C.G) hK₁ hR hOo (fun p hp => hχT hp.2) b.toNat
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => f₁ p * C.R [i] p.1 p.2 j) rfl hF₀ hjet dp
    have h2 : WtSym C.G K₁ R dp b
        (fun z : KZ (n + m) => χ z.2.1 * (f₁ z.2 * C.R [i] z.2.1 z.2.2 j)) :=
      (WtSym.mul (WtSym.param (G := C.G) (R := R) hK₁
        (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => χ p.2) (hχ.comp contDiff_snd)) hmain).degree_congr
        (zero_add b)
    have h3 : WtSym C.G K' R dp b
        (fun z : KZ (n + m) => χ z.2.1 * (f₁ z.2 * C.R [i] z.2.1 z.2.2 j)) := by
      refine WtSym.of_support (W := (tsupport χ)ᶜ) (isClosed_tsupport χ).isOpen_compl
        (fun p hp => ?_) (fun z hz => ?_) h2
      · by_cases h : p.2 ∈ tsupport χ
        · exact Or.inl ⟨hp, h⟩
        · exact Or.inr h
      · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
    refine WtSym.congr (fun z _ => ?_) h3
    simp [smul_eq_mul, mul_assoc]

end LiftedChart

end RothschildStein.P1
