-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeightedPatchCoefficientType
public import RothschildStein.P1.LocalExtensionRegularKernel
public import RothschildStein.P1.TypeClosure

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.P1

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- A coefficient smooth only on its actual
open chart domain, with the required local weighted jets on the cutoff
supports, yields an actual type-λ kernel. The proof constructs the
extension, its finite sharp Taylor decomposition, and the smooth annular
difference; no global coefficient smoothness or type decomposition is
assumed (BB Lemma 11.16 and the proof of Lemma 11.18, pp. 548–549). -/
theorem LiftedChart.isTypeKernel_local_weighted_coefficient_partial
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (star : Bool) (α : Fin (n + m) → ℕ) (low lam : ℕ)
    (hdegree : ((∑ j, F.G.weight j * α j : ℕ) : ℤ) - (low : ℤ) ≤ 2 - (lam : ℤ))
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole star (F.G.dilate r u) =
        r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole star u)
    (a b : TestFunction F.V ℝ (⊤ : ℕ∞))
    (T : Set (((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) × (Fin (n + m) → ℝ)))
    (hT : IsOpen T)
    (A : ((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) × (Fin (n + m) → ℝ) → ℝ)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A T)
    (hTzero : ∀ p ∈ tsupport a ×ˢ tsupport b, (p, (0 : Fin (n + m) → ℝ)) ∈ T)
    (hTθ : ∀ p ∈ C.U ×ˢ C.U, (p, F.Θ p.2 p.1) ∈ T)
    (hjet : ∀ p ∈ tsupport a ×ˢ tsupport b, ∀ I : List (Fin (n + m)),
      (I.map F.G.weight).sum < low → rsPartial I (fun u => A (p, u)) 0 = 0) :
    IsTypeKernel F lam (fun ξ η => a ξ * b η *
      (A ((ξ, η), F.Θ η ξ) * euclideanPartial α (F.pole star) (F.Θ η ξ))) := by
  obtain ⟨B, hB, ε, hε, he⟩ := exists_global_extension_generic_parameter T hT A hA
    (tsupport a ×ˢ tsupport b) (a.hasCompactSupport.prod b.hasCompactSupport) hTzero
  have hjetB := extension_preserves_weighted_jets F.G A B
    (tsupport a ×ˢ tsupport b) ε hε he low hjet
  let B₁ : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) → ℝ :=
    fun q => B ((q.1, q.2.1), q.2.2)
  have hB₁ : ContDiff ℝ (⊤ : ℕ∞) B₁ :=
    hB.comp ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd)
  have hmain := C.isTypeKernel_patch_weighted_coefficient_partial F hΘ hVU star α low lam
    hdegree hΓ hhom a b B₁ hB₁ (fun ξ hξ η hη I hI => hjetB (ξ, η) ⟨hξ, hη⟩ I hI)
  let g := euclideanPartial α (F.pole star)
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) g {(0 : Fin (n + m) → ℝ)}ᶜ := by
    apply contDiffOn_iff_forall_nat_le.mpr
    intro j hj
    exact H1.contDiffOn_euclideanPartial_finite
      ⟨{(0 : Fin (n + m) → ℝ)}ᶜ, isOpen_compl_singleton⟩ α j (F.pole star)
      (hΓ.of_le (by simp))
  have hθ : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => F.Θ p.2 p.1)
      (C.U ×ˢ C.U) := by
    rw [hΘ]
    exact C.theta_smooth.comp (contDiffOn_snd.prodMk contDiffOn_fst)
      (fun _ hp => ⟨hp.2, hp.1⟩)
  have hAθ := hA.comp (contDiffOn_id.prodMk hθ) hTθ
  let r := fun ξ η => a ξ * b η *
    ((A ((ξ, η), F.Θ η ξ) - B ((ξ, η), F.Θ η ξ)) * g (F.Θ η ξ))
  have hregular : ∀ budget, IsRegularKernel F budget r := fun budget =>
    C.isRegularKernel_local_extension_difference F hΘ hVU budget a b A B hAθ hB g hg ε hε he
  have hr : IsTypeKernel F lam r := by
    intro budget
    refine ⟨{
      principal := []
      principal_degree := by simp
      regular := r
      regular_isRegular := hregular budget
      eq_off_diagonal := ?_ }⟩
    intro ξ η hne
    simp only [List.map_nil, List.sum_nil, zero_add]
  change IsTypeKernel F lam (fun ξ η => a ξ * b η *
    (B₁ (ξ, η, F.Θ η ξ) * g (F.Θ η ξ))) at hmain
  have hs := hmain.add hr
  have hsum : (fun ξ η => a ξ * b η *
      (B₁ (ξ, η, F.Θ η ξ) * g (F.Θ η ξ)) + r ξ η) =
      (fun ξ η => a ξ * b η * (A ((ξ, η), F.Θ η ξ) * g (F.Θ η ξ))) := by
    funext ξ η
    dsimp only [B₁, r]
    ring
  rw [hsum] at hs
  exact hs

end RothschildStein.P1
