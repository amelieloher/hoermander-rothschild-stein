-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.PartialJetSums
public import RothschildStein.L1.JetLeibnizFormula
public import RothschildStein.L1.CoordinateJetClasses
public import RothschildStein.L1.PrefixDerivative
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace Filter
open scoped Topology BigOperators
namespace RothschildStein.L1

/-- The second ordinary partial of a radial frame identity gives its
symmetric first-frame-jet cancellation at zero. -/
theorem radial_frame_first_partial_antisymmetry {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) (Z : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Z i) Ω)
    (hrad : ∀ u ∈ Ω, ∑ i, u i • Z i u = u) (i j k : Fin N) :
    rsPartial [j] (fun u => Z i u k) 0 + rsPartial [i] (fun u => Z j u k) 0 = 0 := by
  have hval (u : Fin N → ℝ) (hu : u ∈ Ω) : (∑ l, u l * Z l u k) = u k := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun (hrad u hu) k
  have he : (fun u : Fin N → ℝ => ∑ l, u l * Z l u k) =ᶠ[𝓝 (0 : Fin N → ℝ)]
      (fun u => u k) := Filter.Eventually.mono (Ω.isOpen.mem_nhds h0) hval
  have hj := (rsPartial_eventuallyEq [i,j] he).self_of_nhds
  rw [rsPartial_coordinate_of_two_le k [i,j] (by simp)] at hj
  change rsPartial [i,j] (fun u => ∑ l, u l * Z l u k) 0 = 0 at hj
  have hs (l : Fin N) : ContDiffOn ℝ (⊤ : ℕ∞) (fun u => u l * Z l u k) Ω :=
    (contDiffOn_apply ℝ ℝ l Ω).mul (contDiffOn_pi.mp (hZ l) k)
  rw [rsPartial_finset_sum_on Ω Finset.univ _ (fun l _ => hs l) [i,j] h0] at hj
  have hp (l : Fin N) : rsPartial [i,j] (fun u => u l * Z l u k) 0 =
      (Pi.single i (1 : ℝ) : Fin N → ℝ) l * rsPartial [j] (fun u => Z l u k) 0 +
      (Pi.single j (1 : ℝ) : Fin N → ℝ) l * rsPartial [i] (fun u => Z l u k) 0 := by
    rw [rsPartial_mul_eq_leibniz Ω (fun u => u l) (fun u => Z l u k)
      (contDiffOn_apply ℝ ℝ l Ω) (contDiffOn_pi.mp (hZ l) k) [i,j] 0 h0]
    simp only [jetLeibnizPartitions, List.map_cons, List.map_nil, List.map_append,
      List.sum_append, List.sum_cons, List.sum_nil]
    rw [rsPartial_coordinate_of_two_le l [i,j] (by simp),
      rsPartial_coordinate_single l i, rsPartial_coordinate_single l j]
    simp only [rsPartial, Pi.zero_apply, zero_mul, zero_add, add_zero]
  simp_rw [hp] at hj
  rw [Finset.sum_add_distrib] at hj
  simpa [Pi.single_apply] using hj

/-- The same cancellation is the actual Frechet derivative identity. -/
theorem radial_frame_first_fderiv_antisymmetry {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) (Z : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Z i) Ω)
    (hrad : ∀ u ∈ Ω, ∑ i, u i • Z i u = u) (i j : Fin N) :
    fderiv ℝ (Z i) 0 (Pi.single j 1) + fderiv ℝ (Z j) 0 (Pi.single i 1) = 0 := by
  have hi := ((hZ i).contDiffAt (Ω.isOpen.mem_nhds h0)).differentiableAt (by simp)
  have hj := ((hZ j).contDiffAt (Ω.isOpen.mem_nhds h0)).differentiableAt (by simp)
  ext k
  simp only [Pi.add_apply, Pi.zero_apply]
  rw [← fderiv_coordinate_apply (Z i) hi k (Pi.single j 1),
    ← fderiv_coordinate_apply (Z j) hj k (Pi.single i 1)]
  exact radial_frame_first_partial_antisymmetry Ω h0 Z hZ hrad i j k
end RothschildStein.L1
