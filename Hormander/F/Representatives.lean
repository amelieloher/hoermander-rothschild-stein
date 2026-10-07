-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Hormander.F

/-- In dimension zero, almost-everywhere representatives agree
pointwise wherever both patches contain the unique point. -/
theorem zeroDimensional_representatives_agree
    {U V : Set (Fin 0 → ℝ)} {f g u : (Fin 0 → ℝ) → ℝ}
    {x : Fin 0 → ℝ} (hx : x ∈ U ∩ V)
    (hfu : f =ᵐ[volume.restrict U] u)
    (hgu : g =ᵐ[volume.restrict V] u) :
    f x = g x := by
  classical
  have hvolume : (volume : Measure (Fin 0 → ℝ)) = Measure.dirac x := by
    simpa using (Measure.volume_pi_eq_dirac (ι := Fin 0) (α := fun _ => ℝ) (x := x))
  have hU : volume.restrict U = Measure.dirac x := by
    rw [hvolume, restrict_dirac]
    simp [hx.1]
  have hV : volume.restrict V = Measure.dirac x := by
    rw [hvolume, restrict_dirac]
    simp [hx.2]
  have hfx : f x = u x := by
    have h := hfu
    rw [hU] at h
    have h' : f =ᶠ[pure x] u := by simpa only [ae_dirac_eq] using h
    rcases h'.exists_mem with ⟨s, hs, heq⟩
    have hxs : x ∈ s := by simpa using hs
    exact heq hxs
  have hgx : g x = u x := by
    have h := hgu
    rw [hV] at h
    have h' : g =ᶠ[pure x] u := by simpa only [ae_dirac_eq] using h
    rcases h'.exists_mem with ⟨s, hs, heq⟩
    have hxs : x ∈ s := by simpa using hs
    exact heq hxs
  exact hfx.trans hgx.symm

/-- Continuous local representatives that agree almost everywhere agree
pointwise throughout their open overlap. -/
theorem localRepresentatives_agree_on_overlap {N : ℕ} (hN : 0 < N)
    {U V : Set (Fin N → ℝ)} (hU : IsOpen U) (hV : IsOpen V)
    {f g u : (Fin N → ℝ) → ℝ}
    (hf : ContinuousOn f U) (hg : ContinuousOn g V)
    (hfu : f =ᵐ[volume.restrict U] u)
    (hgu : g =ᵐ[volume.restrict V] u) : EqOn f g (U ∩ V) := by
  have _hN := hN
  have hfu' : f =ᵐ[volume.restrict (U ∩ V)] u :=
    ae_restrict_of_ae_restrict_of_subset (s := U ∩ V) (t := U) inter_subset_left hfu
  have hgu' : g =ᵐ[volume.restrict (U ∩ V)] u :=
    ae_restrict_of_ae_restrict_of_subset (s := U ∩ V) (t := V) inter_subset_right hgu
  have hfg : f =ᵐ[volume.restrict (U ∩ V)] g := hfu'.trans hgu'.symm
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hfg (hU.inter hV)
    (hf.mono inter_subset_left) (hg.mono inter_subset_right)

end Hormander.F
