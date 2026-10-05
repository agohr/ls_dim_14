import QuaternionicSymmetry.FourDimensionalHalfSpinHopfContinuous
import Mathlib.Analysis.Normed.Module.Normalize

/-! Compactness of the genuine projective complex spinor line is proved
from the ordinary unit sphere in finite-dimensional `ℂ²` and the canonical
quotient topology, independently of the Hopf target topology. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCompact

open scoped Quaternion Topology
open FourDimensionalHalfSpinProjective

noncomputable section

private abbrev UnitSpinor := Metric.sphere (0 : Spinor) 1

private theorem unit_ne_zero (v : UnitSpinor) : (v : Spinor) ≠ 0 := by
  have hv : ‖(v : Spinor)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using v.2
  intro hz
  rw [hz, norm_zero] at hv
  norm_num at hv

/-- Projectivization restricted to the compact unit sphere. -/
def unitProjective (v : UnitSpinor) : ProjectiveSpinor :=
  Projectivization.mk ℂ v.1 (unit_ne_zero v)

theorem unitProjective_continuous : Continuous unitProjective := by
  have hsub : Continuous (fun v : UnitSpinor =>
      (⟨v.1, unit_ne_zero v⟩ : {v : Spinor // v ≠ 0})) :=
    continuous_subtype_val.subtype_mk _
  exact (ComplexProjectiveTopology.continuous_mk 1).comp hsub

theorem unitProjective_surjective : Function.Surjective unitProjective := by
  intro p
  induction p using Projectivization.ind with
  | h v hv =>
    let u : Spinor := NormedSpace.normalize v
    have hu : ‖u‖ = 1 := NormedSpace.norm_normalize hv
    let s : UnitSpinor := ⟨u, by simpa [u] using hu⟩
    refine ⟨s, ?_⟩
    change Projectivization.mk ℂ u (unit_ne_zero s) =
      Projectivization.mk ℂ v hv
    apply (Projectivization.mk_eq_mk_iff' ℂ u v _ hv).2
    refine ⟨((‖v‖⁻¹ : ℝ) : ℂ), ?_⟩
    simpa [u, NormedSpace.normalize] using
      (RCLike.real_smul_eq_coe_smul (K := ℂ) (‖v‖⁻¹) v).symm

/-- Genuine compactness of `CP¹`, without transferring it through the
already constructed Hopf equivalence. -/
instance : CompactSpace ProjectiveSpinor := by
  letI : CompactSpace UnitSpinor :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Spinor) 1)
  have hs : IsCompact (Set.univ : Set UnitSpinor) := by
    exact isCompact_univ
  have hr : Set.range unitProjective = Set.univ :=
    Set.range_eq_univ.mpr unitProjective_surjective
  have hc := hs.image_of_continuousOn unitProjective_continuous.continuousOn
  exact ⟨by simpa only [Set.image_univ, hr] using hc⟩

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCompact
