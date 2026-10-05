import QuaternionicSymmetry.FourDimensionalHalfSpinHopfSmoothRaw
import QuaternionicSymmetry.ComplexProjectiveRealManifold

/-! Real-smooth local homogeneous-coordinate formulas for the Hopf map on
each of the two standard genuine `CP¹` affine charts. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfAffineSmooth

open scoped ContDiff
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinQuaternionCoordinates
  FourDimensionalHalfSpinHopfRaw
  FourDimensionalHalfSpinHopfSmoothRaw
open ComplexProjectiveTopology

noncomputable section

private theorem contDiff_insertNth (i : Fin 2) :
    ContDiff ℝ ∞ (homogeneousVector 1 i : (Fin 1 → ℂ) → Spinor) := by
  apply contDiff_pi.mpr
  intro j
  by_cases hij : j = i
  · subst j
    simpa [homogeneousVector] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : Fin 1 → ℂ => (1 : ℂ)))
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij
    rw [← hk]
    simpa [homogeneousVector, Fin.insertNth_apply_succAbove] using
      ((contDiff_apply ℂ ℂ k).restrict_scalars ℝ :
        ContDiff ℝ ∞ (fun w : Fin 1 → ℂ => w k))

/-- The actual normalized Hopf quaternion in either true affine chart is
real C∞, with no map smoothness postulated on projective space. -/
theorem contDiffAt_affineHopfQuaternion (i : Fin 2) (w : Fin 1 → ℂ) :
    ContDiffAt ℝ ∞
      (fun z : Fin 1 → ℂ =>
        (Quaternion.normSq (fromSpinor (homogeneousVector 1 i z)))⁻¹ •
          hopfRaw (homogeneousVector 1 i z)) w := by
  have hne : homogeneousVector 1 i w ≠ 0 :=
    homogeneousVector_ne_zero 1 i w
  exact (contDiffAt_hopfQuaternion (homogeneousVector 1 i w) hne).comp
    w (contDiff_insertNth i).contDiffAt

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfAffineSmooth
