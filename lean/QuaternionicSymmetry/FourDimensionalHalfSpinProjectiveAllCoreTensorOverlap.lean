import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCoreSecondTensor
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCoreReverseTensor
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCoreMixedTensor
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCoreTensorMFDeriv

/-! All four affine source/target cases of the independently constructed
projective bundle-core transition are now packaged under one chart-index
statement. The denominator condition is exactly target affine-chart
membership; its automatic discharge from arbitrary atlas overlap is a
separate global-chart obligation. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveAllCoreTensorOverlap

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjectiveCoreSecondTensor
  FourDimensionalHalfSpinProjectiveCoreReverseTensor
  FourDimensionalHalfSpinProjectiveCoreMixedTensor
  FourDimensionalHalfSpinProjectiveCoreTensorMFDeriv
  FourDimensionalHalfSpinProjectiveCoreSecondGerm
  FourDimensionalHalfSpinProjectiveCoreReverseGerm
  FourDimensionalHalfSpinProjectiveCoreMixedGerm
  FourDimensionalHalfSpinProjectiveCoreTransitionGerm
  FourDimensionalHalfSpinProjectiveActualCoreAffine
  FourDimensionalHalfSpinProjectiveSecondMobius
  FourDimensionalHalfSpinProjectiveReverseMixedGaugeAlgebra
  FourDimensionalHalfSpinProjectiveMixedGaugeAlgebra
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveLocalAHS
  FourDimensionalHalfSpinProjectiveSecondTensor
  FourDimensionalHalfSpinMatrix
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldLocalStandardMaurer
  ManifoldQuaternionicConnection

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

def indexedLocalTensor (i : Fin 2) (p : M) (y : ℍ) (z : ℂ) :
    (ℍ × ℂ) →ₗ[ℝ] (ℍ × ℂ) :=
  if i = 0 then localActualProjectiveAHS Q D p y z
  else secondLocalActualProjectiveAHS Q D p y z

def indexedCoreTransition (i j : Fin 2) (p q : M) : ℍ × ℂ → ℍ × ℂ :=
  if i = 0 then
    if j = 0 then coreAffineTransition Q p q
    else coreMixedTransition Q p q
  else
    if j = 0 then coreReverseTransition Q p q
    else coreSecondTransition Q p q

def indexedDenominator (i j : Fin 2) (A : Mat2) (z : ℂ) : ℂ :=
  if i = 0 then
    if j = 0 then chartDen A z else mixedDen A z
  else
    if j = 0 then reverseDen A z else secondDen A z

theorem indexed_core_tensor_overlap_mfderiv
    (i j : Fin 2) (p q : M) (lift : unitary ℍ)
    (y : ℍ) (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (z : ℂ)
    (hden : indexedDenominator i j
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) z ≠ 0)
    (v : ℍ × ℂ) :
    let T := indexedCoreTransition Q i j p q
    mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) T (y,z)
        (indexedLocalTensor Q D i p y z v) =
      indexedLocalTensor Q D j q (T (y,z)).1 (T (y,z)).2
        (mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) T (y,z) v) := by
  fin_cases i <;> fin_cases j
  · simp [indexedCoreTransition, indexedLocalTensor, indexedDenominator] at hden ⊢
    have hT : coreAffineTransition Q p q (y,z) =
        (chartTransition (I := 𝓘(ℝ, ℍ)) p q y,
          mobius (halfSpinMatrix
            (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) z) := by
      apply Prod.ext
      · rfl
      · exact actual_core_affine_transition Q p q lift y hx z hden
    rw [hT]
    simpa only [mfderiv_eq_fderiv, Prod.fst, Prod.snd] using
      core_tensor_overlap_mfderiv Q D p q lift y hy hx z hden v
  · simp [indexedCoreTransition, indexedLocalTensor, indexedDenominator] at hden ⊢
    rw [actual_core_mixed_transition Q p q lift y hx z hden]
    simpa only [mfderiv_eq_fderiv, Prod.fst, Prod.snd] using
      core_mixed_tensor_overlap_mfderiv Q D p q lift y hy hx z hden v
  · simp [indexedCoreTransition, indexedLocalTensor, indexedDenominator] at hden ⊢
    rw [actual_core_reverse_transition Q p q lift y hx z hden]
    simpa only [mfderiv_eq_fderiv, Prod.fst, Prod.snd] using
      core_reverse_tensor_overlap_mfderiv Q D p q lift y hy hx z hden v
  · simp [indexedCoreTransition, indexedLocalTensor, indexedDenominator] at hden ⊢
    rw [actual_core_second_transition Q p q lift y hx z hden]
    simpa only [mfderiv_eq_fderiv, Prod.fst, Prod.snd] using
      core_second_tensor_overlap_mfderiv Q D p q lift y hy hx z hden v

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveAllCoreTensorOverlap
