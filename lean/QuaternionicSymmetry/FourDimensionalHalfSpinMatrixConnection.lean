import QuaternionicSymmetry.FourDimensionalHalfSpinAffineLeft
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! The left-quaternion connection becomes an honest complex two-by-two
matrix connection. Its affine transformation is the literal GL₂(ℂ) gauge
law for the actual local half-spin matrices, prior to projectivization. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinMatrixConnection

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinAffineLeft
  FourDimensionalHalfSpinLieProjection
  FourDimensionalHalfSpinMatrix
  QuaternionicManifoldLocalStandardMaurer
  QuaternionicManifoldProductGaugeDifferential
  QuaternionicManifoldLocalScalarLifts
  ManifoldQuaternionicConnection

noncomputable section

local instance : NormedRing (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ) :=
  Matrix.linftyOpNormedAlgebra
local instance : NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℂ) :=
  NormedAlgebra.toNormedSpace _

private def halfSpinMatrixLinear : ℍ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun := halfSpinMatrix
  map_add' p q := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      simp [halfSpinMatrix, first, second, Complex.ext_iff] <;> ring
  map_smul' a p := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      simp [halfSpinMatrix, first, second, Complex.ext_iff] <;> ring

theorem halfSpinMatrix_add (p q : ℍ) :
    halfSpinMatrix (p + q) = halfSpinMatrix p + halfSpinMatrix q :=
  halfSpinMatrixLinear.map_add p q

theorem halfSpinMatrix_fderiv {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (r : X → ℍ) (x : X) (hr : DifferentiableAt ℝ r x) (u : X) :
    fderiv ℝ (fun z => halfSpinMatrix (r z)) x u =
      halfSpinMatrix (fderiv ℝ r x u) := by
  let L : ℍ →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
    halfSpinMatrixLinear.toContinuousLinearMap
  change fderiv ℝ (L ∘ r) x u = L (fderiv ℝ r x u)
  have hd : fderiv ℝ (L ∘ r) x = L.comp (fderiv ℝ r x) := by
    exact (L.hasFDerivAt.comp x hr.hasFDerivAt).fderiv
  exact congrArg (fun T : X →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ => T u) hd

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

def spinorMatrixForm (p : M) (y u : ℍ) : Matrix (Fin 2) (Fin 2) ℂ :=
  halfSpinMatrix (leftSpinorForm Q D p y u)

def spinorMatrixConnectionForm (p : M) (y : ℍ) :
    ℍ →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  halfSpinMatrixLinear.toContinuousLinearMap.comp (leftSpinorForm Q D p y)

theorem spinorMatrixConnectionForm_apply (p : M) (y u : ℍ) :
    spinorMatrixConnectionForm Q D p y u = spinorMatrixForm Q D p y u := rfl

theorem spinorMatrixConnectionForm_smooth (p : M) :
    ContDiffOn ℝ ∞ (spinorMatrixConnectionForm Q D p)
      (extChartAt 𝓘(ℝ, ℍ) p).target := by
  exact contDiffOn_const.clm_comp (leftSpinorForm_smooth Q D p)

theorem spinorMatrixForm_affine_refined (p q : M) (lift : unitary ℍ)
    (y u : ℍ) (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift) :
    let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
    spinorMatrixForm Q D p y u =
      halfSpinMatrix (star (r y)) *
        (spinorMatrixForm Q D q
          (chartTransition (I := 𝓘(ℝ, ℍ)) p q y)
          (fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y u) *
            halfSpinMatrix (r y) +
          fderiv ℝ (fun z => halfSpinMatrix (r z)) y u) := by
  dsimp [spinorMatrixForm]
  rw [leftSpinorForm_affine_refined Q D p q lift y u hy hx,
    halfSpinMatrix_mul, halfSpinMatrix_add, halfSpinMatrix_mul]
  let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
  have hr : DifferentiableAt ℝ r y :=
    scalarLift_chart_differentiableAt Q p (achart ℍ p) (achart ℍ q)
      lift y hy.1 hx
  have hd := halfSpinMatrix_fderiv r y hr u
  simpa only [r] using congrArg
    (fun T : Matrix (Fin 2) (Fin 2) ℂ =>
      halfSpinMatrix (star (r y)) *
        (halfSpinMatrix (leftSpinorForm Q D q
          (chartTransition (I := 𝓘(ℝ, ℍ)) p q y)
          (fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y u)) *
            halfSpinMatrix (r y) + T)) hd.symm

end
end QuaternionicSymmetry.FourDimensionalHalfSpinMatrixConnection
