import QuaternionicSymmetry.CompactSymplecticProjectorTwistorUnitFiber

/-! The two complex directions of a unit quaternionic line give an actual
injective complex-linear map `ℂ² → ℂ^{2n+2}` and hence an injective map of
projective lines into ambient complex projective space. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTwistorFiberLine

open CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorColumnPhase
open CompactSymplecticProjectorTwistorNormalized
open CompactSymplecticProjectorTwistorPhaseNorm
open CompactSymplecticProjectorColumnUnit
open scoped LinearAlgebra.Projectivization

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ
private abbrev EV (n : ℕ) := EuclideanSpace ℂ (I n)

def fiberLineMap (n : ℕ) (w : Metric.sphere (0 : EV n) 1) :
    (Fin 2 → ℂ) →ₗ[ℂ] V n where
  toFun z := phaseRotate n (z 0) (z 1) ((EuclideanSpace.equiv (I n) ℂ) w.1)
  map_add' := by
    intro z t
    funext i
    simp [phaseRotate, Pi.add_apply, Pi.smul_apply, mul_add, add_mul]
    ring
  map_smul' := by
    intro c z
    funext i
    simp [phaseRotate, Pi.smul_apply, mul_assoc, mul_add, add_mul]

theorem fiberLineMap_injective (n : ℕ)
    (w : Metric.sphere (0 : EV n) 1) :
    Function.Injective (fiberLineMap n w) := by
  intro z z' h
  have hz : fiberLineMap n w (z - z') = 0 := by
    rw [map_sub, h, sub_self]
  have hzero : phaseRotate n ((z - z') 0) ((z - z') 1)
      ((EuclideanSpace.equiv (I n) ℂ) w.1) = 0 := hz
  have hunit : columnNormSq n ((EuclideanSpace.equiv (I n) ℂ) w.1) = 1 := by
    simpa [columnNormSq] using unit_column_dot_self n w
  have hnorm := columnNormSq_phaseRotate n ((z - z') 0) ((z - z') 1)
    ((EuclideanSpace.equiv (I n) ℂ) w.1)
  rw [hzero, hunit] at hnorm
  simp [columnNormSq] at hnorm
  have hsum : Complex.normSq ((z - z') 0) + Complex.normSq ((z - z') 1) = 0 := by
    apply Complex.ofReal_injective
    simpa [Complex.normSq_eq_conj_mul_self, Complex.star_def] using hnorm.symm
  have h0 : (z - z') 0 = 0 := Complex.normSq_eq_zero.mp (by
    nlinarith [Complex.normSq_nonneg ((z - z') 0), Complex.normSq_nonneg ((z - z') 1)])
  have h1 : (z - z') 1 = 0 := Complex.normSq_eq_zero.mp (by
    nlinarith [Complex.normSq_nonneg ((z - z') 0), Complex.normSq_nonneg ((z - z') 1)])
  have hsub : z - z' = 0 := by
    funext i
    fin_cases i <;> simp [h0, h1]
  exact sub_eq_zero.mp hsub

def fiberProjectiveLine (n : ℕ) (w : Metric.sphere (0 : EV n) 1) :
    ℙ ℂ (Fin 2 → ℂ) → ℙ ℂ (V n) :=
  Projectivization.map (fiberLineMap n w) (fiberLineMap_injective n w)

theorem fiberProjectiveLine_injective (n : ℕ)
    (w : Metric.sphere (0 : EV n) 1) :
    Function.Injective (fiberProjectiveLine n w) :=
  Projectivization.map_injective (fiberLineMap n w) (fiberLineMap_injective n w)

end
end QuaternionicSymmetry.CompactSymplecticProjectorTwistorFiberLine
