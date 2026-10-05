import QuaternionicSymmetry.QuaternionicManifoldKernelOperatorProperties
import QuaternionicSymmetry.QuaternionicManifoldFixedConnectionOverlap

/-! The inverse in the actual fixed tangent affine overlap is the inverse
of the local scalar-times-kernel product. -/

namespace QuaternionicSymmetry.QuaternionicManifoldProductGaugeInverse

open scoped Manifold ContDiff Quaternion
open QuaternionicManifoldLocalScalarLifts
open QuaternionicManifoldSmoothProductLifts
open QuaternionicManifoldKernelOperatorProperties
open QuaternionicManifoldProductGaugeIdentity
open QuaternionicManifoldFixedConnectionOverlap
open QuaternionicProjectiveProductMaurer
open VectorBundleFrameTransitions

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

theorem fixedGaugeInv_eq_productInverse (p q : M) (lift : unitary ℍ)
    (y : E) (hy : y ∈ ManifoldQuaternionicConnection.chartOverlap
      (I := 𝓘(ℝ, E)) p q)
    (hx : (extChartAt 𝓘(ℝ, E) p).symm y ∈
      liftNeighborhood Q (achart E p) (achart E q) lift) :
    fixedGaugeInv S Q p q y =
      (symplecticFactorOperator S Q (achart E p) (achart E q) lift
        ((extChartAt 𝓘(ℝ, E) p).symm y)).adjoint *
      scalarActionLinear S
        (star (scalarLiftRaw Q (achart E p) (achart E q) lift
          ((extChartAt 𝓘(ℝ, E) p).symm y))) := by
  let x := (extChartAt 𝓘(ℝ, E) p).symm y
  let r := scalarLiftRaw Q (achart E p) (achart E q) lift x
  let h := symplecticFactorOperator S Q (achart E p) (achart E q) lift x
  have hq : Quaternion.normSq r = 1 :=
    (scalarLiftRaw_valid Q S _ _ lift x hx).1
  have hq₁ : star r * r = 1 := by
    rw [Quaternion.star_mul_self, hq]
    rfl
  have hq₂ : r * star r = 1 := by
    rw [Quaternion.self_mul_star, hq]
    rfl
  obtain ⟨hh₁, hh₂⟩ := symplecticFactor_adjoint_inverse S Q _ _ lift x hx
  obtain ⟨hleft, hright⟩ := productGauge_inverse S r h h.adjoint
    hq₁ hq₂ hh₁ hh₂
  have hg : fixedGauge S Q p q y = scalarActionLinear S r * h :=
    fixedGauge_eq_product S Q p q lift y hx
  have hgi := (fixedGauge_inverse S Q p q y hy).1
  calc
    fixedGaugeInv S Q p q y =
        fixedGaugeInv S Q p q y *
          (fixedGauge S Q p q y * (h.adjoint * scalarActionLinear S (star r))) := by
      rw [hg, hright, mul_one]
    _ = h.adjoint * scalarActionLinear S (star r) := by
      rw [← mul_assoc, hgi, one_mul]

end
end QuaternionicSymmetry.QuaternionicManifoldProductGaugeInverse
