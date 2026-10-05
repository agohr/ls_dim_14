import QuaternionicSymmetry.HolomorphicLineCoreProjectiveEigenbasisReindex
import QuaternionicSymmetry.ManifoldQuaternionicContactPowerSectionAction

/-! Compact projective equivariance for the actual quaternionic-isometry
action on the complete holomorphic sections of every contact-line power.
The fiber scalar is the constructed contact differential, not a formal
linearization assumption. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicContactPowerProjectiveEquivariance

open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicIsometryContactFiberEquiv
open ManifoldQuaternionicIsometryContactPowerSections
open ManifoldQuaternionicContactPowerSectionAction
open ManifoldQuaternionicContactPowerContinuity
open ManifoldQuaternionicContactPowerWeights
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore HolomorphicLineCorePullback
open HolomorphicLineTensorPowerClasses
open HolomorphicLineCoreProjectiveEvaluation
open HolomorphicLineCoreProjectiveEigenbasis
open ComplexProjectiveDiagonalAction TorusLaurentRepresentation
open TorusCharacterInput
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem contactScalar_ne_zero
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} {B : CompatibleComplexAtlas Q D n}
    (C : HolomorphicContactData Q D n B)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q) :
    contactScalar Q D C.line f z ≠ 0 := by
  let ef : ℂ ≃ₗ[ℂ] ℂ := contactLineFiberEquiv Q D C.line f z
  change ef 1 ≠ 0
  exact ef.map_ne_zero_iff.mpr one_ne_zero

/-- The actual contact scalar to the `k`th power gives the true invertible
map between the preferred fibers of the represented contact power. -/
def contactPowerScalarFiberEquiv
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (f : QuaternionicIsometries Q) (k : ℕ) (z : SphereBundleTotal Q) :
    letI := B.charts
    (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore Q D C.line) k).core.Fiber z ≃ₗ[ℂ]
    (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore Q D C.line) k).core.Fiber (sphereTotalMap Q f z) := by
  letI := B.charts
  exact LinearEquiv.smulOfUnit
    (Units.mk0 (contactScalar Q D C.line f z ^ k)
      (pow_ne_zero k (contactScalar_ne_zero Q D C f z)))

theorem contactPowerScalarFiberEquiv_naturality
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (f : QuaternionicIsometries Q) (k : ℕ)
    (s : letI := B.charts; PowerSections Q D B C k)
    (z : SphereBundleTotal Q) :
    letI := B.charts
    (contactPowerSectionEquiv Q D B C f k s) (sphereTotalMap Q f z) =
      contactPowerScalarFiberEquiv Q D B C f k z (s z) := by
  letI := B.charts
  have h := contactPowerSectionEquiv_apply_at_image Q D B C f k s z
  change (contactPowerSectionEquiv Q D B C f k s) (sphereTotalMap Q f z) =
    contactScalar Q D C.line f z ^ k * (show ℂ from s z) at h
  simpa [contactPowerScalarFiberEquiv, LinearEquiv.smulOfUnit,
    smul_eq_mul] using h

/-- The actual compact torus action on the contact power makes its genuine
complete projective evaluation map equivariant for negative section weights. -/
theorem contactPower_projectiveEvaluation_diagonal_compact
    {r d : ℕ} (A : ContinuousTorusAction Q r)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ)
    (b : letI := B.charts;
      Module.Basis (Fin (d + 1)) ℂ (PowerSections Q D B C k))
    (hGen : letI := B.charts;
      GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.line) k))
    (μ : Fin (d + 1) → Fin r → ℤ)
    (hEig : letI := B.charts; ∀ (t : Torus r) (i : Fin (d + 1)),
      contactPowerTorusRepresentation Q A D B C k t (b i) =
        (weightCharacter (μ i) t : ℂ) • b i)
    (t : Torus r) (z : SphereBundleTotal Q) :
    letI := B.charts
    projectiveEvaluationOfGenerated 𝓘(ℂ,ComplexTwistorModel n)
      (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D C.line) k) d b hGen
      (sphereTotalMap Q (A.representation t) z) =
    projectiveAction (fun i => -(μ i)) (compactInclusion r t)
      (projectiveEvaluationOfGenerated 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.line) k) d b hGen z) := by
  letI := B.charts
  exact projectiveEvaluation_diagonal_compact
    𝓘(ℂ,ComplexTwistorModel n)
    (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore Q D C.line) k)
    b hGen (sphereTotalMap Q (A.representation t))
    (contactPowerScalarFiberEquiv Q D B C (A.representation t) k)
    (contactPowerSectionEquiv Q D B C (A.representation t) k)
    (contactPowerScalarFiberEquiv_naturality Q D B C (A.representation t) k)
    μ t (by simpa [contactPowerTorusRepresentation,
      contactPowerSectionRepresentation] using hEig t) z

end
end QuaternionicSymmetry.ManifoldQuaternionicContactPowerProjectiveEquivariance
