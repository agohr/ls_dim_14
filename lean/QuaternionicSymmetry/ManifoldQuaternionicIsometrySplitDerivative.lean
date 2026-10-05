import QuaternionicSymmetry.ManifoldQuaternionicIsometryBaseComplex

/-! The derivative of the actual smooth twistor lift is block diagonal in
the genuine Levi-Civita horizontal/vertical connection splitting. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometrySplitDerivative

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryTotalHorizontal
open ManifoldQuaternionicIsometrySphereDerivative
open ManifoldQuaternionicIsometryHorizontalAction
open ManifoldQuaternionicIsometryInducedConnection
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicTwistorVerticalAction
open ManifoldQuaternionicTwistorVerticalDerivative
open ManifoldQuaternionicLocalSphereActionSmooth
open ManifoldQuaternionicLocalCoefficientComparison
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorSphereCore
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorVerticalComplex
open ManifoldQuaternionicConnection
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)
local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩
local instance (x : M) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore Q).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2)) geometricSphere
  infer_instance

theorem coefficientOrbit_center
    (f : QuaternionicIsometries Q) (p : M) (a : Fin 3 → ℝ) :
    coefficientOrbit Q f p a (extChartAt 𝓘(ℝ,E) p p) =
      coefficientAction Q f p a := by
  simp only [coefficientOrbit,
    (extChartAt 𝓘(ℝ,E) p).left_inv (mem_extChartAt_source p)]
  exact localCoefficientRotation_center Q f p a

theorem connectionTangentEquiv_mfderiv_fst
    (D : CompatibleTangentConnection Q)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q)
    (t : TangentSpace (J (E := E)) z) :
    (connectionTangentEquiv Q D (sphereTotalMap Q f z)
      (mfderiv (J (E := E)) (J (E := E))
        (sphereTotalMap Q f) z t)).1 =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) z.1
        (connectionTangentEquiv Q D z t).1 := by
  change (mfderiv (J (E := E)) (J (E := E))
    (sphereTotalMap Q f) z t).1 =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) z.1 t.1
  exact congrArg Prod.fst (sphereTotalMap_mfderiv_blocks Q f z t.1 t.2)

/-- The second connection-splitting block of the full differential is
exactly the actual SO(3) coefficient action. This is where the base
variation of the sphere action cancels the affine connection gauge term. -/
theorem connectionTangentEquiv_mfderiv_snd_coefficients
    (D : CompatibleTangentConnection Q)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q)
    (t : TangentSpace (J (E := E)) z) :
    ((connectionTangentEquiv Q D (sphereTotalMap Q f z)
      (mfderiv (J (E := E)) (J (E := E))
        (sphereTotalMap Q f) z t)).2).1 =
      coefficientAction Q f z.1 ((connectionTangentEquiv Q D z t).2).1 := by
  let y := extChartAt 𝓘(ℝ,E) z.1 z.1
  let a := sphereCoefficients z.2
  let b := EuclideanSpace.equiv (Fin 3) ℝ (sphereTangentMap z.2 t.2)
  let R := coefficientAction Q f z.1
  let B := ManifoldQuaternionicAdjointConnection.inducedForm Q D z.1 y t.1 a
  let d := fderiv ℝ (coefficientOrbit Q f z.1 a) y t.1
  let F := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) z.1 t.1
  let B' := ManifoldQuaternionicAdjointConnection.inducedForm Q D (f • z.1)
    (extChartAt 𝓘(ℝ,E) (f • z.1) (f • z.1)) F (R a)
  have ha : R B = B' + d := by
    have h := inducedForm_isometry_affine_center Q D f z.1 t.1 a
    dsimp only at h
    rw [coefficientOrbit_center Q f z.1 B,
      coefficientOrbit_center Q f z.1 a,
      localIsometryChartMap_center Q f z.1,
      localIsometryChartMap_fderiv_center_eq_mfderiv Q f z.1] at h
    exact h
  have hder := localSphereAction_mfderiv_coefficients_center Q f z.1 z.2 t.1 t.2
  change EuclideanSpace.equiv (Fin 3) ℝ
      (sphereTangentMap (localSphereAction Q f z.1 (z.1,z.2))
        (mfderiv (J (E := E)) (𝓡 2)
          (localSphereAction Q f z.1) (z.1,z.2) (t.1,t.2))) = d +
        coefficientOrbit Q f z.1 b y at hder
  rw [coefficientOrbit_center Q f z.1 b] at hder
  have hpoint : (sphereTotalMap Q f z).2 =
      localSphereAction Q f z.1 (z.1,z.2) := by
    rw [sphereTotalMap_fiber Q f z,
      localSphereAction_fixedFiber Q f z.1 z.2]
  have hblocks := sphereTotalMap_mfderiv_blocks Q f z t.1 t.2
  change mfderiv (J (E := E)) (J (E := E))
      (sphereTotalMap Q f) z t = _ at hblocks
  have hpointBase := sphereTotalMap_base Q f z
  have hcoeff : sphereCoefficients (sphereTotalMap Q f z).2 = R a := by
    rw [hpoint, localSphereAction_center_coefficients Q f z.1 z.2,
      coefficientOrbit_center]
  change EuclideanSpace.equiv (Fin 3) ℝ
      (sphereTangentMap (sphereTotalMap Q f z).2
        (mfderiv (J (E := E)) (J (E := E))
          (sphereTotalMap Q f) z t).2) +
      ManifoldQuaternionicAdjointConnection.inducedForm Q D
        (sphereTotalMap Q f z).1
        (extChartAt 𝓘(ℝ,E) (sphereTotalMap Q f z).1
          (sphereTotalMap Q f z).1)
        (mfderiv (J (E := E)) (J (E := E))
          (sphereTotalMap Q f) z t).1
        (sphereCoefficients (sphereTotalMap Q f z).2) =
    R (b + B)
  rw [hblocks, hpointBase, hcoeff, hpoint]
  rw [hder]
  dsimp only [F, B'] at ha ⊢
  rw [map_add, ha]
  abel

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometrySplitDerivative
