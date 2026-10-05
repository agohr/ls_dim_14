import QuaternionicSymmetry.ManifoldTwistorSphereFiberInclusion
import QuaternionicSymmetry.ManifoldTwistorContactSplitting

/-! The corrected CP¹ fiber inclusion intertwines its standard complex
tangent with the actual total-space twistor tensor. This uses the actual
vertical inclusion derivative and the full connection-defined tensor. -/

namespace QuaternionicSymmetry.ManifoldTwistorSphereFiberComplex

open scoped Manifold ContDiff
open ManifoldTwistorSphereCore ManifoldTwistorSphereBundle
open ManifoldTwistorCoefficientSphere ManifoldTwistorVerticalComplex
open ManifoldTwistorGlobalAlmostComplex ManifoldTwistorLocalAlmostComplex
open ManifoldTwistorHorizontalConnection ManifoldTwistorSphereFiberInclusion
open ManifoldTwistorCorrectedHopf
open FourDimensionalHalfSpinProjective FourDimensionalHalfSpinHopfProjectiveDescent
open FourDimensionalHalfSpinAntipodalVerticalSign
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)
local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

theorem tangentComplex_vertical_pair (p : M) (a : coefficientSphere)
    (v : TangentSpace (𝓡 2) (coefficientSphereHomeomorph a)) :
    tangentComplex Q D (sphereFiberInclusion Q p (coefficientSphereHomeomorph a))
      (0,v) = (0,sphereVerticalComplex a v) := by
  let z := sphereFiberInclusion Q p (coefficientSphereHomeomorph a)
  let b := coefficientSphereHomeomorph.symm (coefficientSphereHomeomorph a)
  let y := (extChartAt 𝓘(ℝ,E) p) p
  have hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target :=
    (extChartAt 𝓘(ℝ,E) p).map_source (mem_extChartAt_source p)
  let e := LinearEquiv.prodCongr (LinearEquiv.refl ℝ E)
    (sphereTangentVerticalEquiv b)
  change e.symm (localTwistorComplex Q D p y hy b (e (0,v))) = _
  have hlocal : localTwistorComplex Q D p y hy b (e (0,v)) =
      (0,verticalComplex b (sphereTangentVerticalEquiv b v)) := by
    change ((connectionSplit Q D p y hy b).symm
      (chartSplitComplex Q p y b ((connectionSplit Q D p y hy b)
        (0,sphereTangentVerticalEquiv b v)))) = _
    simp [connectionSplit, chartSplitComplex]
  rw [hlocal]
  change (0,(sphereTangentVerticalEquiv b).symm
    (verticalComplex b (sphereTangentVerticalEquiv b v))) = _
  have hb : b = a := coefficientSphereHomeomorph.symm_apply_apply a
  change ((0 : E),sphereVerticalComplex b v) = (0,sphereVerticalComplex a v)
  rw [hb]

theorem projectiveFiberInclusion_mfderiv (p : M) (s : ProjectiveSpinor)
    (v : Fin 1 → ℂ) :
    mfderiv 𝓘(ℝ,Fin 1 → ℂ) (J (E := E))
      (projectiveFiberInclusion Q p) s v =
      (0,mfderiv 𝓘(ℝ,Fin 1 → ℂ) (𝓡 2) correctedHopf s v) := by
  have hd := mfderiv_comp s
    ((sphereFiberInclusion_smooth Q p).mdifferentiableAt (by simp))
    (correctedHopf_smooth.mdifferentiableAt (by simp))
  have hv := congrArg (fun f => f v) hd
  change mfderiv 𝓘(ℝ,Fin 1 → ℂ) (J (E := E))
      (projectiveFiberInclusion Q p) s v =
    mfderiv (𝓡 2) (J (E := E)) (sphereFiberInclusion Q p) (correctedHopf s)
      (mfderiv 𝓘(ℝ,Fin 1 → ℂ) (𝓡 2) correctedHopf s v) at hv
  rw [sphereFiberInclusion_mfderiv] at hv
  exact hv

theorem projectiveFiberInclusion_mfderiv_complex (p : M) (s : ProjectiveSpinor)
    (v : Fin 1 → ℂ) :
    mfderiv 𝓘(ℝ,Fin 1 → ℂ) (J (E := E))
        (projectiveFiberInclusion Q p) s (Complex.I • v) =
      tangentComplex Q D (projectiveFiberInclusion Q p s)
        (mfderiv 𝓘(ℝ,Fin 1 → ℂ) (J (E := E))
          (projectiveFiberInclusion Q p) s v) := by
  rw [projectiveFiberInclusion_mfderiv, projectiveFiberInclusion_mfderiv]
  rw [correctedHopf_mfderiv_complex (Q.reduction.Q (achart E p))]
  change (0,_) = tangentComplex Q D
    (sphereFiberInclusion Q p (correctedHopf s)) (0,_)
  rw [correctedHopf_coefficient]
  exact (tangentComplex_vertical_pair Q D p _ _).symm

end
end QuaternionicSymmetry.ManifoldTwistorSphereFiberComplex
