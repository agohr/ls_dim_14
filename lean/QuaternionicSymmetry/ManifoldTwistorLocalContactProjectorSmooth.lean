import QuaternionicSymmetry.ManifoldTwistorVerticalComplexLine

/-! A smooth fixed-chart horizontal projection on the actual tangent bundle
of the model base times the genuine twistor sphere. The vertical direction
is corrected by the induced quaternionic rank-three connection. -/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex

open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldTwistorRadialRetraction
open QuaternionicSymmetry.ManifoldTwistorHorizontalConnection
open QuaternionicSymmetry.ManifoldTwistorVerticalComplex
open QuaternionicSymmetry.ManifoldQuaternionicAdjointConnection
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

def localHorizontalProjection (p : M) (r : X (E := E)) : X (E := E) :=
  let a := (coefficientSphereHomeomorph.symm r.2.1).1
  let w := -(inducedForm Q D p r.1.1 r.1.2 a)
  (r.1, radialTangentMap
    (r.2.1, (EuclideanSpace.equiv (Fin 3) ℝ).symm w))

theorem localHorizontalProjection_smooth (p : M) :
    ContMDiffOn (IX (E := E)) (IX (E := E)) ∞
      (localHorizontalProjection Q D p) (localDomain (E := E) p) := by
  let s := localDomain (E := E) p
  have hfirst : ContMDiff (IX (E := E)) 𝓘(ℝ,E) ∞
      (fun r : X (E := E) => r.1.1) :=
    contMDiff_fst.comp contMDiff_fst
  have hu : ContMDiff (IX (E := E)) 𝓘(ℝ,E) ∞
      (fun r : X (E := E) => r.1.2) :=
    contMDiff_snd.comp contMDiff_fst
  have ht : ContMDiff (IX (E := E)) (𝓡 2).tangent ∞
      (fun r : X (E := E) => r.2) := contMDiff_snd
  have ha : ContMDiff (IX (E := E)) (𝓡 2) ∞
      (fun r : X (E := E) => r.2.1) :=
    (Bundle.contMDiff_proj (TangentSpace (𝓡 2))).comp ht
  have hcoef0 : ContMDiff (𝓡 2) 𝓘(ℝ,V) ∞
      (fun a : geometricSphere => (coefficientSphereHomeomorph.symm a).1) := by
    convert ((EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap.contMDiff).comp
      (contMDiff_coe_sphere (n := 2) (E := EuclideanThree)) using 1
  have hcoef : ContMDiff (IX (E := E)) 𝓘(ℝ,V) ∞
      (fun r : X (E := E) => (coefficientSphereHomeomorph.symm r.2.1).1) :=
    hcoef0.comp ha
  have hA : ContMDiffOn (IX (E := E))
      𝓘(ℝ, E →L[ℝ] (V →L[ℝ] V)) ∞
      (fun r : X (E := E) => inducedForm Q D p r.1.1) s :=
    (inducedForm_smooth Q D p).contMDiffOn.comp hfirst.contMDiffOn
      (by intro r hr; exact hr)
  have hAu : ContMDiffOn (IX (E := E)) 𝓘(ℝ,V →L[ℝ] V) ∞
      (fun r : X (E := E) => inducedForm Q D p r.1.1 r.1.2) s :=
    hA.clm_apply hu.contMDiffOn
  have hAua : ContMDiffOn (IX (E := E)) 𝓘(ℝ,V) ∞
      (fun r : X (E := E) => inducedForm Q D p r.1.1 r.1.2
        (coefficientSphereHomeomorph.symm r.2.1).1) s :=
    hAu.clm_apply hcoef.contMDiffOn
  have hradial : ContMDiffOn (IX (E := E)) (𝓡 2).tangent ∞
      (fun r : X (E := E) => radialTangentMap
        (r.2.1, (EuclideanSpace.equiv (Fin 3) ℝ).symm
          (-inducedForm Q D p r.1.1 r.1.2
            (coefficientSphereHomeomorph.symm r.2.1).1))) s :=
    radialTangentMap_smooth.comp_contMDiffOn
      (ha.contMDiffOn.prodMk
        ((EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn
          hAua.neg))
  simpa only [localHorizontalProjection] using
    (hfirst.prodMk hu).contMDiffOn.prodMk hradial

theorem localHorizontalProjection_eq_horizontalLift (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : coefficientSphere) (u : E)
    (v : TangentSpace (𝓡 2) (coefficientSphereHomeomorph a)) :
    localHorizontalProjection Q D p
      ((y,u),⟨coefficientSphereHomeomorph a,v⟩) =
      ((y,u),⟨coefficientSphereHomeomorph a,
        (sphereTangentVerticalEquiv a).symm
          (-(connectionVertical Q D p y hy a u))⟩) := by
  apply Prod.ext
  · rfl
  · apply Bundle.TotalSpace.ext
    · rfl
    · apply heq_of_eq
      change mfderiv 𝓘(ℝ,EuclideanThree) (𝓡 2) radial
          (sphereIntoNonzero (coefficientSphereHomeomorph a))
          ((EuclideanSpace.equiv (Fin 3) ℝ).symm
            (-(connectionVertical Q D p y hy a u)).1) = _
      exact radialDerivative_eq_verticalInverse a
        (-(connectionVertical Q D p y hy a u))

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
