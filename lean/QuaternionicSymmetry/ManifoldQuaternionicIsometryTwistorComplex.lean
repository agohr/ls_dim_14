import QuaternionicSymmetry.ManifoldQuaternionicIsometrySplitDerivative

/-! Complex linearity of the full actual derivative-induced twistor lift. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryTwistorComplex

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometrySplitDerivative
open ManifoldQuaternionicIsometryBaseComplex
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicIsometryOrientation
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicTwistorVerticalAction
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorSphereCore
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorLocalAlmostComplex
open ManifoldTwistorVerticalComplex
open ManifoldQuaternionicConnection
open scoped Manifold ContDiff Matrix
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

/-- The full manifold derivative of a quaternionic isometry's twistor lift
is complex linear for the actual Levi-Civita twistor almost-complex field. -/
theorem sphereTotalMap_mfderiv_intertwines_tangentComplex
    (D : CompatibleTangentConnection Q)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q)
    (t : TangentSpace (J (E := E)) z) :
    mfderiv (J (E := E)) (J (E := E)) (sphereTotalMap Q f) z
      (tangentComplex Q D z t) =
      tangentComplex Q D (sphereTotalMap Q f z)
        (mfderiv (J (E := E)) (J (E := E))
          (sphereTotalMap Q f) z t) := by
  let w := sphereTotalMap Q f z
  let L := mfderiv (J (E := E)) (J (E := E)) (sphereTotalMap Q f) z
  let e := connectionTangentEquiv Q D z
  let e' := connectionTangentEquiv Q D w
  apply e'.injective
  rw [tangentComplex_connectionTangentEquiv Q D w (L t)]
  apply Prod.ext
  · have h₁ := connectionTangentEquiv_mfderiv_fst Q D f z
      (tangentComplex Q D z t)
    have h₂ := connectionTangentEquiv_mfderiv_fst Q D f z t
    change (e' (L (tangentComplex Q D z t))).1 = _ at h₁
    change (e' (L t)).1 = _ at h₂
    rw [h₁, tangentComplex_connectionTangentEquiv Q D z t]
    change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) z.1
        (chartBaseComplex Q z.1 (extChartAt 𝓘(ℝ,E) z.1 z.1)
          (coefficientSphereHomeomorph.symm z.2) (e t).1) =
      chartBaseComplex Q w.1 (extChartAt 𝓘(ℝ,E) w.1 w.1)
        (coefficientSphereHomeomorph.symm w.2) (e' (L t)).1
    rw [h₂]
    change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) z.1
        (chartBaseComplex Q z.1 (extChartAt 𝓘(ℝ,E) z.1 z.1)
          (coefficientSphereHomeomorph.symm z.2) (e t).1) =
      chartBaseComplex Q w.1 (extChartAt 𝓘(ℝ,E) w.1 w.1)
        (coefficientSphereHomeomorph.symm w.2)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) z.1 (e t).1)
    exact isometry_mfderiv_intertwines_chartBaseComplex Q f z (e t).1
  · apply Subtype.ext
    have h₁ := connectionTangentEquiv_mfderiv_snd_coefficients Q D f z
      (tangentComplex Q D z t)
    have h₂ := connectionTangentEquiv_mfderiv_snd_coefficients Q D f z t
    change ((e' (L (tangentComplex Q D z t))).2).1 = _ at h₁
    change ((e' (L t)).2).1 = _ at h₂
    rw [h₁, tangentComplex_connectionTangentEquiv Q D z t]
    change coefficientAction Q f z.1
        ((verticalComplex (coefficientSphereHomeomorph.symm z.2)
          (e t).2).1) =
      (verticalComplex (coefficientSphereHomeomorph.symm w.2)
        (e' (L t)).2).1
    change coefficientAction Q f z.1
        ((coefficientSphereHomeomorph.symm z.2).1 ⨯₃ (e t).2.1) =
      (coefficientSphereHomeomorph.symm w.2).1 ⨯₃ (e' (L t)).2.1
    have ha : (coefficientSphereHomeomorph.symm w.2).1 =
        coefficientAction Q f z.1
          (coefficientSphereHomeomorph.symm z.2).1 := by
      exact congrArg Subtype.val (sphereTotalMap_coefficient Q f z)
    calc
      _ = coefficientAction Q f z.1
            (coefficientSphereHomeomorph.symm z.2).1 ⨯₃
          coefficientAction Q f z.1 (e t).2.1 :=
        coefficientAction_cross Q f z.1 _ _
      _ = (coefficientSphereHomeomorph.symm w.2).1 ⨯₃
          coefficientAction Q f z.1 (e t).2.1 :=
        congrArg (fun a => a ⨯₃ coefficientAction Q f z.1 (e t).2.1) ha.symm
      _ = _ :=
        congrArg (fun a => (coefficientSphereHomeomorph.symm w.2).1 ⨯₃ a) h₂.symm

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryTwistorComplex
