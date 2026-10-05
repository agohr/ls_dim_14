import QuaternionicSymmetry.ManifoldQuaternionicIsometryContactFiberEquiv
import QuaternionicSymmetry.ManifoldQuaternionicIsometryComplexInfinity
import QuaternionicSymmetry.ManifoldTwistorContactComplexLinear

/-! Naturality of the actual complex contact form under a holomorphic
quaternionic-isometry lift. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryContactComplexNaturality

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicIsometryContactFiberEquiv
open ManifoldQuaternionicHolomorphicContactFiberAction
open ManifoldQuaternionicIsometryComplexInfinity
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)
local instance : Fact (Module.finrank ℝ
    ManifoldTwistorCoefficientSphere.EuclideanThree = 2 + 1) := ⟨by simp⟩
local instance (x : M) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore Q).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ManifoldTwistorCoefficientSphere.geometricSphere
  infer_instance

theorem contactLineFiberEquiv_contactFormComplex
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (L : HolomorphicContactLine Q D n B)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q)
    (v : ComplexTwistorModel n) :
    letI := B.charts
    L.contactFormComplex Q D (sphereTotalMap Q f z)
      (mfderiv 𝓘(ℂ,ComplexTwistorModel n)
        𝓘(ℂ,ComplexTwistorModel n) (sphereTotalMap Q f) z v) =
      contactLineFiberEquiv Q D L f z (L.contactFormComplex Q D z v) := by
  letI := B.charts
  let w := sphereTotalMap Q f z
  let T := mfderiv 𝓘(ℝ,ComplexTwistorModel n) (J (E := E))
    (id : SphereBundleTotal Q → SphereBundleTotal Q) z
  let T' := mfderiv 𝓘(ℝ,ComplexTwistorModel n) (J (E := E))
    (id : SphereBundleTotal Q → SphereBundleTotal Q) w
  let R := mfderiv 𝓘(ℝ,ComplexTwistorModel n)
    𝓘(ℝ,ComplexTwistorModel n) (sphereTotalMap Q f) z
  let C := mfderiv 𝓘(ℂ,ComplexTwistorModel n)
    𝓘(ℂ,ComplexTwistorModel n) (sphereTotalMap Q f) z
  let H := mfderiv (J (E := E)) (J (E := E)) (sphereTotalMap Q f) z
  have hT : MDifferentiableAt 𝓘(ℝ,ComplexTwistorModel n) (J (E := E))
      (id : SphereBundleTotal Q → SphereBundleTotal Q) z :=
    B.smoothToExisting.mdifferentiable (by simp) z
  have hT' : MDifferentiableAt 𝓘(ℝ,ComplexTwistorModel n) (J (E := E))
      (id : SphereBundleTotal Q → SphereBundleTotal Q) w :=
    B.smoothToExisting.mdifferentiable (by simp) w
  have hR : MDifferentiableAt 𝓘(ℝ,ComplexTwistorModel n)
      𝓘(ℝ,ComplexTwistorModel n) (sphereTotalMap Q f) z :=
    (ManifoldQuaternionicIsometryComplexAtlas.sphereTotalMap_realSmooth_in_compatibleAtlas
      Q D B f).mdifferentiable (by simp) z
  have hH : MDifferentiableAt (J (E := E)) (J (E := E))
      (sphereTotalMap Q f) z :=
    (ManifoldQuaternionicTwistorLiftSmooth.sphereTotalMap_contMDiff Q f).mdifferentiable
      (by simp) z
  have hC : MDifferentiableAt 𝓘(ℂ,ComplexTwistorModel n)
      𝓘(ℂ,ComplexTwistorModel n) (sphereTotalMap Q f) z :=
    (sphereTotalMap_contMDiff_complex_infty Q D B f).mdifferentiable (by simp) z
  have hsame : R = C.restrictScalars ℝ := by
    rw [show R = _ from hR.mfderiv, show C = _ from hC.mfderiv]
    simp only [modelWithCornersSelf_coe]
    rw [show writtenInExtChartAt 𝓘(ℝ,ComplexTwistorModel n)
        𝓘(ℝ,ComplexTwistorModel n) z (sphereTotalMap Q f) =
      writtenInExtChartAt 𝓘(ℂ,ComplexTwistorModel n)
        𝓘(ℂ,ComplexTwistorModel n) z (sphereTotalMap Q f) from rfl]
    simp only [Set.range_id, fderivWithin_univ]
    have hc : DifferentiableAt ℂ
        (writtenInExtChartAt 𝓘(ℂ,ComplexTwistorModel n)
          𝓘(ℂ,ComplexTwistorModel n) z (sphereTotalMap Q f))
        ((extChartAt 𝓘(ℂ,ComplexTwistorModel n) z) z) := by
      simpa [modelWithCornersSelf_coe, Set.range_id,
        differentiableWithinAt_univ] using
        hC.differentiableWithinAt_writtenInExtChartAt
    exact hc.fderiv_restrictScalars ℝ
  have h₁ := mfderiv_comp z hT' hR
  have h₂ := mfderiv_comp z hH hT
  have hnat : T' ∘L R = H ∘L T := by
    change mfderiv 𝓘(ℝ,ComplexTwistorModel n) (J (E := E))
        (id ∘ sphereTotalMap Q f) z = T' ∘L R at h₁
    change mfderiv 𝓘(ℝ,ComplexTwistorModel n) (J (E := E))
        (sphereTotalMap Q f ∘ id) z = H ∘L T at h₂
    exact h₁.symm.trans h₂
  have hv := congrArg (fun K : ComplexTwistorModel n →L[ℝ]
      TangentSpace (J (E := E)) w => K v) hnat
  change T' (R v) = H (T v) at hv
  change L.contactFormReal Q D w (T' (C v)) =
    contactLineFiberEquiv Q D L f z (L.contactFormReal Q D z (T v))
  have hvalue := congrArg (fun K : ComplexTwistorModel n →L[ℝ]
      ComplexTwistorModel n => K v) hsame
  change R v = C v at hvalue
  rw [← hvalue, hv, contactLineFiberEquiv_apply]
  exact (contactLineFiberMap_contactFormReal Q D L f z (T v)).symm

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryContactComplexNaturality
