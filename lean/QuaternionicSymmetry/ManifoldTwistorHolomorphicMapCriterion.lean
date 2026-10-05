import QuaternionicSymmetry.ComplexManifoldRealSmoothCriterion
import QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

/-! Real-smooth maps intertwining i with the already constructed twistor
tensor are genuinely holomorphic in every compatible T1 complex atlas.
This is an internal chart-comparison theorem, not an integrability premise. -/

namespace QuaternionicSymmetry.ManifoldTwistorHolomorphicMapCriterion

open scoped Manifold ContDiff
open ManifoldTwistorSphereCore ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorLeBrunComplexAtlas ComplexManifoldRealSmoothCriterion
noncomputable section

variable {E M N : Type*} {F : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ,F) ∞ N] [IsManifold 𝓘(ℂ,F) ∞ N]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)

theorem contMDiff_complex_of_twistor_tensor {n : ℕ}
    (A : CompatibleComplexAtlas Q D n) (f : N → SphereBundleTotal Q)
    (hSmooth : ContMDiff 𝓘(ℝ,F) (J (E := E)) ∞ f)
    (hTensor : ∀ (x : N) (v : F),
      mfderiv 𝓘(ℝ,F) (J (E := E)) f x (Complex.I • v) =
        tangentComplex Q D (f x) (mfderiv 𝓘(ℝ,F) (J (E := E)) f x v)) :
    letI := A.charts
    ContMDiff 𝓘(ℂ,F) 𝓘(ℂ,ComplexTwistorModel n) ∞ f := by
  letI := A.charts
  letI := A.realManifold
  letI := A.complexManifold
  have hReal : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,ComplexTwistorModel n) ∞ f :=
    A.smoothFromExisting.comp hSmooth
  apply contMDiff_of_real_complex_derivative f hReal
  intro x v
  let z := f x
  let T := mfderiv 𝓘(ℝ,ComplexTwistorModel n) (J (E := E))
    (id : SphereBundleTotal Q → SphereBundleTotal Q) z
  let U := mfderiv (J (E := E)) 𝓘(ℝ,ComplexTwistorModel n)
    (id : SphereBundleTotal Q → SphereBundleTotal Q) z
  let L := mfderiv 𝓘(ℝ,F) 𝓘(ℝ,ComplexTwistorModel n) f x
  let H := mfderiv 𝓘(ℝ,F) (J (E := E)) f x
  have hT : MDifferentiableAt 𝓘(ℝ,ComplexTwistorModel n) (J (E := E))
      (id : SphereBundleTotal Q → SphereBundleTotal Q) z :=
    A.smoothToExisting.mdifferentiable (by simp) z
  have hU : MDifferentiableAt (J (E := E)) 𝓘(ℝ,ComplexTwistorModel n)
      (id : SphereBundleTotal Q → SphereBundleTotal Q) z :=
    A.smoothFromExisting.mdifferentiable (by simp) z
  have hL : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,ComplexTwistorModel n) f x :=
    hReal.mdifferentiable (by simp) x
  have hUT := mfderiv_comp z hU hT
  change mfderiv 𝓘(ℝ,ComplexTwistorModel n) 𝓘(ℝ,ComplexTwistorModel n)
    id z = U.comp T at hUT
  rw [mfderiv_id] at hUT
  have hTin : Function.Injective T := by
    intro a b hab
    have ha := congrArg (fun K : ComplexTwistorModel n →L[ℝ]
      ComplexTwistorModel n => K a) hUT
    have hb := congrArg (fun K : ComplexTwistorModel n →L[ℝ]
      ComplexTwistorModel n => K b) hUT
    change a = U (T a) at ha
    change b = U (T b) at hb
    exact ha.trans ((congrArg U hab).trans hb.symm)
  have hnat := mfderiv_comp x hT hL
  change H = T.comp L at hnat
  have hnat_apply (w : F) : H w = T (L w) :=
    congrArg (fun K : F →L[ℝ] TangentSpace (J (E := E)) z => K w) hnat
  apply hTin
  calc
    T (L (Complex.I • v)) = H (Complex.I • v) := (hnat_apply _).symm
    _ = tangentComplex Q D z (H v) := hTensor x v
    _ = tangentComplex Q D z (T (L v)) := congrArg (tangentComplex Q D z) (hnat_apply v)
    _ = T (Complex.I • (show ComplexTwistorModel n from L v)) :=
      (A.tangentI z (L v)).symm

end
end QuaternionicSymmetry.ManifoldTwistorHolomorphicMapCriterion
