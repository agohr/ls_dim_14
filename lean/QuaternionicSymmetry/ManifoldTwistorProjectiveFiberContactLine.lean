import QuaternionicSymmetry.ManifoldTwistorProjectiveFiberTransverse
import QuaternionicSymmetry.ManifoldTwistorProjectiveFiberHolomorphic
import QuaternionicSymmetry.ManifoldTwistorContactComplexLinear
import QuaternionicSymmetry.ComplexManifoldDerivativeScalarRestriction
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The actual complex contact form restricts to a complex-linear
isomorphism from the tangent of each parametrized CP¹ fiber. The formula
uses the genuine complex manifold derivative, not a chosen line map. -/

namespace QuaternionicSymmetry.ManifoldTwistorProjectiveFiberContactLine

open scoped Manifold ContDiff
open ManifoldTwistorSphereCore ManifoldTwistorSphereFiberInclusion
open ManifoldTwistorProjectiveFiberTransverse ManifoldTwistorProjectiveFiberHolomorphic
open ManifoldTwistorLeBrunComplexAtlas
open ComplexManifoldDerivativeScalarRestriction
open FourDimensionalHalfSpinProjective
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)

theorem projectiveFiberInclusion_realSmooth {n : ℕ}
    (A : CompatibleComplexAtlas Q D n) (p : M) :
    letI := A.charts
    ContMDiff 𝓘(ℝ,Fin 1 → ℂ) 𝓘(ℝ,ComplexTwistorModel n) ∞
      (projectiveFiberInclusion Q p) := by
  letI := A.charts
  exact A.smoothFromExisting.comp (projectiveFiberInclusion_smooth Q p)

theorem contactFormComplex_fiber_eq_real {n : ℕ}
    (A : CompatibleComplexAtlas Q D n) (L : HolomorphicContactLine Q D n A)
    (p : M) (s : ProjectiveSpinor) (v : Fin 1 → ℂ) :
    letI := A.charts
    L.contactFormComplex Q D (projectiveFiberInclusion Q p s)
      (mfderiv 𝓘(ℂ,Fin 1 → ℂ) 𝓘(ℂ,ComplexTwistorModel n)
        (projectiveFiberInclusion Q p) s v) =
      L.contactFormReal Q D (projectiveFiberInclusion Q p s)
        (mfderiv 𝓘(ℝ,Fin 1 → ℂ) (J (E := E))
          (projectiveFiberInclusion Q p) s v) := by
  letI := A.charts
  have hr := (projectiveFiberInclusion_realSmooth Q D A p).mdifferentiableAt (x := s)
    (by simp)
  have hc := (projectiveFiberInclusion_holomorphic Q D A p).mdifferentiableAt (x := s)
    (by simp)
  have hs := mfderiv_real_eq_complex hr hc
  have h := mfderiv_comp s
    (A.smoothToExisting.mdifferentiableAt (by simp)) hr
  have hv := congrArg (fun f => f v) h
  change mfderiv 𝓘(ℝ,Fin 1 → ℂ) (J (E := E))
    (projectiveFiberInclusion Q p) s v =
    mfderiv 𝓘(ℝ,ComplexTwistorModel n) (J (E := E)) id
      (projectiveFiberInclusion Q p s)
      (mfderiv 𝓘(ℝ,Fin 1 → ℂ) 𝓘(ℝ,ComplexTwistorModel n)
        (projectiveFiberInclusion Q p) s v) at hv
  rw [hs] at hv
  exact congrArg (L.contactFormReal Q D (projectiveFiberInclusion Q p s)) hv.symm

def fiberContactMap {n : ℕ}
    (A : CompatibleComplexAtlas Q D n) (L : HolomorphicContactLine Q D n A)
    (p : M) (s : ProjectiveSpinor) :
    (Fin 1 → ℂ) →ₗ[ℂ] L.core.Fiber (projectiveFiberInclusion Q p s) := by
  letI := A.charts
  exact (L.contactFormComplex Q D (projectiveFiberInclusion Q p s)).comp
    (mfderiv 𝓘(ℂ,Fin 1 → ℂ) 𝓘(ℂ,ComplexTwistorModel n)
      (projectiveFiberInclusion Q p) s).toLinearMap

theorem fiberContactMap_injective {n : ℕ}
    (A : CompatibleComplexAtlas Q D n) (L : HolomorphicContactLine Q D n A)
    (p : M) (s : ProjectiveSpinor) :
    Function.Injective (fiberContactMap Q D A L p s) := by
  have heq : ⇑(fiberContactMap Q D A L p s) =
      ⇑((L.contactFormReal Q D (projectiveFiberInclusion Q p s)).comp
        (mfderiv 𝓘(ℝ,Fin 1 → ℂ) (J (E := E))
          (projectiveFiberInclusion Q p) s).toLinearMap) := by
    funext v
    exact contactFormComplex_fiber_eq_real Q D A L p s v
  rw [heq]
  exact contactFormReal_fiber_injective Q D L p s

def fiberContactEquiv {n : ℕ}
    (A : CompatibleComplexAtlas Q D n) (L : HolomorphicContactLine Q D n A)
    (p : M) (s : ProjectiveSpinor) :
    (Fin 1 → ℂ) ≃ₗ[ℂ] L.core.Fiber (projectiveFiberInclusion Q p s) := by
  letI : FiniteDimensional ℂ (L.core.Fiber (projectiveFiberInclusion Q p s)) :=
    inferInstanceAs (FiniteDimensional ℂ ℂ)
  exact (fiberContactMap Q D A L p s).linearEquivOfInjective
    (fiberContactMap_injective Q D A L p s) (by
      change Module.finrank ℂ (Fin 1 → ℂ) = Module.finrank ℂ ℂ
      simp)

@[simp] theorem fiberContactEquiv_apply {n : ℕ}
    (A : CompatibleComplexAtlas Q D n) (L : HolomorphicContactLine Q D n A)
    (p : M) (s : ProjectiveSpinor) (v : Fin 1 → ℂ) :
    fiberContactEquiv Q D A L p s v =
      L.contactFormReal Q D (projectiveFiberInclusion Q p s)
        (mfderiv 𝓘(ℝ,Fin 1 → ℂ) (J (E := E))
          (projectiveFiberInclusion Q p) s v) :=
  contactFormComplex_fiber_eq_real Q D A L p s v

end
end QuaternionicSymmetry.ManifoldTwistorProjectiveFiberContactLine
