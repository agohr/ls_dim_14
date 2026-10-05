import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereLocalTrivialization

/-! Genuine local product homeomorphisms of the native negative-Hodge sphere
with the base times Mathlib's geometric unit two-sphere. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereGeometricLocal

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeSphereLocalTrivialization
open ManifoldQuaternionicFourNativeSphereLocalCharts
open ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : TopologicalSpace (ManifoldQuaternionicFourNativeSmoothCore.nativeTwoFormVectorCore Q).TotalSpace :=
  (ManifoldQuaternionicFourNativeSmoothCore.nativeTwoFormVectorCore Q).toTopologicalSpace
local instance : TopologicalSpace (ManifoldQuaternionicFourNativeSphereBundleEquiv.NativeSphereBundleTotal Q) := by
  unfold ManifoldQuaternionicFourNativeSphereBundleEquiv.NativeSphereBundleTotal
  infer_instance
local instance (i : atlas E M) : TopologicalSpace (coefficientLocalDomain Q i) := by
  unfold coefficientLocalDomain
  infer_instance
local instance (i : atlas E M) : TopologicalSpace (nativeLocalSphereTotal Q i) := by
  unfold nativeLocalSphereTotal
  infer_instance

def geometricLocalDomain (i : atlas E M) :=
  {p : M × geometricSphere // p.1 ∈ Q.frames.adaptedCore.baseSet i}

local instance (i : atlas E M) : TopologicalSpace (geometricLocalDomain Q i) := by
  unfold geometricLocalDomain
  infer_instance

def coefficientGeometricLocalHomeomorph (i : atlas E M) :
    coefficientLocalDomain Q i ≃ₜ geometricLocalDomain Q i where
  toFun p := ⟨(p.1.1,coefficientSphereHomeomorph p.1.2),p.2⟩
  invFun p := ⟨(p.1.1,coefficientSphereHomeomorph.symm p.1.2),p.2⟩
  left_inv p := by apply Subtype.ext; apply Prod.ext <;> simp
  right_inv p := by apply Subtype.ext; apply Prod.ext <;> simp
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      (coefficientSphereHomeomorph.continuous.comp
        (continuous_snd.comp continuous_subtype_val))
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      (coefficientSphereHomeomorph.symm.continuous.comp
        (continuous_snd.comp continuous_subtype_val))

def nativeGeometricLocalHomeomorph (i : atlas E M) :
    nativeLocalSphereTotal Q i ≃ₜ geometricLocalDomain Q i :=
  (nativeLocalTrivializationHomeomorph Q hdim i).trans
    (coefficientGeometricLocalHomeomorph Q i)

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereGeometricLocal
