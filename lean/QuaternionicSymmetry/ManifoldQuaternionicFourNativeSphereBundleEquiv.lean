import QuaternionicSymmetry.ManifoldQuaternionicFourNativeGlobalHodgeSphere
import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereLocalCharts

/-! A literal fiber-preserving equivalence between the original twistor
sphere and the negative-Hodge unit sphere subset of the independently smooth
native alternating-two-form bundle. Topological and smooth total-space
properties are proved separately. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereBundleEquiv

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeSmoothCore
open ManifoldQuaternionicFourNativeNegativeSphereSet
open ManifoldQuaternionicFourNativeCoefficientExtraction
open ManifoldQuaternionicFourNativeSphereFormSmooth
open ManifoldTwistorSphereBundle
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
local instance : TopologicalSpace (nativeTwoFormVectorCore Q).TotalSpace :=
  (nativeTwoFormVectorCore Q).toTopologicalSpace

def NativeSphereBundleTotal :=
  {p : (nativeTwoFormVectorCore Q).TotalSpace //
    p ∈ nativeNegativeSphereTotal Q}

local instance : TopologicalSpace (NativeSphereBundleTotal Q) := by
  unfold NativeSphereBundleTotal
  infer_instance

def twistorToNativeSphere (z : TwistorSphere Q) :
    NativeSphereBundleTotal Q := by
  let x := projection Q z
  let k := Q.frames.adaptedCore.indexAt x
  have hk : x ∈ Q.frames.adaptedCore.baseSet k :=
    Q.frames.adaptedCore.mem_baseSet_at x
  let a := localCoordinate Q k z hk
  exact ⟨⟨x,nativeSphereForm Q k
    (x,coefficientSphereHomeomorph a)⟩, ⟨a,rfl⟩⟩

private theorem preferredCoefficient_unit (p : NativeSphereBundleTotal Q) :
    squareNorm (nativeCoefficientRaw Q hdim
      (Q.frames.adaptedCore.indexAt p.1.1) p.1.1 p.1.2) = 1 := by
  let k := Q.frames.adaptedCore.indexAt p.1.1
  obtain ⟨a,ha⟩ := p.2
  have hk := Q.frames.adaptedCore.mem_baseSet_at p.1.1
  rw [ha, nativeCoefficientRaw_map Q hdim k p.1.1 hk
    (coefficientSphereHomeomorph a)]
  exact a.2

def nativeSphereToTwistor (p : NativeSphereBundleTotal Q) : TwistorSphere Q := by
  let x := p.1.1
  let k := Q.frames.adaptedCore.indexAt x
  have hk : x ∈ Q.frames.adaptedCore.baseSet k :=
    Q.frames.adaptedCore.mem_baseSet_at x
  let a : coefficientSphere :=
    ⟨nativeCoefficientRaw Q hdim k x p.1.2,
      preferredCoefficient_unit Q hdim p⟩
  exact pointOfLocal Q k x hk a

theorem nativeSphereToTwistor_left (z : TwistorSphere Q) :
    nativeSphereToTwistor Q hdim (twistorToNativeSphere Q z) = z := by
  let x := projection Q z
  let k := Q.frames.adaptedCore.indexAt x
  have hk : x ∈ Q.frames.adaptedCore.baseSet k :=
    Q.frames.adaptedCore.mem_baseSet_at x
  have hcoeff :
      (⟨nativeCoefficientRaw Q hdim k x
        (nativeSphereForm Q k
          (x,coefficientSphereHomeomorph (localCoordinate Q k z hk))),
        preferredCoefficient_unit Q hdim (twistorToNativeSphere Q z)⟩ :
          coefficientSphere) = localCoordinate Q k z hk := by
    apply Subtype.ext
    exact nativeCoefficientRaw_map Q hdim k x hk
      (coefficientSphereHomeomorph (localCoordinate Q k z hk))
  change pointOfLocal Q k x hk
      (⟨nativeCoefficientRaw Q hdim k x
        (nativeSphereForm Q k
          (x,coefficientSphereHomeomorph (localCoordinate Q k z hk))),
        preferredCoefficient_unit Q hdim (twistorToNativeSphere Q z)⟩ :
          coefficientSphere) = z
  rw [hcoeff]
  exact pointOfLocal_localCoordinate Q k z hk

theorem twistorToNativeSphere_right (p : NativeSphereBundleTotal Q) :
    twistorToNativeSphere Q (nativeSphereToTwistor Q hdim p) = p := by
  let x := p.1.1
  let k := Q.frames.adaptedCore.indexAt x
  have hk : x ∈ Q.frames.adaptedCore.baseSet k :=
    Q.frames.adaptedCore.mem_baseSet_at x
  obtain ⟨a,ha⟩ := p.2
  have hraw : nativeCoefficientRaw Q hdim k x p.1.2 = a.1 := by
    rw [ha]
    simpa using nativeCoefficientRaw_map Q hdim k x hk
      (coefficientSphereHomeomorph a)
  have hcoeff :
      (⟨nativeCoefficientRaw Q hdim k x p.1.2,
        preferredCoefficient_unit Q hdim p⟩ : coefficientSphere) = a := by
    apply Subtype.ext
    exact hraw
  let c : coefficientSphere :=
    ⟨nativeCoefficientRaw Q hdim k x p.1.2,
      preferredCoefficient_unit Q hdim p⟩
  have hc : c = a := hcoeff
  apply Subtype.ext
  apply Bundle.TotalSpace.ext
  · rfl
  · apply heq_of_eq
    change nativeSphereForm Q k
      (x,coefficientSphereHomeomorph
        (localCoordinate Q k (pointOfLocal Q k x hk c)
          (by simpa [projection_pointOfLocal] using hk))) = p.1.2
    rw [localCoordinate_pointOfLocal Q k x hk c, hc]
    exact ha.symm

def twistorNativeSphereEquiv : TwistorSphere Q ≃ NativeSphereBundleTotal Q where
  toFun := twistorToNativeSphere Q
  invFun := nativeSphereToTwistor Q hdim
  left_inv := nativeSphereToTwistor_left Q hdim
  right_inv := twistorToNativeSphere_right Q hdim

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereBundleEquiv
