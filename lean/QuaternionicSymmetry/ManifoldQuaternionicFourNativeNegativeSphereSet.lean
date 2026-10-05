import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSmoothCore
import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereFormOverlap
import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereInjective

/-! The negative-Hodge unit sphere is specified inside the independently
smooth native alternating-two-form bundle by its actual local normalized
quaternionic forms. The image condition is proved chart-independent. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeNegativeSphereSet

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeTwoFormCore
open ManifoldQuaternionicFourNativeSmoothCore
open ManifoldQuaternionicFourNativeSphereFormSmooth
open ManifoldQuaternionicFourNativeSphereFormOverlap
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

/-- The fiberwise negative-unit sphere in a particular tangent chart. -/
def nativeLocalSphereSet (i : atlas E M) (x : M) :
    Set (NativeTwoForm (E := E)) :=
  {α | ∃ a : coefficientSphere,
    α = nativeSphereForm Q i (x,coefficientSphereHomeomorph a)}

include hdim in
theorem nativeSphereForm_transition (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (a : coefficientSphere) :
    nativeCoordChange (E := E) (M := M) i j x
      (nativeSphereForm Q i (x,coefficientSphereHomeomorph a)) =
      nativeSphereForm Q j
        (x,coefficientSphereHomeomorph
          (sphereTransition Q i j x hi hj a)) := by
  have h := congrArg (nativeCoordChange (E := E) (M := M) i j x)
    (nativeSphereForm_overlap Q hdim i j x hi hj a)
  change nativeCoordChange (E := E) (M := M) i j x
      (nativeSphereForm Q i (x,coefficientSphereHomeomorph a)) =
    nativeCoordChange (E := E) (M := M) i j x
      (nativeCoordChange (E := E) (M := M) j i x
        (nativeSphereForm Q j
          (x,coefficientSphereHomeomorph
            (sphereTransition Q i j x hi hj a)))) at h
  rw [nativeCoordChange_comp Q j i j x hj hi hj,
    nativeCoordChange_self Q j x hj] at h
  exact h

include hdim in
theorem nativeLocalSphereSet_transition (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (α : NativeTwoForm (E := E))
    (hα : α ∈ nativeLocalSphereSet Q i x) :
    nativeCoordChange (E := E) (M := M) i j x α ∈
      nativeLocalSphereSet Q j x := by
  obtain ⟨a,rfl⟩ := hα
  exact ⟨sphereTransition Q i j x hi hj a,
    nativeSphereForm_transition Q hdim i j x hi hj a⟩

include hdim in
theorem nativeLocalSphereSet_transition_iff (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (α : NativeTwoForm (E := E)) :
    nativeCoordChange (E := E) (M := M) i j x α ∈
      nativeLocalSphereSet Q j x ↔ α ∈ nativeLocalSphereSet Q i x := by
  constructor
  · intro h
    have h' := nativeLocalSphereSet_transition Q hdim j i x hj hi _ h
    rw [nativeCoordChange_comp Q i j i x hi hj hi,
      nativeCoordChange_self Q i x hi] at h'
    exact h'
  · exact nativeLocalSphereSet_transition Q hdim i j x hi hj α

def nativeNegativeSphereTotal :
    Set (nativeTwoFormVectorCore Q).TotalSpace :=
  {p | p.2 ∈ nativeLocalSphereSet Q
    (Q.frames.adaptedCore.indexAt p.1) p.1}

include hdim in
theorem nativeNegativeSphereTotal_iff_chart
    (p : (nativeTwoFormVectorCore Q).TotalSpace)
    (i : atlas E M) (hi : p.1 ∈ Q.frames.adaptedCore.baseSet i) :
    p ∈ nativeNegativeSphereTotal Q ↔
      (nativeTwoFormVectorCore Q).coordChange
        (Q.frames.adaptedCore.indexAt p.1) i p.1 p.2 ∈
        nativeLocalSphereSet Q i p.1 := by
  exact (nativeLocalSphereSet_transition_iff Q hdim
    (Q.frames.adaptedCore.indexAt p.1) i p.1
      (Q.frames.adaptedCore.mem_baseSet_at p.1) hi p.2).symm

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeNegativeSphereSet
