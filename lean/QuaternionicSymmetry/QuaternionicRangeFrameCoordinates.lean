import QuaternionicSymmetry.QuaternionicSmoothRangeFrame
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-! An orthonormal frame of an injective map's range gives invertible
coordinates on its domain and identifies the exact pullback metric. -/
namespace QuaternionicSymmetry.QuaternionicRangeFrameCoordinates
open scoped ContDiff Topology
noncomputable section
variable {E F X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup X] [NormedSpace ℝ X]

variable (A B : F →L[ℝ] E)
  (hB : ∀ v w, inner ℝ (B v) (B w) = inner ℝ v w)
  (hRange : LinearMap.range B.toLinearMap = LinearMap.range A.toLinearMap)

include hB in
theorem adjoint_left_inverse (v : F) : B.adjoint (B v) = v := by
  apply ext_inner_right ℝ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_left,hB]

include hB hRange in
theorem frame_coordinates (v : F) : B (B.adjoint (A v)) = A v := by
  have hm : A v ∈ LinearMap.range B.toLinearMap := by
    rw [hRange]
    exact ⟨v,rfl⟩
  obtain ⟨w,hw⟩ := hm
  change B w = A v at hw
  rw [← hw,adjoint_left_inverse B hB]

include hB hRange in
theorem coordinates_inner (v w : F) :
    inner ℝ (B.adjoint (A v)) (B.adjoint (A w)) = inner ℝ (A v) (A w) := by
  rw [← hB,frame_coordinates A B hB hRange,frame_coordinates A B hB hRange]

include hB hRange in
theorem coordinates_injective (hA : Function.Injective A) :
    Function.Injective (B.adjoint.comp A) := by
  intro v w h
  apply hA
  rw [← frame_coordinates A B hB hRange v,← frame_coordinates A B hB hRange w]
  exact congrArg B h

def coordinatesEquiv (hA : Function.Injective A) : F ≃L[ℝ] F :=
  LinearEquiv.toContinuousLinearEquiv (LinearEquiv.ofBijective (B.adjoint.comp A).toLinearMap
    ⟨coordinates_injective A B hB hRange hA,
      (LinearMap.injective_iff_surjective).mp (coordinates_injective A B hB hRange hA)⟩)

theorem coordinates_contDiffAt (A B : X → F →L[ℝ] E) (a : X)
    (hA : ContDiffAt ℝ ∞ A a) (hB : ContDiffAt ℝ ∞ B a) :
    ContDiffAt ℝ ∞ (fun y => (B y).adjoint.comp (A y)) a :=
  ((ContinuousLinearMap.adjoint : (F →L[ℝ] E) ≃ₗᵢ[ℝ] (E →L[ℝ] F)).contDiff.contDiffAt.comp
    a hB).clm_comp hA

end
end QuaternionicSymmetry.QuaternionicRangeFrameCoordinates
