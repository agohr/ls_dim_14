import QuaternionicSymmetry.ComplexSubmanifoldInput

/-! The dimension of the complex atlas in BG-C4 is not an extra source
assumption. Differentiating its genuine two-way real atlas comparison
identifies tangent models and proves that the original real dimension is
twice the complex dimension. -/

namespace QuaternionicSymmetry.ComplexSubmanifoldInput

open scoped Manifold ContDiff
noncomputable section

variable {F B : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ F] [TopologicalSpace B] [ChartedSpace F B]
  {S : Set B} {k m : ℕ} (A : RealEmbeddedAtlas (F := F) S k)
  (C : CompatibleComplexAtlas A m)

/-- The derivative of the actual identity atlas comparison is a real
linear equivalence, with inverse the derivative of the reverse identity. -/
def CompatibleComplexAtlas.tangentRealEquiv (x : S) :
    EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] EuclideanSpace ℂ (Fin m) := by
  letI := A.charts
  letI := C.charts
  letI := A.manifold
  letI := C.realManifold
  let T := mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k))
    𝓘(ℝ,EuclideanSpace ℂ (Fin m)) (id : S → S) x
  let U := mfderiv 𝓘(ℝ,EuclideanSpace ℂ (Fin m))
    𝓘(ℝ,EuclideanSpace ℝ (Fin k)) (id : S → S) x
  have hT := C.smoothFromReal.mdifferentiableAt (by simp) (x := x)
  have hU := C.smoothToReal.mdifferentiableAt (by simp) (x := x)
  refine { T.toLinearMap with
    invFun := U
    left_inv := ?_
    right_inv := ?_ }
  · intro v
    have h := mfderiv_comp x hU hT
    change mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k))
      𝓘(ℝ,EuclideanSpace ℝ (Fin k)) id x = U.comp T at h
    rw [mfderiv_id] at h
    exact (congrArg (fun L : EuclideanSpace ℝ (Fin k) →L[ℝ]
      EuclideanSpace ℝ (Fin k) => L v) h).symm
  · intro v
    have h := mfderiv_comp x hT hU
    change mfderiv 𝓘(ℝ,EuclideanSpace ℂ (Fin m))
      𝓘(ℝ,EuclideanSpace ℂ (Fin m)) id x = T.comp U at h
    rw [mfderiv_id] at h
    exact (congrArg (fun L : EuclideanSpace ℂ (Fin m) →L[ℝ]
      EuclideanSpace ℂ (Fin m) => L v) h).symm

include A C in
theorem CompatibleComplexAtlas.real_dimension_eq_twice (x : S) :
    k = 2 * m := by
  have h := (CompatibleComplexAtlas.tangentRealEquiv A C x).finrank_eq
  simpa only [finrank_euclideanSpace_fin, finrank_real_of_complex] using h

end
end QuaternionicSymmetry.ComplexSubmanifoldInput
