import QuaternionicSymmetry.ManifoldQuaternionicFourHodgeOverlapBilinear

/-! The canonical exterior Hodge star commutes with the actual adapted
tangent transition, using the source-built SO(3) rotation on Q and the true
exterior pairing. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourHodgeOverlapExterior

open Module
open FourDimensionalExteriorHodge
open FourDimensionalExteriorEvaluationBilinear
open FourDimensionalExteriorCanonicalHodge
open ManifoldQuaternionicFourHodgeOverlapBilinear
open ManifoldQuaternionicMetric
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

private theorem evaluate_swap (α : TwoForm E) (v w : E) :
    BilinearExterior.evaluate w v α = -BilinearExterior.evaluate v w α := by
  have h := (exteriorPower.ιMulti ℝ 2 (M := E)).map_swap
    ![v,w] (i := 0) (j := 1) (by decide)
  have hp : (![v,w] : Fin 2 → E) ∘ Equiv.swap 0 1 = ![w,v] := by
    funext i
    fin_cases i <;> simp
  rw [hp] at h
  simp [BilinearExterior.evaluate, h]

/-- Pull back a genuine exterior two-covector by a real-linear map. The
finite basis only implements exterior duality, and is proved irrelevant. -/
def pullbackTwoForm (b : Basis (Fin 4) ℝ E) (T : E →ₗ[ℝ] E)
    (α : TwoForm E) : TwoForm E :=
  BilinearExterior.ofBilinear b (bilinearPullback T (bilinearOfTwoForm α))

theorem pullbackTwoForm_basis_independent (b c : Basis (Fin 4) ℝ E)
    (T : E →ₗ[ℝ] E) (α : TwoForm E) :
    pullbackTwoForm b T α = pullbackTwoForm c T α :=
  ExteriorDuality.ofBilinear_basis_independent b c _

theorem evaluate_pullbackTwoForm (b : Basis (Fin 4) ℝ E)
    (T : E →ₗ[ℝ] E) (α : TwoForm E) (v w : E) :
    BilinearExterior.evaluate v w (pullbackTwoForm b T α) =
      BilinearExterior.evaluate (T v) (T w) α := by
  apply BilinearExterior.evaluate_of_skew
  intro a c
  change BilinearExterior.evaluate (T a) (T c) α =
    -BilinearExterior.evaluate (T c) (T a) α
  exact evaluate_swap α (T c) (T a)

private theorem bilinearOf_pullbackTwoForm (b : Basis (Fin 4) ℝ E)
    (T : E →ₗ[ℝ] E) (α : TwoForm E) :
    bilinearOfTwoForm (pullbackTwoForm b T α) =
      bilinearPullback T (bilinearOfTwoForm α) := by
  ext v w
  rw [bilinearOfTwoForm_apply, evaluate_pullbackTwoForm,
    bilinearPullback_apply, bilinearOfTwoForm_apply]

theorem evaluate_canonicalStar (S : QuaternionicStructure E)
    (hdim : Module.finrank ℝ E = 4) (α : TwoForm E) (v w : E) :
    BilinearExterior.evaluate v w (canonicalStar S hdim α) =
      quaternionicAverage S (bilinearOfTwoForm α) v w := by
  obtain ⟨z, hz0⟩ := exists_ne (0 : E)
  let z' := NormedSpace.normalize z
  have hz : ‖z'‖ = 1 := NormedSpace.norm_normalize hz0
  rw [canonicalStar_eq_frameStar S hdim z' hz]
  rw [← quaternionicHodgeForm_eq_frameStar S hdim z' hz α]
  rw [evaluate_quaternionicHodgeForm]
  rfl

/-- Hodge naturality on the actual adapted overlap, on genuine exterior
two-covectors rather than only six coefficients or a chosen frame. -/
theorem canonicalStar_overlap
    (Q : SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (hdim : Module.finrank ℝ E = 4)
    (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (b : Basis (Fin 4) ℝ E) (α : TwoForm E) :
    pullbackTwoForm b (Q.frames.coordChange i j x).toLinearMap
      (canonicalStar (Q.reduction.Q j) hdim α) =
    canonicalStar (Q.reduction.Q i) hdim
      (pullbackTwoForm b (Q.frames.coordChange i j x).toLinearMap α) := by
  apply ExteriorDuality.twoform_ext b
  intro v w
  rw [evaluate_pullbackTwoForm,
    evaluate_canonicalStar,
    evaluate_canonicalStar,
    bilinearOf_pullbackTwoForm]
  exact (quaternionicAverage_transition Q i j x hi hj
    (bilinearOfTwoForm α) v w).symm

end
end QuaternionicSymmetry.ManifoldQuaternionicFourHodgeOverlapExterior
