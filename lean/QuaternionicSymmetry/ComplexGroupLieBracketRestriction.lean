import QuaternionicSymmetry.ComplexManifoldLieBracketRestriction
import QuaternionicSymmetry.CommutingLieHomDerivatives

/-! For the same complex Lie-group atlas the real and complex tangent
brackets coincide. Consequently pointwise commutation of real-smooth
homomorphisms into it implies commutation in its genuine complex Lie algebra. -/

namespace QuaternionicSymmetry.ComplexGroupLieBracketRestriction

open ComplexManifoldDerivativeScalarRestriction ComplexManifoldLieBracketRestriction
  CommutingLieHomDerivatives
open scoped Manifold ContDiff
noncomputable section

variable {V K : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [Group K] [TopologicalSpace K] [ChartedSpace V K]
  [IsManifold 𝓘(ℂ,V) ∞ K] [LieGroup 𝓘(ℂ,V) ∞ K]
  [IsManifold 𝓘(ℝ,V) ∞ K] [LieGroup 𝓘(ℝ,V) ∞ K]

local instance realMin : ENat.LEInfty (minSmoothness ℝ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

local instance complexMin : ENat.LEInfty (minSmoothness ℂ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

theorem mulInvariantVectorField_real_eq_complex (v : V) :
    mulInvariantVectorField (I := 𝓘(ℝ,V)) (G := K) v =
      mulInvariantVectorField (I := 𝓘(ℂ,V)) (G := K) v := by
  funext g
  unfold mulInvariantVectorField
  have hr : MDifferentiableAt 𝓘(ℝ,V) 𝓘(ℝ,V) (g * ·) (1 : K) :=
    (contMDiff_mul_left (I := 𝓘(ℝ,V)) (n := ∞)).mdifferentiableAt (by simp)
  have hc : MDifferentiableAt 𝓘(ℂ,V) 𝓘(ℂ,V) (g * ·) (1 : K) :=
    (contMDiff_mul_left (I := 𝓘(ℂ,V)) (n := ∞)).mdifferentiableAt (by simp)
  exact congrArg (fun A : V →L[ℝ] V => A v) (mfderiv_real_eq_complex hr hc)

theorem bracket_real_eq_complex (v w : V) :
    @Bracket.bracket (GroupLieAlgebra 𝓘(ℝ,V) K) (GroupLieAlgebra 𝓘(ℝ,V) K)
        inferInstance v w =
      @Bracket.bracket (GroupLieAlgebra 𝓘(ℂ,V) K) (GroupLieAlgebra 𝓘(ℂ,V) K)
        inferInstance v w := by
  rw [GroupLieAlgebra.bracket_def, GroupLieAlgebra.bracket_def,
    mulInvariantVectorField_real_eq_complex, mulInvariantVectorField_real_eq_complex]
  exact mlieBracket_real_eq_complex _ _ (1 : K)
    (mdifferentiableAt_mulInvariantVectorField (I := 𝓘(ℂ,V)) v)
    (mdifferentiableAt_mulInvariantVectorField (I := 𝓘(ℂ,V)) w)

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [IsManifold 𝓘(ℝ,E) ∞ G] [LieGroup 𝓘(ℝ,E) ∞ G]
  [Group H] [TopologicalSpace H] [ChartedSpace F H]
  [IsManifold 𝓘(ℝ,F) ∞ H] [LieGroup 𝓘(ℝ,F) ∞ H]

theorem complex_bracket_real_derivatives_eq_zero (f : G →* K) (g : H →* K)
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ f)
    (hg : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,V) ∞ g)
    (hComm : ∀ a b, Commute (f a) (g b))
    (v : GroupLieAlgebra 𝓘(ℝ,E) G) (w : GroupLieAlgebra 𝓘(ℝ,F) H) :
    @Bracket.bracket (GroupLieAlgebra 𝓘(ℂ,V) K) (GroupLieAlgebra 𝓘(ℂ,V) K)
      inferInstance (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f 1 v)
        (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) g 1 w) = 0 := by
  rw [← bracket_real_eq_complex (V := V) (K := K)]
  exact bracket_derivatives_eq_zero f g hf hg hComm v w

end
end QuaternionicSymmetry.ComplexGroupLieBracketRestriction
