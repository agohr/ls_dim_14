import QuaternionicSymmetry.ManifoldTwistorVerticalTangent
import QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrientation

/-! The vertical complex rotation is natural under the actual oriented
quaternionic rank-three frame transitions. Its ambient cross-product formula
varies smoothly over Mathlib’s geometric sphere. -/
namespace QuaternionicSymmetry.ManifoldTwistorVerticalComplex
open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrthogonal
open QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrientation
open scoped Matrix Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E] [FiniteDimensional ℝ E]
 [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

def verticalTransition (i j : atlas E M) (x : M)
 (hi : x ∈ Q.frames.adaptedCore.baseSet i)
 (hj : x ∈ Q.frames.adaptedCore.baseSet j)
 (a : coefficientSphere) :
 verticalSubmodule a →ₗ[ℝ] verticalSubmodule (sphereTransition Q i j x hi hj a) where
 toFun v := ⟨Q.reduction.rankThreeCoordChange i j x v.1, by
   have h := rankThreeCoordChange_dot Q i j x hi hj a.1 v.1
   change (∑ t : Fin 3,
     (Q.reduction.rankThreeCoordChange i j x a.1) t *
       (Q.reduction.rankThreeCoordChange i j x v.1) t) = 0
   rw [h]
   simpa only [dotProduct] using v.2⟩
 map_add' u v := by
   apply Subtype.ext
   exact (Q.reduction.rankThreeCoordChange i j x).map_add u.1 v.1
 map_smul' r v := by
   apply Subtype.ext
   exact (Q.reduction.rankThreeCoordChange i j x).map_smul r v.1

theorem verticalTransition_complex (i j : atlas E M) (x : M)
 (hi : x ∈ Q.frames.adaptedCore.baseSet i)
 (hj : x ∈ Q.frames.adaptedCore.baseSet j)
 (a : coefficientSphere) (v : verticalSubmodule a) :
 verticalTransition Q i j x hi hj a (verticalComplex a v) =
 verticalComplex (sphereTransition Q i j x hi hj a)
   (verticalTransition Q i j x hi hj a v) := by
 apply Subtype.ext
 exact rankThreeCoordChange_cross Q i j x hi hj a.1 v.1
local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

theorem crossSmooth : ContDiff ℝ ∞
    (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => crossProduct p.1 p.2) := by
  rw [contDiff_pi]
  intro i
  fin_cases i <;> simp [cross_apply, Matrix.cons_val] <;> fun_prop

theorem sphereCrossSmooth :
  ContMDiff ((𝓡 2).prod 𝓘(ℝ,Fin 3 → ℝ)) 𝓘(ℝ,Fin 3 → ℝ) ∞
    (fun p : geometricSphere × (Fin 3 → ℝ) =>
      crossProduct ((coefficientSphereHomeomorph.symm p.1).1) p.2) := by
  have hcoef : ContMDiff (𝓡 2) 𝓘(ℝ,Fin 3 → ℝ) ∞
      (fun a : geometricSphere => (coefficientSphereHomeomorph.symm a).1) := by
    convert ((EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap.contMDiff).comp
      (contMDiff_coe_sphere (n := 2) (E := EuclideanThree)) using 1
  have hA (i : Fin 3) : ContMDiff ((𝓡 2).prod 𝓘(ℝ,Fin 3 → ℝ)) 𝓘(ℝ) ∞
      (fun p : geometricSphere × (Fin 3 → ℝ) =>
        (coefficientSphereHomeomorph.symm p.1).1 i) :=
    (contMDiff_pi_space.mp (hcoef.comp contMDiff_fst)) i
  have hB (i : Fin 3) : ContMDiff ((𝓡 2).prod 𝓘(ℝ,Fin 3 → ℝ)) 𝓘(ℝ) ∞
      (fun p : geometricSphere × (Fin 3 → ℝ) => p.2 i) :=
    (contMDiff_pi_space.mp (contMDiff_snd (I := 𝓡 2))) i
  rw [contMDiff_pi_space]
  intro i
  fin_cases i <;> simp only [cross_apply] <;>
    first
      | exact ((hA 1).smul (hB 2)).sub ((hA 2).smul (hB 1))
      | exact ((hA 2).smul (hB 0)).sub ((hA 0).smul (hB 2))
      | exact ((hA 0).smul (hB 1)).sub ((hA 1).smul (hB 0))
end
end QuaternionicSymmetry.ManifoldTwistorVerticalComplex
