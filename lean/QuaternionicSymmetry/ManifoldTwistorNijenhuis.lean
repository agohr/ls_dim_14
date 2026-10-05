import QuaternionicSymmetry.ManifoldTwistorGlobalComplexSmooth
import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-! The Nijenhuis expression of the genuine smooth twistor almost-complex
field, formed with the manifold Lie bracket of vector fields. Its vanishing
requires the quaternionic curvature identity and is not asserted here. -/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex

open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

private abbrev I := (𝓘(ℝ,E)).prod (𝓡 2)

/-- Apply the actual twistor almost-complex operator to a vector field. -/
def complexVectorField
    (V : ∀ z : SphereBundleTotal Q, TangentSpace (I (E := E)) z) :
    ∀ z : SphereBundleTotal Q, TangentSpace (I (E := E)) z :=
  fun z => tangentComplex Q D z (V z)

theorem complexVectorField_smooth
    {V : ∀ z : SphereBundleTotal Q, TangentSpace (I (E := E)) z}
    (hV : ContMDiff (I (E := E)) (I (E := E)).tangent ∞
      (fun z => (⟨z,V z⟩ : TangentBundle (I (E := E)) (SphereBundleTotal Q)))) :
    ContMDiff (I (E := E)) (I (E := E)).tangent ∞
      (fun z => (⟨z,complexVectorField Q D V z⟩ :
        TangentBundle (I (E := E)) (SphereBundleTotal Q))) := by
  simpa only [complexVectorField, tangentComplexBundleMap, Function.comp_apply] using
    (tangentComplexBundleMap_smooth Q D).comp hV

theorem complexVectorField_sq
    (V : ∀ z : SphereBundleTotal Q, TangentSpace (I (E := E)) z) :
    complexVectorField Q D (complexVectorField Q D V) = -V := by
  funext z
  exact tangentComplex_sq Q D z (V z)

/-- The Nijenhuis expression, with the convention
`[JV,JW] - J[JV,W] - J[V,JW] - [V,W]`. -/
def nijenhuisField
    (V W : ∀ z : SphereBundleTotal Q, TangentSpace (I (E := E)) z)
    (z : SphereBundleTotal Q) : TangentSpace (I (E := E)) z :=
  VectorField.mlieBracket (I (E := E)) (complexVectorField Q D V)
      (complexVectorField Q D W) z
    - tangentComplex Q D z
        (VectorField.mlieBracket (I (E := E)) (complexVectorField Q D V) W z)
    - tangentComplex Q D z
        (VectorField.mlieBracket (I (E := E)) V (complexVectorField Q D W) z)
    - VectorField.mlieBracket (I (E := E)) V W z

theorem nijenhuisField_swap
    (V W : ∀ z : SphereBundleTotal Q, TangentSpace (I (E := E)) z)
    (z : SphereBundleTotal Q) :
    nijenhuisField Q D V W z = -nijenhuisField Q D W V z := by
  simp only [nijenhuisField]
  rw [VectorField.mlieBracket_swap_apply (I := I (E := E))
      (V := complexVectorField Q D V) (W := complexVectorField Q D W),
    VectorField.mlieBracket_swap_apply (I := I (E := E))
      (V := complexVectorField Q D V) (W := W),
    VectorField.mlieBracket_swap_apply (I := I (E := E))
      (V := V) (W := complexVectorField Q D W),
    VectorField.mlieBracket_swap_apply (I := I (E := E))
      (V := V) (W := W)]
  simp only [map_neg]
  abel

theorem nijenhuisField_complex_left
    (V W : ∀ z : SphereBundleTotal Q, TangentSpace (I (E := E)) z)
    (hV : ContMDiff (I (E := E)) (I (E := E)).tangent ∞
      (fun z => (⟨z,V z⟩ : TangentBundle (I (E := E)) (SphereBundleTotal Q))))
    (z : SphereBundleTotal Q) :
    nijenhuisField Q D (complexVectorField Q D V) W z =
      -tangentComplex Q D z (nijenhuisField Q D V W z) := by
  have hVdiff : MDifferentiableAt (I (E := E)) (I (E := E)).tangent
      (fun z => (⟨z,V z⟩ : TangentBundle (I (E := E)) (SphereBundleTotal Q))) z :=
    hV.contMDiffAt.mdifferentiableAt (by simp)
  have hneg1 := VectorField.mlieBracket_const_smul_left
    (I := I (E := E)) (V := V) (W := complexVectorField Q D W)
    (c := (-1 : ℝ)) hVdiff
  have hneg2 := VectorField.mlieBracket_const_smul_left
    (I := I (E := E)) (V := V) (W := W)
    (c := (-1 : ℝ)) hVdiff
  rw [nijenhuisField, nijenhuisField, complexVectorField_sq]
  simp only [neg_one_smul] at hneg1 hneg2
  rw [hneg1, hneg2]
  simp only [map_sub, map_neg, tangentComplex_sq]
  abel

theorem nijenhuisField_complex_right
    (V W : ∀ z : SphereBundleTotal Q, TangentSpace (I (E := E)) z)
    (hW : ContMDiff (I (E := E)) (I (E := E)).tangent ∞
      (fun z => (⟨z,W z⟩ : TangentBundle (I (E := E)) (SphereBundleTotal Q))))
    (z : SphereBundleTotal Q) :
    nijenhuisField Q D V (complexVectorField Q D W) z =
      -tangentComplex Q D z (nijenhuisField Q D V W z) := by
  calc
    nijenhuisField Q D V (complexVectorField Q D W) z =
        -nijenhuisField Q D (complexVectorField Q D W) V z :=
      nijenhuisField_swap Q D V (complexVectorField Q D W) z
    _ = tangentComplex Q D z (nijenhuisField Q D W V z) := by
      rw [nijenhuisField_complex_left Q D W V hW z]
      simp
    _ = -tangentComplex Q D z (nijenhuisField Q D V W z) := by
      rw [nijenhuisField_swap Q D W V z]
      simp

theorem nijenhuisField_complex_both
    (V W : ∀ z : SphereBundleTotal Q, TangentSpace (I (E := E)) z)
    (hV : ContMDiff (I (E := E)) (I (E := E)).tangent ∞
      (fun z => (⟨z,V z⟩ : TangentBundle (I (E := E)) (SphereBundleTotal Q))))
    (hW : ContMDiff (I (E := E)) (I (E := E)).tangent ∞
      (fun z => (⟨z,W z⟩ : TangentBundle (I (E := E)) (SphereBundleTotal Q))))
    (z : SphereBundleTotal Q) :
    nijenhuisField Q D (complexVectorField Q D V)
      (complexVectorField Q D W) z = -nijenhuisField Q D V W z := by
  rw [nijenhuisField_complex_left Q D V (complexVectorField Q D W) hV z,
    nijenhuisField_complex_right Q D V W hW z]
  simp only [map_neg, tangentComplex_sq, neg_neg]

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
