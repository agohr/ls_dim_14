import QuaternionicSymmetry.ManifoldTwistorVerticalLine
import Mathlib.LinearAlgebra.Projection

/-! The connection splits each genuine twistor tangent fiber into horizontal
and vertical planes. The horizontal plane is invariant under the smooth
almost-complex field and is the differential-geometric contact-distribution
candidate. Contact nondegeneracy and holomorphicity remain separate. -/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex

open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldTwistorVerticalComplex
open QuaternionicSymmetry.ManifoldTwistorHorizontalConnection
open QuaternionicSymmetry.ManifoldTwistorLocalAlmostComplex
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

private theorem centerTarget (z : SphereBundleTotal Q) :
    (extChartAt 𝓘(ℝ,E) z.1 z.1) ∈
      (extChartAt 𝓘(ℝ,E) z.1).target :=
  (extChartAt 𝓘(ℝ,E) z.1).map_source (mem_extChartAt_source z.1)

/-- Preferred tangent coordinates followed by the actual induced
rank-three connection splitting. -/
def connectionTangentEquiv (z : SphereBundleTotal Q) :
    TangentSpace (I (E := E)) z ≃ₗ[ℝ]
      E × verticalSubmodule (coefficientSphereHomeomorph.symm z.2) :=
  (preferredTangentEquiv Q z).trans
    (connectionSplit Q D z.1 (extChartAt 𝓘(ℝ,E) z.1 z.1)
      (centerTarget Q z) (coefficientSphereHomeomorph.symm z.2))

/-- The actual horizontal tangent plane selected by the compatible
connection. -/
def horizontalTangentSubmodule (z : SphereBundleTotal Q) :
    Submodule ℝ (TangentSpace (I (E := E)) z) :=
  LinearMap.ker ((LinearMap.snd ℝ E
    (verticalSubmodule (coefficientSphereHomeomorph.symm z.2))).comp
      (connectionTangentEquiv Q D z).toLinearMap)

theorem mem_horizontalTangentSubmodule_iff (z : SphereBundleTotal Q)
    (v : TangentSpace (I (E := E)) z) :
    v ∈ horizontalTangentSubmodule Q D z ↔
      (connectionTangentEquiv Q D z v).2 = 0 := Iff.rfl

theorem mem_verticalTangentSubmodule_iff_connection (z : SphereBundleTotal Q)
    (v : TangentSpace (I (E := E)) z) :
    v ∈ verticalTangentSubmodule Q z ↔
      (connectionTangentEquiv Q D z v).1 = 0 := by
  rw [mem_verticalTangentSubmodule_iff]
  rfl

/-- The connection horizontal plane and the true projection kernel are
complementary on every twistor tangent fiber. -/
theorem horizontal_vertical_isCompl (z : SphereBundleTotal Q) :
    IsCompl (horizontalTangentSubmodule Q D z)
      (verticalTangentSubmodule Q z) := by
  let e := connectionTangentEquiv Q D z
  constructor
  · rw [disjoint_iff_inf_le]
    intro v hv
    have hh : (e v).2 = 0 :=
      (mem_horizontalTangentSubmodule_iff Q D z v).mp hv.1
    have hvv : (e v).1 = 0 :=
      (mem_verticalTangentSubmodule_iff_connection Q D z v).mp hv.2
    have he : e v = 0 := Prod.ext hvv hh
    exact (e.map_eq_zero_iff).mp he
  · rw [codisjoint_iff_le_sup]
    intro v _
    let h := e.symm ((e v).1,0)
    let w := e.symm (0,(e v).2)
    have hh : h ∈ horizontalTangentSubmodule Q D z := by
      rw [mem_horizontalTangentSubmodule_iff]
      change (e (e.symm ((e v).1,0))).2 = 0
      rw [e.apply_symm_apply]
    have hw : w ∈ verticalTangentSubmodule Q z := by
      rw [mem_verticalTangentSubmodule_iff_connection]
      change (e (e.symm (0,(e v).2))).1 = 0
      rw [e.apply_symm_apply]
    rw [Submodule.mem_sup']
    refine ⟨⟨h, hh⟩, ⟨w, hw⟩, ?_⟩
    apply e.injective
    simp [h, w, e.map_add]

/-- At each twistor point the quotient by the horizontal distribution is
canonically the true vertical tangent plane. -/
def contactQuotientEquiv (z : SphereBundleTotal Q) :
    (TangentSpace (I (E := E)) z ⧸ horizontalTangentSubmodule Q D z) ≃ₗ[ℝ]
      verticalTangentSubmodule Q z :=
  Submodule.quotientEquivOfIsCompl _ _ (horizontal_vertical_isCompl Q D z)

theorem contactQuotient_finrank (z : SphereBundleTotal Q) :
    Module.finrank ℝ
      (TangentSpace (I (E := E)) z ⧸ horizontalTangentSubmodule Q D z) = 2 := by
  rw [(contactQuotientEquiv Q D z).finrank_eq]
  exact verticalTangent_finrank Q z

theorem tangentComplex_connectionTangentEquiv (z : SphereBundleTotal Q)
    (v : TangentSpace (I (E := E)) z) :
    connectionTangentEquiv Q D z (tangentComplex Q D z v) =
      chartSplitComplex Q z.1 (extChartAt 𝓘(ℝ,E) z.1 z.1)
        (coefficientSphereHomeomorph.symm z.2)
        (connectionTangentEquiv Q D z v) := by
  dsimp [connectionTangentEquiv, tangentComplex, localTwistorComplex]
  simp [connectionSplit, chartSplitComplex]
  constructor
  · rfl
  · let a := coefficientSphereHomeomorph.symm z.2
    let y := extChartAt 𝓘(ℝ,E) z.1 z.1
    let u := (preferredTangentEquiv Q z v).1
    let w := (preferredTangentEquiv Q z v).2
    change verticalComplex a w +
        verticalComplex a (connectionVertical Q D z.1 y (centerTarget Q z) a u) -
        connectionVertical Q D z.1 y (centerTarget Q z) a
          (chartBaseComplex Q z.1 y a u) +
        connectionVertical Q D z.1 y (centerTarget Q z) a
          (chartBaseComplex Q z.1 y a u) =
      verticalComplex a w +
        verticalComplex a (connectionVertical Q D z.1 y (centerTarget Q z) a u)
    abel

theorem tangentComplex_mem_horizontalTangentSubmodule
    (z : SphereBundleTotal Q) (v : TangentSpace (I (E := E)) z)
    (hv : v ∈ horizontalTangentSubmodule Q D z) :
    tangentComplex Q D z v ∈ horizontalTangentSubmodule Q D z := by
  rw [mem_horizontalTangentSubmodule_iff] at hv ⊢
  rw [tangentComplex_connectionTangentEquiv]
  simp [chartSplitComplex, hv]

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
