import QuaternionicSymmetry.ManifoldTwistorGlobalContactProjector

/-! The global smooth twistor horizontal projector has precisely the
connection-horizontal image and vertical projection-kernel as its kernel.
These are complementary J-invariant fiber subspaces of constant vertical
rank two. This is the smooth-projector characterization of the two
subbundles; holomorphic bundle charts remain to be constructed. -/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex

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

def horizontalProjectionLinear (z : SphereBundleTotal Q) :
    TangentSpace (I (E := E)) z →ₗ[ℝ] TangentSpace (I (E := E)) z where
  toFun := horizontalProjection Q D z
  map_add' u v := by
    apply (connectionTangentEquiv Q D z).injective
    simp [horizontalProjection, map_add]
  map_smul' r u := by
    apply (connectionTangentEquiv Q D z).injective
    simp [horizontalProjection, map_smul]

theorem horizontalProjection_mem (z : SphereBundleTotal Q)
    (v : TangentSpace (I (E := E)) z) :
    horizontalProjection Q D z v ∈ horizontalTangentSubmodule Q D z := by
  rw [mem_horizontalTangentSubmodule_iff]
  simp [horizontalProjection]

theorem horizontalProjection_fix (z : SphereBundleTotal Q)
    (v : TangentSpace (I (E := E)) z)
    (hv : v ∈ horizontalTangentSubmodule Q D z) :
    horizontalProjection Q D z v = v := by
  have h := (mem_horizontalTangentSubmodule_iff Q D z v).mp hv
  apply (connectionTangentEquiv Q D z).injective
  change connectionTangentEquiv Q D z
      ((connectionTangentEquiv Q D z).symm
        ((connectionTangentEquiv Q D z v).1, 0)) =
      connectionTangentEquiv Q D z v
  rw [(connectionTangentEquiv Q D z).apply_symm_apply]
  exact Prod.ext rfl h.symm

theorem horizontalProjection_idempotent (z : SphereBundleTotal Q)
    (v : TangentSpace (I (E := E)) z) :
    horizontalProjection Q D z (horizontalProjection Q D z v) =
      horizontalProjection Q D z v :=
  horizontalProjection_fix Q D z _ (horizontalProjection_mem Q D z v)

theorem horizontalProjection_range (z : SphereBundleTotal Q) :
    LinearMap.range (horizontalProjectionLinear Q D z) =
      horizontalTangentSubmodule Q D z := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact horizontalProjection_mem Q D z w
  · intro hv
    exact ⟨v, horizontalProjection_fix Q D z v hv⟩

theorem horizontalProjection_ker (z : SphereBundleTotal Q) :
    LinearMap.ker (horizontalProjectionLinear Q D z) =
      verticalTangentSubmodule Q z := by
  ext v
  rw [LinearMap.mem_ker, mem_verticalTangentSubmodule_iff_connection Q D z v]
  constructor
  · intro hv
    have h := congrArg (connectionTangentEquiv Q D z) hv
    simpa [horizontalProjection] using congrArg Prod.fst h
  · intro hv
    apply (connectionTangentEquiv Q D z).injective
    change connectionTangentEquiv Q D z
        ((connectionTangentEquiv Q D z).symm
          ((connectionTangentEquiv Q D z v).1, 0)) =
      connectionTangentEquiv Q D z 0
    rw [(connectionTangentEquiv Q D z).apply_symm_apply, map_zero]
    exact Prod.ext hv rfl

theorem horizontalProjection_complex_commute (z : SphereBundleTotal Q)
    (v : TangentSpace (I (E := E)) z) :
    horizontalProjection Q D z (tangentComplex Q D z v) =
      tangentComplex Q D z (horizontalProjection Q D z v) := by
  apply (connectionTangentEquiv Q D z).injective
  change connectionTangentEquiv Q D z
      (horizontalProjection Q D z (tangentComplex Q D z v)) =
    connectionTangentEquiv Q D z
      (tangentComplex Q D z (horizontalProjection Q D z v))
  simp only [horizontalProjection, LinearEquiv.apply_symm_apply]
  rw [tangentComplex_connectionTangentEquiv Q D z v,
    tangentComplex_connectionTangentEquiv Q D z]
  simp [ManifoldTwistorLocalAlmostComplex.chartSplitComplex]

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
