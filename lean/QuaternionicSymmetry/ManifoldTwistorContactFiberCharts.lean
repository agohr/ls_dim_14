import QuaternionicSymmetry.ManifoldTwistorContactDistributionComplex

/-! Fiber coordinates for the smooth contact projector. The horizontal
plane is linearly identified with the actual model tangent E by the
connection splitting. Its rank is therefore the base tangent rank;
the complementary vertical fiber is the already proved complex line.
Smooth variation is witnessed globally by the checked projector map. -/

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

/-- Connection coordinates identify the genuine horizontal tangent plane
with the base manifold's real tangent model. -/
def horizontalFiberEquiv (z : SphereBundleTotal Q) :
    horizontalTangentSubmodule Q D z ≃ₗ[ℝ] E := by
  let e := connectionTangentEquiv Q D z
  let f : horizontalTangentSubmodule Q D z →ₗ[ℝ] E :=
    { toFun := fun v => (e v.1).1
      map_add' := by intro u v; exact congrArg Prod.fst (e.map_add u.1 v.1)
      map_smul' := by intro r v; exact congrArg Prod.fst (e.map_smul r v.1) }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro u v huv
    apply Subtype.ext
    apply e.injective
    apply Prod.ext
    · exact huv
    · exact ((mem_horizontalTangentSubmodule_iff Q D z u.1).mp u.2).trans
        ((mem_horizontalTangentSubmodule_iff Q D z v.1).mp v.2).symm
  · intro w
    refine ⟨⟨e.symm (w,0), ?_⟩, ?_⟩
    · rw [mem_horizontalTangentSubmodule_iff]
      change (e (e.symm (w,0))).2 = 0
      rw [e.apply_symm_apply]
    · simp [f]

theorem horizontalFiber_finrank (z : SphereBundleTotal Q) :
    Module.finrank ℝ (horizontalTangentSubmodule Q D z) = Module.finrank ℝ E :=
  (horizontalFiberEquiv Q D z).finrank_eq

/-- The actual horizontal lift is the inverse of the base-direction
coordinate on each contact-plane fiber. -/
theorem horizontalFiberEquiv_symm_apply (z : SphereBundleTotal Q) (u : E) :
    ((horizontalFiberEquiv Q D z).symm u : TangentSpace (I (E := E)) z) =
      (connectionTangentEquiv Q D z).symm (u,0) := by
  apply (connectionTangentEquiv Q D z).injective
  have h := (horizontalFiberEquiv Q D z).apply_symm_apply u
  rw [(connectionTangentEquiv Q D z).apply_symm_apply]
  apply Prod.ext
  · exact h
  · exact (mem_horizontalTangentSubmodule_iff Q D z _).mp
      ((horizontalFiberEquiv Q D z).symm u).2

/-- The smooth projector onto this fixed-rank horizontal plane is the
geometric transition datum for its smooth complex distribution. -/
theorem horizontalFiber_projector_smooth :
    ContMDiff (I (E := E)).tangent (I (E := E)).tangent ∞
      (horizontalProjectionBundleMap Q D) :=
  horizontalProjectionBundleMap_smooth Q D

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
