import QuaternionicSymmetry.ComplexProjectiveActualConeGlobalClassicalComparison

/-! An equivariant analytic projective embedding is intertwined on every
classical point by the already constructed genuine global regular scheme
action. The scheme product point is supplied by actual evaluation, not
postulated as an abstract comparison map. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeEquivariantClassicalComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeClassicalPointInjective
open ComplexProjectiveActualConeSpecEvaluationNaturality
open ComplexProjectiveActualConeGlobalSchemeAction
open ComplexProjectiveActualConeGlobalClassicalComparison
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ} {X : Type*}

theorem exists_schemePoint_for_equivariant_image
    (f : X → Space d) (μ : Fin (d + 1) → Fin r → ℤ)
    (ρ : ComplexTorus r →* Equiv.Perm X)
    (hρ : ∀ (z : ComplexTorus r) (x : X),
      f (ρ z x) = projectiveAction μ z (f x))
    (hA : HasHomogeneousEquations (Set.range f))
    (z : ComplexTorus r) (x : X) :
    let A := Set.range f
    let hNonempty : A.Nonempty := ⟨f x, ⟨x, rfl⟩⟩
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    ∃ p : ↥(pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
        (ComplexProjectiveActualConeComplexStructure.actualConeProjToSpecComplex
          A hA hNonempty) : Scheme),
      (pullback.fst _ _ : _ ⟶ Spec (CommRingCat.of (TorusCoordinateRing r))) p =
          specEvaluationPoint (evalTorus z) ∧
      (pullback.snd _ _ : _ ⟶ Proj (quotientPiece A)) p =
          classicalPointToActualProjFixed A hA hNonempty
            ⟨f x, ⟨x, rfl⟩⟩ ∧
      (globalSchemeAction μ A hA hNonempty
        (fun t y hy => by
          obtain ⟨x', rfl⟩ := hy
          exact ⟨ρ (compactInclusion r t) x', hρ _ _⟩)) p =
          classicalPointToActualProjFixed A hA hNonempty
            ⟨f (ρ z x), ⟨ρ z x, rfl⟩⟩ := by
  let A := Set.range f
  let hNonempty : A.Nonempty := ⟨f x, ⟨x, rfl⟩⟩
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA hNonempty
  let hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A := by
    intro t y hy
    obtain ⟨x', rfl⟩ := hy
    exact ⟨ρ (compactInclusion r t) x', hρ _ _⟩
  obtain ⟨p,hfst,hsnd,hact⟩ :=
    exists_globalClassicalProductPoint_action μ A hA hNonempty hCompact z
      ⟨f x, ⟨x, rfl⟩⟩
  refine ⟨p,hfst,hsnd,?_⟩
  simpa only [← hρ] using hact

end
end QuaternionicSymmetry.ComplexProjectiveActualConeEquivariantClassicalComparison
