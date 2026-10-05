import QuaternionicSymmetry.ContinuousEndomorphismExteriorTrace
import QuaternionicSymmetry.QuaternionicTangentUniversalSpecialization

/-! Linear combinations of homogeneous exterior two-forms remain homogeneous
entrywise, so the formal tangent matrices represent genuine two-forms. -/
namespace QuaternionicSymmetry.HomogeneousMatrixCombinations
open QuaternionicExteriorEvenTrace EvenForms ExteriorMatrixWedgeBridge
  RealifiedTracePolynomial QuaternionicTangentUniversalSpecialization
noncomputable section
section Generic

variable {E κ β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype κ] [DecidableEq κ] [Fintype β]

omit [FiniteDimensional ℝ E] [Fintype κ] [DecidableEq κ] in
theorem combination_entries_two (B : β → Matrix κ κ ℝ)
    (η : β → EvenAlgebra E)
    (hη : ∀ a, ((η a : EvenAlgebra E) : ExteriorAlgebra ℝ (Module.Dual ℝ E)) ∈
      ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E))
    (i j : κ) :
    ((combination B η i j : EvenAlgebra E) :
      ExteriorAlgebra ℝ (Module.Dual ℝ E)) ∈
        ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E) := by
  change (↑(∑ a, algebraMap ℝ (EvenAlgebra E) (B a i j) * η a) :
      ExteriorAlgebra ℝ (Module.Dual ℝ E)) ∈ _
  have hs := map_sum (Subalgebra.val (EvenAlgebra E))
    (fun a => algebraMap ℝ (EvenAlgebra E) (B a i j) * η a) Finset.univ
  change ((∑ a, algebraMap ℝ (EvenAlgebra E) (B a i j) * η a :
    EvenAlgebra E) : ExteriorAlgebra ℝ (Module.Dual ℝ E)) = _ at hs
  rw [hs]
  change (∑ a, algebraMap ℝ (ExteriorAlgebra ℝ (Module.Dual ℝ E))
    (B a i j) * (η a : ExteriorAlgebra ℝ (Module.Dual ℝ E))) ∈
      ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E)
  apply Submodule.sum_mem
  intro a ha
  change (B a i j) • (η a : ExteriorAlgebra ℝ (Module.Dual ℝ E)) ∈ _
  exact (ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E)).smul_mem _ (hη a)

end Generic
section Formal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

omit [Nontrivial E] in
theorem formal_sp_matrix_eq_combination (S : QuaternionicStructure E)
    (η : QuaternionicTangentFormalMatrix.Index S → EvenAlgebra E) :
    QuaternionicTangentUniversalSpecialization.spMatrix S η =
      combination (QuaternionicTangentFormalMatrix.spMatrix S)
      (fun a => η (Sum.inl a)) := by
  apply Matrix.ext
  intro i j
  change MvPolynomial.aeval η
    (QuaternionicTangentFormalMatrix.spPolynomial S i j) = _
  simp [QuaternionicTangentFormalMatrix.spPolynomial,
    RealifiedTracePolynomial.combination]

theorem formal_scalar_matrix_eq_combination (S : QuaternionicStructure E)
    (η : QuaternionicTangentFormalMatrix.Index S → EvenAlgebra E) :
    QuaternionicTangentUniversalSpecialization.scalarMatrix S η =
      combination (QuaternionicTangentFormalMatrix.scalarMatrix S)
      (fun i => η (Sum.inr i)) := by
  apply Matrix.ext
  intro i j
  change MvPolynomial.aeval η
    (QuaternionicTangentFormalMatrix.scalarPolynomial S i j) = _
  simp [QuaternionicTangentFormalMatrix.scalarPolynomial,
    RealifiedTracePolynomial.combination]

omit [Nontrivial E] in
theorem formal_sp_entries_two (S : QuaternionicStructure E)
    (η : QuaternionicTangentFormalMatrix.Index S → EvenAlgebra E)
    (hη : ∀ a, ((η a : EvenAlgebra E) : ExteriorAlgebra ℝ (Module.Dual ℝ E)) ∈
      ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E))
    (i j : QuaternionicTangentFormalMatrix.MatrixIndex (E := E)) :
    ((QuaternionicTangentUniversalSpecialization.spMatrix S η i j : EvenAlgebra E) :
      ExteriorAlgebra ℝ (Module.Dual ℝ E)) ∈
        ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E) := by
  rw [formal_sp_matrix_eq_combination]
  exact combination_entries_two _ _ (fun a => hη (Sum.inl a)) i j

theorem formal_scalar_entries_two (S : QuaternionicStructure E)
    (η : QuaternionicTangentFormalMatrix.Index S → EvenAlgebra E)
    (hη : ∀ a, ((η a : EvenAlgebra E) : ExteriorAlgebra ℝ (Module.Dual ℝ E)) ∈
      ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E))
    (i j : QuaternionicTangentFormalMatrix.MatrixIndex (E := E)) :
    ((QuaternionicTangentUniversalSpecialization.scalarMatrix S η i j : EvenAlgebra E) :
      ExteriorAlgebra ℝ (Module.Dual ℝ E)) ∈
        ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E) := by
  rw [formal_scalar_matrix_eq_combination]
  exact combination_entries_two _ _ (fun a => hη (Sum.inr a)) i j

end Formal
end
end QuaternionicSymmetry.HomogeneousMatrixCombinations
