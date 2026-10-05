import QuaternionicSymmetry.LocalChernWeilCubicTransgression
import QuaternionicSymmetry.ContinuousWedgeInstances

/-!
# Cyclic rotation of ordered curvature triples

The raw six-linear coefficient expression rotates three two-form slots by an
even block permutation.  This is the algebraic input for combining the three
ordered cubic first-variation terms after normalized wedge associativity.
-/

namespace QuaternionicSymmetry.LocalChernWeilCubicCyclicity

open QuaternionicSymmetry.LocalChernWeilQuadratic
  QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalChernWeilCubicTransgression
  QuaternionicSymmetry.ContinuousMultilinearProduct
  QuaternionicSymmetry.ContinuousAlternation
  QuaternionicSymmetry.LocalTraceSquareAlgebra
  QuaternionicSymmetry.ContinuousWedge

noncomputable section

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

/-- Taking the trace after a normalized wedge is the same as using the
trace-multiplication pairing in that wedge. -/
theorem trace_wedge_eq_map {p q : ℕ}
    (T : R →L[ℝ] B)
    (α : E [⋀^Fin p]→L[ℝ] R) (β : E [⋀^Fin q]→L[ℝ] R) :
    wedge (traceProduct T) α β =
      T.compContinuousAlternatingMap
        (wedge (ContinuousLinearMap.mul ℝ R) α β) := by
  ext v
  change wedge (traceProduct T) α β v =
    T (wedge (ContinuousLinearMap.mul ℝ R) α β v)
  simp only [wedge_apply, map_smul, map_sum, traceProduct_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simp [hs]
  · simp [hs]

/-- The algebra-valued primitive before applying a cyclic trace. -/
def connectionCurvatureSquareForm
    (Γ θ : Form (E := E) (A := R)) :
    E → E [⋀^Fin 5]→L[ℝ] R := fun x =>
  wedge (ContinuousLinearMap.mul ℝ R)
    (connectionForm θ x)
    (wedge (ContinuousLinearMap.mul ℝ R)
      (curvatureForm Γ x) (curvatureForm Γ x))

theorem traceConnectionCurvatureSquare_eq_map
    (T : R →L[ℝ] B) (Γ θ : Form (E := E) (A := R)) :
    traceConnectionCurvatureSquare T Γ θ =
      fun x => T.compContinuousAlternatingMap
        (connectionCurvatureSquareForm Γ θ x) := by
  funext x
  rw [traceConnectionCurvatureSquare, connectionCurvatureSquareForm]
  rw [QuaternionicSymmetry.ContinuousWedgeInstances.wedge22_eq]
  exact trace_wedge_eq_map T _ _

/-- The coefficient trace is invariant under cyclic rotation of a triple. -/
theorem trace_three_cyclic (T : R →L[ℝ] B)
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (a b c : R) :
    T (a * (b * c)) = T (b * (c * a)) := by
  rw [hT a (b * c), mul_assoc]

/-- Rotation of three adjacent pairs of six vector arguments. -/
def blockCycle : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem blockCycle_sign : Equiv.Perm.sign blockCycle = 1 := by decide

/-- The unalternated ordered triple of two-forms. -/
def rawTriple (T : R →L[ℝ] B)
    (α β γ : E [⋀^Fin 2]→L[ℝ] R) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 6 => E) B :=
  (concatenate (traceProduct T) α.toContinuousMultilinearMap
    ((concatenate (ContinuousLinearMap.mul ℝ R)
      β.toContinuousMultilinearMap
      γ.toContinuousMultilinearMap).domDomCongr
        (finSumFinEquiv (m := 2) (n := 2)))).domDomCongr
          (finSumFinEquiv (m := 2) (n := 4))

theorem rawTriple_apply (T : R →L[ℝ] B)
    (α β γ : E [⋀^Fin 2]→L[ℝ] R) (v : Fin 6 → E) :
    rawTriple T α β γ v =
      T (α ![v 0, v 1] *
        (β ![v 2, v 3] * γ ![v 4, v 5])) := by
  simp [rawTriple, concatenate_apply,
    ContinuousMultilinearMap.domDomCongr_apply,
    finSumFinEquiv, traceProduct_apply]
  have hα : ((fun i : Fin 2 ⊕ Fin 4 =>
      v (Sum.elim (Fin.castAdd 4 : Fin 2 → Fin 6)
        (Fin.natAdd 2 : Fin 4 → Fin 6) i)) ∘ Sum.inl) =
      ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  have hβ : ((fun i : Fin 2 ⊕ Fin 2 =>
      v (Fin.natAdd 2 (Sum.elim
        (Fin.castAdd 2 : Fin 2 → Fin 4)
        (Fin.natAdd 2 : Fin 2 → Fin 4) i))) ∘ Sum.inl) =
      ![v 2, v 3] := by
    funext i
    fin_cases i <;> rfl
  have hγ : ((fun i : Fin 2 ⊕ Fin 2 =>
      v (Fin.natAdd 2 (Sum.elim
        (Fin.castAdd 2 : Fin 2 → Fin 4)
        (Fin.natAdd 2 : Fin 2 → Fin 4) i))) ∘ Sum.inr) =
      ![v 4, v 5] := by
    funext i
    fin_cases i <;> rfl
  rw [hα, hβ, hγ]

/-- Rotating the three two-form blocks changes the raw map only by
precomposition with the even six-slot block cycle. -/
theorem rawTriple_cycle (T : R →L[ℝ] B)
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (α β γ : E [⋀^Fin 2]→L[ℝ] R) :
    rawTriple T β γ α =
      (rawTriple T α β γ).domDomCongr blockCycle := by
  ext v
  rw [rawTriple_apply, ContinuousMultilinearMap.domDomCongr_apply,
    rawTriple_apply]
  change T (β ![v 0, v 1] * (γ ![v 2, v 3] * α ![v 4, v 5])) =
    T (α ![v 4, v 5] * (β ![v 0, v 1] * γ ![v 2, v 3]))
  exact (trace_three_cyclic T hT
    (α ![v 4, v 5]) (β ![v 0, v 1]) (γ ![v 2, v 3])).symm

/-- Cyclicity survives full alternation because a two-form block rotation
has positive sign. -/
theorem alternation_rawTriple_cycle (T : R →L[ℝ] B)
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (α β γ : E [⋀^Fin 2]→L[ℝ] R) :
    alternationCLM (rawTriple T β γ α) =
      alternationCLM (rawTriple T α β γ) := by
  rw [rawTriple_cycle T hT α β γ,
    alternation_domDomCongr, blockCycle_sign, one_smul]

end
end QuaternionicSymmetry.LocalChernWeilCubicCyclicity
