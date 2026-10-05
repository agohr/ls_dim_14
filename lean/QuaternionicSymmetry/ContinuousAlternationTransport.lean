import QuaternionicSymmetry.ContinuousAlternation
import Mathlib.GroupTheory.Perm.Sign

/-! Full alternation is natural under a reindexing equivalence of slots. -/

namespace QuaternionicSymmetry.ContinuousAlternationTransport

open QuaternionicSymmetry.ContinuousAlternation

noncomputable section

variable {ι κ E C : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup C] [NormedSpace ℝ C]

theorem alternationCLM_domDomCongr_apply
    (f : ContinuousMultilinearMap ℝ (fun _ : ι => E) C)
    (e : ι ≃ κ) (v : κ → E) :
    alternationCLM (f.domDomCongr e) v = alternationCLM f (v ∘ e) := by
  simp only [alternationCLM_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  calc
    (∑ σ : Equiv.Perm κ, Equiv.Perm.sign σ • f ((v ∘ σ) ∘ e)) =
        ∑ τ : Equiv.Perm ι,
          Equiv.Perm.sign (e.permCongr τ) •
            f ((v ∘ e.permCongr τ) ∘ e) := by
      exact (Equiv.sum_comp e.permCongr _).symm
    _ = ∑ τ : Equiv.Perm ι,
          Equiv.Perm.sign τ • f ((v ∘ e) ∘ τ) := by
      apply Finset.sum_congr rfl
      intro τ _
      have hs : Equiv.Perm.sign (e.permCongr τ) = Equiv.Perm.sign τ :=
        (Equiv.Perm.sign_eq_sign_of_equiv τ (e.permCongr τ) e
          (by intro i; simp [Equiv.permCongr_apply])).symm
      rw [hs]
      have hv : ((v ∘ e.permCongr τ) ∘ e) = ((v ∘ e) ∘ τ) := by
        funext i
        simp [Function.comp_def, Equiv.permCongr_apply]
      rw [hv]

end
end QuaternionicSymmetry.ContinuousAlternationTransport
