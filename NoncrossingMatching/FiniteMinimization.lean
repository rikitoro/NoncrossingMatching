import NoncrossingMatching.Matching

/-! -/

theorem exists_minimal_matching {n : ℕ} (R B : Fin n → Point) :
  ∃ σmin, ∀ σ, totalLength R B σmin ≤ totalLength R B σ := by
  apply Finite.exists_min
