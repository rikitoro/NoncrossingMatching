import NoncrossingMatching.Basic

open Set

/- all three distinct points are noncollinear -/
@[simp, grind]
def GeneralPosition {n : ℕ} (R B : Fin n → Point) : Prop :=
  ∀ ⦃p q r : Point⦄,
    p ∈ range R ∪ range B → q ∈ range R ∪ range B → r ∈ range R ∪ range B →
    p ≠ q → p ≠ r → q ≠ r →
    ¬ Collinear ℝ {p, q, r}

@[simp, grind .]
theorem GeneralPosition.noncol_RBB {n : ℕ} {R B : Fin n → Point}
  (hgp : GeneralPosition R B)
  (hB : Function.Injective B) (hRB : ∀ i j, R i ≠ B j) (σ : Equiv.Perm (Fin n))
  {i j : Fin n} (hij : i ≠ j) :
  ¬ Collinear ℝ {R i, B (σ i), B (σ j)} := by
  apply hgp
  · grind
  · grind
  · grind
  · grind
  · grind
  · intro h
    apply hij
    apply σ.injective
    grind

@[simp, grind]
def NoncrossingMatching {n : ℕ} (R B : Fin n → Point) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ ⦃i j : Fin n⦄, i ≠ j → ¬ SegmentsCross (R i) (B (σ i)) (R j) (B (σ j))

theorem exists_noncrossing_matching {n : ℕ}
  (R B : Fin n → Point)
  (_ : Function.Injective R) (hB : Function.Injective B)
  (hRB : ∀ i j, R i ≠ B j) (hgp : GeneralPosition R B) :
  ∃ σ : Equiv.Perm (Fin n), NoncrossingMatching R B σ := by
  obtain ⟨σmin, hmin⟩ := exists_minimal_matching R B
  use σmin
  intro i j hij hcross
  --
  have hnoncol : ¬ Collinear ℝ {R i, B (σmin i), B (σmin j)} := by
    grind
  -- uncrossing shorter
  have hshort : totalLength R B ((Equiv.swap i j).trans σmin) < totalLength R B σmin := by
    grind
  --
  grind
