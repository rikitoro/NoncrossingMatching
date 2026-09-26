import NoncrossingMatching.Geometry
/-! -/

open Set

@[simp, grind]
noncomputable def totalLength {n : ℕ}
  (R B : Fin n → Point) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i, dist (R i) (B (σ i))

@[simp, grind .]
theorem totalLength_swap_lt {n : ℕ} (R B : Fin n → Point) (σ : Equiv.Perm (Fin n))
  (i j : Fin n) (hij : i ≠ j)
  (hcross : SegmentsCross (R i) (B (σ i)) (R j) (B (σ j)))
  (hncoll : ¬ Collinear ℝ {R i, B (σ i), B (σ j)}) :
  totalLength R B ((Equiv.swap i j).trans σ) < totalLength R B σ := by
  -- uncrossing inequality
  have hpair :
    dist (R i) (B (σ j)) + dist (R j) (B (σ i)) <
    dist (R i) (B (σ i)) + dist (R j) (B (σ j)) := by
    grind only [uncrossing_shorter_of_cross]
  -- swap the two indices i j
  let τ := (Equiv.swap i j).trans σ
  have hτi : τ i = σ j := by simp [τ]
  have hτj : τ j = σ i := by simp [τ]
  -- all indices exept i and j
  let rest := (Finset.univ.erase i).erase j
  have hrest :
    ∑ k ∈ rest, dist (R k) (B (τ k)) = ∑ k ∈ rest, dist (R k) (B (σ k)) := by
    apply Finset.sum_congr rfl
    grind
  --
  have hdecomp (ρ : Equiv.Perm (Fin n)) :
    dist (R i) (B (ρ i)) + dist (R j) (B (ρ j)) +
    ∑ k ∈ rest, dist (R k) (B (ρ k)) =
    totalLength R B ρ := by
    grind [Finset.add_sum_erase]
  --
  have hτdecomp := hdecomp τ
  have hσdecomp := hdecomp σ
  rw [hτi, hτj] at hτdecomp
  change totalLength R B τ < totalLength R B σ
  grind
