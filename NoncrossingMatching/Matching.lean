import NoncrossingMatching.Geometry
/-! -/

open Set
open Geometry

namespace Matching


noncomputable def totalLength {n : ℕ}
  (R B : Fin n → Point) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i, dist (R i) (B (σ i))

theorem totalLength_swap_lt {n : ℕ} (R B : Fin n → Point) (σ : Equiv.Perm (Fin n))
  (i j : Fin n) (hij : i ≠ j)
  (hcross : SegmentsCross (R i) (B (σ i)) (R j) (B (σ j)))
  (hncoll : ¬ Collinear ℝ {R i, B (σ i), B (σ j)}) :
  totalLength R B ((Equiv.swap i j).trans σ) < totalLength R B σ := by
  sorry


end Matching
