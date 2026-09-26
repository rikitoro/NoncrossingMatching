import Mathlib

/-!
# Noncrossing bichromatic matching
-/

open Set


/-- Points in the Euclidean plane. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)


namespace Geometry

@[simp, grind]
def SegmentsCross (A B C D : Point) : Prop :=
  ∃ X : Point, Sbtw ℝ A X B ∧ Sbtw ℝ C X D


@[simp, grind .]
theorem uncrossing_shorter_of_cross {A B C D : Point}
  (hcross : SegmentsCross A B C D)
  (hABD : ¬ Collinear ℝ {A, B, D}) :
  dist A D + dist C B < dist A B + dist C D := by
  obtain ⟨X, hAB, hCD⟩ := hcross
  have hABdist : dist A X + dist X B = dist A B := by
    apply dist_add_dist_eq_iff.mpr hAB.wbtw
  have hCDdist : dist C X + dist X D = dist C D := by
    apply dist_add_dist_eq_iff.mpr hCD.wbtw
  -- X cannot be between A and D
  have hAXD : ¬ Wbtw ℝ A X D := by
    intro h
    apply hABD
    have hA_line : A ∈ line[ℝ, A, X] := by
      apply left_mem_affineSpan_pair
    have hB_line : B ∈ line[ℝ, A, X] := by
      apply hAB.right_mem_affineSpan
    have hD_line : D ∈ line[ℝ, A, X] := by
      apply h.right_mem_affineSpan_of_left_ne
      apply hAB.left_ne
    apply collinear_triple_of_mem_affineSpan_pair hA_line hB_line hD_line
  have hADstrict : dist A D < dist A X + dist X D := by
    apply dist_lt_dist_add_dist_iff.mpr hAXD
  have hCB : dist C B ≤ dist C X + dist X B := by
    apply dist_triangle
  linarith

end Geometry
