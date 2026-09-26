import NoncrossingMatching.Basic

/-!
# 交差する2本の線分の組み換えによる短縮
-/

open Set

namespace NoncrossingMatching
/--
線分 AB, CD が交差するとき、線分 AC, BD に組み替えると線分の長さの和が小さくなることを示す。
三角不等式をベースとして証明する。座標計算は用いない。
-/
@[simp, grind .]
theorem uncrossing_shorter_of_cross {A B C D : Point}
  (hcross : SegmentsCross A B C D)
  (hABD : ¬ Collinear ℝ {A, B, D}) :
  dist A D + dist C B < dist A B + dist C D := by
  -- AB, CD の交点 X を取ってくる
  obtain ⟨X, hAB, hCD⟩ := hcross
  --
  have hABdist : dist A X + dist X B = dist A B := by
    apply dist_add_dist_eq_iff.mpr hAB.wbtw
  have hCDdist : dist C X + dist X D = dist C D := by
    apply dist_add_dist_eq_iff.mpr hCD.wbtw
  -- X は線分 AD 上には存在しない
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
  -- ΔAXD, ΔCXD での三角不等式
  have hADstrict : dist A D < dist A X + dist X D := by
    apply dist_lt_dist_add_dist_iff.mpr hAXD -- strict な評価 (D がAD上に存在しないことを用いる)
  have hCB : dist C B ≤ dist C X + dist X B := by
    apply dist_triangle
  --
  grind


end NoncrossingMatching
