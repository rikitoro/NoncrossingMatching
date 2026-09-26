import Mathlib

/-!
# Noncrossing Bichromatic Matching — Lean Web / Gist 版

一般位置にある赤点・青点の非交差完全マッチングの存在を、
「総延長が最小のマッチングを選び、交差があれば交換により短くする」
という方針で証明する。平面は `EuclideanSpace ℝ (Fin 2)` とし、
座標成分を使わず、距離・betweenness・共線性・三角不等式を用いる。

## 元レポジトリ

* https://github.com/rikitoro/NoncrossingMatching

元リポジトリの指定:
* Lean: `leanprover/lean4:v4.34.1`
* mathlib: `v4.34.1`
* mathlib commit: `d13f23b723b8a846827a245b89c10fc7d3f11612`

## 参考

- [Putnam 1979 A4]
  (https://prase.cz/kalva/putnam/psoln/psol794.html)
- [必ず交わらないように引く方法がある(YouTube)]
  (https://www.youtube.com/watch?v=x4rE57uV4IU)
- Victor Pambuccian, "A Methodologically Pure Proof of a Convex Geometry Problem",
  Beiträge zur Algebra und Geometrie / Contributions to Algebra and Geometry,
  Vol. 42, No. 2, pp. 401-406 (2001)
-/

set_option linter.dupNamespace false
set_option linter.style.header false

open Set

namespace NoncrossingMatching

/-!
## 1. 基本定義

元ファイル: `NoncrossingMatching/Basic.lean`
-/

/-- ユークリッド平面上の点 -/
abbrev Point := EuclideanSpace ℝ (Fin 2)


/-- 線分 AB, CD に共通の真の内部点が存在する -/
@[simp, grind]
def SegmentsCross (A B C D : Point) : Prop :=
  ∃ X : Point, Sbtw ℝ A X B ∧ Sbtw ℝ C X D

/-- 相異なる任意の3点が同一直線上にない -/
@[simp, grind]
def GeneralPosition {n : ℕ} (R B : Fin n → Point) : Prop :=
  ∀ ⦃p q r : Point⦄,
    p ∈ range R ∪ range B → q ∈ range R ∪ range B → r ∈ range R ∪ range B →
    p ≠ q → p ≠ r → q ≠ r →
    ¬ Collinear ℝ {p, q, r}


/-- 置換 σ が定める異なる2本の線分が交差(`SegmentsCross`)しないこと -/
@[simp, grind]
def NoncrossingMatching {n : ℕ} (R B : Fin n → Point) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ ⦃i j : Fin n⦄, i ≠ j → ¬ SegmentsCross (R i) (B (σ i)) (R j) (B (σ j))

/-!
## 2. 交差する2本の組み替えによる短縮

元ファイル: `NoncrossingMatching/Uncrossing.lean`
-/

/--
線分 AB, CD が交差するとき、線分 AD, CB に組み替えると線分の長さの和が小さくなることを示す。
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
  -- ΔAXD, ΔCXB での三角不等式
  have hADstrict : dist A D < dist A X + dist X D := by
    apply dist_lt_dist_add_dist_iff.mpr hAXD -- strict な評価 (X が AD 上に存在しないことを用いる)
  have hCB : dist C B ≤ dist C X + dist X B := by
    apply dist_triangle
  --
  grind

/-!
## 3. 総延長・交換による短縮・最小マッチング

元ファイル: `NoncrossingMatching/Length.lean`
-/

/-- 各赤点 `R i` とその相手 `B (σ i)` の距離の総和 -/
@[simp, grind]
noncomputable def totalLength {n : ℕ}
  (R B : Fin n → Point) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i, dist (R i) (B (σ i))

/-- 交差がある場合に2つの相手を交換すると総延長が減少する -/
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
  -- all indices except i and j
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

/-- 総延長が最小となる置換が存在する -/
@[simp]
theorem exists_minimal_matching {n : ℕ} (R B : Fin n → Point) :
  ∃ σmin, ∀ σ, totalLength R B σmin ≤ totalLength R B σ := by
  apply Finite.exists_min

/-!
## 4. 一般位置条件と主定理

元ファイル: `NoncrossingMatching/Main.lean`
-/

/-- 交換による短縮に必要な赤1点・青2点を取った時、それら3点が同一直線上にない -/
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

/-- 主定理：非交差完全マッチングが存在する -/
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

end NoncrossingMatching

/-!
## 5. 型と依存公理の確認
-/

#check NoncrossingMatching.uncrossing_shorter_of_cross
#check NoncrossingMatching.totalLength_swap_lt
#check NoncrossingMatching.exists_minimal_matching
#check NoncrossingMatching.exists_noncrossing_matching

#print axioms NoncrossingMatching.uncrossing_shorter_of_cross
#print axioms NoncrossingMatching.totalLength_swap_lt
#print axioms NoncrossingMatching.exists_noncrossing_matching
