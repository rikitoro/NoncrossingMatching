import Mathlib

/-!
# 非交差赤青マッチングの基本定義
ユークリッド平面上の赤点・青点を結ぶ完全マッチング
- [Putnam 1979 A4](https://prase.cz/kalva/putnam/psoln/psol794.html)
- [必ず交わらないように引く方法がある](https://www.youtube.com/watch?v=x4rE57uV4IU)
-/

set_option linter.dupNamespace false

open Set

namespace NoncrossingMatching

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

end NoncrossingMatching
