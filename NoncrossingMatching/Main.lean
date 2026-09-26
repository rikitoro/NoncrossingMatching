import NoncrossingMatching.Length

set_option linter.style.header false

/-!
# 非交差赤青完全マッチングの存在
-/
open Set

namespace NoncrossingMatching

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

/-- 主定理：非交差完全マッチングの存在が存在する -/
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
