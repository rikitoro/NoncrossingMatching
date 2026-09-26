# Noncrossing Bichromatic Matching in Lean

## 概要
一般位置にある赤点・青点について、
非交差完全マッチングの存在を Lean 4 で形式化する。

## 証明方針
総延長が最小の完全マッチングを選ぶ。
交差する2本があれば、相手を交換することで総延長が厳密に減少し、
最小性に矛盾する。

平面は EuclideanSpace ℝ (Fin 2) とし、
三角不等式をベースとした証明を行う。
証明スクリプトでは座標成分を使わない。

## 主定理
NoncrossingMatching.exists_noncrossing_matching

## ファイル構成
Basic → Uncrossing → Length → Main

## 参考文献
- [Putnam 1979 A4](https://prase.cz/kalva/putnam/psoln/psol794.html)
- [必ず交わらないように引く方法がある(YouTube)](https://www.youtube.com/watch?v=x4rE57uV4IU)
- Victor Pambuccian, "A Methodologically Pure Proof of a Convex Geometry Problem", Beiträge zur Algebra und Geometrie / Contributions to Algebra and Geometry, Vol. 42, No. 2, pp. 401-406 (2001)
