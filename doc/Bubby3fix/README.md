[← Back](../README.md) | [English](README-en.md) | [Japanese](README.md)

# Bubby3's fix の停止しない例

| bad root 探索 | bad part 上昇 | 上昇改変 | $`f(n)`$ |
|---|---|---|---|
| 上行枝無視方式 | 全枝有効方式 | 改変なし | $`n^2`$ |

分類ページには「停止しない」「BM1.1と同じ」とあります。Bubby3's fix の規則は BM1.1 とまったく同じです。そこで [BM1.1 の例](../BM1.1/README.md) を使います。

## 主張

$`M =`$ `(0,0,0)(1,1,1)(2,0,0)(1,1,1)` とします。

**定理**（[Main.lean](../../lean/Bubby3fix/Main.lean) の `DeadBms.Bubby3fix.Ex.main`）

1. $`M`$ は Bubby3's fix の標準形である。
2. 任意の $`n \ge 1`$ について、$`M[n]`$ から始まる計算は停止しない。0 の行を足した $`\mathrm{pad}_4(M)`$ についても同じ。
3. $`M`$ から始まる無限下降列がある。

## 証明

Lean の定義で `Bubby3fix` と `BM1_1` は同じ構造体なので（`Bubby3fix_eq : Bubby3fix = BM1_1`、`rfl`）、BM1.1 の主定理そのものです。
