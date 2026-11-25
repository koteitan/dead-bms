[← Back](../README.md) | [English](README-en.md) | [Japanese](README.md)

# BM1

| bad root 探索 | bad part 上昇 | 上昇改変 | $`f(n)`$ |
|---|---|---|---|
| 左隣法 | 全枝有効方式 | 改変なし | $`n^2`$ |

- 左隣法: 最右列 $`C`$ の非零最下行を $`t`$ とします。bad root は、$`C`$ より左にあり $`y \le t`$ のすべての行で $`m_y \lt  c_y`$ を満たす列のうち、最も右のものです。
- 全枝有効方式: bad part のすべての要素が上昇します。
- 定義は [BM1 (BASIC 言語)](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:BashicuHyudora/BASIC%E8%A8%80%E8%AA%9E%E3%81%AB%E3%82%88%E3%82%8B%E5%B7%A8%E5%A4%A7%E6%95%B0%E3%81%AE%E3%81%BE%E3%81%A8%E3%82%81?oldid=9843) です。

## 停止しない例

| 番号 | 行列 | 出典 | 解説 | Lean |
|---|---|---|---|---|
| 1 | `(0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,1,0)` | hyp cos | [1/README.md](1/README.md) | [lean/BM1/1](../../lean/BM1/1) |
| 2 | `(0,0)(1,1)(2,2)(3,0)(2,1)(3,1)(4,1)` | Bubby3 | [2/README.md](2/README.md) | [lean/BM1/2](../../lean/BM1/2) |

どちらの例も、出典には標準形であることの証明がありません。Lean では ι からの経路を具体的に与えて示しています。
