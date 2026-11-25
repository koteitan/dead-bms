import Common.Expand

/-!
# Rule sets

The rule sets of the classification page that are marked as non-terminating.

| rule set     | bad root       | ascension  | f(n)  |
|--------------|----------------|------------|-------|
| BM1          | 左隣法          | 全枝有効方式 | n²    |
| rTSS         | 左隣法          | 全枝有効方式 | n²    |
| BM1.1        | 上行枝無視方式   | 全枝有効方式 | n²    |
| BM2.1        | 上行枝無視方式   | 全枝有効方式 | n + 1 |
| Bubby3's fix | 上行枝無視方式   | 全枝有効方式 | n²    |
| BM2          | 上行枝無視方式   | BM2 方式    | n²    |
| BM3          | 上行枝無視方式   | BM3 方式    | n²    |

All of them use 改変なし.  rTSS is BM1 on 3-row matrices.  The page does not
give `f` for BM3; its BASIC code uses `A=A*A`, i.e. `n²`.
-/

namespace DeadBms

def BM1 : RuleSet := { badRoot := leftAdj, ascend := ascAll, f := fun n => n * n }

/-- rTSS is BM1 on trio (3-row) matrices -/
def rTSS : RuleSet := { badRoot := leftAdj, ascend := ascAll, f := fun n => n * n }

def BM1_1 : RuleSet := { badRoot := ubim, ascend := ascAll, f := fun n => n * n }

def BM2_1 : RuleSet := { badRoot := ubim, ascend := ascAll, f := fun n => n + 1 }

def Bubby3fix : RuleSet := { badRoot := ubim, ascend := ascAll, f := fun n => n * n }

def BM2 : RuleSet := { badRoot := ubim, ascend := ascBM2, f := fun n => n * n }

def BM3 : RuleSet := { badRoot := ubim, ascend := ascBM3, f := fun n => n * n }

end DeadBms
