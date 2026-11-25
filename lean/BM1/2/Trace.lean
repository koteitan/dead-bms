import Common.Rules

/-!
# BM1, example 2: the trace of the source

Bubby3, "BM1 is weaker than expected." (2018-03):

> (0,0)(1,1)(2,2)(3,0)(2,1)(3,1)(4,1) decomposes into
> (0,0)(1,1)(2,2)(3,0)(2,1)(3,1)(4,0)(3,1)(4,1)(5,0)(4,1)(5,1)(6,0)(5,1)(6,1)...,
> which eventually becomes (0,0)(1,1)(2,2)(3,0)(2,1)(3,1)(4,0)(3,1)(4,1)(5,0)(4,1)

The first line is the expansion with bracket 3; the second is a prefix of it.
-/

namespace DeadBms.BM1.Ex2.Trace

example : expand BM1 bm[(0,0)(1,1)(2,2)(3,0)(2,1)(3,1)(4,1)] 3 =
    bm[(0,0)(1,1)(2,2)(3,0)(2,1)(3,1)(4,0)(3,1)(4,1)(5,0)(4,1)(5,1)(6,0)(5,1)(6,1)] := by decide

example : bm[(0,0)(1,1)(2,2)(3,0)(2,1)(3,1)(4,0)(3,1)(4,1)(5,0)(4,1)].isPrefixOf
    (expand BM1 bm[(0,0)(1,1)(2,2)(3,0)(2,1)(3,1)(4,1)] 3) := by decide

end DeadBms.BM1.Ex2.Trace
