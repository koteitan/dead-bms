import Common.Rules

/-!
# BM1, example 1: the trace of the source

hyp cos, Talk:Bashicu matrix system, "Something wrong happens" (2016-04-28):

> (0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,1,0)[n] reduces to
> (0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,0,0)(2,1,0)(3,1,0)...[n], where
> (0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,0,0)(2,1,0)(3,1,0)[n1] reduces to
> (0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,0,0)(2,1,0)(3,0,0)(2,1,0)(3,1,0)...[n1], …

Each line below checks that the right-hand side is a prefix of the expansion
with brackets 2 and 3.
-/

namespace DeadBms.BM1.Ex1.Trace

example : bm[(0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,0,0)(2,1,0)(3,1,0)].isPrefixOf
    (expand BM1 bm[(0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,1,0)] 2) := by decide

example : bm[(0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,0,0)(2,1,0)(3,1,0)].isPrefixOf
    (expand BM1 bm[(0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,1,0)] 3) := by decide

example : bm[(0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,0,0)(2,1,0)(3,0,0)(2,1,0)(3,1,0)].isPrefixOf
    (expand BM1 bm[(0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,0,0)(2,1,0)(3,1,0)] 2) := by decide

example :
    bm[(0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,0,0)(2,1,0)(3,0,0)(2,1,0)(3,0,0)(2,1,0)(3,1,0)].isPrefixOf
    (expand BM1 bm[(0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,0,0)(2,1,0)(3,0,0)(2,1,0)(3,1,0)] 2) := by
  decide

end DeadBms.BM1.Ex1.Trace
