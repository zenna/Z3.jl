using Z3
using Base.Test
x = Z3.Var(Integer)
s = Z3.Solver()

aone = Z3.NumeralAst(Integer, 3)
atwo = Z3.NumeralAst(Integer, 10)
Z3.solver_assert(s, x > aone)
Z3.solver_assert(s, x < atwo)
@show Z3.solver_check(s)

interpretation = Z3.model(Int64, x; solver = s)
@test interpretation > 3 && interpretation < 10
