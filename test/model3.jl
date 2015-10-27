using Z3
A = Var(Integer)
s = Z3.Solver()

# B = Var(Integer)
# add!((A * NumeralAst(Integer, 3)) == 12)
aone = Z3.NumeralAst(Integer, 3)
atwo = Z3.NumeralAst(Integer, 3)
Z3.solver_assert(s, (A * 3) == 12)
Z3.solver_check(s)
@show model(Int, A; solver = s)
