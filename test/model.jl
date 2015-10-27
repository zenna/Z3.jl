using Z3
x = Var(Real)
s = Solver()

aone = NumeralAst(Real, "3.0")
atwo = NumeralAst(Real, "10.0")
solver_assert(s, x > aone)
solver_assert(s, x < atwo)
@show solver_check(s)
m = solver_get_model(s)
model_string = model_to_string(m)
