"""Create a new (incremental) solver. This solver also uses a set of builtin tactics
for handling the first check-sat command, and check-sat commands that take more than
a given number of milliseconds to be solved."""
Solver(;ctx=global_ctx()) = Solver(mk_solver(ctx))

"""Create a new solver customized for the given logic.
It behaves like Z3_mk_solver if the logic is unknown or unsupported."""
Solver(l::Logic;ctx=global_ctx()) = Solver(mk_solver(ctx, string(l)))

create_global_solver(ctx = global_ctx()) =
  (global default_global_solver; default_global_solver = Solver(ctx=ctx))

function global_solver()
  # error("global solver disabled")
  (global default_global_solver; default_global_solver)
end

function set_global_solver(slv::Solver)
  global default_global_solver
  default_global_solver = slv
end

function reset_global_solver()
  error("Unimplemented")
end

## Convenience functions
function add!(x::BoolAst, ctx::Context=global_ctx(),
                          slv::Solver=global_solver())
  solver_assert(ctx, slv, x)
end

function check(ctx::Context=global_ctx(),
               slv::Solver=global_solver())
  solver_check(ctx, slv)
end
