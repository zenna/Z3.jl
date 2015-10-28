module Z3

using Compat
import Base:convert
import Base:rem,ifelse

import Base:
  ==,
  >=,
  <=,
  >,
  <,
  *,
  +,
  -,
  ^,
  /,
  %,
  $,
  &,
  |

# Load shared libs
try
  @compat Libdl.dlopen(joinpath("libz3.so"), Libdl.RTLD_LAZY|Libdl.RTLD_DEEPBIND|Libdl.RTLD_GLOBAL)
catch e
  error("Could not load z3 shared libraries")
  rethrow(e)
end

include("util.jl")
include("wrap.jl")
include("sorts.jl")
include("logic.jl")
include("context.jl")
include("ast.jl")
include("array.jl")
include("numerals.jl")
include("solver.jl")
include("accessor.jl")

# include("auxiliary.jl")

export Var,
  distinct,
  is_int,
  biimplies,
  add!,
  check,
  model,
  reset_global_ctx!,
  global_ctx,
  global_solver

#Z3 Types
export  UnknownSort,
  UninterpretedSort,
  BoolSort,
  IntSort,
  RealSort,
  BitVectorSort,
  FiniteDomainSort,
  ArraySort,
  TupleSort,
  EnumerationSort,
  ListSort,
  Z3Symbol,
  Literals,
  Theory,
  Config,
  Context,
  FuncDecl,
  Ast,
  NumeralAst,
  AppAst,
  RealAppAst,
  VarAst,
  RealVarAst,
  QuantifierAst,
  SortAst,
  FuncDeclAst,
  UnknownAst,
  App,
  Pattern,
  Model,
  Constructor,
  ConstructorList,
  Params,
  ParamDescrs,
  Goal,
  Tactic,
  Probe,
  Stats,
  Solver,
  AstVector,
  AstMap,
  ApplyResult,
  FuncInterp,
  FuncEntry,
  Fixedpoint,
  RcfNum,
  TheoryData,
  ReduceEqCallbackFptr,
  ReduceAppCallbackFptr,
  ReduceDistinctCallbackFptr,
  TheoryCallbackFptr,
  TheoryFinalCheckCallbackFptr,
  TheoryAstBoolCallbackFptr,
  TheoryAstAstCallbackFptr,
  TheoryAstCallbackFptr,
  Z3Bool,
  FixedpointReduceAssignCallbackFptr,
  FixedpointReduceAppCallbackFptr

create_global_ctx()
create_global_solver()

end
