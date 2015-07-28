module Z3

using Compat
import Base:convert
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
include("expression.jl")

# include("helpers.jl")

export Var

create_global_ctx()

end
