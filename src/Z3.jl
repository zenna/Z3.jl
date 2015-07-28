module Z3

using Compat

# Load shared libs
try
  @compat Libdl.dlopen(joinpath("libz3.so"), Libdl.RTLD_LAZY|Libdl.RTLD_DEEPBIND|Libdl.RTLD_GLOBAL)
catch e
  error("Could not load z3 shared libraries")
  rethrow(e)
end

include("wrap.jl")
# include("helpers.jl")

end
