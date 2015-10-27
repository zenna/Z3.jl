using Clang
using Compat

context = wrap_c.init()
# srcdir = joinpath("..", "extern", "z3", "src", "api")
srcdir = joinpath("..", "extern")
headers = [joinpath(srcdir,"z3apiwithmarcos.h.h"), joinpath(srcdir,"z3_api.h")]
wrap_c.wrap_c_headers(context, headers)
