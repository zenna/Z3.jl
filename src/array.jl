## Arrays
## ======

"Make an array variable, e.g. `x = Var(Array{Integer})"
function Var{T}(::Type{Array{T}};
                name::ASCIIString = genvar(),
                ctx::Context = global_ctx())
  s::Z3Symbol = mk_string_symbol(ctx, name)
  RangeSort = mk_sort(T)
  ty = ArraySort(IntSort(;ctx=ctx), mk_sort(T)(;ctx=ctx);ctx=ctx)
  ArrayAst{IntSort, RangeSort}(mk_const(ctx, s, ty))
end

# "Get the value/variable from the array `a` and position"
# function getindex{D,R}(a::ArrayAst{D, R}, index::Integer; ctx::Context = global_ctx())
#   iast = NumericalAst(Integer, index)
#   mk_select(a, index; ctx=ctx)
# end
#
# IntSort => RealVarAst{integer}
# function setindex(a::ArrayAst, index::Integer) ...end
#
# _ast Z3_API 	Z3_mk_select (Z3_context c, Z3_ast a, Z3_ast i)
#  	Array read. The argument a is the array and i is the index of the array that gets read. More...
#
# Z3_ast Z3_API 	Z3_mk_store (Z3_context c, Z3_ast a, Z3_ast i, Z3_ast v)
#  	Array update. More...
#
# Z3_ast Z3_API 	Z3_mk_const_array (Z3_context c, Z3_sort domain, Z3_ast v)
#  	Create the constant array. More...
#
# Z3_ast Z3_API 	Z3_mk_map (Z3_context c, Z3_func_decl f, unsigned n, Z3_ast const *args)
#  	map f on the the argument arrays. More...
#
# Z3_ast Z3_API 	Z3_mk_array_default (Z3_context c, Z3_ast array)
