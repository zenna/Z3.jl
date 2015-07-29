##  AST
## ====
# abstract syntax tree node. That is, the data-structure used in Z3 to represent
# terms, formulas and types.

function Var{T<: MathNumber}(::Type{T};
                          name::ASCIIString = genvar(),
                          ctx::Context = global_context())
  # safe_add!(name, ctx)
  RealVarAst{T}(mk_var(T, ctx, name))
end

## Constructing Sorts
## =================
mk_sort(::Type{Bool}) = mk_bool_sort
mk_sort(::Type{Real}) = mk_real_sort
mk_sort(::Type{Integer}) = mk_int_sort

## Make variables
## ==============
"Create a variable using the given name and type"
function mk_var(ctx::Context, name::ASCIIString, ty::Sort)
  s::Z3Symbol = mk_string_symbol(ctx, name)
  return mk_const(ctx, s, ty)
end

"Create a variable using the given name"
function mk_var{T <: MathNumber}(::Type{T}, ctx::Context, name::ASCIIString)
  ty::Sort = mk_sort(T)(ctx)
  mk_var(ctx, name, ty)
end

## Arithmetic
# ## ==========
boolop2z3 = @compat Dict(:(>=) => mk_ge, :(>) => mk_gt,
                              :(<=) => mk_le, :(<) => mk_lt,
                              :(==) => mk_eq)

## Real × Real -> Bool
for (op,func) in boolop2z3
  @eval ($op){T1<:Real}(x::RealVarAst{Real}, y::T1; ctx::Context = global_context()) =
    AppAst{Bool}($func(ctx, x, NumeralAst(y; ctx=ctx)))
end

# promote



#
# @wrap function Z3_mk_eq(c::Z3_context,l::Z3_ast,r::Z3_ast)
#     ccall((:Z3_mk_eq,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,l,r)
# end
#
# @wrap function Z3_mk_distinct(c::Z3_context,num_args::Uint32,args::Ptr{Z3_ast})
#     ccall((:Z3_mk_distinct,"libz3"),Z3_ast,(Z3_context,Uint32,Ptr{Z3_ast}),c,num_args,args)
# end
#
# @wrap function Z3_mk_not(c::Z3_context,a::Z3_ast)
#     ccall((:Z3_mk_not,"libz3"),Z3_ast,(Z3_context,Z3_ast),c,a)
# end
#
# @wrap function Z3_mk_ite(c::Z3_context,t1::Z3_ast,t2::Z3_ast,t3::Z3_ast)
#     ccall((:Z3_mk_ite,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast,Z3_ast),c,t1,t2,t3)
# end
#
# @wrap function Z3_mk_iff(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
#     ccall((:Z3_mk_iff,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
# end
#
# @wrap function Z3_mk_implies(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
#     ccall((:Z3_mk_implies,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
# end
#
# @wrap function Z3_mk_xor(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
#     ccall((:Z3_mk_xor,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
# end
#
# @wrap function Z3_mk_and(c::Z3_context,num_args::Uint32,args::Ptr{Z3_ast})
#     ccall((:Z3_mk_and,"libz3"),Z3_ast,(Z3_context,Uint32,Ptr{Z3_ast}),c,num_args,args)
# end
#
# @wrap function Z3_mk_or(c::Z3_context,num_args::Uint32,args::Ptr{Z3_ast})
#     ccall((:Z3_mk_or,"libz3"),Z3_ast,(Z3_context,Uint32,Ptr{Z3_ast}),c,num_args,args)
# end
#
# @wrap function Z3_mk_add(c::Z3_context,num_args::Uint32,args::Ptr{Z3_ast})
#     ccall((:Z3_mk_add,"libz3"),Z3_ast,(Z3_context,Uint32,Ptr{Z3_ast}),c,num_args,args)
# end
#
# @wrap function Z3_mk_mul(c::Z3_context,num_args::Uint32,args::Ptr{Z3_ast})
#     ccall((:Z3_mk_mul,"libz3"),Z3_ast,(Z3_context,Uint32,Ptr{Z3_ast}),c,num_args,args)
# end
#
# @wrap function Z3_mk_sub(c::Z3_context,num_args::Uint32,args::Ptr{Z3_ast})
#     ccall((:Z3_mk_sub,"libz3"),Z3_ast,(Z3_context,Uint32,Ptr{Z3_ast}),c,num_args,args)
# end
#
# @wrap function Z3_mk_unary_minus(c::Z3_context,arg::Z3_ast)
#     ccall((:Z3_mk_unary_minus,"libz3"),Z3_ast,(Z3_context,Z3_ast),c,arg)
# end
#
# @wrap function Z3_mk_div(c::Z3_context,arg1::Z3_ast,arg2::Z3_ast)
#     ccall((:Z3_mk_div,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,arg1,arg2)
# end
#
# @wrap function Z3_mk_mod(c::Z3_context,arg1::Z3_ast,arg2::Z3_ast)
#     ccall((:Z3_mk_mod,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,arg1,arg2)
# end
#
# @wrap function Z3_mk_rem(c::Z3_context,arg1::Z3_ast,arg2::Z3_ast)
#     ccall((:Z3_mk_rem,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,arg1,arg2)
# end
#
# @wrap function Z3_mk_power(c::Z3_context,arg1::Z3_ast,arg2::Z3_ast)
#     ccall((:Z3_mk_power,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,arg1,arg2)
# end
#
# @wrap function Z3_mk_lt(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
#     ccall((:Z3_mk_lt,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
# end
#
# @wrap function Z3_mk_le(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
#     ccall((:Z3_mk_le,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
# end
#
# @wrap function Z3_mk_gt(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
#     ccall((:Z3_mk_gt,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
# end
#
# @wrap function Z3_mk_ge(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
#     ccall((:Z3_mk_ge,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
# end
#
# @wrap function Z3_mk_int2real(c::Z3_context,t1::Z3_ast)
#     ccall((:Z3_mk_int2real,"libz3"),Z3_ast,(Z3_context,Z3_ast),c,t1)
# end
#
# @wrap function Z3_mk_real2int(c::Z3_context,t1::Z3_ast)
#     ccall((:Z3_mk_real2int,"libz3"),Z3_ast,(Z3_context,Z3_ast),c,t1)
# end
#
# @wrap function Z3_mk_is_int(c::Z3_context,t1::Z3_ast)
#     ccall((:Z3_mk_is_int,"libz3"),Z3_ast,(Z3_context,Z3_ast),c,t1)
# end
